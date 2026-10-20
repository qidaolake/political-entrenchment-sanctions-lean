# Audit-Round.ps1 — one-command per-round audit gate (Rules 10 / 13 / 17 / 18).
#
# Runs, in order:
#   1. Toolchain pin check     — `lake env lean --version` vs `lean-toolchain`,
#                                manifest revisions present (Rule 17).
#   2. Package architecture    — all six layer aggregators import EVERY module
#                                in their folders, and lower layers never import
#                                a higher layer.
#   3. Source hygiene scan     — no `sorry` / `admit` tactics, no project
#                                `axiom` declarations in Sanctions/ (Rule 10).
#   4. Build                   — incremental `lake build`, exit 0 required.
#      (For a headline-accepting round, run the FROM-EMPTY variant instead:
#       `-CleanRebuild` removes .lake/build first — Rule 17.)
#   5. Headline snapshot       — self-test the structural fingerprint, regenerate
#                                via Generate-HeadlineSnapshot.ps1 and compare with
#                                the committed snapshot (Compare-Snapshot.ps1): a
#                                changed fingerprint / axiom set / vanished row
#                                FAILS (Rule 18); a moved printed hash alone is
#                                reported (round O, doc 82 P5).
#
# Usage (from repo root):
#   pwsh -File scripts\Audit-Round.ps1                # normal round
#   pwsh -File scripts\Audit-Round.ps1 -CleanRebuild  # headline round
#   pwsh -File scripts/Audit-Round.ps1 -SkipBuild            # after a build
# Run under pwsh 7 (or with the BOM these scripts now carry): Windows
# PowerShell 5.1 decodes a BOM-less UTF-8 script with the ANSI codepage and
# mangles the Greek-lettered contract roots in gate 5's probe (2026-09-10).
#
# `-SkipBuild` runs every gate EXCEPT the build. It exists for CI, where the
# workflow has already run `lake build` on the same runner and rebuilding only
# to re-check gates 5 and 6 would double the job time. Never pass it on a
# headline-accepting round: gates 5/6 read a `.lake/build` that must correspond
# to the current source, and skipping the build makes that correspondence an
# assumption rather than a check.
#
# This script runs under Windows PowerShell 5.1 and under PowerShell Core on
# Linux; the only host-specific step is re-invoking the snapshot generator,
# which picks its executable from $PSVersionTable below.
#
# Exit codes: 0 = all gates green; 1 = a gate failed (message says which).

param([switch]$CleanRebuild, [switch]$SkipBuild)

$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root

function Fail($msg) { Write-Host "GATE FAILED: $msg" -ForegroundColor Red; Pop-Location; exit 1 }

try {
    # --- 1. Toolchain pin (Rule 17) ---------------------------------------
    $pin = (Get-Content 'lean-toolchain' -TotalCount 1).Trim()
    $ver = (& lake env lean --version) -join ' '
    $pinVer = ($pin -split ':')[-1].TrimStart('v')
    if ($ver -notmatch [regex]::Escape($pinVer)) {
        Fail "toolchain drift: lean-toolchain=$pin but lake env lean --version=$ver"
    }
    if (-not (Test-Path 'lake-manifest.json')) { Fail 'lake-manifest.json missing' }
    Write-Host "  [1/7] toolchain pin OK ($pin)"

    # --- 2. Aggregator completeness ---------------------------------------
    $aggSpec = @(
        @{ Agg = 'Sanctions/Domain.lean';      Dir = 'Sanctions/Domain';      Prefix = 'Sanctions.Domain.' },
        @{ Agg = 'Sanctions/Foundations.lean'; Dir = 'Sanctions/Foundations'; Prefix = 'Sanctions.Foundations.' },
        @{ Agg = 'Sanctions/Postulates.lean';  Dir = 'Sanctions/Postulates';  Prefix = 'Sanctions.Postulates.' },
        @{ Agg = 'Sanctions/Theory.lean';      Dir = 'Sanctions/Theory';      Prefix = 'Sanctions.Theory.' },
        @{ Agg = 'Sanctions/Examples.lean';    Dir = 'Sanctions/Examples';    Prefix = 'Sanctions.Examples.' },
        @{ Agg = 'Sanctions/Paper.lean';       Dir = 'Sanctions/Paper';       Prefix = 'Sanctions.Paper.' }
    )
    foreach ($s in $aggSpec) {
        $imports = Select-String -Path $s.Agg -Pattern '^import\s+(\S+)' |
            ForEach-Object { $_.Matches[0].Groups[1].Value }
        $missing = @()
        Get-ChildItem -Path $s.Dir -Recurse -Filter '*.lean' | ForEach-Object {
            $rel = $_.FullName.Substring((Join-Path $root '').Length).TrimStart('\','/')
            $mod = ($rel -replace '\\','/' -replace '\.lean$','' -replace '/','.')
            if ($imports -notcontains $mod) { $missing += $mod }
        }
        if ($missing.Count -gt 0) {
            Fail ("aggregator {0} missing: {1}" -f $s.Agg, ($missing -join ', '))
        }
    }

    $layerRules = @(
        @{
            # Domain is the base layer: it declares the state space [0,1] and
            # nothing else, so it may import no project module at all. Written
            # as a positive fence rather than a list of forbidden layers, so a
            # future layer cannot be added above it and silently omitted here.
            Dir = 'Sanctions/Domain'
            Pattern = '^import\s+Sanctions\.(?!Domain\.)'
            Message = 'Domain is the base layer and may import no other project layer'
        },
        @{
            Dir = 'Sanctions/Foundations'
            Pattern = '^import\s+Sanctions\.(Postulates|Theory|Examples|Paper)(\.|$)'
            Message = 'Foundations may not import Postulates, Theory, Examples, or Paper'
        },
        @{
            Dir = 'Sanctions/Postulates'
            Pattern = '^import\s+Sanctions\.(Theory|Examples|Paper)(\.|$)'
            Message = 'Postulates may not import Theory, Examples, or Paper'
        },
        @{
            Dir = 'Sanctions/Theory'
            Pattern = '^import\s+Sanctions\.(Examples|Paper)(\.|$)'
            Message = 'Theory may not import Examples or Paper'
        },
        @{
            Dir = 'Sanctions/Examples'
            Pattern = '^import\s+Sanctions\.Paper(\.|$)'
            Message = 'Examples may not import Paper (the paper interface is the top layer)'
        }
    )
    foreach ($rule in $layerRules) {
        $paths = Get-ChildItem -Path $rule.Dir -Recurse -Filter '*.lean' |
            ForEach-Object { $_.FullName }
        $violations = @(Select-String -Path $paths -Pattern $rule.Pattern)
        if ($violations.Count -gt 0) {
            $violations | ForEach-Object {
                Write-Host ("  {0}:{1}: {2}" -f $_.Path, $_.LineNumber, $_.Line.Trim())
            }
            Fail $rule.Message
        }
    }
    # Stray-module check: a .lean file directly under Sanctions/ that is not
    # one of the five layer roots would be unimported, unbuilt, and unscanned.
    $depth1 = @(Get-ChildItem -Path 'Sanctions' -Filter '*.lean' |
        ForEach-Object { $_.Name })
    $expectedRoots = @('Domain.lean','Examples.lean','Foundations.lean',
                       'Headlines.lean','Paper.lean','Postulates.lean','Theory.lean')
    $stray = @($depth1 | Where-Object { $expectedRoots -notcontains $_ })
    if ($stray.Count -gt 0) {
        Fail ("stray depth-1 module(s) under Sanctions/: {0} (unimported by any layer root; invisible to build and scans)" -f ($stray -join ', '))
    }

    # The statements of the paper interface state results without proving them, so they must not
    # import the proofs that discharge them or the headline gate file (LEANREPO M4, 2026-10-19).
    $stmtImports = @(Select-String -Path 'Sanctions/Paper/Statements.lean' -Pattern '^import\s+(Sanctions\.Paper\.Proofs|Sanctions\.Headlines|Sanctions\.Paper|Sanctions)\s*$')
    if ($stmtImports.Count -gt 0) {
        $stmtImports | ForEach-Object { Write-Host ("  {0}:{1}: {2}" -f $_.Path, $_.LineNumber, $_.Line.Trim()) }
        Fail 'Sanctions/Paper/Statements.lean imports the proofs, the headline gate file or a root aggregator'
    }

    # --- Transitive import closure (Rule 19/23) ----------------------------
    # The regex fence above reads each file's DIRECT imports. That is sound for
    # the layer claim only via an inductive argument -- every module is checked,
    # and the aggregators are complete -- which is true here but couples two
    # gates in a way that is easy to break silently. So walk the graph instead
    # and check the real closure.
    #
    # NOT via `lake env lean --src-deps`, despite that being the obvious tool
    # and the one the migration proposal prescribes for exactly this purpose.
    # Measured on 2026-08-27 at the 4.29.1 pin, --src-deps prints DIRECT imports
    # only: Sanctions/Theory.lean reports 108 Theory files and zero Foundations;
    # Sanctions/Foundations/Basic.lean reports its one Domain import and nothing
    # under it. It is a dependency lister, not a closure, and using it as one
    # would restate the direct check while claiming more.
    $importsOf = @{}
    Get-ChildItem -Path 'Sanctions' -Recurse -Filter '*.lean' | ForEach-Object {
        $rel = $_.FullName.Substring((Join-Path $root '').Length).Replace([char]92, [char]47)
        $mod = ($rel -replace '\.lean$','') -replace '/','.'
        $importsOf[$mod] = @(Select-String -Path $_.FullName -Pattern '^import\s+(Sanctions\S*)' |
            ForEach-Object { $_.Matches[0].Groups[1].Value })
    }
    $layerOf = { param($m) if ($m -match '^Sanctions\.([A-Za-z]+)') { $matches[1] } else { 'root' } }
    $closureSpec = @(
        @{ Root = 'Sanctions.Domain';      Allow = @('Domain') },
        @{ Root = 'Sanctions.Foundations'; Allow = @('Domain', 'Foundations') },
        @{ Root = 'Sanctions.Postulates';  Allow = @('Domain', 'Foundations', 'Postulates') },
        @{ Root = 'Sanctions.Theory';      Allow = @('Domain', 'Foundations', 'Postulates', 'Theory') }
    )
    foreach ($c in $closureSpec) {
        $seen = @{}; $queue = [System.Collections.Queue]::new(); $queue.Enqueue($c.Root)
        while ($queue.Count -gt 0) {
            $m = $queue.Dequeue()
            if ($seen.ContainsKey($m)) { continue }
            $seen[$m] = $true
            foreach ($d in $importsOf[$m]) { if (-not $seen.ContainsKey($d)) { $queue.Enqueue($d) } }
        }
        $reached = @($seen.Keys | Where-Object { $_ -ne $c.Root })
        if ($reached.Count -eq 0) {
            Fail ("import closure for {0} is empty; the check would pass vacuously" -f $c.Root)
        }
        $bad = @($reached | Where-Object { $c.Allow -notcontains (& $layerOf $_) })
        if ($bad.Count -gt 0) {
            $bad | Select-Object -First 8 | ForEach-Object { Write-Host ("  {0}" -f $_) }
            Fail ("{0} transitively imports outside [{1}]" -f $c.Root, ($c.Allow -join ', '))
        }
    }
    Write-Host ('  [2/7] import closure OK (transitive walk over {0} modules)' -f $importsOf.Count)


    # --- A0.4 Foundations vocabulary (Rule 19) -----------------------------
    # Zero declarations in Foundations may name the game surface. Shares its
    # comment stripper with Generate-FoundationRoles.ps1 so the gate and the
    # manifest cannot disagree -- and so the strip order (block comments BEFORE
    # line comments) is fixed in one place. The reverse order decapitates every
    # `/-- ` opener and scans docstrings as code; on 2026-08-27 that produced
    # four phantom violations, every one of them prose saying the opposite.
    . (Join-Path $PSScriptRoot 'FoundationVocabulary.ps1')
    $gameLeaks = @()
    Get-ChildItem -Path 'Sanctions/Foundations' -Recurse -Filter '*.lean' | ForEach-Object {
        $body = Get-StrippedLeanSource -Path $_.FullName
        $hit = Test-TokenMatch -Statement $body -Tokens $script:GameTokens
        if ($hit) { $gameLeaks += ("{0} ({1})" -f $_.Name, $hit) }
    }
    if ($gameLeaks.Count -gt 0) {
        $gameLeaks | ForEach-Object { Write-Host ("  {0}" -f $_) }
        Fail 'Foundations declaration names the game surface (Rule 19): move it to Theory'
    }
    Write-Host '  [2/7] Foundations vocabulary OK (no Params/AbstractGame/affineF in code)'

    # Rule-19 content heuristic (WARN only): a Theory file mentioning no
    # project-specific token is a Foundations-placement candidate.
    $tokenPattern = 'AbstractGame|ValueClass|ShockedParams|FourGroup|Certificate|SenderResponse'
    $genericTheory = @(Get-ChildItem -Path 'Sanctions/Theory' -Recurse -Filter '*.lean' |
        Where-Object { -not (Select-String -Path $_.FullName -Pattern $tokenPattern -Quiet) } |
        ForEach-Object { $_.Name })
    if ($genericTheory.Count -gt 0) {
        Write-Host ("  [2/7] WARN: Theory file(s) with no project-specific tokens (Rule-19 Foundations candidates): {0}" -f ($genericTheory -join ', ')) -ForegroundColor Yellow
    }

    Write-Host '  [2/7] package architecture OK (complete aggregators; layer boundaries clean)'

    # Rule-22 affine-surface ratchet (added round BB, 2026-09-28). It ran only in
    # the manually dispatched workflow, so it lapsed unnoticed: four readers of
    # the inert `p.δ` accumulated outside its baseline, and its ASCII-only regex
    # missed subscripted receivers such as `p₁.δ`. It is part of gate 2 so the
    # gate count stays seven.
    & node scripts/audit-affine-surface.mjs | Out-Null
    if ($LASTEXITCODE -ne 0) {
        & node scripts/audit-affine-surface.mjs
        Fail 'affine surface grew (Rule 22): classify each new reader of p.delta, then node scripts/audit-affine-surface.mjs --write-baseline'
    }
    Write-Host '  [2/7] affine surface OK (no reader of the inert p.delta outside the reviewed baseline)'

    # --- 3. Source hygiene (Rule 10) ---------------------------------------
    # `sorry`/`admit` as standalone tactic tokens; `by sorry` on one line;
    # `axiom` declarations (incl. private/protected).
    # NOTE: this scan is deliberately COMMENT-BLIND. Stripping Lean comments
    # correctly means tracking nested `/- ... -/` depth, and a depth tracker that
    # gets confused would *hide* a real `axiom` — the one direction this gate
    # must never fail in. So prose is scanned too, and the cost is that a
    # docstring line may not BEGIN with `axiom ` (or `sorry` / `admit` alone).
    # That is a real constraint on how comments are wrapped, not a bug; see the
    # note in the header of Sanctions/Headlines.lean, which tripped it.
    # NOTE: the file list is built with an explicit -Recurse enumeration —
    # a 'Sanctions/**/*.lean' glob does NOT recurse in Windows PowerShell 5.1
    # ('**' is a single-segment wildcard there), which silently skipped every
    # Theory subdirectory file until 2026-07-24.
    $leanFiles = @((Get-ChildItem -Path 'Sanctions' -Recurse -Filter '*.lean').FullName) + `
        @((Join-Path $root 'Sanctions.lean'))
    $bad = Select-String -Path $leanFiles `
        -Pattern '^\s*(sorry|admit)\s*$|:=\s*sorry\b|\bby\s+sorry\b|^\s*(private\s+|protected\s+)?axiom\s' -AllMatches
    if ($bad) {
        $bad | ForEach-Object { Write-Host ("  {0}:{1}: {2}" -f $_.Path, $_.LineNumber, $_.Line.Trim()) }
        Fail 'sorry / admit / axiom found in source'
    }
    Write-Host '  [3/7] hygiene scan OK (no sorry/admit/axiom)'

    # --- 4. Build (Rule 17) -------------------------------------------------
    if ($SkipBuild) {
        if ($CleanRebuild) { Fail '-SkipBuild and -CleanRebuild are contradictory' }
        Write-Host '  [4/7] build SKIPPED (-SkipBuild): gates 5/6 trust the existing .lake/build'
    } else {
        if ($CleanRebuild -and (Test-Path '.lake/build')) {
            Write-Host '  [4/7] clean rebuild requested: removing .lake/build ...'
            Remove-Item -Recurse -Force '.lake/build'
        }
        # The job count was piped to Out-Null and then hand-copied into
        # README.md and BUILD-STATUS.md. It drifted three times (2026-07-30,
        # 2026-08-26, 2026-08-27), because nothing forced either file to be
        # rewritten when a round added a module. Capture it here and check it,
        # so the next drift fails the round instead of being noticed months on.
        # A0.3 isolated module builds: each layer must build on its own, so a
        # missing import is caught as a layer fault rather than masked by the
        # aggregate build pulling the module in from somewhere else. Cheap once
        # the full build below has populated the cache -- these are near-no-ops
        # on a warm tree and only bite when a layer is genuinely not standalone.
        foreach ($layer in @('Sanctions.Domain', 'Sanctions.Foundations',
                             'Sanctions.Postulates', 'Sanctions.Theory',
                             'Sanctions.Examples', 'Sanctions.Paper')) {
            & lake build $layer | Out-Null
            if ($LASTEXITCODE -ne 0) { Fail ("isolated build failed: $layer") }
        }
        $buildOut = & lake build 2>&1
        if ($LASTEXITCODE -ne 0) {
            $buildOut | Select-Object -Last 40 | ForEach-Object { Write-Host $_ }
            Fail "lake build exited $LASTEXITCODE"
        }
        $jobLine = $buildOut | Select-String -Pattern 'Build completed successfully \((\d+) jobs\)' |
            Select-Object -Last 1
        if (-not $jobLine) {
            Write-Host '  [4/7] lake build OK (job count not reported; receipt check skipped)'
        } else {
            $jobs = [int]$jobLine.Matches[0].Groups[1].Value
            $stale = @()
            foreach ($doc in @('README.md', 'BUILD-STATUS.md')) {
                $txt = Get-Content $doc -Raw
                if ($txt -notmatch ("(?<![0-9])" + $jobs + "(?![0-9])")) { $stale += $doc }
            }
            if ($stale.Count -gt 0) {
                Fail ("build is {0} jobs; receipt not updated in: {1}" -f $jobs, ($stale -join ', '))
            }
            Write-Host ("  [4/7] lake build OK ({0} jobs; receipt current in README + BUILD-STATUS)" -f $jobs)
        }
    }

    # --- 5. Headline snapshot regenerate + diff (Rule 18) -------------------
    $before = Get-Content 'HEADLINE-SNAPSHOT.md' -Raw
    # Re-invoke under the SAME host edition: 'powershell' does not exist on
    # Linux, so hard-coding it made this gate Windows-only and kept it out of
    # CI. Join-Path rather than a literal backslash for the same reason.
    $psExe = if ($PSVersionTable.PSEdition -eq 'Core') { 'pwsh' } else { 'powershell' }
    # -NoProfile -NonInteractive: without them the nested host loads the user
    # profile and can block on stdin, which hangs this gate silently after the
    # expensive build has already passed (observed 2026-08-26: 44 min, no child
    # process, no output). The child must never be able to wait for a human.
    # Round O (doc 82 P5): the fingerprint's invariants are re-verified before
    # the snapshot is regenerated, and the comparison is keyed on the
    # structural column (scripts/Compare-Snapshot.ps1, shared with the self-test).
    & $psExe -NoProfile -NonInteractive -File (Join-Path $PSScriptRoot 'Test-StructuralFingerprint.ps1')
    if ($LASTEXITCODE -ne 0) { Fail 'structural fingerprint self-test failed (scripts/Test-StructuralFingerprint.ps1)' }
    & $psExe -NoProfile -NonInteractive -File (Join-Path $PSScriptRoot 'Generate-HeadlineSnapshot.ps1')
    if ($LASTEXITCODE -ne 0) { Fail 'snapshot generator failed (vanished headline or dirty axioms)' }
    $after = Get-Content 'HEADLINE-SNAPSHOT.md' -Raw
    # Compare on content, not line endings (the generator writes with
    # Environment.NewLine; git may check the committed file out either way). A
    # headline row whose printed hash moved while its structural fingerprint
    # stayed is a rendering change -- a binder rename, a pretty-printer
    # difference -- and is reported, not failed; every other difference is drift.
    . (Join-Path $PSScriptRoot 'Compare-Snapshot.ps1')
    $cmp = Compare-HeadlineSnapshot $before $after
    if ($cmp.Verdict -eq 'drift') {
        Write-Host '  snapshot CHANGED — diff:'
        & git diff --no-color 'HEADLINE-SNAPSHOT.md' | Write-Host
        Fail 'headline snapshot drift: review the diff; a changed fingerprint, axiom set or row set requires user sign-off (Rule 3/18)'
    }
    if ($cmp.Verdict -eq 'rendering') {
        Write-Host ("  [5/7] NOTE: printed rendering moved for {0} headline row(s), structural fingerprints unchanged (information, not drift): {1}" -f $cmp.Moved.Count, ($cmp.Moved -join ', '))
    }
    # Only the HEADLINE table. The snapshot also carries a "Pinned economy
    # data" table (Rule-18 extension, 2026-08-11); counting both conflates
    # 37 headlines with 100 pinned constants.
    $snapLines = @(Get-Content 'HEADLINE-SNAPSHOT.md')
    $pinIdx = [Array]::FindIndex($snapLines, [Predicate[string]]{ param($l) $l -match '^##\s+Pinned economy data' })
    $headSection = if ($pinIdx -ge 0) { $snapLines[0..($pinIdx - 1)] } else { $snapLines }
    $headlineRows = @(
        $headSection | Where-Object { $_ -match '^\|\s*`[^`]+`\s*\|' }
    ).Count
    Write-Host ("  [5/7] headline snapshot stable ({0} rows, hashes unchanged)" -f $headlineRows)

    # --- 6. Headline replay coverage (Rule 10 x Rule 18) --------------------
    # The snapshot generator and Sanctions/Headlines.lean carry INDEPENDENT
    # lists of the headline set. Gate 5 regenerates the snapshot from the
    # generator's list and never looks at Headlines.lean, so the two drifted
    # apart unnoticed until 2026-08-09: two rows still named the affine
    # theorems after the general-F swap, and four rows had no replay line at
    # all. A snapshot row with no `#print axioms` line is a headline whose
    # kernel scan is NOT replayed on every build, which is precisely the
    # always-on guarantee that file exists to provide.
    $snapNames = @(
        $headSection |
            ForEach-Object { if ($_ -match '^\|\s*`([^`]+)`\s*\|') { $Matches[1] } }
    )
    $replayRaw = @(
        Get-Content 'Sanctions/Headlines.lean' |
            ForEach-Object { if ($_ -match '^#print axioms\s+(\S+)') { $Matches[1] } }
    )
    if ($replayRaw.Count -ne $snapNames.Count) {
        Fail ("headline replay drift: {0} rows in HEADLINE-SNAPSHOT.md but {1} `#print axioms` lines in Sanctions/Headlines.lean. Keep the two lists in sync (Rule 18)." -f $snapNames.Count, $replayRaw.Count)
    }
    # Snapshot records fully-qualified names; Headlines.lean resolves under an
    # `open` list, so compare on the trailing segment chain rather than exactly.
    $missing = @()
    foreach ($n in $snapNames) {
        $hit = $false
        foreach ($r in $replayRaw) {
            if ($n -eq $r -or $n.EndsWith('.' + $r)) { $hit = $true; break }
        }
        if (-not $hit) { $missing += $n }
    }
    if ($missing.Count -gt 0) {
        Write-Host '  headline rows with NO `#print axioms` replay line:'
        $missing | ForEach-Object { Write-Host ("    - {0}" -f $_) }
        Fail 'headline replay gap: every snapshot row needs a matching line in Sanctions/Headlines.lean (Rule 10/18).'
    }
    Write-Host ("  [6/7] headline replay complete ({0}/{0} rows scanned in-build)" -f $snapNames.Count)

    # --- 7. Census coverage + evidence staleness (doc 70, F-G; user-approved D7) --
    # (i) the census's headline root list must be exactly the replay list, so
    # a headline added or renamed without re-running the census fails here;
    # (ii) every evidence hash the census reviewed a status against must equal
    # the regenerated snapshot's row, so a moved evidence declaration cannot
    # carry a "derived"/"refuted" status forward silently. Full regeneration of
    # the census stays a manual step (docs/README.md); this gate only checks
    # that what it recorded is still true of the tree.
    $censusRoots = @(Get-Content 'docs/census/roots-headlines.txt' |
        ForEach-Object { ($_ -split '#')[0].Trim() } | Where-Object { $_ -ne '' })
    if (($censusRoots -join ';') -ne ($replayRaw -join ';')) {
        Fail 'census headline roots (docs/census/roots-headlines.txt) differ from Sanctions/Headlines.lean: regenerate the census (docs/README.md)'
    }
    # (iii) the census instrument's self-test (doc 71 T2): the probe and the
    # builder must report the fixture's constructions as documented, and the
    # runner/builder must fail closed on a bogus root and a truncated file.
    & python scripts/census_selftest.py
    if ($LASTEXITCODE -ne 0) { Fail 'census self-test failed (scripts/census_selftest.py)' }
    # (iv) the unused-binder instrument's self-test (doc 80 M4): the strict
    # parser must reject every malformed-record fixture and accept the valid
    # one, and the probe protocol must round-trip on the fixture theorems.
    & python scripts/unused_run_selftest.py
    if ($LASTEXITCODE -ne 0) { Fail 'unused-binder self-test failed (scripts/unused_run_selftest.py)' }
    $evJson = 'docs/census/status-evidence.json'
    if (Test-Path $evJson) {
        $recorded = Get-Content $evJson -Raw | ConvertFrom-Json
        $snapEv = @{}
        $inEv = $false
        foreach ($l in $snapLines) {
            if ($l -match '^##\s+Evidence declarations') { $inEv = $true; continue }
            if ($l -match '^##\s+') { $inEv = $false; continue }
            if ($inEv -and $l -match '^\| `(?<n>[^`]+)` \| `(?<h>[0-9a-f]{64})` \|$') { $snapEv[$Matches['n']] = $Matches['h'] }
        }
        $stale = @()
        foreach ($prop in $recorded.PSObject.Properties) {
            if (-not $snapEv.ContainsKey($prop.Name)) { $stale += ($prop.Name + ' (no longer in the snapshot)'); continue }
            if ($snapEv[$prop.Name] -ne $prop.Value.hash) { $stale += $prop.Name }
        }
        if ($stale.Count -gt 0) {
            Write-Host '  evidence declarations whose type moved since their status was reviewed:'
            $stale | ForEach-Object { Write-Host ("    - {0}" -f $_) }
            Fail 'stale census evidence: re-review the statuses citing these declarations and regenerate the census (docs/README.md)'
        }
        Write-Host ("  [7/7] census coverage OK ({0} headline roots; {1} evidence hashes current)" -f $censusRoots.Count, @($recorded.PSObject.Properties).Count)
    } else {
        Fail ('census evidence record missing: ' + $evJson + ' (regenerate the census; docs/README.md)')
    }

    Write-Host 'ALL GATES GREEN.' -ForegroundColor Green
    exit 0
} finally {
    Pop-Location
}
