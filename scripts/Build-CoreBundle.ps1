[CmdletBinding()]
param(
    [string]$OutputPath = "dist\SanctionPublicChoiceLean-core.zip",
    [switch]$NoReferences,
    [switch]$NoPdf,
    [switch]$SkipBuildCheck,
    [switch]$Submission
)

<#
Build-CoreBundle.ps1 — the source archive of the project.

Rewritten 2026-09-15 (round S, doc 87 S3) after the reader's 2026-09-12
Lean-and-archive package found the previous recipe omitted
`paper/main_fragments/` (so the archived manuscript could not build), checked
no native exit code, downgraded missing inputs to warnings, deleted the
previous archive before the new one existed, recorded no provenance, and
relied on `Compress-Archive`, which drops dotfiles on non-Windows hosts. The
protocol now:

  1. resolve provenance first: commit, exact tag (or "none"), dirty flag,
     toolchain, mathlib revision;
  2. check every native command's exit code and stop before staging on any
     failure (the pattern of scripts/Audit-Round.ps1);
  3. fail closed on any missing mandatory input; only the reference libraries
     are optional (and excluded under -NoReferences, the public profile);
  4. stage into an empty directory, drop `__pycache__`, and verify the TeX
     input closure of the four roots inside the staged tree;
  5. write CORE-BUNDLE-MANIFEST.txt with the provenance and one
     `sha256  bytes  path` line per member (the manifest cannot hash itself);
  6. compress with the .NET ZipFile API (hidden files included) into a
     uniquely named candidate next to the destination;
  7. reopen the candidate and verify path safety, no duplicate or
     case-colliding members, the exact member set, every length and every
     SHA256 against the staged tree;
  8. only then replace the previous archive (its digest is printed first),
     and write the final archive's digest to a `.sha256` sidecar.

Nothing here runs a hosted job (Rule 25). The archive is a snapshot of the
working tree at the resolved commit; a dirty tree is reported in the manifest
and on the console, not refused, so a packaging-only fix can be archived
before its commit — but the manifest then says so.

Profiles (round Z, 2026-09-17, doc 89 D8, after the reader's S–V audit found
the archive that accompanies the submission carried the unsubmitted notes and
the bracketed authorship sheets):

  default      private transfer bundle: everything below, reference libraries
               included; never redistributed.
  -NoReferences public source archive: the reference libraries excluded.
  -Submission  the archive uploaded with the submission: -NoReferences and,
               in addition, without the notes root and its staging sections
               (paper/sanctions_jet_notes.tex, paper/note_sections), the
               decision sheets (paper/submission), the internal audit notes
               (audit-notes) and the agent instruction files (AGENTS.md,
               CLAUDE.md). The TeX closure check then covers the three
               submitted roots.

Since 2026-10-19 (LEANREPO M3, decision D4) -Submission no longer derives
its contents from the directory lists below: it copies exactly the paths of
the allowlist release/SUBMISSION-MANIFEST.txt (a line ending in "/" stands
for every tracked file under that directory), fails on a listed path that is
missing, and fails if a repository file that the three submitted documents
cite with \path{...} is absent from the staged tree.
#>

$ErrorActionPreference = "Stop"
$PSNativeCommandUseErrorActionPreference = $false
if ($Submission) { $NoReferences = $true }

$repoRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $repoRoot

function Fail([string]$Message) { throw "Build-CoreBundle: $Message" }

function Invoke-Checked {
    param([string]$What, [scriptblock]$Command)
    & $Command
    if ($LASTEXITCODE -ne 0) { Fail "$What exited with code $LASTEXITCODE" }
}

function Resolve-OutputPath {
    param([string]$Path)
    if ([System.IO.Path]::IsPathRooted($Path)) {
        return [System.IO.Path]::GetFullPath($Path)
    }
    return [System.IO.Path]::GetFullPath((Join-Path $repoRoot $Path))
}

function Get-TexInputs([string]$Path) {
    $out = @()
    foreach ($line in (Get-Content -LiteralPath $Path -Encoding UTF8)) {
        $code = [regex]::Replace($line, '(?<!\\)%.*$', '')
        foreach ($m in [regex]::Matches($code, '\\(?:input|include)\{([^}]+)\}')) {
            $out += $m.Groups[1].Value
        }
    }
    return $out
}

function Get-Sha256Hex([System.IO.Stream]$Stream) {
    $sha = [System.Security.Cryptography.SHA256]::Create()
    try {
        return ([BitConverter]::ToString($sha.ComputeHash($Stream))).Replace('-', '').ToLowerInvariant()
    } finally { $sha.Dispose() }
}

# ---- 1. provenance, before anything is copied -------------------------------
$commit = (git rev-parse HEAD)
if ($LASTEXITCODE -ne 0) { Fail "git rev-parse HEAD failed" }
$commit = $commit.Trim()
$tag = (git describe --tags --exact-match HEAD 2>$null)
if ($LASTEXITCODE -ne 0 -or -not $tag) { $tag = "(none: HEAD is not at a tag)" } else { $tag = "$tag".Trim() }
$dirty = @(git status --porcelain --untracked-files=no)
if ($LASTEXITCODE -ne 0) { Fail "git status failed" }
$dirtyNote = if ($dirty.Count -gt 0) { "DIRTY: $($dirty.Count) tracked file(s) differ from $commit" } else { "clean (tracked files match $commit)" }
if ($dirty.Count -gt 0) { Write-Warning $dirtyNote }
$toolchain = (Get-Content -LiteralPath lean-toolchain -Raw).Trim()
$lakeManifest = Get-Content -LiteralPath lake-manifest.json -Raw | ConvertFrom-Json
$mathlibRev = ($lakeManifest.packages | Where-Object { $_.name -eq 'mathlib' }).rev
if (-not $mathlibRev) { Fail "mathlib revision not found in lake-manifest.json" }

$resolvedOutput = Resolve-OutputPath $OutputPath
$outputDir = Split-Path -Parent $resolvedOutput
if (-not (Test-Path -LiteralPath $outputDir)) {
    New-Item -ItemType Directory -Path $outputDir | Out-Null
}

# ---- 2. the toolchain and the build, exit codes checked ---------------------
$leanVersion = "(build check skipped)"
$lakeVersion = "(build check skipped)"
if (-not $SkipBuildCheck) {
    Write-Host "Checking Lean toolchain..."
    $leanVersion = (lean --version) -join "`n"
    if ($LASTEXITCODE -ne 0) { Fail "lean --version exited with code $LASTEXITCODE" }
    $lakeVersion = (lake --version) -join "`n"
    if ($LASTEXITCODE -ne 0) { Fail "lake --version exited with code $LASTEXITCODE" }
    Write-Host "Running lake build before packaging..."
    Invoke-Checked "lake build" { lake build }
}

# ---- 3. the input lists: mandatory unless said otherwise --------------------
$topFiles = @(
    ".gitignore",
    "LICENSE",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "Sanctions.lean",
    "README.md",
    "README-AUDIT.md",
    "REPRODUCIBILITY.md",
    "CITATION.cff",
    "AGENTS.md",
    "BUILD-STATUS.md",
    "HEADLINE-SNAPSHOT.md",
    "ASSUMPTION-SURFACE-REGISTER.md",
    "LEAN-COMPANION.md",
    "CLAUDE.md",
    "CORE-BUNDLE.md",
    # The paper lives in paper/ (CLAUDE.md Rule 21): four thin roots, two
    # shared includes, four section directories (below), its BibTeX
    # database, its style file and the three precompiled bibliographies.
    "paper/annote.bib",
    "paper/econ-aea.bst",
    "paper/sanctions_preamble.tex",
    "paper/sanctions_appendix_body.tex",
    "paper/sanctions_jet_draft.tex",
    "paper/sanctions_jet_appendix.tex",
    "paper/sanctions_jet_notes.tex",
    "paper/sanctions_formal_supplement.tex",
    "paper/sanctions_highlights.txt",
    "paper/sanctions_jet_draft.bbl",
    "paper/sanctions_jet_appendix.bbl",
    "paper/sanctions_formal_supplement.bbl"
)
if ($Submission) {
    $internalTop = @("paper/sanctions_jet_notes.tex", "AGENTS.md", "CLAUDE.md")
    $topFiles = @($topFiles | Where-Object { $internalTop -notcontains $_ })
}
if (-not $NoPdf) {
    $topFiles += "paper/sanctions_jet_draft.pdf"
    $topFiles += "paper/sanctions_jet_appendix.pdf"
    $topFiles += "paper/sanctions_formal_supplement.pdf"
}

$coreDirs = @(
    "Sanctions",
    "docs",
    "audit-notes",
    "scripts",
    "paper/main_sections",
    "paper/appendix_sections",
    "paper/note_sections",
    "paper/submission"
)
if ($Submission) {
    $internalDirs = @("paper/note_sections", "paper/submission", "audit-notes")
    $coreDirs = @($coreDirs | Where-Object { $internalDirs -notcontains $_ })
}

# The submission profile is an explicit allowlist (LEANREPO M3, 2026-10-19):
# a line ending in "/" stands for every tracked file under that directory, any
# other line names one file. A listed file that is absent, or a listed
# directory with no tracked file present, fails the build; nothing outside the
# list is copied. -NoPdf drops the listed PDFs.
$allowlist = "release/SUBMISSION-MANIFEST.txt"
if ($Submission) {
    if (-not (Test-Path -LiteralPath $allowlist -PathType Leaf)) { Fail "submission allowlist missing: $allowlist" }
    $listed = @()
    $absent = @()
    foreach ($raw in (Get-Content -LiteralPath $allowlist -Encoding UTF8)) {
        $entry = $raw.Trim()
        if (-not $entry -or $entry.StartsWith('#')) { continue }
        if ($NoPdf -and $entry.EndsWith('.pdf')) { continue }
        if ($entry.EndsWith('/')) {
            $under = @(git -c core.quotepath=false ls-files -- $entry)
            if ($LASTEXITCODE -ne 0) { Fail "git ls-files failed for $entry" }
            $present = @($under | Where-Object { Test-Path -LiteralPath $_ -PathType Leaf })
            if ($present.Count -eq 0) { $absent += $entry; continue }
            $listed += $present
        } elseif (Test-Path -LiteralPath $entry -PathType Leaf) {
            $listed += $entry
        } else {
            $absent += $entry
        }
    }
    if ($absent.Count -gt 0) { Fail ("allowlisted path(s) missing: " + ($absent -join ', ')) }
    $topFiles = @($listed | Sort-Object -Unique)
    $coreDirs = @()
    # The archive holds only the listed files, so its working-tree note covers
    # exactly those: a modified file outside the list does not make the archive
    # differ from the commit.
    $inArchive = @{}
    foreach ($f in $topFiles) { $inArchive[$f] = $true }
    $dirty = @($dirty | Where-Object { $inArchive.ContainsKey((($_.Substring(3) -split ' -> ')[-1]).Trim('"')) })
    $dirtyNote = if ($dirty.Count -gt 0) { "DIRTY: $($dirty.Count) archived file(s) differ from $commit" } else { "clean (every archived file matches $commit)" }
    Write-Host "Archived files against the commit: $dirtyNote"
}

$referenceDirs = @()
if (-not $NoReferences) { $referenceDirs = @("BookRefer", "PaperRefer") }
$profile = if ($Submission) { "submission" } elseif ($NoReferences) { "public" } else { "private transfer" }
$role = if ($Submission) {
    "submission archive: exactly the paths of $allowlist; the reference libraries, the notes root and paper/note_sections, paper/submission, audit-notes, the planning material and the agent and editor configuration are excluded"
} elseif ($NoReferences) {
    "public source archive: the reference libraries BookRefer/ and PaperRefer/ are excluded"
} else {
    "private transfer bundle: the reference libraries BookRefer/ and PaperRefer/ are included and must not be redistributed"
}

$missing = @()
foreach ($f in $topFiles) { if (-not (Test-Path -LiteralPath $f -PathType Leaf)) { $missing += $f } }
foreach ($d in $coreDirs) { if (-not (Test-Path -LiteralPath $d -PathType Container)) { $missing += $d } }
if ($missing.Count -gt 0) { Fail ("mandatory input(s) missing: " + ($missing -join ', ')) }

# ---- 4. stage into an empty directory -----------------------------------------
$stageRoot = Join-Path ([System.IO.Path]::GetTempPath()) ("SanctionPublicChoiceLean-core-" + [guid]::NewGuid())
$bundleName = "SanctionPublicChoiceLean"
$bundleRoot = Join-Path $stageRoot $bundleName
New-Item -ItemType Directory -Path $bundleRoot | Out-Null
$candidate = "$resolvedOutput.candidate-" + [guid]::NewGuid().ToString('N').Substring(0, 8)

try {
    foreach ($file in $topFiles) {
        $dest = Join-Path $bundleRoot $file
        $destDir = Split-Path -Parent $dest
        if (-not (Test-Path -LiteralPath $destDir)) {
            New-Item -ItemType Directory -Force -Path $destDir | Out-Null
        }
        Copy-Item -LiteralPath $file -Destination $dest -Force
    }
    foreach ($dir in $coreDirs) {
        $dest = Join-Path $bundleRoot $dir
        $destParent = Split-Path -Parent $dest
        if (-not (Test-Path -LiteralPath $destParent)) {
            New-Item -ItemType Directory -Force -Path $destParent | Out-Null
        }
        Copy-Item -LiteralPath $dir -Destination $dest -Recurse -Force
    }
    foreach ($dir in $referenceDirs) {
        if (Test-Path -LiteralPath $dir -PathType Container) {
            Copy-Item -LiteralPath $dir -Destination (Join-Path $bundleRoot $dir) -Recurse -Force
        } else {
            Write-Warning "reference directory absent (optional on this machine): $dir"
        }
    }
    Get-ChildItem -LiteralPath $bundleRoot -Recurse -Directory -Force -Filter '__pycache__' |
        ForEach-Object { Remove-Item -LiteralPath $_.FullName -Recurse -Force }

    # The TeX input closure of the four roots must be complete inside the
    # staged tree (the manuscript is built from paper/, so inputs are relative
    # to it).
    $texRoots = @("paper/sanctions_jet_draft.tex", "paper/sanctions_jet_appendix.tex",
                  "paper/sanctions_jet_notes.tex", "paper/sanctions_formal_supplement.tex")
    if ($Submission) { $texRoots = @($texRoots | Where-Object { $_ -ne "paper/sanctions_jet_notes.tex" }) }
    $queue = New-Object System.Collections.Generic.Queue[string]
    foreach ($r in $texRoots) { $queue.Enqueue($r) }
    $seen = @{}
    $texMissing = @()
    $texCount = 0
    while ($queue.Count -gt 0) {
        $rel = $queue.Dequeue()
        if ($seen.ContainsKey($rel)) { continue }
        $seen[$rel] = $true
        $abs = Join-Path $bundleRoot $rel
        if (-not (Test-Path -LiteralPath $abs -PathType Leaf)) { $texMissing += $rel; continue }
        $texCount++
        foreach ($inp in (Get-TexInputs $abs)) {
            $name = if ($inp.EndsWith('.tex')) { $inp } else { $inp + '.tex' }
            $queue.Enqueue(("paper/" + $name).Replace('\', '/'))
        }
    }
    if ($texMissing.Count -gt 0) {
        Fail ("TeX input closure incomplete in the staged tree: " + ($texMissing -join ', '))
    }
    Write-Host "TeX input closure: $texCount files reachable from the $($texRoots.Count) roots, all present."

    # Every repository file that the submitted documents cite with \path{...}
    # must be in the archive: at the cited path, under Sanctions/, or, for a
    # bare file name, anywhere in the staged tree (LEANREPO M3).
    if ($Submission) {
        $stagedRel = @{}
        $stagedBase = @{}
        foreach ($sf in (Get-ChildItem -LiteralPath $bundleRoot -Recurse -File -Force)) {
            $stagedRel[$sf.FullName.Substring($bundleRoot.Length + 1).Replace('\', '/')] = $true
            $stagedBase[$sf.Name] = $true
        }
        $citeMissing = @()
        foreach ($tex in @($seen.Keys)) {
            $lines = Get-Content -LiteralPath (Join-Path $bundleRoot $tex) -Encoding UTF8
            $body = ($lines | ForEach-Object { [regex]::Replace($_, '(?<!\\)%.*$', '') }) -join "`n"
            foreach ($cm in [regex]::Matches($body, '\\path\{([^}]+)\}')) {
                $c = $cm.Groups[1].Value.Replace('\_', '_')
                if ($c -notmatch '\.(lean|md|txt|json|csv|ps1|py|sh|mjs|tex|cff|toml)$') { continue }
                $found = $stagedRel.ContainsKey($c) -or $stagedRel.ContainsKey("Sanctions/$c") -or
                         ((-not $c.Contains('/')) -and $stagedBase.ContainsKey($c))
                if (-not $found) { $citeMissing += "$c (cited in $tex)" }
            }
        }
        if ($citeMissing.Count -gt 0) {
            Fail ("cited repository file(s) absent from the archive: " + (($citeMissing | Sort-Object -Unique) -join ', '))
        }
        Write-Host "Cited repository files: every \path{...} file of the submitted documents is in the archive."
    }

    # ---- 5. the manifest: provenance + one hash line per member ---------------
    $manifestRel = "CORE-BUNDLE-MANIFEST.txt"
    $manifestPath = Join-Path $bundleRoot $manifestRel
    $files = Get-ChildItem -LiteralPath $bundleRoot -Recurse -File -Force | Sort-Object FullName
    $members = @{}
    $byteCount = [int64]0
    $hashLines = @()
    foreach ($f in $files) {
        $rel = $f.FullName.Substring($bundleRoot.Length + 1).Replace('\', '/')
        $stream = [System.IO.File]::OpenRead($f.FullName)
        try { $h = Get-Sha256Hex $stream } finally { $stream.Dispose() }
        $members[$rel] = [pscustomobject]@{ Bytes = $f.Length; Sha256 = $h }
        $byteCount += $f.Length
        $hashLines += ("{0}  {1,12}  {2}" -f $h, $f.Length, $rel)
    }
    $created = Get-Date -Format "yyyy-MM-dd HH:mm:ss zzz"
    @(
        "SanctionPublicChoiceLean core bundle",
        "Profile: $profile",
        "Role: $role",
        "Created: $created",
        "Source commit: $commit",
        "Tag at that commit: $tag",
        "Working tree: $dirtyNote",
        "Lean toolchain (lean-toolchain): $toolchain",
        "mathlib revision (lake-manifest.json): $mathlibRev",
        "",
        "Lean:",
        $leanVersion,
        "",
        "Lake:",
        $lakeVersion,
        "",
        "Included top-level files: $($topFiles.Count)",
        "Included core directories: $(if ($Submission) { "(none: allowlist $allowlist)" } else { $coreDirs -join ', ' })",
        "Included reference directories: $(if ($referenceDirs.Count -gt 0) { $referenceDirs -join ', ' } else { '(none)' })",
        "Excluded: .git, .lake, tmp, dist, suggestions, __pycache__ and every path not listed above",
        "Member count (excluding this manifest): $($files.Count)",
        "Byte count (excluding this manifest): $byteCount",
        "",
        "Rebuild on target machine:",
        "  lake exe cache get",
        "  lake build",
        "  pwsh scripts/Build-Paper.ps1$(if ($Submission) { ' -SkipNotes' })",
        "",
        "Members (sha256  bytes  path); the manifest cannot hash itself:",
        "(manifest)  $manifestRel"
    ) + $hashLines | Set-Content -LiteralPath $manifestPath -Encoding UTF8
    $mstream = [System.IO.File]::OpenRead($manifestPath)
    try { $mhash = Get-Sha256Hex $mstream } finally { $mstream.Dispose() }
    $members[$manifestRel] = [pscustomobject]@{ Bytes = (Get-Item -LiteralPath $manifestPath).Length; Sha256 = $mhash }

    # ---- 6. compress into a uniquely named candidate ------------------------------
    Add-Type -AssemblyName System.IO.Compression.FileSystem
    if (Test-Path -LiteralPath $candidate) { Remove-Item -LiteralPath $candidate -Force }
    [System.IO.Compression.ZipFile]::CreateFromDirectory($stageRoot, $candidate,
        [System.IO.Compression.CompressionLevel]::Optimal, $false)

    # ---- 7. verify the candidate against the staged tree ------------------------
    $zip = [System.IO.Compression.ZipFile]::OpenRead($candidate)
    $verified = 0
    try {
        $seenNames = @{}
        foreach ($entry in $zip.Entries) {
            $n = $entry.FullName
            if ($n.EndsWith('/')) { continue }
            if ($n.StartsWith('/') -or $n.StartsWith('\') -or $n.Contains('..') -or $n -match '^[A-Za-z]:') {
                Fail "unsafe member path in candidate: $n"
            }
            $key = $n.ToLowerInvariant()
            if ($seenNames.ContainsKey($key)) { Fail "duplicate or case-colliding member: $n" }
            $seenNames[$key] = $true
            if (-not $n.StartsWith("$bundleName/")) { Fail "member outside the bundle root: $n" }
            $rel = $n.Substring($bundleName.Length + 1)
            if (-not $members.ContainsKey($rel)) { Fail "unexpected member in candidate: $n" }
            $exp = $members[$rel]
            if ($entry.Length -ne $exp.Bytes) { Fail "length mismatch for $n ($($entry.Length) vs $($exp.Bytes))" }
            $es = $entry.Open()
            try { $eh = Get-Sha256Hex $es } finally { $es.Dispose() }
            if ($eh -ne $exp.Sha256) { Fail "sha256 mismatch for $n" }
            $verified++
        }
    } finally { $zip.Dispose() }
    if ($verified -ne $members.Count) {
        Fail "member count in candidate ($verified) differs from staged tree ($($members.Count))"
    }

    # ---- 8. replace the previous archive only now ----------------------------------
    if (Test-Path -LiteralPath $resolvedOutput) {
        $old = (Get-FileHash -LiteralPath $resolvedOutput -Algorithm SHA256).Hash.ToLowerInvariant()
        Write-Host "Replacing the previous archive (sha256 $old)."
    }
    Move-Item -LiteralPath $candidate -Destination $resolvedOutput -Force
    $final = (Get-FileHash -LiteralPath $resolvedOutput -Algorithm SHA256).Hash.ToLowerInvariant()
    Set-Content -LiteralPath "$resolvedOutput.sha256" -Value ("{0}  {1}" -f $final, (Split-Path -Leaf $resolvedOutput)) -Encoding ascii

    $zipItem = Get-Item -LiteralPath $resolvedOutput
    Write-Host "Wrote $($zipItem.FullName)"
    Write-Host ("Size: {0:N2} MB; members verified: {1}; source commit {2}; tag {3}; tree {4}" -f ($zipItem.Length / 1MB), $verified, $commit, $tag, $dirtyNote)
    Write-Host "sha256 $final (also in $resolvedOutput.sha256)"
}
finally {
    if (Test-Path -LiteralPath $candidate) { Remove-Item -LiteralPath $candidate -Force }
    if (Test-Path -LiteralPath $stageRoot) { Remove-Item -LiteralPath $stageRoot -Recurse -Force }
}
