# Chord-Field-Census.ps1 -- compiler-derived field census of the chord headline
# rows (round BB, 2026-09-28; doc 110 item R5 step 1).
#
# For each theorem, which own fields of the four chord structures
# `ChordEconomy`, `ChordEconomyTwoSided` (split off by renovation item BJ3.1),
# `ChordEconomyRelief` and `ChordEconomyCs`, and of the inherited
# `AbstractGame.Params`, does its statement-plus-proof closure reach? The field
# lists and their counts are read from the compiled structures at run time
# (the `FC-STRUCT` records) and printed in the report header. The Lean side is
# `scripts/chord_field_census.lean.template` (read its header for what the
# census measures and what it does not). This wrapper splices that template
# after an `import` and an `open` line, elaborates the probe once with
# `lake env lean`, parses the `FC-...` records and writes a Markdown report.
#
# Default theorem set: every row of HEADLINE-SNAPSHOT.md whose fully-qualified
# name lies directly in the `Sanctions.Examples.ChordEconomy`,
# `ChordEconomyTwoSided`, `ChordEconomyRelief` or `ChordEconomyCs` namespace
# (one name component below it; a deeper name is left out) -- the chord rows,
# listed with their row numbers in the report. Pass names to census others;
# they resolve under the snapshot generator's `open` line.
#
# Usage (from the repo root, under pwsh -- not Windows PowerShell 5.1):
#   pwsh -File scripts/Chord-Field-Census.ps1
#   pwsh -File scripts/Chord-Field-Census.ps1 ChordEconomyTwoSided.target_only_regime_generalF
#   pwsh -File scripts/Chord-Field-Census.ps1 -OutFile docs/census/x.md -Imports Sanctions.Examples.PlacableSenderBracket,Sanctions.Examples.PlacableSenderUniqueness
#   pwsh -File scripts/Chord-Field-Census.ps1 -RawFile path/to/records.txt   (also keep every FC- record)
# Lists (theorems, -Imports) may be comma-separated. -Imports defaults to the
# whole library (`Sanctions`); naming only the modules that declare the
# theorems gives the same census (the walk follows only constants reachable
# from them) and is robust to a concurrent rebuild elsewhere in the tree.
#
# Local only (Rule 25): no CI job calls this. Build discipline (Rule 24): it
# never builds; it reads the oleans already on disk, so run it after the
# library is built. It reads HEADLINE-SNAPSHOT.md and writes only $OutFile.
#
# Exit codes: 0 = report written; 1 = elaboration failure, unresolved name, or
# a record set that does not parse.

param(
    [Parameter(Position = 0, ValueFromRemainingArguments = $true)]
    [string[]]$Theorems,
    [string]$OutFile = 'docs/census/chord-field-census.md',
    [string[]]$Imports = @('Sanctions'),
    [int]$Threads = 3,
    # Optional: also save the raw FC- record stream (every reader of every field).
    [string]$RawFile = ''
)

$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
# Under `pwsh -File` an array parameter arrives as one comma-separated string
# (or spills into the positional list); accept commas in both lists.
function Split-List($xs) { @($xs | ForEach-Object { "$_" -split ',' } | ForEach-Object { $_.Trim() } | Where-Object { $_ -ne '' }) }
$Imports = Split-List $Imports
$Theorems = Split-List $Theorems
$openLine = 'open Sanctions Sanctions.Examples Sanctions.AbstractGame.Params Sanctions.AbstractGame.ShockedParams'

# --- 0. The headline table: fully-qualified name -> row number --------------
$snapPath = Join-Path $root 'HEADLINE-SNAPSHOT.md'
$rowOf = New-Object 'System.Collections.Generic.Dictionary[string,int]' ([System.StringComparer]::Ordinal)
$rowNames = @()
if (Test-Path $snapPath) {
    # Only the headline table: from its header to the first line that is not a
    # table row. Later sections (evidence declarations, contract roots, ...)
    # use the same row shape and must not be counted.
    $i = 0
    $inTable = $false
    foreach ($line in [System.IO.File]::ReadAllLines($snapPath, [System.Text.Encoding]::UTF8)) {
        if (-not $inTable) {
            if ($line -match '^\| Headline \(fully qualified\) \| Elaborated-type SHA256 \|') { $inTable = $true }
            continue
        }
        if ($line -notmatch '^\|') { break }
        $m = [regex]::Match($line, '^\| `(?<n>[^`]+)` \| `[0-9a-f]{64}` \|')
        if ($m.Success) {
            $i++
            $rowOf[$m.Groups['n'].Value] = $i
            $rowNames += $m.Groups['n'].Value
        }
    }
}
$defaultSet = $false
if (-not $Theorems -or $Theorems.Count -eq 0) {
    $defaultSet = $true
    $Theorems = @($rowNames | Where-Object {
        $_ -match '^Sanctions\.Examples\.ChordEconomy(Cs|Relief|TwoSided)?\.[^.]+$' })
    if ($Theorems.Count -eq 0) {
        Write-Host 'FAIL: no chord rows found in HEADLINE-SNAPSHOT.md and no names given.'
        exit 1
    }
}

# The R5 verifier's text-closure upper bounds (doc 110 R5, V.source_check (4),
# 2026-09-28): a comment-stripped, dot-tolerant name scan over the
# ChordEconomy/ChordEconomyCs namespaces, counted out of the 81 own fields the
# two structures had on that date (78 + 3, before the round-BC and BJ3.1
# splits), so a bound is not comparable term for term with today's class-field
# total. Reference data for the comparison column only, keyed by the theorem
# that was scanned under its current name (BJ3.1 moved two of them into
# ChordEconomyTwoSided). Row numbers are not kept here: they come from the
# headline table above. A name absent here prints '-', as does a headline row
# whose theorem has since replaced a scanned one (e.g.
# `ChordEconomy.target_only_regime_generalF_core`, `ChordEconomyCs.collapse_sides'`).
$textBound = @{
    'Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin'                 = 71
    'Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF' = 72
    'Sanctions.Examples.ChordEconomyTwoSided.target_only_regime_generalF'                  = 66
    'Sanctions.Examples.ChordEconomyCs.four_cell_generalF'                                 = 75
    'Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF'                        = 63
    'Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief'                     = 76
    'Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp'                      = 37
    'Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero'                  = 74
    'Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side'                  = 77
    'Sanctions.Examples.ChordEconomyCs.collapse_sides'                                     = 27
    'Sanctions.Examples.ChordEconomy.unique_equilibrium_of_monotone_class'                 = 46
    'Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone'            = 25
    'Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief'                = 52
    'Sanctions.Examples.ChordEconomyTwoSided.dynamicSanction_eq_of_sender_side_eq'         = 58
}

# --- 1. The probe ------------------------------------------------------------
# Inside the project, as the snapshot generator does: a source file under the
# system TEMP directory can trigger toolchain discovery from that path.
$tmp = Join-Path $root (".chord_field_census_{0}.lean" -f $PID)
$sb = New-Object System.Text.StringBuilder
foreach ($imp in $Imports) { [void]$sb.AppendLine("import $imp") }
[void]$sb.AppendLine($openLine)
[void]$sb.AppendLine((Get-Content (Join-Path $PSScriptRoot 'chord_field_census.lean.template') -Raw -Encoding UTF8))
[void]$sb.AppendLine('#chordFieldCensus ' + ($Theorems -join ' '))
[System.IO.File]::WriteAllText($tmp, $sb.ToString(), (New-Object System.Text.UTF8Encoding($false)))

# --- 2. Elaborate against the built library ----------------------------------
Push-Location $root
$prevOut = [Console]::OutputEncoding
$prevThreads = $env:LEAN_NUM_THREADS
try {
    [Console]::OutputEncoding = New-Object System.Text.UTF8Encoding($false)
    $env:LEAN_NUM_THREADS = "$Threads"
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $out = & lake env lean $tmp 2>&1 | ForEach-Object { "$_" }
    $leanExit = $LASTEXITCODE
    $sw.Stop()
    $leanVersion = (& lake env lean --version) -join ' '
    $commit = (& git -C $root rev-parse --short HEAD 2>$null)
    $dirty = (& git -C $root status --porcelain 2>$null | Measure-Object).Count
} finally {
    [Console]::OutputEncoding = $prevOut
    $env:LEAN_NUM_THREADS = $prevThreads
    Pop-Location
    Remove-Item $tmp -Force -ErrorAction SilentlyContinue
}
if ($RawFile -ne '') {
    $rawPath = if ([System.IO.Path]::IsPathRooted($RawFile)) { $RawFile } else { Join-Path $root $RawFile }
    [System.IO.File]::WriteAllText($rawPath, ($out -join "`n"), (New-Object System.Text.UTF8Encoding($false)))
}
if ($leanExit -ne 0) {
    Write-Host "FAIL: lake env lean exited $leanExit. Error lines first, then the full output:"
    Write-Host (@($out | Where-Object { $_ -match 'error' }) -join "`n")
    Write-Host '----'
    Write-Host ($out -join "`n")
    exit 1
}

# --- 3. Parse the FC- records ------------------------------------------------
# Not anchored at line start: Lean's messages can arrive merged onto one line
# (see Generate-HeadlineSnapshot.ps1), so split on the record tags themselves.
$text = $out -join "`n"
$recs = [regex]::Matches($text,
    'FC-(?<tag>STRUCT|SUBOBJ|BEGIN|CLOSURE|DIRECT|CLOSED|PROJONLY|COPYONLY|BULK|PATH|READERS|PULLED|END) ?(?<body>.*?)(?=FC-(?:STRUCT|SUBOBJ|BEGIN|CLOSURE|DIRECT|CLOSED|PROJONLY|COPYONLY|BULK|PATH|READERS|PULLED|END)\b|\n|$)')

$structFields = [ordered]@{}   # struct -> own field names, declaration order
$structSub = @{}               # struct -> parent projections
$rows = New-Object System.Collections.Generic.List[object]
$cur = $null
function Split-Names([string]$s) { @($s.Trim() -split '\s+' | Where-Object { $_ -ne '' }) }
foreach ($r in $recs) {
    $tag = $r.Groups['tag'].Value
    $body = $r.Groups['body'].Value.Trim()
    switch ($tag) {
        'STRUCT' {
            $m = [regex]::Match($body, '^(?<s>\S+) (?<k>\d+) ::(?<f>.*)$')
            $structFields[$m.Groups['s'].Value] = @(Split-Names $m.Groups['f'].Value)
        }
        'SUBOBJ' {
            $m = [regex]::Match($body, '^(?<s>\S+) ::(?<f>.*)$')
            $structSub[$m.Groups['s'].Value] = @(Split-Names $m.Groups['f'].Value)
        }
        'BEGIN' {
            $cur = [pscustomobject]@{
                Name = $body; ClosureDirect = 0; ClosureClosed = 0
                Direct = @(); Closed = @(); ProjOnly = @(); CopyOnly = @(); Bulk = @()
                Paths = (New-Object 'System.Collections.Generic.Dictionary[string,string]' ([System.StringComparer]::Ordinal))
                Pulled = (New-Object 'System.Collections.Generic.Dictionary[string,string]' ([System.StringComparer]::Ordinal))
                Readers = (New-Object 'System.Collections.Generic.Dictionary[string,string]' ([System.StringComparer]::Ordinal))
            }
        }
        'CLOSURE' { $p = Split-Names $body; $cur.ClosureDirect = [int]$p[0]; $cur.ClosureClosed = [int]$p[1] }
        'DIRECT'   { $cur.Direct = @(Split-Names $body) }
        'CLOSED'   { $cur.Closed = @(Split-Names $body) }
        'PROJONLY' { $cur.ProjOnly = @(Split-Names $body) }
        'COPYONLY' { $cur.CopyOnly = @(Split-Names $body) }
        'READERS' {
            $m = [regex]::Match($body, '^(?<f>\S+) :: (?<k>\d+) :: ?(?<p>.*)$')
            $cur.Readers[$m.Groups['f'].Value] = $m.Groups['k'].Value + ' :: ' + $m.Groups['p'].Value
        }
        'BULK'     { $cur.Bulk = @(Split-Names $body) }
        'PATH' {
            $m = [regex]::Match($body, '^(?<f>\S+) :: (?<p>.*)$')
            $cur.Paths[$m.Groups['f'].Value] = $m.Groups['p'].Value
        }
        'PULLED' {
            $m = [regex]::Match($body, '^(?<f>\S+) :: (?<p>.*)$')
            $cur.Pulled[$m.Groups['f'].Value] = $m.Groups['p'].Value
        }
        'END' { if ($cur -and $cur.Name -eq $body) { $rows.Add($cur) }; $cur = $null }
    }
}
$sP  = 'Sanctions.AbstractGame.Params'
$sC  = 'Sanctions.Examples.ChordEconomy'
$sT  = 'Sanctions.Examples.ChordEconomyTwoSided'
$sR  = 'Sanctions.Examples.ChordEconomyRelief'
$sCs = 'Sanctions.Examples.ChordEconomyCs'
# The chord structures, base first (each extends the one before), with their
# report labels. Every chord column, count and section below iterates this.
$chord = [ordered]@{
    $sC = 'ChordEconomy'; $sT = 'ChordEconomyTwoSided'
    $sR = 'ChordEconomyRelief'; $sCs = 'ChordEconomyCs'
}
foreach ($s in @($sP) + @($chord.Keys)) {
    if (-not $structFields.Contains($s)) { Write-Host "FAIL: no field list for $s."; exit 1 }
}
if ($rows.Count -ne $Theorems.Count) {
    Write-Host ("FAIL: parsed {0} census records, expected {1}." -f $rows.Count, $Theorems.Count)
    Write-Host $text
    exit 1
}

# Class fields: the own fields of each chord structure, base first, qualified.
$classFields = @()
foreach ($s in $chord.Keys) { foreach ($f in $structFields[$s]) { $classFields += "$s.$f" } }
$paramFields = @($structFields[$sP] | ForEach-Object { "$sP.$_" })
$nClass = $classFields.Count
$nParam = $paramFields.Count
function Short([string]$q) { ($q -split '\.')[-1] }
function Row-Label($r) { if ($rowOf.ContainsKey($r.Name)) { [string]$rowOf[$r.Name] } else { '-' } }
function Theorem-Label([string]$n) { $n -replace '^Sanctions\.Examples\.', '' -replace '^Sanctions\.', '' }

# --- 4. The report -----------------------------------------------------------
function Is-Ctor([string]$n) { $n -match '\.mk$' -or $n -match '\.mk\.' }
$md = New-Object System.Text.StringBuilder
[void]$md.AppendLine('# Chord-economy field census (compiler-derived)')
[void]$md.AppendLine()
[void]$md.AppendLine('Generated by `scripts/Chord-Field-Census.ps1` from `scripts/chord_field_census.lean.template`')
[void]$md.AppendLine('(round BB, 2026-09-28; doc 110 item R5 step 1). Regenerate with')
[void]$md.AppendLine('`pwsh -File scripts/Chord-Field-Census.ps1` after the library is built; the script never builds.')
[void]$md.AppendLine()
[void]$md.AppendLine("- Generated: $(Get-Date -Format 'yyyy-MM-dd HH:mm') from commit ``$commit`` ($dirty uncommitted paths in the working tree; the census reads the oleans on disk)")
[void]$md.AppendLine("- ``lake env lean --version``: ``$leanVersion``")
[void]$md.AppendLine("- Imports: $(($Imports | ForEach-Object { '`' + $_ + '`' }) -join ', '); elaboration $([math]::Round($sw.Elapsed.TotalSeconds)) s at LEAN_NUM_THREADS=$Threads")
$nsTxt = (@($chord.Values | ForEach-Object { '`' + $_ + '`' }) -join ' / ')
[void]$md.AppendLine("- Theorems: $(if ($defaultSet) { "the default set, every row of the ``HEADLINE-SNAPSHOT.md`` headline table in the $nsTxt namespaces ($($rows.Count) rows)" } else { "given on the command line ($($rows.Count))" })")
$ownTxt = @($chord.Keys | ForEach-Object { "$($structFields[$_].Count) of ``$($chord[$_])``" })
$ownTxt[0] = $ownTxt[0] -replace '^(\d+) of', '$1 own fields of'
[void]$md.AppendLine("- Censused: $($ownTxt -join ' + ') = $nClass class fields, and the $nParam fields of the inherited ``AbstractGame.Params``, counted separately")
[void]$md.AppendLine()
[void]$md.AppendLine('## What is measured')
[void]$md.AppendLine()
[void]$md.AppendLine('For each theorem the census walks, breadth-first, every constant of the `Sanctions` library reachable from')
[void]$md.AppendLine('the theorem through types **and** values (statement and proof), and records every field whose projection')
[void]$md.AppendLine('function, or a raw `Expr.proj` at its index, occurs in a visited constant. Two readings:')
[void]$md.AppendLine()
[void]$md.AppendLine('- **Direct**: projection functions are recorded and not expanded. A field is direct when some constant in the closure mentions it.')
[void]$md.AppendLine('- **Closed**: projection functions are also expanded through their types, so a field whose own statement mentions another field pulls that one in (for example `hUS_crossHi` mentions `rhi`). Closed is the smallest field set closed under the structures'' own dependency order: what a tier structure holding the theorem would have to contain. Closed-only fields are marked `°` below.')
[void]$md.AppendLine()
[void]$md.AppendLine('Scope. It is a constant-level census, not a data-flow one: a field counts when any constant in the closure mentions')
[void]$md.AppendLine('its projection. For the class fields the only objects in play are the theorem''s own economies (a theorem over two,')
[void]$md.AppendLine('such as `ChordEconomyCs.exists_defiance_equilibrium_mono_βT`, is censused as their union); for the `Params` fields')
[void]$md.AppendLine('it over-approximates wherever a lemma over an arbitrary `Params`')
[void]$md.AppendLine('is applied to a derived one. It is exact for the proofs as they stand and not minimal over all proofs: a lemma that')
[void]$md.AppendLine('proves more than the theorem needs still contributes every field its own proof reads. The `Params` counts are fields')
[void]$md.AppendLine('*read*, not fields a binder''s type presupposes: an equilibrium record `FeedbackStackelbergEquilibriumTop p` needs a')
[void]$md.AppendLine('whole `p : Params` to be stated, but only the fields some constant in the closure projects are counted.')
[void]$md.AppendLine()
[void]$md.AppendLine('Two kinds of whole-structure use are reported separately:')
[void]$md.AppendLine()
[void]$md.AppendLine('- An **eliminator** use of a censused structure (`casesOn`, `rec`, `recOn`, `noConfusion`) reads fields positionally,')
[void]$md.AppendLine('  invisible to a projection census. A row with an entry in the *Eliminators* column has a census that is a lower bound.')
[void]$md.AppendLine('- A **constructor** use (`mk`) builds a new instance, typically by a structure update `{ p with β_S := … }`, whose')
[void]$md.AppendLine('  elaborated form mentions every field it does not replace. A field every one of whose readers is such a builder')
[void]$md.AppendLine('  is marked `†` (**copy-only**): the closure shows it moved into a new instance and nowhere used. It is still counted,')
[void]$md.AppendLine('  since the closure cannot see whether the copy''s field is later read, but the *excl. †* columns leave it out.')
[void]$md.AppendLine()
[void]$md.AppendLine('The *text bound* column is the R5 verifier''s comment-stripped name-scan closure (doc 110 R5, V.source_check (4)),')
[void]$md.AppendLine('kept as reference data in the script.')
[void]$md.AppendLine()

# Per-row summary.
[void]$md.AppendLine('## Per row')
[void]$md.AppendLine()
[void]$md.AppendLine("| Row | Theorem | Class fields, closed (of $nClass) | Direct | Text bound | Params fields (of $nParam) | Params excl. † | Closure (constants) | Eliminators | Constructors |")
[void]$md.AppendLine('|---|---|---|---|---|---|---|---|---|---|')
foreach ($r in $rows) {
    $cc = @($r.Closed | Where-Object { $classFields -ccontains $_ }).Count
    $cd = @($r.Direct | Where-Object { $classFields -ccontains $_ }).Count
    $pc = @($r.Closed | Where-Object { $paramFields -ccontains $_ }).Count
    $pcx = @($r.Closed | Where-Object { ($paramFields -ccontains $_) -and ($r.CopyOnly -cnotcontains $_) }).Count
    $tb = if ($textBound.ContainsKey($r.Name)) { [string]$textBound[$r.Name] } else { '-' }
    $elim = @($r.Bulk | Where-Object { -not (Is-Ctor $_) })
    $ctor = @($r.Bulk | Where-Object { Is-Ctor $_ })
    $fmtB = { param($xs) if ($xs.Count -gt 0) { ($xs | ForEach-Object { '`' + (Theorem-Label $_) + '`' }) -join ', ' } else { 'none' } }
    [void]$md.AppendLine("| $(Row-Label $r) | ``$(Theorem-Label $r.Name)`` | $cc | $cd | $tb | $pc | $pcx | $($r.ClosureDirect) | $(& $fmtB $elim) | $(& $fmtB $ctor) |")
}
[void]$md.AppendLine()

# Per-row lists.
[void]$md.AppendLine('## Per row: the fields reached')
[void]$md.AppendLine()
[void]$md.AppendLine('Declaration order. `°` = closed only (needed to state a field the proof reads, not itself mentioned); `†` = copy-only.')
[void]$md.AppendLine()
$chordCols = (@($chord.Values | ForEach-Object { "``$_`` fields" }) -join ' | ')
[void]$md.AppendLine("| Row | Theorem | $chordCols | Class fields not reached | ``Params`` fields | ``Params`` fields not reached |")
[void]$md.AppendLine('|' + ('---|' * (5 + $chord.Count)))
foreach ($r in $rows) {
    $fmt = {
        param($q)
        $s = Short $q
        if ($r.Direct -cnotcontains $q) { $s += '°' }
        if ($r.CopyOnly -ccontains $q) { $s += '†' }
        $s
    }
    $j = { param($xs) if ($xs.Count -gt 0) { $xs -join ', ' } else { '-' } }
    # One cell per chord structure, its reached own fields in declaration order.
    $cells = @($chord.Keys | ForEach-Object {
        $s = $_
        & $j @($structFields[$s] | ForEach-Object { "$s.$_" } |
            Where-Object { $r.Closed -ccontains $_ } | ForEach-Object { & $fmt $_ })
    })
    $cno = @($classFields | Where-Object { $r.Closed -cnotcontains $_ } | ForEach-Object { Short $_ })
    $pp  = @($paramFields | Where-Object { $r.Closed -ccontains $_ } | ForEach-Object { & $fmt $_ })
    $pno = @($paramFields | Where-Object { $r.Closed -cnotcontains $_ } | ForEach-Object { Short $_ })
    [void]$md.AppendLine("| $(Row-Label $r) | ``$(Theorem-Label $r.Name)`` | $($cells -join ' | ') | $(& $j $cno) | $(& $j $pp) | $(& $j $pno) |")
}
[void]$md.AppendLine()

# Per-field table.
[void]$md.AppendLine('## Per field: the rows reaching it')
[void]$md.AppendLine()
[void]$md.AppendLine('Rows by headline number (a theorem outside the snapshot by its name). `°` = the row needs the field only through')
[void]$md.AppendLine('the closure (it states a field that mentions this one); `†` = copy-only for that row. A field reached by no')
[void]$md.AppendLine('censused theorem is listed with an empty row set.')
[void]$md.AppendLine()
[void]$md.AppendLine('| Structure | Field | Rows (closed) | Count | Count excl. † |')
[void]$md.AppendLine('|---|---|---|---|---|')
$unreached = @()
$unreachedX = @()
foreach ($s in @($chord.Keys) + @($sP)) {
    $label = if ($s -ceq $sP) { 'Params' } else { $chord[$s] }
    foreach ($f in $structFields[$s]) {
        $q = "$s.$f"
        $hits = @()
        $real = 0
        foreach ($r in $rows) {
            if ($r.Closed -ccontains $q) {
                $lab = if ($rowOf.ContainsKey($r.Name)) { [string]$rowOf[$r.Name] } else { Theorem-Label $r.Name }
                if ($r.Direct -cnotcontains $q) { $lab += '°' }
                if ($r.CopyOnly -ccontains $q) { $lab += '†' } else { $real++ }
                $hits += $lab
            }
        }
        if ($hits.Count -eq 0) { $unreached += "``$label.$f``" }
        elseif ($real -eq 0) { $unreachedX += "``$label.$f``" }
        $hs = if ($hits.Count -gt 0) { $hits -join ', ' } else { '(none)' }
        [void]$md.AppendLine("| ``$label`` | ``$f`` | $hs | $($hits.Count) | $real |")
    }
}
[void]$md.AppendLine()
[void]$md.AppendLine("Fields reached by none of the $($rows.Count) censused theorems: $(if ($unreached.Count -gt 0) { $unreached -join ', ' } else { 'none' }).")
[void]$md.AppendLine()
[void]$md.AppendLine("Fields reached, but copy-only in every theorem that reaches them: $(if ($unreachedX.Count -gt 0) { $unreachedX -join ', ' } else { 'none' }).")
[void]$md.AppendLine()

# Diagnostics.
[void]$md.AppendLine('## Diagnostics')
[void]$md.AppendLine()
[void]$md.AppendLine('- Copy-only fields per row, with their readers:')
foreach ($r in $rows) {
    $co = @($r.CopyOnly)
    if ($co.Count -eq 0) {
        [void]$md.AppendLine("  - row $(Row-Label $r) ``$(Theorem-Label $r.Name)``: none")
    } else {
        $rd = @($co | ForEach-Object { if ($r.Readers.ContainsKey($_)) { ($r.Readers[$_] -split ' :: ', 2)[1] } } |
            ForEach-Object { $_ -split ' ' } | Where-Object { $_ -ne '' } | Sort-Object -Unique -CaseSensitive |
            ForEach-Object { '`' + (Theorem-Label ($_ -replace '^Sanctions\.AbstractGame\.', '')) + '`' })
        [void]$md.AppendLine("  - row $(Row-Label $r) ``$(Theorem-Label $r.Name)``: $(($co | ForEach-Object { '`' + (Short $_) + '`' }) -join ', ') (read by $($rd -join ', '))")
    }
}
[void]$md.AppendLine('- Fields reached only through a raw `Expr.proj` (never a projection-function constant), which a `getUsedConstants`-based walk would have missed:')
foreach ($r in $rows) {
    $po = @($r.ProjOnly)
    [void]$md.AppendLine("  - row $(Row-Label $r) ``$(Theorem-Label $r.Name)``: $(if ($po.Count -gt 0) { ($po | ForEach-Object { '`' + (Short $_) + '`' }) -join ', ' } else { 'none' })")
}
# The parent projections, as the FC-SUBOBJ records list them, base first.
$subTxt = @(@($sP) + @($chord.Keys) | ForEach-Object { if ($structSub.ContainsKey($_)) { $structSub[$_] } } |
    Select-Object -Unique | ForEach-Object { '`' + $_ + '`' }) -join ', '
[void]$md.AppendLine("- Parent projections reached ($subTxt) are not counted as fields.")
[void]$md.AppendLine()

# Citation paths.
[void]$md.AppendLine('## Citation paths')
[void]$md.AppendLine()
[void]$md.AppendLine('For each direct field, one shortest chain of constants from the theorem to the first constant whose type or value')
[void]$md.AppendLine('reads it (`Sanctions.` prefixes dropped), and how many constants in the closure read it (the first few are named')
[void]$md.AppendLine('when there are at most three). For each closed-only field, the constant whose statement pulls it in.')
[void]$md.AppendLine()
function Trim-Names([string]$s) { $s -replace 'Sanctions\.Examples\.', '' -replace 'Sanctions\.AbstractGame\.', '' -replace '(?<![\w.])Sanctions\.', '' }
foreach ($r in $rows) {
    [void]$md.AppendLine("<details><summary>Row $(Row-Label $r): <code>$(Theorem-Label $r.Name)</code></summary>")
    [void]$md.AppendLine()
    foreach ($q in @($classFields + $paramFields)) {
        if ($r.Paths.ContainsKey($q)) {
            $p = Trim-Names $r.Paths[$q]
            $rdTxt = ''
            if ($r.Readers.ContainsKey($q)) {
                $parts = $r.Readers[$q] -split ' :: ', 2
                $k = [int]$parts[0]
                $rdTxt = if ($k -le 3) { " ($k reader$(if ($k -ne 1) { 's' }): $((@($parts[1] -split ' ' | Where-Object { $_ -ne '' } | ForEach-Object { Trim-Names $_ })) -join ', '))" } else { " ($k readers)" }
            }
            $mark = if ($r.CopyOnly -ccontains $q) { '†' } else { '' }
            [void]$md.AppendLine("- ``$(Short $q)``${mark}: $p$rdTxt")
        } elseif ($r.Pulled.ContainsKey($q)) {
            [void]$md.AppendLine("- ``$(Short $q)``°: via ``$(Trim-Names $r.Pulled[$q])``")
        }
    }
    [void]$md.AppendLine()
    [void]$md.AppendLine('</details>')
    [void]$md.AppendLine()
}

$outPath = if ([System.IO.Path]::IsPathRooted($OutFile)) { $OutFile } else { Join-Path $root $OutFile }
$outDir = Split-Path -Parent $outPath
if (-not (Test-Path $outDir)) { New-Item -ItemType Directory -Path $outDir | Out-Null }
[System.IO.File]::WriteAllText($outPath, $md.ToString(), (New-Object System.Text.UTF8Encoding($false)))
Write-Host ("Wrote {0}: {1} theorems, {2} class fields, {3} Params fields." -f $OutFile, $rows.Count, $nClass, $nParam)
exit 0
