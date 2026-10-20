# Test-StructuralFingerprint.ps1 -- self-test of the structural fingerprint
# (round O, doc 82 P5 / the reader's T8) and of the gate-5 comparison it keys.
#
# Part 1 splices scripts/contract_probe.lean.template (the ONE extractor the
# generator uses) above scripts/structural_fingerprint_fixture.lean, runs it,
# and checks the digest invariants: a binder rename, a universe rename and a
# proof refactor inside a statement leave the digest unchanged; a changed
# hypothesis or binder info moves it. Part 2 feeds synthetic snapshots to
# Compare-HeadlineSnapshot (scripts/Compare-Snapshot.ps1, dot-sourced by
# Audit-Round.ps1 gate 5) and checks the three verdicts. Exit 0 only if every
# expectation holds. Gate 5 runs this before regenerating the snapshot.
#
#   pwsh -NoProfile -File scripts/Test-StructuralFingerprint.ps1
param([switch]$NoLean)
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
. (Join-Path $PSScriptRoot 'Compare-Snapshot.ps1')
$script:fails = 0
function Check([bool]$ok, [string]$what) {
    if ($ok) { Write-Host "  ok   $what" } else { Write-Host "  FAIL $what"; $script:fails++ }
}

# --- 1. the digest invariants on the fixture --------------------------------
if (-not $NoLean) {
    Push-Location $root
    try {
        $template = Get-Content (Join-Path $PSScriptRoot 'contract_probe.lean.template') -Raw
        $fixture = Get-Content (Join-Path $PSScriptRoot 'structural_fingerprint_fixture.lean') -Raw
        $probe = "import Lean`nopen Lean Elab Command Meta`n" + $template + "`n" + $fixture
        # Inside the project, like the generator's probe (an external TEMP path
        # can trigger toolchain discovery and a network lookup).
        $tmp = Join-Path $root (".struct_selftest_{0}.lean" -f $PID)
        [System.IO.File]::WriteAllText($tmp, $probe, (New-Object System.Text.UTF8Encoding($false)))
        $prevOut = [Console]::OutputEncoding
        try {
            [Console]::OutputEncoding = New-Object System.Text.UTF8Encoding($false)
            $out = & lake env lean $tmp
            $leanExit = $LASTEXITCODE
        } finally {
            [Console]::OutputEncoding = $prevOut
            Remove-Item $tmp -Force -ErrorAction SilentlyContinue
        }
        if ($leanExit -ne 0) {
            Write-Host ($out -join "`n")
            Write-Host "FAIL: lake env lean exited $leanExit on the fixture probe"
            exit 1
        }
        $recs = @{}; $cur = $null; $buf = $null
        foreach ($line in @($out)) {
            if ($line -match '^STRUCT-BEGIN\s+(?<n>\S+)\s*$') {
                $cur = $Matches['n']; $buf = New-Object System.Collections.Generic.List[string]; continue
            }
            if ($line -match '^STRUCT-END\s*$') {
                if ($null -ne $cur) { $recs[$cur] = (($buf -join ' ') -replace '\s+', ' ').Trim() }
                $cur = $null; continue
            }
            if ($null -ne $cur) { [void]$buf.Add($line) }
        }
        Check ($recs.Count -eq 10) ("10 fixture records parsed ({0})" -f $recs.Count)
        $expect = @(
            @('fxA', 'fxB', $true,  'alpha twins share the digest'),
            @('fxA', 'fxC', $false, 'a changed hypothesis moves the digest'),
            @('fxA', 'fxD', $false, 'a changed binder info moves the digest'),
            @('fxE', 'fxF', $true,  'a proof term inside a statement is elided'),
            @('fxG', 'fxH', $true,  'a renamed universe parameter is invariant'),
            @('fxI', 'fxJ', $true,  'a lambda under a binder is alpha-invariant'))
        foreach ($e in $expect) {
            $have = ($null -ne $recs[$e[0]]) -and ($null -ne $recs[$e[1]])
            $same = $have -and ($recs[$e[0]] -eq $recs[$e[1]])
            Check ($have -and ($same -eq $e[2])) $e[3]
        }
    } finally { Pop-Location }
}

# --- 2. the gate-5 comparison on synthetic snapshots --------------------------
$h1 = 'a' * 64; $h2 = 'b' * 64; $s1 = 'c' * 64; $s2 = 'd' * 64
$head = "# Headline snapshot`n`n| Headline (fully qualified) | Elaborated-type SHA256 | Structural SHA256 | Axioms |`n|---|---|---|---|`n"
$row = { param($n, $p, $s) ('| `{0}` | `{1}` | `{2}` | propext, Classical.choice, Quot.sound |' -f $n, $p, $s) }
$tail = "`n`n## Pinned economy data`n`n| Pinned constant | Value SHA256 |`n|---|---|`n| ``E.q`` | ``$h1`` |`n"
$base       = $head + (& $row 'T.one' $h1 $s1) + "`n" + (& $row 'T.two' $h1 $s1) + $tail
$rendering  = $head + (& $row 'T.one' $h2 $s1) + "`n" + (& $row 'T.two' $h1 $s1) + $tail
$structural = $head + (& $row 'T.one' $h1 $s2) + "`n" + (& $row 'T.two' $h1 $s1) + $tail
$renamed    = $head + (& $row 'T.uno' $h1 $s1) + "`n" + (& $row 'T.two' $h1 $s1) + $tail
$removed    = $head + (& $row 'T.one' $h1 $s1) + $tail
$both       = $head + (& $row 'T.one' $h2 $s1) + "`n" + (& $row 'T.two' $h1 $s2) + $tail
$axioms = $base.Replace((& $row 'T.two' $h1 $s1), ('| `T.two` | `{0}` | `{1}` | propext, sorryAx |' -f $h1, $s1))
$pinned = $base.Replace("| ``E.q`` | ``$h1`` |", "| ``E.q`` | ``$h2`` |")
$crlf = $base.Replace("`n", "`r`n")
Check ((Compare-HeadlineSnapshot $base $base).Verdict -eq 'stable') 'identical files: stable'
Check ((Compare-HeadlineSnapshot $base $crlf).Verdict -eq 'stable') 'line endings only: stable'
$r = Compare-HeadlineSnapshot $base $rendering
Check (($r.Verdict -eq 'rendering') -and (($r.Moved -join ',') -eq 'T.one')) 'printed hash moved, fingerprint kept: rendering, naming T.one'
Check ((Compare-HeadlineSnapshot $base $structural).Verdict -eq 'drift') 'structural fingerprint moved: drift'
Check ((Compare-HeadlineSnapshot $base $renamed).Verdict -eq 'drift') 'headline renamed: drift'
Check ((Compare-HeadlineSnapshot $base $removed).Verdict -eq 'drift') 'headline row removed: drift'
Check ((Compare-HeadlineSnapshot $base $axioms).Verdict -eq 'drift') 'axiom set moved: drift'
Check ((Compare-HeadlineSnapshot $base $pinned).Verdict -eq 'drift') 'pinned data moved, printed hashes kept: drift'
$r2 = Compare-HeadlineSnapshot $base $both
Check (($r2.Verdict -eq 'drift') -and (($r2.Moved -join ',') -eq 'T.one')) 'rendering on one row and a moved fingerprint on another: drift'
# The recorded `lake env lean --version` line is compared modulo the host
# platform triple (Rule 26: the gate runs on Windows and on the Linux HPC node).
$ver = { param($v, $plat, $c) ("- ``lake env lean --version``: ``Lean (version {0}, {1}, commit {2}, Release)```n`n" -f $v, $plat, $c) }
$cA = 'f' * 40; $cB = 'e' * 40
$winBase   = $head.Replace("`n`n|", ("`n`n" + (& $ver '4.29.1' 'x86_64-w64-windows-gnu' $cA) + '|')) + (& $row 'T.one' $h1 $s1) + $tail
$linux     = $winBase.Replace('x86_64-w64-windows-gnu', 'x86_64-unknown-linux-gnu')
$newLean   = $winBase.Replace('version 4.29.1', 'version 4.30.0')
$newCommit = $winBase.Replace($cA, $cB)
Check ((Compare-HeadlineSnapshot $winBase $linux).Verdict -eq 'stable') 'host platform triple only: stable'
Check ((Compare-HeadlineSnapshot $winBase $newLean).Verdict -eq 'drift') 'Lean version moved: drift'
Check ((Compare-HeadlineSnapshot $winBase $newCommit).Verdict -eq 'drift') 'Lean commit moved: drift'

if ($script:fails -gt 0) { Write-Host ("FAIL: {0} check(s) failed" -f $script:fails); exit 1 }
if ($NoLean) { Write-Host 'OK: structural fingerprint self-test (12 comparison cases; digest invariants skipped: -NoLean)' }
else { Write-Host 'OK: structural fingerprint self-test (6 digest invariants on 10 fixture records; 12 comparison cases)' }
exit 0
