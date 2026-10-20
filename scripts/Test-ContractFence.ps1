# Test-ContractFence.ps1 -- probe contract roots against the current build and
# compare their records with the committed HEADLINE-SNAPSHOT.md.
#
# Purpose (doc 68 L9; doc 70 F-1/F-2/F-5): the mutation test for the
# contract-root fence. Mutate a structure or a predicate in a scratch state
# (a worktree, never main), rebuild only its module, run this script, and
# read CHANGED / NEW / DELETED per record. The extractor is the SAME file the
# production generator splices in (scripts/contract_probe.lean.template), with
# the same fixed rendering options, so a record that matches here matches
# there.
#
# Modes
#   check (default): exit 0 only if the requested roots' records are exactly
#     the committed ones; any CHANGED, NEW or DELETED record exits 1.
#   expected mutation: pass -ExpectChanged / -ExpectNew / -ExpectDeleted
#     (arrays of record names, fully qualified) and the script exits 0 only if
#     the observed difference is exactly the expected one.
# Zero records, a probe failure, or an unresolvable root always exit 1.
#
#   pwsh -File scripts/Test-ContractFence.ps1 -Module Sanctions.Examples.PlacableSenderFamilyF `
#        -Roots Sanctions.Examples.PlacableEconomyF,Sanctions.Examples.PlacableEconomyFcs
#   pwsh -File scripts/Test-ContractFence.ps1 ... -ExpectChanged Sanctions.Examples.PlacableEconomyFcs.mk `
#        -ExpectNew Sanctions.Examples.PlacableEconomyFcs.hq1
param(
    [string]$Module = 'Sanctions.Examples.PlacableSenderFamilyF',
    [string[]]$Roots = @('Sanctions.Examples.PlacableEconomyF', 'Sanctions.Examples.PlacableEconomyFcs'),
    [string]$Snapshot = 'HEADLINE-SNAPSHOT.md',
    [string[]]$ExpectChanged = @(),
    [string[]]$ExpectNew = @(),
    [string[]]$ExpectDeleted = @(),
    [switch]$NoBuild
)
$ErrorActionPreference = 'Stop'
# `pwsh -File` hands a comma-joined argument to a [string[]] parameter as ONE
# element; split so both invocation styles work. Roots must be fully qualified.
$Roots = @($Roots | ForEach-Object { $_ -split ',' } | Where-Object { $_ -ne '' })
$ExpectChanged = @($ExpectChanged | ForEach-Object { $_ -split ',' } | Where-Object { $_ -ne '' })
$ExpectNew = @($ExpectNew | ForEach-Object { $_ -split ',' } | Where-Object { $_ -ne '' })
$ExpectDeleted = @($ExpectDeleted | ForEach-Object { $_ -split ',' } | Where-Object { $_ -ne '' })
$root = Split-Path -Parent $PSScriptRoot
Push-Location $root
try {
    if (-not $NoBuild) {
        & lake build $Module | Out-Null
        if ($LASTEXITCODE -ne 0) { throw "lake build $Module failed" }
    }
    $tmp = Join-Path $root ('tmp\_fence_probe_' + [guid]::NewGuid().ToString('N') + '.lean')
    $template = Get-Content (Join-Path $PSScriptRoot 'contract_probe.lean.template') -Raw
    $probe = @"
import $Module
open Lean Elab Command Meta
$template
#contractRoots $($Roots -join ' ')
"@
    New-Item -ItemType Directory -Force (Split-Path $tmp) | Out-Null
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
    if ($leanExit -ne 0) { Write-Host ($out -join "`n"); throw 'probe failed (a root or projection did not resolve)' }
    $sha = [System.Security.Cryptography.SHA256]::Create()
    $rows = @{}
    $cur = $null; $buf = New-Object System.Collections.Generic.List[string]
    foreach ($line in @($out)) {
        if ($line -match '^CONTRACT-BEGIN\s+(?<n>\S+)\s*$') { $cur = $Matches['n']; $buf.Clear(); continue }
        if ($line -match '^CONTRACT-END\s*$') {
            if ($cur) {
                $text = (($buf -join ' ') -replace '\s+', ' ').Trim()
                $b = [System.Text.Encoding]::UTF8.GetBytes($text)
                $rows[$cur] = ([System.BitConverter]::ToString($sha.ComputeHash($b)) -replace '-', '').ToLowerInvariant()
                $cur = $null; $buf.Clear()
            }
            continue
        }
        if ($cur) { [void]$buf.Add($line) }
    }
    if ($cur) { throw 'probe output truncated (a record began without ending)' }
    if ($rows.Count -eq 0) { throw 'zero contract records (probe broken?)' }
    # The committed records that belong to the requested roots: the root, its
    # constructor and its projections all carry the root name as a prefix.
    $committed = @{}
    $inContract = $false
    foreach ($l in Get-Content (Join-Path $root $Snapshot)) {
        if ($l -match '^##\s+Contract roots') { $inContract = $true; continue }
        if ($l -match '^##\s+') { $inContract = $false; continue }
        if ($inContract -and $l -match '^\| `(?<n>[^`]+)` \| `(?<h>[0-9a-f]{64})` \|$') {
            $n = $Matches['n']
            foreach ($r in $Roots) {
                if ($n -eq $r -or $n.StartsWith($r + '.')) { $committed[$n] = $Matches['h']; break }
            }
        }
    }
    $changed = @(); $new = @(); $deleted = @()
    $allKeys = @($rows.Keys + $committed.Keys | Sort-Object -Unique)
    foreach ($k in $allKeys) {
        if ($rows.ContainsKey($k) -and -not $committed.ContainsKey($k)) { Write-Host ("NEW       {0}" -f $k); $new += $k; continue }
        if (-not $rows.ContainsKey($k) -and $committed.ContainsKey($k)) { Write-Host ("DELETED   {0}" -f $k); $deleted += $k; continue }
        if ($committed[$k] -eq $rows[$k]) { Write-Host ("UNCHANGED {0}" -f $k) }
        else { Write-Host ("CHANGED   {0}" -f $k); $changed += $k }
    }
    Write-Host ("summary: {0} records probed, {1} committed for these roots; {2} changed, {3} new, {4} deleted" -f $rows.Count, $committed.Count, $changed.Count, $new.Count, $deleted.Count)
    $expectMode = ($ExpectChanged.Count + $ExpectNew.Count + $ExpectDeleted.Count) -gt 0
    if ($expectMode) {
        $ok = $true
        foreach ($pair in @(@('changed', $changed, $ExpectChanged), @('new', $new, $ExpectNew), @('deleted', $deleted, $ExpectDeleted))) {
            $obs = @($pair[1] | Sort-Object); $exp = @($pair[2] | Sort-Object)
            if (($obs -join ';') -ne ($exp -join ';')) {
                Write-Host ("MISMATCH ({0}): observed [{1}] expected [{2}]" -f $pair[0], ($obs -join ', '), ($exp -join ', '))
                $ok = $false
            }
        }
        if ($ok) { Write-Host 'EXPECTED MUTATION OBSERVED.'; exit 0 } else { Write-Host 'MUTATION TEST FAILED.'; exit 1 }
    } else {
        if ($changed.Count + $new.Count + $deleted.Count -eq 0) { Write-Host 'FENCE INTACT.'; exit 0 }
        Write-Host 'FENCE DIFFERS FROM THE COMMITTED SNAPSHOT.'; exit 1
    }
} finally {
    Pop-Location
}
