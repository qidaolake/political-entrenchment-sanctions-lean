# Compare-Snapshot.ps1 -- the gate-5 comparison of HEADLINE-SNAPSHOT.md
# (round O, doc 82 P5 / T8). Dot-sourced by scripts/Audit-Round.ps1 and by
# scripts/Test-StructuralFingerprint.ps1, so the gate and its self-test cannot
# drift apart.
#
# Compare-HeadlineSnapshot $before $after returns an object with
#   Verdict  'stable'    -- the two files are identical (line endings aside);
#            'rendering' -- they differ ONLY in the printed (elaborated-type)
#                           hash of headline rows whose structural fingerprint
#                           is unchanged: information, not drift;
#            'drift'     -- anything else: a headline row added, removed or
#                           renamed, a structural fingerprint or axiom set
#                           moved, or any change outside the headline table
#                           (header, pinned data, contract or evidence rows);
#   Moved    the headline names whose printed hash moved (both verdicts).
#
# One header field is compared modulo the host: the platform triple inside the
# recorded `lake env lean --version` line (x86_64-w64-windows-gnu on the
# development machine, x86_64-unknown-linux-gnu on the HPC node, CLAUDE.md
# Rule 26). The Lean version and its commit are still compared; a change of
# either is drift. Without this the gate fails on every Linux run for a reason
# that says nothing about the theorems (2026-10-01, round BD).
function Compare-HeadlineSnapshot([string]$Before, [string]$After) {
    $b = $Before.Replace("`r`n", "`n")
    $a = $After.Replace("`r`n", "`n")
    if ($b -eq $a) { return [pscustomobject]@{ Verdict = 'stable'; Moved = @() } }
    # A headline row carries four cells: name, printed hash, structural hash, axioms.
    $rowRx = '^\|\s*`(?<n>[^`]+)`\s*\|\s*`(?<p>[0-9a-f]{64})`\s*\|\s*`(?<s>[0-9a-f]{64})`\s*\|(?<ax>.*)$'
    $versionRx = '^(?<pre>- `lake env lean --version`: `Lean \(version [^,]+, )[^,]+(?<post>, commit [0-9a-f]+, [^)]*\)`)$'
    $normalise = {
        param([string]$text)
        $printed = @{}
        $out = New-Object System.Collections.Generic.List[string]
        $inHead = $true
        foreach ($line in $text.Split("`n")) {
            if ($line -match '^##\s+Pinned economy data') { $inHead = $false }
            if ($inHead -and $line -match $rowRx) {
                $printed[$Matches['n']] = $Matches['p']
                [void]$out.Add(('| `{0}` | `PRINTED` | `{1}` |{2}' -f $Matches['n'], $Matches['s'], $Matches['ax']))
            } elseif ($inHead -and $line -match $versionRx) {
                [void]$out.Add(('{0}PLATFORM{1}' -f $Matches['pre'], $Matches['post']))
            } else {
                [void]$out.Add($line)
            }
        }
        return @{ Text = ($out -join "`n"); Printed = $printed }
    }
    $nb = & $normalise $b
    $na = & $normalise $a
    $moved = @()
    foreach ($k in $nb.Printed.Keys) {
        if ($na.Printed.ContainsKey($k) -and $na.Printed[$k] -ne $nb.Printed[$k]) { $moved += $k }
    }
    $moved = @($moved | Sort-Object)
    if ($nb.Text -eq $na.Text) {
        # Equal after normalising, with no printed hash moved: only the host
        # platform triple differed, which is not a change to the snapshot.
        if ($moved.Count -eq 0) { return [pscustomobject]@{ Verdict = 'stable'; Moved = @() } }
        return [pscustomobject]@{ Verdict = 'rendering'; Moved = $moved }
    }
    return [pscustomobject]@{ Verdict = 'drift'; Moved = $moved }
}
