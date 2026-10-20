<#
.SYNOPSIS
  Regenerate docs/FOUNDATION-DECLARATION-ROLES.csv from the source tree.

.DESCRIPTION
  One row per top-level declaration in Sanctions/Foundations/, with the role it
  plays. The point of the manifest is a single checkable claim:

      every declaration reachable from the Sanctions.Foundations aggregator
      is CORE -- reusable mathematics, not a witness for it.

  Roles are assigned by evidence, not by guesswork:

    DOMAIN_LEAK  the declaration's STATEMENT mentions the project's state space
                 (Sanctions.I / Sanctions.S / clipS). Real, and currently
                 expected: twelve Foundations modules are stated over [0,1].
    GAME_LEAK    the statement mentions Params / AbstractGame / affineF. This
                 is a Rule 19 violation and the count must stay at zero.
    CORE         everything else.

  Comment stripping is ORDER-SENSITIVE and the order here is load-bearing:
  block comments must go BEFORE line comments. Stripping `--` first
  decapitates every `/-- ` doc-comment opener, after which the block stripper
  cannot find the region and doc prose is scanned as if it were code. That
  produced four phantom Rule-19 violations on 2026-08-27 -- every hit was prose
  explaining the Foundations/Theory split, several of them saying "no Params
  here". The gate in Audit-Round.ps1 shares this helper for that reason.
#>
[CmdletBinding()]
param(
    [string] $Root,
    [string] $OutFile
)
$ErrorActionPreference = 'Stop'
# $PSScriptRoot is not reliably bound inside a param() default under -File on
# Windows PowerShell 5.1, so resolve it in the body instead.
if (-not $Root) { $Root = Split-Path -Parent $PSScriptRoot }
if (-not $OutFile) {
    $OutFile = Join-Path $Root 'docs/FOUNDATION-DECLARATION-ROLES.csv'
}

. (Join-Path $PSScriptRoot 'FoundationVocabulary.ps1')

$rows = @()
Get-ChildItem -Path (Join-Path $Root 'Sanctions/Foundations') -Recurse -Filter '*.lean' |
    Sort-Object FullName | ForEach-Object {
        # .Replace is a literal string method, not -replace's regex: a lone
        # backslash needs no escaping, and cannot be eaten in transit.
        $rel  = $_.FullName.Substring((Join-Path $Root '').Length).Replace([char]92, [char]47)
        $mod  = ($rel -replace '\.lean$','') -replace '/','.'
        $body = Get-StrippedLeanSource -Path $_.FullName
        foreach ($m in [regex]::Matches($body,
                '(?m)^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev|structure|instance|class|inductive|opaque)\s+([A-Za-z_][A-Za-z_0-9''!?\.]*)')) {
            $name = $m.Groups[2].Value
            # the declaration's own statement: up to ':=' or end of the block
            $tail = $body.Substring($m.Index)
            $stop = $tail.IndexOf(':=')
            $stmt = if ($stop -gt 0) { $tail.Substring(0, $stop) } else { $tail.Substring(0, [Math]::Min(600, $tail.Length)) }
            $role = Get-DeclarationRole -Statement $stmt
            $rows += [pscustomobject]@{
                declaration = $name
                module      = $mod
                role        = $role
                destination = if ($role -eq 'GAME_LEAK') { 'Theory' } else { '' }
                reason      = Get-RoleReason -Statement $stmt -Role $role
                status      = if ($role -eq 'GAME_LEAK') { 'ACTION REQUIRED' } else { 'accepted' }
            }
        }
    }

$rows | Export-Csv -Path $OutFile -NoTypeInformation -Encoding utf8
$byRole = $rows | Group-Object role | Sort-Object Name
Write-Host ("wrote {0}: {1} declarations" -f $OutFile, $rows.Count)
foreach ($g in $byRole) { Write-Host ("  {0,-12} {1}" -f $g.Name, $g.Count) }
