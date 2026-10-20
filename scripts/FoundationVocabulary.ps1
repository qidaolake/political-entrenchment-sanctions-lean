<#
  Shared vocabulary helpers for the Foundations purity checks.

  Sourced by Generate-FoundationRoles.ps1 and by gate 2 of Audit-Round.ps1, so
  the manifest and the gate can never disagree about what counts as a leak.
#>

<#
.SYNOPSIS
  Lean source with comments removed, in the ONLY safe order.

.DESCRIPTION
  Block comments FIRST, then line comments. The reverse order is a real bug and
  has bitten this project: `--` stripping turns `/-- **Foo** ...` into `/`,
  destroying the block opener, after which doc prose survives into the
  "code" and is scanned for vocabulary. On 2026-08-27 that reported four
  Foundations files as mentioning `Params` when every hit was prose explaining
  that they do not.

  Nested block comments are handled by repeated non-greedy passes; Lean's `/-`
  nests, and a single regex does not.
#>
function Get-StrippedLeanSource {
    param([Parameter(Mandatory)][string] $Path)
    $src = Get-Content -Path $Path -Raw
    if ($null -eq $src) { return '' }
    for ($i = 0; $i -lt 8; $i++) {
        $next = [regex]::Replace($src, '/-(?:(?!/-|-/).)*?-/', ' ', 'Singleline')
        if ($next -eq $src) { break }
        $src = $next
    }
    return [regex]::Replace($src, '--.*?$', ' ', 'Multiline')
}

# The project's own state space. Present in Foundations statements by design:
# reusable operator theory specialized to [0,1]. Tracked, not forbidden.
$script:DomainTokens = @('Sanctions\.I\b', 'Sanctions\.S\b', '\bclipS''?\b')

# The game surface. Rule 19 forbids these in Foundations outright.
$script:GameTokens = @('\bAbstractGame\b', '\bParams\b', '\baffineF\b')

function Test-TokenMatch {
    param([string] $Statement, [string[]] $Tokens)
    foreach ($t in $Tokens) { if ($Statement -match $t) { return $t } }
    return $null
}

function Get-DeclarationRole {
    param([string] $Statement)
    if (Test-TokenMatch -Statement $Statement -Tokens $script:GameTokens)   { return 'GAME_LEAK' }
    if (Test-TokenMatch -Statement $Statement -Tokens $script:DomainTokens) { return 'DOMAIN_LEAK' }
    return 'CORE'
}

function Get-RoleReason {
    param([string] $Statement, [string] $Role)
    switch ($Role) {
        'GAME_LEAK'   { 'statement names ' + (Test-TokenMatch -Statement $Statement -Tokens $script:GameTokens) + ' (Rule 19)' }
        'DOMAIN_LEAK' { 'statement is over the project state space (' + (Test-TokenMatch -Statement $Statement -Tokens $script:DomainTokens) + '); expected, see Sanctions/Domain.lean' }
        default       { 'reusable mathematics over abstract objects' }
    }
}
