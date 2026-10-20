[CmdletBinding()]
param(
    [string]$OutputPath,
    [switch]$Force
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$projectRoot = [System.IO.Path]::GetFullPath((Split-Path -Parent $PSScriptRoot))
if ([string]::IsNullOrWhiteSpace($OutputPath)) {
    $OutputPath = Join-Path $projectRoot 'SanctionPublicChoiceLean.zip'
}
$outputFullPath = [System.IO.Path]::GetFullPath($OutputPath)
$outputDirectory = Split-Path -Parent $outputFullPath
$partialPath = "$outputFullPath.partial"
$checksumPath = "$outputFullPath.sha256"
$archiveRoot = 'SanctionPublicChoiceLean'

if (-not (Test-Path -LiteralPath $outputDirectory -PathType Container)) {
    throw "Output directory does not exist: $outputDirectory"
}
if ((Test-Path -LiteralPath $outputFullPath) -and -not $Force) {
    throw "Archive already exists. Re-run with -Force to replace it: $outputFullPath"
}

$excludedTopLevel = @(
    '.lake',
    '.codegraph',
    'tmp',
    'dist',
    'backups'
)
$excludedNames = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::OrdinalIgnoreCase
)
foreach ($name in $excludedTopLevel) {
    [void]$excludedNames.Add($name)
}
[void]$excludedNames.Add((Split-Path -Leaf $outputFullPath))
[void]$excludedNames.Add((Split-Path -Leaf $partialPath))
[void]$excludedNames.Add((Split-Path -Leaf $checksumPath))

if (Test-Path -LiteralPath $partialPath) {
    Remove-Item -LiteralPath $partialPath -Force
}

$topLevelItems = @(
    Get-ChildItem -LiteralPath $projectRoot -Force |
        Where-Object { -not $excludedNames.Contains($_.Name) } |
        Sort-Object Name
)

$allItems = [System.Collections.Generic.List[System.IO.FileSystemInfo]]::new()
foreach ($topLevelItem in $topLevelItems) {
    if (($topLevelItem.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0) {
        throw "Refusing to archive a top-level reparse point: $($topLevelItem.FullName)"
    }
    $allItems.Add($topLevelItem)
    if ($topLevelItem.PSIsContainer) {
        foreach ($child in Get-ChildItem -LiteralPath $topLevelItem.FullName -Force -Recurse) {
            if (($child.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0) {
                throw "Refusing to archive a reparse point: $($child.FullName)"
            }
            $allItems.Add($child)
        }
    }
}

$directories = @($allItems | Where-Object PSIsContainer | Sort-Object FullName)
$files = @($allItems | Where-Object { -not $_.PSIsContainer } | Sort-Object FullName)
$sourceByteCount = [int64](($files | Measure-Object -Property Length -Sum).Sum)
$createdAt = [DateTimeOffset]::Now

Add-Type -AssemblyName System.IO.Compression
Add-Type -AssemblyName System.IO.Compression.FileSystem

function ConvertTo-ArchiveName {
    param([Parameter(Mandatory)][string]$FullName)

    $relative = $FullName.Substring($projectRoot.Length).TrimStart('\', '/')
    return "$archiveRoot/$($relative.Replace('\', '/'))"
}

try {
    $fileStream = [System.IO.File]::Open(
        $partialPath,
        [System.IO.FileMode]::CreateNew,
        [System.IO.FileAccess]::ReadWrite,
        [System.IO.FileShare]::None
    )
    try {
        $archive = [System.IO.Compression.ZipArchive]::new(
            $fileStream,
            [System.IO.Compression.ZipArchiveMode]::Create,
            $false
        )
        try {
            [void]$archive.CreateEntry("$archiveRoot/")

            foreach ($directory in $directories) {
                $entryName = "$(ConvertTo-ArchiveName -FullName $directory.FullName)/"
                [void]$archive.CreateEntry($entryName)
            }

            foreach ($file in $files) {
                $entryName = ConvertTo-ArchiveName -FullName $file.FullName
                $entry = $archive.CreateEntry(
                    $entryName,
                    [System.IO.Compression.CompressionLevel]::Optimal
                )
                if ($file.LastWriteTime.Year -ge 1980 -and $file.LastWriteTime.Year -le 2107) {
                    $entry.LastWriteTime = [DateTimeOffset]$file.LastWriteTime
                }

                $inputStream = [System.IO.File]::Open(
                    $file.FullName,
                    [System.IO.FileMode]::Open,
                    [System.IO.FileAccess]::Read,
                    [System.IO.FileShare]::ReadWrite
                )
                try {
                    $entryStream = $entry.Open()
                    try {
                        $inputStream.CopyTo($entryStream)
                    }
                    finally {
                        $entryStream.Dispose()
                    }
                }
                finally {
                    $inputStream.Dispose()
                }
            }

            $includedTopLevel = ($topLevelItems.Name | ForEach-Object { "  - $_" }) -join "`n"
            $excludedList = ($excludedTopLevel | ForEach-Object { "  - $_" }) -join "`n"
            $manifestText = @"
SanctionPublicChoiceLean full-project archive
Generated: $($createdAt.ToString('o'))
Source: $projectRoot
Archive root: $archiveRoot/

Included source files: $($files.Count)
Included source bytes: $sourceByteCount

Included top-level items:
$includedTopLevel

Intentionally excluded top-level items:
$excludedList

Exclusion rationale:
  - .lake: downloaded/build dependency cache; explicitly excluded by request
  - .codegraph: generated structural index
  - tmp: scratch files and transient logs
  - dist: previously generated distribution artifacts
  - backups: historical and duplicate archives

The archive itself and its checksum sidecar are also excluded to prevent recursion.
"@
            $manifestEntry = $archive.CreateEntry(
                "$archiveRoot/PROJECT-ARCHIVE-MANIFEST.txt",
                [System.IO.Compression.CompressionLevel]::Optimal
            )
            $manifestStream = $manifestEntry.Open()
            try {
                $writer = [System.IO.StreamWriter]::new(
                    $manifestStream,
                    [System.Text.UTF8Encoding]::new($false),
                    4096,
                    $true
                )
                try {
                    $writer.Write($manifestText)
                }
                finally {
                    $writer.Dispose()
                }
            }
            finally {
                $manifestStream.Dispose()
            }
        }
        finally {
            $archive.Dispose()
        }
    }
    finally {
        $fileStream.Dispose()
    }

    $requiredEntries = @(
        "$archiveRoot/.git/HEAD",
        "$archiveRoot/AGENTS.md",
        "$archiveRoot/BookRefer/",
        "$archiveRoot/CLAUDE.md",
        "$archiveRoot/lakefile.toml",
        "$archiveRoot/lean-toolchain",
        "$archiveRoot/paper/sanctions_jet_draft.tex",
        "$archiveRoot/PaperRefer/",
        "$archiveRoot/Sanctions/",
        "$archiveRoot/Sanctions.lean",
        "$archiveRoot/scripts/Build-FullArchive.ps1",
        "$archiveRoot/PROJECT-ARCHIVE-MANIFEST.txt"
    )

    $validationStream = [System.IO.File]::OpenRead($partialPath)
    try {
        $validationArchive = [System.IO.Compression.ZipArchive]::new(
            $validationStream,
            [System.IO.Compression.ZipArchiveMode]::Read,
            $false
        )
        try {
            $entryNames = [System.Collections.Generic.HashSet[string]]::new(
                [System.StringComparer]::Ordinal
            )
            foreach ($entry in $validationArchive.Entries) {
                [void]$entryNames.Add($entry.FullName)
                if (-not $entry.FullName.StartsWith("$archiveRoot/", [System.StringComparison]::Ordinal)) {
                    throw "Entry outside the archive root: $($entry.FullName)"
                }
                if ($entry.FullName -match '(^|/)\.\.(/|$)' -or
                    $entry.FullName.StartsWith('/') -or
                    $entry.FullName.StartsWith('\')) {
                    throw "Unsafe archive entry: $($entry.FullName)"
                }
                foreach ($excluded in $excludedTopLevel) {
                    if ($entry.FullName.StartsWith(
                        "$archiveRoot/$excluded/",
                        [System.StringComparison]::OrdinalIgnoreCase
                    )) {
                        throw "Excluded path was archived: $($entry.FullName)"
                    }
                }
            }

            foreach ($required in $requiredEntries) {
                if (-not $entryNames.Contains($required)) {
                    throw "Required archive entry is missing: $required"
                }
            }
            $validatedEntryCount = $validationArchive.Entries.Count
            $validatedUncompressedBytes = [int64]((
                $validationArchive.Entries |
                    Measure-Object -Property Length -Sum
            ).Sum)
        }
        finally {
            $validationArchive.Dispose()
        }
    }
    finally {
        $validationStream.Dispose()
    }

    if (Test-Path -LiteralPath $outputFullPath) {
        Remove-Item -LiteralPath $outputFullPath -Force
    }
    Move-Item -LiteralPath $partialPath -Destination $outputFullPath

    $hash = Get-FileHash -LiteralPath $outputFullPath -Algorithm SHA256
    $checksumLine = "$($hash.Hash.ToLowerInvariant())  $(Split-Path -Leaf $outputFullPath)"
    [System.IO.File]::WriteAllText(
        $checksumPath,
        "$checksumLine`r`n",
        [System.Text.UTF8Encoding]::new($false)
    )

    $result = [ordered]@{
        ArchivePath = $outputFullPath
        ChecksumPath = $checksumPath
        ArchiveBytes = (Get-Item -LiteralPath $outputFullPath).Length
        SourceFiles = $files.Count
        SourceBytes = $sourceByteCount
        ZipEntries = $validatedEntryCount
        ZipUncompressedBytes = $validatedUncompressedBytes
        SHA256 = $hash.Hash.ToLowerInvariant()
        ExcludedTopLevel = $excludedTopLevel
    }
    $result | ConvertTo-Json -Depth 3
}
catch {
    if (Test-Path -LiteralPath $partialPath) {
        Remove-Item -LiteralPath $partialPath -Force
    }
    throw
}
