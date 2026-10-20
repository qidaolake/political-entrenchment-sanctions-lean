<#
.SYNOPSIS
    Builds the four paper documents and reports unresolved references.

.DESCRIPTION
    The paper lives in paper/ as four thin root documents, three ordered
    section directories, and two shared includes:

        paper/sanctions_jet_draft.tex      the submission manuscript      (ROOT 1)
        paper/sanctions_jet_appendix.tex   the appendix reference document (ROOT 2)
        paper/sanctions_jet_notes.tex      staging / other information     (ROOT 3)
        paper/sanctions_formal_supplement.tex
                                           formal-verification supplement  (ROOT 4)

        paper/sanctions_preamble.tex       shared packages + macros
        paper/sanctions_appendix_body.tex  ordered appendix index (ROOT 1 combined / ROOT 2)

        paper/main_sections/               manuscript section bodies
        paper/appendix_sections/           appendix section bodies
        paper/note_sections/               staging-note section bodies

    All compilation runs inside paper/ (so \input, annote.bib, and econ-aea.bst
    resolve, and the PDFs land next to their sources).

    The manuscript, appendix, and formal supplement reference one another
    through xr-hyper.  xr reads the *sibling's .aux*, so a document cannot
    resolve into a sibling that has never been compiled.  Hence the ordering
    below: compile all three submission-facing roots once to lay down .aux
    files, run BibTeX, then compile them twice more so each sees the others
    settled.

.PARAMETER Combined
    Build the manuscript with the appendix inlined (single self-contained PDF,
    one unified bibliography) as sanctions_jet_combined.pdf.  Use this if the
    appendix is to be bound into the submission rather than supplied as a
    separate supplementary PDF.  Leaves the split artefacts untouched.

.PARAMETER SkipNotes
    Skip the staging document (sanctions_jet_notes.tex), which is never submitted.

.EXAMPLE
    .\scripts\Build-Paper.ps1
    .\scripts\Build-Paper.ps1 -Combined
#>
[CmdletBinding()]
param(
    [switch]$Combined,
    [switch]$SkipNotes,
    # Keep stale .aux/.toc/.out state instead of clearing it first. Only for
    # fast local iteration -- NEVER for a build whose output is reported.
    [switch]$KeepAux
)

$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
# All paper sources and outputs live in paper/; compile from there.
Push-Location (Join-Path $repo 'paper')

# MiKTeX is not always on PATH in a fresh shell.
$miktex = "$env:LOCALAPPDATA\Programs\MiKTeX\miktex\bin\x64"
if ((Test-Path $miktex) -and ($env:PATH -notlike "*$miktex*")) {
    $env:PATH = "$miktex;$env:PATH"
}

# --- Clear stale cross-reference state before building --------------------
# xr-hyper resolves \Cref across the four roots by READING the sibling's
# .aux. That makes .aux authoritative for what a label points at -- and
# stale, because nothing ever invalidates it. On 2026-08-09 the manuscript
# was restructured into a new section set; the build kept reporting "0
# undefined refs" against .aux entries left over from the OLD sections, and
# a build with cleared .aux came out 19 pages shorter. A reference that
# resolves only against a previous document's leftovers is a dangling
# reference the build cannot see.
#
# Pass 1 below re-seeds every .aux from scratch, so clearing costs nothing
# but the seeding pass that already runs.
if (-not $KeepAux) {
    Write-Host "  clearing stale .aux / .toc / .out state"
    Get-ChildItem -Path . -Include *.aux, *.toc, *.out -File -ErrorAction SilentlyContinue |
        Remove-Item -Force -ErrorAction SilentlyContinue
}
# MiKTeX's user install does not put itself on PATH, and a session started from
# Git Bash or a fresh shell will not see it. That cost a round: the paper was
# reported unbuildable here and the verification was pushed to CI, which is
# exactly backwards under Rule 25 -- and MiKTeX had been installed the whole
# time. So look for it before giving up.
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    $candidates = @(
        "$env:LOCALAPPDATA\Programs\MiKTeX\miktexind",
        "$env:LOCALAPPDATA\Programs\MiKTeX\miktexin",
        "$env:ProgramFiles\MiKTeX\miktexind",
        "${env:ProgramFiles(x86)}\MiKTeX\miktexin",
        "$env:ProgramFiles	exlive5in\windows",
        "$env:ProgramFiles	exlive4in\windows"
    )
    foreach ($c in $candidates) {
        if ($c -and (Test-Path (Join-Path $c 'pdflatex.exe'))) {
            Write-Host "  found TeX at $c (adding to PATH for this build)"
            $env:PATH = "$c;$env:PATH"
            break
        }
    }
}
if (-not (Get-Command pdflatex -ErrorAction SilentlyContinue)) {
    throw "pdflatex not found. Install MiKTeX or TeX Live, or add its bin directory to PATH."
}

# NOTE: latexmk is NOT used by this script -- it drives pdflatex and bibtex
# directly. MiKTeX ships a latexmk wrapper that needs Perl and fails without it;
# that failure is irrelevant here and is not a reason to think TeX is broken.

function Invoke-Pdflatex {
    # $Arg is an ARRAY: each element must reach pdflatex as its own argv entry.
    # Passing "-jobname=x \def\Y{}\input{z}" as one string makes pdflatex treat
    # the whole thing as a single filename and block at its ** prompt.
    param([string]$Job, [string[]]$Arg)
    # stdout is noise unless something failed; the .log is the record.
    $out = & pdflatex -interaction=nonstopmode -halt-on-error -file-line-error @Arg 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  pdflatex FAILED on $Job" -ForegroundColor Red
        $out | Select-String -Pattern '^.*:\d+:.*$' | Select-Object -First 15 |
            ForEach-Object { Write-Host "    $_" -ForegroundColor Red }
        throw "pdflatex failed on $Job"
    }
}

function Invoke-Bibtex {
    param([string]$Job)
    $out = & bibtex $Job 2>&1
    # BibTeX can exit non-zero for warnings, but a real error must not be
    # hidden by a stale .bbl from an earlier successful build.
    $blg = if (Test-Path "$Job.blg") { Get-Content "$Job.blg" -Raw } else { '' }
    if ($blg -match 'There (?:was|were) [1-9]\d* error message') {
        $out | Select-Object -First 15 |
            ForEach-Object { Write-Host "    $_" -ForegroundColor Red }
        throw "bibtex reported an error for $Job"
    }
    if (-not (Test-Path "$Job.bbl")) { throw "bibtex produced no $Job.bbl" }
}

function Invoke-BibtexIfCited {
    param([string]$Job)
    $aux = if (Test-Path "$Job.aux") { Get-Content "$Job.aux" -Raw } else { '' }
    if ($aux -match '\\citation\{') {
        Invoke-Bibtex $Job
        return
    }

    # An empty staging queue legitimately has no citations.  Do not retain a
    # bibliography from an earlier queue, and do not ask BibTeX to process an
    # aux file for which it correctly reports "no \citation commands".
    Remove-Item -LiteralPath "$Job.bbl" -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath "$Job.blg" -Force -ErrorAction SilentlyContinue
    Write-Host "    no citations; bibliography skipped"
}

function Report {
    param([string]$Job)
    if (-not (Test-Path "$Job.log")) { return }
    $log = Get-Content "$Job.log" -Raw
    # pdflatex wraps log lines at 79 characters, mid-word, so a warning can
    # read "...on page 13 unde" / "fined". Flatten before matching (2026-09-06:
    # an undefined citation in the notes was reported as zero this way).
    $flat = $log -replace "\r?\n", ''
    $undefRef  = ([regex]::Matches($flat, 'Reference `[^'']*'' on page')).Count
    $undefCite = ([regex]::Matches(
        $flat,
        "Citation\s+[`']+[^`']+[`']+(?:\s+on page \d+)?\s+undefined",
        [System.Text.RegularExpressions.RegexOptions]::IgnoreCase
    )).Count
    $pages     = 0
    $m = [regex]::Match($log, 'Output written on .*\((\d+) pages?')
    if ($m.Success) { $pages = [int]$m.Groups[1].Value }
    $colour = 'Green'
    if (($undefRef + $undefCite) -gt 0) { $colour = 'Yellow' }
    Write-Host ("  {0,-28} {1,3} pp   undefined refs: {2}   undefined cites: {3}" -f `
        "$Job.pdf", $pages, $undefRef, $undefCite) -ForegroundColor $colour
    return ($undefRef + $undefCite)
}

Write-Host ""
if ($Combined) {
    Write-Host "=== COMBINED build (manuscript + appendix, one PDF) ===" -ForegroundColor Cyan

    # The combined manuscript imports the standalone formal supplement's
    # labels. Seed the split manuscript and appendix so the formal supplement
    # can in turn resolve its references back to them, then settle the formal
    # supplement before compiling the combined manuscript.
    Write-Host "  seeding support .aux files"
    Invoke-Pdflatex 'sanctions_jet_draft'          'sanctions_jet_draft'
    Invoke-Pdflatex 'sanctions_jet_appendix'       'sanctions_jet_appendix'
    Invoke-Pdflatex 'sanctions_formal_supplement'  'sanctions_formal_supplement'
    Invoke-Bibtex   'sanctions_formal_supplement'
    Invoke-Pdflatex 'sanctions_formal_supplement'  'sanctions_formal_supplement'
    Invoke-Pdflatex 'sanctions_formal_supplement'  'sanctions_formal_supplement'

    $arg = @('-jobname=sanctions_jet_combined',
             '\def\COMBINEDAPPENDIX{}\input{sanctions_jet_draft}')
    Invoke-Pdflatex 'sanctions_jet_combined' $arg
    Invoke-Bibtex   'sanctions_jet_combined'
    Invoke-Pdflatex 'sanctions_jet_combined' $arg
    Invoke-Pdflatex 'sanctions_jet_combined' $arg
    Write-Host ""
    $bad = 0
    $bad += Report 'sanctions_jet_combined'
    $bad += Report 'sanctions_formal_supplement'
}
else {
    Write-Host "=== SPLIT build (manuscript / appendix / formal supplement / notes) ===" -ForegroundColor Cyan

    # Pass 1: lay down .aux for all submission-facing roots so xr has
    # something to read.
    Write-Host "  pass 1/3  seeding .aux files"
    Invoke-Pdflatex 'sanctions_jet_draft'          'sanctions_jet_draft'
    Invoke-Pdflatex 'sanctions_jet_appendix'       'sanctions_jet_appendix'
    Invoke-Pdflatex 'sanctions_formal_supplement'  'sanctions_formal_supplement'

    Write-Host "  bibtex"
    Invoke-Bibtex 'sanctions_jet_draft'
    Invoke-Bibtex 'sanctions_jet_appendix'
    Invoke-Bibtex 'sanctions_formal_supplement'

    # Passes 2-3: the roots now resolve into one another; a second pass settles
    # numbering shifts that the first pass's newly resolved refs may cause.
    Write-Host "  pass 2/3  resolving cross-document references"
    Invoke-Pdflatex 'sanctions_jet_draft'          'sanctions_jet_draft'
    Invoke-Pdflatex 'sanctions_jet_appendix'       'sanctions_jet_appendix'
    Invoke-Pdflatex 'sanctions_formal_supplement'  'sanctions_formal_supplement'
    Write-Host "  pass 3/3  settling"
    Invoke-Pdflatex 'sanctions_jet_draft'          'sanctions_jet_draft'
    Invoke-Pdflatex 'sanctions_jet_appendix'       'sanctions_jet_appendix'
    Invoke-Pdflatex 'sanctions_formal_supplement'  'sanctions_formal_supplement'

    if (-not $SkipNotes) {
        Write-Host "  notes (staging document, never submitted)"
        Invoke-Pdflatex 'sanctions_jet_notes' 'sanctions_jet_notes'
        Invoke-BibtexIfCited 'sanctions_jet_notes'
        Invoke-Pdflatex 'sanctions_jet_notes' 'sanctions_jet_notes'
        Invoke-Pdflatex 'sanctions_jet_notes' 'sanctions_jet_notes'
    }

    Write-Host ""
    $bad = 0
    $bad += Report 'sanctions_jet_draft'
    $bad += Report 'sanctions_jet_appendix'
    $bad += Report 'sanctions_formal_supplement'
    if (-not $SkipNotes) { $bad += Report 'sanctions_jet_notes' }
}

Write-Host ""
if ($bad -gt 0) {
    Write-Host "FAIL: $bad unresolved reference(s)/citation(s). See the .log files." -ForegroundColor Red
    Pop-Location
    exit 1
}
Write-Host "OK: all documents built, every reference and citation resolved." -ForegroundColor Green
Pop-Location
