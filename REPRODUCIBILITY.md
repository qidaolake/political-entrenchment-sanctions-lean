# Reproducibility guide

This repository contains the Lean 4 formalization and LaTeX sources for
*Political Entrenchment and the Persistence of Economic Sanctions* (titled *Entrenchment and the Persistence of
Sanctions* until 2026-10-19, *Government Horizons and the Persistence of Sanctions* until 2026-10-11 and *Why Do
Sanctions Persist? A Dynamic Political-Economy Model with Forward-Looking
Governments* until 2026-09-21).

No empirical data are used. The reproducibility object is the formal model,
its machine-checked proofs, the witness economies, and the manuscript-to-Lean
map.

## Pinned environment

- Lean: `leanprover/lean4:v4.29.1` (`lean-toolchain`)
- Mathlib: pinned by `lake-manifest.json`
- Package definition: `lakefile.toml`
- LaTeX: pdfLaTeX and BibTeX; the build script also locates a standard MiKTeX
  installation on Windows

## Verify the Lean development

The build of record runs on the UConn Storrs HPC cluster (Slurm; CLAUDE.md Rule 26). From a clean commit:

```powershell
python scripts/hpc-package.py <run-id>            # package the committed tree; refuses a dirty tree or moved pins
# stage, activate and submit the package; fetch return.zip when the job has ended
python scripts/hpc-verify-return.py return.zip    # check the returned receipt and logs against the local tree
```

The job builds from empty and runs the seven audit gates, the round axiom scan (`scripts/hpc-round-scan.txt`), the
hypothesis census, the map-identifier scan (every Lean identifier the formal supplement's identifier table names must
match a declaration of the compiled environment by its last name component) and the `leanchecker` kernel replay of
every compiled module.
`BUILD-STATUS.md` records the current receipt. On any other machine the same gates run as a targeted check.

From the repository root:

```powershell
lake exe cache get
pwsh -NoProfile -ExecutionPolicy Bypass -File scripts\Audit-Round.ps1 -CleanRebuild
```

Run the scripts under pwsh 7. They carry a UTF-8 byte-order mark (since
2026-09-10) so that Windows PowerShell 5.1 also decodes their Greek
identifiers correctly; before the mark, a 5.1 run on a non-Latin codepage
mangled the snapshot generator's contract roots and reported gate 5 stable
without regenerating the snapshot.

The audit command checks the toolchain pin, aggregator completeness, absence
of project `sorry`, `admit`, and `axiom` declarations, a from-empty build, and
stability of the protected 65-row headline snapshot (keyed on its structural
fingerprint column since round O; a moved printed hash alone is reported, not
failed), the in-build
axiom replay of every headline, and the hypothesis census's coverage and
evidence-staleness check (seven gates in all).

For a faster repeat check that keeps existing build artifacts:

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File scripts\Audit-Round.ps1
```

## Build the paper and supplements

The default build produces the submission manuscript, economic appendix,
online formal-verification supplement, and internal notes:

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File scripts\Build-Paper.ps1
```

The alternative combined build binds the manuscript and economic appendix
into one PDF while keeping the formal-verification supplement separate:

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File scripts\Build-Paper.ps1 -Combined
```

The submission archive carries no notes document; build the three paper documents there with

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File scripts\Build-Paper.ps1 -SkipNotes
```

The script exits nonzero on a LaTeX or BibTeX error and reports unresolved
references and citations.

## Locate the claims

- `paper/sanctions_jet_draft.tex`: submission manuscript root
- `paper/sanctions_jet_appendix.tex`: economic appendix root
- `paper/sanctions_formal_supplement.tex`: theorem-to-Lean map
- `Sanctions/Paper/Statements.lean`: the main-text results stated in Lean, without proofs; `Sanctions/Paper/Proofs.lean`
  proves each by its backing declaration
- `HEADLINE-SNAPSHOT.md`: protected theorem signatures (printed hash and
  structural fingerprint) and axiom dependencies
- `LEAN-COMPANION.md`: paper-to-Lean symbol guide
- `ASSUMPTION-SURFACE-REGISTER.md`: maintained hypothesis hierarchy
- `BUILD-STATUS.md`: the current verification receipt (earlier rounds in `docs/archive/`)

## Create a portable archive

For a public code-and-model deposit, exclude the local research-library
copies:

```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File scripts\Build-CoreBundle.ps1 `
  -NoReferences `
  -OutputPath dist\SanctionPublicChoiceLean-public-source.zip
```

For the archive that accompanies the journal submission use `-Submission`
instead. Since 2026-10-19 it copies exactly the paths listed in
`release/SUBMISSION-MANIFEST.txt`, and it fails if a listed path is missing or
if a repository file that the three paper documents cite is absent from the
archive. The reference libraries, the notes document and its staging sections,
`paper/submission`, `audit-notes`, the planning material and the agent and
editor configuration stay out. `CORE-BUNDLE.md` lists the profiles and the
extract-and-verify check that precedes a release.

This creates `dist/SanctionPublicChoiceLean-public-source.zip` after checking
the Lean build. Generated build directories, local caches, `PaperRefer/`, and
`BookRefer/` are excluded. The default bundle command described in
`CORE-BUNDLE.md` retains the two reference-library directories for private
machine-to-machine transfer and must not be used as the public deposit unless
the author has redistribution rights for every included item.

## Deposit status

`CITATION.cff` supplies local citation metadata. Two of the deposit choices
are made: the licence is MIT for the Lean sources, scripts and documentation
(`LICENSE`, `CITATION.cff`; the paper sources under `paper/` are not covered),
and submission rounds are tagged `vX.Y-submission` (the manuscript names the tag it was submitted
with). The release is public at <https://github.com/qidaolake/political-entrenchment-sanctions-lean>, and the manuscript's data-availability
statement names it. One choice is not made, and is not invented here: an archive DOI under a persistent identifier,
which will accompany publication.
