# Core Transfer Bundle

This project now has a repeatable transfer recipe for moving the runnable
research core to another computer.

## Build the bundle

From the repository root:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\Build-CoreBundle.ps1
```

By default this writes:

```text
dist\SanctionPublicChoiceLean-core.zip
```

The script runs `lake build` first, then creates a zip containing the Lean
library, current JET draft, bibliography/style files, documentation, audit
notes, and the full `BookRefer/` and `PaperRefer/` reference trees. It
intentionally excludes `.lake`, `.git`, `backups`, `scratch`, generated LaTeX
auxiliaries, prior zip files, editor state, and CodeGraph indexes.

Useful options:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\Build-CoreBundle.ps1 -SkipBuildCheck
powershell -ExecutionPolicy Bypass -File scripts\Build-CoreBundle.ps1 -NoReferences
powershell -ExecutionPolicy Bypass -File scripts\Build-CoreBundle.ps1 -OutputPath D:\transfer\SanctionPublicChoiceLean-core.zip
```

Use `-NoReferences` for a smaller runnable zip without the `BookRefer/` and
`PaperRefer/` reference trees. Use that option for any public repository or
archival deposit: the default full-reference bundle is for private transfer
only and may contain research-library material that the project is not
authorized to redistribute.

Use `-Submission` for the archive that accompanies the journal submission.
Since 2026-10-19 (LEANREPO M3) it is an explicit allowlist: the archive holds
exactly the paths listed in `release/SUBMISSION-MANIFEST.txt`, where a line
ending in `/` stands for every tracked file under that directory. A listed
path that is missing fails the build, and so does a repository file that the
three submitted documents cite with `\path{...}` but the archive lacks. The
reference libraries, the notes root and `paper/note_sections` (the staging
document, never submitted), `paper/submission` (the internal decision sheets),
`audit-notes`, the planning material (`suggestions/`, `docs/archive/` except
the one evaluation script the appendix cites, the round plans) and the agent
and editor configuration stay out (decision D4, 2026-10-19). The manifest's
`Profile:` line records which profile built the archive, and the TeX closure
check covers the three submitted roots. The data-availability statement names
this profile.

```powershell
pwsh -NoProfile -File scripts\Build-CoreBundle.ps1 -Submission
```

Before a release the submission archive is extracted into a clean directory
outside the checkout, a scratch Git repository is initialised there, and the
HPC package is cut from that copy and its return verified from it (Rule 26);
the three paper documents are built there with `Build-Paper.ps1 -SkipNotes`.
The receipt is recorded in `BUILD-STATUS.md`. No hosted run is involved
(Rule 25). Under Rule 26 the Lean build of record is the HPC build, so pass
`-SkipBuildCheck` where no local build is wanted.

## Run it on another computer

1. Unzip the archive.
2. Install Lean via elan if needed.
3. From the unzipped project root, run:

```powershell
lake exe cache get
lake build
```

The exact job count can change when modules are added; a successful build ends
with `Build completed successfully`.

To rebuild the paper on the new machine, use the bundled build script — do
**not** run `pdflatex` by hand. The paper has four root documents whose
submission-facing components cross-reference one another through `xr-hyper`,
so each must be compiled
before the others can resolve into it; the script handles that ordering:

```powershell
.\scripts\Build-Paper.ps1              # manuscript + appendix + formal supplement + notes
.\scripts\Build-Paper.ps1 -Combined    # combined main/appendix + formal supplement
```

It reports the page count and the unresolved-reference count for each
document, and exits non-zero if anything is left dangling.

The paper sources live in **`paper/`** as four thin roots, two shared
includes, and three ordered section directories (CLAUDE.md Rule 21):

| File | Role |
|---|---|
| `paper/sanctions_jet_draft.tex` | ROOT — the submission manuscript |
| `paper/sanctions_jet_appendix.tex` | ROOT — the appendix reference document |
| `paper/sanctions_jet_notes.tex` | ROOT — staging / other information, never submitted |
| `paper/sanctions_formal_supplement.tex` | ROOT — online formal-verification supplement |
| `paper/sanctions_preamble.tex` | shared packages + macros (all four roots) |
| `paper/sanctions_appendix_body.tex` | ordered appendix-section index (appendix root; manuscript in `-Combined`) |
| `paper/main_sections/` | manuscript section bodies |
| `paper/appendix_sections/` | appendix section bodies |
| `paper/note_sections/` | staging-note section bodies |

alongside `paper/annote.bib` (BibTeX database) and `paper/econ-aea.bst`
(AEA style). `paper/sanctions_jet_draft.pdf`,
`paper/sanctions_jet_appendix.pdf`, and
`paper/sanctions_formal_supplement.pdf` are included as ready-to-read
snapshots. The repository `LICENSE` ships at the top level.

Since 2026-09-15 (round S; the reader's 2026-09-12 archive audit) the
builder resolves provenance first (commit, exact tag or "none", dirty flag,
toolchain, mathlib revision), checks every native exit code, fails closed on
any missing mandatory input (only `BookRefer/` and `PaperRefer/` are
optional, and `-NoReferences` excludes them for the public profile), verifies
the TeX input closure of the four roots inside the staged tree, writes
`CORE-BUNDLE-MANIFEST.txt` with one `sha256  bytes  path` line per member,
compresses with the .NET ZipFile API into a uniquely named candidate, reopens
it to verify path safety, the exact member set and every length and SHA256,
and only then replaces the previous archive, writing the final digest to a
`.sha256` sidecar next to it. A dirty working tree is recorded in the
manifest and warned about, not refused.
