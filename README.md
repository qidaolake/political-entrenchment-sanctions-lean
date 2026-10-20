# Lean 4 companion to *Political Entrenchment and the Persistence of Economic Sanctions*

This repository accompanies *Political Entrenchment and the Persistence of Economic Sanctions* by Xiaofeng Gong,
Yuechuan Zhao and Chunping Zhong (2026; titled *Entrenchment and the Persistence of Sanctions* until 2026-10-19). It
holds the Lean 4 formalization that machine-checks the paper's results, the LaTeX sources of the three paper documents,
and the scripts that build and audit both. The paper is a working paper under review: cite the paper and a tagged
release (`CITATION.cff`), not a working state of a branch.

## Branch and versions

- **Public repository:** <https://github.com/qidaolake/political-entrenchment-sanctions-lean>. Each release is a tag (`vX.Y-submission`) with the
  manuscript, the Online Appendix and the formal supplement attached. The development history is kept in a private
  repository; a release here is the submission archive built from that repository's tag.
- **Verified states:** each verified state is a commit of the development repository together with the receipt of its
  HPC build in `BUILD-STATUS.md` (commit, Slurm job, return hash, job count); the commits named there are those of the
  development repository. Submission releases are tagged `vX.Y-submission`; the
  manuscript's data-availability statement names the tag it was submitted with (`v1.30-submission`).
- **Pins:** Lean `leanprover/lean4:v4.29.1` (`lean-toolchain`); Mathlib
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (`lake-manifest.json`); package definition `lakefile.toml`.

## The paper documents

| File | Document |
|---|---|
| `paper/sanctions_jet_draft.tex` | the manuscript |
| `paper/sanctions_jet_appendix.tex` | the appendix (proofs and extensions) |
| `paper/sanctions_formal_supplement.tex` | the formal verification supplement: the map from every result to its Lean declarations |

The manuscript names no Lean identifier. The formal supplement is the reviewed correspondence between the paper's
sentences and the formal statements; the kernel checks the statements, not that correspondence.

## Where to start reading

1. `Sanctions/Paper/Statements.lean` states the twelve main-text results in full, without proofs, from the model's
   definitions. It is the file to read against the paper.
2. `Sanctions/Paper/Proofs.lean` proves each statement by the backing declaration the formal supplement names.
3. `Sanctions/Headlines.lean` is the pinned headline set: 65 rows, each with its `#print axioms` output asserted by
   `#guard_msgs`, so a changed axiom set fails the build. Every row depends only on `propext`, `Classical.choice` and
   `Quot.sound`.
4. `HEADLINE-SNAPSHOT.md` pins the elaborated type of every headline row by a structural fingerprint, so a weakened
   statement under the same name is caught.
5. `docs/HYPOTHESIS-CENSUS.md` enumerates the hypotheses of every headline row and of every main-text result's backing
   declaration from their elaborated types; `ASSUMPTION-SURFACE-REGISTER.md` records which are primitive and which
   are derived.
6. `LEAN-COMPANION.md` is the guide to the development: layers, conventions and the paper-to-Lean index.

## Layout

```
Sanctions/
  Domain/          the state and action space [0,1] and the projection onto it
  Foundations/     external mathematics, in modules named after their sources
  Postulates/      the primitive game objects (Params, ShockedParams)
  Theory/          the sanctions-specific theory: Bellman operators, basins, certificates, equilibrium, lock-in, welfare
  Examples/        concrete economies and classes: witnesses, counterexamples, sharpness constructions, the paper's class
  Paper/           the statement interface: Statements.lean (no proofs) and Proofs.lean
  Headlines.lean   the pinned headline rows, each with an asserted `#print axioms`
paper/             the three paper documents, their section files, bibliography and style
scripts/           build, audit, census and HPC packaging scripts
docs/              the hypothesis census, primitive census, reading guides and their inputs (docs/census/)
```

Each layer imports only the layers above it in this list; audit gate 2 enforces the order, and the statements of the
paper interface import neither their proofs nor the headline file. Witnesses live in `Examples/`, not in the layer
whose theorems they certify; each carries its role in its file header. The transition law is general: it is
constrained by ordinal conditions, and the affine law is one worked instance (`Examples/AffineInstance/`). Every
result is either general in the transition or says in its docstring that it is affine-restricted.

## What is checked, and where

The build of record runs on the UConn Storrs HPC cluster (Slurm). `scripts/hpc-package.py` cuts a package from a
clean commit; the job (`scripts/hpc-leanbuild.sh`) builds from empty and runs:

- the seven gates of `scripts/Audit-Round.ps1`: toolchain pin, layer architecture, a source scan for `sorry`, `admit`
  and project `axiom`, the build, the headline snapshot, the replay list, and the census coverage check;
- an axiom scan of the declarations named in `scripts/hpc-round-scan.txt`;
- the hypothesis census and the unused-binder instrument;
- the map-identifier scan: every Lean identifier named by the formal supplement's identifier table
  (`docs/census/map-identifiers.txt`, generated by `scripts/map_identifiers.py`) must match a declaration of the
  compiled environment by its last name component (an existence check, as `checkdecls` makes for a blueprint);
- kernel replay: `leanchecker` re-checks every compiled `Sanctions` module, and the replayed count must equal the
  number of modules.

`scripts/hpc-verify-return.py` checks the returned receipt and logs against the local tree. The current receipt:

| | |
|---|---|
| Lean | `leanprover/lean4:v4.29.1` |
| Mathlib | `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Build | 3780 jobs from empty, zero errors, zero `sorry` (release `v1.30-submission`, UConn HPC job 31883241, built from the extracted submission archive) |
| Headline rows | 65, each with an asserted `#print axioms` |

Audit gate 4 reads the job count from the build and fails if this file or `BUILD-STATUS.md` does not state it.
`.github/workflows/build.yml` runs the same checks on a hosted runner but has no automatic trigger; it is available by
manual dispatch and is not the build of record.

## Reproduce

With [elan](https://github.com/leanprover/elan) installed, from the repository root:

```bash
lake exe cache get          # precompiled Mathlib
lake build                  # the whole development, including Sanctions/Headlines.lean
lake env leanchecker -v Sanctions   # optional: kernel replay of every compiled module
```

`pwsh -File scripts/Audit-Round.ps1` runs the seven gates (PowerShell 7). The paper documents build with
`pwsh -File scripts/Build-Paper.ps1 -SkipNotes`, which compiles the three documents in the order their
cross-references need. `REPRODUCIBILITY.md` has the details.

## Scope and caveats

- Several results are conditional: they consume an ordering, premium or existence condition that is stated precisely
  in Lean and derived from primitives only under further assumptions. The census and the register say which.
- A theorem proved at an exhibited economy certifies that a class is inhabited and nothing more. Such results are
  marked as witnesses; no genericity claim is made from them.
- The cross-equilibrium ordering of the Target's policies is conditional: one channel is signed from separated
  primitives and the other is not, and `Examples/BaselineTwoSidedOrderingUndetermined.lean` exhibits an economy where
  the ordering reverses.
- Sanctions entry is an imposed shock; the threat stage, expiry and review provisions are outside the model.
- `Theory/` keeps some superseded routes because their failure is informative; their docstrings say so.

## Working material

`suggestions/`, `docs/archive/`, `audit-notes/`, the round plans at the top level and `paper/note_sections/` (the
staging document) are the project's working record. They are not asserted results and are not part of the submission
archive, which `scripts/Build-CoreBundle.ps1 -Submission` builds from the allowlist `release/SUBMISSION-MANIFEST.txt`
(`CORE-BUNDLE.md`).

## Licence and citation

The Lean sources, scripts and documentation are released under the MIT License (`LICENSE`). The paper sources under
`paper/` are the authors' manuscript and are not covered by that licence. Citation metadata is in `CITATION.cff`.
