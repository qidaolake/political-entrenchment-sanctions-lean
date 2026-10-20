# Project documentation

This folder separates current program documentation from historical records.

## Active

There is no separate active program plan at present. New plans should live here
only while they are being executed.

## Tooling

- `CODEGRAPH-EVALUATION-2026-08-20.md` records the CodeGraph (Lean fork) install,
  what its citation graph measures on this development, and — load-bearing — the
  boundary of what its answers may be trusted for. It is a candidate generator
  for unused declarations, never a verdict, and it is the wrong instrument for
  Rule 18 type-hash drift and Rule 22 affine-surface audits, both of which need
  elaborated constants rather than cited names.
- `CODEGRAPH-ISSUES.md` is the upstream-facing defect list for that tool: open
  problems with minimal repros and measured impact, plus the fixes absorbed
  during the evaluation. Hand this one to the fork author; the evaluation note
  is for us.

## Archive

`archive/` contains superseded design notes, workflow scratch, the long-form
build history, and completed maintenance recipes. Archived documents preserve
the reasoning record but do not override the Lean sources, the manuscript, or
the current root-level registers.

## Local generated state

- `.lake/` is the active Lean dependency/build cache.
- `paper/*.aux`, `paper/*.log`, and related files are reproducible paper-build
  products and are ignored by Git.
- `backups/` is an ignored local home for workspace snapshots and stale outputs
  retained during cleanup.
- `dist/` is reserved for generated portable bundles.

Temporary work should not be placed in a root `tmp/` directory. Retained
research probes belong under `docs/archive/workflow-scratch/`; disposable
scratch belongs outside the repository.

## Hypothesis census (compiler-derived; round E 2026-09-07, repaired round F 2026-09-08)

`HYPOTHESIS-CENSUS.md` lists every hypothesis of the headline rows (59 since the manuscript rebuild of 2026-10-02) and of
every main-text result's backing declaration, taken from the elaborated
types: binders, structure fields keyed by their declaring structure and
expanded two levels with a frontier list, one-level unfoldings of predicate
binders and fields, and a glossary of the project predicates unfolded once.
Counting units are separate named quantities with a bridge to the round-E
numbers. Roles are regex suggestions; a *status* is asserted only by the
curated tables (every other `Prop` row is `unreviewed`), and every status names
its evidence declarations, whose type hashes live in `HEADLINE-SNAPSHOT.md`
("Evidence declarations", from `docs/census/roots-evidence.txt`) and are
recorded at review time in `docs/census/status-evidence.json`. A moved hash
marks the status **stale** (the builder exits 2; `Audit-Round.ps1` gate 7 fails)
until the row is re-reviewed and the builder is run with `--rereview`.
Regenerate after any round that changes a headline or a main-text backing
declaration (the snapshot first, since the builder reads it):

```
python scripts/census_run.py docs/census/roots-headlines.txt docs/census/raw-headlines.txt
python scripts/census_run.py docs/census/roots-manuscript-names.txt docs/census/raw-manuscript.txt
python scripts/census_run.py docs/census/roots-preds.txt docs/census/raw-preds.txt censusPreds
python scripts/census_build.py docs/census/raw-headlines.txt docs/census/raw-manuscript.txt docs/census/raw-preds.txt docs/HYPOTHESIS-CENSUS.md
```

The unused-binder instrument (doc 78 K12; protocol v2 with a strict, fail-closed
parser, doc 80 M4) runs after a build over the same root lists; its self-test is
part of gate 7:

```
python scripts/unused_run.py docs/census/unused-binders.md docs/census/roots-headlines.txt docs/census/roots-manuscript-names.txt
python scripts/unused_run_selftest.py
```

`docs/census/roots-headlines.txt` is derived from `Sanctions/Headlines.lean`
(`grep '#print axioms'`) and gate 7 checks the two agree; `roots-manuscript.txt`
maps each manuscript label to its backing declaration(s) at clause level and is
hand-maintained (`roots-manuscript-names.txt` is derived from it). The runner
fails closed: a root that does not resolve, a duplicate, a truncated run or a
missing completion marker exits 1, and the builder refuses an incomplete raw
file. `scripts/Test-ContractFence.ps1` is the mutation test of the fence the
census leans on; its record is doc 70 §5.
