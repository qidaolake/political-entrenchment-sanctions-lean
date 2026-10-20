# Lean formalization companion

Companion to *Political Entrenchment and the Persistence of Economic Sanctions* (Gong, Zhao and Zhong 2026; titled
*Entrenchment and the Persistence of Sanctions* until 2026-10-19, *Government Horizons and the Persistence of
Sanctions* until 2026-10-11, and *Why Do Sanctions Persist? A Dynamic Political-Economy Model with Forward-Looking
Governments* until 2026-09-21). This guide describes how the Lean 4 development is organized, where each main-text
result is stated and proved, and how the formal claims are checked. The round-by-round development log that this file
carried until 2026-10-19 is in `docs/archive/LEAN-COMPANION-through-2026-10-19.md`.

## 1. What is verified

Every theorem stated in the main text is formalized and machine-checked in Lean 4 against Mathlib. The headline
results are the 65 rows of `Sanctions/Headlines.lean`; each depends only on `propext`, `Classical.choice` and
`Quot.sound`, and the build fails if that set changes (section 4). No `sorry`, no `admit` and no project `axiom` occurs
in `Sanctions/`. The kernel checks the formal statements; the correspondence between them and the economic sentences
of the paper is the reviewed map of the formal verification supplement (`paper/sanctions_formal_supplement.tex`), not a
kernel fact.

Several results are conditional: they consume an ordering, premium or existence condition that is stated precisely in
Lean and derived from primitives only under further assumptions. `docs/HYPOTHESIS-CENSUS.md` enumerates the
hypotheses of every headline row and every main-text result's backing declaration from their elaborated types, and
`ASSUMPTION-SURFACE-REGISTER.md` records which hypotheses are primitive and which are derived.

## 2. Layers

The development has six layers, in dependency order; audit gate 2 checks that no layer imports a later one.

- `Sanctions/Domain/`: the state and action space `[0,1]` and the projection onto it. It is the base layer because
  twelve `Foundations/` modules are stated over it.
- `Sanctions/Foundations/`: external mathematics (dynamic programming, monotone comparative statics, fixed points,
  the ergodic theory of the state chain), in modules named after their sources. No module mentions the sanctions
  game's parameters or payoffs.
- `Sanctions/Postulates/`: the primitive game objects (`Params`, `ShockedParams`).
- `Sanctions/Theory/`: the sanctions-specific theory: Bellman operators, basins, certificates, equilibrium, lock-in
  and welfare.
- `Sanctions/Examples/`: concrete economies and the paper's class (`ChordEconomy` and its extensions): witnesses,
  counterexamples, sharpness constructions, and the affine transition law as one worked instance.
- `Sanctions/Paper/`: the statement interface (section 3).

`Sanctions/Headlines.lean` sits outside the layers and imports what the headline rows need.

## 3. The paper interface

`Sanctions/Paper/Statements.lean` states each main-text result as a proposition (`def ... : Prop`), written out from
the model's definitions, with no proof and no reference to a theorem. Its imports are the modules that define the
vocabulary; audit gate 2 checks that it imports neither `Sanctions/Paper/Proofs.lean` nor `Sanctions/Headlines.lean`
nor a root aggregator. `Sanctions/Paper/Proofs.lean` proves each statement by the backing declaration, applied as is:
statement and declaration have the same type. The round axiom scan of the HPC job prints the axioms of each proof.

| Paper label | Statement | Backing declaration | File |
|---|---|---|---|
| `prop:myopic-benchmark` | `myopicBenchmark` | `ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage` | `Examples/PlacableSenderRegimes.lean` |
| `thm:regime-separation` | `regimeSeparation` | `ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF` | `Examples/PlacableSenderRegimes.lean` |
| `thm:dominance` | `dominance` | `Params.theorem2_dynamic_dominates_myopic_at_same_alpha` | `Theory/LockIn/SigmaDynComparison.lean` |
| `prop:lock-in` (no exit) | `lockInNoExit` | `Params.standardCompliance_persistence_generalF_from_sender_package` | `Theory/Certificates/SenderPersistencePackage.lean` |
| `prop:lock-in` (entry) | `lockInEntry` | `Params.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent` | `Theory/Certificates/StandardComplianceLocalised.lean` |
| `prop:collapse-threshold` | `collapseThreshold` | `ChordEconomyCs.collapse_equilibrium_threshold_le` | `Examples/PlacableSenderDefianceClosed.lean` |
| `prop:patience-existence` (i) | `patienceSlope` | `ChordEconomyRelief.balance_of_le_βT` | `Examples/PlacableSenderPatienceExistence.lean` |
| `prop:patience-existence` (ii) | `patienceExistence` | `ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | `Examples/PlacableSenderPatienceExistence.lean` |
| `prop:welfare-nonidentification` | `welfareNonidentification` | `ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking` | `Examples/ChordEconomyWelfareGeneral.lean` |
| `prop:zero-sanction-planner` | `zeroSanctionPlanner` | `Welfare.zeroSanction_planner_optimal` | `Theory/Welfare/PlannerZeroSanction.lean` |
| `prop:planner-efficient-persistence` | `plannerEfficientPersistence` | `ChordEconomy.planner_efficient_rep_at_policy_zero` | `Examples/ChordEconomyWelfareGeneral.lean` |
| `thm:four-cells` | `fourCases` | `ChordEconomyCs.four_cell_generalF'` | `Examples/PlacableSenderRegime01.lean` |

Statements and proofs live in the namespace `Sanctions.Paper`; the proofs are named `<statement>_holds`. Paths are
relative to `Sanctions/`. The formal verification supplement maps every result, including those of the appendix, to
its backing declarations; the HPC job checks that each of the 210 identifiers its primary-identifier table names
matches a declaration of the compiled environment by its last name component (`docs/census/map-identifiers.txt`,
`scripts/map_scan.lean`). That is an existence check: types and correspondence are checked by the snapshot, the axiom
scans and the reviewed map.

## 4. Conventions

**External mathematics is separated from the economics.** A theorem about dynamic programming, monotone comparative
statics or fixed points lives in `Foundations/`, in a file named after its source, so it can be checked against the
citation independently of the model. Where Mathlib supplies the underlying theorem, the module derives the cited
statement from it. `Theory/` contains only what is about this game.

**A witness does not live in the library it certifies.** A counterexample, a sharpness construction or an economy
exhibited to show that a hypothesis class is inhabited is evidence about a theorem, so it sits in `Examples/` with its
role declared in the file header, and the theorem it certifies points back to it. A witness proves existence, never
generality.

**The transition law is general.** The state transition is constrained by ordinal conditions (monotone in each
argument, fixing the diagonal), not pinned to a functional form. The affine law `F(x,s) = (1-δ)x + δs` is one member
of the family and lives in `Examples/AffineInstance/`. Every result is either general in the transition or says in its
docstring that it is affine-restricted; `scripts/audit-affine-surface.mjs` fails on any new reader of the affine rate
outside the reviewed baseline.

**The axiom check is a build-time assertion.** Each headline row in `Sanctions/Headlines.lean` is wrapped in
`#guard_msgs`, which compares the `#print axioms` message with the expected one and raises an error on any difference.
A bare `#print axioms` would only print a report: a `sorry` yields a warning and the build still succeeds.

**Statements are pinned by type, not only by name.** `HEADLINE-SNAPSHOT.md` records, for every headline row, an
alpha-invariant structural fingerprint of its elaborated type; audit gate 5 regenerates the snapshot and fails on a
changed fingerprint, axiom set or vanished row, so a statement weakened under the same name is caught.

## 5. Checks and reproduction

The build of record runs on the UConn Storrs HPC cluster: `scripts/hpc-package.py` packages a clean commit, the job
builds from empty and runs the seven audit gates, the round axiom scan, the census, the map-identifier scan and the
`leanchecker` kernel replay of every compiled module, and `scripts/hpc-verify-return.py` checks the return.
`BUILD-STATUS.md` holds the current receipt and `REPRODUCIBILITY.md` the commands. A local `lake build` is a targeted
check, not the record.

## 6. Repository invariant

The Lean development of the released version (the tag the manuscript names, public at <https://github.com/qidaolake/political-entrenchment-sanctions-lean>), whose HPC build
`BUILD-STATUS.md` records, is the ground-truth specification of every formal statement in the paper. Any change to a
paper claim (renaming a theorem, adding an assumption, demoting a proposition) is made in the Lean first and then
mirrored in the paper in the same audit round, never the reverse. When the paper and the Lean disagree, the Lean is
authoritative.
