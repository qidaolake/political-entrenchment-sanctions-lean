/-
Sanctions/Headlines.lean

**The Rule-10 / Rule-18 headline gate file.**

One `#print axioms` per committed headline row of `HEADLINE-SNAPSHOT.md`, in
snapshot order (the count is the snapshot's, and gate 6 of `Audit-Round.ps1`
checks the two lists agree, so no numeral is repeated here). Elaborating this
module replays the kernel axiom scan for every headline theorem: each line
below reports its axiom dependencies, and each must read exactly
`[propext, Classical.choice, Quot.sound]`. The from-empty acceptance build of
a round forces that replay; a cached incremental `lake build` need not
elaborate this module again, which is one reason Rule 17 requires the
from-empty build as the receipt (wording corrected 2026-09-11, the reader's
C15–C16).

(That paragraph is wrapped the way it is on purpose. `Audit-Round.ps1`
gate 3 scans this tree for `axiom` declarations with a deliberately
comment-blind regex, so a prose line *beginning* with `axiom ` fails the
gate. It did, from 2026-08-22 until the CI step that runs the gate was
added and immediately tripped on it. Keep the word off the start of a
line.)

**Each row is wrapped in `#guard_msgs`, and that is what makes this a gate
rather than a report.** `#print axioms` on its own is a *query* command: it
prints, it does not compare against an allowlist, and it does not fail. Left
bare, a `sorry` produces only a `warning`, the line prints `[sorryAx]`, and
`lake build` still exits 0 — verified directly on 2026-08-22, which is how
this hole was found. `#guard_msgs` compares the emitted message against the
docstring above it and raises `error:` on any difference, so a changed axiom
set now fails the build. That was verified the same day by tampering with one
expected set and confirming exit 1.

`(whitespace := lax)` is load-bearing: the axiom list wraps across lines at a
column that depends on the length of the theorem's name, so a strict
comparison would break on a rename that changed nothing mathematically.

Both halves of the gate are therefore enforced in-build: a changed axiom set
fails via `#guard_msgs` (Rule 10), and a headline that vanished or was renamed
fails to resolve (Rule 3). The rows are generated mechanically from the
`#print axioms` output rather than written by hand, so the expected messages
cannot drift from the theorem names.

`scripts/Generate-HeadlineSnapshot.ps1` remains the Rule-18 anchor for the
*elaborated type* hashes, which are a different question from axioms and are
still checked out of band.

The snapshot generator (`scripts/Generate-HeadlineSnapshot.ps1`) remains
the canonical Rule-18 anchor (it also hashes the elaborated types); this
file is the always-on in-build companion. Keep the two lists in sync:
adding a snapshot row adds a `#print axioms` line here, and vice versa.

**This invariant failed silently once and must not again.** On 2026-08-09 an
audit found 6 of the then-32 rows unreplayed here: rows 1 and 3 still named the affine
`..._MS` / `..._low_basin` theorems after the 2026-08-08 Rule-22 swap to their
general-`F` siblings, and rows 29-32 had been added to the snapshot without
lines here. Nothing caught it, because gate 5 of `scripts/Audit-Round.ps1`
regenerated the snapshot from its own generator list and never compared that
list against this file. Gate 6 now performs exactly that comparison, so a
future divergence fails the round instead of shipping.
-/

import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Certificates.StandardComplianceLowBasin
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.LockIn.LockIn
import Sanctions.Theory.Shocked.ShockedLeaderLipschitz
import Sanctions.Theory.Equilibrium.PerovExistence
import Sanctions.Foundations.KrylovBogolyubov
import Sanctions.Examples.EECertWitness
import Sanctions.Examples.EECertWitnessMS
import Sanctions.Examples.MechanismWitnessShocked
import Sanctions.Examples.MechanismWitnessShockedUnconditional
import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Examples.PlacableSenderWitnesses
import Sanctions.Examples.LowBasinCertWitness
import Sanctions.Examples.B2NonMonotoneCertWitness
import Sanctions.Examples.B2GeneralFPersistenceWitness
import Sanctions.Examples.FourGroupCertWitness
import Sanctions.Examples.StageFlipCertWitness
import Sanctions.Examples.DualBasinSelectionWitness
import Sanctions.Examples.CoupledRoute.LowDeltaWindowWitness
import Sanctions.Examples.CoupledRoute.CoupledSchurWitness
import Sanctions.Examples.FeedbackComparativeStatics
import Sanctions.Examples.FourGroupPlannerWitness
import Sanctions.Theory.Certificates.SenderPersistencePackage
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFPersistence
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFRecovery
import Sanctions.Examples.PlacableSenderRegime10
import Sanctions.Examples.DualBasinTwoSidedRegimes
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderReliefActivation
import Sanctions.Examples.PlacableSenderBracket
import Sanctions.Examples.PlacableSenderUniqueness
import Sanctions.Examples.PlacableSenderAllEquilibria
import Sanctions.Examples.PlacableSenderReliefParticipation
import Sanctions.Examples.PlacableSenderBranchInvariance
import Sanctions.Theory.Equilibrium.TopLifetimeVerification
import Sanctions.Examples.PlacableSenderWelfareCompletion
import Sanctions.Theory.Welfare.InterestGroup
import Sanctions.Theory.Welfare.PlannerZeroSanction
import Sanctions.Examples.ChordEconomyWelfareGeneral
-- Round BC (2026-09-29): the modules of the re-pinned rows and the three new rows.
import Sanctions.Theory.Certificates.StandardComplianceLocalised
import Sanctions.Theory.Basin.SenderPersistenceLow
import Sanctions.Theory.Basin.SenderPersistenceLocalisedShock
import Sanctions.Theory.Equilibrium.BranchInvarianceParams
import Sanctions.Theory.Equilibrium.DefianceCore
import Sanctions.Examples.PlacableSenderRegime10Core
import Sanctions.Examples.PlacableSenderCollapseEquilibrium
import Sanctions.Examples.PlacableSenderDefianceClosed
import Sanctions.Examples.PlacableSenderDefianceCore
import Sanctions.Examples.PlacableSenderReliefAtDefiance
import Sanctions.Examples.PlacableSenderSecurity
import Sanctions.Examples.PlacableSenderSecurityHistory
import Sanctions.Examples.PlacableSenderPatienceExistence
import Sanctions.Examples.PlacableSenderNetDefiance
import Sanctions.Examples.PlacableSenderNetDefiance10

open Sanctions Sanctions.Examples Sanctions.AbstractGame.Params
open Sanctions.AbstractGame.ShockedParams

-- ─── ROW NUMBERS IN THE COMMENTS BELOW HAVE DRIFTED (noted 2026-09-01) ───
--
-- HEADLINE-SNAPSHOT.md is authoritative; the inline `-- Row N` labels here are
-- not, and are no longer in step with it. The snapshot held 37 rows when this
-- note was written (2026-09-01) and 46 on 2026-09-11; the comments of the
-- first block below stop at 35 and index the set as it stood when each was
-- written, and rows 38 onward carry their own numbered comments further down.
-- Verified positions in the snapshot as of 2026-09-01:
--
--   34  equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn
--   35  equilibriumTop_attraction_on_derived_interval_of_invariant
--   36  equilibriumTop_derived_dual_basins        (commented below as "Row 35")
--   37  qbCert_three_goals_generalF               (no comment block below)
--
-- The offset begins at or before position 29 and the comments group rows by
-- CONTENT, not by a uniform shift, so they were deliberately NOT renumbered by
-- hand: a wrong number is worse than an absent one. Read a row number here as
-- "roughly here in the list", and take the position from the snapshot.
--
-- Do not "fix" this by shifting every label. Regenerate the mapping from
-- HEADLINE-SNAPSHOT.md, or delete the numbers and keep the descriptions.

-- Round V (2026-09-15, on the user's word; doc 87 §12): six rows retired from
-- the headline set — historical rows 6 (shocked interior existence), 10 and 11
-- (the purified P₃ existence and frontier), 19 (within-carrier uniqueness),
-- 20 (the stage-flip route certificate) and 22 (the coupled-leader concavity
-- obstruction). The theorems stay in the tree and in the supplement's
-- declaration lists; only their protected status ends. Row numbers below stay
-- historical (Rule 18 keys rows on names, not positions); the set has 41 rows.
-- Rows 1–3: three-goals headlines, ALL at a general transition. Row 2 was
-- replaced with the stronger minimum-drift shock theorem on 2026-07-17; rows
-- 1 and 3 were swapped to their `_generalF` siblings on 2026-08-08 (Rule 22),
-- and this file was not updated to match until 2026-08-09 — see the header.
/-- info: 'Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent
-- The row-2 name is too long for one 100-character `#print axioms` line, and the replay gate
-- (Audit-Round gate 6) needs the name on that line: the long-line linter is off for this command.
set_option linter.style.longLine false in
/-- info: 'Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent
/-- info: 'Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms standardCompliance_low_basin_generalF_of_sender_level
-- Rows 4–5: same-α dominance kernel; closed-form shock entry horizon.
/-- info: 'Sanctions.AbstractGame.Params.theorem2_dynamic_dominates_myopic_at_same_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem2_dynamic_dominates_myopic_at_same_alpha
/-- info: 'Sanctions.AbstractGame.Params.shockEntryHorizon_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shockEntryHorizon_bound
-- Historical row 6 (the shocked interior existence, conditional on the
-- three-condition analytic package) was retired from the headline set in
-- round V (2026-09-15); the theorem stays in the tree.
-- Rows 7–16: witness corollaries and the mechanism frontier. The conditional
-- canonical-leader wrapper is retained as a symbolic appendix template, not
-- as a headline existence result; the abstract theorem it wraps is the
-- retired row 6.
/-- info: 'Sanctions.Examples.eeCert_three_goals_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCert_three_goals_dominance
/-- info: 'Sanctions.Examples.eeCertMS_generalF_three_goals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCertMS_generalF_three_goals
/-- info: 'Sanctions.Examples.eeCertMS_three_goals_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCertMS_three_goals_dominance
/-- info: 'Sanctions.Examples.qbCertMS_generalF_three_goals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qbCertMS_generalF_three_goals
/-- info: 'Sanctions.Examples.lbLow_generalF_three_goals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lbLow_generalF_three_goals
-- Row 12b (gap closed 2026-08-21): `wobbleEconMS_three_goals_full` has been a
-- committed snapshot row and a member of the generator's headline list, but had
-- NO `#print axioms` line here — so its kernel axiom set was never replayed
-- in-build. This is the same divergence the header above records for 2026-08-09,
-- found again while adding row 36 and closed here. It is the strongest
-- non-affine row: the wobble economy bends the realised DYNAMICS, not only the
-- hypotheses.
/-- info: 'Sanctions.Examples.wobbleEconMS_three_goals_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.wobbleEconMS_three_goals_full
/-- info: 'Sanctions.Examples.b2NonMono_three_goals_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms b2NonMono_three_goals_dominance
/-- info: 'Sanctions.Examples.b2_integrated_mechanism_active_generalF_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms b2_integrated_mechanism_active_generalF_witness
/-- info: 'Sanctions.Examples.fourGroupCert_three_goals_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourGroupCert_three_goals_dominance
-- Row 17: Krylov–Bogolyubov wash-out invariant law.
/-- info: 'Sanctions.boxTransfer_existsUnique_invariant_attracting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boxTransfer_existsUnique_invariant_attracting
-- Row 18: within-carrier equilibrium uniqueness (Schur margin).
-- Row 19: stage-flip route inhabited (constructor-derived certificate,
-- general-transition three goals at the sfParams witness).
-- Row 20 (user-approved 2026-07-11): initial-condition selection as a
-- theorem — both invariant directional basins certified at one economy
-- and one equilibrium (dual-basin witness). No limit point is named:
-- the declaration proves invariance, a sanction floor/ceiling, and
-- monotone or antitone sanctions -- not convergence to an attractor.
/-- info: 'Sanctions.Examples.dualParams_initial_condition_selects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dualParams_initial_condition_selects
-- Row 21 correction (2026-07-27): the exact coupled Schur matrix remains
-- valid, but its advertised modulus-2 leader premise is false on the current
-- carriers. The obstruction `not_coupledLeaderStrongConcave` (historical row
-- 22) left the headline surface in round V (2026-09-15) and stays in the tree
-- as the Rule 11 refutation. The conditional low-delta purified wrapper was
-- demoted because it consumes rather than constructs the decisive
-- objective-geometry premises.
-- Rows 22–25 (user-approved 2026-07-24): equilibrium-feedback comparative
-- statics at the pinned value family.
/-- info: 'Sanctions.Examples.eeCertB_equilibrium_feedback_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCertB_equilibrium_feedback_decomposition
/-- info: 'Sanctions.Examples.eeCertB_equilibrium_lockin_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCertB_equilibrium_lockin_strict
/-- info: 'Sanctions.Examples.eeCertB_lockin_amplification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCertB_lockin_amplification
/-- info: 'Sanctions.Examples.eeCertB_VT_star_βS_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eeCertB_VT_star_βS_invariant
-- Rows 26–28 (user-approved 2026-07-13): the WELFARE layer, promoted to
-- headline status because R-PAPER4 made it an abstract-level claim.
-- Row 26 — the political weights ARE the distortion: for EVERY four-group
-- economy, the two governments' joint objective equals utilitarian planner
-- welfare plus the politically re-weighted group welfares, and nothing else.
/-- info: 'Sanctions.KaempferLowenberg.FourGroup.plannerW_distortion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KaempferLowenberg.FourGroup.plannerW_distortion
-- Row 27 — the flip boundary, also parametric: the sanctions lock-in corner
-- is strictly planner-dominated by the zero stationary point IFF the flow
-- gain from entrenchment falls short of the resource burn it takes to
-- sustain it, (g_J − q_K) + (b_J − b_K) < kS + d_s. Makes the welfare
-- verdict a checkable sign condition on interest-group primitives rather
-- than a fixture of one calibration.
/-- info: 'Sanctions.KaempferLowenberg.FourGroup.plannerW_lockin_dominated_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KaempferLowenberg.FourGroup.plannerW_lockin_dominated_iff
-- Row 28 — the exact discounted margin at the microfounded witness, stated
-- directly on the constructed top-selector equilibrium and its derived
-- Target/Sender action paths. The zero-sanction FEASIBLE path beats that
-- equilibrium path by exactly
-- 23/(10(1−β)) + 1/(1−β/2), for every start x₀ ∈ [0,1] and every β ∈ [0,1)
-- (the start-state dependence cancels). Both margin terms are positive, so
-- strict dominance is immediate; the strict form fgc_planner_inefficiency_lt
-- is a three-line corollary and needs no separate row.
/-- info: 'Sanctions.Examples.fgc_planner_inefficiency_equilibrium' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fgc_planner_inefficiency_equilibrium
-- Rows 29–30 (user-approved 2026-08-09): P4-free persistence. Row 29 proves
-- conclusions (i)–(iii) with the Target combined chord DELETED from the
-- hypotheses; row 30 is the primitive form, taking no arguments beyond the
-- `SymbolicEconomyF` structure. Both are strictly-weaker-hypothesis siblings
-- of rows already present — a debundling, not a new result.
/-- info: 'Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_sender_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms standardCompliance_persistence_generalF_from_sender_package
/-- info: 'Sanctions.Examples.SymbolicEconomyF.persistence_generalF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.SymbolicEconomyF.persistence_generalF
-- Rows 31–32 (user-approved 2026-08-09): the equilibrium-anchored forms. Each
-- takes an actual `FeedbackStackelbergEquilibriumTop`, so the Target policy
-- driving the trajectory is Bellman-optimal by construction (Rule 1), and each
-- attaches the per-period Target-argmax certificate along the realised path.
/-- info: 'Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_long_run_nonDecreasing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equilibriumTop_senderPersistenceF_long_run_nonDecreasing
/-- info: 'Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent
-- Row 33 (user-approved Rule-3/18 addition 2026-08-15): order-selected
-- convergence. The first headline row that says WHICH rest point an
-- equilibrium path reaches. From any start in a preserved basin, if the
-- equilibrium sanction there is at or above the state the path converges to
-- the LEAST rest point at or above it, and if at or below, to the GREATEST at
-- or below; the realised sanction converges to the rule's value at that limit.
-- The two cases are exhaustive.
--
-- Tier 1 of three, and the weakest: continuity of the realised rule is assumed
-- directly rather than derived, so the row carries no argmax-uniqueness and no
-- StrictAdjustment hypothesis. `_and_rule_limit` and
-- `equilibriumTop_tendsto_order_selected_fixedPoint` are its corollaries.
--
-- NOT an attraction row. The limit is chosen after the starting state and may
-- differ across starts; whole-basin attraction is equivalent to the basin
-- holding a unique rest point, which this does not assume or prove. It also
-- does not dominate the baseline long-run theorem, which assumes less about the
-- rule and concludes less.
/-- info: 'Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn
-- Row 34 (user-approved Rule-3/18 addition 2026-08-15): attraction on a derived
-- interval. Row 33 says WHICH steady state a single path reaches; this says every
-- path from the interval reaches the SAME one, and so does the realised sanction.
--
-- The interval runs from the basin pivot up to the FIRST steady state above it,
-- so it is derived rather than chosen, and uniqueness on it — which is exactly
-- what a common limit requires — holds by construction.
--
-- Weaker hypotheses than the corollaries beneath it: an invariant interval, a
-- monotone continuous realised rule, StrictAdjustment for the sanction half only.
-- No level condition, no floor, no persistence package.
--
-- Scope: the interval may be a single point, and nothing here establishes that
-- the steady state is interior. At the economy witnessing positive length it is
-- the corner.
/-- info: 'Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equilibriumTop_attraction_on_derived_interval_of_invariant
-- Row 35 (user-approved Rule-3/18 addition 2026-08-15, promoted together with the
-- paper claim it backs): the dividing line between the two long-run regimes is
-- derived from the equilibrium closed loop, not assumed.
--
-- Rows 33 and 34 take their interval from outside. This row derives the boundary.
-- From two named long-run states, a certified wash-out region up to xL, a
-- certified ratchet region down from xH, and NOTHING about the sign in between,
-- two steady states t ≤ t' fall out of the closed loop itself: the first state
-- where erosion stops, and the last where building stops. Every path below t
-- washes out; every path above t' ratchets; t = t' exactly when the middle holds
-- one steady state.
--
-- Weaker than rows 33/34 where it counts: NO monotonicity of the realised rule
-- anywhere, and NO StrictAdjustment. Monotonicity is precisely what is unknown
-- between two certified basins, which is what makes this usable there.
--
-- Scope: the gap [t, t'] is not claimed empty at any economy —
-- `derivedThresholds_can_differ` shows a continuous map can fix a whole
-- subinterval. Nothing makes t interior. The conclusion is about the state path,
-- not the realised sanction.
/-- info: 'Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equilibriumTop_derived_dual_basins
-- Row 36 (user-approved 2026-08-21): the first NON-AFFINE inhabitant of the
-- full compliance certificate. `StandardComplianceLocalCoreCertificate` has
-- been general in `F` since 2026-08-20b, but every one of its five instances
-- discharged the sanction chords by rewriting `F` to `affineF` — Rule 9B calls
-- that non-vacuity without generality. `quadBumpF` is refuted as affine at
-- EVERY weight, and it has a lower chord at 47/100 and an upper chord at
-- 53/100, which one rate could not give (since round BJ1.4 the certificate
-- itself carries only the Sender rate d). Full conclusion strength: basin
-- invariance, the free floor s̄ = 1/2, the pivot floor, sanction monotonicity,
-- the per-period Target-argmax certificate, statewise dominance, finite shock
-- entry. Licenses existence only (Rule 9A) — the constants are properties of
-- this economy, not of the theory.
/-- info: 'Sanctions.Examples.qbCert_three_goals_generalF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.qbCert_three_goals_generalF
-- Rows 38–40 (user-approved 2026-09-04, doc 49 §2): the placable-Sender class,
-- since round AV (2026-09-25, doc 104) the chord economy — both stage payoffs
-- abstract, read through one-sided rate bounds.
-- Row 38: the class statement — on every chord economy, given one inequality
-- (the lower rally rate covers the continuation's saturation and the
-- transition's cross-curvature), both
-- continuation channels change equilibrium behaviour at a composed top-selector
-- feedback Stackelberg equilibrium whose two values are Banach-constructed.
-- Row 39: the same, unconditional, at `quadDiagF` — a transition proved not the
-- affine law at any rate (Rule 9B generality, fenced).
-- Row 40: the general theorem behind row 38 — single crossing of the Sender's
-- dynamic objective in (sanction; state) at a value, plus state-local
-- uniqueness, give the upper dynamic response monotone in the state. Zero
-- model assumptions; a reusable comparative static.
/-- info: 'Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net
/-- info: 'Sanctions.Examples.placableQuadDiag_both_channels_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.placableQuadDiag_both_channels_active
/-- info: 'Sanctions.AbstractGame.Params.σ_dyn_top_monotoneOn_x_of_singleCrossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.AbstractGame.Params.σ_dyn_top_monotoneOn_x_of_singleCrossing

-- Rows 41-42 (2026-09-04, doc 56, user-approved). Row 41: on every chord
-- economy, given the rally margin, the fully myopic equilibrium
-- (partial compliance, zero sanction, wash-out) is constructed beside the
-- forward-looking one (defiance, interior sanction strictly above the stage
-- optimum, wash-in, strict dominance, an interior steady state with sanction
-- equal to state) -- general in F and in the payoffs. Row 42: at the affine
-- member the closed loop is a 43/46-contraction: one globally attracting
-- steady state, so both channels active does not deliver same-equilibrium
-- hysteresis there.
/-- info: 'Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_net_of_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChordEconomyRelief.myopic_dynamic_equilibrium_separation_net_of_margin
/-- info: 'Sanctions.Examples.placableAffine_unique_attracting_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.placableAffine_unique_attracting_state

-- Rows 43-44 (2026-09-05, doc 62, user-approved). Row 43: on every chord
-- economy the Target-only reading (Target forward-looking, Sender myopic) is
-- constructed: the Sender's rule is the stage optimum at defiance, defiance is
-- the Target's unique optimum, the state washes in and converges from every
-- start to a fixed point of that rule, and given the rally margin that limit
-- is strictly below the forward-looking one -- general in F and in the
-- payoffs. (The closed form u₀/(q − r) and its uniqueness are the
-- quadratic–linear family's, `PlacableEconomyF.target_only_regime_closedForm`.)
-- Row 44: at the affine dual-basin economy one equilibrium sustains both
-- regimes, and imposed full-sanction
-- and zero-sanction episodes of the canonical lengths move between them.
/-- info: 'Sanctions.Examples.ChordEconomyRelief.target_only_regime_net_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyRelief.target_only_regime_net_core
/-- info: 'Sanctions.Examples.dualParams_two_sided_regimes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.dualParams_two_sided_regimes
-- Rows 45-46 (2026-09-05, doc 65, user-approved). Row 45: the four cells on
-- every member of the enriched subclass (sanction-section semiconvexity, the
-- rally margin and the relief margin as hypotheses): the state washes out
-- under 00 and 01, converges to a positive fixed point of the stage rule under
-- 10 and to a strictly higher state under 11 -- general in F and in the
-- payoffs; the paper's Theorem 1. Row 46: the
-- Sender-only reading behind it: the Target's unique optimum is the zero
-- level, strictly above the myopic placation level, the sanction is zero and
-- the state washes out -- general in F.
/-- info: 'Sanctions.Examples.ChordEconomyCs.four_cell_net_generalF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_net_generalF
/-- info: 'Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF
-- Row 47 (round Q2, 2026-09-11; doc 85 S3, on the user's Rule-18 word): both
-- channels active on the enriched subclass under the rally margin and the
-- relief margin alone, with no stage flip -- the Target channel through a
-- small compliance at the equilibrium value, the Sender channel as in row 38.
-- The affine member `placableReliefOnly` satisfies (RL) and fails the flip,
-- so the class is strictly larger than row 38's.
/-- info: 'Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief_net

-- Rows 48-57 (round AK', 2026-09-23; doc 102 J3, on the user's word): the
-- bracket, the relief equilibrium, the collapse, the monotone-class uniqueness,
-- the all-equilibrium wedge floor, and the four round-AE/AG rows of doc 98 G9.
/-- info: 'Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp
/-- info: 'Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero
/-- info: 'Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side
/-- info: 'Sanctions.Examples.ChordEconomyCs.collapse_sides'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_sides'
/-- info: 'Sanctions.Examples.ChordEconomy.unique_equilibrium_of_rule_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.unique_equilibrium_of_rule_monotone
/-- info: 'Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone
/-- info: 'Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance
/-- info: 'Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF
-- (The row below is printed inside its namespace: the fully qualified name is
-- long enough that the axiom list wraps in a way `whitespace := lax` does not
-- absorb; the theorem is the same.)
namespace Sanctions.AbstractGame.Params
/-- info: 'Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.leader_optimal_against_history_deviation_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FeedbackStackelbergEquilibriumTop.leader_optimal_against_history_deviation_top
end Sanctions.AbstractGame.Params
/-- info: 'Sanctions.Examples.PlacableEconomyFcs.exists_completions_reversing_regime_ranking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.PlacableEconomyFcs.exists_completions_reversing_regime_ranking
/-- info: 'Sanctions.Examples.ChordEconomy.reliefPayoff_le_V_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_le_V_T
/-- info: 'Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT
namespace Sanctions.AbstractGame.Params
/-- info: 'Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone
end Sanctions.AbstractGame.Params
-- Rows 55-59 (manuscript rebuild, 2026-10-01; author decision D4: pin the forms the
-- main text states). Rows 55-56: the Target's security value in pure history-dependent
-- strategies, as minmax and as maxmin (round BD). Row 57: the balance condition is
-- inherited by a more patient Target (round BD). Row 58: no top-selector equilibrium has a
-- sanction rule that is zero at every state. Row 59: the exact collapse threshold for
-- existence of a full-defiance equilibrium, away from equality.
/-- info: 'Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast_history
/-- info: 'Sanctions.Examples.ChordEconomy.reliefPayoff_isGreatest_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_isGreatest_history
/-- info: 'Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance
/-- info: 'Sanctions.Examples.ChordEconomy.no_zero_rule_equilibrium' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.no_zero_rule_equilibrium
/-- info: 'Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le
-- Rows 60-63 (round W, 2026-10-15; the author: welfare in general abstract form, the
-- parametric and numerical cases as witnesses). 60: rescaling one group leaves the game
-- unchanged and can rank two paths for the planner. 61: zero sanctions are planner-optimal
-- when the first unit of sanction does not pay socially, for any bounded welfare flow.
-- 62: on the class under the four-case conditions, two representations reverse the
-- welfare ranking of the four constructed equilibria. 63: on the class under
-- zero-sanction neutrality, the play of every full-defiance equilibrium is
-- planner-optimal for a representation whose welfare is the Sender's payoff.
/-- info: 'Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks
/-- info: 'Sanctions.Welfare.zeroSanction_planner_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Welfare.zeroSanction_planner_optimal
/-- info: 'Sanctions.Examples.ChordEconomyCs.exists_reps_reversing_regime_ranking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyCs.exists_reps_reversing_regime_ranking
/-- info: 'Sanctions.Examples.ChordEconomy.planner_efficient_rep_at_policy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomy.planner_efficient_rep_at_policy_zero
/-- info: 'Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage
/-- info: 'Sanctions.Examples.ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sanctions.Examples.ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking
