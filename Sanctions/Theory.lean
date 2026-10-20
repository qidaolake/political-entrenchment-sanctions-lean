/-
Sanctions/Theory.lean

Aggregator for the theory layer: every definition and theorem derived
from the `Postulates/` assumption surface plus mathlib. This file
imports **every** module under `Sanctions/Theory/` (completeness
invariant, enforced by `scripts/Audit-Round.ps1` gate 2), organized by
the thematic subdirectories introduced in the 2026-07-07 restructure.

## Subfolders

| Folder | Content |
|--------|---------|
| `Theory/Bellman/` | Value-function and operator layer: Bellman T/S operators, monotone-cone preservation, verification, value classes and invariant carriers (Lipschitz balls, gain balls, asymmetric `ValueClass2`), C¹ value track, operator row-Lipschitz estimates. |
| `Theory/Equilibrium/` | Existence and selectors: joint MPE templates, feedback Stackelberg structure, corner / slaved / Perov (Schur-margin) existence, selector robustness and bistability, argmax uniqueness from concavity. |
| `Theory/Mechanism/` | The four continuation regimes. Files above `RegimeComparison/` add no postulate: profile definitions, the `C1`/`C2` reductions to stage-payoff conditions, and the constructions for the two regimes with a myopic Sender, whose existence conclusions keep the selector and carrier hypotheses displayed in their statements. `RegimeComparison/` holds the conditions the baseline does **not** imply, adopted nowhere; the directory boundary is the assumption boundary. |
| `Theory/Basin/` | Basin geography: joint sanction-preference basin, tipping (FD-wedge and stage-flip derived pivots), stage-flip certificate wiring and dischargers, relevant-action region. |
| `Theory/Certificates/` | Paper-facing certificate assembly: the carrier-local `StandardCompliance*` family (BCF, C¹, MS, Schur, low-basin), regular-economy compatibility layer, Target loss-offset mechanism, convex-value route, substituted-Target MCS. |
| `Theory/LockIn/` | Dynamics and comparators: lock-in paths, dynamic-vs-myopic comparison, long-run limit and steady-state band, deep-parameter comparative statics. |
| `Theory/Shocked/` | Atomless-purification (shocked) chain: shocked Bellman/equilibrium, slaved and interior existence, leader-Lipschitz reduction, single-crossing/value-Lipschitz/dominance/hysteresis lifts, He–Sun shock and the moving-average kernel wiring. |
| `Theory/Microfoundations/` | Interest-group polities deriving the stage primitives: Kaempfer–Lowenberg and the four-group Grossman–Helpman aggregation. |
| `Theory/Bridges/` | The JET bridge layer (`JETBridge`, `JETBridgeC1System`) plus the historical write-only `SenderResponse` interface. **The audit-48 deprecation is per-DECLARATION, not folder-wide.** The `jet_*_from_lowerSlopes` theorems consume a Target `LowerSlopeOn` and are sign-correct only under the resistance / noncompliance reading of `a`; they carry deprecation blocks at their definition sites and must not be cited for literal-compliance claims. Their sanctioned replacements — `jet_*_from_lossOffset_on`, `jet_dominance_at_equilibriumTop_audit41` — live in the same files, carry no deprecation, and are consumed by live certificate code (`Certificates/RegularEconomy.lean`). The folder was named `Legacy/` until 2026-08-11, which over-generalised the quarantine to those replacements. The canonical paper-facing route is the general-transition `standardCompliance_three_goals_local_MS_generalF` family in `Certificates/StandardComplianceMain.lean`; the affine `standardCompliance_three_goals_local_uniform_starts` family moved to `Examples/AffineInstance/ComplianceTower.lean` on 2026-08-22, and the homogeneous `standardCompliance_three_goals` wrapper was retired 2026-08-21. |
-/

-- ─── Bellman: value-function and operator layer ────────────────────
import Sanctions.Theory.Bellman.BellmanT
import Sanctions.Theory.Bellman.BellmanS
import Sanctions.Theory.Bellman.Verification
import Sanctions.Theory.Bellman.ValueLipschitz
import Sanctions.Theory.Bellman.InvariantBall
import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Bellman.InvariantLipGainBall
import Sanctions.Theory.Bellman.ChordInvariance
-- Sender analogue of the Target-side lower-slope envelope in
-- `InvariantLipGainBall`: cone preservation for `bellmanS_BCF` and cone
-- membership of the CONSTRUCTED Sender fixed point `V_S` (Rule 15).
import Sanctions.Theory.Bellman.SenderLowerSlopeCone
import Sanctions.Theory.Bellman.GainBallInvariance
import Sanctions.Theory.Bellman.LipschitzPrimitives
import Sanctions.Theory.Bellman.StrongConcaveHolder
import Sanctions.Theory.Bellman.SmoothSanctionClass
-- (`DerivativeOnS` moved to `Foundations/` 2026-07-24 per Rule 19 —
--  generic derivative infrastructure over Foundations-level objects.)
import Sanctions.Theory.Bellman.C1Val
import Sanctions.Theory.Bellman.ValueClassC1
import Sanctions.Theory.Bellman.C1BellmanSystem
import Sanctions.Theory.Bellman.OperatorRowLipschitz

-- ─── Equilibrium: existence, selectors, MPE ────────────────────────
import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.Equilibrium.StackelbergFeedback
import Sanctions.Theory.Equilibrium.HeSunMPE
import Sanctions.Theory.Equilibrium.BergeContinuity
import Sanctions.Theory.Equilibrium.JointLipschitz
import Sanctions.Theory.Equilibrium.BasinCornerExistence
import Sanctions.Theory.Equilibrium.SlavedExistence
import Sanctions.Theory.Equilibrium.PerovExistence
import Sanctions.Theory.Equilibrium.JointExistenceFromPrimitives
-- The two Target integrands agree wherever the Sender's dynamic argmax is
-- unique. Parametric in `p : Params`; moved here from
-- `Examples/C1WitnessEnvelope.lean` on 2026-08-16 (Rule 19).
import Sanctions.Theory.Equilibrium.JointIntegrandCongruence
import Sanctions.Theory.Equilibrium.TargetSelectorFromUnique
import Sanctions.Theory.Equilibrium.SelectionRobust
import Sanctions.Theory.Equilibrium.SelectorBistability
-- (`StateDependent` absorbed into `Foundations/TarskiMPE.lean` 2026-07-24
--  per Rule 19 — pure lattice templates over an arbitrary state type.)
import Sanctions.Theory.Equilibrium.ArgmaxUniquenessFromConcavity
import Sanctions.Theory.Equilibrium.SigmaParamsRefactor
-- Wave-6 (2026-07-12): parametric ε-neighborhood isolation — within-carrier
-- uniqueness upgraded to sup-norm-ε isolation (shape pins carried as
-- hypotheses; the sawtooth counterexample makes them irreducible).
import Sanctions.Theory.Equilibrium.EpsilonIsolation
import Sanctions.Theory.Equilibrium.AbsorbingTopObstruction
-- Parametric refutation of the pointwise-order monotone comparative static
-- for the leader argmax (closes the dual-Tarski route; leaves Curtat's
-- slope-order + Schauder route open).
import Sanctions.Theory.Equilibrium.LeaderArgmaxOrderRefutation
-- The MIXED-MONOTONE (twisted-order) gate, run and closed. Those pointwise
-- refutations hold the Sender continuation fixed, so they leave open a product
-- order with the Sender coordinate REVERSED. Here the Target row's own-value
-- sign is proved to hold and its cross sign is REFUTED at any configuration
-- carrying a strict Sender-response shift under the project's own strict
-- loss-offset margin. Verdict: NO-GO for the unrestricted class; carrier-local
-- orders are not addressed; the contraction route is canonical.
import Sanctions.Theory.Equilibrium.TwistedOrderGate

-- ─── Basin: geography, tipping, stage flip ─────────────────────────
import Sanctions.Theory.Basin.TransitionChords
import Sanctions.Theory.Basin.JointPreferenceBasin
-- P4-free debundling (2026-08-09): the sub-bundle of `JointPreferenceBasinTop`
-- that the three kinematic persistence conclusions actually consume. Makes the
-- manuscript's stated division of labour formally exact.
import Sanctions.Theory.Basin.SenderPersistence
import Sanctions.Theory.Basin.WeakFloorBasin
import Sanctions.Theory.Basin.DerivedFloor
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.Basin.Tipping
import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.StageFlipCertificate
import Sanctions.Theory.Basin.StageFlipDischargers
import Sanctions.Theory.Basin.StageFlipPersistence
import Sanctions.Theory.Basin.RelevantActionRegion

-- ─── Certificates: paper-facing assembly ───────────────────────────
import Sanctions.Theory.Certificates.TwoSidedRuleComparison
import Sanctions.Theory.Certificates.SelectorGeometry
import Sanctions.Theory.Mechanism.ContinuationProfile
import Sanctions.Theory.Mechanism.PrimitiveReduction
import Sanctions.Theory.Mechanism.RegimeExistence
import Sanctions.Theory.Mechanism.RegimeComparison.Conditions
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Theory.Certificates.StandardComplianceLocalDischargers
import Sanctions.Theory.Certificates.GainBallCertificate
import Sanctions.Theory.Certificates.GeneralFDischargers
import Sanctions.Theory.Certificates.StandardComplianceLocalC1
import Sanctions.Theory.Certificates.StandardComplianceMain
-- P4-free debundling (2026-08-09): the persistence-only certificate and the
-- P1–P3+P5 package. Together they make the manuscript's stated division of
-- labour — P4 yields conclusion (vi); (i)–(iii) do not need it — formally exact.
import Sanctions.Theory.Certificates.PersistenceCertificate
import Sanctions.Theory.Certificates.SenderPersistencePackage
import Sanctions.Theory.Certificates.SubpivotChordNecessity
import Sanctions.Theory.Certificates.StandardComplianceBridges
import Sanctions.Theory.Certificates.StandardComplianceSchur
import Sanctions.Theory.Certificates.StandardComplianceLowBasin
import Sanctions.Theory.Certificates.RegularEconomy
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.Certificates.ConvexValueRoute
import Sanctions.Theory.Certificates.SubstitutedTargetMCS

-- ─── LockIn: dynamics, comparators, comparative statics ────────────
import Sanctions.Theory.LockIn.LockIn
import Sanctions.Theory.LockIn.DynamicLockIn
import Sanctions.Theory.LockIn.DynamicTopLockIn
import Sanctions.Theory.LockIn.SubintervalLockIn
import Sanctions.Theory.LockIn.PersistenceMargin
import Sanctions.Theory.LockIn.DynamicStake
import Sanctions.Theory.LockIn.EscalationGap
import Sanctions.Theory.LockIn.PostEntryNonTermination
-- The EXIT half of hysteresis, mirroring LockIn.lean's entry horizon. The file
-- above proves the equilibrium never grants relief inside the basin; this one
-- proves an EXOGENOUS relief phase of an explicit finite length drives every
-- state back out. Spends StrictAdjustment's below-diagonal conjunct, which the
-- entry side never used, so no new assumption. General in F.
import Sanctions.Theory.LockIn.ReliefExit
import Sanctions.Theory.LockIn.EntryExitComparison
-- Relief exit COMPOSED with low-basin equilibrium invariance: the exit-side
-- counterpart of shock-entry hysteresis — an imposed relief phase crosses the
-- pivot, and persistence below it is then conditional on the low-basin level
-- property of the equilibrium at hand. ReliefExit stops at the crossing and says so; this
-- discharges that caveat by feeding its finite horizon into the Hassler-mirror
-- low-basin results in Certificates/StandardComplianceLowBasin.lean, which keep
-- the equilibrium path inside [0, xbar] forever after. No new assumption: the
-- low-basin level condition is a theorem parameter (Round-47 confirmation).
import Sanctions.Theory.LockIn.ReliefPersistence
import Sanctions.Theory.LockIn.RulePathF
import Sanctions.Theory.LockIn.NoCycles
import Sanctions.Theory.LockIn.LockInLimit
import Sanctions.Theory.LockIn.BasinAttraction
import Sanctions.Theory.LockIn.OffCornerResponse
import Sanctions.Theory.LockIn.LockInComparativeStatics
import Sanctions.Theory.LockIn.MyopicComparator
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.LockIn.ResponseStateMonotone
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.LockIn.LimitDependence
import Sanctions.Theory.Equilibrium.CertifiedEquilibria
import Sanctions.Theory.Equilibrium.DefianceCore
import Sanctions.Theory.Equilibrium.SecurityCore
import Sanctions.Theory.Equilibrium.BranchInvarianceParams
import Sanctions.Theory.LockIn.SenderSanctionFloorGeneralF
import Sanctions.Theory.LockIn.LocalisedShockEntry
import Sanctions.Theory.LockIn.LocalisedReliefExit
import Sanctions.Theory.Basin.SenderPersistenceLocalisedShock
import Sanctions.Theory.Basin.SenderPersistenceLow
import Sanctions.Theory.Certificates.StandardComplianceLocalised
import Sanctions.Theory.Certificates.PersistenceThreeGoals
-- The Target-reluctance channel: at a common Sender response, a
-- forward-looking Target complies no more than a myopic one, because the
-- continuation value its own compliance gives up is strictly decreasing in
-- compliance. This isolates the Target channel; on its own it does NOT
-- discharge `hRuleDom`, because the two equilibria face different Sender
-- responses. See TwoSidedForwardLooking below for the cross-response form.
import Sanctions.Theory.LockIn.TargetReluctance
-- The Sender-side mirror of TargetReluctance: a forward-looking Sender
-- sanctions strictly HARDER than a myopic one at the same Target action, under
-- a rising continuation wedge and one chord. The strict rung the Sender ladder
-- was missing -- every prior < over the stage sanction was at one economy or
-- consumed as hRuleDom. Weak step is two lines of Foundations single-crossing;
-- strict step is lt_argmax_of_improves_above. No concavity, no uniqueness.
import Sanctions.Theory.LockIn.SenderInvestment
-- The uniqueness-free strengthening of the audit-41 compliance-direction
-- route in DifferentPolicyComparator §10. That route already reaches
-- `E.α ≤ M.α` at the two equilibria's OWN Sender responses, but assumes the
-- myopic argmax is unique at each state; strengthening the wedge condition
-- from weakly to strictly decreasing removes the uniqueness hypothesis, so
-- the ordering holds for every selection from either argmax correspondence.
import Sanctions.Theory.LockIn.TwoSidedForwardLooking

-- ─── Shocked: atomless-purification chain ──────────────────────────
import Sanctions.Theory.Shocked.ShockedBellman
import Sanctions.Theory.Shocked.ShockedEquilibrium
import Sanctions.Theory.Shocked.ShockedOneStepVerification
import Sanctions.Theory.Shocked.ShockedLifetimeVerification
import Sanctions.Theory.Shocked.ShockedBorelLifetimeVerification
import Sanctions.Theory.Shocked.CoupledPerovExistence
import Sanctions.Theory.Shocked.ValidatedLocalCoupledEquilibrium
import Sanctions.Theory.Shocked.ValidatedLocalCoupledEquilibriumOnCarriers
import Sanctions.Theory.Shocked.ShockedSlavedExistence
import Sanctions.Theory.Shocked.ShockedInteriorExistence
import Sanctions.Theory.Shocked.ShockedLeaderLipschitz
import Sanctions.Theory.Shocked.ShockedRowLipschitz
import Sanctions.Theory.Shocked.HeSunShock
import Sanctions.Theory.Shocked.HeSunShockExistence
import Sanctions.Theory.Shocked.MovingAverageShock
import Sanctions.Theory.Shocked.ShockedSingleCrossing
import Sanctions.Theory.Shocked.ShockedValueLipschitz
import Sanctions.Theory.Shocked.ShockedInvariantLipBall
import Sanctions.Theory.Shocked.ShockedDominance
import Sanctions.Theory.Shocked.ShockedHysteresis

-- ─── Microfoundations: interest-group polities ─────────────────────
import Sanctions.Theory.Microfoundations.KaempferLowenbergPolity
import Sanctions.Theory.Microfoundations.FourGroupPolity
-- Wave-2 (2026-07-11, user-approved): the Becker contest layer — the
-- K-L pressure schedules DERIVED as dominant-strategy contest argmaxes
-- (consumes Foundations/BeckerContest). Its concrete non-vacuity witness
-- lives in Examples/KaempferLowenbergContestWitness, preserving the layer
-- boundary. The planner/welfare layer remains parametric here.
import Sanctions.Theory.Microfoundations.KaempferLowenbergContest
import Sanctions.Theory.Microfoundations.FourGroupPlanner
import Sanctions.Theory.Microfoundations.FourGroupPlannerStateChord
import Sanctions.Theory.Microfoundations.FourGroupPlannerOptimum

-- ─── Bridges: the JET bridge layer. Deprecation is PER-DECLARATION —
--     see the blocks inside; the `_from_lossOffset_on` siblings are the
--     sanctioned literal-compliance replacements and are live. ────────
import Sanctions.Theory.Bridges.JETBridge
import Sanctions.Theory.Bridges.JETBridgeC1System
-- Historical write-only Sender-response interface (moved from
-- `Postulates/` 2026-07-24 — zero consumers; see the file header).
import Sanctions.Theory.Bridges.SenderResponse

-- ─── The Target row of the joint row-Lipschitz matrix, general in `F`.
--     The Sender row (Theory/Bellman/OperatorRowLipschitz) was already
--     general; the Target row was affine-restricted and unconsumed. This
--     replaces `hF : p.F = affineF p.δ` by a sanction UPPER CHORD -- a net
--     weakening under Rule 13's de-affining clause, since affine implies the
--     chord and the converse fails.
import Sanctions.Theory.Bellman.GeneralFOperatorRow

-- ─── Where the Sender-myopic column severs the loop, and how far that reaches.
--     At `β_S = 0` the Sender's forward-looking objective is POINTWISE EQUAL to
--     its stage payoff, so the Sender's best-reply set does not read `V_S` at
--     all -- the circle that blocks regimes `01`/`11` is absent, not merely
--     smaller. The SET identity is free; the SELECTOR identity `σ_dyn_top = σ`
--     is NOT implied by it and remains a Rule-3 stop.
import Sanctions.Theory.Mechanism.RegimeSelectorBridge
-- The continuation STAKES, named once: both discounted values vary across the
-- state. Renamed from MechanismActive on 2026-09-02 after the JET audit noted
-- the name overclaimed -- "mechanism-active" was already the paper's word for
-- the stronger, behavioural property. A definition with witnesses and no
-- universal: a constant-value economy is a legitimate Params.
import Sanctions.Theory.Mechanism.ContinuationStakes
-- The behavioural mechanism, named: the continuation term CHANGES which action
-- is optimal, on each side. Concluded by the strict ordering theorems
-- (TargetReluctance, SenderInvestment); discharged at ceParams, eeCertParams,
-- strictReluctanceParams and maParams. This is what mechanism-active means.
import Sanctions.Theory.Mechanism.ContinuationChangesChoice
import Sanctions.Theory.Mechanism.ZeroDiscountSelector
import Sanctions.Theory.LockIn.RegimePathBounds
import Sanctions.Theory.LockIn.FiniteEpisodePersistence
import Sanctions.Theory.Equilibrium.TopLifetimeVerification
-- Step 2 (2026-10-10): the Sender's stake as a signed parameter. How far the Sender's value falls
-- under a
-- hostile stake bound, and the reverse wedge, cheaper relief price, residual floor and lower paths
-- it gives.
-- Hypotheses 3-4 of the 2026-10-10 approval (rare case: a Sender hostile to hard-liners).
import Sanctions.Theory.Bellman.SenderUpperSlopeCone
import Sanctions.Theory.LockIn.SenderStakeSign
-- Round D (2026-10-12): a state-free Sender stage payoff gives zero sanctions at full defiance.
import Sanctions.Theory.Welfare.RepresentativeSender
import Sanctions.Theory.Welfare.InterestGroup
import Sanctions.Theory.Welfare.PlannerZeroSanction
