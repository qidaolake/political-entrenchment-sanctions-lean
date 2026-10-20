/-
Sanctions/Examples.lean

Complete umbrella for the constructed economies, non-vacuity witnesses,
counterexamples, and comparative-static applications. The audit gate checks
that every module under `Sanctions/Examples/` appears here.

The package layering is:

  Foundations → Postulates → Theory → Examples.

Examples may import one another to reuse a previously constructed economy, but
no Foundations, Postulates, or Theory module may import an Example.
-/

-- Shared construction utilities and baseline economies.
import Sanctions.Examples.WitnessKit
import Sanctions.Examples.EatonEngersWitness
import Sanctions.Examples.JointPositiveSanctions
import Sanctions.Examples.WeakFloorContainmentCounterexample
import Sanctions.Examples.SubstantiveComplianceWitness

-- Paper-facing certificate economies and their integrated applications.
import Sanctions.Examples.EECertWitness
import Sanctions.Examples.EECertWitnessMS
import Sanctions.Examples.EECertMechanismActiveApplication
import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Examples.ReflectionSymmetricWitness
import Sanctions.Examples.QuadBumpTransitionChords
-- First instance of the general-`F` Sender lower-slope cone
-- (`bellmanS_BCF_preserves_lowerSlopeCone_generalF`), at `qbParams`'s
-- non-affine `quadBumpF`.  Before it, that theorem had no instance at all.
import Sanctions.Examples.QuadBumpSenderCone
-- `quadBumpF`'s bump vanishes at full sanction, so its REALIZED corner
-- recursion `x' = F(x,1)` is still affine. `wobbleF` deletes the transience
-- factor: its corner section is a genuine parabola, it carries a strictly
-- two-sided state band `[3/10, 1/2]`, and no `γ` makes it `CornerSectionTop`.
import Sanctions.Examples.WobbleCornerCertWitness
import Sanctions.Examples.GeneralFMarginFeasibility
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralF
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFEmbedding
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFCertificate
-- doc 104 (round AU): the chord economy — the placable-Sender class with both
-- stage payoffs abstract, read through one-sided rate bounds; the
-- quadratic–linear family is an instance through `toChord`.
import Sanctions.Examples.ChordEconomy
import Sanctions.Examples.PlacableSenderFamilyF
import Sanctions.Examples.PlacableSenderEquilibrium
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Examples.PlacableSenderWitnesses
import Sanctions.Examples.QuadBumpFiniteEpisode
import Sanctions.Examples.DualBasinTwoSidedRegimes
import Sanctions.Examples.PlacableSenderRegime10
import Sanctions.Examples.PlacableSenderOpenBox
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderNoCycles
-- ROLE: FLIP-FREE ACTIVATION. Both channels active on the enriched subclass
-- under the rally and relief margins alone (round Q2; headline row 47), and
-- the affine member satisfying (RL) but not the stage flip.
import Sanctions.Examples.PlacableSenderReliefActivation
-- doc 68 (round D): the boundary member at which the constructed Sender-only
-- equilibrium has the Target fully complying (complete relief is not partial
-- compliance on the family: Rule 9, existence only); the economy at which the
-- loss-offset margin fails and defiance is still the unique optimum (the
-- margin is sufficient, not necessary); the finite-episode theorem on the
-- family's constructed equilibrium with pivot and floor u₀/q.
import Sanctions.Examples.PlacableSenderBoundaryMember
import Sanctions.Examples.LossOffsetConverseCounterexample
import Sanctions.Examples.PlacableSenderEpisode
import Sanctions.Examples.PlacableSenderEqualityMember
import Sanctions.Examples.PlacableSenderSharpReliefMember
-- Round J (doc 77): the floor-refined loss-offset member (v = 1199/300, inside
-- the family's loss-offset class and outside the previous one), and the member
-- at which the rally margin binds with a positive left side on a transition
-- with concave state sections (quadDiagF with its arguments swapped).
import Sanctions.Examples.PlacableSenderFloorMember
import Sanctions.Examples.PlacableSenderRallyBindingMember
-- Round K (doc 78 L1): the stage-signs counterexample — an optimising economy with
-- the maintained stage signs at which the substituted Sender objective is not
-- interval-dominant, so P3 (A1) does not follow from stage complementarity.
import Sanctions.Examples.StageSignsNotIDOCounterexample
-- Round L (doc 80 M9): the loose-modulus member — `placableQuadDiag` re-certified
-- with `M_cx = 4`, at which the rally margin fails while the (unchanged) response
-- is monotone: (RM) is a certificate condition, not necessary on the class.
import Sanctions.Examples.PlacableSenderLooseModulusMember
-- Round M (doc 82 P4): the persistence-package nonuniqueness witness — every
-- field of the Sender persistence package at an economy whose equilibrium closed
-- loop is the identity: persistence holds, no common limit exists.
import Sanctions.Examples.PersistencePackageNonuniqueWitness
import Sanctions.Examples.PlacableSenderLowBasin
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFRecovery
-- Argument-free primitive persistence (2026-08-09): the family's persistence
-- theorem needs neither the strict pivot nor the strict placation margin, so it
-- certifies members (e.g. `wobbleEconF`) that the MS route provably cannot.
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFPersistence
import Sanctions.Examples.B2NonMonotoneCertWitness
import Sanctions.Examples.B2GeneralFPersistenceWitness
import Sanctions.Examples.LowBasinCertWitness
import Sanctions.Examples.LowBasinSeparationWitness
import Sanctions.Examples.StageFlipCertWitness
import Sanctions.Examples.FourGroupCertWitness
import Sanctions.Examples.StandardCompliancePolynomialSkeleton

-- General-transition and off-corner equilibrium constructions.
import Sanctions.Examples.NonAffineCornerWitness
import Sanctions.Examples.NonAffineInteriorWitness
import Sanctions.Examples.OffCornerNonVacuity
import Sanctions.Examples.NonAffineMechanismActiveWitness
import Sanctions.Examples.NonAffineSenderChannelCounterexample
import Sanctions.Examples.NonAffineSenderStakeRefutation
-- A non-affine economy in which the myopic and forward-looking Target
-- maximizers are provably DISTINCT (3/4 against 2/3), witnessing that the
-- strict Target-reluctance ordering is not vacuous.
import Sanctions.Examples.StrictTargetReluctanceWitness
-- Rule-11 refutation: the four sign conditions (both Sender responses fall in
-- compliance, the forward-looking one is the harder, the Target's payoff rises
-- in the sanction) do NOT determine the sign of the Sender-response-switch
-- channel. An extra response-gap or curvature condition is logically required.
import Sanctions.Examples.SenderSwitchSignUndetermined
-- Rule-11 refutation: the infimum of a self-sustaining set does NOT characterize
-- it. Even a constant rule -- monotone, continuous, feasibility-preserving --
-- has a self-sustaining set bounded above, so pointwise rule dominance gives the
-- SET INCLUSION and the infimum ordering, and stops short of a basin boundary.
import Sanctions.Examples.SelfSustainingInfNotCharacterizing
-- Rule-11 refutation at the level of an ACTUAL GAME: an economy whose transition
-- is strictly concave in the sanction (non-affine at every delta, with genuine
-- inheritance dF/dx >= 1/4) in which the forward-looking Target complies
-- STRICTLY MORE than the myopic one -- alpha_MM = 0 < 1 = alpha_FF. Both Bellman
-- equations hold exactly and the Sender value is LINEAR, so the adverse
-- Sender-switch channel is produced by the transition's curvature alone. The
-- strictly-decreasing-wedge condition also fails here, so it is a real
-- restriction rather than something the primitives supply.
import Sanctions.Examples.AffineChordKnifeEdge
import Sanctions.Examples.BaselineTwoSidedOrderingUndetermined
-- The strict ordering at a CONSTRUCTED forward-looking equilibrium over a
-- non-affine transition: it complies 1/2 while EVERY myopic equilibrium of the
-- same economy complies strictly more. No wedge condition -- that route is
-- blocked by the refutation above. NOTE the Sender channel is inert here
-- (V_S = 0, so the two Sender responses coincide); this witnesses the
-- Target-continuation channel only.
import Sanctions.Examples.EquilibriumStrictReluctanceWitness

-- Purified-shock and quantitative persistence applications.
import Sanctions.Examples.MechanismWitness
import Sanctions.Examples.MechanismWitnessShocked
import Sanctions.Examples.MechanismWitnessShockedDominance
import Sanctions.Examples.MechanismWitnessShockedUnconditional
import Sanctions.Examples.P3WeakFloorSpreadBound
import Sanctions.Examples.P3SubBasinMonotonicity
import Sanctions.Examples.P3SpreadPinned
import Sanctions.Examples.PerpetualSanctionExistence
import Sanctions.Examples.PerpetualSanctionInterval
import Sanctions.Examples.CoupledRoute.LowDeltaWindowWitness
import Sanctions.Examples.CoupledRoute.LowDeltaLocalBranches
import Sanctions.Examples.CoupledRoute.LowDeltaLocalQuadraticBranches
import Sanctions.Examples.CoupledRoute.LowDeltaStaticStackelberg
import Sanctions.Examples.CoupledRoute.LowDeltaSubpivotChordObstruction
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPerturbation
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenReferenceCenter
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenResidual
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenStageLipschitz
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyReferenceCenter
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCenterResidual
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyTargetResidual
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCenterBudget
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyExpandedPerovBudget
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCarrierPacket
import Sanctions.Examples.CoupledRoute.LowDeltaCarrierLocalTargetRow
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyTargetSelectorFrontier
import Sanctions.Examples.CoupledRoute.LowDeltaCarrierLocalEquilibriumFrontier
import Sanctions.Examples.CoupledRoute.LowDeltaLocalizationFloorCounterexample
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenSharpResidual
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenCoupledLocalization
import Sanctions.Examples.CoupledRoute.LowDeltaRefinedTargetLocalization
import Sanctions.Examples.CoupledRoute.LowDeltaRefinedPerovBudget
import Sanctions.Examples.GeneralFNonLipschitzCounterexample
import Sanctions.Examples.CrossStepWithoutMonotoneRule
import Sanctions.Examples.GeneratedChordStrictlyWeaker
import Sanctions.Examples.MyopicPolicyNotAntitone
import Sanctions.Examples.SelectorShapeNotPreserved
import Sanctions.Examples.TransitionShapeNotPreserved

-- Interest-group microfoundations and welfare.
import Sanctions.Examples.FourGroupWitness
import Sanctions.Examples.FourGroupPlannerWitness
import Sanctions.Examples.FourGroupWelfareSign
import Sanctions.Examples.PlacableSenderWedge
import Sanctions.Examples.PlacableSenderWelfareCompletion
import Sanctions.Examples.PlacableSenderReliefParticipation
import Sanctions.Examples.PlacableSenderBranchInvariance
import Sanctions.Examples.PlacableSenderWedgeSharp
-- Round AJ (2026-09-22): the least Riccati modulus and the two-sided Target
-- value on the placable family (the affine satellites of that round were
-- retired in round AS, 2026-09-23, doc 102).
import Sanctions.Examples.PlacableSenderLeastModulus
import Sanctions.Examples.PlacableSenderTargetLipschitz
-- Round AM (2026-09-22): all-equilibrium statements through certified carriers.
-- Rounds AQ-AS (2026-09-23): the general-transition bracket, its witnesses,
-- uniqueness in the monotone class, and the satellites (doc 102).
import Sanctions.Examples.PlacableSenderAllEquilibria
import Sanctions.Examples.PlacableSenderBracket
import Sanctions.Examples.PlacableSenderBracketWitnesses
import Sanctions.Examples.PlacableSenderUniqueness
import Sanctions.Examples.PlacableSenderDefianceValues
import Sanctions.Examples.PlacableSenderDefianceCore
import Sanctions.Examples.PlacableSenderSecurity
import Sanctions.Examples.PlacableSenderSecurityHistory
import Sanctions.Examples.PlacableSenderReliefAtDefiance
import Sanctions.Examples.PlacableSenderDefianceEpisode
import Sanctions.Examples.PlacableSenderDefianceEquilibriaWelfare
import Sanctions.Examples.PlacableSenderPatienceExistence
import Sanctions.Examples.PlacableSenderCollapseEquilibrium
import Sanctions.Examples.PlacableSenderCollapseWitness
import Sanctions.Examples.ChordEconomyTightChords
import Sanctions.Examples.ChordEconomyBaseOnlyWitness
import Sanctions.Examples.PlacableSenderBranchInvarianceParams
import Sanctions.Examples.PlacableSenderRegime10Core
import Sanctions.Examples.AffineInstance.LockInShockedGeneralFBridge
import Sanctions.Examples.PreBasinAscentStrictness
import Sanctions.Examples.PlacableSenderBracketSatellites
import Sanctions.Examples.PlacableSenderWelfareInterval
-- doc 104 sign-off M9 (round AV): uniqueness on the relief side in the carrier
-- class, and tier 2 (a monotone rule from conditions on the policy alone).
import Sanctions.Examples.PlacableSenderReliefUniqueness
import Sanctions.Examples.PlacableSenderPolicyClass
-- doc 104 section 6 (round AW): a chord economy non-affine in every coordinate
-- (quartic Sender payoff, nonlinear Target payoff, quadDiagF, Berge selector).
import Sanctions.Examples.ChordEconomyQuarticWitness
import Sanctions.Examples.KaempferLowenbergWitness
import Sanctions.Examples.KaempferLowenbergContestWitness
-- Round 2026-10-03 (second ChatGPT review, Lean batch A): a kit for explicit
-- equilibria (quadratic values, the clip-vertex selector lemma, contraction
-- uniqueness); the exact window of the affine family, with both endpoint iffs and
-- a continuum of equilibria at a Target discount strictly inside it (affine-only,
-- Rule 22: F = x/2 + s/2); the closed defiance threshold (general F); a
-- defiance-core witness outside the chord class; and a strict interior
-- equilibrium inside the chord class (both existence-only witnesses, Rule 9).
import Sanctions.Examples.ExplicitEquilibriumKit
import Sanctions.Examples.AffineWindowContinuum
import Sanctions.Examples.AffineWindowBoundaries
import Sanctions.Examples.PlacableSenderDefianceClosed
import Sanctions.Examples.DefianceCoreOutsideChordWitness
import Sanctions.Examples.QuadraticComplianceInterior
-- Round BF (2026-10-03, on the author's word): the exact thresholds in the Target's
-- discount factor in general form (the exact relief test, a monotone relief value,
-- inheritance and closure in beta_T, the two intervals; general F), and the affine window
-- as an instance of them.
import Sanctions.Examples.PlacableSenderExactThresholds
import Sanctions.Examples.AffineWindowInstance
import Sanctions.Examples.PlacableSenderCollapseInstance

-- Comparative statics, selection, and law-of-motion applications.
import Sanctions.Examples.ComparativeStaticsWitness
import Sanctions.Examples.FeedbackComparativeStatics
import Sanctions.Examples.ClosedLoopInvariantLaw
import Sanctions.Examples.C1WitnessEnvelope
import Sanctions.Examples.EpsilonIsolationWitness
import Sanctions.Examples.DualBasinSelectionWitness

-- Obstructions, counterexamples, and scope diagnostics.
import Sanctions.Examples.CoupledRoute.CoupledSchurWitness
import Sanctions.Examples.CoupledRoute.LowDeltaLocalPerovBudget
import Sanctions.Examples.CoupledRoute.CoupledFrontierCounterexamples
import Sanctions.Examples.CoupledRoute.CoupledObjectiveDifference
import Sanctions.Examples.CoupledRoute.CoupledCarrierRedesign
import Sanctions.Examples.CoupledRoute.CoupledCarrierRedesignCounterexamples
import Sanctions.Examples.CoupledRoute.LowDeltaRealizedIDO
import Sanctions.Examples.DeterministicInteriorObstruction
import Sanctions.Examples.DeterministicStrictEscalation
import Sanctions.Examples.ContinuationDrivenEscalation
import Sanctions.Examples.JointBellmanNotOrderHom
import Sanctions.Examples.JointIterationCycleWitness
import Sanctions.Examples.StageFlipInfeasibility
import Sanctions.Examples.SignConditionsInsufficient
-- The symbolic certificate-bearing family: free payoff coefficients, an
-- admissible region carved out by inequalities alone, and non-emptiness
-- proved by `exists_between` / `exists_gt` chaining.
import Sanctions.Examples.SymbolicCertifiedFamily
-- Non-vacuity and separation witnesses for the `V_S`-free sanction floor.
-- Both economies are proved DEGENERATE (`w_not_a_game`, `q_not_a_game`):
-- the Sender's payoff does not depend on the Target's action.
import Sanctions.Examples.SenderConeWitness

-- The affine transition as a worked instance (moved out of `Theory/` on
-- 2026-08-20d, Rule 22). Nothing here is new mathematics: trajectory bridges
-- between the affine and general-`F` families, the chord discharges the affine
-- law satisfies at equality, the affine recoveries of the general certificate
-- theorems, and the two microfoundation bridges that produce the affine law.
import Sanctions.Examples.AffineInstance.Kinematics
import Sanctions.Examples.AffineInstance.EntryExitComparison
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.Microfoundations

-- The rest of the affine tower, moved out of `Theory/` on 2026-08-22 (Rule 22).
-- Eighty-one declarations that carry `hF : p.F = affineF p.delta`: the sanction
-- monotonicity and Lipschitz bridges, the standard-compliance certificate tower
-- in all its affine variants, and the lock-in / shocked route. Each has a
-- general-`F` sibling in `Theory/`; no headline theorem reaches any of these.
import Sanctions.Examples.AffineInstance.Bridges
import Sanctions.Examples.AffineInstance.ComplianceTower
import Sanctions.Examples.AffineInstance.LockInShocked

-- Non-vacuity and necessity witnesses for the two-sided chord carrier (moved
-- out of `Theory/Bellman/ChordInvariance.lean` on 2026-08-22, Rule 22). The
-- non-affine corner section that inhabits the class outside the affine case,
-- and the escape refutation making the interval side condition necessary.
import Sanctions.Examples.ChordInvarianceWitnesses

-- Why the sanction chords are NOT derivable from the five transition
-- primitives: a flat transition admits no positive lower chord, and the
-- square-root mean transition admits no finite upper chord.
import Sanctions.Examples.ChordNotDerivable


-- ## Witnesses relocated out of Foundations (2026-08-27)
--
-- These carry no general content. Each exists to show that some Foundations
-- theorem's hypotheses are inhabited, that its bound is attained, that a
-- dropped hypothesis is genuinely load-bearing, or that a converse fails.
-- Rule 9: a witness is an existence certificate and nothing more, so it must
-- not sit in the library whose theorems it certifies.

-- ROLE: FAILURE OF IMPLICATION. A symbolic two-branch quadratic family
-- separating interval dominance from single crossing.
import Sanctions.Examples.Math.TwoBranchQuadraticSlice

-- ROLE: COUNTEREXAMPLE. A one-sided jump self-map of [0,1] with no fixed
-- point, showing why the monotone fixed-point results need their continuity
-- or order-closure side condition.

-- ROLE: CERTIFICATE COMPUTATION. Exact moving-average integrals over affine
-- and piecewise-affine cells, including the clipped boundary layers, used to
-- discharge numeric certificate obligations.

-- ROLE: FAILURE OF CONVERSE. The pair showing the cardinal gap condition is
-- strictly stronger than the ordinal single-crossing relation it implies.
import Sanctions.Examples.Math.BinaryComparativeStaticsStrictness

-- ROLE: SHARPNESS. The families attaining the two bounds that could otherwise
-- be suspected of slack: the sqrt-rate argmax displacement, and the
-- Schur-complement semiconcavity modulus (with the refutation showing its
-- action-concavity hypothesis is load-bearing).
import Sanctions.Examples.Sharpness.ArgmaxSupNorm
import Sanctions.Examples.Sharpness.SemiconcaveSup

-- ROLE: FAILURE OF CONVERSE (scope). Why the chord predicates are quantified
-- over the feasible square and not the plane.
import Sanctions.Examples.Counterexamples.TransitionChordScoping

-- ROLE: FAILURE OF CONVERSE (attained bound). The corner-chord bound
-- `d ≤ 1 − γ` is attained off the affine law, so equality does not force
-- the law affine (round Q1; the reader's C03–C04).
import Sanctions.Examples.Counterexamples.CornerChordAttained

-- ROLE: FUNCTIONAL-FORM ILLUSTRATION. The affine law discharging every chord
-- predicate -- non-vacuity of the class, and NOT evidence of its generality
-- (Rule 22): it is the member whose two chord rates coincide.
import Sanctions.Examples.AffineInstance.TransitionChords

-- ROLE: NECESSITY. The lower chord is not decorative; the band is not the
-- affine class in disguise; the composition modulus is attained.
import Sanctions.Examples.Counterexamples.SemiconcaveComposition

-- ROLE: FUNCTIONAL-FORM ILLUSTRATION, and NECESSITY. The affine degeneracy of
-- the semiconcave Riccati recursion, and the refutation showing the
-- continuation's monotonicity is load-bearing rather than a regularity
-- convenience.
import Sanctions.Examples.AffineInstance.SemiconcaveRiccati
import Sanctions.Examples.Counterexamples.SemiconcaveRiccatiMonotone
-- doc 68 (round D): a chord at a non-greatest stage maximiser does not put
-- every dynamic maximiser above every stage maximiser (refutes the
-- over-quantified reading of the strict Sender comparison; Rule 9).
import Sanctions.Examples.Counterexamples.TiedStageMaximizers
import Sanctions.Examples.Counterexamples.EndpointFloorRule

-- ROLE: GENERALITY WITNESS (Rule 9B). The single-crossing and cross-order
-- relations instantiated on an integer chain with integer values, so the
-- generalization off `ℝ` is exhibited rather than asserted.
import Sanctions.Examples.Order.IntegerChain

-- ROLE: REFUTING WITNESS (Rule 9A(2)). `min x s` satisfies every transition
-- field of `Params` (mem, continuity, monotone in each argument, F x x = x),
-- depends on BOTH arguments, and yet every threshold CDF it induces is
-- submodular -- so Curtat's (A8) is NOT unavailable across the transition
-- class, as this project's notes had asserted. The verdict for the model is
-- unchanged: the transitions actually used grow strictly in both arguments.
import Sanctions.Examples.MinLawSubmodularityWitness

-- ROLE: NON-VACUITY WITNESS (Rule 9B). HeSunShockParams -- the concrete
-- He-Sun shock layer, an economy plus an idiosyncratic state-shock kernel --
-- had ZERO inhabitants anywhere in the tree, so every shocked result above it
-- was stated over a class nobody had shown was non-empty. Uniform box noise
-- on [-h,h] supplies the kernel and its probability-measure obligation.
-- Licenses inhabitation ONLY: no shocked theorem is discharged at it, and it
-- is not a generality-in-F witness.
import Sanctions.Examples.HeSunShockWitness
-- Step 2 (2026-10-10), JET preparation. Headline results under the net-of-compliance defiance
-- condition
-- (cases 11 and 10; three members where it holds and the loss-offset condition fails).
import Sanctions.Examples.PlacableSenderNetDefiance
import Sanctions.Examples.PlacableSenderNetDefiance10
import Sanctions.Examples.PlacableSenderNetDefianceWitnesses
-- The Sender's stake of either sign: the stake-shift transfer for cases 00 and 10, the hostile
-- class corollaries
-- and the sharp witness (rare case: hostile Sender; the witness is at one example economy only).
import Sanctions.Examples.SenderStakeShift
import Sanctions.Examples.HostileSenderClass
import Sanctions.Examples.HostileSenderWitness
-- The linear-quadratic benchmark: relief iff beta_T <= beta_T*, full defiance iff beta_T >=
-- beta_T*, the continuum at
-- the threshold, comparative statics, the relief side of the collapse, and the non-uniqueness
-- witness above beta_T*.
import Sanctions.Examples.LQBenchmark
import Sanctions.Examples.LQThresholdContinuum
import Sanctions.Examples.LQAboveThresholdWitness
import Sanctions.Examples.CollapseReliefThreshold
-- Classification of affine-policy, quadratic-value equilibria (not general: that class only; n =
-- 0) and existence on
-- the whole window at the affine-window member (one example economy only).
import Sanctions.Examples.LQAffineQuadClass
import Sanctions.Examples.AffineWindowWhole
import Sanctions.Examples.DualBasinNationalWelfare
import Sanctions.Examples.ChordEconomyWelfareGeneral
import Sanctions.Examples.ChordSelectorSquare
