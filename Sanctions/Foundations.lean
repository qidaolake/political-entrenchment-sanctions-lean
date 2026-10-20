/-
Sanctions/Foundations.lean

Aggregator for the foundations layer: math utilities with no
project-specific economic content.

**Convention:** theorems whose substantive mathematical content comes
from *outside sources* (papers cited in `PaperRefer/MathTheory/`,
mathlib extensions) live in this layer. The application of these
theorems to the abstract dynamic game (`Sanctions.AbstractGame.Params`)
lives in `Sanctions.Theory.*`.

Examples:
* `MilgromShannon` — Milgrom & Shannon (1994) Thm 4 (quasi-supermodular
  + single-crossing → monotone argmax in strong-set order).
* `IntervalDominanceOrder` — Quah–Strulovici (2007) interval dominance
  order (scalar specialisation), with a `SingleCrossingOn`-producing
  composite discharger keyed off choice-axis strict monotonicity
  alone (no α-monotonicity needed). Used to shrink the `hSC_on`
  primitive on the non-saturated regime.
* `HeSunMPE` — Skolemization step used inside He-Sun's deterministic
  specialization (given per-state ∃-argmax, extract a global stationary
  policy via classical choice). The abstract specialization in
  `Theory/Equilibrium/HeSunMPE.lean` combines this with `p.σ_isMaxOn_U_S`
  to deliver a `StaticSenderStationaryProfile` (a genuine coupled MPE
  exactly when the equilibrium Sender response coincides with the
  stage argmax, e.g. β_S = 0; otherwise a static-Sender projection).
  Full He-Sun Thm 1 for stochastic kernels (Dynkin-Evstigneev
  measurable selection on a policy-profile correspondence) is open
  future work.
* `Topkis` — Topkis (1998) Ch 2 core results: strong set order,
  supermodular argmax sublattice, monotone selection from increasing
  correspondence.
* `StokeyLucas` — Stokey-Lucas-Prescott (1989) Banach contraction
  fixed-point + abstract Bellman-preservation theorem (Thm 4.6 family).
* `MultistageGames` — Krawczyk-Petkov verification theorem and abstract
  Stackelberg feedback equilibrium structure.
* `Supermodular`, `TopkisDD` — older Topkis 1978 / Milgrom-Roberts 1990
  supermodular-games machinery (kept for backwards compatibility; the
  newer `Topkis` module subsumes / extends some of this content).
* `SupDiff` — sup-difference inequality used in Bellman contraction.
* `SemiconcaveSup` — partial maximisation over a convex, state-independent
  action set preserves semiconcavity, with the **Schur-complement** modulus
  `σ + ρ²/q` (state curvature plus cross term squared over action
  concavity), not the state modulus alone. Includes the exactness witness
  on the quadratic model and the counterexample showing strict action
  concavity cannot be dropped.
* `SemiconcaveComposition` — the chord-form **composition** rule: a
  monotone, Lipschitz, semiconcave value composed with a transition
  section whose sanction chords lie in a two-sided band `[dlo, dhi]`
  (`dlo ≥ 0`) and which is itself semiconcave in the sanction is
  semiconcave with modulus `Σ·dhi² + K·M`. No derivatives, so genuinely
  non-affine transitions qualify. Includes the Lean refutation showing
  the upper chord alone is **not** enough (the squaring step needs a
  two-sided bound), and the sharpness witness for `Σ·dhi²`.
* `SemiconcaveRiccati` — the **fixed-point** layer over
  `SemiconcaveComposition`: reading the composition rule along the *state*
  coordinate, adding the stage payoff, and closing the recursion
  `Sg ↦ ψ + β·(Sg·ghi² + K·M_state)`.  Ships the closed form
  `bellmanSemiconcaveConstant β ghi ψ K M_state = (ψ + β·K·M_state)/(1 − β·ghi²)`
  — the fourth member of the family alongside `bellmanLipConstant`,
  `bellmanLowerSlopeConstant` and `bellmanNormBound` — proves it is a
  **stationary point** of the recursion (equality, not merely a bound) and
  the **least** invariant modulus, and records the refutation showing the
  continuation's monotonicity cannot be dropped.
* `Basic` — the layer's entry point; re-exports the domain layer
  (`Sanctions/Domain/UnitInterval.lean`), which owns `I` and `S`.
-/

-- The domain layer sits below this one and is pulled in through `Basic`:
-- the state space `[0,1]`, the projection `clipS` / `clipS'` onto it, and the
-- derivative-on-`S` primitives all live in `Sanctions/Domain/` since
-- 2026-08-27. Twelve modules in this layer are stated over `S`; that is a
-- specialization of reusable operator theory to the project's interval, and
-- the import records it rather than hiding it in a build prelude.
import Sanctions.Foundations.Basic
import Sanctions.Foundations.SupDiff
import Sanctions.Foundations.SemiconcaveSup
import Sanctions.Foundations.SemiconcaveJointComposition
import Sanctions.Foundations.SemiconvexComposition
import Sanctions.Foundations.CrossDifferenceSemiconvex
import Sanctions.Foundations.SingleCrossingOfIncreasingDifferences
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.TightChords
import Sanctions.Foundations.SemiconcaveComposition
import Sanctions.Foundations.SemiconcaveRiccati
import Sanctions.Foundations.Supermodular
import Sanctions.Foundations.TopkisDD
import Sanctions.Foundations.MilgromShannon
import Sanctions.Foundations.IntervalDominanceOrder
import Sanctions.Foundations.HeSunMPE
import Sanctions.Foundations.FixedPointPerturbation
import Sanctions.Foundations.TiltStability
import Sanctions.Foundations.Topkis
-- A strictly concave function has at most one maximiser: the abstract content
-- behind both `DynamicArgmaxUnique` and `TargetArgmaxUnique`. Added 2026-08-17.
import Sanctions.Foundations.ConcaveArgmax
import Sanctions.Foundations.StokeyLucas
import Sanctions.Foundations.MonotoneAttraction
import Sanctions.Foundations.Hinderer
import Sanctions.Foundations.MultistageGames
import Sanctions.Foundations.InfiniteHorizonVerification
import Sanctions.Foundations.HistoryDependentDeviations
import Sanctions.Foundations.HistoryDependentSecurity
import Sanctions.Foundations.DiscountedExtremum
import Sanctions.Foundations.DiscountedChordSum
import Sanctions.Foundations.FiniteDiscountedTelescope
import Sanctions.Foundations.DiscountedSignCharacterization
import Sanctions.Foundations.QuadraticArgmaxLowerBound
import Sanctions.Foundations.FeynmanKacVerification
import Sanctions.Foundations.FiniteBranchMax
import Sanctions.Foundations.ShockedVerificationBoundary
import Sanctions.Foundations.Curtat
import Sanctions.Foundations.ImplicitFunctionTheorem
import Sanctions.Foundations.ArgmaxSensitivity
import Sanctions.Foundations.DiagonalMonotone
-- Why the estimate above needs a bound on the *slope* of the perturbation and
-- not merely its size: with sup-norm closeness alone the same proof yields a
-- square root, so sup-norm closeness by itself does not supply a linear
-- selector-sensitivity estimate, however strongly concave the payoff is.
-- Special games or restricted carriers can still have one: the slope-bounded
-- (C1) carrier and the derivative-free objective-difference route
-- (`ArgmaxGapStability`, `StrongConcaveArgmaxStability`) supply different
-- sufficient inputs. A rate obstruction, not an existence statement (wording
-- corrected 2026-09-11, the reader's C13).
import Sanctions.Foundations.ArgmaxSupNormLimit
import Sanctions.Foundations.ArgmaxGapStability
import Sanctions.Foundations.StrongConcaveArgmaxStability
import Sanctions.Foundations.QuadraticGrowthPerturbation
import Sanctions.Foundations.Berge
import Sanctions.Foundations.BalbusReffettWozny
import Sanctions.Foundations.VivesLattice
import Sanctions.Foundations.PerovContraction
import Sanctions.Foundations.ValidatedLocalPerov
import Sanctions.Foundations.ValidatedLocalPerovOnCarriers
import Sanctions.Foundations.MonotoneThreshold
-- Discount-factor comparative statics for stationary Bellman equations:
-- the direct/feedback split of a value difference, and its collapse at an
-- absorbing state. Consumed by `Theory/LockIn/LockInComparativeStatics.lean`.
import Sanctions.Foundations.PatienceDecomposition
-- Step-6 measure-side: dual Kantorovich–Rubinstein metric + the abstract
-- transfer-operator contraction (uniqueness in d + geometric convergence).
import Sanctions.Foundations.DualKantorovich
import Sanctions.Foundations.DualKantorovichS
import Sanctions.Foundations.BoxPullback
-- Step-6 measure-side, concrete operator: the box transfer operator
-- `T*μ = map(closed-loop+noise)(μ ⊗ uniform)`, its adjoint identity (constructed,
-- not hypothesized), and the resulting contraction / uniqueness / geometric
-- convergence in `dualKR`.
import Sanctions.Foundations.BoxTransfer
-- Step-6 measure-side, existence: Krylov–Bogolyubov (SLP Thm 12.10) via Cesàro
-- averages on the compact space of probability laws — the invariant law of the
-- box transfer operator now EXISTS by construction (existence + uniqueness +
-- geometric attraction all machine-checked; no citation left).
import Sanctions.Foundations.KrylovBogolyubov
-- Shock-side kernel machinery: the moving-average / box-smear kernel
-- (window-shift Lipschitz bound, value-Lipschitz preservation) feeding the
-- purified/shocked layer in `Theory/Shocked/*`.
import Sanctions.Foundations.MovingAverage
-- Monotone market-clearing map used by the Kaempfer–Lowenberg polity
-- microfoundation (`Theory/Microfoundations/KaempferLowenbergPolity.lean`).
import Sanctions.Foundations.MarketClearingMonotone
-- Tarski / Knaster–Tarski static supermodular-game MPE template (general
-- lattice fixed-point machinery; moved from the since-removed `Theory/Framework/` in the
-- 2026-07-07 restructure per Rule 19 — it mentions no project economics).
-- Also hosts the state-dependent policy-lattice MPE templates
-- (`StateDependentMPE`), absorbed from `Theory/Equilibrium/StateDependent.lean`
-- in the 2026-07-24 Rule-19 sweep.
import Sanctions.Foundations.TarskiMPE
-- Becker (1983) two-group additive-influence quadratic-cost pressure
-- contest: dominant-strategy Nash closed form with completed-square
-- argmax certificates, uniqueness, and stake-monotone comparative
-- statics (Wave-2 2026-07-11; generic — no project economics; consumed
-- by `Theory/Microfoundations/KaempferLowenbergContest.lean`).
import Sanctions.Foundations.BeckerContest
-- State-dependent-drift box chain (Wave-5 2026-07-12): the closed-loop
-- transfer operator x' = clipS'(g(x) + η) with Feller adjoint,
-- Krylov–Bogolyubov invariant-law existence for EVERY continuous drift,
-- the conditional dualKR contraction route (fires only for contractive
-- drift), and the constant-drift compatibility making `boxTransfer`
-- (headline row 15) the special case.
import Sanctions.Foundations.ClosedLoopBoxTransfer
-- Law-side discounted verification for arbitrary time-dependent Borel drifts:
-- measurable box transfers preserve probability, and pointwise Bellman
-- inequalities telescope after integration without a continuous pullback.
import Sanctions.Foundations.BorelBoxLawVerification

-- Comparing the maximizers of TWO DIFFERENT objectives (not one family under a
-- moving parameter, which is MilgromShannon.lean). Strict single-crossing lower
-- dominance orders every pair of maximizers with no continuity, concavity,
-- compactness or uniqueness, and is transitive, so a comparison can be routed
-- through an intermediate objective that is never optimized.
import Sanctions.Foundations.BinaryComparativeStatics

-- The self-sustaining set of a rule, {x in A | x <= R x}: a pointwise-larger
-- rule sustains a larger set and therefore sustains from a lower infimum. Pure
-- order theory, no game content. The infimum is NOT a basin boundary --
-- Examples/SelfSustainingInfNotCharacterizing.lean refutes that reading.
import Sanctions.Foundations.SelfSustainingSet
import Sanctions.Foundations.CrossOrderComparison
import Sanctions.Foundations.SemiconvexityDefect
import Sanctions.Foundations.GeometricApproach
import Sanctions.Foundations.IntervalContraction
import Sanctions.Foundations.TransitionExtension
import Sanctions.Foundations.ControlledRecursion
import Sanctions.Foundations.SemiconvexArgmaxShift
-- doc 68 (round D): a centred geometric error bound for a diagonal-fixing
-- transition driven by a rule affine about its steady state (the Target-only
-- rate); and the Milgrom-Shannon upper-argmax preservation lemma, factored out
-- of Theory/LockIn/SigmaDynComparison where it used nothing of the game.
import Sanctions.Foundations.CenteredContraction
import Sanctions.Foundations.MonotoneDifferenceArgmax
-- doc 104 (round AV): the least zero of an antitone family of nonnegative
-- functions on [0,1], and its continuity under a linear relief rate below it —
-- the Sender's full-relief compliance level, stated without the game.
import Sanctions.Foundations.ZeroLevel


-- ─── 2026-08-30 round: four routes the pointwise-order refutations leave open.
-- Amir 2002 §2.2 as a lattice fact: a deterministic law that strictly increases
-- in both arguments at a quadruple never induces a submodular kernel there.
-- NOT an iff, and NOT a claim about every economy in the class: degeneracy in
-- one coordinate is sufficient, not necessary (f x a = min x a is nonconstant in
-- both and satisfies every threshold inequality). The exact condition is the
-- rectangle-min identity; see the file's own header correction of 2026-08-31.
import Sanctions.Foundations.DiracSubmodularity
-- The slope order (order value functions by their increments, not their
-- levels). Carries a Topkis comparative static that the pointwise order cannot.
-- It is a preorder, not a partial order -- but that does NOT close the Tarski
-- route, since Mathlib's Order/Antisymmetrization quotients any preorder to a
-- partial order. Completeness of a quotient carrier, and Bellman
-- well-definedness / monotonicity / invariance on it, are open. See the file's
-- own header correction of 2026-08-31.
import Sanctions.Foundations.SlopeOrder
-- Abreu-Pearce-Stacchetti self-generation: Tarski on SETS. Monotonicity in the
-- inclusion order is free for an operator built from a support relation, so
-- none of the value-function refutations touch it. Also supplies a sound
-- NONEXISTENCE instrument (an empty finite iterate from the top). NOT the
-- project's first: `Theory/Equilibrium/AbsorbingTopObstruction.lean` already
-- carried `no_equilibrium_of_slope_and_top_gain`. See that file's own header
-- correction of 2026-08-31.
import Sanctions.Foundations.SelfGeneration
-- Strong concavity at a maximiser: the deviation inequality and the
-- argmax-Lipschitz consequence (relocated from Theory in doc 71 round G).
import Sanctions.Foundations.StrongConcaveArgmax
-- Two INGREDIENTS for retyping the value carrier to bounded MEASURABLE
-- functions: measurability survives uniform limits, and the action-supremum of
-- a measurable-in-state, continuous-in-action integrand is measurable. Neither
-- opens the route. There is no carrier type, no sup-norm, and no CompleteSpace
-- instance, so "Banach still applies" is NOT established; and the continuation
-- enters through `V (clipS' (F x s))`, so demoting `V` to measurable breaks the
-- action-continuity that the second lemma itself requires. Measurable selection
-- of the argmax is NOT built here. See the file's §"What is NOT here".
import Sanctions.Foundations.BoundedMeasurable
-- The greatest maximizer of a bounded objective on a compact action set need
-- NOT be upper semicontinuous in the parameter. Kills the retyping hope that a
-- merely-upper-semicontinuous continuation would let the follower's greatest
-- selection stay well-behaved, so `hα` could be dropped. Scope: refutes the
-- general propagation lemma, NOT equilibrium existence -- see the file header.
import Sanctions.Foundations.GreatestSelectionUSC
-- Step 2 (2026-10-10): a reflected shifted-argmax bound and a difference-of-suprema bound, the
-- order duals
-- used by the hostile-Sender results (Theory/LockIn/SenderStakeSign.lean).
import Sanctions.Foundations.ReflectedArgmaxShift
