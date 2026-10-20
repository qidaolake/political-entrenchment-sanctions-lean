/-
Sanctions/Theory/Certificates/TwoSidedRuleComparison.lean

**One theorem that builds both regimes and orders their sanction rules.**

Until now the two-sided comparison was delivered in two pieces that a reader had
to assemble: `PerovExistence` constructs the forward-looking equilibrium `E` from
a value class, and `TwoSidedForwardLooking` compares `E` against a myopic `M`
*given* four conditions checked at `E`. Nothing composed them, because two of the
four conditions are stated at `E.V_T` and `E.V_S`, and `E` does not exist until
the fixed point is built.

This file composes them, and the reason it can is that two of the four conditions
turn out to be **carrier facts** rather than equilibrium facts.

* The Sender response-pair condition is discharged by `Monotone V_S`, which
  `hV_S_mono_carrier_of_gainBall_subset` already derives from nonnegative-gain-ball
  membership. On such a carrier it costs nothing at all.
* The Target-continuation leg is a condition on `V_T` alone, so it can be
  imposed over the Target carrier without ever naming `E` — the same shape as the
  carrier field `hV_S_lip_carrier` (and as `hV_T_gain_on_carrier`, a field of
  the core certificate until round BJ1.4, 2026-10-07).
* Placation is a condition on `p.σ`, a `Params` field, so it does not involve
  values at all.

**What is NOT made carrier-uniform, and why.** The Sender-response-switch leg
stays a hypothesis about equilibria whose values lie in the carrier.

The condition itself — `SenderSwitchWeakSCLowerAt` — is *ordinal*: single-crossing
lower dominance of the Target's `FF` objective relative to its `TM` objective. It
is not a curvature condition, and describing it as second-order would be
describing its chord discharger instead. What blocks a carrier-uniform version is
narrower than that, and worth stating precisely.

* Single crossing is not preserved by addition, so the condition does not
  decompose over a carrier the way a sup-norm or a Lipschitz bound does.
  Membership in a cone constrains each value separately; this constrains a
  *comparison between two objectives* built from both values at once.
* The route that would decompose — the pointwise order `targetFFObjective ≤
  targetTMObjective` at each action — converts the problem rather than solving
  it. It is strictly stronger than single-crossing lower dominance, and it is
  itself unsigned by the primitives: under a deterministic transition the two
  objectives coincide at every action where the two Sender responses coincide,
  so the order reduces to a sign condition on the response switch, which
  `Examples/SenderSwitchSignUndetermined.lean` shows the baseline does not fix.
* The natural sufficient condition that *would* live in a carrier is the
  translated-chord one of `TwoSidedForwardLooking` §12, and that is genuinely
  second-order: every invariant carrier this development has is first-order — the
  `valLipGainBall` cone bundles sup-norm, Lipschitz and lower slope, and
  `mem_valLipGainBall_bellman_chord` keeps exactly that cone invariant under a
  general transition — and a first-order cone does not control second
  differences.

Whether a *curvature* cone could be made invariant through the coupled operator
is no longer open, and the answer is no. Two independent obstructions are now
formalized, and neither implies the other:

* `Examples/TransitionShapeNotPreserved.lean` — the maintained transition class
  alone defeats every modulus. `F x s = min x s` satisfies all five transition
  fields, and along a constant *optimal* sanction the closed-loop successor map
  is `x ↦ min x c`, whose slope drop at `x = c` is a defect linear in the chord
  width against a cap that is quadratic in it
  (`minMeetTransition_closedLoop_not_semiconvex`). The join transition kills the
  semiconcave cone the same way.
* `Examples/SelectorShapeNotPreserved.lean` — restricting to an affine
  transition does not repair it. With `F x s = s` and a Sender whose stage
  argmax is the clamped peak `clipS (2x - 1/2)` — unique, continuous, monotone
  and Lipschitz, hence every selection convention at once — the closed loop has
  a convex kink where the clamp releases and a concave kink where it binds, so
  one economy refutes both cones
  (`clampedPeakSender_closedLoop_not_semiconvex` and `..._not_semiconcave`).

The general argument behind both is `Foundations/SemiconvexityDefect.lean`: a
kink produces a chord defect linear in the width, and a modulus caps it
quadratically, so shrinking the chord onto the kink defeats any proposed
constant. Chen, Li and So (arXiv:2506.04587, Example 3) is the same phenomenon
in the bilevel literature, where a smooth strongly convex lower-level problem
with a unique Lipschitz solution still yields a reduced objective with no
weak-convexity modulus, because the solution meets a constraint boundary.

What survives is order and quantitative continuity, which is what
`valLipGainBall` is built from. So the first-order character of this
development's carriers is not a limitation of the construction — it is the
available option, and the switch condition is left visible rather than hidden in
a carrier that provably cannot deliver it.

**Scope.** Policy ordering, realised-rule dominance, and the self-sustaining-set
inclusion. The *path* comparisons are deliberately absent: they additionally need
the realised rule to be monotone in the state at every candidate value pair,
which is a genuine strengthening of what `TwoSidedForwardLooking` §11 assumes at
`E` alone, and is held pending a decision.

General in the transition (Rule 22): nothing here assumes `F = affineF δ`.

**Round BJ5.1 (2026-10-07).** `SchurValueSystem.ruleOrdered_at_constructed`
states that some myopic equilibrium is dominated, and its proof supplies the
canonical myopic equilibrium `p.myopicFeedbackEquilibrium_canonical` as the
witness; the two E3 existence theorems `exists_ruleOrdered_equilibria_schur`
and `exists_ruleOrdered_equilibria_schur_selfSustaining` produce their myopic
equilibrium the same way. The canonical equilibrium is built from the static
selector's continuity, so the three take `[p.StaticSelectorContinuous]`. That
condition, the joint continuity of the static Sender selector `σ`, was the
`Params` field `σ_continuous`; it is now the class
`Params.StaticSelectorContinuous`. The general comparison theorems, which take
an arbitrary myopic equilibrium, are unchanged.
-/
import Sanctions.Theory.Equilibrium.PerovExistence
import Sanctions.Theory.LockIn.TwoSidedForwardLooking
import Sanctions.Theory.Basin.StageFlipCertificate

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

variable {p : Sanctions.AbstractGame.Params}

/-! ## Level E1 --- one supplied equilibrium

The weakest level, and the one everything else reduces to. The comparison
conditions are imposed **at the equilibrium in hand** and nowhere else: no
carrier, no membership, no construction. Reading the two carrier-membership
theorems below shows they never needed more than this — each consumes its
carrier-quantified hypothesis at a single value function, `E.V_T` or `E.V_S`, and
the membership proof exists only to reach it. Stating that directly drops both
membership hypotheses and leaves a theorem that is shorter and strictly more
general.

The three levels this file now keeps apart are:

* **E1** — conditions at a supplied equilibrium. Weakest; comparison only.
* **E2** — conditions at the equilibrium the Schur/Perov fixed point *constructs*.
  Existence plus verification, with nothing asked of the rest of the carrier.
* **E3** — conditions over the whole carrier, checkable before any equilibrium
  exists. Strongest, and the right ex ante certificate.

Each is strictly stronger than the last, and E3 is retained precisely because its
hypotheses can be discharged without first running the construction. -/

/-- **E1: policy ordering at a supplied equilibrium.**

The forward-looking Target complies no more than the myopic one, on `B`. Needs
the Target-continuation leg and the Sender-switch leg at *this* equilibrium's own
value functions, and neither placation nor any Sender-side condition. -/
theorem alpha_order_at_equilibrium
    {B : Set ℝ}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hB_subS : B ⊆ Sanctions.S)
    (hTarget : ∀ x ∈ B, p.TargetContinuationSCLowerAt E.V_T x)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt E x) :
    ∀ x ∈ B, E.α x ≤ M.α x :=
  fun x hx =>
    p.alpha_order_dynamic_le_myopic_of_switchWeak_targetStrict E M (hB_subS hx)
      (hSwitch x hx) (hTarget x hx)

/-- **E1: rule dominance at a supplied equilibrium.**

The myopic realised sanction never exceeds the forward-looking one, on `B`. The
Sender side enters only through monotonicity of *this* equilibrium's own
continuation value, which is what the local response-order condition needs. -/
theorem ruleDom_at_equilibrium
    {B : Set ℝ}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : Monotone E.V_S)
    (hTarget : ∀ x ∈ B, p.TargetContinuationSCLowerAt E.V_T x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt E x) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
  p.ruleDom_on_of_switchWeak_targetStrict_and_localSender E M hB_subS hSwitch
    hTarget hσ_antiOn_a
    (fun x _ =>
      SenderContinuationOrderAtResponses.of_valueMonotone p hV_S_mono x (E.α x))

/-! ## The comparison at a carrier-valued equilibrium

The half that needs no existence theory: given an equilibrium whose values lie in
the carrier, the carrier-level conditions specialise to it. -/

/-- **Rule dominance at a carrier-valued equilibrium.**

The three conditions that are carrier facts are consumed here in carrier form;
only the Sender-switch leg is asked at `E`. -/
theorem ruleDom_on_of_carrier_membership
    {D : p.ValueClass2} {B : Set ℝ}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S)
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hTarget : ∀ V_T ∈ D.carrier_T, ∀ x ∈ B,
      p.TargetContinuationSCLowerAt V_T x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt E x) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
  -- E3 above E1: the carrier-quantified hypotheses are consumed at exactly one
  -- value function each, and the membership proofs exist only to reach them.
  p.ruleDom_at_equilibrium E M hB_subS (hV_S_mono E.V_S hVS)
    (fun x hx => hTarget E.V_T hVT x hx) hσ_antiOn_a hSwitch

/-- **Policy ordering at a carrier-valued equilibrium.** The first arrow of the
chain, separated out because it needs neither placation nor the Sender-side
condition. -/
theorem alpha_order_of_carrier_membership
    {D : p.ValueClass2} {B : Set ℝ}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hVT : E.V_T ∈ D.carrier_T)
    (hB_subS : B ⊆ Sanctions.S)
    (hTarget : ∀ V_T ∈ D.carrier_T, ∀ x ∈ B,
      p.TargetContinuationSCLowerAt V_T x)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt E x) :
    ∀ x ∈ B, E.α x ≤ M.α x :=
  p.alpha_order_at_equilibrium E M hB_subS
    (fun x hx => hTarget E.V_T hVT x hx) hSwitch

/-! ## Level E2 --- the equilibrium the fixed point constructs

E1 asks its conditions of a supplied equilibrium; E3 below asks them of every
member of a carrier. Between the two sits the level the construction actually
delivers: the Schur/Perov fixed point produces **one** equilibrium, inside the
carrier, and the comparison conditions need hold only there.

Two things are worth being exact about, because the level is easy to oversell.

It is a genuine weakening of E3 — `hV_S_mono` becomes monotonicity of a single
continuation value rather than of every member of `carrier_S`, and the Target leg
is asked at one `V_T` rather than all of them. But the conditions are then stated
*about an object that does not exist until the construction has run*, which is
exactly why E3 is retained rather than replaced: carrier-uniform hypotheses are
checkable in advance, and these are not.

The existence is **constructed, never assumed** (Rule 15). `equilibrium` is a
`def` that chooses from `exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur`,
which is proved from primitives by applying the in-repo Perov contraction
(`Foundations/PerovContraction.lean`) to the two joint Bellman operators, with
completeness of the carriers coming from their closedness. No fixed point is
taken as a hypothesis and no `Prop`-valued stand-in for one appears anywhere in
the chain.

Rule 3: `SchurValueSystem` bundles the hypotheses the existence theorem already
takes, in the same form, and adds none. The assumption surface is unchanged; what
changes is that the bundle can be named, carried, and projected. -/

/-- **The data a Schur/Perov construction needs, bundled.**

Everything `exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur`
consumes: an invariant two-carrier value class, the four non-negative coupling
constants, the two joint-operator Lipschitz bounds, the diagonal bounds, and the
Schur margin `L_TS · L_ST < (1 − β_T)(1 − β_S)` — which is strictly weaker than
requiring each row to sum below one. -/
structure SchurValueSystem (p : Params) where
  /-- The invariant value class supplying both carriers. -/
  D : p.ValueClass2
  /-- Both carriers are mapped into themselves by the joint Bellman operators. -/
  h_inv : D.IsInvariant
  /-- Own-discount and cross-coupling coefficients for the two operator rows. -/
  β_T : ℝ
  β_S : ℝ
  L_TS : ℝ
  L_ST : ℝ
  hβ_T_nn : 0 ≤ β_T
  hβ_S_nn : 0 ≤ β_S
  hL_TS_nn : 0 ≤ L_TS
  hL_ST_nn : 0 ≤ L_ST
  /-- The Target row: own-contraction `β_T`, cross-sensitivity `L_TS`. -/
  hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointTargetOp_sub h_inv (V, W)) (D.jointTargetOp_sub h_inv (V', W'))
      ≤ β_T * dist V V' + L_TS * dist W W'
  /-- The Sender row: cross-sensitivity `L_ST`, own-contraction `β_S`. -/
  hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointSenderOp_sub h_inv (V, W)) (D.jointSenderOp_sub h_inv (V', W'))
      ≤ L_ST * dist V V' + β_S * dist W W'
  hβ_T_lt : β_T < 1
  hβ_S_lt : β_S < 1
  /-- The Schur margin: the coupling product falls below the product of the two
  own-contraction margins. Equivalent to the spectral radius of the coefficient
  matrix lying below one. -/
  hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)

namespace SchurValueSystem

variable (S : p.SchurValueSystem)

/-- The existence statement the bundle discharges, in the form the construction
below consumes. -/
theorem exists_equilibrium :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ∃ hVT : E.V_T ∈ S.D.carrier_T,
      ∃ hVS : E.V_S ∈ S.D.carrier_S,
        E.α = S.D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ :=
  S.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur
    S.h_inv S.hT_T S.hT_S S.hβ_T_lt S.hβ_S_lt S.hSchur

/-- **The constructed equilibrium.** Rule 15: produced by a `def` over an
existence theorem derived from primitives, not consumed as a hypothesis. -/
noncomputable def equilibrium : p.FeedbackStackelbergEquilibriumTop :=
  Classical.choose S.exists_equilibrium

theorem equilibrium_V_T_mem : S.equilibrium.V_T ∈ S.D.carrier_T := by
  obtain ⟨hVT, -⟩ := Classical.choose_spec S.exists_equilibrium
  exact hVT

theorem equilibrium_V_S_mem : S.equilibrium.V_S ∈ S.D.carrier_S := by
  obtain ⟨-, hVS, -⟩ := Classical.choose_spec S.exists_equilibrium
  exact hVS

/-- **E2: policy ordering at the constructed equilibrium.**

The conditions are imposed only at `S.equilibrium`, and nothing is asked of any
other member of either carrier. -/
theorem alpha_order {B : Set ℝ}
    (M : p.MyopicFeedbackEquilibrium)
    (hB_subS : B ⊆ Sanctions.S)
    (hTarget : ∀ x ∈ B, p.TargetContinuationSCLowerAt S.equilibrium.V_T x)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt S.equilibrium x) :
    ∀ x ∈ B, S.equilibrium.α x ≤ M.α x :=
  p.alpha_order_at_equilibrium S.equilibrium M hB_subS hTarget hSwitch

/-- **E2: rule dominance at the constructed equilibrium.** -/
theorem ruleDom {B : Set ℝ}
    (M : p.MyopicFeedbackEquilibrium)
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : Monotone S.equilibrium.V_S)
    (hTarget : ∀ x ∈ B, p.TargetContinuationSCLowerAt S.equilibrium.V_T x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt S.equilibrium x) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule
      S.equilibrium.V_S S.equilibrium.α x :=
  p.ruleDom_at_equilibrium S.equilibrium M hB_subS hV_S_mono hTarget
    hσ_antiOn_a hSwitch

/-- **E2 in one statement: both regimes constructed, both orderings delivered.**

The myopic side is the canonical stage-argmax equilibrium, which exists whenever
the static Sender selector is continuous (`[p.StaticSelectorContinuous]`, a
`Params` field until round BJ5.1, 2026-10-07); the forward-looking side is the
Perov fixed point. Compare with
`exists_ruleOrdered_equilibria_schur` (E3), whose hypotheses range over the whole
carrier — that one is checkable before the construction runs, this one is not,
and that is the entire difference between the levels. -/
theorem ruleOrdered_at_constructed [p.StaticSelectorContinuous] {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : Monotone S.equilibrium.V_S)
    (hTarget : ∀ x ∈ B, p.TargetContinuationSCLowerAt S.equilibrium.V_T x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt S.equilibrium x) :
    ∃ M : p.MyopicFeedbackEquilibrium,
      S.equilibrium.V_T ∈ S.D.carrier_T ∧ S.equilibrium.V_S ∈ S.D.carrier_S
      ∧ (∀ x ∈ B, S.equilibrium.α x ≤ M.α x)
      ∧ (∀ x ∈ B, p.σ x (M.α x)
          ≤ p.dynamicTopRealizedRule S.equilibrium.V_S S.equilibrium.α x) :=
  ⟨p.myopicFeedbackEquilibrium_canonical, S.equilibrium_V_T_mem,
    S.equilibrium_V_S_mem,
    S.alpha_order p.myopicFeedbackEquilibrium_canonical hB_subS hTarget hSwitch,
    S.ruleDom p.myopicFeedbackEquilibrium_canonical hB_subS hV_S_mono hTarget
      hσ_antiOn_a hSwitch⟩

end SchurValueSystem

/-! ## Existence and comparison in one statement -/

/-- **Both regimes are constructed, and their sanction rules are ordered.**

The forward-looking equilibrium comes from the Perov/Schur fixed point on the
value class; the myopic one is the canonical per-state stage argmax. The
conclusion returns carrier membership, the Target-policy ordering, and pointwise
dominance of the forward-looking realised rule.

Reading the hypotheses:

* the first block is exactly what `PerovExistence` already asks — invariance,
  nonnegativity of the four Lipschitz coordinates, the two operator row bounds,
  the two discount bounds, and the Schur condition `L_TS · L_ST < (1−β_T)(1−β_S)`;
* `hV_S_mono` — every Sender value in the carrier is non-decreasing (free on a
  nonnegative-gain ball, via `hV_S_mono_carrier_of_gainBall_subset`);
* `hTarget` — every Target value in the carrier makes compliance strictly less
  attractive through the incumbent's own continuation motive;
* `hσ_antiOn_a` — compliance placates, a condition on `p.σ` alone;
* `hSwitch` — the Sender-response switch does not reverse the comparison, asked
  of any equilibrium whose values lie in the carrier. This is the one condition
  no carrier in this development can deliver; see the file header.

Nothing here is affine-restricted. The binder `[p.StaticSelectorContinuous]`
(round BJ5.1, formerly a `Params` field) supplies the myopic equilibrium: the
statement asserts one exists, and the proof builds the canonical one. -/
theorem exists_ruleOrdered_equilibria_schur [p.StaticSelectorContinuous]
    {D : p.ValueClass2} {B : Set ℝ}
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_T_lt : β_T < 1) (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S))
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hTarget : ∀ V_T ∈ D.carrier_T, ∀ x ∈ B,
      p.TargetContinuationSCLowerAt V_T x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSwitch : ∀ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ D.carrier_T → E.V_S ∈ D.carrier_S →
      ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt E x) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ∃ M : p.MyopicFeedbackEquilibrium,
        E.V_T ∈ D.carrier_T ∧ E.V_S ∈ D.carrier_S
        ∧ (∀ x ∈ B, E.α x ≤ M.α x)
        ∧ (∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x) := by
  -- E3 above E2. The statement is unchanged (Rule 13 drift fence); the route
  -- moved, so that the carrier-uniform hypotheses are visibly *dischargers* of
  -- the point-specific conditions E2 consumes, evaluated at the equilibrium the
  -- Perov fixed point constructs. Each carrier-quantified hypothesis is used at
  -- exactly one value function, which is what makes E2 the weaker level and E3
  -- the one checkable before the construction has run.
  let S : p.SchurValueSystem :=
    { D := D, h_inv := h_inv
      β_T := β_T, β_S := β_S, L_TS := L_TS, L_ST := L_ST
      hβ_T_nn := hβ_T_nn, hβ_S_nn := hβ_S_nn
      hL_TS_nn := hL_TS_nn, hL_ST_nn := hL_ST_nn
      hT_T := hT_T, hT_S := hT_S
      hβ_T_lt := hβ_T_lt, hβ_S_lt := hβ_S_lt, hSchur := hSchur }
  obtain ⟨M, hVT, hVS, hα, hrule⟩ :=
    S.ruleOrdered_at_constructed hB_subS
      (hV_S_mono _ S.equilibrium_V_S_mem)
      (fun x hx => hTarget _ S.equilibrium_V_T_mem x hx)
      hσ_antiOn_a
      (hSwitch S.equilibrium S.equilibrium_V_T_mem S.equilibrium_V_S_mem)
  exact ⟨S.equilibrium, M, hVT, hVS, hα, hrule⟩

/-- **The self-sustaining-set inclusion comes free with the rule ordering.**

Over the whole feasible range, rule dominance alone enlarges the set of states
the rule does not pull down — no monotonicity of either rule, no invariance, no
path argument. What it does *not* say is that either infimum is a basin boundary;
`Examples/SelfSustainingInfNotCharacterizing.lean` refutes that reading. -/
theorem exists_ruleOrdered_equilibria_schur_selfSustaining [p.StaticSelectorContinuous]
    {D : p.ValueClass2}
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_T_lt : β_T < 1) (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S))
    (hV_S_mono : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hTarget : ∀ V_T ∈ D.carrier_T, ∀ x ∈ Sanctions.I,
      p.TargetContinuationSCLowerAt V_T x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSwitch : ∀ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ D.carrier_T → E.V_S ∈ D.carrier_S →
      ∀ x ∈ Sanctions.I, p.SenderSwitchWeakSCLowerAt E x) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ∃ M : p.MyopicFeedbackEquilibrium,
        E.V_T ∈ D.carrier_T ∧ E.V_S ∈ D.carrier_S
        ∧ (∀ x ∈ Sanctions.I, E.α x ≤ M.α x)
        ∧ (∀ x ∈ Sanctions.I,
            p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
        ∧ Sanctions.selfSustainingSet Sanctions.I (p.myopicEquilibriumRule M)
            ⊆ Sanctions.selfSustainingSet Sanctions.I
                (p.dynamicTopRealizedRule E.V_S E.α) := by
  obtain ⟨E, M, hVT, hVS, hα, hrule⟩ :=
    exists_ruleOrdered_equilibria_schur (D := D) (B := Sanctions.I) h_inv
      hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T hT_S hβ_T_lt hβ_S_lt hSchur
      Set.Subset.rfl hV_S_mono hTarget hσ_antiOn_a hSwitch
  exact ⟨E, M, hVT, hVS, hα, hrule,
    Sanctions.selfSustainingSet_mono_of_rule_le hrule⟩

end Params
end AbstractGame
end Sanctions
