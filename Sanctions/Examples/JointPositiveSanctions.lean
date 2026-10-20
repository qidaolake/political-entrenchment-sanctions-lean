/-
Sanctions/Examples/JointPositiveSanctions.lean

**Non-vacuity certificate for `JointPreferenceBasinTop`.**

Constructs a concrete `AbstractGame.Params` (linear payoffs
`U_T = U_S = s`, σ ≡ 1, discount 1/2) along with a witness for
`JointPreferenceBasinTop` at `V_T = V_S = 0`, `α ≡ 0`,
`xbar = sbar = 1/2`. This certifies that the basin Prop is inhabited
— i.e. the abstract three-goal theorems
(`jointPreferenceBasinTop_long_run_nonDecreasing`,
`dynamicTopSanctions_ge_myopify_same_alpha`,
`jointPreferenceBasinTop_temporary_shock_permanent_high`) are not
vacuous.

This file is an **existence certificate** in the sense of Rule 5's
explicit exception ("the result is an existence certificate
discharging non-vacuity of a parameter class"), not a structural model
of sanctions. The choice `U_T = U_S = s`, `σ ≡ 1` is the minimal
"both players prefer sanctions" specification; the `V_T = V_S = 0`
choice for the value functions is a free input to the basin Prop
(the structure does not require V_T, V_S to be Bellman fixed points),
so the witness is *not* the full equilibrium of a non-trivial game.

A richer instantiation (where V_T, V_S are the Bellman fixed points
under a non-trivial U_T, U_S) is deferred to a future representation
layer.

## Rule compliance

**Rule 1.** σ is the Sender stage argmax of `U_S(x, a, ·) = id`,
attaining max at s = 1 (= σ x a). α ≡ 0 is Bellman-optimal against
the joint Target integrand (constant in a here, so any α works).

**Rule 5.** Explicit Rule 5 exception ("existence certificate
discharging non-vacuity of a parameter class").
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.DynamicStake
import Sanctions.Theory.Equilibrium.BasinCornerExistence
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.Bellman.InvariantBall
import Sanctions.Theory.Equilibrium.ArgmaxUniquenessFromConcavity
import Sanctions.Foundations.Curtat
import Sanctions.Foundations.IntervalDominanceOrder

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## Witness parameter point -/

/-- **Witness parameters.** Linear (1-Lipschitz) Sender / Target stage
payoffs `U_T(x, a, s) = U_S(x, a, s) = s`, constant maximum sanction
response `σ ≡ 1`, transition weight `δ = 1/2`, discount `β_T = β_S = 1/2`. -/
def jointPositiveParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1/2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := fun _ _ s => s
  U_S := fun _ _ s => s
  σ := fun _ _ => 1
  σ_mem := fun _ _ => ⟨by norm_num, le_refl _⟩
  σ_isMaxOn_U_S := fun _ _ s hs => hs.2
  U_T_continuous := continuous_snd.comp continuous_snd
  U_S_continuous := continuous_snd.comp continuous_snd
  F := AbstractGame.affineF (1 / 2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`jointPositiveParams` has a continuous static Sender selector.** Affine-restricted:
a concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance jointPositiveParams_staticSelectorContinuous :
    jointPositiveParams.StaticSelectorContinuous where
  σ_continuous := continuous_const

/-- The zero BCF on `↥S`, packaged as a `def` (used as the trivial
witness for both `V_T` and `V_S` in the basin certificate below). -/
def V0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := 0

/-- Pointwise evaluation of the zero BCF. -/
@[simp] lemma V0_apply (y : ↥(Sanctions.S : Set ℝ)) :
    V0 y = 0 := by
  change (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) y = 0
  rw [BoundedContinuousFunction.coe_zero]; rfl

/-! ## Computational lemmas -/

@[simp] lemma jointPositiveParams_δ : jointPositiveParams.δ = 1/2 := rfl
@[simp] lemma jointPositiveParams_β_T : jointPositiveParams.β_T = 1/2 := rfl
@[simp] lemma jointPositiveParams_β_S : jointPositiveParams.β_S = 1/2 := rfl
@[simp] lemma jointPositiveParams_U_T (x a s : ℝ) :
    jointPositiveParams.U_T x a s = s := rfl
@[simp] lemma jointPositiveParams_U_S (x a s : ℝ) :
    jointPositiveParams.U_S x a s = s := rfl
@[simp] lemma jointPositiveParams_σ (x a : ℝ) :
    jointPositiveParams.σ x a = 1 := rfl

/-- **σ_dyn_top is constant 1 at the witness.** With `V_S = 0` and the
linear `U_S = s`, the dynamic Sender objective at `(x, a)` reduces to
`s ↦ s`, whose unique argmax on `[0, 1]` is `s = 1`. -/
theorem jointPositiveParams_σ_dyn_top_eq_one (x a : ℝ) :
    jointPositiveParams.σ_dyn_top V0 x a = 1 := by
  -- 1 ∈ dynamicArgmaxSet (objective at 1 is the max over [0, 1]).
  have h1_mem : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl _⟩
  have h1_max : IsMaxOn
      (fun s' => jointPositiveParams.U_S x a s'
        + jointPositiveParams.β_S * V0 (Sanctions.clipS'
            ((1 - jointPositiveParams.δ) * x + jointPositiveParams.δ * s')))
      Sanctions.I 1 := by
    intro s' hs'
    -- LHS = s' + (1/2) * 0 = s'; RHS = 1 + (1/2) * 0 = 1.
    simp only [jointPositiveParams_U_S, jointPositiveParams_β_S,
               V0_apply, mul_zero, add_zero]
    exact hs'.2
  have h1_set : (1 : ℝ) ∈ jointPositiveParams.dynamicArgmaxSet V0 x a :=
    ⟨h1_mem, h1_max⟩
  -- σ_dyn_top ≥ 1 because 1 ∈ argmax set.
  have hge : 1 ≤ jointPositiveParams.σ_dyn_top V0 x a := by
    unfold Params.σ_dyn_top
    exact le_csSup
      (jointPositiveParams.dynamicArgmaxSet_bddAbove V0 x a) h1_set
  -- σ_dyn_top ≤ 1 because σ_dyn_top ∈ I.
  have hle : jointPositiveParams.σ_dyn_top V0 x a ≤ 1 :=
    (jointPositiveParams.σ_dyn_top_mem_I V0 x a).2
  linarith

/-! ## Basin certificate -/

/-- **Non-vacuity certificate.** The joint preference basin Prop is
inhabited at the witness, with `V_T = V_S = 0`, `α ≡ 0`,
`xbar = sbar = 1/2`. This packages the structural premise of the three
abstract goal theorems into a concrete inhabitant; downstream
applications can specialise:

* `jointPreferenceBasinTop_long_run_nonDecreasing`
* `jointPreferenceBasinTop_temporary_shock_permanent_high`

to this witness to obtain concrete long-run / shock-persistence
conclusions. (Goal 2's same-α dominance theorem does not consume the
basin Prop; it requires only `Monotone V_S` and basin-free
top-rule monotonicity, both trivial for the constant `σ_dyn_top ≡ 1`
selector here.) -/
theorem jointPositiveParams_basinTop_witness :
    jointPositiveParams.JointPreferenceBasinTop V0 V0
      (fun _ => 0) (1/2 : ℝ) (1/2 : ℝ) where
  xbar_nonneg := by norm_num
  xbar_le_one := by norm_num
  sbar_mem := ⟨by norm_num, by norm_num⟩
  target_policy_feasible := by
    intro _ _; exact ⟨le_refl _, by norm_num⟩
  sender_high_argmax_exists := by
    intro x hx
    refine ⟨1, ⟨by norm_num, le_refl _⟩, ?_, ?_⟩
    · -- IsMaxOn senderDynObjective I 1.
      intro s' hs'
      simp only [Params.senderDynObjective, jointPositiveParams_U_S,
                 jointPositiveParams_β_S,
                 V0_apply, mul_zero, add_zero]
      exact hs'.2
    · exact max_le hx.2 (by norm_num)
  top_rule_mono := by
    intro x₁ _ x₂ _ _
    change jointPositiveParams.σ_dyn_top V0 x₁ 0
            ≤ jointPositiveParams.σ_dyn_top V0 x₂ 0
    rw [jointPositiveParams_σ_dyn_top_eq_one,
        jointPositiveParams_σ_dyn_top_eq_one]
  target_prefers_sanctions := by
    intro _ _ s₁ _ s₂ _ hle
    simp only [Params.targetSanctionObjective, jointPositiveParams_U_T,
               jointPositiveParams_β_T,
               V0_apply, mul_zero, add_zero]
    exact hle
  target_policy_optimal := by
    intro x _ a _
    -- joint_T_top_integrand is constant 1 in a (since σ_dyn_top = 1, V_T = 0).
    change jointPositiveParams.joint_T_top_integrand V0 V0 x a
            ≤ jointPositiveParams.joint_T_top_integrand V0 V0 x ((fun _ => (0:ℝ)) x)
    simp only [Params.joint_T_top_integrand, jointPositiveParams_σ_dyn_top_eq_one,
               jointPositiveParams_U_T, jointPositiveParams_β_T,
               V0_apply, mul_zero, add_zero]
    exact le_refl _

/-! ## Round-11 Priority 1 non-vacuity witness

The C¹ discharger
`Sanctions.AbstractGame.Params.LowerLossSlopeOn.of_hasDerivAt_lowerBound`
takes a convex domain, a `HasDerivAt` witness, and a uniform
lower bound `-c ≤ f' s`, and produces `LowerLossSlopeOn f D c`.

The witness below instantiates the discharger at
`jointPositiveParams` (`U_T x a s = s`, so `∂U_T/∂s ≡ 1`) with
`cT = 0`. The discharger's hypotheses are jointly satisfiable
(`-0 = 0 ≤ 1` is trivially true) and the produced
`LowerLossSlopeOn (fun s => s) (Set.Icc 0 1) 0` is provable
non-vacuously by the discharger (not by `True := rfl`). -/

/-- **Round-11 Priority 1 witness, part (a): hypothesis satisfiability.**
The derivative hypothesis of the discharger holds at
`jointPositiveParams` with `U_T_s ≡ 1`. -/
example :
    ∀ x a s,
      HasDerivAt (fun t => jointPositiveParams.U_T x a t) (1 : ℝ) s := by
  intro x a s
  -- jointPositiveParams.U_T x a t = t, so the slice in t is the identity.
  change HasDerivAt (fun t => t) 1 s
  exact hasDerivAt_id s

/-- **Round-11 Priority 1 witness, part (b): slope lower-bound at cT = 0.**
`-0 = 0 ≤ 1` trivially. -/
example : ∀ x a s, -(0 : ℝ) ≤ (fun (_ _ _ : ℝ) => (1 : ℝ)) x a s := by
  intro _ _ _; norm_num

/-- **Round-11 Priority 1 witness, part (c): discharger produces the
predicate non-vacuously.** Apply
`LowerLossSlopeOn.of_hasDerivAt_lowerBound` at `jointPositiveParams`,
the identity-derivative witness, and `cT = 0`; the discharger then
produces `LowerLossSlopeOn (fun s => s) (Set.Icc 0 1) 0`, a real
chord inequality (not the trivially-true `True`). -/
example :
    Sanctions.AbstractGame.Params.LowerLossSlopeOn
      (fun s : ℝ => jointPositiveParams.U_T 0 0 s)
      (Set.Icc (0 : ℝ) 1) 0 := by
  apply
    Sanctions.AbstractGame.Params.LowerLossSlopeOn.of_hasDerivAt_lowerBound
      (f' := fun _ => (1 : ℝ))
  · exact convex_Icc _ _
  · intro s _
    change HasDerivAt (fun t => t) 1 s
    exact hasDerivAt_id s
  · intro _ _; norm_num

/-! ## Round-11 Priority 2 non-vacuity witness

The Berge-discharger
`Sanctions.AbstractGame.Params.myopicFeedbackEquilibrium_exists_of_continuity`
produces a `Nonempty MyopicFeedbackEquilibrium` from continuity
primitives already in `Params` (no new assumption). The witness
below confirms the discharger applies at `jointPositiveParams` and
that the canonical realized myopic sanction rule equals `1` (since
`σ ≡ 1` in this witness). -/

/-- **Round-11 Priority 2 witness, part (a): existence at the minimal
witness.** The Berge discharger produces a canonical
`MyopicFeedbackEquilibrium` at `jointPositiveParams`. -/
example : Nonempty jointPositiveParams.MyopicFeedbackEquilibrium :=
  jointPositiveParams.myopicFeedbackEquilibrium_exists_of_continuity

/-- **Round-11 Priority 2 witness, part (b): myopic realized rule
equals σ-image of α at every state.** For any
`MyopicFeedbackEquilibrium M` at `jointPositiveParams`, the
paper-facing `myopicEquilibriumRule M x` (`= p.σ x (M.α x)`) coincides
with the constant `1` since `jointPositiveParams.σ ≡ 1`. -/
example (M : jointPositiveParams.MyopicFeedbackEquilibrium) (x : ℝ) :
    jointPositiveParams.myopicEquilibriumRule M x = 1 := by
  -- myopicEquilibriumRule unfolds to p.σ x (M.α x); jointPositiveParams.σ ≡ 1.
  rfl

/-! ## Round-13 Priority 3 non-vacuity witness

Sender-side C¹ discharger
`Sanctions.AbstractGame.Params.LowerSlopeOn.of_hasDerivAt_lowerBound`
parallels the Priority-1 Target discharger. The witness below
instantiates the discharger at `jointPositiveParams`
(`U_S x a s = s`, so `∂U_S/∂s ≡ 1`) with `mS = 1`. -/

/-- **Round-13 Priority 3 witness, part (a): `HasDerivAt` hypothesis.**
At `jointPositiveParams`, the slice `t ↦ U_S x a t` is the identity
in `t`, so its derivative is `1` everywhere. -/
example :
    ∀ x a s,
      HasDerivAt (fun t => jointPositiveParams.U_S x a t) (1 : ℝ) s := by
  intro x a s
  change HasDerivAt (fun t => t) 1 s
  exact hasDerivAt_id s

/-- **Round-13 Priority 3 witness, part (b): slope lower bound at mS=1.**
`1 ≤ 1` trivially. -/
example : ∀ x a s, (1 : ℝ) ≤ (fun (_ _ _ : ℝ) => (1 : ℝ)) x a s := by
  intro _ _ _; norm_num

/-- **Round-13 Priority 3 witness, part (c): discharger produces the
predicate non-vacuously.** Apply `LowerSlopeOn.of_hasDerivAt_lowerBound`
at `jointPositiveParams` with `mS = 1`; produces a real
`LowerSlopeOn (fun s => s) (Set.Icc 0 1) 1` (not `True := rfl`). -/
example :
    Sanctions.AbstractGame.Params.LowerSlopeOn
      (fun s : ℝ => jointPositiveParams.U_S 0 0 s)
      (Set.Icc (0 : ℝ) 1) 1 := by
  apply
    Sanctions.AbstractGame.Params.LowerSlopeOn.of_hasDerivAt_lowerBound
      (f' := fun _ => (1 : ℝ))
  · exact convex_Icc _ _
  · intro s _
    change HasDerivAt (fun t => t) 1 s
    exact hasDerivAt_id s
  · intro _ _; norm_num

/-! ## Round-14 Priority 4 non-vacuity witness — asymmetric Schur regime

The Schur-complement criterion `L_TS · L_ST < (1 - β_T)(1 - β_S)` is
strictly weaker than the unweighted `β_T + L_TS < 1` and
`β_S + L_ST < 1` pair. The witness below exhibits an asymmetric
high-discount regime
`(β_T, L_TS, β_S, L_ST) = (9/10, 1/5, 1/20, 1/20)` where:

* `β_T + L_TS = 9/10 + 1/5 = 11/10 ≥ 1`, so unweighted form fails
  (the existing `joint_MPE_under_explicit_bounds` does not apply);
* `(1 - 9/10)(1 - 1/20) = (1/10)(19/20) = 19/200 = 0.095`,
  `L_TS · L_ST = (1/5)(1/20) = 1/100 = 0.01`,
  so `L_TS · L_ST = 0.01 < 0.095 = (1 - β_T)(1 - β_S)` ✓ (Schur holds);
* the closed-form weights from
  `rowSumWeights_of_spectralRadius_lt_one` produce positive weights
  that satisfy the weighted row-sum inequalities consumed by
  `joint_MPE_under_weighted_bounds`. -/

/-- **Round-14 Priority 4 witness, part (a): Schur margin satisfied at
the asymmetric regime.** -/
example :
    ((1 : ℝ)/5) * (1/20) < (1 - 9/10) * (1 - 1/20) := by norm_num

/-- **Round-14 Priority 4 witness, part (b): unweighted row-sum form
FAILS at the same regime — i.e. the Schur form is a genuine regime
expansion, not a re-packaging.** -/
example : ¬ ((9 : ℝ)/10 + 1/5 < 1) := by norm_num

/-- **Round-14 Priority 4 witness, part (c): weight-existence discharger
produces positive weights at this regime.** Since 2026-10-06 (round BG1.1)
the discharger no longer asks for `β_T < 1`; the four remaining checks are
`β_S < 1`, the two cross-constant signs and the Schur margin. -/
example : ∃ c_T c_S : ℝ, 0 < c_T ∧ 0 < c_S ∧
    c_T * (9/10) + c_S * (1/5) < c_T ∧
    c_T * (1/20) + c_S * (1/20) < c_S :=
  Sanctions.AbstractGame.JointMPE.rowSumWeights_of_spectralRadius_lt_one
    (β_T := 9/10) (β_S := 1/20)
    (L_TS := 1/5) (L_ST := 1/20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Round 23 Priority — auto-derive cube bounds `cube_T`, `cube_S`
from `U_T_continuous` + `U_S_continuous` (SLP Theorem 3.1).

Witnesses for the Round-23 cube-bound auto-discharge: at
`jointPositiveParams` (where `U_T = U_S = s`) both `cube_T` and
`cube_S` can be discharged to the existence form `∃ M ≥ 0, ∀ x a s ∈
I, |U_T x a s| ≤ M` (resp. `U_S`) without supplying a hand-chosen
scalar. The witness simply names the generic discharger
`cube_bound_U_T` / `cube_bound_U_S` and checks the existential
unpacks.

Direct sanity check: at `jointPositiveParams` the explicit numeric
bound `M = 1` suffices (since `|s| ≤ 1` on `I = [0, 1]`), confirming
that the generic discharger does not vacuously produce a useless
bound. -/

/-- **Round-23 witness, part (a): `cube_bound_U_T` exists at
`jointPositiveParams`.** Auto-discharged from `U_T_continuous`
(SLP Theorem 3.1, via `cube_bound_unitCube_of_continuous`). -/
example : ∃ cube_T : ℝ, 0 ≤ cube_T ∧
    ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |jointPositiveParams.U_T x a s| ≤ cube_T :=
  jointPositiveParams.cube_bound_U_T

/-- **Round-23 witness, part (b): `cube_bound_U_S` exists at
`jointPositiveParams`.** Sender-side companion. -/
example : ∃ cube_S : ℝ, 0 ≤ cube_S ∧
    ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |jointPositiveParams.U_S x a s| ≤ cube_S :=
  jointPositiveParams.cube_bound_U_S

/-- **Round-23 witness, part (c): the existence is non-vacuous.**
For `jointPositiveParams` the explicit numeric bound `cube_T = 1`
holds since `U_T x a s = s` and `|s| ≤ 1` on `I = [0, 1]`. -/
example : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
    |jointPositiveParams.U_T x a s| ≤ (1 : ℝ) := by
  intro x _ a _ s hs
  simp only [jointPositiveParams_U_T]
  rw [abs_le]
  exact ⟨by linarith [hs.1, hs.2], hs.2⟩

/-! ## Round-24 non-vacuity witness: StrictMonoOn argmax-uniqueness dischargers

Demonstrates that the Round-24 sibling dischargers
(`dynamicArgmaxUnique_of_strictMonoOn` and
`targetArgmaxUnique_of_strictMonoOn` in
`Sanctions/Theory/Equilibrium/ArgmaxUniquenessFromConcavity.lean`) are
non-vacuous: at the linear witness, the Sender dynamic objective at
`V_S = 0` is exactly `s ↦ s` (strictly monotone increasing on
`[0, 1]`), and the new discharger produces `DynamicArgmaxUnique V0`.

This is the *companion* of the strict-concavity discharger that
`jointPositiveParams`'s linear `U_S = s` *cannot* use (linear is not
strictly concave), filling the witness gap noted in the
Round-21 `polyComplianceParams` architectural plan. -/

/-- **The Sender dynamic objective at `V_S = V0` is the identity in `s`.**
Since `U_S(x, a, s) = s` and `V0 = 0`, the dynamic objective collapses
to `s ↦ s + (1/2) · 0 = s`. -/
lemma jointPositiveParams_senderDynObj_eq_id (x a s : ℝ) :
    jointPositiveParams.U_S x a s
      + jointPositiveParams.β_S * V0
          (Sanctions.clipS' ((1 - jointPositiveParams.δ) * x + jointPositiveParams.δ * s))
      = s := by
  simp only [jointPositiveParams_U_S, jointPositiveParams_β_S, V0_apply]
  ring

/-- **Round-24 sibling: the Sender dynamic objective at `V_S = V0` is
`StrictMonoOn` on `Sanctions.I`.** Because the objective reduces to
the identity, strict monotonicity is immediate. -/
theorem jointPositiveParams_senderDynObj_strictMonoOn_at_V0 (x a : ℝ) :
    StrictMonoOn
      (fun s => jointPositiveParams.U_S x a s
        + jointPositiveParams.β_S * V0
            (Sanctions.clipS' ((1 - jointPositiveParams.δ) * x + jointPositiveParams.δ * s)))
      Sanctions.I := by
  intro s₁ _ s₂ _ h_lt
  -- After simplifying both sides to `s₁`, `s₂`, the conclusion is `s₁ < s₂`.
  simp only [jointPositiveParams_senderDynObj_eq_id]
  exact h_lt

/-- **Round-24 non-vacuity certificate: `DynamicArgmaxUnique V0` holds
at `jointPositiveParams` via the new strict-monotonicity discharger.**
This is the witness Round-21 flagged as missing — strict-concavity does
not apply to linear `U_S = s`, but strict-monotonicity does, and the
generic `Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn`
extracts uniqueness directly. -/
theorem jointPositiveParams_dynamicArgmaxUnique_V0_via_strictMonoOn :
    jointPositiveParams.DynamicArgmaxUnique V0 :=
  jointPositiveParams.dynamicArgmaxUnique_of_strictMonoOn
    (fun x _hx a => jointPositiveParams_senderDynObj_strictMonoOn_at_V0 x a)

/-- **Sanity check: the generic Foundations lemma `isMaxOn_unique_of_strictMonoOn`
applies to the simplest non-trivial case `f = id` on `[0, 1]`.** Any two
maximizers of the identity on `[0, 1]` coincide (both equal `1`). -/
example {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Sanctions.I) (hs₂ : s₂ ∈ Sanctions.I)
    (h₁ : IsMaxOn (fun s : ℝ => s) Sanctions.I s₁)
    (h₂ : IsMaxOn (fun s : ℝ => s) Sanctions.I s₂) :
    s₁ = s₂ :=
  Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
    (strictMonoOn_id) hs₁ hs₂ h₁ h₂

/-! ### Round 26 — Rule-9 sibling: Curtat 1996 closed-form non-vacuity

A non-vacuity witness for `Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData`
and its closed-form `toRow`. We pick the trivial primitive scalars
`L_σ = L_U = K_V = L_U_a = L_α_VT = L_α_VS = 0` (every Lipschitz
constant zero — every map is constant in every argument): every
non-negativity hypothesis is satisfied, the closed-form coefficients
collapse to `(β_T_row, L_TS, L_ST, β_S_row) = (β_T, 0, 0, β_S)`, and
the two Schur strict-margin inequalities reduce to
`β_T + 0 < 1` and `β_S + 0 < 1`, which hold for any `(β_T, β_S) ∈ (0, 1)`.

This certifies that the `CurtatPrimitiveLipschitzData` structure is
inhabited at non-trivial values of `(β_T, β_S, δ)` (here `(1/2, 1/2,
1/2)` — matching `jointPositiveParams`), and that the closed-form
`toRow` produces a `CurtatRowLipschitzConstants` whose four scalars
recover the expected formulas. -/

/-- **Witness `CurtatPrimitiveLipschitzData` at `jointPositiveParams`'
discount triple `(1/2, 1/2, 1/2)`.** All six primitive Lipschitz
scalars set to `0`; this is the minimal Curtat data bundle. -/
noncomputable def curtatPrimitiveDataWitness :
    Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData
      ((1 : ℝ) / 2) ((1 : ℝ) / 2) ((1 : ℝ) / 2) where
  L_σ := 0
  L_U := 0
  K_V := 0
  L_U_a := 0
  L_α_VT := 0
  L_α_VS := 0
  hL_σ_nn := le_refl _
  hL_U_nn := le_refl _
  hK_V_nn := le_refl _
  hL_U_a_nn := le_refl _
  hL_α_VT_nn := le_refl _
  hL_α_VS_nn := le_refl _
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hδ_nn := by norm_num

/-- **Closed-form Target-row coefficient at the witness.** `β_T_row =
β_T = 1/2`. -/
example :
    curtatPrimitiveDataWitness.β_T_row = (1 : ℝ) / 2 := rfl

/-- **Closed-form Sender-row coefficient at the witness.** `β_S_row =
L_U_a * L_α_VS + β_S = 0 + 1/2 = 1/2`. -/
example :
    curtatPrimitiveDataWitness.β_S_row = (1 : ℝ) / 2 := by
  unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.β_S_row
  simp [curtatPrimitiveDataWitness]

/-- **Closed-form `V_S → V_T` cross-coefficient at the witness.**
`L_TS = L_σ * (L_U + β_T * K_V * δ) = 0`. -/
example :
    curtatPrimitiveDataWitness.L_TS = 0 := by
  unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.L_TS
  simp [curtatPrimitiveDataWitness]

/-- **Closed-form `V_T → V_S` cross-coefficient at the witness.**
`L_ST = L_U_a * L_α_VT = 0`. -/
example :
    curtatPrimitiveDataWitness.L_ST = 0 := by
  unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.L_ST
  simp [curtatPrimitiveDataWitness]

/-- **Non-vacuity: the closed-form Schur Target margin holds at the
witness.** `β_T_row + L_TS = 1/2 + 0 < 1`. -/
example :
    curtatPrimitiveDataWitness.β_T_row +
        curtatPrimitiveDataWitness.L_TS < 1 := by
  unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.β_T_row
    Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.L_TS
  simp [curtatPrimitiveDataWitness]; norm_num

/-- **Non-vacuity: the closed-form Schur Sender margin holds at the
witness.** `β_S_row + L_ST = 1/2 + 0 < 1`. -/
example :
    curtatPrimitiveDataWitness.β_S_row +
        curtatPrimitiveDataWitness.L_ST < 1 := by
  unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.β_S_row
    Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.L_ST
  simp [curtatPrimitiveDataWitness]; norm_num

/-- **Non-vacuity packaged: the `toRow` bundle exists at the
witness with all four row-Lipschitz scalars derived from the
six primitive scalars via Curtat's Theorem 4.5 closed-form.** -/
noncomputable def curtatRowWitness :
    Sanctions.Foundations.Curtat.CurtatRowLipschitzConstants :=
  curtatPrimitiveDataWitness.toRow
    (by
      unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.β_T_row
        Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.L_TS
      simp [curtatPrimitiveDataWitness]; norm_num)
    (by
      unfold Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.β_S_row
        Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData.L_ST
      simp [curtatPrimitiveDataWitness]; norm_num)

/-- The witness `CurtatRowLipschitzConstants` recovers the expected
`(β_T_row, β_S_row) = (1/2, 1/2)` after the closed-form rewrite. -/
example : curtatRowWitness.β_T_row = (1 : ℝ) / 2 := rfl

/-! ## Round-29 Priority 7 non-vacuity witness

The abstract smooth cross-partial discharger
`Sanctions.MilgromShannon.IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on`
takes a convex parameter set `T`, a pointwise `HasDerivAt` witness in
the parameter axis, and a cross-partial monotonicity hypothesis, and
produces `IncreasingDifferencesOn S T f`.

The witness below instantiates the discharger at the literal supermodular
function `f(s, x) := s * x` on `S = T = Icc 0 1` (cross-partial
`∂²f/∂s∂x = 1 ≥ 0`). The discharger's hypotheses are jointly satisfiable
(`∂f/∂x = s`, which is non-decreasing in `s`) and the produced
`IncreasingDifferencesOn` is provable non-vacuously by the discharger
(not by `True := rfl`). -/

/-- **Round-29 Priority 7 witness, part (a): `HasDerivAt` hypothesis.**
At the supermodular witness `f(s, x) = s * x`, the slice `y ↦ s * y` has
derivative `s` everywhere — the `HasDerivAt` hypothesis of the smooth
cross-partial discharger is jointly satisfiable on the rectangle. -/
example :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun y => s * y) s x := by
  intro s _ x _
  simpa using (hasDerivAt_id x).const_mul s

/-- **Round-29 Priority 7 witness, part (b): cross-partial monotonicity.**
The partial derivative `∂f/∂x(s, x) = s` is (weakly) increasing in `s`
on `[0, 1] × [0, 1]` — for `s ≤ s'`, we have `s ≤ s'`. -/
example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, s ≤ s' → s ≤ s' := by
  intro _ _ _ _ _ _ h; exact h

/-- **Round-29 Priority 7 witness, part (c): discharger produces the
predicate non-vacuously.** Apply
`IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on` at the
supermodular witness; the discharger produces a real
`IncreasingDifferencesOn (Icc 0 1) (Icc 0 1) (fun s x => s * x)` (not
the trivially-true `True`). The conclusion unfolds to the chord
`s' · x - s · x ≤ s' · x' - s · x'` for `s ≤ s'`, `x ≤ x'`, which is a
non-trivial inequality (equivalently `(s' - s) · (x' - x) ≥ 0`). -/
example :
    Sanctions.MilgromShannon.IncreasingDifferencesOn
      (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
      (fun s x => s * x) := by
  apply Sanctions.MilgromShannon.IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on
    (f_x := fun s _ => s)
  · exact convex_Icc _ _
  · intro s _ x _
    simpa using (hasDerivAt_id x).const_mul s
  · intro _ _ _ _ _ _ h; exact h

/-- **Round-29 Priority 7 witness, part (d): ID ⇒ SC bridge applies.**
The discharger output composed with `IncreasingDifferencesOn.toSingleCrossingOn`
yields a real `SingleCrossingOn`, which is the consumer-facing predicate
in `StandardComplianceLocalCoreCertificate.hSC_on`. -/
example :
    Sanctions.MilgromShannon.SingleCrossingOn
      (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
      (fun s x => s * x) := by
  have hID :
      Sanctions.MilgromShannon.IncreasingDifferencesOn
        (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
        (fun s x => s * x) := by
    apply Sanctions.MilgromShannon.IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on
      (f_x := fun s _ => s)
    · exact convex_Icc _ _
    · intro s _ x _
      simpa using (hasDerivAt_id x).const_mul s
    · intro _ _ _ _ _ _ h; exact h
  exact hID.toSingleCrossingOn

/-! ## Round-30 IDO discharger non-vacuity witnesses

The Round-30 sibling discharger
`Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono`
takes only **choice-axis strict monotonicity** of every member of the
parameter family `{F(·, t)}_{t ∈ T}` on a convex `S`, and returns
`SingleCrossingOn S T F` — with NO α-monotonicity required. The
predicate is genuinely non-trivial: it certifies single-crossing on
`I × T` without using the strict-SC + α-monotone combination of the
previous discharger.

The witnesses below instantiate the discharger at `F(s, x) := s`
(constant in `x`, strictly monotone in `s`) and at `F(s, x) := s + x`
(linear; strict-mono in `s` for every fixed `x`). Both are
parameter families for which the QS07-Ext sign-preservation
condition is satisfied, and the produced `SingleCrossingOn` is
provable non-vacuously via the discharger. -/

/-- **Round-30 witness, part (a): scalar parameter family `F(s, x) := s`.**
Every slice `(fun s => s)` is `StrictMonoOn (Set.Icc 0 1)`. -/
example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, StrictMonoOn (fun s : ℝ => s) (Set.Icc (0 : ℝ) 1) := by
  intro _ _ s _ s' _ hss
  exact hss

/-- **Round-30 witness, part (b): IDO family from choice-axis strict
monotonicity, instantiated at `F(s, x) := s`.** No α-monotonicity
hypothesis required. -/
example :
    Sanctions.IntervalDominanceOrder.IDOFamilyOn
      (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
      (fun s _x : ℝ => s) := by
  apply Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_choice_strictMono
  · exact convex_Icc _ _
  · intro _ _ s _ s' _ hss; exact hss

/-- **Round-30 witness, part (c): composite discharger produces
`SingleCrossingOn` non-vacuously at `F(s, x) := s`.** This is the
direct consumer-facing predicate
`StandardComplianceLocalCoreCertificate.hSC_on` would receive — proven
WITHOUT strict-SC or α-monotone primitives, only choice-axis strict
monotonicity. -/
example :
    Sanctions.MilgromShannon.SingleCrossingOn
      (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
      (fun s _x : ℝ => s) := by
  apply Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono
  · exact convex_Icc _ _
  · intro _ _ s _ s' _ hss; exact hss

/-- **Round-30 witness, part (d): IDO discharger at `F(s, x) := s + x`.**
A genuine two-axis dependence in which the slice
`(fun s => s + x)` is strict-mono in `s` for every `x`. The discharger
produces `SingleCrossingOn` directly, with no further input. -/
example :
    Sanctions.MilgromShannon.SingleCrossingOn
      (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
      (fun s x : ℝ => s + x) := by
  apply Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono
  · exact convex_Icc _ _
  · intro x _ s _ s' _ hss
    change s + x < s' + x
    linarith

/-- **Round-30 witness, part (e): negative non-vacuity — the IDO
discharger's choice-strict-monotonicity hypothesis is NOT trivially
true.** For the constant-in-`s` family `F(s, x) := x`, no slice is
strict-mono in `s`, so the discharger's hypothesis genuinely fails;
this confirms the hypothesis is non-degenerate. -/
example :
    ¬ (∀ x ∈ Set.Icc (0 : ℝ) 1,
        StrictMonoOn (fun _s : ℝ => x) (Set.Icc (0 : ℝ) 1)) := by
  intro h
  -- At x = 0, the slice is the constant function 0, which is not strict-mono.
  have h0 := h 0 (Set.left_mem_Icc.mpr zero_le_one)
  -- StrictMonoOn (fun _ => 0) [0, 1] would give 0 < 0 at any (0, 1).
  have : (0 : ℝ) < 0 :=
    h0 (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
      zero_lt_one
  exact lt_irrefl _ this

/-! ## Basin-corner equilibrium existence (general-`F` route, Phase-3 follow-up)

Non-vacuity witness for `feedbackStackelbergTop_of_corner_optimal`
(`Sanctions/Theory/Equilibrium/BasinCornerExistence.lean`): a genuine
`FeedbackStackelbergEquilibriumTop` exists at `jointPositiveParams` with
the saturated corner policy `α ≡ 0`, *constructed* through the
single-agent Target value fixed point `V_T_dyn` (general transition `F`,
Rule-15 constructed) rather than the affine-only Schur/contraction route.

The two use-site hypotheses discharge cleanly here:
* `hσc` (joint continuity of the greatest Sender selector): the Sender
  value `V_S (α ≡ 0)` is monotone (because `U_S = s` is `x`-independent),
  so the dynamic Sender objective `s + β_S·V_S(F(x,s))` is strictly
  increasing in `s`, pinning `σ_dyn_top ≡ 1` — a constant, hence
  continuous.
* `h_corner` (the corner attains the Target's dynamic argmax): both
  `U_T = s` and `U_S = s` are independent of the Target action `a`, so the
  joint Target integrand is constant in `a` and every action (in
  particular `0`) is a maximizer. -/

/-- **The Sender value at the corner policy `α ≡ 0` is monotone** at
`jointPositiveParams`. Discharged from `V_S_monotone_of_integrand_monotone`
since `U_S(x, 0, s) = s` is independent of `x` (so trivially monotone). -/
theorem jointPositiveParams_V_S0_monotone :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x => jointPositiveParams.V_S (fun _ => 0) continuous_const x) :=
  jointPositiveParams.V_S_monotone_of_integrand_monotone continuous_const
    (by intro s _ x _ y _ _; simp [jointPositiveParams_U_S])

/-- **`σ_dyn_top` is constant `1` at the corner Sender value.** Discharged
via the parametric helper `σ_dyn_top_V_S_zero_eq_one_of_monotone`: the
monotone `V_S (α ≡ 0)` and the top-maximized linear stage payoff `U_S = s`
make the dynamic Sender objective maximized at `s = 1`. -/
theorem jointPositiveParams_σ_dyn_top_V_S0_eq_one (x a : ℝ) :
    jointPositiveParams.σ_dyn_top
      (jointPositiveParams.V_S (fun _ => 0) continuous_const) x a = 1 :=
  jointPositiveParams.σ_dyn_top_V_S_zero_eq_one_of_monotone
    jointPositiveParams_V_S0_monotone
    (fun x a s hs => by simp only [jointPositiveParams_U_S]; exact hs.2) x a

/-- **A genuine feedback-Stackelberg equilibrium exists at the saturated
corner.** The non-vacuity certificate for the Phase-3 basin-corner route:
`jointPositiveParams` admits a `FeedbackStackelbergEquilibriumTop` whose
leader policy is `α ≡ 0`, constructed through the general-`F` single-agent
value fixed point `V_T_dyn`. Discharged via the parametric helper
`feedbackStackelbergTop_corner_exists_of_σtop_one` from `σ_dyn_top ≡ 1`
and the `a`-independence of `U_T = s`. -/
theorem jointPositiveParams_feedbackStackelbergTop_corner_exists :
    ∃ E : jointPositiveParams.FeedbackStackelbergEquilibriumTop,
      E.α = (fun _ => 0) :=
  jointPositiveParams.feedbackStackelbergTop_corner_exists_of_σtop_one
    jointPositiveParams_σ_dyn_top_V_S0_eq_one
    (fun _ _ _ => rfl)

/-! ## DYNAMIC-STAKE at `jointPositiveParams`: what the exclusion is, and is not

`jointPositiveParams` (`U_S(x,a,s) = s`, sanction identically `1` forever, a
constructed corner equilibrium) is the economy that refutes the **naive**
conjecture "persistent sanctions require the Sender to profit from the Target's
defiance". DYNAMIC-STAKE declines to cover it. Two separate facts are recorded
below, and they must not be conflated:

1. **The conclusion is false here** (`jp_conclusion_false`) — with a
   state-independent `U_S` the composed payoff cannot rise anywhere. Combined
   with `dynamic_stake`, this excludes a dynamic floor at every *continuous*
   Target policy — `dynamic_stake` carries `Continuous α`, so this route does
   not reach discontinuous ones.  (Route 2 below, the corner argument, does
   cover every policy, and is the reason the exclusion here is overdetermined.)
   This *is* chord content.
2. **The exclusion is also available for free** (`jp_no_dynamic_floor_of_corner`)
   — the greatest stage maximiser here is already the feasibility corner `1`, so
   nothing can exceed it, for **any** continuation value, with no appeal to the
   Sender's state chord and no use of the antitone Bellman machinery.

Because (2) holds, the `jointPositiveParams` row is **not** evidence that
DYNAMIC-STAKE discriminates by chord sign: the exclusion is overdetermined, and
the corner alone would deliver it. It is a corner artefact of this witness, not
a sharp test. -/

/-- At `jointPositiveParams` DYNAMIC-STAKE's **conclusion** is false, at every
Target policy: with `U_S(x,a,s) = s` the Sender's payoff does not depend on the
Target's political state at all, so the composed payoff cannot rise anywhere.
So DYNAMIC-STAKE does not have a vacuously-true conclusion. -/
theorem jp_conclusion_false (α : ℝ → ℝ) :
    ¬ (∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
        y₁ ≤ y₂ ∧ jointPositiveParams.U_S y₁ (α y₁) s
          < jointPositiveParams.U_S y₂ (α y₂) s) := by
  rintro ⟨s, _, y₁, _, y₂, _, _, hlt⟩
  simp only [jointPositiveParams_U_S] at hlt
  exact lt_irrefl s hlt

/-- The greatest **stage** maximiser at `jointPositiveParams` is the feasibility
corner `1`, at every Target policy and every state: with `U_S = s` the myopic
problem is `max_{s ∈ [0,1]} s`. -/
theorem jp_stageTopRule_eq_one (α : ℝ → ℝ) (x : ℝ) :
    jointPositiveParams.stageTopRule α x = 1 := by
  refine le_antisymm
    (csSup_le (jointPositiveParams.stageArgmaxSet_nonempty α x) fun s hs => hs.1.2)
    (le_csSup (jointPositiveParams.stageArgmaxSet_bddAbove α x)
      ⟨⟨by norm_num, le_refl _⟩, fun s' hs' => ?_⟩)
  simpa using hs'.2

/-- **The exclusion, by the corner alone.** One-line corollary of the general
parametric fact `realizedRule_le_stageTopRule_of_corner`: since the greatest
stage maximiser here is already `1`, the greatest forward-looking maximiser
cannot exceed it — for **every** continuation value `V` and every Target policy,
using only that the realised rule is feasible.

No antitone Bellman machinery, no `dynamic_stake`, no reference to the Sender's
state chord. This is the honest description of why `jointPositiveParams` is
excluded. -/
theorem jp_no_dynamic_floor_of_corner
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) :
    jointPositiveParams.dynamicTopRealizedRule V α x
      ≤ jointPositiveParams.stageTopRule α x :=
  jointPositiveParams.realizedRule_le_stageTopRule_of_corner V α x
    (le_of_eq (jp_stageTopRule_eq_one α x).symm)

/-- The same exclusion via DYNAMIC-STAKE, against the *constructed* Sender value.
Redundant given `jp_no_dynamic_floor_of_corner`, and kept only to record that the
chord route reaches the same verdict. -/
theorem jp_no_dynamic_floor {α : ℝ → ℝ} (hα : Continuous α) (x : ℝ) :
    jointPositiveParams.dynamicTopRealizedRule
        (jointPositiveParams.V_S α hα) α x
      ≤ jointPositiveParams.stageTopRule α x := by
  by_contra hcon
  rw [not_le] at hcon
  exact jp_conclusion_false α (jointPositiveParams.dynamic_stake hα x hcon)

/-- The exclusion at `jointPositiveParams`' **constructed** equilibrium
(`jointPositiveParams_feedbackStackelbergTop_corner_exists`), against that
equilibrium's own Sender value. Again a corollary of the corner, not of the
chord. -/
theorem jp_no_dynamic_floor_equilibrium
    (E : jointPositiveParams.FeedbackStackelbergEquilibriumTop) (x : ℝ) :
    jointPositiveParams.dynamicTopRealizedRule E.V_S E.α x
      ≤ jointPositiveParams.stageTopRule E.α x :=
  jp_no_dynamic_floor_of_corner E.V_S E.α x

/-- **The stage ceiling at `jointPositiveParams` sits at the corner, and the
equilibrium sanction is at most it.**

Read the second conjunct as the `≤` it is. This does **not** say the equilibrium
sanction sits *exactly at* the stage ceiling for an arbitrary equilibrium `E`:
nothing here pins `dynamicTopRealizedRule E.V_S E.α x` to `1`. The permanent
maximal sanction of the *specific* corner equilibrium is pinned separately by
`jointPositiveParams_σ_dyn_top_V_S0_eq_one`; for a general `E` all that is
available is the ceiling. -/
theorem jp_stage_ceiling_at_the_corner
    (E : jointPositiveParams.FeedbackStackelbergEquilibriumTop) (x : ℝ) :
    jointPositiveParams.stageTopRule E.α x = 1
      ∧ jointPositiveParams.dynamicTopRealizedRule E.V_S E.α x ≤ 1 :=
  ⟨jp_stageTopRule_eq_one E.α x,
   (jp_no_dynamic_floor_equilibrium E x).trans (le_of_eq (jp_stageTopRule_eq_one E.α x))⟩

#print axioms jp_conclusion_false
#print axioms jp_stageTopRule_eq_one
#print axioms jp_no_dynamic_floor_of_corner
#print axioms jp_no_dynamic_floor
#print axioms jp_no_dynamic_floor_equilibrium
#print axioms jp_stage_ceiling_at_the_corner

end -- noncomputable section

end Examples

end Sanctions
