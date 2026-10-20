/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Basin.WeakFloorBasin
import Sanctions.Examples.JointPositiveSanctions

/-!
# The weak-floor corner condition is not implied at a given floor

**Rule-11 witness (2026-07-29).**  `WeakFloorBasinTop` weakens the basin's
sanction floor from `max x sbar ≤ s` to `sbar ≤ s`, and adds in exchange the
corner condition `xbar ≤ F xbar sbar`.  A natural question is whether that
corner condition is free --- whether the existing `JointPreferenceBasinTop`
already implies it at the same floor `sbar`.

**It does not**, and this file exhibits the failure with an actual economy
rather than with arithmetic.  `weakFloor_strongBasin_at_zero_floor` builds a
full `JointPreferenceBasinTop` instance for `jointPositiveParams` at pivot
`1/2` and floor `0` --- every field discharged, including the Sender's
`IsMaxOn` argmax obligation and the Target's Bellman optimality.  At that
floor the strong condition `max x 0 ≤ s` degenerates to `x ≤ s`, which the
rule pinned at `1` satisfies.  Yet
`weakFloor_corner_fails_at_zero_floor` shows `F (1/2) 0 = 1/4 < 1/2`.

`weakFloor_corner_not_implied_by_strong_basin` packages this as the negation
of the universally quantified implication, so the antecedent really is the
Sender's optimization problem and not a stand-in for it.

**Any transition (renovation item BH5.3, 2026-10-07).** Both values are zero,
so the transition never enters the Sender's objective, the Target's objective
or any basin field: the strong basin at floor `0` holds over *every* transition.
`weakFloorOver p₀` keeps the transition and the discounts of an arbitrary
economy `p₀` and installs the linear payoffs `U_T = U_S = s`;
`weakFloorOver_strongBasin` builds the full basin there at every pivot
`x̄ ∈ [0, 1]`. The corner `x̄ ≤ F(x̄, 0)` then fails exactly when
`F(x̄, 0) < x̄` (`F_mono_s` and `F_diag` give `F(x̄, 0) ≤ x̄` for `x̄ ≥ 0`), so
`weakFloor_corner_fails_generalF` refutes the corner for every transition with
a strict loss at the pivot, and `weakFloor_corner_fails_of_strictAdjustment` at
every pivot in `(0, 1]` under strict adjustment. A hypothesis on `F` is
genuinely needed: the flat transition `F x s = x` is in the class and satisfies
the corner. The affine witness above is now an instance.

**Why this file exists separately.**  The `Theory/` layer may not import a
witness economy, so the counterexample cannot live beside the structure it
constrains (Rule 19).  `Theory/Basin/WeakFloorBasin` therefore carries only
the arithmetic ingredient, under the honest name
`corner_arith_ingredients_at_zero_floor`, and points here for the real claim.

**Consequence.**  The `hCorner` argument of
`WeakFloorBasinTop.of_jointPreferenceBasinTop` is genuinely needed. The
hypothesis-free containment is the *reindexed* one,
`WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed`, which moves the
floor to `max xbar sbar` and obtains the corner condition from `F_diag` and
`F_mono_s` at no cost. Prefer the reindexed form.
-/

noncomputable section

namespace Sanctions
namespace Examples

open Sanctions Sanctions.AbstractGame Sanctions.AbstractGame.Params
open BoundedContinuousFunction

/-! ## The strong basin at floor `0`, over any transition (renovation item BH5.3) -/

/-- **The linear-payoff economy over an arbitrary transition** (renovation item
BH5.3, 2026-10-07). Keeps the transition `F`, both discount factors and the
adjustment rate of `p₀`, and installs the stage payoffs `U_T = U_S = s` and the
constant stage selector `1` of `jointPositiveParams`. General in `F`: the
transition is whatever `p₀` carries. At `p₀ = jointPositiveParams` it is that
economy itself, field for field. -/
def weakFloorOver (p₀ : Params) : Params :=
  { p₀ with
    U_T := fun _ _ s => s
    U_S := fun _ _ s => s
    σ := fun _ _ => 1
    σ_mem := fun _ _ => ⟨zero_le_one, le_refl _⟩
    σ_isMaxOn_U_S := fun _ _ _ hs => hs.2
    U_T_continuous := continuous_snd.comp continuous_snd
    U_S_continuous := continuous_snd.comp continuous_snd }

/-- **`weakFloorOver` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance weakFloorOver_staticSelectorContinuous (p₀ : Params) :
    (weakFloorOver p₀).StaticSelectorContinuous where
  σ_continuous := continuous_const

@[simp] theorem weakFloorOver_U_T (p₀ : Params) (x a s : ℝ) :
    (weakFloorOver p₀).U_T x a s = s := rfl
@[simp] theorem weakFloorOver_U_S (p₀ : Params) (x a s : ℝ) :
    (weakFloorOver p₀).U_S x a s = s := rfl
@[simp] theorem weakFloorOver_F (p₀ : Params) : (weakFloorOver p₀).F = p₀.F := rfl
@[simp] theorem weakFloorOver_β_S (p₀ : Params) : (weakFloorOver p₀).β_S = p₀.β_S := rfl
@[simp] theorem weakFloorOver_β_T (p₀ : Params) : (weakFloorOver p₀).β_T = p₀.β_T := rfl

/-- **The Sender always sanctions fully, whatever the transition.** With the zero
continuation value and `U_S = s`, the Sender's forward-looking objective is
`s ↦ s`, so the greatest maximiser on `[0, 1]` is `1`. General in `F`; this is
`jointPositiveParams_σ_dyn_top_eq_one` with the affine transition dropped. -/
theorem weakFloorOver_σ_dyn_top_eq_one (p₀ : Params) (x a : ℝ) :
    (weakFloorOver p₀).σ_dyn_top V0 x a = 1 := by
  have h1_set : (1 : ℝ) ∈ (weakFloorOver p₀).dynamicArgmaxSet V0 x a := by
    refine ⟨⟨zero_le_one, le_refl _⟩, fun s' hs' => ?_⟩
    simp only [Set.mem_setOf_eq, weakFloorOver_U_S, V0_apply, mul_zero, add_zero]
    exact hs'.2
  have hge : 1 ≤ (weakFloorOver p₀).σ_dyn_top V0 x a :=
    le_csSup ((weakFloorOver p₀).dynamicArgmaxSet_bddAbove V0 x a) h1_set
  exact le_antisymm ((weakFloorOver p₀).σ_dyn_top_mem_I V0 x a).2 hge

/-- **The strong basin at floor `0`, at every pivot and over every transition.**
At the linear-payoff economy over `p₀`, with both values zero and the Target
policy `0`, every field of `JointPreferenceBasinTop` holds at pivot `x̄` and
floor `0`: the Sender's argmax obligation (full sanctions are a maximiser and
clear `max x 0`), monotonicity of the realised rule (constant `1`), the
Target's sanction preference (its objective is `s`) and its Bellman optimality
(its objective does not depend on its action).

General in `F`: the transition enters only inside the zero value. Generalises
`weakFloor_strongBasin_at_zero_floor`, which fixed the affine transition at rate
`1/2` and the pivot `1/2`. -/
theorem weakFloorOver_strongBasin (p₀ : Params) {xbar : ℝ}
    (hx : xbar ∈ Set.Icc (0 : ℝ) 1) :
    (weakFloorOver p₀).JointPreferenceBasinTop V0 V0 (fun _ => 0) xbar 0 where
  xbar_nonneg := hx.1
  xbar_le_one := hx.2
  sbar_mem := ⟨le_rfl, zero_le_one⟩
  target_policy_feasible := fun _ _ => ⟨le_refl _, zero_le_one⟩
  sender_high_argmax_exists := by
    intro x hx'
    refine ⟨1, ⟨zero_le_one, le_refl _⟩, ?_, ?_⟩
    · intro s' hs'
      simp only [Params.senderDynObjective, weakFloorOver_U_S, V0_apply, mul_zero,
        add_zero]
      exact hs'.2
    · exact max_le hx'.2 zero_le_one
  top_rule_mono := by
    intro x₁ _ x₂ _ _
    change (weakFloorOver p₀).σ_dyn_top V0 x₁ 0 ≤ (weakFloorOver p₀).σ_dyn_top V0 x₂ 0
    rw [weakFloorOver_σ_dyn_top_eq_one, weakFloorOver_σ_dyn_top_eq_one]
  target_prefers_sanctions := by
    intro _ _ s₁ _ s₂ _ hle
    simp only [Params.targetSanctionObjective, weakFloorOver_U_T, V0_apply, mul_zero,
      add_zero]
    exact hle
  target_policy_optimal := by
    intro x _ a _
    change (weakFloorOver p₀).joint_T_top_integrand V0 V0 x a
      ≤ (weakFloorOver p₀).joint_T_top_integrand V0 V0 x ((fun _ => (0 : ℝ)) x)
    simp only [Params.joint_T_top_integrand, weakFloorOver_σ_dyn_top_eq_one,
      weakFloorOver_U_T, V0_apply, mul_zero, add_zero]
    exact le_refl _

/-- **The corner fails at floor `0` for every transition with a strict loss at
the pivot** (renovation item BH5.3, 2026-10-07). For any economy `p₀` and any
pivot `x̄ ∈ [0, 1]` at which a zero sanction strictly lowers the state,
`F(x̄, 0) < x̄`, there is an economy with the same transition and discounts at
which the strong basin holds at pivot `x̄` and floor `0` and the corner
`x̄ ≤ F(x̄, 0)` fails.

General in `F`. The hypothesis `F(x̄, 0) < x̄` is exactly the negated corner
(for `x̄ ≥ 0`, `F_mono_s` and `F_diag` already give `F(x̄, 0) ≤ x̄`), and it is
strictly weaker than strict adjustment; some hypothesis on `F` is needed, since
the flat transition `F x s = x` satisfies the corner. -/
theorem weakFloor_corner_fails_generalF (p₀ : Params) {xbar : ℝ}
    (hx : xbar ∈ Set.Icc (0 : ℝ) 1) (hlt : p₀.F xbar 0 < xbar) :
    ∃ p : Params, p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T ∧
      p.JointPreferenceBasinTop V0 V0 (fun _ => 0) xbar 0 ∧ ¬ xbar ≤ p.F xbar 0 :=
  ⟨weakFloorOver p₀, rfl, rfl, rfl, weakFloorOver_strongBasin p₀ hx, not_le.mpr hlt⟩

/-- **Under strict adjustment the corner fails at floor `0` at every positive
pivot.** For any economy `p₀` whose transition moves strictly toward the
sanction and any pivot `x̄ ∈ (0, 1]`, some economy with the same transition and
discounts satisfies the strong basin at `(x̄, 0)` and violates the corner. A
corollary of `weakFloor_corner_fails_generalF`: strict adjustment's
below-diagonal half gives `F(x̄, 0) < x̄`. General in `F`. -/
theorem weakFloor_corner_fails_of_strictAdjustment (p₀ : Params)
    (hAdj : p₀.StrictAdjustment) {xbar : ℝ} (hx : xbar ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ p : Params, p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T ∧
      p.JointPreferenceBasinTop V0 V0 (fun _ => 0) xbar 0 ∧ ¬ xbar ≤ p.F xbar 0 :=
  weakFloor_corner_fails_generalF p₀ ⟨hx.1.le, hx.2⟩
    (hAdj.1 ⟨hx.1.le, hx.2⟩ ⟨le_rfl, zero_le_one⟩ hx.1)

/-! ## The affine witness -/

/-- The existing witness economy also satisfies the STRONG basin at floor `sbar = 0`.
Since round BH-5 (renovation item BH5.3, 2026-10-07) the instance of
`weakFloorOver_strongBasin` at `p₀ = jointPositiveParams` and pivot `1/2`;
statement unchanged. -/
theorem weakFloor_strongBasin_at_zero_floor :
    jointPositiveParams.JointPreferenceBasinTop V0 V0 (fun _ => 0) (1/2 : ℝ) (0 : ℝ) :=
  weakFloorOver_strongBasin jointPositiveParams ⟨by norm_num, by norm_num⟩

/-- ... yet the corner condition FAILS there: `F (1/2) 0 = 1/4 < 1/2`. -/
theorem weakFloor_corner_fails_at_zero_floor :
    ¬ ((1/2 : ℝ) ≤ jointPositiveParams.F (1/2) 0) := by
  show ¬ ((1/2 : ℝ) ≤ AbstractGame.affineF (1/2) (1/2) 0)
  norm_num [AbstractGame.affineF]

/-- **The genuine non-implication.** There is a `Params`, a pivot and a floor
at which `JointPreferenceBasinTop` holds and the corner condition fails.
Hence `WeakFloorBasinTop.of_jointPreferenceBasinTop` really does need its
`hCorner` argument. THIS is the artifact Rule 11 demands; the shipped
`corner_not_implied_at_given_sbar_counterexample` is not it. -/
theorem weakFloor_corner_not_implied_by_strong_basin :
    ¬ (∀ (p : Params) (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
         (xbar sbar : ℝ),
        p.JointPreferenceBasinTop V_T V_S α xbar sbar → xbar ≤ p.F xbar sbar) := by
  intro h
  exact weakFloor_corner_fails_at_zero_floor
    (h jointPositiveParams V0 V0 (fun _ => 0) (1/2) 0 weakFloor_strongBasin_at_zero_floor)

/-! ## Axiom hygiene (Rule 10) -/

#print axioms weakFloor_strongBasin_at_zero_floor
#print axioms weakFloor_corner_fails_at_zero_floor
#print axioms weakFloor_corner_not_implied_by_strong_basin
#print axioms weakFloorOver_strongBasin
#print axioms weakFloor_corner_fails_generalF
#print axioms weakFloor_corner_fails_of_strictAdjustment

end Examples
end Sanctions

end
