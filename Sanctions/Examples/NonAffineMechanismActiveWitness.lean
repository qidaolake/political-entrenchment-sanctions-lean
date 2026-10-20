/-
Sanctions/Examples/NonAffineMechanismActiveWitness.lean

An exact non-affine integrated economy in which the Target's continuation
value is nonconstant and changes its optimal compliance choice.

The construction keeps the Sender side of
`NonAffineInteriorWitness` and replaces the Target stage payoff by
a continuation-adjusted primitive.  At the verified equilibrium the Target's
complete Bellman objective is the old strict objective plus the inherited
state.  Its value is therefore `V_T(x) = x`.  At the basin pivot, however,
the stage payoff alone strictly prefers a higher compliance action than the
dynamic equilibrium action.  Thus the Target continuation term is
behaviorally load-bearing, rather than merely nonzero bookkeeping.

## The family over any transition (round BH-5, item BH5.4, 2026-10-07)

`maParamsOf p₀` is the same construction over the transition of an arbitrary
economy `p₀` (its Target payoff subtracts `(9/10)·clip(F(x, s))` for that `F`).
The equilibrium, the value `V_T(x) = x`, the basin and the persistence evidence
hold for **every** transition (Rule 22: general in `F`).  The pivot reversal is
the one place the transition matters, and there it is exactly priced:
`maOf_pivot_choice_reversal_iff` shows the stage payoff prefers `a = 9/16` to
`a = 1/2` if and only if `F(1/2, 3/4) − F(1/2, 47/64) > 5/1152`, and
`maOf_pivot_gap_of_lowerChord` shows a sanction lower chord above `5/18`
implies it.  The literal `maParams` (transition `quadBumpF`, lower chord
`47/100`) is kept beside the family with its own definition; its lemmas are
one-line instances at `p₀ := niParams`.

Rule 3: no new assumptions.  This is a constructed witness over the existing
model surface.
-/

import Sanctions.Examples.NonAffineInteriorWitness
import Sanctions.Theory.Mechanism.ContinuationChangesChoice

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## Continuation-adjusted Target primitive -/

/-- The mechanism-active Target stage payoff.  The last term is the current
cost associated with the successor political state.  The equilibrium
continuation value restores that state payoff dynamically. -/
def maU_T (x a s : ℝ) : ℝ :=
  niU_T x a s + x
    - (9 / 10 : ℝ) * Sanctions.clipS (quadBumpF x s)

theorem maU_T_continuous :
    Continuous
      (fun xas : ℝ × ℝ × ℝ => maU_T xas.1 xas.2.1 xas.2.2) := by
  unfold maU_T niU_T niIdeal quadBumpF Sanctions.clipS
  fun_prop

/-- The mechanism-active economy.  It has the same Sender primitives,
discount factors, and nonlinear transition as `niParams`; only the Target
stage payoff changes. -/
def maParams : AbstractGame.Params where
  δ := niParams.δ
  δ_mem := niParams.δ_mem
  β_T := niParams.β_T
  β_T_mem := niParams.β_T_mem
  β_S := niParams.β_S
  β_S_mem := niParams.β_S_mem
  U_T := maU_T
  U_S := niParams.U_S
  σ := niParams.σ
  σ_mem := niParams.σ_mem
  σ_isMaxOn_U_S := niParams.σ_isMaxOn_U_S
  U_T_continuous := maU_T_continuous
  U_S_continuous := niParams.U_S_continuous
  F := niParams.F
  F_continuous := niParams.F_continuous
  F_mono_x := niParams.F_mono_x
  F_mono_s := niParams.F_mono_s
  F_diag := niParams.F_diag

/-- **`maParams` has a continuous static Sender selector.** A concrete member with
`niParams`'s non-affine transition `quadBumpF`; the selector is `niParams`'s and does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance maParams_staticSelectorContinuous :
    maParams.StaticSelectorContinuous where
  σ_continuous := niParams.σ_continuous

@[simp] theorem maParams_β_T : maParams.β_T = 9 / 10 := rfl
@[simp] theorem maParams_β_S : maParams.β_S = 1 / 2 := rfl
@[simp] theorem maParams_F : maParams.F = quadBumpF := rfl

theorem maParams_F_ne_affine :
    maParams.F ≠ AbstractGame.affineF (1 / 2) := by
  simpa only [maParams_F] using qbParams_F_ne_affine

/-- The mechanism-active Target stage payoff over the transition of `p₀`: the
current cost of the successor state is `(9/10)·clip(p₀.F(x, s))`.  Rule 22:
general in `F`.  At `p₀ := niParams` it is `maU_T`. -/
def maU_TOf (p₀ : AbstractGame.Params) (x a s : ℝ) : ℝ :=
  niU_T x a s + x
    - (9 / 10 : ℝ) * Sanctions.clipS (p₀.F x s)

/-- The family Target payoff is jointly continuous, from continuity of `p₀.F`.
General in `F`. -/
theorem maU_TOf_continuous (p₀ : AbstractGame.Params) :
    Continuous
      (fun xas : ℝ × ℝ × ℝ => maU_TOf p₀ xas.1 xas.2.1 xas.2.2) := by
  have hF : Continuous (fun xas : ℝ × ℝ × ℝ => p₀.F xas.1 xas.2.2) :=
    p₀.F_continuous.comp
      (by fun_prop : Continuous (fun xas : ℝ × ℝ × ℝ => (xas.1, xas.2.2)))
  unfold maU_TOf
  exact (niU_T_continuous.add continuous_fst).sub
    (continuous_const.mul (Sanctions.clipS_continuous.comp hF))

/-- **The mechanism-active economy over any transition** (round BH-5, item
BH5.4).  The Sender side, the discounts and the transition fields are those of
`niParamsOf p₀`; only the Target stage payoff changes, to `maU_TOf p₀`.
Rule 22: general in `F`.  The literal `maParams` is the member
`p₀ := niParams` (`maParamsOf_niParams`). -/
def maParamsOf (p₀ : AbstractGame.Params) : AbstractGame.Params where
  δ := (niParamsOf p₀).δ
  δ_mem := (niParamsOf p₀).δ_mem
  β_T := (niParamsOf p₀).β_T
  β_T_mem := (niParamsOf p₀).β_T_mem
  β_S := (niParamsOf p₀).β_S
  β_S_mem := (niParamsOf p₀).β_S_mem
  U_T := maU_TOf p₀
  U_S := (niParamsOf p₀).U_S
  σ := (niParamsOf p₀).σ
  σ_mem := (niParamsOf p₀).σ_mem
  σ_isMaxOn_U_S := (niParamsOf p₀).σ_isMaxOn_U_S
  U_T_continuous := maU_TOf_continuous p₀
  U_S_continuous := (niParamsOf p₀).U_S_continuous
  F := (niParamsOf p₀).F
  F_continuous := (niParamsOf p₀).F_continuous
  F_mono_x := (niParamsOf p₀).F_mono_x
  F_mono_s := (niParamsOf p₀).F_mono_s
  F_diag := (niParamsOf p₀).F_diag

/-- **`maParamsOf` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance maParamsOf_staticSelectorContinuous (p₀ : AbstractGame.Params) :
    (maParamsOf p₀).StaticSelectorContinuous where
  σ_continuous := (niParamsOf p₀).σ_continuous

@[simp] theorem maParamsOf_β_T (p₀ : AbstractGame.Params) : (maParamsOf p₀).β_T = 9 / 10 := rfl
@[simp] theorem maParamsOf_β_S (p₀ : AbstractGame.Params) : (maParamsOf p₀).β_S = 1 / 2 := rfl
@[simp] theorem maParamsOf_F (p₀ : AbstractGame.Params) : (maParamsOf p₀).F = p₀.F := rfl
@[simp] theorem maParamsOf_U_T (p₀ : AbstractGame.Params) : (maParamsOf p₀).U_T = maU_TOf p₀ :=
  rfl

/-- The literal economy is the family member at `p₀ := niParams`, by
definition. -/
theorem maParamsOf_niParams : maParamsOf niParams = maParams := rfl

/-! ## Exact equilibrium with a nonconstant Target value -/

/-- The Target value is the inherited political state. -/
def maV_T : Val := affineBCF 1

/-- The Sender value remains zero in this witness. -/
def maV_S : Val := niV0

@[simp] theorem maV_T_apply (y : ↥(Sanctions.S : Set ℝ)) :
    maV_T y = y.val := by
  simp [maV_T]

theorem maV_T_strictMono : StrictMono maV_T := by
  intro x y hxy
  simpa only [maV_T_apply] using hxy

/-- The Sender problem is definitionally unchanged by the Target-payoff
replacement, over any transition.  General in `F`. -/
theorem maOf_sigma_dyn_top_eq (p₀ : AbstractGame.Params) (x a : ℝ) :
    (maParamsOf p₀).σ_dyn_top maV_S x a =
      (niParamsOf p₀).σ_dyn_top niV0 x a :=
  rfl

/-- The Sender problem is definitionally unchanged by the Target-payoff
replacement. -/
theorem ma_sigma_dyn_top_eq (x a : ℝ) :
    maParams.σ_dyn_top maV_S x a =
      niParams.σ_dyn_top niV0 x a :=
  rfl

/-- Whenever the unconstrained Sender ideal is feasible, it is the exact
greatest dynamic response against the zero Sender value, over any transition.
General in `F`. -/
theorem niOf_top_eq_ideal_of_mem (p₀ : AbstractGame.Params)
    {x a : ℝ} (hideal : niIdeal x a ∈ Sanctions.I) :
    (niParamsOf p₀).σ_dyn_top niV0 x a = niIdeal x a := by
  have hmax := (niParamsOf p₀).σ_dyn_top_isMaxOn niV0 x a
  rw [isMaxOn_iff] at hmax
  have hcomp := hmax (niIdeal x a) hideal
  have hcomp' :
      niU_S x a (niIdeal x a) ≤
        niU_S x a ((niParamsOf p₀).σ_dyn_top niV0 x a) := by
    simpa [niParamsOf, niV0] using hcomp
  unfold niU_S at hcomp'
  nlinarith
    [sq_nonneg
      ((niParamsOf p₀).σ_dyn_top niV0 x a - niIdeal x a)]

/-- Whenever the unconstrained Sender ideal is feasible, it is the exact
greatest dynamic response against the zero Sender value. -/
theorem ni_top_eq_ideal_of_mem
    {x a : ℝ} (hideal : niIdeal x a ∈ Sanctions.I) :
    niParams.σ_dyn_top niV0 x a = niIdeal x a :=
  niOf_top_eq_ideal_of_mem niParams hideal

/-- The Target's complete objective equals the original strict objective plus
the current state, over any transition: the nonconstant continuation value
exactly cancels the successor-state cost, whatever the law of motion.  General
in `F`. -/
theorem maOf_joint_integrand_eq (p₀ : AbstractGame.Params) (x a : ℝ) :
    (maParamsOf p₀).joint_T_top_integrand maV_T maV_S x a =
      (niParamsOf p₀).joint_T_top_integrand niV0 niV0 x a + x := by
  unfold AbstractGame.Params.joint_T_top_integrand
  rw [maOf_sigma_dyn_top_eq]
  simp [maParamsOf, maV_T, maU_TOf, niParamsOf, niV0,
    affineBCF_apply]

/-- The Target's complete objective equals the original strict objective plus
the current state: the nonconstant continuation value exactly enters the
Bellman equation. -/
theorem ma_joint_integrand_eq (x a : ℝ) :
    maParams.joint_T_top_integrand maV_T maV_S x a =
      niParams.joint_T_top_integrand niV0 niV0 x a + x :=
  maOf_joint_integrand_eq niParams x a

/-- The same cancellation written as a sanction-level objective, over any
transition.  General in `F`. -/
theorem maOf_target_sanction_objective_eq (p₀ : AbstractGame.Params) (x a s : ℝ) :
    (maParamsOf p₀).targetSanctionObjective maV_T x a s =
      niU_T x a s + x := by
  unfold AbstractGame.Params.targetSanctionObjective
  simp [maParamsOf, maV_T, maU_TOf, niParamsOf, affineBCF_apply]

/-- The same cancellation written as a sanction-level objective. -/
theorem ma_target_sanction_objective_eq (x a s : ℝ) :
    maParams.targetSanctionObjective maV_T x a s =
      niU_T x a s + x :=
  maOf_target_sanction_objective_eq niParams x a s

/-- The zero Sender value is the Sender Bellman fixed point at the interior
policy, over any transition (the Sender side is that of `niParamsOf p₀`).
General in `F`. -/
theorem maOf_sender_value_fix (p₀ : AbstractGame.Params) :
    maV_S =
      (maParamsOf p₀).bellmanS_BCF niAlpha niAlpha_continuous maV_S := by
  exact niOf_sender_value_fix p₀

theorem ma_sender_value_fix :
    maV_S =
      maParams.bellmanS_BCF niAlpha niAlpha_continuous maV_S :=
  maOf_sender_value_fix niParams

/-- The interior policy maximises the Target's complete objective, over any
transition.  General in `F`. -/
theorem maOf_target_policy_optimal (p₀ : AbstractGame.Params)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn
      (fun a =>
        (maParamsOf p₀).joint_T_top_integrand maV_T maV_S x a)
      Sanctions.I (niAlpha x) := by
  rw [isMaxOn_iff]
  intro a ha
  rw [maOf_joint_integrand_eq, maOf_joint_integrand_eq]
  have h := niOf_target_policy_optimal p₀ hx
  rw [isMaxOn_iff] at h
  linarith [h a ha]

theorem ma_target_policy_optimal
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn
      (fun a =>
        maParams.joint_T_top_integrand maV_T maV_S x a)
      Sanctions.I (niAlpha x) :=
  maOf_target_policy_optimal niParams hx

/-- The state value `V_T(x) = x` is the top-selector Target Bellman fixed point,
over any transition.  General in `F`. -/
theorem maOf_target_value_fix_top (p₀ : AbstractGame.Params)
    (x : ↥(Sanctions.S : Set ℝ)) :
    maV_T x =
      sSup
        ((fun a =>
          (maParamsOf p₀).joint_T_top_integrand maV_T maV_S x.val a) ''
          Sanctions.I) := by
  have hmax := maOf_target_policy_optimal p₀ x.property
  have hgreatest :
      IsGreatest
        ((fun a =>
          (maParamsOf p₀).joint_T_top_integrand maV_T maV_S x.val a) ''
          Sanctions.I)
        ((maParamsOf p₀).joint_T_top_integrand
          maV_T maV_S x.val (1 / 2)) := by
    constructor
    · exact ⟨1 / 2, niAlpha_mem x.val, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      simpa [niAlpha] using hmax ha
  rw [hgreatest.csSup_eq, maV_T_apply, maOf_joint_integrand_eq]
  change x.val =
    niU_T x.val (1 / 2)
      ((niParamsOf p₀).σ_dyn_top niV0 x.val (1 / 2))
      + (9 / 10 : ℝ) * 0 + x.val
  rw [niOf_top_at_half p₀ x.property]
  simp [niU_T]

theorem ma_target_value_fix_top
    (x : ↥(Sanctions.S : Set ℝ)) :
    maV_T x =
      sSup
        ((fun a =>
          maParams.joint_T_top_integrand maV_T maV_S x.val a) ''
          Sanctions.I) :=
  maOf_target_value_fix_top niParams x

/-- The exact stationary upper-selector Stackelberg equilibrium with
nonconstant Target value, over any transition.  Rule 15: constructed; Rule 1:
both policies are optima.  General in `F`. -/
def maEquilibriumOf (p₀ : AbstractGame.Params) :
    (maParamsOf p₀).FeedbackStackelbergEquilibriumTop where
  V_T := maV_T
  V_S := maV_S
  α := niAlpha
  hα := niAlpha_continuous
  α_mem := fun x _ => niAlpha_mem x
  V_S_fix := maOf_sender_value_fix p₀
  V_T_fix_top := maOf_target_value_fix_top p₀
  α_opt_top := fun _ hx => maOf_target_policy_optimal p₀ hx

/-- The exact stationary upper-selector Stackelberg equilibrium with
nonconstant Target value. -/
def maEquilibrium : maParams.FeedbackStackelbergEquilibriumTop where
  V_T := maV_T
  V_S := maV_S
  α := niAlpha
  hα := niAlpha_continuous
  α_mem := fun x _ => niAlpha_mem x
  V_S_fix := ma_sender_value_fix
  V_T_fix_top := ma_target_value_fix_top
  α_opt_top := fun _ hx => ma_target_policy_optimal hx

/-- The realised rule is `(x + 1)/2`, over any transition.  General in `F`. -/
theorem maOf_realized_rule_eq (p₀ : AbstractGame.Params)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    (maParamsOf p₀).dynamicTopRealizedRule
        (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x =
      (x + 1) / 2 := by
  unfold AbstractGame.Params.dynamicTopRealizedRule
  change (maParamsOf p₀).σ_dyn_top maV_S x (1 / 2) =
    (x + 1) / 2
  rw [maOf_sigma_dyn_top_eq, niOf_top_at_half p₀ hx, niIdeal_at_half]

theorem ma_realized_rule_eq
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    maParams.dynamicTopRealizedRule
        maEquilibrium.V_S maEquilibrium.α x =
      (x + 1) / 2 :=
  maOf_realized_rule_eq niParams hx

/-! ## Basin and mechanism activity -/

/-- The joint preference basin `[1/2, 1]` at sanction floor `1/2`, over any
transition.  General in `F`. -/
theorem maJointBasinOf (p₀ : AbstractGame.Params) :
    (maParamsOf p₀).JointPreferenceBasinTop
      (maEquilibriumOf p₀).V_T (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α
      (1 / 2) (1 / 2) where
  xbar_nonneg := by norm_num
  xbar_le_one := by norm_num
  sbar_mem := by constructor <;> norm_num
  target_policy_feasible := by
    intro x _
    exact niAlpha_mem x
  sender_high_argmax_exists := by
    intro x hx
    have hxS : x ∈ Sanctions.S :=
      ⟨le_trans (by norm_num) hx.1, hx.2⟩
    refine ⟨(x + 1) / 2, ?_, ?_, ?_⟩
    · constructor <;> linarith [hxS.1, hxS.2]
    · rw [← maOf_realized_rule_eq p₀ hxS]
      exact (maParamsOf p₀).σ_dyn_top_isMaxOn
        (maEquilibriumOf p₀).V_S x ((maEquilibriumOf p₀).α x)
    · simp only [max_eq_left hx.1]
      linarith [hxS.2]
  top_rule_mono := by
    intro x hx y hy hxy
    have hxS : x ∈ Sanctions.S :=
      ⟨le_trans (by norm_num) hx.1, hx.2⟩
    have hyS : y ∈ Sanctions.S :=
      ⟨le_trans (by norm_num) hy.1, hy.2⟩
    rw [maOf_realized_rule_eq p₀ hxS, maOf_realized_rule_eq p₀ hyS]
    linarith
  target_prefers_sanctions := by
    intro x _hx s₁ _hs₁ s₂ _hs₂ hs₁₂
    change
      (maParamsOf p₀).targetSanctionObjective
          maV_T x (1 / 2) s₁ ≤
        (maParamsOf p₀).targetSanctionObjective
          maV_T x (1 / 2) s₂
    rw [maOf_target_sanction_objective_eq,
      maOf_target_sanction_objective_eq]
    unfold niU_T
    linarith
  target_policy_optimal := by
    intro x hx
    exact maOf_target_policy_optimal p₀
      ⟨le_trans (by norm_num) hx.1, hx.2⟩

theorem maJointBasin :
    maParams.JointPreferenceBasinTop
      maEquilibrium.V_T maEquilibrium.V_S maEquilibrium.α
      (1 / 2) (1 / 2) :=
  maJointBasinOf niParams

/-- **The pivot reversal, priced exactly in the transition** (round BH-5, item
BH5.4).  Over the transition of any economy `p₀`, the Target's stage payoff
alone strictly prefers `a = 9/16` to the equilibrium action `a = 1/2` at the
basin pivot if and only if `F(1/2, 3/4) − F(1/2, 47/64) > 5/1152`.  The two
sanctions are the Sender's responses `3/4` and `47/64` to the two actions; the
stage gain of complying more is `1/256` in compliance cost saved against
`(9/10)·(F(1/2, 3/4) − F(1/2, 47/64))` in successor-state cost avoided.
Rule 22: general in `F`; the condition is a single sanction chord of the
transition at one state. -/
theorem maOf_pivot_choice_reversal_iff (p₀ : AbstractGame.Params) :
    (maParamsOf p₀).U_T (1 / 2) (1 / 2)
        ((maParamsOf p₀).σ_dyn_top maV_S (1 / 2) (1 / 2)) <
      (maParamsOf p₀).U_T (1 / 2) (9 / 16)
        ((maParamsOf p₀).σ_dyn_top maV_S (1 / 2) (9 / 16))
    ↔ 5 / 1152 < p₀.F (1 / 2) (3 / 4) - p₀.F (1 / 2) (47 / 64) := by
  have hx : (1 / 2 : ℝ) ∈ Sanctions.S := by
    constructor <;> norm_num
  have hi9 :
      niIdeal (1 / 2) (9 / 16) ∈ Sanctions.I := by
    constructor <;> norm_num [niIdeal]
  rw [maOf_sigma_dyn_top_eq, niOf_top_at_half p₀ hx,
    maOf_sigma_dyn_top_eq, niOf_top_eq_ideal_of_mem p₀ hi9]
  have h34 : niIdeal (1 / 2) (1 / 2) = 3 / 4 := by norm_num [niIdeal]
  have h4764 : niIdeal (1 / 2) (9 / 16) = 47 / 64 := by norm_num [niIdeal]
  have hm1 := p₀.F_mem (1 / 2) (3 / 4) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
  have hm2 := p₀.F_mem (1 / 2) (47 / 64) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
  rw [maParamsOf_U_T, h34, h4764]
  unfold maU_TOf niU_T
  rw [h34, h4764, clipS_of_mem hm1, clipS_of_mem hm2]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

/-- **A sanction lower chord above `5/18` prices the reversal in.** If raising
the sanction by `Δ` raises next period's state by at least `d·Δ` on the
feasible square, with `d > 5/18`, then
`F(1/2, 3/4) − F(1/2, 47/64) ≥ d/64 > 5/1152`.  Rule 22: general in `F`; only
the lower chord is read, at one state and one pair of sanctions. -/
theorem maOf_pivot_gap_of_lowerChord (p₀ : AbstractGame.Params) {d : ℝ}
    (hlo : Sanctions.TransitionChords.SanctionLowerChord p₀.F d) (hd : 5 / 18 < d) :
    5 / 1152 < p₀.F (1 / 2) (3 / 4) - p₀.F (1 / 2) (47 / 64) := by
  have h := hlo (x := 1 / 2) (s₁ := 47 / 64) (s₂ := 3 / 4)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  have h64 : (3 / 4 : ℝ) - 47 / 64 = 1 / 64 := by norm_num
  rw [h64] at h
  linarith

/-- The pivot reversal at the literal economy: `quadBumpF` has the sanction
lower chord `47/100 > 5/18` (`qbCert_hchord_lo`). -/
theorem ma_pivot_gap :
    5 / 1152 < niParams.F (1 / 2) (3 / 4) - niParams.F (1 / 2) (47 / 64) :=
  maOf_pivot_gap_of_lowerChord niParams (d := 47 / 100) qbCert_hchord_lo (by norm_num)

/-- At the basin pivot, the Target's stage payoff alone strictly prefers
`a = 9/16` to the dynamic equilibrium action `a = 1/2`, over the transition of
any `p₀` whose sanction chord at `x = 1/2` clears `5/1152` (exactly the
condition of `maOf_pivot_choice_reversal_iff`).  General in `F`. -/
theorem maOf_target_continuation_changes_pivot_choice (p₀ : AbstractGame.Params)
    (hgap : 5 / 1152 < p₀.F (1 / 2) (3 / 4) - p₀.F (1 / 2) (47 / 64)) :
    (maParamsOf p₀).U_T
        (1 / 2) (1 / 2)
        ((maParamsOf p₀).σ_dyn_top maV_S (1 / 2) (1 / 2)) <
      (maParamsOf p₀).U_T
        (1 / 2) (9 / 16)
        ((maParamsOf p₀).σ_dyn_top maV_S (1 / 2) (9 / 16)) :=
  (maOf_pivot_choice_reversal_iff p₀).mpr hgap

/-- At the basin pivot, the Target's stage payoff alone strictly prefers
`a = 9/16` to the dynamic equilibrium action `a = 1/2`.  The continuation
term reverses this deviation and makes `1/2` dynamically optimal. -/
theorem ma_target_continuation_changes_pivot_choice :
    maParams.U_T
        (1 / 2) (1 / 2)
        (maParams.σ_dyn_top maV_S (1 / 2) (1 / 2)) <
      maParams.U_T
        (1 / 2) (9 / 16)
        (maParams.σ_dyn_top maV_S (1 / 2) (9 / 16)) :=
  maOf_target_continuation_changes_pivot_choice niParams ma_pivot_gap

/-- **Mechanism-active integrated witness over any transition** (round BH-5,
item BH5.4).  For every economy `p₀` whose sanction chord at the pivot clears
`5/1152` (`hgap`; implied by a sanction lower chord above `5/18`,
`maOf_pivot_gap_of_lowerChord`), one exact equilibrium of `maParamsOf p₀`
combines the transition `p₀.F`, positive discounting for both players, a
strictly increasing Target value, a strict stage-versus-dynamic Target choice
reversal, interior Target and Sender choices at the basin pivot, and the
complete general-`F` persistence evidence on the high basin.  Rule 22: general
in `F`; `hgap` is used only for the reversal conjunct, and by
`maOf_pivot_choice_reversal_iff` it cannot be dropped from it. -/
theorem ma_integrated_mechanism_active_persistence_generalF (p₀ : AbstractGame.Params)
    (hgap : 5 / 1152 < p₀.F (1 / 2) (3 / 4) - p₀.F (1 / 2) (47 / 64)) :
    0 < (maParamsOf p₀).β_T
    ∧ 0 < (maParamsOf p₀).β_S
    ∧ (maParamsOf p₀).F = p₀.F
    ∧ StrictMono (maEquilibriumOf p₀).V_T
    ∧ (maParamsOf p₀).U_T
        (1 / 2) (1 / 2)
        ((maParamsOf p₀).σ_dyn_top
          (maEquilibriumOf p₀).V_S (1 / 2) (1 / 2)) <
      (maParamsOf p₀).U_T
        (1 / 2) (9 / 16)
        ((maParamsOf p₀).σ_dyn_top
          (maEquilibriumOf p₀).V_S (1 / 2) (9 / 16))
    ∧ (0 < (maEquilibriumOf p₀).α (1 / 2)
      ∧ (maEquilibriumOf p₀).α (1 / 2) < 1)
    ∧ (0 <
        (maParamsOf p₀).dynamicTopRealizedRule
          (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α (1 / 2)
      ∧ (maParamsOf p₀).dynamicTopRealizedRule
          (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α (1 / 2) < 1)
    ∧ ∀ x₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∀ n,
        (maParamsOf p₀).dynamicTopLockInPathF
          (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n
            ∈ Set.Icc (1 / 2 : ℝ) 1)
      ∧ (∀ n, (1 / 2 : ℝ) ≤
        (maParamsOf p₀).dynamicTopLockInSanctionsF
          (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n)
      ∧ Monotone
        ((maParamsOf p₀).dynamicTopLockInSanctionsF
          (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀)
      ∧ (∀ n,
        IsMaxOn
          (fun a =>
            (maParamsOf p₀).joint_T_top_integrand
              (maEquilibriumOf p₀).V_T (maEquilibriumOf p₀).V_S
              ((maParamsOf p₀).dynamicTopLockInPathF
                (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n) a)
          Sanctions.I
          ((maEquilibriumOf p₀).α
            ((maParamsOf p₀).dynamicTopLockInPathF
              (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n)))
      ∧ (∀ n,
        IsMaxOn
          (fun s' =>
            (maParamsOf p₀).senderDynObjective (maEquilibriumOf p₀).V_S
              ((maParamsOf p₀).dynamicTopLockInPathF
                (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n)
              ((maEquilibriumOf p₀).α
                ((maParamsOf p₀).dynamicTopLockInPathF
                  (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n))
              s')
          Sanctions.I
          ((maParamsOf p₀).dynamicTopLockInSanctionsF
            (maEquilibriumOf p₀).V_S (maEquilibriumOf p₀).α x₀ n)) := by
  refine
    ⟨by norm_num [maParamsOf_β_T],
      by norm_num [maParamsOf_β_S],
      rfl,
      maV_T_strictMono,
      maOf_target_continuation_changes_pivot_choice p₀ hgap,
      ?_, ?_, ?_⟩
  · norm_num [maEquilibriumOf, niAlpha]
  · have hx : (1 / 2 : ℝ) ∈ Sanctions.S := by
      constructor <;> norm_num
    rw [maOf_realized_rule_eq p₀ hx]
    constructor <;> norm_num
  · intro x₀ hx₀
    obtain
      ⟨hpath, _hsbar, hfloor, hmono, _hfeas,
        htarget, hsender, _htarget_mono⟩ :=
      (maParamsOf p₀).jointPreferenceBasinTopF_long_run_with_equilibrium_evidence
        (maJointBasinOf p₀) hx₀
    exact ⟨hpath, hfloor, hmono, htarget, hsender⟩

/-- **Mechanism-active integrated nonlinear witness.**  One exact
equilibrium combines a non-affine transition, positive discounting for both
players, interior Target and Sender choices at the basin pivot, a strictly
increasing Target value, a strict stage-versus-dynamic Target choice
reversal, and the complete general-`F` persistence evidence on the high
basin.  The member `p₀ := niParams` of
`ma_integrated_mechanism_active_persistence_generalF` (with `ma_pivot_gap`),
plus the non-affinity of `quadBumpF`. -/
theorem ma_integrated_nonaffine_mechanism_active_persistence :
    0 < maParams.β_T
    ∧ 0 < maParams.β_S
    ∧ maParams.F ≠ AbstractGame.affineF (1 / 2)
    ∧ StrictMono maEquilibrium.V_T
    ∧ maParams.U_T
        (1 / 2) (1 / 2)
        (maParams.σ_dyn_top
          maEquilibrium.V_S (1 / 2) (1 / 2)) <
      maParams.U_T
        (1 / 2) (9 / 16)
        (maParams.σ_dyn_top
          maEquilibrium.V_S (1 / 2) (9 / 16))
    ∧ (0 < maEquilibrium.α (1 / 2)
      ∧ maEquilibrium.α (1 / 2) < 1)
    ∧ (0 <
        maParams.dynamicTopRealizedRule
          maEquilibrium.V_S maEquilibrium.α (1 / 2)
      ∧ maParams.dynamicTopRealizedRule
          maEquilibrium.V_S maEquilibrium.α (1 / 2) < 1)
    ∧ ∀ x₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∀ n,
        maParams.dynamicTopLockInPathF
          maEquilibrium.V_S maEquilibrium.α x₀ n
            ∈ Set.Icc (1 / 2 : ℝ) 1)
      ∧ (∀ n, (1 / 2 : ℝ) ≤
        maParams.dynamicTopLockInSanctionsF
          maEquilibrium.V_S maEquilibrium.α x₀ n)
      ∧ Monotone
        (maParams.dynamicTopLockInSanctionsF
          maEquilibrium.V_S maEquilibrium.α x₀)
      ∧ (∀ n,
        IsMaxOn
          (fun a =>
            maParams.joint_T_top_integrand
              maEquilibrium.V_T maEquilibrium.V_S
              (maParams.dynamicTopLockInPathF
                maEquilibrium.V_S maEquilibrium.α x₀ n) a)
          Sanctions.I
          (maEquilibrium.α
            (maParams.dynamicTopLockInPathF
              maEquilibrium.V_S maEquilibrium.α x₀ n)))
      ∧ (∀ n,
        IsMaxOn
          (fun s' =>
            maParams.senderDynObjective maEquilibrium.V_S
              (maParams.dynamicTopLockInPathF
                maEquilibrium.V_S maEquilibrium.α x₀ n)
              (maEquilibrium.α
                (maParams.dynamicTopLockInPathF
                  maEquilibrium.V_S maEquilibrium.α x₀ n))
              s')
          Sanctions.I
          (maParams.dynamicTopLockInSanctionsF
            maEquilibrium.V_S maEquilibrium.α x₀ n)) := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ :=
    ma_integrated_mechanism_active_persistence_generalF niParams ma_pivot_gap
  exact ⟨h1, h2, maParams_F_ne_affine, h4, h5, h6, h7, h8⟩

#print axioms ma_integrated_nonaffine_mechanism_active_persistence


/-! ## The pivot-choice change, in the named vocabulary (Rule 5)

`ma_target_continuation_changes_pivot_choice` is a statement at a *solved*
equilibrium: the forward-looking argmax `1/2` is strictly beaten on the stage
objective by `9/16`. That is exactly the shape of
`continuationChangesTargetChoiceSomewhereAt_of_stage_better`, read against the
Sender's own dynamic response, so the existing theorem discharges the
existential predicate directly — no uniqueness argument, and the equilibrium's
own selector as `ρ`. -/

/-- **The continuation changes the Target's optimal compliance at the basin
pivot**, at the solved equilibrium over the transition of any `p₀` whose
sanction chord at the pivot clears `5/1152`.  General in `F`. -/
theorem maOf_continuationChangesTargetChoiceSomewhere (p₀ : AbstractGame.Params)
    (hgap : 5 / 1152 < p₀.F (1 / 2) (3 / 4) - p₀.F (1 / 2) (47 / 64)) :
    (maParamsOf p₀).ContinuationChangesTargetChoiceSomewhereAt
      ((maParamsOf p₀).σ_dyn_top maV_S) maV_T (1 / 2) := by
  have hx : (1 / 2 : ℝ) ∈ Sanctions.S := ⟨by norm_num, by norm_num⟩
  refine (maParamsOf p₀).continuationChangesTargetChoiceSomewhereAt_of_stage_better
    (a := 1 / 2) (a' := 9 / 16)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ?_
    (maOf_target_continuation_changes_pivot_choice p₀ hgap)
  have := maOf_target_policy_optimal p₀ hx
  simpa [AbstractGame.Params.joint_T_top_integrand,
    AbstractGame.Params.targetComplianceContinuation, niAlpha] using this

/-- **The continuation changes the Target's optimal compliance at the basin
pivot**, at the solved non-affine equilibrium. -/
theorem ma_continuationChangesTargetChoiceSomewhere :
    maParams.ContinuationChangesTargetChoiceSomewhereAt
      (maParams.σ_dyn_top maV_S) maV_T (1 / 2) :=
  maOf_continuationChangesTargetChoiceSomewhere niParams ma_pivot_gap

#print axioms ma_continuationChangesTargetChoiceSomewhere
#print axioms ma_integrated_mechanism_active_persistence_generalF
#print axioms maOf_pivot_choice_reversal_iff

end

end Examples
end Sanctions
