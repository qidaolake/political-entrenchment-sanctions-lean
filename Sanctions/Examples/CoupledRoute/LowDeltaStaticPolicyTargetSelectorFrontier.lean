/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticPolicyTargetSelectorFrontier.lean

The exact Target-selector frontier at the actual-transition static-policy
reference center.

The actual dynamic Target objective is jointly continuous on physical states
and Target actions, so it has at least one global maximizer at every state.  We
construct a choice selector, prove that it attains the Target Bellman value,
and localize every possible maximizer within `69/200` of the exact static
Stackelberg policy.

This file deliberately does not claim uniqueness or continuity of the choice
selector.  The available relative perturbation/localization inequality cannot
imply uniqueness: an exact continuous perturbation of a strictly concave
quadratic, with error proportional only to action displacement, has two
distinct global maxima.  A further theorem controlling the shape of the
endogenous-Sender composite objective is therefore still required.

No numerical simulation or additional model assumption enters any statement.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCarrierPacket
import Sanctions.Examples.CoupledRoute.LowDeltaRefinedTargetLocalization

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.AbstractGame.Params
open BoundedContinuousFunction
open scoped NNReal

noncomputable section

/-! ## The exact center objective and its continuity -/

/-- The actual dynamic Target objective at the two actual-transition
static-policy evaluation values. -/
noncomputable def lowDeltaStaticPolicyDynamicTargetObjective
    (x a : ℝ) : ℝ :=
  lowDeltaParams.joint_T_top_integrand
    (lowDeltaShocked.smear lowDeltaStaticTargetPolicyCenter)
    (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) x a

/-- The continuously state-clamped representation used only to prove
continuity.  It agrees with the economic objective on every physical state. -/
private noncomputable def lowDeltaStaticPolicyClampedTargetObjective
    (x a : ℝ) : ℝ :=
  lowDeltaParams.targetDynIntegrand
    (coupledSigmaClamped lowDeltaStaticSenderPolicyCenter)
    (lowDeltaShocked.smear lowDeltaStaticTargetPolicyCenter) x a

private theorem lowDeltaStaticPolicyDynamicTargetObjective_eq_clamped
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    lowDeltaStaticPolicyDynamicTargetObjective x a =
      lowDeltaStaticPolicyClampedTargetObjective x a := by
  simp only [lowDeltaStaticPolicyDynamicTargetObjective,
    lowDeltaStaticPolicyClampedTargetObjective,
    Sanctions.AbstractGame.Params.joint_T_top_integrand,
    Sanctions.AbstractGame.Params.targetDynIntegrand,
    coupledSigmaClamped, lowDeltaShocked_toParams]
  rw [lowDeltaParams.σ_dyn_top_clamped_eq_of_mem
    (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) hx]

private theorem lowDeltaStaticPolicyClampedTargetObjective_continuous :
    Continuous (fun xa : ℝ × ℝ =>
      lowDeltaStaticPolicyClampedTargetObjective xa.1 xa.2) := by
  exact
    lowDeltaParams.targetDynIntegrand_continuous
      (coupledSigmaClamped lowDeltaStaticSenderPolicyCenter)
      (lowDeltaShocked.smear lowDeltaStaticTargetPolicyCenter)
      (coupledSigmaClamped_continuous
        lowDeltaStaticSenderPolicyCenter
        lowDeltaStaticSenderPolicyCenter_mem_coupledCarrierS.2)

/-- The actual Target objective is jointly continuous in the physical state
and Target action. -/
theorem lowDeltaStaticPolicyDynamicTargetObjective_continuous :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      lowDeltaStaticPolicyDynamicTargetObjective xa.1.val xa.2) := by
  have hclamped :
      Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        lowDeltaStaticPolicyClampedTargetObjective xa.1.val xa.2) :=
    lowDeltaStaticPolicyClampedTargetObjective_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  convert hclamped using 1
  funext xa
  exact
    lowDeltaStaticPolicyDynamicTargetObjective_eq_clamped
      xa.1.property xa.2

/-! ## Existence and a globally optimal choice selector -/

/-- At each physical state, the exact center objective has a global maximizer
on the compact Target action interval. -/
theorem lowDeltaStaticPolicyDynamicTargetObjective_exists_isMaxOn
    (x : ↥(Sanctions.S : Set ℝ)) :
    ∃ a ∈ Sanctions.I,
      IsMaxOn
        (lowDeltaStaticPolicyDynamicTargetObjective x.val)
        Sanctions.I a := by
  have hcont :
      Continuous (lowDeltaStaticPolicyClampedTargetObjective x.val) :=
    lowDeltaStaticPolicyClampedTargetObjective_continuous.comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨a, ha, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
      hcont.continuousOn
  refine ⟨a, ha, ?_⟩
  intro b hb
  change
    lowDeltaStaticPolicyDynamicTargetObjective x.val b ≤
      lowDeltaStaticPolicyDynamicTargetObjective x.val a
  rw [lowDeltaStaticPolicyDynamicTargetObjective_eq_clamped x.property b,
    lowDeltaStaticPolicyDynamicTargetObjective_eq_clamped x.property a]
  exact hmax hb

/-- A choice of a genuine global Target maximizer at each physical state.
No continuity claim is made. -/
noncomputable def lowDeltaStaticPolicyTargetArgmax
    (x : ↥(Sanctions.S : Set ℝ)) : ℝ :=
  Classical.choose
    (lowDeltaStaticPolicyDynamicTargetObjective_exists_isMaxOn x)

theorem lowDeltaStaticPolicyTargetArgmax_mem
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaStaticPolicyTargetArgmax x ∈ Sanctions.I :=
  (Classical.choose_spec
    (lowDeltaStaticPolicyDynamicTargetObjective_exists_isMaxOn x)).1

/-- The chosen action is globally Target-optimal, not a hand-chosen policy. -/
theorem lowDeltaStaticPolicyTargetArgmax_isMaxOn
    (x : ↥(Sanctions.S : Set ℝ)) :
    IsMaxOn
      (lowDeltaStaticPolicyDynamicTargetObjective x.val)
      Sanctions.I
      (lowDeltaStaticPolicyTargetArgmax x) :=
  (Classical.choose_spec
    (lowDeltaStaticPolicyDynamicTargetObjective_exists_isMaxOn x)).2

/-- The selected global maximizer realizes the actual Target Bellman value at
the static-policy reference-center pair. -/
theorem lowDeltaStaticPolicyTargetArgmax_realizes_bellman
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaStaticPolicyTargetBellman x =
      lowDeltaStaticPolicyDynamicTargetObjective
        x.val (lowDeltaStaticPolicyTargetArgmax x) := by
  rw [lowDeltaStaticPolicyTargetBellman_apply]
  apply IsGreatest.csSup_eq
  constructor
  · exact
      ⟨lowDeltaStaticPolicyTargetArgmax x,
        lowDeltaStaticPolicyTargetArgmax_mem x, rfl⟩
  · rintro y ⟨a, ha, rfl⟩
    exact lowDeltaStaticPolicyTargetArgmax_isMaxOn x ha

/-! ## Exact maximizer localization -/

/-- Every global maximizer satisfies the exact refined quadratic inequality
obtained from the existing center moduli. -/
theorem lowDeltaStaticPolicyTargetMaximizer_refined_quadratic
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax :
      IsMaxOn
        (lowDeltaStaticPolicyDynamicTargetObjective x)
        Sanctions.I a) :
    (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤
      2 * ((16362665 / 4046689 : ℝ) / 120) +
        (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) *
          (2 * ((16362665 / 4046689 : ℝ) / 120) +
            (5 / 12 : ℝ) *
              |a - lowDeltaStaticTargetPolicy x|) := by
  exact
    lowDelta_jointTarget_maximizer_refined_quadratic
      (lowDeltaShocked.smear lowDeltaStaticTargetPolicyCenter)
      (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
      lowDeltaStaticTargetPolicyCenter_smear_valueLipschitz
      lowDeltaStaticSenderPolicyCenter_smear_valueLipschitz
      hx ha
      (by
        simpa only [lowDeltaStaticPolicyDynamicTargetObjective] using hmax)

/-- The refined inequality implies the simple uniform displacement bound
`69/200`.  This applies to every maximizer, independently of the choice made
above. -/
theorem lowDeltaStaticPolicyTargetMaximizer_abs_sub_static_le
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax :
      IsMaxOn
        (lowDeltaStaticPolicyDynamicTargetObjective x)
        Sanctions.I a) :
    |a - lowDeltaStaticTargetPolicy x| ≤ (69 / 200 : ℝ) := by
  let q : ℝ := |a - lowDeltaStaticTargetPolicy x|
  let C : ℝ :=
    2 * ((16362665 / 4046689 : ℝ) / 120) +
      (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) *
        (2 * ((16362665 / 4046689 : ℝ) / 120))
  let L : ℝ :=
    (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) *
      (5 / 12)
  have hraw :=
    lowDeltaStaticPolicyTargetMaximizer_refined_quadratic hx ha hmax
  have hsq :
      q ^ 2 = (a - lowDeltaStaticTargetPolicy x) ^ 2 := by
    exact sq_abs (a - lowDeltaStaticTargetPolicy x)
  have hq : q ^ 2 ≤ C + L * q := by
    dsimp [C, L, q]
    rw [hsq]
    nlinarith [hraw]
  have hC :
      C + L * (69 / 200 : ℝ) < (69 / 200 : ℝ) ^ 2 := by
    norm_num [C, L]
  have hL : L < 2 * (69 / 200 : ℝ) := by
    norm_num [L]
  have hq0 : 0 ≤ q := by
    simp [q]
  by_contra hnot
  have hgt : (69 / 200 : ℝ) < q := lt_of_not_ge hnot
  have hfac :
      0 < (q - 69 / 200) * (q + 69 / 200 - L) := by
    apply mul_pos
    · linarith
    · nlinarith
  nlinarith

/-- The globally optimal choice selector inherits the same displacement
bound. -/
theorem lowDeltaStaticPolicyTargetArgmax_abs_sub_static_le
    (x : ↥(Sanctions.S : Set ℝ)) :
    |lowDeltaStaticPolicyTargetArgmax x -
        lowDeltaStaticTargetPolicy x.val| ≤ (69 / 200 : ℝ) :=
  lowDeltaStaticPolicyTargetMaximizer_abs_sub_static_le
    x.property
    (lowDeltaStaticPolicyTargetArgmax_mem x)
    (lowDeltaStaticPolicyTargetArgmax_isMaxOn x)

/-! ## Strongest derivative control currently supplied by the centers -/

/-- The Target center's smoothed continuation has the derivative-Lipschitz
bound inherited from its proved value-Lipschitz modulus. -/
theorem lowDeltaStaticTargetPolicyCenter_movAvg_deriv_lipschitz
    (y y' : ℝ) :
    |deriv
          (movAvgReal (1 / 10) lowDeltaStaticTargetPolicyCenter) y -
        deriv
          (movAvgReal (1 / 10) lowDeltaStaticTargetPolicyCenter) y'| ≤
      ((3855250 / 142269 : ℝ) / (1 / 10)) * |y - y'| :=
  movAvgReal_deriv_lipschitz_of_valueLipschitz
    (by norm_num)
    lowDeltaStaticTargetPolicyCenter
    (by norm_num)
    lowDeltaStaticTargetPolicyCenter_valueLipschitz
    y y'

/-- The Sender center's smoothed continuation has the corresponding exact
derivative-Lipschitz bound. -/
theorem lowDeltaStaticSenderPolicyCenter_movAvg_deriv_lipschitz
    (y y' : ℝ) :
    |deriv
          (movAvgReal (1 / 10) lowDeltaStaticSenderPolicyCenter) y -
        deriv
          (movAvgReal (1 / 10) lowDeltaStaticSenderPolicyCenter) y'| ≤
      ((16362665 / 4046689 : ℝ) / (1 / 10)) * |y - y'| :=
  movAvgReal_deriv_lipschitz_of_valueLipschitz
    (by norm_num)
    lowDeltaStaticSenderPolicyCenter
    (by norm_num)
    lowDeltaStaticSenderPolicyCenter_valueLipschitz
    y y'

/-! ## Refutation: localization alone cannot imply uniqueness -/

/-- A continuous objective that differs from the strictly concave quadratic
`-(a-1/2)^2` by exactly `(1/100)|a-1/2|`. -/
noncomputable def lowDeltaRelativePerturbationCounterexampleObjective
    (a : ℝ) : ℝ :=
  -(a - 1 / 2) ^ 2 + (1 / 100) * |a - 1 / 2|

theorem lowDeltaRelativePerturbationCounterexample_exact_bound
    (a : ℝ) :
    |lowDeltaRelativePerturbationCounterexampleObjective a -
        (-(a - 1 / 2) ^ 2)| =
      (1 / 100 : ℝ) * |a - 1 / 2| := by
  dsimp [lowDeltaRelativePerturbationCounterexampleObjective]
  rw [show
      -(a - 1 / 2) ^ 2 + (1 / 100 : ℝ) * |a - 1 / 2| -
          (-(a - 1 / 2) ^ 2) =
        (1 / 100) * |a - 1 / 2| by ring,
    abs_mul, abs_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]

theorem lowDeltaRelativePerturbationCounterexample_left_isMaxOn :
    IsMaxOn
      lowDeltaRelativePerturbationCounterexampleObjective
      Sanctions.I (99 / 200) := by
  intro a ha
  have hs :=
    sq_nonneg (|a - 1 / 2| - (1 / 200 : ℝ))
  have habs :
      |a - 1 / 2| ^ 2 = (a - 1 / 2) ^ 2 :=
    sq_abs _
  dsimp [lowDeltaRelativePerturbationCounterexampleObjective]
  norm_num
  nlinarith

theorem lowDeltaRelativePerturbationCounterexample_right_isMaxOn :
    IsMaxOn
      lowDeltaRelativePerturbationCounterexampleObjective
      Sanctions.I (101 / 200) := by
  intro a ha
  have hs :=
    sq_nonneg (|a - 1 / 2| - (1 / 200 : ℝ))
  have habs :
      |a - 1 / 2| ^ 2 = (a - 1 / 2) ^ 2 :=
    sq_abs _
  dsimp [lowDeltaRelativePerturbationCounterexampleObjective]
  norm_num
  nlinarith

/-- The exact relative perturbation has two distinct global maximizers.  Thus
even a much smaller relative error than the current center estimate does not
by itself yield Target-argmax uniqueness. -/
theorem lowDeltaRelativePerturbationCounterexample_two_maxima :
    (99 / 200 : ℝ) ≠ 101 / 200 ∧
      IsMaxOn
        lowDeltaRelativePerturbationCounterexampleObjective
        Sanctions.I (99 / 200) ∧
      IsMaxOn
        lowDeltaRelativePerturbationCounterexampleObjective
        Sanctions.I (101 / 200) := by
  exact
    ⟨by norm_num,
      lowDeltaRelativePerturbationCounterexample_left_isMaxOn,
      lowDeltaRelativePerturbationCounterexample_right_isMaxOn⟩

/-- The project-specific refined localization inequality is itself compatible
with two distinct feasible candidate actions.  This is an arithmetic
obstruction to using that necessary inequality as a uniqueness proof. -/
def LowDeltaStaticPolicyTargetLocalizationInequality
    (x a : ℝ) : Prop :=
  (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤
    2 * ((16362665 / 4046689 : ℝ) / 120) +
      (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) *
        (2 * ((16362665 / 4046689 : ℝ) / 120) +
          (5 / 12 : ℝ) *
            |a - lowDeltaStaticTargetPolicy x|)

private theorem lowDeltaStaticTargetPolicy_one :
    lowDeltaStaticTargetPolicy 1 = (63 / 116 : ℝ) := by
  rw [lowDeltaStaticTargetPolicy_eq]
  norm_num [max_eq_right]

theorem
    lowDeltaStaticPolicyTargetLocalizationInequality_not_unique :
    ¬ (∀ a b : ℝ,
      a ∈ Sanctions.I →
      b ∈ Sanctions.I →
      LowDeltaStaticPolicyTargetLocalizationInequality 1 a →
      LowDeltaStaticPolicyTargetLocalizationInequality 1 b →
      a = b) := by
  intro h
  have heq :=
    h
      ((63 / 116 : ℝ) - 1 / 100)
      ((63 / 116 : ℝ) + 1 / 100)
      (by norm_num)
      (by norm_num)
      (by
        norm_num [
          LowDeltaStaticPolicyTargetLocalizationInequality,
          lowDeltaStaticTargetPolicy_one])
      (by
        norm_num [
          LowDeltaStaticPolicyTargetLocalizationInequality,
          lowDeltaStaticTargetPolicy_one])
  norm_num at heq

end
end Examples
end Sanctions
