/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticPolicyCenterResidual.lean

Second-order Sender Bellman residual at the actual-transition static-policy
evaluation center.

The center already evaluates the static Stackelberg policies under the true
transition.  The only Sender-row discrepancy is therefore the gain from
reoptimizing sanctions against the continuation value.  Static Sender
quadratic growth and the action-Lipschitz continuation channel give an exact
completed-square bound of order delta squared.

No numerical convergence premise or new model assumption is used.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyReferenceCenter
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPerturbation
import Sanctions.Foundations.QuadraticGrowthPerturbation

namespace Sanctions
namespace Examples

open Set
open AbstractGame
open BoundedContinuousFunction

/-- Moving averaging preserves the sharp state-Lipschitz modulus of the
actual-transition Sender policy-evaluation center. -/
theorem lowDeltaStaticSenderPolicyCenter_smear_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
      (16362665 / 4046689) := by
  simpa only [lowDeltaShocked] using
    (Sanctions.AbstractGame.movAvgShockedParams_smear_valueLipschitz
      lowDeltaParams lowDeltaH_pos
      (by norm_num : (0 : ℝ) ≤ 16362665 / 4046689)
      lowDeltaStaticSenderPolicyCenter_valueLipschitz)

/-- The actual-transition policy pullback is nonexpansive in norm. -/
theorem lowDeltaStaticPolicyPullback_norm_le (V : SBCF) :
    ‖lowDeltaStaticPolicyPullback V‖ ≤ ‖V‖ := by
  have h :=
    lowDeltaStaticPolicyPullback_dist_le V (0 : SBCF)
  have hzero :
      lowDeltaStaticPolicyPullback (0 : SBCF) = 0 := by
    ext x
    simp [lowDeltaStaticPolicyPullback,
      Sanctions.closedLoopPullback, Sanctions.movAvgReal]
  simpa only [hzero, dist_zero_right] using h

/-- The actual-transition Sender policy-evaluation center retains the global
Sender sup-norm budget `523/160`. -/
theorem lowDeltaStaticSenderPolicyCenter_norm_le :
    ‖lowDeltaStaticSenderPolicyCenter‖ ≤ 523 / 160 := by
  have hEq := lowDeltaStaticSenderPolicyCenter_isFixedPoint
  have hnorm :
      ‖lowDeltaStaticSenderPolicyCenter‖ ≤
        ‖lowDeltaFrozenSenderStage‖ +
          (1 / 2) *
            ‖lowDeltaStaticPolicyPullback
              lowDeltaStaticSenderPolicyCenter‖ := by
    calc
      ‖lowDeltaStaticSenderPolicyCenter‖ =
          ‖lowDeltaStaticPolicyOperator (1 / 2)
            lowDeltaFrozenSenderStage
            lowDeltaStaticSenderPolicyCenter‖ := by
              rw [hEq]
      _ ≤ ‖lowDeltaFrozenSenderStage‖ +
          ‖(1 / 2 : ℝ) •
            lowDeltaStaticPolicyPullback
              lowDeltaStaticSenderPolicyCenter‖ :=
        norm_add_le _ _
      _ = ‖lowDeltaFrozenSenderStage‖ +
          (1 / 2) *
            ‖lowDeltaStaticPolicyPullback
              lowDeltaStaticSenderPolicyCenter‖ := by
        rw [norm_smul]
        norm_num [Real.norm_eq_abs]
  have hpull :=
    lowDeltaStaticPolicyPullback_norm_le
      lowDeltaStaticSenderPolicyCenter
  linarith [lowDeltaFrozenSenderStage_norm_le]

/-- The actual-transition Sender center belongs to the already-defined global
Sender regularity carrier. -/
theorem lowDeltaStaticSenderPolicyCenter_mem_coupledCarrierS :
    lowDeltaStaticSenderPolicyCenter ∈ coupledCarrierS := by
  have hlegacy :
      lowDeltaStaticSenderPolicyCenter ∈
        Params.valLipBall (523 / 160) (57377 / 3200) := by
    constructor
    · exact lowDeltaStaticSenderPolicyCenter_norm_le
    · intro x y
      exact
        (lowDeltaStaticSenderPolicyCenter_valueLipschitz x y).trans
          (mul_le_mul_of_nonneg_right (by norm_num) dist_nonneg)
  simpa only [coupledCarrierS, lowDeltaSenderCarrierNorm_eq,
    lowDeltaSenderCarrierLip_eq] using hlegacy

/-- The greatest dynamic Sender selector at the actual-transition Sender
center is jointly continuous on physical states and Target actions. -/
theorem lowDeltaStaticSenderPolicyCenter_sigmaDynTop_continuous :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      lowDeltaParams.σ_dyn_top
        (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
        xa.1.val xa.2) := by
  exact
    coupled_sigmaDynTop_continuous_subtype
      lowDeltaStaticSenderPolicyCenter
      lowDeltaStaticSenderPolicyCenter_mem_coupledCarrierS.2

/-- At a fixed state, the discounted continuation term changes by at most
`(K_S/200)|s-s₀|` when sanctions move away from the static Sender response. -/
theorem lowDeltaStaticSenderPolicyCenter_continuation_lipschitz_action
    (x : ↥(Sanctions.S : Set ℝ)) (s : ℝ) :
    |(1 / 2 : ℝ) *
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
            (Sanctions.clipS' (lowDeltaParams.F x.val s)) -
        (1 / 2 : ℝ) *
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
            (Sanctions.clipS' (lowDeltaParams.F x.val
              (lowDeltaStaticSenderPolicy x.val)))| ≤
      ((16362665 / 4046689 : ℝ) / 200) *
        |s - lowDeltaStaticSenderPolicy x.val| := by
  let ys := Sanctions.clipS' (lowDeltaParams.F x.val s)
  let y₀ := Sanctions.clipS'
    (lowDeltaParams.F x.val (lowDeltaStaticSenderPolicy x.val))
  have hdist :
      dist y₀ ys ≤
        (1 / 100 : ℝ) *
          |s - lowDeltaStaticSenderPolicy x.val| := by
    have h :=
      lowDelta_clipF_lip x.val
        (lowDeltaStaticSenderPolicy x.val) s
    simpa only [ys, y₀, Subtype.dist_eq, Real.dist_eq,
      abs_sub_comm] using h
  have hvalue :
      |(lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) ys -
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) y₀| ≤
        (16362665 / 4046689 : ℝ) *
          ((1 / 100 : ℝ) *
            |s - lowDeltaStaticSenderPolicy x.val|) := by
    exact
      (lowDeltaStaticSenderPolicyCenter_smear_valueLipschitz y₀ ys).trans
        (mul_le_mul_of_nonneg_left hdist (by norm_num))
  change
    |(1 / 2 : ℝ) *
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) ys -
        (1 / 2 : ℝ) *
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) y₀| ≤
      ((16362665 / 4046689 : ℝ) / 200) *
        |s - lowDeltaStaticSenderPolicy x.val|
  rw [show
      (1 / 2 : ℝ) *
            (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) ys -
          (1 / 2 : ℝ) *
            (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) y₀ =
        (1 / 2 : ℝ) *
          ((lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) ys -
            (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) y₀) by
      ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) *
        |(lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) ys -
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) y₀|
      ≤ (1 / 2 : ℝ) *
          ((16362665 / 4046689 : ℝ) *
            ((1 / 100 : ℝ) *
              |s - lowDeltaStaticSenderPolicy x.val|)) := by
        gcongr
    _ = ((16362665 / 4046689 : ℝ) / 200) *
        |s - lowDeltaStaticSenderPolicy x.val| := by ring

/-- Pointwise second-order Sender Bellman residual at the actual-transition
static-policy evaluation center. -/
theorem lowDeltaStaticSenderPolicyCenter_bellman_residual_pointwise
    (x : ↥(Sanctions.S : Set ℝ)) :
    |lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaStaticSenderPolicyCenter x -
        lowDeltaStaticSenderPolicyCenter x| ≤
      (16362665 / 4046689 : ℝ) ^ 2 / 96000 := by
  let f : ℝ → ℝ := fun s =>
    mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s
  let g : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) *
      (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
        (Sanctions.clipS' (lowDeltaParams.F x.val s))
  let s₀ : ℝ := lowDeltaStaticSenderPolicy x.val
  have hs₀ : s₀ ∈ Sanctions.I := by
    simpa only [s₀] using lowDeltaStaticSenderPolicy_mem x.val
  have hgrowth :
      ∀ s ∈ Sanctions.I,
        (3 / 5 : ℝ) * (s - s₀) ^ 2 ≤ f s₀ - f s := by
    intro s hs
    simpa only [f, s₀, lowDeltaStaticSenderPolicy] using
      lowDeltaStaticSenderPolicy_quadraticGrowth
        (x := x.val) (a := lowDeltaStaticTargetPolicy x.val)
        (s := s) hs
  have hperturb :
      ∀ s ∈ Sanctions.I,
        |g s - g s₀| ≤
          ((16362665 / 4046689 : ℝ) / 200) * |s - s₀| := by
    intro s _hs
    simpa only [g, s₀] using
      lowDeltaStaticSenderPolicyCenter_continuation_lipschitz_action x s
  have hsup :=
    Sanctions.abs_sSup_add_perturbation_sub_base_le
      hs₀ (by norm_num : (0 : ℝ) < 3 / 5)
      hgrowth hperturb
  have hbase :
      f s₀ + g s₀ = lowDeltaStaticSenderPolicyCenter x := by
    have hF :
        lowDeltaParams.F x.val s₀ ∈ Sanctions.S :=
      lowDeltaParams.F_mem x.val s₀ x.property hs₀
    rw [lowDeltaStaticSenderPolicyCenter_eq]
    simp only [lowDeltaFrozenSenderStage_apply,
      lowDeltaStaticPolicyPullback_apply, f, g, s₀,
      lowDeltaStaticPolicyDrift, lowDeltaShocked_smear,
      Sanctions.movAvgBCF_apply]
    rw [Sanctions.clipS'_val_eq_of_mem hF]
  rw [AbstractGame.ShockedParams.bellmanS_shock]
  change
    |sSup ((fun s =>
        mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s +
          (1 / 2 : ℝ) *
            (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
              (Sanctions.clipS' (lowDeltaParams.F x.val s))) ''
          Sanctions.I) -
        lowDeltaStaticSenderPolicyCenter x| ≤
      (16362665 / 4046689 : ℝ) ^ 2 / 96000
  rw [← hbase]
  convert hsup using 1
  norm_num [f, g]

/-- Sup-norm form of the second-order Sender Bellman residual. -/
theorem lowDeltaStaticSenderPolicyCenter_bellman_residual :
    dist
        (lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaStaticSenderPolicyCenter)
        lowDeltaStaticSenderPolicyCenter ≤
      (16362665 / 4046689 : ℝ) ^ 2 / 96000 := by
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro x
  rw [Real.dist_eq]
  exact lowDeltaStaticSenderPolicyCenter_bellman_residual_pointwise x

end Examples
end Sanctions
