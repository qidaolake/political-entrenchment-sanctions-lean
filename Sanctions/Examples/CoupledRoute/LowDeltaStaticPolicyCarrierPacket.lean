/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticPolicyCarrierPacket.lean

Carrier membership of the actual-transition static-policy reference pair.

These are validation-center facts.  They neither replace the endogenous
two-sided policies nor assert that the coupled operator preserves a local
ball.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyExpandedPerovBudget
import Sanctions.Examples.CoupledRoute.CoupledCarrierRedesign

namespace Sanctions
namespace Examples

open AbstractGame BoundedContinuousFunction

/-- The actual-transition Target policy-evaluation center satisfies the
primitive-derived Target sup-norm budget. -/
theorem lowDeltaStaticTargetPolicyCenter_norm_le :
    ‖lowDeltaStaticTargetPolicyCenter‖ ≤ lowDeltaTargetCarrierNorm := by
  have hEq := lowDeltaStaticTargetPolicyCenter_isFixedPoint
  have hnorm :
      ‖lowDeltaStaticTargetPolicyCenter‖ ≤
        ‖lowDeltaFrozenTargetStage‖ +
          (9 / 10) *
            ‖lowDeltaStaticPolicyPullback
              lowDeltaStaticTargetPolicyCenter‖ := by
    calc
      ‖lowDeltaStaticTargetPolicyCenter‖ =
          ‖lowDeltaStaticPolicyOperator (9 / 10)
            lowDeltaFrozenTargetStage
            lowDeltaStaticTargetPolicyCenter‖ := by
              rw [hEq]
      _ ≤ ‖lowDeltaFrozenTargetStage‖ +
          ‖(9 / 10 : ℝ) •
            lowDeltaStaticPolicyPullback
              lowDeltaStaticTargetPolicyCenter‖ :=
        norm_add_le _ _
      _ = ‖lowDeltaFrozenTargetStage‖ +
          (9 / 10) *
            ‖lowDeltaStaticPolicyPullback
              lowDeltaStaticTargetPolicyCenter‖ := by
        rw [norm_smul]
        norm_num [Real.norm_eq_abs]
  have hpull :=
    lowDeltaStaticPolicyPullback_norm_le
      lowDeltaStaticTargetPolicyCenter
  have hstage :
      ‖lowDeltaFrozenTargetStage‖ ≤ lowDeltaTargetStageBound := by
    simpa only [lowDeltaTargetStageBound] using
      lowDeltaFrozenTargetStage_norm_le
  have hmargin :=
    lowDeltaParams.carrierMinNormT_margin_eq
      lowDeltaTargetStageBound
  have hβT_lt : lowDeltaParams.β_T < 1 :=
    lowDeltaParams.β_T_mem.2
  rw [lowDeltaParams_β_T] at hmargin hβT_lt
  change
    ‖lowDeltaStaticTargetPolicyCenter‖ ≤
      lowDeltaParams.carrierMinNormT lowDeltaTargetStageBound
  linarith

/-- The actual-transition Target center belongs to the redesigned
norm-Lipschitz Target carrier. -/
theorem lowDeltaStaticTargetPolicyCenter_mem_coupledCarrierTLip :
    lowDeltaStaticTargetPolicyCenter ∈ coupledCarrierTLip := by
  rw [coupledCarrierTLip, targetPrimitiveValLipCarrier]
  constructor
  · exact lowDeltaStaticTargetPolicyCenter_norm_le
  · intro x y
    have hK : (3855250 / 142269 : ℝ) ≤ coupledTargetLipK := by
      rw [coupledTargetLipK_eq]
      norm_num
    exact
      (lowDeltaStaticTargetPolicyCenter_valueLipschitz x y).trans
        (mul_le_mul_of_nonneg_right hK dist_nonneg)

/-- The actual-transition static-policy reference pair is in the redesigned
Target carrier and the existing Sender carrier. -/
theorem lowDeltaStaticPolicyCenterPair_mem_carriers :
    lowDeltaStaticTargetPolicyCenter ∈ coupledCarrierTLip ∧
      lowDeltaStaticSenderPolicyCenter ∈ coupledCarrierS :=
  ⟨lowDeltaStaticTargetPolicyCenter_mem_coupledCarrierTLip,
    lowDeltaStaticSenderPolicyCenter_mem_coupledCarrierS⟩

end Examples
end Sanctions
