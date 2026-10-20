/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticPolicyCenterBudget.lean

Exact local-Perov budget arithmetic for the actual-transition static-policy
evaluation center.

The Sender residual proved at this center fits the already-selected Sender
allowance.  The generic Target estimate obtained by replacing the static
Sender response with only its global displacement bound does not fit the
Target allowance.  That second comparison refutes the sufficiency of the
generic upper bound only; it does not lower-bound the true Target residual.

No numerical convergence premise or new model assumption is used.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCenterResidual
import Sanctions.Examples.CoupledRoute.LowDeltaRefinedPerovBudget

namespace Sanctions
namespace Examples

open AbstractGame

/-! ## Sender row -/

/-- Reduced rational form of the actual-transition Sender residual bound. -/
theorem lowDelta_staticPolicySenderResidualBound_eq :
    ((16362665 / 4046689 : ℝ) ^ 2 / 96000) =
      10709472236089 / 62882656752848640 := by
  norm_num

/-- The second-order Sender residual bound at the actual-transition
static-policy center is strictly below the existing Sender-row allowance. -/
theorem lowDelta_staticPolicySenderResidualBound_lt_localAllowance :
    ((16362665 / 4046689 : ℝ) ^ 2 / 96000) <
      2275459929739 / 221799538143400 := by
  norm_num

/-- Consequently, the proved Sender Bellman residual itself is strictly below
the existing Sender-row allowance. -/
theorem lowDeltaStaticSenderPolicyCenter_bellman_residual_lt_localAllowance :
    dist
        (lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaStaticSenderPolicyCenter)
        lowDeltaStaticSenderPolicyCenter <
      2275459929739 / 221799538143400 := by
  exact lt_of_le_of_lt
    lowDeltaStaticSenderPolicyCenter_bellman_residual
    lowDelta_staticPolicySenderResidualBound_lt_localAllowance

/-! ## Exact Sender-policy displacement -/

/-- Reduced rational form of the dynamic Sender displacement budget
`K_S/120` at the actual-transition center. -/
theorem lowDelta_staticPolicySenderDisplacement_eq :
    ((16362665 / 4046689 : ℝ) / 120) =
      3272533 / 97120536 := by
  norm_num

/-- The second-order residual completion is exactly `(3/20)` times the square
of the associated Sender displacement budget. -/
theorem lowDelta_staticPolicySenderResidual_eq_quadraticDisplacement :
    ((16362665 / 4046689 : ℝ) ^ 2 / 96000) =
      (3 / 20) * ((16362665 / 4046689) / 120) ^ 2 := by
  ring

/-- The greatest dynamic Sender response at the actual-transition center is
uniformly within the exact distance `3272533/97120536` of the static Sender
response. -/
theorem lowDeltaStaticSenderPolicyCenter_sigmaDynTop_abs_sub_staticSender_le
    (x a : ℝ) :
    |lowDeltaParams.σ_dyn_top
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) x a -
        mwσ x a| ≤
      3272533 / 97120536 := by
  calc
    |lowDeltaParams.σ_dyn_top
          (lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter) x a -
        mwσ x a|
      ≤ (16362665 / 4046689 : ℝ) / 120 :=
        lowDelta_sigmaDynTop_abs_sub_staticSender_le
          (V := lowDeltaShocked.smear lowDeltaStaticSenderPolicyCenter)
          (K := 16362665 / 4046689)
          lowDeltaStaticSenderPolicyCenter_smear_valueLipschitz x a
    _ = 3272533 / 97120536 :=
      lowDelta_staticPolicySenderDisplacement_eq

/-! ## Generic Target replacement budget -/

/-- Reduced rational form of the Target sensitivity multiplier associated
with `K_T = 3855250/142269`. -/
theorem lowDelta_staticPolicyTargetSenderReplacementFactor_eq :
    (1 + (9 / 10 : ℝ) * (3855250 / 142269) / 100) =
      235955 / 189692 := by
  norm_num

/-- Reduced rational form of the generic Target objective-difference estimate
obtained from the global Sender displacement `K_S/120`. -/
theorem lowDelta_staticPolicyTargetSenderReplacementBound_eq :
    (1 + (9 / 10 : ℝ) * (3855250 / 142269) / 100) *
        ((16362665 / 4046689) / 120) =
      772170524015 / 18422988714912 := by
  norm_num

/-- The generic Target Sender-replacement upper bound exceeds the existing
Target-row allowance.  This proves only that this sufficient estimate cannot
close the Target row; it does not lower-bound the true Target Bellman
residual. -/
theorem
    lowDelta_staticPolicyTargetSenderReplacementBound_exceeds_localAllowance :
    (8071 / 773000 : ℝ) <
      (1 + (9 / 10) * (3855250 / 142269) / 100) *
        ((16362665 / 4046689) / 120) := by
  norm_num

/-- If a later exact argument proves a uniform Sender-replacement error `q`,
then the same generic Target estimate fits the Target allowance exactly when
`q ≤ 382751033/45598303750`.  This is arithmetic, not a claim that the
realized error satisfies the threshold. -/
theorem lowDelta_staticPolicyTargetSenderReplacement_q_iff_localAllowance
    (q : ℝ) :
    (1 + (9 / 10 : ℝ) * (3855250 / 142269) / 100) * q ≤
        8071 / 773000 ↔
      q ≤ 382751033 / 45598303750 := by
  constructor <;> intro h <;> norm_num at h ⊢ <;> nlinarith

/-- Writing the second-order Sender completion as `(3/20) q²`, the exact
Sender-row allowance is equivalent to the displayed rational threshold on
`q²`.  No claim that an independently defined policy error obeys this
conversion is made here. -/
theorem lowDelta_senderQuadratic_q_iff_localAllowance (q : ℝ) :
    (3 / 20 : ℝ) * q ^ 2 ≤
        2275459929739 / 221799538143400 ↔
      q ^ 2 ≤ 2275459929739 / 33269930721510 := by
  constructor <;> intro h <;> norm_num at h ⊢ <;> nlinarith

end Examples
end Sanctions
