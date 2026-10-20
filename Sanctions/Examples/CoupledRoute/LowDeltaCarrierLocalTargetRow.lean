/-
Sanctions/Examples/CoupledRoute/LowDeltaCarrierLocalTargetRow.lean

Target-side ingredients for the carrier-local coupled proof.

The redesigned Target carrier supplies exactly the norm premise required by
the already-proved two-sided Target row estimate.  Hence the Target row is
both invariant and row-Lipschitz on the carrier-ball intersections; no local
Target-policy hypothesis is needed for this coordinate.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCarrierPacket

namespace Sanctions
namespace Examples

open AbstractGame

/-- The existing two-sided Target row estimate applies directly on the
redesigned Target carrier. -/
theorem coupled_L_TS_on_lip_carrier
    (V_T V_T' V_S W_S : SBCF)
    (hV_T' : V_T' ∈ coupledCarrierTLip)
    (hV_S : V_S ∈ coupledCarrierS)
    (hW_S : W_S ∈ coupledCarrierS) :
    dist
        (lowDeltaShocked.targetDynBCF_shock
          (coupledSigmaClamped V_S)
          (coupledSigmaClamped_continuous V_S hV_S.2)
          V_T)
        (lowDeltaShocked.targetDynBCF_shock
          (coupledSigmaClamped W_S)
          (coupledSigmaClamped_continuous W_S hW_S.2)
          V_T')
      ≤ (9 / 10) * dist V_T V_T' +
        (1280 / 5411) * dist V_S W_S := by
  exact coupled_L_TS V_T V_T' V_S W_S hV_T'.1 hV_S hW_S

/-- The Target row at the static-policy reference pair is definitionally the
continuum Bellman row whose residual was bounded in the expanded packet. -/
theorem lowDeltaStaticPolicyTargetBellman_eq_carrierRow :
    lowDeltaStaticPolicyTargetBellman =
      lowDeltaShocked.targetDynBCF_shock
        (coupledSigmaClamped lowDeltaStaticSenderPolicyCenter)
        (coupledSigmaClamped_continuous
          lowDeltaStaticSenderPolicyCenter
          lowDeltaStaticSenderPolicyCenter_mem_coupledCarrierS.2)
        lowDeltaStaticTargetPolicyCenter := by
  rfl

/-- The actual Target row maps every redesigned-Target/existing-Sender
carrier pair back into the redesigned Target carrier. -/
theorem coupled_target_row_mem_carrierTLip
    (V_T V_S : SBCF)
    (hV_T : V_T ∈ coupledCarrierTLip)
    (hV_S : V_S ∈ coupledCarrierS) :
    lowDeltaShocked.targetDynBCF_shock
        (coupledSigmaClamped V_S)
        (coupledSigmaClamped_continuous V_S hV_S.2)
        V_T ∈ coupledCarrierTLip :=
  coupled_target_Bellman_mem_lip_carrier V_T hV_T V_S hV_S

end Examples
end Sanctions
