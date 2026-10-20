/-
Sanctions/Examples/CoupledRoute/LowDeltaRefinedPerovBudget.lean

Exact local-Perov budget after the sharp frozen-center estimates.

This file contains only rational arithmetic for the already-proved coupled
row matrix and the already-selected local radii `27/100` and `7/100`.  It
identifies the necessary and sufficient residual allowance in each row and
records that the present global frozen-center bounds are not, by themselves,
small enough to discharge those inequalities.

These are statements about the strength of available proof bounds, not claims
that the true Bellman residuals attain those upper bounds.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaFrozenSharpResidual
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenCoupledLocalization
import Sanctions.Examples.CoupledRoute.LowDeltaLocalPerovBudget

namespace Sanctions
namespace Examples

/-- Exact Target-row residual allowance left by the existing local radii and
coupled row matrix. -/
theorem lowDelta_localTargetResidualAllowance_eq :
    (27 / 100 : ℝ) -
        (9 / 10) * (27 / 100) -
        (1280 / 5411) * (7 / 100) =
      8071 / 773000 := by
  norm_num

/-- Exact Sender-row residual allowance left by the existing local radii and
coupled row matrix. -/
theorem lowDelta_localSenderResidualAllowance_eq :
    (7 / 100 : ℝ) -
        (2880 / 37877) * (27 / 100) -
        (8697049946379 / 15525967670038) * (7 / 100) =
      2275459929739 / 221799538143400 := by
  norm_num

/-- The Target local self-map inequality is equivalent to the exact residual
threshold `8071/773000`. -/
theorem lowDelta_targetLocalRadius_iff_residualAllowance
    (ε_T : ℝ) :
    ε_T +
          (9 / 10) * (27 / 100) +
          (1280 / 5411) * (7 / 100)
        ≤ (27 / 100 : ℝ) ↔
      ε_T ≤ 8071 / 773000 := by
  constructor <;> intro h <;> nlinarith

/-- The Sender local self-map inequality is equivalent to the exact residual
threshold `2275459929739/221799538143400`. -/
theorem lowDelta_senderLocalRadius_iff_residualAllowance
    (ε_S : ℝ) :
    ε_S +
          (2880 / 37877) * (27 / 100) +
          (8697049946379 / 15525967670038) * (7 / 100)
        ≤ (7 / 100 : ℝ) ↔
      ε_S ≤ 2275459929739 / 221799538143400 := by
  constructor <;> intro h <;> nlinarith

/-- The sharp global Target perturbation estimate is still larger than the
Target-row residual allowance.  Therefore that uniform estimate alone cannot
close the local Target self-map proof. -/
theorem lowDelta_globalTargetPerturbationBound_exceeds_localAllowance :
    (8071 / 773000 : ℝ) <
      (3272533 / 807360) / 120 +
        (9 / 10) * (77105 / 2784) * (1 / 100) := by
  norm_num

/-- The sharp proved Sender residual upper bound is still larger than the
Sender-row allowance.  This comparison does not lower-bound the true residual;
it says that the present global upper bound is insufficient for the packet. -/
theorem lowDelta_sharpSenderResidualBound_exceeds_localAllowance :
    (2275459929739 / 221799538143400 : ℝ) <
      3272533 / 161472000 := by
  norm_num

end Examples
end Sanctions
