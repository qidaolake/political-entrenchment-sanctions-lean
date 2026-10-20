/-
Sanctions/Examples/CoupledRoute/LowDeltaLocalPerovBudget.lean

Exact radius arithmetic for the assumption-neutral local Perov route at the
existing low-delta coupled economy.

This file deliberately contains no proposed center, residual estimate, policy,
or equilibrium assumption.  It records three kernel-checked facts about the
already proved coupled row matrix:

* the old full carrier radii cannot serve as a local self-map budget, even
  with zero residual;
* residual bounds of one percent in both coordinates would fit inside the
  much smaller Target and Sender balls of radii 27/100 and 7/100; and
* those two radii are not a free choice — they dominate the closed-form
  radii `(I - M)⁻¹ ε`, which the general minimality lemma in
  `Foundations/ValidatedLocalPerov` proves are the componentwise smallest
  admissible pair.

Thus the remaining model-specific obligation is exact continuum control of a
genuine center and its optimal-policy branches, not numerical convergence and
not further matrix arithmetic.
-/

import Sanctions.Examples.CoupledRoute.CoupledSchurWitness
import Sanctions.Foundations.ValidatedLocalPerov

namespace Sanctions
namespace Examples

/-! ## Disprove-first check on the old global radii -/

/-- The old full Target/Sender sup-norm carrier radii `20` and `523/160`
cannot satisfy the Sender radius inequality for the certified two-sided row
matrix.  The propagated radius already exceeds `523/160` before adding any
center residual. -/
theorem lowDelta_fullCarrierRadii_fail_localSenderSelfMap :
    (523 / 160 : ℝ) <
      (2880 / 37877) * 20
        + (8697049946379 / 15525967670038) * (523 / 160) := by
  norm_num

/-! ## A precise residual target for the local route -/

/-- If the eventual exact center has both continuum Bellman residuals bounded
by `1/100`, the certified coupled row matrix propagates the Target radius
`27/100` and Sender radius `7/100` back into those same balls.  This is only
the radius arithmetic; it does not assert that a center with those residual
bounds has already been constructed. -/
theorem lowDelta_onePercentResidual_fits_localRadii :
    (1 / 100 : ℝ)
        + (9 / 10) * (27 / 100)
        + (1280 / 5411) * (7 / 100)
      ≤ 27 / 100 ∧
    (1 / 100 : ℝ)
        + (2880 / 37877) * (27 / 100)
        + (8697049946379 / 15525967670038) * (7 / 100)
      ≤ 7 / 100 := by
  constructor <;> norm_num

/-- **The one-percent radius packet dominates the derived one.**

The radii `27/100` and `7/100` were chosen as a convenient round packet for a
one-percent residual. The theorem above says exactly that this pair passes the
two Perov self-map budget checks; the general minimality lemma
`Foundations.Perov.perov2_canonicalRadii_le_of_mem_admissible` then says the
closed-form pair `(I − M)⁻¹ ε` — which is determined, not chosen, once the
certified coupled row matrix and the residual vector `ε = (1/100, 1/100)` are
fixed — is componentwise no larger.

So the two numerals are an over-estimate of a determined quantity rather than a
free design choice. (Numerically the derived radii are `≈ 0.2602` and
`≈ 0.0677`; the round packet is the same quantity rounded up.) -/
theorem lowDelta_onePercentRadii_dominate_canonical :
    Foundations.Perov.perov2CanonicalRadiusX
        (9 / 10) (1280 / 5411) (2880 / 37877)
        (8697049946379 / 15525967670038) (1 / 100) (1 / 100)
      ≤ 27 / 100 ∧
    Foundations.Perov.perov2CanonicalRadiusY
        (9 / 10) (1280 / 5411) (2880 / 37877)
        (8697049946379 / 15525967670038) (1 / 100) (1 / 100)
      ≤ 7 / 100 :=
  Foundations.Perov.perov2_canonicalRadii_le_of_mem_admissible
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    coupledSchur_margin_robust
    (r := (27 / 100, 7 / 100))
    lowDelta_onePercentResidual_fits_localRadii

end Examples
end Sanctions
