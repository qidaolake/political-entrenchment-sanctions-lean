/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticPolicyExpandedPerovBudget.lean

Exact radius arithmetic for the actual-transition static-policy reference
center.

The earlier radii `27/100` and `7/100` were a convenient one-percent packet,
not model primitives.  This file proves that the already-established
continuum Target and Sender residual bounds fit the larger rational packet

  r_T = 4/5,   r_S = 3/20

under the same already-proved two-row matrix.  This is only residual and
radius arithmetic.  It does not assert local Target optimality, identify the
local rows, or claim a coupled equilibrium.

The closing lemma records that `4/5` and `3/20` are themselves not a free
choice: they dominate the closed-form radii `(I - M)⁻¹ ε`, which the general
minimality lemma in `Foundations/ValidatedLocalPerov` proves are the
componentwise smallest pair passing the same two budget checks.

No numerical convergence premise or new model assumption is used.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyTargetResidual
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyCenterBudget
import Sanctions.Foundations.ValidatedLocalPerov

namespace Sanctions
namespace Examples

/-- The Target radius in the expanded exact packet. -/
noncomputable def lowDeltaExpandedTargetRadius : ℝ := 4 / 5

/-- The Sender radius in the expanded exact packet. -/
noncomputable def lowDeltaExpandedSenderRadius : ℝ := 3 / 20

/-- The proved Target residual upper bound at the actual-transition
static-policy center. -/
noncomputable def lowDeltaStaticPolicyTargetResidualBound : ℝ :=
  (1 + (9 / 10) * (3855250 / 142269) * (1 / 100)) *
      ((16362665 / 4046689) / 120) +
    ((9 / 10) * (3855250 / 142269) * (1 / 100) * (5 / 12)) ^ 2 / 4

/-- The proved Sender residual upper bound at the actual-transition
static-policy center. -/
noncomputable def lowDeltaStaticPolicySenderResidualBound : ℝ :=
  (16362665 / 4046689) ^ 2 / 96000

/-- The largest Sender residual admitted by the expanded packet after the
Target-to-Sender and Sender-to-Sender row contributions have been charged.
This is the honest residual budget for a realized (possibly non-static)
Target policy at the reference value pair. -/
noncomputable def lowDeltaExpandedSenderResidualAllowance : ℝ :=
  lowDeltaExpandedSenderRadius -
    (2880 / 37877) * lowDeltaExpandedTargetRadius -
    (8697049946379 / 15525967670038) *
      lowDeltaExpandedSenderRadius

theorem lowDeltaExpandedTargetRadius_pos :
    0 < lowDeltaExpandedTargetRadius := by
  norm_num [lowDeltaExpandedTargetRadius]

theorem lowDeltaExpandedSenderRadius_pos :
    0 < lowDeltaExpandedSenderRadius := by
  norm_num [lowDeltaExpandedSenderRadius]

/-- Closed form of the Sender residual allowance left by the expanded
carrier-local packet. -/
theorem lowDeltaExpandedSenderResidualAllowance_eq :
    lowDeltaExpandedSenderResidualAllowance =
      1598335655457 / 310519353400760 := by
  norm_num [
    lowDeltaExpandedSenderResidualAllowance,
    lowDeltaExpandedTargetRadius,
    lowDeltaExpandedSenderRadius]

/-- The static-policy residual bound uses only part of the available Sender
residual budget.  The strict gap is what a later realized-policy estimate may
use; no equality between the static and realized policies is presumed. -/
theorem lowDeltaStaticPolicySenderResidualBound_lt_expandedAllowance :
    lowDeltaStaticPolicySenderResidualBound <
      lowDeltaExpandedSenderResidualAllowance := by
  norm_num [
    lowDeltaStaticPolicySenderResidualBound,
    lowDeltaExpandedSenderResidualAllowance,
    lowDeltaExpandedTargetRadius,
    lowDeltaExpandedSenderRadius]

/-- Exact Target-row self-map arithmetic for the expanded packet. -/
theorem lowDeltaStaticPolicyTargetResidualBound_fits_expandedRadius :
    lowDeltaStaticPolicyTargetResidualBound +
          (9 / 10) * lowDeltaExpandedTargetRadius +
          (1280 / 5411) * lowDeltaExpandedSenderRadius
        ≤ lowDeltaExpandedTargetRadius := by
  norm_num [
    lowDeltaStaticPolicyTargetResidualBound,
    lowDeltaExpandedTargetRadius,
    lowDeltaExpandedSenderRadius]

/-- Exact Sender-row self-map arithmetic for the expanded packet. -/
theorem lowDeltaStaticPolicySenderResidualBound_fits_expandedRadius :
    lowDeltaStaticPolicySenderResidualBound +
          (2880 / 37877) * lowDeltaExpandedTargetRadius +
          (8697049946379 / 15525967670038) *
            lowDeltaExpandedSenderRadius
        ≤ lowDeltaExpandedSenderRadius := by
  norm_num [
    lowDeltaStaticPolicySenderResidualBound,
    lowDeltaExpandedTargetRadius,
    lowDeltaExpandedSenderRadius]

/-- Any realized Sender residual below the exact remaining allowance satisfies
the Sender-row radius inequality. -/
theorem lowDeltaSenderResidual_fits_expandedRadius_of_le_allowance
    {εS : ℝ}
    (hεS : εS ≤ lowDeltaExpandedSenderResidualAllowance) :
    εS +
          (2880 / 37877) * lowDeltaExpandedTargetRadius +
          (8697049946379 / 15525967670038) *
            lowDeltaExpandedSenderRadius
        ≤ lowDeltaExpandedSenderRadius := by
  dsimp only [lowDeltaExpandedSenderResidualAllowance] at hεS
  linarith

/-- The actual Target Bellman residual, not merely its displayed upper bound,
fits the expanded Target-row radius inequality. -/
theorem lowDeltaStaticPolicyTargetCenter_fits_expandedRadius :
    dist lowDeltaStaticPolicyTargetBellman
          lowDeltaStaticTargetPolicyCenter +
          (9 / 10) * lowDeltaExpandedTargetRadius +
          (1280 / 5411) * lowDeltaExpandedSenderRadius
        ≤ lowDeltaExpandedTargetRadius := by
  calc
    dist lowDeltaStaticPolicyTargetBellman
          lowDeltaStaticTargetPolicyCenter +
          (9 / 10) * lowDeltaExpandedTargetRadius +
          (1280 / 5411) * lowDeltaExpandedSenderRadius
        ≤ lowDeltaStaticPolicyTargetResidualBound +
          (9 / 10) * lowDeltaExpandedTargetRadius +
          (1280 / 5411) * lowDeltaExpandedSenderRadius := by
            have h := lowDeltaStaticPolicyTargetCenter_bellman_residual
            simp only [lowDeltaStaticPolicyTargetResidualBound]
            nlinarith
    _ ≤ lowDeltaExpandedTargetRadius :=
      lowDeltaStaticPolicyTargetResidualBound_fits_expandedRadius

/-- The actual Sender Bellman residual fits the expanded Sender-row radius
inequality. -/
theorem lowDeltaStaticPolicySenderCenter_fits_expandedRadius :
    dist
          (lowDeltaShocked.bellmanS_shock
            lowDeltaStaticTargetPolicy
            lowDeltaStaticTargetPolicy_continuous
            lowDeltaStaticSenderPolicyCenter)
          lowDeltaStaticSenderPolicyCenter +
          (2880 / 37877) * lowDeltaExpandedTargetRadius +
          (8697049946379 / 15525967670038) *
            lowDeltaExpandedSenderRadius
        ≤ lowDeltaExpandedSenderRadius := by
  calc
    dist
          (lowDeltaShocked.bellmanS_shock
            lowDeltaStaticTargetPolicy
            lowDeltaStaticTargetPolicy_continuous
            lowDeltaStaticSenderPolicyCenter)
          lowDeltaStaticSenderPolicyCenter +
          (2880 / 37877) * lowDeltaExpandedTargetRadius +
          (8697049946379 / 15525967670038) *
            lowDeltaExpandedSenderRadius
        ≤ lowDeltaStaticPolicySenderResidualBound +
          (2880 / 37877) * lowDeltaExpandedTargetRadius +
          (8697049946379 / 15525967670038) *
            lowDeltaExpandedSenderRadius := by
            have h := lowDeltaStaticSenderPolicyCenter_bellman_residual
            simp only [lowDeltaStaticPolicySenderResidualBound]
            nlinarith
    _ ≤ lowDeltaExpandedSenderRadius :=
      lowDeltaStaticPolicySenderResidualBound_fits_expandedRadius

/-! ## The chosen radii are the derived radii plus slack

The two radii above (`4/5` and `3/20`) are hand-picked numerals, and the two
`fits_expandedRadius` theorems are exactly the assertion that this pair passes
the Perov self-map budget checks — i.e. that it lies in
`Foundations.Perov.perov2AdmissibleRadii`. The general minimality result
`Foundations.Perov.perov2_canonicalRadii_le_of_mem_admissible` therefore applies
and pins the chosen pair against the *derived* pair `(I − M)⁻¹ ε`.

This does not remove the numerals from this file — the statements above still
mention them, and removing them would change what those statements say. What it
does is retire the *justification* for them: they are no longer unexplained
choices, but a proved over-estimate of a determined quantity. -/

/-- **The chosen low-adjustment radius packet dominates the derived one.**

The hand-picked Target radius `4/5` and Sender radius `3/20` are componentwise
at least the closed-form radii `(I − M)⁻¹ ε` built from the certified coupled
row matrix

  `M = [[9/10, 1280/5411], [2880/37877, 8697049946379/15525967670038]]`

and the two proved centre-residual bounds at the actual-transition
static-policy centre.

Proof content: none of its own. The two `fits_expandedRadius` theorems already
say the chosen pair is an admissible self-map budget; the general minimality
lemma then says the derived pair is componentwise below *every* admissible
pair. So the numerals carry only slack, never sharpness — no choice of radii
could have done better than the closed form, and this particular choice did
strictly worse.

(Numerically the derived radii are `≈ 0.7543` and `≈ 0.1308` against the chosen
`0.8` and `0.15`; that evaluation is not needed for the statement and is not
performed here.) -/
theorem lowDeltaExpandedRadii_dominate_canonical :
    Foundations.Perov.perov2CanonicalRadiusX
        (9 / 10) (1280 / 5411) (2880 / 37877)
        (8697049946379 / 15525967670038)
        lowDeltaStaticPolicyTargetResidualBound
        lowDeltaStaticPolicySenderResidualBound
      ≤ lowDeltaExpandedTargetRadius ∧
    Foundations.Perov.perov2CanonicalRadiusY
        (9 / 10) (1280 / 5411) (2880 / 37877)
        (8697049946379 / 15525967670038)
        lowDeltaStaticPolicyTargetResidualBound
        lowDeltaStaticPolicySenderResidualBound
      ≤ lowDeltaExpandedSenderRadius :=
  Foundations.Perov.perov2_canonicalRadii_le_of_mem_admissible
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    coupledSchur_margin_robust
    (r := (lowDeltaExpandedTargetRadius, lowDeltaExpandedSenderRadius))
    ⟨lowDeltaStaticPolicyTargetResidualBound_fits_expandedRadius,
      lowDeltaStaticPolicySenderResidualBound_fits_expandedRadius⟩

end Examples
end Sanctions
