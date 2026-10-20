/-
Sanctions/Examples/CoupledRoute/LowDeltaRealizedIDO.lean

A sufficient realised-policy interval-dominance result for the low-delta
coupled witness.

This module does not claim that the endogenous Target policy satisfies the
displayed one-sided slope bound. It isolates the exact remaining policy
regularity implication: if the realised policy rises no faster than
`2959677 / 3200000`, then every `K_S`-Lipschitz Sender value (in particular
every value in `coupledCarrierS`) gives a full-state interval-dominance family.

The threshold is an instance of a general one on the quadratic Sender family
under the affine transition and the box kernel
(`quadSender_movAvg_realized_IDOFamilyOn_of_policy_slope`):
`(r − β_S·(K/h)·(1−δ)·δ)/w`, here `2·(27/20 − (1/2)·(57377/320)·(99/10000))`.
-/

import Sanctions.Examples.CoupledRoute.CoupledCarrierRedesign
import Sanctions.Theory.Certificates.SubpivotChordNecessity

namespace Sanctions
namespace Examples

open Set
open Sanctions.AbstractGame

noncomputable section

/-- The exact low-delta realised-policy IDO threshold is twice the residual
fixed-action cross-state margin. -/
theorem lowDelta_realized_IDO_slope_threshold_eq :
    2 * ((27 / 20 : ℝ) - (99 / 2000) * (57377 / 3200)) =
      2959677 / 3200000 := by
  norm_num

/-- The exact low-delta realised-policy IDO slope threshold is positive. -/
theorem lowDelta_realized_IDO_slope_threshold_pos :
    (0 : ℝ) < 2959677 / 3200000 := by
  norm_num

/-! ## General threshold on the quadratic Sender family -/

/-- **Realised-policy interval dominance on the quadratic Sender family.**

Affine-restricted (Rule 22, axis 1): the transition is the affine law
`F = affineF p.δ`, the Sender stage payoff is the quadratic family
`quadSenderPayoff c r u0 w q` (rally cross-partial `r`, placation
cross-partial `w`), and the continuation is smoothed by the box kernel of
half-width `h`.  Every other primitive of `p` is free, and no sign is imposed
on `c`, `r`, `u0`, `w` or `q`.

For a `K`-Lipschitz Sender continuation `V_S`, the realised dynamic Sender
objective has increasing differences, hence interval dominance, on the whole
physical state space whenever the Target policy obeys

`w * (α y - α x) ≤ (r - β_S * (K / h) * ((1 - δ) * δ)) * (y - x)` for `x ≤ y`.

Per unit of sanction, the stage payoff contributes the cross term
`r (y - x) - w (α y - α x)`, and the smoothed continuation can take away at most
`β_S (K / h) (1 - δ) δ (y - x)`: a `K`-Lipschitz value has a `K/h`-Lipschitz
one-box derivative, and the affine law scales the mixed rectangle by
`(1 - δ) δ`.  A version general in `F` would need a mixed-difference chord on
`F`, which is a new regularity condition, so it is not stated. -/
theorem quadSender_movAvg_realized_IDOFamilyOn_of_policy_slope
    (p : Params) {c r u0 w q : ℝ}
    (hU : p.U_S = Params.quadSenderPayoff c r u0 w q)
    (hF : p.F = affineF p.δ)
    {h : ℝ} (hh : 0 < h) (V_S : SBCF) {K : ℝ}
    (hV_S : Params.ValueLipschitzWith V_S K) (α : ℝ → ℝ)
    (hαslope :
      ∀ ⦃x y : ℝ⦄, x ∈ Sanctions.S → y ∈ Sanctions.S → x ≤ y →
        w * (α y - α x)
          ≤ (r - p.β_S * (K / h) * ((1 - p.δ) * p.δ)) * (y - x)) :
    Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I Sanctions.S
      (fun s x =>
        p.senderDynObjective (Sanctions.movAvgBCF hh V_S) x (α x) s) := by
  apply Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
  apply Sanctions.MilgromShannon.IncreasingDifferencesOn.toSingleCrossingOn
  intro s t x y hs ht hst hx hy hxy
  have hxy0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hst0 : 0 ≤ t - s := sub_nonneg.mpr hst
  have hα := hαslope hx hy hxy
  have hδ0 : 0 ≤ p.δ := p.δ_mem.1.le
  have hδ1 : 0 ≤ 1 - p.δ := sub_nonneg.mpr p.δ_mem.2.le
  have hβ : 0 ≤ p.β_S := p.β_S_mem.1
  have hφ : ∀ z, DifferentiableAt ℝ (Sanctions.movAvgReal h V_S) z :=
    fun z => (Sanctions.movAvgReal_hasDerivAt hh V_S z).differentiableAt
  have hφ' :
      ∀ u v, |deriv (Sanctions.movAvgReal h V_S) u
          - deriv (Sanctions.movAvgReal h V_S) v| ≤ (K / h) * |u - v| :=
    Sanctions.movAvgReal_deriv_lipschitz_of_valueLipschitz
      hh V_S hV_S.nonneg hV_S
  have hmixed :=
    Sanctions.affine_mixed_rectangle_of_deriv_lipschitz
      (Sanctions.movAvgReal h V_S) hφ hφ'
      (c := 1 - p.δ) (d := p.δ) (x := y) (y := x) (s := t) (t := s)
  rw [abs_of_nonneg hδ1, abs_of_nonneg hδ0, abs_of_nonneg hxy0,
    abs_of_nonneg hst0] at hmixed
  have hmixed_lower := neg_le_of_abs_le hmixed
  have hmem : ∀ {z u : ℝ}, z ∈ Sanctions.S → u ∈ Sanctions.I →
      (1 - p.δ) * z + p.δ * u ∈ Sanctions.S := by
    intro z u hz hu
    simpa only [hF, affineF] using p.F_mem z u hz hu
  simp only [Params.senderDynObjective, hU, hF, affineF,
    Sanctions.movAvgBCF_apply]
  rw [Sanctions.clipS'_val_eq_of_mem (hmem hx hs),
    Sanctions.clipS'_val_eq_of_mem (hmem hx ht),
    Sanctions.clipS'_val_eq_of_mem (hmem hy hs),
    Sanctions.clipS'_val_eq_of_mem (hmem hy ht)]
  simp only [Params.quadSenderPayoff]
  nlinarith [mul_nonneg hst0 (sub_nonneg.mpr hα),
    mul_le_mul_of_nonneg_left hmixed_lower hβ]

/-! ## The low-delta witness -/

/-- **Full-state realised-policy interval dominance from a one-sided policy
slope bound.**

For every `K_S`-Lipschitz Sender continuation (in particular every value in
`coupledCarrierS`), the realised Sender dynamic objective satisfies interval
dominance on the whole physical state space whenever the Target policy obeys

`α y - α x ≤ (2959677 / 3200000) * (y - x)` for `x ≤ y`.

This is a sufficient implication, not a discharge of the endogenous policy
premise.  Witness-specific (Rule 22): the instance of the affine-restricted
`quadSender_movAvg_realized_IDOFamilyOn_of_policy_slope` at the mechanism
payoff (`c = 6/5`, `r = 27/20`, `w = 1/2`), `δ = 1/100`, `h = 1/10`,
`β_S = 1/2`, `K = K_S`.  Only the Lipschitz half of Sender-carrier membership is
assumed; the norm half is dropped. -/
theorem lowDelta_senderDynObjective_realized_IDOFamilyOn_of_policy_slope
    (V_S : SBCF)
    (hV_S : Params.ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (α : ℝ → ℝ)
    (hαslope :
      ∀ ⦃x y : ℝ⦄, x ∈ Sanctions.S → y ∈ Sanctions.S → x ≤ y →
        α y - α x ≤ (2959677 / 3200000 : ℝ) * (y - x)) :
    Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I Sanctions.S
      (fun s x =>
        lowDeltaParams.senderDynObjective
          (lowDeltaShocked.smear V_S) x (α x) s) := by
  have hV : Params.ValueLipschitzWith V_S (57377 / 3200) := by
    simpa only [lowDeltaSenderCarrierLip_eq] using hV_S
  have hU : lowDeltaParams.U_S
      = Params.quadSenderPayoff (6 / 5) (27 / 20) (1 / 10) (1 / 2) (2 / 5) := by
    funext x a s
    simp only [lowDeltaParams_U_S, mwU_S, Params.quadSenderPayoff]
    ring
  rw [lowDeltaShocked_smear]
  refine quadSender_movAvg_realized_IDOFamilyOn_of_policy_slope
    lowDeltaParams hU rfl lowDeltaH_pos V_S hV α ?_
  intro x y hx hy hxy
  have h := hαslope hx hy hxy
  simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
  norm_num
  linarith

end

end Examples
end Sanctions
