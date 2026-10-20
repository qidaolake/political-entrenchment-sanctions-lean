/-
Sanctions/Examples/AffineInstance/EntryExitComparison.lean

**The affine entry/exit comparison, as a corollary of the general one** (round
BD, 2026-10-01). **Rule 22: AFFINE BY HYPOTHESIS** — every theorem here assumes
`p.F = affineF δ`; the general statements are in
`Theory/LockIn/EntryExitComparison.lean`.

The appendix remark ("Entry and exit horizons compared", `app:supporting`) says
that under the affine law the least drifts are `η_δ(x̄) = δ(1 − x̄)` and
`η^R_δ(x̄) = δx̄`, so before rounding the exit bound exceeds the entry bound
exactly when `x̄ < 1/2`, with `δ` cancelling, and the integer horizons compare
only weakly. That remark was marked "elementary algebra, not machine-checked";
this file checks it:

* `affineF_reflect` — the affine law is reflection-symmetric,
  `affineF δ (1 − x) (1 − s) = 1 − affineF δ x s`;
* `affine_fullReliefMinDrift_eq` — `η^R_δ(x̄) = δx̄` (the exit-side mirror of the
  existing `affine_fullShockMinDrift_eq`), read through the reflection;
* `affine_fullReliefExitHorizon_eq` — the exit horizon is `⌈(1 − x̄)/(δx̄)⌉`;
* `affine_entryBound_lt_exitBound_iff` — `x̄/(δ(1 − x̄)) < (1 − x̄)/(δx̄)` iff
  `x̄ < 1/2`, a one-line instance of `entryBound_lt_exitBound_iff_lt_half`;
* the weak integer comparisons on each side of the midpoint.
-/
import Sanctions.Theory.LockIn.EntryExitComparison
import Sanctions.Examples.AffineInstance.Kinematics

namespace Sanctions

open Set

namespace AbstractGame

/-- **The affine law is reflection-symmetric** on all of `ℝ²`. -/
theorem affineF_reflect (δ x s : ℝ) : affineF δ (1 - x) (1 - s) = 1 - affineF δ x s := by
  unfold affineF
  ring

/-- The reflection, in the form the general theorems read. -/
theorem reflect_of_F_eq_affineF (p : Params) {δ : ℝ} (hF : p.F = affineF δ) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s := by
  intro x _ s _
  rw [hF]
  exact affineF_reflect δ x s

/-- **The affine least relief drift**: `η^R_δ(x̄) = δx̄` on `(0, 1]`. -/
theorem affine_fullReliefMinDrift_eq (p : Params) {δ xbar : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hF : p.F = affineF δ) (hxbar : xbar ∈ Ioc (0 : ℝ) 1) :
    p.fullReliefMinDrift xbar = δ * xbar := by
  rw [p.fullReliefMinDrift_eq_reflect (reflect_of_F_eq_affineF p hF) hxbar.1.le,
    affine_fullShockMinDrift_eq p hδ hF ⟨by linarith [hxbar.2], by linarith [hxbar.1]⟩]
  ring

/-- **The affine exit horizon**: `⌈(1 − x̄)/(δx̄)⌉`. -/
theorem affine_fullReliefExitHorizon_eq (p : Params) {δ xbar : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hF : p.F = affineF δ) (hxbar : xbar ∈ Ioc (0 : ℝ) 1) :
    p.fullReliefExitHorizon xbar = Nat.ceil ((1 - xbar) / (δ * xbar)) := by
  unfold Params.fullReliefExitHorizon
  rw [affine_fullReliefMinDrift_eq p hδ hF hxbar]

/-- **The affine comparison** (the appendix remark): for `0 < x̄ < 1`, the exit
bound `(1 − x̄)/(δx̄)` exceeds the entry bound `x̄/(δ(1 − x̄))` iff `x̄ < 1/2`, at
every rate `δ`. -/
theorem affine_entryBound_lt_exitBound_iff (p : Params) {δ xbar : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hF : p.F = affineF δ) (h0 : 0 < xbar) (h1 : xbar < 1) :
    xbar / (δ * (1 - xbar)) < (1 - xbar) / (δ * xbar) ↔ xbar < 1 / 2 := by
  rw [← affine_fullShockMinDrift_eq p hδ hF ⟨h0.le, h1⟩,
    ← affine_fullReliefMinDrift_eq p hδ hF ⟨h0, h1.le⟩]
  exact p.entryBound_lt_exitBound_iff_lt_half (strictAdjustment_of_F_eq_affineF p hδ hF)
    (reflect_of_F_eq_affineF p hF) h0 h1

/-- **Affine integer horizons below the midpoint**: entry at most exit. -/
theorem affine_entryHorizon_le_exitHorizon_of_le_half (p : Params) {δ xbar : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hF : p.F = affineF δ) (h0 : 0 < xbar) (hhalf : xbar ≤ 1 / 2) :
    p.fullShockEntryHorizon xbar ≤ p.fullReliefExitHorizon xbar :=
  p.entryHorizon_le_exitHorizon_of_le_half
    (strictAdjustment_of_F_eq_affineF p hδ hF) (reflect_of_F_eq_affineF p hF) h0 hhalf

/-- **Affine integer horizons above the midpoint**: exit at most entry. -/
theorem affine_exitHorizon_le_entryHorizon_of_half_le (p : Params) {δ xbar : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hF : p.F = affineF δ) (hhalf : 1 / 2 ≤ xbar) (h1 : xbar < 1) :
    p.fullReliefExitHorizon xbar ≤ p.fullShockEntryHorizon xbar :=
  p.exitHorizon_le_entryHorizon_of_half_le
    (strictAdjustment_of_F_eq_affineF p hδ hF) (reflect_of_F_eq_affineF p hF) hhalf h1

end AbstractGame
end Sanctions

#print axioms Sanctions.AbstractGame.affineF_reflect
#print axioms Sanctions.AbstractGame.affine_fullReliefMinDrift_eq
#print axioms Sanctions.AbstractGame.affine_fullReliefExitHorizon_eq
#print axioms Sanctions.AbstractGame.affine_entryBound_lt_exitBound_iff
#print axioms Sanctions.AbstractGame.affine_entryHorizon_le_exitHorizon_of_le_half
#print axioms Sanctions.AbstractGame.affine_exitHorizon_le_entryHorizon_of_half_le
