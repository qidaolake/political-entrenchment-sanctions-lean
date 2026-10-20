/-
Sanctions/Theory/LockIn/EntryExitComparison.lean

**Entry and exit horizons compared, under a general transition** (round BD,
2026-10-01; the remark of `app:supporting`, "Entry and exit horizons compared",
whose affine specialisation was marked "not machine-checked").

The shock-entry bound `x̄/η(x̄)` (`η` the least drift `F(x,1) − x` on `[0, x̄]`,
`LockIn.lean`) and the relief-exit bound `(1 − x̄)/η_R(x̄)` (`η_R` the least drift
`x − F(x,0)` on `[x̄, 1]`, `ReliefExit.lean`) are read off different sections of
the transition, so they need not coincide. This file says when each is the
larger, in three layers.

1. **Any transition** (`entryBound_lt_exitBound_iff`). With both drifts positive
   (strict adjustment, `0 < x̄ < 1`), the exit bound exceeds the entry bound iff
   `x̄·η_R(x̄) < (1 − x̄)·η(x̄)`: the comparison weighs each distance by the other
   side's drift. Nothing more general is true without further structure.
2. **Reflection-symmetric transitions** (`F(1 − x, 1 − s) = 1 − F(x, s)` on the
   square: relief at state `x` is the mirror of a shock at `1 − x`). Then
   `η_R(x̄) = η(1 − x̄)` (`fullReliefMinDrift_eq_reflect`), the exit horizon at `x̄`
   is the entry horizon at `1 − x̄` (`fullReliefExitHorizon_eq_reflect`), and,
   because the entry bound is strictly increasing in the threshold
   (`entryBound_strictMonoOn`), **the exit bound exceeds the entry bound exactly
   when the threshold is below the midpoint** (`entryBound_lt_exitBound_iff_lt_half`),
   the two coinciding at `x̄ = 1/2`. The integer horizons compare weakly
   (`entryHorizon_le_exitHorizon_of_le_half` and its mirror),
   since distinct bounds can share a ceiling.
3. **The affine law** is reflection-symmetric, so the paper's affine remark —
   `η_δ(x̄) = δ(1 − x̄)`, `η^R_δ(x̄) = δx̄`, the exit bound above the entry bound
   exactly when `x̄ < 1/2`, `δ` cancelling — is a corollary
   (`Examples/AffineInstance/EntryExitComparison.lean`). A non-affine
   reflection-symmetric transition is exhibited in
   `Examples/ReflectionSymmetricWitness.lean` (Rule 9B).

Scope. These are comparisons of two *sufficient* durations of imposed phases
(Rule 1's exogenous-phase exception), not of required durations and not of
equilibrium behaviour. Rule 3: no existing result changes; the symmetry is a
hypothesis of these new theorems only, written directly over `p.F` (no new
`Prop`), implied by and strictly weaker than the affine law (Rule 13's
de-affining exception). Rule 22: general in `F`.
-/
import Sanctions.Theory.LockIn.ReliefExit

namespace Sanctions

open Set

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Any transition -/

/-- The shock drift is nonnegative on the feasible interval (`F x 1 ≥ F x x = x`). -/
theorem fullShockDrift_nonneg {x : ℝ} (hx1 : x ≤ 1) : 0 ≤ p.fullShockDrift x := by
  have := p.shockStepF_ge_self hx1
  unfold fullShockDrift
  unfold shockStepF at this
  linarith

/-- **The least shock drift falls as the threshold rises**: the minimum is taken
over a larger interval. No strict adjustment needed. -/
theorem fullShockMinDrift_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    p.fullShockMinDrift b ≤ p.fullShockMinDrift a := by
  unfold fullShockMinDrift
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact p.fullShockDrift_nonneg (hx.2.trans hb)
  · exact ⟨_, ⟨0, ⟨le_rfl, ha⟩, rfl⟩⟩
  · exact Set.image_mono (Set.Icc_subset_Icc_right hab)

/-- **The entry bound is strictly increasing in the threshold.** Under strict
adjustment, for `0 ≤ a < b < 1`, `a/η(a) < b/η(b)`: a farther threshold is both
farther away and reached with a smaller least drift. -/
theorem entryBound_strictMonoOn (hAdj : p.StrictAdjustment) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < 1) :
    a / p.fullShockMinDrift a < b / p.fullShockMinDrift b := by
  have hηb := (p.fullShockMinDrift_pos_attains_isMinOn hAdj ⟨ha.trans hab.le, hb⟩).1
  have hanti := p.fullShockMinDrift_anti ha hab.le hb.le
  calc a / p.fullShockMinDrift a ≤ a / p.fullShockMinDrift b :=
        div_le_div_of_nonneg_left ha hηb hanti
    _ < b / p.fullShockMinDrift b := div_lt_div_of_pos_right hab hηb

/-- **The comparison, for any transition.** Under strict adjustment and
`0 < x̄ < 1`, the exit bound `(1 − x̄)/η_R(x̄)` exceeds the entry bound `x̄/η(x̄)`
iff `x̄·η_R(x̄) < (1 − x̄)·η(x̄)`. -/
theorem entryBound_lt_exitBound_iff (hAdj : p.StrictAdjustment) {xbar : ℝ}
    (h0 : 0 < xbar) (h1 : xbar < 1) :
    xbar / p.fullShockMinDrift xbar < (1 - xbar) / p.fullReliefMinDrift xbar ↔
      xbar * p.fullReliefMinDrift xbar < (1 - xbar) * p.fullShockMinDrift xbar := by
  have hη := (p.fullShockMinDrift_pos_attains_isMinOn hAdj ⟨h0.le, h1⟩).1
  have hηR := (p.fullReliefMinDrift_pos_attains_isMinOn hAdj ⟨h0, h1.le⟩).1
  exact div_lt_div_iff₀ hη hηR

/-! ## 2. Reflection-symmetric transitions -/

/-- **Relief at `x` mirrors a shock at `1 − x`.** If `F(1 − x, 1 − s) = 1 − F(x, s)`
on the square, the relief drift at `x` is the shock drift at `1 − x`. -/
theorem fullReliefDrift_eq_reflect
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    p.fullReliefDrift x = p.fullShockDrift (1 - x) := by
  have h := hsym (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ 1 ⟨zero_le_one, le_rfl⟩
  rw [sub_sub_cancel, sub_self] at h
  unfold fullReliefDrift fullShockDrift
  rw [h]
  ring

/-- **The least relief drift above `x̄` is the least shock drift below `1 − x̄`.** -/
theorem fullReliefMinDrift_eq_reflect
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (h0 : 0 ≤ xbar) :
    p.fullReliefMinDrift xbar = p.fullShockMinDrift (1 - xbar) := by
  unfold fullReliefMinDrift fullShockMinDrift
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
    exact (p.fullReliefDrift_eq_reflect hsym ⟨h0.trans hx.1, hx.2⟩).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
    rw [p.fullReliefDrift_eq_reflect hsym ⟨by linarith [hx.2, h0], by linarith [hx.1]⟩,
      sub_sub_cancel]

/-- **The exit horizon at `x̄` is the entry horizon at the mirror threshold
`1 − x̄`.** -/
theorem fullReliefExitHorizon_eq_reflect
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (h0 : 0 ≤ xbar) :
    p.fullReliefExitHorizon xbar = p.fullShockEntryHorizon (1 - xbar) := by
  unfold fullReliefExitHorizon fullShockEntryHorizon
  rw [p.fullReliefMinDrift_eq_reflect hsym h0]

/-- **Below the midpoint, exit takes longer.** For a reflection-symmetric transition
under strict adjustment and `0 < x̄ < 1/2`, the exit bound strictly exceeds the
entry bound. -/
theorem entryBound_lt_exitBound_of_lt_half (hAdj : p.StrictAdjustment)
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (h0 : 0 < xbar) (hhalf : xbar < 1 / 2) :
    xbar / p.fullShockMinDrift xbar < (1 - xbar) / p.fullReliefMinDrift xbar := by
  rw [p.fullReliefMinDrift_eq_reflect hsym h0.le]
  exact p.entryBound_strictMonoOn hAdj h0.le (by linarith) (by linarith)

/-- **Above the midpoint, entry takes longer.** For a reflection-symmetric
transition under strict adjustment and `1/2 < x̄ < 1`, the exit bound is strictly
below the entry bound. -/
theorem exitBound_lt_entryBound_of_half_lt (hAdj : p.StrictAdjustment)
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (hhalf : 1 / 2 < xbar) (h1 : xbar < 1) :
    (1 - xbar) / p.fullReliefMinDrift xbar < xbar / p.fullShockMinDrift xbar := by
  rw [p.fullReliefMinDrift_eq_reflect hsym (by linarith)]
  exact p.entryBound_strictMonoOn hAdj (by linarith) (by linarith) h1

/-- **At the midpoint the two bounds coincide.** -/
theorem entryBound_eq_exitBound_half
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s) :
    (1 / 2 : ℝ) / p.fullShockMinDrift (1 / 2) = (1 - 1 / 2) / p.fullReliefMinDrift (1 / 2) := by
  rw [p.fullReliefMinDrift_eq_reflect hsym (by norm_num)]
  norm_num

/-- **The side of the midpoint decides the comparison.** For a
reflection-symmetric transition under strict adjustment and `0 < x̄ < 1`, the exit
bound exceeds the entry bound **if and only if** `x̄ < 1/2`. -/
theorem entryBound_lt_exitBound_iff_lt_half (hAdj : p.StrictAdjustment)
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (h0 : 0 < xbar) (h1 : xbar < 1) :
    xbar / p.fullShockMinDrift xbar < (1 - xbar) / p.fullReliefMinDrift xbar ↔
      xbar < 1 / 2 := by
  constructor
  · intro h
    by_contra hge
    rcases (not_lt.mp hge).lt_or_eq with hlt | heq
    · exact lt_asymm h (p.exitBound_lt_entryBound_of_half_lt hAdj hsym hlt h1)
    · subst heq
      rw [← p.entryBound_eq_exitBound_half hsym] at h
      exact lt_irrefl _ h
  · exact p.entryBound_lt_exitBound_of_lt_half hAdj hsym h0

/-- **Integer horizons, weakly: below the midpoint the entry horizon is at most
the exit horizon.** Distinct bounds can share a ceiling, so only the weak
comparison survives rounding. -/
theorem entryHorizon_le_exitHorizon_of_le_half
    (hAdj : p.StrictAdjustment)
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (h0 : 0 < xbar) (hhalf : xbar ≤ 1 / 2) :
    p.fullShockEntryHorizon xbar ≤ p.fullReliefExitHorizon xbar := by
  unfold fullShockEntryHorizon fullReliefExitHorizon
  apply Nat.ceil_mono
  rcases hhalf.lt_or_eq with hlt | heq
  · exact (p.entryBound_lt_exitBound_of_lt_half hAdj hsym h0 hlt).le
  · subst heq
    exact (p.entryBound_eq_exitBound_half hsym).le

/-- **Integer horizons, weakly: above the midpoint the exit horizon is at most the
entry horizon.** -/
theorem exitHorizon_le_entryHorizon_of_half_le
    (hAdj : p.StrictAdjustment)
    (hsym : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.F (1 - x) (1 - s) = 1 - p.F x s)
    {xbar : ℝ} (hhalf : 1 / 2 ≤ xbar) (h1 : xbar < 1) :
    p.fullReliefExitHorizon xbar ≤ p.fullShockEntryHorizon xbar := by
  unfold fullShockEntryHorizon fullReliefExitHorizon
  apply Nat.ceil_mono
  rcases hhalf.lt_or_eq with hlt | heq
  · exact (p.exitBound_lt_entryBound_of_half_lt hAdj hsym hlt h1).le
  · subst heq
    exact (p.entryBound_eq_exitBound_half hsym).ge

end Params
end AbstractGame
end Sanctions

#print axioms Sanctions.AbstractGame.Params.fullShockMinDrift_anti
#print axioms Sanctions.AbstractGame.Params.entryBound_strictMonoOn
#print axioms Sanctions.AbstractGame.Params.entryBound_lt_exitBound_iff
#print axioms Sanctions.AbstractGame.Params.fullReliefDrift_eq_reflect
#print axioms Sanctions.AbstractGame.Params.fullReliefMinDrift_eq_reflect
#print axioms Sanctions.AbstractGame.Params.fullReliefExitHorizon_eq_reflect
#print axioms Sanctions.AbstractGame.Params.entryBound_lt_exitBound_of_lt_half
#print axioms Sanctions.AbstractGame.Params.exitBound_lt_entryBound_of_half_lt
#print axioms Sanctions.AbstractGame.Params.entryBound_eq_exitBound_half
#print axioms Sanctions.AbstractGame.Params.entryBound_lt_exitBound_iff_lt_half
#print axioms Sanctions.AbstractGame.Params.entryHorizon_le_exitHorizon_of_le_half
#print axioms Sanctions.AbstractGame.Params.exitHorizon_le_entryHorizon_of_half_le
