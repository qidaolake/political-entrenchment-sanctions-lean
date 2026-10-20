/-
Sanctions/Foundations/FiniteDiscountedTelescope.lean

**Finite discounted telescoping with per-date Bellman residuals** (round AE,
2026-09-20; doc 94, item A3).

If a sequence of values `V t`, flows `u t` and residuals `D t` satisfies the
one-step inequality `u t + β·V (t+1) + D t ≤ V t` at every date before `T`, then

  `Σ_{t<T} β^t·u t + β^T·V T + Σ_{t<T} β^t·D t ≤ V 0`.

This is the finite-horizon half of the standard verification argument
(Stokey–Lucas–Prescott §4.1), kept with its residuals instead of discarding
them: the residuals measure how much a finite imposed episode followed by a
given continuation value falls short of the value at the start. The sequence
form needs no state space, no plan type and no summability.

Rule 19: a statement about real sequences; the consumer is
`Examples/PlacableSenderReliefParticipation.lean`.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sanctions
namespace Foundations
namespace FiniteDiscountedTelescope

open Finset

/-- **Finite telescoping with residuals.** -/
theorem sum_add_terminal_add_residual_le {β : ℝ} (hβ : 0 ≤ β) {V u D : ℕ → ℝ} :
    ∀ T : ℕ, (∀ t < T, u t + β * V (t + 1) + D t ≤ V t) →
      ∑ t ∈ range T, β ^ t * u t + β ^ T * V T + ∑ t ∈ range T, β ^ t * D t ≤ V 0 := by
  intro T
  induction T with
  | zero => intro _; simp
  | succ T ih =>
      intro h
      have ih' := ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
      have hT := mul_le_mul_of_nonneg_left (h T (Nat.lt_succ_self T)) (pow_nonneg hβ T)
      rw [sum_range_succ, sum_range_succ, pow_succ]
      nlinarith [ih', hT]

/-- The constant-residual form: a uniform one-step gap `δ` accumulates to
`δ·Σ_{t<T} β^t`. -/
theorem sum_add_terminal_add_gap_le {β δ : ℝ} (hβ : 0 ≤ β) {V u : ℕ → ℝ} (T : ℕ)
    (h : ∀ t < T, u t + β * V (t + 1) + δ ≤ V t) :
    ∑ t ∈ range T, β ^ t * u t + β ^ T * V T + δ * ∑ t ∈ range T, β ^ t ≤ V 0 := by
  have := sum_add_terminal_add_residual_le hβ (V := V) (u := u) (D := fun _ => δ) T h
  rw [mul_sum]
  simpa [mul_comm] using this

/-- The discounted weight of a nonempty episode is at least one (the date-zero
term), for a nonnegative discount factor. -/
theorem one_le_geom_sum {β : ℝ} (hβ : 0 ≤ β) {T : ℕ} (hT : 0 < T) :
    1 ≤ ∑ t ∈ range T, β ^ t := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  rw [sum_range_succ']
  have : 0 ≤ ∑ t ∈ range n, β ^ (t + 1) := sum_nonneg fun t _ => pow_nonneg hβ _
  simp only [pow_zero]
  linarith

end FiniteDiscountedTelescope
end Foundations
end Sanctions

#print axioms Sanctions.Foundations.FiniteDiscountedTelescope.sum_add_terminal_add_residual_le
#print axioms Sanctions.Foundations.FiniteDiscountedTelescope.sum_add_terminal_add_gap_le
#print axioms Sanctions.Foundations.FiniteDiscountedTelescope.one_le_geom_sum
