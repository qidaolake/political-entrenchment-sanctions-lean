/-
Sanctions/Foundations/ShockedVerificationBoundary.lean

Why nonexpansiveness alone is not an expected-continuation semantics.

The abstract shocked model currently asks only that `smear` be nonexpansive in
sup norm.  That property is enough for the Banach fixed-point construction, but
it does not imply the order preservation or constant preservation supplied by
a probability kernel.  The scalar map below is an exact counterexample: it is
an isometry, yet reverses order and turns the constant one into minus one.

The final two lemmas make the verification failure numerical.  With one unit
of payoff each period and discount factor one half, the fake Bellman equation
has fixed point `2/3`, whereas the genuine infinite discounted payoff is `2`.
Thus a lifetime-payoff theorem cannot follow from nonexpansiveness alone.
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace Sanctions.Foundations

/-- A nonexpansive continuation transform that is not a probability expectation. -/
noncomputable def nonexpectationalSmear (v : ℝ) : ℝ := -v

/-- Negation is exactly distance preserving, hence satisfies the abstract
nonexpansiveness inequality. -/
theorem nonexpectationalSmear_nonexpansive (v w : ℝ) :
    dist (nonexpectationalSmear v) (nonexpectationalSmear w) ≤ dist v w := by
  simp [nonexpectationalSmear, dist_neg_neg]

/-- The nonexpansive transform reverses, rather than preserves, order. -/
theorem nonexpectationalSmear_not_monotone :
    ¬ Monotone nonexpectationalSmear := by
  intro h
  have h01 := h (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num [nonexpectationalSmear] at h01

/-- The nonexpansive transform does not preserve the constant one, another
property every probability expectation must satisfy. -/
theorem nonexpectationalSmear_not_preserves_one :
    nonexpectationalSmear 1 ≠ 1 := by
  norm_num [nonexpectationalSmear]

/-- The fake one-state Bellman equation with unit flow payoff and discount
factor one half has fixed point `2/3`. -/
theorem nonexpectational_bellman_fixed_point :
    (2 / 3 : ℝ) =
      1 + (1 / 2 : ℝ) * nonexpectationalSmear (2 / 3 : ℝ) := by
  norm_num [nonexpectationalSmear]

/-- The genuine infinite discounted sum of one unit per period at discount
factor one half equals `2`. -/
theorem geometric_half_tsum :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
  rw [tsum_geometric_of_norm_lt_one]
  · norm_num
  · norm_num

/-- Consequently, the fake Bellman fixed point is not the corresponding
infinite discounted lifetime payoff. -/
theorem nonexpectational_fixed_point_ne_lifetime_payoff :
    (2 / 3 : ℝ) ≠ ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
  rw [geometric_half_tsum]
  norm_num

end Sanctions.Foundations
