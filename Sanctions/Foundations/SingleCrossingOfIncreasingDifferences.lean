/-
Sanctions/Foundations/SingleCrossingOfIncreasingDifferences.lean

**Increasing differences imply single crossing.**

The cardinal condition (Topkis) implies the ordinal one (Milgrom–Shannon): if
the increment `f y t − f x t` is nondecreasing in the parameter `t`, then its
sign, and its strict sign, persist as the parameter rises. External mathematics
over an abstract `f`; placed in `Foundations/` (Rule 19). Both predicates are
the ones in `MilgromShannon.lean`, with the same `(action, parameter)` order.
-/
import Sanctions.Foundations.MilgromShannon

namespace Sanctions.MilgromShannon

/-- Increasing differences in `(action; parameter)` give single crossing in the
same order. -/
theorem singleCrossingOn_of_increasingDifferencesOn {S T : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : IncreasingDifferencesOn S T f) : SingleCrossingOn S T f := by
  intro x y t t' hx hy hxy ht ht' htt
  have := h hx hy hxy ht ht' htt
  constructor
  · intro h0; linarith
  · intro h0; linarith

end Sanctions.MilgromShannon
