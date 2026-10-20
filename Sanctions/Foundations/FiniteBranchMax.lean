/-
Sanctions/Foundations/FiniteBranchMax.lean

A small reusable envelope lemma for validated branchwise maximization.

The substantive work in a finite-branch certificate is to prove that the
branches cover the feasible set, identify a maximizer on every branch, and
compare the finitely many candidate values.  The theorem below packages the
last logical step without introducing any project-specific economics.
-/

import Sanctions.Foundations.Basic

namespace Sanctions
namespace Foundations

/-- If a family of sets covers the feasible domain, each branch has a known
maximizer, and one candidate weakly dominates all branch candidates, then that
candidate maximizes the objective on the full domain.  Finiteness is not needed
for the logical implication; applications use a finite index so the final
candidate comparison reduces to exact arithmetic. -/
theorem isMaxOn_of_branch_cover
    {ι α β : Type*} [Preorder β]
    (f : α → β) (domain : Set α) (branch : ι → Set α)
    (candidate : ι → α) (winner : ι)
    (hcover : ∀ x ∈ domain, ∃ i, x ∈ branch i)
    (hbranch : ∀ i, IsMaxOn f (branch i) (candidate i))
    (hwinner : ∀ i, f (candidate i) ≤ f (candidate winner)) :
    IsMaxOn f domain (candidate winner) := by
  intro x hx
  obtain ⟨i, hxi⟩ := hcover x hx
  exact le_trans (hbranch i hxi) (hwinner i)

/-- Feasibility-aware form of `isMaxOn_of_branch_cover`.  The extra conjunct is
the exact package needed by downstream argmax and equilibrium constructors,
because mathlib's `IsMaxOn` records domination but not membership. -/
theorem mem_and_isMaxOn_of_branch_cover
    {ι α β : Type*} [Preorder β]
    (f : α → β) (domain : Set α) (branch : ι → Set α)
    (candidate : ι → α) (winner : ι)
    (hcover : ∀ x ∈ domain, ∃ i, x ∈ branch i)
    (hbranch : ∀ i, IsMaxOn f (branch i) (candidate i))
    (hwinner : ∀ i, f (candidate i) ≤ f (candidate winner))
    (hwinner_mem : candidate winner ∈ domain) :
    candidate winner ∈ domain ∧ IsMaxOn f domain (candidate winner) :=
  ⟨hwinner_mem,
    isMaxOn_of_branch_cover f domain branch candidate winner
      hcover hbranch hwinner⟩

/-- Completed-square normal form used by the branch certificate. -/
noncomputable def concaveQuadratic (κ v c x : ℝ) : ℝ :=
  c - κ / 2 * (x - v) ^ 2

/-- A concave quadratic is maximized at its vertex on any domain when its
curvature is nonnegative.  Feasibility of the vertex is deliberately separate:
the branch certificate must still prove that the selected candidate belongs to
the relevant feasible cell. -/
theorem concaveQuadratic_vertex_isMaxOn
    (κ v c : ℝ) (hκ : 0 ≤ κ) (domain : Set ℝ) :
    IsMaxOn (concaveQuadratic κ v c) domain v := by
  intro x _hx
  change c - κ / 2 * (x - v) ^ 2 ≤ c - κ / 2 * (v - v) ^ 2
  rw [sub_self, zero_pow (by norm_num), mul_zero, sub_zero]
  exact sub_le_self c
    (mul_nonneg (div_nonneg hκ (by norm_num)) (sq_nonneg _))

/-- If the quadratic vertex lies weakly to the left of an interval, the left
endpoint is a branch maximizer. -/
theorem concaveQuadratic_left_isMaxOn_Icc
    (κ v c lo hi : ℝ) (hκ : 0 ≤ κ) (hv : v ≤ lo) :
    IsMaxOn (concaveQuadratic κ v c) (Set.Icc lo hi) lo := by
  intro x hx
  change c - κ / 2 * (x - v) ^ 2 ≤ c - κ / 2 * (lo - v) ^ 2
  rcases hx with ⟨hlo, _hhi⟩
  have hdist : (lo - v) ^ 2 ≤ (x - v) ^ 2 := by
    nlinarith
  exact sub_le_sub_left
    (mul_le_mul_of_nonneg_left hdist
      (div_nonneg hκ (by norm_num))) c

/-- If the quadratic vertex lies weakly to the right of an interval, the right
endpoint is a branch maximizer. -/
theorem concaveQuadratic_right_isMaxOn_Icc
    (κ v c lo hi : ℝ) (hκ : 0 ≤ κ) (hv : hi ≤ v) :
    IsMaxOn (concaveQuadratic κ v c) (Set.Icc lo hi) hi := by
  intro x hx
  change c - κ / 2 * (x - v) ^ 2 ≤ c - κ / 2 * (hi - v) ^ 2
  rcases hx with ⟨_hlo, hhi⟩
  have hdist : (hi - v) ^ 2 ≤ (x - v) ^ 2 := by
    nlinarith
  exact sub_le_sub_left
    (mul_le_mul_of_nonneg_left hdist
      (div_nonneg hκ (by norm_num))) c

end Foundations
end Sanctions
