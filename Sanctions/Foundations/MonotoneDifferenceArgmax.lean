/-
Sanctions/Foundations/MonotoneDifferenceArgmax.lean

**Milgrom–Shannon upper-argmax preservation under a monotone difference**
(doc 68, item L7: factored out of `Theory/LockIn/SigmaDynComparison.lean`,
where it had lived in the `Params` namespace while using nothing of the game).

If `g − f` is nondecreasing on a set `K ⊆ ℝ`, then for any maximiser `s_f` of
`f` on `K` and any maximiser `s_g` of `g` on `K`, the larger of the two is again
a maximiser of `g` on `K`. This is the one-dimensional core of the monotone
comparative statics of Milgrom and Shannon (1994): a nondecreasing difference is
increasing differences in the pair (objective, choice).
-/
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

namespace Sanctions
namespace Foundations
namespace MonotoneDifferenceArgmax

/-- **Upper-argmax preservation.** -/
theorem isMaxOn_max_of_monotone_diff
    {f g : ℝ → ℝ} {K : Set ℝ}
    (h_diff_mono : MonotoneOn (fun s => g s - f s) K)
    {s_f s_g : ℝ} (hs_f : s_f ∈ K) (hs_g : s_g ∈ K)
    (h_f_max : IsMaxOn f K s_f) (h_g_max : IsMaxOn g K s_g) :
    IsMaxOn g K (max s_f s_g) := by
  intro s hs
  change g s ≤ g (max s_f s_g)
  by_cases hle : s_g ≤ s_f
  · rw [max_eq_left hle]
    have h_diff_app : g s_g - f s_g ≤ g s_f - f s_f := by
      have := h_diff_mono hs_g hs_f hle
      simpa using this
    have h_f_max_g : f s_g ≤ f s_f := h_f_max hs_g
    have h_g_max_s : g s ≤ g s_g := h_g_max hs
    have h_gsg_le_gsf : g s_g ≤ g s_f := by linarith
    exact le_trans h_g_max_s h_gsg_le_gsf
  · rw [not_le] at hle
    rw [max_eq_right (le_of_lt hle)]
    exact h_g_max hs

/-- `max` of two elements of a set closed under `max` on an interval: the
special case used downstream, `[0,1]`. -/
theorem max_mem_Icc {a b s_f s_g : ℝ}
    (hs_f : s_f ∈ Set.Icc a b) (hs_g : s_g ∈ Set.Icc a b) :
    max s_f s_g ∈ Set.Icc a b :=
  ⟨le_max_iff.mpr (Or.inl hs_f.1), max_le hs_f.2 hs_g.2⟩

end MonotoneDifferenceArgmax
end Foundations
end Sanctions
