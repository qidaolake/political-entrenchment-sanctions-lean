/-
Sanctions/Foundations/StrongConcaveArgmax.lean

**Strong concavity at a maximiser: the deviation inequality and the
argmax-Lipschitz consequence** (relocated from `Theory/Bellman/StrongConcaveHolder`
and `Theory/Shocked/ShockedArgmaxLipschitz` in doc 71 round G, T4; Rule 19:
both statements are generic mathematics over mathlib's `StrongConcaveOn` and
mention no project structure).

* `StrongConcaveOn.deviation_at_maximizer`: if `f` is `c`-strongly concave on
  a convex set `S` and `s_max ∈ S` maximises `f` on `S`, then every `s' ∈ S`
  satisfies `f s' ≤ f s_max − (c/4)(s_max − s')²`. Apply strong concavity at
  the midpoint of `s_max` and `s'`, then maximality at the midpoint.
* `argmax_lipschitz_of_strongConcave_lipschitzDiff`: if `f, g` are
  `c`-strongly concave on `S` with maximisers `af, ag`, and the *difference*
  `f − g` moves by at most `L·|af − ag|` between the two maximisers, then
  `c·|af − ag| ≤ 2L`. This is the conceptual core of the atomless-shock
  upgrade from Hölder-½ to Lipschitz argmaxes: replace the sup bound on the
  objective difference by a Lipschitz bound. No first-order condition, no
  implicit function theorem.

Reference: Montrucchio (1987), Lipschitz policies from strong concavity
(`PaperRefer/MathTheory/LipschitzPolicyStronglyConcave-Montrucchio-1987.md`).
-/
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace Sanctions

open scoped NNReal

/-- **Deviation-at-maximiser lemma for strongly concave functions on a
convex set.** If `f` is `c`-strongly concave on `S`, `s_max ∈ S` is a
maximiser of `f` on `S`, and `s' ∈ S`, then
`f s' ≤ f s_max - (c/4)(s_max - s')^2`. -/
theorem StrongConcaveOn.deviation_at_maximizer
    {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ}
    (hS_convex : Convex ℝ S)
    (hf : StrongConcaveOn S c f)
    {s_max s' : ℝ} (hs_max : s_max ∈ S) (hs' : s' ∈ S)
    (h_max : ∀ y ∈ S, f y ≤ f s_max) :
    f s' ≤ f s_max - (c / 4) * (s_max - s') ^ 2 := by
  have h_half : (0:ℝ) ≤ 1/2 := by norm_num
  have h_sum : (1/2 : ℝ) + 1/2 = 1 := by norm_num
  unfold StrongConcaveOn UniformConcaveOn at hf
  have h_sc := hf.2 hs_max hs' h_half h_half h_sum
  dsimp only at h_sc
  have h_norm_sq : ‖s_max - s'‖ ^ 2 = (s_max - s') ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_norm_sq] at h_sc
  have h_mid_mem : (1/2 : ℝ) • s_max + (1/2 : ℝ) • s' ∈ S :=
    hS_convex hs_max hs' h_half h_half h_sum
  have h_mid_le : f ((1/2 : ℝ) • s_max + (1/2 : ℝ) • s') ≤ f s_max :=
    h_max _ h_mid_mem
  simp only [smul_eq_mul] at h_sc h_mid_le
  have h_chain := le_trans h_sc h_mid_le
  have h_compute :
      (1/2 : ℝ) * (1/2) * (c / 2 * (s_max - s') ^ 2)
        = c / 8 * (s_max - s') ^ 2 := by ring
  rw [h_compute] at h_chain
  linarith

/-- **Argmax-Lipschitz from strong concavity and a Lipschitz objective
difference.** If `f, g` are `c`-strongly concave on a convex set `S` with
maximisers `af, ag`, and `f − g` moves by at most `L·|af − ag|` between the two
maximisers, then `c·|af − ag| ≤ 2L`. -/
theorem argmax_lipschitz_of_strongConcave_lipschitzDiff
    {f g : ℝ → ℝ} {S : Set ℝ} {c L : ℝ} (hL : 0 ≤ L)
    (hS : Convex ℝ S)
    (hf_sc : StrongConcaveOn S c f) (hg_sc : StrongConcaveOn S c g)
    {af ag : ℝ} (haf : af ∈ S) (hag : ag ∈ S)
    (hf_max : ∀ y ∈ S, f y ≤ f af) (hg_max : ∀ y ∈ S, g y ≤ g ag)
    (h_diff_lip : |(f af - g af) - (f ag - g ag)| ≤ L * |af - ag|) :
    c * |af - ag| ≤ 2 * L := by
  have hdf : f ag ≤ f af - (c / 4) * (af - ag) ^ 2 :=
    StrongConcaveOn.deviation_at_maximizer hS hf_sc haf hag hf_max
  have hdg : g af ≤ g ag - (c / 4) * (ag - af) ^ 2 :=
    StrongConcaveOn.deviation_at_maximizer hS hg_sc hag haf hg_max
  have hsq : (ag - af) ^ 2 = (af - ag) ^ 2 := by ring
  rw [hsq] at hdg
  have hkey : (c / 2) * (af - ag) ^ 2 ≤ (f af - g af) - (f ag - g ag) := by linarith
  have hbound : (c / 2) * (af - ag) ^ 2 ≤ L * |af - ag| :=
    le_trans hkey (le_trans (le_abs_self _) h_diff_lip)
  have hsq2 : (af - ag) ^ 2 = |af - ag| ^ 2 := (sq_abs _).symm
  rw [hsq2] at hbound
  rcases (abs_nonneg (af - ag)).lt_or_eq with hpos | h0
  · nlinarith [hbound, hpos]
  · rw [← h0]; simpa using hL

end Sanctions
