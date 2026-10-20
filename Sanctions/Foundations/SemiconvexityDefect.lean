/-
Sanctions/Foundations/SemiconvexityDefect.lean

**A kink admits no curvature modulus.**

External mathematics, stated over an abstract `g : ℝ → ℝ`: nothing here mentions
the sanctions model, and the file is placed in `Foundations/` accordingly
(Rule 19).

*Semiconvexity* caps how far a function may rise above its own chords: `g` is
`c`-semiconvex when `g + (c/2)·x²` is convex, equivalently when the excess of
`g` over the chord is at most `(c/2)·t(1−t)(y₁−y₂)²`. Semiconcavity is the
mirror, capping how far the function may dip below its chords. Both are the standard way to say "curvature is
bounded on one side" without assuming differentiability, and the chord form is
the one this development uses for value carriers: the pair
`SemiconcaveOnSet` / `SemiconvexOnSet` in `Foundations/SemiconcaveSup` (one
shape, two signs; the second spelling this file once carried was retired on
2026-09-04 in favour of that pair).

The observation isolated here is why a *kink* — a jump in slope — escapes both
caps. The cap is **quadratic** in the width of the chord, while the defect a
kink produces is **linear** in it. Shrink the chord onto the kink and the defect
outruns the cap, whatever modulus was proposed. No derivative is taken and no
smoothness is assumed anywhere: the hypothesis is a family of symmetric triples
whose defect is bounded below linearly, which is exactly what a slope jump
supplies.

The two theorems are stated as refutations of `∃ c, …`, so they say *no finite
modulus works*, not merely that some particular one fails.
-/
import Sanctions.Foundations.SemiconcaveSup
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set Sanctions.Semiconcave

namespace Sanctions

/-! ## Kinks escape both caps -/

/-- **A concave kink admits no semiconvexity modulus.** If, on every symmetric
triple `t − ε, t, t + ε` of half-width `ε ≤ d` inside `A`, the value at the
midpoint sits at least `ε/2` above the chord — a defect *linear* in the width —
then no `c` makes `g` `c`-semiconvex on `A`: the cap allows only `(c/2)·ε²`, and
any proposed `c` is defeated by taking `ε` below `1/(|c|+1)`.

No smoothness, no differentiability, and no sign condition on `c`: a negative or
zero modulus is refuted along with the positive ones. -/
theorem not_semiconvexOnSet_of_linearDefect {g : ℝ → ℝ} {A : Set ℝ} {t d : ℝ}
    (hd : 0 < d)
    (hmemL : ∀ ε : ℝ, 0 < ε → ε ≤ d → t - ε ∈ A)
    (hmemR : ∀ ε : ℝ, 0 < ε → ε ≤ d → t + ε ∈ A)
    (hdef : ∀ ε : ℝ, 0 < ε → ε ≤ d → g (t - ε) + g (t + ε) + ε ≤ 2 * g t) :
    ¬ ∃ c : ℝ, SemiconvexOnSet g A c := by
  rintro ⟨c, hc⟩
  set ε : ℝ := min d (1 / (|c| + 1)) with hε_def
  have habs : (0:ℝ) < |c| + 1 := by positivity
  have hε_pos : 0 < ε := lt_min hd (by positivity)
  have hε_le_d : ε ≤ d := min_le_left _ _
  have hε_le : ε ≤ 1 / (|c| + 1) := min_le_right _ _
  -- The proposed cap, read on the symmetric triple of half-width `ε`.
  have hmid : (1/2 : ℝ) * (t - ε) + (1 - 1/2) * (t + ε) = t := by ring
  have hcap := hc (t - ε) (hmemL ε hε_pos hε_le_d) (t + ε)
    (hmemR ε hε_pos hε_le_d) (1/2) (by norm_num) (by norm_num)
  rw [hmid] at hcap
  have hsq : ((t - ε) - (t + ε)) ^ 2 = 4 * ε ^ 2 := by ring
  rw [hsq] at hcap
  -- The kink's own defect, on the same triple.
  have hk := hdef ε hε_pos hε_le_d
  -- Cap says `ε/2 ≤ (c/2)·ε²`; the modulus bound says `c·ε < 1`.
  have hstep : ε / 2 ≤ c / 2 * ε ^ 2 := by nlinarith [hcap, hk]
  have hcε : c * ε < 1 := by
    have h1 : c ≤ |c| := le_abs_self c
    have h2 : ε * (|c| + 1) ≤ 1 := by
      rw [← le_div_iff₀ habs]
      simpa using hε_le
    nlinarith [hε_pos, abs_nonneg c]
  nlinarith [hε_pos, hstep, hcε]

/-- **A convex kink admits no semiconcavity modulus.** The mirror of
`not_semiconvexOnSet_of_linearDefect`: here the midpoint sits at least `ε/2`
*below* the chord, and the semiconcavity cap is again quadratic. -/
theorem not_semiconcaveOnSet_of_linearDefect {g : ℝ → ℝ} {A : Set ℝ} {t d : ℝ}
    (hd : 0 < d)
    (hmemL : ∀ ε : ℝ, 0 < ε → ε ≤ d → t - ε ∈ A)
    (hmemR : ∀ ε : ℝ, 0 < ε → ε ≤ d → t + ε ∈ A)
    (hdef : ∀ ε : ℝ, 0 < ε → ε ≤ d → 2 * g t + ε ≤ g (t - ε) + g (t + ε)) :
    ¬ ∃ c : ℝ, SemiconcaveOnSet g A c := by
  rintro ⟨c, hc⟩
  set ε : ℝ := min d (1 / (|c| + 1)) with hε_def
  have habs : (0:ℝ) < |c| + 1 := by positivity
  have hε_pos : 0 < ε := lt_min hd (by positivity)
  have hε_le_d : ε ≤ d := min_le_left _ _
  have hε_le : ε ≤ 1 / (|c| + 1) := min_le_right _ _
  have hmid : (1/2 : ℝ) * (t - ε) + (1 - 1/2) * (t + ε) = t := by ring
  have hcap := hc (t - ε) (hmemL ε hε_pos hε_le_d) (t + ε)
    (hmemR ε hε_pos hε_le_d) (1/2) (by norm_num) (by norm_num)
  rw [hmid] at hcap
  have hsq : ((t - ε) - (t + ε)) ^ 2 = 4 * ε ^ 2 := by ring
  rw [hsq] at hcap
  have hk := hdef ε hε_pos hε_le_d
  have hstep : ε / 2 ≤ c / 2 * ε ^ 2 := by nlinarith [hcap, hk]
  have hcε : c * ε < 1 := by
    have h1 : c ≤ |c| := le_abs_self c
    have h2 : ε * (|c| + 1) ≤ 1 := by
      rw [← le_div_iff₀ habs]
      simpa using hε_le
    nlinarith [hε_pos, abs_nonneg c]
  nlinarith [hε_pos, hstep, hcε]

end Sanctions
