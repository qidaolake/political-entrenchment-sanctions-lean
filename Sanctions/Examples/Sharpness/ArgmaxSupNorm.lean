/-
Sanctions/Examples/Sharpness/ArgmaxSupNorm.lean

**ROLE: SHARPNESS.**

`Foundations/ArgmaxSupNormLimit.lean` proves the upper bound: if two objectives
are within `eps` in sup norm and one is strongly concave, their maximizers are
within `O(sqrt eps)`. That bound could in principle be loose. This file shows it
is not, by exhibiting a one-parameter family that attains the square-root rate.

Rule 9: attainment at this family licenses no claim about the constant at any
other family, and no claim that the rate is attained generically. It blocks one
specific improvement --- a linear-in-eps bound --- and nothing more.

Relocated 2026-08-27 from `Foundations/ArgmaxSupNormLimit.lean`, whose general
bound remains there. Statements are byte-identical and the namespace is
unchanged, so every fully-qualified name is preserved.
-/

import Sanctions.Foundations.ArgmaxSupNormLimit

namespace Sanctions
namespace ArgmaxSupNormLimit

open Set

/-! ## 2. The square root is attained: a localised perturbation

The three objects below make one family, indexed by `t ∈ (0,1]`. The base
objective `negSq` is fixed and strongly concave with modulus `2`; the
perturbation `clampedRamp t` has sup norm exactly `t²`; and it moves the
maximizer from `0` to `t/2`. Writing `ε := t²`, the displacement is `√ε / 2`.

The shape is forced. To move the maximizer of a curvature-`c` function by `d`,
the perturbation must overcome a value deficit of order `c·d²`, so on a budget
of `ε` the best a perturbation can do is `d ≍ √ε` -- and only if it spends its
whole budget across a window of width `d`, i.e. with slope `ε/d ≍ √ε`. A
globally-slope-`O(ε)` perturbation (like the affine one this file used to use)
moves the argmax only `O(ε)`. -/

/-- The fixed base objective `s ↦ -s²`. -/
noncomputable def negSq : ℝ → ℝ := fun s => -s ^ 2

/-- **The localised perturbation.** A ramp that is `0` for `s ≤ 0`, rises with
slope `t` on `[0, t]`, and is flat at height `t²` thereafter. Its sup norm is
`t²` and its slope on the rising window is `t = √(t²)`. -/
noncomputable def clampedRamp (t : ℝ) : ℝ → ℝ :=
  fun s => max 0 (min (t ^ 2) (t * s))

/-- The perturbed objective `negSq + clampedRamp t`. -/
noncomputable def perturbed (t : ℝ) : ℝ → ℝ :=
  fun s => negSq s + clampedRamp t s

/-- `s ↦ -s²` is strongly concave with modulus `2` on any convex set. The
defining inequality holds with equality, which is why the modulus is exactly
`2` and not less. -/
theorem negSq_strongConcaveOn {A : Set ℝ} (hA : Convex ℝ A) :
    StrongConcaveOn A 2 negSq := by
  unfold StrongConcaveOn UniformConcaveOn
  refine ⟨hA, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [negSq, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (x - y)]

/-- The base objective peaks at `0`. -/
theorem negSq_isMaxOn : IsMaxOn negSq (Icc (-1 : ℝ) 1) 0 := by
  intro z _
  simp only [negSq, mem_setOf_eq]
  nlinarith [sq_nonneg z]

/-- The ramp is bounded between `0` and `t²`. -/
theorem clampedRamp_bounds {t : ℝ} (ht0 : 0 < t) (s : ℝ) :
    0 ≤ clampedRamp t s ∧ clampedRamp t s ≤ t ^ 2 :=
  ⟨le_max_left _ _, max_le (by positivity) (min_le_left _ _)⟩

/-- The ramp never exceeds the bare line `max 0 (t·s)`; this is the only
property of it the maximizer argument needs. -/
theorem clampedRamp_le_line {t : ℝ} (s : ℝ) :
    clampedRamp t s ≤ max 0 (t * s) :=
  max_le_max le_rfl (min_le_right _ _)

/-- **The perturbed objective peaks at `t/2`.** The ramp's rising window is
`[0, t]`, and inside it the objective is `-s² + t·s`, whose peak is at `t/2`.
The flat part beyond `t` and the zero part below `0` are both dominated. -/
theorem perturbed_isMaxOn {t : ℝ} (ht0 : 0 < t) :
    IsMaxOn (perturbed t) (Icc (-1 : ℝ) 1) (t / 2) := by
  have hpeak : perturbed t (t / 2) = t ^ 2 / 4 := by
    have hmin : min (t ^ 2) (t * (t / 2)) = t ^ 2 / 2 := by
      rw [min_eq_right (by nlinarith)]; ring
    simp only [perturbed, negSq, clampedRamp, hmin]
    rw [max_eq_right (by positivity)]
    ring
  intro z _
  simp only [mem_setOf_eq, hpeak]
  have hline : perturbed t z ≤ negSq z + max 0 (t * z) := by
    simp only [perturbed]
    linarith [clampedRamp_le_line (t := t) z]
  rcases le_or_gt (0 : ℝ) z with hz | hz
  · -- rising side: `-z² + t·z ≤ t²/4`, with equality exactly at `z = t/2`
    have hmax : max 0 (t * z) = t * z := max_eq_right (by positivity)
    rw [hmax] at hline
    simp only [negSq] at hline
    nlinarith [sq_nonneg (z - t / 2)]
  · -- left of the window the ramp is zero and the base objective is already ≤ 0
    have hmax : max 0 (t * z) = 0 := max_eq_left (by nlinarith)
    rw [hmax] at hline
    simp only [negSq] at hline
    nlinarith [sq_nonneg z]

/-- **The sup-norm size of the perturbation is exactly `t²`**, and it is
attained at the right endpoint. Proving attainment matters: a bound `≤ t²` alone
would leave open that the true gap is far smaller, which would break the
sharpness reading. -/
theorem perturbed_sup_gap {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∀ z ∈ Icc (-1 : ℝ) 1, |negSq z - perturbed t z| ≤ t ^ 2)
    ∧ |negSq 1 - perturbed t 1| = t ^ 2 := by
  have hsub : ∀ z : ℝ, negSq z - perturbed t z = -clampedRamp t z := by
    intro z; simp only [perturbed]; ring
  constructor
  · intro z _
    have h := clampedRamp_bounds ht0 (t := t) z
    rw [hsub z, abs_neg, abs_of_nonneg h.1]
    exact h.2
  · have hmin : min (t ^ 2) (t * 1) = t ^ 2 := min_eq_left (by nlinarith)
    rw [hsub 1, abs_neg, clampedRamp, hmin, max_eq_right (by positivity),
      abs_of_nonneg (by positivity)]

/-- **The `√ε` rate in `argmax_sq_dist_le_of_sup_close` is attained.**

For every `t ∈ (0,1]`, setting `ε := t²` gives a configuration satisfying *every*
hypothesis of `argmax_sq_dist_le_of_sup_close` at modulus `c = 2` -- strong
concavity of the base objective, both maximizers, and the sup-norm bound, which
is moreover *exact* -- and in which the squared displacement is exactly `ε/4`.
That is `|a - b| = √ε / 2`.

So no inequality of the form `|a - b| ≤ L·ε` can hold across this family: as
`t → 0` the left side falls like `t` and the right like `t²`. The modulus is
held fixed at `2` throughout, so this is not repaired by assuming more
curvature.

Rule 9A: one family, licensing the non-existence of a linear bound *for these
hypotheses* -- read contrapositively, it refutes the universal "strong concavity
plus sup-norm closeness implies a Lipschitz argmax estimate". It licenses
nothing about whether a linear bound holds under stronger hypotheses; it does
not, for instance, touch the slope-controlled estimate in
`ArgmaxSensitivity.lean`, which is exactly the point of the contrast. -/
theorem sqrt_rate_is_attained {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ ε : ℝ,
      0 < ε
      ∧ StrongConcaveOn (Icc (-1 : ℝ) 1) 2 negSq
      ∧ IsMaxOn negSq (Icc (-1 : ℝ) 1) 0
      ∧ IsMaxOn (perturbed t) (Icc (-1 : ℝ) 1) (t / 2)
      ∧ (0 : ℝ) ∈ Icc (-1 : ℝ) 1
      ∧ t / 2 ∈ Icc (-1 : ℝ) 1
      ∧ (∀ z ∈ Icc (-1 : ℝ) 1, |negSq z - perturbed t z| ≤ ε)
      ∧ (∃ z ∈ Icc (-1 : ℝ) 1, |negSq z - perturbed t z| = ε)
      ∧ (0 - t / 2) ^ 2 = ε / 4 :=
  ⟨t ^ 2, by positivity, negSq_strongConcaveOn (convex_Icc _ _),
    negSq_isMaxOn, perturbed_isMaxOn ht0,
    ⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩,
    (perturbed_sup_gap ht0 ht1).1,
    ⟨1, ⟨by norm_num, le_rfl⟩, (perturbed_sup_gap ht0 ht1).2⟩, by ring⟩

end ArgmaxSupNormLimit
end Sanctions
