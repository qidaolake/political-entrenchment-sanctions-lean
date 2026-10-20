/-
Sanctions/Examples/Sharpness/SemiconcaveSup.lean

**ROLE: SHARPNESS, and NECESSITY.**

`Foundations/SemiconcaveSup.lean` proves that a partial supremum of a jointly
semiconcave function is semiconcave with Schur-complement modulus
`sigma + rho^2/q`. Two things about that theorem are not visible from its
statement, and both are settled here by construction:

* the modulus is **attained** on the quadratic model, so `sigma + rho^2/q` is
  not a convenient over-estimate and cannot later be "improved" to `sigma`;
* the action-concavity hypothesis `q > 0` is **load-bearing** --- drop it and
  the conclusion is false, so it is not a regularity convenience.

Rule 9: each is a refutation of one specific universal. Neither says anything
about how far from sharp the modulus is on any other family.

Relocated 2026-08-27 from `Foundations/SemiconcaveSup.lean`, whose general
theorem remains there. Statements are byte-identical and the namespace is
unchanged, so every fully-qualified name is preserved.
-/

import Sanctions.Foundations.SemiconcaveSup

noncomputable section
open Set

namespace Sanctions.Semiconcave

/-- **The modulus is exact on the quadratic model.** For
`Φ(x,a) = (σ/2)x² + ρ·x·a − (q/2)a²` with an unconstrained action, the
maximiser is `a = ρx/q` and the value is `((σ + ρ²/q)/2)·x²`.

This pins the constant: `σ + ρ²/q` is not a convenient over-estimate, it is
attained. Recorded so no later round "improves" the modulus to `σ`. -/
theorem schur_modulus_exact {σ ρ q : ℝ} (hq : 0 < q) (x : ℝ) :
    IsGreatest ((fun a => σ / 2 * x ^ 2 + ρ * x * a - q / 2 * a ^ 2) '' univ)
      ((σ + ρ ^ 2 / q) / 2 * x ^ 2) := by
  constructor
  · refine ⟨ρ * x / q, mem_univ _, ?_⟩
    field_simp
    ring
  · rintro y ⟨a, -, rfl⟩
    have h : 0 ≤ q * (a - ρ * x / q) ^ 2 := by positivity
    have hq' := hq.ne'
    field_simp at h ⊢
    nlinarith [h]

/-- **`q > 0` is necessary.** With no action concavity and a live cross
term, the value of the two-point action set `{0, 1}` at `Φ(x,a) = x·a` is
`max x 0`, which is convex with a corner at the origin and therefore
semiconcave with *no* finite modulus on any neighbourhood of `0`.

Recorded as a fence: the strict-concavity hypothesis of
`sup_semiconcave_of_joint` cannot be dropped. -/
theorem schur_needs_action_concavity :
    ¬ ∃ c : ℝ, SemiconcaveOnSet (fun x => max x 0) (Icc (-1 : ℝ) 1) c := by
  rintro ⟨c, hc⟩
  -- Chord at `x₁ = -ε`, `x₂ = ε`, midpoint `0`, weight `1/2`:
  -- the left value is `0`, the right is `ε`, the midpoint value is `0`,
  -- so the defect is `ε/2` while the budget is `c/2 · (1/4) · (2ε)² = cε²`.
  -- For small `ε` the defect beats the budget.
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ε ≤ c * ε ^ 2 := by
    intro ε hε hε1
    have h := hc (-ε) ⟨by linarith, by linarith⟩ ε ⟨by linarith, hε1⟩ (1/2)
      (by norm_num) (by norm_num)
    simp only [show (1:ℝ)/2 * (-ε) + (1 - 1/2) * ε = 0 by ring,
      max_eq_right (by linarith : (-ε : ℝ) ≤ 0), max_eq_left hε.le,
      max_self] at h
    linarith
  -- Dividing by `ε > 0`: the modulus would have to satisfy `1 ≤ c·ε` for
  -- every small `ε`, which is impossible.
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ c * ε := by
    intro ε hε hε1
    nlinarith [key ε hε hε1]
  have hc1 : (1:ℝ) ≤ c := by have := hstep 1 (by norm_num) le_rfl; linarith
  have hcpos : (0:ℝ) < c := by linarith
  have h2 := hstep (1 / (2 * c)) (by positivity)
    (by rw [div_le_one (by linarith)]; linarith)
  have hval : c * (1 / (2 * c)) = 1 / 2 := by field_simp
  rw [hval] at h2
  linarith

end Sanctions.Semiconcave

end
