/-
Sanctions/Foundations/DiscountedExtremum.lean

**The discounted-extremum argument** (round BB, 2026-09-28; doc 110 §5, the
shared lemma M8 of the completeness review).

If a bounded-below quantity `f i` dominates a discounted copy of itself at a
successor index, `β·f (φ i) ≤ f i` with `0 ≤ β < 1`, then `f` is nonnegative:
its infimum `D` satisfies `D ≥ β·D`, hence `D ≥ 0`. This is the step the
project's uniqueness and relief proofs wrote inline twice
(`PlacableSenderUniqueness.lean`, the deficit infimum; and
`PlacableSenderReliefUniqueness.lean`, the dual supremum). It is the
closed-cone step of Stokey–Lucas–Prescott §4.1 in its barest form: no
operator, no completeness of a function space, only a bound and a map.

Two corollaries:

* `monotone_of_eq_add_mul_comp` — a bounded solution of `W = h + β·W∘z`, with
  `h` monotone and `z` monotone, is monotone (the monotone cone is closed under
  the discounted composition).
* `monotone_sub_of_solves` — **patience increasing differences**: if bounded
  `V₁`, `V₂` solve `Vᵢ = u + βᵢ·Vᵢ∘z` along a common monotone `z`, with
  `0 ≤ β₁ ≤ β₂ < 1`, and either `Vᵢ` is monotone, then `β₂·V₂ − β₁·V₁` is
  monotone. It needs no monotonicity of the flow `u`, unlike the lemma of
  Acemoglu–Jensen (2015, Lemma 2) it resembles; boundedness is what it needs.

Rule 19: statements about real functions on an arbitrary index type or
preorder; the consumers are in `Theory/` and `Examples/`.
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Archimedean

namespace Sanctions
namespace Foundations
namespace DiscountedExtremum

open Set

/-- **The discounted-extremum lemma.** A bounded-below `f` with
`β·f (φ i) ≤ f i` for every `i`, and `0 ≤ β < 1`, is nonnegative. -/
theorem nonneg_of_mul_comp_le {ι : Type*} {f : ι → ℝ} {φ : ι → ι} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hbdd : BddBelow (range f))
    (hstep : ∀ i, β * f (φ i) ≤ f i) (i : ι) : 0 ≤ f i := by
  have hne : (range f).Nonempty := ⟨f i, i, rfl⟩
  set D := sInf (range f) with hD
  have hle : ∀ j, D ≤ f j := fun j => csInf_le hbdd ⟨j, rfl⟩
  have hDD : β * D ≤ D := by
    apply le_csInf hne
    rintro _ ⟨j, rfl⟩
    exact (mul_le_mul_of_nonneg_left (hle (φ j)) hβ0).trans (hstep j)
  have hD0 : 0 ≤ D := by
    by_contra hcon
    have hneg : D < 0 := not_le.mp hcon
    have := mul_lt_mul_of_neg_right hβ1 hneg
    linarith
  exact hD0.trans (hle i)

/-- **The dual form.** A bounded-above `f` with `f i ≤ β·f (φ i)` for every
`i`, and `0 ≤ β < 1`, is nonpositive. -/
theorem nonpos_of_le_mul_comp {ι : Type*} {f : ι → ℝ} {φ : ι → ι} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hbdd : BddAbove (range f))
    (hstep : ∀ i, f i ≤ β * f (φ i)) (i : ι) : f i ≤ 0 := by
  have hbdd' : BddBelow (range (fun j => -f j)) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨-b, by rintro _ ⟨j, rfl⟩; exact neg_le_neg (hb ⟨j, rfl⟩)⟩
  have h := nonneg_of_mul_comp_le (f := fun j => -f j) (φ := φ) hβ0 hβ1 hbdd'
    (fun j => by have := hstep j; simp only; linarith) i
  simp only at h
  linarith

/-- **The monotone cone is closed under discounted composition.** If `W` is
bounded, `W x = h x + β·W (z x)` for every `x`, `h` and `z` are monotone and
`0 ≤ β < 1`, then `W` is monotone. -/
theorem monotone_of_eq_add_mul_comp {X : Type*} [Preorder X] {W h : X → ℝ} {z : X → X}
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M : ℝ} (hWb : ∀ x, |W x| ≤ M)
    (hh : Monotone h) (hz : Monotone z) (hW : ∀ x, W x = h x + β * W (z x)) :
    Monotone W := by
  let ι := {q : X × X // q.1 ≤ q.2}
  let f : ι → ℝ := fun q => W q.1.2 - W q.1.1
  let φ : ι → ι := fun q => ⟨(z q.1.1, z q.1.2), hz q.2⟩
  have hbdd : BddBelow (range f) := by
    refine ⟨-(2 * M), ?_⟩
    rintro _ ⟨q, rfl⟩
    have h1 := abs_le.mp (hWb q.1.1)
    have h2 := abs_le.mp (hWb q.1.2)
    simp only [f]
    linarith
  have hstep : ∀ q, β * f (φ q) ≤ f q := by
    intro q
    simp only [f, φ]
    rw [hW q.1.2, hW q.1.1]
    have := hh q.2
    linarith
  intro x y hxy
  have := nonneg_of_mul_comp_le hβ0 hβ1 hbdd hstep ⟨(x, y), hxy⟩
  simp only [f] at this
  linarith

/-- **Patience increasing differences.** Let bounded `V₁`, `V₂` solve
`Vᵢ x = u x + βᵢ·Vᵢ (z x)` along a common monotone `z`, with
`0 ≤ β₁ ≤ β₂ < 1`. If `V₂` is monotone, then `β₂·V₂ − β₁·V₁` is monotone.
(`W := β₂V₂ − β₁V₁` solves `W = (β₂ − β₁)·V₂ + β₁·W∘z`.) -/
theorem monotone_sub_of_solves_of_monotone_right {X : Type*} [Preorder X]
    {V₁ V₂ u : X → ℝ} {z : X → X} {β₁ β₂ M : ℝ}
    (hβ₁ : 0 ≤ β₁) (hβ₁₂ : β₁ ≤ β₂) (hβ₂ : β₂ < 1)
    (hV₁b : ∀ x, |V₁ x| ≤ M) (hV₂b : ∀ x, |V₂ x| ≤ M)
    (hz : Monotone z)
    (hV₁ : ∀ x, V₁ x = u x + β₁ * V₁ (z x)) (hV₂ : ∀ x, V₂ x = u x + β₂ * V₂ (z x))
    (hmono : Monotone V₂) :
    Monotone (fun x => β₂ * V₂ x - β₁ * V₁ x) := by
  have hβ₂0 : 0 ≤ β₂ := hβ₁.trans hβ₁₂
  have hβ₁1 : β₁ < 1 := lt_of_le_of_lt hβ₁₂ hβ₂
  refine monotone_of_eq_add_mul_comp (W := fun x => β₂ * V₂ x - β₁ * V₁ x)
    (h := fun x => (β₂ - β₁) * V₂ x) hβ₁ hβ₁1 (M := β₂ * M + β₁ * M) ?_ ?_ hz ?_
  · intro x
    have h1 := abs_le.mp (hV₁b x)
    have h2 := abs_le.mp (hV₂b x)
    rw [abs_le]
    constructor <;> nlinarith
  · intro x y hxy
    exact mul_le_mul_of_nonneg_left (hmono hxy) (sub_nonneg.mpr hβ₁₂)
  · intro x
    have e1 := hV₁ x
    have e2 := hV₂ x
    simp only
    -- `β₁·u x = β₁·(V₂ x − β₂·V₂ (z x))`
    have hu : u x = V₂ x - β₂ * V₂ (z x) := by linarith
    rw [e1, hu]
    ring

/-- **Patience increasing differences, the other side.** As
`monotone_sub_of_solves_of_monotone_right`, when `V₁` is the monotone one.
(`D := V₂ − V₁` solves `D = (β₂ − β₁)·V₁∘z + β₂·D∘z`, so `D` is monotone, and
`β₂V₂ − β₁V₁ = β₂·D + (β₂ − β₁)·V₁`.) -/
theorem monotone_sub_of_solves_of_monotone_left {X : Type*} [Preorder X]
    {V₁ V₂ u : X → ℝ} {z : X → X} {β₁ β₂ M : ℝ}
    (hβ₁ : 0 ≤ β₁) (hβ₁₂ : β₁ ≤ β₂) (hβ₂ : β₂ < 1)
    (hV₁b : ∀ x, |V₁ x| ≤ M) (hV₂b : ∀ x, |V₂ x| ≤ M)
    (hz : Monotone z)
    (hV₁ : ∀ x, V₁ x = u x + β₁ * V₁ (z x)) (hV₂ : ∀ x, V₂ x = u x + β₂ * V₂ (z x))
    (hmono : Monotone V₁) :
    Monotone (fun x => β₂ * V₂ x - β₁ * V₁ x) := by
  have hβ₂0 : 0 ≤ β₂ := hβ₁.trans hβ₁₂
  have hD : Monotone (fun x => V₂ x - V₁ x) := by
    refine monotone_of_eq_add_mul_comp (W := fun x => V₂ x - V₁ x)
      (h := fun x => (β₂ - β₁) * V₁ (z x)) hβ₂0 hβ₂ (M := M + M) ?_ ?_ hz ?_
    · intro x
      have h1 := abs_le.mp (hV₁b x)
      have h2 := abs_le.mp (hV₂b x)
      rw [abs_le]
      constructor <;> linarith
    · intro x y hxy
      exact mul_le_mul_of_nonneg_left (hmono (hz hxy)) (sub_nonneg.mpr hβ₁₂)
    · intro x
      simp only
      rw [hV₁ x, hV₂ x]
      ring
  intro x y hxy
  have h1 := mul_le_mul_of_nonneg_left (hD hxy) hβ₂0
  have h2 := mul_le_mul_of_nonneg_left (hmono hxy) (sub_nonneg.mpr hβ₁₂)
  simp only at h1 h2 ⊢
  nlinarith [h1, h2]

end DiscountedExtremum
end Foundations
end Sanctions

#print axioms Sanctions.Foundations.DiscountedExtremum.nonneg_of_mul_comp_le
#print axioms Sanctions.Foundations.DiscountedExtremum.nonpos_of_le_mul_comp
#print axioms Sanctions.Foundations.DiscountedExtremum.monotone_of_eq_add_mul_comp
#print axioms Sanctions.Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_right
#print axioms Sanctions.Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_left
