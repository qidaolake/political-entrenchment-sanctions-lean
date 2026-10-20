/-
Sanctions/Foundations/TransitionExtension.lean

**From a transition on the square to a transition on the plane, losing nothing.**

The manuscript states its transition conditions on `[0,1]²`, where states and
sanctions are meaningful; the formalisation's `Params` carries `F : ℝ → ℝ → ℝ`
with monotonicity and the diagonal identity on all of `ℝ`, because a global
order hypothesis is easier to carry through the order arguments. The paper
records the gap and says every witness satisfies the stronger form. That is
true and it is not the right justification: the right one is that **no
cube-defined economy is lost**. This file proves it for the transition
(doc 54 §5, Rung 5).

Given `F₀` continuous and coordinatewise nondecreasing on the square with
`F₀(t,t) = t` there, define

  `F̂(x, s) = F₀(clip x, clip s) + min(0, min(x, s)) + max(0, max(x, s) − 1)`.

Then `F̂` agrees with `F₀` on the square, is continuous and coordinatewise
nondecreasing on all of `ℝ`, and satisfies `F̂(t, t) = t` for every real `t`.
Every chord condition stated on the square is inherited verbatim, since `F̂`
*is* `F₀` there.

The naive extension `F₀(clip x, clip s)` alone fails: its diagonal is `clip t`,
not `t`, outside the square. The two correction terms restore it — the first
is active only when both arguments are negative, the second only when one
exceeds one — and each is monotone and continuous, so nothing else is
disturbed.

Nothing here mentions `Params` (Rule 19); the bridge to a `Params` constructor
is a Theory-side task.
-/
import Sanctions.Domain.UnitIntervalProjection

namespace Sanctions
namespace TransitionExtension

open Set

variable (F₀ : ℝ → ℝ → ℝ)

/-- The global extension of a square-defined transition. -/
def extend (x s : ℝ) : ℝ :=
  F₀ (clipS x) (clipS s) + min 0 (min x s) + max 0 (max x s - 1)

theorem clipS_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clipS t = t := by
  simp only [clipS]
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- On the square the extension is the original. -/
theorem extend_eq_on_square {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    extend F₀ x s = F₀ x s := by
  unfold extend
  rw [clipS_of_mem hx, clipS_of_mem hs]
  have h1 : min 0 (min x s) = 0 := min_eq_left (le_min hx.1 hs.1)
  have h2 : max 0 (max x s - 1) = 0 := max_eq_left (by linarith [max_le hx.2 hs.2])
  rw [h1, h2]; ring

/-- The extension maps the square into itself whenever the original does. -/
theorem extend_mem (hmem : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F₀ x s ∈ Icc (0 : ℝ) 1)
    {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    extend F₀ x s ∈ Icc (0 : ℝ) 1 := by
  rw [extend_eq_on_square F₀ hx hs]; exact hmem x hx s hs

/-- **Global continuity** from continuity on the square. -/
theorem extend_continuous
    (hF₀ : ContinuousOn (fun p : ℝ × ℝ => F₀ p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    Continuous (fun p : ℝ × ℝ => extend F₀ p.1 p.2) := by
  unfold extend
  have hc : Continuous (fun p : ℝ × ℝ => (clipS p.1, clipS p.2)) :=
    (clipS_continuous.comp continuous_fst).prodMk (clipS_continuous.comp continuous_snd)
  have h1 : Continuous (fun p : ℝ × ℝ => F₀ (clipS p.1) (clipS p.2)) :=
    hF₀.comp_continuous hc (fun p => ⟨clipS_mem p.1, clipS_mem p.2⟩)
  have h2 : Continuous (fun p : ℝ × ℝ => min 0 (min p.1 p.2)) := by fun_prop
  have h3 : Continuous (fun p : ℝ × ℝ => max 0 (max p.1 p.2 - 1)) := by fun_prop
  exact (h1.add h2).add h3

/-- **Global monotonicity in the state** from monotonicity on the square. -/
theorem extend_mono_x
    (hF₀ : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun x => F₀ x s) (Icc (0 : ℝ) 1)) (s : ℝ) :
    Monotone (fun x => extend F₀ x s) := by
  intro x₁ x₂ h
  simp only [extend]
  have h1 : F₀ (clipS x₁) (clipS s) ≤ F₀ (clipS x₂) (clipS s) :=
    hF₀ _ (clipS_mem s) (clipS_mem x₁) (clipS_mem x₂) (clipS_mono h)
  have h2 : min 0 (min x₁ s) ≤ min 0 (min x₂ s) := min_le_min le_rfl (min_le_min h le_rfl)
  have h3 : max 0 (max x₁ s - 1) ≤ max 0 (max x₂ s - 1) :=
    max_le_max le_rfl (by linarith [max_le_max h (le_refl s)])
  linarith

/-- **Global monotonicity in the sanction** from monotonicity on the square. -/
theorem extend_mono_s
    (hF₀ : ∀ x ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F₀ x s) (Icc (0 : ℝ) 1)) (x : ℝ) :
    Monotone (fun s => extend F₀ x s) := by
  intro s₁ s₂ h
  simp only [extend]
  have h1 : F₀ (clipS x) (clipS s₁) ≤ F₀ (clipS x) (clipS s₂) :=
    hF₀ _ (clipS_mem x) (clipS_mem s₁) (clipS_mem s₂) (clipS_mono h)
  have h2 : min 0 (min x s₁) ≤ min 0 (min x s₂) := min_le_min le_rfl (min_le_min le_rfl h)
  have h3 : max 0 (max x s₁ - 1) ≤ max 0 (max x s₂ - 1) :=
    max_le_max le_rfl (by linarith [max_le_max (le_refl x) h])
  linarith

/-- **The global diagonal identity** from the diagonal identity on the square:
the correction terms restore `t` outside `[0,1]`. -/
theorem extend_diag (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, F₀ t t = t) (t : ℝ) :
    extend F₀ t t = t := by
  unfold extend
  rw [hdiag _ (clipS_mem t), min_self, max_self]
  simp only [clipS]
  rcases le_or_gt t 0 with h | h
  · rw [min_eq_right (by linarith : t ≤ 1), max_eq_left h, min_eq_right h,
      max_eq_left (by linarith : t - 1 ≤ 0)]
    ring
  · rcases le_or_gt t 1 with h1 | h1
    · rw [min_eq_right h1, max_eq_right h.le, min_eq_left h.le,
        max_eq_left (by linarith : t - 1 ≤ 0)]
      ring
    · rw [min_eq_left h1.le, max_eq_right zero_le_one, min_eq_left h.le,
        max_eq_right (by linarith : (0 : ℝ) ≤ t - 1)]
      ring

end TransitionExtension
end Sanctions
