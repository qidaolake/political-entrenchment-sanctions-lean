/-
Sanctions/Examples/AffineInstance/TransitionChords.lean

**ROLE: FUNCTIONAL-FORM ILLUSTRATION (non-vacuity of the chord class).**

The affine law `F x s = (1 - delta) x + delta s` satisfies every predicate in
`Foundations/TransitionChords.lean`: both chords at its own adjustment rate and
with equality, the normalised corner section with `gamma = 1 - delta`, and zero
curvature. That makes it the reference member of the class and shows the class
is inhabited.

Rule 9, and Rule 22 in particular: inhabiting the class at the affine point
proves non-vacuity and **not** generality. The affine law is the one member for
which the lower and upper chords coincide, so it cannot witness that the
two-rate machinery says more than a one-rate theory would. The non-affine
witnesses do that, and they live elsewhere in `Examples/`.

Relocated 2026-08-27 from `Foundations/TransitionChords.lean`. This keeps the
general chord theory free of the one functional form it is meant to generalise.
Statements are byte-identical and the namespace is unchanged, so every
fully-qualified name is preserved.
-/

import Sanctions.Foundations.TransitionChords

namespace Sanctions.TransitionChords

open Set

/-! ## 4. Affine reference point

The affine law is the reference member: it satisfies every predicate,
with the lower and upper chords coinciding and zero curvature. Stated
here over the explicit affine formula so that `Foundations` stays free of
the game's `Params` structure (Rule 19); the `Params`-level discharge is
in `Theory/Basin/TransitionChords.lean`. -/

/-- The affine law satisfies the lower chord at its own adjustment rate,
with equality. -/
theorem affine_sanctionLowerChord (δ : ℝ) :
    SanctionLowerChord (fun x s => (1 - δ) * x + δ * s) δ := by
  intro x s₁ s₂ _ _ _ _
  simp only
  ring_nf
  linarith [le_refl ((1 - δ) * x + δ * s₂ - ((1 - δ) * x + δ * s₁))]

/-- The affine law satisfies the upper chord at the same rate. -/
theorem affine_sanctionUpperChord (δ : ℝ) :
    SanctionUpperChord (fun x s => (1 - δ) * x + δ * s) δ := by
  intro x s₁ s₂ _ _ _ _
  simp only
  ring_nf
  linarith [le_refl ((1 - δ) * x + δ * s₂ - ((1 - δ) * x + δ * s₁))]

/-- The affine law has the normalised corner section with `γ = 1 − δ`. -/
theorem affine_cornerSectionTop (δ : ℝ) :
    CornerSectionTop (fun x s => (1 - δ) * x + δ * s) (1 - δ) := by
  intro y _
  simp only
  ring

/-- The affine law is linear in the sanction, hence semiconcave with
modulus `0` — the reference point of the curvature scale. -/
theorem affine_sanctionSemiconcave (δ : ℝ) :
    SanctionSemiconcave (fun x s => (1 - δ) * x + δ * s) 0 := by
  intro x _ s₁ _ s₂ _ t _ _
  simp only
  ring_nf
  linarith [le_refl (0 : ℝ)]

theorem affine_cornerStateChord (δ : ℝ) :
    CornerStateChord (fun x s => (1 - δ) * x + δ * s) (1 - δ) (1 - δ) :=
  cornerStateChord_of_cornerSectionTop (affine_cornerSectionTop δ)

end Sanctions.TransitionChords
