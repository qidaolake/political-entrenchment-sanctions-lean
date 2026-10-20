/-
Sanctions/Examples/Counterexamples/TransitionChordScoping.lean

**ROLE: FAILURE OF CONVERSE (scope).**

The chord predicates in `Foundations/TransitionChords.lean` are quantified over
the feasible square rather than over all of the plane. That restriction looks
like fussiness until one asks what the unrestricted version would claim. This
file answers: it is refuted by any transition that clips its sanction argument,
which is every transition in this development.

Rule 9: the refutation is definitive about the global form and says nothing
about how much room there is between the feasible square and the largest set on
which a given transition does satisfy a chord.

Relocated 2026-08-27 from `Foundations/TransitionChords.lean`, whose predicates
and general consequences remain there. The statement is byte-identical and the
namespace is unchanged, so the fully-qualified name is preserved.
-/

import Sanctions.Foundations.TransitionChords

namespace Sanctions.TransitionChords

open Set

/-! ## 3. The scoping fence

The predicates are deliberately scoped to the feasible square. This is
not a stylistic choice: the unrestricted form is refuted by any
transition that clips its arguments, which is every transition in this
development. -/

/-- **Global scoping is unavailable.** For a transition that clips its
sanction argument — so that `F x s` is constant in `s` above `1` — no
positive lower chord can hold on all of `ℝ`. Stated for a clipped law
directly, so it applies to every witness in the tree. -/
theorem sanctionLowerChord_global_fails
    {F : ℝ → ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hclip : ∀ s, 2 ≤ s → F 0 s = F 0 2) :
    ¬ (∀ x s₁ s₂ : ℝ, s₁ ≤ s₂ → d * (s₂ - s₁) ≤ F x s₂ - F x s₁) := by
  intro h
  have h23 := h 0 2 3 (by norm_num)
  rw [hclip 3 (by norm_num), hclip 2 (le_refl 2)] at h23
  simp only [sub_self] at h23
  linarith

end Sanctions.TransitionChords
