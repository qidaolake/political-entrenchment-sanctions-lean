/-
Sanctions/Foundations/ArgmaxGapStability.lean

Generic branch-stability lemmas for validated local argmax constructions.

A strict objective gap outside a designated branch survives any uniform
perturbation smaller than half that gap.  Consequently every maximizer of the
perturbed objective remains on the designated branch.  If the perturbed
objective is strictly concave on that branch, its global maximizer is unique.

These are pure analysis lemmas.  They add no model field or economic
assumption; a concrete consumer must prove the center gap and perturbation
bound from its existing primitives.
-/

import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic

namespace Sanctions

open Set

/-- A strict center-objective gap outside `B` survives a uniform perturbation
smaller than half the gap.  Hence every global maximizer of the perturbed
objective on `K` lies in `B`. -/
theorem isMaxOn_mem_branch_of_uniform_perturbation
    {A : Type*} {K B : Set A} {f₀ f : A → ℝ}
    {a₀ a : A} {gap ε : ℝ}
    (ha₀ : a₀ ∈ K) (ha : a ∈ K)
    (hmax : IsMaxOn f K a)
    (hgap : ∀ z ∈ K, z ∉ B → f₀ z + gap ≤ f₀ a₀)
    (hclose : ∀ z ∈ K, |f z - f₀ z| ≤ ε)
    (hstrict : 2 * ε < gap) :
    a ∈ B := by
  by_contra haB
  have hcenter := hgap a ha haB
  have hopt : f a₀ ≤ f a := hmax ha₀
  have hclose₀ := abs_le.mp (hclose a₀ ha₀)
  have hclosea := abs_le.mp (hclose a ha)
  linarith

/-- A uniform branch gap and strict concavity on the surviving branch give a
unique global maximizer of the perturbed objective. -/
theorem isMaxOn_eq_of_uniform_gap_strictConcave
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {K B : Set E} {f₀ f : E → ℝ}
    {a₀ a b : E} {gap ε : ℝ}
    (ha₀ : a₀ ∈ K)
    (hgap : ∀ z ∈ K, z ∉ B → f₀ z + gap ≤ f₀ a₀)
    (hclose : ∀ z ∈ K, |f z - f₀ z| ≤ ε)
    (hstrict : 2 * ε < gap)
    (hsc : StrictConcaveOn ℝ (K ∩ B) f)
    (ha : a ∈ K) (hb : b ∈ K)
    (hmaxa : IsMaxOn f K a) (hmaxb : IsMaxOn f K b) :
    a = b := by
  have haB : a ∈ B :=
    isMaxOn_mem_branch_of_uniform_perturbation
      ha₀ ha hmaxa hgap hclose hstrict
  have hbB : b ∈ B :=
    isMaxOn_mem_branch_of_uniform_perturbation
      ha₀ hb hmaxb hgap hclose hstrict
  exact hsc.eq_of_isMaxOn
    (hmaxa.on_subset inter_subset_left)
    (hmaxb.on_subset inter_subset_left)
    ⟨ha, haB⟩ ⟨hb, hbB⟩

end Sanctions
