/-
Sanctions/Examples/SelfSustainingInfNotCharacterizing.lean

**The infimum of a self-sustaining set is not a basin boundary (Rule-11
refutation).**

`Foundations/SelfSustainingSet.lean` proves two things about

    H(A, R) = {x ∈ A | x ≤ R x}:

a pointwise-larger rule has a larger `H`, and therefore a smaller `inf H`. The
tempting next sentence — *so `inf H` is the lowest state the rule sustains, and
everything above it is sustained* — is the one this file blocks.

It is tempting because it is how the pivot is read economically: a single
threshold, below which entrenchment decays and above which it holds. That
reading is a claim of **upward closure**, and upward closure is an extra
hypothesis, not a consequence. The inclusion result never touches it.

## The witness

The rule is as well-behaved as a rule can be: the constant

    R(x) = 1/2   on   A = [0, 1].

It is monotone, continuous, and maps `[0,1]` into itself, so it satisfies every
regularity condition the path-comparison theorems impose on the upper rule. Its
self-sustaining set is

    H = [0, 1/2],

with `inf H = 0`. And `3/4 ∈ A` sits above the infimum while failing to be
sustained: the rule answers `1/2 < 3/4`, so the state falls.

Nothing pathological is doing the work. The set is closed, the region is
compact, the infimum is attained, and the rule has no discontinuity or tie. The
infimum simply is not the boundary of anything, because `H` is bounded *above*
by the rule's own ceiling rather than opening upward.

## What this settles

The pivot ordering
`sInf_selfSustainingSet_le_of_rule_le` remains true and remains the correct
conclusion. What it may not be promoted to is *"the forward-looking regime's
basin is `[x̄, 1]` for a lower `x̄`"*. That sentence needs an upward-closure,
single-crossing, or unique-root condition supplied and discharged separately.
Until one is, the honest statement is the set inclusion.

Rule 19 places this here rather than in `Foundations/` because it fixes a
functional form. It is the companion refutation to
`SenderSwitchSignUndetermined.lean`, which blocks a different over-reading in the
same chain.
-/

import Sanctions.Foundations.SelfSustainingSet
import Mathlib.Tactic

namespace Sanctions
namespace Examples

open Set

/-- The region: the unit interval, exactly the feasible state space. -/
def flatA : Set ℝ := Icc 0 1

/-- The rule: a constant sanction of one half. Monotone, continuous, and
feasibility-preserving — it clears every regularity condition the path
comparators require of the upper rule. -/
noncomputable def flatR : ℝ → ℝ := fun _ => 1 / 2

theorem flatR_monotone : Monotone flatR := fun _ _ _ => le_rfl

theorem flatR_continuous : Continuous flatR := continuous_const

theorem flatR_mem : ∀ x ∈ flatA, flatR x ∈ flatA := by
  intro x _
  norm_num [flatR, flatA, mem_Icc]

/-- **The self-sustaining set of the constant rule is `[0, 1/2]`.** Closed,
compact, and with its infimum attained — the witness has no pathology to hide
behind. -/
theorem flat_selfSustainingSet_eq :
    selfSustainingSet flatA flatR = Icc (0 : ℝ) (1 / 2) := by
  ext x
  simp only [mem_selfSustainingSet, flatA, flatR, mem_Icc]
  constructor
  · rintro ⟨⟨h0, _⟩, hx⟩
    exact ⟨h0, hx⟩
  · rintro ⟨h0, hx⟩
    exact ⟨⟨h0, by linarith⟩, hx⟩

/-- The lowest sustained point is in the set, so the infimum sits at or below
it. -/
theorem flat_zero_mem : (0 : ℝ) ∈ selfSustainingSet flatA flatR := by
  rw [flat_selfSustainingSet_eq]
  exact ⟨le_refl 0, by norm_num⟩

theorem flat_bddBelow : BddBelow (selfSustainingSet flatA flatR) := by
  refine selfSustainingSet_bddBelow flatR ?_
  simp only [flatA]
  exact bddBelow_Icc

theorem flat_sInf_le : sInf (selfSustainingSet flatA flatR) ≤ 3 / 4 := by
  have h : sInf (selfSustainingSet flatA flatR) ≤ 0 :=
    csInf_le flat_bddBelow flat_zero_mem
  linarith

/-- **And a feasible state strictly above the infimum is not sustained.** At
`3/4` the rule answers `1/2`, so the state falls. -/
theorem flat_three_quarters_not_mem :
    (3 / 4 : ℝ) ∉ selfSustainingSet flatA flatR := by
  rw [flat_selfSustainingSet_eq]
  intro h
  have := h.2
  norm_num at this

/-! ## The refutation -/

/-- **The infimum of a self-sustaining set does not characterize it.**

Sitting in the region and at or above the infimum is *not* sufficient for being
sustained. Every hypothesis holds at the witness and the conclusion fails, so the
universal is false — Rule 11: definitive, not inconclusive.

The consequence for the sanctions chain: pointwise rule dominance gives the set
inclusion and the infimum ordering, and stops there. Reading the infimum as a
basin boundary requires an upward-closure condition that must be assumed and
discharged on its own. -/
theorem selfSustaining_sInf_does_not_characterize :
    ¬ ∀ (A : Set ℝ) (R : ℝ → ℝ) (x : ℝ),
        x ∈ A → sInf (selfSustainingSet A R) ≤ x →
        x ∈ selfSustainingSet A R := by
  intro h
  refine flat_three_quarters_not_mem (h flatA flatR (3 / 4) ?_ flat_sInf_le)
  norm_num [flatA, mem_Icc]

/-- The positive reading of the same witness: the self-sustaining set is *not*
upward closed within its region, which is precisely the missing hypothesis. -/
theorem flat_selfSustainingSet_not_upwardClosed :
    ¬ ∀ x ∈ flatA, ∀ y ∈ flatA, x ≤ y →
        x ∈ selfSustainingSet flatA flatR → y ∈ selfSustainingSet flatA flatR := by
  intro h
  refine flat_three_quarters_not_mem (h 0 ?_ (3 / 4) ?_ (by norm_num) flat_zero_mem)
  · norm_num [flatA, mem_Icc]
  · norm_num [flatA, mem_Icc]

end Examples
end Sanctions
