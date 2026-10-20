/-
Sanctions/Foundations/SelfSustainingSet.lean

**Self-sustaining sets of a rule, and what their infimum does and does not say.**

For a rule `R : ℝ → ℝ` on a feasible region `A`, the *self-sustaining set* is

    H(A, R) = {x ∈ A | x ≤ R x}

— the points the rule does not pull down. In the sanctions reading `R` is a
realized sanction rule and `x` a political state, so `x ≤ R x` says the sanction
the rule returns at `x` is at least `x` itself. Under the two transition
primitives the project already carries — `F` non-decreasing in the sanction and
`F x x = x` — that is a **sufficient** condition for the state not to fall in one
step, and, on those two facts alone, not a characterisation of it. If the rule
answers below the state then `F x (R x) ≤ F x x = x`, and the weak inequality
permits equality: a state can fail to fall while the rule sustaining it sits
strictly beneath it. The converse needs a strict separation, and the project
already carries one — `Params.StrictAdjustment`.
`Theory/LockIn/TwoSidedForwardLooking.lean` proves the two directions
separately: `le_ruleStepF_of_mem_selfSustainingSet` one way with no strictness,
and `le_rule_iff_le_ruleStepF_of_strictAdjustment` as the equivalence with it.
Neither needs an affine transition or any functional form.

Two positive facts are proved here, both purely order-theoretic:

* **Monotonicity.** A pointwise-larger rule has a larger self-sustaining set.
  This is the whole content of the claim that a harder Sender sustains more
  states, and it needs nothing beyond the pointwise comparison — no continuity,
  no monotonicity of either rule, no invariance.
* **Infimum ordering.** The larger set therefore has the smaller infimum, so a
  pointwise-larger rule sustains states from at least as low a starting point.

One fact is recorded **negatively**, and it is the reason this file is careful
about its own conclusion. The infimum does *not* characterize the set:
`Examples/SelfSustainingInfNotCharacterizing.lean` exhibits
a constant rule whose self-sustaining set is the **closed** interval `[0, 1/2]`
— infimum `0`, and every feasible state above `1/2` unsustained.
Calling that infimum "the basin boundary" needs
an upward-closure, single-crossing, or unique-root condition that this file
neither assumes nor supplies. Without one, the **inclusion** is the result and
the infimum ordering is a corollary; neither is a description of the geography.

Rule 19: no field of `AbstractGame.Params` appears here, and nothing below
mentions sanctions. The wiring to the two equilibrium rules lives in `Theory/`.
-/

import Sanctions.Foundations.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace Sanctions

open Set

/-- **The self-sustaining set of a rule `R` on a region `A`.** The points of `A`
the rule answers with at least their own level. -/
def selfSustainingSet (A : Set ℝ) (R : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ A ∧ x ≤ R x}

@[simp] theorem mem_selfSustainingSet {A : Set ℝ} {R : ℝ → ℝ} {x : ℝ} :
    x ∈ selfSustainingSet A R ↔ x ∈ A ∧ x ≤ R x := Iff.rfl

/-- A self-sustaining set is carved out of the region it is taken over. -/
theorem selfSustainingSet_subset (A : Set ℝ) (R : ℝ → ℝ) :
    selfSustainingSet A R ⊆ A := fun _ hx => hx.1

/-- **A pointwise-larger rule sustains at least as much.**

The only hypothesis is the pointwise comparison on `A`. Neither rule need be
monotone, continuous, or feasibility-preserving: if `R₁` already fails to pull
`x` down, a rule that answers at least as high at `x` cannot pull it down
either. -/
theorem selfSustainingSet_mono_of_rule_le
    {A : Set ℝ} {R₁ R₂ : ℝ → ℝ} (hle : ∀ x ∈ A, R₁ x ≤ R₂ x) :
    selfSustainingSet A R₁ ⊆ selfSustainingSet A R₂ :=
  fun _ hx => ⟨hx.1, le_trans hx.2 (hle _ hx.1)⟩

/-- Nonemptiness transfers upward along the inclusion: if the weaker rule
sustains something, so does the stronger one. -/
theorem selfSustainingSet_nonempty_of_rule_le
    {A : Set ℝ} {R₁ R₂ : ℝ → ℝ} (hle : ∀ x ∈ A, R₁ x ≤ R₂ x)
    (hne : (selfSustainingSet A R₁).Nonempty) :
    (selfSustainingSet A R₂).Nonempty :=
  hne.mono (selfSustainingSet_mono_of_rule_le hle)

/-- A self-sustaining set inherits a lower bound from its region. -/
theorem selfSustainingSet_bddBelow
    {A : Set ℝ} (R : ℝ → ℝ) (hA : BddBelow A) :
    BddBelow (selfSustainingSet A R) := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨y, fun _ hz => hy hz.1⟩

/-- **A pointwise-larger rule sustains from at least as low a point.**

The infimum ordering that the inclusion gives. Stated with the *weaker* rule's
set required nonempty, since that is the side the infimum is taken of on the
right; the stronger rule's set is then nonempty automatically.

What this does *not* say: that either infimum is attained, that either set is an
interval, or that every point above an infimum belongs to its set. See the file
header, and the refutation it points to. -/
theorem sInf_selfSustainingSet_le_of_rule_le
    {A : Set ℝ} {R₁ R₂ : ℝ → ℝ}
    (hA : BddBelow A)
    (hle : ∀ x ∈ A, R₁ x ≤ R₂ x)
    (hne : (selfSustainingSet A R₁).Nonempty) :
    sInf (selfSustainingSet A R₂) ≤ sInf (selfSustainingSet A R₁) :=
  csInf_le_csInf (selfSustainingSet_bddBelow R₂ hA) hne
    (selfSustainingSet_mono_of_rule_le hle)

end Sanctions
