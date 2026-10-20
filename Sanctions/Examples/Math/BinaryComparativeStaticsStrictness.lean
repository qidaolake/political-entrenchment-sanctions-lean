/-
Sanctions/Examples/Math/BinaryComparativeStaticsStrictness.lean

**ROLE: FAILURE OF CONVERSE.**

`Foundations/BinaryComparativeStatics.lean` proves the cardinal-to-ordinal
arrow: a strictly falling gap `f - g` implies the strict single-crossing lower
relation (`strictSCLowerOn_of_sub_strictAntiOn`). This file exhibits the pair
that stops the arrow reversing, so the two conditions are known to be *ordered*
rather than equivalent.

Rule 9: the witness refutes a universal and licenses nothing else. It says
nothing about which condition any particular economy satisfies, and nothing
about how much stronger the cardinal route is anywhere else.

Relocated 2026-08-27 from `Foundations/BinaryComparativeStatics.lean`, whose
general theorems remain there. Statements are byte-identical to the originals
and the namespace is unchanged, so every fully-qualified name is preserved.
-/

import Sanctions.Foundations.BinaryComparativeStatics

namespace Sanctions
namespace BinaryComparativeStatics

open Set

/-! ### The cardinal condition is *strictly* stronger

`strictSCLowerOn_of_sub_strictAntiOn` sends a strictly falling gap to the
ordinal relation. The converse fails, and the reason is structural rather than
accidental: the ordinal relation is invariant under an arbitrary strictly
increasing transformation of either objective, while a statement about the
*difference* `f - g` is not. So the two conditions are ordered, not
incomparable, and any prose that calls them incomparable is wrong in one
direction.

The witness below is the cheapest one: on `[0,1]`, take `f a = a ^ 3` and
`g a = a`. The relation holds for free because `g` is strictly increasing, so
its conclusion never has to be earned; the gap `a ^ 3 - a` nevertheless *rises*
from `9/10` to `1`, because it is pinned to `0` at both endpoints. -/

/-- **The ordinal relation holds between `a ^ 3` and `a` on `[0,1]`.**
Trivially: the dominated objective is strictly increasing, so the implication's
conclusion holds at every ordered pair regardless of its hypothesis. -/
theorem strictSCLowerOn_cube_id :
    StrictSCLowerOn (fun a : ℝ => a ^ 3) (fun a : ℝ => a) (Icc (0 : ℝ) 1) :=
  fun _ _ _ _ hlt _ => hlt

/-- **But their gap is not strictly decreasing there.**
At `a = 9/10` the gap is `-171/1000`; at `a = 1` it is `0`. -/
theorem not_strictAntiOn_cube_sub_id :
    ¬ StrictAntiOn (fun a : ℝ => a ^ 3 - a) (Icc (0 : ℝ) 1) := by
  intro h
  have := h (by constructor <;> norm_num : (9 / 10 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num)
  norm_num at this

/-- **So the cardinal route is strictly stronger than the ordinal one.**

Packaged as the existential it is: there is a pair of objectives standing in the
strict single-crossing relation whose gap is not strictly decreasing. Hence
`strictSCLowerOn_of_sub_strictAntiOn` cannot be upgraded to an equivalence, and
a model that delivers the ordinal relation need not deliver the difference
condition that is usually used to establish it.

Rule 9: this refutes a universal and licenses nothing else. It says nothing
about which of the two conditions any particular economy satisfies. -/
theorem exists_strictSCLowerOn_without_gap_strictAnti :
    ∃ f g : ℝ → ℝ,
      StrictSCLowerOn f g (Icc (0 : ℝ) 1)
        ∧ ¬ StrictAntiOn (fun a => f a - g a) (Icc (0 : ℝ) 1) :=
  ⟨_, _, strictSCLowerOn_cube_id, not_strictAntiOn_cube_sub_id⟩

end BinaryComparativeStatics
end Sanctions
