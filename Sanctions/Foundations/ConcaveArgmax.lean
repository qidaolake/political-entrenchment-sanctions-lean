/-
Sanctions/Foundations/ConcaveArgmax.lean

**Uniqueness of maximisers under strict concavity.**

Abstract convex analysis over `ℝ`: no `Params`, no value functions, no game.
The project's two argmax-uniqueness conditions — `DynamicArgmaxUnique` on the
Sender side and `TargetArgmaxUnique` on the leader side — are both instances of
the single fact proved here, and `Theory/` should carry only the wiring.

## Why this file exists

`DynamicArgmaxUnique` is the most-consumed `Prop` in the development and
`TargetArgmaxUnique` is not far behind. Both docstrings name the intended route
("strict concavity or strict monotonicity of the objective"), and neither had a
parametric discharger; the first was written on 2026-08-17 directly against the
`Params`-level objective, which mixed a general fact about concave functions with
the specific shape of the Sender's dynamic payoff. This file separates them.

## Strict, not strong

Uniqueness needs only *strict* concavity. A modulus is not required, and
demanding one is not innocuous here: the project's headline row
`not_coupledLeaderStrongConcave` refutes a *modulus-2* leader strong-concavity
package on the coupled carriers, and the counterexample fires across a kink in
the Sender's lower response. Since the leader objective composes with the
follower's best response, and best-response selectors generically kink, a
modulus is exactly the wrong thing to insist on. Strict concavity is weaker, is
what uniqueness actually uses, and sidesteps that refutation — which is scoped to
a modulus, not to strictness.

Mathlib supplies `StrongConcaveOn.strictConcaveOn`, so the strong-concavity form
remains available as a corollary for callers that already have a modulus.

## What mathlib does and does not have

`Mathlib.Analysis.Convex.Function` carries a rich `StrictConcaveOn` API —
`lt_on_openSegment`, the composition rules, `subset`, `congr` — but no
argmax-uniqueness lemma. Searched before writing. `lt_on_openSegment` is the
tool: it gives `min (f x) (f y) < f z` strictly between two points, which two
maximisers cannot survive.
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Strong

namespace Sanctions
namespace ConcaveArgmax

/-- **A strictly concave function has at most one maximiser.**

If `a₁` and `a₂` both maximise `f` over `S` and `f` is strictly concave there,
they coincide. The midpoint would otherwise be strictly better than the smaller
of the two — and hence than both, since the two values are equal at a maximum.

This is the abstract content behind every argmax-uniqueness condition in the
development. -/
theorem eq_of_isMaxOn_of_strictConcaveOn
    {f : ℝ → ℝ} {S : Set ℝ}
    (hf : StrictConcaveOn ℝ S f)
    {a₁ a₂ : ℝ} (h₁ : a₁ ∈ S) (h₂ : a₂ ∈ S)
    (hm₁ : ∀ y ∈ S, f y ≤ f a₁) (hm₂ : ∀ y ∈ S, f y ≤ f a₂) :
    a₁ = a₂ := by
  by_contra hne
  -- The midpoint lies strictly between `a₁` and `a₂`.
  have hz : ((1 : ℝ) / 2) • a₁ + ((1 : ℝ) / 2) • a₂ ∈ openSegment ℝ a₁ a₂ :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hlt := hf.lt_on_openSegment h₁ h₂ hne hz
  -- and inside `S`, by convexity of the domain.
  have hzS : ((1 : ℝ) / 2) • a₁ + ((1 : ℝ) / 2) • a₂ ∈ S :=
    hf.1 h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
  exact absurd (lt_of_le_of_lt (le_min (hm₁ _ hzS) (hm₂ _ hzS)) hlt) (lt_irrefl _)

/-- **Strong-concavity corollary.** For callers who already carry a modulus.
Note that the modulus is not what uniqueness needs — see the file header on why
insisting on one is the wrong move for the leader objective. -/
theorem eq_of_isMaxOn_of_strongConcaveOn
    {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ}
    (hf : StrongConcaveOn S c f) (hc : 0 < c)
    {a₁ a₂ : ℝ} (h₁ : a₁ ∈ S) (h₂ : a₂ ∈ S)
    (hm₁ : ∀ y ∈ S, f y ≤ f a₁) (hm₂ : ∀ y ∈ S, f y ≤ f a₂) :
    a₁ = a₂ :=
  eq_of_isMaxOn_of_strictConcaveOn (hf.strictConcaveOn hc) h₁ h₂ hm₁ hm₂

end ConcaveArgmax
end Sanctions
