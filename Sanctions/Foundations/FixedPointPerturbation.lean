/-
Sanctions/Foundations/FixedPointPerturbation.lean

**How far apart two fixed points can be when the operators are close.**

If two Bellman operators differ a little, their value functions differ a little
— and the amplification factor is `1/(1-q)`, where `q` is the contraction
modulus. A patient economy, `q` near one, amplifies a small change in primitives
into a large change in values; an impatient one does not. That is the whole
content, and it is what any continuity-in-parameters argument rests on.

## Relation to Mathlib

`ContractingWith.edist_le_of_fixedPoint` bounds the distance from an arbitrary
point to *one* operator's fixed point. The statement wanted here compares the
fixed points of *two* operators, and is a two-line consequence — but of the
triangle inequality directly, not of that lemma, which lets it be stated with
`dist` in a bare `MetricSpace` and avoid `ℝ≥0∞` arithmetic entirely.

## Two hypotheses fewer than expected

Only **one** of the two operators has to be a contraction. The proof measures
the discrepancy at the *other* operator's fixed point and lets the contraction
absorb it, so which operator is assumed contracting decides which one's fixed
point the discrepancy is evaluated at — nothing else. Both orderings are given
below.

Nor is `0 ≤ q` needed. It was in the first draft and the unused-variable linter
rejected it: the argument uses only `q < 1`, to keep `1 - q` positive. The
nonnegativity is what makes the modulus *interpretable* as a contraction rate,
but it is not what makes the bound true, and carrying it would have overstated
what the theorem requires.
-/

import Sanctions.Domain.UnitInterval

namespace Sanctions
namespace FixedPointPerturbation

variable {α : Type*} [MetricSpace α]

/-- **Two fixed points are as far apart as the operators disagree, amplified by
`1/(1-q)`.**

`v₀` is fixed by `T₀`, `v₁` by `T₁`, and only `T₁` need be a contraction. The
discrepancy is measured at `v₀` — the fixed point of the operator that is *not*
assumed contracting.

The factor `1/(1-q)` is the economics: closeness of primitives buys closeness of
values only in proportion to impatience. As `q → 1` the bound degrades without
limit, which is why a patience-heavy calibration cannot inherit robustness from
a small perturbation argument. -/
theorem dist_fixedPoint_le
    {T₀ T₁ : α → α} {v₀ v₁ : α} {q : ℝ}
    (hq1 : q < 1)
    (hT₁ : ∀ u v, dist (T₁ u) (T₁ v) ≤ q * dist u v)
    (h₀ : T₀ v₀ = v₀) (h₁ : T₁ v₁ = v₁) :
    dist v₀ v₁ ≤ dist (T₀ v₀) (T₁ v₀) / (1 - q) := by
  have hstep : dist v₀ v₁ ≤ dist (T₀ v₀) (T₁ v₀) + q * dist v₀ v₁ := by
    calc dist v₀ v₁
        = dist (T₀ v₀) (T₁ v₁) := by rw [h₀, h₁]
      _ ≤ dist (T₀ v₀) (T₁ v₀) + dist (T₁ v₀) (T₁ v₁) := dist_triangle _ _ _
      _ ≤ dist (T₀ v₀) (T₁ v₀) + q * dist v₀ v₁ := by
          have := hT₁ v₀ v₁; linarith
  have hpos : 0 < 1 - q := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [hstep]

/-- The mirror image: assume the *first* operator contracting, and the
discrepancy is read at the second's fixed point. -/
theorem dist_fixedPoint_le'
    {T₀ T₁ : α → α} {v₀ v₁ : α} {q : ℝ}
    (hq1 : q < 1)
    (hT₀ : ∀ u v, dist (T₀ u) (T₀ v) ≤ q * dist u v)
    (h₀ : T₀ v₀ = v₀) (h₁ : T₁ v₁ = v₁) :
    dist v₀ v₁ ≤ dist (T₀ v₁) (T₁ v₁) / (1 - q) := by
  have h := dist_fixedPoint_le (T₀ := T₁) (T₁ := T₀) hq1 hT₀ h₁ h₀
  rwa [dist_comm v₁ v₀, dist_comm (T₁ v₁)] at h

/-- **Uniform closeness of the operators gives uniform closeness of the fixed
points.** The form a parameter-continuity argument consumes: a sup-norm bound on
the operator discrepancy transfers, with the same amplification. -/
theorem dist_fixedPoint_le_of_uniform
    {T₀ T₁ : α → α} {v₀ v₁ : α} {q ε : ℝ}
    (hq1 : q < 1)
    (hT₁ : ∀ u v, dist (T₁ u) (T₁ v) ≤ q * dist u v)
    (h₀ : T₀ v₀ = v₀) (h₁ : T₁ v₁ = v₁)
    (hclose : ∀ u, dist (T₀ u) (T₁ u) ≤ ε) :
    dist v₀ v₁ ≤ ε / (1 - q) := by
  have hpos : 0 < 1 - q := by linarith
  refine le_trans (dist_fixedPoint_le hq1 hT₁ h₀ h₁) ?_
  gcongr
  exact hclose v₀

/-- **Fixed points coincide when the operators do.** The degenerate case, worth
having so a caller need not special-case it. -/
theorem fixedPoint_eq_of_operators_eq
    {T₀ T₁ : α → α} {v₀ v₁ : α} {q : ℝ}
    (hq1 : q < 1)
    (hT₁ : ∀ u v, dist (T₁ u) (T₁ v) ≤ q * dist u v)
    (h₀ : T₀ v₀ = v₀) (h₁ : T₁ v₁ = v₁)
    (heq : ∀ u, T₀ u = T₁ u) :
    v₀ = v₁ := by
  have h := dist_fixedPoint_le_of_uniform (ε := 0) hq1 hT₁ h₀ h₁
    (fun u => by rw [heq u, dist_self])
  simp only [zero_div] at h
  exact dist_le_zero.mp h

end FixedPointPerturbation
end Sanctions
