/-
Sanctions/Examples/AffineInstance/SemiconcaveRiccati.lean

**ROLE: FUNCTIONAL-FORM ILLUSTRATION (the degenerate member of the recursion).**

Two facts about the affine case, kept out of the recursion they illustrate.

An affine section sits in the two-sided state chord band with its two rates
equal, which is the `glo = ghi` degeneracy the band was introduced to escape;
and the Riccati constant collapses at zero transition curvature to
`psi / (1 - beta * ghi^2)`, so the extra term `beta * K * M_state` in the
general formula is visibly the price of curvature and nothing else.

Rule 9, and Rule 22: both are non-vacuity at the affine point. Neither shows the
band says more than a one-rate theory would --- the affine law is precisely the
member for which it does not. The non-affine inhabitants elsewhere in
`Examples/` carry that.

Relocated 2026-08-27 from `Foundations/SemiconcaveRiccati.lean`, whose symbolic
recursion, fixed-point identity and least-invariant-modulus results remain
there. Statements are byte-identical and the namespace is unchanged, so every
fully-qualified name is preserved.
-/
import Sanctions.Foundations.SemiconcaveRiccati

noncomputable section
open Set

namespace Sanctions.Semiconcave

/-- An affine section sits in the band at both ends, with `glo = ghi`. -/
theorem affine_stateChordBand (γ c : ℝ) :
    StateChordBand (fun y => γ * y + c) γ γ := by
  intro y₁ _ y₂ _ _
  constructor <;> · simp only; ring_nf; linarith [le_refl (γ * y₂ - γ * y₁)]

/-- **The affine route as the degenerate case.** With an affine successor
section (`M_state = 0`) the numerator collapses to `ψ` and the threshold to
`ψ/(1 − β·ghi²)`.  Recorded so the generalisation is visibly a widening:
the extra term `β·K·M_state` is exactly the price of curvature in the
transition. -/
theorem bellmanSemiconcaveConstant_affine (β ghi ψ K : ℝ) :
    bellmanSemiconcaveConstant β ghi ψ K 0 = ψ / (1 - β * ghi ^ 2) := by
  simp only [bellmanSemiconcaveConstant, mul_zero, add_zero]

end Sanctions.Semiconcave

end
