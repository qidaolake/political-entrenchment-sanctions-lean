/-
Sanctions/Foundations/TiltStability.lean

**Quadratic growth is tilt stability, so tilt instability denies growth.**

Domínguez Corella and Lê, *On the growth of nonconvex functionals at strict local
minimizers*, arXiv:2409.01833, prove that at a strict local minimizer three
conditions are equivalent: quadratic growth, tilt sub-stability (every small
linear perturbation moves the minimizer only proportionally), and a Łojasiewicz
inequality. The direction this development needs is the contrapositive of the
first implication, and it is the direction that requires no strictness and no
local analysis at all — only the definition of a maximizer.

## Why it is worth stating

This tree holds four separate refutations of carrier-uniform quadratic growth:

* `not_coupledTargetQuadraticGrowthAt`,
* `not_coupledTargetQuadraticGrowthLipCarrierAt`,
* `not_coupledRedesign_optimal_selector_state_lipschitz_budget`,
* `lowDeltaStaticTarget_not_quadraticGrowth_29_div_24`.

Each is proved by exhibiting an engineered numerical configuration — a ramp of
slope `92800/3`, a tie at `5/12`, a curvature ratio `10001/10000`, a separation
of `10⁻⁸`. Those numerals are how the *witness* was found, not what the
*argument* needs. The argument needs one thing: that arbitrarily small
perturbations move the maximizer a distance bounded away from zero. Stated that
way it is symbolic, it strengthens each conclusion from "this modulus fails" to
"no modulus exists", and it explains why redesigning the carrier did not help.

## The mechanism, in one line

Growth forces `γ·|a₁ − a₀|² ≤ f a₀ − f a₁`. A perturbation of size `ε` can move
the maximizer only so far as it can pay for: optimality of `a₁` for the perturbed
problem caps the right side at `2ε`. So displacement is at most `√(2ε/γ)` — and
a displacement that does *not* shrink with `ε` leaves no room for a positive `γ`.

The square root is not an artifact of the proof; it is why sup-norm closeness of
objectives cannot by itself produce the *linear* selector bound a Perov row
needs, and why an action-chord factor is a separate hypothesis in
`ArgmaxSensitivity`. See `argmax_lipschitz_two_coordinates_of_quadraticGrowth`.

## Orientation

The source minimises and this project maximises, so the statements below are
written for `IsMaxOn` rather than cited. That is a sign flip and nothing more,
but it is the reason this file exists instead of a bibliography entry.
-/

import Sanctions.Domain.UnitInterval

namespace Sanctions
namespace TiltStability

open Set

/-- **Quadratic growth at a maximizer.** The objective falls off at least
quadratically as the action moves away from `a₀`, at rate `γ`. -/
def QuadraticGrowthAt (f : ℝ → ℝ) (A : Set ℝ) (a₀ γ : ℝ) : Prop :=
  ∀ a ∈ A, γ * (a - a₀) ^ 2 ≤ f a₀ - f a

/-- **The displacement bound.** Growth converts sup-norm closeness of two
objectives into a square-root bound on how far the maximizer can move.

`a₁` maximizes the perturbed objective `f + h`, and `h` is uniformly within `ε`.
Optimality gives `f a₀ − f a₁ ≤ h a₁ − h a₀ ≤ 2ε`, and growth reads the left
side from below. -/
theorem sq_displacement_le_of_growth
    {f h : ℝ → ℝ} {A : Set ℝ} {a₀ a₁ γ ε : ℝ}
    (hgrowth : QuadraticGrowthAt f A a₀ γ)
    (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A)
    (hbound : ∀ a ∈ A, |h a| ≤ ε)
    (hmax : IsMaxOn (fun a => f a + h a) A a₁) :
    γ * (a₁ - a₀) ^ 2 ≤ 2 * ε := by
  have hopt : f a₀ + h a₀ ≤ f a₁ + h a₁ := hmax ha₀
  have h0 := abs_le.mp (hbound a₀ ha₀)
  have h1 := abs_le.mp (hbound a₁ ha₁)
  have := hgrowth a₁ ha₁
  linarith

/-- **Tilt instability at a scale that does not shrink.**

For every perturbation budget `ε > 0` there is a perturbation within `ε` whose
maximizer sits at distance at least `d` from `a₀` — with `d` fixed, independent
of `ε`. This is the property the engineered counterexamples exhibit, freed of
their numerals. -/
def TiltUnstableAt (f : ℝ → ℝ) (A : Set ℝ) (a₀ d : ℝ) : Prop :=
  ∀ ε > 0, ∃ h : ℝ → ℝ, ∃ a₁ ∈ A,
    (∀ a ∈ A, |h a| ≤ ε) ∧ IsMaxOn (fun a => f a + h a) A a₁ ∧ d ≤ |a₁ - a₀|

/-- **Tilt instability denies every growth modulus.**

Not "the proposed modulus fails" — *no positive modulus exists*. Given a
candidate `γ`, choose the perturbation budget `ε = γd²/4`; the displacement bound
then caps `γd²` by `γd²/2`, which is impossible for `γ, d > 0`.

This is the general theorem the four in-tree numeric refutations instantiate. -/
theorem not_exists_growth_of_tiltUnstable
    {f : ℝ → ℝ} {A : Set ℝ} {a₀ d : ℝ}
    (hd : 0 < d) (ha₀ : a₀ ∈ A)
    (hunstable : TiltUnstableAt f A a₀ d) :
    ¬ ∃ γ : ℝ, 0 < γ ∧ QuadraticGrowthAt f A a₀ γ := by
  rintro ⟨γ, hγ, hgrowth⟩
  obtain ⟨h, a₁, ha₁, hbound, hmax, hfar⟩ :=
    hunstable (γ * d ^ 2 / 4) (by positivity)
  have hkey := sq_displacement_le_of_growth hgrowth ha₀ ha₁ hbound hmax
  have hsq : d ^ 2 ≤ (a₁ - a₀) ^ 2 := by
    have habs : d ^ 2 ≤ |a₁ - a₀| ^ 2 := by
      nlinarith [abs_nonneg (a₁ - a₀), hd.le, hfar]
    rwa [sq_abs] at habs
  have hmul : γ * d ^ 2 ≤ γ * (a₁ - a₀) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hγ.le
  have hpos : 0 < γ * d ^ 2 := mul_pos hγ (pow_pos hd 2)
  linarith

/-! ## Ties

The four in-tree refutations all work the same way: the Sender's response
switches affine branch, which ties two Target branch vertices, and the tie kills
growth. The two results here are why, and they are sharper than the numerals that
found them.

The first is the positive fact, and it was found by the unused-variable linter
rejecting a hypothesis in the draft of the second: a positive growth modulus at a
point is *already* a uniqueness claim about that point. One never has to assume
separately that the reference point is a maximizer — growth says so. -/

/-- **Growth at a point makes it the unique maximizer.**

`γ · (a − a₀)² ≤ f a₀ − f a` with `γ > 0` says every other feasible action is
strictly worse, quadratically so. Uniqueness is therefore not an extra
regularity assumption alongside growth; it is part of what growth asserts. -/
theorem eq_of_growth_of_isMaxOn
    {f : ℝ → ℝ} {A : Set ℝ} {a₀ b γ : ℝ}
    (hγ : 0 < γ) (hgrowth : QuadraticGrowthAt f A a₀ γ)
    (ha₀ : a₀ ∈ A) (hb : b ∈ A) (hmaxb : IsMaxOn f A b) :
    b = a₀ := by
  by_contra hne
  have hle := hgrowth b hb
  have hge : f a₀ ≤ f b := hmaxb ha₀
  have hpos : 0 < (b - a₀) ^ 2 := by
    have : b - a₀ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith

/-- **A tie denies growth.** Two distinct maximizers, and no positive modulus can
exist at either — nor at any other point, since growth would make its own base
point the unique maximizer and there are two.

This is the shape of every growth refutation in this tree, and it shows at once
why redesigning the carrier did not repair them: a tie is a property of the
objective's shape, not of the carrier's regularity. -/
theorem not_exists_growth_of_two_maximizers
    {f : ℝ → ℝ} {A : Set ℝ} {a₀ b : ℝ}
    (ha₀ : a₀ ∈ A) (hb : b ∈ A) (hne : a₀ ≠ b)
    (hmaxb : IsMaxOn f A b) :
    ¬ ∃ γ : ℝ, 0 < γ ∧ QuadraticGrowthAt f A a₀ γ := by
  rintro ⟨γ, hγ, hgrowth⟩
  exact hne (eq_of_growth_of_isMaxOn hγ hgrowth ha₀ hb hmaxb).symm

end TiltStability
end Sanctions
