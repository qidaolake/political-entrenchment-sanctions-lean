/-
Sanctions/Foundations/SemiconcaveSup.lean

Partial maximisation of a jointly semiconcave objective over a convex,
state-independent action set: the value inherits semiconcavity, with the
**Schur-complement** modulus `σ + ρ²/q`.

Everything here is elementary convex analysis over abstract data — no
`Params`, no sanctions content, no differentiability, no interiority.
Rule 19 therefore puts it in `Foundations/`.

## Why the naive statement is false

It is tempting to say "the sup of a jointly semiconcave objective is
semiconcave with the *same* modulus." That is **wrong**, and the reason is
visible in one line. Chord-comparing the value at two states forces a
comparison of the objective at two *different* maximisers, so the joint
chord inequality is charged for the action gap `|a₁ − a₂|` as well as the
state gap. Nothing bounds the action gap by the state gap for free.

What rescues it is strict concavity in the action. The action gap then
pays for itself: the joint chord budget spends `2ρ|Δx||Δa| − q|Δa|²` on
the action, and that expression is maximised over `|Δa|` at `ρ²|Δx|²/q`.
So the value is semiconcave with modulus `σ + ρ²/q` — the Schur complement
of the joint form `[[σ, ρ], [ρ, −q]]`, not `σ`.

In the quadratic model `Φ(x,a) = (σ/2)x² + ρ·x·a − (q/2)a²` this is exact:
`maxₐ Φ(x,a) = (σ/2 + ρ²/(2q))·x²`.

## Where this is used

This is the partial-maximisation step of the curvature-pinned carrier: a
Bellman image is a sup over the action of stage payoff plus discounted
continuation, so a curvature bound on the continuation propagates to a
curvature bound on the image through exactly this lemma, generating the
`q − β·δ²·Σ` denominator that the project's Riccati recursion carries.

`Sanctions/Examples/DualBasinSelectionWitness.lean` already exhibits the
resulting invariance concretely (its `dbCarrierS` pins a sup-norm bound, a
Lipschitz constant, and `SemiconcaveOn V 40`, with the Bellman image
proved `137/4`-semiconcave).

## Scope, stated honestly

* `q > 0` is **required**, not cosmetic: at `q = 0` with `ρ ≠ 0` the sup of
  a family affine in the state is convex, and no finite modulus survives.
  `sup_semiconcave_of_joint` fails without it.
* The action set must be **convex** and **state-independent**. Convexity
  supplies the midpoint action; state-independence is what makes that
  midpoint feasible at the midpoint state.
* No differentiability anywhere — every hypothesis is a chord inequality.

## Where the evidence lives

Two facts about the theorem below are settled by construction rather than by
its statement: the Schur modulus `sigma + rho^2/q` is attained, and the
action-concavity hypothesis `q > 0` is load-bearing. Both witnesses are in
`Examples/Sharpness/SemiconcaveSup.lean`, moved there 2026-08-27.
-/

import Sanctions.Foundations.Basic
import Mathlib.Analysis.Convex.Basic

noncomputable section
open Set

namespace Sanctions.Semiconcave

/-- **Chord-form joint semiconcavity of a two-variable objective.**

`Φ` is jointly semiconcave on `X × A` with state modulus `σ`, cross modulus
`ρ` and action concavity `q` when every chord defect is bounded by the
quadratic form `σ·Δx² + 2ρ·|Δx|·|Δa| − q·Δa²`.

In English: moving along a segment in the state–action plane, the objective
can bulge upward at rate at most `σ` in the state, gains at most `ρ` per
unit of state–action interaction, and is *strictly concave* in the action at
rate at least `q`. Taking `ρ = 0` and `q = 0` recovers ordinary
`σ`-semiconcavity in the state alone, uniformly in the action. -/
def JointSemiconcaveOn (Φ : ℝ → ℝ → ℝ) (X A : Set ℝ) (σ ρ q : ℝ) : Prop :=
  ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    t * Φ x₁ a₁ + (1 - t) * Φ x₂ a₂
        - Φ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂)
      ≤ t * (1 - t) / 2
          * (σ * (x₁ - x₂) ^ 2 + 2 * ρ * |x₁ - x₂| * |a₁ - a₂|
              - q * (a₁ - a₂) ^ 2)

/-- **Chord-form semiconcavity of a one-variable value.** `v` bulges upward
at rate at most `c`: equivalently `v(x) − (c/2)x²` is concave on `X`. -/
def SemiconcaveOnSet (v : ℝ → ℝ) (X : Set ℝ) (c : ℝ) : Prop :=
  ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    t * v x₁ + (1 - t) * v x₂ - v (t * x₁ + (1 - t) * x₂)
      ≤ c / 2 * (t * (1 - t) * (x₁ - x₂) ^ 2)

/-- **Chord-form `c`-semiconvexity on a set.** The mirror of `SemiconcaveOnSet`:
`v` rises *above* its chords by at most `(c/2)·t(1−t)(x₁ − x₂)²` (a convex
function never does, and is `0`-semiconvex); equivalently `v + (c/2)·x²` is
convex. Convex kinks are permitted; concave kinks are what this forbids. Same
shape as the semiconcave predicate, so the two form one chord-form pair. -/
def SemiconvexOnSet (v : ℝ → ℝ) (X : Set ℝ) (c : ℝ) : Prop :=
  ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    v (t * x₁ + (1 - t) * x₂) - (t * v x₁ + (1 - t) * v x₂)
      ≤ c / 2 * (t * (1 - t) * (x₁ - x₂) ^ 2)

/-- A convex combination of two points of `[0,1]` lies in `[0,1]`. -/
theorem mem_Icc_convexComb {y₁ y₂ t : ℝ} (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1)
    (hy₂ : y₂ ∈ Set.Icc (0 : ℝ) 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * y₁ + (1 - t) * y₂ ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := mul_nonneg ht0 hy₁.1
  have h2 := mul_nonneg (sub_nonneg.2 ht1) hy₂.1
  have h3 := mul_le_mul_of_nonneg_left hy₁.2 ht0
  have h4 := mul_le_mul_of_nonneg_left hy₂.2 (sub_nonneg.2 ht1)
  constructor <;> linarith

/-- **The action gap pays for itself.** For `q > 0`, the joint chord budget
spent on the action, `2ρ·u·w − q·w²`, never exceeds `ρ²·u²/q`.

This is the whole content of the Schur complement, in one inequality: the
worst the action gap `w` can do is `ρ²/q` per unit of squared state gap. -/
theorem cross_le_schur {ρ q u w : ℝ} (hq : 0 < q) :
    2 * ρ * u * w - q * w ^ 2 ≤ ρ ^ 2 * u ^ 2 / q := by
  rw [le_div_iff₀ hq]
  nlinarith [sq_nonneg (q * w - ρ * u)]

/-- **Partial maximisation preserves semiconcavity, with the Schur modulus.**

Let the action set `A` be convex, the state set `X` convex, and let `Φ` be
jointly semiconcave on `X × A` with state modulus `σ`, cross modulus `ρ ≥ 0`
and *strict* action concavity `q > 0`. Let `v x` be the greatest value of
`Φ x ·` over `A`. Then `v` is semiconcave on `X` with modulus `σ + ρ²/q`.

The modulus is the Schur complement of the joint form, **not** `σ`: the
maximisers at two different states need not coincide, and the action gap
between them is charged to the chord. Strict concavity in the action is what
bounds that charge; without it (`q = 0`, `ρ ≠ 0`) the conclusion is false.

Nothing here is differentiable, and `A` need not be compact — attainment is
supplied by the `IsGreatest` hypothesis, which in the intended application
comes from continuity on a compact action interval.

No sign is required of the cross modulus `ρ`: the Schur bound goes through a
completed square, so a rally term of either orientation is covered. -/
theorem sup_semiconcave_of_joint
    {Φ : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {X A : Set ℝ} {σ ρ q : ℝ}
    (hX : Convex ℝ X) (hA : Convex ℝ A) (hq : 0 < q)
    (hΦ : JointSemiconcaveOn Φ X A σ ρ q)
    (hv : ∀ x ∈ X, IsGreatest (Φ x '' A) (v x)) :
    SemiconcaveOnSet v X (σ + ρ ^ 2 / q) := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  -- The midpoint state is feasible, so the value is defined there.
  have hm : t * x₁ + (1 - t) * x₂ ∈ X := hX hx₁ hx₂ ht0 (by linarith) (by ring)
  -- Maximisers at the two endpoint states.
  obtain ⟨⟨a₁, ha₁, hΦ₁⟩, -⟩ := hv x₁ hx₁
  obtain ⟨⟨a₂, ha₂, hΦ₂⟩, -⟩ := hv x₂ hx₂
  -- The midpoint action is feasible *at the midpoint state*, because `A`
  -- is convex and does not depend on the state. This is the step that
  -- state-dependent feasibility would break.
  have hma : t * a₁ + (1 - t) * a₂ ∈ A := hA ha₁ ha₂ ht0 (by linarith) (by ring)
  -- The value at the midpoint dominates the objective at the midpoint action.
  have hdom : Φ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂)
      ≤ v (t * x₁ + (1 - t) * x₂) :=
    (hv _ hm).2 ⟨_, hma, rfl⟩
  -- The joint chord inequality at the two maximisers.
  have hchord := hΦ x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  rw [hΦ₁, hΦ₂] at hchord
  -- Spend the action budget: `2ρ|Δx||Δa| − q·Δa² ≤ ρ²Δx²/q`.
  have hgap : 2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2
      ≤ ρ ^ 2 * |x₁ - x₂| ^ 2 / q := by
    have := cross_le_schur (ρ := ρ) (q := q) (u := |x₁ - x₂|) (w := |a₁ - a₂|) hq
    calc 2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2
        = 2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * |a₁ - a₂| ^ 2 := by
          rw [sq_abs]
      _ ≤ ρ ^ 2 * |x₁ - x₂| ^ 2 / q := this
  have habs : |x₁ - x₂| ^ 2 = (x₁ - x₂) ^ 2 := sq_abs _
  rw [habs] at hgap
  -- Split the chord budget into its state part and its action part, so the
  -- action part can be bounded by the Schur term with a nonnegative weight.
  have hsplit : t * (1 - t) / 2
        * (σ * (x₁ - x₂) ^ 2 + 2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2)
      = t * (1 - t) / 2 * (σ * (x₁ - x₂) ^ 2)
        + t * (1 - t) / 2
            * (2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2) := by ring
  rw [hsplit] at hchord
  have hmul : t * (1 - t) / 2
        * (2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2)
      ≤ t * (1 - t) / 2 * (ρ ^ 2 * (x₁ - x₂) ^ 2 / q) :=
    mul_le_mul_of_nonneg_left hgap
      (by nlinarith [mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 1 - t)])
  have hgoal : (σ + ρ ^ 2 / q) / 2 * (t * (1 - t) * (x₁ - x₂) ^ 2)
      = t * (1 - t) / 2 * (σ * (x₁ - x₂) ^ 2)
        + t * (1 - t) / 2 * (ρ ^ 2 * (x₁ - x₂) ^ 2 / q) := by ring
  rw [hgoal]
  linarith [hchord, hdom, hmul]

/-- **Specialisation to the project's geometry**: state and action both the
unit interval. The unit interval is convex, so the hypotheses reduce to the
joint chord bound plus attainment. -/
theorem sup_semiconcave_of_joint_unitInterval
    {Φ : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {σ ρ q : ℝ} (hq : 0 < q)
    (hΦ : JointSemiconcaveOn Φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) σ ρ q)
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, IsGreatest (Φ x '' Icc (0 : ℝ) 1) (v x)) :
    SemiconcaveOnSet v (Icc (0 : ℝ) 1) (σ + ρ ^ 2 / q) :=
  sup_semiconcave_of_joint (convex_Icc _ _) (convex_Icc _ _) hq hΦ hv

end Sanctions.Semiconcave

end
