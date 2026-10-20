/-
Sanctions/Foundations/PatienceDecomposition.lean

**Discount-factor comparative statics for stationary Bellman equations.**

General dynamic-programming algebra on an abstract state type. Nothing here
mentions sanctions, a transition law, an equilibrium, a payoff family, or a
parameter value (Rule 19).

## What this is

Fix a stage payoff `u`, a successor map `z`, and let `V₁`, `V₂` solve the
stationary Bellman equation along `z` at two discount factors `β₁`, `β₂`:

  `Vᵢ x = u x + βᵢ · Vᵢ (z x)`.

Subtracting the two equations splits the value difference into two economically
distinct pieces:

  `V₂ x − V₁ x = (β₂ − β₁) · V₂ (z x)      -- DIRECT: the same continuation,
                                            --   valued at the new patience
              + β₁ · (V₂ (z x) − V₁ (z x))  -- FEEDBACK: the continuation itself
                                            --   has moved`

That is `difference_decomposition`, and it is the finite-difference form of the
full-adjustment comparative static: the total response to a patience change is
the direct revaluation plus the propagated change in the continuation value. The
reference for the *direction* of a discount-factor change as a shock is Acemoglu
and Jensen (2015), Lemma 2 — an increase in the discount factor is a positive
shock when the payoff is increasing in the state and the constraint is
expansive (`PaperRefer/MathTheory/RobustComparativeStatics-AcemogluJensen-2015.md`;
the 2013 aggregate-comparative-statics paper, cited here through round AH, does
not contain this lemma; re-anchored round AI, 2026-09-22). The identity itself
is elementary and needs no fixed-point theory.

## What it costs, which is nothing

The three hypotheses are the two Bellman equations and, where a limit is taken,
that `z` fixes the state in question. No contraction, no monotonicity, no
continuity, no boundedness, and **no functional form for `z`** — so a caller
carrying a general transition keeps it. The state type is arbitrary, which is
what lets the project instantiate at value functions living on a subtype rather
than on `ℝ`.

## Absorbing states

Where `z` fixes `x` the decomposition collapses. `amplification_at_fixedPoint`
gives `(1 − β₁)·(V₂ x − V₁ x) = (β₂ − β₁)·V₂ x`: the total response is the direct
response amplified by the patience resolvent `1/(1 − β₁)`. `value_at_fixedPoint`
gives the capitalised flow `V x = u x / (1 − β)`, and
`strict_at_fixedPoint_iff` settles the sign — more patience raises the value at an
absorbing state **exactly** when the flow there is positive. The `iff` matters:
at a state whose stage payoff is negative, patience makes the value *worse*, and
nothing about the dynamics rescues that.

## Scope

`SolvesAlong` is consumed as a hypothesis, not constructed here (Rule 15): every
statement below is conditional on being handed two solutions. That is the honest
shape for an algebraic identity — existence of the value functions is a separate
question, answered at the callers by the project's fixed-point machinery. Nothing
in this file asserts that a solution exists.

`decomposition_needs_common_stage_payoff` records that the shared `u` is
load-bearing: two value functions each solving *their own* Bellman equation do
not decompose this way.
-/

import Sanctions.Foundations.Basic

namespace Sanctions
namespace PatienceDecomposition

variable {X : Type*}

/-- **`V` solves the stationary Bellman equation along `z` at discount `β`.**

Written directly over the data — the equation `V x = u x + β · V (z x)` at every
state — rather than as an opaque named property (Rule 14), so an instance cannot
satisfy it while saying nothing about `V`. -/
def SolvesAlong (u : X → ℝ) (z : X → X) (β : ℝ) (V : X → ℝ) : Prop :=
  ∀ x, V x = u x + β * V (z x)

/-- **The value difference splits into a direct and a feedback term.**

For two solutions at the *same* stage payoff and the *same* successor map,

  `V₂ x − V₁ x = (β₂ − β₁)·V₂ (z x) + β₁·(V₂ (z x) − V₁ (z x))`.

The first term revalues an unchanged continuation at the new patience; the second
carries the change in the continuation itself. Subtraction of the two Bellman
equations and nothing else. -/
theorem difference_decomposition {u : X → ℝ} {z : X → X} {β₁ β₂ : ℝ} {V₁ V₂ : X → ℝ}
    (h₁ : SolvesAlong u z β₁ V₁) (h₂ : SolvesAlong u z β₂ V₂) (x : X) :
    V₂ x - V₁ x = (β₂ - β₁) * V₂ (z x) + β₁ * (V₂ (z x) - V₁ (z x)) := by
  rw [h₁ x, h₂ x]; ring

/-- **At an absorbing state the response is the direct response amplified.**

Where the successor map fixes `x`, the feedback term is the value difference
itself, and collecting it gives `(1 − β₁)·(V₂ x − V₁ x) = (β₂ − β₁)·V₂ x`. The
amplification factor is the patience resolvent `1/(1 − β₁)`. Stated
multiplication-only so no division hypothesis is needed. -/
theorem amplification_at_fixedPoint {u : X → ℝ} {z : X → X} {β₁ β₂ : ℝ} {V₁ V₂ : X → ℝ}
    (h₁ : SolvesAlong u z β₁ V₁) (h₂ : SolvesAlong u z β₂ V₂)
    {x : X} (hz : z x = x) :
    (1 - β₁) * (V₂ x - V₁ x) = (β₂ - β₁) * V₂ x := by
  have h := difference_decomposition h₁ h₂ x
  rw [hz] at h; linarith

/-- **The capitalised flow at an absorbing state, division-free.** -/
theorem value_mul_at_fixedPoint {u : X → ℝ} {z : X → X} {β : ℝ} {V : X → ℝ}
    (h : SolvesAlong u z β V) {x : X} (hz : z x = x) :
    (1 - β) * V x = u x := by
  have hx := h x; rw [hz] at hx; linarith

/-- **The capitalised flow at an absorbing state.** A state the successor map
fixes is worth its own stage payoff capitalised at the discount factor. -/
theorem value_at_fixedPoint {u : X → ℝ} {z : X → X} {β : ℝ} {V : X → ℝ}
    (h : SolvesAlong u z β V) {x : X} (hz : z x = x) (hβ : β ≠ 1) :
    V x = u x / (1 - β) := by
  have hne : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  rw [eq_div_iff hne, mul_comm]
  exact value_mul_at_fixedPoint h hz

/-- **More patience raises the absorbing-state value exactly when the flow there
is positive.**

An `iff`, deliberately. The economically expected direction — patience deepens
the value of a locked-in state — holds only where that state pays a positive
flow; where it pays a negative one, patience makes it strictly worse. So the sign
of the comparative static is a property of the stage payoff at the absorbing
state and of nothing else. -/
theorem strict_at_fixedPoint_iff {u : X → ℝ} {z : X → X} {β₁ β₂ : ℝ} {V₁ V₂ : X → ℝ}
    (h₁ : SolvesAlong u z β₁ V₁) (h₂ : SolvesAlong u z β₂ V₂)
    {x : X} (hz : z x = x) (hβ₁ : β₁ < 1) (hlt : β₁ < β₂) (hβ₂ : β₂ < 1) :
    V₁ x < V₂ x ↔ 0 < u x := by
  have hamp := amplification_at_fixedPoint h₁ h₂ hz
  have hV₂ := value_mul_at_fixedPoint h₂ hz
  constructor
  · intro hlt'
    have h1 : 0 < (β₂ - β₁) * V₂ x := by nlinarith
    have h2 : 0 < V₂ x := by nlinarith
    nlinarith
  · intro hu
    have h2 : 0 < V₂ x := by nlinarith
    nlinarith

/-- **The shared stage payoff is load-bearing.**

Two value functions each solving *their own* Bellman equation, at their own stage
payoffs, do not decompose this way: constant flows `0` and `1` at zero discount
give values `0` and `1`, and the claimed identity would force `1 = 0`.

Rule-11 artifact: `difference_decomposition`'s common `u` is not a convenience of
the statement. -/
theorem decomposition_needs_common_stage_payoff :
    ¬ ∀ (u₁ u₂ : ℝ → ℝ) (z : ℝ → ℝ) (β₁ β₂ : ℝ) (V₁ V₂ : ℝ → ℝ),
        SolvesAlong u₁ z β₁ V₁ → SolvesAlong u₂ z β₂ V₂ → ∀ x,
        V₂ x - V₁ x = (β₂ - β₁) * V₂ (z x) + β₁ * (V₂ (z x) - V₁ (z x)) := by
  intro h
  have hbad := h (fun _ => 0) (fun _ => 1) id 0 0 (fun _ => 0) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num) 0
  norm_num at hbad

end PatienceDecomposition
end Sanctions
