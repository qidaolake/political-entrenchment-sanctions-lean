/-
Sanctions/Theory/Mechanism/ContinuationStakes.lean

**Both continuation values are nondegenerate — the stakes, named once.**

## Renamed 2026-09-02, and why

This file was created on 2026-09-01 as `MechanismActive.lean`, defining
`ContinuationStakesNondegenerateOn`. The 2026-09-02 JET readiness audit (§3.5) observed that the
name promised more than the definition delivers, and it was right — more right
than it said. "Mechanism-active" was already established vocabulary in this
project, in the paper's Appendix §04 and in five witness files that predate this
one, and there it means something *behavioural*: the continuation term reverses
a player's stage ranking, so that looking ahead changes the action chosen. The
definition here proves only that the discounted continuation *values* vary
across the state. That is necessary for the behavioural claim and not
sufficient: a value can vary across states the equilibrium never visits, or vary
without moving any argmax.

So the predicate is now named for what it proves — **the continuation stakes
are nondegenerate** — and the behavioural property has its own file,
`ContinuationChangesChoice.lean`, whose predicates are concluded by the strict
ordering theorems on both sides (`TargetReluctance.lean`,
`SenderInvestment.lean`) rather than merely asserted.

## What this predicate does say

There are two feasible states across which the Target's discounted continuation
value strictly rises, and two across which the Sender's does. Neither player's
forward-looking channel is silenced by a constant value function or by a zero
discount factor. That is a real non-vacuity fact — a model with constant value
functions satisfies every persistence, basin and certificate result in this
tree, because none of them tests whether the values vary — and it remains a
definition with witnesses and no universal, because nondegeneracy in *this*
sense is false at some economies.

## The discounting is load-bearing

The condition is stated on `β · ΔV`, not on `ΔV` alone. A myopic player has no
continuation channel *however* its value function looks: at `β = 0` the product
is identically zero and the existential fails. `betaT_pos` and `betaS_pos` below
turn that into a theorem — nondegenerate stakes **imply** both discount factors
are strictly positive — which is the sanity check that the definition has teeth
rather than merely a suggestive name.

## Rule 14

Written directly over the value functions, so there is nothing an instance could
set to `True`. It is a conclusion witnesses prove, never a hypothesis a theorem
consumes, so Rule 3 does not fire either.

## Rule 19

`Theory/`: it mentions `Params` and `FeedbackStackelbergEquilibriumTop`. The
discharges at particular economies live in `Examples/`.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions

open Set BoundedContinuousFunction

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Nondegenerate continuation stakes, at a bare pair of value functions.**

There are two feasible states across which the Target's discounted continuation
value strictly rises, and two across which the Sender's does. Neither player's
forward-looking channel is silenced — by a constant value function, or by a zero
discount factor.

Stated on the value functions rather than on an equilibrium **deliberately**:
the shocked layer's `ShockedFeedbackStackelbergEquilibriumTop` carries `V_T` and
`V_S` of exactly this type, so both layers discharge the same predicate rather
than needing parallel definitions. -/
def ContinuationStakesNondegenerateOn (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : Prop :=
  (∃ y₀ y₁ : ↥(Sanctions.S : Set ℝ), 0 < p.β_T * (V_T y₁ - V_T y₀))
  ∧ (∃ z₀ z₁ : ↥(Sanctions.S : Set ℝ), 0 < p.β_S * (V_S z₁ - V_S z₀))

/-- **Nondegenerate stakes at the equilibrium `E`.** -/
def ContinuationStakesNondegenerate (E : p.FeedbackStackelbergEquilibriumTop) : Prop :=
  p.ContinuationStakesNondegenerateOn E.V_T E.V_S

namespace ContinuationStakesNondegenerate

/-! `MechanismActive` is a `def` unfolding to an `And`, not a structure, so dot
notation on a hypothesis `h : p.ContinuationStakesNondegenerateOn V_T V_S` resolves against `And` and
fails. Call these by their full names — `ContinuationStakesNondegenerate.betaT_pos h`. -/

variable {p} {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}

/-- **A live Target channel forces a patient Target.** If `β_T` were zero the
product would vanish identically, so the existential could not hold. -/
theorem betaT_pos (h : p.ContinuationStakesNondegenerateOn V_T V_S) : 0 < p.β_T := by
  obtain ⟨⟨y₀, y₁, hy⟩, _⟩ := h
  rcases lt_trichotomy (0 : ℝ) p.β_T with hpos | hzero | hneg
  · exact hpos
  · rw [← hzero, zero_mul] at hy; exact absurd hy (lt_irrefl 0)
  · exact absurd (p.β_T_mem.1) (not_le.mpr hneg)

/-- **A live Sender channel forces a patient Sender.** -/
theorem betaS_pos (h : p.ContinuationStakesNondegenerateOn V_T V_S) : 0 < p.β_S := by
  obtain ⟨_, ⟨z₀, z₁, hz⟩⟩ := h
  rcases lt_trichotomy (0 : ℝ) p.β_S with hpos | hzero | hneg
  · exact hpos
  · rw [← hzero, zero_mul] at hz; exact absurd hz (lt_irrefl 0)
  · exact absurd (p.β_S_mem.1) (not_le.mpr hneg)

/-- **The Target's equilibrium value is nonconstant.** -/
theorem target_nonconstant (h : p.ContinuationStakesNondegenerateOn V_T V_S) :
    ∃ y₀ y₁ : ↥(Sanctions.S : Set ℝ), V_T y₀ < V_T y₁ := by
  have hβ := betaT_pos h
  obtain ⟨⟨y₀, y₁, hy⟩, _⟩ := h
  exact ⟨y₀, y₁, by nlinarith [hβ, hy]⟩

/-- **The Sender's equilibrium value is nonconstant.** -/
theorem sender_nonconstant (h : p.ContinuationStakesNondegenerateOn V_T V_S) :
    ∃ z₀ z₁ : ↥(Sanctions.S : Set ℝ), V_S z₀ < V_S z₁ := by
  have hβ := betaS_pos h
  obtain ⟨_, ⟨z₀, z₁, hz⟩⟩ := h
  exact ⟨z₀, z₁, by nlinarith [hβ, hz]⟩

end ContinuationStakesNondegenerate

/-- **Constructor from strict value inequalities and positive discounting.**

The form the `mechanismWitnessParams` frontier already has, and the form any new
witness should aim at: exhibit two states for each player across which the value
strictly rises, plus the two discount factors positive. -/
theorem continuationStakesNondegenerateOn_of_lt {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hβT : 0 < p.β_T) (hβS : 0 < p.β_S)
    {y₀ y₁ z₀ z₁ : ↥(Sanctions.S : Set ℝ)}
    (hT : V_T y₀ < V_T y₁) (hS : V_S z₀ < V_S z₁) :
    p.ContinuationStakesNondegenerateOn V_T V_S :=
  ⟨⟨y₀, y₁, mul_pos hβT (sub_pos.mpr hT)⟩,
   ⟨z₀, z₁, mul_pos hβS (sub_pos.mpr hS)⟩⟩

/-- **Constructor from exact discounted magnitudes.**

The form `b2_integrated_mechanism_active_generalF_witness` already has: the
discounted changes are pinned to specific positive reals, and only their
positivity is needed. -/
theorem continuationStakesNondegenerateOn_of_eq_pos {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {y₀ y₁ z₀ z₁ : ↥(Sanctions.S : Set ℝ)} {cT cS : ℝ}
    (hcT : 0 < cT) (hcS : 0 < cS)
    (hT : p.β_T * (V_T y₁ - V_T y₀) = cT)
    (hS : p.β_S * (V_S z₁ - V_S z₀) = cS) :
    p.ContinuationStakesNondegenerateOn V_T V_S :=
  ⟨⟨y₀, y₁, hT ▸ hcT⟩, ⟨z₀, z₁, hS ▸ hcS⟩⟩

/-! ## Rule 10 — axiom inventory -/

#print axioms Sanctions.AbstractGame.Params.ContinuationStakesNondegenerate.betaT_pos
#print axioms Sanctions.AbstractGame.Params.ContinuationStakesNondegenerate.betaS_pos
#print axioms Sanctions.AbstractGame.Params.ContinuationStakesNondegenerate.target_nonconstant
#print axioms Sanctions.AbstractGame.Params.continuationStakesNondegenerateOn_of_lt
#print axioms Sanctions.AbstractGame.Params.continuationStakesNondegenerateOn_of_eq_pos

end Params
end AbstractGame
end Sanctions
