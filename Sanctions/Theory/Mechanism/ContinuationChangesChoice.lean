/-
Sanctions/Theory/Mechanism/ContinuationChangesChoice.lean

**The behavioural mechanism, named: the continuation term changes which action
is optimal.**

## Why this file exists

`Theory/Mechanism/ContinuationStakes.lean` names *value* nondegeneracy: both
players' discounted continuation values vary across the state. The 2026-09-02
JET readiness audit (§3.5) pointed out, correctly, that this is weaker than
what the project means by "mechanism-active" — a phrase that in the paper
(Appendix §04) and in five pre-existing witness files denotes something
stronger: the continuation term *reverses a player's stage ranking*, so that
looking ahead changes the action chosen. Value nondegeneracy is necessary for
that and not sufficient: a value can vary across states the equilibrium never
visits, or vary without moving any argmax.

The stronger property already had general theorems on both sides —
`TargetReluctance.lean` on the Target, and (as of the same round)
`SenderInvestment.lean` on the Sender. What it lacked was a name over the
structure's own fields that those theorems conclude and the witnesses discharge.
This file supplies it.

## The predicate, and why it is stated this way

`ContinuationChangesSenderChoiceAt V_S x a` says: **no maximizer of the
forward-looking Sender objective is a maximizer of the stage objective.** Looking
ahead did not merely shift the value; it changed the set of optimal actions.

Three design points.

* It is stated over *every* forward-looking maximizer, so it is selection-robust
  — no choice of `σ_dyn` or `σ_dyn_top` is baked in. This is the form the strict
  ordering theorems already deliver.
* It is a **negation of stage optimality**, not a strict ordering. The strict
  ordering (`sM < sD` for all pairs) implies it (`…_of_strict_ordering` below),
  but the converse fails: a forward-looking argmax can fail to be stage-optimal
  by sitting *below* the stage argmax as easily as above. The predicate records
  that the channel is live; the direction is a separate, ordered statement.
* Rule 14: written directly over `p.U_S`, `p.F`, `V_S` and the argmax
  correspondences. Nothing here can be set to `True`.

The existential form `…Somewhere` — *some* forward-looking maximizer is not
stage-optimal — is provided alongside, because one existing witness
(`ma_target_continuation_changes_pivot_choice`) discharges it directly without
a uniqueness argument, and Rule 5 wants that witness to be a corollary rather
than a parallel statement.

## Rule 3

Definitions and lemmas only. Every theorem here is a restatement of an existing
conclusion in the new vocabulary; no hypothesis is introduced. The predicates are
conclusions witnesses prove, never hypotheses a load-bearing theorem consumes.

## Rule 19

`Theory/`: mentions `Params`. Imports both `LockIn` siblings; `Theory/Mechanism`
already imports from `Theory/LockIn` (via `DifferentPolicyComparator`) and
nothing in `LockIn` imports `Mechanism`, so the layering is unchanged.
-/

import Sanctions.Theory.LockIn.TargetReluctance
import Sanctions.Theory.LockIn.SenderInvestment

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The Sender side -/

/-- **The Sender's continuation term changes its optimal sanction at `(x, a)`.**
No forward-looking maximizer is a stage maximizer. -/
def ContinuationChangesSenderChoiceAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : Prop :=
  ∀ s ∈ Sanctions.I,
    IsMaxOn (fun t => p.U_S x a t + p.β_S * p.senderSanctionContinuation V_S x t)
      Sanctions.I s →
    ¬ IsMaxOn (fun t => p.U_S x a t) Sanctions.I s

/-- **The existential form**: some forward-looking maximizer is not stage
optimal. -/
def ContinuationChangesSenderChoiceSomewhereAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : Prop :=
  ∃ s ∈ Sanctions.I,
    IsMaxOn (fun t => p.U_S x a t + p.β_S * p.senderSanctionContinuation V_S x t)
      Sanctions.I s
    ∧ ¬ IsMaxOn (fun t => p.U_S x a t) Sanctions.I s

/-- **From the strict ordering.** If every stage maximizer sits strictly below
every forward-looking maximizer, no forward-looking maximizer can be a stage
maximizer — it would have to sit strictly below itself. -/
theorem continuationChangesSenderChoiceAt_of_strict_ordering
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a : ℝ}
    (h : ∀ sM ∈ Sanctions.I, ∀ sD ∈ Sanctions.I,
      IsMaxOn (fun t => p.U_S x a t) Sanctions.I sM →
      IsMaxOn (fun t => p.U_S x a t + p.β_S * p.senderSanctionContinuation V_S x t)
        Sanctions.I sD →
      sM < sD) :
    p.ContinuationChangesSenderChoiceAt V_S x a :=
  fun s hs hdyn hstage => lt_irrefl s (h s hs s hs hstage hdyn)

/-- **From one stage-better point.** If some forward-looking maximizer `s` is
strictly beaten on the stage objective by a feasible `s'`, then `s` is not stage
optimal. The shape `ma_target_continuation_changes_pivot_choice` has on the
Target side. -/
theorem continuationChangesSenderChoiceSomewhereAt_of_stage_better
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a s s' : ℝ}
    (hs : s ∈ Sanctions.I) (hs' : s' ∈ Sanctions.I)
    (hdyn : IsMaxOn (fun t => p.U_S x a t + p.β_S * p.senderSanctionContinuation V_S x t)
      Sanctions.I s)
    (hbetter : p.U_S x a s < p.U_S x a s') :
    p.ContinuationChangesSenderChoiceSomewhereAt V_S x a :=
  ⟨s, hs, hdyn, fun hstage => absurd (hstage hs') (not_le.mpr hbetter)⟩

/-- The universal form implies the existential one, given that a forward-looking
maximizer exists — which it always does, by `sender_arg_max_exists`. -/
theorem ContinuationChangesSenderChoiceAt.somewhere
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a : ℝ}
    (h : p.ContinuationChangesSenderChoiceAt V_S x a) :
    p.ContinuationChangesSenderChoiceSomewhereAt V_S x a := by
  obtain ⟨s, hs, hmax⟩ := p.sender_arg_max_exists V_S x a
  refine ⟨s, hs, hmax, h s hs hmax⟩

/-! ## 2. The Target side -/

/-- **The Target's continuation term changes its optimal compliance at `x`**,
against the Sender response `ρ`. No forward-looking maximizer is a stage
maximizer. -/
def ContinuationChangesTargetChoiceAt
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ∀ a ∈ Sanctions.I,
    IsMaxOn (fun b => p.U_T x b (ρ x b)
                        + p.β_T * p.targetComplianceContinuation ρ V_T x b)
      Sanctions.I a →
    ¬ IsMaxOn (fun b => p.U_T x b (ρ x b)) Sanctions.I a

/-- **The existential form** on the Target side. -/
def ContinuationChangesTargetChoiceSomewhereAt
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ∃ a ∈ Sanctions.I,
    IsMaxOn (fun b => p.U_T x b (ρ x b)
                        + p.β_T * p.targetComplianceContinuation ρ V_T x b)
      Sanctions.I a
    ∧ ¬ IsMaxOn (fun b => p.U_T x b (ρ x b)) Sanctions.I a

/-- **From the strict ordering** — the Target direction is reversed: every
forward-looking maximizer sits strictly *below* every stage maximizer. -/
theorem continuationChangesTargetChoiceAt_of_strict_ordering
    {ρ : ℝ → ℝ → ℝ} {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x : ℝ}
    (h : ∀ aM ∈ Sanctions.I, ∀ aD ∈ Sanctions.I,
      IsMaxOn (fun b => p.U_T x b (ρ x b)) Sanctions.I aM →
      IsMaxOn (fun b => p.U_T x b (ρ x b)
                          + p.β_T * p.targetComplianceContinuation ρ V_T x b)
        Sanctions.I aD →
      aD < aM) :
    p.ContinuationChangesTargetChoiceAt ρ V_T x :=
  fun a ha hdyn hstage => lt_irrefl a (h a ha a ha hstage hdyn)

/-- **From one stage-better point**, on the Target side. -/
theorem continuationChangesTargetChoiceSomewhereAt_of_stage_better
    {ρ : ℝ → ℝ → ℝ} {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a a' : ℝ}
    (ha : a ∈ Sanctions.I) (ha' : a' ∈ Sanctions.I)
    (hdyn : IsMaxOn (fun b => p.U_T x b (ρ x b)
                        + p.β_T * p.targetComplianceContinuation ρ V_T x b)
      Sanctions.I a)
    (hbetter : p.U_T x a (ρ x a) < p.U_T x a' (ρ x a')) :
    p.ContinuationChangesTargetChoiceSomewhereAt ρ V_T x :=
  ⟨a, ha, hdyn, fun hstage => absurd (hstage ha') (not_le.mpr hbetter)⟩

/-! ## 3. Both channels

The conjunction is what "mechanism-active" has always meant here. It is stated
at a state, a Target action, and a Sender response, because that is where the
two theorems above are stated; an equilibrium-level version reads it at the
equilibrium's own `α` and `σ_dyn_top`. -/

/-- **Both continuation channels change an optimal action.** -/
def BothContinuationsChangeChoiceAt
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (ρ : ℝ → ℝ → ℝ) (x a : ℝ) : Prop :=
  p.ContinuationChangesSenderChoiceAt V_S x a
  ∧ p.ContinuationChangesTargetChoiceAt ρ V_T x

/-! ## Rule 10 — axiom inventory -/

#print axioms Sanctions.AbstractGame.Params.continuationChangesSenderChoiceAt_of_strict_ordering
#print axioms Sanctions.AbstractGame.Params.continuationChangesSenderChoiceSomewhereAt_of_stage_better
#print axioms Sanctions.AbstractGame.Params.ContinuationChangesSenderChoiceAt.somewhere
#print axioms Sanctions.AbstractGame.Params.continuationChangesTargetChoiceAt_of_strict_ordering
#print axioms Sanctions.AbstractGame.Params.continuationChangesTargetChoiceSomewhereAt_of_stage_better

end Params
end AbstractGame
end Sanctions
