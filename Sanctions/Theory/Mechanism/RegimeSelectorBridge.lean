/-
Sanctions/Theory/Mechanism/RegimeSelectorBridge.lean

**Where the Sender-myopic column severs the loop — and exactly how far that gets
you.**

## The circularity, and the one place it is not there

The obstruction to constructing regimes `01` and `11` is a genuine circle: the
Sender's forward-looking response `σ_dyn` reads the Sender value `V_S`; `V_S` is
the value of following the Target's policy `α` against that response; and `α` is
chosen against the response. There is no single operator to contract.

The Sender-myopic column is not merely *easier*. The circle is **absent**, and
this file says so as a theorem rather than as a remark. When the Sender does not
discount the future — `p.β_S = 0` — the Sender's forward-looking objective is
*pointwise equal* to the Sender's stage payoff:

    senderDynObjective V_S x a s = U_S x a s + β_S * V_S (clipS' (F x s))
                                 = U_S x a s                    when β_S = 0.

The continuation term is not small, or dominated, or bounded: it is **gone**.
Consequently the Sender's best-reply *set* does not depend on `V_S` at all
(`senderDyn_isMaxOn_indep_of_value`), which is precisely the statement that the
Sender's response has stopped reading the object that closes the loop.

## What this does and does not deliver

It delivers the **set** identity, unconditionally and with no new assumption: the
forward-looking Sender argmax set coincides with the stage argmax set.

It does **not** deliver the **selector** identity `σ_dyn_top V_S = p.σ` that a
regime-`10` equilibrium bridge needs. Two maximizers of the same set-valued
problem need not be the same point when the argmax is not a singleton, and
`β_S = 0` does nothing about that: with a Sender stage payoff constant in the
sanction, every action is optimal, the primitive selector `p.σ` may choose `0`
and the greatest selector `σ_dyn_top` chooses `1`, and both are correct. Closing
that gap requires either

* a hypothesis that `p.σ` *is* the greatest maximizer of the stage problem, or
* uniqueness of the stage argmax (from strict concavity or strict single crossing
  of `U_S` in the sanction),

and **each is a Rule-3 stop** — neither is derivable from the current `Params`
surface. Nothing here assumes either, and no theorem below may be read as
inhabiting `FeedbackStackelbergEquilibriumTop` at any continuation profile; see
`Theory/Mechanism/RegimeExistence.lean`, where inhabitation is recorded as open
at all four profiles.

## Rule 22

General in `F`. The transition appears only inside the continuation term, which
is exactly the term that vanishes; no chord, no functional form, no `hF`.

## Rule 19

`Params`-level wiring, so `Theory/`, not `Foundations/`.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace Sanctions
namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. At `β_S = 0` the continuation term vanishes -/

/-- **The Sender's forward-looking objective collapses to its stage payoff.**

Pointwise in the state, the Target's action, and the sanction — and, crucially,
*for every* continuation value `V_S`. -/
theorem senderDynObjective_eq_stage_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a s : ℝ) :
    p.senderDynObjective V_S x a s = p.U_S x a s := by
  simp [senderDynObjective, hβ]

/-- The same statement as an equality of functions of the sanction, which is the
form an argmax argument consumes. -/
theorem senderDynObjective_fun_eq_stage_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    (fun s => p.senderDynObjective V_S x a s) = fun s => p.U_S x a s := by
  funext s; exact p.senderDynObjective_eq_stage_of_βS_zero hβ V_S x a s

/-! ## 2. The Sender's best-reply set is the stage best-reply set -/

/-- **The forward-looking Sender argmax is the stage argmax.**

A sanction is optimal for a non-discounting Sender exactly when it is optimal in
the current period. This is the loop-severing statement in its cleanest form. -/
theorem isMaxOn_senderDyn_iff_stage_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a s : ℝ) :
    IsMaxOn (fun s' => p.senderDynObjective V_S x a s') Sanctions.I s ↔
      IsMaxOn (fun s' => p.U_S x a s') Sanctions.I s := by
  rw [p.senderDynObjective_fun_eq_stage_of_βS_zero hβ V_S x a]

/-- **The argmax set, as a set identity.** -/
theorem senderDyn_argmaxSet_eq_stage_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    {s | s ∈ Sanctions.I ∧
        IsMaxOn (fun s' => p.senderDynObjective V_S x a s') Sanctions.I s}
      = {s | s ∈ Sanctions.I ∧ IsMaxOn (fun s' => p.U_S x a s') Sanctions.I s} := by
  ext s
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  exact fun _ => p.isMaxOn_senderDyn_iff_stage_of_βS_zero hβ V_S x a s

/-! ## 3. The loop is severed: the response stops reading the value -/

/-- **The Sender's best reply does not depend on the continuation value.**

This is the content that distinguishes the Sender-myopic column structurally,
not merely quantitatively. In regimes `01` and `11` the Sender's response reads
`V_S`, which is what closes the circle with the Target's policy; at `β_S = 0` it
provably does not, for *any* pair of continuation values. -/
theorem senderDyn_isMaxOn_indep_of_value (hβ : p.β_S = 0)
    (V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a s : ℝ) :
    IsMaxOn (fun s' => p.senderDynObjective V_S x a s') Sanctions.I s ↔
      IsMaxOn (fun s' => p.senderDynObjective W_S x a s') Sanctions.I s := by
  rw [p.isMaxOn_senderDyn_iff_stage_of_βS_zero hβ V_S x a s,
      p.isMaxOn_senderDyn_iff_stage_of_βS_zero hβ W_S x a s]

/-- The set form of the previous theorem. -/
theorem senderDyn_argmaxSet_indep_of_value (hβ : p.β_S = 0)
    (V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    {s | s ∈ Sanctions.I ∧
        IsMaxOn (fun s' => p.senderDynObjective V_S x a s') Sanctions.I s}
      = {s | s ∈ Sanctions.I ∧
        IsMaxOn (fun s' => p.senderDynObjective W_S x a s') Sanctions.I s} := by
  rw [p.senderDyn_argmaxSet_eq_stage_of_βS_zero hβ V_S x a,
      p.senderDyn_argmaxSet_eq_stage_of_βS_zero hβ W_S x a]

/-! ## 4. Why the selector identity does NOT follow

The set identity above is as far as `β_S = 0` reaches. The remaining gap is
recorded here rather than papered over: a set having the same members does not
make two *selections* from it agree, and the regime-`10` equilibrium bridge needs
the selections to agree.

`selector_gap_is_real` below is the general fact, stated with no reference to the
game: a set with two distinct members admits two selectors that disagree. Applied
to a Sender stage payoff that is constant in the sanction — where every action in
`[0,1]` is a maximizer — it says the primitive selector and the greatest selector
may differ at every state, with both optimal. That is a Rule-3 stop, not a
lemma. -/

/-- **The selector gap is real.** If a set has two distinct members, then
agreeing on the set does not force two selections to agree. -/
theorem selector_gap_is_real {A : Set ℝ} {u v : ℝ}
    (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) :
    ∃ f g : Unit → ℝ, (∀ t, f t ∈ A) ∧ (∀ t, g t ∈ A) ∧ f () ≠ g () :=
  ⟨fun _ => u, fun _ => v, fun _ => hu, fun _ => hv, huv⟩

end Params
end AbstractGame
end Sanctions

end
