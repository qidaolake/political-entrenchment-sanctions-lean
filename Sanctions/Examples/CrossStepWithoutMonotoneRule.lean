/-
Sanctions/Examples/CrossStepWithoutMonotoneRule.lean

**The path-comparison hypothesis was strictly stronger than the path comparison
needs.**

`rulePathF_le_of_rule_le_on_stopped` asks the upper sanction rule to be
non-decreasing on `[0,1]`. `rulePathF_le_on_stopped_of_crossStepOrder` asks
instead for the cross-order condition on the two closed-loop *state* maps, which
is what the induction actually consumes, and
`crossClosedLoopStepOrderOn_of_rule_le_and_upper_mono` shows the old pair implies
the new one.

That leaves the question Rule 9B exists to force: is the new class genuinely
wider, or does it merely look wider? This file answers it. Without an answer the
weakening is a rearrangement, not a generalization, and the general theorem —
though true — would not yet be known to say more than its predecessor did.

**The economy.** Take the lattice-meet transition `F x s = min x s`, already in
the tree as `Params.minMeetTransition`: a sanction below the political state
pulls the state down to it, a sanction above it leaves the state alone. Every
maintained transition field holds, `min t t = t` being the diagonal. Take the
realised rule

    R x = max x (1 - x),

which is feasible on `[0,1]` and **not** monotone there — it falls from `R 0 = 1`
to `R (1/2) = 1/2`. Because `R x ≥ x` everywhere, the closed loop is

    x ↦ min x (R x) = x,

the identity. So cross-order holds for free, at every pair of feasible states and
with the *same* rule on both legs, while the hypothesis it replaces fails.

**What the example means, and not just that it works.** The rule oscillates, and
the dynamics do not care, because every sanction it names sits above the state
and the meet transition discards it. Rule monotonicity is a property of the
*rule*; what the comparison needs is a property of the *composition* of the rule
with the transition. Wherever the transition is insensitive to the sanction — a
saturated region, a binding floor, a phase where sanctions are already above the
state — the two come apart, and the old hypothesis was charging for regularity
the dynamics never spent.

**Why this is not the degenerate case.** `F x s = x` — a transition ignoring
sanctions entirely — would also do it, and would prove far less; the tree already
records that transition's pathology as
`diagonal_and_sanction_monotone_insufficient_for_strict_step`. Here `F` responds
to sanctions genuinely and strictly below the diagonal, and it is only the
*particular* rule's placement above the diagonal that flattens the loop.

**The same economy separates closed-loop from rule monotonicity** (BG1.8,
2026-10-06). The path comparators in `DifferentPolicyComparator.lean` and
`TwoSidedForwardLooking.lean` now have siblings that ask the upper *closed
loop* `x ↦ F(x, R x)` to be non-decreasing instead of the rule `R`
(`rulePathF_le_of_rule_le_and_closedLoop_mono` and its stopped and
equilibrium forms). Here the closed loop is the identity, so it is monotone,
while `R` is not: `exists_closedLoopMono_without_monotone_rule` shows those
siblings' hypothesis class strictly contains the old one.

**What this licenses, and what it does not** (Rule 9A). It refutes a universal:
monotonicity of the upper rule is not necessary for cross-order, so the general
theorem's hypothesis class strictly contains the old one. It exhibits no economy
in which the ordering conclusion fails, says nothing about which condition holds
in any economy of interest, and makes no claim that non-monotone realised rules
are typical.

Rule 1: the sanction is not posited. `Params.minMeetTransition` fixes the Sender
stage payoff to `-(s - c)^2`, whose stage argmax is `c`; the rule `R` here is a
comparison object supplied to a *path* theorem that quantifies over rules, not a
strategy attributed to a player. Rule 3: no new assumption — refuting a universal
widens nothing. Rule 22: the transition is a general member of the maintained
class, not the affine law.
-/
import Sanctions.Examples.TransitionShapeNotPreserved
import Sanctions.Theory.LockIn.DifferentPolicyComparator

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame
namespace Params

variable {p : Params}

/-- The oscillating rule: sanction at least as high as the state, and highest at
the two ends. -/
def wobbleRule (x : ℝ) : ℝ := max x (1 - x)

theorem wobbleRule_mem {x : ℝ} (hx : x ∈ Sanctions.I) :
    Sanctions.AbstractGame.Params.wobbleRule x ∈ Sanctions.I := by
  obtain ⟨h0, h1⟩ := hx
  constructor
  · exact le_trans h0 (le_max_left _ _)
  · exact max_le h1 (by linarith)

theorem self_le_wobbleRule (x : ℝ) :
    x ≤ Sanctions.AbstractGame.Params.wobbleRule x := le_max_left _ _

/-- **The rule is not monotone on the feasible interval.** It falls from `1` at
the left endpoint to `1/2` at the midpoint. -/
theorem wobbleRule_not_monotoneOn :
    ¬ MonotoneOn Sanctions.AbstractGame.Params.wobbleRule Sanctions.I := by
  intro h
  have := h (by constructor <;> norm_num : (0 : ℝ) ∈ Sanctions.I)
    (by constructor <;> norm_num : (1 / 2 : ℝ) ∈ Sanctions.I) (by norm_num)
  simp only [Sanctions.AbstractGame.Params.wobbleRule] at this
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 1 - 0),
    max_eq_left (by norm_num : (1 : ℝ) - 1 / 2 ≤ 1 / 2)] at this
  norm_num at this

/-- **Under the meet transition this rule leaves the state alone.** The closed
loop is the identity, because every sanction the rule names sits weakly above the
state and `min` discards it. -/
theorem minMeet_ruleStepF_wobble (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    (p.minMeetTransition c hc).ruleStepF
        Sanctions.AbstractGame.Params.wobbleRule x = x := by
  change min x (Sanctions.AbstractGame.Params.wobbleRule x) = x
  exact min_eq_left (self_le_wobbleRule x)

/-- **Cross-order holds with a non-monotone rule on both legs.**

The witness. Both closed loops are the identity, so the condition reduces to
`x ≤ y`, which is its own hypothesis. -/
theorem minMeet_crossClosedLoopStepOrderOn_wobble
    (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (B : Set ℝ) :
    (p.minMeetTransition c hc).CrossClosedLoopStepOrderOn
      Sanctions.AbstractGame.Params.wobbleRule
      Sanctions.AbstractGame.Params.wobbleRule B := by
  intro x _ y _ hxy
  rw [minMeet_ruleStepF_wobble, minMeet_ruleStepF_wobble]
  exact hxy

/-- **So the cross-order surface is strictly weaker than the one it replaces.**

There is an economy in the maintained transition class, and a feasible realised
rule on it, satisfying the cross-order condition consumed by
`rulePathF_le_on_stopped_of_crossStepOrder` while failing the monotonicity
required by `rulePathF_le_of_rule_le_on_stopped`. The implication proved in
`crossClosedLoopStepOrderOn_of_rule_le_and_upper_mono` therefore does not
reverse, and the generalization is genuine rather than notational. -/
theorem exists_crossStepOrder_without_monotone_rule (p₀ : Params) :
    ∃ (q : Params) (R : ℝ → ℝ) (B : Set ℝ),
      q.CrossClosedLoopStepOrderOn R R B
        ∧ (∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
        ∧ ¬ MonotoneOn R Sanctions.I :=
  ⟨p₀.minMeetTransition (1 / 2) (by constructor <;> norm_num),
    Sanctions.AbstractGame.Params.wobbleRule, Sanctions.I,
    minMeet_crossClosedLoopStepOrderOn_wobble _ _ _,
    fun _ hx => wobbleRule_mem hx,
    wobbleRule_not_monotoneOn⟩

/-- **The closed loop is monotone although the rule is not.** Under the meet
transition the wobble rule's closed loop is the identity, hence non-decreasing
on `[0,1]`, while the rule itself is not (`wobbleRule_not_monotoneOn`). General
member of the maintained transition class, not the affine law (Rule 22). -/
theorem minMeet_ruleStepF_wobble_monotoneOn (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    MonotoneOn ((p.minMeetTransition c hc).ruleStepF
      Sanctions.AbstractGame.Params.wobbleRule) Sanctions.I := by
  intro x _ y _ hxy
  rw [minMeet_ruleStepF_wobble, minMeet_ruleStepF_wobble]
  exact hxy

/-- **So closed-loop monotonicity is strictly weaker than rule monotonicity.**

There is an economy in the maintained transition class, and a feasible rule on
it, whose closed loop `x ↦ F(x, R x)` is non-decreasing on `[0,1]` although the
rule is not. The implication `ruleStepF_monotoneOn_of_rule_monotoneOn` therefore
does not reverse, and the closed-loop siblings of the path comparators
(`rulePathF_le_of_rule_le_and_closedLoop_mono`,
`rulePathF_le_of_rule_le_on_stopped_closedLoopMono`,
`crossClosedLoopStepOrderOn_of_rule_le_and_closedLoop_mono`) cover economies the
rule-monotone forms do not (Rule 9B, BG1.8). An existence statement only
(Rule 9A): it says nothing about which condition holds in an economy of
interest. The witness transition is the lattice meet, a general member of the
maintained class, not the affine law (Rule 22). -/
theorem exists_closedLoopMono_without_monotone_rule (p₀ : Params) :
    ∃ (q : Params) (R : ℝ → ℝ),
      MonotoneOn (q.ruleStepF R) Sanctions.I
        ∧ (∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
        ∧ ¬ MonotoneOn R Sanctions.I :=
  ⟨p₀.minMeetTransition (1 / 2) (by constructor <;> norm_num),
    Sanctions.AbstractGame.Params.wobbleRule,
    minMeet_ruleStepF_wobble_monotoneOn _ _,
    fun _ hx => wobbleRule_mem hx,
    wobbleRule_not_monotoneOn⟩

end Params
end AbstractGame

end

end Sanctions
