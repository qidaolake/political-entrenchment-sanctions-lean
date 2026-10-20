/-
Sanctions/Examples/PlacableSenderSecurityHistory.lean

**The Target's security value survives history-dependent strategies on both
sides** (round BD, 2026-10-01; the remark of `PlacableSenderSecurity.lean` and of
the staged security item, previously marked "not formalised").

`PlacableSenderSecurity.lean` proves, under the unrefined loss-offset margin
`LossOffset₀` (the Target's marginal sanction pain `c` is at most the discounted
value `β_T·d_lo·g_T⁰` of the entrenchment a unit of sanction builds), that

* always defying earns the Target at least its permanent-relief payoff `W(x₀)`
  against every feasible open-loop sanction sequence
  (`reliefPayoff_le_defiancePayoff`), and
* permanent relief holds every feasible compliance sequence to at most `W(x₀)`
  (`targetPathPayoff_relief_le`),

so `W(x₀)` is the Target's minmax over pure open-loop sanction sequences
(`reliefPayoff_isLeast`). Its docstring remarked that a history-dependent Sender
strategy, played against the always-defy plan, induces one such sequence, and
left that unformalised. This file proves the stronger two-sided statement, via
`Foundations/HistoryDependentSecurity.lean`:

* `reliefPayoff_isLeast_history` — `W(x₀)` is the least ceiling the Sender can
  impose with a feasible **pure history-dependent** sanction strategy (one that
  conditions on all past states, compliance and sanctions, and on current
  compliance) against every feasible pure history-dependent compliance strategy;
* `reliefPayoff_isGreatest_history` — `W(x₀)` is the greatest floor the Target can
  guarantee with such a strategy against every such Sender strategy, attained by
  always defying;
* `defiance_secures_reliefPayoff_history` — the always-defy plan earns at least
  `W(x₀)` against every feasible pure history-dependent Sender strategy.

So in pure strategies `W(x₀)` is the value of the zero-sum security game on the
Target's payoff, whatever the information the strategies condition on.

Scope (Rules 1 and 9). Security levels of fixed plans, not equilibrium
statements; nothing here says which history-dependent equilibria exist. Pure
strategies only (no randomisation), deterministic transition, perfect monitoring.
General in `F` (Rule 22): only the chord conditions read by the open-loop lemmas.
Rule 3: no new assumption — `LossOffset₀` is the existing margin, and the
history-plan types are definitions.

Since renovation item BH3.6 (2026-10-06) the three theorems are corollaries of their
`Params`-level forms in `Theory/Equilibrium/SecurityCore.lean`, with their statements
unchanged: the two-sided security value holds over any economy with the zero-section
state chord, the sanction lower chord from zero, the Target's three bounds and the
margin, for any Sender objective.
-/
import Sanctions.Examples.PlacableSenderSecurity
import Sanctions.Foundations.HistoryDependentSecurity

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.HistoryDependentSecurity

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The transition in the joint-history form: compliance does not move the state. -/
def histF : ℝ → ℝ → ℝ → ℝ := fun x _ s => E.F x s

/-- The open-loop path of the joint-history form is the episode path of the
sanction sequence. -/
theorem openLoopPath_histF (a s : ℕ → ℝ) (x₀ : ℝ) :
    openLoopPath E.histF a s x₀ = E.toParams.episodePath s x₀ :=
  E.toParams.openLoopPath_histF a s x₀

/-- The Target's open-loop payoff is `targetPathPayoff`. -/
theorem targetPathPayoff_eq_openLoopPayoff (a s : ℕ → ℝ) (x₀ : ℝ) :
    E.targetPathPayoff a s x₀ = openLoopPayoff E.toParams.U_T E.histF E.β_T a s x₀ :=
  E.toParams.targetPathPayoff_eq_openLoopPayoff a s x₀

/-- **The Target's payoff from a profile of pure history-dependent strategies**:
`τ` chooses compliance from the past and the current state, `σ` chooses the
sanction from the past, the current state and current compliance. -/
def targetHistoryPayoff (τ : LeaderPlan ℝ ℝ ℝ) (σ : FollowerPlan ℝ ℝ ℝ) (x₀ : ℝ) : ℝ :=
  jointPayoff E.toParams.U_T E.histF E.β_T τ σ x₀

/-- **Minmax over pure history-dependent strategies.** Under `LossOffset₀`, the
least payoff ceiling the Sender can impose on the Target with a feasible pure
history-dependent sanction strategy, against every feasible pure
history-dependent compliance strategy, is the permanent-relief payoff `W(x₀)`,
attained by permanent relief. General in `F`. A pinned headline, kept verbatim; since
BH3.6 the corollary of `AbstractGame.Params.reliefPayoff_isLeast_history`, which holds
for any Sender objective. -/
theorem reliefPayoff_isLeast_history (hTM : E.LossOffset₀) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    IsLeast {v : ℝ | ∃ σ : FollowerPlan ℝ ℝ ℝ, (∀ h x a, σ h x a ∈ Sanctions.I) ∧
        ∀ τ : LeaderPlan ℝ ℝ ℝ, (∀ h x, τ h x ∈ Sanctions.I) →
          E.targetHistoryPayoff τ σ x₀ ≤ v}
      (E.reliefPayoff x₀) :=
  E.toParams.reliefPayoff_isLeast_history E.security_band0 E.security_sanction0 E.security_pain0
    E.security_state0 E.hvlo.le E.security_costSign0 hTM hx₀

/-- **Maxmin over pure history-dependent strategies.** Under `LossOffset₀`, the
greatest payoff floor the Target can guarantee with a feasible pure
history-dependent compliance strategy, against every feasible pure
history-dependent sanction strategy, is `W(x₀)`, attained by always defying.
General in `F`. A pinned headline, kept verbatim; since BH3.6 the corollary of
`AbstractGame.Params.reliefPayoff_isGreatest_history`. -/
theorem reliefPayoff_isGreatest_history (hTM : E.LossOffset₀) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    IsGreatest {v : ℝ | ∃ τ : LeaderPlan ℝ ℝ ℝ, (∀ h x, τ h x ∈ Sanctions.I) ∧
        ∀ σ : FollowerPlan ℝ ℝ ℝ, (∀ h x a, σ h x a ∈ Sanctions.I) →
          v ≤ E.targetHistoryPayoff τ σ x₀}
      (E.reliefPayoff x₀) :=
  E.toParams.reliefPayoff_isGreatest_history E.security_band0 E.security_sanction0
    E.security_pain0 E.security_state0 E.hvlo.le E.security_costSign0 hTM hx₀

/-- **Always defying secures `W(x₀)` against every pure history-dependent Sender
strategy** (the remark of `PlacableSenderSecurity.lean`). Under `LossOffset₀`, the
Target's plan that never complies earns at least its permanent-relief payoff
against every feasible sanction strategy, however it conditions on the past. Since
BH3.6 the corollary of `AbstractGame.Params.defiance_secures_reliefPayoff_history`. -/
theorem defiance_secures_reliefPayoff_history (hTM : E.LossOffset₀) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) (σ : FollowerPlan ℝ ℝ ℝ) (hσ : ∀ h x a, σ h x a ∈ Sanctions.I) :
    E.reliefPayoff x₀ ≤ E.targetHistoryPayoff (LeaderPlan.ofSeq fun _ => 0) σ x₀ :=
  E.toParams.defiance_secures_reliefPayoff_history E.security_band0 E.security_sanction0
    E.security_pain0 E.security_state0 E.hvlo.le hTM hx₀ σ hσ

end ChordEconomy

/-! ## Non-vacuity at the quartic member (Rule 9B) -/

/-- **The history-dependent security value at the quartic member**, outside the
quadratic–linear family and non-affine in `F`: its margin
(`qwDefiance_security_margin`) instantiates `reliefPayoff_isLeast_history` at the
start `x₀ = 0`. Existence only. -/
theorem qwDefiance_reliefPayoff_isLeast_history :
    IsLeast {v : ℝ | ∃ σ : FollowerPlan ℝ ℝ ℝ, (∀ h x a, σ h x a ∈ Sanctions.I) ∧
        ∀ τ : LeaderPlan ℝ ℝ ℝ, (∀ h x, τ h x ∈ Sanctions.I) →
          qwDefiance.toChordEconomy.targetHistoryPayoff τ σ 0 ≤ v}
      (qwDefiance.toChordEconomy.reliefPayoff 0) :=
  qwDefiance.toChordEconomy.reliefPayoff_isLeast_history qwDefiance_security_margin
    ChordEconomy.zero_mem_I

end

end Examples
end Sanctions

#print axioms Sanctions.Examples.ChordEconomy.openLoopPath_histF
#print axioms Sanctions.Examples.ChordEconomy.targetPathPayoff_eq_openLoopPayoff
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast_history
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_isGreatest_history
#print axioms Sanctions.Examples.ChordEconomy.defiance_secures_reliefPayoff_history
#print axioms Sanctions.Examples.qwDefiance_reliefPayoff_isLeast_history
