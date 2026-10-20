/-
Sanctions/Theory/LockIn/OffCornerResponse.lean

**The equilibrium sanction is strictly interior, and the state still converges.**

The broad primitive persistence family reaches its theorem by driving the Sender
to the top: `σ_dyn_top_V_S_zero_eq_one_of_monotone` needs the Sender's stage
payoff to be maximized at `s = 1` and the corner value to be monotone, so both
summands of the objective peak at the same place and the realized rule is the
constant function `1`. That is a clean theorem about a degenerate rule: it does
not respond to the political state at all, and no trade-off is visible in it.

This module states the alternative. Two conditions on the Sender's *complete*
objective say that nothing at or below the current state beats freezing, and
that some strictly interior sanction beats both freezing and maximum pressure.
Together they place **every** dynamic maximizer strictly between the state and
the top — every one, not a selected one, so no selection principle is used and
the conclusion survives ties.

**These conditions are incompatible with the corner route, not weaker than it.**
If the stage payoff peaks at `1` and the continuation is monotone then nothing
interior beats `1`, so `SenderInteriorBeatsBoundariesAt` fails. This is a
disjoint region of the parameter space, and per Rule 9 it needs its own
inhabitation evidence; see `Examples/ContinuationDrivenEscalation.lean` and
`Examples/NonAffineInteriorWitness.lean`.

**What is not claimed.** Interiority holds strictly *below* the top state and
cannot hold at it: with a high-basin floor `max x sbar ≤ R x` and feasibility,
`R 1 = 1` is forced — that is exactly `no_upper_basin_floor_of_top_lt_one`. So
the interior response is a property of the transition *path*, not of the rest
point, and the convergence theorem below has the state approaching a corner
along a strictly interior rule.
-/

import Sanctions.Foundations.BinaryComparativeStatics
import Sanctions.Foundations.MonotoneAttraction
import Sanctions.Theory.LockIn.BasinAttraction

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Params)

/-! ## The two conditions, on the complete Sender objective

Both are stated over `U_S x a s + β_S · V_S (clip (F x s))` — the exact
expression `dynamicArgmaxSet` maximizes — rather than over a named `Prop`. That
is deliberate: a field of bare type `Prop` whose only tie to the data is its name
can be set to `True` by a supplier, and Rule 14 bans that pattern for anything a
headline theorem reads. Written this way the content is fixed by the model. -/

/-- **Nothing at or below the state beats freezing.**

`F x x = x`, so the sanction `s = x` is exactly the action that leaves the
political state where it is. The condition says the Sender does not want to
de-escalate below it: the within-period cost of a weaker sanction outweighs
whatever the resulting erosion of entrenchment is worth in continuation.

Note it is silent on the *sign* of the Sender's stake in the state. It never
asks whether `V_S` rises or falls with entrenchment, which matters because that
sign is a parameter of this model rather than a fact about it. -/
def SenderAboveDiagonalAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : Prop :=
  ∀ s ∈ Sanctions.I, s ≤ x →
    p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
      ≤ p.U_S x a x + p.β_S * V_S (Sanctions.clipS' (p.F x x))

/-- **Some interior sanction beats both freezing and maximum pressure.**

Escalation pays — the Sender does better than holding the state still — but full
escalation does not, because the entrenchment it causes costs more in
continuation than the extra coercion buys within the period. The optimum is
therefore strictly inside, and that is the trade-off the model is about. -/
def SenderInteriorBeatsBoundariesAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : Prop :=
  ∃ s₀ ∈ Ioo x (1 : ℝ),
    p.U_S x a x + p.β_S * V_S (Sanctions.clipS' (p.F x x))
        < p.U_S x a s₀ + p.β_S * V_S (Sanctions.clipS' (p.F x s₀))
      ∧ p.U_S x a 1 + p.β_S * V_S (Sanctions.clipS' (p.F x 1))
        < p.U_S x a s₀ + p.β_S * V_S (Sanctions.clipS' (p.F x s₀))

/-! ## Every maximizer is off both corners -/

/-- **Boundary exclusion at the dynamic Sender problem.**

Every element of `dynamicArgmaxSet` lies strictly between the state and the top.
`Foundations.argmax_mem_Ioo_top_of_improves_inward` supplies the order argument;
nothing beyond the two conditions and feasibility of the state is used — in
particular no continuity, no concavity, no differentiability, and **no
uniqueness of the maximizer**. -/
theorem every_dynamic_argmax_mem_Ioo_self_one
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a : ℝ} (hxI : x ∈ Sanctions.I)
    (hdiag : p.SenderAboveDiagonalAt V_S x a)
    (hint : p.SenderInteriorBeatsBoundariesAt V_S x a)
    {s : ℝ} (hs : s ∈ p.dynamicArgmaxSet V_S x a) :
    s ∈ Ioo x 1 := by
  obtain ⟨s₀, hs₀mem, hs₀diag, hs₀top⟩ := hint
  obtain ⟨hsI, hsmax⟩ := hs
  exact Sanctions.BinaryComparativeStatics.argmax_mem_Ioo_top_of_improves_inward
    hdiag ⟨le_of_lt (lt_of_le_of_lt hxI.1 hs₀mem.1), le_of_lt hs₀mem.2⟩
    hs₀diag hs₀top hsI hsmax

/-- The greatest selector is one of them, so it is interior too. -/
theorem σ_dyn_top_mem_Ioo_self_one
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a : ℝ} (hxI : x ∈ Sanctions.I)
    (hdiag : p.SenderAboveDiagonalAt V_S x a)
    (hint : p.SenderInteriorBeatsBoundariesAt V_S x a) :
    p.σ_dyn_top V_S x a ∈ Ioo x 1 :=
  p.every_dynamic_argmax_mem_Ioo_self_one hxI hdiag hint
    (p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a)

/-! ## The basin-uniform form, at a supplied equilibrium -/

/-- **The realized rule is strictly interior across the basin.**

Both conditions imposed uniformly at the equilibrium policy, for basin states
below the top. The exclusion of `x = 1` is not a gap in the argument: `R 1 = 1`
is *forced* by feasibility together with any high-basin floor, and
`no_upper_basin_floor_of_top_lt_one` is the proof that no floor can coexist with
`R 1 < 1`. -/
theorem dynamicTopRealizedRule_mem_Ioo_self_one_on
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {B : Set ℝ}
    (hBI : B ⊆ Sanctions.I)
    (hdiag : ∀ x ∈ B, x < 1 → p.SenderAboveDiagonalAt V_S x (α x))
    (hint : ∀ x ∈ B, x < 1 → p.SenderInteriorBeatsBoundariesAt V_S x (α x)) :
    ∀ x ∈ B, x < 1 → p.dynamicTopRealizedRule V_S α x ∈ Ioo x 1 :=
  fun x hx hlt =>
    p.σ_dyn_top_mem_Ioo_self_one (hBI hx) (hdiag x hx hlt) (hint x hx hlt)

/-! ## Convergence, with an interior rule and no rule monotonicity

The rule is strictly above the diagonal below the top, so under strict
adjustment the closed loop is too, and `MonotoneAttraction`'s strict-drift
theorem closes it. Nothing here asks the rule to be monotone — which is
essential, because `dynamicTopRealizedRule` is a greatest-argmax selector
composed with a Bellman-optimal policy and has no reason to be.

Continuity of the closed loop is the one hypothesis that must be earned rather
than derived. It is **not** available parametrically: the rule is upper
semicontinuous at best. `σ_dyn_top_continuous_of_unique` discharges it under
uniqueness of the dynamic argmax, via Berge, and that is the only route in this
development. -/

/-- **The state path converges to full entrenchment.**

An interior rule that stays strictly above the diagonal still drives the state to
the top: the path rises strictly, is bounded, and continuity makes its limit a
fixed point that strict drift excludes below `1`.

Read together with the interiority theorem above, this is the honest shape of the
result — sanctions strictly inside `(x, 1)` all along the path, and a corner in
the limit. -/
theorem dynamicTopLockInPathF_tendsto_top
    (hAdj : p.StrictAdjustment)
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {xbar x₀ : ℝ}
    (hbar : xbar ≤ 1) (hx₀ : x₀ ∈ Icc xbar 1)
    (hbarI : Icc xbar 1 ⊆ Sanctions.I)
    (hcont : ContinuousOn (p.dynamicTopLockInStepF V_S α) (Icc xbar 1))
    (hgt : ∀ x ∈ Icc xbar (1 : ℝ), x < 1 →
      x < p.dynamicTopRealizedRule V_S α x)
    (htop : p.dynamicTopLockInStepF V_S α 1 = 1) :
    Tendsto (fun n => p.dynamicTopLockInPathF V_S α x₀ n) atTop (𝓝 1) := by
  refine Sanctions.MonotoneAttraction.tendsto_top_of_continuous_strict_above_diagonal
    hbar hx₀ hcont ?_ ?_ htop
  · intro x hx
    exact (p.F_mem x _ (hbarI hx) (p.dynamicTopRealizedRule_mem V_S α x)).2
  · intro x hx
    exact p.self_lt_stepF_of_self_lt_rule hAdj V_S α (hbarI ⟨hx.1, le_of_lt hx.2⟩)
      (hgt x ⟨hx.1, le_of_lt hx.2⟩ hx.2)

end Params
end AbstractGame

end

end Sanctions
