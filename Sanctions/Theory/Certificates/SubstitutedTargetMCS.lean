/-
Sanctions/Theory/Certificates/SubstitutedTargetMCS.lean

**Round E4: monotone comparative statics of the equilibrium Target
policy — α-antitonicity from the substituted-objective chord sign,
and the discount-weight comparison ("the myopified Target complies
more").**

Two deliverables, both identified by the 2026-06-11 enhancement sweep
(T6 and T2) and built under the user's standing Rule-3 enrichment
authorization:

1. **`SubstitutedTargetDD`** (NEW per-equilibrium chord Prop —
   Rule-3 enrichment, recorded): for every carrier value pair, the
   Target's substituted Stackelberg objective
   `joint_T_integrand V_T V_S x a`
   (stage payoff at the dynamic Sender response plus discounted
   continuation) has *decreasing differences* in `(a; x)` on
   `[0,1] × [x̄, 1]` — a harder political state lowers the marginal
   value of compliance. **Orientation decision (recorded)**: the
   rally story makes the equilibrium Target policy ANTITONE on the
   basin (defiance rises with the hardline state); this is also the
   direction that composes with the existing Sender-side
   action-complementarity sign `∂²U_S/∂s∂a ≤ 0` (a less compliant
   Target raises the Sender's sanction marginal along the path) and
   with the next-state coordinates of the sweep's T3 route.
2. **`α_on_antitoneOn_of_substitutedDD`** — the equilibrium policy
   `D.α_on` is antitone on the basin. Engine: Topkis antitone
   selection (`antitone_argmax_of_decreasingDifferencesOn`,
   Foundations) + carrier argmax uniqueness (`target_unique_on`).
   Topkis 1998 Thm 2.8.1/2.8.3(a); Puterman Lemma 4.7.1 dual.
3. **`α_on_le_myopified_of_unique`** — the T2 ingredient: at any
   state, the dynamic equilibrium compliance is weakly below the
   (unique) *myopified* compliance — the argmax of the stage payoff
   at the same dynamic Sender response with the continuation switched
   off (`β_T := 0`). Engine: the two-point discount-weight lemma
   (`Foundations.MilgromShannon.argmax_le_of_add_antitone`, MS Thm 5
   with the discount weight as the parameter). The antitone
   continuation hypothesis follows from σ-antitonicity in the action
   (the existing R28 consequence) plus carrier `V_T` monotonicity on
   the transition image — supplied as a hypothesis here, with the
   composition lemma left to the consumer.

## Rule compliance

**Rule 1** ✓ — α_on is the Bellman-derived equilibrium policy; no
fixed strategies. **Rule 3** — `SubstitutedTargetDD` is a new
per-equilibrium chord Prop on the assumption surface (the only
enrichment in this file), introduced under the explicit user
authorization of 2026-06-11 (Tier-2 of the enhancement sweep);
recorded in BUILD-STATUS with the orientation rationale.
**Rule 5** ✓ — parametric. **Rule 19** ✓ — generic two-point lemma in
`Foundations/MilgromShannon.lean`; this file is Params wiring.
-/

import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Foundations.MilgromShannon

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Substituted-objective decreasing differences (Round E4 Rule-3
enrichment).** For every carrier value pair, the Target's substituted
Stackelberg objective has decreasing differences in
(compliance; state) on `[0,1] × [x̄, 1]`: raising the hardline state
weakly lowers the marginal value of compliance. The chord-form,
per-equilibrium analog of `∂²(joint Target objective)/∂a∂x ≤ 0`. -/
def SubstitutedTargetDD (D : p.ValueClass2) (xbar : ℝ) : Prop :=
  ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
    Sanctions.MilgromShannon.DecreasingDifferencesOn
      Sanctions.I (Set.Icc xbar 1)
      (fun a x => p.joint_T_integrand V_T.val V_S.val x a)

/-- **The equilibrium Target policy is antitone on the basin
(Round E4).** Under `SubstitutedTargetDD`, the Bellman-derived
equilibrium compliance policy `D.α_on V_T V_S` is non-increasing on
`[x̄, 1]`: deeper into the hardline basin, the Target complies weakly
less. Topkis antitone selection + carrier argmax uniqueness. -/
theorem α_on_antitoneOn_of_substitutedDD
    (D : p.ValueClass2) {xbar : ℝ}
    (hDD : p.SubstitutedTargetDD D xbar) (hxbar_nn : 0 ≤ xbar)
    (V_T : D.CarrierT) (V_S : D.CarrierS) :
    AntitoneOn (D.α_on V_T V_S) (Set.Icc xbar 1) := by
  intro x hx x' hx' hxx'
  -- Both comparison states are physical (`x, x' ∈ S = [0,1]`), since the
  -- basin threshold `xbar ≥ 0`; this is where the (state-local) leader
  -- optimality `α_on_isMaxOn` applies.
  have hxS : x ∈ Sanctions.S := ⟨le_trans hxbar_nn hx.1, hx.2⟩
  have hx'S : x' ∈ Sanctions.S := ⟨le_trans hxbar_nn hx'.1, hx'.2⟩
  have hmem := D.α_on_mem V_T V_S x
  have hmem' := D.α_on_mem V_T V_S x'
  have hmax : ∀ y ∈ Sanctions.I,
      p.joint_T_integrand V_T.val V_S.val x y
        ≤ p.joint_T_integrand V_T.val V_S.val x (D.α_on V_T V_S x) :=
    fun y hy => D.α_on_isMaxOn V_T V_S hxS hy
  have hmax' : ∀ y ∈ Sanctions.I,
      p.joint_T_integrand V_T.val V_S.val x' y
        ≤ p.joint_T_integrand V_T.val V_S.val x' (D.α_on V_T V_S x') :=
    fun y hy => D.α_on_isMaxOn V_T V_S hx'S hy
  obtain ⟨hmaxmax, -⟩ :=
    Sanctions.MilgromShannon.antitone_argmax_of_decreasingDifferencesOn
      (hDD V_T V_S) hxx' hx hx' hmem hmem' hmax hmax'
  have hmax_mem :
      max (D.α_on V_T V_S x) (D.α_on V_T V_S x') ∈ Sanctions.I :=
    Sanctions.max_mem_I hmem hmem'
  have huniq :=
    D.target_unique_on V_T.val V_T.property V_S.val V_S.property
  have heq : max (D.α_on V_T V_S x) (D.α_on V_T V_S x')
      = D.α_on V_T V_S x := by
    refine huniq x hxS _ _ hmax_mem hmem ?_ ?_
    · intro y hy
      exact hmaxmax y hy
    · intro y hy
      exact hmax y hy
  calc D.α_on V_T V_S x'
      ≤ max (D.α_on V_T V_S x) (D.α_on V_T V_S x') := le_max_right _ _
    _ = D.α_on V_T V_S x := heq

/-- **The myopified Target complies more (Round E4, T2 ingredient).**
At any state, the dynamic equilibrium compliance `D.α_on V_T V_S x`
is weakly below the (unique) maximizer `a₀` of the *myopified*
objective — the stage payoff at the same dynamic Sender response with
the continuation channel switched off. Hypotheses: `a₀` uniquely
maximizes the myopified objective, and the continuation channel
`a ↦ V_T(F(x, σ_dyn(x, a)))` is antitone in compliance (which follows
from σ-antitonicity in the action — the R28 consequence — plus
carrier `V_T` monotonicity on the transition image). MS Theorem 5
with the discount weight as the parameter. -/
theorem α_on_le_myopified_of_unique
    (D : p.ValueClass2)
    (V_T : D.CarrierT) (V_S : D.CarrierS) {x : ℝ} (hxS : x ∈ Sanctions.S)
    {a₀ : ℝ} (ha₀ : a₀ ∈ Sanctions.I)
    (hmax₀ : ∀ y ∈ Sanctions.I,
      p.U_T x y (p.σ_dyn V_S.val x y) ≤ p.U_T x a₀ (p.σ_dyn V_S.val x a₀))
    (huniq₀ : ∀ y ∈ Sanctions.I,
      (∀ z ∈ Sanctions.I,
        p.U_T x z (p.σ_dyn V_S.val x z) ≤ p.U_T x y (p.σ_dyn V_S.val x y))
      → y = a₀)
    (hh_anti : AntitoneOn
      (fun a => (V_T.val (Sanctions.clipS'
        (p.F x (p.σ_dyn V_S.val x a))) : ℝ))
      Sanctions.I) :
    D.α_on V_T V_S x ≤ a₀ := by
  refine Sanctions.MilgromShannon.argmax_le_of_add_antitone
    p.β_T_mem.1 hh_anti ha₀ (D.α_on_mem V_T V_S x) hmax₀ huniq₀ ?_
  intro y hy
  exact D.α_on_isMaxOn V_T V_S hxS hy

end Params
end AbstractGame

end

end Sanctions
