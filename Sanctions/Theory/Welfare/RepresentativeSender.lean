/-
Sanctions/Theory/Welfare/RepresentativeSender.lean

**A Sender whose per-period payoff does not depend on the political state has
no reason to sanction when the Target defies fully.**

Plain words. Take any economy. Suppose the Target's policy is full defiance
(compliance `0`) at every feasible state, and suppose that at compliance `0`
the Sender's stage payoff is `0` with no sanction and strictly negative with
any positive sanction, whatever the political state. Then the Sender's value
is the constant `0`, and its forward-looking best response is no sanction at
every feasible state, including the greatest forward-looking maximiser
`σ_dyn_top` that the realised rule uses.

The statements are parametric in the economy (Rule 5). They add no hypothesis
to any existing theorem (Rule 3): every condition is a hypothesis of the new
lemma only. The example economy that inhabits them is in
`Sanctions/Examples/DualBasinNationalWelfare.lean`.
-/
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.DynamicTopLockIn

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

variable (p : Sanctions.AbstractGame.Params)

/-- **With a constant continuation value, the greatest forward-looking
sanction is zero if the stage payoff is strictly best at zero.**
At a given state `x` and compliance `a`, if the Sender's continuation value is
the same at every state and every positive sanction gives a strictly lower
stage payoff than no sanction, then the greatest dynamic maximiser
`σ_dyn_top V_S x a` is `0`. Scope: any economy; the conclusion is for the
single pair `(x, a)` whose stage hypothesis is supplied. -/
theorem σ_dyn_top_eq_zero_of_stateFree_of_alpha_zero
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (hV : ∀ y z, V_S y = V_S z) (x a : ℝ)
    (hneg : ∀ s ∈ Sanctions.I, s ≠ 0 → p.U_S x a s < p.U_S x a 0) :
    p.σ_dyn_top V_S x a = 0 := by
  by_contra hne
  have hmem := p.σ_dyn_top_mem_I V_S x a
  have hmax := p.σ_dyn_top_isMaxOn V_S x a
  have h0 : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have h := isMaxOn_iff.1 hmax 0 h0
  have hc := hV (Sanctions.clipS' (p.F x 0))
    (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)))
  have hlt := hneg _ hmem hne
  rw [hc] at h
  linarith

/-- **A Sender whose stage payoff is never positive and is zero at no
sanction has the zero value function.**
If, along a Target policy `α`, the Sender's stage payoff `U_S x (α x) s` is
at most `0` for every sanction and exactly `0` at no sanction, at every
feasible state, then the Sender's Bellman operator maps the zero function to
itself. Scope: any economy and any continuous policy. -/
theorem bellmanS_BCF_zero_of_stage_nonpos
    {α : ℝ → ℝ} (hα : Continuous α)
    (hU : ∀ x ∈ Sanctions.S, ∀ s ∈ Sanctions.I, p.U_S x (α x) s ≤ 0)
    (h0 : ∀ x ∈ Sanctions.S, p.U_S x (α x) 0 = 0) :
    p.bellmanS_BCF α hα 0 = 0 := by
  ext x
  change sSup ((fun s => p.U_S x.val (α x.val) s
      + p.β_S * (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (Sanctions.clipS' (p.F x.val s))) ''
        Sanctions.I) = 0
  have hg : IsGreatest ((fun s => p.U_S x.val (α x.val) s
      + p.β_S * (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (Sanctions.clipS' (p.F x.val s))) ''
        Sanctions.I) 0 := by
    refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
    · simp [h0 x.val x.property]
    · rintro _ ⟨s, hs, rfl⟩
      simpa using hU x.val x.property s hs
  exact hg.csSup_eq

/-- **The Sender's value is zero under such a stage payoff.**
Under the stage conditions of `bellmanS_BCF_zero_of_stage_nonpos`, any
function that is a fixed point of the Sender's Bellman operator along `α` is the
zero function. The proof is the contraction estimate of the Sender operator:
`‖V‖ ≤ β_S ‖V‖` with `β_S < 1`. Scope: any economy. -/
theorem V_S_eq_zero_of_stage_nonpos
    {α : ℝ → ℝ} (hα : Continuous α)
    (hU : ∀ x ∈ Sanctions.S, ∀ s ∈ Sanctions.I, p.U_S x (α x) s ≤ 0)
    (h0 : ∀ x ∈ Sanctions.S, p.U_S x (α x) 0 = 0)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (hV : V = p.bellmanS_BCF α hα V) :
    V = 0 := by
  have hz := p.bellmanS_BCF_zero_of_stage_nonpos hα hU h0
  have hβ0 := p.β_S_mem.1
  have hβ1 := p.β_S_mem.2
  have hd : dist V 0 ≤ p.β_S * dist V 0 := by
    refine (BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)).2 ?_
    intro x
    have h := p.bellmanS_BCF_pointwise_dist hα V 0 x
    rw [← hV, hz] at h
    exact h
  have hn : 0 ≤ dist V 0 := dist_nonneg
  have : dist V 0 ≤ 0 := by nlinarith
  exact dist_le_zero.1 this

/-- **A Sender with a state-free stage payoff plays no sanction in equilibrium.**
In an upper-selector feedback Stackelberg equilibrium `E`, suppose the Target's
policy is full defiance (`E.α x = 0`) at every feasible state, and the Sender's
stage payoff at compliance `0` is `0` at no sanction and strictly negative at
every positive sanction, at every feasible state. Then the Sender's value is
identically `0` and the realised sanction rule is `0` at every feasible state.
Scope: any economy and any equilibrium `E` of it satisfying these conditions;
it says nothing about equilibria that violate them. -/
theorem dynamicTopRealizedRule_eq_zero_of_stateFree
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hα0 : ∀ x ∈ Sanctions.S, E.α x = 0)
    (hzero : ∀ x ∈ Sanctions.S, p.U_S x 0 0 = 0)
    (hneg : ∀ x ∈ Sanctions.S, ∀ s ∈ Sanctions.I, s ≠ 0 → p.U_S x 0 s < 0) :
    E.V_S = 0 ∧ ∀ x ∈ Sanctions.S, p.dynamicTopRealizedRule E.V_S E.α x = 0 := by
  have hV : E.V_S = 0 := by
    refine p.V_S_eq_zero_of_stage_nonpos E.hα ?_ ?_ E.V_S E.V_S_fix
    · intro x hx s hs
      rw [hα0 x hx]
      by_cases hs0 : s = 0
      · rw [hs0, hzero x hx]
      · exact (hneg x hx s hs hs0).le
    · intro x hx
      rw [hα0 x hx]
      exact hzero x hx
  refine ⟨hV, fun x hx => ?_⟩
  change p.σ_dyn_top E.V_S x (E.α x) = 0
  rw [hα0 x hx]
  refine p.σ_dyn_top_eq_zero_of_stateFree_of_alpha_zero E.V_S (fun y z => by rw [hV]; rfl) x 0 ?_
  intro s hs hs0
  rw [hzero x hx]
  exact hneg x hx s hs hs0

end Params
end AbstractGame
end Sanctions
