/-
Sanctions/Theory/LockIn/TargetReluctance.lean

**The Target-reluctance channel: a forward-looking Target complies less.**

This is the Target-side mirror of `theorem2_dynamic_dominates_myopic_at_same_alpha`
(`Theory/LockIn/SigmaDynComparison.lean`), and it exists to close the same gap on
the other player.

The Sender-side theorem isolates the Sender-investment channel by holding the
Target's policy fixed: at a *common* Target policy, the forward-looking Sender
sanctions at least as hard as the myopic Sender. The obvious complaint is that
this is not the comparison the paper's third goal wants. Comparing the two
*equilibria* at their own policies additionally needs the Target policies
ordered, `α ≤ α^M` — the forward-looking Target complying no more than the
myopic one — and until now that ordering was exhibited by constructed economies
rather than derived. It entered the cross-policy comparator
(`dynamicTopSanctions_ge_myopicEquilibrium_different_alpha`) as the hypothesis
`hRuleDom`.

**What is proved here.** At a common Sender response, every maximizer of the
Target's forward-looking objective lies at or below every maximizer of its
myopic objective. Written out, with `ρ` the Sender's response to compliance:

* myopic Target    `g(a) = U_T(x, a, ρ(x,a))`
* forward-looking  `f(a) = U_T(x, a, ρ(x,a)) + β_T · V_T(clip(F(x, ρ(x,a))))`

so `f = g + β_T·h`, where `h` is the discounted continuation value the Target
gets from the political state its own compliance induces.

**The economics, and why the sign comes out this way.** Compliance placates the
Sender, so `ρ(x, ·)` falls in `a`. Fewer sanctions erode entrenchment, so
`F(x, ·)` rises in `s`. An incumbent who values entrenchment has `V_T` rising in
the state. Composing the three, the continuation term `h` *falls* in `a`: every
unit of compliance the Target offers costs it political ground it wanted to
keep. The myopic Target does not see that cost and the forward-looking one does,
so the forward-looking Target complies less. Reluctance is not assumed; it is
what a Target that values its own entrenchment does once it looks ahead.

**The argument is elementary and needs no concavity.** Suppose a forward-looking
maximizer `aD` were strictly above a myopic maximizer `aM`. Then
`g(aD) ≤ g(aM)` because `aM` maximizes `g`, and `h(aD) < h(aM)` because `h` is
strictly decreasing, so `f(aD) < f(aM)` — contradicting `aD` maximizing `f`.
No Topkis, no single crossing, no differentiability: the continuation term is a
strictly decreasing wedge added to the myopic objective, and a strictly
decreasing wedge cannot move an argmax up.

That strictness is what buys "*every* maximizer", which is the selection-robust
form. The non-strict version appears below and concludes only that a myopic
maximizer remains a forward-looking maximizer.

**Scope — what this does and does not close.** It supplies the Target-policy
ordering from primitives, at a common Sender response. It does *not* by itself
deliver the full equilibrium-versus-equilibrium sanction comparison: that also
needs the two equilibria's Sender responses related, which is the separate
`hRuleDom` decomposition in `DifferentPolicyComparator.lean`. What was one
un-derived ordering is now one derived ordering plus one remaining bridge.

General in the transition: `F` enters only through the hypotheses, and `p.δ` is
never read.
-/

import Sanctions.Theory.LockIn.MyopicComparator

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

variable (p : Sanctions.AbstractGame.Params)

/-- **The continuation wedge the Target's own compliance moves.** For a Sender
response `ρ` and a Target continuation value `V_T`, this is the discounted value
of the political state that compliance `a` induces at state `x`. -/
noncomputable def targetComplianceContinuation
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  V_T (Sanctions.clipS' (p.F x (ρ x a)))

/-- **A forward-looking Target complies no more than a myopic one.**

At a common Sender response `ρ`, if the continuation wedge is *strictly*
decreasing in compliance, then every maximizer of the forward-looking Target
objective lies at or below every maximizer of the myopic one.

Rule 1: both `aM` and `aD` are argmaxes, supplied as `IsMaxOn` obligations; no
policy is posited. -/
theorem target_dynamic_complies_le_myopic_at_same_response
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {x aM aD : ℝ}
    (haM_mem : aM ∈ Sanctions.I) (haD_mem : aD ∈ Sanctions.I)
    (haM : IsMaxOn (fun a => p.U_T x a (ρ x a)) Sanctions.I aM)
    (haD : IsMaxOn
      (fun a => p.U_T x a (ρ x a)
                  + p.β_T * p.targetComplianceContinuation ρ V_T x a)
      Sanctions.I aD)
    (hβ_T_pos : 0 < p.β_T)
    (h_wedge_strictAnti : ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ →
      p.targetComplianceContinuation ρ V_T x a₂
        < p.targetComplianceContinuation ρ V_T x a₁) :
    aD ≤ aM := by
  by_contra hcon
  have hlt : aM < aD := lt_of_not_ge hcon
  -- the myopic objective cannot be higher at `aD`
  have hg : p.U_T x aD (ρ x aD) ≤ p.U_T x aM (ρ x aM) := haM haD_mem
  -- the wedge is strictly lower at `aD`
  have hh : p.targetComplianceContinuation ρ V_T x aD
              < p.targetComplianceContinuation ρ V_T x aM :=
    h_wedge_strictAnti aM haM_mem aD haD_mem hlt
  have hβh : p.β_T * p.targetComplianceContinuation ρ V_T x aD
               < p.β_T * p.targetComplianceContinuation ρ V_T x aM :=
    mul_lt_mul_of_pos_left hh hβ_T_pos
  -- so the forward-looking objective is strictly lower at `aD`, contradicting
  -- that `aD` maximizes it
  have hmax : p.U_T x aM (ρ x aM)
                + p.β_T * p.targetComplianceContinuation ρ V_T x aM
              ≤ p.U_T x aD (ρ x aD)
                + p.β_T * p.targetComplianceContinuation ρ V_T x aD :=
    haD haM_mem
  linarith

/-- **When the ordering is *strict*: the forward-looking Target complies
strictly less.**

`target_dynamic_complies_le_myopic_at_same_response` concludes `aD ≤ aM`, which
is consistent with the two Targets choosing the same action — so on its own it
does not show the reluctance channel is ever behaviourally active. It cannot: if
the myopic Target already sits at full defiance `aM = 0`, no wedge can push the
forward-looking one lower, and the conclusion is vacuously tight. Strictness
therefore needs a quantitative condition, and this is the weakest natural one.

**The condition, in words.** There is some smaller compliance level `a'` at
which the Target would give up less stage payoff than it would gain in
discounted continuation value:

  `U_T(x, aM, ρ(x,aM)) - U_T(x, a', ρ(x,a')) < β_T · (h(a') - h(aM))`

where `h` is the continuation wedge `targetComplianceContinuation`. The left
side is what the myopic Target pays to back off from `aM` to `a'`; the right
side is the political ground it thereby keeps. When the right side is bigger,
`aM` is not optimal for a Target that looks ahead, so the forward-looking
maximizer is strictly below it.

**Symbol economy (Rule 3).** The condition is a strict inequality among
quantities that already exist — the stage payoff, the discount factor, and the
continuation wedge. No margin constant is named, and the gap `aM - aD` is left
implicit rather than bounded below by a new scalar.

The conclusion holds for every maximizer of either objective; no uniqueness is
assumed anywhere. -/
theorem target_dynamic_complies_lt_myopic_at_same_response
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {x aM aD a' : ℝ}
    (haM_mem : aM ∈ Sanctions.I) (haD_mem : aD ∈ Sanctions.I)
    (ha'_mem : a' ∈ Sanctions.I)
    (haM : IsMaxOn (fun a => p.U_T x a (ρ x a)) Sanctions.I aM)
    (haD : IsMaxOn
      (fun a => p.U_T x a (ρ x a)
                  + p.β_T * p.targetComplianceContinuation ρ V_T x a)
      Sanctions.I aD)
    (hβ_T_pos : 0 < p.β_T)
    (h_wedge_strictAnti : ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ →
      p.targetComplianceContinuation ρ V_T x a₂
        < p.targetComplianceContinuation ρ V_T x a₁)
    (h_chord : p.U_T x aM (ρ x aM) - p.U_T x a' (ρ x a')
                 < p.β_T * (p.targetComplianceContinuation ρ V_T x a'
                            - p.targetComplianceContinuation ρ V_T x aM)) :
    aD < aM := by
  -- the weak ordering is already available
  have hle : aD ≤ aM :=
    p.target_dynamic_complies_le_myopic_at_same_response ρ V_T
      haM_mem haD_mem haM haD hβ_T_pos h_wedge_strictAnti
  -- `a'` strictly beats `aM` on the forward-looking objective ...
  have hbeat : p.U_T x aM (ρ x aM)
                 + p.β_T * p.targetComplianceContinuation ρ V_T x aM
               < p.U_T x a' (ρ x a')
                 + p.β_T * p.targetComplianceContinuation ρ V_T x a' := by
    have hexpand : p.β_T * (p.targetComplianceContinuation ρ V_T x a'
                            - p.targetComplianceContinuation ρ V_T x aM)
          = p.β_T * p.targetComplianceContinuation ρ V_T x a'
              - p.β_T * p.targetComplianceContinuation ρ V_T x aM := by ring
    rw [hexpand] at h_chord
    linarith
  -- ... and `aD` is at least as good as `a'`, so `aD` cannot be `aM`
  have hbest : p.U_T x a' (ρ x a')
                 + p.β_T * p.targetComplianceContinuation ρ V_T x a'
               ≤ p.U_T x aD (ρ x aD)
                 + p.β_T * p.targetComplianceContinuation ρ V_T x aD :=
    haD ha'_mem
  have hne : aD ≠ aM := by
    intro heq
    rw [heq] at hbest
    linarith
  exact lt_of_le_of_ne hle hne

/-- **The wedge falls in compliance, from the three sign primitives.**

Discharges `h_wedge_strictAnti` above:

* `hρ_anti` — compliance placates the Sender: more compliance, strictly fewer
  sanctions;
* `hF_mono` — sanctions build entrenchment: more sanctions, weakly higher next
  state;
* `hV_T_strictAnti_comp` — the incumbent values entrenchment, carried through the
  clip and the transition.

The third is stated on the composite rather than on `V_T` alone because
`clipS'` is not strictly monotone at the interval boundary, so strictness of
`V_T` alone would not survive the composition there. -/
theorem targetComplianceContinuation_strictAnti_of_placate
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (hρ_anti : ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ → ρ x a₂ < ρ x a₁)
    (hV_T_strictAnti_comp : ∀ s₁ s₂ : ℝ, s₂ < s₁ →
      V_T (Sanctions.clipS' (p.F x s₂)) < V_T (Sanctions.clipS' (p.F x s₁))) :
    ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ →
      p.targetComplianceContinuation ρ V_T x a₂
        < p.targetComplianceContinuation ρ V_T x a₁ := by
  intro a₁ h₁ a₂ h₂ hlt
  exact hV_T_strictAnti_comp (ρ x a₁) (ρ x a₂) (hρ_anti a₁ h₁ a₂ h₂ hlt)

/-- **Non-strict companion.** With only a weakly decreasing wedge the conclusion
weakens accordingly: a myopic maximizer is still a forward-looking maximizer, so
the forward-looking argmax set reaches down to it. This is the honest form when
compliance placates the Sender only weakly. -/
theorem myopic_argmax_is_dynamic_argmax_of_wedge_anti
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {x aM : ℝ}
    (haM : IsMaxOn (fun a => p.U_T x a (ρ x a)) Sanctions.I aM)
    (hβ_T_nn : 0 ≤ p.β_T)
    (h_wedge_anti : ∀ a ∈ Sanctions.I,
      p.targetComplianceContinuation ρ V_T x a
        ≤ p.targetComplianceContinuation ρ V_T x aM) :
    IsMaxOn
      (fun a => p.U_T x a (ρ x a)
                  + p.β_T * p.targetComplianceContinuation ρ V_T x a)
      Sanctions.I aM := by
  intro a ha
  have hg : p.U_T x a (ρ x a) ≤ p.U_T x aM (ρ x aM) := haM ha
  have hh : p.β_T * p.targetComplianceContinuation ρ V_T x a
              ≤ p.β_T * p.targetComplianceContinuation ρ V_T x aM :=
    mul_le_mul_of_nonneg_left (h_wedge_anti a ha) hβ_T_nn
  exact add_le_add hg hh

/-- **The wedge falls in compliance, from *separated* primitives.**

`targetComplianceContinuation_strictAnti_of_placate` above takes the composite

  `s₂ < s₁ → V_T(clip F(x,s₂)) < V_T(clip F(x,s₁))`,

which bundles three distinct economic facts into the conclusion it is wanted
for: that the transition is strictly increasing in the sanction, that the
incumbent's value is strictly increasing in the state, and that the clip is
inert on the successors actually reached. Bundling them makes the hypothesis
hard to audit — a supplier could satisfy it for reasons unrelated to any of the
three. This version separates them:

* `hρ_mem` — the Sender's response is a feasible sanction, so the successors
  reached are `F x s` for `s` in the state space;
* `hρ_anti` — **compliance placates**: more compliance, strictly fewer sanctions;
* `hF_strictMono_s` — **sanctions entrench, strictly**: on the feasible sanction
  range, a heavier sanction gives a strictly higher next state. Note this is a
  genuine strengthening of the `Params` field `F_mono_s`, which is only *weakly*
  monotone; strictness is what the strict conclusion needs and the baseline
  model does not supply it;
* `hV_T_strictMono` — **the incumbent values entrenchment, strictly**: on the
  state space, a higher political state is strictly better for the Target
  incumbent.

Feasibility of the successor is *not* a hypothesis: it is the existing `F_mem`
field, which is what makes the clip inert here rather than something that has to
be assumed away. That is why the composite above could be split at all. -/
theorem targetComplianceContinuation_strictAnti_of_separated_primitives
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ))
    (hρ_mem : ∀ a ∈ Sanctions.I, ρ x a ∈ (Sanctions.S : Set ℝ))
    (hρ_anti : ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ → ρ x a₂ < ρ x a₁)
    (hF_strictMono_s : ∀ s₁ ∈ (Sanctions.S : Set ℝ), ∀ s₂ ∈ (Sanctions.S : Set ℝ),
      s₁ < s₂ → p.F x s₁ < p.F x s₂)
    (hV_T_strictMono : ∀ y₁ ∈ (Sanctions.S : Set ℝ), ∀ y₂ ∈ (Sanctions.S : Set ℝ),
      y₁ < y₂ → V_T (Sanctions.clipS' y₁) < V_T (Sanctions.clipS' y₂)) :
    ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ →
      p.targetComplianceContinuation ρ V_T x a₂
        < p.targetComplianceContinuation ρ V_T x a₁ := by
  intro a₁ h₁ a₂ h₂ hlt
  have hm₁ : ρ x a₁ ∈ (Sanctions.S : Set ℝ) := hρ_mem a₁ h₁
  have hm₂ : ρ x a₂ ∈ (Sanctions.S : Set ℝ) := hρ_mem a₂ h₂
  -- compliance placates, so the higher action draws the lighter sanction
  have hs : ρ x a₂ < ρ x a₁ := hρ_anti a₁ h₁ a₂ h₂ hlt
  -- the lighter sanction leaves a strictly lower political state
  have hF : p.F x (ρ x a₂) < p.F x (ρ x a₁) :=
    hF_strictMono_s _ hm₂ _ hm₁ hs
  -- both successors are feasible, so the incumbent's strict state preference
  -- applies to them directly
  exact hV_T_strictMono _ (p.F_mem x (ρ x a₂) hx hm₂) _ (p.F_mem x (ρ x a₁) hx hm₁) hF

end Params
end AbstractGame
end Sanctions
