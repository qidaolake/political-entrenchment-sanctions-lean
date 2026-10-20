/-
Sanctions/Theory/LockIn/SenderInvestment.lean

**The Sender-investment channel: a forward-looking Sender sanctions strictly
harder.**

This is the Sender-side mirror of `Theory/LockIn/TargetReluctance.lean`, and it
exists to close the same gap on this player. The ladder on the Target side runs
weak → strict → from-primitives:

    target_dynamic_complies_le_myopic_at_same_response
    target_dynamic_complies_lt_myopic_at_same_response
    targetComplianceContinuation_strictAnti_of_separated_primitives

The Sender side had the weak rung — `theorem2_dynamic_dominates_myopic_at_same_alpha`
(pinned row 4) and its local forms in `TwoSidedForwardLooking.lean` §9–§10 — and
had the *interiority* rung (`OffCornerResponse.lean`), but not the strict rung
over the stage argmax. Every `<` in the tree comparing the dynamic sanction to
the stage sanction was either at a single economy (`ce_wedge`, exactly `1/8`) or
consumed as a hypothesis (`hRuleDom` in `DifferentPolicyComparator.lean`). The
2026-09-02 JET readiness audit asked, in §3.5, whether the continuation term
ever *changes an optimal action*; on the Sender side that was a theorem nobody
had stated.

**What is proved here.** At a common Target action, every maximizer of the
Sender's forward-looking objective lies at or above every maximizer of its stage
objective (weak), and strictly above (strict) under a chord condition. Written
out, with `a` the Target's action:

* stage             `f(s) = U_S(x, a, s)`
* forward-looking   `g(s) = U_S(x, a, s) + β_S · V_S(clip(F(x, s)))`

so `g = f + β_S·W`, where `W` is the discounted-away continuation value the
Sender gets from the political state its own sanction induces.

**The economics, and why the sign comes out this way.** Sanctions build
entrenchment, so `F(x, ·)` rises in `s`. A Sender who values entrenchment — the
lock-in regime — has `V_S` rising in the state. Composing the two, `W` *rises*
in `s`: every unit of sanction the Sender applies buys it political ground it
wanted. The myopic Sender does not see that gain and the forward-looking one
does, so the forward-looking Sender sanctions harder. Investment is not assumed;
it is what a Sender that values entrenchment does once it looks ahead.

**The argument is elementary and needs no concavity.** The weak step is a
two-line instance of `Sanctions.BinaryComparativeStatics.argmax_le_of_strictSCLowerOn`: `f − g = −β_S·W`
is strictly decreasing, so `f` is strict-single-crossing-lower than `g`, and every
`f`-maximizer sits weakly below every `g`-maximizer. The strict step is
`Sanctions.BinaryComparativeStatics.lt_argmax_of_improves_above` with the stage maximizer as the
reference point: nothing at or below it beats it on `g` (stage optimality plus
the rising wedge), and the chord supplies one point above it that does.
No Topkis, no differentiability, no uniqueness anywhere, and the conclusion
holds for *every* pair of maximizers, which is the selection-robust form.

**Symbol economy (Rule 3).** The chord condition is a strict inequality among
quantities that already exist — the stage payoff, the discount factor, and the
continuation wedge. No margin constant is named, and the gap `sD − sM` is left
implicit rather than bounded below by a new scalar. This is the form
`TargetReluctance.lean` already argued for, on the other player.

**Scope — what this does and does not close.** It supplies the Sender-policy
ordering from primitives, at a common Target action. Combined with the Target
side it says both continuation channels are behaviourally live — see
`Theory/Mechanism/ContinuationChangesChoice.lean` for the named predicate. It
does *not* deliver interiority (that is `OffCornerResponse.lean`, and a strict
wedge is consistent with both sanctions sitting at corners), and it does not
deliver the cross-policy equilibrium comparison, which still runs through
`hRuleDom`.

General in the transition: `F` enters only through the hypotheses, and `p.δ`
is never read.
-/

import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Foundations.BinaryComparativeStatics
import Sanctions.Foundations.BalbusReffettWozny

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

variable (p : Sanctions.AbstractGame.Params)

/-- **The Sender's continuation term, as a function of its own sanction.** The
value of the political state that sanction `s` induces from `x`. This is the
exact mirror of `targetComplianceContinuation`, and equals
`TwoSidedForwardLooking.senderContinuationTerm` with the `β_S` factored out. -/
noncomputable def senderSanctionContinuation
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x s : ℝ) : ℝ :=
  V_S (Sanctions.clipS' (p.F x s))

/-- **A forward-looking Sender sanctions no less than a myopic one.**

At a common Target action `a`, if the continuation wedge is *strictly*
increasing in the sanction, then every maximizer of the forward-looking Sender
objective lies at or above every maximizer of the stage one.

Rule 1: both `sM` and `sD` are argmaxes, supplied as `IsMaxOn` obligations; no
policy is posited. -/
theorem sender_dynamic_sanctions_ge_myopic_at_same_action
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a sM sD : ℝ}
    (hsM_mem : sM ∈ Sanctions.I) (hsD_mem : sD ∈ Sanctions.I)
    (hsM : IsMaxOn (fun s => p.U_S x a s) Sanctions.I sM)
    (hsD : IsMaxOn
      (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s)
      Sanctions.I sD)
    (hβ_S_pos : 0 < p.β_S)
    (h_wedge_strictMono : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      p.senderSanctionContinuation V_S x s₁
        < p.senderSanctionContinuation V_S x s₂) :
    sM ≤ sD := by
  refine Sanctions.BinaryComparativeStatics.argmax_le_of_strictSCLowerOn ?_ hsM_mem hsD_mem hsM hsD
  apply Sanctions.BinaryComparativeStatics.strictSCLowerOn_of_gap_strictAnti
  intro s₁ h₁ s₂ h₂ hlt
  have hW := h_wedge_strictMono s₁ h₁ s₂ h₂ hlt
  have hβW := mul_lt_mul_of_pos_left hW hβ_S_pos
  linarith

/-- **When the ordering is *strict*: the forward-looking Sender sanctions
strictly harder.**

`sender_dynamic_sanctions_ge_myopic_at_same_action` concludes `sM ≤ sD`, which is
consistent with the two Senders choosing the same sanction — so on its own it
does not show the investment channel is ever behaviourally active. It cannot: if
the myopic Sender already sits at maximum pressure `sM = 1`, no wedge can push
the forward-looking one higher, and the conclusion is vacuously tight.
Strictness therefore needs a quantitative condition, and this is the weakest
natural one.

**The condition, in words.** There is some larger sanction `s'` at which the
Sender would give up less stage payoff than it would gain in discounted
continuation value:

  `U_S(x, a, sM) − U_S(x, a, s') < β_S · (W(s') − W(sM))`

where `W` is the continuation wedge `senderSanctionContinuation`. The left side
is what the myopic Sender pays to escalate from `sM` to `s'`; the right side is
the political ground it thereby gains. When the right side is bigger, `sM` is
not optimal for a Sender that looks ahead, so the forward-looking maximizer is
strictly above it.

The conclusion holds for every maximizer of either objective; no uniqueness is
assumed anywhere. -/
theorem sender_dynamic_sanctions_gt_myopic_at_same_action
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a sM sD s' : ℝ}
    (hsM_mem : sM ∈ Sanctions.I) (hsD_mem : sD ∈ Sanctions.I)
    (hs'_mem : s' ∈ Sanctions.I)
    (hsM : IsMaxOn (fun s => p.U_S x a s) Sanctions.I sM)
    (hsD : IsMaxOn
      (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s)
      Sanctions.I sD)
    (hβ_S_pos : 0 < p.β_S)
    (h_wedge_strictMono : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      p.senderSanctionContinuation V_S x s₁
        < p.senderSanctionContinuation V_S x s₂)
    (h_chord : p.U_S x a sM - p.U_S x a s'
                 < p.β_S * (p.senderSanctionContinuation V_S x s'
                            - p.senderSanctionContinuation V_S x sM)) :
    sM < sD := by
  -- `s'` strictly beats `sM` on the forward-looking objective
  have hbeat :
      p.U_S x a sM + p.β_S * p.senderSanctionContinuation V_S x sM
        < p.U_S x a s' + p.β_S * p.senderSanctionContinuation V_S x s' := by
    have hexpand : p.β_S * (p.senderSanctionContinuation V_S x s'
                            - p.senderSanctionContinuation V_S x sM)
        = p.β_S * p.senderSanctionContinuation V_S x s'
          - p.β_S * p.senderSanctionContinuation V_S x sM := by ring
    linarith
  -- and nothing at or below `sM` beats `sM` on it: stage optimality supplies the
  -- stage half, the rising wedge supplies the continuation half
  refine Sanctions.BinaryComparativeStatics.lt_argmax_of_improves_above ?_ hs'_mem hbeat hsD_mem hsD
  intro s hs hle
  have hstage : p.U_S x a s ≤ p.U_S x a sM := hsM hs
  rcases hle.lt_or_eq with hlt | heq
  · have hW := h_wedge_strictMono s hs sM hsM_mem hlt
    have hβW := mul_lt_mul_of_pos_left hW hβ_S_pos
    linarith
  · rw [heq]

/-- **At the greatest dynamic selector.** The strict wedge, read at the selector
the persistence machinery uses: `σ` (the stage argmax) sits strictly below
`σ_dyn_top` (the greatest forward-looking argmax). -/
theorem sigma_lt_sigma_dyn_top_of_wedge_and_chord
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a s' : ℝ}
    (hs'_mem : s' ∈ Sanctions.I)
    (hβ_S_pos : 0 < p.β_S)
    (h_wedge_strictMono : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      p.senderSanctionContinuation V_S x s₁
        < p.senderSanctionContinuation V_S x s₂)
    (h_chord : p.U_S x a (p.σ x a) - p.U_S x a s'
                 < p.β_S * (p.senderSanctionContinuation V_S x s'
                            - p.senderSanctionContinuation V_S x (p.σ x a))) :
    p.σ x a < p.σ_dyn_top V_S x a :=
  p.sender_dynamic_sanctions_gt_myopic_at_same_action V_S
    (p.σ_mem x a) (p.σ_dyn_top_mem_I V_S x a) hs'_mem
    (p.σ_isMaxOn_U_S x a) (p.σ_dyn_top_isMaxOn V_S x a)
    hβ_S_pos h_wedge_strictMono h_chord

/-! ## The wedge from separated primitives

The strict-increase hypothesis above is stated on the composite `W`. Here it is
derived from the two factors it is built from — exactly as
`targetComplianceContinuation_strictAnti_of_separated_primitives` does on the
Target side, and one composition shorter, because the Sender's own sanction
enters `F` directly rather than through the opponent's response. -/

/-- **The Sender continuation wedge is strictly increasing, from primitives.**

Sanctions build entrenchment (`F` strictly increasing in `s`), and the Sender
values entrenchment (`V_S` strictly increasing in the state). Feasibility of the
successor is the existing `F_mem` field, which is what makes the clip inert. -/
theorem senderSanctionContinuation_strictMono_of_separated_primitives
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ))
    (hF_strictMono_s : ∀ s₁ ∈ (Sanctions.S : Set ℝ), ∀ s₂ ∈ (Sanctions.S : Set ℝ),
      s₁ < s₂ → p.F x s₁ < p.F x s₂)
    (hV_S_strictMono : ∀ y₁ ∈ (Sanctions.S : Set ℝ), ∀ y₂ ∈ (Sanctions.S : Set ℝ),
      y₁ < y₂ → V_S (Sanctions.clipS' y₁) < V_S (Sanctions.clipS' y₂)) :
    ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      p.senderSanctionContinuation V_S x s₁
        < p.senderSanctionContinuation V_S x s₂ := by
  intro s₁ h₁ s₂ h₂ hlt
  -- the heavier sanction leaves a strictly higher political state
  have hF : p.F x s₁ < p.F x s₂ := hF_strictMono_s _ h₁ _ h₂ hlt
  -- both successors are feasible, so the Sender's strict state preference
  -- applies to them directly
  exact hV_S_strictMono _ (p.F_mem x s₁ hx h₁) _ (p.F_mem x s₂ hx h₂) hF

/-! ## The correctly quantified strict comparison (doc 68, L1)

`sender_dynamic_sanctions_gt_myopic_at_same_action` orders the *supplied* stage
maximiser `sM` below every forward-looking maximiser, given a chord improvement
measured from that `sM`. It does **not** order every stage maximiser: a chord
at a low tied stage optimum says nothing about a higher one (the regression
`Examples/Counterexamples/TiedStageMaximizers.lean` exhibits stage maximisers
`{0, 1}`, a chord at `0`, and the unique dynamic maximiser `1`). The
all-maximiser statement holds once the chord is measured from the **greatest**
stage maximiser, which exists on the compact action set by continuity. -/

/-- **A greatest stage maximiser exists.** -/
theorem exists_greatest_stage_maximizer (x a : ℝ) :
    ∃ m ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I m ∧
      ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ m := by
  have hc : Continuous (fun s => p.U_S x a s) :=
    p.U_S_continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  exact Sanctions.Foundations.BalbusReffettWozny.exists_isGreatest_argmax_of_continuous
    isCompact_Icc ⟨0, by simp [Sanctions.I]⟩ hc.continuousOn

/-- **Strict dominance from one wedge comparison per lower sanction** (round
BH-2, 2026-10-06, plan item BH2.8). Every stage maximiser lies strictly below
every forward-looking maximiser, given only:

* `m` is a stage maximiser and every stage maximiser in `I` lies at or below it;
* the continuation wedge at any feasible sanction `d ≤ m` is at most its value
  at `m`, `W(d) ≤ W(m)` — one comparison against `m` per lower sanction;
* one feasible sanction `s'` at which the discounted continuation gain
  outweighs the stage loss measured from `m` (the chord).

In plain terms: if no sanction at or below the greatest stage optimum promises
the Sender a better continuation than that optimum itself, and one heavier
sanction pays for its stage cost through the continuation, then looking ahead
moves every Sender best response strictly above every myopic one.

The proof: if a forward-looking maximiser `d` lay at or below `m`, stage
maximality of `m` and `W(d) ≤ W(m)` would give `J(d) ≤ J(m)`, while the chord
gives `J(m) < J(s')`, contradicting the optimality of `d`. The discount enters
only through `0 ≤ β_S`, which `Params` supplies.

Dropped relative to `all_stage_lt_dynamic_of_greatest_stage_improvement_mono`:
the wedge need not be monotone on all pairs of sanctions (only pairs `(d, m)`
with `d ≤ m` are compared), and `m ∈ I` is not assumed (`IsMaxOn` needs no
membership of `m`, and the old binder was read only to apply monotonicity at
`m`). Relative to the strict root it also drops `0 < β_S` and strictness of the
wedge. General in `F`: the transition enters only through the wedge `W`, and
`p.δ` is never read. -/
theorem all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a m s' : ℝ}
    (hs'_mem : s' ∈ Sanctions.I)
    (hm_max : IsMaxOn (fun s => p.U_S x a s) Sanctions.I m)
    (hm_greatest : ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ m)
    (h_wedge_le : ∀ d ∈ Sanctions.I, d ≤ m →
      p.senderSanctionContinuation V_S x d ≤ p.senderSanctionContinuation V_S x m)
    (h_chord : p.U_S x a m - p.U_S x a s'
                 < p.β_S * (p.senderSanctionContinuation V_S x s'
                            - p.senderSanctionContinuation V_S x m)) :
    ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t →
      ∀ d ∈ Sanctions.I,
        IsMaxOn (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s)
          Sanctions.I d → t < d := by
  intro t ht htmax d hd hdmax
  by_contra hnot
  have hdm : d ≤ m := (not_lt.mp hnot).trans (hm_greatest t ht htmax)
  have hβ : 0 ≤ p.β_S := p.β_S_mem.1
  have hU : p.U_S x a d ≤ p.U_S x a m := hm_max hd
  have hC : p.senderSanctionContinuation V_S x d ≤ p.senderSanctionContinuation V_S x m :=
    h_wedge_le d hd hdm
  have hs' : p.U_S x a s' + p.β_S * p.senderSanctionContinuation V_S x s'
      ≤ p.U_S x a d + p.β_S * p.senderSanctionContinuation V_S x d := hdmax hs'_mem
  linarith [mul_le_mul_of_nonneg_left hC hβ]

/-- **Every stage maximiser lies strictly below every forward-looking
maximiser**, given a strictly increasing continuation wedge and one sanction `s'`
at which the discounted continuation gain outweighs the stage loss measured from
the **greatest** stage maximiser `m`. No concavity, no uniqueness.

Since round BH-2 (2026-10-06, BH2.8) this is a one-line corollary of
`all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le`: a strictly
increasing wedge gives `W(d) ≤ W(m)` for every feasible `d ≤ m`. Neither the
strictness nor the positive discount is used, so the latter binder is now
`_hβ_S_pos`; the statement is unchanged (it is a manuscript root and a pinned
evidence row). General in `F`. -/
theorem all_stage_lt_dynamic_of_greatest_stage_improvement
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a m s' : ℝ}
    (hm_mem : m ∈ Sanctions.I) (hs'_mem : s' ∈ Sanctions.I)
    (hm_max : IsMaxOn (fun s => p.U_S x a s) Sanctions.I m)
    (hm_greatest : ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ m)
    (_hβ_S_pos : 0 < p.β_S)
    (h_wedge_strictMono : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      p.senderSanctionContinuation V_S x s₁
        < p.senderSanctionContinuation V_S x s₂)
    (h_chord : p.U_S x a m - p.U_S x a s'
                 < p.β_S * (p.senderSanctionContinuation V_S x s'
                            - p.senderSanctionContinuation V_S x m)) :
    ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t →
      ∀ d ∈ Sanctions.I,
        IsMaxOn (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s)
          Sanctions.I d → t < d :=
  p.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le V_S hs'_mem hm_max
    hm_greatest (fun _ hd hdm => (show StrictMonoOn (p.senderSanctionContinuation V_S x)
      Sanctions.I from h_wedge_strictMono).monotoneOn hd hm_mem hdm) h_chord

/-- **Strict dominance from a nondecreasing wedge** (round L, doc 80 M8; the
reader's round-K validation package, document 03 §2): the conclusion of
`all_stage_lt_dynamic_of_greatest_stage_improvement` needs neither a strictly
increasing continuation nor a positive Sender discount. If a forward-looking
maximiser `d` lay at or below the greatest stage maximiser `m`, stage maximality
of `m` and a nondecreasing wedge would give `J(d) ≤ J(m)`, while the profitable
chord gives `J(m) < J(s')`, contradicting the optimality of `d`. The discount
enters only through `0 ≤ β_S`, which `Params` supplies. The parent theorem keeps
its statement (it is a manuscript root).

Since round BH-2 (2026-10-06, BH2.8) a one-line corollary of
`all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le`, which reads
the wedge only at pairs `(d, m)` with `d ≤ m`. Statement unchanged (pinned
evidence row). General in `F`. -/
theorem all_stage_lt_dynamic_of_greatest_stage_improvement_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a m s' : ℝ}
    (hm_mem : m ∈ Sanctions.I) (hs'_mem : s' ∈ Sanctions.I)
    (hm_max : IsMaxOn (fun s => p.U_S x a s) Sanctions.I m)
    (hm_greatest : ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ m)
    (h_wedge_mono : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      p.senderSanctionContinuation V_S x s₁
        ≤ p.senderSanctionContinuation V_S x s₂)
    (h_chord : p.U_S x a m - p.U_S x a s'
                 < p.β_S * (p.senderSanctionContinuation V_S x s'
                            - p.senderSanctionContinuation V_S x m)) :
    ∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t →
      ∀ d ∈ Sanctions.I,
        IsMaxOn (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s)
          Sanctions.I d → t < d :=
  p.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le V_S hs'_mem hm_max
    hm_greatest (fun d hd hdm => h_wedge_mono d hd m hm_mem hdm) h_chord

end Params
end AbstractGame
end Sanctions
