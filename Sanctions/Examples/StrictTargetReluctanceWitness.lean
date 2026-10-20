/-
Sanctions/Examples/StrictTargetReluctanceWitness.lean

**An economy where the forward-looking Target complies *strictly* less.**

Every Target-ordering theorem in this development concludes `≤`:
`target_dynamic_complies_le_myopic_at_same_response` at a common Sender
response, `alpha_order_dynamic_le_myopic_of_decreasingDifferences` and its
uniqueness-free strengthening at the two equilibria's own responses. All are
true, and none of them shows the reluctance channel is ever *active*: `aD ≤ aM`
is satisfied when the two Targets choose identically, so a model in which
looking ahead changes nothing at all satisfies the entire family.

**What already existed, and why this is not it.**
`NonAffineMechanismActiveWitness.lean` proves
`ma_target_continuation_changes_pivot_choice`: at a *constructed equilibrium*
over a non-affine transition, the Target's stage payoff strictly prefers `9/16`
to the equilibrium action `1/2`, so the continuation term is behaviourally
load-bearing rather than decorative. That is a strict statement and it is
stronger than this file in one respect — the dynamic action there is an
equilibrium argmax, produced by a solved Bellman fixed point, not a chosen one.

It is a different statement, though. It says the equilibrium action *fails* to
maximize the stage objective; it does not name the stage maximizer, so it does
not order the two argmaxes. The ordering theorems are about argmaxes, so what
witnesses their strictness is a pair of maximizers that are named and distinct.
That is what follows.

This file exhibits one economy, one state, and two maximizers that are provably
**distinct**:

* the myopic Target's optimal compliance is `3/4`;
* the forward-looking Target's optimal compliance is `2/3`;
* and `2/3 < 3/4`.

Rule 9A: this licenses *existence* — that the channel is active somewhere — and
nothing about genericity, magnitude, or necessity. It does not show reluctance
is typical, does not measure how large the gap usually is, and refutes no
universal.

## The economy

**Transition (non-affine).** `ratchetF` from `NonAffineCornerWitness.lean`,
already proved there to differ from `affineF δ` for *every* `δ`: it closes a
quarter of a downward state-sanction gap and half of an upward one, so its
chord rate in the sanction is `1/4` below the diagonal and `1/2` above. The five
`Params` transition obligations are reused from that file rather than restated.

This matters beyond tidiness. Rule 9B asks a witness for a class that
generalises a special case to sit *outside* that case, and the existing strict-
mechanism witnesses are affine. This one is not, so the strict Target ordering
is not an artefact of a linear reduced form.

**Sender.** `U_S(x,a,s) = -(s - (1 - clip a))²`, single-peaked in the sanction
with its peak at `1 - clip a`. The peak is always feasible, so the Sender's
stage argmax is exactly `σ(x,a) = 1 - clip a` — which is *derived* from `U_S`
through the `σ_isMaxOn_U_S` field, not posited (Rule 1). Compliance strictly
placates: every unit of compliance lowers the sanction the Sender most wants by
one unit.

**Target.** `U_T(x,a,s) = -(s - 1/4)²`, single-peaked in the sanction with ideal
point `1/4`. The Target incumbent is not simply sanction-averse: a little
pressure rallies its coalition and too much hurts. Facing `σ`, its myopic
objective is `-(3/4 - a)²`, peaking at `a = 3/4` — the compliance level that
delivers its ideal sanction `1/4`.

**Continuation.** `V_T` is the identity on the state space: the incumbent values
entrenchment, strictly and linearly. `β_T = 2/3`.

## Why the two differ

The myopic Target complies to `3/4` because that buys its ideal sanction level.
The forward-looking Target sees what the myopic one does not: the sanction it
induces is also the input to the transition, and a lighter sanction leaves it a
*weaker* political position next period. Backing off from `3/4` to `2/3` costs
it `1/144` in stage payoff and buys `1/48` of political ground, worth
`(2/3)·(1/48) = 1/72` — twice the cost. So it holds out, and `2/3` is where the
two margins balance.

At the state `x = 1/2` the objective is exactly

  `f(a) = -(3/4 - a)² + (2/3)·ratchetF(1/2, 1-a)`,

and the ratchet's kink at the diagonal splits `[0,1]` at `a = 1/2`. On the upper
piece `43/144 - f(a) = (a - 2/3)²`; on the lower piece
`43/144 - f(a) = (a - 7/12)² + 1/48`. Both are sums of squares, so `2/3` is the
maximizer and the verification is exact arithmetic — no numerical tolerance
anywhere.

The candidate was located in Python and snapped to rationals before any Lean was
written (Rule 9C); `docs/archive/workflow-scratch/strict_reluctance.py` records
the search, the exact re-verification, and a perturbation check showing the
strict gap survives `β_T` from `1/2` to `9/10` rather than being a knife edge.

## What this does NOT show

The comparison is at a **common** Sender response `σ`, so it witnesses the
hypotheses of `target_dynamic_complies_lt_myopic_at_same_response`, not of the
cross-response `alpha_order_dynamic_lt_myopic_of_strictDecreasingDifferences`.
It exhibits no equilibrium: neither Bellman fixed point is constructed here, and
`V_T` is a chosen strictly-increasing value function rather than a solved one.
For a strict statement at a *solved* equilibrium, use
`ma_target_continuation_changes_pivot_choice` instead — the two witnesses are
complementary, each stronger where the other is weaker, and neither shows that
two *equilibria of one economy* have different Target policies.
-/

import Sanctions.Examples.NonAffineCornerWitness
import Sanctions.Theory.LockIn.TargetReluctance
import Sanctions.Theory.Mechanism.ContinuationChangesChoice

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 1. The payoffs -/

/-- **Sender stage payoff.** Single-peaked in the sanction, peak at
`1 - clip a`: the more the Target complies, the lower the sanction the Sender
most wants. -/
def strU_S (_x a s : ℝ) : ℝ := -(s - (1 - Sanctions.clipS a)) ^ 2

/-- **The Sender's stage argmax.** Coupled to `strU_S` by the `σ_isMaxOn_U_S`
field below, so it is derived rather than posited (Rule 1). -/
def strσ (_x a : ℝ) : ℝ := 1 - Sanctions.clipS a

/-- **Target stage payoff.** Single-peaked in the sanction with ideal point
`1/4`: a little pressure rallies the incumbent's coalition, too much hurts. -/
def strU_T (_x _a s : ℝ) : ℝ := -(s - 1 / 4) ^ 2

/-- The ratchet is *strictly* increasing in the sanction. `F_mono_s` gives only
weak monotonicity, and the strict wedge needs strictness: the `s/4` term is
strictly increasing and the `max 0 (s-x)` term is monotone, so the sum is. -/
theorem ratchetF_strictMono_s (x : ℝ) {s t : ℝ} (h : s < t) :
    ratchetF x s < ratchetF x t := by
  unfold ratchetF
  have hm : max 0 (s - x) ≤ max 0 (t - x) := max_le_max le_rfl (by linarith)
  linarith

/-! ## 2. The witness economy -/

/-- **The strict-reluctance witness `Params`.** Non-affine ratchet transition,
single-peaked payoffs on both sides, `β_T = 2/3`. -/
def strictReluctanceParams : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 2 / 3
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1 / 2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := strU_T
  U_S := strU_S
  σ := strσ
  σ_mem := by
    intro _ a
    obtain ⟨h0, h1⟩ := Sanctions.clipS_mem a
    exact ⟨by show (0:ℝ) ≤ 1 - Sanctions.clipS a; linarith,
           by show (1:ℝ) - Sanctions.clipS a ≤ 1; linarith⟩
  σ_isMaxOn_U_S := by
    intro _ a s _
    show -(s - (1 - Sanctions.clipS a)) ^ 2
           ≤ -((1 - Sanctions.clipS a) - (1 - Sanctions.clipS a)) ^ 2
    nlinarith [sq_nonneg (s - (1 - Sanctions.clipS a))]
  U_T_continuous := by
    show Continuous (fun xas : ℝ × ℝ × ℝ => -(xas.2.2 - 1 / 4) ^ 2)
    fun_prop
  U_S_continuous := by
    show Continuous (fun xas : ℝ × ℝ × ℝ =>
      -(xas.2.2 - (1 - Sanctions.clipS xas.2.1)) ^ 2)
    have hc : Continuous (fun xas : ℝ × ℝ × ℝ => Sanctions.clipS xas.2.1) :=
      Sanctions.clipS_continuous.comp (continuous_fst.comp continuous_snd)
    exact ((((continuous_snd.comp continuous_snd).sub
      (continuous_const.sub hc))).pow 2).neg
  F := ratchetF
  F_continuous := ratchetF_continuous
  F_mono_x := ratchetF_mono_x
  F_mono_s := ratchetF_mono_s
  F_diag := ratchetF_diag

/-- **`strictReluctanceParams` has a continuous static Sender selector.** A concrete
member with the non-affine transition `ratchetF`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance strictReluctanceParams_staticSelectorContinuous :
    strictReluctanceParams.StaticSelectorContinuous where
  σ_continuous := by
    show Continuous (fun xa : ℝ × ℝ => 1 - Sanctions.clipS xa.2)
    exact continuous_const.sub (Sanctions.clipS_continuous.comp continuous_snd)

/-- **The Target's continuation value.** The identity on the state space: the
incumbent values entrenchment, strictly and linearly. -/
def strV_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun y => y.val, by fun_prop⟩

@[simp] theorem strV_T_apply (y : ↥(Sanctions.S : Set ℝ)) : strV_T y = y.val := rfl

/-- The witness transition is outside the affine family, for every `δ`. -/
theorem strictReluctanceParams_F_ne_affineF (δ : ℝ) :
    strictReluctanceParams.F ≠ AbstractGame.affineF δ :=
  ratchetF_ne_affineF δ

/-! ## 3. The objective, evaluated -/

/-- The clip is inert on the feasible interval. -/
private theorem clip_self {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Sanctions.clipS t = t := Sanctions.clipS'_val_eq_of_mem ht

/-- On `[0,1]` the Sender's response is literally `1 - a`. -/
theorem strσ_of_mem {a : ℝ} (ha : a ∈ Sanctions.I) :
    strictReluctanceParams.σ (1 / 2) a = 1 - a := by
  show 1 - Sanctions.clipS a = 1 - a
  rw [clip_self ha]

/-- The myopic Target objective at `x = 1/2` is `-(3/4 - a)²`. -/
theorem strMyopic_eq {a : ℝ} (ha : a ∈ Sanctions.I) :
    strictReluctanceParams.U_T (1 / 2) a (strictReluctanceParams.σ (1 / 2) a)
      = -(3 / 4 - a) ^ 2 := by
  rw [strσ_of_mem ha]
  show -((1 - a) - 1 / 4) ^ 2 = -(3 / 4 - a) ^ 2
  ring

/-- The continuation wedge at `x = 1/2` is the ratchet applied to the induced
sanction. The successor is feasible, so the clip does no work. -/
theorem strContinuation_eq {a : ℝ} (ha : a ∈ Sanctions.I) :
    strictReluctanceParams.targetComplianceContinuation
        strictReluctanceParams.σ strV_T (1 / 2) a
      = ratchetF (1 / 2) (1 - a) := by
  have hs : (1 - a) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hx : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem : ratchetF (1 / 2) (1 - a) ∈ Set.Icc (0 : ℝ) 1 :=
    ratchetF_mem _ _ hx hs
  show strV_T (Sanctions.clipS' (strictReluctanceParams.F (1 / 2)
    (strictReluctanceParams.σ (1 / 2) a))) = _
  rw [strσ_of_mem ha]
  show Sanctions.clipS (ratchetF (1 / 2) (1 - a)) = ratchetF (1 / 2) (1 - a)
  exact clip_self hmem

/-- Below the kink (`a ≤ 1/2`, so the induced sanction is above the diagonal)
the ratchet closes half the gap. -/
theorem strContinuation_lo {a : ℝ} (ha : a ∈ Sanctions.I) (h : a ≤ 1 / 2) :
    strictReluctanceParams.targetComplianceContinuation
        strictReluctanceParams.σ strV_T (1 / 2) a
      = 1 / 4 + (1 - a) / 2 := by
  rw [strContinuation_eq ha, ratchetF_of_ge (by linarith)]
  ring

/-- Above the kink (`a ≥ 1/2`, induced sanction below the diagonal) it closes a
quarter. -/
theorem strContinuation_hi {a : ℝ} (ha : a ∈ Sanctions.I) (h : 1 / 2 ≤ a) :
    strictReluctanceParams.targetComplianceContinuation
        strictReluctanceParams.σ strV_T (1 / 2) a
      = 3 / 8 + (1 - a) / 4 := by
  rw [strContinuation_eq ha, ratchetF_of_le (by linarith)]
  ring

/-- **The wedge strictly falls in compliance**, discharging the general
theorem's `h_wedge_strictAnti` hypothesis at this economy. Compliance strictly
placates the Sender, and the ratchet is strictly increasing in the sanction. -/
theorem strWedge_strictAnti :
    ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ →
      strictReluctanceParams.targetComplianceContinuation
          strictReluctanceParams.σ strV_T (1 / 2) a₂
        < strictReluctanceParams.targetComplianceContinuation
            strictReluctanceParams.σ strV_T (1 / 2) a₁ := by
  intro a₁ h₁ a₂ h₂ hlt
  rw [strContinuation_eq h₁, strContinuation_eq h₂]
  exact ratchetF_strictMono_s _ (by linarith)

/-! ## 4. The two maximizers, and that they differ -/

/-- **The myopic Target complies to `3/4`** — the compliance that delivers its
ideal sanction level `1/4`. -/
theorem strMyopic_isMaxOn :
    IsMaxOn
      (fun a => strictReluctanceParams.U_T (1 / 2) a
                  (strictReluctanceParams.σ (1 / 2) a))
      Sanctions.I (3 / 4) := by
  intro a ha
  have hM : (3 / 4 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  show strictReluctanceParams.U_T (1 / 2) a (strictReluctanceParams.σ (1 / 2) a)
         ≤ strictReluctanceParams.U_T (1 / 2) (3 / 4)
             (strictReluctanceParams.σ (1 / 2) (3 / 4))
  rw [strMyopic_eq ha, strMyopic_eq hM]
  nlinarith [sq_nonneg (3 / 4 - a)]

/-- **The forward-looking Target complies only to `2/3`.**

The verification is exact: on the upper piece of the ratchet
`43/144 - f(a) = (a - 2/3)²`, and on the lower piece
`43/144 - f(a) = (a - 7/12)² + 1/48`. Both are nonnegative, so `2/3` attains the
maximum value `43/144`. -/
theorem strDynamic_isMaxOn :
    IsMaxOn
      (fun a => strictReluctanceParams.U_T (1 / 2) a
                  (strictReluctanceParams.σ (1 / 2) a)
                + strictReluctanceParams.β_T *
                    strictReluctanceParams.targetComplianceContinuation
                      strictReluctanceParams.σ strV_T (1 / 2) a)
      Sanctions.I (2 / 3) := by
  have hD : (2 / 3 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hβ : strictReluctanceParams.β_T = 2 / 3 := rfl
  have hpeak :
      strictReluctanceParams.U_T (1 / 2) (2 / 3)
          (strictReluctanceParams.σ (1 / 2) (2 / 3))
        + strictReluctanceParams.β_T *
            strictReluctanceParams.targetComplianceContinuation
              strictReluctanceParams.σ strV_T (1 / 2) (2 / 3)
      = 43 / 144 := by
    rw [strMyopic_eq hD, strContinuation_hi hD (by norm_num), hβ]
    norm_num
  intro a ha
  show strictReluctanceParams.U_T (1 / 2) a (strictReluctanceParams.σ (1 / 2) a)
         + strictReluctanceParams.β_T *
             strictReluctanceParams.targetComplianceContinuation
               strictReluctanceParams.σ strV_T (1 / 2) a
       ≤ strictReluctanceParams.U_T (1 / 2) (2 / 3)
           (strictReluctanceParams.σ (1 / 2) (2 / 3))
         + strictReluctanceParams.β_T *
             strictReluctanceParams.targetComplianceContinuation
               strictReluctanceParams.σ strV_T (1 / 2) (2 / 3)
  rw [hpeak, strMyopic_eq ha, hβ]
  rcases le_or_gt a (1 / 2) with h | h
  · -- induced sanction above the diagonal: the ratchet closes half the gap
    rw [strContinuation_lo ha h]
    nlinarith [sq_nonneg (a - 7 / 12)]
  · -- induced sanction below the diagonal: it closes a quarter
    rw [strContinuation_hi ha (le_of_lt h)]
    nlinarith [sq_nonneg (a - 2 / 3)]

/-- **The chord condition of the general strictness theorem holds here**, at
`a' = 2/3`: backing off from `3/4` costs `1/144` in stage payoff and buys
`1/48` of political ground, worth `(2/3)·(1/48) = 1/72` — twice the cost. -/
theorem strChord :
    strictReluctanceParams.U_T (1 / 2) (3 / 4)
        (strictReluctanceParams.σ (1 / 2) (3 / 4))
      - strictReluctanceParams.U_T (1 / 2) (2 / 3)
          (strictReluctanceParams.σ (1 / 2) (2 / 3))
    < strictReluctanceParams.β_T *
        (strictReluctanceParams.targetComplianceContinuation
            strictReluctanceParams.σ strV_T (1 / 2) (2 / 3)
          - strictReluctanceParams.targetComplianceContinuation
              strictReluctanceParams.σ strV_T (1 / 2) (3 / 4)) := by
  have hM : (3 / 4 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hD : (2 / 3 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  rw [strMyopic_eq hM, strMyopic_eq hD,
    strContinuation_hi hD (by norm_num), strContinuation_hi hM (by norm_num)]
  show _ < (2 / 3 : ℝ) * _
  norm_num

/-- **The strict ordering, as a one-line corollary of the general theorem**
(Rule 5). Every hypothesis of
`target_dynamic_complies_lt_myopic_at_same_response` is discharged above, so
this instantiation also serves as the Rule-9B joint-satisfiability check: the
hypothesis bundle is not contradictory, because this economy satisfies all of
it at once. -/
theorem strictReluctance_strict_ordering : (2 : ℝ) / 3 < 3 / 4 :=
  strictReluctanceParams.target_dynamic_complies_lt_myopic_at_same_response
    strictReluctanceParams.σ strV_T
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
    strMyopic_isMaxOn strDynamic_isMaxOn
    (by show (0 : ℝ) < 2 / 3; norm_num)
    strWedge_strictAnti strChord

/-- **The witness, assembled.** One economy, one state, two provably distinct
optimal compliance levels, over a transition that is not affine for any `δ`.

Rule 9A: existence only. It shows the Target-reluctance channel is active
somewhere; it says nothing about how often, how large, or whether it must be. -/
theorem strictTargetReluctance_witness :
    (∀ δ : ℝ, strictReluctanceParams.F ≠ AbstractGame.affineF δ)
    ∧ IsMaxOn
        (fun a => strictReluctanceParams.U_T (1 / 2) a
                    (strictReluctanceParams.σ (1 / 2) a))
        Sanctions.I (3 / 4)
    ∧ IsMaxOn
        (fun a => strictReluctanceParams.U_T (1 / 2) a
                    (strictReluctanceParams.σ (1 / 2) a)
                  + strictReluctanceParams.β_T *
                      strictReluctanceParams.targetComplianceContinuation
                        strictReluctanceParams.σ strV_T (1 / 2) a)
        Sanctions.I (2 / 3)
    ∧ (2 : ℝ) / 3 < 3 / 4 :=
  ⟨strictReluctanceParams_F_ne_affineF, strMyopic_isMaxOn, strDynamic_isMaxOn,
    by norm_num⟩


/-! ## The strict ordering, in the named vocabulary (Rule 5)

`strictReluctance_strict_ordering` concludes `2/3 < 3/4` — the specific
forward-looking maximizer below the specific stage maximizer. The universal
predicate wants it for *every* pair, which needs only that the stage maximizer
is unique (it is: `strMyopic_eq` makes the stage objective `−(3/4 − a)²`).
Then the general theorem, at that one stage maximizer, delivers the ordering
against every forward-looking maximizer at once. -/

/-- **The stage argmax at `x = 1/2` is unique, and it is `3/4`.** -/
theorem str_stage_isMaxOn_eq {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn
      (fun b => strictReluctanceParams.U_T (1 / 2) b (strictReluctanceParams.σ (1 / 2) b))
      Sanctions.I a) : a = 3 / 4 := by
  have h34 : (3 / 4 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have h := hmax h34
  simp only [Set.mem_setOf_eq] at h
  rw [strMyopic_eq h34, strMyopic_eq ha] at h
  have hsq : (3 / 4 - a) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  linarith [(pow_eq_zero_iff two_ne_zero).mp hsq]

/-- **The continuation changes the Target's optimal compliance at `x = 1/2`.**
The named form of the strict reluctance witness. -/
theorem strictReluctance_continuationChangesTargetChoice :
    strictReluctanceParams.ContinuationChangesTargetChoiceAt
      strictReluctanceParams.σ strV_T (1 / 2) := by
  apply AbstractGame.Params.continuationChangesTargetChoiceAt_of_strict_ordering
  intro aM haM aD haD hstage hdyn
  rw [str_stage_isMaxOn_eq haM hstage]
  exact strictReluctanceParams.target_dynamic_complies_lt_myopic_at_same_response
    strictReluctanceParams.σ strV_T
    ⟨by norm_num, by norm_num⟩ haD ⟨by norm_num, by norm_num⟩
    strMyopic_isMaxOn hdyn
    (by show (0 : ℝ) < 2 / 3; norm_num)
    strWedge_strictAnti strChord

#print axioms strictReluctance_continuationChangesTargetChoice

end

end Examples
end Sanctions
