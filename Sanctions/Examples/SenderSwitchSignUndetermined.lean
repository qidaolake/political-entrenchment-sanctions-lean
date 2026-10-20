/-
Sanctions/Examples/SenderSwitchSignUndetermined.lean

**The Sender-response-switch channel's sign is not determined by the sign
conditions (Rule-11 refutation).**

When the Target's compliance choice is compared between the fully
forward-looking regime and the fully myopic one, the gap between the two
objectives splits into two channels:

* the **Target-continuation** channel — the incumbent values the political state
  its compliance leads to; and
* the **Sender-response-switch** channel — the Target faces the forward-looking
  Sender response `d` rather than the static one `m`, and those are different
  sanctions.

The first channel is signed by the model's primitives: compliance placates, a
lower sanction erodes entrenchment, and the incumbent values entrenchment. The
natural expectation is that the second channel is signed too, since the same
primitives say both responses fall in compliance and the forward-looking Sender
sanctions at least as hard as the static one.

**That expectation is false, and this file refutes it.**

## The claim under test

Let `Q x (a, s)` be the Target's complete payoff from complying `a` and being
sanctioned `s`, and write the switch channel as

    S(a) = Q(a, d(a)) - Q(a, m(a)).

The claim is that the following four facts force `S` to be non-increasing:

1. the static response `m` strictly falls in compliance;
2. the forward-looking response `d` strictly falls in compliance;
3. the forward-looking response is at least the static one, `m ≤ d`;
4. the Target's payoff is non-decreasing in the sanction.

`senderSwitch_sign_not_determined` below shows the claim is false. The witness
is as simple as it can be: `Q(a,s) = s`, `m(a) = 1 - 2a`, `d(a) = 1 - a` on
`a ∈ [0, 1/2]`. All four hypotheses hold, and yet

    S(a) = d(a) - m(a) = a,

which strictly *rises*. Both responses fall, but the static one falls twice as
fast, so the gap between them widens as the Target complies — and it is the
gap, not the level, that the switch channel sees.

## What this settles, and what it does not

It settles that no theorem can derive the cross-response compliance ordering
from these sign conditions alone: an additional condition on response-gap
geometry, or on the curvature of the Target's sanction payoff, is *logically*
required rather than merely convenient. Under Rule 3 that makes such a condition
a legitimate new assumption instead of a gap being papered over, and this file is
the justification the Rule-3 stop is supposed to carry.

It does **not** claim that the ordering fails in the sanctions model, that no
economy satisfies the ordering, or that the two channels cannot both be signed
in a particular economy. It is a statement about what the *listed hypotheses*
entail, which is exactly Rule 11's disprove-before-prove step: the universal is
refuted, so the proof attempt is abandoned rather than continued.

The refutation is stated over abstract `Q`, `m`, `d` rather than at a `Params`,
because that is the level the claim is about — it uses no field of the game, and
adding one would narrow the result without strengthening it. It sits in
`Examples/` rather than `Foundations/` because it fixes functional forms, which
Rule 19 keeps out of the theory layers; `SignConditionsInsufficient.lean` is in
this directory for the same reason and refutes a different claim (that the sign
conditions imply perpetual sanctions).
-/

import Sanctions.Foundations.BinaryComparativeStatics
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

namespace Sanctions
namespace Examples

open Set

/-! ## The switch channel

The notion itself is `Sanctions.BinaryComparativeStatics.switchWedge`, in
`Foundations/` — it mentions no field of the sanctions game (Rule 19). Only the
counterexample, which fixes functional forms, belongs here. -/

open Sanctions.BinaryComparativeStatics

/-! ## The witness -/

/-- Target payoff: the incumbent's complete payoff is the sanction itself, so it
is non-decreasing in the sanction and has no curvature to hide anything in. -/
def cxQ : ℝ → ℝ → ℝ := fun _ s => s

/-- Static Sender response: falls in compliance, at rate 2. -/
def cxM : ℝ → ℝ := fun a => 1 - 2 * a

/-- Forward-looking Sender response: falls in compliance, at rate 1. Always at
least the static response on the region below. -/
def cxD : ℝ → ℝ := fun a => 1 - a

/-- The compliance region. -/
def cxA : Set ℝ := Icc 0 (1 / 2)

/-- Hypothesis 1: the static response strictly falls in compliance. -/
theorem cxM_strictAntiOn : StrictAntiOn cxM cxA := by
  intro a _ b _ hab
  simp only [cxM]
  linarith

/-- Hypothesis 2: the forward-looking response strictly falls in compliance. -/
theorem cxD_strictAntiOn : StrictAntiOn cxD cxA := by
  intro a _ b _ hab
  simp only [cxD]
  linarith

/-- Hypothesis 3: the forward-looking Sender sanctions at least as hard as the
static one, everywhere on the region. -/
theorem cxM_le_cxD : ∀ a ∈ cxA, cxM a ≤ cxD a := by
  rintro a ⟨ha0, _⟩
  simp only [cxM, cxD]
  linarith

/-- Hypothesis 4: the Target's payoff is non-decreasing in the sanction. -/
theorem cxQ_monotone_in_sanction : ∀ a : ℝ, Monotone (cxQ a) := by
  intro a s t hst
  exact hst

/-- The switch wedge at this witness is the identity: it strictly **rises** in
compliance. Both responses fall, but the static one falls twice as fast, so the
gap between them widens. -/
theorem cx_senderSwitch_eq (a : ℝ) : switchWedge cxQ cxM cxD a = a := by
  simp only [switchWedge, cxQ, cxM, cxD]
  ring

/-! ## The refutation -/

/-- **The four sign conditions do not determine the switch channel's sign.**

Every hypothesis holds at the witness and the conclusion fails, so the universal
is false. Rule 11: this is a definitive refutation, not an inconclusive proof
attempt, and it is what makes an extra response-gap or curvature condition a
*logically required* addition rather than a convenience. -/
theorem senderSwitch_sign_not_determined :
    ¬ ∀ (Q : ℝ → ℝ → ℝ) (m d : ℝ → ℝ) (A : Set ℝ),
        StrictAntiOn m A →
        StrictAntiOn d A →
        (∀ a ∈ A, m a ≤ d a) →
        (∀ a, Monotone (Q a)) →
        AntitoneOn (switchWedge Q m d) A := by
  intro h
  have hanti :=
    h cxQ cxM cxD cxA cxM_strictAntiOn cxD_strictAntiOn cxM_le_cxD
      cxQ_monotone_in_sanction
  have h0 : (0 : ℝ) ∈ cxA := ⟨le_refl 0, by norm_num⟩
  have hhalf : (1 / 2 : ℝ) ∈ cxA := ⟨by norm_num, le_refl _⟩
  -- antitone would force the wedge at 1/2 to sit below its value at 0 ...
  have hle : switchWedge cxQ cxM cxD (1 / 2) ≤ switchWedge cxQ cxM cxD 0 :=
    hanti h0 hhalf (by norm_num)
  -- ... but the wedge is the identity, so that reads `1/2 ≤ 0`.
  rw [cx_senderSwitch_eq, cx_senderSwitch_eq] at hle
  norm_num at hle

/-- The positive form of the same fact: at this witness the switch channel is
*strictly increasing*, so it works against the Target-continuation channel
rather than alongside it. Any route to the compliance ordering must therefore
either bound this channel or dominate it. -/
theorem cx_senderSwitch_strictMonoOn :
    StrictMonoOn (switchWedge cxQ cxM cxD) cxA := by
  intro a _ b _ hab
  rw [cx_senderSwitch_eq, cx_senderSwitch_eq]
  exact hab


/-! ## Which hypothesis fails

`switchWedge_antitone_of_gap_and_shape` signs the channel from six hypotheses:
three on the payoff's shape, two saying both responses fall with `m ≤ d`, and
one saying the **gap does not widen**. The witness below satisfies all of the
first five and violates only the last, so the refutation is not merely "some
extra condition is needed" — it locates the condition exactly. -/

/-- The witness satisfies the payoff-shape hypotheses: `Q` is non-decreasing in
the sanction, its equal-width chords are constant (so trivially non-decreasing
under translation, which is convexity in the consumed form), and it has
decreasing differences because it does not depend on the action at all. -/
theorem cx_satisfies_payoff_shape :
    (∀ a s₁ s₂, s₁ ≤ s₂ → cxQ a s₁ ≤ cxQ a s₂)
    ∧ (∀ a s₁ s₂ t, s₁ ≤ s₂ → 0 ≤ t →
        cxQ a s₂ - cxQ a s₁ ≤ cxQ a (s₂ + t) - cxQ a (s₁ + t))
    ∧ (∀ aL aH s₁ s₂, aL ≤ aH → s₁ ≤ s₂ →
        cxQ aH s₂ - cxQ aH s₁ ≤ cxQ aL s₂ - cxQ aL s₁) := by
  refine ⟨fun a s₁ s₂ h => h, fun a s₁ s₂ t _ _ => by simp only [cxQ]; linarith,
    fun aL aH s₁ s₂ _ _ => by simp only [cxQ]; exact le_refl _⟩

/-- The witness also satisfies the two selection hypotheses: the static response
falls in compliance, and the forward-looking response is the harder one. -/
theorem cx_satisfies_selection_shape :
    (∀ aL ∈ cxA, ∀ aH ∈ cxA, aL ≤ aH → cxM aH ≤ cxM aL)
    ∧ (∀ a ∈ cxA, cxM a ≤ cxD a) := by
  refine ⟨fun aL _ aH _ h => by simp only [cxM]; linarith, fun a ha => ?_⟩
  simp only [cxM, cxD]
  linarith [ha.1]

/-- **And it violates exactly the gap hypothesis.** The forward-looking Sender
relaxes at rate `1` while the myopic one relaxes at rate `2`, so each unit of
compliance widens the distance between them. That is the whole content of the
counterexample, and it is the reason the gap condition cannot be dropped. -/
theorem cx_violates_gap :
    ¬ (∀ aL ∈ cxA, ∀ aH ∈ cxA, aL ≤ aH → cxD aH - cxM aH ≤ cxD aL - cxM aL) := by
  intro h
  have := h 0 ⟨le_refl 0, by norm_num⟩ (1 / 2) ⟨by norm_num, le_refl _⟩ (by norm_num)
  simp only [cxM, cxD] at this
  norm_num at this

end Examples
end Sanctions
