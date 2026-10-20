/-
Sanctions/Examples/AffineChordKnifeEdge.lean

**The affine instance of the response-gap chord condition — the knife edge.**

`Theory/LockIn/TwoSidedForwardLooking.lean` §12 states the Sender-side condition
on *chords of the composite* `s ↦ β_S · V_S (F (x, s))`, and proves the
comparative static from that alone. Curvature of `V_S` and curvature of `F` are
dischargers, never the statement.

**Affine-restricted (Rule 22).** Every result below assumes
`p.F = affineF p.δ`, the linear adjustment law `F(x,s) = (1−δ)x + δs`. Nothing
here is claimed for a general transition.

**What is conditional and what is witnessed.** The first three results are
*conditional theorems*, quantified over an unspecified `p` and `V_S` under
hypotheses; on their own they exhibit nothing. `affineKnifeEdge_nonvacuous` at
the end is the actual existence certificate: a concrete economy
(`Examples.ceParams`, whose transition is `affineF (1/2)`) paired with a concrete
linear Sender value, for which both chord conditions hold. That, and only that,
answers "is the Sender-side condition inhabited?".

**What is deliberately NOT witnessed.** `affine_responseGap_constant` carries
five hypotheses — the two above plus a translated-loss stage payoff, placation,
and feasibility of the translated responses. No economy is exhibited satisfying
all five simultaneously, so that theorem is conditional and is not evidence that
the package is jointly satisfiable. Read it as an implication, not a finding.

**Instances of the general theorems (BG1.9, 2026-10-06).** The two affine
results are now one-line instances of general-`F` theorems in §12:
`affine_senderContinuation_chords_both` applies
`senderContinuationChords_of_affine`, which since BG1.9 asks the composite to be
affine only on the feasible sanctions `[0,1]` (affinity on all of `ℝ` forced
slope `0`, because `V_S` is bounded), and `affine_responseGap_constant` applies
`responseGap_eq_of_senderContinuationChords`. The affine law enters only to make
the composite affine on `[0,1]`.

**What it shows, where it applies.** Under the affine law, a Sender value acting
affinely on the reachable range makes the composite continuation term exactly
affine in the sanction, with slope `β_S · c · δ`. Both chord conditions then hold
simultaneously, with equality, so the dynamic-versus-static response gap is
**constant** in compliance — neither widening nor narrowing.

That places affineness between the two economies the project exhibits:
`Examples/BaselineTwoSidedOrderingUndetermined.lean` has a strictly *concave*
composite and a strictly widening gap. The placement is in the **sufficient**
direction only — a composite that is neither convex nor concave may still leave
some particular pair of gaps equal, which is why §12's theorems are stated on
chords rather than on curvature.

**A scope note on the chord form itself.** On an interval, with a continuous
composite, increasing translated chords are *equivalent* to convexity of the
composite (the midpoint case gives midpoint convexity, and Sierpiński's theorem
closes it). Since `Sanctions.I` is an interval and the composite here is
continuous, the chord condition and `SenderContinuationConvexAt` say the same
thing at this application. The chord form is preferred for two narrower reasons —
it does not bundle `Convex ℝ A`, and it names exactly the inequality the proof
consumes — not because it is weaker here. The converse implication is not proved
in this tree; Mathlib has no midpoint-convexity theorem at the pinned revision.
-/
import Sanctions.Theory.LockIn.TwoSidedForwardLooking
import Sanctions.Examples.ContinuationDrivenEscalation
import Mathlib.Tactic

namespace Sanctions
namespace Examples

open Sanctions.AbstractGame BoundedContinuousFunction

variable (p : Params)

/-- Under the affine law the successor state is feasible, so the clip is
inert on it. -/
theorem affine_F_mem {x s : ℝ} (hF : p.F = affineF p.δ)
    (hx : x ∈ (Sanctions.S : Set ℝ)) (hs : s ∈ Sanctions.I) :
    p.F x s ∈ (Sanctions.S : Set ℝ) := by
  obtain ⟨hδ0, hδ1⟩ := p.δ_mem
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hs0, hs1⟩ := hs
  rw [hF]
  constructor <;> · simp only [affineF]; nlinarith

/-- **Under the affine law, a Sender value affine on the reachable range gives an
affine composite continuation term.**

The slope is `β_S · c · δ`: the Sender's discount, the value's slope, and the
adjustment rate, multiplied. Affine-restricted (Rule 22). -/
theorem affine_senderContinuationTerm_eq
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x c b : ℝ}
    (hF : p.F = affineF p.δ) (hx : x ∈ (Sanctions.S : Set ℝ))
    (hV : ∀ y : ℝ, ∀ _hy : y ∈ (Sanctions.S : Set ℝ),
      V_S (Sanctions.clipS' y) = c * y + b) :
    ∀ s ∈ Sanctions.I, p.senderContinuationTerm V_S x s
      = (p.β_S * c * p.δ) * s
        + (p.β_S * (c * ((1 - p.δ) * x) + b)) := by
  intro s hs
  unfold AbstractGame.Params.senderContinuationTerm
  rw [hV _ (affine_F_mem p hF hx hs), hF]
  simp only [affineF]
  ring

/-- **The knife edge, at the affine instance.**

Both chord conditions hold at once, so the general theorems of §12 apply in both
directions and pin the response gap to a constant in compliance.

This is an existence statement about the hypothesis class and nothing more
(Rule 9A): it exhibits economies satisfying the Sender-side condition, and says
nothing about whether a typical or calibrated economy does. Affine-restricted
(Rule 22). Since BG1.9 an instance of the general
`senderContinuationChords_of_affine` (composite affine on `[0,1]`), fed by
`affine_senderContinuationTerm_eq`. -/
theorem affine_senderContinuation_chords_both
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x c b : ℝ}
    (hF : p.F = affineF p.δ) (hx : x ∈ (Sanctions.S : Set ℝ))
    (hV : ∀ y : ℝ, ∀ _hy : y ∈ (Sanctions.S : Set ℝ),
      V_S (Sanctions.clipS' y) = c * y + b) :
    p.SenderContinuationIncreasingChordsAt V_S x
      ∧ p.SenderContinuationDecreasingChordsAt V_S x :=
  p.senderContinuationChords_of_affine (affine_senderContinuationTerm_eq p hF hx hV)

/-- **The response gap is exactly constant in compliance, at the affine
instance.**

Both directions of the §12 comparison, composed: the gap neither widens nor
narrows. Read against `Examples/BaselineTwoSidedOrderingUndetermined.lean`,
where a strictly concave composite makes the same gap strictly widen, this
locates affineness as the boundary between the adverse and favourable cases —
in the sufficient direction only. Affine-restricted (Rule 22).

Since BG1.9 (2026-10-06) an instance of the general-`F`
`responseGap_eq_of_senderContinuationChords`. The ordering hypothesis
`a₁ ≤ a₂` was dropped: the gap is the same at any two feasible compliance
levels, in either order. -/
theorem affine_responseGap_constant
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x c b : ℝ} {g : ℝ → ℝ}
    (hF : p.F = affineF p.δ) (hx : x ∈ (Sanctions.S : Set ℝ))
    (hV : ∀ y : ℝ, ∀ _hy : y ∈ (Sanctions.S : Set ℝ),
      V_S (Sanctions.clipS' y) = c * y + b)
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x)
    {a₁ a₂ : ℝ} (h₁ : a₁ ∈ Sanctions.I) (h₂ : a₂ ∈ Sanctions.I) :
    p.σ_dyn_top V_S x a₂ - p.σ x a₂ = p.σ_dyn_top V_S x a₁ - p.σ x a₁ := by
  obtain ⟨hinc, hdec⟩ := affine_senderContinuation_chords_both p hF hx hV
  exact p.responseGap_eq_of_senderContinuationChords V_S hform hinc hdec
    hσ_anti hfeas h₁ h₂

/-! ## A concrete witness

Everything above is conditional. This section discharges the hypotheses at a
concrete economy, so that the Sender-side chord condition is known to be
inhabited rather than merely defined.

`ceParams` is an existing witness economy whose transition is `affineF (1/2)`
and whose discount is `β_S = 1/2`; `akeLinBCF c` is a linear Sender value. The
composite is then affine with slope `c/4`, and both chord conditions hold. -/

/-- A linear bounded-continuous value on the feasible state space. -/
noncomputable def akeLinBCF (c : ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => c * y.val) (by fun_prop))

@[simp] theorem akeLinBCF_apply (c : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    akeLinBCF c y = c * y.val := rfl

theorem akeLinBCF_at {c y : ℝ} (hy : y ∈ (Sanctions.S : Set ℝ)) :
    akeLinBCF c (Sanctions.clipS' y) = c * y + 0 := by
  simp only [akeLinBCF_apply]
  rw [Sanctions.clipS'_val_eq_of_mem hy]
  ring

/-- The witness economy's transition really is the affine law at its own `δ`. -/
theorem ceParams_F_affine : ceParams.F = AbstractGame.affineF ceParams.δ := rfl

/-- **Non-vacuity of the Sender-side chord condition.**

A concrete economy and a concrete Sender value at which the composite
continuation term has both increasing and decreasing translated chords — hence
the knife edge is inhabited, and §12's favourable branch is not an empty
hypothesis class.

Rule 9A: this licenses `∃ p V_S x, …` and nothing more. It says nothing about
whether a typical or calibrated economy satisfies the condition, and it does not
witness the larger package of `affine_responseGap_constant`. -/
theorem affineKnifeEdge_nonvacuous (c : ℝ) {x : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ)) :
    ceParams.SenderContinuationIncreasingChordsAt (akeLinBCF c) x
      ∧ ceParams.SenderContinuationDecreasingChordsAt (akeLinBCF c) x :=
  affine_senderContinuation_chords_both ceParams ceParams_F_affine hx
    (fun _ hy => akeLinBCF_at hy)

/-- The composite at the witness is affine with slope `c/4` — `β_S · c · δ` at
`β_S = δ = 1/2`. Recorded so the witness is checkable by inspection. -/
theorem ake_witness_composite (c : ℝ) {x : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) :
    ∀ s ∈ Sanctions.I,
      ceParams.senderContinuationTerm (akeLinBCF c) x s
        = (c / 4) * s + (1 / 2 : ℝ) * (c * ((1 - (1 / 2 : ℝ)) * x) + 0) := by
  have h := affine_senderContinuationTerm_eq ceParams ceParams_F_affine hx
    (fun _ hy => akeLinBCF_at (c := c) hy)
  have hδ : ceParams.δ = (1 / 2 : ℝ) := rfl
  have hβ : ceParams.β_S = (1 / 2 : ℝ) := rfl
  intro s hs
  rw [h s hs, hδ, hβ]
  ring

end Examples
end Sanctions
