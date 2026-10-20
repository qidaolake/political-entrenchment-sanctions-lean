/-
Sanctions/Theory/Mechanism/PrimitiveReduction.lean

**Two of the five proposed complementarity conditions are not assumptions about
the complete objective at all.**

`suggestions/33` proposes a five-condition class `C1`–`C5` for the four-regime
mechanism theorem, and states each one *"for each state and admissible
continuation value"* — phrasing that reads as a carrier-uniform requirement on
the complete objective, of the same kind that
`Theory/Certificates/SelectorGeometry.lean` documents as refuted here.

For two of the five that reading is too pessimistic, and this file says by how
much. What remains genuinely endogenous is `C3`–`C5`, which live on the Target's
*reduced* objective after the Sender's response has been substituted in;
`suggestions/33` §6 already concedes that the preservation of those through the
reduction is an unproved obligation rather than a closure property.

The point of separating them is Rule 3 hygiene. An assumption bundle whose
members have different characters should not be signed off as one primitive: two
of these are conditions on stage payoffs, of the kind the model already carries,
and burying them next to three endogenous conditions would overstate the cost of
the first two and hide the cost of the last three.
-/

import Sanctions.Theory.Bellman.BellmanS
import Sanctions.Theory.Mechanism.ContinuationProfile

namespace Sanctions
namespace Mechanism

open Set

/-! ## C1 — the continuation cancels identically

`C1` asks the Sender's complete objective to have increasing differences in
Target defiance and the sanction. But the Sender's continuation term depends on
the sanction and **not** on the Target's action, so it contributes the same
increment to both sides of the cross-difference and drops out.

`C1` is therefore not a condition on the complete objective, on a carrier, or on
a profile. It is exactly increasing differences of the **stage payoff** `U_S` —
the compliance-placation property, a statement about primitives. -/

/-- **Increasing differences of a stage-plus-continuation objective in the two
actions is exactly increasing differences of the stage payoff.**

Stated over an arbitrary continuation `W`, because the fact does not depend on
what the continuation is: it depends only on the continuation not seeing the
first action. Every profile, every value function, every carrier. -/
theorem completeID_iff_stageID
    (U : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (dL dH sL sH : ℝ) :
    (U dL sH + W sH) - (U dL sL + W sL)
        ≤ (U dH sH + W sH) - (U dH sL + W sL)
      ↔ U dL sH - U dL sL ≤ U dH sH - U dH sL := by
  constructor <;> intro h <;> linarith

/-- The quantified form: the Sender's complete objective has increasing
differences at *every* continuation exactly when the stage payoff does. -/
theorem completeID_forall_iff_stageID
    (U : ℝ → ℝ → ℝ) (D S : Set ℝ) :
    (∀ W : ℝ → ℝ, ∀ dL ∈ D, ∀ dH ∈ D, ∀ sL ∈ S, ∀ sH ∈ S, dL ≤ dH → sL ≤ sH →
        (U dL sH + W sH) - (U dL sL + W sL)
          ≤ (U dH sH + W sH) - (U dH sL + W sL))
      ↔ (∀ dL ∈ D, ∀ dH ∈ D, ∀ sL ∈ S, ∀ sH ∈ S, dL ≤ dH → sL ≤ sH →
        U dL sH - U dL sL ≤ U dH sH - U dH sL) := by
  constructor
  · intro h dL hdL dH hdH sL hsL sH hsH hd hs
    exact (completeID_iff_stageID U (fun _ => 0) dL dH sL sH).mp
      (h (fun _ => 0) dL hdL dH hdH sL hsL sH hsH hd hs)
  · intro h W dL hdL dH hdH sL hsL sH hsH hd hs
    exact (completeID_iff_stageID U W dL dH sL sH).mpr
      (h dL hdL dH hdH sL hsL sH hsH hd hs)

end Mechanism

namespace AbstractGame
namespace Params

open Sanctions.Mechanism
open BoundedContinuousFunction

variable (p : Params)

/-! ## C2 — derivable, through machinery already in the tree

`C2` asks that raising the sanction not lower the Sender's continuation, i.e.
that `s ↦ V_S (F x s)` be nondecreasing. Two of the three links are `Params`
fields, and the third is an existing theorem:

* `F_mono_s` — the transition is nondecreasing in the sanction. A `Params` field.
* `clipS'_mono` — clipping to the feasible interval preserves order.
* `bellmanS_BCF_preserves_monotone` — the Sender Bellman operator preserves
  monotonicity of the value in the state, given that the **stage payoff**
  `U_S(·, α(·), s)` is nondecreasing in the state.

So `C2` reduces to a monotonicity condition on `U_S`, which is again a statement
about primitives rather than about an endogenous value function. The first step
is below; the second is `bellmanS_BCF_preserves_monotone` unchanged. -/

/-- **A state-monotone Sender value gives a sanction-monotone continuation.**

The transition is nondecreasing in the sanction and clipping preserves order, so
a value function that rises with entrenchment composes to a continuation term
that rises with the sanction. This is the step from `C2`'s conclusion to a
property of `V_S` alone; `bellmanS_BCF_preserves_monotone` then takes that to a
property of `U_S`. -/
theorem senderContinuation_mono_of_value_mono
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hV : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => V z))
    (x : ℝ) :
    Monotone (fun s => V (Sanctions.clipS' (p.F x s))) := by
  intro s₁ s₂ h
  exact hV (Sanctions.clipS'_mono (p.F_mono_s x h))

/-- The same statement for the discounted continuation actually appearing in the
Sender's objective, at any profile. The discount factor is nonnegative at every
profile (`profileβ_S_mem`), so it cannot reverse the order. -/
theorem profileSenderContinuation_mono_of_value_mono
    (c : Sanctions.Mechanism.ContinuationProfile)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hV : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => V z))
    (x : ℝ) :
    Monotone (fun s => p.profileβ_S c * V (Sanctions.clipS' (p.F x s))) := by
  intro s₁ s₂ h
  exact mul_le_mul_of_nonneg_left
    (p.senderContinuation_mono_of_value_mono V hV x h) (p.profileβ_S_mem c).1

/-! ## The two conditions, named at the primitive level

`C1` and `C2` are stated here as conditions on `U_S` — where the reductions
above show they actually live — rather than on the complete objective. Naming
them is not adopting them: nothing in this development takes either as a
hypothesis, and doing so would still be a Rule 3 event, because the baseline
does not imply them. What the naming buys is that if they are ever adopted, the
cost on the record is a *stage-payoff sign condition* and not a carrier-uniform
requirement on an endogenous object. Those are very different prices, and
`suggestions/33`'s phrasing charges the higher one for both.

See `ASSUMPTION-SURFACE-REGISTER.md` for the classification and the quarantine
terms. -/

/-- **`C1` at the primitive level — compliance placates.**

Raising the sanction is worth less to the Sender when the Target complies more.
In defiance terms this is increasing differences in `(defiance, sanction)`; in
compliance terms, which is how `U_S` is written, it is decreasing differences.

By `Mechanism.completeID_iff_stageID` this is *equivalent* to the same condition
on the Sender's complete objective, at every continuation value, every carrier
and every profile — the continuation cancels. -/
def SenderStagePlacation (x : ℝ) : Prop :=
  ∀ aL ∈ Sanctions.I, ∀ aH ∈ Sanctions.I, ∀ sL ∈ Sanctions.I, ∀ sH ∈ Sanctions.I,
    aL ≤ aH → sL ≤ sH →
      p.U_S x aH sH - p.U_S x aH sL ≤ p.U_S x aL sH - p.U_S x aL sL

/-- **`C1` transfers to the complete objective, at any continuation.**

The economic reading: whether compliance placates is a property of the *stage*
payoff, and no continuation motive — of either government, at any discount
factor — can create or destroy it. -/
theorem senderComplete_placation_of_stage
    {x : ℝ} (h : p.SenderStagePlacation x) (W : ℝ → ℝ)
    {aL aH sL sH : ℝ} (haL : aL ∈ Sanctions.I) (haH : aH ∈ Sanctions.I)
    (hsL : sL ∈ Sanctions.I) (hsH : sH ∈ Sanctions.I)
    (ha : aL ≤ aH) (hs : sL ≤ sH) :
    (p.U_S x aH sH + W sH) - (p.U_S x aH sL + W sL)
      ≤ (p.U_S x aL sH + W sH) - (p.U_S x aL sL + W sL) := by
  have := h aL haL aH haH sL hsL sH hsH ha hs
  linarith

/-- **`C2` at the primitive level — the Sender's stage payoff does not fall with
entrenchment**, along the Target's policy.

This is exactly the hypothesis `bellmanS_BCF_preserves_monotone` consumes, named
so the chain to `C2` is legible: this condition gives a state-monotone `V_S` by
cone preservation, and `senderContinuation_mono_of_value_mono` then gives the
sanction-monotone continuation that `C2` asserts. -/
def SenderStageStateMonotone (α : ℝ → ℝ) : Prop :=
  ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
    x ≤ y → p.U_S x (α x) s ≤ p.U_S y (α y) s

/-- **The second link of the `C2` chain, made explicit.**

Given the primitive condition, the Sender Bellman operator preserves state
monotonicity of the value — so the monotone cone is invariant and its fixed
point is monotone. Stated as the one-step preservation, which is what a cone
iteration consumes; `bellmanS_BCF_preserves_monotone` does the work. -/
theorem bellmanS_preserves_monotone_of_stageStateMonotone
    {α : ℝ → ℝ} (hα : Continuous α) (h : p.SenderStageStateMonotone α)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hV : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => V z)) :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => p.bellmanS_BCF α hα V z) :=
  p.bellmanS_BCF_preserves_monotone hα h V hV

/-- **The third link: the *constructed* Sender value is state-monotone.**

The primitive stage condition is definitionally the hypothesis that the
cone-preservation theorem in `Theory/Bellman/BellmanS.lean` already consumes, so
the monotone cone is invariant under the Sender Bellman operator and its limit —
the actual contraction fixed point `p.V_S α hα`, not a supplied value — inherits
monotonicity. This is what makes the chain a *reduction to primitives* rather
than a restatement (Rule 15). -/
theorem V_S_monotone_of_stageStateMonotone
    {α : ℝ → ℝ} (hα : Continuous α) (h : p.SenderStageStateMonotone α) :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => p.V_S α hα z) :=
  p.V_S_monotone_of_integrand_monotone hα h

/-- **The `C2` conclusion, at the constructed fixed point, from the primitive
alone.**

Closing the chain: the primitive stage-payoff condition gives exactly what `C2`
asks — the Sender's discounted continuation does not fall when the sanction
rises — at every profile, with the value being the Sender's own Bellman fixed
point and no free monotonicity hypothesis.

**Corrected 2026-08-31.** This theorem previously carried the name
`..._of_stageStateMonotone` while its signature took a *supplied* value `V`
together with a free hypothesis `hV` asserting that value already monotone, and
consumed no primitive condition at all — it was `profileSenderContinuation_mono_of_value_mono`
under a name that advertised a reduction it did not perform. The value-level
form remains available under its accurate name; this is the primitive-level one.

What `C2` still does **not** give, and what a strict activation result would
need, is a *strict* continuation chord; monotonicity alone leaves the Sender's
dynamic response weakly above its static one and no more. -/
theorem senderProfileContinuation_mono_of_stageStateMonotone
    (c : Sanctions.Mechanism.ContinuationProfile)
    {α : ℝ → ℝ} (hα : Continuous α) (h : p.SenderStageStateMonotone α)
    (x : ℝ) :
    Monotone (fun s =>
      p.profileβ_S c * p.V_S α hα (Sanctions.clipS' (p.F x s))) :=
  p.profileSenderContinuation_mono_of_value_mono c (p.V_S α hα)
    (p.V_S_monotone_of_stageStateMonotone hα h) x

end Params
end AbstractGame
end Sanctions
