/-
Sanctions/Examples/PlacableSenderBranchInvarianceParams.lean

**Branch invariance on the chord class, for every full-defiance equilibrium;
row 49 as a corollary** (round BB, 2026-09-28; doc 110, item R10(a)).

`Theory/Equilibrium/BranchInvarianceParams.lean` proves, over abstract `Params`,
that two economies with the same transition on the square, the same Sender
discount factor and the same Sender payoff at defiance have, at *any* two
full-defiance equilibria, the same Sender value, the same realised sanction rule
on `[0,1]`, and the same state and sanction paths from every feasible start —
with no margin and no argmax uniqueness. This file instantiates it on the chord
class.

* **Row 49 as a corollary.** The constructed equilibria
  `equilibriumTop_of_margin` have the Target defying everywhere
  (`equilibriumTop_of_margin_α_eq_zero`, by definition), so the pinned row
  `dynamicSanction_eq_of_sender_side_eq` and its path companion
  `dynamicPath_eq_of_sender_side_eq` (`PlacableSenderBranchInvariance.lean`)
  follow from the `Params` theorem: `dynamicSanction_eq_of_sender_side_eq_of_params`
  and `dynamicPath_eq_of_sender_side_eq_of_params` restate them verbatim and
  prove them that way. The originals are untouched. The eight premises of the
  restated rows are the originals'; the two loss-offset conditions and the two
  rally margins are used **only** to name the constructed equilibria, not in the
  argument.
* **Every full-defiance equilibrium** (`defiance_branch_invariance`). For two
  chord economies with the same transition on the square, the same Sender
  discount factor and the same Sender payoff at defiance, and *any*
  full-defiance equilibrium of each: both Sender values are the constructed
  value `VSstar`, and the two members' `VSstar` coincide; both realised rules are
  the constructed response at defiance on `[0,1]`, and they coincide; and the
  two equilibrium state paths and sanction paths coincide from every feasible
  start. Five premises: the three agreement conditions, the two class premises
  `α ≡ 0`, and nothing else — no loss-offset condition, no rally margin.

**Scope (Rule 9).** Universal over full-defiance equilibria of pairs of chord
economies; conditional on those equilibria existing (existence of the
constructed one still needs each member's loss-offset condition and rally
margin, as in row 49). Nothing about equilibria in which the Target complies
somewhere, about the Target's value, or about the Sender's off-path responses
to compliance.

Rule 22: general in `F`. Rule 3: no new assumption — the premises are row 49's
agreement conditions (the transition agreement weakened to the square in
`defiance_branch_invariance`) and the class restriction `α ≡ 0`. Rule 1: both
equilibria are arbitrary top-selector feedback Stackelberg equilibria; `α ≡ 0`
selects which equilibria the statement is about.
-/
import Sanctions.Theory.Equilibrium.BranchInvarianceParams
import Sanctions.Examples.PlacableSenderBranchInvariance
import Sanctions.Examples.PlacableSenderDefianceValues

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E₁ E₂ : ChordEconomy)

/-- **Branch invariance on the chord class, for every full-defiance
equilibrium.** Two chord economies with the same transition on the square, the
same Sender discount factor and the same Sender payoff at defiance; any
full-defiance equilibrium of each. Then (i) each Sender value is its member's
constructed `VSstar`, and the two coincide; (ii) at every feasible state each
realised rule is its member's constructed response at defiance, and the two
rules coincide; (iii) from every feasible start the two equilibrium state paths,
and the sanctions realised along them, coincide at every date. No loss-offset
condition, no rally margin; the Target's payoff and discount factor, and the
placation slope, are unrestricted. General in `F`. -/
theorem defiance_branch_invariance
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.F x s = E₂.F x s)
    (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s)
    (Eq₁ : E₁.toParams.FeedbackStackelbergEquilibriumTop)
    (Eq₂ : E₂.toParams.FeedbackStackelbergEquilibriumTop)
    (hα₁ : ∀ x ∈ Sanctions.I, Eq₁.α x = 0) (hα₂ : ∀ x ∈ Sanctions.I, Eq₂.α x = 0) :
    (Eq₁.V_S = E₁.VSstar ∧ Eq₂.V_S = E₂.VSstar ∧ E₁.VSstar = E₂.VSstar) ∧
    (∀ x ∈ Sanctions.I,
      E₁.toParams.dynamicEquilibriumRule Eq₁ x = E₁.responsePath E₁.VSstar x ∧
      E₂.toParams.dynamicEquilibriumRule Eq₂ x = E₂.responsePath E₂.VSstar x ∧
      E₁.toParams.dynamicEquilibriumRule Eq₁ x = E₂.toParams.dynamicEquilibriumRule Eq₂ x) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t,
      E₁.toParams.rulePathF (E₁.toParams.dynamicEquilibriumRule Eq₁) x₀ t
          = E₂.toParams.rulePathF (E₂.toParams.dynamicEquilibriumRule Eq₂) x₀ t ∧
        E₁.toParams.dynamicEquilibriumRule Eq₁
            (E₁.toParams.rulePathF (E₁.toParams.dynamicEquilibriumRule Eq₁) x₀ t)
          = E₂.toParams.dynamicEquilibriumRule Eq₂
            (E₂.toParams.rulePathF (E₂.toParams.dynamicEquilibriumRule Eq₂) x₀ t)) := by
  obtain ⟨hV, hR, hP⟩ :=
    Params.defiance_branch_invariance_generalF hF hβS hUS Eq₁ Eq₂ hα₁ hα₂
  obtain ⟨hV₁, -, hR₁⟩ := E₁.values_eq_of_policy_zero Eq₁ hα₁
  obtain ⟨hV₂, -, hR₂⟩ := E₂.values_eq_of_policy_zero Eq₂ hα₂
  refine ⟨⟨hV₁, hV₂, ?_⟩, fun x hx => ⟨hR₁ x hx, hR₂ x hx, hR x hx⟩, hP⟩
  rw [← hV₁, ← hV₂, hV]

end ChordEconomy

/-! ### The rally-margin corollaries, on the two-sided extension (renovation item BJ3.1)

The rally margin reads the two-sided curvature data, so since 2026-10-07 the three
margin-form statements below are stated on `ChordEconomyTwoSided`; until then they were on
`ChordEconomy`, otherwise unchanged. Each is general in `F`. -/

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The constructed equilibrium is a full-defiance equilibrium: its Target
policy is zero (by construction, `equilibriumTop`, where it is derived as the
unique Target argmax). -/
theorem equilibriumTop_of_margin_α_eq_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    ∀ x ∈ Sanctions.I, ((E.equilibriumTop_of_margin hTM) hmargin).α x = 0 :=
  fun _ _ => rfl

variable (E₁ E₂ : ChordEconomyTwoSided)

/-- **Row 49's path companion, derived from the `Params` theorem.** The same
statement as `dynamicPath_eq_of_sender_side_eq`: under each member's own
loss-offset condition and rally margin, the forward-looking state paths coincide
from every feasible start. The loss-offset conditions and margins serve only to
name the constructed equilibria. -/
theorem dynamicPath_eq_of_sender_side_eq_of_params
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s)
    (hTM₁ : E₁.LossOffset) (hTM₂ : E₂.LossOffset)
    (hm₁ : E₁.β_S * (E₁.SigC * E₁.ghi * E₁.dhi + (E₁.KS + 2 * E₁.SigC) * E₁.Mmix) ≤ E₁.rlo)
    (hm₂ : E₂.β_S * (E₂.SigC * E₂.ghi * E₂.dhi + (E₂.KS + 2 * E₂.SigC) * E₂.Mmix) ≤ E₂.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E₁.dynamicPath hTM₁) hm₁ x₀ t = (E₂.dynamicPath hTM₂) hm₂ x₀ t :=
  Params.equilibriumPath_eq_of_defiance_section_eq (fun x _ s _ => by rw [hF]) hβS hUS
    ((E₁.equilibriumTop_of_margin hTM₁) hm₁) ((E₂.equilibriumTop_of_margin hTM₂) hm₂)
    (E₁.equilibriumTop_of_margin_α_eq_zero hTM₁ hm₁)
    (E₂.equilibriumTop_of_margin_α_eq_zero hTM₂ hm₂) hx₀

/-- **Row 49, derived from the `Params` theorem.** The same statement as the
pinned `dynamicSanction_eq_of_sender_side_eq`: under each member's own
loss-offset condition and rally margin, the realised sanctions along the two
forward-looking paths coincide at every date. The loss-offset conditions and
margins serve only to name the constructed equilibria; the argument is the
general one over any two full-defiance equilibria, and uses no argmax
uniqueness. -/
theorem dynamicSanction_eq_of_sender_side_eq_of_params
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s)
    (hTM₁ : E₁.LossOffset) (hTM₂ : E₂.LossOffset)
    (hm₁ : E₁.β_S * (E₁.SigC * E₁.ghi * E₁.dhi + (E₁.KS + 2 * E₁.SigC) * E₁.Mmix) ≤ E₁.rlo)
    (hm₂ : E₂.β_S * (E₂.SigC * E₂.ghi * E₂.dhi + (E₂.KS + 2 * E₂.SigC) * E₂.Mmix) ≤ E₂.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E₁.toParams.dynamicEquilibriumRule ((E₁.equilibriumTop_of_margin hTM₁) hm₁)
        ((E₁.dynamicPath hTM₁) hm₁ x₀ t)
      = E₂.toParams.dynamicEquilibriumRule ((E₂.equilibriumTop_of_margin hTM₂) hm₂)
        ((E₂.dynamicPath hTM₂) hm₂ x₀ t) :=
  Params.equilibriumSanction_eq_of_defiance_section_eq (fun x _ s _ => by rw [hF]) hβS hUS
    ((E₁.equilibriumTop_of_margin hTM₁) hm₁) ((E₂.equilibriumTop_of_margin hTM₂) hm₂)
    (E₁.equilibriumTop_of_margin_α_eq_zero hTM₁ hm₁)
    (E₂.equilibriumTop_of_margin_α_eq_zero hTM₂ hm₂) hx₀ t

end ChordEconomyTwoSided

end

#print axioms Sanctions.Examples.ChordEconomyTwoSided.equilibriumTop_of_margin_α_eq_zero
#print axioms Sanctions.Examples.ChordEconomyTwoSided.dynamicPath_eq_of_sender_side_eq_of_params
#print axioms Sanctions.Examples.ChordEconomyTwoSided.dynamicSanction_eq_of_sender_side_eq_of_params
#print axioms Sanctions.Examples.ChordEconomy.defiance_branch_invariance

end Examples
end Sanctions
