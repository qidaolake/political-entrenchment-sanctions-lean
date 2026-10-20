/-
Sanctions/Examples/PlacableSenderBranchInvariance.lean

**On the defiance branch the realised path does not depend on the Target's
payoff** (round AE, 2026-09-20; doc 94, item A2; the outside reader's
literature-verification package §2; on the abstract payoffs since round AV,
2026-09-25, doc 104).

Take two chord economies with the same transition, the same Sender discount
factor and the same **defiance section of the Sender's payoff**,
`U_S₁(x, 0, s) = U_S₂(x, 0, s)` on the square; the Sender's payoff away from
defiance, and the Target's payoff, are *not* required to agree. (On the
quadratic–linear family this is "the same `q, u₀, r, w`"; the placation slope
`k` need not agree, because at defiance the term `−k·a·s` vanishes.) Then

* the two constructed Sender values coincide (`VSstar_eq_of_sender_side_eq`):
  both are fixed points of one and the same Bellman operator at the defiance
  policy, and that operator is a contraction of the **ambient** space of bounded
  continuous values, so its fixed point is unique there. The two members'
  carriers need not coincide — their chord certificates and rate bounds may
  differ — and the argument does not use them;
* the realised responses at defiance coincide at every feasible state
  (`responsePath_eq_of_sender_side_eq`), by the first member's argmax uniqueness
  on its carrier;
* under each member's own rally margin, the forward-looking state paths and the
  realised sanctions coincide from every feasible start
  (`dynamicPath_eq_of_sender_side_eq`, `dynamicSanction_eq_of_sender_side_eq`).

**Reading.** The Target's patience `β_T` and its whole payoff — sanction pain,
rally, valuation of the state, compliance cost — and the Sender's payoff away
from defiance (placation) decide *whether* an economy is on the certified
defiance branch. Given that it is, they do not move the path of sanctions or of
the political state.
This is a statement about two members that are both in the family; it does not
say the branch survives an arbitrary parameter change, it says nothing about the
Target's own value (which does change), and nothing about other equilibria.
Off-path responses can differ when the placation differs.

Rule 22: general in `F`. Rule 9: parametric; no witness.
-/
import Sanctions.Examples.PlacableSenderWedge

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E₁ E₂ : ChordEconomy)

/-- The two members' Sender objectives at defiance are the same function. -/
theorem senderObj_zero_eq_of_sender_side_eq
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s)
    (V : Val) {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    E₁.senderObj V x 0 s = E₂.senderObj V x 0 s := by
  simp only [senderObj]
  rw [hUS x hx s hs, hF, hβS]

/-- The two members' Sender Bellman operators at the defiance policy coincide. -/
theorem bellmanS_zero_eq_of_sender_side_eq
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s) (V : Val) :
    E₁.toParams.bellmanS_BCF (fun _ => 0) continuous_const V
      = E₂.toParams.bellmanS_BCF (fun _ => 0) continuous_const V := by
  ext y
  change sSup ((fun s => E₁.senderObj V y.val 0 s) '' Sanctions.I)
    = sSup ((fun s => E₂.senderObj V y.val 0 s) '' Sanctions.I)
  congr 1
  exact Set.image_congr fun s hs =>
    senderObj_zero_eq_of_sender_side_eq E₁ E₂ hF hβS hUS V y.property hs

/-- **The constructed Sender values coincide**, by uniqueness of the fixed point
of the common Bellman contraction on the ambient value space. -/
theorem VSstar_eq_of_sender_side_eq
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s) :
    E₁.VSstar = E₂.VSstar := by
  have h₁ : Function.IsFixedPt (E₁.toParams.bellmanS_BCF (fun _ => 0) continuous_const)
      E₁.VSstar := E₁.VSstar_fix
  have h₂ : Function.IsFixedPt (E₁.toParams.bellmanS_BCF (fun _ => 0) continuous_const)
      E₂.VSstar := by
    change E₁.toParams.bellmanS_BCF (fun _ => 0) continuous_const E₂.VSstar = E₂.VSstar
    rw [bellmanS_zero_eq_of_sender_side_eq E₁ E₂ hF hβS hUS]
    exact E₂.VSstar_fix
  exact (E₁.toParams.bellmanS_BCF_contracting (α := fun _ => 0)
    continuous_const).fixedPoint_unique' h₁ h₂

/-- **The realised responses at defiance coincide** at every feasible state. -/
theorem responsePath_eq_of_sender_side_eq
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
        E₁.U_S x 0 s = E₂.U_S x 0 s) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E₁.responsePath E₁.VSstar x = E₂.responsePath E₂.VSstar x := by
  have hV := VSstar_eq_of_sender_side_eq E₁ E₂ hF hβS hUS
  have hmax₁ : IsMaxOn (fun s => E₁.senderObj E₁.VSstar x 0 s) Sanctions.I
      (E₁.responsePath E₁.VSstar x) := E₁.response_isMaxOn E₁.VSstar x 0
  have hmax₂ : IsMaxOn (fun s => E₁.senderObj E₁.VSstar x 0 s) Sanctions.I
      (E₂.responsePath E₂.VSstar x) := by
    have h := E₂.response_isMaxOn E₂.VSstar x 0
    intro s hs
    have hs' := h hs
    simp only [mem_setOf_eq] at hs' ⊢
    rw [hV, senderObj_zero_eq_of_sender_side_eq E₁ E₂ hF hβS hUS _ hx hs,
      senderObj_zero_eq_of_sender_side_eq E₁ E₂ hF hβS hUS _ hx (E₂.responsePath_mem _ _)]
    exact hs'
  exact E₁.DAU_on_carrier E₁.VSstar_mem x hx 0 _ _ (E₁.responsePath_mem _ _)
    (E₂.responsePath_mem _ _) hmax₁ hmax₂

end ChordEconomy

/-! ### The paths under the rally margin, on the two-sided extension (renovation item BJ3.1)

The rally margin reads the two-sided curvature data, so since 2026-10-07 the two path
statements below are stated on `ChordEconomyTwoSided`; until then they were on
`ChordEconomy`, otherwise unchanged. Each is general in `F`. -/

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E₁ E₂ : ChordEconomyTwoSided)

/-- **The forward-looking state paths coincide** from every feasible start, each
under its own member's rally margin. -/
theorem dynamicPath_eq_of_sender_side_eq
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s)
    (hTM₁ : E₁.LossOffset) (hTM₂ : E₂.LossOffset)
    (hm₁ : E₁.β_S * (E₁.SigC * E₁.ghi * E₁.dhi + (E₁.KS + 2 * E₁.SigC) * E₁.Mmix) ≤ E₁.rlo)
    (hm₂ : E₂.β_S * (E₂.SigC * E₂.ghi * E₂.dhi + (E₂.KS + 2 * E₂.SigC) * E₂.Mmix) ≤ E₂.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E₁.dynamicPath hTM₁) hm₁ x₀ t = (E₂.dynamicPath hTM₂) hm₂ x₀ t := by
  intro t
  induction t with
  | zero =>
      change E₁.toParams.rulePathF _ x₀ 0 = E₂.toParams.rulePathF _ x₀ 0
      rw [AbstractGame.Params.rulePathF_zero, AbstractGame.Params.rulePathF_zero]
  | succ t ih =>
      have hmem : (E₁.dynamicPath hTM₁) hm₁ x₀ t ∈ Sanctions.I :=
        E₁.toParams.rulePathF_mem_I ((E₁.dynamicRule_mem hTM₁) hm₁) hx₀ t
      have hmem₂ : (E₂.dynamicPath hTM₂) hm₂ x₀ t ∈ Sanctions.I := ih ▸ hmem
      have hstep₁ : (E₁.dynamicPath hTM₁) hm₁ x₀ (t + 1)
          = E₁.F ((E₁.dynamicPath hTM₁) hm₁ x₀ t)
              (E₁.toParams.dynamicEquilibriumRule ((E₁.equilibriumTop_of_margin hTM₁) hm₁)
                ((E₁.dynamicPath hTM₁) hm₁ x₀ t)) :=
        E₁.toParams.rulePathF_succ _ _ _
      have hstep₂ : (E₂.dynamicPath hTM₂) hm₂ x₀ (t + 1)
          = E₂.F ((E₂.dynamicPath hTM₂) hm₂ x₀ t)
              (E₂.toParams.dynamicEquilibriumRule ((E₂.equilibriumTop_of_margin hTM₂) hm₂)
                ((E₂.dynamicPath hTM₂) hm₂ x₀ t)) :=
        E₂.toParams.rulePathF_succ _ _ _
      rw [hstep₁, hstep₂, (E₁.dynamicRule_eq_responsePath hTM₁) hm₁ hmem,
          (E₂.dynamicRule_eq_responsePath hTM₂) hm₂ hmem₂, ← ih,
          responsePath_eq_of_sender_side_eq E₁.toChordEconomy E₂.toChordEconomy hF hβS hUS hmem,
          hF]

/-- **The realised sanctions coincide** along the two paths, at every date. -/
theorem dynamicSanction_eq_of_sender_side_eq
    (hF : E₁.F = E₂.F) (hβS : E₁.β_S = E₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, E₁.U_S x 0 s = E₂.U_S x 0 s)
    (hTM₁ : E₁.LossOffset) (hTM₂ : E₂.LossOffset)
    (hm₁ : E₁.β_S * (E₁.SigC * E₁.ghi * E₁.dhi + (E₁.KS + 2 * E₁.SigC) * E₁.Mmix) ≤ E₁.rlo)
    (hm₂ : E₂.β_S * (E₂.SigC * E₂.ghi * E₂.dhi + (E₂.KS + 2 * E₂.SigC) * E₂.Mmix) ≤ E₂.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E₁.toParams.dynamicEquilibriumRule ((E₁.equilibriumTop_of_margin hTM₁) hm₁)
        ((E₁.dynamicPath hTM₁) hm₁ x₀ t)
      = E₂.toParams.dynamicEquilibriumRule ((E₂.equilibriumTop_of_margin hTM₂) hm₂)
        ((E₂.dynamicPath hTM₂) hm₂ x₀ t) := by
  have hmem : (E₁.dynamicPath hTM₁) hm₁ x₀ t ∈ Sanctions.I :=
    E₁.toParams.rulePathF_mem_I ((E₁.dynamicRule_mem hTM₁) hm₁) hx₀ t
  have hpath := dynamicPath_eq_of_sender_side_eq E₁ E₂ hF hβS hUS hTM₁ hTM₂ hm₁ hm₂ hx₀ t
  have hmem₂ : (E₂.dynamicPath hTM₂) hm₂ x₀ t ∈ Sanctions.I := hpath ▸ hmem
  rw [(E₁.dynamicRule_eq_responsePath hTM₁) hm₁ hmem,
      (E₂.dynamicRule_eq_responsePath hTM₂) hm₂ hmem₂, ← hpath,
      responsePath_eq_of_sender_side_eq E₁.toChordEconomy E₂.toChordEconomy hF hβS hUS hmem]

end ChordEconomyTwoSided

end

#print axioms ChordEconomy.VSstar_eq_of_sender_side_eq
#print axioms ChordEconomy.responsePath_eq_of_sender_side_eq
#print axioms ChordEconomyTwoSided.dynamicPath_eq_of_sender_side_eq
#print axioms ChordEconomyTwoSided.dynamicSanction_eq_of_sender_side_eq

end Examples
end Sanctions
