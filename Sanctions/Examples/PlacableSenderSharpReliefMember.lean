/-
Sanctions/Examples/PlacableSenderSharpReliefMember.lean

**A non-affine member with positive cross coefficients that satisfies the sharp
relief margin and not the two-branch one** (round I, doc 75 R1″; the reader's
package `suggestions/2026-09-08-content-validation/`, doc 01 §1.6).

The Sender-only reading and the four-cell theorem take a relief margin. Round I
weakened it from `2ℓ·max(M_tot, k) < k(c − n)` to `ℓ·M_tot < k(c − n)`
(`PlacableSenderRegime01`, `reliefSharp_of_relief`). This file shows the
weakening is not empty: at the transition `quadDiagF` — proved not the affine
law at any rate — with coefficients

    (q, u₀, k, r, w, ℓ, c, n, v) = (3, 2, 3, 1/100, 3/10, 3/5, 1, 1/100, 5),

every family margin holds, the sharp relief margin holds
(`ℓ·M_tot = 6393/3500 < 297/100 = k(c − n)`), and the old one fails
(`2ℓ·max(M_tot, k) = 6393/1750 > 297/100`). Both cross coefficients `r` and `n`
are strictly positive, so the member sits in the interior of the family's sign
restrictions, not on the `r = n = 0` face.

Rule 9: this is an existence certificate. It licenses "the sharp sufficient
class strictly contains the old one, off the affine law" and nothing about
genericity, magnitudes or necessity. Rule 9C: the point was located and
perturbed (±5 % in every coefficient, exact rationals) before any Lean was
written — `docs/archive/workflow-scratch/round_I_stage0_disprove.py`; `v` was
raised from the reader's `41/10` to `5` because the loss-offset margin
failed at −5 % in `v` there. The transition proofs are those of
`placableQuadDiag` (`PlacableSenderWitnesses`), reused verbatim; the scalar
fields are `norm_num`.
Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and
stage relief fields (only the sign field `hcn : n < c`). The member's interiority is the
lemma `placableSharpReliefBase_interior` (chord forms `placableSharpRelief_chordInterior`,
`placableSharpRelief_chordLossOffset`), and the myopic cell's stage relief margin comes from
the sharp relief margin (`stageRelief_of_reliefSharp`, BG3.2;
`placableSharpRelief_chordStageRelief`); the statements below are unchanged up to these proof
terms.
-/
import Sanctions.Examples.PlacableSenderRegime01

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame

noncomputable section

/-- The base member: `quadDiagF` with the sharp-relief coefficients. -/
def placableSharpReliefBase : PlacableEconomyF where
  F := quadDiagF
  F_continuous := quadDiagF_continuous
  F_mono_x := quadDiagF_mono_x
  F_mono_s := quadDiagF_mono_s
  F_diag := quadDiagF_diag
  glo := 2/5
  ghi := 3/5
  dlo := 2/5
  dhi := 3/5
  Mx := 1/5
  Mm := 0
  Ms := 0
  hbandAll := quadDiagF_bandAll
  hSlo := quadDiagF_lo
  hShi := quadDiagF_hi
  hFjsc := quadDiagF_jsc
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  hMx0 := by norm_num
  hMm0 := by norm_num
  hMs0 := by norm_num
  Mcx := 0
  hMcx0 := by norm_num
  hFcx := quadDiagF_cx
  Mmix := 0
  hFmix := quadDiagF_mix
  δ := 1/2
  βS := 1/2
  βT := 1/2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  q := 3
  u₀ := 2
  k := 3
  r := 1/100
  w := 3/10
  ℓ := 3/5
  c := 1
  n := 1/100
  v := 5
  hu₀ := by norm_num
  hr := by norm_num
  hw := by norm_num
  hℓ := by norm_num
  hn := by norm_num
  SigV := 1
  hCurv := by norm_num [plKS]
  hSigV := by norm_num [plSigImg, plSig, plRho, plMu, plKS]
  hk := by norm_num
  hv := by norm_num
  hcn := by norm_num

/-- Placability at `placableSharpReliefBase` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableSharpReliefBase_placable : placableSharpReliefBase.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableSharpReliefBase]

/-- The loss-offset margin at `placableSharpReliefBase` (a hypothesis since round AP). -/
theorem placableSharpReliefBase_margin : placableSharpReliefBase.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableSharpReliefBase]

/-- Interiority at `placableSharpReliefBase` (a field of the family until renovation item
BJ2.3, 2026-10-07, now a hypothesis). At the non-affine transition `quadDiagF`. -/
theorem placableSharpReliefBase_interior : placableSharpReliefBase.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableSharpReliefBase]

/-- The enriched member: sanction-section modulus `1/5` at `quadDiagF`. -/
def placableSharpRelief : PlacableEconomyFcs where
  toPlacableEconomyF := placableSharpReliefBase
  Mcs := 1/5
  hMcs0 := by norm_num
  hFcs := quadDiagF_cs

theorem placableSharpRelief_base :
    placableSharpRelief.toPlacableEconomyF = placableSharpReliefBase := rfl

/-- The member's interiority in the chord form (renovation item BJ2.3). At the
non-affine transition `quadDiagF`. -/
theorem placableSharpRelief_chordInterior : placableSharpRelief.toChordCs.Interior :=
  placableSharpRelief.toChordCs_interior placableSharpReliefBase_interior

/-- The member's loss-offset margin in the chord form; the floor condition `u₀ ≤ q`
comes from interiority (renovation item BJ2.3). At the non-affine transition
`quadDiagF`. -/
theorem placableSharpRelief_chordLossOffset : placableSharpReliefBase.toChord.LossOffset :=
  placableSharpReliefBase.toChord_lossOffset
    (placableSharpReliefBase.u₀_le_q placableSharpReliefBase_interior)
    placableSharpReliefBase_margin

/-- `M_tot = q + β_S·KS·Mcs = 3 + (1/2)(31/70)(1/5) = 2131/700`. -/
theorem placableSharpRelief_Mtot : placableSharpRelief.toChordCs.Mtot = 2131 / 700 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableSharpRelief,
    placableSharpReliefBase]

/-- **The sharp relief margin holds:** `ℓ·M_tot = 6393/3500 < 297/100 = k(c − n)`. -/
theorem placableSharpRelief_relief_sharp :
    placableSharpRelief.ℓ * placableSharpRelief.toChordCs.Mtot
      < placableSharpRelief.k * (placableSharpRelief.c - placableSharpRelief.n) := by
  rw [placableSharpRelief_Mtot]
  norm_num [placableSharpRelief, placableSharpReliefBase]

/-- The member's stage relief margin in the chord form, from the sharp relief margin
(`stageRelief_of_reliefSharp`, BG3.2; renovation item BJ2.3: no longer a field). At the
non-affine transition `quadDiagF`. -/
theorem placableSharpRelief_chordStageRelief : placableSharpReliefBase.toChord.StageRelief :=
  placableSharpRelief.toChordCs.stageRelief_of_reliefSharp placableSharpRelief_relief_sharp

/-- **The two-branch relief margin fails:** `2ℓ·max(M_tot, k) = 6393/1750 > 297/100`. -/
theorem placableSharpRelief_not_relief_old :
    ¬ (2 * placableSharpRelief.ℓ * max placableSharpRelief.toChordCs.Mtot placableSharpRelief.k
      < placableSharpRelief.k * (placableSharpRelief.c - placableSharpRelief.n)) := by
  rw [placableSharpRelief_Mtot]
  norm_num [placableSharpRelief, placableSharpReliefBase]

/-- **The larger relief discharger applies here** (round J,
`reliefSharp_of_scaled_Mtot_le`): `u₀·M_tot = 2131/350 ≤ 9 = k·q`, although
`M_tot = 2131/700 > 3 = q`, so this member lies outside the `M_tot = q`
subfamily of `reliefSharp_of_Mtot_eq_q` and inside the larger one. -/
theorem placableSharpRelief_relief_disch :
    placableSharpRelief.u₀ * placableSharpRelief.toChordCs.Mtot
      ≤ placableSharpRelief.k * placableSharpRelief.q := by
  rw [placableSharpRelief_Mtot]
  norm_num [placableSharpRelief, placableSharpReliefBase]

theorem placableSharpRelief_Mtot_gt_q :
    placableSharpRelief.q < placableSharpRelief.toChordCs.Mtot := by
  rw [placableSharpRelief_Mtot]
  norm_num [placableSharpRelief, placableSharpReliefBase]

/-- The member's transition is not the affine law at any rate. -/
theorem placableSharpRelief_F_ne_affineF (δ : ℝ) :
    placableSharpRelief.F ≠ AbstractGame.affineF δ :=
  quadDiagF_ne_affineF δ

/-- Both cross coefficients are strictly positive. -/
theorem placableSharpRelief_cross_pos :
    0 < placableSharpRelief.r ∧ 0 < placableSharpRelief.n := by
  norm_num [placableSharpRelief, placableSharpReliefBase]

/-- **The Sender-only reading at the sharp-relief member**, through the sharp
constructor: the Target's unique optimum is the zero level, the realised
sanction is zero, the state washes out. -/
theorem placableSharpRelief_sender_only :
    (∀ x ∈ Sanctions.I,
      placableSharpRelief.toChordCs.myopicPolicy x
        < ((placableSharpRelief.toChordCs.senderOnlyEquilibriumTop'
            placableSharpRelief_chordInterior
            (placableSharpReliefBase.toChord_placable placableSharpReliefBase_placable))
            placableSharpRelief_relief_sharp placableSharpReliefBase.toChord_zeroSanctionNeutral).α
                x ∧
      placableSharpRelief.toChordCs.pS.dynamicEquilibriumRule
        ((placableSharpRelief.toChordCs.senderOnlyEquilibriumTop'
            placableSharpRelief_chordInterior
            (placableSharpReliefBase.toChord_placable placableSharpReliefBase_placable))
            placableSharpRelief_relief_sharp placableSharpReliefBase.toChord_zeroSanctionNeutral)
          x = 0) ∧
    (∀ x₀ ∈ Sanctions.I,
      Tendsto ((placableSharpRelief.toChordCs.senderOnlyPath' placableSharpRelief_chordInterior
          (placableSharpReliefBase.toChord_placable placableSharpReliefBase_placable))
          placableSharpRelief_relief_sharp placableSharpReliefBase.toChord_zeroSanctionNeutral x₀)
        atTop (𝓝 0)) := by
  obtain ⟨-, h2, h3⟩ := (placableSharpRelief.toChordCs.sender_only_regime_generalF'
      placableSharpRelief_chordInterior
    (placableSharpReliefBase.toChord_placable placableSharpReliefBase_placable))
    placableSharpRelief_relief_sharp placableSharpReliefBase.toChord_zeroSanctionNeutral
  exact ⟨fun x hx => ⟨(h2 x hx).1, (h2 x hx).2.2.2⟩, fun x₀ hx₀ => (h3 x₀ hx₀).2⟩

/-- **The four cells at the sharp-relief member** (rally margin empty: `Mmix = 0`
and `Mcx = 0`, so `SigC = 0`), in closed form. -/
theorem placableSharpRelief_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableSharpReliefBase.toChord.myopicPath
        placableSharpRelief_chordInterior placableSharpRelief_chordStageRelief
      (placableSharpReliefBase.toChord_placable placableSharpReliefBase_placable)) x₀) atTop
      (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableSharpRelief.toChordCs.senderOnlyPath'
        placableSharpRelief_chordInterior
      (placableSharpReliefBase.toChord_placable placableSharpReliefBase_placable))
      placableSharpRelief_relief_sharp placableSharpReliefBase.toChord_zeroSanctionNeutral x₀)
      atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (placableSharpReliefBase.toChord.targetOnlyPath
      placableSharpRelief_chordLossOffset x₀) atTop
      (𝓝 placableSharpReliefBase.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableSharpReliefBase.toChord.responsePath placableSharpReliefBase.toChord.VSstar z = z ∧
      placableSharpReliefBase.steady10 < z ∧
      Tendsto (placableSharpReliefBase.toChord.dynamicPath
        placableSharpRelief_chordLossOffset
        (placableSharpReliefBase.toChord_margin
          (placableSharpReliefBase.familyMargin_of_flat rfl rfl)) x₀)
        atTop (𝓝 z)) ∧
    0 < placableSharpReliefBase.steady10 :=
  placableSharpRelief.four_cell_closedForm placableSharpReliefBase_interior
    placableSharpReliefBase_margin
    placableSharpReliefBase_placable (placableSharpReliefBase.familyMargin_of_flat rfl rfl)
    placableSharpRelief_relief_sharp

/-- **Non-vacuity of the strict inclusion** (Rule 9A): there is a member, not the
affine law at any rate and with `r, n > 0`, inside the sharp sufficient class and
outside the two-branch one. Existence, and nothing more. -/
theorem exists_sharp_relief_member_not_old :
    ∃ E : PlacableEconomyFcs,
      (∀ δ, E.F ≠ AbstractGame.affineF δ) ∧ 0 < E.r ∧ 0 < E.n ∧
      E.ℓ * E.toChordCs.Mtot < E.k * (E.c - E.n) ∧
      ¬ (2 * E.ℓ * max E.toChordCs.Mtot E.k < E.k * (E.c - E.n)) :=
  ⟨placableSharpRelief, placableSharpRelief_F_ne_affineF,
    placableSharpRelief_cross_pos.1, placableSharpRelief_cross_pos.2,
    placableSharpRelief_relief_sharp, placableSharpRelief_not_relief_old⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.placableSharpRelief_four_cells
#print axioms Sanctions.Examples.exists_sharp_relief_member_not_old

end Examples
end Sanctions
