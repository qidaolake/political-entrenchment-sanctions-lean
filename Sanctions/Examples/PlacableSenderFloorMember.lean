/-
Sanctions/Examples/PlacableSenderFloorMember.lean

**A non-affine member inside the floor-refined loss-offset class and outside
the previous one** (round J, doc 77 K2; the reader's package
`suggestions/2026-09-09-round-I-validation/`, doc 01 §1).

Round J weakened the family's loss-offset margin from `c ≤ β_T·d_lo·v/(1 − β_T·glo)`
to `c ≤ β_T·d_lo·(v + n·u₀/q)/(1 − β_T·glo)` (`PlacableEconomyF.LossOffset`, a hypothesis since round AP,
`plGTn`): the Target value's lower state slope now carries the rally term `n`
at the response floor `u₀/q`, which the previous Target-carrier proof discarded
(`targetOp_mem_of_monotone`, `responsePath_ge_b`). This file shows the
weakening is not empty: at the transition `quadDiagF` — proved not the affine
law at any rate — with the sharp-relief member's coefficients and the Target's
state valuation lowered to `v = 1199/300`,

    (q, u₀, k, r, w, ℓ, c, n, v) = (3, 2, 3, 1/100, 3/10, 3/5, 1, 1/100, 1199/300),

the previous margin fails (`β_T·d_lo·v/(1 − β_T·glo) = 1199/1200 < 1 = c`), the
floor-refined one holds (`1 ≤ 1201/1200`), every other family field holds, the
sharp relief margin holds and the two-branch one fails. Both cross coefficients
`r` and `n` are strictly positive. The separation persists for every
`v ∈ (599/150, 4)`, an interval of width `1/150` in one coefficient
(`docs/archive/workflow-scratch/round_J_stage0_check.py`), so the member is not
a knife edge in `v` (Rule 9C).

Rule 9: an existence certificate. It licenses "the floor-refined loss-offset
class strictly contains the previous one, off the affine law" and nothing about
genericity, magnitudes or necessity. The transition proofs are those of
`placableQuadDiag` (`PlacableSenderWitnesses`), reused verbatim; the scalar
fields are `norm_num`. Rule 3: no new assumption — the field weakened is the
one the previous form implied (`hTMargin_of_old`).
Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and
stage relief fields (only the sign field `hcn : n < c`). The member's interiority is the
lemma `placableFloorBase_interior` (chord forms `placableFloor_chordInterior`,
`placableFloor_chordLossOffset`), and the myopic cell's stage relief margin comes from
the sharp relief margin (`stageRelief_of_reliefSharp`, BG3.2;
`placableFloor_chordStageRelief`); the statements below are unchanged up to these proof
terms.
-/
import Sanctions.Examples.PlacableSenderRegime01

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame

noncomputable section

/-- The base member: `quadDiagF` with the floor coefficients. -/
def placableFloorBase : PlacableEconomyF where
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
  v := 1199/300
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

/-- Placability at `placableFloorBase` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableFloorBase_placable : placableFloorBase.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableFloorBase]

/-- The loss-offset margin at `placableFloorBase` (a hypothesis since round AP). -/
theorem placableFloorBase_margin : placableFloorBase.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableFloorBase]

/-- Interiority at `placableFloorBase` (a field of the family until renovation item
BJ2.3, 2026-10-07, now a hypothesis). At the non-affine transition `quadDiagF`. -/
theorem placableFloorBase_interior : placableFloorBase.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableFloorBase]

/-- The enriched member: sanction-section modulus `1/5` at `quadDiagF`. -/
def placableFloor : PlacableEconomyFcs where
  toPlacableEconomyF := placableFloorBase
  Mcs := 1/5
  hMcs0 := by norm_num
  hFcs := quadDiagF_cs

theorem placableFloor_base : placableFloor.toPlacableEconomyF = placableFloorBase := rfl

/-- The member's interiority in the chord form (renovation item BJ2.3). At the
non-affine transition `quadDiagF`. -/
theorem placableFloor_chordInterior : placableFloor.toChordCs.Interior :=
  placableFloor.toChordCs_interior placableFloorBase_interior

/-- The member's loss-offset margin in the chord form; the floor condition `u₀ ≤ q`
comes from interiority (renovation item BJ2.3). At the non-affine transition
`quadDiagF`. -/
theorem placableFloor_chordLossOffset : placableFloorBase.toChord.LossOffset :=
  placableFloorBase.toChord_lossOffset (placableFloorBase.u₀_le_q placableFloorBase_interior)
    placableFloorBase_margin

/-- **The previous loss-offset form fails here**: `β_T·d_lo·v/(1 − β_T·glo) = 1199/1200 < 1 = c`. -/
theorem placableFloor_not_old_loss :
    ¬ (placableFloor.c ≤ placableFloor.βT * placableFloor.dlo
        * plGT placableFloor.βT placableFloor.glo placableFloor.v) := by
  unfold plGT
  norm_num [placableFloor, placableFloorBase]

/-- **The floor-refined form holds**: `β_T·d_lo·(v + n·u₀/q)/(1 − β_T·glo) = 1201/1200 ≥ 1 = c`
(the margin, a hypothesis of the family since round AP, restated). -/
theorem placableFloor_loss_floor :
    placableFloor.c ≤ placableFloor.βT * placableFloor.dlo
      * plGTn placableFloor.βT placableFloor.glo placableFloor.v placableFloor.n
          placableFloor.u₀ placableFloor.q :=
  placableFloorBase_margin

/-- `M_tot = 2131/700`, as at the sharp-relief member (the Sender constants do
not depend on `v`). -/
theorem placableFloor_Mtot : placableFloor.toChordCs.Mtot = 2131 / 700 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableFloor, placableFloorBase]

/-- The sharp relief margin holds: `6393/3500 < 297/100`. -/
theorem placableFloor_relief_sharp :
    placableFloor.ℓ * placableFloor.toChordCs.Mtot
      < placableFloor.k * (placableFloor.c - placableFloor.n) := by
  rw [placableFloor_Mtot]
  norm_num [placableFloor, placableFloorBase]

/-- The member's stage relief margin in the chord form, from the sharp relief margin
(`stageRelief_of_reliefSharp`, BG3.2; renovation item BJ2.3: no longer a field). At the
non-affine transition `quadDiagF`. -/
theorem placableFloor_chordStageRelief : placableFloorBase.toChord.StageRelief :=
  placableFloor.toChordCs.stageRelief_of_reliefSharp placableFloor_relief_sharp

/-- The two-branch relief margin fails: `6393/1750 > 297/100`. -/
theorem placableFloor_not_relief_old :
    ¬ (2 * placableFloor.ℓ * max placableFloor.toChordCs.Mtot placableFloor.k
      < placableFloor.k * (placableFloor.c - placableFloor.n)) := by
  rw [placableFloor_Mtot]
  norm_num [placableFloor, placableFloorBase]

/-- The member's transition is not the affine law at any rate. -/
theorem placableFloor_F_ne_affineF (δ : ℝ) : placableFloor.F ≠ AbstractGame.affineF δ :=
  quadDiagF_ne_affineF δ

/-- Both cross coefficients are strictly positive. -/
theorem placableFloor_cross_pos : 0 < placableFloor.r ∧ 0 < placableFloor.n := by
  norm_num [placableFloor, placableFloorBase]

/-- **The four cells at the floor member** (rally margin empty: `Mmix = 0` and
`Mcx = 0`), in closed form: the family theorem's instance, with the Target
defying under the floor-refined margin alone. -/
theorem placableFloor_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableFloorBase.toChord.myopicPath
        placableFloor_chordInterior placableFloor_chordStageRelief
      (placableFloorBase.toChord_placable placableFloorBase_placable)) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableFloor.toChordCs.senderOnlyPath'
        placableFloor_chordInterior
      (placableFloorBase.toChord_placable placableFloorBase_placable) placableFloor_relief_sharp
      placableFloorBase.toChord_zeroSanctionNeutral) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (placableFloorBase.toChord.targetOnlyPath
      placableFloor_chordLossOffset x₀) atTop
      (𝓝 placableFloorBase.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableFloorBase.toChord.responsePath placableFloorBase.toChord.VSstar z = z ∧
      placableFloorBase.steady10 < z ∧
      Tendsto (placableFloorBase.toChord.dynamicPath
        placableFloor_chordLossOffset
        (placableFloorBase.toChord_margin (placableFloorBase.familyMargin_of_flat rfl rfl)) x₀)
        atTop (𝓝 z)) ∧
    0 < placableFloorBase.steady10 :=
  placableFloor.four_cell_closedForm placableFloorBase_interior placableFloorBase_margin
    placableFloorBase_placable
    (placableFloorBase.familyMargin_of_flat rfl rfl) placableFloor_relief_sharp

/-- **Non-vacuity of the strict inclusion** (Rule 9A): there is a member of the
enriched subclass, not the affine law at any rate and with `r, n > 0`, inside
the floor-refined loss-offset class and outside the previous one. Existence,
and nothing more. -/
theorem exists_floor_member_not_old :
    ∃ E : PlacableEconomyFcs,
      (∀ δ, E.F ≠ AbstractGame.affineF δ) ∧ 0 < E.r ∧ 0 < E.n ∧
      ¬ (E.c ≤ E.βT * E.dlo * plGT E.βT E.glo E.v) :=
  ⟨placableFloor, placableFloor_F_ne_affineF, placableFloor_cross_pos.1,
    placableFloor_cross_pos.2, placableFloor_not_old_loss⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.placableFloor_four_cells
#print axioms Sanctions.Examples.exists_floor_member_not_old

end Examples
end Sanctions
