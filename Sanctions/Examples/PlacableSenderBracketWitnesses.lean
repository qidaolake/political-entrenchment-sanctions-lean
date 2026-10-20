/-
Sanctions/Examples/PlacableSenderBracketWitnesses.lean

**The bracket is inhabited on both sides, at the affine member and off the
affine law** (round AQ, 2026-09-23; doc 102 §2; Rule 9: existence certificates
and nothing more; read through the chord economy since round AV, 2026-09-25,
doc 104).

Two members of the enriched subclass differ from the pinned members
`placableAffineCs` and `placableQuadDiagCs` only in the Target's discount
factor, `β_T = 1/8` instead of `1/2`. At `β_T = 1/8` both relief sides hold
(the relief equilibrium exists, and the defiance profile is not a Target best
reply at its own values); at `β_T = 1/2` the sharp defiance side holds at
`g_T` (indeed the margin does). The probe `bracket_probe3_2026-09-23.py`
(exact rationals on a grid of step 1/400, archived) locates the two sides at
these members: at the affine member the relief side holds for `β_T ≤ 0.180` and
the sharp side at `g_T` from `β_T ≥ 0.185`; at the non-affine member for
`β_T ≤ 0.145` and from `β_T ≥ 0.2325`. At the affine member the gap comes from
the Sender's cross rate `r = 1/2` (through `L_resp`) and the supplied modulus
`σ_V = 1` together, not from the modulus alone; at the other the split chords
add to it. At a tight-modulus, rally-free affine member (`σ_V = 0`, `r = 0`) the
two sides are complementary, under the sixteen tightness equalities of
`collapse_sides` (a sufficient condition; `collapse_threshold`). The sharp side at
`g_T` certifies defiance where `g_T` is a certified slope, under the loss-offset
margin or where `L_resp = 0` (`gT_balance`, `gT_balance_of_Lresp_eq_zero`);
otherwise the certificate is the side at `gSharp` (`gSharp_balance`), which the
probe reports from `3/16` and `47/200`, and every such certificate implies the
side at `g_T` (`sharp_gT_of_sharp_of_balance`).

Rule 22: the non-affine member's transition is `quadDiagF`, refuted against
the affine law at every rate (`quadDiagF_ne_affineF`).

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority field;
the two low members' interiority is the pair of lemmas `affineLoC_interior`,
`quadDiagLoC_interior`, and the pinned members' loss-offset margins are read in their
chord forms (`placableAffine_chordLossOffset`, `placableQuadDiag_chordLossOffset`). The
statements are unchanged up to these proof-term arguments.
-/
import Sanctions.Examples.PlacableSenderBracket

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-- The affine member at `β_T = 1/8` (every other field as `placableAffineCs`). -/
def placableAffineLo : PlacableEconomyFcs :=
  { placableAffineCs with
    toPlacableEconomyF :=
      { placableAffine with βT := 1/8, hβT0 := by norm_num, hβT1 := by norm_num } }

/-- The non-affine member at `β_T = 1/8` (every other field as `placableQuadDiagCs`). -/
def placableQuadDiagLo : PlacableEconomyFcs :=
  { placableQuadDiagCs with
    toPlacableEconomyF :=
      { placableQuadDiag with βT := 1/8, hβT0 := by norm_num, hβT1 := by norm_num } }

/-- The two low members as enriched chord economies. -/
abbrev affineLoC : ChordEconomyCs := placableAffineLo.toChordCs
abbrev quadDiagLoC : ChordEconomyCs := placableQuadDiagLo.toChordCs

theorem placableAffineLo_placable : affineLoC.Placable := by
  change placableAffineLo.toPlacableEconomyF.Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableAffineLo, placableAffineCs, placableAffine]

theorem placableQuadDiagLo_placable : quadDiagLoC.Placable := by
  change placableQuadDiagLo.toPlacableEconomyF.Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableQuadDiagLo, placableQuadDiagCs, placableQuadDiag]

/-- Interiority at the affine low member, in the chord form (a field of the family until
renovation item BJ2.3, 2026-10-07, now a hypothesis). Affine-restricted. -/
theorem affineLoC_interior : affineLoC.Interior := by
  change placableAffineLo.toPlacableEconomyF.Interior
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableAffineLo, placableAffineCs, placableAffine]

/-- Interiority at the non-affine low member, in the chord form (renovation item BJ2.3).
At the non-affine transition `quadDiagF`. -/
theorem quadDiagLoC_interior : quadDiagLoC.Interior := by
  change placableQuadDiagLo.toPlacableEconomyF.Interior
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableQuadDiagLo, placableQuadDiagCs, placableQuadDiag]

theorem affineLoC_neutral : affineLoC.ZeroSanctionNeutral :=
  placableAffineLo.toPlacableEconomyF.toChord_zeroSanctionNeutral

theorem quadDiagLoC_neutral : quadDiagLoC.ZeroSanctionNeutral :=
  placableQuadDiagLo.toPlacableEconomyF.toChord_zeroSanctionNeutral

/-! ## The constants at the two low members -/

theorem placableAffineLo_mu : affineLoC.mu = 23/8 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableAffineLo, placableAffineCs, placableAffine]

theorem placableAffineLo_Lresp : affineLoC.Lresp = 5/8 := by
  norm_num [ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp, ChordEconomy.KS, chKS,
    ChordEconomyTwoSided.SigC, chSigC, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableAffineLo, placableAffineCs, placableAffine]

theorem placableAffineLo_Mtot : affineLoC.Mtot = 3 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo, placableAffineCs,
    placableAffine]

theorem placableAffineLo_LloopSharp : affineLoC.LloopSharp = 14/23 := by
  unfold ChordEconomyTwoSided.LloopSharp
  rw [placableAffineLo_Lresp, placableAffineLo_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo,
    placableAffineCs, placableAffine]

theorem placableAffineLo_KTrel : affineLoC.KTrel = 2224/69 := by
  unfold ChordEconomyCs.KTrel ChordEconomyCs.Lalpha
  rw [placableAffineLo_Mtot, placableAffineLo_Lresp, placableAffineLo_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo,
    placableAffineCs, placableAffine]

theorem placableAffineLo_KT : affineLoC.KT = 568/17 := by
  unfold ChordEconomyRelief.KT ChordEconomyRelief.LUT
  rw [placableAffineLo_LloopSharp, placableAffineLo_Lresp, placableAffineLo_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo,
    placableAffineCs, placableAffine]

theorem placableQuadDiagLo_mu : quadDiagLoC.mu = 141/50 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableQuadDiagLo, placableQuadDiagCs, placableQuadDiag]

theorem placableQuadDiagLo_Lresp : quadDiagLoC.Lresp = 17/25 := by
  norm_num [ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp, ChordEconomy.KS, chKS,
    ChordEconomyTwoSided.SigC, chSigC, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableQuadDiagLo, placableQuadDiagCs, placableQuadDiag]

theorem placableQuadDiagLo_Mtot : quadDiagLoC.Mtot = 45/14 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

theorem placableQuadDiagLo_LloopSharp : quadDiagLoC.LloopSharp = 35/47 := by
  unfold ChordEconomyTwoSided.LloopSharp
  rw [placableQuadDiagLo_Lresp, placableQuadDiagLo_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

theorem placableQuadDiagLo_KTrel : quadDiagLoC.KTrel = 398200/12173 := by
  unfold ChordEconomyCs.KTrel ChordEconomyCs.Lalpha
  rw [placableQuadDiagLo_Mtot, placableQuadDiagLo_Lresp, placableQuadDiagLo_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

theorem placableQuadDiagLo_KT : quadDiagLoC.KT = 34928/1023 := by
  unfold ChordEconomyRelief.KT ChordEconomyRelief.LUT
  rw [placableQuadDiagLo_LloopSharp, placableQuadDiagLo_Lresp, placableQuadDiagLo_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

/-! ## The relief side at `β_T = 1/8` -/

theorem placableAffineLo_γ : affineLoC.β_T * affineLoC.LloopSharp < 1 := by
  rw [placableAffineLo_LloopSharp]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo,
    placableAffineCs, placableAffine]

theorem placableQuadDiagLo_γ : quadDiagLoC.β_T * quadDiagLoC.LloopSharp < 1 := by
  rw [placableQuadDiagLo_LloopSharp]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

/-- The relief equilibrium exists at the affine member with `β_T = 1/8`:
`3 < 3·(4 − 2224/1104)`. -/
theorem placableAffineLo_relief_exists :
    affineLoC.ℓhi * affineLoC.Mtot
      < affineLoC.klo * (affineLoC.plo - affineLoC.β_T * affineLoC.dhi * affineLoC.KTrel) := by
  rw [placableAffineLo_Mtot, placableAffineLo_KTrel]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo,
    placableAffineCs, placableAffine]

/-- Defiance is not a best reply at the affine member with `β_T = 1/8`. -/
theorem placableAffineLo_relief_notdef :
    affineLoC.ℓhi * affineLoC.Mtot
      < affineLoC.klo * (affineLoC.plo - affineLoC.β_T * affineLoC.dhi * affineLoC.KT) := by
  rw [placableAffineLo_Mtot, placableAffineLo_KT]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineLo,
    placableAffineCs, placableAffine]

theorem placableQuadDiagLo_relief_exists :
    quadDiagLoC.ℓhi * quadDiagLoC.Mtot
      < quadDiagLoC.klo
          * (quadDiagLoC.plo - quadDiagLoC.β_T * quadDiagLoC.dhi * quadDiagLoC.KTrel) := by
  rw [placableQuadDiagLo_Mtot, placableQuadDiagLo_KTrel]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

theorem placableQuadDiagLo_relief_notdef :
    quadDiagLoC.ℓhi * quadDiagLoC.Mtot
      < quadDiagLoC.klo
          * (quadDiagLoC.plo - quadDiagLoC.β_T * quadDiagLoC.dhi * quadDiagLoC.KT) := by
  rw [placableQuadDiagLo_Mtot, placableQuadDiagLo_KT]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagLo,
    placableQuadDiagCs, placableQuadDiag]

/-- **The relief equilibrium at the affine member with `β_T = 1/8`**: the
forward-looking Target complies at the zero level, the realised sanction is
zero at every state. -/
noncomputable def placableAffineLo_reliefEquilibrium :
    affineLoC.toParams.FeedbackStackelbergEquilibriumTop :=
  affineLoC.reliefEquilibriumTop affineLoC_interior placableAffineLo_placable
      placableAffineLo_relief_exists
    affineLoC_neutral

theorem placableAffineLo_relief_rule_zero :
    ∀ x ∈ Sanctions.I,
      affineLoC.toParams.dynamicEquilibriumRule placableAffineLo_reliefEquilibrium x = 0 :=
  fun _ hx => affineLoC.reliefEquilibriumTop_rule_eq_zero affineLoC_interior
      placableAffineLo_placable
    placableAffineLo_relief_exists affineLoC_neutral hx

/-- **The relief equilibrium off the affine law** (`quadDiagF`, `β_T = 1/8`). -/
noncomputable def placableQuadDiagLo_reliefEquilibrium :
    quadDiagLoC.toParams.FeedbackStackelbergEquilibriumTop :=
  quadDiagLoC.reliefEquilibriumTop quadDiagLoC_interior placableQuadDiagLo_placable
    placableQuadDiagLo_relief_exists quadDiagLoC_neutral

theorem placableQuadDiagLo_relief_rule_zero :
    ∀ x ∈ Sanctions.I,
      quadDiagLoC.toParams.dynamicEquilibriumRule placableQuadDiagLo_reliefEquilibrium x = 0 :=
  fun _ hx => quadDiagLoC.reliefEquilibriumTop_rule_eq_zero quadDiagLoC_interior
      placableQuadDiagLo_placable
    placableQuadDiagLo_relief_exists quadDiagLoC_neutral hx

/-- **On the relief side defiance is not a best reply, off the affine law.** -/
theorem placableQuadDiagLo_defiance_not_maxOn {x : ℝ} (hx : x ∈ Sanctions.I) :
    ¬ IsMaxOn (fun a => quadDiagLoC.toParams.joint_T_integrand quadDiagLoC.VTdef
      quadDiagLoC.VSstar x a) Sanctions.I 0 :=
  quadDiagLoC.defiance_not_maxOn_of_relief_side quadDiagLoC_interior
      placableQuadDiagLo_placable
    placableQuadDiagLo_γ placableQuadDiagLo_relief_notdef hx

/-! ## The sharp defiance side at `β_T = 1/2` (the pinned members) -/

theorem placableAffine_gT : placableAffine.toChord.gT = 40 := by
  norm_num [ChordEconomy.gT, PlacableEconomyF.toChord, placableAffine]

theorem placableQuadDiag_gT : placableQuadDiag.toChord.gT = 75/2 := by
  norm_num [ChordEconomy.gT, PlacableEconomyF.toChord, placableQuadDiag]

theorem placableAffine_mu : placableAffine.toChord.mu = 23/8 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyF.toChord,
    placableAffine]

theorem placableQuadDiag_mu : placableQuadDiag.toChord.mu = 141/50 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyF.toChord,
    placableQuadDiag]

/-- The sharp defiance side at `g_T` holds at the affine member: `4 − 23/24 < 10`. -/
theorem placableAffine_sharp :
    placableAffine.toChord.c - placableAffine.toChord.ℓlo * placableAffine.toChord.mu
        / placableAffine.toChord.khi
      < placableAffine.toChord.β_T * placableAffine.toChord.dlo * placableAffine.toChord.gT := by
  rw [placableAffine_mu, placableAffine_gT]
  norm_num [PlacableEconomyF.toChord, placableAffine]

theorem placableQuadDiag_sharp :
    placableQuadDiag.toChord.c - placableQuadDiag.toChord.ℓlo * placableQuadDiag.toChord.mu
        / placableQuadDiag.toChord.khi
      < placableQuadDiag.toChord.β_T * placableQuadDiag.toChord.dlo
        * placableQuadDiag.toChord.gT := by
  rw [placableQuadDiag_mu, placableQuadDiag_gT]
  norm_num [PlacableEconomyF.toChord, placableQuadDiag]

/-- **The sharp-side equilibrium at the affine member**: `g = g_T` balances under
the margin, so the composed defiance equilibrium is the sharp-side one. -/
noncomputable def placableAffine_sharpEquilibrium :
    placableAffine.toChord.toParams.FeedbackStackelbergEquilibriumTop :=
  placableAffine.toChord.equilibriumTop_sharp
    (placableAffine.toChord.responsePath_monotoneOn_of_margin placableAffine_rallyMargin)
    placableAffine.toChord.gT_pos.le
    (placableAffine.toChord.gT_balance placableAffine_chordLossOffset)
    placableAffine_sharp.le

noncomputable def placableQuadDiag_sharpEquilibrium :
    placableQuadDiag.toChord.toParams.FeedbackStackelbergEquilibriumTop :=
  placableQuadDiag.toChord.equilibriumTop_sharp
    (placableQuadDiag.toChord.responsePath_monotoneOn_of_margin placableQuadDiag_rallyMargin)
    placableQuadDiag.toChord.gT_pos.le
    (placableQuadDiag.toChord.gT_balance
      placableQuadDiag_chordLossOffset)
    placableQuadDiag_sharp.le

/-- **Both sides witnessed off the affine law** (Rule 9B, Rule 22): the
non-affine transition carries a relief equilibrium at `β_T = 1/8` and a
defiance equilibrium at `β_T = 1/2`, and the two members differ only in `β_T`. -/
theorem exists_bracket_both_sides_nonaffine :
    (∃ (E : ChordEconomyCs) (hInt : E.Interior) (hP : E.Placable)
        (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
        (hN : E.ZeroSanctionNeutral),
        E.F ≠ AbstractGame.affineF E.δ ∧
        ∀ x ∈ Sanctions.I,
          E.toParams.dynamicEquilibriumRule (E.reliefEquilibriumTop hInt hP hrel hN) x = 0) ∧
    (∃ (E : ChordEconomyRelief) (hTM : E.LossOffset)
        (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
        (hsharp : E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT),
        E.F ≠ AbstractGame.affineF E.δ ∧
        ∀ x, (E.equilibriumTop_sharp hmono E.gT_pos.le (E.gT_balance hTM) hsharp.le).α x = 0) :=
  ⟨⟨quadDiagLoC, quadDiagLoC_interior, placableQuadDiagLo_placable,
      placableQuadDiagLo_relief_exists,
      quadDiagLoC_neutral, placableQuadDiag_F_ne_affineF _, placableQuadDiagLo_relief_rule_zero⟩,
   ⟨placableQuadDiag.toChord, placableQuadDiag_chordLossOffset,
      placableQuadDiag.toChord.responsePath_monotoneOn_of_margin placableQuadDiag_rallyMargin,
      placableQuadDiag_sharp, placableQuadDiag_F_ne_affineF _, fun _ => rfl⟩⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp
#print axioms Sanctions.Examples.ChordEconomy.targetObj_antitoneOn_of_sharp_le
#print axioms Sanctions.Examples.ChordEconomyRelief.targetOp_mem_lowerSlopeCone
#print axioms Sanctions.Examples.ChordEconomyRelief.VTdef_lowerSlope
#print axioms Sanctions.Examples.ChordEconomyRelief.equilibriumTop_sharp
#print axioms Sanctions.Examples.ChordEconomyRelief.gSharp_balance
#print axioms Sanctions.Examples.ChordEconomyRelief.gSharp_balance_lo
#print axioms Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz
#print axioms Sanctions.Examples.ChordEconomyCs.VTrel_lipschitz
#print axioms Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop
#print axioms Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side
#print axioms Sanctions.Examples.ChordEconomyCs.bracket_sides_disjoint
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_sides
#print axioms Sanctions.Examples.placableAffineLo_reliefEquilibrium
#print axioms Sanctions.Examples.exists_bracket_both_sides_nonaffine

end Examples
end Sanctions
