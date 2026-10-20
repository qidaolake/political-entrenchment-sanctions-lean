/-
Sanctions/Examples/PlacableSenderReliefActivation.lean

**Both channels active on the enriched subclass under the relief margin alone,
with no stage flip** (round Q2, 2026-09-11; doc 85 §3, on the user's word; the
reader's 2026-09-11 package, document 02; on the abstract payoffs since round
AV, 2026-09-25, doc 104).

`both_channels_active_of_margin` (headline row 32) shows the Target channel
active through the *endpoint* stage comparison: full compliance beats full
defiance at the stage, which is the stage flip `ℓ_hi < b·p_lo`, a hypothesis of
that theorem. This file shows the same conclusion on the enriched subclass
`ChordEconomyCs` under the relief margin (RL), `ℓ_hi·M_tot < k_lo·p_lo`, through
a *small* compliance instead. At the Sender's equilibrium value the response at
defiance is positive; it falls by at most `k_hi·a/μ` when compliance rises to
`a` (`response_sub_le_of_le`), so for `a` small it stays positive; and then the
sharp relief rate `ρ(x,0) − ρ(x,a) ≥ k_lo·a/M_tot` makes the Target's stage
payoff at `a` exceed its stage payoff at defiance by at least
`a·(k_lo·p_lo/M_tot − ℓ_hi) > 0`. Full defiance is still the unique
forward-looking optimum (`targetArgmax_eq_zero`, untouched), so it is not a
stage optimum: the Target channel is active with no comparison at full
compliance anywhere. No zero-sanction neutrality is read.

The reader's affine example makes the point Rule 9 allows: `placableReliefOnly`
satisfies (RL) (`6 < 12`) and fails the flip (`6 < 4` is false): the enriched
relief class admits members failing the endpoint flip, so on it the flip is
sufficient and not necessary for both channels' activation. Existence only;
nothing about how many members.

Rule 22: the theorems are general in `F`; the example is affine and marked so.
Rule 9C: the example's margins were checked in exact arithmetic by the reader
(`validation_checks.py`, 71 checks) before any Lean was written.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderBracket

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords

noncomputable section

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## 1. The relief rate at any carrier value, interiority supplied -/

/-- **The sharp relief rate at any carrier value**: between `a < a'` in `[0,1]`
with the response at `a'` positive, `ρ(a) − ρ(a') ≥ k_lo(a' − a)/M_tot` (the
zero-level form is `response_shift_ge_linear_at`; here the interiority is
supplied). -/
theorem response_shift_ge_linear_carrier (hInt : E.Interior) {V : Val} (hV : V ∈ E.carrierS2) {x :
    ℝ}
    (hx : x ∈ Sanctions.I) {a a' : ℝ} (ha : 0 ≤ a) (haa' : a < a') (ha'1 : a' ≤ 1)
    (hint : 0 < E.response V x a') :
    E.klo * (a' - a) / E.Mtot ≤ E.response V x a - E.response V x a' := by
  have haI : a ∈ Sanctions.I := ⟨ha, by linarith⟩
  have ha'I : a' ∈ Sanctions.I := ⟨by linarith, ha'1⟩
  exact Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_tilt_of_semiconvex_interior
    E.Mtot_pos (E.senderObj_semiconvex_carrier hV hx ha'I)
    (E.senderObj_semiconvex_carrier hV hx haI) hint
    (E.response_lt_one hInt hV.1 hx ha'I) (E.response_isMaxOn _ x a')
    (mul_pos E.hklo (by linarith)) (E.response_mem _ x a)
    (E.response_lt_one hInt hV.1 hx haI) (E.response_isMaxOn _ x a)
    (fun u₁ hu₁ u₂ hu₂ hu => by
      have hdd := E.hUS_placLo x hx a haI a' ha'I u₁ hu₁ u₂ hu₂ haa'.le hu
      simp only [senderObj]
      nlinarith [hdd])

/-! ## 2. A small compliance keeps the response positive -/

/-- **The response falls by at most `k_hi·a/μ` between defiance and compliance
`a`** (and does not rise): the objective at `a` differs from the objective at
defiance by a perturbation of cross rate at most `k_hi·a` (S10u), and the sharp
argmax stability bounds the shift by that rate over the strong-concavity
modulus. -/
theorem response_dist_le_of_compliance {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    |E.response V x 0 - E.response V x a| ≤ E.khi * a / E.mu := by
  have h1 := E.response_sub_le_of_le E.placationCeiling hV hx zero_mem_I ha ha.1
  have h2 : E.response V x a ≤ E.response V x 0 :=
    E.response_antitoneOn_a hV hx zero_mem_I ha ha.1
  rw [abs_of_nonneg (by linarith)]
  simpa using h1

/-! ## 3. The stage gain of a small compliance under (RL) -/

/-- **A small compliance beats defiance at the stage, at the equilibrium value,
under (RL)**: with the response at `a` still positive, the relief it buys is at
least `k_lo·a/M_tot`, worth at least `p_lo` per unit in pain (T2), against a
cost of at most `ℓ_hi·a` (T4u). -/
theorem targetStage_small_gain (hInt : E.Interior) (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hpos : 0 < E.response E.VSstar x a) :
    E.toParams.U_T x 0 (E.response E.VSstar x 0)
      < E.toParams.U_T x a (E.response E.VSstar x a) := by
  have hshift := E.response_shift_ge_linear_carrier hInt E.VSstar_mem2 hx (le_refl 0) ha0 ha1 hpos
  have haI : a ∈ Sanctions.I := ⟨ha0.le, ha1⟩
  have hρ0 := E.response_mem E.VSstar x 0
  have hρa := E.response_mem E.VSstar x a
  have hanti : E.response E.VSstar x a ≤ E.response E.VSstar x 0 :=
    E.response_antitoneOn_a E.VSstar_mem hx zero_mem_I haI ha0.le
  have hstage := E.UT_sub_ge hx zero_mem_I haI hρ0 hρa ha0.le hanti
  have hM := E.Mtot_pos
  have h1 : E.klo * (a - 0) / E.Mtot * E.plo
      ≤ (E.response E.VSstar x 0 - E.response E.VSstar x a) * E.plo :=
    mul_le_mul_of_nonneg_right hshift E.hplo.le
  have h2 : E.ℓhi * a < E.klo * (a - 0) / E.Mtot * E.plo := by
    rw [sub_zero, div_mul_eq_mul_div, lt_div_iff₀ hM]
    have := mul_lt_mul_of_pos_right hrelief ha0
    nlinarith [this]
  change E.U_T x 0 (E.response E.VSstar x 0) < E.U_T x a (E.response E.VSstar x a)
  nlinarith [h1, h2, hstage]

/-- **The Target channel is active under (RL), at every Target carrier value and
every state, with no stage flip**: the forward-looking optimum is full defiance
(`targetArgmax_eq_zero`), and a compliance `a ≤ min(1, μρ(x,0)/(2k_hi))`, which
keeps the response positive, beats it at the stage. -/
theorem target_channel_active_of_relief (hInt : E.Interior) (hTM : E.LossOffset)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    {V_T : Val} (hV_T : V_T ∈ E.carrierT) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.ContinuationChangesTargetChoiceAt (fun y b => E.response E.VSstar y b) V_T x := by
  intro a ha hdyn hstage
  have hdyn' : IsMaxOn (fun b => E.toParams.joint_T_integrand V_T E.VSstar x b) Sanctions.I a :=
    hdyn
  have ha0 : a = 0 := E.targetArgmax_eq_zero hTM hV_T E.VSstar_mem hx ha hdyn'
  subst ha0
  have hk := E.khi_pos
  have hμ := E.mu_pos
  have hρ0 : 0 < E.response E.VSstar x 0 := E.responsePath_pos E.VSstar_mem hx
  set a₁ := min (1 : ℝ) (E.mu * E.response E.VSstar x 0 / (2 * E.khi)) with ha₁def
  have ha₁pos : 0 < a₁ := lt_min one_pos (by positivity)
  have ha₁I : a₁ ∈ Sanctions.I := ⟨ha₁pos.le, min_le_left _ _⟩
  have hsmall : E.khi * a₁ / E.mu < E.response E.VSstar x 0 := by
    have h1 : a₁ ≤ E.mu * E.response E.VSstar x 0 / (2 * E.khi) := min_le_right _ _
    have h2 : E.khi * a₁ / E.mu
        ≤ E.khi * (E.mu * E.response E.VSstar x 0 / (2 * E.khi)) / E.mu :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hk.le) hμ.le
    have h3 : E.khi * (E.mu * E.response E.VSstar x 0 / (2 * E.khi)) / E.mu
        = E.response E.VSstar x 0 / 2 := by
      have hk' : E.khi ≠ 0 := hk.ne'
      have hμ' : E.mu ≠ 0 := hμ.ne'
      field_simp
    linarith
  have hpos : 0 < E.response E.VSstar x a₁ := by
    have h := E.response_dist_le_of_compliance E.VSstar_mem hx ha₁I
    have := (abs_le.mp h).2
    linarith
  have hgain := E.targetStage_small_gain hInt hrelief hx ha₁pos ha₁I.2 hpos
  have h := hstage ha₁I
  simp only [Set.mem_setOf_eq] at h
  exact absurd h (not_le.mpr hgain)

/-! ## 4. Both channels, under the rally and relief margins alone -/

/-- **Both channels active at the composed equilibrium under (RL), with no stage
flip**, given a monotone response: the Sender side as in
`both_channels_active_of_response_monotone`, the Target side through the small
compliance. -/
theorem both_channels_active_of_relief_response_monotone (hInt : E.Interior)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt (E.equilibriumTop hTM hmono).V_S x
        ((E.equilibriumTop hTM hmono).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.equilibriumTop hTM hmono).V_S y b)
          (E.equilibriumTop hTM hmono).V_T x :=
  fun x hx => ⟨E.sender_channel_active (E.uhi_lt_q hInt) hx,
    (E.target_channel_active_of_relief hInt hTM) hrelief (E.VTstar_mem hTM hmono) hx⟩

/-- **Both channels active on the enriched subclass under the rally margin and
the relief margin alone** (headline row 41, round Q2): at every state of the
composed equilibrium, no forward-looking Sender maximiser is a stage maximiser
and no forward-looking Target maximiser is a stage maximiser — with no stage
flip. Row 32 is the same conclusion on the base class under the flip. -/
theorem both_channels_active_of_relief (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt ((E.equilibriumTop_of_margin hTM) hmargin).V_S x
        (((E.equilibriumTop_of_margin hTM) hmargin).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response ((E.equilibriumTop_of_margin hTM) hmargin).V_S y b)
          ((E.equilibriumTop_of_margin hTM) hmargin).V_T x :=
  E.both_channels_active_of_relief_response_monotone hInt hrelief hTM
    (E.responsePath_monotoneOn_of_margin hmargin)

end ChordEconomyCs

/-! ## 5. The example: (RL) holds and the flip fails (the reader's document 02 §4)

`(q, u₀, k, r, w, ℓ, c, n, v) = (3, 1, 3, 0, 1, 2, 4, 0, 30)`, the affine law
at rate `1/2`, both discounts `1/2`, supplied modulus `σ_V = 0`, `M_cs = 0`.
Then `K_S = A = 4/3`, `μ = M_tot = 3`; interiority `4/3 < 3`, placability
`4/3 ≤ 3`, the stage relief margin `6 < 12`, the loss offset `4 ≤ 10`, the
rally margin `0 ≤ 0`, and (RL) `6 < 12` all hold — while the stage flip would
read `6 < 4`. The member is read as a chord economy through `toChordCs`. Rule
22: affine-restricted and marked so. Since renovation item BJ2.3 (2026-10-07)
interiority and the stage relief margin are not fields of the family: the member's
interiority is the lemma `placableReliefOnly_interior`, its stage relief margin comes
from (RL) (`stageRelief_of_reliefSharp`), and the results read their chord forms. -/

/-- The member. -/
def placableReliefOnly : PlacableEconomyFcs where
  toPlacableEconomyF :=
    { F := AbstractGame.affineF (1/2)
      F_continuous := AbstractGame.affineF_continuous _
      F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
      F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
      F_diag := AbstractGame.affineF_diag _
      glo := 1/2
      ghi := 1/2
      dlo := 1/2
      dhi := 1/2
      Mx := 0
      Mm := 0
      Ms := 0
      hbandAll := affineF_half_bandAll
      hSlo := affineF_half_lo
      hShi := affineF_half_hi
      hFjsc := affineF_half_jsc
      hglo0 := by norm_num
      hghi1 := by norm_num
      hdlo0 := by norm_num
      hMx0 := by norm_num
      hMm0 := by norm_num
      hMs0 := by norm_num
      Mcx := 0
      hMcx0 := by norm_num
      hFcx := affineF_half_cx
      Mmix := 0
      hFmix := affineF_half_mix
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
      u₀ := 1
      k := 3
      r := 0
      w := 1
      ℓ := 2
      c := 4
      n := 0
      v := 30
      hu₀ := by norm_num
      hr := by norm_num
      hw := by norm_num
      hℓ := by norm_num
      hn := by norm_num
      SigV := 0
      hCurv := by norm_num [plKS]
      hSigV := by norm_num [plSigImg, plSig, plRho, plMu, plKS]
      hk := by norm_num
      hv := by norm_num
      hcn := by norm_num }
  Mcs := 0
  hMcs0 := by norm_num
  hFcs := affineF_half_cs

/-- Placability at `placableReliefOnly` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableReliefOnly_placable : placableReliefOnly.toPlacableEconomyF.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableReliefOnly]

/-- The loss-offset margin at `placableReliefOnly` (a hypothesis since round AP). -/
theorem placableReliefOnly_lossOffset : placableReliefOnly.toPlacableEconomyF.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableReliefOnly]

/-- Interiority at `placableReliefOnly`: `A = 4/3 < 3 = q` (a field of the family until
renovation item BJ2.3, 2026-10-07, now a hypothesis). Affine-restricted. -/
theorem placableReliefOnly_interior : placableReliefOnly.toPlacableEconomyF.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableReliefOnly]

/-- The member's interiority in the chord form (renovation item BJ2.3). Affine-restricted. -/
theorem placableReliefOnly_chordInterior : placableReliefOnly.toChordCs.Interior :=
  placableReliefOnly.toChordCs_interior placableReliefOnly_interior

/-- The member's loss-offset margin in the chord form; the floor condition `u₀ ≤ q` comes
from interiority (renovation item BJ2.3). Affine-restricted. -/
theorem placableReliefOnly_chordLossOffset :
    placableReliefOnly.toPlacableEconomyF.toChord.LossOffset :=
  placableReliefOnly.toPlacableEconomyF.toChord_lossOffset
    (placableReliefOnly.toPlacableEconomyF.u₀_le_q placableReliefOnly_interior)
    placableReliefOnly_lossOffset

/-- **The stage flip fails at the member**: `6 < 4` is false. -/
theorem placableReliefOnly_not_flip :
    ¬ (placableReliefOnly.ℓ * placableReliefOnly.q
        < placableReliefOnly.u₀ * (placableReliefOnly.c - placableReliefOnly.n)) := by
  norm_num [placableReliefOnly]

theorem placableReliefOnly_Mtot : placableReliefOnly.toChordCs.Mtot = 3 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableReliefOnly]

/-- **(RL) holds at the member**: `6 < 12`. -/
theorem placableReliefOnly_relief :
    placableReliefOnly.ℓ * placableReliefOnly.toChordCs.Mtot
      < placableReliefOnly.k * (placableReliefOnly.c - placableReliefOnly.n) := by
  rw [placableReliefOnly_Mtot]
  norm_num [placableReliefOnly]

/-- The member's stage relief margin in the chord form, from (RL)
(`stageRelief_of_reliefSharp`, BG3.2; renovation item BJ2.3: no longer a field).
Affine-restricted. -/
theorem placableReliefOnly_chordStageRelief :
    placableReliefOnly.toPlacableEconomyF.toChord.StageRelief :=
  placableReliefOnly.toChordCs.stageRelief_of_reliefSharp placableReliefOnly_relief

/-- The rally margin at the member (flat transition: `0 ≤ r`). -/
theorem placableReliefOnly_margin :
    placableReliefOnly.βS * (placableReliefOnly.SigC * placableReliefOnly.ghi
        * placableReliefOnly.dhi
      + (placableReliefOnly.KS + 2 * placableReliefOnly.SigC) * placableReliefOnly.Mmix)
      ≤ placableReliefOnly.r :=
  placableReliefOnly.toPlacableEconomyF.familyMargin_of_flat rfl rfl

/-- **Both channels active at the member, with no stage flip** (the instance of
row 41 at an economy where the flip fails). -/
theorem placableReliefOnly_both_channels :
    ∀ x ∈ Sanctions.I,
      placableReliefOnly.toChordCs.toParams.ContinuationChangesSenderChoiceAt
        ((placableReliefOnly.toChordCs.equilibriumTop_of_margin
          placableReliefOnly_chordLossOffset)
          (placableReliefOnly.toPlacableEconomyF.toChord_margin placableReliefOnly_margin)).V_S x
        (((placableReliefOnly.toChordCs.equilibriumTop_of_margin
          placableReliefOnly_chordLossOffset)
          (placableReliefOnly.toPlacableEconomyF.toChord_margin placableReliefOnly_margin)).α x)
      ∧ placableReliefOnly.toChordCs.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => placableReliefOnly.toChordCs.response
            ((placableReliefOnly.toChordCs.equilibriumTop_of_margin
              placableReliefOnly_chordLossOffset)
              (placableReliefOnly.toPlacableEconomyF.toChord_margin
                placableReliefOnly_margin)).V_S y b)
          ((placableReliefOnly.toChordCs.equilibriumTop_of_margin
            placableReliefOnly_chordLossOffset)
            (placableReliefOnly.toPlacableEconomyF.toChord_margin placableReliefOnly_margin)).V_T x
                :=
  placableReliefOnly.toChordCs.both_channels_active_of_relief placableReliefOnly_chordInterior
    placableReliefOnly_chordLossOffset
    (placableReliefOnly.toPlacableEconomyF.toChord_margin placableReliefOnly_margin)
    placableReliefOnly_relief

/-- **The four cells at the member**, with no stage flip, in closed form:
wash-out under `00` and `01`, `u₀/(q − r) = 1/3` under `10`, a strictly higher
steady state under `11`. -/
theorem placableReliefOnly_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableReliefOnly.toPlacableEconomyF.toChord.myopicPath
        placableReliefOnly_chordInterior placableReliefOnly_chordStageRelief
      (placableReliefOnly.toPlacableEconomyF.toChord_placable placableReliefOnly_placable)) x₀)
      atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableReliefOnly.toChordCs.senderOnlyPath'
        placableReliefOnly_chordInterior
      (placableReliefOnly.toPlacableEconomyF.toChord_placable placableReliefOnly_placable))
      placableReliefOnly_relief placableReliefOnly.toPlacableEconomyF.toChord_zeroSanctionNeutral
      x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (placableReliefOnly.toPlacableEconomyF.toChord.targetOnlyPath
      placableReliefOnly_chordLossOffset x₀)
      atTop (𝓝 placableReliefOnly.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableReliefOnly.toPlacableEconomyF.toChord.responsePath
        placableReliefOnly.toPlacableEconomyF.toChord.VSstar z = z ∧
      placableReliefOnly.steady10 < z ∧
      Tendsto (placableReliefOnly.toPlacableEconomyF.toChord.dynamicPath
        placableReliefOnly_chordLossOffset
        (placableReliefOnly.toPlacableEconomyF.toChord_margin placableReliefOnly_margin) x₀)
        atTop (𝓝 z)) ∧
    0 < placableReliefOnly.steady10 :=
  placableReliefOnly.four_cell_closedForm placableReliefOnly_interior placableReliefOnly_lossOffset
    placableReliefOnly_placable placableReliefOnly_margin placableReliefOnly_relief

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief
#print axioms Sanctions.Examples.placableReliefOnly_not_flip
#print axioms Sanctions.Examples.placableReliefOnly_both_channels
#print axioms Sanctions.Examples.placableReliefOnly_four_cells

end Examples
end Sanctions
