/-
Sanctions/Examples/CoupledRoute/CoupledFrontierCounterexamples.lean

Disprove-first artifacts for the current coupled-equilibrium frontier.

The Target carrier in `CoupledSchurWitness` imposes only a sup-norm bound and
monotonicity.  A narrow monotone ramp can therefore cancel the primitive
quadratic loss over a nondegenerate action interval after box smoothing.  The
resulting Target objective has multiple global maximizers, which refutes every
carrier-uniform quadratic-growth package with the capstone coefficient `1/2`.

No new primitive or analytic assumption is introduced here.
-/

import Sanctions.Examples.CoupledRoute.CoupledSchurWitness

open MeasureTheory intervalIntegral BoundedContinuousFunction

namespace Sanctions

noncomputable section

namespace Examples

open Set AbstractGame Sanctions.AbstractGame.Params

/-! ## The monotone-ramp carrier witness -/

/-- A narrow monotone ramp whose box average offsets the Target's primitive
quadratic loss immediately to the left of `35/1392`. -/
noncomputable def coupledGrowthRamp : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (92800 / 3 : ℝ) *
        max 0 (min (7 / 66816 : ℝ) (z.val - 862343 / 1670400)), by fun_prop⟩

@[simp] theorem coupledGrowthRamp_apply (z : ↥(Sanctions.S : Set ℝ)) :
    coupledGrowthRamp z = (92800 / 3 : ℝ) *
      max 0 (min (7 / 66816 : ℝ) (z.val - 862343 / 1670400)) := rfl

theorem coupledGrowthRamp_mono {x y : ↥(Sanctions.S : Set ℝ)} (hxy : x ≤ y) :
    coupledGrowthRamp x ≤ coupledGrowthRamp y := by
  rw [coupledGrowthRamp_apply, coupledGrowthRamp_apply]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact max_le_max le_rfl
    (min_le_min le_rfl (sub_le_sub_right (show x.val ≤ y.val from hxy) _))

/-- The ramp is in the current Target carrier: it is nondecreasing and its
sup-norm is at most `175/54`, hence strictly below the carrier radius `20`. -/
theorem coupledGrowthRamp_mem : coupledGrowthRamp ∈ coupledCarrierT := by
  constructor
  · change ‖coupledGrowthRamp‖ ≤ lowDeltaTargetCarrierNorm
    rw [lowDeltaTargetCarrierNorm_eq]
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 20)]
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · calc
        coupledGrowthRamp z ≤ (92800 / 3 : ℝ) * (7 / 66816) := by
          rw [coupledGrowthRamp_apply]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact max_le (by norm_num) (min_le_left _ _)
        _ ≤ 20 := by norm_num
    · rw [coupledGrowthRamp_apply]
      positivity
  · intro y₁ y₂ _ _ hy
    change (0 : ℝ) * dist y₁ y₂ ≤ coupledGrowthRamp y₂ - coupledGrowthRamp y₁
    simp only [zero_mul]
    exact sub_nonneg.mpr (coupledGrowthRamp_mono hy)

/-! ## Exact box-average calculations -/

/-- On the low-action interval, the moving window cuts through the linear part
of the ramp.  Its triangular area is exactly quadratic in the distance from
`35/1392`. -/
theorem coupledGrowthRamp_movAvg_low {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 35 / 1392) :
    movAvgReal (1 / 10) coupledGrowthRamp (3997 / 9600 - a / 240) =
      (145 / 108) * (35 / 1392 - a) ^ 2 := by
  let lo : ℝ := 3997 / 9600 - a / 240 - 1 / 10
  let hi : ℝ := 3997 / 9600 - a / 240 + 1 / 10
  let z0 : ℝ := 862343 / 1670400
  have hlo : lo ≤ z0 := by
    norm_num [lo, z0] at ha0 ha1 ⊢
    linarith
  have hhi : z0 ≤ hi := by
    norm_num [hi, z0] at ha0 ha1 ⊢
    linarith
  have hInt : ∀ u v : ℝ,
      IntervalIntegrable (fun z => coupledGrowthRamp (Sanctions.clipS' z)) volume u v :=
    fun u v => (Sanctions.clipComp_cont coupledGrowthRamp).intervalIntegrable u v
  have hleft :
      (∫ z in lo..z0, coupledGrowthRamp (Sanctions.clipS' z)) = 0 := by
    calc
      (∫ z in lo..z0, coupledGrowthRamp (Sanctions.clipS' z)) =
          ∫ _z in lo..z0, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le hlo] at hz
        have hz_nonneg : 0 ≤ z := by
          norm_num [lo] at ha1 hz ⊢
          linarith
        have hz_one : z ≤ 1 := by
          norm_num [z0] at hz ⊢
          linarith
        have hclip : (Sanctions.clipS' z).val = z := by
          simp only [Sanctions.clipS', Sanctions.clipS]
          rw [min_eq_right hz_one, max_eq_right hz_nonneg]
        change coupledGrowthRamp (Sanctions.clipS' z) = 0
        rw [coupledGrowthRamp_apply, hclip]
        have hnonpos :
            min (7 / 66816 : ℝ) (z - 862343 / 1670400) ≤ 0 :=
          le_trans (min_le_right _ _)
            (sub_nonpos.mpr (by simpa [z0] using hz.2))
        rw [max_eq_left hnonpos]
        norm_num
      _ = 0 := by simp
  have hright :
      (∫ z in z0..hi, coupledGrowthRamp (Sanctions.clipS' z)) =
        (92800 / 3 : ℝ) / 2 * (hi - z0) ^ 2 := by
    calc
      (∫ z in z0..hi, coupledGrowthRamp (Sanctions.clipS' z)) =
          ∫ z in z0..hi, (92800 / 3 : ℝ) * (z - z0) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le hhi] at hz
        have hz_nonneg : 0 ≤ z := by
          norm_num [z0] at hz ⊢
          linarith
        have hz_one : z ≤ 1 := by
          norm_num [hi] at ha0 hz ⊢
          linarith
        have hclip : (Sanctions.clipS' z).val = z := by
          simp only [Sanctions.clipS', Sanctions.clipS]
          rw [min_eq_right hz_one, max_eq_right hz_nonneg]
        have hdiff_nonneg : 0 ≤ z - 862343 / 1670400 := by
          norm_num [z0] at hz ⊢
          linarith
        have hdiff_le : z - 862343 / 1670400 ≤ 7 / 66816 := by
          norm_num [hi] at ha0 hz ⊢
          linarith
        change coupledGrowthRamp (Sanctions.clipS' z) =
          (92800 / 3 : ℝ) * (z - z0)
        rw [coupledGrowthRamp_apply, hclip, min_eq_right hdiff_le,
          max_eq_right hdiff_nonneg]
      _ = (92800 / 3 : ℝ) / 2 * (hi - z0) ^ 2 := by
        have hderiv : ∀ z ∈ Set.uIcc z0 hi,
            HasDerivAt (fun t : ℝ => (92800 / 3 : ℝ) / 2 * (t - z0) ^ 2)
              ((92800 / 3 : ℝ) * (z - z0)) z := by
          intro z _
          convert (((hasDerivAt_id z).sub_const z0).pow 2).const_mul
            ((92800 / 3 : ℝ) / 2) using 1
          simp only [id_eq]
          ring
        have hint :
            IntervalIntegrable (fun z : ℝ => (92800 / 3 : ℝ) * (z - z0))
              volume z0 hi :=
          (by fun_prop : Continuous
            (fun z : ℝ => (92800 / 3 : ℝ) * (z - z0))).intervalIntegrable _ _
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
        calc
          (∫ z in z0..hi, (92800 / 3 : ℝ) * (z - z0)) =
              (92800 / 3 : ℝ) / 2 * (hi - z0) ^ 2 -
                (92800 / 3 : ℝ) / 2 * (z0 - z0) ^ 2 := hFTC
          _ = (92800 / 3 : ℝ) / 2 * (hi - z0) ^ 2 := by ring
  unfold movAvgReal
  change (1 / (2 * (1 / 10))) *
      (∫ z in lo..hi, coupledGrowthRamp (Sanctions.clipS' z)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hInt lo z0) (hInt z0 hi), hleft, hright]
  norm_num [hi, z0]
  ring

/-- If the upper edge of the moving window lies weakly below the ramp start,
the ramp's moving average is zero. -/
theorem coupledGrowthRamp_movAvg_zero_of_window_le {y : ℝ}
    (hy : y + 1 / 10 ≤ 862343 / 1670400) :
    movAvgReal (1 / 10) coupledGrowthRamp y = 0 := by
  unfold movAvgReal
  have horder : y - 1 / 10 ≤ y + 1 / 10 := by linarith
  have hint :
      (∫ z in (y - 1 / 10)..(y + 1 / 10),
        coupledGrowthRamp (Sanctions.clipS' z)) = 0 := by
    calc
      (∫ z in (y - 1 / 10)..(y + 1 / 10),
          coupledGrowthRamp (Sanctions.clipS' z)) =
          ∫ _z in (y - 1 / 10)..(y + 1 / 10), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le horder] at hz
        have hz_le : z ≤ 862343 / 1670400 := le_trans hz.2 hy
        have hclip_le :
            (Sanctions.clipS' z).val ≤ 862343 / 1670400 := by
          change max 0 (min 1 z) ≤ 862343 / 1670400
          exact max_le (by norm_num) (le_trans (min_le_right _ _) hz_le)
        change coupledGrowthRamp (Sanctions.clipS' z) = 0
        rw [coupledGrowthRamp_apply]
        have hnonpos :
            min (7 / 66816 : ℝ)
              ((Sanctions.clipS' z).val - 862343 / 1670400) ≤ 0 :=
          le_trans (min_le_right _ _) (sub_nonpos.mpr hclip_le)
        rw [max_eq_left hnonpos]
        norm_num
      _ = 0 := by simp
  rw [hint]
  ring

/-! ## The induced objective plateau -/

theorem coupledGrowthRamp_landing_low {a : ℝ} (haI : a ∈ Sanctions.I) :
    (Sanctions.clipS' ((1 - 1 / 100) * (5 / 12) +
      1 / 100 * (37 / 96 - (5 / 12) * a))).val =
        3997 / 9600 - a / 240 := by
  rcases haI with ⟨ha0, ha1⟩
  have hraw0 : 0 ≤ (1 - 1 / 100 : ℝ) * (5 / 12) +
      1 / 100 * (37 / 96 - (5 / 12) * a) := by
    nlinarith
  have hraw1 : (1 - 1 / 100 : ℝ) * (5 / 12) +
      1 / 100 * (37 / 96 - (5 / 12) * a) ≤ 1 := by
    nlinarith
  simp only [Sanctions.clipS', Sanctions.clipS]
  rw [min_eq_right hraw1, max_eq_right hraw0]
  ring

/-- Exact objective formula on the compensated low-action interval. -/
theorem coupledGrowthRamp_obj_low_formula {a : ℝ}
    (haI : a ∈ Sanctions.I) (ha : a ≤ 35 / 1392) :
    coupledLeaderObj coupledGrowthRamp 0 (5 / 12) a =
      -37 / 1152 + (35 / 576) * a - (29 / 24) * a ^ 2 +
        (29 / 24) * (35 / 1392 - a) ^ 2 := by
  have hkink : a ≤ 37 / 40 := by
    norm_num at ha ⊢
    linarith
  have hstage := coupledLeaderObj_zero_zero_low haI hkink
  rw [coupledLeaderObj_zero_zero,
    coupled_mwσ_five_twelfths_of_le haI hkink] at hstage
  unfold coupledLeaderObj
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [lowDelta_sigmaDynTop_smear_zero,
    coupled_mwσ_five_twelfths_of_le haI hkink]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_β_T, lowDeltaParams_F,
    lowDeltaParams_U_T, AbstractGame.affineF]
  rw [hstage, lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    coupledGrowthRamp_landing_low haI,
    coupledGrowthRamp_movAvg_low haI.1 ha]
  ring

/-- Weakly to the right of `35/1392`, the ramp contributes zero continuation
value, so the coupled objective equals the zero-continuation objective. -/
theorem coupledGrowthRamp_obj_eq_zero_of_a0_le {a : ℝ}
    (haI : a ∈ Sanctions.I) (ha : 35 / 1392 ≤ a) :
    coupledLeaderObj coupledGrowthRamp 0 (5 / 12) a =
      coupledLeaderObj 0 0 (5 / 12) a := by
  by_cases hkink : a ≤ 37 / 40
  · have hwindow :
        3997 / 9600 - a / 240 + 1 / 10 ≤ 862343 / 1670400 := by
      norm_num at ha ⊢
      linarith
    unfold coupledLeaderObj
    simp only [AbstractGame.Params.joint_T_top_integrand]
    rw [lowDelta_sigmaDynTop_smear_zero,
      coupled_mwσ_five_twelfths_of_le haI hkink]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_β_T, lowDeltaParams_F,
      lowDeltaParams_U_T, AbstractGame.affineF]
    rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
      coupledGrowthRamp_landing_low haI,
      coupledGrowthRamp_movAvg_zero_of_window_le hwindow]
    simp [movAvgReal]
  · have hkink' : 37 / 40 ≤ a := by linarith
    have hwindow :
        (1 - 1 / 100 : ℝ) * (5 / 12) + 1 / 100 * 0 + 1 / 10 ≤
          862343 / 1670400 := by
      norm_num
    unfold coupledLeaderObj
    simp only [AbstractGame.Params.joint_T_top_integrand]
    rw [lowDelta_sigmaDynTop_smear_zero,
      coupled_mwσ_five_twelfths_of_ge hkink']
    simp only [lowDeltaShocked_toParams, lowDeltaParams_β_T, lowDeltaParams_F,
      lowDeltaParams_U_T, AbstractGame.affineF]
    rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply]
    have hclip :
        (Sanctions.clipS' ((1 - 1 / 100 : ℝ) * (5 / 12) +
          1 / 100 * 0)).val =
            (1 - 1 / 100 : ℝ) * (5 / 12) + 1 / 100 * 0 := by
      norm_num [Sanctions.clipS', Sanctions.clipS]
    rw [hclip, coupledGrowthRamp_movAvg_zero_of_window_le hwindow]
    simp [movAvgReal]

/-- Every feasible action between zero and `35/1392` gives exactly the same
Target objective under the ramp continuation value. -/
theorem coupledGrowthRamp_obj_plateau {a : ℝ}
    (haI : a ∈ Sanctions.I) (ha : a ≤ 35 / 1392) :
    coupledLeaderObj coupledGrowthRamp 0 (5 / 12) a =
      coupledLeaderObj coupledGrowthRamp 0 (5 / 12) (35 / 1392) := by
  have ha0I : (35 / 1392 : ℝ) ∈ Sanctions.I := by
    constructor <;> norm_num
  rw [coupledGrowthRamp_obj_low_formula haI ha,
    coupledGrowthRamp_obj_low_formula ha0I le_rfl]
  ring

/-- The entire plateau is globally optimal.  To its right, the continuation
term vanishes and the already-proved zero-pair growth estimate supplies the
global upper bound. -/
theorem coupledGrowthRamp_isMaxOn :
    IsMaxOn (fun a => coupledLeaderObj coupledGrowthRamp 0 (5 / 12) a)
      Sanctions.I (35 / 1392) := by
  rw [isMaxOn_iff]
  intro a haI
  by_cases ha : a ≤ 35 / 1392
  · exact (coupledGrowthRamp_obj_plateau haI ha).le
  · have ha' : 35 / 1392 ≤ a := by linarith
    rw [coupledGrowthRamp_obj_eq_zero_of_a0_le haI ha',
      coupledGrowthRamp_obj_eq_zero_of_a0_le
        (show (35 / 1392 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
        le_rfl]
    have h := coupledLeaderObj_zero_zero_quadratic_growth haI
    nlinarith [sq_nonneg (a - 35 / 1392)]

/-! ## Refutation and valid local salvage -/

/-- The carrier-uniform Target quadratic-growth package at an arbitrary
positive modulus `q`, retaining only the selector-feasibility premise needed
by the counterexample.  This is a diagnostic proposition, not an assumption. -/
abbrev CoupledTargetQuadraticGrowthAt (q : ℝ) : Prop :=
  ∃ lead : SBCF → SBCF → ℝ → ℝ,
    (∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S,
      lead V_T V_S x ∈ Sanctions.I) ∧
    ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        q * (a - lead V_T V_S x.val) ^ 2 ≤
          coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val) -
            coupledLeaderObj V_T V_S x.val a

/-- No positive quadratic-growth modulus works uniformly on the current
Target carrier.  The growth inequality forces the proposed action to be
`35/1392`, while the distinct global maximizer `0` makes the strictly positive
quadratic loss bounded by zero. -/
theorem not_coupledTargetQuadraticGrowthAt
    (q : ℝ) (hq : 0 < q) :
    ¬ CoupledTargetQuadraticGrowthAt q := by
  rintro ⟨lead, hmem, hgrowth⟩
  let x : ↥(Sanctions.S : Set ℝ) :=
    ⟨5 / 12, by constructor <;> norm_num⟩
  have hleadI :
      lead coupledGrowthRamp 0 x.val ∈ Sanctions.I :=
    hmem coupledGrowthRamp 0 x.val x.property
  have hlead_le := coupledGrowthRamp_isMaxOn hleadI
  have ha0I : (35 / 1392 : ℝ) ∈ Sanctions.I := by
    constructor <;> norm_num
  have hg0 :=
    hgrowth coupledGrowthRamp coupledGrowthRamp_mem
      0 zero_mem_coupledCarrierS x 0
        (by constructor <;> norm_num)
  have hga0 :=
    hgrowth coupledGrowthRamp coupledGrowthRamp_mem
      0 zero_mem_coupledCarrierS x (35 / 1392) ha0I
  have hlead_eq :
      lead coupledGrowthRamp 0 x.val = 35 / 1392 := by
    dsimp [x] at hlead_le hga0 ⊢
    have hprod_le :
        q * ((35 / 1392 : ℝ) -
          lead coupledGrowthRamp 0 (5 / 12)) ^ 2 ≤ 0 := by
      linarith
    have hprod_eq :
        q * ((35 / 1392 : ℝ) -
          lead coupledGrowthRamp 0 (5 / 12)) ^ 2 = 0 :=
      le_antisymm hprod_le
        (mul_nonneg (le_of_lt hq)
          (sq_nonneg ((35 / 1392 : ℝ) -
            lead coupledGrowthRamp 0 (5 / 12))))
    rcases mul_eq_zero.mp hprod_eq with hq0 | hsq0
    · exact (ne_of_gt hq hq0).elim
    · nlinarith
  dsimp [x] at hg0
  rw [hlead_eq,
    coupledGrowthRamp_obj_plateau
      (show (0 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
      (by norm_num)] at hg0
  have hsq :
      0 < ((0 : ℝ) - 35 / 1392) ^ 2 := by
    norm_num
  nlinarith [mul_pos hq hsq]

/-- Historical modulus-`1/2` formulation, retained only as a one-line
specialization of the positive-modulus obstruction. -/
abbrev CoupledTargetQuadraticGrowth : Prop :=
  CoupledTargetQuadraticGrowthAt (1 / 2)

theorem not_coupledTargetQuadraticGrowth :
    ¬ CoupledTargetQuadraticGrowth :=
  not_coupledTargetQuadraticGrowthAt (1 / 2) (by norm_num)

/-- Valid local salvage: at the zero continuation pair, the original
modulus-one quadratic-growth theorem remains available exactly as proved in
`CoupledSchurWitness`. -/
theorem coupledTargetQuadraticGrowth_zero_pair_salvage {a : ℝ}
    (haI : a ∈ Sanctions.I) :
    (a - 35 / 1392) ^ 2 ≤
      coupledLeaderObj 0 0 (5 / 12) (35 / 1392) -
        coupledLeaderObj 0 0 (5 / 12) a :=
  coupledLeaderObj_zero_zero_quadratic_growth haI

end Examples

end

end Sanctions
