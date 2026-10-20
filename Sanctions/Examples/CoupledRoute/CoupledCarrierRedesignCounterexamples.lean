/-
Sanctions/Examples/CoupledRoute/CoupledCarrierRedesignCounterexamples.lean

Disprove-first artifacts for the norm--Lipschitz coupled-carrier redesign.

The replacement Target carrier is invariant, but its regularity alone does
not restore carrier-uniform Target quadratic growth or a Lipschitz endogenous
Target policy.  An admissible ramp-shaped Sender continuation makes the
endogenous Sender response change affine branch near `a = 1/100`.  An
admissible linear Target continuation then makes the two branch vertices
exactly tied at `x = 5/12`.  The exact pair of states separated by
`2 / 100000000` breaks the tie into two unique global maxima, so every optimal
Target selector moves faster than the Sender-invariance policy budget.

No new model primitive, hypothesis, or carrier condition is introduced.
-/

import Sanctions.Examples.CoupledRoute.CoupledCarrierRedesign

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction
open MeasureTheory intervalIntegral
open AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-! ## Exact counterexample constants -/

private def redesignX0 : ℝ := 5 / 12

private def redesignXMinus : ℝ := 5 / 12 - 1 / 100000000

private def redesignXPlus : ℝ := 5 / 12 + 1 / 100000000

private def redesignA0 : ℝ := 1 / 100

private def redesignResponseK0 : ℝ := 5 / 12

private def redesignCurvatureRatio : ℝ := 10001 / 10000

private def redesignResponseK1 : ℝ :=
  (2 + redesignResponseK0) * redesignCurvatureRatio ^ 2 - 2

private def redesignRampSlope : ℝ :=
  4000 * (6 / 5 - 1 / (2 * redesignResponseK1))

private def redesignSenderThreshold0 : ℝ := 61 / 160

private def redesignLandingThreshold : ℝ :=
  (99 / 100) * redesignX0 + (1 / 100) * redesignSenderThreshold0

private def redesignRampStart : ℝ :=
  redesignLandingThreshold + 1 / 10

private def redesignTargetLandingSlope : ℝ :=
  2636363 / 30017400

private def redesignTargetLinearSlope : ℝ :=
  redesignTargetLandingSlope / (9 / 1000)

private def redesignResponseU0 : ℝ := 9 / 8

private def redesignResponseV0 : ℝ := -(1 / 12)

private def redesignResponseD : ℝ :=
  6 / 5 - redesignRampSlope / 4000

private def redesignResponseU1 : ℝ :=
  (27 / 20 + (99 / 4000) * redesignRampSlope) / redesignResponseD

private def redesignResponseV1 : ℝ :=
  (-(1 / 10) - (redesignRampSlope / 40) * redesignLandingThreshold) /
    redesignResponseD

private def redesignSenderThreshold (x : ℝ) : ℝ :=
  100 * (redesignLandingThreshold - (99 / 100) * x)

private def redesignActionThreshold (x : ℝ) : ℝ :=
  (redesignResponseU0 * x + redesignResponseV0 -
      redesignSenderThreshold x) /
    redesignResponseK0

private def redesignZeroActionThreshold (x : ℝ) : ℝ :=
  (redesignResponseU0 * x + redesignResponseV0) /
    redesignResponseK0

private def redesignResponseActive (x a : ℝ) : ℝ :=
  redesignResponseU1 * x + redesignResponseV1 -
    redesignResponseK1 * a

private def redesignResponseInactive (x a : ℝ) : ℝ :=
  redesignResponseU0 * x + redesignResponseV0 -
    redesignResponseK0 * a

private def redesignBranchVertex (x k u v : ℝ) : ℝ :=
  (2 * x - 1 + (u * x + v) / 2 -
      k * (x - 1 / 2 + redesignTargetLandingSlope)) /
    (2 + k)

private def redesignLeftVertex (x : ℝ) : ℝ :=
  redesignBranchVertex x redesignResponseK1
    redesignResponseU1 redesignResponseV1

private def redesignRightVertex (x : ℝ) : ℝ :=
  redesignBranchVertex x redesignResponseK0
    redesignResponseU0 redesignResponseV0

private def redesignReducedTargetObj (x k u v a : ℝ) : ℝ :=
  -a ^ 2 + (2 * x - 1) * a +
    (x - 1 / 2 + redesignTargetLandingSlope + a / 2) *
      (u * x + v - k * a)

private def redesignTargetConstant (x : ℝ) : ℝ :=
  (9 / 10) * redesignTargetLinearSlope * (99 / 100) * x

theorem redesignResponseK1_eq :
    redesignResponseK1 = 500580029 / 1200000000 := by
  norm_num [redesignResponseK1, redesignResponseK0,
    redesignCurvatureRatio]

theorem redesignRampSlope_eq :
    redesignRampSlope = 2784139200 / 500580029 := by
  norm_num [redesignRampSlope, redesignResponseK1,
    redesignResponseK0, redesignCurvatureRatio]

theorem redesignTargetLinearSlope_eq :
    redesignTargetLinearSlope = 13181815 / 1350783 := by
  norm_num [redesignTargetLinearSlope, redesignTargetLandingSlope]

theorem redesignResponseU1_eq :
    redesignResponseU1 = 4964603229 / 4000000000 := by
  norm_num [redesignResponseU1, redesignResponseD,
    redesignRampSlope_eq]

theorem redesignResponseV1_eq :
    redesignResponseV1 =
      -(31613920667 / 240000000000) := by
  norm_num [redesignResponseV1, redesignResponseD,
    redesignRampSlope_eq, redesignLandingThreshold,
    redesignX0, redesignSenderThreshold0]

/-- The state at which the two Target branch maxima tie. -/
def coupledRedesignTieState : ℝ := 5 / 12

/-- The lower state used to test every optimal Target selector. -/
def coupledRedesignLowerState : ℝ := 5 / 12 - 1 / 100000000

/-- The upper state used to test every optimal Target selector. -/
def coupledRedesignUpperState : ℝ := 5 / 12 + 1 / 100000000

/-- The left-branch Target maximizer at the tie state. -/
def coupledRedesignTieLeftAction : ℝ :=
  500292529 / 50034002900

/-- The right-branch Target maximizer at the tie state. -/
def coupledRedesignTieRightAction : ℝ :=
  40027 / 4002320

/-- The unique Target maximizer at the lower test state. -/
def coupledRedesignLowerOptimalAction : ℝ :=
  5803909847013 / 580336400000000

/-- The unique Target maximizer at the upper test state. -/
def coupledRedesignUpperOptimalAction : ℝ :=
  2901989483510859414103 / 290226236541682000000000

/-! ## Exact reduced branch envelopes -/

/-- The maximum value of the reduced Target objective on the active
Sender-response branch. -/
noncomputable def coupledRedesignActiveBranchEnvelope (x : ℝ) : ℝ :=
  redesignReducedTargetObj x redesignResponseK1
    redesignResponseU1 redesignResponseV1 (redesignLeftVertex x)

/-- The maximum value of the reduced Target objective on the inactive
Sender-response branch. -/
noncomputable def coupledRedesignInactiveBranchEnvelope (x : ℝ) : ℝ :=
  redesignReducedTargetObj x redesignResponseK0
    redesignResponseU0 redesignResponseV0 (redesignRightVertex x)

/-- Exact factorization of the difference between the two smooth reduced
Target branch envelopes.  The factor at `x = 5/12` is the branch tie used
below; the second factor stays positive on the audited local state window. -/
theorem coupledRedesign_reduced_branch_envelope_sub (x : ℝ) :
    coupledRedesignActiveBranchEnvelope x -
        coupledRedesignInactiveBranchEnvelope x =
      (155725362300363003763 / 928185609280000000000 : ℝ) *
        (x - coupledRedesignTieState) *
          (x - 4141379076715 / 10098013652916) := by
  simp only [coupledRedesignActiveBranchEnvelope,
    coupledRedesignInactiveBranchEnvelope, coupledRedesignTieState,
    redesignLeftVertex, redesignRightVertex, redesignBranchVertex,
    redesignReducedTargetObj, redesignResponseK1_eq,
    redesignResponseU1_eq, redesignResponseV1_eq,
    redesignResponseK0, redesignResponseU0, redesignResponseV0,
    redesignTargetLandingSlope]
  ring

/-- No strictly positive branch-envelope gap can hold uniformly across the
audited state window: the two smooth branch envelopes tie exactly at
`x = 5/12`. -/
theorem not_coupledRedesign_positive_uniform_reduced_branch_gap :
    ¬ ∃ gap : ℝ, 0 < gap ∧
      ∀ x ∈ Set.Icc coupledRedesignLowerState coupledRedesignUpperState,
        gap ≤
          |coupledRedesignActiveBranchEnvelope x -
            coupledRedesignInactiveBranchEnvelope x| := by
  rintro ⟨gap, hgap, huniform⟩
  have hx :
      coupledRedesignTieState ∈
        Set.Icc coupledRedesignLowerState coupledRedesignUpperState := by
    constructor <;>
      norm_num [coupledRedesignTieState, coupledRedesignLowerState,
        coupledRedesignUpperState]
  have h := huniform coupledRedesignTieState hx
  have hzero :
      coupledRedesignActiveBranchEnvelope coupledRedesignTieState -
          coupledRedesignInactiveBranchEnvelope coupledRedesignTieState = 0 := by
    rw [coupledRedesign_reduced_branch_envelope_sub]
    ring
  rw [hzero, abs_zero] at h
  linarith

/-- A state at least `ρ` above the tie has an exact branch-envelope margin
of at least `ρ / 1000` in favor of the active Sender-response branch,
uniformly up to the audited upper state. -/
theorem coupledRedesign_active_branch_gap_above_tie
    {ρ x : ℝ} (hρ : 0 ≤ ρ)
    (hxρ : coupledRedesignTieState + ρ ≤ x)
    (hxUpper : x ≤ coupledRedesignUpperState) :
    coupledRedesignInactiveBranchEnvelope x + ρ / 1000 ≤
      coupledRedesignActiveBranchEnvelope x := by
  have henv :=
    coupledRedesign_reduced_branch_envelope_sub x
  have hfactor :
      (1 / 1000 : ℝ) ≤
        (155725362300363003763 / 928185609280000000000) *
          (x - 4141379076715 / 10098013652916) := by
    have hxWindow :
        x ≤ 5 / 12 + 1 / 100000000 := by
      simpa only [coupledRedesignUpperState] using hxUpper
    norm_num [coupledRedesignTieState] at hxρ
    nlinarith
  have hxTie : ρ ≤ x - coupledRedesignTieState := by
    linarith
  have hfactor0 :
      0 ≤
        (155725362300363003763 / 928185609280000000000 : ℝ) *
          (x - 4141379076715 / 10098013652916) := by
    linarith
  have hprod :
      ρ / 1000 ≤
        (155725362300363003763 / 928185609280000000000 : ℝ) *
          (x - coupledRedesignTieState) *
            (x - 4141379076715 / 10098013652916) := by
    calc
      ρ / 1000 ≤
          ρ * ((155725362300363003763 / 928185609280000000000 : ℝ) *
            (x - 4141379076715 / 10098013652916)) := by
        nlinarith [mul_le_mul_of_nonneg_left hfactor hρ]
      _ ≤ (x - coupledRedesignTieState) *
          ((155725362300363003763 / 928185609280000000000 : ℝ) *
            (x - 4141379076715 / 10098013652916)) :=
        mul_le_mul_of_nonneg_right hxTie hfactor0
      _ = _ := by ring
  nlinarith [henv, hprod]

/-- A state at least `ρ` below the tie has an exact branch-envelope margin
of at least `ρ / 1000` in favor of the inactive Sender-response branch,
uniformly down to the audited lower state. -/
theorem coupledRedesign_inactive_branch_gap_below_tie
    {ρ x : ℝ} (hρ : 0 ≤ ρ)
    (hxLower : coupledRedesignLowerState ≤ x)
    (hxρ : x + ρ ≤ coupledRedesignTieState) :
    coupledRedesignActiveBranchEnvelope x + ρ / 1000 ≤
      coupledRedesignInactiveBranchEnvelope x := by
  have henv :=
    coupledRedesign_reduced_branch_envelope_sub x
  have hfactor :
      (1 / 1000 : ℝ) ≤
        (155725362300363003763 / 928185609280000000000) *
          (x - 4141379076715 / 10098013652916) := by
    have hxWindow :
        5 / 12 - 1 / 100000000 ≤ x := by
      simpa only [coupledRedesignLowerState] using hxLower
    norm_num [coupledRedesignTieState] at hxρ
    nlinarith
  have hxTie : ρ ≤ coupledRedesignTieState - x := by
    linarith
  have hfactor0 :
      0 ≤
        (155725362300363003763 / 928185609280000000000 : ℝ) *
          (x - 4141379076715 / 10098013652916) := by
    linarith
  have hprod :
      ρ / 1000 ≤
        (coupledRedesignTieState - x) *
          ((155725362300363003763 / 928185609280000000000 : ℝ) *
            (x - 4141379076715 / 10098013652916)) := by
    calc
      ρ / 1000 ≤
          ρ * ((155725362300363003763 / 928185609280000000000 : ℝ) *
            (x - 4141379076715 / 10098013652916)) := by
        nlinarith [mul_le_mul_of_nonneg_left hfactor hρ]
      _ ≤ (coupledRedesignTieState - x) *
          ((155725362300363003763 / 928185609280000000000 : ℝ) *
            (x - 4141379076715 / 10098013652916)) :=
        mul_le_mul_of_nonneg_right hxTie hfactor0
  nlinarith [henv, hprod]

/-- The active branch remains strictly preferred after perturbing both branch
envelope values by at most `ε`, provided the state is `ρ` above the tie and
the exact branch margin `ρ / 1000` exceeds `2ε`. -/
theorem coupledRedesign_active_branch_stable_of_envelope_perturbation
    {ρ ε x activeValue inactiveValue : ℝ}
    (hρ : 0 ≤ ρ)
    (hxρ : coupledRedesignTieState + ρ ≤ x)
    (hxUpper : x ≤ coupledRedesignUpperState)
    (hactive :
      |activeValue - coupledRedesignActiveBranchEnvelope x| ≤ ε)
    (hinactive :
      |inactiveValue - coupledRedesignInactiveBranchEnvelope x| ≤ ε)
    (hsmall : 2 * ε < ρ / 1000) :
    inactiveValue < activeValue := by
  have hgap :=
    coupledRedesign_active_branch_gap_above_tie hρ hxρ hxUpper
  have hactive' := abs_le.mp hactive
  have hinactive' := abs_le.mp hinactive
  linarith

/-- The inactive branch remains strictly preferred after perturbing both
branch envelope values by at most `ε`, provided the state is `ρ` below the
tie and the exact branch margin `ρ / 1000` exceeds `2ε`. -/
theorem coupledRedesign_inactive_branch_stable_of_envelope_perturbation
    {ρ ε x activeValue inactiveValue : ℝ}
    (hρ : 0 ≤ ρ)
    (hxLower : coupledRedesignLowerState ≤ x)
    (hxρ : x + ρ ≤ coupledRedesignTieState)
    (hactive :
      |activeValue - coupledRedesignActiveBranchEnvelope x| ≤ ε)
    (hinactive :
      |inactiveValue - coupledRedesignInactiveBranchEnvelope x| ≤ ε)
    (hsmall : 2 * ε < ρ / 1000) :
    activeValue < inactiveValue := by
  have hgap :=
    coupledRedesign_inactive_branch_gap_below_tie hρ hxLower hxρ
  have hactive' := abs_le.mp hactive
  have hinactive' := abs_le.mp hinactive
  linarith

/-! ## The two admissible continuation values -/

/-- A shallow monotone ramp in the Sender continuation value. -/
noncomputable def coupledRedesignSenderRamp : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => redesignRampSlope * max 0 (z.val - redesignRampStart),
      by fun_prop⟩

@[simp] theorem coupledRedesignSenderRamp_apply
    (z : ↥(Sanctions.S : Set ℝ)) :
    coupledRedesignSenderRamp z =
      redesignRampSlope * max 0 (z.val - redesignRampStart) := rfl

/-- A positive linear Target continuation value. -/
noncomputable def coupledRedesignTargetLinear : SBCF :=
  redesignTargetLinearSlope • coupledSenderIdentity

@[simp] theorem coupledRedesignTargetLinear_apply
    (z : ↥(Sanctions.S : Set ℝ)) :
    coupledRedesignTargetLinear z = redesignTargetLinearSlope * z.val := by
  simp [coupledRedesignTargetLinear, coupledSenderIdentity_apply]

theorem coupledRedesignSenderRamp_mem :
    coupledRedesignSenderRamp ∈ coupledCarrierS := by
  rw [coupledCarrierS, mem_valLipBall_iff]
  constructor
  · rw [lowDeltaSenderCarrierNorm_eq,
      BoundedContinuousFunction.norm_le
      (by norm_num : (0 : ℝ) ≤ 523 / 160)]
    intro z
    rw [Real.norm_eq_abs, coupledRedesignSenderRamp_apply,
      abs_of_nonneg]
    · calc
        redesignRampSlope * max 0 (z.val - redesignRampStart)
            ≤ redesignRampSlope * (1 - redesignRampStart) := by
              apply mul_le_mul_of_nonneg_left _
                (by norm_num [redesignRampSlope_eq])
              exact max_le
                (by norm_num [redesignRampStart, redesignLandingThreshold,
                  redesignX0, redesignSenderThreshold0])
                (sub_le_sub_right z.property.2 redesignRampStart)
        _ ≤ 523 / 160 := by
          norm_num [redesignRampSlope_eq, redesignRampStart,
            redesignLandingThreshold, redesignX0,
            redesignSenderThreshold0]
    · exact mul_nonneg
        (by norm_num [redesignRampSlope_eq])
        (le_max_left _ _)
  · intro y₁ y₂
    rw [coupledRedesignSenderRamp_apply,
      coupledRedesignSenderRamp_apply]
    have hmax :
        |max 0 (y₂.val - redesignRampStart) -
            max 0 (y₁.val - redesignRampStart)|
          ≤ |y₂.val - y₁.val| := by
      simpa only [max_comm, sub_sub_sub_cancel_right] using
        (abs_max_sub_max_le_abs
          (y₂.val - redesignRampStart)
          (y₁.val - redesignRampStart) (0 : ℝ))
    rw [← mul_sub, abs_mul,
      abs_of_nonneg
        (by norm_num [redesignRampSlope_eq] :
          0 ≤ redesignRampSlope)]
    calc
      redesignRampSlope *
          |max 0 (y₂.val - redesignRampStart) -
            max 0 (y₁.val - redesignRampStart)|
        ≤ redesignRampSlope * |y₂.val - y₁.val| :=
          mul_le_mul_of_nonneg_left hmax
            (by norm_num [redesignRampSlope_eq])
      _ ≤ (57377 / 3200) * |y₂.val - y₁.val| := by
        apply mul_le_mul_of_nonneg_right
          (by norm_num [redesignRampSlope_eq]) (abs_nonneg _)
      _ = (57377 / 3200) * dist y₁ y₂ := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      _ = lowDeltaSenderCarrierLip * dist y₁ y₂ := by
        rw [lowDeltaSenderCarrierLip_eq]

theorem coupledRedesignTargetLinear_mem :
    coupledRedesignTargetLinear ∈ coupledCarrierTLip := by
  change coupledRedesignTargetLinear ∈
    Params.valLipBall lowDeltaTargetCarrierNorm coupledTargetLipK
  rw [mem_valLipBall_iff]
  constructor
  · rw [lowDeltaTargetCarrierNorm_eq,
      BoundedContinuousFunction.norm_le
      (by norm_num : (0 : ℝ) ≤ 20)]
    intro z
    rw [Real.norm_eq_abs, coupledRedesignTargetLinear_apply,
      abs_mul,
      abs_of_nonneg
        (by norm_num [redesignTargetLinearSlope_eq] :
          0 ≤ redesignTargetLinearSlope),
      abs_of_nonneg z.property.1]
    calc
      redesignTargetLinearSlope * z.val
        ≤ redesignTargetLinearSlope * 1 :=
          mul_le_mul_of_nonneg_left z.property.2
            (by norm_num [redesignTargetLinearSlope_eq])
      _ ≤ 20 := by norm_num [redesignTargetLinearSlope_eq]
  · intro y₁ y₂
    rw [coupledRedesignTargetLinear_apply,
      coupledRedesignTargetLinear_apply, ← mul_sub, abs_mul,
      abs_of_nonneg
        (by norm_num [redesignTargetLinearSlope_eq] :
          0 ≤ redesignTargetLinearSlope)]
    rw [Subtype.dist_eq, Real.dist_eq]
    rw [abs_sub_comm y₂.val y₁.val]
    exact mul_le_mul_of_nonneg_right
      (by
        norm_num [redesignTargetLinearSlope_eq, coupledTargetLipK_eq])
      (abs_nonneg _)

/-! ## Exact moving-average formulas for the Sender ramp -/

private theorem coupledRedesignSenderRamp_intervalIntegrable
    (u v : ℝ) :
    IntervalIntegrable
      (fun z => coupledRedesignSenderRamp (Sanctions.clipS' z))
      volume u v :=
  (Sanctions.clipComp_cont
    coupledRedesignSenderRamp).intervalIntegrable u v

theorem coupledRedesignSenderRamp_movAvg_zero
    {y : ℝ} (hy0 : 1 / 10 ≤ y)
    (hy : y ≤ redesignLandingThreshold) :
    Sanctions.movAvgReal (1 / 10) coupledRedesignSenderRamp y = 0 := by
  unfold Sanctions.movAvgReal
  have horder : y - 1 / 10 ≤ y + 1 / 10 := by linarith
  have hint :
      (∫ z in (y - 1 / 10)..(y + 1 / 10),
        coupledRedesignSenderRamp (Sanctions.clipS' z)) = 0 := by
    calc
      (∫ z in (y - 1 / 10)..(y + 1 / 10),
          coupledRedesignSenderRamp (Sanctions.clipS' z)) =
          ∫ _z in (y - 1 / 10)..(y + 1 / 10), (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro z hz
            rw [Set.uIcc_of_le horder] at hz
            have hz0 : 0 ≤ z := by
              norm_num at hy0 hz ⊢
              linarith
            have hz1 : z ≤ 1 := by
              norm_num [redesignLandingThreshold, redesignX0,
                redesignSenderThreshold0] at hy hz ⊢
              linarith
            have hclip : (Sanctions.clipS' z).val = z :=
              Sanctions.clipS'_val_eq_of_mem ⟨hz0, hz1⟩
            change coupledRedesignSenderRamp (Sanctions.clipS' z) = 0
            rw [coupledRedesignSenderRamp_apply, hclip]
            have hzStart : z ≤ redesignRampStart := by
              exact le_trans hz.2 (by
                dsimp only [redesignRampStart]
                linarith)
            rw [max_eq_left (sub_nonpos.mpr hzStart)]
            ring
      _ = 0 := by simp
  rw [hint]
  ring

theorem coupledRedesignSenderRamp_movAvg_quadratic
    {y : ℝ} (hy0 : 1 / 10 ≤ y)
    (hy : redesignLandingThreshold ≤ y)
    (hy1 : y ≤ redesignLandingThreshold + 1 / 10) :
    Sanctions.movAvgReal (1 / 10) coupledRedesignSenderRamp y =
      (5 / 2) * redesignRampSlope *
        (y - redesignLandingThreshold) ^ 2 := by
  let lo : ℝ := y - 1 / 10
  let hi : ℝ := y + 1 / 10
  let z0 : ℝ := redesignRampStart
  have hlo : lo ≤ z0 := by
    dsimp only [lo, z0, redesignRampStart]
    linarith
  have hhi : z0 ≤ hi := by
    dsimp only [hi, z0, redesignRampStart]
    linarith
  have hleft :
      (∫ z in lo..z0,
        coupledRedesignSenderRamp (Sanctions.clipS' z)) = 0 := by
    calc
      (∫ z in lo..z0,
          coupledRedesignSenderRamp (Sanctions.clipS' z)) =
          ∫ _z in lo..z0, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro z hz
            rw [Set.uIcc_of_le hlo] at hz
            have hz0 : 0 ≤ z := by
              dsimp only [lo] at hz
              norm_num at hy0 hz ⊢
              linarith
            have hz1 : z ≤ 1 := by
              norm_num [z0, redesignRampStart,
                redesignLandingThreshold, redesignX0,
                redesignSenderThreshold0] at hz ⊢
              linarith
            have hclip : (Sanctions.clipS' z).val = z :=
              Sanctions.clipS'_val_eq_of_mem ⟨hz0, hz1⟩
            change coupledRedesignSenderRamp (Sanctions.clipS' z) = 0
            rw [coupledRedesignSenderRamp_apply, hclip]
            have hzStart : z ≤ redesignRampStart := by
              simpa only [z0] using hz.2
            rw [max_eq_left (sub_nonpos.mpr hzStart)]
            ring
      _ = 0 := by simp
  have hright :
      (∫ z in z0..hi,
        coupledRedesignSenderRamp (Sanctions.clipS' z)) =
        redesignRampSlope / 2 * (hi - z0) ^ 2 := by
    calc
      (∫ z in z0..hi,
          coupledRedesignSenderRamp (Sanctions.clipS' z)) =
          ∫ z in z0..hi,
            redesignRampSlope * (z - z0) := by
              apply intervalIntegral.integral_congr
              intro z hz
              rw [Set.uIcc_of_le hhi] at hz
              have hz0 : 0 ≤ z := by
                norm_num [z0, redesignRampStart,
                  redesignLandingThreshold, redesignX0,
                  redesignSenderThreshold0] at hz ⊢
                linarith
              have hz1 : z ≤ 1 := by
                dsimp only [hi] at hz
                norm_num [redesignLandingThreshold, redesignX0,
                  redesignSenderThreshold0] at hy1 hz ⊢
                linarith
              have hclip : (Sanctions.clipS' z).val = z :=
                Sanctions.clipS'_val_eq_of_mem ⟨hz0, hz1⟩
              change coupledRedesignSenderRamp (Sanctions.clipS' z) =
                redesignRampSlope * (z - z0)
              rw [coupledRedesignSenderRamp_apply, hclip]
              have hzStart : redesignRampStart ≤ z := by
                simpa only [z0] using hz.1
              rw [max_eq_right (sub_nonneg.mpr hzStart)]
      _ = redesignRampSlope / 2 * (hi - z0) ^ 2 := by
        have hderiv :
            ∀ z ∈ Set.uIcc z0 hi,
              HasDerivAt
                (fun t : ℝ =>
                  redesignRampSlope / 2 * (t - z0) ^ 2)
                (redesignRampSlope * (z - z0)) z := by
          intro z _
          convert
            (((hasDerivAt_id z).sub_const z0).pow 2).const_mul
              (redesignRampSlope / 2) using 1
          simp only [id_eq]
          ring
        have hint :
            IntervalIntegrable
              (fun z : ℝ => redesignRampSlope * (z - z0))
              volume z0 hi :=
          (by
            fun_prop : Continuous
              (fun z : ℝ => redesignRampSlope * (z - z0))
          ).intervalIntegrable _ _
        have hFTC :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
        calc
          (∫ z in z0..hi,
              redesignRampSlope * (z - z0)) =
              redesignRampSlope / 2 * (hi - z0) ^ 2 -
                redesignRampSlope / 2 * (z0 - z0) ^ 2 := hFTC
          _ = redesignRampSlope / 2 * (hi - z0) ^ 2 := by ring
  unfold Sanctions.movAvgReal
  change (1 / (2 * (1 / 10 : ℝ))) *
      (∫ z in lo..hi,
        coupledRedesignSenderRamp (Sanctions.clipS' z)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (coupledRedesignSenderRamp_intervalIntegrable lo z0)
      (coupledRedesignSenderRamp_intervalIntegrable z0 hi),
    hleft, hright]
  dsimp only [hi, z0, redesignRampStart]
  ring

/-! ## Endogenous Sender response on the two relevant branches -/

private theorem coupledRedesignSenderRamp_smear_transition_zero
    {x s : ℝ} (hx : x ∈ Sanctions.S) (hs : s ∈ Sanctions.I)
    (hland :
      (99 / 100 : ℝ) * x + (1 / 100) * s ≤
        redesignLandingThreshold)
    (hlow :
      (1 / 10 : ℝ) ≤
        (99 / 100) * x + (1 / 100) * s) :
    lowDeltaShocked.smear coupledRedesignSenderRamp
        (Sanctions.clipS' (lowDeltaShocked.toParams.F x s)) = 0 := by
  have hF : lowDeltaShocked.toParams.F x s ∈ Sanctions.S := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F]
    exact Sanctions.AbstractGame.affineF_mem
      (δ := (1 / 100 : ℝ)) (by constructor <;> norm_num)
      x s hx hs
  rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hF]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
    Sanctions.AbstractGame.affineF]
  norm_num at hlow hland ⊢
  exact coupledRedesignSenderRamp_movAvg_zero hlow hland

private theorem coupledRedesignSenderRamp_smear_transition_quadratic
    {x s : ℝ} (hx : x ∈ Sanctions.S) (hs : s ∈ Sanctions.I)
    (hland :
      redesignLandingThreshold ≤
        (99 / 100 : ℝ) * x + (1 / 100) * s)
    (hlow :
      (1 / 10 : ℝ) ≤
        (99 / 100) * x + (1 / 100) * s)
    (hhigh :
      (99 / 100 : ℝ) * x + (1 / 100) * s ≤
        redesignLandingThreshold + 1 / 10) :
    lowDeltaShocked.smear coupledRedesignSenderRamp
        (Sanctions.clipS' (lowDeltaShocked.toParams.F x s)) =
      (5 / 2) * redesignRampSlope *
        ((99 / 100 : ℝ) * x + (1 / 100) * s -
          redesignLandingThreshold) ^ 2 := by
  have hF : lowDeltaShocked.toParams.F x s ∈ Sanctions.S := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F]
    exact Sanctions.AbstractGame.affineF_mem
      (δ := (1 / 100 : ℝ)) (by constructor <;> norm_num)
      x s hx hs
  rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hF]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
    Sanctions.AbstractGame.affineF]
  norm_num at hlow hland hhigh ⊢
  exact coupledRedesignSenderRamp_movAvg_quadratic
    hlow hland hhigh

private theorem redesign_narrow_state_mem
    {x : ℝ} (hx0 : redesignXMinus ≤ x)
    (hx1 : x ≤ redesignXPlus) :
    x ∈ Sanctions.S := by
  constructor
  · norm_num [redesignXMinus] at hx0 ⊢
    linarith
  · norm_num [redesignXPlus] at hx1 ⊢
    linarith

private theorem redesign_active_response_above_threshold
    {x a : ℝ} (haActive : a ≤ redesignActionThreshold x) :
    redesignSenderThreshold x ≤ redesignResponseActive x a := by
  norm_num [redesignSenderThreshold, redesignActionThreshold,
    redesignResponseActive, redesignResponseU1,
    redesignResponseV1, redesignResponseK1_eq,
    redesignResponseD, redesignRampSlope_eq,
    redesignLandingThreshold, redesignX0,
    redesignSenderThreshold0, redesignResponseU0,
    redesignResponseV0, redesignResponseK0] at haActive ⊢
  linarith

private theorem redesign_active_response_mem
    {x a : ℝ}
    (hx1 : x ≤ redesignXPlus)
    (ha : a ∈ Sanctions.I)
    (haActive : a ≤ redesignActionThreshold x) :
    redesignResponseActive x a ∈ Sanctions.I := by
  rcases ha with ⟨ha0, _ha1⟩
  have hAbove :=
    redesign_active_response_above_threshold haActive
  constructor
  · have hThresholdNonneg :
        0 ≤ redesignSenderThreshold x := by
      norm_num [redesignSenderThreshold, redesignLandingThreshold,
        redesignX0, redesignSenderThreshold0,
        redesignXPlus] at hx1 ⊢
      linarith
    exact le_trans hThresholdNonneg hAbove
  · norm_num [redesignResponseActive, redesignResponseU1,
      redesignResponseV1, redesignResponseK1_eq,
      redesignResponseD, redesignRampSlope_eq,
      redesignLandingThreshold, redesignX0,
      redesignSenderThreshold0, redesignXPlus] at hx1 ha0 ⊢
    linarith

private theorem coupledRedesign_sigmaDynTop_active
    {x a : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (ha : a ∈ Sanctions.I)
    (haActive : a ≤ redesignActionThreshold x) :
    lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a =
      redesignResponseActive x a := by
  let t : ℝ := redesignResponseActive x a
  have hx : x ∈ Sanctions.S :=
    redesign_narrow_state_mem hx0 hx1
  have ht : t ∈ Sanctions.I := by
    simpa only [t] using
      redesign_active_response_mem hx1 ha haActive
  have htAbove :
      redesignSenderThreshold x ≤ t := by
    simpa only [t] using
      redesign_active_response_above_threshold haActive
  have htLand :
      redesignLandingThreshold ≤
        (99 / 100 : ℝ) * x + (1 / 100) * t := by
    norm_num [redesignSenderThreshold] at htAbove ⊢
    linarith
  have htLow :
      (1 / 10 : ℝ) ≤
        (99 / 100) * x + (1 / 100) * t := by
    rcases ht with ⟨ht0, _ht1⟩
    norm_num [redesignXMinus] at hx0 ⊢
    linarith
  have htHigh :
      (99 / 100 : ℝ) * x + (1 / 100) * t ≤
        redesignLandingThreshold + 1 / 10 := by
    rcases ht with ⟨_ht0, ht1⟩
    norm_num [redesignXPlus, redesignLandingThreshold,
      redesignX0, redesignSenderThreshold0] at hx1 ⊢
    linarith
  have hsmear_t :=
    coupledRedesignSenderRamp_smear_transition_quadratic
      hx ht htLand htLow htHigh
  have hmax : IsMaxOn
      (fun s =>
        lowDeltaShocked.toParams.U_S x a s +
          lowDeltaShocked.toParams.β_S *
            lowDeltaShocked.smear coupledRedesignSenderRamp
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F x s)))
      Sanctions.I t := by
    rw [isMaxOn_iff]
    intro s hs
    have hsLow :
        (1 / 10 : ℝ) ≤
          (99 / 100) * x + (1 / 100) * s := by
      rcases hs with ⟨hs0, _hs1⟩
      norm_num [redesignXMinus] at hx0 ⊢
      linarith
    have hsHigh :
        (99 / 100 : ℝ) * x + (1 / 100) * s ≤
          redesignLandingThreshold + 1 / 10 := by
      rcases hs with ⟨_hs0, hs1⟩
      norm_num [redesignXPlus, redesignLandingThreshold,
        redesignX0, redesignSenderThreshold0] at hx1 ⊢
      linarith
    by_cases hsInactive : s ≤ redesignSenderThreshold x
    · have hsLand :
          (99 / 100 : ℝ) * x + (1 / 100) * s ≤
            redesignLandingThreshold := by
        norm_num [redesignSenderThreshold] at hsInactive ⊢
        linarith
      have hsmear_s :=
        coupledRedesignSenderRamp_smear_transition_zero
          hx hs hsLand hsLow
      rw [hsmear_s, hsmear_t]
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
        lowDeltaParams_β_S]
      norm_num [mwU_S, t, redesignResponseActive,
        redesignResponseU1, redesignResponseV1,
        redesignResponseK1_eq, redesignResponseD,
        redesignRampSlope_eq, redesignLandingThreshold,
        redesignX0, redesignSenderThreshold0,
        redesignSenderThreshold, redesignActionThreshold,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0] at hx0 hx1 haActive hsInactive ⊢
      nlinarith [sq_nonneg
        (s - (100 *
          (6661 / 16000 - (99 / 100) * x)))]
    · have hsLand :
          redesignLandingThreshold ≤
            (99 / 100 : ℝ) * x + (1 / 100) * s := by
        have hsAbove : redesignSenderThreshold x ≤ s := by
          linarith
        norm_num [redesignSenderThreshold] at hsAbove ⊢
        linarith
      have hsmear_s :=
        coupledRedesignSenderRamp_smear_transition_quadratic
          hx hs hsLand hsLow hsHigh
      rw [hsmear_s, hsmear_t]
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
        lowDeltaParams_β_S]
      norm_num [mwU_S, t, redesignResponseActive,
        redesignResponseU1, redesignResponseV1,
        redesignResponseK1_eq, redesignResponseD,
        redesignRampSlope_eq, redesignLandingThreshold,
        redesignX0, redesignSenderThreshold0] at ⊢
      nlinarith [sq_nonneg (s -
        (4964603229 / 4000000000 * x -
          31613920667 / 240000000000 -
          500580029 / 1200000000 * a))]
  simpa only [t] using
    (AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
      ((coupled_sender_strongConcave coupledRedesignSenderRamp
        coupledRedesignSenderRamp_mem.2 x hx a).strictConcaveOn
        (by norm_num))
      (lowDeltaShocked.toParams.σ_dyn_top_mem_I
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a)
      ht
      (lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a)
      hmax)

private theorem redesign_inactive_response_below_threshold
    {x a : ℝ} (haInactive : redesignActionThreshold x ≤ a) :
    redesignResponseInactive x a ≤ redesignSenderThreshold x := by
  norm_num [redesignSenderThreshold, redesignActionThreshold,
    redesignResponseInactive, redesignResponseU0,
    redesignResponseV0, redesignResponseK0] at haInactive ⊢
  linarith

private theorem redesign_inactive_response_mem
    {x a : ℝ} (hx1 : x ≤ redesignXPlus)
    (ha : a ∈ Sanctions.I)
    (haZero : a ≤ redesignZeroActionThreshold x) :
    redesignResponseInactive x a ∈ Sanctions.I := by
  rcases ha with ⟨ha0, _ha1⟩
  constructor
  · norm_num [redesignZeroActionThreshold,
      redesignResponseInactive, redesignResponseU0,
      redesignResponseV0, redesignResponseK0] at haZero ⊢
    linarith
  · norm_num [redesignResponseInactive, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignXPlus] at hx1 ha0 ⊢
    linarith

private theorem coupledRedesign_sigmaDynTop_inactive
    {x a : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (ha : a ∈ Sanctions.I)
    (haInactive : redesignActionThreshold x ≤ a)
    (haZero : a ≤ redesignZeroActionThreshold x) :
    lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a =
      redesignResponseInactive x a := by
  let t : ℝ := redesignResponseInactive x a
  have hx : x ∈ Sanctions.S :=
    redesign_narrow_state_mem hx0 hx1
  have ht : t ∈ Sanctions.I := by
    simpa only [t] using
      redesign_inactive_response_mem hx1 ha haZero
  have htBelow :
      t ≤ redesignSenderThreshold x := by
    simpa only [t] using
      redesign_inactive_response_below_threshold haInactive
  have htLand :
      (99 / 100 : ℝ) * x + (1 / 100) * t ≤
        redesignLandingThreshold := by
    norm_num [redesignSenderThreshold] at htBelow ⊢
    linarith
  have htLow :
      (1 / 10 : ℝ) ≤
        (99 / 100) * x + (1 / 100) * t := by
    rcases ht with ⟨ht0, _ht1⟩
    norm_num [redesignXMinus] at hx0 ⊢
    linarith
  have hsmear_t :=
    coupledRedesignSenderRamp_smear_transition_zero
      hx ht htLand htLow
  have hmax : IsMaxOn
      (fun s =>
        lowDeltaShocked.toParams.U_S x a s +
          lowDeltaShocked.toParams.β_S *
            lowDeltaShocked.smear coupledRedesignSenderRamp
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F x s)))
      Sanctions.I t := by
    rw [isMaxOn_iff]
    intro s hs
    have hsLow :
        (1 / 10 : ℝ) ≤
          (99 / 100) * x + (1 / 100) * s := by
      rcases hs with ⟨hs0, _hs1⟩
      norm_num [redesignXMinus] at hx0 ⊢
      linarith
    have hsHigh :
        (99 / 100 : ℝ) * x + (1 / 100) * s ≤
          redesignLandingThreshold + 1 / 10 := by
      rcases hs with ⟨_hs0, hs1⟩
      norm_num [redesignXPlus, redesignLandingThreshold,
        redesignX0, redesignSenderThreshold0] at hx1 ⊢
      linarith
    by_cases hsInactive : s ≤ redesignSenderThreshold x
    · have hsLand :
          (99 / 100 : ℝ) * x + (1 / 100) * s ≤
            redesignLandingThreshold := by
        norm_num [redesignSenderThreshold] at hsInactive ⊢
        linarith
      have hsmear_s :=
        coupledRedesignSenderRamp_smear_transition_zero
          hx hs hsLand hsLow
      rw [hsmear_s, hsmear_t]
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
        lowDeltaParams_β_S]
      norm_num [mwU_S, t, redesignResponseInactive,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0] at ⊢
      nlinarith [sq_nonneg
        (s - (9 / 8 * x - 1 / 12 - 5 / 12 * a))]
    · have hsLand :
          redesignLandingThreshold ≤
            (99 / 100 : ℝ) * x + (1 / 100) * s := by
        have hsAbove : redesignSenderThreshold x ≤ s := by
          linarith
        norm_num [redesignSenderThreshold] at hsAbove ⊢
        linarith
      have hsmear_s :=
        coupledRedesignSenderRamp_smear_transition_quadratic
          hx hs hsLand hsLow hsHigh
      rw [hsmear_s, hsmear_t]
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
        lowDeltaParams_β_S]
      norm_num [mwU_S, t, redesignResponseInactive,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignRampSlope_eq,
        redesignLandingThreshold, redesignX0,
        redesignSenderThreshold0, redesignActionThreshold,
        redesignSenderThreshold] at haInactive hsInactive ⊢
      nlinarith [sq_nonneg
        (s - (100 *
          (6661 / 16000 - 99 / 100 * x)))]
  simpa only [t] using
    (AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
      ((coupled_sender_strongConcave coupledRedesignSenderRamp
        coupledRedesignSenderRamp_mem.2 x hx a).strictConcaveOn
        (by norm_num))
      (lowDeltaShocked.toParams.σ_dyn_top_mem_I
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a)
      ht
      (lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a)
      hmax)

private theorem coupledRedesign_sigmaDynTop_zero
    {x a : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (haZero : redesignZeroActionThreshold x ≤ a) :
    lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a = 0 := by
  have hx : x ∈ Sanctions.S :=
    redesign_narrow_state_mem hx0 hx1
  have hzero : (0 : ℝ) ∈ Sanctions.I := by
    constructor <;> norm_num [Sanctions.I]
  have hzeroLand :
      (99 / 100 : ℝ) * x + (1 / 100) * 0 ≤
        redesignLandingThreshold := by
    norm_num [redesignLandingThreshold, redesignX0,
      redesignSenderThreshold0, redesignXPlus] at hx1 ⊢
    linarith
  have hzeroLow :
      (1 / 10 : ℝ) ≤
        (99 / 100) * x + (1 / 100) * 0 := by
    norm_num [redesignXMinus] at hx0 ⊢
    linarith
  have hsmear_zero :=
    coupledRedesignSenderRamp_smear_transition_zero
      hx hzero hzeroLand hzeroLow
  have hresponseNonpos :
      redesignResponseInactive x a ≤ 0 := by
    norm_num [redesignZeroActionThreshold,
      redesignResponseInactive, redesignResponseU0,
      redesignResponseV0, redesignResponseK0] at haZero ⊢
    linarith
  have hmax : IsMaxOn
      (fun s =>
        lowDeltaShocked.toParams.U_S x a s +
          lowDeltaShocked.toParams.β_S *
            lowDeltaShocked.smear coupledRedesignSenderRamp
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F x s)))
      Sanctions.I 0 := by
    rw [isMaxOn_iff]
    intro s hs
    have hsLow :
        (1 / 10 : ℝ) ≤
          (99 / 100) * x + (1 / 100) * s := by
      rcases hs with ⟨hs0, _hs1⟩
      norm_num [redesignXMinus] at hx0 ⊢
      linarith
    have hsHigh :
        (99 / 100 : ℝ) * x + (1 / 100) * s ≤
          redesignLandingThreshold + 1 / 10 := by
      rcases hs with ⟨_hs0, hs1⟩
      norm_num [redesignXPlus, redesignLandingThreshold,
        redesignX0, redesignSenderThreshold0] at hx1 ⊢
      linarith
    by_cases hsInactive : s ≤ redesignSenderThreshold x
    · have hsLand :
          (99 / 100 : ℝ) * x + (1 / 100) * s ≤
            redesignLandingThreshold := by
        norm_num [redesignSenderThreshold] at hsInactive ⊢
        linarith
      have hsmear_s :=
        coupledRedesignSenderRamp_smear_transition_zero
          hx hs hsLand hsLow
      rw [hsmear_s, hsmear_zero]
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
        lowDeltaParams_β_S]
      rcases hs with ⟨hs0, _hs1⟩
      norm_num [mwU_S, redesignResponseInactive,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0] at hresponseNonpos ⊢
      nlinarith [sq_nonneg
        (s - (9 / 8 * x - 1 / 12 - 5 / 12 * a))]
    · have hsLand :
          redesignLandingThreshold ≤
            (99 / 100 : ℝ) * x + (1 / 100) * s := by
        have hsAbove : redesignSenderThreshold x ≤ s := by
          linarith
        norm_num [redesignSenderThreshold] at hsAbove ⊢
        linarith
      have hsmear_s :=
        coupledRedesignSenderRamp_smear_transition_quadratic
          hx hs hsLand hsLow hsHigh
      have hthresholdNonneg :
          0 ≤ redesignSenderThreshold x := by
        norm_num [redesignSenderThreshold, redesignLandingThreshold,
          redesignX0, redesignSenderThreshold0,
          redesignXPlus] at hx1 ⊢
        linarith
      have hlandExcessNonneg :
          0 ≤ (99 / 100 : ℝ) * x + (1 / 100) * s -
            redesignLandingThreshold := by
        linarith
      have hlandExcessUpper :
          (99 / 100 : ℝ) * x + (1 / 100) * s -
              redesignLandingThreshold ≤
            s / 100 := by
        norm_num [redesignSenderThreshold] at hthresholdNonneg ⊢
        linarith
      have hlandSquareUpper :
          ((99 / 100 : ℝ) * x + (1 / 100) * s -
              redesignLandingThreshold) ^ 2 ≤
            (s / 100) ^ 2 := by
        have hsDivNonneg : (0 : ℝ) ≤ s / 100 := by
          exact div_nonneg hs.1 (by norm_num : (0 : ℝ) ≤ 100)
        have hprod := mul_nonneg
          (sub_nonneg.mpr hlandExcessUpper)
          (add_nonneg hsDivNonneg
            hlandExcessNonneg)
        nlinarith
      rw [hsmear_s, hsmear_zero]
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
        lowDeltaParams_β_S]
      rcases hs with ⟨hs0, _hs1⟩
      norm_num [mwU_S, redesignResponseInactive,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignRampSlope_eq,
        redesignLandingThreshold, redesignX0,
        redesignSenderThreshold0, redesignZeroActionThreshold,
        redesignSenderThreshold] at haZero hsInactive hresponseNonpos ⊢
      norm_num [redesignLandingThreshold, redesignX0,
        redesignSenderThreshold0] at hlandSquareUpper
      nlinarith
  exact
    (AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
      ((coupled_sender_strongConcave coupledRedesignSenderRamp
        coupledRedesignSenderRamp_mem.2 x hx a).strictConcaveOn
        (by norm_num))
      (lowDeltaShocked.toParams.σ_dyn_top_mem_I
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a)
      hzero
      (lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
        (lowDeltaShocked.smear coupledRedesignSenderRamp) x a)
      hmax)

/-! ## Exact Target continuation and reduced objectives -/

private theorem coupledRedesignTargetLinear_smear
    (y : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaShocked.smear coupledRedesignTargetLinear y =
      redesignTargetLinearSlope *
        lowDeltaShocked.smear coupledSenderIdentity y := by
  rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    Sanctions.movAvgBCF_apply]
  unfold Sanctions.movAvgReal
  change (1 / (2 * (1 / 10 : ℝ))) *
      (∫ z in (y.val - 1 / 10)..(y.val + 1 / 10),
        redesignTargetLinearSlope *
          coupledSenderIdentity (Sanctions.clipS' z)) =
    redesignTargetLinearSlope *
      ((1 / (2 * (1 / 10 : ℝ))) *
        (∫ z in (y.val - 1 / 10)..(y.val + 1 / 10),
          coupledSenderIdentity (Sanctions.clipS' z)))
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem coupledRedesignTargetLinear_smear_transition
    {x s : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (hs : s ∈ Sanctions.I) :
    lowDeltaShocked.smear coupledRedesignTargetLinear
        (Sanctions.clipS'
          (lowDeltaShocked.toParams.F x s)) =
      redesignTargetLinearSlope *
        lowDeltaShocked.toParams.F x s := by
  have hy0 : (1 / 10 : ℝ) ≤
      lowDeltaShocked.toParams.F x s := by
    rcases hs with ⟨hs0, _hs1⟩
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    norm_num [redesignXMinus] at hx0 ⊢
    linarith
  have hy1 : lowDeltaShocked.toParams.F x s
      ≤ (9 / 10 : ℝ) := by
    rcases hs with ⟨_hs0, hs1⟩
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    norm_num [redesignXPlus] at hx1 ⊢
    linarith
  have hyS : lowDeltaShocked.toParams.F x s
      ∈ Sanctions.S := ⟨le_trans (by norm_num) hy0,
        le_trans hy1 (by norm_num)⟩
  rw [coupledRedesignTargetLinear_smear,
    lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hyS]
  congr 1
  exact coupledSenderIdentity_movAvg hy0 hy1

private theorem coupledRedesignLeaderObj_active
    {x a : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (ha : a ∈ Sanctions.I)
    (haActive : a ≤ redesignActionThreshold x) :
    coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp x a =
      redesignTargetConstant x +
        redesignReducedTargetObj x redesignResponseK1
          redesignResponseU1 redesignResponseV1 a := by
  have ht : redesignResponseActive x a ∈ Sanctions.I :=
    redesign_active_response_mem hx1 ha haActive
  unfold coupledLeaderObj
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [coupledRedesign_sigmaDynTop_active hx0 hx1 ha haActive,
    coupledRedesignTargetLinear_smear_transition hx0 hx1 ht]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_β_T,
    lowDeltaParams_F, lowDeltaParams_U_T, AbstractGame.affineF]
  norm_num [mwU_T, redesignTargetConstant,
    redesignReducedTargetObj, redesignResponseActive,
    redesignTargetLinearSlope, redesignTargetLandingSlope] at ⊢
  ring

private theorem coupledRedesignLeaderObj_inactive
    {x a : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (ha : a ∈ Sanctions.I)
    (haInactive : redesignActionThreshold x ≤ a)
    (haZero : a ≤ redesignZeroActionThreshold x) :
    coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp x a =
      redesignTargetConstant x +
        redesignReducedTargetObj x redesignResponseK0
          redesignResponseU0 redesignResponseV0 a := by
  have ht : redesignResponseInactive x a ∈ Sanctions.I :=
    redesign_inactive_response_mem hx1 ha haZero
  unfold coupledLeaderObj
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [coupledRedesign_sigmaDynTop_inactive
      hx0 hx1 ha haInactive haZero,
    coupledRedesignTargetLinear_smear_transition hx0 hx1 ht]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_β_T,
    lowDeltaParams_F, lowDeltaParams_U_T, AbstractGame.affineF]
  norm_num [mwU_T, redesignTargetConstant,
    redesignReducedTargetObj, redesignResponseInactive,
    redesignTargetLinearSlope, redesignTargetLandingSlope] at ⊢
  ring

private theorem coupledRedesignLeaderObj_zero
    {x a : ℝ}
    (hx0 : redesignXMinus ≤ x) (hx1 : x ≤ redesignXPlus)
    (haZero : redesignZeroActionThreshold x ≤ a) :
    coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp x a =
      redesignTargetConstant x - a ^ 2 + (2 * x - 1) * a := by
  have hzero : (0 : ℝ) ∈ Sanctions.I := by
    constructor <;> norm_num [Sanctions.I]
  unfold coupledLeaderObj
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [coupledRedesign_sigmaDynTop_zero hx0 hx1 haZero,
    coupledRedesignTargetLinear_smear_transition hx0 hx1 hzero]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_β_T,
    lowDeltaParams_F, lowDeltaParams_U_T, AbstractGame.affineF]
  norm_num [mwU_T, redesignTargetConstant] at ⊢
  ring

private theorem redesignReducedTargetObj_vertex_gap
    (x k u v a : ℝ) (hk : 2 + k ≠ 0) :
    redesignReducedTargetObj x k u v
          (redesignBranchVertex x k u v) -
        redesignReducedTargetObj x k u v a =
      (1 + k / 2) *
        (a - redesignBranchVertex x k u v) ^ 2 := by
  unfold redesignReducedTargetObj redesignBranchVertex
  field_simp [hk]
  ring

private theorem redesign_exact_vertices :
    redesignLeftVertex redesignX0 = coupledRedesignTieLeftAction ∧
    redesignRightVertex redesignX0 = coupledRedesignTieRightAction ∧
    redesignRightVertex redesignXMinus =
      coupledRedesignLowerOptimalAction ∧
    redesignLeftVertex redesignXPlus =
      coupledRedesignUpperOptimalAction := by
  norm_num [redesignLeftVertex, redesignRightVertex,
    redesignBranchVertex, redesignResponseK1_eq,
    redesignResponseU1_eq, redesignResponseV1_eq,
    redesignResponseK0, redesignResponseU0, redesignResponseV0,
    redesignX0, redesignXMinus, redesignXPlus,
    coupledRedesignTieLeftAction, coupledRedesignTieRightAction,
    coupledRedesignLowerOptimalAction,
    coupledRedesignUpperOptimalAction,
    redesignTargetLandingSlope]

private theorem coupledRedesign_tie_left_isMaxOn :
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignX0)
      Sanctions.I coupledRedesignTieLeftAction := by
  have hx0 : redesignXMinus ≤ redesignX0 := by
    norm_num [redesignXMinus, redesignX0]
  have hx1 : redesignX0 ≤ redesignXPlus := by
    norm_num [redesignXPlus, redesignX0]
  have haL : coupledRedesignTieLeftAction ∈ Sanctions.I := by
    constructor <;> norm_num [coupledRedesignTieLeftAction]
  have haLActive :
      coupledRedesignTieLeftAction ≤
        redesignActionThreshold redesignX0 := by
    norm_num [coupledRedesignTieLeftAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignX0, redesignSenderThreshold0]
  rw [isMaxOn_iff]
  intro a ha
  by_cases haActive : a ≤ redesignActionThreshold redesignX0
  · rw [coupledRedesignLeaderObj_active hx0 hx1 ha haActive,
      coupledRedesignLeaderObj_active hx0 hx1 haL haLActive]
    have hgap := redesignReducedTargetObj_vertex_gap
      redesignX0 redesignResponseK1 redesignResponseU1
        redesignResponseV1 a (by
          norm_num [redesignResponseK1_eq])
    have hvertex :
        redesignBranchVertex redesignX0 redesignResponseK1
            redesignResponseU1 redesignResponseV1 =
          coupledRedesignTieLeftAction := by
      exact redesign_exact_vertices.1
    rw [hvertex] at hgap
    have hcoef :
        0 ≤ 1 + redesignResponseK1 / 2 := by
      norm_num [redesignResponseK1_eq]
    nlinarith [mul_nonneg hcoef
      (sq_nonneg (a - coupledRedesignTieLeftAction))]
  · have haInactive :
        redesignActionThreshold redesignX0 ≤ a := by
      linarith
    by_cases haBelowZero :
        a ≤ redesignZeroActionThreshold redesignX0
    · rw [coupledRedesignLeaderObj_inactive
          hx0 hx1 ha haInactive haBelowZero,
        coupledRedesignLeaderObj_active hx0 hx1 haL haLActive]
      have hgap := redesignReducedTargetObj_vertex_gap
        redesignX0 redesignResponseK0 redesignResponseU0
          redesignResponseV0 a (by
            norm_num [redesignResponseK0])
      have hvertex :
          redesignBranchVertex redesignX0 redesignResponseK0
              redesignResponseU0 redesignResponseV0 =
            coupledRedesignTieRightAction := by
        exact redesign_exact_vertices.2.1
      rw [hvertex] at hgap
      have htie :
          redesignReducedTargetObj redesignX0 redesignResponseK1
              redesignResponseU1 redesignResponseV1
              coupledRedesignTieLeftAction =
            redesignReducedTargetObj redesignX0 redesignResponseK0
              redesignResponseU0 redesignResponseV0
              coupledRedesignTieRightAction := by
        norm_num [redesignReducedTargetObj,
          redesignResponseK1_eq, redesignResponseU1_eq,
          redesignResponseV1_eq, redesignResponseK0,
          redesignResponseU0, redesignResponseV0,
          redesignX0, redesignTargetLandingSlope,
          coupledRedesignTieLeftAction,
          coupledRedesignTieRightAction]
      have hcoef :
          0 ≤ 1 + redesignResponseK0 / 2 := by
        norm_num [redesignResponseK0]
      nlinarith [mul_nonneg hcoef
        (sq_nonneg (a - coupledRedesignTieRightAction))]
    · have haAboveZero :
          redesignZeroActionThreshold redesignX0 ≤ a := by
        linarith
      rw [coupledRedesignLeaderObj_zero hx0 hx1 haAboveZero,
        coupledRedesignLeaderObj_active hx0 hx1 haL haLActive]
      norm_num [redesignReducedTargetObj,
        redesignResponseK1_eq, redesignResponseU1_eq,
        redesignResponseV1_eq, redesignX0,
        redesignTargetLandingSlope,
        coupledRedesignTieLeftAction] at ⊢
      norm_num [redesignZeroActionThreshold,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignX0] at haAboveZero
      nlinarith [sq_nonneg a]

private theorem coupledRedesign_tie_objective_eq :
    coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignX0
        coupledRedesignTieLeftAction =
      coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignX0
        coupledRedesignTieRightAction := by
  have hx0 : redesignXMinus ≤ redesignX0 := by
    norm_num [redesignXMinus, redesignX0]
  have hx1 : redesignX0 ≤ redesignXPlus := by
    norm_num [redesignXPlus, redesignX0]
  have haL : coupledRedesignTieLeftAction ∈ Sanctions.I := by
    constructor <;> norm_num [coupledRedesignTieLeftAction]
  have haR : coupledRedesignTieRightAction ∈ Sanctions.I := by
    constructor <;> norm_num [coupledRedesignTieRightAction]
  have haLActive :
      coupledRedesignTieLeftAction ≤
        redesignActionThreshold redesignX0 := by
    norm_num [coupledRedesignTieLeftAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignX0, redesignSenderThreshold0]
  have haRInactive :
      redesignActionThreshold redesignX0 ≤
        coupledRedesignTieRightAction := by
    norm_num [coupledRedesignTieRightAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignX0, redesignSenderThreshold0]
  have haRZero :
      coupledRedesignTieRightAction ≤
        redesignZeroActionThreshold redesignX0 := by
    norm_num [coupledRedesignTieRightAction,
      redesignZeroActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0, redesignX0]
  rw [coupledRedesignLeaderObj_active hx0 hx1 haL haLActive,
    coupledRedesignLeaderObj_inactive
      hx0 hx1 haR haRInactive haRZero]
  norm_num [redesignReducedTargetObj,
    redesignResponseK1_eq, redesignResponseU1_eq,
    redesignResponseV1_eq, redesignResponseK0,
    redesignResponseU0, redesignResponseV0,
    redesignX0, redesignTargetLandingSlope,
    coupledRedesignTieLeftAction,
    coupledRedesignTieRightAction]

private theorem coupledRedesign_tie_right_isMaxOn :
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignX0)
      Sanctions.I coupledRedesignTieRightAction := by
  rw [isMaxOn_iff]
  intro a ha
  have hle := (isMaxOn_iff.mp
    coupledRedesign_tie_left_isMaxOn) a ha
  rw [coupledRedesign_tie_objective_eq] at hle
  exact hle

/-- At `x = 5/12`, the admissible ramp/linear continuation pair has two
distinct global Target maximizers.  Hence no positive quadratic-growth
inequality can hold uniformly on the redesigned continuation carriers. -/
theorem coupledRedesignTarget_two_global_maxima :
    coupledRedesignTieState ∈ Sanctions.S ∧
    coupledRedesignTieLeftAction ∈ Sanctions.I ∧
    coupledRedesignTieRightAction ∈ Sanctions.I ∧
    coupledRedesignTieLeftAction ≠ coupledRedesignTieRightAction ∧
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp coupledRedesignTieState)
      Sanctions.I coupledRedesignTieLeftAction ∧
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp coupledRedesignTieState)
      Sanctions.I coupledRedesignTieRightAction := by
  constructor
  · constructor <;> norm_num [coupledRedesignTieState, Sanctions.S]
  constructor
  · constructor <;> norm_num [coupledRedesignTieLeftAction, Sanctions.I]
  constructor
  · constructor <;> norm_num [coupledRedesignTieRightAction, Sanctions.I]
  constructor
  · norm_num [coupledRedesignTieLeftAction,
      coupledRedesignTieRightAction]
  constructor
  · simpa only [coupledRedesignTieState, redesignX0] using
      coupledRedesign_tie_left_isMaxOn
  · simpa only [coupledRedesignTieState, redesignX0] using
      coupledRedesign_tie_right_isMaxOn

/-- At the fixed admissible continuation pair, no feasible proposed Target
action can satisfy a quadratic-growth inequality with any positive modulus at
the tie state.  The conclusion quantifies over the proposed action; it does not
assume that the proposal was selected by a particular tie-breaking rule. -/
theorem coupledRedesign_no_target_quadratic_growth_at_tie_of_pos
    (q : ℝ) (hq : 0 < q) :
    ¬ ∃ proposed : ℝ,
      proposed ∈ Sanctions.I ∧
      ∀ a ∈ Sanctions.I,
        q * (a - proposed) ^ 2 ≤
          coupledLeaderObj coupledRedesignTargetLinear
              coupledRedesignSenderRamp coupledRedesignTieState proposed -
            coupledLeaderObj coupledRedesignTargetLinear
              coupledRedesignSenderRamp coupledRedesignTieState a := by
  rintro ⟨proposed, hproposed, hgrowth⟩
  rcases coupledRedesignTarget_two_global_maxima with
    ⟨_hx, haL, haR, hne, hmaxL, _hmaxR⟩
  have hproposal_le :=
    (isMaxOn_iff.mp hmaxL) proposed hproposed
  have hgL := hgrowth coupledRedesignTieLeftAction haL
  have hproposal_eq :
      proposed = coupledRedesignTieLeftAction := by
    have hprod_le :
        q * (coupledRedesignTieLeftAction - proposed) ^ 2 ≤ 0 := by
      linarith
    have hprod_eq :
        q * (coupledRedesignTieLeftAction - proposed) ^ 2 = 0 :=
      le_antisymm hprod_le
        (mul_nonneg (le_of_lt hq)
          (sq_nonneg (coupledRedesignTieLeftAction - proposed)))
    rcases mul_eq_zero.mp hprod_eq with hq0 | hsq0
    · exact (ne_of_gt hq hq0).elim
    · nlinarith
  have hgR := hgrowth coupledRedesignTieRightAction haR
  rw [hproposal_eq] at hgR
  have heq :
      coupledLeaderObj coupledRedesignTargetLinear
          coupledRedesignSenderRamp coupledRedesignTieState
          coupledRedesignTieLeftAction =
        coupledLeaderObj coupledRedesignTargetLinear
          coupledRedesignSenderRamp coupledRedesignTieState
          coupledRedesignTieRightAction := by
    simpa only [coupledRedesignTieState, redesignX0] using
      coupledRedesign_tie_objective_eq
  rw [heq] at hgR
  have hsq :
      0 < (coupledRedesignTieRightAction -
        coupledRedesignTieLeftAction) ^ 2 := by
    norm_num [coupledRedesignTieRightAction,
      coupledRedesignTieLeftAction]
  nlinarith [mul_pos hq hsq]

/-- The redesigned-carrier Target quadratic-growth obligation at an arbitrary
modulus `q`.  This is a diagnostic proposition, not a new model assumption. -/
abbrev CoupledTargetQuadraticGrowthLipCarrierAt (q : ℝ) : Prop :=
  ∃ lead : SBCF → SBCF → ℝ → ℝ,
    (∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S,
      lead V_T V_S x ∈ Sanctions.I) ∧
    ∀ V_T ∈ coupledCarrierTLip, ∀ V_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        q * (a - lead V_T V_S x.val) ^ 2 ≤
          coupledLeaderObj V_T V_S x.val
              (lead V_T V_S x.val) -
            coupledLeaderObj V_T V_S x.val a

/-- Even after replacing the Target carrier by the invariant norm--Lipschitz
carrier, no positive carrier-uniform Target quadratic-growth modulus exists. -/
theorem not_coupledTargetQuadraticGrowthLipCarrierAt
    (q : ℝ) (hq : 0 < q) :
    ¬ CoupledTargetQuadraticGrowthLipCarrierAt q := by
  rintro ⟨lead, hmem, hgrowth⟩
  let x : ↥(Sanctions.S : Set ℝ) :=
    ⟨coupledRedesignTieState,
      coupledRedesignTarget_two_global_maxima.1⟩
  have hleadI :
      lead coupledRedesignTargetLinear coupledRedesignSenderRamp x.val
        ∈ Sanctions.I :=
    hmem coupledRedesignTargetLinear coupledRedesignSenderRamp
      x.val x.property
  have hg :
      ∀ a ∈ Sanctions.I,
        q *
            (a -
              lead coupledRedesignTargetLinear
                coupledRedesignSenderRamp x.val) ^ 2 ≤
          coupledLeaderObj coupledRedesignTargetLinear
              coupledRedesignSenderRamp x.val
              (lead coupledRedesignTargetLinear
                coupledRedesignSenderRamp x.val) -
            coupledLeaderObj coupledRedesignTargetLinear
              coupledRedesignSenderRamp x.val a :=
    hgrowth coupledRedesignTargetLinear
      coupledRedesignTargetLinear_mem
      coupledRedesignSenderRamp coupledRedesignSenderRamp_mem x
  apply coupledRedesign_no_target_quadratic_growth_at_tie_of_pos q hq
  refine ⟨lead coupledRedesignTargetLinear
      coupledRedesignSenderRamp x.val, hleadI, ?_⟩
  simpa only [x] using hg

/-- Historical modulus-`1/2` redesigned-carrier formulation, retained only
as a one-line specialization of the positive-modulus obstruction. -/
abbrev CoupledTargetQuadraticGrowthLipCarrier : Prop :=
  CoupledTargetQuadraticGrowthLipCarrierAt (1 / 2)

theorem not_coupledTargetQuadraticGrowthLipCarrier :
    ¬ CoupledTargetQuadraticGrowthLipCarrier :=
  not_coupledTargetQuadraticGrowthLipCarrierAt (1 / 2) (by norm_num)

private theorem coupledRedesign_lower_isMaxOn :
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignXMinus)
      Sanctions.I coupledRedesignLowerOptimalAction := by
  have hx0 : redesignXMinus ≤ redesignXMinus := le_rfl
  have hx1 : redesignXMinus ≤ redesignXPlus := by
    norm_num [redesignXMinus, redesignXPlus]
  have haC : coupledRedesignLowerOptimalAction ∈ Sanctions.I := by
    constructor <;>
      norm_num [coupledRedesignLowerOptimalAction, Sanctions.I]
  have haCInactive :
      redesignActionThreshold redesignXMinus ≤
        coupledRedesignLowerOptimalAction := by
    norm_num [coupledRedesignLowerOptimalAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignXMinus, redesignX0, redesignSenderThreshold0]
  have haCZero :
      coupledRedesignLowerOptimalAction ≤
        redesignZeroActionThreshold redesignXMinus := by
    norm_num [coupledRedesignLowerOptimalAction,
      redesignZeroActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0, redesignXMinus]
  rw [isMaxOn_iff]
  intro a ha
  by_cases haActive :
      a ≤ redesignActionThreshold redesignXMinus
  · rw [coupledRedesignLeaderObj_active hx0 hx1 ha haActive,
      coupledRedesignLeaderObj_inactive
        hx0 hx1 haC haCInactive haCZero]
    have hgap := redesignReducedTargetObj_vertex_gap
      redesignXMinus redesignResponseK1 redesignResponseU1
        redesignResponseV1 a (by
          norm_num [redesignResponseK1_eq])
    have hcoef :
        0 ≤ 1 + redesignResponseK1 / 2 := by
      norm_num [redesignResponseK1_eq]
    have hbranch :
        redesignReducedTargetObj redesignXMinus redesignResponseK1
            redesignResponseU1 redesignResponseV1
            (redesignLeftVertex redesignXMinus) <
          redesignReducedTargetObj redesignXMinus redesignResponseK0
            redesignResponseU0 redesignResponseV0
            coupledRedesignLowerOptimalAction := by
      norm_num [redesignReducedTargetObj, redesignLeftVertex,
        redesignBranchVertex, redesignResponseK1_eq,
        redesignResponseU1_eq, redesignResponseV1_eq,
        redesignResponseK0, redesignResponseU0,
        redesignResponseV0, redesignXMinus,
        redesignTargetLandingSlope,
        coupledRedesignLowerOptimalAction]
    have hvertex :
        redesignBranchVertex redesignXMinus redesignResponseK1
            redesignResponseU1 redesignResponseV1 =
          redesignLeftVertex redesignXMinus := rfl
    rw [hvertex] at hgap
    nlinarith [mul_nonneg hcoef
      (sq_nonneg
        (a - redesignLeftVertex redesignXMinus))]
  · have haInactive :
        redesignActionThreshold redesignXMinus ≤ a := by
      linarith
    by_cases haBelowZero :
        a ≤ redesignZeroActionThreshold redesignXMinus
    · rw [coupledRedesignLeaderObj_inactive
          hx0 hx1 ha haInactive haBelowZero,
        coupledRedesignLeaderObj_inactive
          hx0 hx1 haC haCInactive haCZero]
      have hgap := redesignReducedTargetObj_vertex_gap
        redesignXMinus redesignResponseK0 redesignResponseU0
          redesignResponseV0 a (by
            norm_num [redesignResponseK0])
      have hvertex :
          redesignBranchVertex redesignXMinus redesignResponseK0
              redesignResponseU0 redesignResponseV0 =
            coupledRedesignLowerOptimalAction := by
        exact redesign_exact_vertices.2.2.1
      rw [hvertex] at hgap
      have hcoef :
          0 ≤ 1 + redesignResponseK0 / 2 := by
        norm_num [redesignResponseK0]
      nlinarith [mul_nonneg hcoef
        (sq_nonneg
          (a - coupledRedesignLowerOptimalAction))]
    · have haAboveZero :
          redesignZeroActionThreshold redesignXMinus ≤ a := by
        linarith
      rw [coupledRedesignLeaderObj_zero hx0 hx1 haAboveZero,
        coupledRedesignLeaderObj_inactive
          hx0 hx1 haC haCInactive haCZero]
      norm_num [redesignReducedTargetObj,
        redesignResponseK0, redesignResponseU0,
        redesignResponseV0, redesignXMinus,
        redesignTargetLandingSlope,
        coupledRedesignLowerOptimalAction] at ⊢
      norm_num [redesignZeroActionThreshold,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignXMinus] at haAboveZero
      nlinarith [sq_nonneg a]

private theorem coupledRedesign_lower_unique
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignXMinus)
      Sanctions.I a) :
    a = coupledRedesignLowerOptimalAction := by
  have hx0 : redesignXMinus ≤ redesignXMinus := le_rfl
  have hx1 : redesignXMinus ≤ redesignXPlus := by
    norm_num [redesignXMinus, redesignXPlus]
  have haC : coupledRedesignLowerOptimalAction ∈ Sanctions.I := by
    constructor <;>
      norm_num [coupledRedesignLowerOptimalAction, Sanctions.I]
  have haCInactive :
      redesignActionThreshold redesignXMinus ≤
        coupledRedesignLowerOptimalAction := by
    norm_num [coupledRedesignLowerOptimalAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignXMinus, redesignX0, redesignSenderThreshold0]
  have haCZero :
      coupledRedesignLowerOptimalAction ≤
        redesignZeroActionThreshold redesignXMinus := by
    norm_num [coupledRedesignLowerOptimalAction,
      redesignZeroActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0, redesignXMinus]
  have hge := (isMaxOn_iff.mp hmax)
    coupledRedesignLowerOptimalAction haC
  by_cases haActive :
      a ≤ redesignActionThreshold redesignXMinus
  · rw [coupledRedesignLeaderObj_inactive
        hx0 hx1 haC haCInactive haCZero,
      coupledRedesignLeaderObj_active hx0 hx1 ha haActive] at hge
    have hgap := redesignReducedTargetObj_vertex_gap
      redesignXMinus redesignResponseK1 redesignResponseU1
        redesignResponseV1 a (by
          norm_num [redesignResponseK1_eq])
    have hcoef :
        0 ≤ 1 + redesignResponseK1 / 2 := by
      norm_num [redesignResponseK1_eq]
    have hbranch :
        redesignReducedTargetObj redesignXMinus redesignResponseK1
            redesignResponseU1 redesignResponseV1
            (redesignLeftVertex redesignXMinus) <
          redesignReducedTargetObj redesignXMinus redesignResponseK0
            redesignResponseU0 redesignResponseV0
            coupledRedesignLowerOptimalAction := by
      norm_num [redesignReducedTargetObj, redesignLeftVertex,
        redesignBranchVertex, redesignResponseK1_eq,
        redesignResponseU1_eq, redesignResponseV1_eq,
        redesignResponseK0, redesignResponseU0,
        redesignResponseV0, redesignXMinus,
        redesignTargetLandingSlope,
        coupledRedesignLowerOptimalAction]
    have hvertex :
        redesignBranchVertex redesignXMinus redesignResponseK1
            redesignResponseU1 redesignResponseV1 =
          redesignLeftVertex redesignXMinus := rfl
    rw [hvertex] at hgap
    exfalso
    nlinarith [mul_nonneg hcoef
      (sq_nonneg
        (a - redesignLeftVertex redesignXMinus))]
  · have haInactive :
        redesignActionThreshold redesignXMinus ≤ a := by
      linarith
    by_cases haBelowZero :
        a ≤ redesignZeroActionThreshold redesignXMinus
    · rw [coupledRedesignLeaderObj_inactive
          hx0 hx1 haC haCInactive haCZero,
        coupledRedesignLeaderObj_inactive
          hx0 hx1 ha haInactive haBelowZero] at hge
      have hgap := redesignReducedTargetObj_vertex_gap
        redesignXMinus redesignResponseK0 redesignResponseU0
          redesignResponseV0 a (by
            norm_num [redesignResponseK0])
      have hvertex :
          redesignBranchVertex redesignXMinus redesignResponseK0
              redesignResponseU0 redesignResponseV0 =
            coupledRedesignLowerOptimalAction := by
        exact redesign_exact_vertices.2.2.1
      rw [hvertex] at hgap
      have hcoef :
          0 < 1 + redesignResponseK0 / 2 := by
        norm_num [redesignResponseK0]
      have hsquare_le :
          (a - coupledRedesignLowerOptimalAction) ^ 2 ≤ 0 := by
        nlinarith
      have hsquare :
          (a - coupledRedesignLowerOptimalAction) ^ 2 = 0 :=
        le_antisymm hsquare_le
          (sq_nonneg
            (a - coupledRedesignLowerOptimalAction))
      have hdiff :
          a - coupledRedesignLowerOptimalAction = 0 :=
        sq_eq_zero_iff.mp hsquare
      linarith
    · have haAboveZero :
          redesignZeroActionThreshold redesignXMinus ≤ a := by
        linarith
      rw [coupledRedesignLeaderObj_inactive
          hx0 hx1 haC haCInactive haCZero,
        coupledRedesignLeaderObj_zero hx0 hx1 haAboveZero] at hge
      norm_num [redesignReducedTargetObj,
        redesignResponseK0, redesignResponseU0,
        redesignResponseV0, redesignXMinus,
        redesignTargetLandingSlope,
        coupledRedesignLowerOptimalAction] at hge
      norm_num [redesignZeroActionThreshold,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignXMinus] at haAboveZero
      exfalso
      nlinarith [sq_nonneg a]

private theorem coupledRedesign_upper_isMaxOn :
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignXPlus)
      Sanctions.I coupledRedesignUpperOptimalAction := by
  have hx0 : redesignXMinus ≤ redesignXPlus := by
    norm_num [redesignXMinus, redesignXPlus]
  have hx1 : redesignXPlus ≤ redesignXPlus := le_rfl
  have haC : coupledRedesignUpperOptimalAction ∈ Sanctions.I := by
    constructor <;>
      norm_num [coupledRedesignUpperOptimalAction, Sanctions.I]
  have haCActive :
      coupledRedesignUpperOptimalAction ≤
        redesignActionThreshold redesignXPlus := by
    norm_num [coupledRedesignUpperOptimalAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignXPlus, redesignX0, redesignSenderThreshold0]
  rw [isMaxOn_iff]
  intro a ha
  by_cases haActive :
      a ≤ redesignActionThreshold redesignXPlus
  · rw [coupledRedesignLeaderObj_active hx0 hx1 ha haActive,
      coupledRedesignLeaderObj_active hx0 hx1 haC haCActive]
    have hgap := redesignReducedTargetObj_vertex_gap
      redesignXPlus redesignResponseK1 redesignResponseU1
        redesignResponseV1 a (by
          norm_num [redesignResponseK1_eq])
    have hvertex :
        redesignBranchVertex redesignXPlus redesignResponseK1
            redesignResponseU1 redesignResponseV1 =
          coupledRedesignUpperOptimalAction := by
      exact redesign_exact_vertices.2.2.2
    rw [hvertex] at hgap
    have hcoef :
        0 ≤ 1 + redesignResponseK1 / 2 := by
      norm_num [redesignResponseK1_eq]
    nlinarith [mul_nonneg hcoef
      (sq_nonneg
        (a - coupledRedesignUpperOptimalAction))]
  · have haInactive :
        redesignActionThreshold redesignXPlus ≤ a := by
      linarith
    by_cases haBelowZero :
        a ≤ redesignZeroActionThreshold redesignXPlus
    · rw [coupledRedesignLeaderObj_inactive
          hx0 hx1 ha haInactive haBelowZero,
        coupledRedesignLeaderObj_active hx0 hx1 haC haCActive]
      have hgap := redesignReducedTargetObj_vertex_gap
        redesignXPlus redesignResponseK0 redesignResponseU0
          redesignResponseV0 a (by
            norm_num [redesignResponseK0])
      have hcoef :
          0 ≤ 1 + redesignResponseK0 / 2 := by
        norm_num [redesignResponseK0]
      have hbranch :
          redesignReducedTargetObj redesignXPlus redesignResponseK0
              redesignResponseU0 redesignResponseV0
              (redesignRightVertex redesignXPlus) <
            redesignReducedTargetObj redesignXPlus redesignResponseK1
              redesignResponseU1 redesignResponseV1
              coupledRedesignUpperOptimalAction := by
        norm_num [redesignReducedTargetObj, redesignRightVertex,
          redesignBranchVertex, redesignResponseK1_eq,
          redesignResponseU1_eq, redesignResponseV1_eq,
          redesignResponseK0, redesignResponseU0,
          redesignResponseV0, redesignXPlus,
          redesignTargetLandingSlope,
          coupledRedesignUpperOptimalAction]
      have hvertex :
          redesignBranchVertex redesignXPlus redesignResponseK0
              redesignResponseU0 redesignResponseV0 =
            redesignRightVertex redesignXPlus := rfl
      rw [hvertex] at hgap
      nlinarith [mul_nonneg hcoef
        (sq_nonneg
          (a - redesignRightVertex redesignXPlus))]
    · have haAboveZero :
          redesignZeroActionThreshold redesignXPlus ≤ a := by
        linarith
      rw [coupledRedesignLeaderObj_zero hx0 hx1 haAboveZero,
        coupledRedesignLeaderObj_active hx0 hx1 haC haCActive]
      norm_num [redesignReducedTargetObj,
        redesignResponseK1_eq, redesignResponseU1_eq,
        redesignResponseV1_eq, redesignXPlus,
        redesignTargetLandingSlope,
        coupledRedesignUpperOptimalAction] at ⊢
      norm_num [redesignZeroActionThreshold,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignXPlus] at haAboveZero
      nlinarith [sq_nonneg a]

private theorem coupledRedesign_upper_unique
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignXPlus)
      Sanctions.I a) :
    a = coupledRedesignUpperOptimalAction := by
  have hx0 : redesignXMinus ≤ redesignXPlus := by
    norm_num [redesignXMinus, redesignXPlus]
  have hx1 : redesignXPlus ≤ redesignXPlus := le_rfl
  have haC : coupledRedesignUpperOptimalAction ∈ Sanctions.I := by
    constructor <;>
      norm_num [coupledRedesignUpperOptimalAction, Sanctions.I]
  have haCActive :
      coupledRedesignUpperOptimalAction ≤
        redesignActionThreshold redesignXPlus := by
    norm_num [coupledRedesignUpperOptimalAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignXPlus, redesignX0, redesignSenderThreshold0]
  have hge := (isMaxOn_iff.mp hmax)
    coupledRedesignUpperOptimalAction haC
  by_cases haActive :
      a ≤ redesignActionThreshold redesignXPlus
  · rw [coupledRedesignLeaderObj_active
        hx0 hx1 haC haCActive,
      coupledRedesignLeaderObj_active hx0 hx1 ha haActive] at hge
    have hgap := redesignReducedTargetObj_vertex_gap
      redesignXPlus redesignResponseK1 redesignResponseU1
        redesignResponseV1 a (by
          norm_num [redesignResponseK1_eq])
    have hvertex :
        redesignBranchVertex redesignXPlus redesignResponseK1
            redesignResponseU1 redesignResponseV1 =
          coupledRedesignUpperOptimalAction := by
      exact redesign_exact_vertices.2.2.2
    rw [hvertex] at hgap
    have hcoef :
        0 < 1 + redesignResponseK1 / 2 := by
      norm_num [redesignResponseK1_eq]
    have hsquare_le :
        (a - coupledRedesignUpperOptimalAction) ^ 2 ≤ 0 := by
      nlinarith
    have hsquare :
        (a - coupledRedesignUpperOptimalAction) ^ 2 = 0 :=
      le_antisymm hsquare_le
        (sq_nonneg
          (a - coupledRedesignUpperOptimalAction))
    have hdiff :
        a - coupledRedesignUpperOptimalAction = 0 :=
      sq_eq_zero_iff.mp hsquare
    linarith
  · have haInactive :
        redesignActionThreshold redesignXPlus ≤ a := by
      linarith
    by_cases haBelowZero :
        a ≤ redesignZeroActionThreshold redesignXPlus
    · rw [coupledRedesignLeaderObj_active
          hx0 hx1 haC haCActive,
        coupledRedesignLeaderObj_inactive
          hx0 hx1 ha haInactive haBelowZero] at hge
      have hgap := redesignReducedTargetObj_vertex_gap
        redesignXPlus redesignResponseK0 redesignResponseU0
          redesignResponseV0 a (by
            norm_num [redesignResponseK0])
      have hcoef :
          0 ≤ 1 + redesignResponseK0 / 2 := by
        norm_num [redesignResponseK0]
      have hbranch :
          redesignReducedTargetObj redesignXPlus redesignResponseK0
              redesignResponseU0 redesignResponseV0
              (redesignRightVertex redesignXPlus) <
            redesignReducedTargetObj redesignXPlus redesignResponseK1
              redesignResponseU1 redesignResponseV1
              coupledRedesignUpperOptimalAction := by
        norm_num [redesignReducedTargetObj, redesignRightVertex,
          redesignBranchVertex, redesignResponseK1_eq,
          redesignResponseU1_eq, redesignResponseV1_eq,
          redesignResponseK0, redesignResponseU0,
          redesignResponseV0, redesignXPlus,
          redesignTargetLandingSlope,
          coupledRedesignUpperOptimalAction]
      have hvertex :
          redesignBranchVertex redesignXPlus redesignResponseK0
              redesignResponseU0 redesignResponseV0 =
            redesignRightVertex redesignXPlus := rfl
      rw [hvertex] at hgap
      exfalso
      nlinarith [mul_nonneg hcoef
        (sq_nonneg
          (a - redesignRightVertex redesignXPlus))]
    · have haAboveZero :
          redesignZeroActionThreshold redesignXPlus ≤ a := by
        linarith
      rw [coupledRedesignLeaderObj_active
          hx0 hx1 haC haCActive,
        coupledRedesignLeaderObj_zero hx0 hx1 haAboveZero] at hge
      norm_num [redesignReducedTargetObj,
        redesignResponseK1_eq, redesignResponseU1_eq,
        redesignResponseV1_eq, redesignXPlus,
        redesignTargetLandingSlope,
        coupledRedesignUpperOptimalAction] at hge
      norm_num [redesignZeroActionThreshold,
        redesignResponseU0, redesignResponseV0,
        redesignResponseK0, redesignXPlus] at haAboveZero
      exfalso
      nlinarith [sq_nonneg a]

/-- On the two sides of the tie state, the same admissible continuation pair
has the displayed unique global Target maximizers. -/
theorem coupledRedesignTarget_nearby_unique_maxima :
    coupledRedesignLowerState ∈ Sanctions.S ∧
    coupledRedesignUpperState ∈ Sanctions.S ∧
    coupledRedesignLowerOptimalAction ∈ Sanctions.I ∧
    coupledRedesignUpperOptimalAction ∈ Sanctions.I ∧
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp coupledRedesignLowerState)
      Sanctions.I coupledRedesignLowerOptimalAction ∧
    (∀ a ∈ Sanctions.I,
      IsMaxOn
        (coupledLeaderObj coupledRedesignTargetLinear
          coupledRedesignSenderRamp coupledRedesignLowerState)
        Sanctions.I a →
      a = coupledRedesignLowerOptimalAction) ∧
    IsMaxOn
      (coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp coupledRedesignUpperState)
      Sanctions.I coupledRedesignUpperOptimalAction ∧
    (∀ a ∈ Sanctions.I,
      IsMaxOn
        (coupledLeaderObj coupledRedesignTargetLinear
          coupledRedesignSenderRamp coupledRedesignUpperState)
        Sanctions.I a →
      a = coupledRedesignUpperOptimalAction) := by
  constructor
  · constructor <;>
      norm_num [coupledRedesignLowerState, Sanctions.S]
  constructor
  · constructor <;>
      norm_num [coupledRedesignUpperState, Sanctions.S]
  constructor
  · constructor <;>
      norm_num [coupledRedesignLowerOptimalAction, Sanctions.I]
  constructor
  · constructor <;>
      norm_num [coupledRedesignUpperOptimalAction, Sanctions.I]
  constructor
  · simpa only [coupledRedesignLowerState, redesignXMinus] using
      coupledRedesign_lower_isMaxOn
  constructor
  · intro a ha hmax
    exact coupledRedesign_lower_unique ha
      (by simpa only [coupledRedesignLowerState, redesignXMinus] using hmax)
  constructor
  · simpa only [coupledRedesignUpperState, redesignXPlus] using
      coupledRedesign_upper_isMaxOn
  · intro a ha hmax
    exact coupledRedesign_upper_unique ha
      (by simpa only [coupledRedesignUpperState, redesignXPlus] using hmax)

/-- Every feasible selector that chooses a global Target maximizer for this
fixed admissible continuation pair violates the exact state-Lipschitz budget
needed for Sender-carrier invariance.  Uniqueness at the two test states makes
the conclusion independent of tie-breaking. -/
theorem coupledRedesign_every_optimal_selector_violates_budget
    (lead : ℝ → ℝ)
    (hopt : ∀ x ∈ Sanctions.S,
      lead x ∈ Sanctions.I ∧
      IsMaxOn
        (coupledLeaderObj coupledRedesignTargetLinear
          coupledRedesignSenderRamp x)
        Sanctions.I (lead x)) :
    coupledAlphaStateBudget *
        |coupledRedesignUpperState - coupledRedesignLowerState| <
      |lead coupledRedesignUpperState -
        lead coupledRedesignLowerState| := by
  have hdata := coupledRedesignTarget_nearby_unique_maxima
  have hlow := hopt coupledRedesignLowerState hdata.1
  have hupp := hopt coupledRedesignUpperState hdata.2.1
  have hlowEq :
      lead coupledRedesignLowerState =
        coupledRedesignLowerOptimalAction :=
    hdata.2.2.2.2.2.1
      (lead coupledRedesignLowerState) hlow.1 hlow.2
  have huppEq :
      lead coupledRedesignUpperState =
        coupledRedesignUpperOptimalAction :=
    hdata.2.2.2.2.2.2.2
      (lead coupledRedesignUpperState) hupp.1 hupp.2
  rw [hlowEq, huppEq, coupledAlphaStateBudget_eq]
  norm_num [coupledAlphaStateBudget,
    coupledRedesignUpperState, coupledRedesignLowerState,
    coupledRedesignUpperOptimalAction,
    coupledRedesignLowerOptimalAction, abs_of_nonneg,
    abs_of_nonpos]

/-- There is no globally optimal Target selector for the fixed admissible
continuation pair satisfying the Sender-invariance state modulus. -/
theorem not_coupledRedesign_optimal_selector_state_lipschitz_budget :
    ¬ ∃ lead : ℝ → ℝ,
      (∀ x ∈ Sanctions.S,
        lead x ∈ Sanctions.I ∧
        IsMaxOn
          (coupledLeaderObj coupledRedesignTargetLinear
            coupledRedesignSenderRamp x)
          Sanctions.I (lead x)) ∧
      ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
        |lead y - lead x| ≤
          coupledAlphaStateBudget * |y - x| := by
  rintro ⟨lead, hopt, hlip⟩
  have hdata := coupledRedesignTarget_nearby_unique_maxima
  have hstrict :=
    coupledRedesign_every_optimal_selector_violates_budget lead hopt
  have hweak := hlip coupledRedesignLowerState hdata.1
    coupledRedesignUpperState hdata.2.1
  linarith [abs_sub_comm
    (lead coupledRedesignUpperState)
    (lead coupledRedesignLowerState)]

/-- Local salvage: on each smooth Sender-response branch, the reduced Target
objective retains an exact positive quadratic-growth identity.  The global
failure above is therefore caused by switching and tying the two branch
envelopes, not by loss of curvature within either branch. -/
theorem coupledRedesign_reduced_branches_exact_quadratic_growth
    (x a : ℝ) :
    redesignReducedTargetObj x redesignResponseK1
          redesignResponseU1 redesignResponseV1
          (redesignLeftVertex x) -
        redesignReducedTargetObj x redesignResponseK1
          redesignResponseU1 redesignResponseV1 a =
      (1 + redesignResponseK1 / 2) *
        (a - redesignLeftVertex x) ^ 2 ∧
    redesignReducedTargetObj x redesignResponseK0
          redesignResponseU0 redesignResponseV0
          (redesignRightVertex x) -
        redesignReducedTargetObj x redesignResponseK0
          redesignResponseU0 redesignResponseV0 a =
      (1 + redesignResponseK0 / 2) *
        (a - redesignRightVertex x) ^ 2 := by
  constructor
  · exact redesignReducedTargetObj_vertex_gap
      x redesignResponseK1 redesignResponseU1
        redesignResponseV1 a
        (by norm_num [redesignResponseK1_eq])
  · exact redesignReducedTargetObj_vertex_gap
      x redesignResponseK0 redesignResponseU0
        redesignResponseV0 a
        (by norm_num [redesignResponseK0])

/-- At the tie state, the Target argmax correspondence is not convex-valued:
the midpoint of the two distinct global maximizers is strictly suboptimal.
Consequently, a standard Kakutani route cannot use the pure-action argmax
correspondence on the current carriers. -/
theorem coupledRedesignTarget_argmax_not_convex_at_tie :
    ¬ Convex ℝ
      {a : ℝ |
        a ∈ Sanctions.I ∧
          IsMaxOn
            (coupledLeaderObj coupledRedesignTargetLinear
              coupledRedesignSenderRamp coupledRedesignTieState)
            Sanctions.I a} := by
  intro hconv
  let aM : ℝ :=
    (coupledRedesignTieLeftAction + coupledRedesignTieRightAction) / 2
  have hdata := coupledRedesignTarget_two_global_maxima
  have hL :
      coupledRedesignTieLeftAction ∈
        {a : ℝ |
          a ∈ Sanctions.I ∧
            IsMaxOn
              (coupledLeaderObj coupledRedesignTargetLinear
                coupledRedesignSenderRamp coupledRedesignTieState)
              Sanctions.I a} :=
    ⟨hdata.2.1, hdata.2.2.2.2.1⟩
  have hR :
      coupledRedesignTieRightAction ∈
        {a : ℝ |
          a ∈ Sanctions.I ∧
            IsMaxOn
              (coupledLeaderObj coupledRedesignTargetLinear
                coupledRedesignSenderRamp coupledRedesignTieState)
              Sanctions.I a} :=
    ⟨hdata.2.2.1, hdata.2.2.2.2.2⟩
  have hM := hconv.midpoint_mem hL hR
  have hmidpoint :
      midpoint ℝ coupledRedesignTieLeftAction
          coupledRedesignTieRightAction = aM := by
    rw [midpoint_eq_smul_add]
    change (2 : ℝ)⁻¹ *
        (coupledRedesignTieLeftAction +
          coupledRedesignTieRightAction) = aM
    dsimp only [aM]
    ring
  rw [hmidpoint] at hM
  have hM' :
      aM ∈ Sanctions.I ∧
        IsMaxOn
          (coupledLeaderObj coupledRedesignTargetLinear
            coupledRedesignSenderRamp coupledRedesignTieState)
          Sanctions.I aM := by
    exact hM
  have hleft_le :=
    (isMaxOn_iff.mp hM'.2) coupledRedesignTieLeftAction hdata.2.1
  have hx0 : redesignXMinus ≤ redesignX0 := by
    norm_num [redesignXMinus, redesignX0]
  have hx1 : redesignX0 ≤ redesignXPlus := by
    norm_num [redesignXPlus, redesignX0]
  have haM : aM ∈ Sanctions.I := hM'.1
  have haMInactive : redesignActionThreshold redesignX0 ≤ aM := by
    norm_num [aM, coupledRedesignTieLeftAction,
      coupledRedesignTieRightAction, redesignActionThreshold,
      redesignResponseU0, redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignX0, redesignSenderThreshold0]
  have haMZero : aM ≤ redesignZeroActionThreshold redesignX0 := by
    norm_num [aM, coupledRedesignTieLeftAction,
      coupledRedesignTieRightAction, redesignZeroActionThreshold,
      redesignResponseU0, redesignResponseV0, redesignResponseK0,
      redesignX0]
  have haLActive :
      coupledRedesignTieLeftAction ≤
        redesignActionThreshold redesignX0 := by
    norm_num [coupledRedesignTieLeftAction,
      redesignActionThreshold, redesignResponseU0,
      redesignResponseV0, redesignResponseK0,
      redesignSenderThreshold, redesignLandingThreshold,
      redesignX0, redesignSenderThreshold0]
  change
    coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignX0
        coupledRedesignTieLeftAction ≤
      coupledLeaderObj coupledRedesignTargetLinear
        coupledRedesignSenderRamp redesignX0 aM at hleft_le
  rw [coupledRedesignLeaderObj_active hx0 hx1 hdata.2.1 haLActive,
    coupledRedesignLeaderObj_inactive hx0 hx1 haM
      haMInactive haMZero] at hleft_le
  have hgap := redesignReducedTargetObj_vertex_gap
    redesignX0 redesignResponseK0 redesignResponseU0
      redesignResponseV0 aM (by norm_num [redesignResponseK0])
  have hvertex :
      redesignBranchVertex redesignX0 redesignResponseK0
          redesignResponseU0 redesignResponseV0 =
        coupledRedesignTieRightAction := redesign_exact_vertices.2.1
  rw [hvertex] at hgap
  have htie :
      redesignReducedTargetObj redesignX0 redesignResponseK1
          redesignResponseU1 redesignResponseV1
          coupledRedesignTieLeftAction =
        redesignReducedTargetObj redesignX0 redesignResponseK0
          redesignResponseU0 redesignResponseV0
          coupledRedesignTieRightAction := by
    norm_num [redesignReducedTargetObj,
      redesignResponseK1_eq, redesignResponseU1_eq,
      redesignResponseV1_eq, redesignResponseK0,
      redesignResponseU0, redesignResponseV0,
      redesignX0, redesignTargetLandingSlope,
      coupledRedesignTieLeftAction,
      coupledRedesignTieRightAction]
  have hcoef :
      0 < 1 + redesignResponseK0 / 2 := by
    norm_num [redesignResponseK0]
  have hne : aM ≠ coupledRedesignTieRightAction := by
    norm_num [aM, coupledRedesignTieLeftAction,
      coupledRedesignTieRightAction]
  have hsq : 0 < (aM - coupledRedesignTieRightAction) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith

end

end Examples

end Sanctions
