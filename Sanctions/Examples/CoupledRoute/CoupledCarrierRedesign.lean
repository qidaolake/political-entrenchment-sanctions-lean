/-
Sanctions/Examples/CoupledRoute/CoupledCarrierRedesign.lean

Assumption-neutral carrier redesign for the low-adjustment coupled witness.

The old Target carrier combined a norm bound with monotonicity and is formally
not invariant. This file installs, alongside that audit artifact, a replacement
Target carrier combining the same norm radius with an exact value-Lipschitz
ceiling. It then proves:

* the equilibrium Sender response is state-Lipschitz on the current Sender
  carrier;
* the shocked Target Bellman row preserves the replacement Target carrier;
* the current Sender carrier is preserved by any continuous feasible realized
  Target policy satisfying an exact state-Lipschitz budget.

The final policy budget is conditional: this file does not assume or claim that
the coupled Target argmax has that modulus. Carrier-uniform Target growth and
the selected-policy modulus remain a separate mixed state-action frontier.

No new economic primitive or field is added.
-/

import Sanctions.Examples.CoupledRoute.CoupledObjectiveDifference
import Sanctions.Theory.Shocked.ShockedInvariantLipBall

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction
open AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-! ## Primitive-derived redesign constants and carrier -/

/-- State-action chord coefficient of the Sender objective.  It combines the
stage cross effect with the discounted moving-average rectangle bound. -/
def coupledSigmaStateObjectiveDiffK : ℝ :=
  27 / 20
    + lowDeltaParams.β_S
      * (lowDeltaSenderCarrierLip / (1 / 10))
      * ((1 - lowDeltaParams.δ) * lowDeltaParams.δ)

/-- Conservative Sender-objective curvature used by the redesign numerals
(`= 37877/32000`).  It subtracts from the primitive stage curvature `6/5` a
norm-based continuation term `β_S·δ²·M_S/h²` written with the Sender norm
radius `M_S`.  That is not the one-box derivation: the one-box proof
(`coupled_sender_strongConcave_of_lipschitz`) subtracts `β_S·δ²·K_S/h` and
gives the larger modulus `6/5 − K_S/2000 = 7622623/6400000`.  This constant is
kept, through the corollary `coupled_sender_strongConcave`, because the
downstream numerals are derived from it. -/
def coupledSenderObjectiveCurvature : ℝ :=
  6 / 5
    - lowDeltaParams.β_S * lowDeltaParams.δ ^ 2
      * lowDeltaSenderCarrierNorm / (1 / 10) ^ 2

/-- State modulus of the equilibrium Sender response, derived by dividing the
objective-difference chord by the objective curvature. -/
def coupledSigmaStateK : ℝ :=
  (2 / coupledSenderObjectiveCurvature) * coupledSigmaStateObjectiveDiffK

/-- Direct Target-stage state modulus before the endogenous Sender response
channel is added. -/
def coupledTargetStageStateLip : ℝ := 3

/-- State modulus of the transition after substituting a Sender response with
modulus `coupledSigmaStateK`. -/
def coupledTargetTransitionStateLip : ℝ :=
  (1 - lowDeltaParams.δ) + lowDeltaParams.δ * coupledSigmaStateK

/-- Target value modulus obtained by solving its carrier self-map inequality
at equality. -/
def coupledTargetLipK : ℝ :=
  (coupledTargetStageStateLip + coupledSigmaStateK) /
    (1 - lowDeltaParams.β_T * coupledTargetTransitionStateLip)

/-- Largest Target-policy state modulus compatible with the Sender carrier,
obtained as the residual in the Sender state-Lipschitz self-map inequality. -/
def coupledAlphaStateBudget : ℝ :=
  lowDeltaSenderCarrierLip - lowDeltaSenderStageStateLip
    - lowDeltaParams.β_S * lowDeltaSenderCarrierLip
      * (1 - lowDeltaParams.δ)

/-- The redesigned Target carrier: its norm and state moduli are both
primitive-derived. -/
def coupledCarrierTLip : Set SBCF :=
  targetPrimitiveValLipCarrier
    lowDeltaParams lowDeltaTargetStageBound coupledTargetLipK

/-- Optional exact-rational check of the objective chord coefficient. -/
theorem coupledSigmaStateObjectiveDiffK_eq :
    coupledSigmaStateObjectiveDiffK = 14320323 / 6400000 := by
  rw [coupledSigmaStateObjectiveDiffK, lowDeltaSenderCarrierLip_eq]
  norm_num [lowDeltaParams_β_S, lowDeltaParams_δ]

/-- Optional exact-rational check of the retained Sender curvature. -/
theorem coupledSenderObjectiveCurvature_eq :
    coupledSenderObjectiveCurvature = 37877 / 32000 := by
  rw [coupledSenderObjectiveCurvature, lowDeltaSenderCarrierNorm_eq]
  norm_num [lowDeltaParams_β_S, lowDeltaParams_δ]

/-- Optional exact-rational check of the derived Sender-response modulus. -/
theorem coupledSigmaStateK_eq :
    coupledSigmaStateK = 14320323 / 3787700 := by
  rw [coupledSigmaStateK, coupledSenderObjectiveCurvature_eq,
    coupledSigmaStateObjectiveDiffK_eq]
  norm_num

/-- Optional exact-rational check of the derived transition modulus. -/
theorem coupledTargetTransitionStateLip_eq :
    coupledTargetTransitionStateLip =
      99 / 100 + (1 / 100) * (14320323 / 3787700) := by
  rw [coupledTargetTransitionStateLip, coupledSigmaStateK_eq]
  norm_num [lowDeltaParams_δ]

/-- Optional exact-rational check of the Target value modulus. -/
theorem coupledTargetLipK_eq :
    coupledTargetLipK = 25683423000 / 283976393 := by
  rw [coupledTargetLipK, coupledSigmaStateK_eq,
    coupledTargetTransitionStateLip_eq]
  norm_num [coupledTargetStageStateLip, lowDeltaParams_β_T]

/-- Optional exact-rational check of the Sender policy budget. -/
theorem coupledAlphaStateBudget_eq :
    coupledAlphaStateBudget = 4675077 / 640000 := by
  rw [coupledAlphaStateBudget, lowDeltaSenderCarrierLip_eq]
  norm_num [lowDeltaSenderStageStateLip, lowDeltaParams_β_S,
    lowDeltaParams_δ]

theorem coupledSigmaStateK_pos : 0 < coupledSigmaStateK := by
  rw [coupledSigmaStateK_eq]
  norm_num

theorem coupledTargetLipK_pos : 0 < coupledTargetLipK := by
  rw [coupledTargetLipK_eq]
  norm_num

theorem coupledAlphaStateBudget_pos : 0 < coupledAlphaStateBudget := by
  rw [coupledAlphaStateBudget_eq]
  norm_num

theorem coupledCarrierTLip_isClosed : IsClosed coupledCarrierTLip := by
  simpa only [coupledCarrierTLip, targetPrimitiveValLipCarrier,
    lowDeltaTargetCarrierNorm] using
    (valLipBall_isClosed lowDeltaTargetCarrierNorm coupledTargetLipK)

theorem coupledCarrierTLip_nonempty : coupledCarrierTLip.Nonempty := by
  simpa only [coupledCarrierTLip, targetPrimitiveValLipCarrier,
    lowDeltaTargetCarrierNorm] using
    (valLipBall_nonempty
      (lowDeltaParams.carrierMinNormT_nonneg
        (by norm_num [lowDeltaTargetStageBound]))
      coupledTargetLipK_pos.le)

theorem zero_mem_coupledCarrierTLip :
    (0 : SBCF) ∈ coupledCarrierTLip := by
  simpa only [coupledCarrierTLip, targetPrimitiveValLipCarrier,
    lowDeltaTargetCarrierNorm] using
    (zero_mem_valLipBall
      (lowDeltaParams.carrierMinNormT_nonneg
        (by norm_num [lowDeltaTargetStageBound]))
      coupledTargetLipK_pos.le)

/-- Exact Target self-map denominator after feeding the Sender response
state modulus through the affine transition. -/
theorem coupledTargetLip_denominator :
    1 - lowDeltaParams.β_T * coupledTargetTransitionStateLip
      = 283976393 / 3787700000 := by
  rw [coupledTargetTransitionStateLip_eq]
  norm_num [lowDeltaParams_β_T]

/-- The chosen Target modulus exactly exhausts the Target self-map budget. -/
theorem coupledTargetLipK_balance :
    coupledTargetStageStateLip + coupledSigmaStateK
        + lowDeltaParams.β_T * coupledTargetLipK
          * coupledTargetTransitionStateLip
      = coupledTargetLipK := by
  rw [coupledTargetLipK_eq]
  rw [coupledTargetTransitionStateLip, coupledSigmaStateK_eq]
  norm_num [coupledTargetStageStateLip, lowDeltaParams_δ,
    lowDeltaParams_β_T]

/-- Optional expanded witness check of the Target balance identity. -/
theorem coupledTargetLipK_balance_witness :
    3 + coupledSigmaStateK
        + (9 / 10 : ℝ) * coupledTargetLipK
          * (99 / 100 + (1 / 100) * coupledSigmaStateK)
      = coupledTargetLipK := by
  have h := coupledTargetLipK_balance
  norm_num [coupledTargetStageStateLip, lowDeltaParams_β_T,
    coupledTargetTransitionStateLip, lowDeltaParams_δ] at h ⊢
  exact h

/-- The Target-policy budget exactly fills the existing Sender state
modulus. -/
theorem coupledSenderLip_margin :
    lowDeltaSenderStageStateLip + coupledAlphaStateBudget
        + lowDeltaParams.β_S * lowDeltaSenderCarrierLip
          * (1 - lowDeltaParams.δ)
      = lowDeltaSenderCarrierLip := by
  simp only [coupledAlphaStateBudget]
  ring

/-- Optional expanded witness check of the Sender carrier balance identity. -/
theorem coupledSenderLip_margin_witness :
    7 / 4 + coupledAlphaStateBudget
        + (1 / 2 : ℝ) * (57377 / 3200) * (99 / 100)
      = 57377 / 3200 := by
  rw [coupledAlphaStateBudget_eq]
  norm_num

/-! ## Equilibrium Sender response: state modulus -/

/-- For every `K_S`-Lipschitz Sender value, the equilibrium dynamic Sender
response is state-Lipschitz at every fixed Target action with the exact
redesign constant.  Witness-specific (Rule 22): the low-δ economy, not a
general-`F` statement.  Only the Lipschitz half of Sender-carrier membership is
assumed; the norm half is dropped. -/
theorem coupled_sigmaDynTop_state_lipschitz
    (V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (x y : ℝ) (hx : x ∈ Sanctions.S) (hy : y ∈ Sanctions.S)
    (a : ℝ) :
    |lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear V_S) x a
      - lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear V_S) y a|
      ≤ coupledSigmaStateK * |x - y| := by
  let f : ℝ → ℝ := fun s =>
    lowDeltaShocked.toParams.U_S x a s
      + lowDeltaShocked.toParams.β_S
        * (lowDeltaShocked.smear V_S)
          (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))
  let g : ℝ → ℝ := fun s =>
    lowDeltaShocked.toParams.U_S y a s
      + lowDeltaShocked.toParams.β_S
        * (lowDeltaShocked.smear V_S)
          (Sanctions.clipS' (lowDeltaShocked.toParams.F y s))
  let σx :=
    lowDeltaShocked.toParams.σ_dyn_top
      (lowDeltaShocked.smear V_S) x a
  let σy :=
    lowDeltaShocked.toParams.σ_dyn_top
      (lowDeltaShocked.smear V_S) y a
  have hσx_mem : σx ∈ Sanctions.I :=
    lowDeltaShocked.toParams.σ_dyn_top_mem_I
      (lowDeltaShocked.smear V_S) x a
  have hσy_mem : σy ∈ Sanctions.I :=
    lowDeltaShocked.toParams.σ_dyn_top_mem_I
      (lowDeltaShocked.smear V_S) y a
  have hfmax : ∀ z ∈ Sanctions.I, f z ≤ f σx :=
    fun z hz =>
      lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
        (lowDeltaShocked.smear V_S) x a hz
  have hgmax : ∀ z ∈ Sanctions.I, g z ≤ g σy :=
    fun z hz =>
      lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
        (lowDeltaShocked.smear V_S) y a hz
  let A : ℝ :=
    (lowDeltaShocked.toParams.U_S x a σx
        - lowDeltaShocked.toParams.U_S y a σx)
      - (lowDeltaShocked.toParams.U_S x a σy
        - lowDeltaShocked.toParams.U_S y a σy)
  let B : ℝ :=
    ((lowDeltaShocked.smear V_S)
        (Sanctions.clipS' (lowDeltaShocked.toParams.F x σx))
      - (lowDeltaShocked.smear V_S)
        (Sanctions.clipS' (lowDeltaShocked.toParams.F y σx)))
      - ((lowDeltaShocked.smear V_S)
          (Sanctions.clipS' (lowDeltaShocked.toParams.F x σy))
        - (lowDeltaShocked.smear V_S)
          (Sanctions.clipS' (lowDeltaShocked.toParams.F y σy)))
  have hstage :
      |A| ≤ (27 / 20) * |x - y| * |σx - σy| := by
    dsimp only [A]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S]
    have heq :
        (mwU_S x a σx - mwU_S y a σx)
            - (mwU_S x a σy - mwU_S y a σy)
          = (27 / 20) * (x - y) * (σx - σy) := by
      simp only [mwU_S]
      ring
    rw [heq, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 20)]
  have hFxx :
      lowDeltaShocked.toParams.F x σx ∈ Sanctions.S := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F]
    exact Sanctions.AbstractGame.affineF_mem
      (δ := (1 / 100 : ℝ))
      (by constructor <;> norm_num) x σx hx hσx_mem
  have hFyx :
      lowDeltaShocked.toParams.F y σx ∈ Sanctions.S := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F]
    exact Sanctions.AbstractGame.affineF_mem
      (δ := (1 / 100 : ℝ))
      (by constructor <;> norm_num) y σx hy hσx_mem
  have hFxy :
      lowDeltaShocked.toParams.F x σy ∈ Sanctions.S := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F]
    exact Sanctions.AbstractGame.affineF_mem
      (δ := (1 / 100 : ℝ))
      (by constructor <;> norm_num) x σy hx hσy_mem
  have hFyy :
      lowDeltaShocked.toParams.F y σy ∈ Sanctions.S := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F]
    exact Sanctions.AbstractGame.affineF_mem
      (δ := (1 / 100 : ℝ))
      (by constructor <;> norm_num) y σy hy hσy_mem
  let φ : ℝ → ℝ :=
    Sanctions.movAvgReal (1 / 10) V_S
  have hφ : ∀ z, DifferentiableAt ℝ φ z := by
    intro z
    exact
      (Sanctions.movAvgReal_hasDerivAt
        lowDeltaH_pos V_S z).differentiableAt
  have hφ' :
      ∀ u v, |deriv φ u - deriv φ v|
        ≤ ((57377 / 3200 : ℝ) / (1 / 10)) * |u - v| := by
    intro u v
    have hV_S_lip :
        ValueLipschitzWith V_S (57377 / 3200) := by
      simpa only [lowDeltaSenderCarrierLip_eq] using hV_S
    exact
      Sanctions.movAvgReal_deriv_lipschitz_of_valueLipschitz
        lowDeltaH_pos V_S (by norm_num) hV_S_lip u v
  have hrect :=
    Sanctions.affine_mixed_rectangle_of_deriv_lipschitz
      (φ := φ) (K := (57377 / 3200 : ℝ) / (1 / 10))
      (c := 1 - (1 / 100 : ℝ)) (d := 1 / 100)
      (x := x) (y := y) (s := σx) (t := σy) hφ hφ'
  have hrect' :
      |(φ ((1 - (1 / 100 : ℝ)) * x + (1 / 100) * σx)
          - φ ((1 - (1 / 100 : ℝ)) * y + (1 / 100) * σx))
        - (φ ((1 - (1 / 100 : ℝ)) * x + (1 / 100) * σy)
          - φ ((1 - (1 / 100 : ℝ)) * y + (1 / 100) * σy))|
        ≤ (5680323 / 3200000) * |x - y| * |σx - σy| := by
    norm_num at hrect ⊢
    exact hrect
  have hcont :
      |B| ≤ (5680323 / 3200000) * |x - y| * |σx - σy| := by
    dsimp only [B]
    rw [lowDeltaShocked_smear]
    simp only [Sanctions.movAvgBCF_apply]
    rw [Sanctions.clipS'_val_eq_of_mem hFxx,
      Sanctions.clipS'_val_eq_of_mem hFyx,
      Sanctions.clipS'_val_eq_of_mem hFxy,
      Sanctions.clipS'_val_eq_of_mem hFyy]
    simpa only [lowDeltaShocked_toParams, lowDeltaParams_F,
      Sanctions.AbstractGame.affineF, φ] using hrect'
  have hcont_scaled :
      |(1 / 2 : ℝ) * B|
        ≤ (5680323 / 6400000) * |x - y| * |σx - σy| := by
    rw [abs_mul, abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      (1 / 2 : ℝ) * |B|
          ≤ (1 / 2)
              * ((5680323 / 3200000) * |x - y| * |σx - σy|) :=
        mul_le_mul_of_nonneg_left hcont (by norm_num)
      _ = (5680323 / 6400000) * |x - y| * |σx - σy| := by
        ring
  have hdecomp :
      (f σx - g σx) - (f σy - g σy)
        = A + (1 / 2) * B := by
    dsimp only [f, g, A, B]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_β_S]
    ring
  have hdiff :
      |(f σx - g σx) - (f σy - g σy)|
        ≤ ((14320323 / 6400000) * |x - y|)
          * |σx - σy| := by
    rw [hdecomp]
    calc
      |A + (1 / 2) * B| ≤ |A| + |(1 / 2) * B| :=
        abs_add_le _ _
      _ ≤ (27 / 20) * |x - y| * |σx - σy|
          + (5680323 / 6400000) * |x - y| * |σx - σy| :=
        add_le_add hstage hcont_scaled
      _ = ((14320323 / 6400000) * |x - y|)
          * |σx - σy| := by
        ring
  have hL0 :
      0 ≤ (14320323 / 6400000 : ℝ) * |x - y| := by
    positivity
  have hcore :=
    Sanctions.argmax_lipschitz_of_strongConcave_lipschitzDiff
      hL0 (convex_Icc 0 1)
      (coupled_sender_strongConcave V_S hV_S x hx a)
      (coupled_sender_strongConcave V_S hV_S y hy a)
      hσx_mem hσy_mem hfmax hgmax hdiff
  have hgen :
      |σx - σy| ≤
        (2 / (37877 / 32000 : ℝ))
          * ((14320323 / 6400000) * |x - y|) := by
    rw [div_mul_eq_mul_div,
      le_div_iff₀
        (show (0 : ℝ) < 37877 / 32000 by norm_num)]
    nlinarith [hcore]
  dsimp only [σx, σy] at hgen ⊢
  rw [coupledSigmaStateK_eq]
  convert hgen using 1
  · ring

/-! ## Target carrier invariance -/

/-- The equilibrium-derived greatest Sender response, extended continuously
off the physical state interval by clipping the state first. -/
noncomputable def coupledSigmaClamped
    (V_S : SBCF) (x a : ℝ) : ℝ :=
  lowDeltaShocked.toParams.σ_dyn_top_clamped
    (lowDeltaShocked.smear V_S) x a

theorem coupledSigmaClamped_mem
    (V_S : SBCF) (x a : ℝ) :
    coupledSigmaClamped V_S x a ∈ Sanctions.I := by
  unfold coupledSigmaClamped
    AbstractGame.Params.σ_dyn_top_clamped
  exact lowDeltaShocked.toParams.σ_dyn_top_mem_I
    (lowDeltaShocked.smear V_S) _ _

/-- The clamped equilibrium Sender response is jointly continuous for every
`K_S`-Lipschitz Sender value.  Witness-specific (Rule 22).  Only the Lipschitz
half of Sender-carrier membership is assumed; the norm half is dropped. -/
theorem coupledSigmaClamped_continuous
    (V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip) :
    Continuous (fun xa : ℝ × ℝ =>
      coupledSigmaClamped V_S xa.1 xa.2) :=
  coupled_sigmaDynTop_clamped_continuous_of_lipschitz V_S hV_S

/-- The moving-average shock does not increase the sup norm. -/
theorem lowDelta_smear_norm_le (V : SBCF) :
    ‖lowDeltaShocked.smear V‖ ≤ ‖V‖ := by
  calc
    ‖lowDeltaShocked.smear V‖
        = dist (lowDeltaShocked.smear V)
            (lowDeltaShocked.smear (0 : SBCF)) := by
          rw [lowDelta_smear_zero, dist_zero_right]
    _ ≤ dist V (0 : SBCF) :=
      lowDeltaShocked.smear_nonexpansive V 0
    _ = ‖V‖ := by
      simpa only using (dist_zero_right V)

/-- The Target stage payoff is bounded by `2` on the unit cube. -/
theorem lowDelta_UT_cube_bound
    (x : ℝ) (hx : x ∈ Sanctions.I)
    (a : ℝ) (ha : a ∈ Sanctions.I)
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |lowDeltaShocked.toParams.U_T x a s| ≤ 2 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases ha with ⟨ha0, ha1⟩
  rcases hs with ⟨hs0, hs1⟩
  rw [lowDeltaShocked_toParams, lowDeltaParams_U_T]
  unfold mwU_T
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg a, mul_nonneg hx0 ha0,
      mul_nonneg hs0 (sub_nonneg.mpr (by nlinarith))]

/-- Holding the sanction fixed, the Target stage payoff varies by at most
three times the inherited-state change on the unit cube. -/
theorem lowDelta_UT_state_lipschitz
    (x y : ℝ)
    (a : ℝ) (ha : a ∈ Sanctions.I)
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |lowDeltaShocked.toParams.U_T y a s
      - lowDeltaShocked.toParams.U_T x a s|
      ≤ 3 * |y - x| := by
  have hcoef0 : 0 ≤ 2 * a + s := by
    nlinarith [ha.1, hs.1]
  have hcoef3 : 2 * a + s ≤ 3 := by
    nlinarith [ha.2, hs.2]
  have heq :
      lowDeltaShocked.toParams.U_T y a s
          - lowDeltaShocked.toParams.U_T x a s
        = (2 * a + s) * (y - x) := by
    simp only [lowDeltaShocked_toParams,
      lowDeltaParams_U_T, mwU_T]
    ring
  rw [heq, abs_mul, abs_of_nonneg hcoef0]
  exact mul_le_mul_of_nonneg_right hcoef3 (abs_nonneg _)

/-- Holding inherited state and Target action fixed, the Target stage payoff
is one-Lipschitz in the Sender sanction on the unit cube. -/
theorem lowDelta_UT_sanction_lipschitz
    (x : ℝ) (hx : x ∈ Sanctions.I)
    (a : ℝ) (ha : a ∈ Sanctions.I)
    (s t : ℝ) :
    |lowDeltaShocked.toParams.U_T x a t
      - lowDeltaShocked.toParams.U_T x a s|
      ≤ |t - s| := by
  have hcoef : |x + a / 2 - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hx.1, hx.2, ha.1, ha.2]
  have heq :
      lowDeltaShocked.toParams.U_T x a t
          - lowDeltaShocked.toParams.U_T x a s
        = (t - s) * (x + a / 2 - 1 / 2) := by
    simp only [lowDeltaShocked_toParams,
      lowDeltaParams_U_T, mwU_T]
    ring
  rw [heq, abs_mul]
  nlinarith [
    mul_le_mul_of_nonneg_left hcoef (abs_nonneg (t - s))]

/-- Under a `Kσ` state modulus for a feasible response, the low-adjustment
transition has state modulus `99/100 + Kσ/100`. -/
theorem lowDelta_F_response_state_lipschitz
    (ρ : ℝ → ℝ → ℝ) {Kσ : ℝ}
    (hρ : ∀ x y : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      |ρ y.val a - ρ x.val a| ≤ Kσ * dist x y)
    (x y : ↥(Sanctions.S : Set ℝ))
    (a : ℝ) (ha : a ∈ Sanctions.I) :
    |lowDeltaShocked.toParams.F y.val (ρ y.val a)
      - lowDeltaShocked.toParams.F x.val (ρ x.val a)|
      ≤ (99 / 100 + (1 / 100) * Kσ) * dist x y := by
  have heq :
      lowDeltaShocked.toParams.F y.val (ρ y.val a)
          - lowDeltaShocked.toParams.F x.val (ρ x.val a)
        = (99 / 100 : ℝ) * (y.val - x.val)
          + (1 / 100 : ℝ) * (ρ y.val a - ρ x.val a) := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    ring
  rw [heq]
  calc
    |(99 / 100 : ℝ) * (y.val - x.val)
        + (1 / 100 : ℝ) * (ρ y.val a - ρ x.val a)|
        ≤ |(99 / 100 : ℝ) * (y.val - x.val)|
          + |(1 / 100 : ℝ) * (ρ y.val a - ρ x.val a)| :=
      abs_add_le _ _
    _ = (99 / 100 : ℝ) * |y.val - x.val|
        + (1 / 100 : ℝ) * |ρ y.val a - ρ x.val a| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ (99 / 100 : ℝ) * dist x y
        + (1 / 100 : ℝ) * (Kσ * dist x y) := by
      apply add_le_add
      · rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      · exact
          mul_le_mul_of_nonneg_left (hρ x y a ha) (by norm_num)
    _ = (99 / 100 + (1 / 100) * Kσ) * dist x y := by
      ring

/-- The realized Target integrand has the redesigned state modulus whenever
the equilibrium Sender selector has `coupledSigmaStateK` as a state
modulus. -/
theorem coupled_target_integrand_state_lipschitz
    (V_T : SBCF) (hV_T : V_T ∈ coupledCarrierTLip)
    (V_S : SBCF)
    (hσstate : ∀ x y : ↥(Sanctions.S : Set ℝ),
      ∀ a ∈ Sanctions.I,
      |coupledSigmaClamped V_S y.val a
        - coupledSigmaClamped V_S x.val a|
        ≤ coupledSigmaStateK * dist x y)
    (x y : ↥(Sanctions.S : Set ℝ))
    (a : ℝ) (ha : a ∈ Sanctions.I) :
    |lowDeltaShocked.toParams.targetDynIntegrand
        (coupledSigmaClamped V_S)
        (lowDeltaShocked.smear V_T) y.val a
      - lowDeltaShocked.toParams.targetDynIntegrand
        (coupledSigmaClamped V_S)
        (lowDeltaShocked.smear V_T) x.val a|
      ≤ coupledTargetLipK * dist x y := by
  have hx : x.val ∈ Sanctions.I :=
    ⟨x.property.1, x.property.2⟩
  have hσy :=
    coupledSigmaClamped_mem V_S y.val a
  have hstage_x :=
    lowDelta_UT_state_lipschitz x.val y.val a ha
      (coupledSigmaClamped V_S y.val a) hσy
  have hstage_s :=
    lowDelta_UT_sanction_lipschitz x.val hx a ha
      (coupledSigmaClamped V_S x.val a)
      (coupledSigmaClamped V_S y.val a)
  have hstage :
      |lowDeltaShocked.toParams.U_T y.val a
          (coupledSigmaClamped V_S y.val a)
        - lowDeltaShocked.toParams.U_T x.val a
          (coupledSigmaClamped V_S x.val a)|
        ≤ (3 + coupledSigmaStateK) * dist x y := by
    have heq :
        lowDeltaShocked.toParams.U_T y.val a
              (coupledSigmaClamped V_S y.val a)
            - lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S x.val a)
          = (lowDeltaShocked.toParams.U_T y.val a
              (coupledSigmaClamped V_S y.val a)
            - lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S y.val a))
            + (lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S y.val a)
            - lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S x.val a)) := by
      ring
    rw [heq]
    calc
      |_ + _| ≤
          |lowDeltaShocked.toParams.U_T y.val a
              (coupledSigmaClamped V_S y.val a)
            - lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S y.val a)|
          + |lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S y.val a)
            - lowDeltaShocked.toParams.U_T x.val a
              (coupledSigmaClamped V_S x.val a)| :=
        abs_add_le _ _
      _ ≤ 3 * dist x y
          + coupledSigmaStateK * dist x y := by
        apply add_le_add
        · simpa [Subtype.dist_eq, Real.dist_eq,
            abs_sub_comm] using hstage_x
        · exact hstage_s.trans (hσstate x y a ha)
      _ = (3 + coupledSigmaStateK) * dist x y := by
        ring
  have hsmear :
      ValueLipschitzWith
        (lowDeltaShocked.smear V_T) coupledTargetLipK := by
    intro z₁ z₂
    rw [lowDeltaShocked_smear]
    exact Sanctions.movAvgBCF_valueLipschitz
      lowDeltaH_pos V_T coupledTargetLipK_pos.le hV_T.2 z₁ z₂
  have hF :=
    lowDelta_F_response_state_lipschitz
      (coupledSigmaClamped V_S) hσstate x y a ha
  have hclip :
      dist
          (Sanctions.clipS'
            (lowDeltaShocked.toParams.F x.val
              (coupledSigmaClamped V_S x.val a)))
          (Sanctions.clipS'
            (lowDeltaShocked.toParams.F y.val
              (coupledSigmaClamped V_S y.val a)))
        ≤ (99 / 100 + (1 / 100) * coupledSigmaStateK)
          * dist x y := by
    have hc :=
      Sanctions.clipS'_lipschitz_dist
        (lowDeltaShocked.toParams.F y.val
          (coupledSigmaClamped V_S y.val a))
        (lowDeltaShocked.toParams.F x.val
          (coupledSigmaClamped V_S x.val a))
    rw [dist_comm] at hc
    exact hc.trans hF
  have hcontinuation :
      |lowDeltaShocked.smear V_T
          (Sanctions.clipS'
            (lowDeltaShocked.toParams.F y.val
              (coupledSigmaClamped V_S y.val a)))
        - lowDeltaShocked.smear V_T
          (Sanctions.clipS'
            (lowDeltaShocked.toParams.F x.val
              (coupledSigmaClamped V_S x.val a)))|
        ≤ coupledTargetLipK
          * ((99 / 100 + (1 / 100) * coupledSigmaStateK)
            * dist x y) :=
    (hsmear _ _).trans
      (mul_le_mul_of_nonneg_left hclip coupledTargetLipK_pos.le)
  simp only [AbstractGame.Params.targetDynIntegrand]
  have heq :
      (lowDeltaShocked.toParams.U_T y.val a
            (coupledSigmaClamped V_S y.val a)
          + lowDeltaShocked.toParams.β_T
            * lowDeltaShocked.smear V_T
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F y.val
                  (coupledSigmaClamped V_S y.val a))))
        - (lowDeltaShocked.toParams.U_T x.val a
            (coupledSigmaClamped V_S x.val a)
          + lowDeltaShocked.toParams.β_T
            * lowDeltaShocked.smear V_T
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F x.val
                  (coupledSigmaClamped V_S x.val a))))
        = (lowDeltaShocked.toParams.U_T y.val a
            (coupledSigmaClamped V_S y.val a)
          - lowDeltaShocked.toParams.U_T x.val a
            (coupledSigmaClamped V_S x.val a))
          + lowDeltaShocked.toParams.β_T
            * (lowDeltaShocked.smear V_T
                (Sanctions.clipS'
                  (lowDeltaShocked.toParams.F y.val
                    (coupledSigmaClamped V_S y.val a)))
              - lowDeltaShocked.smear V_T
                (Sanctions.clipS'
                  (lowDeltaShocked.toParams.F x.val
                    (coupledSigmaClamped V_S x.val a)))) := by
    ring
  rw [heq]
  calc
    |_ + _| ≤
        |lowDeltaShocked.toParams.U_T y.val a
            (coupledSigmaClamped V_S y.val a)
          - lowDeltaShocked.toParams.U_T x.val a
            (coupledSigmaClamped V_S x.val a)|
        + |lowDeltaShocked.toParams.β_T
          * (lowDeltaShocked.smear V_T
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F y.val
                  (coupledSigmaClamped V_S y.val a)))
            - lowDeltaShocked.smear V_T
              (Sanctions.clipS'
                (lowDeltaShocked.toParams.F x.val
                  (coupledSigmaClamped V_S x.val a))))| :=
      abs_add_le _ _
    _ ≤ (3 + coupledSigmaStateK) * dist x y
        + (9 / 10 : ℝ)
          * (coupledTargetLipK
            * ((99 / 100 + (1 / 100) * coupledSigmaStateK)
              * dist x y)) := by
      apply add_le_add hstage
      rw [abs_mul,
        abs_of_nonneg lowDeltaShocked.toParams.β_T_mem.1,
        lowDeltaShocked_toParams, lowDeltaParams_β_T]
      exact
        mul_le_mul_of_nonneg_left hcontinuation (by norm_num)
    _ = (3 + coupledSigmaStateK
        + (9 / 10 : ℝ) * coupledTargetLipK
          * (99 / 100 + (1 / 100) * coupledSigmaStateK))
        * dist x y := by
      ring
    _ = coupledTargetLipK * dist x y := by
      rw [coupledTargetLipK_balance_witness]

/-- Conditional Target-row invariance at the redesigned carrier, stated with
the selector state modulus as an explicit theorem input. -/
theorem coupled_target_Bellman_mem_lip_carrier_of_selector_state_lipschitz
    (V_T : SBCF) (hV_T : V_T ∈ coupledCarrierTLip)
    (V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS)
    (hσstate : ∀ x y : ↥(Sanctions.S : Set ℝ),
      ∀ a ∈ Sanctions.I,
      |coupledSigmaClamped V_S y.val a
        - coupledSigmaClamped V_S x.val a|
        ≤ coupledSigmaStateK * dist x y) :
    lowDeltaShocked.targetDynBCF_shock
      (coupledSigmaClamped V_S)
      (coupledSigmaClamped_continuous V_S hV_S.2) V_T
        ∈ coupledCarrierTLip := by
  have h :=
    Sanctions.AbstractGame.movAvg_targetDynBCF_shock_mem_targetPrimitiveValLipCarrier_of_integrand
        lowDeltaParams lowDeltaH_pos
        (coupledSigmaClamped V_S)
        (coupledSigmaClamped_continuous V_S hV_S.2)
        (fun x _hx a _ha => coupledSigmaClamped_mem V_S x a)
        V_T
        (by norm_num [lowDeltaTargetStageBound])
        hV_T
        (by
          simpa only [lowDeltaShocked_toParams, lowDeltaTargetStageBound] using
            lowDelta_UT_cube_bound)
        (coupled_target_integrand_state_lipschitz
          V_T hV_T V_S hσstate)
  simpa only [lowDeltaShocked, coupledCarrierTLip] using h

/-- **Unconditional Target invariance on the redesigned carrier.** The actual
equilibrium Sender response supplies the state modulus required by the
conditional self-map theorem. -/
theorem coupled_target_Bellman_mem_lip_carrier
    (V_T : SBCF) (hV_T : V_T ∈ coupledCarrierTLip)
    (V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS) :
    lowDeltaShocked.targetDynBCF_shock
      (coupledSigmaClamped V_S)
      (coupledSigmaClamped_continuous V_S hV_S.2) V_T
        ∈ coupledCarrierTLip := by
  apply
    coupled_target_Bellman_mem_lip_carrier_of_selector_state_lipschitz
      V_T hV_T V_S hV_S
  intro x y a _ha
  change
    |lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear V_S) y.val a
      - lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear V_S) x.val a|
      ≤ coupledSigmaStateK * dist x y
  rw [
    lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
      (lowDeltaShocked.smear V_S) y.property,
    lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
      (lowDeltaShocked.smear V_S) x.property]
  simpa [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using
    coupled_sigmaDynTop_state_lipschitz
      V_S hV_S.2 y.val x.val y.property x.property a

/-! ## Conditional Sender carrier invariance -/

/-- The Sender stage payoff is bounded by its exact cube radius
`523 / 320`. -/
theorem lowDelta_US_cube_bound :
    ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |lowDeltaParams.U_S x a s| ≤ 523 / 320 := by
  intro x hx a ha s hs
  have hsquad : s ^ 2 ≤ s := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hA0 : 0 ≤ (27 / 20 : ℝ) * s + 2 / 5 := by
    nlinarith [hs.1]
  have hB0 : 0 ≤ (1 : ℝ) - s / 2 := by
    nlinarith [hs.2]
  have hAx0 :
      0 ≤ ((27 / 20 : ℝ) * s + 2 / 5) * x :=
    mul_nonneg hA0 hx.1
  have hBa0 :
      0 ≤ ((1 : ℝ) - s / 2) * a :=
    mul_nonneg hB0 ha.1
  have hAx1 :
      ((27 / 20 : ℝ) * s + 2 / 5) * x
        ≤ (27 / 20 : ℝ) * s + 2 / 5 :=
    mul_le_of_le_one_right hA0 hx.2
  have hBa1 :
      ((1 : ℝ) - s / 2) * a
        ≤ (1 : ℝ) - s / 2 :=
    mul_le_of_le_one_right hB0 ha.2
  have hdecomp :
      lowDeltaParams.U_S x a s
        = (-(3 / 5 : ℝ) * s ^ 2 - (1 / 10) * s)
          + ((27 / 20) * s + 2 / 5) * x
          + (1 - s / 2) * a := by
    simp only [lowDeltaParams_U_S]
    unfold mwU_S
    ring
  rw [hdecomp, abs_le]
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (s - 5 / 8)]

/-- A state-Lipschitz bound on a Target policy forces its modulus to be
nonnegative: at the states `0` and `1` it reads `0 ≤ |α 1 − α 0| ≤ Lα`.  General
in `F` (it involves no transition).  This is why the policy-Lipschitz theorems
below carry no separate `0 ≤ Lα` premise. -/
theorem lowDelta_policy_lip_nonneg
    {α : ℝ → ℝ} {Lα : ℝ}
    (hα_lip : ∀ x₁ x₂ : ℝ,
      |α x₂ - α x₁| ≤ Lα * |x₂ - x₁|) :
    0 ≤ Lα := by
  have h := hα_lip 0 1
  norm_num at h
  exact (abs_nonneg _).trans h

/-- Composing the Sender stage payoff with an `Lα`-Lipschitz Target policy
gives state modulus `7/4 + Lα`.  Witness-specific (Rule 22): the low-δ Sender
stage payoff.  The former premise `0 ≤ Lα` is dropped: it follows from the
Lipschitz bound itself, evaluated at the states `0` and `1`. -/
theorem lowDelta_US_composed_state_lipschitz
    {α : ℝ → ℝ} {Lα : ℝ}
    (hα_lip : ∀ x₁ x₂ : ℝ,
      |α x₂ - α x₁| ≤ Lα * |x₂ - x₁|) :
    ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |lowDeltaParams.U_S x₂ (α x₂) s
        - lowDeltaParams.U_S x₁ (α x₁) s|
        ≤ (7 / 4 + Lα) * |x₂ - x₁| := by
  have hLα : 0 ≤ Lα := lowDelta_policy_lip_nonneg hα_lip
  intro x₁ x₂ s hs
  have hA0 : 0 ≤ (27 / 20 : ℝ) * s + 2 / 5 := by
    nlinarith [hs.1]
  have hA1 : (27 / 20 : ℝ) * s + 2 / 5 ≤ 7 / 4 := by
    nlinarith [hs.2]
  have hB0 : 0 ≤ (1 : ℝ) - s / 2 := by
    nlinarith [hs.2]
  have hB1 : (1 : ℝ) - s / 2 ≤ 1 := by
    nlinarith [hs.1]
  have hdecomp :
      lowDeltaParams.U_S x₂ (α x₂) s
          - lowDeltaParams.U_S x₁ (α x₁) s
        = ((27 / 20 : ℝ) * s + 2 / 5) * (x₂ - x₁)
          + (1 - s / 2) * (α x₂ - α x₁) := by
    simp only [lowDeltaParams_U_S]
    unfold mwU_S
    ring
  rw [hdecomp]
  calc
    |((27 / 20 : ℝ) * s + 2 / 5) * (x₂ - x₁)
        + (1 - s / 2) * (α x₂ - α x₁)|
        ≤ |((27 / 20 : ℝ) * s + 2 / 5) * (x₂ - x₁)|
          + |(1 - s / 2) * (α x₂ - α x₁)| := by
      simpa only [Real.norm_eq_abs] using
        norm_add_le
          (((27 / 20 : ℝ) * s + 2 / 5) * (x₂ - x₁))
          ((1 - s / 2) * (α x₂ - α x₁))
    _ = ((27 / 20 : ℝ) * s + 2 / 5) * |x₂ - x₁|
        + (1 - s / 2) * |α x₂ - α x₁| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA0,
        abs_of_nonneg hB0]
    _ ≤ (7 / 4) * |x₂ - x₁|
        + 1 * (Lα * |x₂ - x₁|) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hA1 (abs_nonneg _)
      · calc
          (1 - s / 2) * |α x₂ - α x₁|
              ≤ (1 - s / 2) * (Lα * |x₂ - x₁|) :=
            mul_le_mul_of_nonneg_left
              (hα_lip x₁ x₂) hB0
          _ ≤ 1 * (Lα * |x₂ - x₁|) :=
            mul_le_mul_of_nonneg_right hB1
              (mul_nonneg hLα (abs_nonneg _))
    _ = (7 / 4 + Lα) * |x₂ - x₁| := by
      ring

/-- The low-adjustment transition is `99/100`-Lipschitz in inherited state
at a fixed sanction. -/
theorem lowDelta_F_state_lipschitz :
    ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |lowDeltaParams.F x₂ s - lowDeltaParams.F x₁ s|
        ≤ (99 / 100) * |x₂ - x₁| := by
  intro x₁ x₂ s _hs
  simp only [lowDeltaParams_F, AbstractGame.affineF]
  have heq :
      (1 - (1 / 100 : ℝ)) * x₂ + (1 / 100) * s
          - ((1 - (1 / 100)) * x₁ + (1 / 100) * s)
        = (99 / 100) * (x₂ - x₁) := by
    ring
  rw [heq, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 100)]

/-- The canonical Sender carrier indexed by the policy modulus derived from
objective geometry.  Both carrier radii are closed forms of model primitives;
no independently calibrated Sender radius appears. -/
def coupledSenderPrimitiveCarrier (Lα : ℝ) : Set SBCF :=
  senderPrimitiveValLipCarrier lowDeltaParams
    lowDeltaSenderStageBound
    (lowDeltaSenderStageStateLip + Lα)
    (1 - lowDeltaParams.δ)

/-- **Primitive-derived Sender invariance.** Once objective geometry supplies
the realised Target policy modulus `Lα`, the Sender carrier indexed by that
modulus is invariant.  There is no numerical policy-budget hypothesis.
Witness-specific (Rule 22).  The former premise `0 ≤ Lα` is dropped: it is
derived from `hα_lip` (`lowDelta_policy_lip_nonneg`). -/
theorem coupled_sender_Bellman_mem_primitive_carrier
    (α : ℝ → ℝ) (hα : Continuous α)
    (hα_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    {Lα : ℝ}
    (hα_lip : ∀ x₁ x₂ : ℝ,
      |α x₂ - α x₁| ≤ Lα * |x₂ - x₁|)
    (V_S : SBCF) (hV_S : V_S ∈ coupledSenderPrimitiveCarrier Lα) :
    lowDeltaShocked.bellmanS_shock α hα V_S
      ∈ coupledSenderPrimitiveCarrier Lα := by
  have hLα : 0 ≤ Lα := lowDelta_policy_lip_nonneg hα_lip
  have hβγ :
      lowDeltaParams.β_S * (1 - lowDeltaParams.δ) < 1 := by
    simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
    norm_num
  have h :=
    Sanctions.AbstractGame.movAvg_bellmanS_shock_mem_senderPrimitiveValLipCarrier
      lowDeltaParams lowDeltaH_pos hα hα_mem V_S
      (cube_S := lowDeltaSenderStageBound)
      (L_U_S := lowDeltaSenderStageStateLip + Lα)
      (γ_F := 1 - lowDeltaParams.δ)
      (by norm_num [lowDeltaSenderStageBound])
      (add_nonneg (by norm_num [lowDeltaSenderStageStateLip]) hLα)
      (by simp only [lowDeltaParams_δ]; norm_num)
      (by simp only [lowDeltaParams_β_S]; norm_num)
      hβγ hV_S
      (by simpa only [lowDeltaSenderStageBound] using lowDelta_US_cube_bound)
      (by
        simpa only [lowDeltaSenderStageStateLip] using
          lowDelta_US_composed_state_lipschitz hα_lip)
      (by
        intro x₁ x₂ s hs
        have hF := lowDelta_F_state_lipschitz x₁ x₂ s hs
        norm_num [lowDeltaParams_δ] at hF ⊢
        exact hF)
  simpa only [lowDeltaShocked, coupledSenderPrimitiveCarrier] using h

/-- **Legacy fixed-carrier witness check.** The current Sender carrier is
preserved whenever the realized Target policy is continuous, feasible, and
state-Lipschitz with modulus no larger than
`coupledAlphaStateBudget`.  This exact budget is retained only to document the
refuted fixed-carrier route; the canonical invariant set is
`coupledSenderPrimitiveCarrier`.  Witness-specific (Rule 22).  The former
premise `0 ≤ Lα` is dropped: it is derived from `hα_lip`. -/
theorem coupled_sender_Bellman_mem_carrier_of_policy_lipschitz
    (α : ℝ → ℝ) (hα : Continuous α)
    (hα_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    {Lα : ℝ}
    (hLα_max : Lα ≤ coupledAlphaStateBudget)
    (hα_lip : ∀ x₁ x₂ : ℝ,
      |α x₂ - α x₁| ≤ Lα * |x₂ - x₁|)
    (V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS) :
    lowDeltaShocked.bellmanS_shock α hα V_S
      ∈ coupledCarrierS := by
  have hV :
      V_S ∈ valLipBall (523 / 160) (57377 / 3200) := by
    simpa only [coupledCarrierS, lowDeltaSenderCarrierNorm_eq,
      lowDeltaSenderCarrierLip_eq] using hV_S
  have hmargin :
      (7 / 4 + Lα)
          + lowDeltaParams.β_S
            * (57377 / 3200) * (99 / 100)
        ≤ 57377 / 3200 := by
    simp only [lowDeltaParams_β_S]
    linarith [coupledSenderLip_margin_witness]
  have h :=
    Sanctions.AbstractGame.movAvg_bellmanS_shock_mem_valLipBall
      lowDeltaParams lowDeltaH_pos hα hα_mem V_S
      (M := 523 / 160) (K := 57377 / 3200)
      (cube_S := 523 / 320) (L_U_S := 7 / 4 + Lα)
      (γ_F := 99 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp only [lowDeltaParams_β_S]; norm_num)
      hV lowDelta_US_cube_bound
      (lowDelta_US_composed_state_lipschitz hα_lip)
      lowDelta_F_state_lipschitz
      (by simp only [lowDeltaParams_β_S]; norm_num)
      hmargin
  simpa only [lowDeltaShocked, coupledCarrierS,
    lowDeltaSenderCarrierNorm_eq, lowDeltaSenderCarrierLip_eq] using h

end
end Examples
end Sanctions
