/-
Sanctions/Examples/CoupledRoute/CoupledSchurWitness.lean

**W3: a genuinely two-sided-coupled Schur-matrix diagnostic.**

At the existing low-δ window economy `lowDeltaParams` (P3 stage payoffs,
δ = 1/100, box-kernel half-width h = 1/10, β_S = 1/2, β_T = 9/10, basin
[1/2, 77/100]; `Examples/CoupledRoute/LowDeltaWindowWitness.lean`), the shocked joint
(Target, Sender) Bellman operator pair carries a genuinely two-sided-coupled
2×2 row-Lipschitz matrix: BOTH governments' value functions feed back into
each other's Bellman rows with strictly positive constants,

  Target row :  β_T = 9/10,       L_TS = 1280/5411   ≈ 0.2366 > 0
  Sender row :  L_ST = 2880/37877 ≈ 0.0760 > 0,      b_S,row = 8697049946379/15525967670038 ≈ 0.5602,

and the exact Schur margin holds:

  L_TS · L_ST = 3686400/204952447 ≈ 0.017987
    <  (1 − β_T)(1 − b_S,row) = 6828917723659/155259676700380 ≈ 0.043984,

with slack +4036322267659/155259676700380 ≈ +0.026 (Perov spectral radius
≈ 0.9466 < 1).  **The decisive structural fact**: the legacy ROW-SUM route
provably FAILS on the Target row — β_T + L_TS = 61499/54110 ≈ 1.1366 ≥ 1
(`coupled_rowSum_fails`). Thus any successful contraction proof at these
constants must use the Schur/Perov layer rather than the row-sum route.
However, the current carrier package does not yet supply such a proof.
The legacy modulus-`2` Target premise is false
(`not_coupledLeaderStrongConcave`), and the corrected quadratic-growth
interface is also formally false uniformly on the current Target carrier
(`not_coupledTargetQuadraticGrowth`).  In addition,
`coupledSteepPolicy_sender_image_not_mem` proves that continuity and
feasibility of the leader policy alone do not preserve the present Sender
Lipschitz carrier.

## What is delivered

1. **Carrier pair** (`coupledCarrierT`, `coupledCarrierS`): the Target carrier
   is the MONOTONE gain-ball — a primitive-derived sup-norm ball intersected
   with the zero-slope lower-slope pin
   `LowerSlopeOnValueOn V (Icc 0 1) 0` (i.e. `V` non-decreasing: the monotone
   pin that discharges the A2 combined-chord condition with loss rate
   `c_T-loss = 0`, and which the box smear preserves, `movAvgBCF_mono`); the
   Sender carrier is the Lipschitz ball `valLipBall M_S K_S`, where `M_S`
   is computed by `carrierMinNormS` from the stage cube bound and discount,
   and `K_S` is computed from the stage state modulus and moving-average
   transition geometry. Their reduced rationals are optional witness checks.
   Both carriers are closed and nonempty.

2. **Row-Lipschitz bounds at the witness** (`coupled_L_TS`, `coupled_L_ST`):
   the Target row instantiates the already-proved shocked row theorem
   through its Theory-level box-restricted sibling
   `targetDynBCF_shock_row_lipschitz_box` because the P3 payoff is
   action-affine with an x-slope, so its stage sanction-Lipschitz constant
   `L_UT = 1` is true on the state–action box but false on all of ℝ²) at the
   exact chain numbers `(L_UT + β_T·(M_T/h)·δ)·Lσ = (14/5)·(3200/37877)
   = 1280/5411`, with `Lσ = 2·β_S·(1/h)·δ/c_S = 3200/37877` derived from
   `sigma_top_lipschitz_in_V_pair` at the certified smeared concavity
   `c_S = 37877/32000` (window (C3), `lowDelta_window_C3_eq`).  (The
   deterministic two-carrier Target row
   `ValueClass2.jointTargetOp_sub_row_lipschitz_generalF` likewise asks for
   the stage sanction-Lipschitz bound only on `S × I × I × I`, round BH1.2.)
   The Sender row mirrors the deterministic two-carrier
   `ValueClass2.jointSenderOp_sub_row_lipschitz_of_alphaOn`
   shape: value channel `β_S = 1/2` plus policy channel
   `L_Ua·(2/c_T)·(L_leadT·dist V_T + L_leadS·dist V_S)` with `L_Ua = 1`,
   `c_T = 2` (the P3 leader constants), `L_leadT = κ_a·β_T·δ·(1/h)
   = 2880/37877` (the κ_a channel through the leader policy — the V_T-side of
   the leader objective-difference constant, with the slaved bound
   `‖ΔV_T‖ ≤ L_VT·dist V_S` replaced by the direct two-sided `dist V_T V_T'`)
   and `L_leadS = T1 + T2S + T3 = 467033055680/7762983835019`.

3. **Strict positivity of both cross channels**: `coupled_L_TS_pos`,
   `coupled_L_ST_pos` (the certified cross constants are strictly positive),
   plus the kernel-checked stage-level activity identities
   `coupled_crosspartial_UT` (∂²U_T/∂a∂s = +1/2: the Target payoff's exact
   action–sanction cross difference) and `coupled_crosspartial_US`
   (∂²U_S/∂s∂a = −1/2: compliance placates).  HONEST RESIDUAL: the Rule-16
   style operator-image exhibit (two explicit carrier pairs whose OPERATOR
   images differ through each channel — kernel-checked strict coupling of the
   maps, not just positive tight bounds on the constants) is NOT delivered
   here; it needs computable argmax evaluations at explicit carrier values and
   remains the one open sub-item of this witness.

4. **Exact Schur margin** (`coupledSchur_margin_robust`, `…_exact`), stated
   under the ROBUST repo factor-2 argmax-core κ_a convention
   (κ_a = 2·|∂²U_S/∂s∂a|/c_S = 32000/37877), plus the favorable IFT-form
   variant (`coupledSchur_margin_favorable`, κ_a halved, margin +0.0356), the
   split-consistency identity `coupledSchur_margin_eq_slaved_slack` (the
   two-sided Schur margin equals (1−β_T) times the slaved C4 contraction
   slack of `lowDelta_window_C4_robust` — the exact algebraic consistency of
   the two-sided channel split with the certified slaved chain), and the
   row-sum failure `coupled_rowSum_fails`.

5. **Corrected conditional templates and their obstruction**:
   `coupledSchur_exists_equilibrium` and
   `coupledSchur_unique_in_carrier` package the Perov conclusion under a
   named analytic premise set.  They now consume quadratic growth at the
   realised Target policy rather than the refuted strong-concavity premise.
   Sender strong concavity and Sender-selector continuity are proved in this
   file, not assumed.  They still do not establish existence at the current
   carriers: carrier-uniform Target growth and Target-carrier invariance are
   formally refuted, the Target-value half of the two-sided
   objective-difference estimate is proved, and the advertised
   carrier-uniform all-actions Sender-value half is formally refuted.
   The narrower realised-leader-only premise and selected-policy Sender
   invariance remain conditional.  The exact matrix and Schur margin remain
   valid candidate bounds, but the coupled capstone is not presently
   inhabited.  The joint operator `coupledJointOp` these templates were
   stated over is itself retired to the commented evidence block of §6
   (round BG3.9, 2026-10-06): its Target-invariance premise `h_invT` fails
   at the zero continuation pair (`coupledZeroPair_target_image_not_mem`).

## Honest scope (what is and is not claimed)

This file supplies conditional coupled-existence and in-carrier-uniqueness
templates; it does not establish either conclusion at the current economy.
The full three-goals compliance certificate is likewise not claimed: in
particular the
`hIDO_on` field (the interval-dominance family in the state x at the realized
policy α(x)) remains a separate open discharge item at this low-δ coupled
diagnostic — the fixed-a strong-rally margin
2959677/6400000 ≈ +0.4625 is exact, but the realized-α channel needs an
α-slope bound not derived here.  Full-width realized-policy interval dominance
is separately proved at the explicit mechanism equilibrium by
`mwEqSenderDynObjective_realized_IDOFamilyOn`.

The capstones consume, at this economy, the following remaining analytic
package (NO new primitive field is introduced — Rule 3):

* `lead`, `lead_cont`, `lead_mem` — the two-sided leader best-response family
  and its continuity/feasibility (the shape of the interior-existence leader
  package, `shockedFeedbackStackelbergTop_interior_discharged_canonical`);
* Sender regularity is **discharged**: `coupled_sender_strongConcave_of_lipschitz`
  proves the one-box modulus `6/5 − K/2000` for every `K`-Lipschitz Sender
  value, and `coupled_sender_strongConcave` keeps the conservative
  `c_S = 37877/32000` used downstream.  Both read only the Lipschitz half of
  Sender-carrier membership.  `coupled_sigmaDynTop_continuous_subtype` /
  `coupled_sigmaDynTop_clamped_continuous_of_lipschitz` derive the physical and
  clamped selector continuity from uniqueness plus Berge;
* `growth_T` — carrier-uniform quadratic growth at the realised Target
  maximizer.  This replaces both the false `sc_T` and the separate `lopt`
  input: `coupled_isMaxOn_of_quadraticGrowth` derives Rule-1 optimality.
  `coupledLeaderObj_zero_zero_quadratic_growth` proves the route at the
  zero pair and diagnostic state, while `not_coupledTargetQuadraticGrowth`
  proves that no such carrier-uniform theorem is available on the present
  Target carrier;
* `h_obj_diff` — the Stackelberg-coupling leader objective-difference
  action-Lipschitz estimate in its TWO-SIDED channel-split form, at the
  pinned constants `(L_leadT, L_leadS) = (2880/37877,
  467033055680/7762983835019)`: this NARROWS the accepted slaved `h_obj_diff`
  surface of `lowDelta_purified_existence` (a free scalar against
  `dist V_S W_S` on the slaved objective) to the split constants the
  C²-kernel chain produces — no new primitive, a re-decomposition of the
  same named regularity.  `coupledLeaderObj_diff_lip_in_VT` proves the
  Target-value channel.
  `not_coupledLeaderObj_sender_uniform_advertised` refutes the advertised
  Sender-value coefficient as a carrier-uniform all-actions theorem, but does
  not independently refute this narrower realised-leader-only premise;
* `h_invT`, `h_invS` — invariance of the two carriers under the respective
  shocked Bellman rows.  `coupledZeroPair_target_image_not_mem` directly
  refutes `h_invT`: at the admissible zero continuation pair, the endogenous
  greatest Sender response makes the Target Bellman value fall from `0` at
  state `0` to `-7/600` at state `1/10`, violating the Target carrier's
  monotonicity pin.  `coupledSteepPolicy_sender_image_not_mem` separately shows
  that `h_invS` cannot be derived from `lead_cont` and `lead_mem` alone: the
  stage policy channel can exhaust any fixed state-Lipschitz budget.  A carrier
  redesign is therefore mandatory on the Target side, while a quantitative
  state modulus for the selected leader or a carrier redesign is required on
  the Sender side.

The row constants, Schur margin, contraction diagonals, and row-sum failure
are exact-rational witness checks. The conditional coupled templates still
consume numerical specializations of symbolic objective geometry, so this
diagnostic packet is not promoted as an existence theorem.

Standing prohibitions honored: nothing here touches δ = 1/5, and no Tarski
isotonicity is used anywhere.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaWindowWitness
import Sanctions.Foundations.ArgmaxSensitivity
import Sanctions.Foundations.Berge
import Sanctions.Theory.Bellman.InvariantLipGainBall
import Sanctions.Theory.Shocked.CoupledPerovExistence
import Sanctions.Theory.Shocked.ShockedRowLipschitz

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace Examples

open AbstractGame Sanctions.AbstractGame.Params

/-! ## §1 Primitive-derived carrier bounds

The carrier definitions below use closed forms obtained from the payoff
cube bounds, discounts, transition state modulus, and moving-average
geometry.  Their reduced rational values are recorded only by the witness
equalities that follow. -/

/-- Target stage-payoff cube bound used to derive the value radius. -/
def lowDeltaTargetStageBound : ℝ := 2

/-- Sender stage-payoff cube bound used to derive the value radius. -/
def lowDeltaSenderStageBound : ℝ := 523 / 320

/-- Direct state-Lipschitz bound for the Sender stage payoff. -/
def lowDeltaSenderStageStateLip : ℝ := 7 / 4

/-- Minimal Target sup-norm radius implied by the stage bound and discount. -/
def lowDeltaTargetCarrierNorm : ℝ :=
  lowDeltaParams.carrierMinNormT lowDeltaTargetStageBound

/-- Minimal Sender sup-norm radius implied by the stage bound and discount. -/
def lowDeltaSenderCarrierNorm : ℝ :=
  lowDeltaParams.carrierMinNormS lowDeltaSenderStageBound

/-- Sender state modulus created by the stage slope and smoothed continuation
geometry on the primitive-derived norm ball. -/
def lowDeltaSenderCarrierLip : ℝ :=
  lowDeltaSenderStageStateLip
    + lowDeltaParams.β_S
      * (lowDeltaSenderCarrierNorm / (1 / 10))
      * (1 - lowDeltaParams.δ)

/-- Optional exact-rational check of the Target carrier radius. -/
theorem lowDeltaTargetCarrierNorm_eq :
    lowDeltaTargetCarrierNorm = 20 := by
  norm_num [lowDeltaTargetCarrierNorm, lowDeltaTargetStageBound,
    AbstractGame.Params.carrierMinNormT]

/-- Optional exact-rational check of the Sender carrier radius. -/
theorem lowDeltaSenderCarrierNorm_eq :
    lowDeltaSenderCarrierNorm = 523 / 160 := by
  norm_num [lowDeltaSenderCarrierNorm, lowDeltaSenderStageBound,
    AbstractGame.Params.carrierMinNormS]

/-- Optional exact-rational check of the Sender carrier state modulus. -/
theorem lowDeltaSenderCarrierLip_eq :
    lowDeltaSenderCarrierLip = 57377 / 3200 := by
  norm_num [lowDeltaSenderCarrierLip, lowDeltaSenderStageStateLip,
    lowDeltaSenderCarrierNorm, lowDeltaSenderStageBound,
    AbstractGame.Params.carrierMinNormS]

/-- **The Target carrier**: the primitive-derived sup-norm ball intersected
with the monotone gain-ball pin (`LowerSlopeOnValueOn` with `gT = 0`).  The
monotonicity component is retained only as the audited legacy obstruction:
the redesigned invariant Target carrier below replaces it. -/
def coupledCarrierT : Set SBCF :=
  {V : SBCF | ‖V‖ ≤ lowDeltaTargetCarrierNorm} ∩
    {V : SBCF | LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) 0}

/-- **The Sender carrier**: the norm-Lipschitz invariant set whose two
moduli are derived above from stage-payoff and transition geometry. -/
def coupledCarrierS : Set SBCF :=
  valLipBall lowDeltaSenderCarrierNorm lowDeltaSenderCarrierLip

/-- The Target carrier is closed (norm ball ∩ pointwise-inequality set). -/
theorem coupledCarrierT_isClosed : IsClosed coupledCarrierT :=
  (isClosed_le continuous_norm continuous_const).inter
    (lowerSlopeOnValueOn_isClosed (Set.Icc (0 : ℝ) 1) 0)

/-- The Sender carrier is closed. -/
theorem coupledCarrierS_isClosed : IsClosed coupledCarrierS :=
  valLipBall_isClosed lowDeltaSenderCarrierNorm lowDeltaSenderCarrierLip

/-- The zero value lies in the Target carrier (nonemptiness). -/
theorem coupledCarrierT_nonempty : coupledCarrierT.Nonempty := by
  refine ⟨0, ?_, ?_⟩
  · change ‖(0 : SBCF)‖ ≤ lowDeltaTargetCarrierNorm
    rw [lowDeltaTargetCarrierNorm_eq]
    norm_num
  · intro y₁ y₂ _ _ _
    change (0 : ℝ) * dist y₁ y₂ ≤ (0 : SBCF) y₂ - (0 : SBCF) y₁
    simp

/-- The zero value lies in the Sender carrier (nonemptiness). -/
theorem coupledCarrierS_nonempty : coupledCarrierS.Nonempty :=
  valLipBall_nonempty
    (by
      norm_num [lowDeltaSenderCarrierNorm, lowDeltaSenderStageBound,
        AbstractGame.Params.carrierMinNormS])
    (by
      norm_num [lowDeltaSenderCarrierLip, lowDeltaSenderStageStateLip,
        lowDeltaSenderCarrierNorm, lowDeltaSenderStageBound,
        AbstractGame.Params.carrierMinNormS])

/-- The zero value is an explicit member of the Target carrier. -/
theorem zero_mem_coupledCarrierT : (0 : SBCF) ∈ coupledCarrierT := by
  refine ⟨?_, ?_⟩
  · change ‖(0 : SBCF)‖ ≤ lowDeltaTargetCarrierNorm
    rw [lowDeltaTargetCarrierNorm_eq]
    norm_num
  · intro y₁ y₂ _ _ _
    change (0 : ℝ) * dist y₁ y₂ ≤ (0 : SBCF) y₂ - (0 : SBCF) y₁
    simp

/-- The zero value is an explicit member of the Sender carrier. -/
theorem zero_mem_coupledCarrierS : (0 : SBCF) ∈ coupledCarrierS :=
  AbstractGame.Params.zero_mem_valLipBall
    (by
      norm_num [lowDeltaSenderCarrierNorm, lowDeltaSenderStageBound,
        AbstractGame.Params.carrierMinNormS])
    (by
      norm_num [lowDeltaSenderCarrierLip, lowDeltaSenderStageStateLip,
        lowDeltaSenderCarrierNorm, lowDeltaSenderStageBound,
        AbstractGame.Params.carrierMinNormS])

/-- A continuous feasible policy that changes from `0` to `1` over the first
one-hundredth of the state space.  It is the disprove-first witness for the
current Sender-carrier invariance claim: continuity alone gives no quantitative
state regularity to the policy channel in `U_S(x, α(x), s)`. -/
noncomputable def coupledSteepPolicy (x : ℝ) : ℝ :=
  Sanctions.clipS (100 * x)

theorem coupledSteepPolicy_continuous : Continuous coupledSteepPolicy := by
  exact Sanctions.clipS_continuous.comp (continuous_const.mul continuous_id)

theorem coupledSteepPolicy_mem (x : ℝ) :
    coupledSteepPolicy x ∈ Sanctions.I := by
  exact Sanctions.clipS_mem _

theorem coupledSteepPolicy_at_zero :
    coupledSteepPolicy 0 = 0 := by
  simp [coupledSteepPolicy, Sanctions.clipS]

theorem coupledSteepPolicy_at_one_hundredth :
    coupledSteepPolicy (1 / 100) = 1 := by
  norm_num [coupledSteepPolicy, Sanctions.clipS]

private theorem coupled_lowDelta_smear_zero :
    lowDeltaShocked.smear (0 : SBCF) = 0 := by
  ext x
  simp [lowDeltaShocked, AbstractGame.movAvgShockedParams, movAvgBCF, movAvgReal]

/-- At state zero, zero continuation and the steep policy give Sender Bellman
value zero: the stage objective is `-(3/5)s²-(1/10)s`, maximized at `s=0`. -/
theorem coupledSteepPolicy_sender_bellman_zero :
    lowDeltaShocked.bellmanS_shock coupledSteepPolicy
      coupledSteepPolicy_continuous (0 : SBCF) ⟨0, by norm_num⟩ = 0 := by
  rw [AbstractGame.ShockedParams.bellmanS_shock, coupled_lowDelta_smear_zero]
  change sSup
      ((fun s => lowDeltaParams.integrandS coupledSteepPolicy
        (fun _ => (0 : ℝ)) (0, s)) '' Sanctions.I) = 0
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, 0, by norm_num, ?_⟩
      simp [AbstractGame.Params.integrandS, lowDeltaParams_U_S,
        lowDeltaParams_β_S, mwU_S, coupledSteepPolicy_at_zero]
    · rintro _ ⟨s, hs, rfl⟩
      rcases hs with ⟨hs0, _hs1⟩
      simp [AbstractGame.Params.integrandS, lowDeltaParams_U_S,
        lowDeltaParams_β_S, mwU_S, coupledSteepPolicy_at_zero]
      nlinarith [sq_nonneg s]
  · apply le_csSup
      (lowDeltaParams.integrandS_image_bddAbove
        coupledSteepPolicy_continuous continuous_const 0)
    exact ⟨0, by norm_num, by
      simp [AbstractGame.Params.integrandS, lowDeltaParams_U_S,
        lowDeltaParams_β_S, mwU_S, coupledSteepPolicy_at_zero]⟩

/-- At state `1/100`, the same Bellman image is at least `251/250`: action
`s=0` is feasible and the steep policy has already reached `α=1`. -/
theorem coupledSteepPolicy_sender_bellman_one_hundredth_lower :
    (251 / 250 : ℝ) ≤
      lowDeltaShocked.bellmanS_shock coupledSteepPolicy
        coupledSteepPolicy_continuous (0 : SBCF) ⟨1 / 100, by norm_num⟩ := by
  rw [AbstractGame.ShockedParams.bellmanS_shock, coupled_lowDelta_smear_zero]
  change (251 / 250 : ℝ) ≤ sSup
      ((fun s => lowDeltaParams.integrandS coupledSteepPolicy
        (fun _ => (0 : ℝ)) (1 / 100, s)) '' Sanctions.I)
  apply le_csSup
      (lowDeltaParams.integrandS_image_bddAbove
        coupledSteepPolicy_continuous continuous_const (1 / 100))
  refine ⟨0, by norm_num, ?_⟩
  norm_num [AbstractGame.Params.integrandS, lowDeltaParams_U_S,
    lowDeltaParams_β_S, lowDeltaParams_F, mwU_S,
    coupledSteepPolicy_at_one_hundredth]

/-- **The current Sender carrier is not invariant under arbitrary continuous
feasible leader policies.**  The zero continuation belongs to
`coupledCarrierS`, but the Bellman image under `coupledSteepPolicy` violates
the carrier's `57377/3200` state-Lipschitz bound between `0` and `1/100`.

This is a deliberately narrow obstruction: it refutes derivation of `h_invS`
from `lead_cont` and `lead_mem` alone.  It does not say that an actual leader
selected by the coupled objective must equal this policy; closing invariance
requires a quantitative state-regularity theorem for that selected policy or
a carrier redesign. -/
theorem coupledSteepPolicy_sender_image_not_mem :
    lowDeltaShocked.bellmanS_shock coupledSteepPolicy
      coupledSteepPolicy_continuous (0 : SBCF) ∉ coupledCarrierS := by
  intro hmem
  have hLip := hmem.2
    (⟨0, by norm_num⟩ : ↥(Sanctions.S : Set ℝ))
    (⟨1 / 100, by norm_num⟩ : ↥(Sanctions.S : Set ℝ))
  have h0 := coupledSteepPolicy_sender_bellman_zero
  have h1 := coupledSteepPolicy_sender_bellman_one_hundredth_lower
  rw [h0] at hLip
  rw [Subtype.dist_eq, Real.dist_eq] at hLip
  rw [lowDeltaSenderCarrierLip_eq] at hLip
  norm_num at hLip
  have habs :
      lowDeltaShocked.bellmanS_shock coupledSteepPolicy
          coupledSteepPolicy_continuous (0 : SBCF)
          ⟨1 / 100, by norm_num⟩
        ≤
      |lowDeltaShocked.bellmanS_shock coupledSteepPolicy
          coupledSteepPolicy_continuous (0 : SBCF)
          ⟨1 / 100, by norm_num⟩| :=
    le_abs_self _
  norm_num at h1 ⊢
  linarith

/-- Members of the Target carrier are monotone (the `gT = 0` slope pin on the
full state space is exactly monotonicity — the property the box smear
preserves, `movAvgBCF_mono`). -/
theorem monotone_of_mem_coupledCarrierT {V : SBCF}
    (hV : V ∈ coupledCarrierT) : Monotone ⇑V := by
  intro y₁ y₂ hle
  have h := hV.2 y₁ y₂ y₁.property y₂.property hle
  have hnn : (0 : ℝ) ≤ 0 * dist y₁ y₂ := by simp
  linarith

/-! ## §2 Stage-level activity of the two cross channels (Rule-16 style)

Kernel-checked exact chord identities showing both coupling channels are
structurally active at this economy: the Target payoff's action–sanction
cross difference is EXACTLY `(1/2)·(a'−a)·(s−s')` (so the Target row's
σ-sensitivity channel has a genuinely nonzero stage source), and the Sender
payoff's is EXACTLY `−(1/2)·(a'−a)·(s−s')` (compliance placates — the κ_a
channel through the leader policy has a genuinely nonzero cross-partial).
The remaining operator-image strict-coupling exhibit is the honest residual
recorded in the header. -/

/-- Exact Target cross-chord: `∂²U_T/∂a∂s = +1/2 ≠ 0`. -/
theorem coupled_crosspartial_UT (x a a' s s' : ℝ) :
    (mwU_T x a' s - mwU_T x a s) - (mwU_T x a' s' - mwU_T x a s')
      = (1 / 2) * (a' - a) * (s - s') := by
  simp only [mwU_T]; ring

/-- Exact Sender cross-chord: `∂²U_S/∂s∂a = −1/2 ≠ 0` (compliance placates). -/
theorem coupled_crosspartial_US (x a a' s s' : ℝ) :
    (mwU_S x a' s - mwU_S x a s) - (mwU_S x a' s' - mwU_S x a s')
      = -(1 / 2) * (a' - a) * (s - s') := by
  simp only [mwU_S]; ring

/-! ## §3 Witness-level ingredient bounds (all proved, no hypotheses) -/

/-- `clip ∘ F` is action-Lipschitz with constant `LF = δ = 1/100` at the
witness (the affine transition moves the next state by `δ·|s−s'|` and the
clip is 1-Lipschitz). -/
theorem lowDelta_clipF_lip (x s s' : ℝ) :
    |(Sanctions.clipS' (lowDeltaShocked.toParams.F x s)).val
      - (Sanctions.clipS' (lowDeltaShocked.toParams.F x s')).val|
      ≤ (1 / 100) * |s - s'| := by
  have h := Sanctions.clipS'_lipschitz_dist
    (lowDeltaShocked.toParams.F x s) (lowDeltaShocked.toParams.F x s')
  rw [Subtype.dist_eq, Real.dist_eq] at h
  have he : lowDeltaShocked.toParams.F x s - lowDeltaShocked.toParams.F x s'
      = (1 / 100) * (s - s') := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      Sanctions.AbstractGame.affineF]
    ring
  calc |(Sanctions.clipS' (lowDeltaShocked.toParams.F x s)).val
      - (Sanctions.clipS' (lowDeltaShocked.toParams.F x s')).val|
      ≤ |lowDeltaShocked.toParams.F x s - lowDeltaShocked.toParams.F x s'| := h
    _ = (1 / 100) * |s - s'| := by
        rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]

/-- The box smear of the witness is state-Lipschitz with the creation-bound
constant `Lκ·‖U‖ = 10·‖U‖` (`Lκ = 1/h = 10`). -/
theorem lowDelta_smear_creation_lip (U : SBCF)
    (z z' : ↥(Sanctions.S : Set ℝ)) :
    |lowDeltaShocked.smear U z - lowDeltaShocked.smear U z'|
      ≤ 10 * ‖U‖ * dist z z' := by
  have h := lowDeltaShocked_smear_lipschitz U z z'
  have he : ‖U‖ / (1 / 10 : ℝ) = 10 * ‖U‖ := by ring
  rwa [he] at h

/-- `U_T` is sanction-Lipschitz with `L_UT = 1` on the state–action box
(the sanction slope is `x + a/2 − 1/2 ∈ [−1, 1]` there). -/
theorem lowDelta_UT_action_lip :
    ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I,
      |lowDeltaShocked.toParams.U_T x a s - lowDeltaShocked.toParams.U_T x a s'|
        ≤ 1 * |s - s'| := by
  intro x hx a ha s _hs s' _hs'
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha0, ha1⟩ := ha
  have hkey : lowDeltaShocked.toParams.U_T x a s
      - lowDeltaShocked.toParams.U_T x a s' = (s' - s) * (1 / 2 - a / 2 - x) := by
    simp only [lowDeltaShocked_toParams, lowDeltaParams_U_T, mwU_T]; ring
  rw [hkey, abs_mul, one_mul]
  have h1 : |1 / 2 - a / 2 - x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |s' - s| * |1 / 2 - a / 2 - x| ≤ |s' - s| * 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |s - s'| := by rw [mul_one, abs_sub_comm]

/-- The low-delta box smear maps the zero continuation value to zero. -/
theorem lowDelta_smear_zero :
    lowDeltaShocked.smear (0 : SBCF) = 0 := by
  ext x
  simp [lowDeltaShocked, AbstractGame.movAvgShockedParams, movAvgBCF, movAvgReal]

/-- The witness Sender stage objective is `6/5`-strongly concave in sanctions. -/
theorem lowDelta_sender_stage_strongConcave (x a : ℝ) :
    StrongConcaveOn Sanctions.I (6 / 5) (fun s => mwU_S x a s) := by
  unfold StrongConcaveOn UniformConcaveOn
  refine ⟨convex_Icc _ _, ?_⟩
  intro s hs t ht u v hu hv huv
  simp only [smul_eq_mul]
  rw [Real.norm_eq_abs, sq_abs]
  unfold mwU_S
  have hv_eq : v = 1 - u := by linarith
  rw [hv_eq]
  ring_nf
  exact le_rfl

/-- **The `6/5` stage modulus is SHARP — it carries no unbanked slack.**

Rule-11 refutation gate for the de-numericalization programme (2026-07-28).
If `6/5` were a padded hand-tuned constant, every downstream constant in the
`coupledEps*` chain (`coupledEpsCS`, and through it `coupledEpsLσ`,
`coupledEpsG`, the row constants and the Schur margin) would inherit
unaccounted slack, and restating those constants symbolically would be
papering over a loose bound rather than recording a derivation.

It is not padded: **no** modulus strictly above `6/5` works, at **any**
state and action, for **any** positive slack. The witness is the pair of
endpoints `s = 0`, `s = 1` at equal weights, where
`lowDelta_sender_stage_strongConcave` above is an exact equality
(its proof closes with `ring_nf; exact le_rfl`) — so there is no room left.

Consequence: the `6/5` appearing in `coupledEpsCS` and in
`redesignResponseD` is the exact stage curvature `|∂²U_S/∂s²|`, not a
tuning choice. -/
theorem lowDelta_sender_stage_strongConcave_sharp (x a ε : ℝ) (hε : 0 < ε) :
    ¬ StrongConcaveOn Sanctions.I (6 / 5 + ε) (fun s => mwU_S x a s) := by
  intro h
  have h0 : (0 : ℝ) ∈ Sanctions.I := by simp [Sanctions.I]
  have h1 : (1 : ℝ) ∈ Sanctions.I := by simp [Sanctions.I]
  have hineq := h.2 h0 h1
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, mwU_S, Real.norm_eq_abs] at hineq
  norm_num at hineq
  nlinarith [hineq, hε]

/-- **The Sender objective is strongly concave at the one-box modulus
`6/5 − K/2000`, for every `K`-Lipschitz continuation value.**

Witness-specific (Rule 22): this is the low-δ economy (`U_S = mwU_S`, affine
transition `F = affineF (1/100)`, box kernel `h = 1/10`, `β_S = 1/2`), not a
general-`F` statement.  A one-box average of a `K`-Lipschitz value has a
`K/h`-Lipschitz derivative, so its curvature is at worst `−K/h`.  Composing
with the affine transition multiplies that adverse curvature by `δ²`, and
discounting multiplies it by `β_S`.  What is left of the sharp stage
curvature `6/5` is `6/5 − β_S·δ²·K/h = 6/5 − K/2000`.

Only the Lipschitz half of Sender-carrier membership is read: the norm bound
is dropped and the modulus `K` is free.  For `K > 2400` the modulus is
negative and the statement is weaker than concavity, but still true.  No
differentiability of the continuation value is assumed. -/
theorem coupled_sender_strongConcave_of_lipschitz
    (V_S : SBCF) {K : ℝ} (hV_S : ValueLipschitzWith V_S K)
    (x : ℝ) (hx : x ∈ Sanctions.S) (a : ℝ) :
    StrongConcaveOn Sanctions.I (6 / 5 - K / 2000)
      (fun s => lowDeltaShocked.toParams.U_S x a s
        + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear V_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))) := by
  have hsmear : StrongConcaveOn Set.univ (-(K / (1 / 10)))
      (Sanctions.movAvgReal (1 / 10) V_S) :=
    Sanctions.movAvgReal_strongConcaveOn_of_valueLipschitz
      lowDeltaH_pos V_S hV_S.nonneg hV_S
  have hcomp := Sanctions.strongConcaveOn_comp_affine_real
    (s := Sanctions.I) (t := Set.univ)
    (m := -(K / (1 / 10)))
    (c := (1 - (1 / 100 : ℝ)) * x) (d := 1 / 100)
    (convex_Icc 0 1) hsmear (fun _ _ => Set.mem_univ _)
  have hscaled := Sanctions.strongConcaveOn_const_mul_real
    (c := (1 / 2 : ℝ)) (by norm_num) hcomp
  have hadd := Sanctions.strongConcaveOn_add_real
    (lowDelta_sender_stage_strongConcave x a) hscaled
  have hstrong : StrongConcaveOn Sanctions.I (6 / 5 - K / 2000)
      (fun s => mwU_S x a s + (1 / 2) *
        Sanctions.movAvgReal (1 / 10) V_S
          ((1 - (1 / 100 : ℝ)) * x + (1 / 100) * s)) := by
    apply hadd.mono
    exact le_of_eq (by ring)
  apply Sanctions.strongConcaveOn_congr_real hstrong
  intro s hs
  simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S, lowDeltaParams_β_S,
    lowDeltaParams_F, Sanctions.AbstractGame.affineF,
    lowDeltaShocked_smear, Sanctions.movAvgBCF_apply]
  have hF : (1 - (1 / 100 : ℝ)) * x + (1 / 100) * s ∈ Sanctions.S :=
    Sanctions.AbstractGame.affineF_mem (δ := (1 / 100 : ℝ))
      (by constructor <;> norm_num) x s hx hs
  rw [Sanctions.clipS'_val_eq_of_mem hF]

/-- **The Sender strong-concavity premise is discharged on every
`K_S`-Lipschitz Sender value**, at the conservative modulus `37877/32000`.

Witness-specific (Rule 22), like `coupled_sender_strongConcave_of_lipschitz`,
of which it is the corollary at `K = K_S = 57377/3200`: the one-box modulus
there is `6/5 − K_S/2000 = 7622623/6400000`, which is strictly larger than
`37877/32000`.  The smaller constant is kept because the downstream numerals
(`coupledSigmaStateK`, the σ-Lipschitz constants, the row constants) are
derived from it.  The hypothesis is the Lipschitz half of
`V_S ∈ coupledCarrierS`; the norm half, never used, is dropped. -/
theorem coupled_sender_strongConcave
    (V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (x : ℝ) (hx : x ∈ Sanctions.S) (a : ℝ) :
    StrongConcaveOn Sanctions.I (37877 / 32000)
      (fun s => lowDeltaShocked.toParams.U_S x a s
        + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear V_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))) := by
  apply (coupled_sender_strongConcave_of_lipschitz V_S hV_S x hx a).mono
  rw [lowDeltaSenderCarrierLip_eq]
  norm_num

/-- **The shocked greatest Sender selector is jointly continuous on physical
states for every `K_S`-Lipschitz Sender value.**  Strong concavity above gives
argmax uniqueness; the state-local Berge theorem then gives continuity on
`↥S × ℝ`.  This is the economically relevant interface.  A globally
continuous whole-line selector is obtained, when needed by generic Bellman
constructors, by the existing state-clamped extension.  Witness-specific
(Rule 22).  Only the Lipschitz half of Sender-carrier membership is assumed;
the norm half is dropped. -/
theorem coupled_sigmaDynTop_continuous_subtype
    (V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip) :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear V_S) xa.1.val xa.2) := by
  have huniq : lowDeltaShocked.toParams.DynamicArgmaxUnique
      (lowDeltaShocked.smear V_S) := by
    apply lowDeltaShocked.toParams.dynamicArgmaxUnique_of_strictConcaveOn
    intro x hx a
    exact (coupled_sender_strongConcave V_S hV_S x hx a).strictConcaveOn
      (by norm_num)
  exact lowDeltaShocked.toParams.σ_dyn_top_continuous_subtype_of_unique_on
    (lowDeltaShocked.smear V_S) huniq

/-- The continuous whole-line extension used by generic Target Bellman
constructors, for every `K_S`-Lipschitz Sender value.  It clips only the
inherited state; on every physical state it equals the equilibrium-derived
greatest Sender selector.  Witness-specific (Rule 22).  Only the Lipschitz half
of Sender-carrier membership is assumed. -/
theorem coupled_sigmaDynTop_clamped_continuous_of_lipschitz
    (V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip) :
    Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear V_S) xa.1 xa.2) :=
  lowDeltaShocked.toParams.σ_dyn_top_clamped_continuous
    (lowDeltaShocked.smear V_S)
    (coupled_sigmaDynTop_continuous_subtype V_S hV_S)

/-- The continuous whole-line extension on the Sender carrier: the
carrier-membership form of
`coupled_sigmaDynTop_clamped_continuous_of_lipschitz`, kept for the
carrier-indexed operators and their consumers.  Witness-specific (Rule 22). -/
theorem coupled_sigmaDynTop_clamped_continuous
    (V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS) :
    Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear V_S) xa.1 xa.2) :=
  coupled_sigmaDynTop_clamped_continuous_of_lipschitz V_S hV_S.2

/-- With the zero continuation value, the dynamic top Sender selector is
exactly the primitive clipped quadratic best response. -/
theorem lowDelta_sigmaDynTop_smear_zero (x a : ℝ) :
    lowDeltaShocked.toParams.σ_dyn_top
      (lowDeltaShocked.smear (0 : SBCF)) x a = mwσ x a := by
  have htop := lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
    (lowDeltaShocked.smear (0 : SBCF)) x a
  have htop' : IsMaxOn (fun s => mwU_S x a s) Sanctions.I
      (lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear (0 : SBCF)) x a) := by
    intro s hs
    simpa [lowDelta_smear_zero] using htop hs
  exact AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
    ((lowDelta_sender_stage_strongConcave x a).strictConcaveOn (by norm_num))
    (lowDeltaShocked.toParams.σ_dyn_top_mem_I _ x a) (mwσ_mem x a)
    htop' (mwσ_isMaxOn x a)

private theorem coupled_mwσ_zero_state {a : ℝ} (ha : a ∈ Sanctions.I) :
    mwσ 0 a = 0 := by
  rcases ha with ⟨ha0, _ha1⟩
  unfold mwσ
  have hraw : (9 / 8 : ℝ) * 0 - 1 / 12 - (5 / 12) * a ≤ 0 := by
    nlinarith
  rw [min_eq_right (by linarith), max_eq_left hraw]

private theorem coupled_mwσ_one_tenth_low {a : ℝ}
    (haI : a ∈ Sanctions.I) (ha : a ≤ 7 / 100) :
    mwσ (1 / 10) a = 7 / 240 - (5 / 12) * a := by
  rcases haI with ⟨ha0, _ha1⟩
  unfold mwσ
  have hraw0 : 0 ≤ (9 / 8 : ℝ) * (1 / 10) - 1 / 12 - (5 / 12) * a := by
    nlinarith
  have hraw1 : (9 / 8 : ℝ) * (1 / 10) - 1 / 12 - (5 / 12) * a ≤ 1 := by
    nlinarith
  rw [min_eq_right hraw1, max_eq_right hraw0]
  ring

private theorem coupled_mwσ_one_tenth_high {a : ℝ} (ha : 7 / 100 ≤ a) :
    mwσ (1 / 10) a = 0 := by
  unfold mwσ
  have hraw : (9 / 8 : ℝ) * (1 / 10) - 1 / 12 - (5 / 12) * a ≤ 0 := by
    nlinarith
  rw [min_eq_right (by linarith), max_eq_left hraw]

private theorem lowDelta_sigmaDynTop_clamped_smear_zero
    (x : ℝ) (hx : x ∈ Sanctions.S) (a : ℝ) :
    lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear (0 : SBCF)) x a = mwσ x a := by
  rw [lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
    (lowDeltaShocked.smear (0 : SBCF)) hx]
  exact lowDelta_sigmaDynTop_smear_zero x a

/-- At the zero continuation pair and physical state zero, the endogenous
greatest Sender selector gives Target Bellman value zero.  The realized Sender
sanction is `mwσ 0 a = 0`, and the Target maximizes `-a²-a` at `a=0`. -/
theorem coupledZeroPair_target_bellman_zero :
    lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear (0 : SBCF)))
      (coupled_sigmaDynTop_clamped_continuous 0 zero_mem_coupledCarrierS)
      (0 : SBCF) ⟨0, by norm_num⟩ = 0 := by
  change sSup ((fun a => lowDeltaShocked.toParams.targetDynIntegrand
    (lowDeltaShocked.toParams.σ_dyn_top_clamped
      (lowDeltaShocked.smear (0 : SBCF)))
    (lowDeltaShocked.smear (0 : SBCF)) 0 a) '' Sanctions.I) = 0
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, 0, by norm_num, ?_⟩
      simp only [AbstractGame.Params.targetDynIntegrand]
      rw [lowDelta_sigmaDynTop_clamped_smear_zero 0 (by norm_num) 0,
        coupled_mwσ_zero_state (by norm_num)]
      norm_num [lowDelta_smear_zero, lowDeltaShocked_toParams,
        lowDeltaParams_U_T, mwU_T]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [AbstractGame.Params.targetDynIntegrand]
      rw [lowDelta_sigmaDynTop_clamped_smear_zero 0 (by norm_num) a,
        coupled_mwσ_zero_state ha]
      simp [lowDelta_smear_zero, lowDeltaShocked_toParams,
        lowDeltaParams_U_T, mwU_T]
      rcases ha with ⟨ha0, _ha1⟩
      nlinarith [sq_nonneg a]
  · apply le_csSup
      (lowDeltaShocked.toParams.targetDynIntegrand_image_bddAbove
        (lowDeltaShocked.toParams.σ_dyn_top_clamped
          (lowDeltaShocked.smear (0 : SBCF)))
        (lowDeltaShocked.smear (0 : SBCF))
        (coupled_sigmaDynTop_clamped_continuous 0 zero_mem_coupledCarrierS) 0)
    refine ⟨0, by norm_num, ?_⟩
    simp only [AbstractGame.Params.targetDynIntegrand]
    rw [lowDelta_sigmaDynTop_clamped_smear_zero 0 (by norm_num) 0,
      coupled_mwσ_zero_state (by norm_num)]
    norm_num [lowDelta_smear_zero, lowDeltaShocked_toParams,
      lowDeltaParams_U_T, mwU_T]

/-- At the zero continuation pair and state `1/10`, the endogenous greatest
Sender selector gives Target Bellman value `-7/600`.  On the active branch
`a ≤ 7/100`, the objective is
`-7/600 - (99/160)a - (29/24)a²`; on the remaining branch it is
`-a²-(4/5)a`.  Both are maximized over their feasible portions at `a=0`. -/
theorem coupledZeroPair_target_bellman_one_tenth :
    lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear (0 : SBCF)))
      (coupled_sigmaDynTop_clamped_continuous 0 zero_mem_coupledCarrierS)
      (0 : SBCF) ⟨1 / 10, by norm_num⟩ = -7 / 600 := by
  change sSup ((fun a => lowDeltaShocked.toParams.targetDynIntegrand
    (lowDeltaShocked.toParams.σ_dyn_top_clamped
      (lowDeltaShocked.smear (0 : SBCF)))
    (lowDeltaShocked.smear (0 : SBCF)) (1 / 10) a) '' Sanctions.I) = -7 / 600
  apply le_antisymm
  · apply csSup_le
    · refine ⟨-7 / 600, 0, by norm_num, ?_⟩
      simp only [AbstractGame.Params.targetDynIntegrand]
      rw [lowDelta_sigmaDynTop_clamped_smear_zero (1 / 10) (by norm_num) 0,
        coupled_mwσ_one_tenth_low (by norm_num) (by norm_num)]
      norm_num [lowDelta_smear_zero, lowDeltaShocked_toParams,
        lowDeltaParams_U_T, mwU_T]
    · rintro _ ⟨a, haI, rfl⟩
      simp only [AbstractGame.Params.targetDynIntegrand]
      rw [lowDelta_sigmaDynTop_clamped_smear_zero (1 / 10) (by norm_num) a]
      by_cases ha : a ≤ 7 / 100
      · rw [coupled_mwσ_one_tenth_low haI ha]
        simp [lowDelta_smear_zero, lowDeltaShocked_toParams,
          lowDeltaParams_U_T, mwU_T]
        rcases haI with ⟨ha0, _ha1⟩
        nlinarith [sq_nonneg a]
      · have hge : 7 / 100 ≤ a := by linarith
        rw [coupled_mwσ_one_tenth_high hge]
        simp [lowDelta_smear_zero, lowDeltaShocked_toParams,
          lowDeltaParams_U_T, mwU_T]
        rcases haI with ⟨ha0, _ha1⟩
        nlinarith [sq_nonneg a]
  · apply le_csSup
      (lowDeltaShocked.toParams.targetDynIntegrand_image_bddAbove
        (lowDeltaShocked.toParams.σ_dyn_top_clamped
          (lowDeltaShocked.smear (0 : SBCF)))
        (lowDeltaShocked.smear (0 : SBCF))
        (coupled_sigmaDynTop_clamped_continuous 0 zero_mem_coupledCarrierS)
        (1 / 10))
    refine ⟨0, by norm_num, ?_⟩
    simp only [AbstractGame.Params.targetDynIntegrand]
    rw [lowDelta_sigmaDynTop_clamped_smear_zero (1 / 10) (by norm_num) 0,
      coupled_mwσ_one_tenth_low (by norm_num) (by norm_num)]
    norm_num [lowDelta_smear_zero, lowDeltaShocked_toParams,
      lowDeltaParams_U_T, mwU_T]

/-- **The current Target carrier is not invariant under its endogenous
zero-pair Bellman row.**  Both zero continuation values belong to their
respective carriers, and the shocked Sender selector is the actual greatest
best response.  Nevertheless the Target Bellman image falls from `0` at state
`0` to `-7/600` at state `1/10`, violating the carrier's nondecreasing-value
pin.  Thus the existing `h_invT` premise is false, not merely unfinished. -/
theorem coupledZeroPair_target_image_not_mem :
    lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top_clamped
        (lowDeltaShocked.smear (0 : SBCF)))
      (coupled_sigmaDynTop_clamped_continuous 0 zero_mem_coupledCarrierS)
      (0 : SBCF) ∉ coupledCarrierT := by
  intro hmem
  have hmono := hmem.2
    (⟨0, by norm_num⟩ : ↥(Sanctions.S : Set ℝ))
    (⟨1 / 10, by norm_num⟩ : ↥(Sanctions.S : Set ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rw [coupledZeroPair_target_bellman_zero,
    coupledZeroPair_target_bellman_one_tenth] at hmono
  norm_num at hmono

/-! ## §4 The two row-Lipschitz bounds at the exact witness constants -/

/-- **`coupled_L_TS`: the Target ROW at the witness — cross constant
`L_TS = 1280/5411 > 0`.**  Instantiates the box-restricted shocked Target-row
theorem at the exact chain numbers `L_UT = 1`, `L_smVT = M_T/h = 200` (from
the Target-carrier norm `‖V_T'‖ ≤ 20` and the box-kernel creation bound),
`LF = δ = 1/100`, and `Lσ = 2·β_S·(1/h)·δ/c_S = 3200/37877` (derived from
the pair-form σ-Lipschitz lemma at the certified smeared Sender concavity
`c_S = 37877/32000`, window (C3)).  So
`(L_UT + β_T·L_smVT·LF)·Lσ = (14/5)·(3200/37877) = 1280/5411`.
Sender strong concavity and physical-state selector continuity are discharged
from carrier membership.  The generic Target operator receives the proved
continuous state-clamped extension. -/
theorem coupled_L_TS
    (V_T V_T' V_S W_S : SBCF)
    (hV_T'_norm : ‖V_T'‖ ≤ lowDeltaTargetCarrierNorm)
    (hV_S : V_S ∈ coupledCarrierS) (hW_S : W_S ∈ coupledCarrierS) :
    dist (lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear V_S))
        (coupled_sigmaDynTop_clamped_continuous V_S hV_S) V_T)
      (lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear W_S))
        (coupled_sigmaDynTop_clamped_continuous W_S hW_S) V_T')
      ≤ (9 / 10) * dist V_T V_T' + (1280 / 5411) * dist V_S W_S := by
  -- σ-Lipschitz in `V_S` at `Lσ = 3200/37877`, via the pair lemma.
  have hσ_lip : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      |lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x a
        - lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear W_S) x a|
        ≤ (3200 / 37877) * dist V_S W_S := by
    intro x hx a ha
    have h := Sanctions.AbstractGame.Params.sigma_top_lipschitz_in_V_pair
      (p := lowDeltaShocked.toParams) lowDeltaShocked.smear
      (Lκ := 10) (by norm_num)
      (AbstractGame.movAvgShockedParams_smear_sub lowDeltaParams lowDeltaH_pos)
      lowDelta_smear_creation_lip
      (c := 37877 / 32000) (by norm_num) x a V_S W_S
      (coupled_sender_strongConcave V_S hV_S.2 x hx a)
      (coupled_sender_strongConcave W_S hW_S.2 x hx a)
      (LF := 1 / 100) (by norm_num) (fun s s' => lowDelta_clipF_lip x s s')
    have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
    rw [hβ] at h
    linarith [h]
  -- Smear creation bound on the Target-carrier norm: `L_smVT = 200`.
  have hsmVT_lip : ∀ z z' : ↥(Sanctions.S : Set ℝ),
      |lowDeltaShocked.smear V_T' z - lowDeltaShocked.smear V_T' z'|
        ≤ 200 * dist z z' := by
    intro z z'
    have hV_T'_norm_witness : ‖V_T'‖ ≤ 20 := by
      simpa only [lowDeltaTargetCarrierNorm_eq] using hV_T'_norm
    have h := lowDelta_smear_creation_lip V_T' z z'
    have h2 : 10 * ‖V_T'‖ * dist z z' ≤ 200 * dist z z' := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      linarith [hV_T'_norm_witness]
    exact le_trans h h2
  have h := lowDeltaShocked.targetDynBCF_shock_row_lipschitz_box
    (Lσ := 3200 / 37877) (L_UT := 1) (L_smVT := 200) (LF := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    V_T V_T' V_S W_S
    (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear V_S))
    (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear W_S))
    (coupled_sigmaDynTop_clamped_continuous V_S hV_S)
    (coupled_sigmaDynTop_clamped_continuous W_S hW_S)
    (fun x hx a _ha => by
      rw [lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
        (lowDeltaShocked.smear V_S) hx]
      exact lowDeltaShocked.toParams.σ_dyn_top_mem_I
        (lowDeltaShocked.smear V_S) x a)
    (fun x hx a _ha => by
      rw [lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
        (lowDeltaShocked.smear W_S) hx]
      exact lowDeltaShocked.toParams.σ_dyn_top_mem_I
        (lowDeltaShocked.smear W_S) x a)
    (fun x hx a ha => by
      simpa only [
        lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
          (lowDeltaShocked.smear V_S) hx,
        lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
          (lowDeltaShocked.smear W_S) hx] using hσ_lip x hx a ha)
    lowDelta_UT_action_lip hsmVT_lip
    (fun x s s' => lowDelta_clipF_lip x s s')
  have hβ : lowDeltaShocked.toParams.β_T = 9 / 10 := rfl
  rw [hβ] at h
  linarith [h]

/-- **The shocked leader objective at the witness** — the REAL shocked Target
integrand at a free continuation pair: `joint_T_top_integrand` at the smeared
values `(smear V_T, smear V_S)` (the two-sided generalization of the slaved
objective consumed by `lowDelta_purified_existence`; at the joint fixed point
`V_T = V_T_dyn_shock V_S`, the two coincide). -/
noncomputable def coupledLeaderObj (V_T V_S : SBCF) (x a : ℝ) : ℝ :=
  lowDeltaShocked.toParams.joint_T_top_integrand
    (lowDeltaShocked.smear V_T) (lowDeltaShocked.smear V_S) x a

/-- At the zero continuation pair, the coupled leader objective reduces to
the primitive static Stackelberg composite. -/
theorem coupledLeaderObj_zero_zero (x a : ℝ) :
    coupledLeaderObj 0 0 x a = mwU_T x a (mwσ x a) := by
  simp only [coupledLeaderObj, AbstractGame.Params.joint_T_top_integrand]
  rw [lowDelta_sigmaDynTop_smear_zero]
  simp [lowDelta_smear_zero]

/-! ## §4a The refuted leader strong-concavity hypothesis

**Canonical-leader layer DELETED (2026-07-24 scope repair, user decision,
option c).** A Berge-selector construction (`coupledCanonicalLeaderOnS` /
`coupledCanonicalLeader` and their continuity / feasibility / argmax
lemmas) and its §9 capstones
(`coupledSchur_unique_in_carrier_canonical`,
`coupledSchur_exists_equilibrium_canonical`) previously lived here and
removed the free leader map from the capstone surface — but every result
in that layer consumed the modulus-`2` leader strong-concavity premise
below, which is REFUTED on the current carriers
(`not_coupledLeaderStrongConcave`, a headline row), making the whole
layer vacuously true and uninstantiable (Rule 11.3 / 12.2). What remains
is the honest surface: the named hypothesis, its machine-checked
refutation, and the §7/§8 conditional templates that take the leader map
as an explicit input. A future revival must first substitute a valid
replacement premise (a parametrized modulus, or the weaker
uniqueness-plus-quadratic-growth route the paper appendix names). -/

/-- The carrier-restricted modulus-`2` leader strong-concavity hypothesis —
REFUTED by `not_coupledLeaderStrongConcave` below; retained as the named
statement of the obstruction. -/
abbrev CoupledLeaderStrongConcave : Prop :=
  ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
    ∀ x : ↥(Sanctions.S : Set ℝ),
      StrongConcaveOn Sanctions.I 2
        (fun a => coupledLeaderObj V_T V_S x.val a)

/-- The advertised modulus-`2` coupled leader strong-concavity package is
false on the current carriers. The counterexample is the zero continuation
pair at state `5/12`; there the objective is the static clipped composite and
violates the defining midpoint inequality across the lower-response kink. -/
theorem not_coupledLeaderStrongConcave :
    ¬ CoupledLeaderStrongConcave := by
  intro hsc
  have h := hsc 0 zero_mem_coupledCarrierT 0 zero_mem_coupledCarrierS
    ⟨5 / 12, by constructor <;> norm_num⟩
  unfold StrongConcaveOn UniformConcaveOn at h
  have hmid := h.2
    (show (9 / 10 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
    (show (19 / 20 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [coupledLeaderObj_zero_zero] at hmid
  norm_num [mwU_T, mwσ, Sanctions.I] at hmid

/-- Below the response kink at state `5/12`, the static Sender selector is
the unclipped affine vertex. -/
theorem coupled_mwσ_five_twelfths_of_le {a : ℝ}
    (haI : a ∈ Sanctions.I) (ha : a ≤ 37 / 40) :
    mwσ (5 / 12) a = 37 / 96 - (5 / 12) * a := by
  have hnonneg :
      0 ≤ (9 / 8 : ℝ) * (5 / 12) - 1 / 12 - (5 / 12) * a := by
    nlinarith
  have hleone :
      (9 / 8 : ℝ) * (5 / 12) - 1 / 12 - (5 / 12) * a ≤ 1 := by
    rcases haI with ⟨ha0, ha1⟩
    nlinarith
  rw [mwσ, min_eq_right hleone, max_eq_right hnonneg]
  ring

/-- Above the response kink at state `5/12`, the static Sender selector is
clipped at zero. -/
theorem coupled_mwσ_five_twelfths_of_ge {a : ℝ} (ha : 37 / 40 ≤ a) :
    mwσ (5 / 12) a = 0 := by
  have hnonpos :
      (9 / 8 : ℝ) * (5 / 12) - 1 / 12 - (5 / 12) * a ≤ 0 := by
    nlinarith
  rw [mwσ, max_eq_left]
  exact le_trans (min_le_right _ _) hnonpos

/-- Exact lower-branch formula for the zero-continuation leader objective at
the state used by the strong-concavity obstruction. -/
theorem coupledLeaderObj_zero_zero_low {a : ℝ}
    (haI : a ∈ Sanctions.I) (ha : a ≤ 37 / 40) :
    coupledLeaderObj 0 0 (5 / 12) a =
      -37 / 1152 + (35 / 576) * a - (29 / 24) * a ^ 2 := by
  rw [coupledLeaderObj_zero_zero, coupled_mwσ_five_twelfths_of_le haI ha]
  unfold mwU_T
  ring

/-- Exact upper-branch formula for the zero-continuation leader objective at
the state used by the strong-concavity obstruction. -/
theorem coupledLeaderObj_zero_zero_high {a : ℝ} (ha : 37 / 40 ≤ a) :
    coupledLeaderObj 0 0 (5 / 12) a = -a ^ 2 - a / 6 := by
  rw [coupledLeaderObj_zero_zero, coupled_mwσ_five_twelfths_of_ge ha]
  unfold mwU_T
  ring

/-- Although global strong concavity is false, the same zero-continuation
objective has a valid modulus-one quadratic-growth bound at its actual
maximizer `35/1392`. This is deliberately local to the exhibited carrier pair
and state; it does not assert the carrier-uniform replacement needed by the
coupled Perov capstone. -/
theorem coupledLeaderObj_zero_zero_quadratic_growth {a : ℝ}
    (haI : a ∈ Sanctions.I) :
    (a - 35 / 1392) ^ 2 ≤
      coupledLeaderObj 0 0 (5 / 12) (35 / 1392) -
        coupledLeaderObj 0 0 (5 / 12) a := by
  have ha0I : (35 / 1392 : ℝ) ∈ Sanctions.I := by
    constructor <;> norm_num
  have ha0low : (35 / 1392 : ℝ) ≤ 37 / 40 := by norm_num
  rw [coupledLeaderObj_zero_zero_low ha0I ha0low]
  by_cases ha : a ≤ 37 / 40
  · rw [coupledLeaderObj_zero_zero_low haI ha]
    nlinarith [sq_nonneg (a - 35 / 1392)]
  · have hhigh : 37 / 40 ≤ a := by linarith
    rw [coupledLeaderObj_zero_zero_high hhigh]
    rcases haI with ⟨ha_nonneg, ha_one⟩
    nlinarith [sq_nonneg (a - 37 / 40)]

/-- The actual maximizer at the counterexample pair is unique despite the
failure of global strong concavity. The second conjunct gives the strict
comparison against every other feasible Target action. -/
theorem coupledLeaderObj_zero_zero_unique_max :
    IsMaxOn (fun a => coupledLeaderObj 0 0 (5 / 12) a)
        Sanctions.I (35 / 1392) ∧
      ∀ a ∈ Sanctions.I, a ≠ 35 / 1392 →
        coupledLeaderObj 0 0 (5 / 12) a <
          coupledLeaderObj 0 0 (5 / 12) (35 / 1392) := by
  constructor
  · rw [isMaxOn_iff]
    intro a ha
    have h := coupledLeaderObj_zero_zero_quadratic_growth ha
    nlinarith [sq_nonneg (a - 35 / 1392)]
  · intro a ha hne
    have h := coupledLeaderObj_zero_zero_quadratic_growth ha
    have hsq : 0 < (a - 35 / 1392) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    linarith

/-- **Optional low-δ specialization of the symbolic two-coordinate
leader-policy sensitivity theorem.**
`|lead(V_T,V_S)(x) − lead(V_T',W_S)(x)|
  ≤ L_leadT·dist V_T V_T' + L_leadS·dist V_S W_S`,
with `L_leadT = 2880/37877` and
`L_leadS = 467033055680/7762983835019`.  Leader strong concavity is **not**
required.  Instead, each realized policy satisfies the weaker quadratic-growth
inequality `(1/2)|a-lead|² ≤ objective(lead)-objective(a)` on `I`.  Adding the
two growth inequalities and applying the channel-split objective-difference
bound yields the policy estimate. The general theorem with symbolic growth
and chord moduli is
`argmax_lipschitz_two_coordinates_of_quadraticGrowth` in `Foundations`; the
fractions here are witness checks rather than primitive assumptions. -/
theorem coupled_lead_lipschitz
    (lead : SBCF → SBCF → ℝ → ℝ)
    (V_T V_S V_T' W_S : SBCF) (x : ↥(Sanctions.S : Set ℝ))
    (hmemV : lead V_T V_S x.val ∈ Sanctions.I)
    (hmemW : lead V_T' W_S x.val ∈ Sanctions.I)
    (growthV : ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T V_S x.val) ^ 2
        ≤ coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T V_S x.val a)
    (growthW : ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T' W_S x.val) ^ 2
        ≤ coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val a)
    (hod : |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37877) * dist V_T V_T'
            + (467033055680 / 7762983835019) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|) :
    |lead V_T V_S x.val - lead V_T' W_S x.val|
      ≤ (2880 / 37877) * dist V_T V_T'
        + (467033055680 / 7762983835019) * dist V_S W_S := by
  have h := Sanctions.argmax_lipschitz_two_coordinates_of_quadraticGrowth
    (objective := fun VT VS a => coupledLeaderObj VT VS x.val a)
    (select := fun VT VS => lead VT VS x.val)
    (q := 1 / 2)
    (Lx := 2880 / 37877)
    (Ly := 467033055680 / 7762983835019)
    (by norm_num) (by positivity) (by positivity)
    V_T V_T' V_S W_S hmemV hmemW growthV growthW hod
  norm_num at h
  exact h

/-- Quadratic growth at a realized policy implies its Rule-1 `IsMaxOn`
condition. -/
theorem coupled_isMaxOn_of_quadraticGrowth
    (lead : SBCF → SBCF → ℝ → ℝ)
    (V_T V_S : SBCF) (x : ↥(Sanctions.S : Set ℝ))
    (growth : ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T V_S x.val) ^ 2
        ≤ coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T V_S x.val a) :
    IsMaxOn (fun a => coupledLeaderObj V_T V_S x.val a)
      Sanctions.I (lead V_T V_S x.val) := by
  rw [isMaxOn_iff]
  intro a ha
  have h := growth a ha
  have hsq : 0 ≤ (1 / 2 : ℝ) * (a - lead V_T V_S x.val) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

/-- **`coupled_L_ST`: the Sender ROW at the witness — cross constant
`L_ST = 2880/37877 > 0`, diagonal `b_S,row = β_S + L_Ua·(2/c_T)·L_leadS
= 8697049946379/15525967670038`.**  Value channel: the shocked Sender Bellman
operator is a `β_S = 1/2` contraction in its own continuation
(`bellmanS_shock_pointwise_dist`).  Policy channel: `U_S` is action-Lipschitz
with `L_Ua = 1` (proved: `∂U_S/∂a = 1 − s/2` on `s ∈ [0,1]`), so the operator
moves by at most the leader-policy shift, bounded by the supplied two-sided
policy bound `hpol` (discharged upstream by `coupled_lead_lipschitz`). -/
theorem coupled_L_ST
    (α₁ α₂ : ℝ → ℝ) (hα₁ : Continuous α₁) (hα₂ : Continuous α₂)
    (V_T V_S V_T' W_S : SBCF)
    (hpol : ∀ x : ↥(Sanctions.S : Set ℝ), |α₁ x.val - α₂ x.val|
      ≤ (2880 / 37877) * dist V_T V_T'
        + (467033055680 / 7762983835019) * dist V_S W_S) :
    dist (lowDeltaShocked.bellmanS_shock α₁ hα₁ V_S)
      (lowDeltaShocked.bellmanS_shock α₂ hα₂ W_S)
      ≤ (2880 / 37877) * dist V_T V_T'
        + (8697049946379 / 15525967670038) * dist V_S W_S := by
  have hC0 : (0 : ℝ) ≤ (2880 / 37877) * dist V_T V_T'
      + (8697049946379 / 15525967670038) * dist V_S W_S := by
    have h1 := dist_nonneg (x := V_T) (y := V_T')
    have h2 := dist_nonneg (x := V_S) (y := W_S)
    positivity
  rw [BoundedContinuousFunction.dist_le hC0]
  intro x
  -- value channel at the fixed policy α₁
  have h1 : dist (lowDeltaShocked.bellmanS_shock α₁ hα₁ V_S x)
      (lowDeltaShocked.bellmanS_shock α₁ hα₁ W_S x)
      ≤ (1 / 2) * dist V_S W_S := by
    have h := lowDeltaShocked.bellmanS_shock_pointwise_dist hα₁ V_S W_S x
    have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
    rwa [hβ] at h
  -- policy channel at the fixed value W_S
  have h2 : dist (lowDeltaShocked.bellmanS_shock α₁ hα₁ W_S x)
      (lowDeltaShocked.bellmanS_shock α₂ hα₂ W_S x)
      ≤ |α₁ x.val - α₂ x.val| := by
    rw [Real.dist_eq]
    refine lowDeltaShocked.toParams.bellmanS_BCF_policy_pointwise_dist α₁ α₂
      hα₁ hα₂ (lowDeltaShocked.smear W_S) x _ ?_
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hkey : lowDeltaShocked.toParams.U_S x.val (α₁ x.val) s
        - lowDeltaShocked.toParams.U_S x.val (α₂ x.val) s
        = (α₁ x.val - α₂ x.val) * (1 - s / 2) := by
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S, mwU_S]; ring
    rw [hkey, abs_mul]
    have habs : |1 - s / 2| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s / 2)]; linarith
    nlinarith [habs, abs_nonneg (α₁ x.val - α₂ x.val)]
  have h3 := hpol x
  have htri := dist_triangle (lowDeltaShocked.bellmanS_shock α₁ hα₁ V_S x)
    (lowDeltaShocked.bellmanS_shock α₁ hα₁ W_S x)
    (lowDeltaShocked.bellmanS_shock α₂ hα₂ W_S x)
  linarith [h1, h2, h3, htri]

/-! ## §5 Exact Schur margin, both κ_a conventions, and row-sum failure -/

/-- Chain identity: `L_TS = (L_UT + β_T·(M_T/h)·δ)·Lσ = 1280/5411`. -/
theorem coupled_L_TS_eq :
    ((1 : ℝ) + 9 / 10 * 200 * (1 / 100)) * (3200 / 37877) = 1280 / 5411 := by
  norm_num

/-- **Strict positivity of the Target-row cross channel**: `L_TS > 0`. -/
theorem coupled_L_TS_pos : (0 : ℝ) < 1280 / 5411 := by norm_num

/-- Chain identity: `L_ST = κ_a·β_T·δ·(1/h) = 2880/37877` (repo factor-2
argmax-core `κ_a = 32000/37877`). -/
theorem coupled_L_ST_eq :
    ((32000 : ℝ) / 37877) * (9 / 10) * (1 / 100) * 10 = 2880 / 37877 := by
  norm_num

/-- **Strict positivity of the Sender-row cross channel**: `L_ST > 0`. -/
theorem coupled_L_ST_pos : (0 : ℝ) < 2880 / 37877 := by norm_num

/-- Chain identity: the Sender row diagonal
`b_S,row = β_S + L_Ua·(2/c_T)·L_leadS = 1/2 + 467033055680/7762983835019
= 8697049946379/15525967670038`. -/
theorem coupled_b_S_row_eq :
    (1 : ℝ) / 2 + 467033055680 / 7762983835019
      = 8697049946379 / 15525967670038 := by
  norm_num

/-- Exact product: `L_TS·L_ST = 3686400/204952447`. -/
theorem coupledSchur_lhs_eq :
    (1280 / 5411 : ℝ) * (2880 / 37877) = 3686400 / 204952447 := by
  norm_num

/-- **The exact Schur margin (ROBUST repo factor-2 κ_a convention)**:
`L_TS·L_ST < (1 − β_T)(1 − b_S,row)`.  This is the load-bearing inequality
the Perov capstone consumes — the two-sided coupling contracts spectrally
even though the Target row-sum exceeds 1. -/
theorem coupledSchur_margin_robust :
    (1280 / 5411 : ℝ) * (2880 / 37877)
      < (1 - 9 / 10) * (1 - 8697049946379 / 15525967670038) := by
  norm_num

/-- Exact robust Schur slack: `+4036322267659/155259676700380 ≈ +0.026`. -/
theorem coupledSchur_margin_robust_exact :
    (1 - (9 : ℝ) / 10) * (1 - 8697049946379 / 15525967670038)
        - (1280 / 5411) * (2880 / 37877)
      = 4036322267659 / 155259676700380 := by
  norm_num

/-- **The favorable (IFT-form, κ_a halved) Schur margin variant**:
`L_ST = 1440/37877` and
`b_S,row = 1/2 + (T1 + T2S/2 + T3)` — the margin is even wider
(`≈ +0.0356`). -/
theorem coupledSchur_margin_favorable :
    (1280 / 5411 : ℝ) * (1440 / 37877)
      < (1 - 9 / 10)
        * (1 - (1 / 2 + 1600 / 37877 + 9216000 / 1434667129
                  + 39373588480 / 7762983835019)) := by
  norm_num

/-- Exact favorable Schur slack: `+5532355547659/155259676700380 ≈ +0.0356`. -/
theorem coupledSchur_margin_favorable_exact :
    (1 - (9 : ℝ) / 10)
        * (1 - (1 / 2 + 1600 / 37877 + 9216000 / 1434667129
                  + 39373588480 / 7762983835019))
        - (1280 / 5411) * (1440 / 37877)
      = 5532355547659 / 155259676700380 := by
  norm_num

/-- **Split-consistency identity**: the two-sided Schur margin equals
`(1 − β_T)` times the slaved C4 contraction slack at the repo κ_a
(`L_lead = 1863330783680/7762983835019`, `lowDelta_window_C4_robust`) —
the exact algebraic certificate that the two-sided channel split
`L_lead = L_leadS + L_leadT·L_VT` reproduces the certified slaved chain. -/
theorem coupledSchur_margin_eq_slaved_slack :
    (1 - (9 : ℝ) / 10) * (1 - 8697049946379 / 15525967670038)
        - (1280 / 5411) * (2880 / 37877)
      = (1 - 9 / 10) * (1 / 2 - 1863330783680 / 7762983835019) := by
  norm_num

/-- **The legacy row-sum route FAILS at this economy**: the Target row sum is
`β_T + L_TS = 61499/54110 ≈ 1.1366 ≥ 1`, so the row-sum certificate
(`exists_fixedPoint_in_carrier`, `JointMPE`-form) cannot certify this
packet. Any contraction proof using these row constants would therefore have
to use the Schur/Perov form, but the matrix arithmetic alone does not discharge
its objective-geometry and carrier-invariance premises.  (Exact fraction per
the adversarial verification; the claim file's `61379/54110` was a typo.) -/
theorem coupled_rowSum_fails :
    (9 : ℝ) / 10 + 1280 / 5411 = 61499 / 54110 ∧
      (1 : ℝ) < 9 / 10 + 1280 / 5411 := by
  constructor <;> norm_num

/-! ## §6 The joint two-sided shocked operator and the Perov capstones — retired

The joint two-sided shocked operator `coupledJointOp` and the two conditional
capstones stated over it are kept below as commented audit evidence; none of
them enters the Lean environment.  See the retirement notes inside the block. -/

/- Retired numerical equilibrium wrappers (2026-07-27, user-approved).
The historical declarations are kept as commented audit evidence below; they
no longer enter the Lean environment.  They embedded witness fractions in
quadratic-growth and objective-difference hypotheses of uniqueness and
existence statements.  The sole equilibrium-facing replacement is the
symbolic canonical local-Perov theorem in
`Theory/Shocked/ValidatedLocalCoupledEquilibriumOnCarriers.lean`.

2026-10-06 (round BG3.9): the operator `coupledJointOp` joined this block.
Its Target-invariance premise `h_invT` is false.  Instantiated at the zero
continuation pair, which lies in both carriers, it contradicts
`coupledZeroPair_target_image_not_mem`: the term
`coupledZeroPair_target_image_not_mem
  (h_invT 0 zero_mem_coupledCarrierT 0 zero_mem_coupledCarrierS)`
proves `False`.  Every use of the operator must supply that premise, so every
statement about it is a vacuous conditional; its only consumers were the two
wrappers retired below.  The same disposition, with the new refutation
`coupledJointOpWide_h_invT_contradictory`, applies to the enlarged operator in
`Examples/EpsilonIsolationWitness.lean`.  Rule 22: this is a witness-specific
object of the low-δ economy, not a general-`F` statement.

/-- **The joint two-sided shocked Bellman operator on the carrier product.**
Target coordinate: the shocked Target Bellman operator at the continuous
state-clamped extension of `σ_dyn_top (smear V_S)`, applied to the
own-continuation `V_T`
(genuinely two-sided: `V_S` enters the Target row).  Sender coordinate: the
shocked Sender Bellman operator at the two-sided leader policy
`lead V_T V_S` applied to `V_S` (genuinely two-sided: `V_T` enters the Sender
row through the leader policy — the κ_a channel).  Carrier invariance is
consumed (`h_invT`, `h_invS` — the shocked counterpart of
`ValueClass2.IsInvariant`). -/
noncomputable def coupledJointOp
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (h_invT : ∀ V_T ∈ coupledCarrierT, ∀ V_S, ∀ hS : V_S ∈ coupledCarrierS,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear V_S))
        (coupled_sigmaDynTop_clamped_continuous V_S hS) V_T ∈ coupledCarrierT)
    (h_invS : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS)
    (z : ↥coupledCarrierT × ↥coupledCarrierS) :
    ↥coupledCarrierT × ↥coupledCarrierS :=
  (⟨lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear z.2.val))
      (coupled_sigmaDynTop_clamped_continuous z.2.val z.2.property) z.1.val,
    h_invT z.1.val z.1.property z.2.val z.2.property⟩,
   ⟨lowDeltaShocked.bellmanS_shock (lead z.1.val z.2.val)
      (lead_cont z.1.val z.2.val) z.2.val,
    h_invS z.1.val z.1.property z.2.val z.2.property⟩)

/-- **Conditional template (currently uninstantiable): within-carrier
uniqueness via the Perov fixed point.** If its analytic premises hold, the
joint two-sided shocked Bellman operator has EXACTLY ONE fixed
point in the carrier product — Perov's 2×2 contraction principle
(`perov2_existsUnique_fixedPoint`) at the certified matrix
`[[9/10, 1280/5411], [2880/37877, 8697049946379/15525967670038]]`, whose
Schur margin `coupledSchur_margin_robust` holds while the Target ROW SUM
exceeds 1 (`coupled_rowSum_fails`). Numeric surface: fully discharged by
`norm_num`. Consumed analytic
package: two-sided leader family (`lead`, `lead_cont`, `lead_mem`),
carrier-uniform Target quadratic growth `growth_T`, the
two-sided channel-split Stackelberg-coupling regularity `h_obj_diff` at the
pinned constants, and carrier invariance `h_invT`, `h_invS`.  Sender strong
concavity is now proved by `coupled_sender_strongConcave`; Rule-1 Target
optimality is implied by `growth_T`. -/
theorem coupledSchur_unique_in_carrier
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S, lead V_T V_S x ∈ Sanctions.I)
    (growth_T : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T V_S x.val) ^ 2
        ≤ coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T V_S x.val a)
    (h_obj_diff : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      ∀ V_T' ∈ coupledCarrierT, ∀ W_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37877) * dist V_T V_T'
            + (467033055680 / 7762983835019) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|)
    (h_invT : ∀ V_T ∈ coupledCarrierT, ∀ V_S, ∀ hS : V_S ∈ coupledCarrierS,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear V_S))
        (coupled_sigmaDynTop_clamped_continuous V_S hS) V_T ∈ coupledCarrierT)
    (h_invS : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS) :
    ∃! z : ↥coupledCarrierT × ↥coupledCarrierS,
      coupledJointOp lead lead_cont h_invT h_invS z = z := by
  have hσc : ∀ V_S : ↥coupledCarrierS,
      Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        lowDeltaShocked.toParams.σ_dyn_top
          (lowDeltaShocked.smear V_S.val) xa.1.val xa.2) :=
    fun V_S =>
      coupled_sigmaDynTop_continuous_subtype V_S.val V_S.property
  let lead' : ↥coupledCarrierT → ↥coupledCarrierS → ℝ → ℝ :=
    fun V_T V_S => lead V_T.val V_S.val
  have lead'_cont : ∀ V_T V_S, Continuous (lead' V_T V_S) :=
    fun V_T V_S => lead_cont V_T.val V_S.val
  have hInvT' : ∀ (V_T : ↥coupledCarrierT) (V_S : ↥coupledCarrierS),
      lowDeltaShocked.coupledTargetBCF hσc V_T V_S ∈ coupledCarrierT := by
    intro V_T V_S
    simpa only [AbstractGame.ShockedParams.coupledTargetBCF] using
      h_invT V_T.val V_T.property V_S.val V_S.property
  have hInvS' : ∀ (V_T : ↥coupledCarrierT) (V_S : ↥coupledCarrierS),
      lowDeltaShocked.coupledSenderBCF lead' lead'_cont V_T V_S
        ∈ coupledCarrierS := by
    intro V_T V_S
    simpa only [AbstractGame.ShockedParams.coupledSenderBCF, lead'] using
      h_invS V_T.val V_T.property V_S.val V_S.property
  have hop :
      lowDeltaShocked.coupledJointOp hσc lead' lead'_cont hInvT' hInvS'
        = coupledJointOp lead lead_cont h_invT h_invS := by
    funext z
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  have hrowT : ∀ z z',
      dist
          (lowDeltaShocked.coupledJointOp
            hσc lead' lead'_cont hInvT' hInvS' z).1
          (lowDeltaShocked.coupledJointOp
            hσc lead' lead'_cont hInvT' hInvS' z').1
        ≤ (9 / 10) * dist z.1 z'.1 + (1280 / 5411) * dist z.2 z'.2 := by
    intro z z'
    have h := coupled_L_TS z.1.val z'.1.val z.2.val z'.2.val
      z'.1.property.1 z.2.property z'.2.property
    rw [hop]
    simpa only [Subtype.dist_eq] using h
  have hrowS : ∀ z z',
      dist
          (lowDeltaShocked.coupledJointOp
            hσc lead' lead'_cont hInvT' hInvS' z).2
          (lowDeltaShocked.coupledJointOp
            hσc lead' lead'_cont hInvT' hInvS' z').2
        ≤ (2880 / 37877) * dist z.1 z'.1
          + (8697049946379 / 15525967670038) * dist z.2 z'.2 := by
    intro z z'
    rw [hop]
    have hpol : ∀ x : ↥(Sanctions.S : Set ℝ),
        |lead z.1.val z.2.val x.val - lead z'.1.val z'.2.val x.val|
          ≤ (2880 / 37877) * dist z.1.val z'.1.val
            + (467033055680 / 7762983835019) * dist z.2.val z'.2.val :=
      fun x => coupled_lead_lipschitz lead z.1.val z.2.val
        z'.1.val z'.2.val x
        (lead_mem z.1.val z.2.val x.val x.property)
        (lead_mem z'.1.val z'.2.val x.val x.property)
        (growth_T z.1.val z.1.property z.2.val z.2.property x)
        (growth_T z'.1.val z'.1.property z'.2.val z'.2.property x)
        (h_obj_diff z.1.val z.1.property z.2.val z.2.property
          z'.1.val z'.1.property z'.2.val z'.2.property x)
    have h := coupled_L_ST
      (lead z.1.val z.2.val) (lead z'.1.val z'.2.val)
      (lead_cont z.1.val z.2.val) (lead_cont z'.1.val z'.2.val)
      z.1.val z.2.val z'.1.val z'.2.val hpol
    simpa only [Subtype.dist_eq] using h
  have hfp :=
    lowDeltaShocked.coupledShocked_existsUnique_fixedPoint_conditional
      coupledCarrierT_isClosed coupledCarrierS_isClosed
      coupledCarrierT_nonempty coupledCarrierS_nonempty
      hσc lead' lead'_cont hInvT' hInvS'
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hrowT hrowS (by norm_num) (by norm_num)
      coupledSchur_margin_robust
  simpa only [hop] using hfp

/-- **Conditional template (currently uninstantiable): a two-sided-coupled
shocked feedback-Stackelberg TOP equilibrium.** If its analytic premises hold,
the Perov fixed point of the joint two-sided
operator is packaged as a `ShockedFeedbackStackelbergEquilibriumTop`: the
Sender value solves the shocked Sender Bellman equation at the two-sided
leader policy `lead V_T V_S`; the Target coordinate is identified with the
state-local slaved shocked Target value `V_T_dyn_shock_local V_S`
(uniqueness of the
`β_T`-contraction fixed point), which yields the shocked Target Bellman
equation; the leader policy is the argmax of the REAL shocked Target
integrand (implied by `growth_T`, Rule-1).  Both values lie in the carriers and the
equilibrium policy is exactly `lead E.V_T E.V_S`.  Same consumed analytic
package as `coupledSchur_unique_in_carrier` (see its docstring and the file
header); everything numeric is `norm_num`-discharged.  Honest scope: coupled
existence + in-carrier uniqueness only — no three-goals claim (the `hIDO_on`
realized-α channel stays open at this economy). -/
theorem coupledSchur_exists_equilibrium
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S, lead V_T V_S x ∈ Sanctions.I)
    (growth_T : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T V_S x.val) ^ 2
        ≤ coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T V_S x.val a)
    (h_obj_diff : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      ∀ V_T' ∈ coupledCarrierT, ∀ W_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37877) * dist V_T V_T'
            + (467033055680 / 7762983835019) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|)
    (h_invT : ∀ V_T ∈ coupledCarrierT, ∀ V_S, ∀ hS : V_S ∈ coupledCarrierS,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear V_S))
        (coupled_sigmaDynTop_clamped_continuous V_S hS) V_T ∈ coupledCarrierT)
    (h_invS : ∀ V_T ∈ coupledCarrierT, ∀ V_S ∈ coupledCarrierS,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS) :
    ∃ E : lowDeltaShocked.ShockedFeedbackStackelbergEquilibriumTop,
      E.V_T ∈ coupledCarrierT ∧ E.V_S ∈ coupledCarrierS
        ∧ E.α = lead E.V_T E.V_S := by
  obtain ⟨z, hz, -⟩ := coupledSchur_unique_in_carrier lead lead_cont lead_mem
    growth_T h_obj_diff h_invT h_invS
  have hz_T : lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear z.2.val))
      (coupled_sigmaDynTop_clamped_continuous z.2.val z.2.property)
      z.1.val = z.1.val :=
    congrArg (fun w : ↥coupledCarrierT × ↥coupledCarrierS => w.1.val) hz
  have hz_S : lowDeltaShocked.bellmanS_shock (lead z.1.val z.2.val)
      (lead_cont z.1.val z.2.val) z.2.val = z.2.val :=
    congrArg (fun w : ↥coupledCarrierT × ↥coupledCarrierS => w.2.val) hz
  -- Identify the Target coordinate with the slaved shocked Target value
  -- (uniqueness of the β_T-contraction fixed point).
  have hfix2 : lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear z.2.val))
      (coupled_sigmaDynTop_clamped_continuous z.2.val z.2.property)
      (lowDeltaShocked.V_T_dyn_shock_local z.2.val
        (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property))
      = lowDeltaShocked.V_T_dyn_shock_local z.2.val
        (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property) := by
    simpa only [Sanctions.AbstractGame.ShockedParams.V_T_dyn_shock_local] using
      lowDeltaShocked.targetDynValue_shock_isFixedPoint
        (lowDeltaShocked.toParams.σ_dyn_top_clamped
          (lowDeltaShocked.smear z.2.val))
        (coupled_sigmaDynTop_clamped_continuous z.2.val z.2.property)
  have hcontr := lowDeltaShocked.targetDynBCF_shock_dist_le
    (lowDeltaShocked.toParams.σ_dyn_top_clamped (lowDeltaShocked.smear z.2.val))
    (coupled_sigmaDynTop_clamped_continuous z.2.val z.2.property) z.1.val
    (lowDeltaShocked.V_T_dyn_shock_local z.2.val
      (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property))
  rw [hz_T, hfix2] at hcontr
  have hβ : lowDeltaShocked.toParams.β_T = 9 / 10 := rfl
  rw [hβ] at hcontr
  have hd0 : dist z.1.val
      (lowDeltaShocked.V_T_dyn_shock_local z.2.val
        (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property)) = 0 := by
    have hnn := dist_nonneg (x := z.1.val)
      (y := lowDeltaShocked.V_T_dyn_shock_local z.2.val
        (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property))
    linarith
  have hVT_eq : z.1.val = lowDeltaShocked.V_T_dyn_shock_local z.2.val
      (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property) := by
    rwa [dist_eq_zero] at hd0
  refine ⟨{ V_T := z.1.val
            V_S := z.2.val
            α := lead z.1.val z.2.val
            hα := lead_cont z.1.val z.2.val
            α_mem := fun x hx => lead_mem z.1.val z.2.val x hx
            V_S_fix_shock := hz_S.symm
            V_T_fix_shock := ?_
            α_opt_shock := ?_ }, z.1.property, z.2.property, rfl⟩
  · intro x
    rw [hVT_eq]
    exact lowDeltaShocked.V_T_dyn_shock_local_bellman_eq z.2.val
      (coupled_sigmaDynTop_continuous_subtype z.2.val z.2.property) x
  · intro x hx
    exact coupled_isMaxOn_of_quadraticGrowth lead z.1.val z.2.val ⟨x, hx⟩
      (growth_T z.1.val z.1.property z.2.val z.2.property ⟨x, hx⟩)
-/

/-! The exact two-row constants, their Schur margin, the row-sum failure, and
the numerical selector corollary remain diagnostic facts.  They no longer
support a numerical conditional existence or uniqueness declaration.  A
future low-adjustment equilibrium corollary must instantiate the symbolic
canonical theorem from derived optimal-policy, local-row, residual, and
carrier certificates. -/

end Examples

end -- noncomputable section

end Sanctions
