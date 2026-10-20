/-
Sanctions/Examples/CoupledRoute/CoupledObjectiveDifference.lean

Exact assumption-preserving progress on the coupled leader
objective-difference estimate.  The file proves the action modulus of the
realized Sender selector and, from it, the complete Target-continuation-value
channel at `2880 / 37877`.

The Sender-continuation mixed channel is then tested disprove-first.  An
explicit pair in the current carriers violates the advertised uniform
all-actions modulus.  This refutes that route to the conditional capstone; it
does not independently refute the capstone's literal realized-leader-only
hypothesis, which is already entangled with the separately refuted
carrier-uniform Target-growth package.
-/

import Sanctions.Examples.CoupledRoute.CoupledFrontierCounterexamples
import Sanctions.Theory.Bellman.InvariantLipBall

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction
open MeasureTheory intervalIntegral
open scoped NNReal
open AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-- For every `K_S`-Lipschitz Sender value, the realized dynamic Sender response
is `32000 / 37877`-Lipschitz in the Target action.  Witness-specific
(Rule 22): the low-δ economy, not a general-`F` statement.  Only the Lipschitz
half of Sender-carrier membership is assumed; the norm half is dropped. -/
theorem coupled_sigmaDynTop_action_lipschitz
    (V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (x : ℝ) (hx : x ∈ Sanctions.S) (a b : ℝ) :
    |lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x a
      - lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x b|
      ≤ (32000 / 37877) * |a - b| := by
  let f : ℝ → ℝ := fun s => lowDeltaShocked.toParams.U_S x a s
    + lowDeltaShocked.toParams.β_S * (lowDeltaShocked.smear V_S)
      (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))
  let g : ℝ → ℝ := fun s => lowDeltaShocked.toParams.U_S x b s
    + lowDeltaShocked.toParams.β_S * (lowDeltaShocked.smear V_S)
      (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))
  let σa := lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x a
  let σb := lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x b
  have hσa_mem : σa ∈ Sanctions.I :=
    lowDeltaShocked.toParams.σ_dyn_top_mem_I (lowDeltaShocked.smear V_S) x a
  have hσb_mem : σb ∈ Sanctions.I :=
    lowDeltaShocked.toParams.σ_dyn_top_mem_I (lowDeltaShocked.smear V_S) x b
  have hfmax : ∀ y ∈ Sanctions.I, f y ≤ f σa :=
    fun y hy => lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
      (lowDeltaShocked.smear V_S) x a hy
  have hgmax : ∀ y ∈ Sanctions.I, g y ≤ g σb :=
    fun y hy => lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
      (lowDeltaShocked.smear V_S) x b hy
  have hL0 : 0 ≤ (1 / 2 : ℝ) * |a - b| := by positivity
  have hdiff : |(f σa - g σa) - (f σb - g σb)|
      ≤ ((1 / 2 : ℝ) * |a - b|) * |σa - σb| := by
    dsimp only [f, g]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S, mwU_S]
    ring_nf
    have heq : a * σa * (-1 / 2) + a * σb * (1 / 2)
        + σa * b * (1 / 2) + b * σb * (-1 / 2)
        = (1 / 2 : ℝ) * (b - a) * (σa - σb) := by
      ring
    rw [heq, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [abs_sub_comm a b]
    ring_nf
    exact le_rfl
  have hcore := Sanctions.argmax_lipschitz_of_strongConcave_lipschitzDiff
    hL0 (convex_Icc 0 1)
    (coupled_sender_strongConcave V_S hV_S x hx a)
    (coupled_sender_strongConcave V_S hV_S x hx b)
    hσa_mem hσb_mem hfmax hgmax hdiff
  have hgen : |σa - σb| ≤ (2 / (37877 / 32000 : ℝ))
      * ((1 / 2 : ℝ) * |a - b|) := by
    rw [div_mul_eq_mul_div,
      le_div_iff₀ (show (0 : ℝ) < 37877 / 32000 by norm_num)]
    nlinarith [hcore]
  dsimp only [σa, σb] at hgen ⊢
  convert hgen using 1
  ring

/-- The Target-value channel of the coupled leader-objective difference has
the exact action modulus `2880 / 37877`, for every `K_S`-Lipschitz Sender
value.  Witness-specific (Rule 22).  Only the Lipschitz half of Sender-carrier
membership is assumed; the norm half is dropped. -/
theorem coupledLeaderObj_diff_lip_in_VT
    (V_T V_T' V_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (x : ↥(Sanctions.S : Set ℝ)) (a b : ℝ) :
    |(coupledLeaderObj V_T V_S x.val a
          - coupledLeaderObj V_T' V_S x.val a)
      - (coupledLeaderObj V_T V_S x.val b
          - coupledLeaderObj V_T' V_S x.val b)|
      ≤ ((2880 / 37877) * dist V_T V_T') * |a - b| := by
  let σa := lowDeltaShocked.toParams.σ_dyn_top
    (lowDeltaShocked.smear V_S) x.val a
  let σb := lowDeltaShocked.toParams.σ_dyn_top
    (lowDeltaShocked.smear V_S) x.val b
  let za := Sanctions.clipS' (lowDeltaShocked.toParams.F x.val σa)
  let zb := Sanctions.clipS' (lowDeltaShocked.toParams.F x.val σb)
  have hσ : |σa - σb| ≤ (32000 / 37877) * |a - b| :=
    coupled_sigmaDynTop_action_lipschitz V_S hV_S x.val x.property a b
  have hz : dist za zb
      ≤ (1 / 100) * ((32000 / 37877) * |a - b|) := by
    calc
      dist za zb = |za.val - zb.val| := by
        rw [Subtype.dist_eq, Real.dist_eq]
      _ ≤ (1 / 100) * |σa - σb| :=
        lowDelta_clipF_lip x.val σa σb
      _ ≤ (1 / 100) * ((32000 / 37877) * |a - b|) :=
        mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hsm0 := lowDelta_smear_creation_lip (V_T - V_T') za zb
  have hsm : |lowDeltaShocked.smear (V_T - V_T') za
        - lowDeltaShocked.smear (V_T - V_T') zb|
      ≤ 10 * dist V_T V_T'
          * ((1 / 100) * ((32000 / 37877) * |a - b|)) := by
    calc
      |lowDeltaShocked.smear (V_T - V_T') za
          - lowDeltaShocked.smear (V_T - V_T') zb|
          ≤ 10 * ‖V_T - V_T'‖ * dist za zb := hsm0
      _ ≤ 10 * ‖V_T - V_T'‖
          * ((1 / 100) * ((32000 / 37877) * |a - b|)) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      _ = 10 * dist V_T V_T'
          * ((1 / 100) * ((32000 / 37877) * |a - b|)) := by
        rw [dist_eq_norm]
  have hsub : lowDeltaShocked.smear (V_T - V_T') =
      lowDeltaShocked.smear V_T - lowDeltaShocked.smear V_T' := by
    simpa [lowDeltaShocked] using
      (AbstractGame.movAvgShockedParams_smear_sub
        lowDeltaParams lowDeltaH_pos V_T V_T')
  have hpoint (c : ℝ) :
      coupledLeaderObj V_T V_S x.val c
          - coupledLeaderObj V_T' V_S x.val c
        = lowDeltaShocked.toParams.β_T
          * lowDeltaShocked.smear (V_T - V_T')
            (Sanctions.clipS' (lowDeltaShocked.toParams.F x.val
              (lowDeltaShocked.toParams.σ_dyn_top
                (lowDeltaShocked.smear V_S) x.val c))) := by
    simp only [coupledLeaderObj,
      AbstractGame.Params.joint_T_top_integrand]
    have heval : lowDeltaShocked.smear V_T
          (Sanctions.clipS' (lowDeltaShocked.toParams.F x.val
            (lowDeltaShocked.toParams.σ_dyn_top
              (lowDeltaShocked.smear V_S) x.val c)))
        - lowDeltaShocked.smear V_T'
          (Sanctions.clipS' (lowDeltaShocked.toParams.F x.val
            (lowDeltaShocked.toParams.σ_dyn_top
              (lowDeltaShocked.smear V_S) x.val c)))
        = lowDeltaShocked.smear (V_T - V_T')
          (Sanctions.clipS' (lowDeltaShocked.toParams.F x.val
            (lowDeltaShocked.toParams.σ_dyn_top
              (lowDeltaShocked.smear V_S) x.val c))) := by
      rw [hsub]
      rfl
    rw [← heval]
    ring
  rw [hpoint a, hpoint b, ← mul_sub, abs_mul,
    abs_of_nonneg lowDeltaShocked.toParams.β_T_mem.1]
  change (9 / 10 : ℝ)
      * |lowDeltaShocked.smear (V_T - V_T') za
        - lowDeltaShocked.smear (V_T - V_T') zb|
      ≤ ((2880 / 37877) * dist V_T V_T') * |a - b|
  calc
    (9 / 10 : ℝ)
        * |lowDeltaShocked.smear (V_T - V_T') za
          - lowDeltaShocked.smear (V_T - V_T') zb|
      ≤ (9 / 10) * (10 * dist V_T V_T'
          * ((1 / 100) * ((32000 / 37877) * |a - b|))) :=
        mul_le_mul_of_nonneg_left hsm (by norm_num)
    _ = ((2880 / 37877) * dist V_T V_T') * |a - b| := by
      ring

/-! ## The strongest one-box two-sided salvage on the redesigned carrier

The one-box kernel controls the *size* of the objective perturbation, but not
its mixed action--continuation modulus.  The first theorem below records the
exact pointwise size bound on the norm--Lipschitz Target carrier.  Combining
that bound with the quadratic-growth hypotheses already consumed by the
coupled capstone gives a squared (Hölder-`1/2`) realised-policy estimate.
Neither result asserts the stronger product-form objective-difference bound. -/

/-- For `K_S`-Lipschitz Sender values, the realised dynamic Sender response is
`3200 / 37877`-Lipschitz in the Sender continuation value.  Witness-specific
(Rule 22).  Only the Lipschitz half of Sender-carrier membership is assumed for
either value; the norm half is dropped. -/
theorem coupled_sigmaDynTop_value_lipschitz
    (V_S W_S : SBCF) (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (hW_S : ValueLipschitzWith W_S lowDeltaSenderCarrierLip)
    (x : ℝ) (hx : x ∈ Sanctions.S)
    (a : ℝ) :
    |lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x a
      - lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear W_S) x a|
      ≤ (3200 / 37877) * dist V_S W_S := by
  have h := Sanctions.AbstractGame.Params.sigma_top_lipschitz_in_V_pair
    (p := lowDeltaShocked.toParams) lowDeltaShocked.smear
    (Lκ := 10) (by norm_num)
    (AbstractGame.movAvgShockedParams_smear_sub lowDeltaParams lowDeltaH_pos)
    lowDelta_smear_creation_lip
    (c := 37877 / 32000) (by norm_num) x a V_S W_S
    (coupled_sender_strongConcave V_S hV_S x hx a)
    (coupled_sender_strongConcave W_S hW_S x hx a)
    (LF := 1 / 100) (by norm_num) (fun s s' => lowDelta_clipF_lip x s s')
  have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
  rw [hβ] at h
  linarith [h]

/-- **Uniform size of the two-sided leader-objective perturbation.**
At every feasible action, the Target-value channel has coefficient `9 / 10`
and the Sender-value channel has the exact coefficient
`43520000 / 283976393`.

Only the Lipschitz halves of the carrier memberships are assumed: `V_T'` is
`25683423000 / 283976393`-Lipschitz (the modulus of the redesigned Target
carrier `coupledCarrierTLip`, which lives in the downstream redesign module),
and `V_S`, `W_S` are `K_S`-Lipschitz.  The two norm bounds are dropped; they
were never used.  Witness-specific (Rule 22). -/
theorem coupledLeaderObj_pair_pointwise_bound_on_lip_carrier
    (V_T V_T' V_S W_S : SBCF)
    (hV_T' : ValueLipschitzWith V_T' (25683423000 / 283976393))
    (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (hW_S : ValueLipschitzWith W_S lowDeltaSenderCarrierLip)
    (x : ↥(Sanctions.S : Set ℝ)) (a : ℝ) (ha : a ∈ Sanctions.I) :
    |coupledLeaderObj V_T V_S x.val a - coupledLeaderObj V_T' W_S x.val a|
      ≤ (9 / 10) * dist V_T V_T'
        + (43520000 / 283976393) * dist V_S W_S := by
  let σV := lowDeltaShocked.toParams.σ_dyn_top
    (lowDeltaShocked.smear V_S) x.val a
  let σW := lowDeltaShocked.toParams.σ_dyn_top
    (lowDeltaShocked.smear W_S) x.val a
  let zV := Sanctions.clipS' (lowDeltaShocked.toParams.F x.val σV)
  let zW := Sanctions.clipS' (lowDeltaShocked.toParams.F x.val σW)
  have hσV_mem : σV ∈ Sanctions.I :=
    lowDeltaShocked.toParams.σ_dyn_top_mem_I (lowDeltaShocked.smear V_S) x.val a
  have hσW_mem : σW ∈ Sanctions.I :=
    lowDeltaShocked.toParams.σ_dyn_top_mem_I (lowDeltaShocked.smear W_S) x.val a
  have hσ : |σV - σW| ≤ (3200 / 37877) * dist V_S W_S := by
    dsimp only [σV, σW]
    exact coupled_sigmaDynTop_value_lipschitz V_S W_S hV_S hW_S
      x.val x.property a
  have hsmVT_lip : ∀ u v : ↥(Sanctions.S : Set ℝ),
      |lowDeltaShocked.smear V_T' v - lowDeltaShocked.smear V_T' u|
        ≤ (25683423000 / 283976393) * dist u v := by
    intro u v
    rw [lowDeltaShocked_smear]
    exact Sanctions.movAvgBCF_valueLipschitz lowDeltaH_pos V_T'
      (by norm_num) hV_T' u v
  have hz : dist zV zW ≤ (1 / 100) * |σV - σW| := by
    dsimp only [zV, zW]
    rw [Subtype.dist_eq, Real.dist_eq]
    exact lowDelta_clipF_lip x.val σV σW
  have hown :
      |coupledLeaderObj V_T V_S x.val a - coupledLeaderObj V_T' V_S x.val a|
        ≤ (9 / 10) * dist V_T V_T' := by
    have hmov : |lowDeltaShocked.smear V_T zV - lowDeltaShocked.smear V_T' zV|
        ≤ dist V_T V_T' := by
      rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
        Sanctions.movAvgBCF_apply]
      exact Sanctions.movAvg_dist_le lowDeltaH_pos V_T V_T' zV.val
    simp only [coupledLeaderObj, AbstractGame.Params.joint_T_top_integrand]
    change |(lowDeltaShocked.toParams.U_T x.val a σV
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T zV)
        - (lowDeltaShocked.toParams.U_T x.val a σV
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zV)|
      ≤ (9 / 10) * dist V_T V_T'
    rw [show (lowDeltaShocked.toParams.U_T x.val a σV
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T zV)
        - (lowDeltaShocked.toParams.U_T x.val a σV
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zV)
        = lowDeltaShocked.toParams.β_T
          * (lowDeltaShocked.smear V_T zV - lowDeltaShocked.smear V_T' zV) by
            ring,
      abs_mul, abs_of_nonneg lowDeltaShocked.toParams.β_T_mem.1]
    change (9 / 10 : ℝ)
        * |lowDeltaShocked.smear V_T zV - lowDeltaShocked.smear V_T' zV|
      ≤ (9 / 10) * dist V_T V_T'
    exact mul_le_mul_of_nonneg_left hmov (by norm_num)
  have hsender :
      |coupledLeaderObj V_T' V_S x.val a - coupledLeaderObj V_T' W_S x.val a|
        ≤ (43520000 / 283976393) * dist V_S W_S := by
    have hstage := lowDelta_UT_action_lip x.val x.property a ha
      σV hσV_mem σW hσW_mem
    have hcont :
        |lowDeltaShocked.smear V_T' zV - lowDeltaShocked.smear V_T' zW|
          ≤ (25683423000 / 283976393) * ((1 / 100) * |σV - σW|) := by
      calc
        |lowDeltaShocked.smear V_T' zV - lowDeltaShocked.smear V_T' zW|
            ≤ (25683423000 / 283976393) * dist zV zW := by
              simpa only [abs_sub_comm] using hsmVT_lip zV zW
        _ ≤ (25683423000 / 283976393) * ((1 / 100) * |σV - σW|) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    simp only [coupledLeaderObj, AbstractGame.Params.joint_T_top_integrand]
    change |(lowDeltaShocked.toParams.U_T x.val a σV
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zV)
        - (lowDeltaShocked.toParams.U_T x.val a σW
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zW)|
      ≤ (43520000 / 283976393) * dist V_S W_S
    calc
      |(lowDeltaShocked.toParams.U_T x.val a σV
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zV)
        - (lowDeltaShocked.toParams.U_T x.val a σW
          + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zW)|
        ≤ |lowDeltaShocked.toParams.U_T x.val a σV
              - lowDeltaShocked.toParams.U_T x.val a σW|
            + lowDeltaShocked.toParams.β_T
              * |lowDeltaShocked.smear V_T' zV
                - lowDeltaShocked.smear V_T' zW| := by
          rw [show (lowDeltaShocked.toParams.U_T x.val a σV
                + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zV)
              - (lowDeltaShocked.toParams.U_T x.val a σW
                + lowDeltaShocked.toParams.β_T * lowDeltaShocked.smear V_T' zW)
              = (lowDeltaShocked.toParams.U_T x.val a σV
                  - lowDeltaShocked.toParams.U_T x.val a σW)
                + lowDeltaShocked.toParams.β_T
                  * (lowDeltaShocked.smear V_T' zV
                    - lowDeltaShocked.smear V_T' zW) by
                  ring]
          calc
            |(lowDeltaShocked.toParams.U_T x.val a σV
                - lowDeltaShocked.toParams.U_T x.val a σW)
              + lowDeltaShocked.toParams.β_T
                * (lowDeltaShocked.smear V_T' zV
                  - lowDeltaShocked.smear V_T' zW)|
              ≤ |lowDeltaShocked.toParams.U_T x.val a σV
                    - lowDeltaShocked.toParams.U_T x.val a σW|
                + |lowDeltaShocked.toParams.β_T
                  * (lowDeltaShocked.smear V_T' zV
                    - lowDeltaShocked.smear V_T' zW)| := abs_add_le _ _
            _ = _ := by
              rw [abs_mul, abs_of_nonneg lowDeltaShocked.toParams.β_T_mem.1]
      _ ≤ |σV - σW| + (9 / 10)
          * ((25683423000 / 283976393) * ((1 / 100) * |σV - σW|)) := by
        have hβ : lowDeltaShocked.toParams.β_T = 9 / 10 := rfl
        rw [hβ]
        exact add_le_add (by simpa only [one_mul] using hstage)
          (mul_le_mul_of_nonneg_left hcont (by norm_num))
      _ = ((1 : ℝ) + (9 / 10) * (25683423000 / 283976393) * (1 / 100))
          * |σV - σW| := by ring
      _ ≤ ((1 : ℝ) + (9 / 10) * (25683423000 / 283976393) * (1 / 100))
          * ((3200 / 37877) * dist V_S W_S) :=
        mul_le_mul_of_nonneg_left hσ (by positivity)
      _ = (43520000 / 283976393) * dist V_S W_S := by ring
  calc
    |coupledLeaderObj V_T V_S x.val a - coupledLeaderObj V_T' W_S x.val a|
      ≤ |coupledLeaderObj V_T V_S x.val a - coupledLeaderObj V_T' V_S x.val a|
        + |coupledLeaderObj V_T' V_S x.val a
          - coupledLeaderObj V_T' W_S x.val a| := by
          calc
            |coupledLeaderObj V_T V_S x.val a
                - coupledLeaderObj V_T' W_S x.val a|
              = |(coupledLeaderObj V_T V_S x.val a
                    - coupledLeaderObj V_T' V_S x.val a)
                  + (coupledLeaderObj V_T' V_S x.val a
                    - coupledLeaderObj V_T' W_S x.val a)| := by
                  congr 1
                  ring
            _ ≤ _ := abs_add_le _ _
    _ ≤ (9 / 10) * dist V_T V_T'
        + (43520000 / 283976393) * dist V_S W_S :=
      add_le_add hown hsender

/-- **Squared realised-leader stability on the redesigned carrier.**
The already-required modulus-`1/2` quadratic-growth inequalities and the
one-box pointwise perturbation bound imply a Hölder-`1/2`, not Lipschitz,
policy estimate:

`|Δα|² ≤ (9/5) dist(V_T,V_T') + (87040000/283976393) dist(V_S,W_S)`.

This is the strongest estimate obtained from the approved zero-order bounds;
it does not discharge the product-form premise of the Perov capstone.  Only the
Lipschitz halves of the carrier memberships are assumed (the norm bounds are
dropped).  Witness-specific (Rule 22). -/
theorem coupled_lead_sq_holder_of_quadraticGrowth_on_lip_carrier
    (lead : SBCF → SBCF → ℝ → ℝ)
    (V_T V_S V_T' W_S : SBCF)
    (hV_T' : ValueLipschitzWith V_T' (25683423000 / 283976393))
    (hV_S : ValueLipschitzWith V_S lowDeltaSenderCarrierLip)
    (hW_S : ValueLipschitzWith W_S lowDeltaSenderCarrierLip)
    (x : ↥(Sanctions.S : Set ℝ))
    (hmemV : lead V_T V_S x.val ∈ Sanctions.I)
    (hmemW : lead V_T' W_S x.val ∈ Sanctions.I)
    (growthV : ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T V_S x.val) ^ 2
        ≤ coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T V_S x.val a)
    (growthW : ∀ a ∈ Sanctions.I,
      (1 / 2) * (a - lead V_T' W_S x.val) ^ 2
        ≤ coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val a) :
    (lead V_T V_S x.val - lead V_T' W_S x.val) ^ 2
      ≤ (9 / 5) * dist V_T V_T'
        + (87040000 / 283976393) * dist V_S W_S := by
  let aV := lead V_T V_S x.val
  let aW := lead V_T' W_S x.val
  let E := (9 / 10 : ℝ) * dist V_T V_T'
    + (43520000 / 283976393) * dist V_S W_S
  have hgV := growthV aW hmemW
  have hgW := growthW aV hmemV
  have hchord :
      (aV - aW) ^ 2
        ≤ (coupledLeaderObj V_T V_S x.val aV
              - coupledLeaderObj V_T' W_S x.val aV)
          - (coupledLeaderObj V_T V_S x.val aW
              - coupledLeaderObj V_T' W_S x.val aW) := by
    dsimp only [aV, aW] at hgV hgW ⊢
    nlinarith [sq_nonneg
      (lead V_T V_S x.val - lead V_T' W_S x.val)]
  have hEV :
      |coupledLeaderObj V_T V_S x.val aV
        - coupledLeaderObj V_T' W_S x.val aV| ≤ E := by
    dsimp only [E]
    exact coupledLeaderObj_pair_pointwise_bound_on_lip_carrier
      V_T V_T' V_S W_S hV_T' hV_S hW_S x aV hmemV
  have hEW :
      |coupledLeaderObj V_T V_S x.val aW
        - coupledLeaderObj V_T' W_S x.val aW| ≤ E := by
    dsimp only [E]
    exact coupledLeaderObj_pair_pointwise_bound_on_lip_carrier
      V_T V_T' V_S W_S hV_T' hV_S hW_S x aW hmemW
  have hE :
      (aV - aW) ^ 2 ≤ 2 * E := by
    calc
      (aV - aW) ^ 2
          ≤ (coupledLeaderObj V_T V_S x.val aV
                - coupledLeaderObj V_T' W_S x.val aV)
            - (coupledLeaderObj V_T V_S x.val aW
                - coupledLeaderObj V_T' W_S x.val aW) := hchord
      _ ≤ |coupledLeaderObj V_T V_S x.val aV
              - coupledLeaderObj V_T' W_S x.val aV|
          + |coupledLeaderObj V_T V_S x.val aW
              - coupledLeaderObj V_T' W_S x.val aW| := by
            linarith [
              le_abs_self (coupledLeaderObj V_T V_S x.val aV
                - coupledLeaderObj V_T' W_S x.val aV),
              neg_le_abs (coupledLeaderObj V_T V_S x.val aW
                - coupledLeaderObj V_T' W_S x.val aW)]
      _ ≤ E + E := add_le_add hEV hEW
      _ = 2 * E := by ring
  dsimp only [aV, aW, E] at hE ⊢
  nlinarith

/-! ## Disproof of the uniform Sender-value channel -/

/-- The identity Sender continuation value used in the counterexample. -/
noncomputable def coupledSenderIdentity : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z : ↥(Sanctions.S : Set ℝ) => z.val, continuous_subtype_val⟩

@[simp] theorem coupledSenderIdentity_apply
    (z : ↥(Sanctions.S : Set ℝ)) :
    coupledSenderIdentity z = z.val := rfl

theorem coupledSenderIdentity_mem :
    coupledSenderIdentity ∈ coupledCarrierS := by
  rw [coupledCarrierS, AbstractGame.Params.mem_valLipBall_iff]
  constructor
  · rw [lowDeltaSenderCarrierNorm_eq]
    rw [BoundedContinuousFunction.norm_le
      (by norm_num : (0 : ℝ) ≤ 523 / 160)]
    intro z
    rw [Real.norm_eq_abs, coupledSenderIdentity_apply,
      abs_of_nonneg z.property.1]
    exact le_trans z.property.2 (by norm_num : (1 : ℝ) ≤ 523 / 160)
  · intro y₁ y₂
    rw [coupledSenderIdentity_apply, coupledSenderIdentity_apply,
      Subtype.dist_eq, Real.dist_eq]
    calc
      |y₂.val - y₁.val| = 1 * |y₁.val - y₂.val| := by
        rw [one_mul, abs_sub_comm]
      _ ≤ lowDeltaSenderCarrierLip * |y₁.val - y₂.val| :=
        mul_le_mul_of_nonneg_right
          (by rw [lowDeltaSenderCarrierLip_eq]; norm_num) (abs_nonneg _)

theorem coupledSenderIdentity_movAvg {y : ℝ}
    (hy0 : 1 / 10 ≤ y) (hy1 : y ≤ 9 / 10) :
    Sanctions.movAvgReal (1 / 10) coupledSenderIdentity y = y := by
  unfold Sanctions.movAvgReal
  have hlohi : y - 1 / 10 ≤ y + 1 / 10 := by linarith
  have hint :
      (∫ z in (y - 1 / 10)..(y + 1 / 10),
          coupledSenderIdentity (Sanctions.clipS' z)) =
        ∫ z in (y - 1 / 10)..(y + 1 / 10), z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le hlohi] at hz
    have hz0 : 0 ≤ z := by linarith [hz.1]
    have hz1 : z ≤ 1 := by linarith [hz.2]
    change coupledSenderIdentity (Sanctions.clipS' z) = z
    rw [coupledSenderIdentity_apply,
      Sanctions.clipS'_val_eq_of_mem ⟨hz0, hz1⟩]
  have hderiv :
      ∀ z ∈ Set.uIcc (y - 1 / 10) (y + 1 / 10),
        HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) z z := by
    intro z _
    convert ((hasDerivAt_id z).pow 2).const_mul (1 / 2 : ℝ) using 1
    simp only [id_eq]
    ring
  have hInt : IntervalIntegrable (fun z : ℝ => z) volume
      (y - 1 / 10) (y + 1 / 10) :=
    continuous_id.intervalIntegrable _ _
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
  rw [hint, hFTC]
  ring

theorem coupledSenderIdentity_smear_transition
    {s : ℝ} (hs : s ∈ Sanctions.I) :
    lowDeltaShocked.smear coupledSenderIdentity
        (Sanctions.clipS'
          (lowDeltaShocked.toParams.F (5 / 12) s)) =
      lowDeltaShocked.toParams.F (5 / 12) s := by
  have hy0 : (1 / 10 : ℝ) ≤
      lowDeltaShocked.toParams.F (5 / 12) s := by
    rcases hs with ⟨hs0, hs1⟩
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    linarith
  have hy1 : lowDeltaShocked.toParams.F (5 / 12) s
      ≤ (9 / 10 : ℝ) := by
    rcases hs with ⟨hs0, hs1⟩
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    linarith
  have hyS : lowDeltaShocked.toParams.F (5 / 12) s
      ∈ Sanctions.S := ⟨le_trans (by norm_num) hy0,
        le_trans hy1 (by norm_num)⟩
  rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hyS]
  exact coupledSenderIdentity_movAvg hy0 hy1

/-- The identity continuation shifts the realized Sender selector by exactly
`1 / 240` over the two-action counterexample window. -/
theorem coupled_sigmaDynTop_senderIdentity_eq {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 35 / 1392) :
    lowDeltaShocked.toParams.σ_dyn_top
        (lowDeltaShocked.smear coupledSenderIdentity) (5 / 12) a =
      37 / 96 - (5 / 12) * a + 1 / 240 := by
  let t : ℝ := 37 / 96 - (5 / 12) * a + 1 / 240
  have ht : t ∈ Sanctions.I := by
    dsimp only [t]
    constructor <;> norm_num at ha0 ha1 ⊢ <;> linarith
  have hmax : IsMaxOn
      (fun s => lowDeltaShocked.toParams.U_S (5 / 12) a s
        + lowDeltaShocked.toParams.β_S
          * lowDeltaShocked.smear coupledSenderIdentity
            (Sanctions.clipS'
              (lowDeltaShocked.toParams.F (5 / 12) s)))
      Sanctions.I t := by
    rw [isMaxOn_iff]
    intro s hs
    rw [coupledSenderIdentity_smear_transition hs,
      coupledSenderIdentity_smear_transition ht]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S,
      lowDeltaParams_β_S, lowDeltaParams_F, AbstractGame.affineF]
    dsimp only [t]
    unfold mwU_S
    nlinarith [sq_nonneg
      (s - (37 / 96 - (5 / 12) * a + 1 / 240))]
  exact AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
    ((coupled_sender_strongConcave coupledSenderIdentity
      coupledSenderIdentity_mem.2 (5 / 12)
      (by constructor <;> norm_num) a).strictConcaveOn (by norm_num))
    (lowDeltaShocked.toParams.σ_dyn_top_mem_I
      (lowDeltaShocked.smear coupledSenderIdentity) (5 / 12) a)
    ht
    (lowDeltaShocked.toParams.σ_dyn_top_isMaxOn
      (lowDeltaShocked.smear coupledSenderIdentity) (5 / 12) a)
    hmax

/-- Six times the existing monotone ramp remains within the Target carrier
but makes the mixed Sender-value channel exceed its advertised modulus. -/
noncomputable def coupledObjectiveTargetRampSix : SBCF :=
  (6 : ℝ) • coupledGrowthRamp

@[simp] theorem coupledObjectiveTargetRampSix_apply
    (z : ↥(Sanctions.S : Set ℝ)) :
    coupledObjectiveTargetRampSix z = 6 * coupledGrowthRamp z := rfl

theorem coupledObjectiveTargetRampSix_mem :
    coupledObjectiveTargetRampSix ∈ coupledCarrierT := by
  constructor
  · simp only [Set.mem_setOf_eq]
    rw [lowDeltaTargetCarrierNorm_eq]
    rw [BoundedContinuousFunction.norm_le
      (by norm_num : (0 : ℝ) ≤ 20)]
    intro z
    rw [Real.norm_eq_abs, coupledObjectiveTargetRampSix_apply,
      abs_of_nonneg]
    · calc
        6 * coupledGrowthRamp z
            ≤ 6 * ((92800 / 3 : ℝ) * (7 / 66816)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [coupledGrowthRamp_apply]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact max_le (by norm_num) (min_le_left _ _)
        _ ≤ 20 := by norm_num
    · have hz : 0 ≤ coupledGrowthRamp z := by
        rw [coupledGrowthRamp_apply]
        positivity
      positivity
  · intro y₁ y₂ _ _ hy
    change (0 : ℝ) * dist y₁ y₂
      ≤ 6 * coupledGrowthRamp y₂ - 6 * coupledGrowthRamp y₁
    rw [zero_mul]
    nlinarith [coupledGrowthRamp_mono hy]

theorem coupledObjectiveTargetRampSix_smear
    (y : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaShocked.smear coupledObjectiveTargetRampSix y =
      6 * lowDeltaShocked.smear coupledGrowthRamp y := by
  rw [lowDeltaShocked_smear, Sanctions.movAvgBCF_apply,
    Sanctions.movAvgBCF_apply]
  unfold Sanctions.movAvgReal
  change (1 / (2 * (1 / 10 : ℝ))) *
      (∫ z in (y.val - 1 / 10)..(y.val + 1 / 10),
        6 * coupledGrowthRamp (Sanctions.clipS' z)) =
    6 * ((1 / (2 * (1 / 10 : ℝ))) *
      (∫ z in (y.val - 1 / 10)..(y.val + 1 / 10),
        coupledGrowthRamp (Sanctions.clipS' z)))
  rw [intervalIntegral.integral_const_mul]
  ring

theorem coupledLeaderObj_senderIdentity_channel_formula {a : ℝ}
    (ha0 : 1 / 100 ≤ a) (ha1 : a ≤ 35 / 1392) :
    coupledLeaderObj coupledObjectiveTargetRampSix 0 (5 / 12) a
        - coupledLeaderObj coupledObjectiveTargetRampSix
          coupledSenderIdentity (5 / 12) a =
      (1 / 2880 - a / 480)
        + (9 / 10) * 6 * (145 / 108)
          * ((35 / 1392 - a) ^ 2
            - (35 / 1392 - a + 1 / 100) ^ 2) := by
  have haI : a ∈ Sanctions.I := by
    constructor
    · linarith
    · norm_num at ha1 ⊢
      linarith
  have hakink : a ≤ 37 / 40 := by
    norm_num at ha1 ⊢
    linarith
  have hc0 : 0 ≤ a - 1 / 100 := by linarith
  have hc1 : a - 1 / 100 ≤ 35 / 1392 := by linarith
  have hcI : a - 1 / 100 ∈ Sanctions.I := by
    constructor
    · exact hc0
    · norm_num at hc1 ⊢
      linarith
  have hland0 := coupledGrowthRamp_landing_low haI
  have hland1 :
      (Sanctions.clipS' ((1 - 1 / 100) * (5 / 12) +
        1 / 100 * (37 / 96 - (5 / 12) * a + 1 / 240))).val =
          3997 / 9600 - (a - 1 / 100) / 240 := by
    convert coupledGrowthRamp_landing_low hcI using 1
    ring_nf
  have hsm0 :
      lowDeltaShocked.smear coupledObjectiveTargetRampSix
          (Sanctions.clipS' (lowDeltaShocked.toParams.F (5 / 12)
            (37 / 96 - (5 / 12) * a))) =
        6 * ((145 / 108) * (35 / 1392 - a) ^ 2) := by
    rw [coupledObjectiveTargetRampSix_smear, lowDeltaShocked_smear,
      Sanctions.movAvgBCF_apply]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    rw [hland0, coupledGrowthRamp_movAvg_low haI.1 ha1]
  have hsm1 :
      lowDeltaShocked.smear coupledObjectiveTargetRampSix
          (Sanctions.clipS' (lowDeltaShocked.toParams.F (5 / 12)
            (37 / 96 - (5 / 12) * a + 1 / 240))) =
        6 * ((145 / 108) * (35 / 1392 - a + 1 / 100) ^ 2) := by
    rw [coupledObjectiveTargetRampSix_smear, lowDeltaShocked_smear,
      Sanctions.movAvgBCF_apply]
    simp only [lowDeltaShocked_toParams, lowDeltaParams_F,
      AbstractGame.affineF]
    rw [hland1, coupledGrowthRamp_movAvg_low hc0 hc1]
    congr 3
    ring
  unfold coupledLeaderObj
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [lowDelta_sigmaDynTop_smear_zero,
    coupled_mwσ_five_twelfths_of_le haI hakink,
    coupled_sigmaDynTop_senderIdentity_eq
      (le_trans (by norm_num) ha0) ha1,
    hsm0, hsm1]
  simp only [lowDeltaShocked_toParams, lowDeltaParams_U_T,
    lowDeltaParams_β_T]
  unfold mwU_T
  ring

theorem coupledSenderIdentity_norm : ‖coupledSenderIdentity‖ = 1 := by
  apply le_antisymm
  · rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro z
    rw [Real.norm_eq_abs, coupledSenderIdentity_apply,
      abs_of_nonneg z.property.1]
    exact z.property.2
  · have h := BoundedContinuousFunction.norm_coe_le_norm
      coupledSenderIdentity (Sanctions.clipS' 1)
    simpa [coupledSenderIdentity_apply, Real.norm_eq_abs] using h

theorem coupledSenderIdentity_dist_zero :
    dist (0 : SBCF) coupledSenderIdentity = 1 := by
  rw [dist_eq_norm]
  simpa using coupledSenderIdentity_norm

theorem coupledLeaderObj_senderIdentity_exact_difference :
    (coupledLeaderObj coupledObjectiveTargetRampSix 0
        (5 / 12) (1 / 100)
      - coupledLeaderObj coupledObjectiveTargetRampSix
        coupledSenderIdentity (5 / 12) (1 / 100))
    - (coupledLeaderObj coupledObjectiveTargetRampSix 0
        (5 / 12) (35 / 1392)
      - coupledLeaderObj coupledObjectiveTargetRampSix
        coupledSenderIdentity (5 / 12) (35 / 1392)) =
      (343 / 2400) * ((1 / 100) - (35 / 1392)) := by
  rw [coupledLeaderObj_senderIdentity_channel_formula
      (by norm_num) (by norm_num),
    coupledLeaderObj_senderIdentity_channel_formula
      (by norm_num) le_rfl]
  ring

theorem coupledLeaderObj_sender_advertised_bound_fails :
    ¬ |(coupledLeaderObj coupledObjectiveTargetRampSix 0
          (5 / 12) (1 / 100)
        - coupledLeaderObj coupledObjectiveTargetRampSix
          coupledSenderIdentity (5 / 12) (1 / 100))
      - (coupledLeaderObj coupledObjectiveTargetRampSix 0
          (5 / 12) (35 / 1392)
        - coupledLeaderObj coupledObjectiveTargetRampSix
          coupledSenderIdentity (5 / 12) (35 / 1392))|
      ≤ (467033055680 / 7762983835019)
          * dist (0 : SBCF) coupledSenderIdentity
          * |(1 / 100) - (35 / 1392)| := by
  rw [coupledLeaderObj_senderIdentity_exact_difference,
    coupledSenderIdentity_dist_zero]
  norm_num [abs_mul]

/-- The advertised Sender-value modulus is false as a carrier-uniform
all-actions estimate.  This does not independently refute the conditional
capstone's weaker realized-leader-only premise. -/
theorem not_coupledLeaderObj_sender_uniform_advertised :
    ¬ (∀ V_T ∈ coupledCarrierT,
      ∀ V_S ∈ coupledCarrierS, ∀ W_S ∈ coupledCarrierS,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      ∀ a ∈ Sanctions.I, ∀ b ∈ Sanctions.I,
      |(coupledLeaderObj V_T V_S x.val a
            - coupledLeaderObj V_T W_S x.val a)
        - (coupledLeaderObj V_T V_S x.val b
            - coupledLeaderObj V_T W_S x.val b)|
        ≤ (467033055680 / 7762983835019) * dist V_S W_S
            * |a - b|) := by
  intro h
  have hbad := h coupledObjectiveTargetRampSix
    coupledObjectiveTargetRampSix_mem
    0 zero_mem_coupledCarrierS
    coupledSenderIdentity coupledSenderIdentity_mem
    ⟨5 / 12, by constructor <;> norm_num⟩
    (1 / 100) (by constructor <;> norm_num)
    (35 / 1392) (by constructor <;> norm_num)
  exact coupledLeaderObj_sender_advertised_bound_fails hbad

end
end Examples
end Sanctions
