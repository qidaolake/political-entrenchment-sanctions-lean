/-
Sanctions/Examples/NonAffineInteriorWitness.lean

## One nonlinear, positive-discount, off-corner persistence economy

This module closes the narrow logical non-vacuity gap left by the
separate B2 and quadratic-bump examples.  A single explicitly defined
economy has:

* the genuinely non-affine `quadBumpF` transition;
* strictly positive discount factors for both players;
* an interior Target policy `α = 1/2`;
* an interior Sender sanction at the basin pivot (`3/4` at `x = 1/2`);
* a strict Target preference for higher sanctions along the certified
  high-action range; and
* the complete general-`F` persistence floor and monotonicity result.

The witness is intentionally transparent.  Both equilibrium values are
zero, so discount factors are positive but the continuation channel is
inactive at this example.  Its purpose is therefore logical integration
of the theorem's features, not calibration or a claim that this is the
paper's substantive political-economy application.

## The family over any transition (round BH-5, item BH5.4, 2026-10-07)

Because both equilibrium values are zero, the transition never enters a
payoff: the successor state is read only inside `V(F(x, s)) = 0`.  So every
result above holds over **any** transition.  `niParamsOf p₀` takes the
transition and its four structural fields from an arbitrary economy `p₀` and
keeps the stage data, and every lemma is proved for that family
(`ni_integrated_interior_persistence_generalF`, Rule 22: general in `F`).  The
literal `niParams` (transition `quadBumpF`) is kept beside the family with its
own definition; its lemmas are one-line instances at `p₀ := niParams`, and the
only literal-specific content is the non-affinity of `quadBumpF`.

No assumption or headline theorem is changed.
-/

import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Certificates.StandardComplianceMain

namespace Sanctions
namespace Examples

open Set AbstractGame AbstractGame.Params
open WitnessKit

noncomputable section

/-! ## Primitives -/

/-- The Sender's unconstrained ideal sanction.  Compliance lowers the
ideal sanction, while a higher inherited hardliner state raises it. -/
def niIdeal (x a : ℝ) : ℝ :=
  x / 2 + 5 / 8 - a / 4

/-- The feasible static Sender response. -/
def niSigma (x a : ℝ) : ℝ :=
  Sanctions.clipS (niIdeal x a)

/-- Sender stage payoff: a strictly concave loss around `niIdeal`. -/
def niU_S (x a s : ℝ) : ℝ :=
  - (s - niIdeal x a) ^ 2

/-- Target stage payoff.  Holding `(x,a)` fixed, the Target strictly
prefers a higher sanction.  Against the Sender's clipped ideal,
`a = 1/2` remains optimal. -/
def niU_T (x a s : ℝ) : ℝ :=
  - (a - 1 / 2) ^ 2 + s - niIdeal x a

theorem niSigma_mem (x a : ℝ) :
    niSigma x a ∈ Set.Icc (0 : ℝ) 1 :=
  Sanctions.clipS_mem _

theorem niSigma_continuous :
    Continuous (fun xa : ℝ × ℝ => niSigma xa.1 xa.2) := by
  unfold niSigma
  apply Sanctions.clipS_continuous.comp
  unfold niIdeal
  fun_prop

theorem niU_S_continuous :
    Continuous
      (fun xas : ℝ × ℝ × ℝ => niU_S xas.1 xas.2.1 xas.2.2) := by
  unfold niU_S niIdeal
  fun_prop

theorem niU_T_continuous :
    Continuous
      (fun xas : ℝ × ℝ × ℝ => niU_T xas.1 xas.2.1 xas.2.2) := by
  unfold niU_T niIdeal
  fun_prop

theorem niSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => niU_S x a s) Sanctions.I (niSigma x a) := by
  refine clipVertex_isMaxOn (k := (1 : ℝ)) (C := 0)
    (t := niIdeal x a) (U := fun s => niU_S x a s)
    (by norm_num) ?_
  intro s
  simp [niU_S]

/-- The nonlinear integrated-witness economy. -/
def niParams : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 9 / 10
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := niU_T
  U_S := niU_S
  σ := niSigma
  σ_mem := niSigma_mem
  σ_isMaxOn_U_S := niSigma_isMaxOn
  U_T_continuous := niU_T_continuous
  U_S_continuous := niU_S_continuous
  F := quadBumpF
  F_continuous := quadBumpF_continuous
  F_mono_x := quadBumpF_mono_x
  F_mono_s := quadBumpF_mono_s
  F_diag := quadBumpF_diag

/-- **`niParams` has a continuous static Sender selector.** A concrete member with the
non-affine transition `quadBumpF`; the selector itself does not read the transition. The
proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance niParams_staticSelectorContinuous :
    niParams.StaticSelectorContinuous where
  σ_continuous := niSigma_continuous

@[simp] theorem niParams_U_S : niParams.U_S = niU_S := rfl
@[simp] theorem niParams_U_T : niParams.U_T = niU_T := rfl
@[simp] theorem niParams_β_S : niParams.β_S = 1 / 2 := rfl
@[simp] theorem niParams_β_T : niParams.β_T = 9 / 10 := rfl
@[simp] theorem niParams_F : niParams.F = quadBumpF := rfl

theorem niParams_F_ne_affine :
    niParams.F ≠ AbstractGame.affineF (1 / 2) := by
  simpa only [niParams_F] using qbParams_F_ne_affine

theorem niParams_strictAdjustment :
    niParams.StrictAdjustment := by
  simpa only [niParams_F] using qbParams_strictAdjustment

/-- **The integrated-witness economy over any transition** (round BH-5, item
BH5.4).  The stage payoffs, the stage selector, the discounts and the inert
rate `δ` of `niParams`, with the transition `F` and its four structural fields
taken from an arbitrary economy `p₀`.  Rule 22: general in `F`; nothing is
assumed about `p₀.F` beyond the `Params` fields it already carries.  The
literal `niParams` is the member `p₀ := niParams` (`niParamsOf_self`). -/
def niParamsOf (p₀ : AbstractGame.Params) : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 9 / 10
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := niU_T
  U_S := niU_S
  σ := niSigma
  σ_mem := niSigma_mem
  σ_isMaxOn_U_S := niSigma_isMaxOn
  U_T_continuous := niU_T_continuous
  U_S_continuous := niU_S_continuous
  F := p₀.F
  F_continuous := p₀.F_continuous
  F_mono_x := p₀.F_mono_x
  F_mono_s := p₀.F_mono_s
  F_diag := p₀.F_diag

/-- **`niParamsOf` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance niParamsOf_staticSelectorContinuous (p₀ : AbstractGame.Params) :
    (niParamsOf p₀).StaticSelectorContinuous where
  σ_continuous := niSigma_continuous

@[simp] theorem niParamsOf_U_S (p₀ : AbstractGame.Params) : (niParamsOf p₀).U_S = niU_S := rfl
@[simp] theorem niParamsOf_U_T (p₀ : AbstractGame.Params) : (niParamsOf p₀).U_T = niU_T := rfl
@[simp] theorem niParamsOf_β_S (p₀ : AbstractGame.Params) : (niParamsOf p₀).β_S = 1 / 2 := rfl
@[simp] theorem niParamsOf_β_T (p₀ : AbstractGame.Params) : (niParamsOf p₀).β_T = 9 / 10 := rfl
@[simp] theorem niParamsOf_F (p₀ : AbstractGame.Params) : (niParamsOf p₀).F = p₀.F := rfl

/-- The literal economy is the family member at its own transition, by
definition. -/
theorem niParamsOf_self : niParamsOf niParams = niParams := rfl

/-! ## Exact top-selector equilibrium -/

/-- The zero bounded-continuous value used by both players. -/
def niV0 : Val := 0

/-- The interior Target policy. -/
def niAlpha (_x : ℝ) : ℝ := 1 / 2

theorem niAlpha_continuous : Continuous niAlpha :=
  continuous_const

theorem niAlpha_mem (x : ℝ) :
    niAlpha x ∈ Sanctions.I := by
  constructor <;> norm_num [niAlpha]

theorem niIdeal_nonneg_of_mem
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    0 ≤ niIdeal x a := by
  rcases hx with ⟨hx0, hx1⟩
  rcases ha with ⟨ha0, ha1⟩
  unfold niIdeal
  linarith

theorem niIdeal_at_half (x : ℝ) :
    niIdeal x (1 / 2) = (x + 1) / 2 := by
  unfold niIdeal
  ring

theorem niIdeal_at_half_mem
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    niIdeal x (1 / 2) ∈ Sanctions.I := by
  rw [niIdeal_at_half]
  constructor <;> linarith [hx.1, hx.2]

theorem niSigma_at_half
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    niSigma x (1 / 2) = niIdeal x (1 / 2) := by
  unfold niSigma
  exact clipS_of_mem (niIdeal_at_half_mem hx)

/-- At every feasible `(x,a)`, the upper dynamic Sender response is weakly
below the unconstrained ideal, over any transition.  If the ideal is feasible,
the response equals it; if it exceeds one, feasibility gives the same
inequality.  General in `F`: the zero continuation never reads the successor
state. -/
theorem niOf_top_le_ideal (p₀ : AbstractGame.Params)
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    (niParamsOf p₀).σ_dyn_top niV0 x a ≤ niIdeal x a := by
  have htopI := (niParamsOf p₀).σ_dyn_top_mem_I niV0 x a
  have hideal0 := niIdeal_nonneg_of_mem hx ha
  rcases le_total (niIdeal x a) 1 with hideal1 | hone
  · have hidealI : niIdeal x a ∈ Sanctions.I := ⟨hideal0, hideal1⟩
    have hmax := (niParamsOf p₀).σ_dyn_top_isMaxOn niV0 x a
    rw [isMaxOn_iff] at hmax
    have hcomp := hmax (niIdeal x a) hidealI
    have hcomp' : niU_S x a (niIdeal x a)
        ≤ niU_S x a ((niParamsOf p₀).σ_dyn_top niV0 x a) := by
      simpa [niParamsOf, niV0] using hcomp
    unfold niU_S at hcomp'
    nlinarith [sq_nonneg ((niParamsOf p₀).σ_dyn_top niV0 x a - niIdeal x a)]
  · exact le_trans htopI.2 hone

/-- At every feasible `(x,a)`, the upper dynamic Sender response is
weakly below the unconstrained ideal.  If the ideal is feasible, the
response equals it; if it exceeds one, feasibility gives the same
inequality. -/
theorem ni_top_le_ideal
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    niParams.σ_dyn_top niV0 x a ≤ niIdeal x a :=
  niOf_top_le_ideal niParams hx ha

/-- At the interior policy the upper dynamic Sender response is the ideal
`(x + 1)/2`, over any transition.  General in `F`. -/
theorem niOf_top_at_half (p₀ : AbstractGame.Params)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    (niParamsOf p₀).σ_dyn_top niV0 x (1 / 2) = niIdeal x (1 / 2) := by
  have hidealI := niIdeal_at_half_mem hx
  have hmax := (niParamsOf p₀).σ_dyn_top_isMaxOn niV0 x (1 / 2)
  rw [isMaxOn_iff] at hmax
  have hcomp := hmax (niIdeal x (1 / 2)) hidealI
  have hcomp' : niU_S x (1 / 2) (niIdeal x (1 / 2))
      ≤ niU_S x (1 / 2) ((niParamsOf p₀).σ_dyn_top niV0 x (1 / 2)) := by
    simpa [niParamsOf, niV0] using hcomp
  unfold niU_S at hcomp'
  nlinarith [sq_nonneg
    ((niParamsOf p₀).σ_dyn_top niV0 x (1 / 2) - niIdeal x (1 / 2))]

theorem ni_top_at_half
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    niParams.σ_dyn_top niV0 x (1 / 2) = niIdeal x (1 / 2) :=
  niOf_top_at_half niParams hx

/-- The zero Sender value is the Sender Bellman fixed point at the interior
policy, over any transition.  General in `F`. -/
theorem niOf_sender_value_fix (p₀ : AbstractGame.Params) :
    niV0 = (niParamsOf p₀).bellmanS_BCF niAlpha niAlpha_continuous niV0 := by
  ext y
  have hidealI := niIdeal_at_half_mem y.property
  have hmax : IsMaxOn
      (fun s => (niParamsOf p₀).U_S y.val (niAlpha y.val) s
        + (niParamsOf p₀).β_S * niV0
          (Sanctions.clipS' ((niParamsOf p₀).F y.val s)))
      Sanctions.I (niIdeal y.val (1 / 2)) := by
    rw [isMaxOn_iff]
    intro s hs
    simp only [niParamsOf_U_S, niParamsOf_β_S]
    simp only [niAlpha, niV0, BoundedContinuousFunction.coe_zero,
      Pi.zero_apply, mul_zero, add_zero]
    unfold niU_S
    nlinarith [sq_nonneg (s - niIdeal y.val (1 / 2))]
  have himage :=
    WitnessKit.bellmanS_image_of_isMaxOn
      (p := niParamsOf p₀) niAlpha_continuous niV0 y hidealI hmax
  change (0 : ℝ) =
    (niParamsOf p₀).bellmanS_BCF niAlpha niAlpha_continuous niV0 y
  rw [himage]
  simp [niAlpha, niU_S, niV0]

theorem ni_sender_value_fix :
    niV0 = niParams.bellmanS_BCF niAlpha niAlpha_continuous niV0 :=
  niOf_sender_value_fix niParams

/-- The interior policy maximises the Target's top-selector objective, over any
transition.  General in `F`. -/
theorem niOf_target_policy_optimal (p₀ : AbstractGame.Params)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn
      (fun a => (niParamsOf p₀).joint_T_top_integrand niV0 niV0 x a)
      Sanctions.I (niAlpha x) := by
  intro a ha
  have htop_le := niOf_top_le_ideal p₀ hx ha
  have hhalf := niOf_top_at_half p₀ hx
  change
    niU_T x a ((niParamsOf p₀).σ_dyn_top niV0 x a)
        + (9 / 10 : ℝ) * 0
      ≤ niU_T x (1 / 2) ((niParamsOf p₀).σ_dyn_top niV0 x (1 / 2))
        + (9 / 10 : ℝ) * 0
  rw [hhalf]
  unfold niU_T
  nlinarith [sq_nonneg (a - 1 / 2)]

theorem ni_target_policy_optimal
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn
      (fun a => niParams.joint_T_top_integrand niV0 niV0 x a)
      Sanctions.I (niAlpha x) :=
  niOf_target_policy_optimal niParams hx

/-- The zero Target value is the top-selector Target Bellman fixed point, over
any transition.  General in `F`. -/
theorem niOf_target_value_fix_top (p₀ : AbstractGame.Params) (x : ↥(Sanctions.S : Set ℝ)) :
    niV0 x =
      sSup ((fun a =>
        (niParamsOf p₀).joint_T_top_integrand niV0 niV0 x.val a)
        '' Sanctions.I) := by
  have hmax := niOf_target_policy_optimal p₀ x.property
  have hgreatest : IsGreatest
      ((fun a =>
        (niParamsOf p₀).joint_T_top_integrand niV0 niV0 x.val a)
        '' Sanctions.I)
      ((niParamsOf p₀).joint_T_top_integrand niV0 niV0 x.val (1 / 2)) := by
    constructor
    · exact ⟨1 / 2, niAlpha_mem x.val, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hmax ha
  rw [hgreatest.csSup_eq]
  change (0 : ℝ) =
    niU_T x.val (1 / 2) ((niParamsOf p₀).σ_dyn_top niV0 x.val (1 / 2))
      + (9 / 10 : ℝ) * 0
  rw [niOf_top_at_half p₀ x.property]
  simp [niU_T]

theorem ni_target_value_fix_top (x : ↥(Sanctions.S : Set ℝ)) :
    niV0 x =
      sSup ((fun a =>
        niParams.joint_T_top_integrand niV0 niV0 x.val a)
        '' Sanctions.I) :=
  niOf_target_value_fix_top niParams x

/-- The exact stationary upper-selector Stackelberg equilibrium, over any
transition.  Rule 15: constructed; Rule 1: both policies are optima, not
posits.  General in `F`. -/
def niEquilibriumOf (p₀ : AbstractGame.Params) :
    (niParamsOf p₀).FeedbackStackelbergEquilibriumTop where
  V_T := niV0
  V_S := niV0
  α := niAlpha
  hα := niAlpha_continuous
  α_mem := fun x _ => niAlpha_mem x
  V_S_fix := niOf_sender_value_fix p₀
  V_T_fix_top := niOf_target_value_fix_top p₀
  α_opt_top := fun _ hx => niOf_target_policy_optimal p₀ hx

/-- The exact stationary upper-selector Stackelberg equilibrium. -/
def niEquilibrium : niParams.FeedbackStackelbergEquilibriumTop where
  V_T := niV0
  V_S := niV0
  α := niAlpha
  hα := niAlpha_continuous
  α_mem := fun x _ => niAlpha_mem x
  V_S_fix := ni_sender_value_fix
  V_T_fix_top := ni_target_value_fix_top
  α_opt_top := fun _ hx => ni_target_policy_optimal hx

/-! ## Joint preference basin and integrated conclusion -/

/-- The realised rule is `(x + 1)/2`, over any transition.  General in `F`. -/
theorem niOf_realized_rule_eq (p₀ : AbstractGame.Params)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    (niParamsOf p₀).dynamicTopRealizedRule (niEquilibriumOf p₀).V_S
      (niEquilibriumOf p₀).α x = (x + 1) / 2 := by
  unfold AbstractGame.Params.dynamicTopRealizedRule
  change (niParamsOf p₀).σ_dyn_top niV0 x (1 / 2) = (x + 1) / 2
  rw [niOf_top_at_half p₀ hx, niIdeal_at_half]

theorem ni_realized_rule_eq
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    niParams.dynamicTopRealizedRule niEquilibrium.V_S
      niEquilibrium.α x = (x + 1) / 2 :=
  niOf_realized_rule_eq niParams hx

/-- The joint preference basin `[1/2, 1]` at sanction floor `1/2`, over any
transition.  General in `F`. -/
theorem niJointBasinOf (p₀ : AbstractGame.Params) :
    (niParamsOf p₀).JointPreferenceBasinTop
      (niEquilibriumOf p₀).V_T (niEquilibriumOf p₀).V_S (niEquilibriumOf p₀).α
      (1 / 2) (1 / 2) where
  xbar_nonneg := by norm_num
  xbar_le_one := by norm_num
  sbar_mem := by constructor <;> norm_num
  target_policy_feasible := by
    intro x _
    exact niAlpha_mem x
  sender_high_argmax_exists := by
    intro x hx
    have hxS : x ∈ Sanctions.S :=
      ⟨le_trans (by norm_num) hx.1, hx.2⟩
    refine ⟨(x + 1) / 2, ?_, ?_, ?_⟩
    · constructor <;> linarith [hxS.1, hxS.2]
    · rw [← niOf_realized_rule_eq p₀ hxS]
      exact (niParamsOf p₀).σ_dyn_top_isMaxOn (niEquilibriumOf p₀).V_S
        x ((niEquilibriumOf p₀).α x)
    · simp only [max_eq_left hx.1]
      linarith [hxS.2]
  top_rule_mono := by
    intro x hx y hy hxy
    have hxS : x ∈ Sanctions.S :=
      ⟨le_trans (by norm_num) hx.1, hx.2⟩
    have hyS : y ∈ Sanctions.S :=
      ⟨le_trans (by norm_num) hy.1, hy.2⟩
    rw [niOf_realized_rule_eq p₀ hxS, niOf_realized_rule_eq p₀ hyS]
    linarith
  target_prefers_sanctions := by
    intro x hx s₁ hs₁ s₂ hs₂ hs₁₂
    change niU_T x (1 / 2) s₁ + (9 / 10 : ℝ) * 0
      ≤ niU_T x (1 / 2) s₂ + (9 / 10 : ℝ) * 0
    unfold niU_T
    linarith
  target_policy_optimal := by
    intro x hx
    exact niOf_target_policy_optimal p₀
      ⟨le_trans (by norm_num) hx.1, hx.2⟩

theorem niJointBasin :
    niParams.JointPreferenceBasinTop
      niEquilibrium.V_T niEquilibrium.V_S niEquilibrium.α
      (1 / 2) (1 / 2) :=
  niJointBasinOf niParams

/-- **Integrated interior witness over any transition** (round BH-5, item
BH5.4).  For every economy `p₀`, the economy `niParamsOf p₀` has transition
`p₀.F`, both discount factors positive, an interior Target policy and an
interior Sender sanction at the basin pivot, and the complete general-`F`
persistence conclusion on `[1/2, 1]`.  Rule 22: general in `F`; nothing about
the transition is assumed, because both equilibrium values are zero and the
successor state is never priced.  The non-affine literal is
`ni_integrated_nonaffine_interior_persistence`. -/
theorem ni_integrated_interior_persistence_generalF (p₀ : AbstractGame.Params) :
    0 < (niParamsOf p₀).β_T
    ∧ 0 < (niParamsOf p₀).β_S
    ∧ (niParamsOf p₀).F = p₀.F
    ∧ (0 < (niEquilibriumOf p₀).α (1 / 2)
      ∧ (niEquilibriumOf p₀).α (1 / 2) < 1)
    ∧ (0 <
        (niParamsOf p₀).dynamicTopRealizedRule (niEquilibriumOf p₀).V_S
          (niEquilibriumOf p₀).α (1 / 2)
      ∧ (niParamsOf p₀).dynamicTopRealizedRule (niEquilibriumOf p₀).V_S
          (niEquilibriumOf p₀).α (1 / 2) < 1)
    ∧ ∀ x₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∀ n, (niParamsOf p₀).dynamicTopLockInPathF
          (niEquilibriumOf p₀).V_S (niEquilibriumOf p₀).α x₀ n
            ∈ Set.Icc (1 / 2 : ℝ) 1)
      ∧ (∀ n, (1 / 2 : ℝ) ≤
          (niParamsOf p₀).dynamicTopLockInSanctionsF
            (niEquilibriumOf p₀).V_S (niEquilibriumOf p₀).α x₀ n)
      ∧ Monotone
          ((niParamsOf p₀).dynamicTopLockInSanctionsF
            (niEquilibriumOf p₀).V_S (niEquilibriumOf p₀).α x₀) := by
  refine ⟨by norm_num [niParamsOf_β_T], by norm_num [niParamsOf_β_S], rfl, ?_, ?_, ?_⟩
  · norm_num [niEquilibriumOf, niAlpha]
  · have hx : (1 / 2 : ℝ) ∈ Sanctions.S := by
      constructor <;> norm_num
    rw [niOf_realized_rule_eq p₀ hx]
    constructor <;> norm_num
  · intro x₀ hx₀
    obtain ⟨hpath, -, hfloor, hmono, -⟩ :=
      (niParamsOf p₀).jointPreferenceBasinTopF_long_run_with_equilibrium_evidence
        (niJointBasinOf p₀) hx₀
    exact ⟨hpath, hfloor, hmono⟩

/-- **Integrated nonlinear interior witness.**  One exact equilibrium
has both positive discount factors, an interior Target policy, an
interior Sender sanction at the basin pivot, a genuinely non-affine
transition, and the complete general-`F` persistence conclusion with
equilibrium evidence along every basin path.  The member `p₀ := niParams`
of `ni_integrated_interior_persistence_generalF`, plus the non-affinity of
`quadBumpF`. -/
theorem ni_integrated_nonaffine_interior_persistence :
    0 < niParams.β_T
    ∧ 0 < niParams.β_S
    ∧ niParams.F ≠ AbstractGame.affineF (1 / 2)
    ∧ (0 < niEquilibrium.α (1 / 2)
      ∧ niEquilibrium.α (1 / 2) < 1)
    ∧ (0 <
        niParams.dynamicTopRealizedRule niEquilibrium.V_S
          niEquilibrium.α (1 / 2)
      ∧ niParams.dynamicTopRealizedRule niEquilibrium.V_S
          niEquilibrium.α (1 / 2) < 1)
    ∧ ∀ x₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∀ n, niParams.dynamicTopLockInPathF
          niEquilibrium.V_S niEquilibrium.α x₀ n
            ∈ Set.Icc (1 / 2 : ℝ) 1)
      ∧ (∀ n, (1 / 2 : ℝ) ≤
          niParams.dynamicTopLockInSanctionsF
            niEquilibrium.V_S niEquilibrium.α x₀ n)
      ∧ Monotone
          (niParams.dynamicTopLockInSanctionsF
            niEquilibrium.V_S niEquilibrium.α x₀) := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := ni_integrated_interior_persistence_generalF niParams
  exact ⟨h1, h2, niParams_F_ne_affine, h4, h5, h6⟩

end

end Examples
end Sanctions
