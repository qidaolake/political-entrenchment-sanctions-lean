/-
Sanctions/Examples/MechanismWitnessShockedUnconditional.lean

Exact full-width (`h = 1`) construction for the P3 shocked equilibrium.

At full width, every smeared continuation is affine on the physical state
interval and is therefore summarized, for choice purposes, by its endpoint
spread.  The coupled Bellman system reduces to two scalar spread equations.
Eliminating the Target spread leaves the quartic `mwEqQuartic` below.

This file constructs the economically relevant quartic root and the induced
piecewise-affine leader policy before building the two value functions and
packaging the unconditional equilibrium.  No strong-concavity,
cross-value/action coupling, or carrier-invariance hypothesis is introduced.
-/

import Sanctions.Examples.MechanismWitnessShockedDominance
import Sanctions.Theory.Mechanism.ContinuationStakes

namespace Sanctions.Examples

open Set
open AbstractGame
open scoped NNReal Topology
open BoundedContinuousFunction

noncomputable section

/-! ## 1. The exact two-spread system -/

/-- The scalar polynomial obtained after eliminating the Target endpoint
spread from the full-width P3 Bellman spread equations. -/
def mwEqQuartic (D : ℝ) : ℝ :=
  81 * D ^ 4 - 186120 * D ^ 3 + 108518950 * D ^ 2
    - 6625517528 * D + 11351103145

/-- The economically relevant Sender spread root lies in a tight rational
interval.  This is a direct intermediate-value argument; no numeric oracle is
part of the theorem. -/
theorem mwEqQuartic_root_exists :
    ∃ D ∈ Set.Icc (441 / 250 : ℝ) (17641 / 10000), mwEqQuartic D = 0 := by
  let f : ℝ → ℝ := fun D => -mwEqQuartic D
  have hf : Continuous f := by
    dsimp [f, mwEqQuartic]
    fun_prop
  have hbounds : (441 / 250 : ℝ) ≤ 17641 / 10000 := by norm_num
  have hzero :
      (0 : ℝ) ∈ Set.Icc (f (441 / 250)) (f (17641 / 10000)) := by
    dsimp [f, mwEqQuartic]
    constructor <;> norm_num
  rcases (intermediate_value_Icc hbounds hf.continuousOn) hzero with
    ⟨D, hD, hD0⟩
  refine ⟨D, hD, ?_⟩
  dsimp [f] at hD0
  linarith

/-- The selected exact Sender endpoint spread. -/
noncomputable def mwEqSenderSpread : ℝ :=
  Classical.choose mwEqQuartic_root_exists

theorem mwEqSenderSpread_mem :
    mwEqSenderSpread ∈ Set.Icc (441 / 250 : ℝ) (17641 / 10000) :=
  (Classical.choose_spec mwEqQuartic_root_exists).1

theorem mwEqSenderSpread_quartic :
    mwEqQuartic mwEqSenderSpread = 0 :=
  (Classical.choose_spec mwEqQuartic_root_exists).2

/-- The eliminated Target endpoint spread. -/
noncomputable def mwEqTargetSpread : ℝ :=
  -(mwEqSenderSpread ^ 2 - 878 * mwEqSenderSpread + 1469) / 46

theorem mwEqSenderSpread_bounds :
    (441 / 250 : ℝ) ≤ mwEqSenderSpread ∧
      mwEqSenderSpread ≤ 17641 / 10000 :=
  mwEqSenderSpread_mem

theorem mwEqTargetSpread_bounds :
    (5 / 3 : ℝ) ≤ mwEqTargetSpread ∧ mwEqTargetSpread ≤ 17 / 10 := by
  obtain ⟨hlo, hhi⟩ := mwEqSenderSpread_bounds
  unfold mwEqTargetSpread
  constructor <;>
    nlinarith [sq_nonneg (mwEqSenderSpread - 441 / 250),
      sq_nonneg (17641 / 10000 - mwEqSenderSpread)]

/-- The linear identity used to recover the Target spread from the Sender
spread. -/
theorem mwEq_spread_elimination :
    mwEqSenderSpread ^ 2 - 878 * mwEqSenderSpread
      + 46 * mwEqTargetSpread + 1469 = 0 := by
  unfold mwEqTargetSpread
  ring

/-- Sender endpoint equation after substituting the interior top-state leader
and Sender choices. -/
theorem mwEq_sender_spread_polynomial :
    2809 * mwEqSenderSpread ^ 2
      + 954 * mwEqSenderSpread * mwEqTargetSpread
      - 2435402 * mwEqSenderSpread
      + 81 * mwEqTargetSpread ^ 2
      - 29682 * mwEqTargetSpread + 4333921 = 0 := by
  have hq := mwEqSenderSpread_quartic
  have hid := mwEq_spread_elimination
  unfold mwEqTargetSpread at *
  unfold mwEqQuartic at hq
  field_simp at *
  nlinarith

/-- Target endpoint equation after substituting the same top-state choices. -/
theorem mwEq_target_spread_polynomial :
    25 * mwEqSenderSpread ^ 2
      + 954 * mwEqSenderSpread * mwEqTargetSpread
      + 8950 * mwEqSenderSpread
      + 81 * mwEqTargetSpread ^ 2
      - 157746 * mwEqTargetSpread + 244225 = 0 := by
  have hS := mwEq_sender_spread_polynomial
  have hid := mwEq_spread_elimination
  nlinarith

/-! ## 2. The induced leader and Sender rules -/

/-- Unconstrained leader vertex in the interior Sender-response region. -/
noncomputable def mwEqLeaderVertex (x : ℝ) : ℝ :=
  (5 * mwEqSenderSpread - 9 * mwEqTargetSpread + 515 * x - 200) / 580

/-- The equilibrium leader policy.  The upper action constraint never binds;
the lower constraint binds on the low-state interval. -/
noncomputable def mwEqLeaderPolicy (x : ℝ) : ℝ :=
  max 0 (mwEqLeaderVertex x)

@[fun_prop] theorem mwEqLeaderPolicy_continuous : Continuous mwEqLeaderPolicy := by
  unfold mwEqLeaderPolicy mwEqLeaderVertex
  fun_prop

theorem mwEqLeaderPolicy_mem (x : ℝ) (hx : x ∈ Sanctions.S) :
    mwEqLeaderPolicy x ∈ Sanctions.I := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  constructor
  · exact le_max_left _ _
  · unfold mwEqLeaderPolicy
    rw [max_le_iff]
    constructor
    · norm_num
    · unfold mwEqLeaderVertex
      nlinarith [hx.2]

/-- The Sender vertex associated with the selected equilibrium spread. -/
noncomputable def mwEqSenderVertex (x a : ℝ) : ℝ :=
  (9 / 8) * x - 1 / 12 - (5 / 12) * a + mwEqSenderSpread / 24

/-- The exact clipped Sender response associated with the selected spread. -/
noncomputable def mwEqSenderRule (x a : ℝ) : ℝ :=
  max 0 (min 1 (mwEqSenderVertex x a))

@[fun_prop] theorem mwEqSenderRule_continuous :
    Continuous (fun xa : ℝ × ℝ => mwEqSenderRule xa.1 xa.2) := by
  unfold mwEqSenderRule mwEqSenderVertex
  fun_prop

theorem mwEqSenderRule_mem (x a : ℝ) :
    mwEqSenderRule x a ∈ Sanctions.I := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

@[simp] theorem mwEqLeaderPolicy_zero :
    mwEqLeaderPolicy 0 = 0 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  unfold mwEqLeaderPolicy mwEqLeaderVertex
  rw [max_eq_left]
  nlinarith

theorem mwEqLeaderVertex_one_pos : 0 < mwEqLeaderVertex 1 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  unfold mwEqLeaderVertex
  nlinarith

@[simp] theorem mwEqLeaderPolicy_one :
    mwEqLeaderPolicy 1 = mwEqLeaderVertex 1 := by
  unfold mwEqLeaderPolicy
  rw [max_eq_right mwEqLeaderVertex_one_pos.le]

@[simp] theorem mwEqSenderRule_zero :
    mwEqSenderRule 0 (mwEqLeaderPolicy 0) = 0 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  rw [mwEqLeaderPolicy_zero]
  unfold mwEqSenderRule mwEqSenderVertex
  rw [min_eq_right, max_eq_left] <;> nlinarith

theorem mwEqSenderVertex_top_mem :
    mwEqSenderVertex 1 (mwEqLeaderPolicy 1) ∈ Sanctions.I := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  rw [mwEqLeaderPolicy_one]
  unfold mwEqSenderVertex mwEqLeaderVertex
  constructor <;> nlinarith

@[simp] theorem mwEqSenderRule_one :
    mwEqSenderRule 1 (mwEqLeaderPolicy 1) =
      mwEqSenderVertex 1 (mwEqLeaderPolicy 1) := by
  obtain ⟨h0, h1⟩ := mwEqSenderVertex_top_mem
  unfold mwEqSenderRule
  rw [min_eq_right h1, max_eq_right h0]

/-! ## 3. Explicit Sender value -/

/-- The nonconstant part of the Sender Bellman value.  The continuation
coefficient is `D_S / 4` because full-width smoothing has slope `D_S / 2`
and the Sender discount factor is `1/2`. -/
noncomputable def mwEqSenderGain (x : ℝ) : ℝ :=
  mwU_S x (mwEqLeaderPolicy x)
      (mwEqSenderRule x (mwEqLeaderPolicy x))
    + (mwEqSenderSpread / 4) *
      mechanismWitnessParams.F x (mwEqSenderRule x (mwEqLeaderPolicy x))

theorem mwEqSenderGain_continuous : Continuous mwEqSenderGain := by
  unfold mwEqSenderGain mwU_S
  simp only [mechanismWitnessParams_F]
  unfold AbstractGame.affineF
  fun_prop

@[simp] theorem mwEqSenderGain_zero : mwEqSenderGain 0 = 0 := by
  unfold mwEqSenderGain
  rw [show mwEqSenderRule 0 (mwEqLeaderPolicy 0) = 0 from mwEqSenderRule_zero,
    mwEqLeaderPolicy_zero]
  simp [mwU_S, mechanismWitnessParams_F,
    AbstractGame.affineF]

theorem mwEqSenderGain_one : mwEqSenderGain 1 = mwEqSenderSpread := by
  have hp := mwEq_sender_spread_polynomial
  unfold mwEqSenderGain
  rw [mwEqSenderRule_one, mwEqLeaderPolicy_one]
  simp only [mechanismWitnessParams_F]
  unfold mwEqSenderVertex mwEqLeaderVertex mwU_S AbstractGame.affineF
  field_simp at *
  nlinarith

/-- Additive constant that makes the explicit Sender value solve the full
Bellman level equation, not only its endpoint-spread equation. -/
noncomputable def mwEqSenderValueConst : ℝ :=
  (1 / 2) *
    (mwEqSenderGain 0 + ∫ z in (0 : ℝ)..1, mwEqSenderGain z)

/-- The explicit full-width Sender value. -/
noncomputable def mwEqSenderValue : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : ↥(Sanctions.S : Set ℝ) =>
        mwEqSenderGain x.val + mwEqSenderValueConst,
      mwEqSenderGain_continuous.comp continuous_subtype_val
        |>.add continuous_const⟩

@[simp] theorem mwEqSenderValue_apply
    (x : ↥(Sanctions.S : Set ℝ)) :
    mwEqSenderValue x = mwEqSenderGain x.val + mwEqSenderValueConst := rfl

theorem mwEqSenderValue_clip_apply {x : ℝ} (hx : x ∈ Sanctions.S) :
    mwEqSenderValue (Sanctions.clipS' x) =
      mwEqSenderGain x + mwEqSenderValueConst := by
  rw [mwEqSenderValue_apply, Sanctions.clipS'_val_eq_of_mem hx]

theorem mwEqSenderValue_endpoint_spread :
    mwEqSenderValue (Sanctions.clipS' 1)
        - mwEqSenderValue (Sanctions.clipS' 0) =
      mwEqSenderSpread := by
  rw [mwEqSenderValue_clip_apply (by norm_num),
    mwEqSenderValue_clip_apply (by norm_num),
    mwEqSenderGain_one, mwEqSenderGain_zero]
  ring

theorem mwEqSenderValue_integral :
    (∫ z in (0 : ℝ)..1,
        mwEqSenderValue (Sanctions.clipS' z)) =
      (∫ z in (0 : ℝ)..1, mwEqSenderGain z) + mwEqSenderValueConst := by
  have hg : IntervalIntegrable mwEqSenderGain MeasureTheory.volume (0 : ℝ) 1 :=
    mwEqSenderGain_continuous.intervalIntegrable 0 1
  have hc : IntervalIntegrable (fun _z : ℝ => mwEqSenderValueConst)
      MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_const.intervalIntegrable 0 1
  calc
    (∫ z in (0 : ℝ)..1, mwEqSenderValue (Sanctions.clipS' z)) =
        ∫ z in (0 : ℝ)..1, (mwEqSenderGain z + mwEqSenderValueConst) := by
          apply intervalIntegral.integral_congr
          intro z hz
          rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
          exact mwEqSenderValue_clip_apply hz
    _ = (∫ z in (0 : ℝ)..1, mwEqSenderGain z)
          + ∫ _z in (0 : ℝ)..1, mwEqSenderValueConst :=
        intervalIntegral.integral_add hg hc
    _ = (∫ z in (0 : ℝ)..1, mwEqSenderGain z)
          + mwEqSenderValueConst := by
        rw [intervalIntegral.integral_const]
        norm_num

/-- Closed form of the smeared explicit Sender value on the physical state
interval. -/
theorem mwEqSenderSmear_eq (y : ↥(Sanctions.S : Set ℝ)) :
    Sanctions.movAvgBCF one_pos mwEqSenderValue y =
      2 * mwEqSenderValueConst + (mwEqSenderSpread / 2) * y.val := by
  rw [Sanctions.movAvgBCF_apply,
    Sanctions.movAvgReal_one_eq_on_S mwEqSenderValue y.property,
    mwEqSenderValue_clip_apply (by norm_num),
    mwEqSenderValue_clip_apply (by norm_num),
    mwEqSenderValue_integral, mwEqSenderGain_zero, mwEqSenderGain_one]
  unfold mwEqSenderValueConst
  rw [mwEqSenderGain_zero]
  ring

/-- The existing greatest dynamic Sender argmax coincides with the explicit
clipped rule at the constructed Sender value. -/
theorem mwEq_sigma_dyn_top_eq {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne mwEqSenderValue) x a =
      mwEqSenderRule x a := by
  rw [mwSigmaDynTop_eq_clip_vertex_one mwEqSenderValue hx a]
  unfold mwEqSenderRule mwEqSenderVertex mwSenderVertexOne
  rw [mwEqSenderValue_endpoint_spread]
  ring_nf

/-- The explicit Sender value solves the shocked Bellman fixed-point equation
under the constructed leader policy. -/
theorem mwEqSenderValue_fix :
    mwEqSenderValue =
      (mwShocked one_pos).bellmanS_shock
        mwEqLeaderPolicy mwEqLeaderPolicy_continuous mwEqSenderValue := by
  apply BoundedContinuousFunction.ext
  intro x
  symm
  change mechanismWitnessParams.bellmanS_BCF
      mwEqLeaderPolicy mwEqLeaderPolicy_continuous
      (mwSenderValueOne mwEqSenderValue) x = mwEqSenderValue x
  let sStar := mechanismWitnessParams.σ_dyn_top
    (mwSenderValueOne mwEqSenderValue) x.val (mwEqLeaderPolicy x.val)
  have hs : sStar ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I
      (mwSenderValueOne mwEqSenderValue) x.val (mwEqLeaderPolicy x.val)
  have hmax : IsMaxOn
      (fun s => mechanismWitnessParams.U_S x.val (mwEqLeaderPolicy x.val) s
        + mechanismWitnessParams.β_S
          * mwSenderValueOne mwEqSenderValue
            (Sanctions.clipS' (mechanismWitnessParams.F x.val s)))
      Sanctions.I sStar := by
    simpa [sStar, AbstractGame.Params.senderDynObjective] using
      mechanismWitnessParams.σ_dyn_top_isMaxOn
        (mwSenderValueOne mwEqSenderValue) x.val (mwEqLeaderPolicy x.val)
  rw [WitnessKit.bellmanS_image_of_isMaxOn
    mwEqLeaderPolicy_continuous (mwSenderValueOne mwEqSenderValue) x hs hmax]
  have hs_eq : sStar = mwEqSenderRule x.val (mwEqLeaderPolicy x.val) := by
    exact mwEq_sigma_dyn_top_eq x.property (mwEqLeaderPolicy x.val)
  rw [hs_eq]
  have hF : mechanismWitnessParams.F x.val
      (mwEqSenderRule x.val (mwEqLeaderPolicy x.val)) ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x.val
      (mwEqSenderRule x.val (mwEqLeaderPolicy x.val))
      x.property (mwEqSenderRule_mem _ _)
  change mwU_S x.val (mwEqLeaderPolicy x.val)
      (mwEqSenderRule x.val (mwEqLeaderPolicy x.val))
      + (1 / 2) * Sanctions.movAvgBCF one_pos mwEqSenderValue
        (Sanctions.clipS' (mechanismWitnessParams.F x.val
          (mwEqSenderRule x.val (mwEqLeaderPolicy x.val)))) =
    mwEqSenderGain x.val + mwEqSenderValueConst
  rw [mwEqSenderSmear_eq]
  rw [Sanctions.clipS'_val_eq_of_mem hF]
  unfold mwEqSenderGain
  ring

/-! ## 4. Global Target optimality -/

theorem mwEqLeaderPolicy_eq_zero {x : ℝ}
    (h : mwEqLeaderVertex x ≤ 0) :
    mwEqLeaderPolicy x = 0 := by
  unfold mwEqLeaderPolicy
  exact max_eq_left h

theorem mwEqLeaderPolicy_eq_vertex {x : ℝ}
    (h : 0 ≤ mwEqLeaderVertex x) :
    mwEqLeaderPolicy x = mwEqLeaderVertex x := by
  unfold mwEqLeaderPolicy
  exact max_eq_right h

/-- The explicit equilibrium leader action is weakly increasing in the
political state. -/
theorem mwEqLeaderPolicy_monotone : Monotone mwEqLeaderPolicy := by
  intro x y hxy
  unfold mwEqLeaderPolicy
  apply max_le_max_left
  unfold mwEqLeaderVertex
  linarith

/-- Even after accounting for the equilibrium leader's increasing compliance
choice, the Sender's unconstrained sanction vertex is increasing in the state. -/
theorem mwEqSenderVertex_along_leader_monotone :
    Monotone (fun x => mwEqSenderVertex x (mwEqLeaderPolicy x)) := by
  intro x y hxy
  change
    mwEqSenderVertex x (mwEqLeaderPolicy x) ≤
      mwEqSenderVertex y (mwEqLeaderPolicy y)
  by_cases hy : mwEqLeaderVertex y ≤ 0
  · have hx : mwEqLeaderVertex x ≤ 0 := by
      unfold mwEqLeaderVertex at hy ⊢
      linarith
    rw [mwEqLeaderPolicy_eq_zero hx, mwEqLeaderPolicy_eq_zero hy]
    unfold mwEqSenderVertex
    linarith
  · have hypos : 0 < mwEqLeaderVertex y := lt_of_not_ge hy
    rw [mwEqLeaderPolicy_eq_vertex hypos.le]
    by_cases hx : mwEqLeaderVertex x ≤ 0
    · rw [mwEqLeaderPolicy_eq_zero hx]
      unfold mwEqSenderVertex mwEqLeaderVertex at *
      nlinarith
    · have hxpos : 0 < mwEqLeaderVertex x := lt_of_not_ge hx
      rw [mwEqLeaderPolicy_eq_vertex hxpos.le]
      unfold mwEqSenderVertex mwEqLeaderVertex
      linarith

/-- Clipping preserves the preceding monotonicity, so the equilibrium Sender
sanction rule is weakly increasing in the political state. -/
theorem mwEqSenderRule_along_leader_monotone :
    Monotone (fun x => mwEqSenderRule x (mwEqLeaderPolicy x)) := by
  intro x y hxy
  change
    max 0 (min 1 (mwEqSenderVertex x (mwEqLeaderPolicy x))) ≤
      max 0 (min 1 (mwEqSenderVertex y (mwEqLeaderPolicy y)))
  apply max_le_max_left
  apply min_le_min_left
  exact mwEqSenderVertex_along_leader_monotone hxy

/-- On physical states, the equilibrium's actual greatest-response rule is the
explicit clipped Sender rule. -/
theorem mwEqDynamicTopRealizedRule_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x =
      mwEqSenderRule x (mwEqLeaderPolicy x) := by
  exact mwEq_sigma_dyn_top_eq hx (mwEqLeaderPolicy x)

/-- **Equilibrium dominance monotonicity.**  The realized sanction rule of the
explicit unconditional equilibrium is weakly increasing on the physical state
space.  Both actions in this rule are the proved equilibrium optimizers. -/
theorem mwEqDynamicTopRealizedRule_monotoneOn :
    MonotoneOn
      (mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy)
      Sanctions.S := by
  intro x hx y hy hxy
  rw [mwEqDynamicTopRealizedRule_eq hx, mwEqDynamicTopRealizedRule_eq hy]
  exact mwEqSenderRule_along_leader_monotone hxy

/-! ## 4a. Interval dominance after the realized equilibrium policy

The preceding monotonicity proof uses the explicit clipped Sender rule.  The
next declarations establish the stronger order-theoretic statement requested
by the manuscript: after substituting the Target's actual equilibrium policy,
the Sender objective has increasing differences and therefore satisfies
interval dominance. -/

/-- The equilibrium Target policy, after subtracting the state coefficient
that enters the Sender's sanction incentive, is non-increasing.  This is the
explicit-equilibrium counterpart of
`mwCanonicalLeaderOne_adjusted_antitoneOn`. -/
theorem mwEqLeaderPolicy_adjusted_antitoneOn :
    ∀ x₁ ∈ Sanctions.S, ∀ x₂ ∈ Sanctions.S, x₁ ≤ x₂ →
      mwEqLeaderPolicy x₂ - (27 / 10) * x₂ ≤
        mwEqLeaderPolicy x₁ - (27 / 10) * x₁ := by
  intro x₁ hx₁ x₂ hx₂ hxx
  by_cases h₂ : mwEqLeaderVertex x₂ ≤ 0
  · have h₁ : mwEqLeaderVertex x₁ ≤ 0 := by
      unfold mwEqLeaderVertex at h₂ ⊢
      nlinarith
    rw [mwEqLeaderPolicy_eq_zero h₁, mwEqLeaderPolicy_eq_zero h₂]
    nlinarith
  · have h₂pos : 0 < mwEqLeaderVertex x₂ := lt_of_not_ge h₂
    rw [mwEqLeaderPolicy_eq_vertex h₂pos.le]
    by_cases h₁ : mwEqLeaderVertex x₁ ≤ 0
    · rw [mwEqLeaderPolicy_eq_zero h₁]
      unfold mwEqLeaderVertex at h₁ ⊢
      nlinarith
    · have h₁pos : 0 < mwEqLeaderVertex x₁ := lt_of_not_ge h₁
      rw [mwEqLeaderPolicy_eq_vertex h₁pos.le]
      unfold mwEqLeaderVertex
      nlinarith

/-- At the explicit equilibrium continuation value, the Sender's dynamic
objective has increasing differences in sanctions and the political state
after substituting the realized Target policy. -/
theorem mwEqSenderDynObjective_realized_increasingDifferencesOn :
    Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.S
      (fun s x => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne mwEqSenderValue) x (mwEqLeaderPolicy x) s) := by
  intro s s' x x' hs hs' hss hx hx' hxx
  have hb := mwEqLeaderPolicy_adjusted_antitoneOn x hx x' hx' hxx
  have hFxs : mechanismWitnessParams.F x s ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x s hx hs
  have hFxs' : mechanismWitnessParams.F x s' ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x s' hx hs'
  have hFx's : mechanismWitnessParams.F x' s ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x' s hx' hs
  have hFx's' : mechanismWitnessParams.F x' s' ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x' s' hx' hs'
  have hslope_x := Sanctions.movAvgBCF_one_sub_eq mwEqSenderValue
    (Sanctions.clipS' (mechanismWitnessParams.F x s))
    (Sanctions.clipS' (mechanismWitnessParams.F x s'))
  have hslope_x' := Sanctions.movAvgBCF_one_sub_eq mwEqSenderValue
    (Sanctions.clipS' (mechanismWitnessParams.F x' s))
    (Sanctions.clipS' (mechanismWitnessParams.F x' s'))
  rw [Sanctions.clipS'_val_eq_of_mem hFxs,
    Sanctions.clipS'_val_eq_of_mem hFxs'] at hslope_x
  rw [Sanctions.clipS'_val_eq_of_mem hFx's,
    Sanctions.clipS'_val_eq_of_mem hFx's'] at hslope_x'
  change mwU_S x (mwEqLeaderPolicy x) s'
        + (1 / 2) * Sanctions.movAvgBCF one_pos mwEqSenderValue
          (Sanctions.clipS' (mechanismWitnessParams.F x s'))
      - (mwU_S x (mwEqLeaderPolicy x) s
        + (1 / 2) * Sanctions.movAvgBCF one_pos mwEqSenderValue
          (Sanctions.clipS' (mechanismWitnessParams.F x s))) ≤
    mwU_S x' (mwEqLeaderPolicy x') s'
        + (1 / 2) * Sanctions.movAvgBCF one_pos mwEqSenderValue
          (Sanctions.clipS' (mechanismWitnessParams.F x' s'))
      - (mwU_S x' (mwEqLeaderPolicy x') s
        + (1 / 2) * Sanctions.movAvgBCF one_pos mwEqSenderValue
          (Sanctions.clipS' (mechanismWitnessParams.F x' s)))
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope_x hslope_x'
  unfold mwU_S
  simp only [mechanismWitnessParams_F, AbstractGame.affineF]
  nlinarith [hslope_x, hslope_x']

/-- **Realized-policy interval dominance at the explicit equilibrium.**
Both the Target policy and the Sender continuation value in this statement are
the optimizers and value function packaged in `mwEqEquilibrium`; no free policy
is substituted. -/
theorem mwEqSenderDynObjective_realized_IDOFamilyOn :
    Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I Sanctions.S
      (fun s x => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne mwEqSenderValue) x (mwEqLeaderPolicy x) s) :=
  Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
    mwEqSenderDynObjective_realized_increasingDifferencesOn.toSingleCrossingOn

theorem mwEqSenderRule_eq_zero {x a : ℝ}
    (h : mwEqSenderVertex x a ≤ 0) :
    mwEqSenderRule x a = 0 := by
  unfold mwEqSenderRule
  rw [min_eq_right (le_trans h (by norm_num)), max_eq_left h]

theorem mwEqSenderRule_eq_vertex {x a : ℝ}
    (h0 : 0 ≤ mwEqSenderVertex x a)
    (h1 : mwEqSenderVertex x a ≤ 1) :
    mwEqSenderRule x a = mwEqSenderVertex x a := by
  unfold mwEqSenderRule
  rw [min_eq_right h1, max_eq_right h0]

theorem mwEqSenderRule_eq_one {x a : ℝ}
    (h : 1 ≤ mwEqSenderVertex x a) :
    mwEqSenderRule x a = 1 := by
  unfold mwEqSenderRule
  rw [min_eq_left h, max_eq_right (by norm_num)]

/-- Target choice payoff after removing the action-independent level of the
smeared Target continuation. -/
noncomputable def mwEqTargetChoiceGain (x a : ℝ) : ℝ :=
  mwU_T x a (mwEqSenderRule x a)
    + (9 / 20) * mwEqTargetSpread
      * mechanismWitnessParams.F x (mwEqSenderRule x a)

/-- Raw Target payoff in the lower-clipped Sender region. -/
noncomputable def mwEqTargetGainZero (x a : ℝ) : ℝ :=
  mwU_T x a 0
    + (9 / 20) * mwEqTargetSpread * mechanismWitnessParams.F x 0

/-- Raw Target payoff in the interior Sender region. -/
noncomputable def mwEqTargetGainInterior (x a : ℝ) : ℝ :=
  mwU_T x a (mwEqSenderVertex x a)
    + (9 / 20) * mwEqTargetSpread
      * mechanismWitnessParams.F x (mwEqSenderVertex x a)

/-- Raw Target payoff in the upper-clipped Sender region. -/
noncomputable def mwEqTargetGainOne (x a : ℝ) : ℝ :=
  mwU_T x a 1
    + (9 / 20) * mwEqTargetSpread * mechanismWitnessParams.F x 1

theorem mwEqTargetChoiceGain_eq_zero {x a : ℝ}
    (h : mwEqSenderVertex x a ≤ 0) :
    mwEqTargetChoiceGain x a = mwEqTargetGainZero x a := by
  rw [mwEqTargetChoiceGain, mwEqTargetGainZero,
    mwEqSenderRule_eq_zero h]

theorem mwEqTargetChoiceGain_eq_interior {x a : ℝ}
    (h0 : 0 ≤ mwEqSenderVertex x a)
    (h1 : mwEqSenderVertex x a ≤ 1) :
    mwEqTargetChoiceGain x a = mwEqTargetGainInterior x a := by
  rw [mwEqTargetChoiceGain, mwEqTargetGainInterior,
    mwEqSenderRule_eq_vertex h0 h1]

theorem mwEqTargetChoiceGain_eq_one {x a : ℝ}
    (h : 1 ≤ mwEqSenderVertex x a) :
    mwEqTargetChoiceGain x a = mwEqTargetGainOne x a := by
  rw [mwEqTargetChoiceGain, mwEqTargetGainOne,
    mwEqSenderRule_eq_one h]

/-- Action at which the Sender vertex crosses zero. -/
noncomputable def mwEqZeroBoundary (x : ℝ) : ℝ :=
  (mwEqSenderSpread + 27 * x - 2) / 10

/-- Action at which the Sender vertex crosses one. -/
noncomputable def mwEqOneBoundary (x : ℝ) : ℝ :=
  (mwEqSenderSpread + 27 * x - 26) / 10

theorem mwEqSenderVertex_eq_zero_boundary (x a : ℝ) :
    mwEqSenderVertex x a = (5 / 12) * (mwEqZeroBoundary x - a) := by
  unfold mwEqSenderVertex mwEqZeroBoundary
  ring

theorem mwEqSenderVertex_sub_one_eq_boundary (x a : ℝ) :
    mwEqSenderVertex x a - 1 =
      (5 / 12) * (mwEqOneBoundary x - a) := by
  unfold mwEqSenderVertex mwEqOneBoundary
  ring

/-- Complete-the-square identity for the interior Target branch. -/
theorem mwEqTargetInterior_vertex_gap (x a : ℝ) :
    mwEqTargetGainInterior x (mwEqLeaderVertex x)
        - mwEqTargetGainInterior x a =
      (5 * mwEqSenderSpread - 9 * mwEqTargetSpread - 580 * a
        + 515 * x - 200) ^ 2 / 278400 := by
  simp only [mwEqTargetGainInterior, mwEqSenderVertex, mwU_T,
    mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqLeaderVertex
  ring

/-- Interior payoff loss relative to the lower action boundary `a = 0`. -/
theorem mwEqTargetInterior_zero_gap (x a : ℝ) :
    mwEqTargetGainInterior x 0 - mwEqTargetGainInterior x a =
      -a * (5 * mwEqSenderSpread - 9 * mwEqTargetSpread - 290 * a
        + 515 * x - 200) / 240 := by
  simp only [mwEqTargetGainInterior, mwEqSenderVertex, mwU_T,
    mechanismWitnessParams_F]
  unfold AbstractGame.affineF
  ring

theorem mwEqTarget_zero_boundary_value (x : ℝ) :
    mwEqTargetGainZero x (mwEqZeroBoundary x) =
      mwEqTargetGainInterior x (mwEqZeroBoundary x) := by
  simp only [mwEqTargetGainZero, mwEqTargetGainInterior,
    mwEqSenderVertex, mwU_T, mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqZeroBoundary
  ring

theorem mwEqTarget_one_boundary_value (x : ℝ) :
    mwEqTargetGainOne x (mwEqOneBoundary x) =
      mwEqTargetGainInterior x (mwEqOneBoundary x) := by
  simp only [mwEqTargetGainOne, mwEqTargetGainInterior,
    mwEqSenderVertex, mwU_T, mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqOneBoundary
  ring

theorem mwEqTargetZero_boundary_gap (x a : ℝ) :
    mwEqTargetGainZero x (mwEqZeroBoundary x)
        - mwEqTargetGainZero x a =
      -(mwEqSenderSpread - 10 * a + 27 * x - 2)
        * (mwEqSenderSpread + 10 * a + 7 * x + 8) / 100 := by
  simp only [mwEqTargetGainZero, mwU_T, mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqZeroBoundary
  ring

theorem mwEqTargetInterior_zero_boundary_gap (x : ℝ) :
    mwEqTargetGainInterior x 0
        - mwEqTargetGainInterior x (mwEqZeroBoundary x) =
      (mwEqSenderSpread + 27 * x - 2)
        * (24 * mwEqSenderSpread + 9 * mwEqTargetSpread + 268 * x + 142)
          / 2400 := by
  simp only [mwEqTargetGainInterior, mwEqSenderVertex, mwU_T,
    mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqZeroBoundary
  ring

theorem mwEqTargetOne_boundary_gap (x a : ℝ) :
    mwEqTargetGainOne x (mwEqOneBoundary x)
        - mwEqTargetGainOne x a =
      -(mwEqSenderSpread - 10 * a + 27 * x - 26)
        * (mwEqSenderSpread + 10 * a + 7 * x - 21) / 100 := by
  simp only [mwEqTargetGainOne, mwU_T, mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqOneBoundary
  ring

theorem mwEqTargetInterior_one_boundary_gap (x : ℝ) :
    mwEqTargetGainInterior x (mwEqLeaderVertex x)
        - mwEqTargetGainInterior x (mwEqOneBoundary x) =
      (53 * mwEqSenderSpread + 9 * mwEqTargetSpread + 1051 * x - 1308) ^ 2
        / 278400 := by
  simp only [mwEqTargetGainInterior, mwEqSenderVertex, mwU_T,
    mechanismWitnessParams_F]
  unfold AbstractGame.affineF mwEqLeaderVertex mwEqOneBoundary
  ring

/-- **Global leader optimum.**  The piecewise-affine policy maximizes the
actual Target choice payoff through both Sender clipping kinks. -/
theorem mwEqLeaderPolicy_isMaxOn (x : ℝ) (hx : x ∈ Sanctions.S) :
    IsMaxOn (fun a => mwEqTargetChoiceGain x a)
      Sanctions.I (mwEqLeaderPolicy x) := by
  rw [isMaxOn_iff]
  intro a ha
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  by_cases hL : mwEqLeaderVertex x ≤ 0
  · have hpol : mwEqLeaderPolicy x = 0 := mwEqLeaderPolicy_eq_zero hL
    rw [hpol]
    by_cases hv0 : mwEqSenderVertex x 0 ≤ 0
    · have hva : mwEqSenderVertex x a ≤ 0 := by
        unfold mwEqSenderVertex at hv0 ⊢
        nlinarith [ha.1]
      rw [mwEqTargetChoiceGain_eq_zero hva,
        mwEqTargetChoiceGain_eq_zero hv0]
      have hxhalf : x ≤ 1 / 2 := by
        unfold mwEqLeaderVertex at hL
        nlinarith
      simp only [mwEqTargetGainZero, mwU_T, mechanismWitnessParams_F]
      unfold AbstractGame.affineF
      have hfac : 0 ≤ a + 1 - 2 * x := by
        nlinarith [ha.1, hxhalf]
      nlinarith [mul_nonneg ha.1 hfac]
    · have hv0pos : 0 < mwEqSenderVertex x 0 := lt_of_not_ge hv0
      have hv0one : mwEqSenderVertex x 0 ≤ 1 := by
        have hLlin := hL
        unfold mwEqLeaderVertex at hLlin
        unfold mwEqSenderVertex
        nlinarith [hx.2, hLlin]
      rw [mwEqTargetChoiceGain_eq_interior hv0pos.le hv0one]
      by_cases hva0 : mwEqSenderVertex x a ≤ 0
      · rw [mwEqTargetChoiceGain_eq_zero hva0]
        have hb0_nonneg : 0 ≤ mwEqZeroBoundary x := by
          rw [mwEqSenderVertex_eq_zero_boundary x 0] at hv0pos
          nlinarith
        have hb0_le_a : mwEqZeroBoundary x ≤ a := by
          rw [mwEqSenderVertex_eq_zero_boundary x a] at hva0
          nlinarith
        have hfac_pos :
            0 ≤ mwEqSenderSpread + 10 * a + 7 * x + 8 := by
          nlinarith [ha.1, hx.1]
        have hzero_gap : 0 ≤
            mwEqTargetGainZero x (mwEqZeroBoundary x)
              - mwEqTargetGainZero x a := by
          rw [mwEqTargetZero_boundary_gap]
          have hfirst :
              mwEqSenderSpread - 10 * a + 27 * x - 2 ≤ 0 := by
            unfold mwEqSenderVertex at hva0
            nlinarith
          have hprod := mul_nonneg (neg_nonneg.mpr hfirst) hfac_pos
          nlinarith
        have hinterior_gap : 0 ≤
            mwEqTargetGainInterior x 0
              - mwEqTargetGainInterior x (mwEqZeroBoundary x) := by
          rw [mwEqTargetInterior_zero_boundary_gap]
          have hfirst : 0 ≤ mwEqSenderSpread + 27 * x - 2 := by
            unfold mwEqZeroBoundary at hb0_nonneg
            nlinarith
          have hsecond :
              0 ≤ 24 * mwEqSenderSpread + 9 * mwEqTargetSpread
                + 268 * x + 142 := by
            nlinarith [hx.1]
          positivity
        rw [← mwEqTarget_zero_boundary_value x] at hinterior_gap
        linarith
      · have hva_pos : 0 < mwEqSenderVertex x a := lt_of_not_ge hva0
        have hva_one : mwEqSenderVertex x a ≤ 1 := by
          unfold mwEqSenderVertex at hv0one ⊢
          nlinarith [ha.1]
        rw [mwEqTargetChoiceGain_eq_interior hva_pos.le hva_one]
        have hnum :
            5 * mwEqSenderSpread - 9 * mwEqTargetSpread - 290 * a
                + 515 * x - 200 ≤ 0 := by
          unfold mwEqLeaderVertex at hL
          nlinarith [ha.1]
        have hgap : 0 ≤ mwEqTargetGainInterior x 0
            - mwEqTargetGainInterior x a := by
          rw [mwEqTargetInterior_zero_gap]
          have hprod := mul_nonneg ha.1 (neg_nonneg.mpr hnum)
          nlinarith
        linarith
  · have hLpos : 0 < mwEqLeaderVertex x := lt_of_not_ge hL
    have hpol : mwEqLeaderPolicy x = mwEqLeaderVertex x :=
      mwEqLeaderPolicy_eq_vertex hLpos.le
    rw [hpol]
    have hvpol0 : 0 ≤ mwEqSenderVertex x (mwEqLeaderVertex x) := by
      unfold mwEqSenderVertex mwEqLeaderVertex
      nlinarith [hx.1]
    have hvpol1 : mwEqSenderVertex x (mwEqLeaderVertex x) ≤ 1 := by
      unfold mwEqSenderVertex mwEqLeaderVertex
      nlinarith [hx.2]
    rw [mwEqTargetChoiceGain_eq_interior hvpol0 hvpol1]
    have hva_pos : 0 < mwEqSenderVertex x a := by
      unfold mwEqLeaderVertex at hLpos
      unfold mwEqSenderVertex
      nlinarith [ha.2]
    by_cases hva1 : 1 ≤ mwEqSenderVertex x a
    · rw [mwEqTargetChoiceGain_eq_one hva1]
      have hfirst :
          0 ≤ mwEqSenderSpread - 10 * a + 27 * x - 26 := by
        unfold mwEqSenderVertex at hva1
        nlinarith
      have hsecond :
          mwEqSenderSpread + 10 * a + 7 * x - 21 ≤ 0 := by
        nlinarith [ha.2, hx.2]
      have hone_gap : 0 ≤
          mwEqTargetGainOne x (mwEqOneBoundary x)
            - mwEqTargetGainOne x a := by
        rw [mwEqTargetOne_boundary_gap]
        have hprod := mul_nonneg hfirst (neg_nonneg.mpr hsecond)
        nlinarith
      have hinterior_gap : 0 ≤
          mwEqTargetGainInterior x (mwEqLeaderVertex x)
            - mwEqTargetGainInterior x (mwEqOneBoundary x) := by
        rw [mwEqTargetInterior_one_boundary_gap]
        positivity
      rw [← mwEqTarget_one_boundary_value x] at hinterior_gap
      linarith
    · have hva_lt : mwEqSenderVertex x a < 1 := lt_of_not_ge hva1
      rw [mwEqTargetChoiceGain_eq_interior hva_pos.le hva_lt.le]
      have hgap : 0 ≤
          mwEqTargetGainInterior x (mwEqLeaderVertex x)
            - mwEqTargetGainInterior x a := by
        rw [mwEqTargetInterior_vertex_gap]
        positivity
      linarith

/-! ## 5. Explicit Target value and unconditional equilibrium -/

/-- Nonconstant part of the Target value at the proved optimal policy. -/
noncomputable def mwEqTargetGain (x : ℝ) : ℝ :=
  mwEqTargetChoiceGain x (mwEqLeaderPolicy x)

theorem mwEqTargetGain_continuous : Continuous mwEqTargetGain := by
  unfold mwEqTargetGain mwEqTargetChoiceGain mwU_T
  simp only [mechanismWitnessParams_F]
  unfold AbstractGame.affineF
  fun_prop

@[simp] theorem mwEqTargetGain_zero : mwEqTargetGain 0 = 0 := by
  unfold mwEqTargetGain mwEqTargetChoiceGain
  have hr := mwEqSenderRule_zero
  rw [mwEqLeaderPolicy_zero] at hr
  rw [mwEqLeaderPolicy_zero, hr]
  simp [mwU_T, mechanismWitnessParams_F, AbstractGame.affineF]

theorem mwEqTargetGain_one : mwEqTargetGain 1 = mwEqTargetSpread := by
  have hp := mwEq_target_spread_polynomial
  unfold mwEqTargetGain mwEqTargetChoiceGain
  have hr := mwEqSenderRule_one
  rw [mwEqLeaderPolicy_one] at hr
  rw [mwEqLeaderPolicy_one, hr]
  simp only [mechanismWitnessParams_F]
  unfold mwEqSenderVertex mwEqLeaderVertex mwU_T AbstractGame.affineF
  field_simp at *
  nlinarith

/-- Additive constant solving the Target Bellman level equation. -/
noncomputable def mwEqTargetValueConst : ℝ :=
  (9 / 2) *
    (mwEqTargetGain 0 + ∫ z in (0 : ℝ)..1, mwEqTargetGain z)

/-- Explicit full-width Target value. -/
noncomputable def mwEqTargetValue : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : ↥(Sanctions.S : Set ℝ) =>
        mwEqTargetGain x.val + mwEqTargetValueConst,
      mwEqTargetGain_continuous.comp continuous_subtype_val
        |>.add continuous_const⟩

@[simp] theorem mwEqTargetValue_apply
    (x : ↥(Sanctions.S : Set ℝ)) :
    mwEqTargetValue x = mwEqTargetGain x.val + mwEqTargetValueConst := rfl

theorem mwEqTargetValue_clip_apply {x : ℝ} (hx : x ∈ Sanctions.S) :
    mwEqTargetValue (Sanctions.clipS' x) =
      mwEqTargetGain x + mwEqTargetValueConst := by
  rw [mwEqTargetValue_apply, Sanctions.clipS'_val_eq_of_mem hx]

theorem mwEqTargetValue_endpoint_spread :
    mwEqTargetValue (Sanctions.clipS' 1)
        - mwEqTargetValue (Sanctions.clipS' 0) =
      mwEqTargetSpread := by
  rw [mwEqTargetValue_clip_apply (by norm_num),
    mwEqTargetValue_clip_apply (by norm_num),
    mwEqTargetGain_one, mwEqTargetGain_zero]
  ring

theorem mwEqTargetValue_integral :
    (∫ z in (0 : ℝ)..1,
        mwEqTargetValue (Sanctions.clipS' z)) =
      (∫ z in (0 : ℝ)..1, mwEqTargetGain z) + mwEqTargetValueConst := by
  have hg : IntervalIntegrable mwEqTargetGain MeasureTheory.volume (0 : ℝ) 1 :=
    mwEqTargetGain_continuous.intervalIntegrable 0 1
  have hc : IntervalIntegrable (fun _z : ℝ => mwEqTargetValueConst)
      MeasureTheory.volume (0 : ℝ) 1 :=
    continuous_const.intervalIntegrable 0 1
  calc
    (∫ z in (0 : ℝ)..1, mwEqTargetValue (Sanctions.clipS' z)) =
        ∫ z in (0 : ℝ)..1, (mwEqTargetGain z + mwEqTargetValueConst) := by
          apply intervalIntegral.integral_congr
          intro z hz
          rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
          exact mwEqTargetValue_clip_apply hz
    _ = (∫ z in (0 : ℝ)..1, mwEqTargetGain z)
          + ∫ _z in (0 : ℝ)..1, mwEqTargetValueConst :=
        intervalIntegral.integral_add hg hc
    _ = (∫ z in (0 : ℝ)..1, mwEqTargetGain z)
          + mwEqTargetValueConst := by
        rw [intervalIntegral.integral_const]
        norm_num

/-- Closed form of the smeared Target value. -/
theorem mwEqTargetSmear_eq (y : ↥(Sanctions.S : Set ℝ)) :
    Sanctions.movAvgBCF one_pos mwEqTargetValue y =
      (10 / 9) * mwEqTargetValueConst
        + (mwEqTargetSpread / 2) * y.val := by
  rw [Sanctions.movAvgBCF_apply,
    Sanctions.movAvgReal_one_eq_on_S mwEqTargetValue y.property,
    mwEqTargetValue_clip_apply (by norm_num),
    mwEqTargetValue_clip_apply (by norm_num),
    mwEqTargetValue_integral, mwEqTargetGain_zero, mwEqTargetGain_one]
  unfold mwEqTargetValueConst
  rw [mwEqTargetGain_zero]
  ring

/-- The actual shocked leader objective is the reduced choice gain plus the
Target value's additive Bellman constant. -/
theorem mwEqLeaderObjective_eq
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos mwEqTargetValue)
      (mwSenderValueOne mwEqSenderValue) x a =
        mwEqTargetChoiceGain x a + mwEqTargetValueConst := by
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [mwEq_sigma_dyn_top_eq hx a]
  have hF : mechanismWitnessParams.F x (mwEqSenderRule x a) ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x (mwEqSenderRule x a)
      hx (mwEqSenderRule_mem _ _)
  rw [mwEqTargetSmear_eq]
  rw [Sanctions.clipS'_val_eq_of_mem hF]
  change mwU_T x a (mwEqSenderRule x a)
      + (9 / 10) *
        ((10 / 9) * mwEqTargetValueConst
          + mwEqTargetSpread / 2
            * mechanismWitnessParams.F x (mwEqSenderRule x a)) =
      mwEqTargetChoiceGain x a + mwEqTargetValueConst
  unfold mwEqTargetChoiceGain
  ring

theorem mwEqLeaderPolicy_actual_isMaxOn (x : ℝ) (hx : x ∈ Sanctions.S) :
    IsMaxOn
      (fun a => mechanismWitnessParams.joint_T_top_integrand
        (Sanctions.movAvgBCF one_pos mwEqTargetValue)
        (mwSenderValueOne mwEqSenderValue) x a)
      Sanctions.I (mwEqLeaderPolicy x) := by
  rw [isMaxOn_iff]
  intro a ha
  rw [mwEqLeaderObjective_eq hx a,
    mwEqLeaderObjective_eq hx (mwEqLeaderPolicy x)]
  have hmax := mwEqLeaderPolicy_isMaxOn x hx
  rw [isMaxOn_iff] at hmax
  simpa [add_comm] using
    (add_le_add_right (hmax a ha) mwEqTargetValueConst)

/-- The explicit Target value solves the shocked Target Bellman equation. -/
theorem mwEqTargetValue_fix (x : ↥(Sanctions.S : Set ℝ)) :
    mwEqTargetValue x =
      sSup ((fun a => mechanismWitnessParams.joint_T_top_integrand
        (Sanctions.movAvgBCF one_pos mwEqTargetValue)
        (mwSenderValueOne mwEqSenderValue) x.val a) '' Sanctions.I) := by
  let f : ℝ → ℝ := fun a => mechanismWitnessParams.joint_T_top_integrand
    (Sanctions.movAvgBCF one_pos mwEqTargetValue)
    (mwSenderValueOne mwEqSenderValue) x.val a
  have hmem : mwEqLeaderPolicy x.val ∈ Sanctions.I :=
    mwEqLeaderPolicy_mem x.val x.property
  have hmax : IsMaxOn f Sanctions.I (mwEqLeaderPolicy x.val) := by
    simpa [f] using mwEqLeaderPolicy_actual_isMaxOn x.val x.property
  have hgreatest : IsGreatest (f '' Sanctions.I) (f (mwEqLeaderPolicy x.val)) := by
    constructor
    · exact ⟨mwEqLeaderPolicy x.val, hmem, rfl⟩
    · rintro y ⟨a, ha, rfl⟩
      exact hmax ha
  rw [hgreatest.csSup_eq]
  change mwEqTargetGain x.val + mwEqTargetValueConst =
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos mwEqTargetValue)
      (mwSenderValueOne mwEqSenderValue) x.val (mwEqLeaderPolicy x.val)
  rw [mwEqLeaderObjective_eq x.property]
  rfl

/-- The explicitly constructed unconditional full-width P3 equilibrium. -/
noncomputable def mwEqEquilibrium :
    (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop where
  V_T := mwEqTargetValue
  V_S := mwEqSenderValue
  α := mwEqLeaderPolicy
  hα := mwEqLeaderPolicy_continuous
  α_mem := mwEqLeaderPolicy_mem
  V_S_fix_shock := by
    simpa [mwShocked, AbstractGame.movAvgShockedParams_smear] using
      mwEqSenderValue_fix
  V_T_fix_shock := by
    intro x
    simpa [mwShocked, AbstractGame.movAvgShockedParams_smear,
      mwSenderValueOne] using mwEqTargetValue_fix x
  α_opt_shock := by
    intro x hx
    simpa [mwShocked, AbstractGame.movAvgShockedParams_smear,
      mwSenderValueOne] using mwEqLeaderPolicy_actual_isMaxOn x hx

/-- **Unconditional full-width P3 shocked equilibrium existence.**

All strategies are equilibrium-derived and every analytic condition is
discharged in Lean.  In particular, this theorem has no strong-concavity,
cross-value/action coupling, carrier-invariance, or policy hypothesis. -/
theorem mechanismWitnessParams_purified_existence_unconditional_one :
    Nonempty (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop :=
  ⟨mwEqEquilibrium⟩

/-- **Unconditional full-width P3 equilibrium with endogenous monotonicity.**
The constructed equilibrium exists and its own equilibrium-derived realized
sanction rule is weakly increasing on the physical state space. -/
theorem mechanismWitnessParams_purified_existence_unconditional_one_monotone :
    ∃ E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop,
      MonotoneOn
        (mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne E.V_S) E.α)
        Sanctions.S := by
  exact ⟨mwEqEquilibrium, mwEqDynamicTopRealizedRule_monotoneOn⟩

/-- The explicit full-width equilibrium has a strictly increasing Sender
endpoint value: its continuation value is not constant. -/
theorem mwEqEquilibrium_sender_value_nonconstant :
    mwEqEquilibrium.V_S (Sanctions.clipS' 0) <
      mwEqEquilibrium.V_S (Sanctions.clipS' 1) := by
  change mwEqSenderValue (Sanctions.clipS' 0) <
    mwEqSenderValue (Sanctions.clipS' 1)
  have hspread := mwEqSenderValue_endpoint_spread
  have hlo := mwEqSenderSpread_bounds.1
  nlinarith

/-- The explicit full-width equilibrium also has a strictly increasing Target
endpoint value. -/
theorem mwEqEquilibrium_target_value_nonconstant :
    mwEqEquilibrium.V_T (Sanctions.clipS' 0) <
      mwEqEquilibrium.V_T (Sanctions.clipS' 1) := by
  change mwEqTargetValue (Sanctions.clipS' 0) <
    mwEqTargetValue (Sanctions.clipS' 1)
  have hspread := mwEqTargetValue_endpoint_spread
  have hlo := mwEqTargetSpread_bounds.1
  nlinarith

/-- **Mechanism activity at the top state.**  Holding fixed the Target's
equilibrium action, the Sender's forward-looking optimal sanction is strictly
above the Sender's myopic stage optimum.  The strict wedge is the positive
endpoint-spread correction `mwEqSenderSpread / 24` in the dynamic vertex. -/
theorem mwEqEquilibrium_sender_continuation_strict_at_top :
    mechanismWitnessParams.σ 1 (mwEqLeaderPolicy 1) <
      mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy 1 := by
  rw [mwEqDynamicTopRealizedRule_eq (by norm_num)]
  change mwσ 1 (mwEqLeaderPolicy 1) <
    mwEqSenderRule 1 (mwEqLeaderPolicy 1)
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  have hstatic0 :
      0 ≤ (25 / 24 : ℝ) - (5 / 12) * mwEqLeaderPolicy 1 := by
    rw [mwEqLeaderPolicy_one]
    unfold mwEqLeaderVertex
    nlinarith
  have hstatic1 :
      (25 / 24 : ℝ) - (5 / 12) * mwEqLeaderPolicy 1 ≤ 1 := by
    rw [mwEqLeaderPolicy_one]
    unfold mwEqLeaderVertex
    nlinarith
  obtain ⟨hdyn0, hdyn1⟩ := mwEqSenderVertex_top_mem
  unfold mwσ mwEqSenderRule
  norm_num only [mul_one]
  rw [min_eq_right hstatic1, max_eq_right hstatic0,
    min_eq_right hdyn1, max_eq_right hdyn0]
  unfold mwEqSenderVertex
  nlinarith

/-- The constructed equilibrium illustrates the sharp full-width boundary:
its realized sanction rule is monotone, but its top-state sanction is strictly
below one, so the stronger endpoint floor does not hold. -/
theorem mwEqEquilibrium_realizedRule_one_lt_one :
    mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α 1 < 1 := by
  exact lt_of_not_ge (mwShockedOne_no_top_floor mwEqEquilibrium)

/-- The equilibrium Target policy is genuinely state-varying: compliance is
zero at the bottom state and strictly positive at the top state. -/
theorem mwEqLeaderPolicy_endpoint_strict :
    mwEqLeaderPolicy 0 < mwEqLeaderPolicy 1 := by
  rw [mwEqLeaderPolicy_zero, mwEqLeaderPolicy_one]
  exact mwEqLeaderVertex_one_pos

/-- The equilibrium-derived realised sanction is zero at the bottom state. -/
theorem mwEqDynamicTopRealizedRule_zero :
    mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy 0 = 0 := by
  rw [mwEqDynamicTopRealizedRule_eq (by norm_num)]
  exact mwEqSenderRule_zero

/-- The equilibrium-derived realised sanction is strictly positive at the
top state.  This follows from the strict dynamic-over-myopic wedge and
feasibility of the myopic sanction. -/
theorem mwEqDynamicTopRealizedRule_one_pos :
    0 < mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy 1 := by
  have hstrict := mwEqEquilibrium_sender_continuation_strict_at_top
  have hmem := mechanismWitnessParams.σ_mem 1 (mwEqLeaderPolicy 1)
  exact lt_of_le_of_lt hmem.1 hstrict

/-- The realised equilibrium sanction is genuinely state-varying, not merely
weakly monotone. -/
theorem mwEqDynamicTopRealizedRule_endpoint_strict :
    mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy 0
      <
    mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy 1 := by
  rw [mwEqDynamicTopRealizedRule_zero]
  exact mwEqDynamicTopRealizedRule_one_pos

/-- **Strongest unconditional state-varying mechanism frontier.**  At one
fully constructed feedback Stackelberg equilibrium, both value functions
are nonconstant, the Target policy rises strictly between the endpoint
states, and the realised sanction rises from zero to a strictly interior
positive level.  This is an equilibrium state comparative static, not a
cross-economy policy-feedback theorem and not a two-sided coupled-carrier
existence result. -/
theorem mechanismWitnessParams_fullWidth_state_varying_frontier :
    mwEqEquilibrium.α 0 < mwEqEquilibrium.α 1 ∧
      mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α 0
        <
      mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α 1 ∧
      mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α 1 < 1 ∧
      mwEqEquilibrium.V_T (Sanctions.clipS' 0) <
        mwEqEquilibrium.V_T (Sanctions.clipS' 1) ∧
      mwEqEquilibrium.V_S (Sanctions.clipS' 0) <
        mwEqEquilibrium.V_S (Sanctions.clipS' 1) := by
  exact ⟨mwEqLeaderPolicy_endpoint_strict,
    mwEqDynamicTopRealizedRule_endpoint_strict,
    mwEqEquilibrium_realizedRule_one_lt_one,
    mwEqEquilibrium_target_value_nonconstant,
    mwEqEquilibrium_sender_value_nonconstant⟩

/-- Consequently, no nonempty basin ending at the top state can satisfy the
strong dynamic floor for this constructed equilibrium. -/
theorem mwEqEquilibrium_no_dynamic_floor
    {xbar sbar : ℝ} (hxbar1 : xbar ≤ 1) :
    ¬ (∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤ mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x) :=
  mwShockedOne_no_dynamic_floor mwEqEquilibrium hxbar1

/-- **Unconditional mechanism-active frontier at full-width `P3`.**

The exact equilibrium has nonconstant values for both players, a monotone
equilibrium-derived sanction rule, and a strict continuation-induced Sender
wedge over the myopic sanction at the top state.  Nevertheless, every
nonempty high basin ending at one fails the dynamic floor.  This isolates the
precise obstruction to combining the mechanism-active equilibrium with the
full persistence package at this transparent specialization. -/
theorem mechanismWitnessParams_fullWidth_mechanism_active_frontier :
    mwEqEquilibrium.V_T (Sanctions.clipS' 0) <
          mwEqEquilibrium.V_T (Sanctions.clipS' 1) ∧
      mwEqEquilibrium.V_S (Sanctions.clipS' 0) <
          mwEqEquilibrium.V_S (Sanctions.clipS' 1) ∧
      MonotoneOn
        (mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α)
        Sanctions.S ∧
      mechanismWitnessParams.σ 1 (mwEqEquilibrium.α 1) <
        mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α 1 ∧
      ∀ xbar sbar : ℝ, xbar ≤ 1 →
        ¬ (∀ x ∈ Set.Icc xbar 1,
          max x sbar ≤ mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne mwEqEquilibrium.V_S)
            mwEqEquilibrium.α x) := by
  refine ⟨mwEqEquilibrium_target_value_nonconstant,
    mwEqEquilibrium_sender_value_nonconstant,
    mwEqDynamicTopRealizedRule_monotoneOn,
    mwEqEquilibrium_sender_continuation_strict_at_top, ?_⟩
  intro xbar sbar hxbar
  exact mwEqEquilibrium_no_dynamic_floor hxbar

/-- **The mechanism witness has nondegenerate continuation stakes.**

The named form of the first two conjuncts of
`mechanismWitnessParams_fullWidth_mechanism_active_frontier`. Uses the
value-function form because this equilibrium lives in the **shocked** layer,
whose `V_T` and `V_S` have the same type but whose bundle does not. -/
theorem mw_continuationStakesNondegenerateOn :
    mechanismWitnessParams.ContinuationStakesNondegenerateOn
      mwEqEquilibrium.V_T mwEqEquilibrium.V_S := by
  obtain ⟨hT, hS, _rest⟩ := mechanismWitnessParams_fullWidth_mechanism_active_frontier
  exact AbstractGame.Params.continuationStakesNondegenerateOn_of_lt mechanismWitnessParams
    (by norm_num) (by norm_num) hT hS

#print axioms mw_continuationStakesNondegenerateOn

end

end Sanctions.Examples
