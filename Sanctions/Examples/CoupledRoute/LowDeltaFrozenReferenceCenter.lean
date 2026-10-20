/-
Sanctions/Examples/CoupledRoute/LowDeltaFrozenReferenceCenter.lean

Exact frozen-transition reference values for the low-adjustment coupled
problem.

At the static Stackelberg policies proved in
`LowDeltaStaticStackelberg`, freeze the inherited state in the continuation
channel while retaining the already-defined box shock.  Each reference value
is then constructed, rather than assumed, as the Banach fixed point

  V_i = g_i + beta_i * movAvgBCF(V_i).

These values are an internal comparison center for a later validated-local
argument.  This file does not identify them with the delta = 1/100
equilibrium values and does not add a model assumption.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticStackelberg
import Sanctions.Examples.CoupledRoute.CoupledCarrierRedesign

namespace Sanctions
namespace Examples

open Set
open AbstractGame
open scoped NNReal
open BoundedContinuousFunction

/-! ## Static-policy regularity -/

/-- The exact static Target policy is continuous. -/
@[fun_prop] theorem lowDeltaStaticTargetPolicy_continuous :
    Continuous lowDeltaStaticTargetPolicy := by
  rw [show lowDeltaStaticTargetPolicy =
      fun x => max 0 ((103 / 116) * x - 10 / 29) by
    funext x
    exact lowDeltaStaticTargetPolicy_eq x]
  fun_prop

/-- The exact static Sender policy is continuous. -/
@[fun_prop] theorem lowDeltaStaticSenderPolicy_continuous :
    Continuous lowDeltaStaticSenderPolicy := by
  unfold lowDeltaStaticSenderPolicy
  exact mwσ_continuous.comp
    (continuous_id.prodMk lowDeltaStaticTargetPolicy_continuous)

/-- The exact static Sender policy is feasible at every real state. -/
theorem lowDeltaStaticSenderPolicy_mem (x : ℝ) :
    lowDeltaStaticSenderPolicy x ∈ Sanctions.I := by
  exact mwσ_mem x (lowDeltaStaticTargetPolicy x)

/-! ## Frozen stage-value functions -/

/-- Target stage payoff under the exact static Stackelberg policies. -/
noncomputable def lowDeltaFrozenTargetStage : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x =>
        mwU_T x.val
          (lowDeltaStaticTargetPolicy x.val)
          (lowDeltaStaticSenderPolicy x.val),
      mwU_T_continuous.comp
        (continuous_subtype_val.prodMk
          ((lowDeltaStaticTargetPolicy_continuous.comp continuous_subtype_val).prodMk
            (lowDeltaStaticSenderPolicy_continuous.comp continuous_subtype_val)))⟩

/-- Sender stage payoff under the exact static Stackelberg policies. -/
noncomputable def lowDeltaFrozenSenderStage : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x =>
        mwU_S x.val
          (lowDeltaStaticTargetPolicy x.val)
          (lowDeltaStaticSenderPolicy x.val),
      mwU_S_continuous.comp
        (continuous_subtype_val.prodMk
          ((lowDeltaStaticTargetPolicy_continuous.comp continuous_subtype_val).prodMk
            (lowDeltaStaticSenderPolicy_continuous.comp continuous_subtype_val)))⟩

@[simp] theorem lowDeltaFrozenTargetStage_apply
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaFrozenTargetStage x =
      mwU_T x.val
        (lowDeltaStaticTargetPolicy x.val)
        (lowDeltaStaticSenderPolicy x.val) := rfl

@[simp] theorem lowDeltaFrozenSenderStage_apply
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaFrozenSenderStage x =
      mwU_S x.val
        (lowDeltaStaticTargetPolicy x.val)
        (lowDeltaStaticSenderPolicy x.val) := rfl

/-- Exact sup-norm bound for the frozen Target stage value. -/
theorem lowDeltaFrozenTargetStage_norm_le :
    ‖lowDeltaFrozenTargetStage‖ ≤ 2 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs, lowDeltaFrozenTargetStage_apply]
  simpa only [lowDeltaShocked_toParams, lowDeltaParams_U_T] using
    lowDelta_UT_cube_bound
      x.val x.property
      (lowDeltaStaticTargetPolicy x.val)
      (lowDeltaStaticTargetPolicy_mem x.property)
      (lowDeltaStaticSenderPolicy x.val)
      (lowDeltaStaticSenderPolicy_mem x.val)

/-- Exact sup-norm bound for the frozen Sender stage value. -/
theorem lowDeltaFrozenSenderStage_norm_le :
    ‖lowDeltaFrozenSenderStage‖ ≤ 523 / 320 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num)]
  intro x
  rw [Real.norm_eq_abs, lowDeltaFrozenSenderStage_apply]
  simpa only [lowDeltaParams_U_S] using
    lowDelta_US_cube_bound
      x.val x.property
      (lowDeltaStaticTargetPolicy x.val)
      (lowDeltaStaticTargetPolicy_mem x.property)
      (lowDeltaStaticSenderPolicy x.val)
      (lowDeltaStaticSenderPolicy_mem x.val)

/-! ## Exact affine contractions -/

/-- Affine frozen-transition Bellman map with stage value `g` and discount
factor `beta`. -/
noncomputable def lowDeltaFrozenAffineOperator
    (β : ℝ) (g V : SBCF) : SBCF :=
  g + β • Sanctions.movAvgBCF lowDeltaH_pos V

/-- Pointwise contraction estimate for the affine frozen operator. -/
theorem lowDeltaFrozenAffineOperator_pointwise_dist
    (β : ℝ) (hβ : 0 ≤ β) (g V W : SBCF)
    (x : ↥(Sanctions.S : Set ℝ)) :
    dist (lowDeltaFrozenAffineOperator β g V x)
        (lowDeltaFrozenAffineOperator β g W x)
      ≤ β * dist V W := by
  have hMglobal :=
    Sanctions.movAvgBCF_dist_le lowDeltaH_pos V W
  have hM :
      dist (Sanctions.movAvgBCF lowDeltaH_pos V x)
          (Sanctions.movAvgBCF lowDeltaH_pos W x)
        ≤ dist V W :=
    (BoundedContinuousFunction.dist_le dist_nonneg).mp hMglobal x
  change
    dist
        (g x + β * Sanctions.movAvgBCF lowDeltaH_pos V x)
        (g x + β * Sanctions.movAvgBCF lowDeltaH_pos W x)
      ≤ β * dist V W
  rw [dist_add_left, Real.dist_eq]
  rw [show
      β * Sanctions.movAvgBCF lowDeltaH_pos V x -
          β * Sanctions.movAvgBCF lowDeltaH_pos W x =
        β * (Sanctions.movAvgBCF lowDeltaH_pos V x -
          Sanctions.movAvgBCF lowDeltaH_pos W x) by ring,
    abs_mul, abs_of_nonneg hβ]
  rw [Real.dist_eq] at hM
  exact mul_le_mul_of_nonneg_left hM hβ

/-- The frozen Target map is a `9/10`-contraction. -/
theorem lowDeltaFrozenTargetOperator_contracting :
    ContractingWith (9 / 10 : ℝ≥0)
      (lowDeltaFrozenAffineOperator (9 / 10) lowDeltaFrozenTargetStage) := by
  constructor
  · norm_num
  · apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    exact lowDeltaFrozenAffineOperator_pointwise_dist
      (9 / 10) (by norm_num) lowDeltaFrozenTargetStage V W x

/-- The frozen Sender map is a `1/2`-contraction. -/
theorem lowDeltaFrozenSenderOperator_contracting :
    ContractingWith (1 / 2 : ℝ≥0)
      (lowDeltaFrozenAffineOperator (1 / 2) lowDeltaFrozenSenderStage) := by
  constructor
  · norm_num
  · apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    exact lowDeltaFrozenAffineOperator_pointwise_dist
      (1 / 2) (by norm_num) lowDeltaFrozenSenderStage V W x

/-! ## Banach-constructed reference center -/

/-- Exact frozen-transition Target reference value, constructed by Banach. -/
noncomputable def lowDeltaFrozenTargetCenter : SBCF :=
  ContractingWith.fixedPoint
    (lowDeltaFrozenAffineOperator (9 / 10) lowDeltaFrozenTargetStage)
    lowDeltaFrozenTargetOperator_contracting

/-- Exact frozen-transition Sender reference value, constructed by Banach. -/
noncomputable def lowDeltaFrozenSenderCenter : SBCF :=
  ContractingWith.fixedPoint
    (lowDeltaFrozenAffineOperator (1 / 2) lowDeltaFrozenSenderStage)
    lowDeltaFrozenSenderOperator_contracting

/-- The frozen Target reference value satisfies its defining Bellman
equation. -/
theorem lowDeltaFrozenTargetCenter_isFixedPoint :
    lowDeltaFrozenAffineOperator (9 / 10)
        lowDeltaFrozenTargetStage lowDeltaFrozenTargetCenter =
      lowDeltaFrozenTargetCenter := by
  exact ContractingWith.fixedPoint_isFixedPt _

/-- The frozen Sender reference value satisfies its defining Bellman
equation. -/
theorem lowDeltaFrozenSenderCenter_isFixedPoint :
    lowDeltaFrozenAffineOperator (1 / 2)
        lowDeltaFrozenSenderStage lowDeltaFrozenSenderCenter =
      lowDeltaFrozenSenderCenter := by
  exact ContractingWith.fixedPoint_isFixedPt _

/-- Pointwise form of the frozen Target reference equation. -/
theorem lowDeltaFrozenTargetCenter_eq
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaFrozenTargetCenter x =
      mwU_T x.val
          (lowDeltaStaticTargetPolicy x.val)
          (lowDeltaStaticSenderPolicy x.val)
        + (9 / 10) *
          Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenTargetCenter x := by
  have h := congrArg
    (fun V : SBCF => V x)
    lowDeltaFrozenTargetCenter_isFixedPoint
  simpa only [lowDeltaFrozenAffineOperator,
    lowDeltaFrozenTargetStage_apply,
    BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply] using h.symm

/-- Pointwise form of the frozen Sender reference equation. -/
theorem lowDeltaFrozenSenderCenter_eq
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaFrozenSenderCenter x =
      mwU_S x.val
          (lowDeltaStaticTargetPolicy x.val)
          (lowDeltaStaticSenderPolicy x.val)
        + (1 / 2) *
          Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter x := by
  have h := congrArg
    (fun V : SBCF => V x)
    lowDeltaFrozenSenderCenter_isFixedPoint
  simpa only [lowDeltaFrozenAffineOperator,
    lowDeltaFrozenSenderStage_apply,
    BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply] using h.symm

/-! ## Exact norm and smoothing budgets -/

/-- The moving average is sup-norm nonexpansive. -/
theorem lowDelta_movAvgBCF_norm_le (V : SBCF) :
    ‖Sanctions.movAvgBCF lowDeltaH_pos V‖ ≤ ‖V‖ := by
  have h :=
    Sanctions.movAvgBCF_dist_le lowDeltaH_pos V (0 : SBCF)
  simpa only [dist_zero_right,
    show Sanctions.movAvgBCF lowDeltaH_pos (0 : SBCF) = 0 by
      simpa using Sanctions.movAvgBCF_const lowDeltaH_pos 0] using h

/-- Exact Target-center sup-norm budget inherited from the stage cube bound. -/
theorem lowDeltaFrozenTargetCenter_norm_le :
    ‖lowDeltaFrozenTargetCenter‖ ≤ 20 := by
  have hEq := lowDeltaFrozenTargetCenter_isFixedPoint
  have hnorm :
      ‖lowDeltaFrozenTargetCenter‖ ≤
        ‖lowDeltaFrozenTargetStage‖ +
          (9 / 10) *
            ‖Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenTargetCenter‖ := by
    calc
      ‖lowDeltaFrozenTargetCenter‖ =
          ‖lowDeltaFrozenAffineOperator (9 / 10)
            lowDeltaFrozenTargetStage lowDeltaFrozenTargetCenter‖ := by
              rw [hEq]
      _ ≤ ‖lowDeltaFrozenTargetStage‖ +
          ‖(9 / 10 : ℝ) •
            Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenTargetCenter‖ := by
              exact norm_add_le _ _
      _ = ‖lowDeltaFrozenTargetStage‖ +
          (9 / 10) *
            ‖Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenTargetCenter‖ := by
              rw [norm_smul]
              norm_num [Real.norm_eq_abs]
  have hM :=
    lowDelta_movAvgBCF_norm_le lowDeltaFrozenTargetCenter
  linarith [lowDeltaFrozenTargetStage_norm_le]

/-- Exact Sender-center sup-norm budget inherited from the stage cube bound. -/
theorem lowDeltaFrozenSenderCenter_norm_le :
    ‖lowDeltaFrozenSenderCenter‖ ≤ 523 / 160 := by
  have hEq := lowDeltaFrozenSenderCenter_isFixedPoint
  have hnorm :
      ‖lowDeltaFrozenSenderCenter‖ ≤
        ‖lowDeltaFrozenSenderStage‖ +
          (1 / 2) *
            ‖Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenSenderCenter‖ := by
    calc
      ‖lowDeltaFrozenSenderCenter‖ =
          ‖lowDeltaFrozenAffineOperator (1 / 2)
            lowDeltaFrozenSenderStage lowDeltaFrozenSenderCenter‖ := by
              rw [hEq]
      _ ≤ ‖lowDeltaFrozenSenderStage‖ +
          ‖(1 / 2 : ℝ) •
            Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenSenderCenter‖ := by
              exact norm_add_le _ _
      _ = ‖lowDeltaFrozenSenderStage‖ +
          (1 / 2) *
            ‖Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenSenderCenter‖ := by
              rw [norm_smul]
              norm_num [Real.norm_eq_abs]
  have hM :=
    lowDelta_movAvgBCF_norm_le lowDeltaFrozenSenderCenter
  linarith [lowDeltaFrozenSenderStage_norm_le]

/-- Exact state-Lipschitz budget for the smoothed frozen Target center, using
only the already-proved sup-norm budget and the box half-width. -/
theorem lowDeltaFrozenTargetCenter_smear_lipschitz
    (x y : ↥(Sanctions.S : Set ℝ)) :
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenTargetCenter x -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenTargetCenter y|
      ≤ 200 * dist x y := by
  calc
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenTargetCenter x -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenTargetCenter y|
      ≤ (‖lowDeltaFrozenTargetCenter‖ / (1 / 10)) * dist x y :=
        Sanctions.movAvgBCF_lipschitz_state
          lowDeltaH_pos lowDeltaFrozenTargetCenter x y
    _ ≤ 200 * dist x y := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      nlinarith [lowDeltaFrozenTargetCenter_norm_le]

/-- Exact state-Lipschitz budget for the smoothed frozen Sender center, using
only the already-proved sup-norm budget and the box half-width. -/
theorem lowDeltaFrozenSenderCenter_smear_lipschitz
    (x y : ↥(Sanctions.S : Set ℝ)) :
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter x -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter y|
      ≤ (523 / 16) * dist x y := by
  calc
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter x -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter y|
      ≤ (‖lowDeltaFrozenSenderCenter‖ / (1 / 10)) * dist x y :=
        Sanctions.movAvgBCF_lipschitz_state
          lowDeltaH_pos lowDeltaFrozenSenderCenter x y
    _ ≤ (523 / 16) * dist x y := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      nlinarith [lowDeltaFrozenSenderCenter_norm_le]

end Examples
end Sanctions
