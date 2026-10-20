/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticPolicyReferenceCenter.lean

Exact policy-evaluation values for the already-derived static Stackelberg
policies under the actual low-adjustment transition.

Unlike `LowDeltaFrozenReferenceCenter`, the continuation state here is

  F(x, σ₀(x)) = (99/100) x + (1/100) σ₀(x),

before the existing box shock is applied.  The resulting Target and Sender
values are constructed as Banach fixed points of their affine policy-
evaluation operators.  They are internal comparison centers, not claims that
the static policies are dynamically optimal.

No numerical convergence premise or new model assumption is used.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaFrozenStageLipschitz
import Sanctions.Foundations.FeynmanKacVerification

namespace Sanctions
namespace Examples

open Set AbstractGame
open scoped NNReal
open BoundedContinuousFunction Filter Topology

/-! ## The actual closed-loop drift -/

/-- The pre-noise state transition under the exact static Stackelberg
policies. -/
noncomputable def lowDeltaStaticPolicyDrift :
    ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x =>
    lowDeltaParams.F x.val (lowDeltaStaticSenderPolicy x.val)

/-- The actual static-policy drift is continuous. -/
theorem lowDeltaStaticPolicyDrift_continuous :
    Continuous lowDeltaStaticPolicyDrift :=
  lowDeltaParams.F_continuous.comp
    (continuous_subtype_val.prodMk
      (lowDeltaStaticSenderPolicy_continuous.comp continuous_subtype_val))

/-- Below the Sender-entry threshold, the actual drift has slope `99/100`. -/
theorem lowDeltaStaticPolicyDrift_eq_low
    (x : ↥(Sanctions.S : Set ℝ)) (hx : x.val ≤ 2 / 27) :
    lowDeltaStaticPolicyDrift x = (99 / 100) * x.val := by
  rw [lowDeltaStaticPolicyDrift, lowDeltaParams_F,
    lowDeltaStaticSenderPolicy_eq_zero_of_le hx]
  unfold Sanctions.AbstractGame.affineF
  ring

/-- Between the two static-policy thresholds, the actual drift has slope
`801/800`. -/
theorem lowDeltaStaticPolicyDrift_eq_mid
    (x : ↥(Sanctions.S : Set ℝ))
    (hx0 : 2 / 27 ≤ x.val) (hx1 : x.val ≤ 40 / 103) :
    lowDeltaStaticPolicyDrift x =
      (801 / 800) * x.val - 1 / 1200 := by
  have hα : lowDeltaStaticTargetPolicy x.val = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le hx1
  have hσ :
      lowDeltaStaticSenderPolicy x.val =
        (9 / 8) * x.val - 1 / 12 := by
    rw [lowDeltaStaticSenderPolicy_eq_vertex_of_ge hx0 x.property.2, hα]
    norm_num [lowDeltaSenderInteriorVertex]
  rw [lowDeltaStaticPolicyDrift, lowDeltaParams_F, hσ]
  unfold Sanctions.AbstractGame.affineF
  ring

/-- Above the Target-activation threshold, the actual drift has slope
`138859/139200`. -/
theorem lowDeltaStaticPolicyDrift_eq_high
    (x : ↥(Sanctions.S : Set ℝ)) (hx : 40 / 103 ≤ x.val) :
    lowDeltaStaticPolicyDrift x =
      (138859 / 139200) * x.val + 7 / 11600 := by
  have hα :
      lowDeltaStaticTargetPolicy x.val =
        (103 / 116) * x.val - 10 / 29 :=
    lowDeltaStaticTargetPolicy_eq_vertex_of_ge hx
  have hσ :
      lowDeltaStaticSenderPolicy x.val =
        lowDeltaSenderInteriorVertex 0 x.val
          ((103 / 116) * x.val - 10 / 29) := by
    rw [lowDeltaStaticSenderPolicy_eq_vertex_of_ge (by linarith) x.property.2, hα]
  rw [lowDeltaStaticPolicyDrift, lowDeltaParams_F, hσ]
  unfold Sanctions.AbstractGame.affineF lowDeltaSenderInteriorVertex
  ring

private theorem concatenate_state_chords
    {f : ↥(Sanctions.S : Set ℝ) → ℝ} {K : ℝ}
    (x b y : ↥(Sanctions.S : Set ℝ))
    (hxb : x.val ≤ b.val) (hby : b.val ≤ y.val)
    (hleft : |f b - f x| ≤ K * dist x b)
    (hright : |f y - f b| ≤ K * dist b y) :
    |f y - f x| ≤ K * dist x y := by
  have htriangle :
      |f y - f x| ≤ |f y - f b| + |f b - f x| := by
    calc
      |f y - f x| = |(f y - f b) + (f b - f x)| := by ring_nf
      _ ≤ |f y - f b| + |f b - f x| := abs_add_le _ _
  have hdist : dist x b + dist b y = dist x y := by
    rw [Subtype.dist_eq, Subtype.dist_eq, Subtype.dist_eq,
      Real.dist_eq, Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxb),
      abs_of_nonpos (sub_nonpos.mpr hby),
      abs_of_nonpos (sub_nonpos.mpr (le_trans hxb hby))]
    ring
  calc
    |f y - f x| ≤ |f y - f b| + |f b - f x| := htriangle
    _ ≤ K * dist b y + K * dist x b := add_le_add hright hleft
    _ = K * dist x y := by rw [← mul_add, add_comm, hdist]

private theorem lowDeltaStaticPolicyDrift_chord_low
    (x y : ↥(Sanctions.S : Set ℝ))
    (hxy : x.val ≤ y.val) (hy : y.val ≤ 2 / 27) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (801 / 800) * dist x y := by
  rw [lowDeltaStaticPolicyDrift_eq_low x (le_trans hxy hy),
    lowDeltaStaticPolicyDrift_eq_low y hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show (99 / 100) * y.val - (99 / 100) * x.val =
      (99 / 100) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 100),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]
  apply mul_le_mul_of_nonneg_right _ hd
  norm_num

private theorem lowDeltaStaticPolicyDrift_chord_mid
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 2 / 27 ≤ x.val) (hxy : x.val ≤ y.val)
    (hy : y.val ≤ 40 / 103) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (801 / 800) * dist x y := by
  rw [lowDeltaStaticPolicyDrift_eq_mid x hx (le_trans hxy hy),
    lowDeltaStaticPolicyDrift_eq_mid y (le_trans hx hxy) hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show
      ((801 / 800) * y.val - 1 / 1200) -
          ((801 / 800) * x.val - 1 / 1200) =
        (801 / 800) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 801 / 800),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]

private theorem lowDeltaStaticPolicyDrift_chord_high
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 40 / 103 ≤ x.val) (hxy : x.val ≤ y.val) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (801 / 800) * dist x y := by
  rw [lowDeltaStaticPolicyDrift_eq_high x hx,
    lowDeltaStaticPolicyDrift_eq_high y (le_trans hx hxy)]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show
      ((138859 / 139200) * y.val + 7 / 11600) -
          ((138859 / 139200) * x.val + 7 / 11600) =
        (138859 / 139200) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 138859 / 139200),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]
  apply mul_le_mul_of_nonneg_right _ hd
  norm_num

private theorem lowDeltaStaticPolicyDrift_chord_ordered
    (x y : ↥(Sanctions.S : Set ℝ)) (hxy : x.val ≤ y.val) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (801 / 800) * dist x y := by
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  by_cases hyLow : y.val ≤ b₁.val
  · exact lowDeltaStaticPolicyDrift_chord_low x y hxy hyLow
  by_cases hxHigh : b₂.val ≤ x.val
  · exact lowDeltaStaticPolicyDrift_chord_high x y hxHigh hxy
  by_cases hyMid : y.val ≤ b₂.val
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_state_chords x b₁ y hxLow (by linarith)
      · exact lowDeltaStaticPolicyDrift_chord_low x b₁ hxLow le_rfl
      · exact lowDeltaStaticPolicyDrift_chord_mid b₁ y le_rfl (by linarith) hyMid
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      exact lowDeltaStaticPolicyDrift_chord_mid x y
        (by simpa [b₁] using hxAbove) hxy hyMid
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_state_chords x b₂ y (by linarith) (by linarith)
      · apply concatenate_state_chords x b₁ b₂ hxLow (by norm_num)
        · exact lowDeltaStaticPolicyDrift_chord_low x b₁ hxLow le_rfl
        · exact lowDeltaStaticPolicyDrift_chord_mid b₁ b₂ le_rfl (by norm_num) le_rfl
      · exact lowDeltaStaticPolicyDrift_chord_high b₂ y le_rfl (by linarith)
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      have hxBelow : x.val ≤ b₂.val := le_of_not_ge hxHigh
      apply concatenate_state_chords x b₂ y hxBelow (by linarith)
      · exact lowDeltaStaticPolicyDrift_chord_mid x b₂
          (by simpa [b₁] using hxAbove) hxBelow le_rfl
      · exact lowDeltaStaticPolicyDrift_chord_high b₂ y le_rfl (by linarith)

/-- The exact global state modulus of the actual static-policy drift is at
most `801/800`. -/
theorem lowDeltaStaticPolicyDrift_valueLipschitz :
    ∀ x y : ↥(Sanctions.S : Set ℝ),
      |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
        (801 / 800) * dist x y := by
  intro x y
  rcases le_total x.val y.val with hxy | hyx
  · exact lowDeltaStaticPolicyDrift_chord_ordered x y hxy
  · simpa [abs_sub_comm, dist_comm] using
      lowDeltaStaticPolicyDrift_chord_ordered y x hyx

/-- The modulus `801/800` is sharp: every strictly smaller proposed global
drift modulus is refuted by the two endpoints of the middle affine cell. -/
theorem lowDeltaStaticPolicyDrift_not_lipschitz_below
    {K : ℝ} (hK : K < 801 / 800) :
    ¬ (∀ x y : ↥(Sanctions.S : Set ℝ),
      |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
        K * dist x y) := by
  intro h
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  have hbad := h b₁ b₂
  rw [lowDeltaStaticPolicyDrift_eq_mid b₁ le_rfl (by norm_num),
    lowDeltaStaticPolicyDrift_eq_mid b₂ (by norm_num) le_rfl,
    Subtype.dist_eq, Real.dist_eq] at hbad
  norm_num [b₁, b₂] at hbad
  nlinarith

/-- Disprove-first boundary: the actual static-policy drift is not
one-Lipschitz.  Its middle cell has the strictly larger exact slope
`801/800`. -/
theorem lowDeltaStaticPolicyDrift_not_oneLipschitz :
    ¬ (∀ x y : ↥(Sanctions.S : Set ℝ),
      |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
        dist x y) := by
  intro h
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  have hbad := h b₁ b₂
  rw [lowDeltaStaticPolicyDrift_eq_mid b₁ le_rfl (by norm_num),
    lowDeltaStaticPolicyDrift_eq_mid b₂ (by norm_num) le_rfl,
    Subtype.dist_eq, Real.dist_eq] at hbad
  norm_num [b₁, b₂] at hbad

/-! ## Policy pullback and affine evaluation operators -/

/-- The moving-average continuation operator evaluated along the actual
static-policy drift. -/
noncomputable def lowDeltaStaticPolicyPullback (V : SBCF) : SBCF :=
  Sanctions.closedLoopPullback
    lowDeltaStaticPolicyDrift
    lowDeltaStaticPolicyDrift_continuous
    (1 / 10) lowDeltaH_pos V

@[simp] theorem lowDeltaStaticPolicyPullback_apply
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaStaticPolicyPullback V x =
      Sanctions.movAvgReal (1 / 10) V
        (lowDeltaStaticPolicyDrift x) := rfl

/-- The actual-transition policy pullback is nonexpansive in sup norm. -/
theorem lowDeltaStaticPolicyPullback_dist_le (V W : SBCF) :
    dist (lowDeltaStaticPolicyPullback V)
        (lowDeltaStaticPolicyPullback W) ≤
      dist V W := by
  rw [BoundedContinuousFunction.dist_le dist_nonneg]
  intro x
  rw [lowDeltaStaticPolicyPullback_apply,
    lowDeltaStaticPolicyPullback_apply, Real.dist_eq]
  exact Sanctions.movAvg_dist_le lowDeltaH_pos V W
    (lowDeltaStaticPolicyDrift x)

/-- Affine policy-evaluation map using the actual low-adjustment transition. -/
noncomputable def lowDeltaStaticPolicyOperator
    (β : ℝ) (g V : SBCF) : SBCF :=
  g + β • lowDeltaStaticPolicyPullback V

/-- Pointwise contraction estimate for the actual-transition policy operator. -/
theorem lowDeltaStaticPolicyOperator_pointwise_dist
    (β : ℝ) (hβ : 0 ≤ β) (g V W : SBCF)
    (x : ↥(Sanctions.S : Set ℝ)) :
    dist (lowDeltaStaticPolicyOperator β g V x)
        (lowDeltaStaticPolicyOperator β g W x) ≤
      β * dist V W := by
  have hPglobal := lowDeltaStaticPolicyPullback_dist_le V W
  have hP :
      dist (lowDeltaStaticPolicyPullback V x)
          (lowDeltaStaticPolicyPullback W x) ≤ dist V W :=
    (BoundedContinuousFunction.dist_le dist_nonneg).mp hPglobal x
  change
    dist
        (g x + β * lowDeltaStaticPolicyPullback V x)
        (g x + β * lowDeltaStaticPolicyPullback W x) ≤
      β * dist V W
  rw [dist_add_left, Real.dist_eq]
  rw [show
      β * lowDeltaStaticPolicyPullback V x -
          β * lowDeltaStaticPolicyPullback W x =
        β * (lowDeltaStaticPolicyPullback V x -
          lowDeltaStaticPolicyPullback W x) by ring,
    abs_mul, abs_of_nonneg hβ]
  rw [Real.dist_eq] at hP
  exact mul_le_mul_of_nonneg_left hP hβ

/-- The actual-transition Target policy-evaluation map is a
`9/10`-contraction. -/
theorem lowDeltaStaticTargetPolicyOperator_contracting :
    ContractingWith (9 / 10 : ℝ≥0)
      (lowDeltaStaticPolicyOperator
        (9 / 10) lowDeltaFrozenTargetStage) := by
  constructor
  · norm_num
  · apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    exact lowDeltaStaticPolicyOperator_pointwise_dist
      (9 / 10) (by norm_num) lowDeltaFrozenTargetStage V W x

/-- The actual-transition Sender policy-evaluation map is a
`1/2`-contraction. -/
theorem lowDeltaStaticSenderPolicyOperator_contracting :
    ContractingWith (1 / 2 : ℝ≥0)
      (lowDeltaStaticPolicyOperator
        (1 / 2) lowDeltaFrozenSenderStage) := by
  constructor
  · norm_num
  · apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    exact lowDeltaStaticPolicyOperator_pointwise_dist
      (1 / 2) (by norm_num) lowDeltaFrozenSenderStage V W x

/-! ## Banach-constructed actual-transition reference centers -/

/-- Target policy-evaluation value under the actual transition, constructed
by Banach. -/
noncomputable def lowDeltaStaticTargetPolicyCenter : SBCF :=
  ContractingWith.fixedPoint
    (lowDeltaStaticPolicyOperator
      (9 / 10) lowDeltaFrozenTargetStage)
    lowDeltaStaticTargetPolicyOperator_contracting

/-- Sender policy-evaluation value under the actual transition, constructed
by Banach. -/
noncomputable def lowDeltaStaticSenderPolicyCenter : SBCF :=
  ContractingWith.fixedPoint
    (lowDeltaStaticPolicyOperator
      (1 / 2) lowDeltaFrozenSenderStage)
    lowDeltaStaticSenderPolicyOperator_contracting

/-- The Target actual-transition reference center satisfies its defining
policy-evaluation equation. -/
theorem lowDeltaStaticTargetPolicyCenter_isFixedPoint :
    lowDeltaStaticPolicyOperator
        (9 / 10) lowDeltaFrozenTargetStage
        lowDeltaStaticTargetPolicyCenter =
      lowDeltaStaticTargetPolicyCenter := by
  exact ContractingWith.fixedPoint_isFixedPt _

/-- The Sender actual-transition reference center satisfies its defining
policy-evaluation equation. -/
theorem lowDeltaStaticSenderPolicyCenter_isFixedPoint :
    lowDeltaStaticPolicyOperator
        (1 / 2) lowDeltaFrozenSenderStage
        lowDeltaStaticSenderPolicyCenter =
      lowDeltaStaticSenderPolicyCenter := by
  exact ContractingWith.fixedPoint_isFixedPt _

/-- Pointwise Target policy-evaluation equation under the actual transition. -/
theorem lowDeltaStaticTargetPolicyCenter_eq
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaStaticTargetPolicyCenter x =
      lowDeltaFrozenTargetStage x +
        (9 / 10) *
          lowDeltaStaticPolicyPullback
            lowDeltaStaticTargetPolicyCenter x := by
  have h := congrArg (fun V : SBCF => V x)
    lowDeltaStaticTargetPolicyCenter_isFixedPoint
  simpa only [lowDeltaStaticPolicyOperator,
    BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply] using h.symm

/-- Pointwise Sender policy-evaluation equation under the actual transition. -/
theorem lowDeltaStaticSenderPolicyCenter_eq
    (x : ↥(Sanctions.S : Set ℝ)) :
    lowDeltaStaticSenderPolicyCenter x =
      lowDeltaFrozenSenderStage x +
        (1 / 2) *
          lowDeltaStaticPolicyPullback
            lowDeltaStaticSenderPolicyCenter x := by
  have h := congrArg (fun V : SBCF => V x)
    lowDeltaStaticSenderPolicyCenter_isFixedPoint
  simpa only [lowDeltaStaticPolicyOperator,
    BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply] using h.symm

/-! ## Cellwise bounds for the sharp center moduli -/

private theorem lowDeltaStaticPolicyDrift_chord_low_exact
    (x y : ↥(Sanctions.S : Set ℝ))
    (hxy : x.val ≤ y.val) (hy : y.val ≤ 2 / 27) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (99 / 100) * dist x y := by
  rw [lowDeltaStaticPolicyDrift_eq_low x (le_trans hxy hy),
    lowDeltaStaticPolicyDrift_eq_low y hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show (99 / 100) * y.val - (99 / 100) * x.val =
      (99 / 100) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 100),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]

private theorem lowDeltaStaticPolicyDrift_chord_mid_exact
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 2 / 27 ≤ x.val) (hxy : x.val ≤ y.val)
    (hy : y.val ≤ 40 / 103) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (801 / 800) * dist x y := by
  exact lowDeltaStaticPolicyDrift_chord_mid x y hx hxy hy

private theorem lowDeltaStaticPolicyDrift_chord_high_exact
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 40 / 103 ≤ x.val) (hxy : x.val ≤ y.val) :
    |lowDeltaStaticPolicyDrift y - lowDeltaStaticPolicyDrift x| ≤
      (138859 / 139200) * dist x y := by
  rw [lowDeltaStaticPolicyDrift_eq_high x hx,
    lowDeltaStaticPolicyDrift_eq_high y (le_trans hx hxy)]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show
      ((138859 / 139200) * y.val + 7 / 11600) -
          ((138859 / 139200) * x.val + 7 / 11600) =
        (138859 / 139200) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 138859 / 139200),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]

private theorem lowDeltaTargetStage_chord_low_sharp
    (x y : ↥(Sanctions.S : Set ℝ))
    (hxy : x.val ≤ y.val) (hy : y.val ≤ 2 / 27) :
    |lowDeltaFrozenTargetStage y - lowDeltaFrozenTargetStage x| ≤
      0 * dist x y := by
  rw [lowDeltaFrozenTargetStage_eq_zero_of_le x (le_trans hxy hy),
    lowDeltaFrozenTargetStage_eq_zero_of_le y hy]
  norm_num

private theorem lowDeltaTargetStage_chord_mid_sharp
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 2 / 27 ≤ x.val) (hxy : x.val ≤ y.val)
    (hy : y.val ≤ 40 / 103) :
    |lowDeltaFrozenTargetStage y - lowDeltaFrozenTargetStage x| ≤
      (23 / 48) * dist x y := by
  rw [lowDeltaFrozenTargetStage_eq_mid x hx (le_trans hxy hy),
    lowDeltaFrozenTargetStage_eq_mid y (le_trans hx hxy) hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  have hq :
      |-(31 / 48 : ℝ) + (9 / 8) * (x.val + y.val)| ≤
        23 / 48 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hfactor :
      (1 / 24 - (31 / 48) * y.val + (9 / 8) * y.val ^ 2) -
          (1 / 24 - (31 / 48) * x.val + (9 / 8) * x.val ^ 2) =
        (y.val - x.val) *
          (-(31 / 48) + (9 / 8) * (x.val + y.val)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hd, Subtype.dist_eq,
    Real.dist_eq, abs_sub_comm x.val y.val, abs_of_nonneg hd]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hd

private theorem lowDeltaTargetStage_chord_high_sharp
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 40 / 103 ≤ x.val) (hxy : x.val ≤ y.val) :
    |lowDeltaFrozenTargetStage y - lowDeltaFrozenTargetStage x| ≤
      (15421 / 5568) * dist x y := by
  rw [lowDeltaFrozenTargetStage_eq_high x hx,
    lowDeltaFrozenTargetStage_eq_high y (le_trans hx hxy)]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  have hq :
      |-(643 / 464 : ℝ) +
          (23137 / 11136) * (x.val + y.val)| ≤
        15421 / 5568 := by
    rw [abs_le]
    constructor <;> nlinarith [x.property.2, y.property.2]
  have hfactor :
      (43 / 232 - (643 / 464) * y.val +
          (23137 / 11136) * y.val ^ 2) -
          (43 / 232 - (643 / 464) * x.val +
            (23137 / 11136) * x.val ^ 2) =
        (y.val - x.val) *
          (-(643 / 464) + (23137 / 11136) * (x.val + y.val)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hd, Subtype.dist_eq,
    Real.dist_eq, abs_sub_comm x.val y.val, abs_of_nonneg hd]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hd

private theorem lowDeltaSenderStage_chord_low_sharp
    (x y : ↥(Sanctions.S : Set ℝ))
    (hxy : x.val ≤ y.val) (hy : y.val ≤ 2 / 27) :
    |lowDeltaFrozenSenderStage y - lowDeltaFrozenSenderStage x| ≤
      (2 / 5) * dist x y := by
  rw [lowDeltaFrozenSenderStage_eq_low x (le_trans hxy hy),
    lowDeltaFrozenSenderStage_eq_low y hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show (2 / 5) * y.val - (2 / 5) * x.val =
      (2 / 5) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]

private theorem lowDeltaSenderStage_chord_mid_sharp
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 2 / 27 ≤ x.val) (hxy : x.val ≤ y.val)
    (hy : y.val ≤ 40 / 103) :
    |lowDeltaFrozenSenderStage y - lowDeltaFrozenSenderStage x| ≤
      (7229 / 8240) * dist x y := by
  rw [lowDeltaFrozenSenderStage_eq_mid x hx (le_trans hxy hy),
    lowDeltaFrozenSenderStage_eq_mid y (le_trans hx hxy) hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  have hq :
      |(23 / 80 : ℝ) + (243 / 320) * (x.val + y.val)| ≤
        7229 / 8240 := by
    rw [abs_le]
    constructor <;> nlinarith [x.property.1, y.property.1]
  have hfactor :
      (1 / 240 + (23 / 80) * y.val + (243 / 320) * y.val ^ 2) -
          (1 / 240 + (23 / 80) * x.val + (243 / 320) * x.val ^ 2) =
        (y.val - x.val) *
          ((23 / 80) + (243 / 320) * (x.val + y.val)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hd, Subtype.dist_eq,
    Real.dist_eq, abs_sub_comm x.val y.val, abs_of_nonneg hd]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hd

private theorem lowDeltaSenderStage_chord_high_sharp
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 40 / 103 ≤ x.val) (hxy : x.val ≤ y.val) :
    |lowDeltaFrozenSenderStage y - lowDeltaFrozenSenderStage x| ≤
      (3272533 / 1614720) * dist x y := by
  rw [lowDeltaFrozenSenderStage_eq_high x hx,
    lowDeltaFrozenSenderStage_eq_high y (le_trans hx hxy)]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  have hq :
      |(180661 / 134560 : ℝ) +
          (1104601 / 3229440) * (x.val + y.val)| ≤
        3272533 / 1614720 := by
    rw [abs_le]
    constructor <;> nlinarith [x.property.2, y.property.2]
  have hfactor :
      (-23053 / 67280 + (180661 / 134560) * y.val +
          (1104601 / 3229440) * y.val ^ 2) -
          (-23053 / 67280 + (180661 / 134560) * x.val +
            (1104601 / 3229440) * x.val ^ 2) =
        (y.val - x.val) *
          ((180661 / 134560) +
            (1104601 / 3229440) * (x.val + y.val)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hd, Subtype.dist_eq,
    Real.dist_eq, abs_sub_comm x.val y.val, abs_of_nonneg hd]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hd

/-- Pullback chord of the static-policy operator.  Witness-specific
(Rule 22).  The modulus `K` is nonnegative because `V` is `K`-Lipschitz
(`ValueLipschitzWith.nonneg`); it is derived, not assumed. -/
private theorem lowDeltaStaticPolicyPullback_chord_of_drift
    {V : SBCF} {K γ : ℝ}
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith V K)
    (x y : ↥(Sanctions.S : Set ℝ))
    (hdrift :
      |lowDeltaStaticPolicyDrift y -
          lowDeltaStaticPolicyDrift x| ≤
        γ * dist x y) :
    |lowDeltaStaticPolicyPullback V y -
        lowDeltaStaticPolicyPullback V x| ≤
      (K * γ) * dist x y := by
  have hK : 0 ≤ K := hV.nonneg
  rw [lowDeltaStaticPolicyPullback_apply,
    lowDeltaStaticPolicyPullback_apply]
  have hsmear :=
    Sanctions.movAvgReal_valueLipschitz
      lowDeltaH_pos V hK hV
      (lowDeltaStaticPolicyDrift y)
      (lowDeltaStaticPolicyDrift x)
  calc
    |Sanctions.movAvgReal (1 / 10) V
          (lowDeltaStaticPolicyDrift y) -
        Sanctions.movAvgReal (1 / 10) V
          (lowDeltaStaticPolicyDrift x)|
        ≤ K *
          |lowDeltaStaticPolicyDrift y -
            lowDeltaStaticPolicyDrift x| := hsmear
    _ ≤ K * (γ * dist x y) :=
      mul_le_mul_of_nonneg_left hdrift hK
    _ = (K * γ) * dist x y := by ring

/-- Chord of the static-policy operator from stage, drift and margin bounds.
Witness-specific (Rule 22).  No `0 ≤ K` premise: it follows from the Lipschitz
bound on `V`. -/
private theorem lowDeltaStaticPolicyOperator_chord_of_bounds
    {V stage : SBCF} {β K L γ : ℝ}
    (hβ : 0 ≤ β)
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith V K)
    (x y : ↥(Sanctions.S : Set ℝ))
    (hstage : |stage y - stage x| ≤ L * dist x y)
    (hdrift :
      |lowDeltaStaticPolicyDrift y -
          lowDeltaStaticPolicyDrift x| ≤
        γ * dist x y)
    (hmargin : L + β * K * γ ≤ K) :
    |lowDeltaStaticPolicyOperator β stage V y -
        lowDeltaStaticPolicyOperator β stage V x| ≤
      K * dist x y := by
  have hpull :=
    lowDeltaStaticPolicyPullback_chord_of_drift
      hV x y hdrift
  change
    |(stage y + β * lowDeltaStaticPolicyPullback V y) -
        (stage x + β * lowDeltaStaticPolicyPullback V x)| ≤
      K * dist x y
  rw [show
      (stage y + β * lowDeltaStaticPolicyPullback V y) -
          (stage x + β * lowDeltaStaticPolicyPullback V x) =
        (stage y - stage x) +
          β * (lowDeltaStaticPolicyPullback V y -
            lowDeltaStaticPolicyPullback V x) by ring]
  calc
    |(stage y - stage x) +
        β * (lowDeltaStaticPolicyPullback V y -
          lowDeltaStaticPolicyPullback V x)|
        ≤ |stage y - stage x| +
          |β * (lowDeltaStaticPolicyPullback V y -
            lowDeltaStaticPolicyPullback V x)| := abs_add_le _ _
    _ = |stage y - stage x| +
          β * |lowDeltaStaticPolicyPullback V y -
            lowDeltaStaticPolicyPullback V x| := by
          rw [abs_mul, abs_of_nonneg hβ]
    _ ≤ L * dist x y +
          β * ((K * γ) * dist x y) := by
          exact add_le_add hstage
            (mul_le_mul_of_nonneg_left hpull hβ)
    _ = (L + β * K * γ) * dist x y := by ring
    _ ≤ K * dist x y :=
      mul_le_mul_of_nonneg_right hmargin dist_nonneg

/-! ## Sharp Target center modulus -/

private theorem lowDeltaStaticTargetPolicyOperator_chord_ordered
    (V : SBCF)
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith
      V (3855250 / 142269))
    (x y : ↥(Sanctions.S : Set ℝ)) (hxy : x.val ≤ y.val) :
    |lowDeltaStaticPolicyOperator
        (9 / 10) lowDeltaFrozenTargetStage V y -
      lowDeltaStaticPolicyOperator
        (9 / 10) lowDeltaFrozenTargetStage V x| ≤
      (3855250 / 142269) * dist x y := by
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  by_cases hyLow : y.val ≤ b₁.val
  · apply lowDeltaStaticPolicyOperator_chord_of_bounds
      (β := 9 / 10) (K := 3855250 / 142269)
      (L := 0) (γ := 99 / 100) (by norm_num) hV
    · exact lowDeltaTargetStage_chord_low_sharp x y hxy hyLow
    · exact lowDeltaStaticPolicyDrift_chord_low_exact x y hxy hyLow
    · norm_num
  by_cases hxHigh : b₂.val ≤ x.val
  · apply lowDeltaStaticPolicyOperator_chord_of_bounds
      (β := 9 / 10) (K := 3855250 / 142269)
      (L := 15421 / 5568) (γ := 138859 / 139200)
      (by norm_num) hV
    · exact lowDeltaTargetStage_chord_high_sharp x y hxHigh hxy
    · exact lowDeltaStaticPolicyDrift_chord_high_exact x y hxHigh hxy
    · norm_num
  by_cases hyMid : y.val ≤ b₂.val
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_state_chords x b₁ y hxLow (by linarith)
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 9 / 10) (K := 3855250 / 142269)
          (L := 0) (γ := 99 / 100) (by norm_num) hV
        · exact lowDeltaTargetStage_chord_low_sharp x b₁ hxLow le_rfl
        · exact lowDeltaStaticPolicyDrift_chord_low_exact x b₁ hxLow le_rfl
        · norm_num
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 9 / 10) (K := 3855250 / 142269)
          (L := 23 / 48) (γ := 801 / 800)
          (by norm_num) hV
        · exact lowDeltaTargetStage_chord_mid_sharp b₁ y le_rfl (by linarith) hyMid
        · exact lowDeltaStaticPolicyDrift_chord_mid_exact b₁ y le_rfl (by linarith) hyMid
        · norm_num
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 9 / 10) (K := 3855250 / 142269)
          (L := 23 / 48) (γ := 801 / 800)
          (by norm_num) hV
      · exact lowDeltaTargetStage_chord_mid_sharp x y
          (by simpa [b₁] using hxAbove) hxy hyMid
      · exact lowDeltaStaticPolicyDrift_chord_mid_exact x y
          (by simpa [b₁] using hxAbove) hxy hyMid
      · norm_num
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_state_chords x b₂ y (by linarith) (by linarith)
      · apply concatenate_state_chords x b₁ b₂ hxLow (by norm_num)
        · apply lowDeltaStaticPolicyOperator_chord_of_bounds
            (β := 9 / 10) (K := 3855250 / 142269)
            (L := 0) (γ := 99 / 100)
            (by norm_num) hV
          · exact lowDeltaTargetStage_chord_low_sharp x b₁ hxLow le_rfl
          · exact lowDeltaStaticPolicyDrift_chord_low_exact x b₁ hxLow le_rfl
          · norm_num
        · apply lowDeltaStaticPolicyOperator_chord_of_bounds
            (β := 9 / 10) (K := 3855250 / 142269)
            (L := 23 / 48) (γ := 801 / 800)
            (by norm_num) hV
          · exact lowDeltaTargetStage_chord_mid_sharp b₁ b₂ le_rfl
              (by norm_num) le_rfl
          · exact lowDeltaStaticPolicyDrift_chord_mid_exact b₁ b₂ le_rfl
              (by norm_num) le_rfl
          · norm_num
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 9 / 10) (K := 3855250 / 142269)
          (L := 15421 / 5568) (γ := 138859 / 139200)
          (by norm_num) hV
        · exact lowDeltaTargetStage_chord_high_sharp b₂ y le_rfl (by linarith)
        · exact lowDeltaStaticPolicyDrift_chord_high_exact b₂ y le_rfl (by linarith)
        · norm_num
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      have hxBelow : x.val ≤ b₂.val := le_of_not_ge hxHigh
      apply concatenate_state_chords x b₂ y hxBelow (by linarith)
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 9 / 10) (K := 3855250 / 142269)
          (L := 23 / 48) (γ := 801 / 800)
          (by norm_num) hV
        · exact lowDeltaTargetStage_chord_mid_sharp x b₂
            (by simpa [b₁] using hxAbove) hxBelow le_rfl
        · exact lowDeltaStaticPolicyDrift_chord_mid_exact x b₂
            (by simpa [b₁] using hxAbove) hxBelow le_rfl
        · norm_num
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 9 / 10) (K := 3855250 / 142269)
          (L := 15421 / 5568) (γ := 138859 / 139200)
          (by norm_num) hV
        · exact lowDeltaTargetStage_chord_high_sharp b₂ y le_rfl (by linarith)
        · exact lowDeltaStaticPolicyDrift_chord_high_exact b₂ y le_rfl (by linarith)
        · norm_num

private theorem lowDeltaStaticTargetPolicyOperator_preserves_lipschitz
    (V : SBCF)
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith
      V (3855250 / 142269)) :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaStaticPolicyOperator
        (9 / 10) lowDeltaFrozenTargetStage V)
      (3855250 / 142269) := by
  intro x y
  rcases le_total x.val y.val with hxy | hyx
  · exact lowDeltaStaticTargetPolicyOperator_chord_ordered V hV x y hxy
  · simpa [abs_sub_comm, dist_comm] using
      lowDeltaStaticTargetPolicyOperator_chord_ordered V hV y x hyx

/-- The actual-transition Target policy-evaluation center is globally
Lipschitz with the cellwise sharp closed-form bound
`(15421/5568) / (1 - (9/10)(138859/139200)) = 3855250/142269`. -/
theorem lowDeltaStaticTargetPolicyCenter_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      lowDeltaStaticTargetPolicyCenter (3855250 / 142269) := by
  let T : SBCF → SBCF :=
    lowDeltaStaticPolicyOperator
      (9 / 10) lowDeltaFrozenTargetStage
  have hK : (0 : ℝ) ≤ 3855250 / 142269 := by norm_num
  have hiter :
      ∀ n, Sanctions.AbstractGame.Params.ValueLipschitzWith
        (T^[n] (0 : SBCF)) (3855250 / 142269) := by
    intro n
    induction n with
    | zero =>
        simpa using
          (Sanctions.AbstractGame.Params.valueLipschitzWith_zero hK)
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact lowDeltaStaticTargetPolicyOperator_preserves_lipschitz _ ih
  have htendsto :
      Tendsto (fun n => T^[n] (0 : SBCF)) atTop
        (𝓝 lowDeltaStaticTargetPolicyCenter) := by
    exact ContractingWith.tendsto_iterate_fixedPoint
      lowDeltaStaticTargetPolicyOperator_contracting (0 : SBCF)
  exact Sanctions.AbstractGame.Params.valueLipschitzWith_of_tendsto
    hK hiter htendsto

/-! ## Sharp Sender center modulus -/

private theorem lowDeltaStaticSenderPolicyOperator_chord_ordered
    (V : SBCF)
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith
      V (16362665 / 4046689))
    (x y : ↥(Sanctions.S : Set ℝ)) (hxy : x.val ≤ y.val) :
    |lowDeltaStaticPolicyOperator
        (1 / 2) lowDeltaFrozenSenderStage V y -
      lowDeltaStaticPolicyOperator
        (1 / 2) lowDeltaFrozenSenderStage V x| ≤
      (16362665 / 4046689) * dist x y := by
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  by_cases hyLow : y.val ≤ b₁.val
  · apply lowDeltaStaticPolicyOperator_chord_of_bounds
      (β := 1 / 2) (K := 16362665 / 4046689)
      (L := 2 / 5) (γ := 99 / 100) (by norm_num) hV
    · exact lowDeltaSenderStage_chord_low_sharp x y hxy hyLow
    · exact lowDeltaStaticPolicyDrift_chord_low_exact x y hxy hyLow
    · norm_num
  by_cases hxHigh : b₂.val ≤ x.val
  · apply lowDeltaStaticPolicyOperator_chord_of_bounds
      (β := 1 / 2) (K := 16362665 / 4046689)
      (L := 3272533 / 1614720) (γ := 138859 / 139200)
      (by norm_num) hV
    · exact lowDeltaSenderStage_chord_high_sharp x y hxHigh hxy
    · exact lowDeltaStaticPolicyDrift_chord_high_exact x y hxHigh hxy
    · norm_num
  by_cases hyMid : y.val ≤ b₂.val
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_state_chords x b₁ y hxLow (by linarith)
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 1 / 2) (K := 16362665 / 4046689)
          (L := 2 / 5) (γ := 99 / 100)
          (by norm_num) hV
        · exact lowDeltaSenderStage_chord_low_sharp x b₁ hxLow le_rfl
        · exact lowDeltaStaticPolicyDrift_chord_low_exact x b₁ hxLow le_rfl
        · norm_num
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 1 / 2) (K := 16362665 / 4046689)
          (L := 7229 / 8240) (γ := 801 / 800)
          (by norm_num) hV
        · exact lowDeltaSenderStage_chord_mid_sharp b₁ y le_rfl (by linarith) hyMid
        · exact lowDeltaStaticPolicyDrift_chord_mid_exact b₁ y le_rfl (by linarith) hyMid
        · norm_num
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 1 / 2) (K := 16362665 / 4046689)
          (L := 7229 / 8240) (γ := 801 / 800)
          (by norm_num) hV
      · exact lowDeltaSenderStage_chord_mid_sharp x y
          (by simpa [b₁] using hxAbove) hxy hyMid
      · exact lowDeltaStaticPolicyDrift_chord_mid_exact x y
          (by simpa [b₁] using hxAbove) hxy hyMid
      · norm_num
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_state_chords x b₂ y (by linarith) (by linarith)
      · apply concatenate_state_chords x b₁ b₂ hxLow (by norm_num)
        · apply lowDeltaStaticPolicyOperator_chord_of_bounds
            (β := 1 / 2) (K := 16362665 / 4046689)
            (L := 2 / 5) (γ := 99 / 100)
            (by norm_num) hV
          · exact lowDeltaSenderStage_chord_low_sharp x b₁ hxLow le_rfl
          · exact lowDeltaStaticPolicyDrift_chord_low_exact x b₁ hxLow le_rfl
          · norm_num
        · apply lowDeltaStaticPolicyOperator_chord_of_bounds
            (β := 1 / 2) (K := 16362665 / 4046689)
            (L := 7229 / 8240) (γ := 801 / 800)
            (by norm_num) hV
          · exact lowDeltaSenderStage_chord_mid_sharp b₁ b₂ le_rfl
              (by norm_num) le_rfl
          · exact lowDeltaStaticPolicyDrift_chord_mid_exact b₁ b₂ le_rfl
              (by norm_num) le_rfl
          · norm_num
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 1 / 2) (K := 16362665 / 4046689)
          (L := 3272533 / 1614720) (γ := 138859 / 139200)
          (by norm_num) hV
        · exact lowDeltaSenderStage_chord_high_sharp b₂ y le_rfl (by linarith)
        · exact lowDeltaStaticPolicyDrift_chord_high_exact b₂ y le_rfl (by linarith)
        · norm_num
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      have hxBelow : x.val ≤ b₂.val := le_of_not_ge hxHigh
      apply concatenate_state_chords x b₂ y hxBelow (by linarith)
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 1 / 2) (K := 16362665 / 4046689)
          (L := 7229 / 8240) (γ := 801 / 800)
          (by norm_num) hV
        · exact lowDeltaSenderStage_chord_mid_sharp x b₂
            (by simpa [b₁] using hxAbove) hxBelow le_rfl
        · exact lowDeltaStaticPolicyDrift_chord_mid_exact x b₂
            (by simpa [b₁] using hxAbove) hxBelow le_rfl
        · norm_num
      · apply lowDeltaStaticPolicyOperator_chord_of_bounds
          (β := 1 / 2) (K := 16362665 / 4046689)
          (L := 3272533 / 1614720) (γ := 138859 / 139200)
          (by norm_num) hV
        · exact lowDeltaSenderStage_chord_high_sharp b₂ y le_rfl (by linarith)
        · exact lowDeltaStaticPolicyDrift_chord_high_exact b₂ y le_rfl (by linarith)
        · norm_num

private theorem lowDeltaStaticSenderPolicyOperator_preserves_lipschitz
    (V : SBCF)
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith
      V (16362665 / 4046689)) :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaStaticPolicyOperator
        (1 / 2) lowDeltaFrozenSenderStage V)
      (16362665 / 4046689) := by
  intro x y
  rcases le_total x.val y.val with hxy | hyx
  · exact lowDeltaStaticSenderPolicyOperator_chord_ordered V hV x y hxy
  · simpa [abs_sub_comm, dist_comm] using
      lowDeltaStaticSenderPolicyOperator_chord_ordered V hV y x hyx

/-- The actual-transition Sender policy-evaluation center is globally
Lipschitz with the cellwise sharp closed-form bound
`(3272533/1614720) / (1 - (1/2)(138859/139200))
  = 16362665/4046689`. -/
theorem lowDeltaStaticSenderPolicyCenter_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      lowDeltaStaticSenderPolicyCenter
      (16362665 / 4046689) := by
  let T : SBCF → SBCF :=
    lowDeltaStaticPolicyOperator
      (1 / 2) lowDeltaFrozenSenderStage
  have hK : (0 : ℝ) ≤ 16362665 / 4046689 := by norm_num
  have hiter :
      ∀ n, Sanctions.AbstractGame.Params.ValueLipschitzWith
        (T^[n] (0 : SBCF)) (16362665 / 4046689) := by
    intro n
    induction n with
    | zero =>
        simpa using
          (Sanctions.AbstractGame.Params.valueLipschitzWith_zero hK)
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact lowDeltaStaticSenderPolicyOperator_preserves_lipschitz _ ih
  have htendsto :
      Tendsto (fun n => T^[n] (0 : SBCF)) atTop
        (𝓝 lowDeltaStaticSenderPolicyCenter) := by
    exact ContractingWith.tendsto_iterate_fixedPoint
      lowDeltaStaticSenderPolicyOperator_contracting (0 : SBCF)
  exact Sanctions.AbstractGame.Params.valueLipschitzWith_of_tendsto
    hK hiter htendsto

end Examples
end Sanctions
