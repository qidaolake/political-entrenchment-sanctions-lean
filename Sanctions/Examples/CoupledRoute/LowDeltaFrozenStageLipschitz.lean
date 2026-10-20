/-
Sanctions/Examples/CoupledRoute/LowDeltaFrozenStageLipschitz.lean

Exact state-Lipschitz budgets for the frozen static-Stackelberg reference.

The two frozen stage flows are piecewise quadratic, with the only breakpoints
coming from the already-derived static Sender and Target policies.  Their
global chord bounds are then propagated through the affine moving-average
Bellman iterations.  The resulting Banach centers inherit the closed-form
moduli `L / (1 - β)`.

No numerical convergence premise or new model assumption is used.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaFrozenReferenceCenter
import Sanctions.Theory.Shocked.ShockedValueLipschitz

namespace Sanctions
namespace Examples

open Set AbstractGame
open scoped NNReal
open BoundedContinuousFunction Filter Topology

/-! ## Exact piecewise stage flows -/

/-- Below the Sender-entry threshold, the frozen Target stage payoff is zero. -/
theorem lowDeltaFrozenTargetStage_eq_zero_of_le
    (x : ↥(Sanctions.S : Set ℝ)) (hx : x.val ≤ 2 / 27) :
    lowDeltaFrozenTargetStage x = 0 := by
  have hα : lowDeltaStaticTargetPolicy x.val = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le (by linarith)
  have hσ : lowDeltaStaticSenderPolicy x.val = 0 :=
    lowDeltaStaticSenderPolicy_eq_zero_of_le hx
  rw [lowDeltaFrozenTargetStage_apply, hα, hσ]
  norm_num [mwU_T]

/-- Between the Sender-entry and Target-activation thresholds, the frozen
Target stage payoff is the displayed quadratic. -/
theorem lowDeltaFrozenTargetStage_eq_mid
    (x : ↥(Sanctions.S : Set ℝ))
    (hx0 : 2 / 27 ≤ x.val) (hx1 : x.val ≤ 40 / 103) :
    lowDeltaFrozenTargetStage x =
      1 / 24 - (31 / 48) * x.val + (9 / 8) * x.val ^ 2 := by
  have hα : lowDeltaStaticTargetPolicy x.val = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le hx1
  have hσ :
      lowDeltaStaticSenderPolicy x.val =
        (9 / 8) * x.val - 1 / 12 := by
    rw [lowDeltaStaticSenderPolicy_eq_vertex_of_ge hx0 x.property.2, hα]
    norm_num [lowDeltaSenderInteriorVertex]
  rw [lowDeltaFrozenTargetStage_apply, hα, hσ]
  unfold mwU_T
  ring

/-- Above the Target-activation threshold, the frozen Target stage payoff is
the displayed quadratic. -/
theorem lowDeltaFrozenTargetStage_eq_high
    (x : ↥(Sanctions.S : Set ℝ)) (hx : 40 / 103 ≤ x.val) :
    lowDeltaFrozenTargetStage x =
      43 / 232 - (643 / 464) * x.val +
        (23137 / 11136) * x.val ^ 2 := by
  have hα :
      lowDeltaStaticTargetPolicy x.val =
        (103 / 116) * x.val - 10 / 29 :=
    lowDeltaStaticTargetPolicy_eq_vertex_of_ge hx
  have hσ :
      lowDeltaStaticSenderPolicy x.val =
        lowDeltaSenderInteriorVertex 0 x.val
          ((103 / 116) * x.val - 10 / 29) := by
    rw [lowDeltaStaticSenderPolicy_eq_vertex_of_ge (by linarith) x.property.2, hα]
  rw [lowDeltaFrozenTargetStage_apply, hα, hσ]
  unfold mwU_T lowDeltaSenderInteriorVertex
  ring

/-- Below the Sender-entry threshold, the frozen Sender stage payoff is
linear in the inherited state. -/
theorem lowDeltaFrozenSenderStage_eq_low
    (x : ↥(Sanctions.S : Set ℝ)) (hx : x.val ≤ 2 / 27) :
    lowDeltaFrozenSenderStage x = (2 / 5) * x.val := by
  have hα : lowDeltaStaticTargetPolicy x.val = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le (by linarith)
  have hσ : lowDeltaStaticSenderPolicy x.val = 0 :=
    lowDeltaStaticSenderPolicy_eq_zero_of_le hx
  rw [lowDeltaFrozenSenderStage_apply, hα, hσ]
  norm_num [mwU_S]

/-- Between the Sender-entry and Target-activation thresholds, the frozen
Sender stage payoff is the displayed quadratic. -/
theorem lowDeltaFrozenSenderStage_eq_mid
    (x : ↥(Sanctions.S : Set ℝ))
    (hx0 : 2 / 27 ≤ x.val) (hx1 : x.val ≤ 40 / 103) :
    lowDeltaFrozenSenderStage x =
      1 / 240 + (23 / 80) * x.val + (243 / 320) * x.val ^ 2 := by
  have hα : lowDeltaStaticTargetPolicy x.val = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le hx1
  have hσ :
      lowDeltaStaticSenderPolicy x.val =
        (9 / 8) * x.val - 1 / 12 := by
    rw [lowDeltaStaticSenderPolicy_eq_vertex_of_ge hx0 x.property.2, hα]
    norm_num [lowDeltaSenderInteriorVertex]
  rw [lowDeltaFrozenSenderStage_apply, hα, hσ]
  unfold mwU_S
  ring

/-- Above the Target-activation threshold, the frozen Sender stage payoff is
the displayed quadratic. -/
theorem lowDeltaFrozenSenderStage_eq_high
    (x : ↥(Sanctions.S : Set ℝ)) (hx : 40 / 103 ≤ x.val) :
    lowDeltaFrozenSenderStage x =
      -23053 / 67280 + (180661 / 134560) * x.val +
        (1104601 / 3229440) * x.val ^ 2 := by
  have hα :
      lowDeltaStaticTargetPolicy x.val =
        (103 / 116) * x.val - 10 / 29 :=
    lowDeltaStaticTargetPolicy_eq_vertex_of_ge hx
  have hσ :
      lowDeltaStaticSenderPolicy x.val =
        lowDeltaSenderInteriorVertex 0 x.val
          ((103 / 116) * x.val - 10 / 29) := by
    rw [lowDeltaStaticSenderPolicy_eq_vertex_of_ge (by linarith) x.property.2, hα]
  rw [lowDeltaFrozenSenderStage_apply, hα, hσ]
  unfold mwU_S lowDeltaSenderInteriorVertex
  ring

/-! ## Chord bounds for each quadratic cell -/

private theorem concatenate_lipschitz_bounds
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

private theorem lowDeltaFrozenTargetStage_chord_low
    (x y : ↥(Sanctions.S : Set ℝ))
    (hxy : x.val ≤ y.val) (hy : y.val ≤ 2 / 27) :
    |lowDeltaFrozenTargetStage y - lowDeltaFrozenTargetStage x| ≤
      (15421 / 5568) * dist x y := by
  rw [lowDeltaFrozenTargetStage_eq_zero_of_le y hy,
    lowDeltaFrozenTargetStage_eq_zero_of_le x (le_trans hxy hy)]
  simp only [sub_self, abs_zero]
  exact mul_nonneg (by positivity) dist_nonneg

private theorem lowDeltaFrozenTargetStage_chord_mid
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 2 / 27 ≤ x.val) (hxy : x.val ≤ y.val)
    (hy : y.val ≤ 40 / 103) :
    |lowDeltaFrozenTargetStage y - lowDeltaFrozenTargetStage x| ≤
      (15421 / 5568) * dist x y := by
  rw [lowDeltaFrozenTargetStage_eq_mid x hx (le_trans hxy hy),
    lowDeltaFrozenTargetStage_eq_mid y (le_trans hx hxy) hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  have hq :
      |-(31 / 48 : ℝ) + (9 / 8) * (x.val + y.val)| ≤
        15421 / 5568 := by
    rw [abs_le]
    constructor <;> nlinarith [x.property.1, y.property.2]
  have hfactor :
      (1 / 24 - (31 / 48) * y.val + (9 / 8) * y.val ^ 2) -
          (1 / 24 - (31 / 48) * x.val + (9 / 8) * x.val ^ 2) =
        (y.val - x.val) *
          (-(31 / 48) + (9 / 8) * (x.val + y.val)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hd, Subtype.dist_eq,
    Real.dist_eq, abs_sub_comm x.val y.val, abs_of_nonneg hd]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hd

private theorem lowDeltaFrozenTargetStage_chord_high
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

private theorem lowDeltaFrozenSenderStage_chord_low
    (x y : ↥(Sanctions.S : Set ℝ))
    (hxy : x.val ≤ y.val) (hy : y.val ≤ 2 / 27) :
    |lowDeltaFrozenSenderStage y - lowDeltaFrozenSenderStage x| ≤
      (3272533 / 1614720) * dist x y := by
  rw [lowDeltaFrozenSenderStage_eq_low x (le_trans hxy hy),
    lowDeltaFrozenSenderStage_eq_low y hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  rw [show (2 / 5) * y.val - (2 / 5) * x.val =
      (2 / 5) * (y.val - x.val) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 5),
    abs_of_nonneg hd, Subtype.dist_eq, Real.dist_eq,
    abs_sub_comm x.val y.val, abs_of_nonneg hd]
  apply mul_le_mul_of_nonneg_right _ hd
  norm_num

private theorem lowDeltaFrozenSenderStage_chord_mid
    (x y : ↥(Sanctions.S : Set ℝ))
    (hx : 2 / 27 ≤ x.val) (hxy : x.val ≤ y.val)
    (hy : y.val ≤ 40 / 103) :
    |lowDeltaFrozenSenderStage y - lowDeltaFrozenSenderStage x| ≤
      (3272533 / 1614720) * dist x y := by
  rw [lowDeltaFrozenSenderStage_eq_mid x hx (le_trans hxy hy),
    lowDeltaFrozenSenderStage_eq_mid y (le_trans hx hxy) hy]
  have hd : 0 ≤ y.val - x.val := sub_nonneg.mpr hxy
  have hq :
      |(23 / 80 : ℝ) + (243 / 320) * (x.val + y.val)| ≤
        3272533 / 1614720 := by
    rw [abs_le]
    constructor <;> nlinarith [x.property.1, y.property.2]
  have hfactor :
      (1 / 240 + (23 / 80) * y.val + (243 / 320) * y.val ^ 2) -
          (1 / 240 + (23 / 80) * x.val + (243 / 320) * x.val ^ 2) =
        (y.val - x.val) *
          ((23 / 80) + (243 / 320) * (x.val + y.val)) := by
    ring
  rw [hfactor, abs_mul, abs_of_nonneg hd, Subtype.dist_eq,
    Real.dist_eq, abs_sub_comm x.val y.val, abs_of_nonneg hd]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hq hd

private theorem lowDeltaFrozenSenderStage_chord_high
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

/-! ## Global frozen-stage moduli -/

private theorem lowDeltaFrozenTargetStage_chord_ordered
    (x y : ↥(Sanctions.S : Set ℝ)) (hxy : x.val ≤ y.val) :
    |lowDeltaFrozenTargetStage y - lowDeltaFrozenTargetStage x| ≤
      (15421 / 5568) * dist x y := by
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  by_cases hyLow : y.val ≤ b₁.val
  · exact lowDeltaFrozenTargetStage_chord_low x y hxy hyLow
  by_cases hxHigh : b₂.val ≤ x.val
  · exact lowDeltaFrozenTargetStage_chord_high x y hxHigh hxy
  by_cases hyMid : y.val ≤ b₂.val
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_lipschitz_bounds x b₁ y hxLow (by linarith)
      · exact lowDeltaFrozenTargetStage_chord_low x b₁ hxLow le_rfl
      · exact lowDeltaFrozenTargetStage_chord_mid b₁ y le_rfl (by linarith) hyMid
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      exact lowDeltaFrozenTargetStage_chord_mid x y
        (by simpa [b₁] using hxAbove) hxy hyMid
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_lipschitz_bounds x b₂ y (by linarith) (by linarith)
      · apply concatenate_lipschitz_bounds x b₁ b₂ hxLow (by norm_num)
        · exact lowDeltaFrozenTargetStage_chord_low x b₁ hxLow le_rfl
        · exact lowDeltaFrozenTargetStage_chord_mid b₁ b₂ le_rfl (by norm_num) le_rfl
      · exact lowDeltaFrozenTargetStage_chord_high b₂ y le_rfl (by linarith)
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      have hxBelow : x.val ≤ b₂.val := le_of_not_ge hxHigh
      apply concatenate_lipschitz_bounds x b₂ y hxBelow (by linarith)
      · exact lowDeltaFrozenTargetStage_chord_mid x b₂
          (by simpa [b₁] using hxAbove) hxBelow le_rfl
      · exact lowDeltaFrozenTargetStage_chord_high b₂ y le_rfl (by linarith)

/-- The frozen Target stage flow is globally Lipschitz with exact closed-form
constant `15421/5568`. -/
theorem lowDeltaFrozenTargetStage_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      lowDeltaFrozenTargetStage (15421 / 5568) := by
  intro x y
  rcases le_total x.val y.val with hxy | hyx
  · exact lowDeltaFrozenTargetStage_chord_ordered x y hxy
  · simpa [abs_sub_comm, dist_comm] using
      lowDeltaFrozenTargetStage_chord_ordered y x hyx

private theorem lowDeltaFrozenSenderStage_chord_ordered
    (x y : ↥(Sanctions.S : Set ℝ)) (hxy : x.val ≤ y.val) :
    |lowDeltaFrozenSenderStage y - lowDeltaFrozenSenderStage x| ≤
      (3272533 / 1614720) * dist x y := by
  let b₁ : ↥(Sanctions.S : Set ℝ) :=
    ⟨2 / 27, by constructor <;> norm_num⟩
  let b₂ : ↥(Sanctions.S : Set ℝ) :=
    ⟨40 / 103, by constructor <;> norm_num⟩
  by_cases hyLow : y.val ≤ b₁.val
  · exact lowDeltaFrozenSenderStage_chord_low x y hxy hyLow
  by_cases hxHigh : b₂.val ≤ x.val
  · exact lowDeltaFrozenSenderStage_chord_high x y hxHigh hxy
  by_cases hyMid : y.val ≤ b₂.val
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_lipschitz_bounds x b₁ y hxLow (by linarith)
      · exact lowDeltaFrozenSenderStage_chord_low x b₁ hxLow le_rfl
      · exact lowDeltaFrozenSenderStage_chord_mid b₁ y le_rfl (by linarith) hyMid
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      exact lowDeltaFrozenSenderStage_chord_mid x y
        (by simpa [b₁] using hxAbove) hxy hyMid
  · by_cases hxLow : x.val ≤ b₁.val
    · apply concatenate_lipschitz_bounds x b₂ y (by linarith) (by linarith)
      · apply concatenate_lipschitz_bounds x b₁ b₂ hxLow (by norm_num)
        · exact lowDeltaFrozenSenderStage_chord_low x b₁ hxLow le_rfl
        · exact lowDeltaFrozenSenderStage_chord_mid b₁ b₂ le_rfl (by norm_num) le_rfl
      · exact lowDeltaFrozenSenderStage_chord_high b₂ y le_rfl (by linarith)
    · have hxAbove : b₁.val ≤ x.val := le_of_not_ge hxLow
      have hxBelow : x.val ≤ b₂.val := le_of_not_ge hxHigh
      apply concatenate_lipschitz_bounds x b₂ y hxBelow (by linarith)
      · exact lowDeltaFrozenSenderStage_chord_mid x b₂
          (by simpa [b₁] using hxAbove) hxBelow le_rfl
      · exact lowDeltaFrozenSenderStage_chord_high b₂ y le_rfl (by linarith)

/-- The frozen Sender stage flow is globally Lipschitz with exact closed-form
constant `3272533/1614720`. -/
theorem lowDeltaFrozenSenderStage_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      lowDeltaFrozenSenderStage (3272533 / 1614720) := by
  intro x y
  rcases le_total x.val y.val with hxy | hyx
  · exact lowDeltaFrozenSenderStage_chord_ordered x y hxy
  · simpa [abs_sub_comm, dist_comm] using
      lowDeltaFrozenSenderStage_chord_ordered y x hyx

/-! ## Closed-form Banach-center moduli -/

/-- The Banach-constructed frozen Target center is globally Lipschitz with
`(15421/5568)/(1-9/10) = 77105/2784`. -/
theorem lowDeltaFrozenTargetCenter_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      lowDeltaFrozenTargetCenter (77105 / 2784) := by
  let T : SBCF → SBCF :=
    lowDeltaFrozenAffineOperator (9 / 10) lowDeltaFrozenTargetStage
  have hK : (0 : ℝ) ≤ 77105 / 2784 := by norm_num
  have hpreserves :
      ∀ V : SBCF,
        Sanctions.AbstractGame.Params.ValueLipschitzWith V (77105 / 2784) →
          Sanctions.AbstractGame.Params.ValueLipschitzWith (T V) (77105 / 2784) := by
    intro V hV x y
    have hstage := lowDeltaFrozenTargetStage_valueLipschitz x y
    have hsmear :=
      Sanctions.movAvgBCF_valueLipschitz lowDeltaH_pos V hK hV x y
    change
      |(lowDeltaFrozenTargetStage y +
            (9 / 10) * Sanctions.movAvgBCF lowDeltaH_pos V y) -
          (lowDeltaFrozenTargetStage x +
            (9 / 10) * Sanctions.movAvgBCF lowDeltaH_pos V x)| ≤
        (77105 / 2784) * dist x y
    have htriangle :
        |(lowDeltaFrozenTargetStage y -
              lowDeltaFrozenTargetStage x) +
            (9 / 10) *
              (Sanctions.movAvgBCF lowDeltaH_pos V y -
                Sanctions.movAvgBCF lowDeltaH_pos V x)| ≤
          |lowDeltaFrozenTargetStage y -
              lowDeltaFrozenTargetStage x| +
            (9 / 10) *
              |Sanctions.movAvgBCF lowDeltaH_pos V y -
                Sanctions.movAvgBCF lowDeltaH_pos V x| := by
      calc
        |(lowDeltaFrozenTargetStage y -
              lowDeltaFrozenTargetStage x) +
            (9 / 10) *
              (Sanctions.movAvgBCF lowDeltaH_pos V y -
                Sanctions.movAvgBCF lowDeltaH_pos V x)|
            ≤ |lowDeltaFrozenTargetStage y -
                  lowDeltaFrozenTargetStage x| +
                |(9 / 10) *
                  (Sanctions.movAvgBCF lowDeltaH_pos V y -
                    Sanctions.movAvgBCF lowDeltaH_pos V x)| :=
              abs_add_le _ _
        _ = |lowDeltaFrozenTargetStage y -
                lowDeltaFrozenTargetStage x| +
              (9 / 10) *
                |Sanctions.movAvgBCF lowDeltaH_pos V y -
                  Sanctions.movAvgBCF lowDeltaH_pos V x| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10)]
    rw [show
        (lowDeltaFrozenTargetStage y +
            (9 / 10) * Sanctions.movAvgBCF lowDeltaH_pos V y) -
          (lowDeltaFrozenTargetStage x +
            (9 / 10) * Sanctions.movAvgBCF lowDeltaH_pos V x) =
        (lowDeltaFrozenTargetStage y -
            lowDeltaFrozenTargetStage x) +
          (9 / 10) *
            (Sanctions.movAvgBCF lowDeltaH_pos V y -
              Sanctions.movAvgBCF lowDeltaH_pos V x) by ring]
    calc
      |(lowDeltaFrozenTargetStage y -
            lowDeltaFrozenTargetStage x) +
          (9 / 10) *
            (Sanctions.movAvgBCF lowDeltaH_pos V y -
              Sanctions.movAvgBCF lowDeltaH_pos V x)|
          ≤ |lowDeltaFrozenTargetStage y -
                lowDeltaFrozenTargetStage x| +
              (9 / 10) *
                |Sanctions.movAvgBCF lowDeltaH_pos V y -
                  Sanctions.movAvgBCF lowDeltaH_pos V x| := htriangle
      _ ≤ (15421 / 5568) * dist x y +
            (9 / 10) * ((77105 / 2784) * dist x y) := by
              gcongr
      _ = (77105 / 2784) * dist x y := by ring
  have hiter :
      ∀ n, Sanctions.AbstractGame.Params.ValueLipschitzWith
        (T^[n] (0 : SBCF)) (77105 / 2784) := by
    intro n
    induction n with
    | zero =>
        simpa using
          (Sanctions.AbstractGame.Params.valueLipschitzWith_zero hK)
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hpreserves _ ih
  have htendsto :
      Tendsto (fun n => T^[n] (0 : SBCF)) atTop
        (𝓝 lowDeltaFrozenTargetCenter) := by
    exact ContractingWith.tendsto_iterate_fixedPoint
      lowDeltaFrozenTargetOperator_contracting (0 : SBCF)
  exact Sanctions.AbstractGame.Params.valueLipschitzWith_of_tendsto
    hK hiter htendsto

/-- The Banach-constructed frozen Sender center is globally Lipschitz with
`(3272533/1614720)/(1-1/2) = 3272533/807360`. -/
theorem lowDeltaFrozenSenderCenter_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      lowDeltaFrozenSenderCenter (3272533 / 807360) := by
  let T : SBCF → SBCF :=
    lowDeltaFrozenAffineOperator (1 / 2) lowDeltaFrozenSenderStage
  have hK : (0 : ℝ) ≤ 3272533 / 807360 := by norm_num
  have hpreserves :
      ∀ V : SBCF,
        Sanctions.AbstractGame.Params.ValueLipschitzWith V (3272533 / 807360) →
          Sanctions.AbstractGame.Params.ValueLipschitzWith (T V) (3272533 / 807360) := by
    intro V hV x y
    have hstage := lowDeltaFrozenSenderStage_valueLipschitz x y
    have hsmear :=
      Sanctions.movAvgBCF_valueLipschitz lowDeltaH_pos V hK hV x y
    change
      |(lowDeltaFrozenSenderStage y +
            (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos V y) -
          (lowDeltaFrozenSenderStage x +
            (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos V x)| ≤
        (3272533 / 807360) * dist x y
    have htriangle :
        |(lowDeltaFrozenSenderStage y -
              lowDeltaFrozenSenderStage x) +
            (1 / 2) *
              (Sanctions.movAvgBCF lowDeltaH_pos V y -
                Sanctions.movAvgBCF lowDeltaH_pos V x)| ≤
          |lowDeltaFrozenSenderStage y -
              lowDeltaFrozenSenderStage x| +
            (1 / 2) *
              |Sanctions.movAvgBCF lowDeltaH_pos V y -
                Sanctions.movAvgBCF lowDeltaH_pos V x| := by
      calc
        |(lowDeltaFrozenSenderStage y -
              lowDeltaFrozenSenderStage x) +
            (1 / 2) *
              (Sanctions.movAvgBCF lowDeltaH_pos V y -
                Sanctions.movAvgBCF lowDeltaH_pos V x)|
            ≤ |lowDeltaFrozenSenderStage y -
                  lowDeltaFrozenSenderStage x| +
                |(1 / 2) *
                  (Sanctions.movAvgBCF lowDeltaH_pos V y -
                    Sanctions.movAvgBCF lowDeltaH_pos V x)| :=
              abs_add_le _ _
        _ = |lowDeltaFrozenSenderStage y -
                lowDeltaFrozenSenderStage x| +
              (1 / 2) *
                |Sanctions.movAvgBCF lowDeltaH_pos V y -
                  Sanctions.movAvgBCF lowDeltaH_pos V x| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show
        (lowDeltaFrozenSenderStage y +
            (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos V y) -
          (lowDeltaFrozenSenderStage x +
            (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos V x) =
        (lowDeltaFrozenSenderStage y -
            lowDeltaFrozenSenderStage x) +
          (1 / 2) *
            (Sanctions.movAvgBCF lowDeltaH_pos V y -
              Sanctions.movAvgBCF lowDeltaH_pos V x) by ring]
    calc
      |(lowDeltaFrozenSenderStage y -
            lowDeltaFrozenSenderStage x) +
          (1 / 2) *
            (Sanctions.movAvgBCF lowDeltaH_pos V y -
              Sanctions.movAvgBCF lowDeltaH_pos V x)|
          ≤ |lowDeltaFrozenSenderStage y -
                lowDeltaFrozenSenderStage x| +
              (1 / 2) *
                |Sanctions.movAvgBCF lowDeltaH_pos V y -
                  Sanctions.movAvgBCF lowDeltaH_pos V x| := htriangle
      _ ≤ (3272533 / 1614720) * dist x y +
            (1 / 2) * ((3272533 / 807360) * dist x y) := by
              gcongr
      _ = (3272533 / 807360) * dist x y := by ring
  have hiter :
      ∀ n, Sanctions.AbstractGame.Params.ValueLipschitzWith
        (T^[n] (0 : SBCF)) (3272533 / 807360) := by
    intro n
    induction n with
    | zero =>
        simpa using
          (Sanctions.AbstractGame.Params.valueLipschitzWith_zero hK)
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hpreserves _ ih
  have htendsto :
      Tendsto (fun n => T^[n] (0 : SBCF)) atTop
        (𝓝 lowDeltaFrozenSenderCenter) := by
    exact ContractingWith.tendsto_iterate_fixedPoint
      lowDeltaFrozenSenderOperator_contracting (0 : SBCF)
  exact Sanctions.AbstractGame.Params.valueLipschitzWith_of_tendsto
    hK hiter htendsto

/-! ## Sharpened smeared-center corollaries -/

/-- Moving averaging preserves the sharpened Target-center modulus
`77105/2784`; it does not revert to the coarser norm-over-bandwidth bound. -/
theorem lowDeltaFrozenTargetSmear_sharp_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaShocked.smear lowDeltaFrozenTargetCenter)
      (77105 / 2784) := by
  simpa only [lowDeltaShocked] using
    (Sanctions.AbstractGame.movAvgShockedParams_smear_valueLipschitz
      lowDeltaParams lowDeltaH_pos
      (by norm_num : (0 : ℝ) ≤ 77105 / 2784)
      lowDeltaFrozenTargetCenter_valueLipschitz)

/-- Moving averaging preserves the sharpened Sender-center modulus
`3272533/807360`; it does not revert to the coarser norm-over-bandwidth bound. -/
theorem lowDeltaFrozenSenderSmear_sharp_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaShocked.smear lowDeltaFrozenSenderCenter)
      (3272533 / 807360) := by
  simpa only [lowDeltaShocked] using
    (Sanctions.AbstractGame.movAvgShockedParams_smear_valueLipschitz
      lowDeltaParams lowDeltaH_pos
      (by norm_num : (0 : ℝ) ≤ 3272533 / 807360)
      lowDeltaFrozenSenderCenter_valueLipschitz)

end Examples
end Sanctions
