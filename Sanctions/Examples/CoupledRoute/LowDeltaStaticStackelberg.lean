/-
Sanctions/Examples/CoupledRoute/LowDeltaStaticStackelberg.lean

Exact static Stackelberg reference for the low-adjustment economy.

The Target policy is the nonnegative part of the interior static vertex,

  α₀(x) = max 0 ((103 / 116) x - 10 / 29).

The Sender then plays its already-proved optimal static response `mwσ`.
The main theorem proves a global modulus-one quadratic-growth inequality for
the Target objective on the full state-action square.  Thus both policies are
derived optimizers; no numerical convergence premise, fixed-point witness, or
new model assumption is introduced.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaLocalQuadraticBranches
import Sanctions.Examples.CoupledRoute.CoupledObjectiveDifference

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.AbstractGame.Params

/-! ## Exact static policies -/

/-- The exact static Stackelberg Target policy. -/
noncomputable def lowDeltaStaticTargetPolicy (x : ℝ) : ℝ :=
  max 0 (lowDeltaTargetInteriorVertex 0 0 x)

/-- The optimal static Sender response to the exact Target policy. -/
noncomputable def lowDeltaStaticSenderPolicy (x : ℝ) : ℝ :=
  mwσ x (lowDeltaStaticTargetPolicy x)

/-- The Target's static Stackelberg objective after substituting the optimal
Sender response. -/
noncomputable def lowDeltaStaticTargetObjective (x a : ℝ) : ℝ :=
  mwU_T x a (mwσ x a)

@[simp] theorem lowDeltaStaticTargetPolicy_eq (x : ℝ) :
    lowDeltaStaticTargetPolicy x =
      max 0 ((103 / 116) * x - 10 / 29) := by
  simp [lowDeltaStaticTargetPolicy, lowDeltaTargetInteriorVertex]

theorem lowDeltaStaticTargetPolicy_mem
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    lowDeltaStaticTargetPolicy x ∈ Sanctions.I := by
  rcases hx with ⟨hx0, hx1⟩
  rw [lowDeltaStaticTargetPolicy_eq]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (by nlinarith)

theorem lowDeltaStaticTargetPolicy_eq_zero_of_le
    {x : ℝ} (hx : x ≤ 40 / 103) :
    lowDeltaStaticTargetPolicy x = 0 := by
  rw [lowDeltaStaticTargetPolicy_eq, max_eq_left]
  nlinarith

theorem lowDeltaStaticTargetPolicy_eq_vertex_of_ge
    {x : ℝ} (hx : 40 / 103 ≤ x) :
    lowDeltaStaticTargetPolicy x =
      (103 / 116) * x - 10 / 29 := by
  rw [lowDeltaStaticTargetPolicy_eq, max_eq_right]
  nlinarith

private theorem mwσ_eq_zero_of_vertex_nonpos
    {x a : ℝ}
    (h : lowDeltaSenderInteriorVertex 0 x a ≤ 0) :
    mwσ x a = 0 := by
  have h' :
      (9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a ≤ 0 := by
    norm_num [lowDeltaSenderInteriorVertex] at h ⊢
    exact h
  rw [mwσ, max_eq_left]
  exact le_trans (min_le_right _ _) h'

private theorem mwσ_eq_vertex_of_vertex_mem
    {x a : ℝ}
    (h0 : 0 ≤ lowDeltaSenderInteriorVertex 0 x a)
    (h1 : lowDeltaSenderInteriorVertex 0 x a ≤ 1) :
    mwσ x a = lowDeltaSenderInteriorVertex 0 x a := by
  have h0' :
      0 ≤ (9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a := by
    norm_num [lowDeltaSenderInteriorVertex] at h0 ⊢
    exact h0
  have h1' :
      (9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a ≤ 1 := by
    norm_num [lowDeltaSenderInteriorVertex] at h1 ⊢
    exact h1
  rw [mwσ, min_eq_right h1', max_eq_right h0']
  norm_num [lowDeltaSenderInteriorVertex]

private theorem mwσ_eq_one_of_one_le_vertex
    {x a : ℝ}
    (h : 1 ≤ lowDeltaSenderInteriorVertex 0 x a) :
    mwσ x a = 1 := by
  have h' :
      1 ≤ (9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a := by
    norm_num [lowDeltaSenderInteriorVertex] at h ⊢
    exact h
  rw [mwσ, min_eq_left h', max_eq_right]
  norm_num

/-- Below `x = 2/27`, the exact static Target policy is zero and the optimal
Sender response is also zero. -/
theorem lowDeltaStaticSenderPolicy_eq_zero_of_le
    {x : ℝ} (hx : x ≤ 2 / 27) :
    lowDeltaStaticSenderPolicy x = 0 := by
  have hα : lowDeltaStaticTargetPolicy x = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le (by linarith)
  rw [lowDeltaStaticSenderPolicy, hα]
  apply mwσ_eq_zero_of_vertex_nonpos
  simp only [lowDeltaSenderInteriorVertex]
  nlinarith

/-- From `x = 2/27` upward, the optimal Sender response to the exact Target
policy is the unclipped interior vertex. -/
theorem lowDeltaStaticSenderPolicy_eq_vertex_of_ge
    {x : ℝ} (hx : 2 / 27 ≤ x) (hx1 : x ≤ 1) :
    lowDeltaStaticSenderPolicy x =
      lowDeltaSenderInteriorVertex 0 x (lowDeltaStaticTargetPolicy x) := by
  by_cases hxSwitch : x ≤ 40 / 103
  · have hα : lowDeltaStaticTargetPolicy x = 0 :=
      lowDeltaStaticTargetPolicy_eq_zero_of_le hxSwitch
    rw [lowDeltaStaticSenderPolicy, hα]
    apply mwσ_eq_vertex_of_vertex_mem
    · simp only [lowDeltaSenderInteriorVertex]
      nlinarith
    · simp only [lowDeltaSenderInteriorVertex]
      nlinarith
  · have hxSwitch' : 40 / 103 ≤ x := by
      linarith
    have hα :
        lowDeltaStaticTargetPolicy x =
          (103 / 116) * x - 10 / 29 :=
      lowDeltaStaticTargetPolicy_eq_vertex_of_ge hxSwitch'
    rw [lowDeltaStaticSenderPolicy, hα]
    apply mwσ_eq_vertex_of_vertex_mem
    · simp only [lowDeltaSenderInteriorVertex]
      nlinarith
    · simp only [lowDeltaSenderInteriorVertex]
      nlinarith

/-! ## Disprove-first modulus check -/

/-- The interior-branch coefficient `29/24` cannot be promoted to a global
quadratic-growth modulus across the Sender-response kink.  At the exact
Target switch state and action one, the global objective gap is smaller. -/
theorem lowDeltaStaticTarget_not_quadraticGrowth_29_div_24 :
    ¬ (29 / 24 : ℝ) *
          ((1 : ℝ) - lowDeltaStaticTargetPolicy (40 / 103)) ^ 2 ≤
        lowDeltaStaticTargetObjective (40 / 103)
            (lowDeltaStaticTargetPolicy (40 / 103)) -
          lowDeltaStaticTargetObjective (40 / 103) 1 := by
  have hα :
      lowDeltaStaticTargetPolicy (40 / 103) = 0 :=
    lowDeltaStaticTargetPolicy_eq_zero_of_le le_rfl
  have hσ0 :
      mwσ (40 / 103) 0 =
        lowDeltaSenderInteriorVertex 0 (40 / 103) 0 := by
    apply mwσ_eq_vertex_of_vertex_mem
    · norm_num [lowDeltaSenderInteriorVertex]
    · norm_num [lowDeltaSenderInteriorVertex]
  have hσ1 : mwσ (40 / 103) 1 = 0 := by
    apply mwσ_eq_zero_of_vertex_nonpos
    norm_num [lowDeltaSenderInteriorVertex]
  rw [hα]
  simp only [lowDeltaStaticTargetObjective, hσ0, hσ1]
  norm_num [mwU_T, lowDeltaSenderInteriorVertex]

/-! ## Global static Target optimality -/

/-- **Global exact static Target quadratic growth.** At every physical state,
the displayed Target policy beats every feasible deviation by at least the
squared action distance.  The proof covers all three realized Sender-response
branches (`0`, interior, and `1`) with exact rational algebra. -/
theorem lowDeltaStaticTargetPolicy_quadraticGrowth
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤
      lowDeltaStaticTargetObjective x (lowDeltaStaticTargetPolicy x) -
        lowDeltaStaticTargetObjective x a := by
  rcases hx with ⟨hx0, hx1⟩
  rcases ha with ⟨ha0, ha1⟩
  by_cases hxLow : x ≤ 2 / 27
  · have hα : lowDeltaStaticTargetPolicy x = 0 :=
      lowDeltaStaticTargetPolicy_eq_zero_of_le (by linarith)
    have hσ0 : mwσ x 0 = 0 := by
      apply mwσ_eq_zero_of_vertex_nonpos
      simp only [lowDeltaSenderInteriorVertex]
      nlinarith
    have hσa : mwσ x a = 0 := by
      apply mwσ_eq_zero_of_vertex_nonpos
      simp only [lowDeltaSenderInteriorVertex]
      nlinarith
    rw [hα]
    simp only [lowDeltaStaticTargetObjective, hσ0, hσa, mwU_T]
    nlinarith
  · have hxAbove : 2 / 27 ≤ x := by linarith
    by_cases hxSwitch : x ≤ 40 / 103
    · have hα : lowDeltaStaticTargetPolicy x = 0 :=
        lowDeltaStaticTargetPolicy_eq_zero_of_le hxSwitch
      have hvertex0 :
          0 ≤ lowDeltaSenderInteriorVertex 0 x 0 ∧
            lowDeltaSenderInteriorVertex 0 x 0 ≤ 1 := by
        simp only [lowDeltaSenderInteriorVertex]
        constructor <;> nlinarith
      have hσ0 :
          mwσ x 0 = lowDeltaSenderInteriorVertex 0 x 0 :=
        mwσ_eq_vertex_of_vertex_mem hvertex0.1 hvertex0.2
      by_cases hvertexA :
          lowDeltaSenderInteriorVertex 0 x a ≤ 0
      · have hσa : mwσ x a = 0 :=
          mwσ_eq_zero_of_vertex_nonpos hvertexA
        have hthreshold :
            (27 / 10 : ℝ) * x - 1 / 5 ≤ a := by
          simp only [lowDeltaSenderInteriorVertex] at hvertexA
          linarith
        have hxHalf : x ≤ 1 / 2 := by
          linarith
        have hbase :
            0 ≤ (171 / 40 : ℝ) * (x - 2 / 27) * (1 / 2 - x) :=
          mul_nonneg
            (mul_nonneg (by norm_num) (sub_nonneg.mpr hxAbove))
            (sub_nonneg.mpr hxHalf)
        rw [hα]
        simp only [lowDeltaStaticTargetObjective, hσ0, hσa,
          mwU_T, lowDeltaSenderInteriorVertex]
        nlinarith
      · have hvertexA0 :
            0 ≤ lowDeltaSenderInteriorVertex 0 x a := by
          linarith
        have hvertexA1 :
            lowDeltaSenderInteriorVertex 0 x a ≤ 1 := by
          simp only [lowDeltaSenderInteriorVertex] at hvertexA0 ⊢
          nlinarith
        have hσa :
            mwσ x a = lowDeltaSenderInteriorVertex 0 x a :=
          mwσ_eq_vertex_of_vertex_mem hvertexA0 hvertexA1
        rw [hα]
        simp only [lowDeltaStaticTargetObjective, hσ0, hσa,
          mwU_T, lowDeltaSenderInteriorVertex]
        nlinarith [sq_nonneg a]
    · have hxSwitch' : 40 / 103 ≤ x := by
        linarith
      have hα :
          lowDeltaStaticTargetPolicy x =
            (103 / 116) * x - 10 / 29 :=
        lowDeltaStaticTargetPolicy_eq_vertex_of_ge hxSwitch'
      let α : ℝ := (103 / 116) * x - 10 / 29
      have hvertexα :
          0 ≤ lowDeltaSenderInteriorVertex 0 x α ∧
            lowDeltaSenderInteriorVertex 0 x α ≤ 1 := by
        dsimp only [α]
        simp only [lowDeltaSenderInteriorVertex]
        constructor <;> nlinarith
      have hσα :
          mwσ x α = lowDeltaSenderInteriorVertex 0 x α :=
        mwσ_eq_vertex_of_vertex_mem hvertexα.1 hvertexα.2
      by_cases hvertexA0 :
          lowDeltaSenderInteriorVertex 0 x a ≤ 0
      · have hσa : mwσ x a = 0 :=
          mwσ_eq_zero_of_vertex_nonpos hvertexA0
        have hthreshold :
            (27 / 10 : ℝ) * x - 1 / 5 ≤ a := by
          simp only [lowDeltaSenderInteriorVertex] at hvertexA0
          linarith
        have hcoef : 0 ≤ (18 - 13 * x) / 58 := by
          nlinarith
        have hprod :
            0 ≤ ((18 - 13 * x) / 58) *
              (a - ((27 / 10) * x - 1 / 5)) :=
          mul_nonneg hcoef (sub_nonneg.mpr hthreshold)
        have hbase :
            0 ≤ (147 / 33640 : ℝ) + (7357 / 67280) * x +
              (1104601 / 1614720) * x ^ 2 := by
          positivity
        rw [hα]
        change
          (a - α) ^ 2 ≤
            lowDeltaStaticTargetObjective x α -
              lowDeltaStaticTargetObjective x a
        simp only [lowDeltaStaticTargetObjective, hσα, hσa,
          mwU_T, lowDeltaSenderInteriorVertex, α]
        nlinarith
      · have hvertexApos :
            0 ≤ lowDeltaSenderInteriorVertex 0 x a := by
          linarith
        by_cases hvertexA1 :
            lowDeltaSenderInteriorVertex 0 x a ≤ 1
        · have hσa :
              mwσ x a = lowDeltaSenderInteriorVertex 0 x a :=
            mwσ_eq_vertex_of_vertex_mem hvertexApos hvertexA1
          rw [hα]
          change
            (a - α) ^ 2 ≤
              lowDeltaStaticTargetObjective x α -
                lowDeltaStaticTargetObjective x a
          simp only [lowDeltaStaticTargetObjective, hσα, hσa,
            mwU_T, lowDeltaSenderInteriorVertex, α]
          nlinarith [sq_nonneg (a - α)]
        · have hvertexAone :
              1 ≤ lowDeltaSenderInteriorVertex 0 x a := by
            linarith
          have hσa : mwσ x a = 1 :=
            mwσ_eq_one_of_one_le_vertex hvertexAone
          have hthreshold :
              a ≤ (27 / 10 : ℝ) * x - 13 / 5 := by
            simp only [lowDeltaSenderInteriorVertex] at hvertexAone
            linarith
          have hcoef :
              (-11 - 13 * x) / 58 ≤ (0 : ℝ) := by
            nlinarith
          have hprod :
              0 ≤ ((-11 - 13 * x) / 58) *
                (a - ((27 / 10) * x - 13 / 5)) :=
            mul_nonneg_of_nonpos_of_nonpos hcoef
              (sub_nonpos.mpr hthreshold)
          have hbase :
              0 ≤ (1104601 / 1614720 : ℝ) *
                (x - 1308 / 1051) ^ 2 :=
            mul_nonneg (by norm_num) (sq_nonneg _)
          rw [hα]
          change
            (a - α) ^ 2 ≤
              lowDeltaStaticTargetObjective x α -
                lowDeltaStaticTargetObjective x a
          simp only [lowDeltaStaticTargetObjective, hσα, hσa,
            mwU_T, lowDeltaSenderInteriorVertex, α]
          nlinarith

/-- The exact Target policy is a global maximizer of the static Stackelberg
objective after substituting the Sender's optimal response. -/
theorem lowDeltaStaticTargetPolicy_isMaxOn
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn (lowDeltaStaticTargetObjective x) Sanctions.I
      (lowDeltaStaticTargetPolicy x) := by
  rw [isMaxOn_iff]
  intro a ha
  have h := lowDeltaStaticTargetPolicy_quadraticGrowth hx ha
  nlinarith [sq_nonneg (a - lowDeltaStaticTargetPolicy x)]

/-- The exact Target policy is the unique feasible maximizer of the static
Stackelberg objective. -/
theorem lowDeltaStaticTargetPolicy_unique
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (lowDeltaStaticTargetObjective x) Sanctions.I a) :
    a = lowDeltaStaticTargetPolicy x := by
  have hmem := lowDeltaStaticTargetPolicy_mem hx
  have hge :=
    (isMaxOn_iff.mp hmax) (lowDeltaStaticTargetPolicy x) hmem
  have hgap := lowDeltaStaticTargetPolicy_quadraticGrowth hx ha
  have hsquare :
      (a - lowDeltaStaticTargetPolicy x) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - lowDeltaStaticTargetPolicy x)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-! ## Uniform perturbation consequence -/

/-- Any maximizer of an objective uniformly within `ε` of the exact static
Stackelberg objective lies within squared action distance `2ε` of the exact
Target policy.  This is the model-specific perturbation consequence of the
global modulus-one quadratic-growth theorem. -/
theorem lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation
    {f : ℝ → ℝ} {x a ε : ℝ}
    (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn f Sanctions.I a)
    (hclose :
      ∀ z ∈ Sanctions.I,
        |f z - lowDeltaStaticTargetObjective x z| ≤ ε) :
    (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤ 2 * ε := by
  have hαmem := lowDeltaStaticTargetPolicy_mem hx
  have hopt :=
    (isMaxOn_iff.mp hmax) (lowDeltaStaticTargetPolicy x) hαmem
  have hgap := lowDeltaStaticTargetPolicy_quadraticGrowth hx ha
  have hcloseα := abs_le.mp
    (hclose (lowDeltaStaticTargetPolicy x) hαmem)
  have hclosea := abs_le.mp (hclose a ha)
  linarith

/-- Consequently, if `2ε < r²`, every maximizer of the perturbed objective
lies strictly inside the radius-`r` action branch around the exact Target
policy. -/
theorem lowDeltaStaticTargetPolicy_maximizer_mem_Ioo_of_uniform_perturbation
    {f : ℝ → ℝ} {x a ε r : ℝ}
    (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hr : 0 ≤ r)
    (hmax : IsMaxOn f Sanctions.I a)
    (hclose :
      ∀ z ∈ Sanctions.I,
        |f z - lowDeltaStaticTargetObjective x z| ≤ ε)
    (hsmall : 2 * ε < r ^ 2) :
    a ∈ Set.Ioo
      (lowDeltaStaticTargetPolicy x - r)
      (lowDeltaStaticTargetPolicy x + r) := by
  have hsq :=
    lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation
      hx ha hmax hclose
  constructor <;> nlinarith [sq_nonneg
    (a - lowDeltaStaticTargetPolicy x)]

/-! ## Direct application to the coupled dynamic objective -/

/-- On the existing Sender continuation carrier, the coupled dynamic Target
objective is uniformly close to the exact static Stackelberg objective.  The
exact bound is linear in the two continuation-value norms and follows from
the already-proved one-box pointwise perturbation estimate. -/
theorem coupledLeaderObj_close_lowDeltaStaticTargetObjective
    (V_T V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS)
    (x : ↥(Sanctions.S : Set ℝ)) (a : ℝ) (ha : a ∈ Sanctions.I) :
    |coupledLeaderObj V_T V_S x.val a -
        lowDeltaStaticTargetObjective x.val a| ≤
      (9 / 10) * ‖V_T‖ +
        (43520000 / 283976393) * ‖V_S‖ := by
  have h :=
    coupledLeaderObj_pair_pointwise_bound_on_lip_carrier
      V_T 0 V_S 0
      (zero_mem_valLipBall (M := 20) (by norm_num) (by norm_num)).2
      hV_S.2 zero_mem_coupledCarrierS.2 x a ha
  rw [coupledLeaderObj_zero_zero] at h
  simpa only [lowDeltaStaticTargetObjective, dist_zero_right] using h

/-- Any feasible maximizer of the actual coupled dynamic Target objective is
localized around the exact static Target policy.  Its squared displacement is
at most twice the exact continuation-value perturbation bound. -/
theorem coupledLeaderObj_maximizer_sq_le_staticTargetPolicy
    (V_T V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS)
    (x : ↥(Sanctions.S : Set ℝ)) (a : ℝ) (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (coupledLeaderObj V_T V_S x.val) Sanctions.I a) :
    (a - lowDeltaStaticTargetPolicy x.val) ^ 2 ≤
      2 * ((9 / 10) * ‖V_T‖ +
        (43520000 / 283976393) * ‖V_S‖) := by
  apply
    lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation
      x.property ha hmax
  intro z hz
  exact coupledLeaderObj_close_lowDeltaStaticTargetObjective
    V_T V_S hV_S x z hz

/-- If the exact continuation-value perturbation budget is smaller than
`r² / 2`, every coupled dynamic Target maximizer remains in the radius-`r`
action branch around the exact static policy. -/
theorem coupledLeaderObj_maximizer_mem_staticTargetPolicy_Ioo
    (V_T V_S : SBCF) (hV_S : V_S ∈ coupledCarrierS)
    (x : ↥(Sanctions.S : Set ℝ)) (a : ℝ) (ha : a ∈ Sanctions.I)
    (r : ℝ) (hr : 0 ≤ r)
    (hmax : IsMaxOn (coupledLeaderObj V_T V_S x.val) Sanctions.I a)
    (hsmall :
      2 * ((9 / 10) * ‖V_T‖ +
        (43520000 / 283976393) * ‖V_S‖) < r ^ 2) :
    a ∈ Set.Ioo
      (lowDeltaStaticTargetPolicy x.val - r)
      (lowDeltaStaticTargetPolicy x.val + r) := by
  apply
    lowDeltaStaticTargetPolicy_maximizer_mem_Ioo_of_uniform_perturbation
      x.property ha hr hmax
  · intro z hz
    exact coupledLeaderObj_close_lowDeltaStaticTargetObjective
      V_T V_S hV_S x z hz
  · exact hsmall

end Examples
end Sanctions
