/-
Sanctions/Theory/Basin/Tipping.lean

**Parametric tipping mechanism (extracted from
`Theory/Equilibrium/Tipping.lean` during the 2026-05-23 AbstractGame
refactor).**

All content here is purely parametric — no `Bilateral.Params` dependency.
The bilateral-specific `σ_dynamic` wedge form was DELETED with the
bilateral concrete spec; the abstract forward-looking Sender argmax is
`Sanctions.AbstractGame.Params.σ_dyn` (via Classical.choose, in
`Theory/Equilibrium/JointMPE.lean`).

**Rule-1 compliance.** Theorems work at the scalar FD level; they don't
take a fixed-action policy. `optimizer_at_zero_from_*` theorems
produce an a = 0 conclusion from concavity/wedge-domination
hypotheses — Rule-1 compliant when used in dynamic equilibrium chains.

**Rule-3 compliance.** No new hypothesis. All theorems extracted
verbatim from `Tipping.lean`.

**Rule-5 compliance.** Fully parametric.
-/

import Sanctions.Foundations.Basic
import Sanctions.Theory.Bellman.BellmanT  -- for clipS' re-use via re-export

noncomputable section
open Set Filter Topology

namespace Sanctions
namespace Tipping

/-! ## Setup -/

def boundaryMyopic (U_T_a U_T_s σ_a : ℝ) : ℝ := U_T_a + σ_a * U_T_s

def continuationWedge (β_T σ_a δ V_T_x_F : ℝ) : ℝ :=
  β_T * σ_a * δ * V_T_x_F

theorem continuationWedge_nonpos
    {β_T σ_a δ V_T_x_F : ℝ}
    (hβ : 0 < β_T) (hσ : σ_a < 0) (hδ : 0 ≤ δ) (hV : 0 ≤ V_T_x_F) :
    continuationWedge β_T σ_a δ V_T_x_F ≤ 0 := by
  unfold continuationWedge
  have h1 : β_T * σ_a < 0 := mul_neg_of_pos_of_neg hβ hσ
  have h2 : β_T * σ_a * δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt h1) hδ
  exact mul_nonpos_of_nonpos_of_nonneg h2 hV

theorem continuationWedge_neg
    {β_T σ_a δ V_T_x_F : ℝ}
    (hβ : 0 < β_T) (hσ : σ_a < 0) (hδ : 0 < δ) (hV : 0 < V_T_x_F) :
    continuationWedge β_T σ_a δ V_T_x_F < 0 := by
  unfold continuationWedge
  have h1 : β_T * σ_a < 0 := mul_neg_of_pos_of_neg hβ hσ
  have h2 : β_T * σ_a * δ < 0 := mul_neg_of_neg_of_pos h1 hδ
  exact mul_neg_of_neg_of_pos h2 hV

def boundaryDynamic (U_T_a U_T_s σ_a β_T δ V_T_x_F : ℝ) : ℝ :=
  boundaryMyopic U_T_a U_T_s σ_a + continuationWedge β_T σ_a δ V_T_x_F

theorem boundary_wedge_eq
    (U_T_a U_T_s σ_a β_T δ V_T_x_F : ℝ) :
    boundaryDynamic U_T_a U_T_s σ_a β_T δ V_T_x_F
      = boundaryMyopic U_T_a U_T_s σ_a + continuationWedge β_T σ_a δ V_T_x_F := rfl

theorem dynamic_le_myopic_boundary
    {U_T_a U_T_s σ_a β_T δ V_T_x_F : ℝ}
    (hβ : 0 < β_T) (hσ : σ_a < 0) (hδ : 0 ≤ δ) (hV : 0 ≤ V_T_x_F) :
    boundaryDynamic U_T_a U_T_s σ_a β_T δ V_T_x_F
      ≤ boundaryMyopic U_T_a U_T_s σ_a := by
  unfold boundaryDynamic
  have := continuationWedge_nonpos hβ hσ hδ hV
  linarith

theorem tipping_at_x0
    {U_T_a U_T_s σ_a β_T δ V_T_x_F : ℝ}
    (_hβ : 0 < β_T) (_hσ : σ_a < 0)
    (_hδ : 0 < δ) (_hV : 0 < V_T_x_F)
    (_hmyo_pos : 0 < boundaryMyopic U_T_a U_T_s σ_a)
    (hwedge_dominates :
      boundaryMyopic U_T_a U_T_s σ_a
        < -(continuationWedge β_T σ_a δ V_T_x_F)) :
    boundaryDynamic U_T_a U_T_s σ_a β_T δ V_T_x_F < 0 := by
  unfold boundaryDynamic; linarith

/-! ## Finite-difference wedge -/

def continuationWedge_FD (β_T σ_a V_diff : ℝ) : ℝ :=
  β_T * σ_a * V_diff

def boundaryDynamic_FD (U_T_a U_T_s σ_a β_T V_diff : ℝ) : ℝ :=
  boundaryMyopic U_T_a U_T_s σ_a + continuationWedge_FD β_T σ_a V_diff

theorem continuationWedge_FD_nonpos
    {β_T σ_a V_diff : ℝ}
    (hβ : 0 < β_T) (hσ : σ_a < 0) (h_diff : 0 ≤ V_diff) :
    continuationWedge_FD β_T σ_a V_diff ≤ 0 := by
  unfold continuationWedge_FD
  have h1 : β_T * σ_a < 0 := mul_neg_of_pos_of_neg hβ hσ
  exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt h1) h_diff

theorem continuationWedge_FD_neg
    {β_T σ_a V_diff : ℝ}
    (hβ : 0 < β_T) (hσ : σ_a < 0) (h_diff : 0 < V_diff) :
    continuationWedge_FD β_T σ_a V_diff < 0 := by
  unfold continuationWedge_FD
  have h1 : β_T * σ_a < 0 := mul_neg_of_pos_of_neg hβ hσ
  exact mul_neg_of_neg_of_pos h1 h_diff

theorem tipping_at_x0_FD
    {U_T_a U_T_s σ_a β_T V_diff : ℝ}
    (_hβ : 0 < β_T) (_hσ : σ_a < 0)
    (_h_diff : 0 < V_diff)
    (_hmyo_pos : 0 < boundaryMyopic U_T_a U_T_s σ_a)
    (hwedge_dominates :
      boundaryMyopic U_T_a U_T_s σ_a
        < -(continuationWedge_FD β_T σ_a V_diff)) :
    boundaryDynamic_FD U_T_a U_T_s σ_a β_T V_diff < 0 := by
  unfold boundaryDynamic_FD; linarith

/-! ## Optimizer-at-zero theorems -/

theorem optimizer_at_zero_from_secant_decrease
    {R_dyn : ℝ → ℝ}
    (h_secant_dec : ∀ a ∈ Set.Ioc (0 : ℝ) 1, R_dyn a < R_dyn 0) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, R_dyn a ≤ R_dyn 0 := by
  intro a ha
  rcases eq_or_lt_of_le ha.1 with h_eq | h_pos
  · rw [← h_eq]
  · exact le_of_lt (h_secant_dec a ⟨h_pos, ha.2⟩)

theorem strictConcave_negSlope_implies_strict_decreasing
    {f : ℝ → ℝ}
    (h_concave : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) a)
    (h_slope_neg : (f x₀ - f 0) / x₀ < 0) :
    f a < f 0 := by
  obtain ⟨ha_pos, ha_le⟩ := ha
  obtain ⟨hx₀_pos, hx₀_lt_a⟩ := hx₀
  have h_0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have h_x₀_mem : x₀ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt hx₀_pos, le_of_lt (lt_of_lt_of_le hx₀_lt_a ha_le)⟩
  have h_a_mem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ha_pos, ha_le⟩
  have h_x₀_ne_0 : x₀ ≠ 0 := ne_of_gt hx₀_pos
  have h_a_ne_0 : a ≠ 0 := ne_of_gt ha_pos
  have h_slope_a_lt_x₀ :
      (f a - f 0) / (a - 0) < (f x₀ - f 0) / (x₀ - 0) :=
    h_concave.secant_strict_mono h_0_mem h_x₀_mem h_a_mem h_x₀_ne_0 h_a_ne_0 hx₀_lt_a
  simp only [sub_zero] at h_slope_a_lt_x₀
  have h_slope_a_neg : (f a - f 0) / a < 0 := lt_trans h_slope_a_lt_x₀ h_slope_neg
  have h_diff_neg : f a - f 0 < 0 := by
    have h_eq : (f a - f 0) / a * a = f a - f 0 := div_mul_cancel₀ _ h_a_ne_0
    have h_lt : (f a - f 0) / a * a < 0 * a :=
      mul_lt_mul_of_pos_right h_slope_a_neg ha_pos
    rw [h_eq, zero_mul] at h_lt
    exact h_lt
  linarith

theorem optimizer_at_zero_from_strictConcave_local_decrease_at_zero
    {R_dyn : ℝ → ℝ}
    (h_concave : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) R_dyn)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_local : ∀ x ∈ Set.Ioo (0 : ℝ) δ, R_dyn x < R_dyn 0) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, R_dyn a ≤ R_dyn 0 := by
  intro a ha
  obtain ⟨ha_lo, ha_hi⟩ := ha
  rcases eq_or_lt_of_le ha_lo with h_eq | h_pos
  · rw [← h_eq]
  rcases lt_or_ge a δ with h_lt | h_ge
  · exact le_of_lt (h_local a ⟨h_pos, h_lt⟩)
  · have hδ2_pos : (0 : ℝ) < δ / 2 := by linarith
    have hδ2_lt_δ : δ / 2 < δ := by linarith
    have hδ2_lt_a : δ / 2 < a := lt_of_lt_of_le hδ2_lt_δ h_ge
    have h_R_lt : R_dyn (δ / 2) < R_dyn 0 := h_local (δ / 2) ⟨hδ2_pos, hδ2_lt_δ⟩
    have h_slope_neg : (R_dyn (δ / 2) - R_dyn 0) / (δ / 2) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hδ2_pos
    have h_strict :=
      strictConcave_negSlope_implies_strict_decreasing
        h_concave a ⟨h_pos, ha_hi⟩ (δ / 2) ⟨hδ2_pos, hδ2_lt_a⟩ h_slope_neg
    exact le_of_lt h_strict

/-! ## Long-run sanction gap -/

theorem long_run_gap
    {s_dyn s_myo : ℕ → ℝ} {x_inf s_lb : ℝ}
    (hdyn : Tendsto s_dyn atTop (𝓝 x_inf))
    (hmyo : Tendsto s_myo atTop (𝓝 0))
    (hlb : s_lb ≤ x_inf) :
    Tendsto (fun n => s_dyn n - s_myo n) atTop (𝓝 x_inf) ∧ s_lb ≤ x_inf := by
  refine ⟨?_, hlb⟩
  have h : Tendsto (fun n => s_dyn n - s_myo n) atTop (𝓝 (x_inf - 0)) :=
    hdyn.sub hmyo
  simpa using h

theorem long_run_gap_eventually_geq
    {s_dyn s_myo : ℕ → ℝ} {x_inf : ℝ}
    (h_gap : Tendsto (fun n => s_dyn n - s_myo n) atTop (𝓝 x_inf))
    (h_pos : 0 < x_inf) :
    ∀ᶠ n in atTop, s_myo n ≤ s_dyn n := by
  have h_eventually_pos : ∀ᶠ n in atTop, 0 < s_dyn n - s_myo n :=
    h_gap.eventually (eventually_gt_nhds h_pos)
  filter_upwards [h_eventually_pos] with n hn
  linarith

/-! ## FD tipping evaluated at an abstract `V_T : ↥S → ℝ` -/

/-- Per-state FD of V_T : ↥S → ℝ at a post-transition state F : ℝ with perturbation h. -/
noncomputable def V_diff_at
    (V_T : ↥(Sanctions.S : Set ℝ) → ℝ)
    (F : ℝ) (h : ℝ) : ℝ :=
  V_T (Sanctions.clipS' (F + h)) - V_T (Sanctions.clipS' F)

noncomputable def boundaryDynamic_FD_at
    (U_T_a U_T_s σ_a β_T : ℝ)
    (V_T : ↥(Sanctions.S : Set ℝ) → ℝ)
    (F : ℝ) (h : ℝ) : ℝ :=
  boundaryDynamic_FD U_T_a U_T_s σ_a β_T (V_diff_at V_T F h)

/-- **FD-form tipping evaluated at a value function `V_T`.** Convenience
wrapper of `tipping_at_x0_FD` that takes `V_T : ↥S → ℝ` and
`F : ℝ` directly and consumes `V_diff = V_diff_at V_T F h` inside.
Fully parametric over scalar `U_T_a, U_T_s, σ_a, β_T` and the
abstract value function `V_T`; the previous name `tipping_at_bilateral_FD`
was a vestige of the deleted bilateral spec and did not reflect the
theorem's abstract content. -/
theorem tipping_at_FD_via_V_T
    {U_T_a U_T_s σ_a β_T : ℝ}
    (V_T : ↥(Sanctions.S : Set ℝ) → ℝ) (F : ℝ) {h : ℝ}
    (_hβ : 0 < β_T) (_hσ : σ_a < 0)
    (_h_diff : 0 < V_diff_at V_T F h)
    (_hmyo_pos : 0 < boundaryMyopic U_T_a U_T_s σ_a)
    (hwedge_dominates :
      boundaryMyopic U_T_a U_T_s σ_a
        < -(continuationWedge_FD β_T σ_a (V_diff_at V_T F h))) :
    boundaryDynamic_FD_at U_T_a U_T_s σ_a β_T V_T F h < 0 := by
  unfold boundaryDynamic_FD_at
  exact tipping_at_x0_FD _hβ _hσ _h_diff _hmyo_pos hwedge_dominates

theorem V_diff_at_nonneg_of_le_nondec
    (V_T : ↥(Sanctions.S : Set ℝ) → ℝ)
    (F h : ℝ)
    (h_clip_le : (Sanctions.clipS' F : ℝ) ≤ (Sanctions.clipS' (F + h) : ℝ))
    (h_V_T_mono : ∀ ⦃x y : ↥(Sanctions.S : Set ℝ)⦄,
        (x : ℝ) ≤ (y : ℝ) → V_T x ≤ V_T y) :
    0 ≤ V_diff_at V_T F h := by
  unfold V_diff_at
  have := h_V_T_mono (x := Sanctions.clipS' F)
    (y := Sanctions.clipS' (F + h)) h_clip_le
  linarith

theorem V_diff_at_pos_of_lt_strict_mono
    (V_T : ↥(Sanctions.S : Set ℝ) → ℝ)
    (F h : ℝ)
    (h_clip_lt : (Sanctions.clipS' F : ℝ) < (Sanctions.clipS' (F + h) : ℝ))
    (h_V_T_strict :
      ∀ ⦃x y : ↥(Sanctions.S : Set ℝ)⦄,
        (x : ℝ) < (y : ℝ) → V_T x < V_T y) :
    0 < V_diff_at V_T F h := by
  unfold V_diff_at
  have := h_V_T_strict (x := Sanctions.clipS' F)
    (y := Sanctions.clipS' (F + h)) h_clip_lt
  linarith

end Tipping
end Sanctions

end -- noncomputable section
