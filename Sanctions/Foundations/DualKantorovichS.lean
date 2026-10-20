/-
Sanctions/Foundations/DualKantorovichS.lean

**Separation of the dual Kantorovich–Rubinstein metric on the state space `↥S = [0,1]`:
`dualKR μ ν = 0 ⟹ μ = ν`.**

This is the determining-class half of the step-6 measure-side: `dualKR` is a genuine
metric on probability measures (it separates points), so the abstract
`dualKR_eq_zero_of_invariant` (uniqueness *in `d`*) upgrades to honest uniqueness
`μ = ν` of the lock-in invariant distribution.

The argument is the CDF route: two probability measures on the linearly-ordered compact
state space agree iff their cumulative distributions agree (`Measure.ext_of_Iic`), and
`μ(Iic a) = ν(Iic a)` is recovered by integrating Lipschitz *ramps* `clipS(n·(a−x)+1)`
that decrease to the indicator of `Iic a` (dominated convergence), since `dualKR = 0`
forces equal integrals of every Lipschitz test function. The ramps reuse the project's
`clipS` clamp.
-/

import Sanctions.Foundations.DualKantorovich
import Sanctions.Domain.UnitIntervalProjection
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory BoundedContinuousFunction Filter Topology

namespace Sanctions

/-- **Lipschitz ramp** at `a` with slope `n`: `clipS(n·(a−x)+1)`, valued in `[0,1]`,
equal to `1` for `x ≤ a` and decaying to `0` just past `a`. -/
noncomputable def rampBCF (a : ↥(Sanctions.S)) (n : ℕ) : ↥(Sanctions.S) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Sanctions.clipS ((n : ℝ) * (a.val - x.val) + 1),
     Sanctions.clipS_continuous.comp (by fun_prop)⟩

@[simp] theorem rampBCF_apply (a : ↥(Sanctions.S)) (n : ℕ) (x : ↥(Sanctions.S)) :
    rampBCF a n x = Sanctions.clipS ((n : ℝ) * (a.val - x.val) + 1) := rfl

theorem rampBCF_lipschitz (a : ↥(Sanctions.S)) (n : ℕ) : LipschitzWith n (rampBCF a n) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [rampBCF_apply, rampBCF_apply, Real.dist_eq]
  have h := Sanctions.clipS_lipschitz_abs ((n:ℝ)*(a.val - x.val)+1) ((n:ℝ)*(a.val - y.val)+1)
  have heq : |((n:ℝ)*(a.val - x.val)+1) - ((n:ℝ)*(a.val - y.val)+1)| = (n:ℝ) * dist x y := by
    rw [show ((n:ℝ)*(a.val - x.val)+1) - ((n:ℝ)*(a.val - y.val)+1) = (n:ℝ)*(y.val - x.val) from by ring,
        abs_mul, Nat.abs_cast, Subtype.dist_eq, Real.dist_eq, abs_sub_comm y.val x.val]
  rw [heq] at h; simpa [NNReal.coe_natCast] using h

theorem rampBCF_mem_unitInterval (a : ↥(Sanctions.S)) (n : ℕ) (x : ↥(Sanctions.S)) :
    rampBCF a n x ∈ Set.Icc (0:ℝ) 1 := by
  rw [rampBCF_apply]; exact Sanctions.clipS_mem _

theorem clipS_eq_one_of_one_le {u : ℝ} (h : 1 ≤ u) : Sanctions.clipS u = 1 := by
  unfold Sanctions.clipS; rw [min_eq_left h, max_eq_right (by norm_num)]

theorem clipS_eq_zero_of_le_zero {u : ℝ} (h : u ≤ 0) : Sanctions.clipS u = 0 := by
  unfold Sanctions.clipS
  rcases le_total 1 u with h1 | h1
  · linarith
  · rw [min_eq_right h1, max_eq_left h]

/-- The ramps converge pointwise to the indicator of `Iic a`. -/
theorem rampBCF_tendsto (a x : ↥(Sanctions.S)) :
    Filter.Tendsto (fun n => rampBCF a n x) Filter.atTop
      (nhds (Set.indicator (Set.Iic a) (1 : ↥(Sanctions.S) → ℝ) x)) := by
  by_cases hx : x ≤ a
  · rw [Set.indicator_of_mem (show x ∈ Set.Iic a from hx), Pi.one_apply]
    apply tendsto_const_nhds.congr
    intro n
    rw [rampBCF_apply, clipS_eq_one_of_one_le]
    have hle : (0:ℝ) ≤ a.val - x.val := by
      have : x.val ≤ a.val := hx; linarith
    nlinarith [hle, Nat.cast_nonneg (α := ℝ) n]
  · rw [Set.indicator_of_notMem (show x ∉ Set.Iic a from hx)]
    have hpos : 0 < x.val - a.val := by
      have : a.val < x.val := Subtype.coe_lt_coe.mpr (not_le.mp hx)
      linarith
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (x.val - a.val))
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hle : (n:ℝ) * (a.val - x.val) + 1 ≤ 0 := by
      have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have h1 : 1 / (x.val - a.val) ≤ (n:ℝ) := le_trans hN hNn
      have h2 : 1 ≤ (n:ℝ) * (x.val - a.val) := by
        rw [div_le_iff₀ hpos] at h1; linarith
      nlinarith [h2]
    show (0:ℝ) = rampBCF a n x
    rw [rampBCF_apply, clipS_eq_zero_of_le_zero hle]

/-- **Determining class.** Two probability measures on `↥S` that integrate every
1-Lipschitz test function identically are equal (CDF route via `ext_of_Iic` and the
ramp dominated-convergence). -/
theorem eq_of_forall_lipschitz_integral_eq
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hL : ∀ f : ↥(Sanctions.S) →ᵇ ℝ, LipschitzWith 1 f → (∫ x, f x ∂μ) = ∫ x, f x ∂ν) :
    μ = ν := by
  have hLK : ∀ (K : ℕ) (f : ↥(Sanctions.S) →ᵇ ℝ), LipschitzWith K f →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
    intro K f hf
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0
      obtain ⟨x₀⟩ := (inferInstance : Nonempty ↥(Sanctions.S))
      have hconst' : ∀ x, f x = f x₀ := fun x =>
        dist_le_zero.mp (by simpa using hf.dist_le_mul x x₀)
      rw [integral_congr_ae (ae_of_all μ hconst'), integral_congr_ae (ae_of_all ν hconst')]
      simp
    · have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
      have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKR
      have hg1 : LipschitzWith 1 ((K:ℝ)⁻¹ • f) := by
        rw [lipschitzWith_iff_dist_le_mul]
        intro x y
        have hb : dist (f x) (f y) ≤ (K:ℝ) * dist x y := by
          have := hf.dist_le_mul x y; rwa [NNReal.coe_natCast] at this
        have hd : dist (((K:ℝ)⁻¹ • f) x) (((K:ℝ)⁻¹ • f) y) = (K:ℝ)⁻¹ * dist (f x) (f y) := by
          simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
              abs_of_pos (by positivity : (0:ℝ) < (K:ℝ)⁻¹)]
        rw [hd, NNReal.coe_one, one_mul]
        calc (K:ℝ)⁻¹ * dist (f x) (f y) ≤ (K:ℝ)⁻¹ * ((K:ℝ) * dist x y) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
      have heq := hL _ hg1
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul] at heq
      rw [integral_const_mul, integral_const_mul] at heq
      exact mul_left_cancel₀ (by positivity : (K:ℝ)⁻¹ ≠ 0) heq
  apply Measure.ext_of_Iic
  intro a
  have heq_n : ∀ n, (∫ x, rampBCF a n x ∂μ) = ∫ x, rampBCF a n x ∂ν :=
    fun n => hLK n (rampBCF a n) (rampBCF_lipschitz a n)
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖rampBCF a n x‖ ≤ 1 := fun n =>
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rampBCF_mem_unitInterval a n x).1]
      exact (rampBCF_mem_unitInterval a n x).2
  have hboundν : ∀ n, ∀ᵐ x ∂ν, ‖rampBCF a n x‖ ≤ 1 := fun n =>
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rampBCF_mem_unitInterval a n x).1]
      exact (rampBCF_mem_unitInterval a n x).2
  have htμ := tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => (rampBCF a n).continuous.aestronglyMeasurable) (integrable_const 1) hbound
    (Filter.Eventually.of_forall (rampBCF_tendsto a))
  have htν := tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => (rampBCF a n).continuous.aestronglyMeasurable) (integrable_const 1) hboundν
    (Filter.Eventually.of_forall (rampBCF_tendsto a))
  rw [integral_indicator_one measurableSet_Iic] at htμ htν
  have hlim : μ.real (Set.Iic a) = ν.real (Set.Iic a) := by
    have h' : Tendsto (fun n => ∫ x, rampBCF a n x ∂ν) atTop (𝓝 (μ.real (Set.Iic a))) := by
      simpa only [heq_n] using htμ
    exact tendsto_nhds_unique h' htν
  rw [Measure.real, Measure.real] at hlim
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp hlim

/-- **Separation: `dualKR = 0 ⟹ μ = ν`** on the state space. Combines the easy half
(`dualKR = 0` forces equal Lipschitz integrals) with the determining class above. Thus
`dualKR` is a genuine metric on `ProbabilityMeasure ↥S`. -/
theorem eq_of_dualKR_eq_zero
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : dualKR μ ν = 0) :
    μ = ν :=
  eq_of_forall_lipschitz_integral_eq μ ν (forall_lipschitz_integral_eq_of_dualKR_eq_zero h)

/-- **Uniqueness of the invariant distribution, as `μ = ν`.** Specialisation of
`dualKR_eq_zero_of_invariant` to the state space, upgraded through separation: with
`0 < c < 1`, any two `S`-invariant probability measures are *equal*. -/
theorem eq_of_invariant
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : (↥(Sanctions.S) →ᵇ ℝ) → (↥(Sanctions.S) →ᵇ ℝ)) {c : ℝ} (hcpos : 0 < c) (hc1 : c < 1)
    (hS : ∀ f : ↥(Sanctions.S) →ᵇ ℝ, LipschitzWith 1 f → LipschitzWith (Real.toNNReal c) (S f))
    (hInvμ : ∀ f : ↥(Sanctions.S) →ᵇ ℝ, (∫ x, f x ∂μ) = ∫ x, (S f) x ∂μ)
    (hInvν : ∀ f : ↥(Sanctions.S) →ᵇ ℝ, (∫ x, f x ∂ν) = ∫ x, (S f) x ∂ν) :
    μ = ν :=
  eq_of_dualKR_eq_zero μ ν (dualKR_eq_zero_of_invariant μ ν S hcpos hc1 hS hInvμ hInvν)

end Sanctions
