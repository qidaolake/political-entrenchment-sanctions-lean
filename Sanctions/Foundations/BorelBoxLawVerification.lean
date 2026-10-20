/-
Sanctions/Foundations/BorelBoxLawVerification.lean

Law-side infinite-horizon verification for the uniform box shock under
time-dependent Borel feedback drifts.

The Feller pullback in `ClosedLoopBoxTransfer.lean` is deliberately formulated
on bounded continuous functions and therefore asks the closed-loop drift to be
continuous.  A Borel deviation need not preserve that function space.  This
file takes the complementary law-side route:

* a merely measurable drift still pushes a probability law forward;
* bounded continuous continuation values satisfy the same adjoint identity;
* pointwise Bellman inequalities integrate to Bellman inequalities on the
  probability-law state space; and
* the existing deterministic infinite-horizon telescope, applied to that law
  state space, gives discounted-payoff inequalities for arbitrary
  time-dependent Borel feedback deviations.

No new model assumption is introduced.  Measurability and feasibility are
properties of the deviations quantified over by downstream verification
theorems.
-/

import Sanctions.Foundations.ClosedLoopBoxTransfer
import Sanctions.Foundations.InfiniteHorizonVerification

open Filter MeasureTheory BoundedContinuousFunction
open scoped Topology

namespace Sanctions

noncomputable section

abbrev BoxState := ↥(Sanctions.S : Set ℝ)

/-- The state-dependent box-noise map is Borel measurable whenever its drift
is Borel measurable. -/
theorem closedLoopMap_measurable_of_measurable
    (g : BoxState → ℝ) (hg : Measurable g) :
    Measurable (closedLoopMap g) := by
  unfold closedLoopMap
  exact Sanctions.clipS'_continuous.measurable.comp
    ((hg.comp measurable_fst).add measurable_snd)

/-- The closed-loop box transfer preserves probability laws for every Borel
drift.  Continuity is unnecessary for this law-side fact. -/
theorem closedLoopBoxTransfer_isProb_of_measurable
    (g : BoxState → ℝ) (hg : Measurable g)
    (h : ℝ) (hh : 0 < h) (μ : Measure BoxState) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (closedLoopBoxTransfer g h μ) := by
  have : IsProbabilityMeasure (boxNoise h) := boxNoise_isProb h hh
  rw [closedLoopBoxTransfer]
  exact Measure.isProbabilityMeasure_map
    (closedLoopMap_measurable_of_measurable g hg).aemeasurable

/-- Integrating a bounded continuous value over one box shock equals its
moving average at the pre-noise state. -/
theorem boxNoise_integral_eq_movAvgReal
    (h : ℝ) (hh : 0 < h) (f : BoxState →ᵇ ℝ) (c : ℝ) :
    (∫ η, f (Sanctions.clipS' (c + η)) ∂(boxNoise h)) =
      Sanctions.movAvgReal h f c := by
  rw [boxNoise, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (2 * h)),
      smul_eq_mul, movAvgReal]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  have hcomp := intervalIntegral.integral_comp_add_left
    (f := fun z => f (Sanctions.clipS' z)) (a := -h) (b := h) c
  rw [hcomp, show c + -h = c - h by ring]

/-- Law-side adjoint identity for a merely Borel drift.  The continuation value
remains bounded continuous, but the pullback only needs to be measurable; it
need not lie in the bounded-continuous carrier. -/
theorem closedLoopBoxTransfer_adjoint_of_measurable
    (g : BoxState → ℝ) (hg : Measurable g)
    (h : ℝ) (hh : 0 < h)
    (μ : Measure BoxState) [IsProbabilityMeasure μ]
    (f : BoxState →ᵇ ℝ) :
    (∫ y, f y ∂(closedLoopBoxTransfer g h μ)) =
      ∫ x, Sanctions.movAvgReal h f (g x) ∂μ := by
  have hprob : IsProbabilityMeasure (boxNoise h) := boxNoise_isProb h hh
  have hGmeas : AEMeasurable (closedLoopMap g) (μ.prod (boxNoise h)) :=
    (closedLoopMap_measurable_of_measurable g hg).aemeasurable
  have hInt : Integrable (fun p => f (closedLoopMap g p))
      (μ.prod (boxNoise h)) :=
    ⟨(f.continuous.measurable.comp
        (closedLoopMap_measurable_of_measurable g hg)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := ‖f‖)
        (Filter.Eventually.of_forall
          (fun p => f.norm_coe_le_norm (closedLoopMap g p)))⟩
  rw [closedLoopBoxTransfer, integral_map hGmeas
      f.continuous.aestronglyMeasurable, integral_prod _ hInt]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (fun x => boxNoise_integral_eq_movAvgReal h hh f (g x))

/-- Probability laws on the compact political-state interval. -/
abbrev BorelBoxProbabilityLaw :=
  {μ : Measure BoxState // IsProbabilityMeasure μ}

/-- One Borel closed-loop box-noise step, packaged as a map of probability
laws. -/
noncomputable def borelBoxLawStep
    (g : BoxState → BoxState) (hg : Measurable g)
    (h : ℝ) (hh : 0 < h)
    (μ : BorelBoxProbabilityLaw) : BorelBoxProbabilityLaw := by
  letI : IsProbabilityMeasure μ.1 := μ.2
  exact ⟨closedLoopBoxTransfer (fun x => (g x).val) h μ.1,
    closedLoopBoxTransfer_isProb_of_measurable
      (fun x => (g x).val) (measurable_subtype_coe.comp hg) h hh μ.1⟩

/-- The time-indexed law transition induced by a sequence of Borel feedback
drifts. -/
noncomputable def borelBoxLawTransition
    (g : ℕ → BoxState → BoxState) (hg : ∀ n, Measurable (g n))
    (h : ℝ) (hh : 0 < h) :
    BorelBoxProbabilityLaw → ℕ → BorelBoxProbabilityLaw :=
  fun μ n => borelBoxLawStep (g n) (hg n) h hh μ

/-- Expected stage payoff under a probability law. -/
noncomputable def borelBoxLawStage
    (u : ℕ → BoxState → ℝ) :
    BorelBoxProbabilityLaw → ℕ → ℝ :=
  fun μ n => ∫ x, u n x ∂μ.1

/-- Expected continuation value under a probability law. -/
noncomputable def borelBoxLawValue
    (V : BoxState →ᵇ ℝ) :
    BorelBoxProbabilityLaw → ℝ :=
  fun μ => ∫ x, V x ∂μ.1

/-- The canonical plan uses the period-`n` Borel feedback rule in period `n`. -/
def borelBoxTimePlan :
    InfiniteHorizonVerification.MarkovPlan BorelBoxProbabilityLaw ℕ :=
  fun n _ => n

/-- The expected discounted payoff generated by a sequence of Borel feedback
drifts and measurable stage-payoff functions.  The state path in this
deterministic expression is the recursively evolving probability law. -/
noncomputable def borelBoxExpectedDiscountedPayoff
    (g : ℕ → BoxState → BoxState) (hg : ∀ n, Measurable (g n))
    (h : ℝ) (hh : 0 < h)
    (u : ℕ → BoxState → ℝ) (β : ℝ)
    (μ₀ : BorelBoxProbabilityLaw) : ℝ :=
  InfiniteHorizonVerification.discountedPayoff
    (borelBoxLawStage u) (borelBoxLawTransition g hg h hh)
    β borelBoxTimePlan μ₀

/-- A measurable function with a uniform absolute bound is integrable under a
probability law. -/
theorem integrable_probability_of_measurable_abs_le
    (μ : BorelBoxProbabilityLaw) (f : BoxState → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    Integrable f μ.1 := by
  letI : IsProbabilityMeasure μ.1 := μ.2
  exact ⟨hf.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (f := f) (C := M)
      (Filter.Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using hM x))⟩

/-- The expectation of a uniformly bounded measurable function under a
probability law has the same absolute bound. -/
theorem abs_integral_probability_le_of_abs_le
    (μ : BorelBoxProbabilityLaw) (f : BoxState → ℝ)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    |∫ x, f x ∂μ.1| ≤ M := by
  letI : IsProbabilityMeasure μ.1 := μ.2
  have h := norm_integral_le_of_norm_le_const
    (μ := μ.1) (f := f) (C := M)
    (Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using hM x))
  simpa [Real.norm_eq_abs, probReal_univ] using h

/-- **Borel law-side Bellman verification (inequality).**  If a bounded
continuous candidate value dominates current payoff plus the box-smoothed
continuation value pointwise, then every time-dependent Borel feedback
deviation has expected discounted payoff at most the candidate's expectation
under the initial law. -/
theorem borelBoxExpectedDiscountedPayoff_le_value
    (g : ℕ → BoxState → BoxState) (hg : ∀ n, Measurable (g n))
    (h : ℝ) (hh : 0 < h)
    (u : ℕ → BoxState → ℝ) (hu : ∀ n, Measurable (u n))
    (β : ℝ) (hβ : 0 ≤ β) (hβ_lt : β < 1)
    (V : BoxState →ᵇ ℝ)
    (h_bellman : ∀ n x,
      u n x + β * (Sanctions.movAvgBCF hh V) (g n x) ≤ V x)
    (M_u : ℝ) (h_u_bound : ∀ n x, |u n x| ≤ M_u)
    (μ₀ : BorelBoxProbabilityLaw) :
    borelBoxExpectedDiscountedPayoff g hg h hh u β μ₀ ≤
      borelBoxLawValue V μ₀ := by
  apply InfiniteHorizonVerification.discountedPayoff_le_value_of_uniform_bounds
    (borelBoxLawStage u) (borelBoxLawTransition g hg h hh)
    β (borelBoxLawValue V) hβ hβ_lt
    (M_u := M_u) (M_V := ‖V‖)
  · intro μ n
    letI : IsProbabilityMeasure μ.1 := μ.2
    have huInt : Integrable (u n) μ.1 :=
      integrable_probability_of_measurable_abs_le μ (u n) (hu n) M_u
        (h_u_bound n)
    have hcontMeas : Measurable
        (fun x => (Sanctions.movAvgBCF hh V) (g n x)) :=
      (Sanctions.movAvgBCF hh V).continuous.measurable.comp (hg n)
    have hcontInt : Integrable
        (fun x => (Sanctions.movAvgBCF hh V) (g n x)) μ.1 :=
      ⟨hcontMeas.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := ‖Sanctions.movAvgBCF hh V‖)
          (Filter.Eventually.of_forall
            (fun x => (Sanctions.movAvgBCF hh V).norm_coe_le_norm (g n x)))⟩
    have hVInt : Integrable (fun x => V x) μ.1 :=
      ⟨V.continuous.measurable.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := ‖V‖)
          (Filter.Eventually.of_forall (fun x => V.norm_coe_le_norm x))⟩
    rw [borelBoxLawStage, borelBoxLawTransition, borelBoxLawValue,
      borelBoxLawStep]
    rw [closedLoopBoxTransfer_adjoint_of_measurable
      (fun x => (g n x).val) (measurable_subtype_coe.comp (hg n)) h hh μ.1 V]
    change (∫ x, u n x ∂μ.1) +
      β * ∫ x, (Sanctions.movAvgBCF hh V) (g n x) ∂μ.1 ≤
        ∫ x, V x ∂μ.1
    calc
      (∫ x, u n x ∂μ.1) +
          β * ∫ x, (Sanctions.movAvgBCF hh V) (g n x) ∂μ.1 =
          ∫ x, u n x + β * (Sanctions.movAvgBCF hh V) (g n x) ∂μ.1 := by
            rw [integral_add huInt (hcontInt.const_mul β), integral_const_mul]
      _ ≤ ∫ x, V x ∂μ.1 :=
        integral_mono (huInt.add (hcontInt.const_mul β)) hVInt
          (fun x => h_bellman n x)
  · intro n
    apply abs_integral_probability_le_of_abs_le
    exact h_u_bound n
  · intro n
    apply abs_integral_probability_le_of_abs_le
    exact fun x => by
      simpa [Real.norm_eq_abs] using V.norm_coe_le_norm x

/-- Equality counterpart of the law-side verification theorem.  A Borel
feedback sequence that attains the pointwise Bellman equation realizes the
candidate value exactly in expected discounted payoff. -/
theorem borelBoxExpectedDiscountedPayoff_eq_value
    (g : ℕ → BoxState → BoxState) (hg : ∀ n, Measurable (g n))
    (h : ℝ) (hh : 0 < h)
    (u : ℕ → BoxState → ℝ) (hu : ∀ n, Measurable (u n))
    (β : ℝ) (hβ : 0 ≤ β) (hβ_lt : β < 1)
    (V : BoxState →ᵇ ℝ)
    (h_bellman : ∀ n x,
      u n x + β * (Sanctions.movAvgBCF hh V) (g n x) = V x)
    (M_u : ℝ) (h_u_bound : ∀ n x, |u n x| ≤ M_u)
    (μ₀ : BorelBoxProbabilityLaw) :
    borelBoxExpectedDiscountedPayoff g hg h hh u β μ₀ =
      borelBoxLawValue V μ₀ := by
  apply InfiniteHorizonVerification.discountedPayoff_eq_value_of_uniform_bounds
    (borelBoxLawStage u) (borelBoxLawTransition g hg h hh)
    β (borelBoxLawValue V) hβ hβ_lt borelBoxTimePlan μ₀
    (M_u := M_u) (M_V := ‖V‖)
  · intro n
    let μ := InfiniteHorizonVerification.statePath
      (borelBoxLawTransition g hg h hh) borelBoxTimePlan μ₀ n
    letI : IsProbabilityMeasure μ.1 := μ.2
    have huInt : Integrable (u n) μ.1 :=
      integrable_probability_of_measurable_abs_le μ (u n) (hu n) M_u
        (h_u_bound n)
    have hcontMeas : Measurable
        (fun x => (Sanctions.movAvgBCF hh V) (g n x)) :=
      (Sanctions.movAvgBCF hh V).continuous.measurable.comp (hg n)
    have hcontInt : Integrable
        (fun x => (Sanctions.movAvgBCF hh V) (g n x)) μ.1 :=
      ⟨hcontMeas.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := ‖Sanctions.movAvgBCF hh V‖)
          (Filter.Eventually.of_forall
            (fun x => (Sanctions.movAvgBCF hh V).norm_coe_le_norm (g n x)))⟩
    rw [InfiniteHorizonVerification.statePath_succ]
    change borelBoxLawStage u μ n +
      β * borelBoxLawValue V (borelBoxLawTransition g hg h hh μ n) =
        borelBoxLawValue V μ
    rw [borelBoxLawStage, borelBoxLawTransition, borelBoxLawValue, borelBoxLawStep]
    rw [closedLoopBoxTransfer_adjoint_of_measurable
      (fun x => (g n x).val) (measurable_subtype_coe.comp (hg n)) h hh μ.1 V]
    change (∫ x, u n x ∂μ.1) +
      β * ∫ x, (Sanctions.movAvgBCF hh V) (g n x) ∂μ.1 =
        ∫ x, V x ∂μ.1
    calc
      (∫ x, u n x ∂μ.1) +
          β * ∫ x, (Sanctions.movAvgBCF hh V) (g n x) ∂μ.1 =
          ∫ x, u n x + β * (Sanctions.movAvgBCF hh V) (g n x) ∂μ.1 := by
            rw [integral_add huInt (hcontInt.const_mul β), integral_const_mul]
      _ = ∫ x, V x ∂μ.1 := integral_congr_ae
        (Filter.Eventually.of_forall (fun x => h_bellman n x))
  · intro n
    apply abs_integral_probability_le_of_abs_le
    exact h_u_bound n
  · intro n
    apply abs_integral_probability_le_of_abs_le
    exact fun x => by
      simpa [Real.norm_eq_abs] using V.norm_coe_le_norm x

end

end Sanctions
