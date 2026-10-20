/-
Sanctions/Foundations/BoxTransfer.lean

**The box transfer operator `T*` as a pushforward of the product, and its
adjoint identity — discharging the dual-Kantorovich contraction hypothesis
concretely.**

The dual-Kantorovich machinery (`Foundations/DualKantorovich.lean`,
`DualKantorovichS.lean`, `BoxPullback.lean`) proves: if the forward operator
`T*` has adjoint `S` on test functions (`∫ f d(T*μ) = ∫ (S f) dμ`) and `S`
maps 1-Lipschitz to `(1−δ)`-Lipschitz, then `T*` is a `(1−δ)`-contraction in
`dualKR`, hence (with separation) has at most one invariant law with geometric
convergence. `boxPullback_lipschitz` already supplies the `(1−δ)`-Lipschitz
half. The **only** missing piece was the construction of `T*` together with the
adjoint identity, previously taken as a hypothesis (`hAdjμ`/`hAdjν`).

This file constructs it without any Bochner `integral_bind` (which mathlib lacks):
the box transfer operator is the law of `clipS'((1−δ)X + δ + η)` for `X ~ μ` and
independent uniform box noise `η ~ boxNoise h`, i.e. the **pushforward of the
product** `μ ⊗ boxNoise h` under the closed-loop-plus-noise map. The adjoint
identity then follows from `integral_map` + the Bochner Fubini theorem
`integral_prod` (both present in mathlib), with the inner `η`-integral matching
`boxPullback` by a translation change of variables. No new assumption: this is a
`def` plus theorems from existing primitives that *discharge* the previously
hypothesized adjoint. Uniqueness + geometric convergence are unconditional on
the adjoint, and existence of the invariant law is now also **constructed**
in-repo (`Foundations/KrylovBogolyubov.lean`, Cesàro-average fixed point on the
compact space of probability laws — mathlib has no Krylov–Bogolyubov/Schauder,
so the assembly lemma is proved there): see
`boxTransfer_existsUnique_invariant_attracting`.
-/

import Sanctions.Foundations.BoxPullback
import Sanctions.Foundations.DualKantorovichS
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory BoundedContinuousFunction

namespace Sanctions

noncomputable section

/-- The uniform box-noise probability measure on `[−h, h]`:
`(1/2h) · volume.restrict [−h, h]` (total mass `1` for `h > 0`). -/
noncomputable def boxNoise (h : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * h)) • (volume.restrict (Set.Icc (-h) h))

instance boxNoise_isProb (h : ℝ) (hh : 0 < h) : IsProbabilityMeasure (boxNoise h) := by
  have h2h : (0 : ℝ) < 2 * h := by linarith
  constructor
  rw [boxNoise, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Icc,
      show h - -h = 2 * h by ring, ← ENNReal.ofReal_mul (by positivity), one_div,
      inv_mul_cancel₀ (ne_of_gt h2h), ENNReal.ofReal_one]

/-- The box closed-loop-plus-noise map `↥S × ℝ → ↥S`:
`(x, η) ↦ clipS'((1−δ)·x + δ + η)`. -/
noncomputable def boxLoopMap (δ : ℝ) : ↥(Sanctions.S) × ℝ → ↥(Sanctions.S) :=
  fun p => Sanctions.clipS' ((1 - δ) * p.1.val + δ + p.2)

theorem boxLoopMap_continuous (δ : ℝ) : Continuous (boxLoopMap δ) := by
  unfold boxLoopMap
  exact Sanctions.clipS'_continuous.comp (by fun_prop)

/-- **Box transfer operator** `T*μ`: the law of `clipS'((1−δ)X + δ + η)` when
`X ~ μ` and the noise `η ~ boxNoise h` are independent, realised as the
pushforward of the product `μ ⊗ boxNoise h`. -/
noncomputable def boxTransfer (δ h : ℝ) (μ : Measure ↥(Sanctions.S)) :
    Measure ↥(Sanctions.S) :=
  Measure.map (boxLoopMap δ) (μ.prod (boxNoise h))

/-- The transfer operator preserves probability measures. -/
instance boxTransfer_isProb (δ h : ℝ) (hh : 0 < h) (μ : Measure ↥(Sanctions.S))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (boxTransfer δ h μ) := by
  have : IsProbabilityMeasure (boxNoise h) := boxNoise_isProb h hh
  rw [boxTransfer]
  exact Measure.isProbabilityMeasure_map (boxLoopMap_continuous δ).measurable.aemeasurable

/-- **Inner noise integral = the smear.** Integrating a test function `f` along
the closed loop with box noise equals the moving-average pullback
`boxPullback`, by a translation change of variables. -/
theorem boxNoise_integral_eq_boxPullback (δ h : ℝ) (hh : 0 < h)
    (f : ↥(Sanctions.S) →ᵇ ℝ) (x : ↥(Sanctions.S)) :
    (∫ η, f (Sanctions.clipS' ((1 - δ) * x.val + δ + η)) ∂(boxNoise h))
      = boxPullback δ h hh f x := by
  rw [boxPullback_apply]
  set c := (1 - δ) * x.val + δ with hc
  rw [boxNoise, integral_smul_measure, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (2 * h)),
      smul_eq_mul, movAvgReal]
  congr 1
  -- ∫ η in Icc(-h,h), f(clipS'(c+η)) = ∫ z in (c-h)..(c+h), f(clipS' z)
  rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  have hcomp := intervalIntegral.integral_comp_add_left
    (f := fun z => f (Sanctions.clipS' z)) (a := -h) (b := h) c
  rw [hcomp, show c + -h = c - h by ring]

/-- **The box transfer-operator adjoint identity.** For a 1-Lipschitz (indeed
any bounded-continuous) test function `f`, integrating `f` against the
push-forward `T*μ` equals integrating the smear `boxPullback f` against `μ`.
This is the concrete discharge of the `hAdjμ` hypothesis of
`dualKR_le_of_adjoint_lipschitz`. -/
theorem boxTransfer_adjoint (δ h : ℝ) (hh : 0 < h)
    (μ : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ]
    (f : ↥(Sanctions.S) →ᵇ ℝ) :
    (∫ y, f y ∂(boxTransfer δ h μ)) = ∫ x, boxPullback δ h hh f x ∂μ := by
  have hprob : IsProbabilityMeasure (boxNoise h) := boxNoise_isProb h hh
  have hGmeas : AEMeasurable (boxLoopMap δ) (μ.prod (boxNoise h)) :=
    (boxLoopMap_continuous δ).measurable.aemeasurable
  have hInt : Integrable (fun p => f (boxLoopMap δ p)) (μ.prod (boxNoise h)) :=
    ⟨(f.continuous.comp (boxLoopMap_continuous δ)).aestronglyMeasurable,
     HasFiniteIntegral.of_bounded (C := ‖f‖)
       (Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm (boxLoopMap δ p)))⟩
  rw [boxTransfer, integral_map hGmeas f.continuous.aestronglyMeasurable,
      integral_prod _ hInt]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact boxNoise_integral_eq_boxPullback δ h hh f x

/-- **The box transfer operator is a `(1−δ)`-contraction in `dualKR`.** Concrete
discharge of `dualKR_le_of_adjoint_lipschitz_of_nonneg` at the box operator: its
adjoint is `boxPullback`, which maps 1-Lipschitz test functions to `(1−δ)`-Lipschitz
ones (`boxPullback_lipschitz`), and the adjoint identity is `boxTransfer_adjoint`.

Affine-restricted: the drift is the constant-sanction affine law `(1−δ)·x + δ`
(the general-drift form is `closedLoopBoxTransfer_dualKR_contraction`). Needs only
`δ ≤ 1` (round BH-2, item BH2.11; was `δ < 1`): the dual contraction now accepts
the factor `1 − δ = 0`, the case where the next state forgets the current one. -/
theorem boxTransfer_dualKR_contraction (δ h : ℝ) (hh : 0 < h) (hδ1 : δ ≤ 1)
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dualKR (boxTransfer δ h μ) (boxTransfer δ h ν) ≤ (1 - δ) * dualKR μ ν :=
  dualKR_le_of_adjoint_lipschitz_of_nonneg μ ν (boxTransfer δ h μ) (boxTransfer δ h ν)
    (boxPullback δ h hh) (by linarith)
    (fun f hf => boxPullback_lipschitz δ h hh hδ1 f hf)
    (boxTransfer_adjoint δ h hh μ) (boxTransfer_adjoint δ h hh ν)

/-- **Uniqueness of the invariant law.** Two `boxTransfer`-invariant
probability measures coincide — the contraction has at most one fixed point.
(Existence is constructed in `Foundations/KrylovBogolyubov.lean`:
`boxTransfer_exists_invariant`; the combined headline is
`boxTransfer_existsUnique_invariant_attracting`.)

Affine-restricted (constant-sanction affine drift). Needs only `0 < δ ≤ 1`
(round BH-2, item BH2.11; was `δ < 1`), through
`dualKR_eq_zero_of_invariant_of_nonneg` at factor `1 − δ ∈ [0, 1)`. -/
theorem boxTransfer_unique_invariant (δ h : ℝ) (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : boxTransfer δ h μ = μ) (hν : boxTransfer δ h ν = ν) :
    μ = ν := by
  apply eq_of_dualKR_eq_zero
  refine dualKR_eq_zero_of_invariant_of_nonneg μ ν (boxPullback δ h hh) (c := 1 - δ)
    (by linarith) (by linarith)
    (fun f hf => boxPullback_lipschitz δ h hh hδ1 f hf) ?_ ?_
  · intro f; rw [← boxTransfer_adjoint δ h hh μ f, hμ]
  · intro f; rw [← boxTransfer_adjoint δ h hh ν f, hν]

/-- **Geometric convergence to an invariant law.** If `seq` is generated by
iterating `boxTransfer` and `lam` is invariant, the dual distance to `lam`
contracts as `(1−δ)ⁿ`. With `δ ∈ (0,1]` this gives `dualKR (seq n) lam → 0`.

Affine-restricted (constant-sanction affine drift). Needs only `δ ≤ 1` (round
BH-2, item BH2.11; was `δ < 1`). -/
theorem boxTransfer_dualKR_geometric (δ h : ℝ) (hh : 0 < h) (hδ1 : δ ≤ 1)
    (seq : ℕ → Measure ↥(Sanctions.S)) (lam : Measure ↥(Sanctions.S))
    (hseq : ∀ n, IsProbabilityMeasure (seq n)) [IsProbabilityMeasure lam]
    (hstep : ∀ n, seq (n + 1) = boxTransfer δ h (seq n))
    (hlam : boxTransfer δ h lam = lam) :
    ∀ n, dualKR (seq n) lam ≤ (1 - δ) ^ n * dualKR (seq 0) lam := by
  apply dualKR_geometric seq lam (show (0 : ℝ) ≤ 1 - δ by linarith)
  intro n
  haveI := hseq n
  have hc := boxTransfer_dualKR_contraction δ h hh hδ1 (seq n) lam
  rw [hlam] at hc
  rw [hstep n]
  exact hc

end

end Sanctions
