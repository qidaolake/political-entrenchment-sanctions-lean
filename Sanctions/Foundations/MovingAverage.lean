/-
Sanctions/Foundations/MovingAverage.lean

**The moving-average (uniform-kernel) smoothing operator and its estimates.**

The He–Sun atomless shock, taken with the *uniform* density on `[-h,h]`, gives the
moving-average smoothing operator on continuation values,

  `movAvg h U (y) = (1/2h) ∫_{y-h}^{y+h} U(clipS' z) dz`.

This file proves, from elementary `intervalIntegral` estimates, the three
properties the interior shocked-existence argument needs:

* **nonexpansive** in sup-norm (`movAvg_dist_le`): averaging is a contraction;
* **state-Lipschitz** with constant `‖U‖/h` (`movAvg_lipschitz`): the window-shift
  bound `|∫_{y-h}^{y+h} g - ∫_{y'-h}^{y'+h} g| ≤ 2‖g‖_∞|y-y'|` — this is the
  mollifier-Lipschitz estimate that upgrades the argmaxes from Hölder-½ to
  Lipschitz, discharged here from a concrete kernel;
* **linear** in the value (`movAvg_sub`): needed so the objective *difference*
  inherits a Lipschitz constant `∝ ‖V-W‖` (not `‖V‖+‖W‖`).

Pure measure theory; no `Params`. Used by the interior shocked-existence
development to instantiate the `smear` regularity from a concrete shock kernel.
-/

import Sanctions.Domain.UnitIntervalProjection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open MeasureTheory intervalIntegral BoundedContinuousFunction

namespace Sanctions

noncomputable section

/-- Strong concavity is preserved by precomposition with a real affine map;
the modulus is multiplied by the square of the slope. -/
theorem strongConcaveOn_comp_affine_real
    {s t : Set ℝ} {m c d : ℝ} {f : ℝ → ℝ}
    (hs : Convex ℝ s) (hf : StrongConcaveOn t m f)
    (hmap : Set.MapsTo (fun x : ℝ => c + d * x) s t) :
    StrongConcaveOn s (m * d ^ 2) (fun x => f (c + d * x)) := by
  unfold StrongConcaveOn UniformConcaveOn at hf ⊢
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 (hmap hx) (hmap hy) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have haff : c + d * (a * x + b * y) =
      a * (c + d * x) + b * (c + d * y) := by
    calc
      c + d * (a * x + b * y) =
          (a + b) * c + d * (a * x + b * y) := by rw [hab]; ring
      _ = a * (c + d * x) + b * (c + d * y) := by ring
  have hnorm :
      ‖c + d * x - (c + d * y)‖ ^ 2 = d ^ 2 * ‖x - y‖ ^ 2 := by
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  rw [haff]
  rw [hnorm] at h
  convert h using 1 <;> ring

/-- Multiplying a real-valued objective by a nonnegative scalar multiplies
its strong-concavity modulus by the same scalar. -/
theorem strongConcaveOn_const_mul_real
    {s : Set ℝ} {m c : ℝ} {f : ℝ → ℝ}
    (hc : 0 ≤ c) (hf : StrongConcaveOn s m f) :
    StrongConcaveOn s (c * m) (fun x => c * f x) := by
  unfold StrongConcaveOn UniformConcaveOn at hf ⊢
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
  simp only [smul_eq_mul] at h ⊢
  convert h using 1 <;> ring

/-- The sum of two strongly concave real-valued objectives has the sum of
their moduli.  Negative moduli are allowed, so this also combines a concave
stage payoff with a semiconcave continuation. -/
theorem strongConcaveOn_add_real
    {s : Set ℝ} {m n : ℝ} {f g : ℝ → ℝ}
    (hf : StrongConcaveOn s m f) (hg : StrongConcaveOn s n g) :
    StrongConcaveOn s (m + n) (fun x => f x + g x) := by
  unfold StrongConcaveOn at hf hg ⊢
  have h := hf.add hg
  convert h using 1
  funext r
  simp only [Pi.add_apply]
  ring

/-- Strong concavity depends only on the objective's values on its domain. -/
theorem strongConcaveOn_congr_real
    {s : Set ℝ} {m : ℝ} {f g : ℝ → ℝ}
    (hf : StrongConcaveOn s m f) (hfg : Set.EqOn f g s) :
    StrongConcaveOn s m g := by
  unfold StrongConcaveOn UniformConcaveOn at hf ⊢
  refine ⟨hf.1, ?_⟩
  intro x hx y hy u v hu hv huv
  have hm : u • x + v • y ∈ s := hf.1 hx hy hu hv huv
  rw [← hfg hx, ← hfg hy, ← hfg hm]
  exact hf.2 hx hy hu hv huv

/-- **Window-shift bound.** For continuous `g` bounded by `B`, the moving window
integral `∫_{y-h}^{y+h} g` moves by at most `2B|y-y'|`. -/
theorem window_shift_bound
    (g : ℝ → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ z, |g z| ≤ B)
    (h y y' : ℝ) :
    |(∫ z in (y - h)..(y + h), g z) - (∫ z in (y' - h)..(y' + h), g z)|
      ≤ 2 * B * |y - y'| := by
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hg.intervalIntegrable a b
  have hrw : (∫ z in (y - h)..(y + h), g z) - (∫ z in (y' - h)..(y' + h), g z)
      = (∫ z in (y - h)..(y' - h), g z) - (∫ z in (y + h)..(y' + h), g z) := by
    rw [← integral_add_adjacent_intervals (a := y - h) (b := y' - h) (c := y + h)
          (hgi _ _) (hgi _ _),
        ← integral_add_adjacent_intervals (a := y' - h) (b := y + h) (c := y' + h)
          (hgi _ _) (hgi _ _)]
    ring
  rw [hrw]
  have hb1 : |∫ z in (y - h)..(y' - h), g z| ≤ B * |y - y'| := by
    have hc := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := y - h) (b := y' - h) (C := B) (f := g)
      (fun z _ => by rw [Real.norm_eq_abs]; exact hB z)
    rw [Real.norm_eq_abs] at hc
    calc |∫ z in (y - h)..(y' - h), g z| ≤ B * |(y' - h) - (y - h)| := hc
      _ = B * |y - y'| := by rw [show (y' - h) - (y - h) = -(y - y') from by ring, abs_neg]
  have hb2 : |∫ z in (y + h)..(y' + h), g z| ≤ B * |y - y'| := by
    have hc := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := y + h) (b := y' + h) (C := B) (f := g)
      (fun z _ => by rw [Real.norm_eq_abs]; exact hB z)
    rw [Real.norm_eq_abs] at hc
    calc |∫ z in (y + h)..(y' + h), g z| ≤ B * |(y' + h) - (y + h)| := hc
      _ = B * |y - y'| := by rw [show (y' + h) - (y + h) = -(y - y') from by ring, abs_neg]
  calc |(∫ z in (y - h)..(y' - h), g z) - (∫ z in (y + h)..(y' + h), g z)|
      ≤ |∫ z in (y - h)..(y' - h), g z| + |∫ z in (y + h)..(y' + h), g z| := abs_sub _ _
    _ ≤ B * |y - y'| + B * |y - y'| := add_le_add hb1 hb2
    _ = 2 * B * |y - y'| := by ring

/-- The moving-average smoothing of a Sender value `U`, as a function `ℝ → ℝ`. -/
noncomputable def movAvgReal (h : ℝ) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (y : ℝ) : ℝ :=
  (1 / (2 * h)) * ∫ z in (y - h)..(y + h), U (Sanctions.clipS' z)

/-- `z ↦ U(clipS' z)` is continuous and bounded by `‖U‖`. -/
theorem clipComp_cont (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    Continuous (fun z => U (Sanctions.clipS' z)) :=
  U.continuous.comp Sanctions.clipS'_continuous

theorem clipComp_bdd (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (z : ℝ) :
    |U (Sanctions.clipS' z)| ≤ ‖U‖ := by
  rw [← Real.norm_eq_abs]; exact U.norm_coe_le_norm _

/-- **A full-width box average is affine on the physical state interval.**
For half-width `1`, the moving window at `y ∈ [0,1]` contains the whole physical
interval. Its two remaining tails are clipped to the endpoint values, so the
dependence on `y` is exactly affine. -/
theorem movAvgReal_one_eq_on_S (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    movAvgReal 1 U y =
      (1 / 2) * ((1 - y) * U (clipS' 0) +
        (∫ z in (0 : ℝ)..1, U (clipS' z)) + y * U (clipS' 1)) := by
  let g : ℝ → ℝ := fun z => U (clipS' z)
  have hg : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => (clipComp_cont U).intervalIntegrable a b
  have hleft : (∫ z in (y - 1)..0, g z) = (1 - y) * g 0 := by
    have horder : y - 1 ≤ 0 := by linarith [hy.2]
    calc
      (∫ z in (y - 1)..0, g z) = ∫ _z in (y - 1)..0, g 0 := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le horder] at hz
        dsimp only [g]
        congr 1
        apply Subtype.ext
        simp only [clipS', clipS]
        rw [min_eq_right (by linarith [hz.2] : z ≤ 1), max_eq_left hz.2]
        norm_num
      _ = (1 - y) * g 0 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hright : (∫ z in (1 : ℝ)..(y + 1), g z) = y * g 1 := by
    have horder : (1 : ℝ) ≤ y + 1 := by linarith [hy.1]
    calc
      (∫ z in (1 : ℝ)..(y + 1), g z) = ∫ _z in (1 : ℝ)..(y + 1), g 1 := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [Set.uIcc_of_le horder] at hz
        dsimp only [g]
        congr 1
        apply Subtype.ext
        simp only [clipS', clipS]
        rw [min_eq_left hz.1]
        norm_num
      _ = y * g 1 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hsplit :
      (∫ z in (y - 1)..(y + 1), g z) =
        (∫ z in (y - 1)..0, g z) + (∫ z in (0 : ℝ)..1, g z) +
          (∫ z in (1 : ℝ)..(y + 1), g z) := by
    have h01 := intervalIntegral.integral_add_adjacent_intervals
      (hg (y - 1) 0) (hg 0 1)
    have h1y := intervalIntegral.integral_add_adjacent_intervals
      (hg (y - 1) 1) (hg 1 (y + 1))
    calc
      (∫ z in (y - 1)..(y + 1), g z) =
          (∫ z in (y - 1)..1, g z) + (∫ z in (1 : ℝ)..(y + 1), g z) := h1y.symm
      _ = ((∫ z in (y - 1)..0, g z) + (∫ z in (0 : ℝ)..1, g z)) +
          (∫ z in (1 : ℝ)..(y + 1), g z) := by rw [h01]
  unfold movAvgReal
  change (1 / (2 * 1)) * (∫ z in (y - 1)..(y + 1), g z) = _
  rw [hsplit, hleft, hright]
  dsimp only [g]
  ring

/-- **State-Lipschitz: the moving average has Lipschitz constant `‖U‖/h`.** This
is the mollifier-Lipschitz estimate, from a concrete (uniform) kernel. -/
theorem movAvg_lipschitz {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (y y' : ℝ) :
    |movAvgReal h U y - movAvgReal h U y'| ≤ (‖U‖ / h) * |y - y'| := by
  unfold movAvgReal
  rw [← mul_sub, abs_mul]
  have hwin := window_shift_bound (fun z => U (Sanctions.clipS' z))
    (clipComp_cont U) (clipComp_bdd U) h y y'
  have h2h : (0 : ℝ) < 2 * h := by linarith
  have habs : |1 / (2 * h)| = 1 / (2 * h) := by
    rw [abs_of_pos]; positivity
  rw [habs]
  calc (1 / (2 * h)) *
        |(∫ z in (y - h)..(y + h), U (Sanctions.clipS' z))
          - ∫ z in (y' - h)..(y' + h), U (Sanctions.clipS' z)|
      ≤ (1 / (2 * h)) * (2 * ‖U‖ * |y - y'|) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
    _ = (‖U‖ / h) * |y - y'| := by field_simp

/-- **The moving average PRESERVES a Lipschitz constant** — as opposed to the
`‖U‖/h` *creation* bound `movAvg_lipschitz`. If `U` (read through `clipS'`) is
`K`-Lipschitz on `↥S`, then `movAvgReal h U` is `K`-Lipschitz on `ℝ` with the
**same** constant `K`, independent of the window width `h`. A window
change-of-variables turns the shifted-window difference into a single integral of
the translate-difference of the integrand, bounded pointwise by `K·|y−y'|` (since
`clipS'` is 1-Lipschitz and `U` is `K`-Lipschitz). This is the estimate the shocked
single-crossing gate needs: the smear keeps the equilibrium value's intrinsic
Lipschitz constant, so the strong-rally margin `β_S·K·δ < m` carries over unchanged
under the atomless shock. -/
theorem movAvgReal_valueLipschitz {h : ℝ} (hh : 0 < h)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hUK : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ), |U z₂ - U z₁| ≤ K * dist z₁ z₂)
    (y y' : ℝ) :
    |movAvgReal h U y - movAvgReal h U y'| ≤ K * |y - y'| := by
  have hbound : ∀ z : ℝ,
      |U (Sanctions.clipS' z) - U (Sanctions.clipS' (z + (y' - y)))| ≤ K * |y - y'| := by
    intro z
    have h1 := hUK (Sanctions.clipS' (z + (y' - y))) (Sanctions.clipS' z)
    have h2 : dist (Sanctions.clipS' (z + (y' - y))) (Sanctions.clipS' z) ≤ |y - y'| := by
      have hcl := Sanctions.clipS'_lipschitz_dist (z + (y' - y)) z
      have he : |(z + (y' - y)) - z| = |y - y'| := by
        rw [show (z + (y' - y)) - z = -(y - y') from by ring, abs_neg]
      calc dist (Sanctions.clipS' (z + (y' - y))) (Sanctions.clipS' z)
          ≤ |(z + (y' - y)) - z| := hcl
        _ = |y - y'| := he
    calc |U (Sanctions.clipS' z) - U (Sanctions.clipS' (z + (y' - y)))|
        ≤ K * dist (Sanctions.clipS' (z + (y' - y))) (Sanctions.clipS' z) := h1
      _ ≤ K * |y - y'| := mul_le_mul_of_nonneg_left h2 hK
  have hcov : (∫ z in (y' - h)..(y' + h), U (Sanctions.clipS' z))
      = ∫ z in (y - h)..(y + h), U (Sanctions.clipS' (z + (y' - y))) := by
    rw [intervalIntegral.integral_comp_add_right
          (fun z => U (Sanctions.clipS' z)) (y' - y)]
    congr 1 <;> ring
  have hcont2 : Continuous (fun z : ℝ => U (Sanctions.clipS' (z + (y' - y)))) :=
    (U.continuous.comp Sanctions.clipS'_continuous).comp (continuous_id.add continuous_const)
  have hint1 : IntervalIntegrable (fun z : ℝ => U (Sanctions.clipS' z))
      MeasureTheory.volume (y - h) (y + h) := (clipComp_cont U).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun z : ℝ => U (Sanctions.clipS' (z + (y' - y))))
      MeasureTheory.volume (y - h) (y + h) := hcont2.intervalIntegrable _ _
  unfold movAvgReal
  rw [← mul_sub, hcov, ← intervalIntegral.integral_sub hint1 hint2, abs_mul]
  have h2h : (0 : ℝ) < 2 * h := by linarith
  have habs : |1 / (2 * h)| = 1 / (2 * h) := by rw [abs_of_pos]; positivity
  rw [habs]
  have hc := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y - h) (b := y + h) (C := K * |y - y'|)
    (f := fun z => U (Sanctions.clipS' z) - U (Sanctions.clipS' (z + (y' - y))))
    (fun z _ => by rw [Real.norm_eq_abs]; exact hbound z)
  rw [Real.norm_eq_abs] at hc
  calc (1 / (2 * h)) * |∫ z in (y - h)..(y + h),
          (U (Sanctions.clipS' z) - U (Sanctions.clipS' (z + (y' - y))))|
      ≤ (1 / (2 * h)) * (K * |y - y'| * |(y + h) - (y - h)|) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = K * |y - y'| := by
        rw [show (y + h) - (y - h) = 2 * h from by ring, abs_of_pos h2h]
        field_simp

/-- **The moving average PRESERVES monotonicity.** If the base value `U` is
non-decreasing on `↥S`, so is its box moving average `movAvgReal h U` on all of
`ℝ` — translating the averaging window upward translates the integrand, and
`clipS'` is monotone, so the translated integrand dominates pointwise.
Window-width independent (any `h > 0`). Companion of `movAvgReal_valueLipschitz`:
that lemma preserves the Lipschitz constant, this one preserves the order. -/
theorem movAvgReal_mono {h : ℝ} (hh : 0 < h)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hU_mono : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ), z₁ ≤ z₂ → U z₁ ≤ U z₂)
    {y y' : ℝ} (hyy : y ≤ y') :
    movAvgReal h U y ≤ movAvgReal h U y' := by
  have hcov : (∫ z in (y' - h)..(y' + h), U (Sanctions.clipS' z))
      = ∫ z in (y - h)..(y + h), U (Sanctions.clipS' (z + (y' - y))) := by
    rw [intervalIntegral.integral_comp_add_right
          (fun z => U (Sanctions.clipS' z)) (y' - y)]
    congr 1 <;> ring
  have hcont2 : Continuous (fun z : ℝ => U (Sanctions.clipS' (z + (y' - y)))) :=
    (U.continuous.comp Sanctions.clipS'_continuous).comp
      (continuous_id.add continuous_const)
  have hint1 : IntervalIntegrable (fun z : ℝ => U (Sanctions.clipS' z))
      MeasureTheory.volume (y - h) (y + h) := (clipComp_cont U).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun z : ℝ => U (Sanctions.clipS' (z + (y' - y))))
      MeasureTheory.volume (y - h) (y + h) := hcont2.intervalIntegrable _ _
  have hpt : ∀ z ∈ Set.Icc (y - h) (y + h),
      U (Sanctions.clipS' z) ≤ U (Sanctions.clipS' (z + (y' - y))) := fun z _ =>
    hU_mono _ _ (Sanctions.clipS'_mono (by linarith : z ≤ z + (y' - y)))
  unfold movAvgReal
  rw [hcov]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by linarith) hint1 hint2 hpt)
    (by positivity)

/-- **Dual transfer-operator contraction (the step-6 engine).** The pullback of a
`K`-Lipschitz test function `U` under the box-smeared closed loop,
`(S U)(x) := movAvgReal h U ((1−δ)·x + δ) = (1/2h)∫_{−h}^{h} U(clipS'((1−δ)x+δ+η))dη`,
is `(1−δ)·K`-Lipschitz: the moving average preserves `K` (`movAvgReal_valueLipschitz`)
and the affine closed-loop map `x ↦ (1−δ)x+δ` is `(1−δ)`-Lipschitz, so the composition
contracts the Lipschitz seminorm by `(1−δ)`. This is the Kantorovich–Rubinstein dual of
the statement *"the box-smeared Markov transfer operator is a `(1−δ)`-contraction in the
`1`-Lipschitz test-function pseudometric"* — the engine giving the lock-in chain a
unique invariant distribution with geometric convergence (uniqueness + convergence from
this contraction; existence separately, via a compactness fixed point). Stated for the
saturated-basin closed loop `F(x,1)=(1−δ)x+δ`; for `K=1` it is the `(1−δ)`-contraction
on `1`-Lipschitz functions. -/
theorem movAvgReal_affine_lipschitz_contraction {h δ : ℝ} (hh : 0 < h) (hδ : δ ≤ 1)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hUK : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ), |U z₂ - U z₁| ≤ K * dist z₁ z₂)
    (x x' : ℝ) :
    |movAvgReal h U ((1 - δ) * x + δ) - movAvgReal h U ((1 - δ) * x' + δ)|
      ≤ (1 - δ) * K * |x - x'| := by
  have h1 := movAvgReal_valueLipschitz hh U hK hUK ((1 - δ) * x + δ) ((1 - δ) * x' + δ)
  have heq : |((1 - δ) * x + δ) - ((1 - δ) * x' + δ)| = (1 - δ) * |x - x'| := by
    rw [show ((1 - δ) * x + δ) - ((1 - δ) * x' + δ) = (1 - δ) * (x - x') from by ring,
        abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - δ)]
  rw [heq] at h1
  calc |movAvgReal h U ((1 - δ) * x + δ) - movAvgReal h U ((1 - δ) * x' + δ)|
      ≤ K * ((1 - δ) * |x - x'|) := h1
    _ = (1 - δ) * K * |x - x'| := by ring

/-- **Linearity: `movAvg (U - W) = movAvg U - movAvg W`.** -/
theorem movAvg_sub (h : ℝ) (U W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (y : ℝ) :
    movAvgReal h (U - W) y = movAvgReal h U y - movAvgReal h W y := by
  have hcong : (∫ z in (y - h)..(y + h), (U - W) (Sanctions.clipS' z))
      = (∫ z in (y - h)..(y + h),
          (U (Sanctions.clipS' z) - W (Sanctions.clipS' z))) :=
    intervalIntegral.integral_congr (fun z _ => by simp)
  unfold movAvgReal
  rw [hcong, intervalIntegral.integral_sub
        ((clipComp_cont U).intervalIntegrable _ _)
        ((clipComp_cont W).intervalIntegrable _ _), mul_sub]

/-- **Nonexpansive: `|movAvg U y - movAvg W y| ≤ dist U W`.** -/
theorem movAvg_dist_le {h : ℝ} (hh : 0 < h) (U W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (y : ℝ) :
    |movAvgReal h U y - movAvgReal h W y| ≤ dist U W := by
  unfold movAvgReal
  rw [← mul_sub, abs_mul,
      ← intervalIntegral.integral_sub
        ((clipComp_cont U).intervalIntegrable _ _)
        ((clipComp_cont W).intervalIntegrable _ _)]
  have h2h : (0 : ℝ) < 2 * h := by linarith
  have habs : |1 / (2 * h)| = 1 / (2 * h) := by rw [abs_of_pos]; positivity
  rw [habs]
  have hbd : ∀ z, |U (Sanctions.clipS' z) - W (Sanctions.clipS' z)| ≤ dist U W := by
    intro z; rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist _
  have hc := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y - h) (b := y + h) (C := dist U W)
    (f := fun z => U (Sanctions.clipS' z) - W (Sanctions.clipS' z))
    (fun z _ => by rw [Real.norm_eq_abs]; exact hbd z)
  rw [Real.norm_eq_abs] at hc
  calc (1 / (2 * h)) * |∫ z in (y - h)..(y + h),
          (U (Sanctions.clipS' z) - W (Sanctions.clipS' z))|
      ≤ (1 / (2 * h)) * (dist U W * |(y + h) - (y - h)|) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = dist U W := by
        rw [show (y + h) - (y - h) = 2 * h from by ring, abs_of_pos h2h, one_div,
            mul_comm (dist U W) (2 * h), ← mul_assoc, inv_mul_cancel₀ h2h.ne', one_mul]

/-! ## The moving average as a bounded continuous function on `↥S` -/

/-- `movAvgReal h U` is `LipschitzWith (‖U‖/h)` (hence continuous). -/
theorem movAvgReal_lipschitzWith {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    LipschitzWith (‖U‖ / h).toNNReal (movAvgReal h U) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro y y'
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact movAvg_lipschitz hh U y y'

theorem movAvgReal_continuous {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    Continuous (movAvgReal h U) :=
  (movAvgReal_lipschitzWith hh U).continuous

/-- **Derivative of a one-box moving average.**  For a continuous clipped
value, differentiating the two moving endpoints gives the difference quotient
of the endpoint values.  This is the analytic bridge from a Lipschitz value
carrier to semiconcavity of its smoothed continuation. -/
theorem movAvgReal_hasDerivAt {h : ℝ} (hh : 0 < h)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (y : ℝ) :
    HasDerivAt (movAvgReal h U)
      ((U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y - h))) / (2 * h)) y := by
  let g : ℝ → ℝ := fun z => U (Sanctions.clipS' z)
  have hg : Continuous g := clipComp_cont U
  have hp : HasDerivAt (fun y : ℝ => ∫ z in (0 : ℝ)..(y + h), g z) (g (y + h)) y := by
    simpa [Function.comp_def] using
      (hg.integral_hasStrictDerivAt 0 (y + h)).hasDerivAt.comp y
        ((hasDerivAt_id y).add_const h)
  have hm : HasDerivAt (fun y : ℝ => ∫ z in (0 : ℝ)..(y - h), g z) (g (y - h)) y := by
    simpa [Function.comp_def] using
      (hg.integral_hasStrictDerivAt 0 (y - h)).hasDerivAt.comp y
        ((hasDerivAt_id y).sub_const h)
  have hsub := hp.sub hm
  have hint : (fun y : ℝ =>
      (∫ z in (0 : ℝ)..(y + h), g z) - ∫ z in (0 : ℝ)..(y - h), g z)
      = fun y : ℝ => ∫ z in (y - h)..(y + h), g z := by
    funext t
    exact intervalIntegral.integral_interval_sub_left
      (hg.intervalIntegrable 0 (t + h)) (hg.intervalIntegrable 0 (t - h))
  have hwin : HasDerivAt (fun y : ℝ => ∫ z in (y - h)..(y + h), g z)
      (g (y + h) - g (y - h)) y := by
    rw [← hint]
    exact hsub
  unfold movAvgReal
  change HasDerivAt (fun y : ℝ => (1 / (2 * h)) * ∫ z in (y - h)..(y + h), g z) _ y
  convert hwin.const_mul (1 / (2 * h)) using 1 <;> field_simp <;> ring

/-- The derivative formula corresponding to `movAvgReal_hasDerivAt`. -/
theorem movAvgReal_deriv_eq {h : ℝ} (hh : 0 < h)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (y : ℝ) :
    deriv (movAvgReal h U) y =
      (U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y - h))) / (2 * h) :=
  (movAvgReal_hasDerivAt hh U y).deriv

/-- **A one-box average of a `K`-Lipschitz value has a `K/h`-Lipschitz
derivative.**  Thus one box already supplies the semiconcavity needed for the
Sender argmax, even though a second box is useful for stronger objective-
difference estimates. -/
theorem movAvgReal_deriv_lipschitz_of_valueLipschitz {h : ℝ} (hh : 0 < h)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hUK : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ),
      |U z₂ - U z₁| ≤ K * dist z₁ z₂)
    (y y' : ℝ) :
    |deriv (movAvgReal h U) y - deriv (movAvgReal h U) y'|
      ≤ (K / h) * |y - y'| := by
  rw [movAvgReal_deriv_eq hh U y, movAvgReal_deriv_eq hh U y']
  have hp := hUK (Sanctions.clipS' (y' + h)) (Sanctions.clipS' (y + h))
  have hm := hUK (Sanctions.clipS' (y' - h)) (Sanctions.clipS' (y - h))
  have hcp := Sanctions.clipS'_lipschitz_dist (y + h) (y' + h)
  have hcm := Sanctions.clipS'_lipschitz_dist (y - h) (y' - h)
  rw [Subtype.dist_eq, Real.dist_eq] at hp hm hcp hcm
  have hplus : |U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y' + h))|
      ≤ K * |y - y'| := by
    calc
      |U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y' + h))|
          ≤ K * |(Sanctions.clipS' (y + h)).val
              - (Sanctions.clipS' (y' + h)).val| := by
            simpa [abs_sub_comm] using hp
      _ ≤ K * |(y + h) - (y' + h)| :=
        mul_le_mul_of_nonneg_left hcp hK
      _ = K * |y - y'| := by
        rw [show (y + h) - (y' + h) = y - y' by ring]
  have hminus : |U (Sanctions.clipS' (y - h)) - U (Sanctions.clipS' (y' - h))|
      ≤ K * |y - y'| := by
    calc
      |U (Sanctions.clipS' (y - h)) - U (Sanctions.clipS' (y' - h))|
          ≤ K * |(Sanctions.clipS' (y - h)).val
              - (Sanctions.clipS' (y' - h)).val| := by
            simpa [abs_sub_comm] using hm
      _ ≤ K * |(y - h) - (y' - h)| :=
        mul_le_mul_of_nonneg_left hcm hK
      _ = K * |y - y'| := by
        rw [show (y - h) - (y' - h) = y - y' by ring]
  have hnum :
      |(U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y - h)))
        - (U (Sanctions.clipS' (y' + h)) - U (Sanctions.clipS' (y' - h)))|
        ≤ 2 * K * |y - y'| := by
    calc
      |(U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y - h)))
        - (U (Sanctions.clipS' (y' + h)) - U (Sanctions.clipS' (y' - h)))|
          = |(U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y' + h)))
            - (U (Sanctions.clipS' (y - h)) - U (Sanctions.clipS' (y' - h)))| := by ring
      _ ≤ |U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y' + h))|
          + |U (Sanctions.clipS' (y - h)) - U (Sanctions.clipS' (y' - h))| :=
        abs_sub _ _
      _ ≤ K * |y - y'| + K * |y - y'| := add_le_add hplus hminus
      _ = 2 * K * |y - y'| := by ring
  have hden : 0 < 2 * h := by linarith
  rw [div_sub_div_same, abs_div, abs_of_pos hden]
  calc
    |(U (Sanctions.clipS' (y + h)) - U (Sanctions.clipS' (y - h)))
        - (U (Sanctions.clipS' (y' + h)) - U (Sanctions.clipS' (y' - h)))| / (2 * h)
        ≤ (2 * K * |y - y'|) / (2 * h) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = (K / h) * |y - y'| := by field_simp

/-- **Affine mixed-rectangle bound from a Lipschitz derivative.** If `φ` is
everywhere differentiable and `deriv φ` is `K`-Lipschitz, shifting both affine
arguments from `s` to `t` changes their `x`-versus-`y` difference by at most
`K * |c| * |d| * |x-y| * |s-t|`.

This is the general four-point estimate used to turn one-box derivative
regularity into a state modulus for an equilibrium argmax. -/
theorem affine_mixed_rectangle_of_deriv_lipschitz
    (φ : ℝ → ℝ) {K c d x y s t : ℝ}
    (hφ : ∀ z, DifferentiableAt ℝ φ z)
    (hφ' : ∀ u v, |deriv φ u - deriv φ v| ≤ K * |u - v|) :
    |(φ (c * x + d * s) - φ (c * y + d * s))
        - (φ (c * x + d * t) - φ (c * y + d * t))|
      ≤ K * |c| * |d| * |x - y| * |s - t| := by
  let q : ℝ → ℝ := fun z =>
    φ (c * x + d * z) - φ (c * y + d * z)
  have hq : ∀ z, HasDerivAt q
      (d * (deriv φ (c * x + d * z)
        - deriv φ (c * y + d * z))) z := by
    intro z
    have hxaff : HasDerivAt (fun w : ℝ => c * x + d * w) d z := by
      simpa using ((hasDerivAt_id z).const_mul d).const_add (c * x)
    have hyaff : HasDerivAt (fun w : ℝ => c * y + d * w) d z := by
      simpa using ((hasDerivAt_id z).const_mul d).const_add (c * y)
    have hxcomp := (hφ (c * x + d * z)).hasDerivAt.comp z hxaff
    have hycomp := (hφ (c * y + d * z)).hasDerivAt.comp z hyaff
    change HasDerivAt
      (fun w => φ (c * x + d * w) - φ (c * y + d * w))
      (d * (deriv φ (c * x + d * z)
        - deriv φ (c * y + d * z))) z
    convert hxcomp.sub hycomp using 1
    ring
  have hderiv :
      ∀ z, ‖deriv q z‖ ≤ K * |c| * |d| * |x - y| := by
    intro z
    rw [(hq z).deriv, Real.norm_eq_abs, abs_mul]
    calc
      |d| * |deriv φ (c * x + d * z)
          - deriv φ (c * y + d * z)|
          ≤ |d| * (K * |(c * x + d * z)
            - (c * y + d * z)|) :=
        mul_le_mul_of_nonneg_left
          (hφ' (c * x + d * z) (c * y + d * z))
          (abs_nonneg d)
      _ = K * |c| * |d| * |x - y| := by
        rw [show (c * x + d * z) - (c * y + d * z)
          = c * (x - y) by ring, abs_mul]
        ring
  have hmean := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := t) (y := s)
    (fun z _ => (hq z).differentiableAt)
    (fun z _ => hderiv z) (by simp) (by simp)
  simpa only [q, Real.norm_eq_abs] using hmean

/-- **Semiconcavity of the box-smoothed value.**  If the carrier value is
`K`-Lipschitz, then its one-box average is `(-K/h)`-strongly concave on the
real line (equivalently, semiconcave with curvature bound `K/h`). -/
theorem movAvgReal_strongConcaveOn_of_valueLipschitz {h : ℝ} (hh : 0 < h)
    (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hUK : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ),
      |U z₂ - U z₁| ≤ K * dist z₁ z₂) :
    StrongConcaveOn Set.univ (-(K / h)) (movAvgReal h U) := by
  rw [strongConcaveOn_iff_convex]
  let q : ℝ → ℝ := fun y => movAvgReal h U y - (K / h) / 2 * y ^ 2
  have hq_cont : Continuous q :=
    (movAvgReal_continuous hh U).sub
      (continuous_const.mul (continuous_id.pow 2))
  have hq_diff : Differentiable ℝ q := by
    intro y
    have hs : HasDerivAt (fun y : ℝ => (K / h) / 2 * y ^ 2) ((K / h) * y) y := by
      convert (hasDerivAt_pow 2 y).const_mul ((K / h) / 2) using 1 <;> norm_num <;> ring
    simpa only [q] using
      ((movAvgReal_hasDerivAt hh U y).sub hs).differentiableAt
  have hq_deriv (y : ℝ) :
      deriv q y = deriv (movAvgReal h U) y - (K / h) * y := by
    have hg := movAvgReal_hasDerivAt hh U y
    have hs : HasDerivAt (fun y : ℝ => (K / h) / 2 * y ^ 2) ((K / h) * y) y := by
      convert (hasDerivAt_pow 2 y).const_mul ((K / h) / 2) using 1 <;> norm_num <;> ring
    simpa only [q, movAvgReal_deriv_eq hh U y] using (hg.sub hs).deriv
  have hanti : Antitone (deriv q) := by
    intro x y hxy
    rw [hq_deriv x, hq_deriv y]
    have hder := movAvgReal_deriv_lipschitz_of_valueLipschitz hh U hK hUK y x
    have habs : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
    have hupper : deriv (movAvgReal h U) y - deriv (movAvgReal h U) x
        ≤ (K / h) * (y - x) := by
      rw [habs] at hder
      exact le_trans (le_abs_self _) hder
    linarith
  have hq_conc : ConcaveOn ℝ Set.univ q :=
    AntitoneOn.concaveOn_of_deriv convex_univ
      hq_cont.continuousOn hq_diff.differentiableOn
      (hanti.antitoneOn (interior Set.univ))
  have heq :
      (fun x : ℝ => movAvgReal h U x + -(K / h) / 2 * ‖x‖ ^ 2) = q := by
    funext x
    simp only [q, Real.norm_eq_abs, sq_abs]
    ring
  rw [heq]
  exact hq_conc

/-- **The moving-average smoothing as a bounded continuous function on `↥S`.** -/
noncomputable def movAvgBCF {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => movAvgReal h U z.val, (movAvgReal_continuous hh U).comp continuous_subtype_val⟩

@[simp] theorem movAvgBCF_apply {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (z : ↥(Sanctions.S : Set ℝ)) :
    movAvgBCF hh U z = movAvgReal h U z.val := rfl

/-- **The box moving average preserves constant functions.**  This is the
`P 1 = 1` property of a probability transition operator, derived directly
from the normalized window integral rather than added to `ShockedParams`. -/
theorem movAvgBCF_const {h : ℝ} (hh : 0 < h) (c : ℝ) :
    movAvgBCF hh (c • (1 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) =
      c • (1 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) := by
  ext z
  rw [movAvgBCF_apply]
  simp [movAvgReal]
  field_simp
  ring

/-- **The box moving average preserves pointwise order.**  If one continuation
value is everywhere below another, then its expected box-smoothed continuation
is also below the other's at every state.  This is the positivity property
needed for Bellman verification, and is derived from integral monotonicity. -/
theorem movAvgBCF_mono_operator {h : ℝ} (hh : 0 < h)
    (U W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hUW : ∀ z, U z ≤ W z) (y : ↥(Sanctions.S : Set ℝ)) :
    movAvgBCF hh U y ≤ movAvgBCF hh W y := by
  rw [movAvgBCF_apply, movAvgBCF_apply]
  unfold movAvgReal
  apply mul_le_mul_of_nonneg_left
  · exact intervalIntegral.integral_mono_on
      (by linarith : y.val - h ≤ y.val + h)
      ((clipComp_cont U).intervalIntegrable _ _)
      ((clipComp_cont W).intervalIntegrable _ _)
      (fun z _hz => hUW (Sanctions.clipS' z))
  · positivity

/-- **Full-width box smoothing has zero chord defect on `S`.**
This is the bounded-continuous-function form of `movAvgReal_one_eq_on_S`: every
chord of the half-width-`1` moving average on the physical state interval is
an equality, independently of the curvature of the unsmoothed value. -/
theorem movAvgBCF_one_affine_chord (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (y₁ y₂ m : ↥(Sanctions.S : Set ℝ)) (t : ℝ)
    (hm : m.val = t * y₁.val + (1 - t) * y₂.val) :
    t * movAvgBCF one_pos U y₁ + (1 - t) * movAvgBCF one_pos U y₂ =
      movAvgBCF one_pos U m := by
  rw [movAvgBCF_apply, movAvgBCF_apply, movAvgBCF_apply,
    movAvgReal_one_eq_on_S U y₁.property,
    movAvgReal_one_eq_on_S U y₂.property,
    movAvgReal_one_eq_on_S U m.property]
  rw [hm]
  ring

/-- **Exact full-width slope formula on `S`.**  The difference between two
smoothed values is the state difference times the endpoint slope.  This is the
two-point form of `movAvgBCF_one_affine_chord`. -/
theorem movAvgBCF_one_sub_eq (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    movAvgBCF one_pos U y₂ - movAvgBCF one_pos U y₁ =
      (1 / 2) * (y₂.val - y₁.val) *
        (U (Sanctions.clipS' 1) - U (Sanctions.clipS' 0)) := by
  rw [movAvgBCF_apply, movAvgBCF_apply,
    movAvgReal_one_eq_on_S U y₂.property,
    movAvgReal_one_eq_on_S U y₁.property]
  ring

/-- **State-Lipschitz of the BCF moving average** with constant `‖U‖/h`. -/
theorem movAvgBCF_lipschitz_state {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (z z' : ↥(Sanctions.S : Set ℝ)) :
    |movAvgBCF hh U z - movAvgBCF hh U z'| ≤ (‖U‖ / h) * dist z z' := by
  rw [movAvgBCF_apply, movAvgBCF_apply, Subtype.dist_eq, Real.dist_eq]
  exact movAvg_lipschitz hh U z.val z'.val

/-- **The BCF moving average PRESERVES a Lipschitz constant `K`** (the BCF-level
form of `movAvgReal_valueLipschitz`). If `U` is `K`-Lipschitz on `↥S` then so is
`movAvgBCF hh U`, with the **same** `K` (not the `‖U‖/h` mollifier bound). The
hypothesis/conclusion are stated in the inlined finite-difference Lipschitz form
`∀ z₁ z₂, |U z₂ − U z₁| ≤ K·dist z₁ z₂`, which is definitionally the Theory-layer
`ValueLipschitzWith U K` (kept inline here so `Foundations/` stays free of any
`Theory/` import, per Rule 19). This is the lemma that discharges the shocked
single-crossing gate at the concrete box kernel. -/
theorem movAvgBCF_valueLipschitz {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hUK : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ), |U z₂ - U z₁| ≤ K * dist z₁ z₂)
    (z₁ z₂ : ↥(Sanctions.S : Set ℝ)) :
    |movAvgBCF hh U z₂ - movAvgBCF hh U z₁| ≤ K * dist z₁ z₂ := by
  rw [movAvgBCF_apply, movAvgBCF_apply]
  calc |movAvgReal h U z₂.val - movAvgReal h U z₁.val|
      ≤ K * |z₂.val - z₁.val| := movAvgReal_valueLipschitz hh U hK hUK z₂.val z₁.val
    _ = K * dist z₁ z₂ := by rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]

/-- **The BCF moving average PRESERVES monotonicity** (BCF-level form of
`movAvgReal_mono`). If `U` is non-decreasing on `↥S` then so is `movAvgBCF hh U`.
Stated in the inlined pointwise form so `Foundations/` stays free of any
`Theory/` import, per Rule 19. -/
theorem movAvgBCF_mono {h : ℝ} (hh : 0 < h) (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hU_mono : ∀ z₁ z₂ : ↥(Sanctions.S : Set ℝ), z₁ ≤ z₂ → U z₁ ≤ U z₂)
    (z₁ z₂ : ↥(Sanctions.S : Set ℝ)) (hz : z₁ ≤ z₂) :
    movAvgBCF hh U z₁ ≤ movAvgBCF hh U z₂ := by
  rw [movAvgBCF_apply, movAvgBCF_apply]
  exact movAvgReal_mono hh U hU_mono (Subtype.coe_le_coe.mpr hz)

/-- **Linearity of the BCF moving average.** -/
theorem movAvgBCF_sub {h : ℝ} (hh : 0 < h) (U W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    movAvgBCF hh (U - W) = movAvgBCF hh U - movAvgBCF hh W := by
  ext z
  rw [BoundedContinuousFunction.sub_apply, movAvgBCF_apply, movAvgBCF_apply, movAvgBCF_apply]
  exact movAvg_sub h U W z.val

/-- **Nonexpansiveness of the BCF moving average.** -/
theorem movAvgBCF_dist_le {h : ℝ} (hh : 0 < h) (U W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    dist (movAvgBCF hh U) (movAvgBCF hh W) ≤ dist U W := by
  rw [BoundedContinuousFunction.dist_le dist_nonneg]
  intro z
  rw [movAvgBCF_apply, movAvgBCF_apply, Real.dist_eq]
  exact movAvg_dist_le hh U W z.val

end -- noncomputable section
end Sanctions
