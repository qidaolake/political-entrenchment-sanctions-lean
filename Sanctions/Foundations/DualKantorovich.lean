/-
Sanctions/Foundations/DualKantorovich.lean

**The dual Kantorovich–Rubinstein metric on probability measures, and the abstract
contraction → uniqueness + geometric-convergence machinery.**

This is the measure-side engine for "lock-in as a unique invariant distribution"
(step 6 of the shocked-persistence program). Mathlib has no Wasserstein/Kantorovich
metric and no stochastic order on measures (so Hopenhayn–Prescott's order argument is
unavailable), but the box-smeared transfer operator is a genuine **contraction** in
the dual 1-Lipschitz test-function metric, and that route needs none of the missing
infrastructure — only the elementary fact that the operator's dual pullback maps
1-Lipschitz test functions to `(1−δ)`-Lipschitz ones (which the project's
`movAvgReal_affine_lipschitz_contraction` supplies).

Contents (all generic over a compact metric measurable space `E`):
* `dualKR μ ν` — the dual Kantorovich–Rubinstein distance
  `sup over 1-Lipschitz f of (∫f dμ − ∫f dν)`.
* `dualKR_set_bddAbove`, `dualKR_nonneg` — well-definedness (constant-shift bound) and
  nonnegativity.
* `dualKR_le_of_adjoint_lipschitz` — **the contraction**: if `T`'s adjoint is `S`
  (`∫f d(Tμ)=∫(Sf)dμ`) and `S` maps 1-Lipschitz to `c`-Lipschitz (`0<c`), then
  `dualKR (Tμ) (Tν) ≤ c · dualKR μ ν`. The sibling
  `dualKR_le_of_adjoint_lipschitz_of_nonneg` needs only `0 ≤ c` (round BH-2).
* `dualKR_eq_zero_of_invariant` — **uniqueness in `d`**: with `0<c<1`, any two
  `S`-invariant probability measures have `dualKR = 0`. The sibling
  `dualKR_eq_zero_of_invariant_of_nonneg` needs only `0 ≤ c < 1`.
* `dualKR_geometric` — **geometric convergence**: a sequence whose dual distance to a
  limit contracts per step is within `cⁿ` of it.

`dualKR=0 ⟹ μ=ν` (the separation half: `d` is a genuine metric, the standard
bounded-Lipschitz determining-class fact) is not re-proved here — the `↥S`
specialization is in `Foundations/DualKantorovichS.lean` — and existence of the
invariant law (a compactness fixed point, Krylov–Bogolyubov / SLP Thm 12.10) is
constructed in `Foundations/KrylovBogolyubov.lean`; the contraction itself — the
load-bearing content — is proved here.
-/

import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory BoundedContinuousFunction

namespace Sanctions

/-- **Dual Kantorovich–Rubinstein distance** on measures over a metric space, via
1-Lipschitz bounded test functions: `sup over 1-Lipschitz f of (∫f dμ − ∫f dν)`. -/
noncomputable def dualKR {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    (μ ν : Measure E) : ℝ :=
  sSup {r : ℝ | ∃ f : E →ᵇ ℝ, LipschitzWith 1 f ∧ r = (∫ x, f x ∂μ) - ∫ x, f x ∂ν}

variable {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [CompactSpace E]
  [BorelSpace E] [Nonempty E]

/-- The defining set contains `0` (take `f = 0`). -/
theorem dualKR_set_zero_mem (μ ν : Measure E) :
    (0 : ℝ) ∈ {r : ℝ | ∃ f : E →ᵇ ℝ, LipschitzWith 1 f ∧ r = (∫ x, f x ∂μ) - ∫ x, f x ∂ν} :=
  ⟨0, by simpa using (LipschitzWith.const (0 : ℝ)).weaken (by norm_num), by simp⟩

/-- The defining set is bounded above by `2·diam(univ)` (the constant-shift bound:
adding a constant to a test function leaves `∫f dμ − ∫f dν` unchanged for probability
measures, so we may assume `f x₀ = 0`, whence `|f| ≤ diam`). -/
theorem dualKR_set_bddAbove (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {r : ℝ | ∃ f : E →ᵇ ℝ, LipschitzWith 1 f ∧ r = (∫ x, f x ∂μ) - ∫ x, f x ∂ν} := by
  obtain ⟨x₀⟩ := ‹Nonempty E›
  have hbdd : Bornology.IsBounded (Set.univ : Set E) := isCompact_univ.isBounded
  refine ⟨2 * Metric.diam (Set.univ : Set E), ?_⟩
  rintro r ⟨f, hf, rfl⟩
  have hint : Integrable (fun x => f x) μ := f.integrable μ
  have hintν : Integrable (fun x => f x) ν := f.integrable ν
  have hpt : ∀ x, f x - f x₀ ≤ Metric.diam (Set.univ : Set E) := by
    intro x
    have h1 : |f x - f x₀| ≤ dist x x₀ := by
      have := hf.dist_le_mul x x₀; simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
    have h2 : dist x x₀ ≤ Metric.diam (Set.univ : Set E) :=
      Metric.dist_le_diam_of_mem hbdd (Set.mem_univ x) (Set.mem_univ x₀)
    calc f x - f x₀ ≤ |f x - f x₀| := le_abs_self _
      _ ≤ dist x x₀ := h1
      _ ≤ _ := h2
  have hptν : ∀ x, -(Metric.diam (Set.univ : Set E)) ≤ f x - f x₀ := by
    intro x
    have h1 : |f x - f x₀| ≤ dist x x₀ := by
      have := hf.dist_le_mul x x₀; simpa [Real.dist_eq, NNReal.coe_one, one_mul] using this
    have h2 : dist x x₀ ≤ Metric.diam (Set.univ : Set E) :=
      Metric.dist_le_diam_of_mem hbdd (Set.mem_univ x) (Set.mem_univ x₀)
    have : -(f x - f x₀) ≤ Metric.diam (Set.univ : Set E) := by
      calc -(f x - f x₀) ≤ |f x - f x₀| := neg_le_abs _
        _ ≤ _ := le_trans h1 h2
    linarith
  have hμ : (∫ x, f x ∂μ) - f x₀ ≤ Metric.diam (Set.univ : Set E) := by
    have hrw : (∫ x, f x ∂μ) - f x₀ = ∫ x, (f x - f x₀) ∂μ := by
      rw [integral_sub hint (integrable_const _), integral_const]; simp
    rw [hrw]
    calc ∫ x, (f x - f x₀) ∂μ ≤ ∫ _x, Metric.diam (Set.univ : Set E) ∂μ :=
          integral_mono (hint.sub (integrable_const _)) (integrable_const _) hpt
      _ = Metric.diam (Set.univ : Set E) := by rw [integral_const]; simp
  have hν : -(Metric.diam (Set.univ : Set E)) ≤ (∫ x, f x ∂ν) - f x₀ := by
    have hrw : (∫ x, f x ∂ν) - f x₀ = ∫ x, (f x - f x₀) ∂ν := by
      rw [integral_sub hintν (integrable_const _), integral_const]; simp
    rw [hrw]
    calc -(Metric.diam (Set.univ : Set E)) = ∫ _x, -(Metric.diam (Set.univ : Set E)) ∂ν := by
          rw [integral_const]; simp
      _ ≤ ∫ x, (f x - f x₀) ∂ν :=
          integral_mono (integrable_const _) (hintν.sub (integrable_const _)) hptν
  linarith

/-- `dualKR` is nonnegative (the defining set contains `0`). -/
theorem dualKR_nonneg (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ dualKR μ ν :=
  le_csSup (dualKR_set_bddAbove μ ν) (dualKR_set_zero_mem μ ν)

/-- **Separation, easy half.** `dualKR μ ν = 0` forces equal integrals of every
1-Lipschitz test function (each `∫f dμ − ∫f dν ≤ sSup = 0`, and applying this to `−f`
gives the reverse). The full separation `dualKR = 0 ⟹ μ = ν` then needs only that
1-Lipschitz functions determine measures (a CDF/determining-class argument, supplied on
the state space in `DualKantorovichS`). -/
theorem forall_lipschitz_integral_eq_of_dualKR_eq_zero
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : dualKR μ ν = 0) :
    ∀ f : E →ᵇ ℝ, LipschitzWith 1 f → (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  intro f hf
  have hle : (∫ x, f x ∂μ) - ∫ x, f x ∂ν ≤ 0 := by
    rw [← h]; exact le_csSup (dualKR_set_bddAbove μ ν) ⟨f, hf, rfl⟩
  have hfneg : LipschitzWith 1 (⇑(-f)) := by simpa using hf.neg
  have hge : (∫ x, (-f) x ∂μ) - ∫ x, (-f) x ∂ν ≤ 0 := by
    rw [← h]; exact le_csSup (dualKR_set_bddAbove μ ν) ⟨-f, hfneg, rfl⟩
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, integral_neg] at hge
  linarith

/-- **The abstract dual contraction.** If `T`'s adjoint is `S` (`∫f d(Tμ)=∫(Sf)dμ`,
written here as the relation between the image measures `μ' = Tμ`, `ν' = Tν` and the
originals `μ`, `ν`) and `S` maps every 1-Lipschitz test function to a `c`-Lipschitz one
with `0 < c`, then `dualKR μ' ν' ≤ c · dualKR μ ν`. -/
theorem dualKR_le_of_adjoint_lipschitz
    (μ ν μ' ν' : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : (E →ᵇ ℝ) → (E →ᵇ ℝ)) {c : ℝ} (hcpos : 0 < c)
    (hS : ∀ f : E →ᵇ ℝ, LipschitzWith 1 f → LipschitzWith (Real.toNNReal c) (S f))
    (hAdjμ : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂μ') = ∫ x, (S f) x ∂μ)
    (hAdjν : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂ν') = ∫ x, (S f) x ∂ν) :
    dualKR μ' ν' ≤ c * dualKR μ ν := by
  apply csSup_le ⟨0, dualKR_set_zero_mem μ' ν'⟩
  rintro r ⟨f, hf, rfl⟩
  rw [hAdjμ f, hAdjν f]
  set g : E →ᵇ ℝ := c⁻¹ • S f with hg
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hg_lip : LipschitzWith 1 g := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hSf := hS f hf
    rw [lipschitzWith_iff_dist_le_mul] at hSf
    have hb : dist (S f x) (S f y) ≤ c * dist x y := by
      have := hSf x y; rwa [Real.coe_toNNReal c hcpos.le] at this
    have hdist : dist (g x) (g y) = c⁻¹ * dist (S f x) (S f y) := by
      simp only [hg, BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0:ℝ) < c⁻¹)]
    rw [hdist, NNReal.coe_one, one_mul]
    calc c⁻¹ * dist (S f x) (S f y) ≤ c⁻¹ * (c * dist x y) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = dist x y := by rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  have hmem : (∫ x, g x ∂μ) - ∫ x, g x ∂ν ∈
      {r : ℝ | ∃ f : E →ᵇ ℝ, LipschitzWith 1 f ∧ r = (∫ x, f x ∂μ) - ∫ x, f x ∂ν} :=
    ⟨g, hg_lip, rfl⟩
  have hle : (∫ x, g x ∂μ) - ∫ x, g x ∂ν ≤ dualKR μ ν :=
    le_csSup (dualKR_set_bddAbove μ ν) hmem
  have hgμ : (∫ x, g x ∂μ) = c⁻¹ * ∫ x, (S f) x ∂μ := by
    simp only [hg, BoundedContinuousFunction.coe_smul, smul_eq_mul]; rw [integral_const_mul]
  have hgν : (∫ x, g x ∂ν) = c⁻¹ * ∫ x, (S f) x ∂ν := by
    simp only [hg, BoundedContinuousFunction.coe_smul, smul_eq_mul]; rw [integral_const_mul]
  rw [hgμ, hgν, ← mul_sub] at hle
  have hfactor : (∫ x, (S f) x ∂μ) - ∫ x, (S f) x ∂ν
        = c * (c⁻¹ * ((∫ x, (S f) x ∂μ) - ∫ x, (S f) x ∂ν)) := by
    rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hle hcpos.le

/-- **The abstract dual contraction, at a nonnegative factor.** As
`dualKR_le_of_adjoint_lipschitz`, with `0 ≤ c` in place of `0 < c` (round BH-2,
item BH2.11). The new case is `c = 0`: then every `S f` is `0`-Lipschitz, hence
constant, so its integrals against the two probability measures agree and every
element of the defining set of `dualKR μ' ν'` is `0`. Generic over the space `E`;
no transition law is involved. -/
theorem dualKR_le_of_adjoint_lipschitz_of_nonneg
    (μ ν μ' ν' : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : (E →ᵇ ℝ) → (E →ᵇ ℝ)) {c : ℝ} (hc0 : 0 ≤ c)
    (hS : ∀ f : E →ᵇ ℝ, LipschitzWith 1 f → LipschitzWith (Real.toNNReal c) (S f))
    (hAdjμ : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂μ') = ∫ x, (S f) x ∂μ)
    (hAdjν : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂ν') = ∫ x, (S f) x ∂ν) :
    dualKR μ' ν' ≤ c * dualKR μ ν := by
  rcases hc0.lt_or_eq with hcpos | hc
  · exact dualKR_le_of_adjoint_lipschitz μ ν μ' ν' S hcpos hS hAdjμ hAdjν
  · subst hc
    rw [zero_mul]
    apply csSup_le ⟨0, dualKR_set_zero_mem μ' ν'⟩
    rintro r ⟨f, hf, rfl⟩
    rw [hAdjμ f, hAdjν f]
    obtain ⟨x₀⟩ := ‹Nonempty E›
    have hconst : ∀ x, (S f) x = (S f) x₀ := by
      intro x
      have hd := (hS f hf).dist_le_mul x x₀
      rw [Real.toNNReal_zero, NNReal.coe_zero, zero_mul] at hd
      exact dist_le_zero.mp hd
    have hμc : (∫ x, (S f) x ∂μ) = (S f) x₀ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const]; simp
    have hνc : (∫ x, (S f) x ∂ν) = (S f) x₀ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const]; simp
    rw [hμc, hνc, sub_self]

/-- **Uniqueness in the dual metric, at a nonnegative factor.** If `0 ≤ c < 1`
and `μ`, `ν` are both `S`-invariant probability measures (`∫f dμ = ∫(Sf)dμ`,
likewise `ν`), then `dualKR μ ν = 0`. As `dualKR_eq_zero_of_invariant`, with
`0 ≤ c` in place of `0 < c` (round BH-2, item BH2.11); generic over `E`. -/
theorem dualKR_eq_zero_of_invariant_of_nonneg
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : (E →ᵇ ℝ) → (E →ᵇ ℝ)) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hS : ∀ f : E →ᵇ ℝ, LipschitzWith 1 f → LipschitzWith (Real.toNNReal c) (S f))
    (hInvμ : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂μ) = ∫ x, (S f) x ∂μ)
    (hInvν : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂ν) = ∫ x, (S f) x ∂ν) :
    dualKR μ ν = 0 := by
  have hcontr : dualKR μ ν ≤ c * dualKR μ ν :=
    dualKR_le_of_adjoint_lipschitz_of_nonneg μ ν μ ν S hc0 hS hInvμ hInvν
  have hnn : 0 ≤ dualKR μ ν := dualKR_nonneg μ ν
  nlinarith [hcontr, hnn]

/-- **Uniqueness in the dual metric.** If `0 < c < 1` and `μ`, `ν` are both
`S`-invariant probability measures (`∫f dμ = ∫(Sf)dμ`, likewise `ν`), then
`dualKR μ ν = 0`. Since `dualKR` is a genuine metric on probability measures over a
compact space (the standard bounded-Lipschitz determining-class fact, not re-proved
here), this is uniqueness of the invariant law. The corollary of
`dualKR_eq_zero_of_invariant_of_nonneg` at a positive factor. -/
theorem dualKR_eq_zero_of_invariant
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : (E →ᵇ ℝ) → (E →ᵇ ℝ)) {c : ℝ} (hcpos : 0 < c) (hc1 : c < 1)
    (hS : ∀ f : E →ᵇ ℝ, LipschitzWith 1 f → LipschitzWith (Real.toNNReal c) (S f))
    (hInvμ : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂μ) = ∫ x, (S f) x ∂μ)
    (hInvν : ∀ f : E →ᵇ ℝ, (∫ x, f x ∂ν) = ∫ x, (S f) x ∂ν) :
    dualKR μ ν = 0 :=
  dualKR_eq_zero_of_invariant_of_nonneg μ ν S hcpos.le hc1 hS hInvμ hInvν

/-- **Geometric convergence in the dual metric.** If the dual distance of a sequence
of measures to a fixed limit contracts by a factor `c` each step, then it is within
`cⁿ` of the limit at step `n`. (For `0 ≤ c < 1` this gives `dualKR (seq n) lam → 0`.) -/
theorem dualKR_geometric (seq : ℕ → Measure E) (lam : Measure E) {c : ℝ} (hc0 : 0 ≤ c)
    (hstep : ∀ n, dualKR (seq (n + 1)) lam ≤ c * dualKR (seq n) lam) :
    ∀ n, dualKR (seq n) lam ≤ c ^ n * dualKR (seq 0) lam := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      calc dualKR (seq (k + 1)) lam
          ≤ c * dualKR (seq k) lam := hstep k
        _ ≤ c * (c ^ k * dualKR (seq 0) lam) := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (k + 1) * dualKR (seq 0) lam := by ring

end Sanctions
