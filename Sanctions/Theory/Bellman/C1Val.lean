/-
Sanctions/Theory/Bellman/C1Val.lean

**C¹ migration iter 2: `C1Val K_d` structure packaging BCF value +
derivative with uniform bound.**

**PARTIALLY UNFROZEN (2026-07-12; supersedes the 2026-07-04 A6 freeze
for the witness layer only).** The *witness* layer now carries
paper-facing load: `Examples/C1WitnessEnvelope.lean` inhabits `C1Val`,
`ValueClass_C1`, `ValueClass_C1Complete` and `C1BellmanSystem` at the
two pinned exact Bellman fixed points (eeCert, fourGroup), and the
paper's shadow-price passage cites the resulting equilibrium slopes.
At those witnesses the completeness field is *proved*
(`eeC1Class_complete` / `fgcC1Class_complete` — a singleton carrier is
trivially complete) and `T = id`, so the `c1distPair`-fixed point is a
genuine fixed point: no assumed-completeness postulate and no
pseudo-metric artefact enters any shipped result. No headline row
fences the C¹ layer.

The *abstract* layer STAYS FROZEN: each general form (the
`SmoothSanctionClass` IFT Prop fields, an abstract
`ValueClass_C1Complete` derivation, general-`F` RZS-style statements)
would need new differentiability hypotheses (Rule 3). Both structural
deficiencies persist at abstract generality: `c1distPair` is a
pseudo-metric (`V'` stored on all of `ℝ`), and completeness
(`ValueClass_C1Complete`) is consumed per-certificate, not derived. Revival order if ever needed: (1) the within-set
uniform-limits-of-derivatives theorem (a mathlib gap, not an analytic
one — `Foundations/` candidate), (2) the `V'`-domain refactor,
(3) asymmetric duplication only once a consumer exists.

Iter 1 (`DerivativeOnS.lean`) provided the derivative-on-S
predicates. This file packages a BCF with its derivative as a
single structure, which becomes the underlying type for the C¹
subspace in subsequent iterations.

## Definitions

* `C1Val K_d` — a structure carrying:
  - `V : ↥S →ᵇ ℝ` (BCF value),
  - `V' : ℝ → ℝ` (derivative function),
  - `hasDeriv : HasBoundedDerivOnS V V' K_d` (witnesses).
* `C1Val.zero K_d hK_d : C1Val K_d` — the zero element.
* Coercion `C1Val K_d → Val`.

Iters 5-15 subsequently landed the C¹ distance (`c1dist` /
`c1distPair`, a `Dist`-instance-level pseudo-metric), the
`IsC1Cauchy` / `IsC1CauchyPair` predicates, the limit packaging
`toC1ValLim`, and a Banach iteration on `ValueClass_C1`. The true
residual: no `PseudoMetricSpace` / `CompleteSpace` instance is
registered, and completeness is consumed as a certificate field
(`ValueClass_C1Complete`), not derived from
uniform-convergence-of-derivatives.

## Rule compliance

**Rule 1.** Constructive structure + concrete zero instance; no
`sorry`.

**Rule 3.** No new `Params` fields. `C1Val K_d` is a project-theory
scaffold; the parameter `K_d` (derivative bound) and the derivative
function are theorem-parameter primitives.

**Rule 5.** Fully parametric over `K_d`.
-/

import Sanctions.Domain.UnitIntervalDerivatives
import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Postulates.AbstractGame
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

/-! ## C¹ structure -/

/-- **`C1Val K_d`** — a BCF `V : ↥S →ᵇ ℝ` packaged with a
derivative function `V' : ℝ → ℝ` that is uniformly bounded by
`K_d` on `Sanctions.S`. The pair `(V, V')` is the natural carrier
for the C¹ subspace; subsequent iterations equip
`C1Val K_d` with the C¹ norm (sup-norm of `V` + sup-norm of `V'`)
and prove completeness via uniform-convergence-of-derivatives. -/
structure C1Val (K_d : ℝ) where
  /-- The underlying BCF value. -/
  V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- The derivative function on `Sanctions.S` (extended to `ℝ`). -/
  V' : ℝ → ℝ
  /-- Derivative existence + sup-bound `K_d` witness. -/
  hasDeriv : HasBoundedDerivOnS V V' K_d

namespace C1Val

variable {K_d : ℝ}

/-! ## Forgetful coercion to the underlying BCF value -/

/-- Forgetful projection: `C1Val K_d → ↥S →ᵇ ℝ`. -/
instance : CoeOut (C1Val K_d) (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) where
  coe c := c.V

/-! ## Zero element -/

/-- **Zero C¹ value** — the zero BCF with the zero derivative
function, bounded by any `K_d ≥ 0`. -/
noncomputable def zero (K_d : ℝ) (hK_d : 0 ≤ K_d) : C1Val K_d where
  V := 0
  V' := fun _ => 0
  hasDeriv := by
    refine ⟨zero_hasDerivOnS, ?_⟩
    intro x _hx
    simp
    exact hK_d

/-- Sanity: the zero element's value is the zero BCF. -/
@[simp] theorem zero_V (K_d : ℝ) (hK_d : 0 ≤ K_d) :
    (C1Val.zero K_d hK_d).V = 0 := rfl

/-- Sanity: the zero element's derivative is the zero function. -/
@[simp] theorem zero_V' (K_d : ℝ) (hK_d : 0 ≤ K_d) :
    (C1Val.zero K_d hK_d).V' = (fun _ : ℝ => (0 : ℝ)) := rfl

/-! ## Existence: nonempty whenever `K_d ≥ 0` -/

theorem nonempty_of_nonneg {K_d : ℝ} (hK_d : 0 ≤ K_d) :
    Nonempty (C1Val K_d) :=
  ⟨C1Val.zero K_d hK_d⟩

/-! ## C¹ distance (iter 3 minimal)

The C¹ distance between two `C1Val K_d` packages is the sum of:
* the BCF sup-norm distance between the values,
* the sup over `Sanctions.S` of the absolute difference between
  derivative functions.

The second term is well-defined: since `|c.V' x| ≤ K_d` on `S` for
both, the difference `|c₁.V' x - c₂.V' x| ≤ 2·K_d` uniformly on
`S`, so the image is bounded above and its sSup exists. -/

/-- **C¹ distance on `C1Val K_d`.** Sum of BCF distance of values
and sup-on-`S` of absolute derivative-difference. -/
noncomputable def c1dist (c₁ c₂ : C1Val K_d) : ℝ :=
  dist c₁.V c₂.V
    + sSup ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S)

/-- The derivative-difference image is bounded above by `2·K_d`. -/
theorem deriv_diff_image_bddAbove
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d) (c₁ c₂ : C1Val K_d) :
    BddAbove ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S) := by
  refine ⟨2 * K_d, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have h₁ : |c₁.V' x| ≤ K_d := c₁.hasDeriv.bound x hx
  have h₂ : |c₂.V' x| ≤ K_d := c₂.hasDeriv.bound x hx
  have h_tri : |c₁.V' x - c₂.V' x| ≤ |c₁.V' x| + |c₂.V' x| := by
    have := abs_sub (c₁.V' x) (c₂.V' x)
    linarith
  linarith

/-- The derivative-difference image is nonempty (`S` contains `0`). -/
theorem deriv_diff_image_nonempty
    (c₁ c₂ : C1Val K_d) :
    ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S).Nonempty := by
  refine ⟨_, ⟨0, ?_, rfl⟩⟩
  exact ⟨le_refl 0, zero_le_one⟩

/-- The C¹ distance is non-negative. -/
theorem c1dist_nonneg {K_d : ℝ} (hK_d_nn : 0 ≤ K_d) (c₁ c₂ : C1Val K_d) :
    0 ≤ C1Val.c1dist c₁ c₂ := by
  unfold C1Val.c1dist
  have h_bcf : 0 ≤ dist c₁.V c₂.V := dist_nonneg
  have h_sup_nn :
      0 ≤ sSup ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S) := by
    apply le_csSup_of_le (deriv_diff_image_bddAbove hK_d_nn c₁ c₂)
      ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
    exact abs_nonneg _
  linarith

/-- C¹ distance is symmetric. -/
theorem c1dist_comm (c₁ c₂ : C1Val K_d) :
    C1Val.c1dist c₁ c₂ = C1Val.c1dist c₂ c₁ := by
  unfold C1Val.c1dist
  have h_bcf : dist c₁.V c₂.V = dist c₂.V c₁.V := dist_comm _ _
  have h_deriv :
      (fun x => |c₁.V' x - c₂.V' x|) = (fun x => |c₂.V' x - c₁.V' x|) := by
    funext x
    exact abs_sub_comm _ _
  rw [h_bcf, h_deriv]

/-- C¹ distance of an element with itself is zero. -/
theorem c1dist_self (c : C1Val K_d) :
    C1Val.c1dist c c = 0 := by
  unfold C1Val.c1dist
  have h_self : (fun x => |c.V' x - c.V' x|) = (fun _ => (0 : ℝ)) := by
    funext x; simp
  rw [h_self]
  have h_sSup_zero :
      sSup ((fun _ : ℝ => (0 : ℝ)) '' Sanctions.S) = 0 := by
    have h_image : (fun _ : ℝ => (0 : ℝ)) '' Sanctions.S = {0} := by
      ext y
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, _, h_eq⟩
        exact h_eq.symm
      · intro h_eq
        refine ⟨0, ?_, h_eq.symm⟩
        exact ⟨le_refl 0, zero_le_one⟩
    rw [h_image]
    exact csSup_singleton 0
  rw [h_sSup_zero, dist_self]
  ring

/-- **C¹ triangle inequality (iter 4).** Sup over `S` of the
absolute difference is sub-additive (standard triangle bound on
sup-norms); combined with BCF triangle inequality, the C¹ distance
inherits the triangle inequality. -/
theorem c1dist_triangle {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (c₁ c₂ c₃ : C1Val K_d) :
    C1Val.c1dist c₁ c₃ ≤ C1Val.c1dist c₁ c₂ + C1Val.c1dist c₂ c₃ := by
  unfold C1Val.c1dist
  -- Two-piece triangle: BCF + sup-on-S derivative diff.
  have h_bcf_tri : dist c₁.V c₃.V ≤ dist c₁.V c₂.V + dist c₂.V c₃.V :=
    dist_triangle c₁.V c₂.V c₃.V
  -- For the sup-on-S piece, prove sub-additivity.
  -- Pointwise: |V'₁ x - V'₃ x| ≤ |V'₁ x - V'₂ x| + |V'₂ x - V'₃ x|.
  -- Hence sSup of LHS ≤ sSup of (point-wise sum) ≤ sSup of LHS-only + sSup of RHS-only.
  have h_bdd_13 : BddAbove ((fun x => |c₁.V' x - c₃.V' x|) '' Sanctions.S) :=
    deriv_diff_image_bddAbove hK_d_nn c₁ c₃
  have h_bdd_12 : BddAbove ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S) :=
    deriv_diff_image_bddAbove hK_d_nn c₁ c₂
  have h_bdd_23 : BddAbove ((fun x => |c₂.V' x - c₃.V' x|) '' Sanctions.S) :=
    deriv_diff_image_bddAbove hK_d_nn c₂ c₃
  have h_ne_13 :
      ((fun x => |c₁.V' x - c₃.V' x|) '' Sanctions.S).Nonempty :=
    deriv_diff_image_nonempty c₁ c₃
  -- Bound each |V'₁ x - V'₃ x| by sSup_{12} + sSup_{23} pointwise.
  have h_pt_bound : ∀ y ∈ (fun x => |c₁.V' x - c₃.V' x|) '' Sanctions.S,
      y ≤ sSup ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S)
          + sSup ((fun x => |c₂.V' x - c₃.V' x|) '' Sanctions.S) := by
    rintro y ⟨x, hx, rfl⟩
    have h_tri_abs : |c₁.V' x - c₃.V' x|
                      ≤ |c₁.V' x - c₂.V' x| + |c₂.V' x - c₃.V' x| := by
      have h_eq : c₁.V' x - c₃.V' x
                    = (c₁.V' x - c₂.V' x) + (c₂.V' x - c₃.V' x) := by ring
      rw [h_eq]
      exact abs_add_le _ _
    have h_le_12 : |c₁.V' x - c₂.V' x|
                    ≤ sSup ((fun x => |c₁.V' x - c₂.V' x|) ''
                              Sanctions.S) :=
      le_csSup h_bdd_12 ⟨x, hx, rfl⟩
    have h_le_23 : |c₂.V' x - c₃.V' x|
                    ≤ sSup ((fun x => |c₂.V' x - c₃.V' x|) ''
                              Sanctions.S) :=
      le_csSup h_bdd_23 ⟨x, hx, rfl⟩
    linarith
  have h_sSup_tri :
      sSup ((fun x => |c₁.V' x - c₃.V' x|) '' Sanctions.S)
        ≤ sSup ((fun x => |c₁.V' x - c₂.V' x|) '' Sanctions.S)
          + sSup ((fun x => |c₂.V' x - c₃.V' x|) '' Sanctions.S) :=
    csSup_le h_ne_13 h_pt_bound
  linarith

/-! ## iter 5: lightweight `Dist` instance + Cauchy criterion

A full `MetricSpace`/`PseudoMetricSpace` typeclass requires the
`K_d ≥ 0` hypothesis to be carried inside the typeclass, which
complicates the instance. The lighter-weight `Dist` typeclass (just
a distance function, no axioms) requires no positivity — useful for
notation. -/

/-- `Dist` instance on `C1Val K_d` using `c1dist`. -/
noncomputable instance instDist : Dist (C1Val K_d) where
  dist := C1Val.c1dist

@[simp] theorem dist_eq_c1dist (c₁ c₂ : C1Val K_d) :
    dist c₁ c₂ = C1Val.c1dist c₁ c₂ := rfl

/-- **Cauchy criterion for sequences in `C1Val K_d`** (under
`c1dist`). Standard definition. -/
def IsC1Cauchy {K_d : ℝ} (s : ℕ → C1Val K_d) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    C1Val.c1dist (s m) (s n) < ε

/-- **Cauchy sequence in C1Val projects to BCF-Cauchy sequence of
values.** Direct consequence of `dist V_m V_n ≤ c1dist (s m) (s n)`
(the BCF dist is one summand of c1dist; the other summand is
non-negative when `K_d ≥ 0`). -/
theorem IsC1Cauchy.V_isBCFCauchy {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      dist (s m).V (s n).V < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have h_c1 : C1Val.c1dist (s m) (s n) < ε := hN m n hm hn
  -- c1dist = dist V V + sSup_deriv_diff; the sSup is ≥ 0, so dist V V ≤ c1dist
  have h_sup_nn :
      0 ≤ sSup ((fun x => |(s m).V' x - (s n).V' x|) '' Sanctions.S) := by
    apply le_csSup_of_le (deriv_diff_image_bddAbove hK_d_nn (s m) (s n))
      ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
    exact abs_nonneg _
  unfold C1Val.c1dist at h_c1
  linarith

/-- **iter 6: Cauchy sequence in C1Val projects to sup-on-S-Cauchy
sequence of derivatives.** Symmetric companion to
`IsC1Cauchy.V_isBCFCauchy`: the sup-on-S derivative-difference is
the other summand of `c1dist`, so it's bounded above by `c1dist`. -/
theorem IsC1Cauchy.V'_isSupOnSCauchy {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      sSup ((fun x => |(s m).V' x - (s n).V' x|) '' Sanctions.S) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have h_c1 : C1Val.c1dist (s m) (s n) < ε := hN m n hm hn
  have h_bcf_nn : 0 ≤ dist (s m).V (s n).V := _root_.dist_nonneg
  unfold C1Val.c1dist at h_c1
  linarith

/-- **iter 7: V projection is mathlib-Cauchy in BCF.** Bridges our
custom `IsC1Cauchy` to mathlib's `CauchySeq` for the V projection,
so we can invoke mathlib's BCF completeness to get a limit. -/
theorem IsC1Cauchy.V_cauchySeq {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) :
    CauchySeq (fun n => (s n).V) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hs.V_isBCFCauchy hK_d_nn ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  exact hN m n hm hn

/-- **iter 7 corollary: V projection has a BCF limit.** BCF
(over a compact like `↥S`) is a complete metric space, so any
Cauchy sequence converges. -/
theorem IsC1Cauchy.V_hasLimit {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) :
    ∃ V_lim : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Filter.Tendsto (fun n => (s n).V) Filter.atTop (nhds V_lim) := by
  have h_cauchy : CauchySeq (fun n => (s n).V) := hs.V_cauchySeq hK_d_nn
  exact cauchySeq_tendsto_of_complete h_cauchy

/-- **iter 8: V' is pointwise Cauchy on S.** At every fixed
`x ∈ Sanctions.S`, the sequence `(s n).V' x` is Cauchy in ℝ.
Proof: bound the pointwise difference by the sup-on-S difference
(which is itself bounded by `c1dist`). -/
theorem IsC1Cauchy.V'_pointwise_cauchySeq
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    (x : ℝ) (hx : x ∈ Sanctions.S) :
    CauchySeq (fun n => (s n).V' x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hs.V'_isSupOnSCauchy hK_d_nn ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have h_sup : sSup ((fun y => |(s m).V' y - (s n).V' y|) '' Sanctions.S) < ε :=
    hN m n hm hn
  have h_pt_le_sup :
      |(s m).V' x - (s n).V' x|
        ≤ sSup ((fun y => |(s m).V' y - (s n).V' y|) '' Sanctions.S) := by
    apply le_csSup
    · exact deriv_diff_image_bddAbove hK_d_nn (s m) (s n)
    · exact ⟨x, hx, rfl⟩
  have h_dist :
      dist ((s m).V' x) ((s n).V' x) = |(s m).V' x - (s n).V' x| :=
    Real.dist_eq _ _
  rw [h_dist]
  linarith

/-- **iter 8 corollary: V' has a pointwise limit on S.**
Pointwise Cauchy in ℝ → pointwise limit exists. -/
theorem IsC1Cauchy.V'_pointwise_hasLimit
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    (x : ℝ) (hx : x ∈ Sanctions.S) :
    ∃ L : ℝ, Filter.Tendsto (fun n => (s n).V' x) Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_complete (hs.V'_pointwise_cauchySeq hK_d_nn x hx)

/-- **iter 9: pointwise limit function `V'_lim`.** Defined via
`Classical.choose` from `V'_pointwise_hasLimit` for x ∈ S; arbitrary
(zero) outside S. -/
noncomputable def IsC1Cauchy.V'_lim
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) (x : ℝ) : ℝ :=
  if hx : x ∈ Sanctions.S then
    Classical.choose (hs.V'_pointwise_hasLimit hK_d_nn x hx)
  else 0

/-- **`V'_lim` is the pointwise limit on `S`.** -/
theorem IsC1Cauchy.V'_lim_tendsto
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    (x : ℝ) (hx : x ∈ Sanctions.S) :
    Filter.Tendsto (fun n => (s n).V' x) Filter.atTop
      (nhds (hs.V'_lim hK_d_nn x)) := by
  unfold IsC1Cauchy.V'_lim
  rw [dif_pos hx]
  exact Classical.choose_spec (hs.V'_pointwise_hasLimit hK_d_nn x hx)

/-- **`V'_lim` is bounded by `K_d` on `S`.** Limit of a sequence of
`K_d`-bounded values is `K_d`-bounded. -/
theorem IsC1Cauchy.V'_lim_bound
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    (x : ℝ) (hx : x ∈ Sanctions.S) :
    |hs.V'_lim hK_d_nn x| ≤ K_d := by
  -- |V'_n x| ≤ K_d for all n; take limit.
  have h_each : ∀ n, |(s n).V' x| ≤ K_d :=
    fun n => (s n).hasDeriv.bound x hx
  -- |·| is continuous; tendsto + each bound → limit bound.
  have h_tendsto_abs :
      Filter.Tendsto (fun n => |(s n).V' x|) Filter.atTop
        (nhds |hs.V'_lim hK_d_nn x|) := by
    exact (continuous_abs.tendsto _).comp (hs.V'_lim_tendsto hK_d_nn x hx)
  exact le_of_tendsto h_tendsto_abs (Filter.Eventually.of_forall h_each)

/-- **iter 10: V'_n → V'_lim uniformly on `S`.** Standard
"uniform Cauchy + pointwise limit ⇒ uniform convergence" pattern.
At each ε > 0, find `N` such that `sup_{x∈S} |V'_m - V'_n| < ε/2`
for m, n ≥ N (from `V'_isSupOnSCauchy`). Pass to limit as n → ∞
(pointwise) to get `sup_{x∈S} |V'_m - V'_lim| ≤ ε/2 < ε` for m ≥ N. -/
theorem IsC1Cauchy.V'_lim_tendstoUniformlyOn
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ x ∈ Sanctions.S,
      |(s m).V' x - hs.V'_lim hK_d_nn x| ≤ ε := by
  intro ε hε
  -- Take N from V'_isSupOnSCauchy at ε/2 (strict).
  obtain ⟨N, hN⟩ := hs.V'_isSupOnSCauchy hK_d_nn (ε / 2) (by linarith)
  refine ⟨N, fun m hm x hx => ?_⟩
  -- Pointwise: |V'_m(x) - V'_lim(x)| = lim_{n→∞} |V'_m(x) - V'_n(x)|.
  -- Each |V'_m(x) - V'_n(x)| ≤ sSup_{y∈S} |V'_m(y) - V'_n(y)| < ε/2
  -- for n ≥ N. Take n → ∞: |V'_m(x) - V'_lim(x)| ≤ ε/2 ≤ ε.
  have h_tendsto :
      Filter.Tendsto (fun n => |(s m).V' x - (s n).V' x|) Filter.atTop
        (nhds |(s m).V' x - hs.V'_lim hK_d_nn x|) := by
    have h_inner : Filter.Tendsto (fun n => (s m).V' x - (s n).V' x)
                                  Filter.atTop
                                  (nhds ((s m).V' x - hs.V'_lim hK_d_nn x)) :=
      (Filter.Tendsto.const_sub _ (hs.V'_lim_tendsto hK_d_nn x hx))
    exact (continuous_abs.tendsto _).comp h_inner
  -- For n ≥ N, |V'_m(x) - V'_n(x)| ≤ ε/2.
  have h_event : ∀ᶠ n in Filter.atTop, |(s m).V' x - (s n).V' x| ≤ ε / 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have h_sup_lt :
        sSup ((fun y => |(s m).V' y - (s n).V' y|) '' Sanctions.S) < ε / 2 :=
      hN m n hm hn
    have h_pt_le_sup :
        |(s m).V' x - (s n).V' x|
          ≤ sSup ((fun y => |(s m).V' y - (s n).V' y|) '' Sanctions.S) := by
      apply le_csSup
      · exact deriv_diff_image_bddAbove hK_d_nn (s m) (s n)
      · exact ⟨x, hx, rfl⟩
    linarith
  -- Take limit.
  have h_le : |(s m).V' x - hs.V'_lim hK_d_nn x| ≤ ε / 2 :=
    le_of_tendsto h_tendsto h_event
  linarith

/-! ## iter 11: V_lim has V'_lim as derivative on interior of S

Applies mathlib's `hasDerivAt_of_tendstoUniformlyOn` for open sets
to the open interior `Set.Ioo 0 1 ⊂ Sanctions.S`. The three
hypotheses are: uniform convergence of derivatives on the open set,
each member's derivative existence, and pointwise convergence of
values. -/

/-- **Converts our ε-N form `V'_lim_tendstoUniformlyOn`** to
mathlib's `TendstoUniformlyOn` form, restricted to the open
interior `Set.Ioo 0 1`. -/
theorem IsC1Cauchy.V'_tendstoUniformlyOn_Ioo
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s) :
    TendstoUniformlyOn (fun n x => (s n).V' x)
      (hs.V'_lim hK_d_nn) Filter.atTop (Set.Ioo 0 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Use V'_lim_tendstoUniformlyOn at ε/2 < ε (strict).
  obtain ⟨N, hN⟩ := hs.V'_lim_tendstoUniformlyOn hK_d_nn (ε / 2) (by linarith)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn x hx => ?_⟩
  -- Ioo 0 1 ⊆ Icc 0 1 = S.
  have hx_S : x ∈ Sanctions.S := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have h_le : |(s n).V' x - hs.V'_lim hK_d_nn x| ≤ ε / 2 :=
    hN n hn x hx_S
  have h_dist :
      dist (hs.V'_lim hK_d_nn x) ((s n).V' x)
        = |(s n).V' x - hs.V'_lim hK_d_nn x| := by
    rw [dist_comm, Real.dist_eq]
  rw [h_dist]
  linarith

/-- **Pointwise convergence of `bcfExtendToR (s n).V → bcfExtendToR V_lim`**
on `Set.Ioo 0 1`. Direct consequence of BCF norm convergence and
the BCF→pointwise inequality. -/
theorem IsC1Cauchy.V_extendToR_tendsto_pointwise_on_Ioo
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    {V_lim : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV_lim : Filter.Tendsto (fun n => (s n).V) Filter.atTop (nhds V_lim)) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      Filter.Tendsto (fun n => bcfExtendToR (s n).V x) Filter.atTop
        (nhds (bcfExtendToR V_lim x)) := by
  intro x hx
  -- For x ∈ Ioo, clipS' x = ⟨x, _⟩ (no clamping), so bcfExtendToR V x = V ⟨x, _⟩.
  -- Tendsto of BCF gives uniform → pointwise tendsto at each subtype point.
  have hx_S : x ∈ Sanctions.S := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- Use mathlib's `BoundedContinuousFunction.tendsto_iff_tendstoUniformly`? Or
  -- just bound pointwise by sup norm.
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hV_lim
  obtain ⟨N, hN⟩ := hV_lim ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h_dist_bcf : dist ((s n).V) V_lim < ε := hN n hn
  -- |bcfExtendToR (s n).V x - bcfExtendToR V_lim x| ≤ dist BCF
  -- bcfExtendToR f x = f (clipS' x); pointwise BCF inequality.
  have h_clip_pt :
      dist (bcfExtendToR (s n).V x) (bcfExtendToR V_lim x)
        ≤ dist ((s n).V) V_lim := by
    unfold bcfExtendToR
    exact BoundedContinuousFunction.dist_coe_le_dist (Sanctions.clipS' x)
  linarith

/-- **iter 11: V_lim has V'_lim as derivative on `Set.Ioo 0 1`.**
Applies mathlib's `hasDerivAt_of_tendstoUniformlyOn` for the open
interior. Each `(s n).V` has the derivative `(s n).V'` on S (in the
within-set sense); on the open interior, HasDerivWithinAt ⇒
HasDerivAt. Uniform convergence of derivatives + pointwise
convergence of values ⇒ V_lim is differentiable with V'_lim as
derivative on the interior. -/
theorem IsC1Cauchy.V_lim_hasDerivAt_on_Ioo
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    {V_lim : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV_lim : Filter.Tendsto (fun n => (s n).V) Filter.atTop (nhds V_lim))
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (bcfExtendToR V_lim) (hs.V'_lim hK_d_nn x) x := by
  apply hasDerivAt_of_tendstoUniformlyOn (s := Set.Ioo (0 : ℝ) 1)
    isOpen_Ioo
    (hs.V'_tendstoUniformlyOn_Ioo hK_d_nn)
  · -- ∀ᶠ n in atTop, ∀ x ∈ Ioo 0 1, HasDerivAt (bcfExtendToR V_n) (V'_n x) x.
    rw [Filter.eventually_atTop]
    refine ⟨0, fun n _ x hx => ?_⟩
    -- From HasDerivWithinAt on S to HasDerivAt on interior.
    have hx_S : x ∈ Sanctions.S :=
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have h_within : HasDerivWithinAt (bcfExtendToR (s n).V) ((s n).V' x)
        Sanctions.S x :=
      (s n).hasDeriv.hasDerivOnS x hx_S
    -- For x in interior of S, S is a nhd of x.
    have h_Ioo_nhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := isOpen_Ioo.mem_nhds hx
    have h_subset : Set.Ioo (0 : ℝ) 1 ⊆ Sanctions.S := fun y hy =>
      ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have h_S_nhds : Sanctions.S ∈ nhds x :=
      Filter.mem_of_superset h_Ioo_nhds h_subset
    exact h_within.hasDerivAt h_S_nhds
  · exact hs.V_extendToR_tendsto_pointwise_on_Ioo hK_d_nn hV_lim
  · exact hx

/-! ## iter 12: package limit as a `C1Val K_d`

Combines the interior derivative (iter 11) with boundary
derivatives (supplied as hypotheses) to construct
`HasBoundedDerivOnS V_lim (V'_lim) K_d`. The boundary hypotheses
package the one-sided derivative limit behavior at `x = 0` and
`x = 1` that the interior result doesn't directly cover. -/

/-- **iter 12: `HasBoundedDerivOnS` for V_lim with V'_lim from limit
data + boundary derivatives.** Discharges:
* Interior derivative: from `V_lim_hasDerivAt_on_Ioo` →
  `HasDerivAt.hasDerivWithinAt`.
* Boundary derivatives: assumed as hypotheses (`h_deriv_0`,
  `h_deriv_1`).
* Bound: from `V'_lim_bound`. -/
theorem IsC1Cauchy.hasBoundedDerivOnS_limit
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    {V_lim : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV_lim : Filter.Tendsto (fun n => (s n).V) Filter.atTop (nhds V_lim))
    (h_deriv_0 :
      HasDerivWithinAt (bcfExtendToR V_lim) (hs.V'_lim hK_d_nn 0)
        Sanctions.S 0)
    (h_deriv_1 :
      HasDerivWithinAt (bcfExtendToR V_lim) (hs.V'_lim hK_d_nn 1)
        Sanctions.S 1) :
    HasBoundedDerivOnS V_lim (hs.V'_lim hK_d_nn) K_d := by
  refine ⟨?_, ?_⟩
  · -- HasDerivOnS V_lim (V'_lim)
    intro x hx
    -- Case split: x ∈ {0}, x ∈ Ioo 0 1, x ∈ {1}.
    rcases hx with ⟨hx_low, hx_high⟩
    by_cases hx_0 : x = 0
    · rw [hx_0]; exact h_deriv_0
    · by_cases hx_1 : x = 1
      · rw [hx_1]; exact h_deriv_1
      · -- x ∈ (0, 1) — interior case via iter 11.
        have hx_Ioo : x ∈ Set.Ioo (0 : ℝ) 1 := by
          refine ⟨?_, ?_⟩
          · exact lt_of_le_of_ne hx_low (Ne.symm hx_0)
          · exact lt_of_le_of_ne hx_high hx_1
        have h_at : HasDerivAt (bcfExtendToR V_lim) (hs.V'_lim hK_d_nn x) x :=
          hs.V_lim_hasDerivAt_on_Ioo hK_d_nn hV_lim x hx_Ioo
        exact h_at.hasDerivWithinAt
  · -- Bound: |V'_lim x| ≤ K_d on S.
    exact hs.V'_lim_bound hK_d_nn

/-- **iter 12 corollary: limit packaged as a `C1Val K_d` element.**
Direct construction from `hasBoundedDerivOnS_limit`. -/
noncomputable def IsC1Cauchy.toC1ValLim
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    {s : ℕ → C1Val K_d} (hs : IsC1Cauchy s)
    {V_lim : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV_lim : Filter.Tendsto (fun n => (s n).V) Filter.atTop (nhds V_lim))
    (h_deriv_0 :
      HasDerivWithinAt (bcfExtendToR V_lim) (hs.V'_lim hK_d_nn 0)
        Sanctions.S 0)
    (h_deriv_1 :
      HasDerivWithinAt (bcfExtendToR V_lim) (hs.V'_lim hK_d_nn 1)
        Sanctions.S 1) :
    C1Val K_d where
  V := V_lim
  V' := hs.V'_lim hK_d_nn
  hasDeriv := hs.hasBoundedDerivOnS_limit hK_d_nn hV_lim h_deriv_0 h_deriv_1

/-! ## iter 13: substantive σ_dyn Lipschitz in C¹ norm

The signature theorem: under (i) IFT-derived strong-monotonicity-bound
on the difference of objective derivatives, expressed as
`c·|σ - σ'| ≤ |β_S·δ·(V_S.V'(F) - V_W.V'(F))|`, and (ii)
`F(x, σ')` lying in `S`, we get **Lipschitz σ_dyn in C¹ norm**:
`|σ - σ'| ≤ (β_S·δ/c) · c1dist V_S V_W`.

The premise (i) is the standard IFT-at-FOC outcome under strong
concavity + FOC interiority + C¹ value functions — it is given here
as a hypothesis so the user supplies it from whatever route works
at their concrete payoff class (smooth U_S + IFT-at-FOC, or via a
direct calculation in LQ, etc.). -/

variable (p : Sanctions.AbstractGame.Params)

/-- **iter 13: substantive σ_dyn Lipschitz in C¹ norm.**

Under the IFT-derived strong-monotonicity bound + `F(x, σ') ∈ S`,
`|σ - σ'| ≤ (β_S·δ/c) · c1dist V_S V_W`. The Lipschitz constant is
`β_S·δ/c` where `c` is the uniform strong-concavity modulus and `β_S·δ`
is the V_S-induced sensitivity from the Bellman integrand. -/
theorem sigma_dyn_lipschitz_in_C1
    {K_d c : ℝ} (hK_d_nn : 0 ≤ K_d) (hc_pos : 0 < c)
    (V_S V_W : C1Val K_d) (x : ℝ)
    (σ σ' : ℝ)
    (hF_mem : (1 - p.δ) * x + p.δ * σ' ∈ Sanctions.S)
    (h_bound : c * |σ - σ'|
        ≤ |p.β_S * p.δ *
            (V_S.V' ((1 - p.δ) * x + p.δ * σ')
              - V_W.V' ((1 - p.δ) * x + p.δ * σ'))|) :
    |σ - σ'| ≤ (p.β_S * p.δ / c) * C1Val.c1dist V_S V_W := by
  -- Unpack the absolute value: |β_S δ (V_S' - V_W') (F)| = β_S δ |V_S' - V_W'| (F)
  -- since β_S δ ≥ 0.
  have hβS_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have hβSδ_nn : 0 ≤ p.β_S * p.δ := mul_nonneg hβS_nn hδ_nn
  have h_bound_unfold :
      |p.β_S * p.δ * (V_S.V' ((1 - p.δ) * x + p.δ * σ')
                       - V_W.V' ((1 - p.δ) * x + p.δ * σ'))|
        = p.β_S * p.δ * |V_S.V' ((1 - p.δ) * x + p.δ * σ')
                          - V_W.V' ((1 - p.δ) * x + p.δ * σ')| := by
    rw [abs_mul, abs_of_nonneg hβSδ_nn]
  -- Pointwise diff ≤ sSup_{y ∈ S} of |V_S.V'(y) - V_W.V'(y)|.
  have h_pt_le_sup :
      |V_S.V' ((1 - p.δ) * x + p.δ * σ')
        - V_W.V' ((1 - p.δ) * x + p.δ * σ')|
        ≤ sSup ((fun y => |V_S.V' y - V_W.V' y|) '' Sanctions.S) := by
    apply le_csSup
    · exact deriv_diff_image_bddAbove hK_d_nn V_S V_W
    · exact ⟨(1 - p.δ) * x + p.δ * σ', hF_mem, rfl⟩
  -- sSup ≤ c1dist V_S V_W (one summand; BCF dist ≥ 0).
  have h_sup_le_c1 :
      sSup ((fun y => |V_S.V' y - V_W.V' y|) '' Sanctions.S)
        ≤ C1Val.c1dist V_S V_W := by
    unfold C1Val.c1dist
    have h_bcf_nn : 0 ≤ dist V_S.V V_W.V := _root_.dist_nonneg
    linarith
  -- Combine: c|σ-σ'| ≤ β_S δ * c1dist V_S V_W.
  have h_chain : c * |σ - σ'| ≤ p.β_S * p.δ * C1Val.c1dist V_S V_W := by
    calc c * |σ - σ'|
        ≤ |p.β_S * p.δ *
            (V_S.V' ((1 - p.δ) * x + p.δ * σ')
              - V_W.V' ((1 - p.δ) * x + p.δ * σ'))| := h_bound
      _ = p.β_S * p.δ * |V_S.V' ((1 - p.δ) * x + p.δ * σ')
                          - V_W.V' ((1 - p.δ) * x + p.δ * σ')| := h_bound_unfold
      _ ≤ p.β_S * p.δ *
            sSup ((fun y => |V_S.V' y - V_W.V' y|) '' Sanctions.S) :=
              mul_le_mul_of_nonneg_left h_pt_le_sup hβSδ_nn
      _ ≤ p.β_S * p.δ * C1Val.c1dist V_S V_W :=
              mul_le_mul_of_nonneg_left h_sup_le_c1 hβSδ_nn
  -- Divide by c (positive) to get |σ-σ'| ≤ (β_S δ / c) * c1dist V_S V_W.
  have h_div : |σ - σ'|
        ≤ (p.β_S * p.δ * C1Val.c1dist V_S V_W) / c :=
    le_div_iff₀ hc_pos |>.mpr (by linarith)
  calc |σ - σ'|
      ≤ (p.β_S * p.δ * C1Val.c1dist V_S V_W) / c := h_div
    _ = p.β_S * p.δ / c * C1Val.c1dist V_S V_W := by ring

end C1Val

/-! ## iter 14: `SigmaDynLipschitzOn_C1` Prop wrapper + IFT-bound
discharger of iter-13 form (Item A closure)

The audit-34 critique of iter 13 (`sigma_dyn_lipschitz_in_C1`):

> What is actually proved is a conditional inequality given an
> IFT-style strong-monotonicity bound. It is not yet a complete
> theorem saying: *primitive smooth payoff assumptions ⇒ σ_dyn is
> Lipschitz in C¹ value distance.*

This iter packages the iter-13 conditional into:

1. **`SigmaDynLipschitzOn_C1 L_σ`** — the C¹ analog of the BCF
   `SigmaDynLipschitzOn` from `LipschitzPrimitives.lean`. Quantifies
   `|σ_dyn V_S x a - σ_dyn V_W x a| ≤ L_σ · c1dist V_S V_W` over
   `(V_S, V_W) : C1Val K_d × C1Val K_d` and `(x, a) ∈ S × I`.

2. **`SigmaDynC1IFTBound c`** — the IFT-at-FOC primitive: at every
   `(V_S, V_W, x, a)` with `x ∈ S`, the dynamic Sender argmaxes
   `σ := σ_dyn V_S x a` and `σ' := σ_dyn V_W x a` satisfy
   `c · |σ - σ'| ≤ |β_S · δ · (V_S'(F) - V_W'(F))|` where
   `F := (1 - δ)·x + δ·σ'`. This is the algebraic content of the
   IFT-at-FOC under uniform strong concavity (modulus `c`) of the
   dynamic Sender objective in `s` — discharged at a concrete smooth
   payoff class by direct partial-derivative inspection of the FOC.

3. **`sigmaDynLipschitzOn_C1_of_IFT_bound`** — derives
   `SigmaDynLipschitzOn_C1 (β_S · δ / c)` from `SigmaDynC1IFTBound c`
   + `c > 0`, by applying iter-13 pointwise. **No `sorry`**;
   composition of iter-13 with `Sanctions.σ_dyn_mem` (gives
   `σ_dyn ∈ I`) and the convex-combination membership argument
   (`x ∈ [0,1]` + `σ_dyn ∈ [0,1]` + `δ ∈ [0,1]` ⇒ `F ∈ [0,1]`).

The audit's substantive-Lipschitz request — "primitive smooth payoff
assumptions ⇒ σ_dyn is Lipschitz in C¹ value distance" — is closed
**modulo** the IFT primitive itself. At any concrete smooth payoff
class, `SigmaDynC1IFTBound c` is computable by direct calculation
from the Sender objective's partial derivatives. The constant
`c = β_S · δ / L_σ` matches the canonical IFT-at-FOC formula. -/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **C¹ analog of `SigmaDynLipschitzOn`** (`LipschitzPrimitives.lean`).
The dynamic Sender argmax `σ_dyn V x a` is `L_σ`-Lipschitz in the
underlying value function `V`, measured in the C¹ distance `c1dist`,
when `(V_S, V_W) ∈ C1Val K_d × C1Val K_d` and `(x, a) ∈ S × I`.
The same feasible domain `S × I` is used by the two-carrier BCF form
`ValueClass2.SigmaDynLipschitzOn` (round BH1.2, 2026-10-06), which the
general-`F` Target row reads. -/
def SigmaDynLipschitzOn_C1 {K_d : ℝ} (L_σ : ℝ) : Prop :=
  ∀ V_S V_W : C1Val K_d, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
    |p.σ_dyn V_S.V x a - p.σ_dyn V_W.V x a|
      ≤ L_σ * C1Val.c1dist V_S V_W

/-- **C¹ IFT-at-FOC primitive.** At every `(V_S, V_W, x, a)` with
`x ∈ S` and `a ∈ I`, the dynamic Sender argmaxes
`σ := p.σ_dyn V_S.V x a` and `σ' := p.σ_dyn V_W.V x a` satisfy the
strong-monotonicity bound

```
c · |σ - σ'| ≤ |p.β_S · p.δ · (V_S.V'(F) - V_W.V'(F))|
```

where `F := (1 - p.δ) · x + p.δ · σ'` is the transition image at
the second argmax. This is the algebraic outcome of the IFT-at-FOC
under uniform strong concavity (modulus `c`) of the dynamic Sender
objective `a ↦ U_S(x, _, s) + β_S · V_S(F(x, s))` in `s` —
discharged at concrete smooth payoff classes by direct
partial-derivative calculation of the FOC. -/
def SigmaDynC1IFTBound {K_d : ℝ} (c : ℝ) : Prop :=
  ∀ V_S V_W : C1Val K_d, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
    c * |p.σ_dyn V_S.V x a - p.σ_dyn V_W.V x a|
      ≤ |p.β_S * p.δ *
          (V_S.V' ((1 - p.δ) * x + p.δ * (p.σ_dyn V_W.V x a))
            - V_W.V' ((1 - p.δ) * x + p.δ * (p.σ_dyn V_W.V x a)))|

/-- **Item A closure: discharger of `SigmaDynLipschitzOn_C1` from
`SigmaDynC1IFTBound`.** Direct application of iter-13
(`sigma_dyn_lipschitz_in_C1`) pointwise across all
`(V_S, V_W, x, a) ∈ C1Val × C1Val × S × I`. The `F ∈ S` membership
required by iter-13 follows from `x ∈ [0,1]` + `σ_dyn ∈ [0,1]` (via
`σ_dyn_mem`) + `δ ∈ [0,1]` (convex combination of two points in `[0,1]`
with weights in `[0,1]`). -/
theorem sigmaDynLipschitzOn_C1_of_IFT_bound
    {K_d c : ℝ} (hK_d_nn : 0 ≤ K_d) (hc_pos : 0 < c)
    (h_IFT : p.SigmaDynC1IFTBound (K_d := K_d) c) :
    p.SigmaDynLipschitzOn_C1 (K_d := K_d) (p.β_S * p.δ / c) := by
  intro V_S V_W x hx a ha
  -- F = (1 - δ)·x + δ·σ_W ∈ Sanctions.S = [0, 1] by convex combination.
  have hδ_mem_I : p.δ ∈ Sanctions.I := ⟨le_of_lt p.δ_mem.1, le_of_lt p.δ_mem.2⟩
  have h1δ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have hx_nn : 0 ≤ x := hx.1
  have hx_le : x ≤ 1 := hx.2
  have hσ_W_mem : p.σ_dyn V_W.V x a ∈ Sanctions.I :=
    p.σ_dyn_mem V_W.V x a
  have hσ_W_nn : 0 ≤ p.σ_dyn V_W.V x a := hσ_W_mem.1
  have hσ_W_le : p.σ_dyn V_W.V x a ≤ 1 := hσ_W_mem.2
  have hF_nn : 0 ≤ (1 - p.δ) * x + p.δ * (p.σ_dyn V_W.V x a) :=
    add_nonneg (mul_nonneg h1δ_nn hx_nn) (mul_nonneg hδ_nn hσ_W_nn)
  have hF_le : (1 - p.δ) * x + p.δ * (p.σ_dyn V_W.V x a) ≤ 1 := by
    have h1 : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
      mul_le_mul_of_nonneg_left hx_le h1δ_nn
    have h2 : p.δ * (p.σ_dyn V_W.V x a) ≤ p.δ * 1 :=
      mul_le_mul_of_nonneg_left hσ_W_le hδ_nn
    linarith
  have hF_mem : (1 - p.δ) * x + p.δ * (p.σ_dyn V_W.V x a) ∈ Sanctions.S :=
    ⟨hF_nn, hF_le⟩
  -- Apply iter-13. iter-13 lives in `Sanctions.C1Val` namespace (not
  -- `Params`), so dot-notation `p.sigma_dyn_lipschitz_in_C1` doesn't
  -- apply; we call it with the explicit `p` argument.
  exact Sanctions.C1Val.sigma_dyn_lipschitz_in_C1 p hK_d_nn hc_pos V_S V_W x
    (p.σ_dyn V_S.V x a) (p.σ_dyn V_W.V x a) hF_mem
    (h_IFT V_S V_W x hx a ha)

end Params
end AbstractGame

/-! ## iter 15: Banach contraction principle on `C1Val K_d`

`C1Val K_d` is not registered as a `PseudoMetricSpace` typeclass (the
`K_d ≥ 0` requirement complicates the typeclass; see the iter-5
note above). Instead, this iter provides a direct Banach
contraction principle expressed in terms of `c1dist` and `IsC1Cauchy`:
under a `q`-contraction on `C1Val K_d` with `0 ≤ q < 1`, the iteration
`T^n x₀` is `IsC1Cauchy` (and therefore has BCF + uniform-on-S
derivative limits via iters 7-12).

This is the **Banach iteration result on `C1Val K_d`** — the input
to `IsC1Cauchy.toC1ValLim` for constructing the fixed-point element
modulo `c1dist`.
-/

namespace C1Val

/-- **Contraction predicate for `C1Val K_d`.** `T : C1Val K_d →
C1Val K_d` is a `q`-contraction in the C¹ distance if
`c1dist (T c₁) (T c₂) ≤ q · c1dist c₁ c₂` for `0 ≤ q < 1`. -/
structure ContractingC1With (K_d : ℝ) (q : ℝ) (T : C1Val K_d → C1Val K_d) : Prop where
  q_nn : 0 ≤ q
  q_lt_one : q < 1
  contracts : ∀ c₁ c₂ : C1Val K_d,
    C1Val.c1dist (T c₁) (T c₂) ≤ q * C1Val.c1dist c₁ c₂

/-- **Banach iteration**: `banachIter T x₀ n := T^n x₀`. -/
noncomputable def banachIter {K_d : ℝ} (T : C1Val K_d → C1Val K_d)
    (x₀ : C1Val K_d) : ℕ → C1Val K_d
  | 0 => x₀
  | n + 1 => T (banachIter T x₀ n)

@[simp] theorem banachIter_zero {K_d : ℝ} (T : C1Val K_d → C1Val K_d)
    (x₀ : C1Val K_d) : banachIter T x₀ 0 = x₀ := rfl

@[simp] theorem banachIter_succ {K_d : ℝ} (T : C1Val K_d → C1Val K_d)
    (x₀ : C1Val K_d) (n : ℕ) :
    banachIter T x₀ (n + 1) = T (banachIter T x₀ n) := rfl

/-- **Geometric decay of consecutive iterate distances.**
`c1dist (s_n, s_{n+1}) ≤ q^n · c1dist (x₀, T x₀)`. -/
theorem banachIter_step_dist {K_d q : ℝ} {T : C1Val K_d → C1Val K_d}
    (hT : ContractingC1With K_d q T) (x₀ : C1Val K_d) (n : ℕ) :
    C1Val.c1dist (banachIter T x₀ n) (banachIter T x₀ (n + 1))
      ≤ q^n * C1Val.c1dist x₀ (T x₀) := by
  induction n with
  | zero =>
    simp [banachIter]
  | succ n ih =>
    have h_contract := hT.contracts (banachIter T x₀ n) (banachIter T x₀ (n + 1))
    have hq_nn := hT.q_nn
    have h_pow_nn : 0 ≤ q^n := pow_nonneg hq_nn n
    calc C1Val.c1dist (banachIter T x₀ (n + 1)) (banachIter T x₀ (n + 2))
        = C1Val.c1dist (T (banachIter T x₀ n)) (T (banachIter T x₀ (n + 1))) := rfl
      _ ≤ q * C1Val.c1dist (banachIter T x₀ n) (banachIter T x₀ (n + 1)) := h_contract
      _ ≤ q * (q^n * C1Val.c1dist x₀ (T x₀)) :=
          mul_le_mul_of_nonneg_left ih hq_nn
      _ = q^(n + 1) * C1Val.c1dist x₀ (T x₀) := by ring

/-- **Tight geometric-series bound on Banach iterates.** For any `p`
and any `k`, `c1dist (s_p, s_{p+k}) ≤ q^p · D · (1 - q^k) / (1 - q)`
where `D := c1dist (x₀, T x₀)`. Proof by induction on `k` using the
triangle inequality + the step bound. -/
theorem banachIter_dist_le_tight {K_d q : ℝ} {T : C1Val K_d → C1Val K_d}
    (hK_d_nn : 0 ≤ K_d)
    (hT : ContractingC1With K_d q T) (x₀ : C1Val K_d) :
    ∀ p k : ℕ,
      C1Val.c1dist (banachIter T x₀ p) (banachIter T x₀ (p + k))
        ≤ q^p * C1Val.c1dist x₀ (T x₀) * (1 - q^k) / (1 - q) := by
  have hq_nn := hT.q_nn
  have hq_lt := hT.q_lt_one
  have h1mq_pos : 0 < 1 - q := by linarith
  have hD_nn : 0 ≤ C1Val.c1dist x₀ (T x₀) :=
    C1Val.c1dist_nonneg hK_d_nn x₀ (T x₀)
  intro p k
  induction k with
  | zero =>
    -- c1dist (s_p, s_p) = 0; RHS = q^p · D · (1 - 1) / (1 - q) = 0.
    have h_self : C1Val.c1dist (banachIter T x₀ p) (banachIter T x₀ (p + 0)) = 0 := by
      rw [Nat.add_zero, C1Val.c1dist_self]
    rw [h_self]
    simp
  | succ k ih =>
    -- c1dist (s_p, s_{p+(k+1)}) ≤ c1dist (s_p, s_{p+k}) + c1dist (s_{p+k}, s_{p+k+1})
    --   ≤ q^p · D · (1 - q^k) / (1 - q) + q^(p+k) · D
    --   = q^p · D / (1 - q) · [(1 - q^k) + q^k · (1 - q)]
    --   = q^p · D / (1 - q) · (1 - q^(k+1))
    have h_eq : p + (k + 1) = (p + k) + 1 := by ring
    have h_tri := C1Val.c1dist_triangle hK_d_nn
      (banachIter T x₀ p)
      (banachIter T x₀ (p + k))
      (banachIter T x₀ (p + (k + 1)))
    have h_step := banachIter_step_dist hT x₀ (p + k)
    have h_step_dist :
        C1Val.c1dist (banachIter T x₀ (p + k)) (banachIter T x₀ (p + (k + 1)))
          ≤ q^(p + k) * C1Val.c1dist x₀ (T x₀) := by
      rw [h_eq]; exact h_step
    have h_pow_split : q^(p + k) = q^p * q^k := by rw [pow_add]
    have h_pow_p_nn : 0 ≤ q^p := pow_nonneg hq_nn p
    have h_pow_k_nn : 0 ≤ q^k := pow_nonneg hq_nn k
    calc C1Val.c1dist (banachIter T x₀ p) (banachIter T x₀ (p + (k + 1)))
        ≤ C1Val.c1dist (banachIter T x₀ p) (banachIter T x₀ (p + k))
          + C1Val.c1dist (banachIter T x₀ (p + k)) (banachIter T x₀ (p + (k + 1))) :=
          h_tri
      _ ≤ q^p * C1Val.c1dist x₀ (T x₀) * (1 - q^k) / (1 - q)
          + q^(p + k) * C1Val.c1dist x₀ (T x₀) :=
          add_le_add ih h_step_dist
      _ = q^p * C1Val.c1dist x₀ (T x₀) * (1 - q^(k + 1)) / (1 - q) := by
          rw [h_pow_split, pow_succ]
          field_simp
          ring

/-- **Standard (loose) geometric-series bound**: drop the `(1 - q^k)`
factor since `1 - q^k ≤ 1`. -/
theorem banachIter_dist_le {K_d q : ℝ} {T : C1Val K_d → C1Val K_d}
    (hK_d_nn : 0 ≤ K_d)
    (hT : ContractingC1With K_d q T) (x₀ : C1Val K_d) (p k : ℕ) :
    C1Val.c1dist (banachIter T x₀ p) (banachIter T x₀ (p + k))
      ≤ q^p * C1Val.c1dist x₀ (T x₀) / (1 - q) := by
  have hq_nn := hT.q_nn
  have hq_lt := hT.q_lt_one
  have h1mq_pos : 0 < 1 - q := by linarith
  have h1mq_nn : 0 ≤ 1 - q := le_of_lt h1mq_pos
  have hD_nn : 0 ≤ C1Val.c1dist x₀ (T x₀) :=
    C1Val.c1dist_nonneg hK_d_nn x₀ (T x₀)
  have h_pow_p_nn : 0 ≤ q^p := pow_nonneg hq_nn p
  have h_pow_k_nn : 0 ≤ q^k := pow_nonneg hq_nn k
  have h_tight := banachIter_dist_le_tight hK_d_nn hT x₀ p k
  have h_factor : (1 - q^k) ≤ 1 := by linarith
  have h_coef_nn : 0 ≤ q^p * C1Val.c1dist x₀ (T x₀) :=
    mul_nonneg h_pow_p_nn hD_nn
  -- q^p · D · (1 - q^k) ≤ q^p · D · 1.
  have h_prod_le :
      q^p * C1Val.c1dist x₀ (T x₀) * (1 - q^k)
        ≤ q^p * C1Val.c1dist x₀ (T x₀) := by
    have := mul_le_mul_of_nonneg_left h_factor h_coef_nn
    simpa using this
  -- Divide by (1 - q) > 0.
  have h_rhs_le :
      q^p * C1Val.c1dist x₀ (T x₀) * (1 - q^k) / (1 - q)
        ≤ q^p * C1Val.c1dist x₀ (T x₀) / (1 - q) :=
    div_le_div_of_nonneg_right h_prod_le h1mq_nn
  linarith [h_tight]

/-- **Helper: symmetric form of `banachIter_dist_le` covering both
`m ≤ n` and `n ≤ m` cases.** Standard `wlog`-free version. -/
theorem banachIter_dist_le_symm {K_d q : ℝ} {T : C1Val K_d → C1Val K_d}
    (hK_d_nn : 0 ≤ K_d)
    (hT : ContractingC1With K_d q T) (x₀ : C1Val K_d) (m n : ℕ) :
    C1Val.c1dist (banachIter T x₀ m) (banachIter T x₀ n)
      ≤ q^(min m n) * C1Val.c1dist x₀ (T x₀) / (1 - q) := by
  rcases le_total m n with h_mn | h_nm
  · -- m ≤ n: min = m. n = m + (n - m).
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_mn
    have h_min : min m (m + k) = m := by omega
    rw [h_min]
    exact banachIter_dist_le hK_d_nn hT x₀ m k
  · -- n ≤ m: min = n. m = n + (m - n). Use symmetry.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_nm
    have h_min : min (n + k) n = n := by omega
    rw [h_min, C1Val.c1dist_comm]
    exact banachIter_dist_le hK_d_nn hT x₀ n k

/-- **Banach iteration is `IsC1Cauchy`.** Given a `q`-contraction `T`
on `C1Val K_d` with `0 ≤ q < 1`, the iteration `T^n x₀` is Cauchy in
`c1dist`: pick `N` with `q^N · D / (1 - q) < ε`. -/
theorem banachIter_isC1Cauchy {K_d q : ℝ} {T : C1Val K_d → C1Val K_d}
    (hK_d_nn : 0 ≤ K_d)
    (hT : ContractingC1With K_d q T) (x₀ : C1Val K_d) :
    IsC1Cauchy (banachIter T x₀) := by
  intro ε hε
  have hq_nn := hT.q_nn
  have hq_lt := hT.q_lt_one
  have h1mq_pos : 0 < 1 - q := by linarith
  have h1mq_nn : 0 ≤ 1 - q := le_of_lt h1mq_pos
  set D : ℝ := C1Val.c1dist x₀ (T x₀) with hD_def
  have hD_nn : 0 ≤ D := C1Val.c1dist_nonneg hK_d_nn x₀ (T x₀)
  set C : ℝ := D + 1 with hC_def
  have hC_pos : 0 < C := by linarith
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  -- Find N : ℕ with q^N · C / (1 - q) < ε, equivalently q^N < ε (1 - q) / C.
  set δ : ℝ := ε * (1 - q) / C with hδ_def
  have hδ_pos : 0 < δ := div_pos (mul_pos hε h1mq_pos) hC_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, q^N < δ := by
    by_cases hq_zero : q = 0
    · refine ⟨1, ?_⟩
      rw [hq_zero, pow_one]; exact hδ_pos
    exact exists_pow_lt_of_lt_one hδ_pos hq_lt
  refine ⟨N, fun m n hm hn => ?_⟩
  -- Use the symmetric bound.
  have h_bound := banachIter_dist_le_symm hK_d_nn hT x₀ m n
  -- q^min(m,n) ≤ q^N since min(m, n) ≥ N.
  have h_min_ge : N ≤ min m n := le_min hm hn
  have h_q_in : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq_nn, le_of_lt hq_lt⟩
  have h_pow_min_le_pow_N : q^(min m n) ≤ q^N :=
    pow_le_pow_of_le_one h_q_in.1 h_q_in.2 h_min_ge
  have h_step_le :
      q^(min m n) * D / (1 - q) ≤ q^N * D / (1 - q) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h_pow_min_le_pow_N hD_nn) h1mq_nn
  have h_D_le_C : D ≤ C := by linarith
  have h_C_step :
      q^N * D / (1 - q) ≤ q^N * C / (1 - q) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_D_le_C (pow_nonneg hq_nn N)) h1mq_nn
  -- q^N · C / (1 - q) < ε: from q^N < ε(1-q)/C.
  rw [hδ_def] at hN
  have h_cross : q^N * C < ε * (1 - q) := by
    have h_step : q^N * C < (ε * (1 - q) / C) * C :=
      (mul_lt_mul_iff_of_pos_right hC_pos).mpr hN
    rwa [div_mul_cancel₀ _ hC_ne] at h_step
  have h_final : q^N * C / (1 - q) < ε := by
    rw [div_lt_iff₀ h1mq_pos]
    linarith
  calc C1Val.c1dist (banachIter T x₀ m) (banachIter T x₀ n)
      ≤ q^(min m n) * D / (1 - q) := h_bound
    _ ≤ q^N * D / (1 - q) := h_step_le
    _ ≤ q^N * C / (1 - q) := h_C_step
    _ < ε := h_final

end C1Val

/-! ## iter 16: symmetric `AlphaOnLipschitzOn_C1` + IFT-bound discharger

The leader joint-Bellman argmax `α_on` analog in C¹ ambient. Parametric
over the user-supplied `α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ`
(typically defined via `Classical.choose` of an argmax existence
hypothesis for the leader joint Bellman integrand on C¹ data).

Same template as iter 14 (sigma):
* `AlphaOnLipschitzOn_C1` — Lipschitz Prop wrapper.
* `AlphaOnC1IFTBound` — IFT-at-FOC primitive (`c · |α - α'| ≤
  IFT-derived sensitivity bound`).
* `alphaOnLipschitzOn_C1_of_IFT_bound` — direct discharge.

The IFT primitive for the leader has two sensitivity terms (one from
V_T via the continuation `β_T · V_T(F)`, one from V_S via the σ-mediated
stage payoff). Both compose into the joint `(L_α_VT, L_α_VS)` constants
of the Lipschitz form.
-/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **C¹ analog of the BCF `AlphaOnLipschitzOn` from
`LipschitzPrimitives.lean`.** The leader argmax `α_on_C1 V_T V_S x`
is jointly `(L_α_VT, L_α_VS)`-Lipschitz in `(V_T, V_S)` over
`C1Val K_d × C1Val K_d` w.r.t. `c1dist`, restricted to feasible
states `x ∈ S`. The two-carrier BCF form `ValueClass2.AlphaOnLipschitzOn`
(round BH1.2, 2026-10-06) is restricted to feasible states in the same way. -/
def AlphaOnLipschitzOn_C1 {K_d : ℝ}
    (α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ)
    (L_α_VT L_α_VS : ℝ) : Prop :=
  ∀ V_T V_T' V_S V_S' : C1Val K_d, ∀ x ∈ Sanctions.S,
    |α_on_C1 V_T V_S x - α_on_C1 V_T' V_S' x|
      ≤ L_α_VT * C1Val.c1dist V_T V_T' + L_α_VS * C1Val.c1dist V_S V_S'

/-- **C¹ IFT-at-FOC primitive for the leader argmax.** Under uniform
strong concavity of the leader joint-Bellman integrand `a ↦
joint_T_top_integrand V_T V_S x a` in `a` (modulus `c > 0`), the
strong-monotonicity bound is

```
c · |α - α'| ≤ |L_VT_sens · (V_T.V'(F_α') - V_T'.V'(F_α'))|
              + |L_VS_sens · sup_{y ∈ S} |V_S.V'(y) - V_S'.V'(y)| |
```

where `F_α' := (1 - δ)·x + δ · σ_dyn_top V_S x α'` is the transition at
the second argmax, `L_VT_sens` is the V_T-induced FOC sensitivity
(scale `β_T · δ`), and `L_VS_sens` is the V_S-induced FOC sensitivity
(scale `β_T · δ · σ_dyn_lip_const + L_U_a · σ_dyn_lip_const`).

The bound is the algebraic outcome of the IFT-at-FOC under joint C¹
smoothness — discharged at concrete smooth payoff classes by direct
partial-derivative calculation of the leader FOC.

We package the bound in a generic form: the user supplies the two
sensitivities `L_VT_sens, L_VS_sens` and the bound holds at every
`(V_T, V_T', V_S, V_S', x ∈ S)`. -/
def AlphaOnC1IFTBound {K_d : ℝ}
    (α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ)
    (c L_VT_sens L_VS_sens : ℝ) : Prop :=
  ∀ V_T V_T' V_S V_S' : C1Val K_d, ∀ x ∈ Sanctions.S,
    c * |α_on_C1 V_T V_S x - α_on_C1 V_T' V_S' x|
      ≤ L_VT_sens * C1Val.c1dist V_T V_T'
        + L_VS_sens * C1Val.c1dist V_S V_S'

/-- **iter 16 discharger: `AlphaOnLipschitzOn_C1` from
`AlphaOnC1IFTBound`.** Direct division by `c > 0`. The Lipschitz
constants are `L_α_VT = L_VT_sens / c` and `L_α_VS = L_VS_sens / c`,
mirroring iter 14's `L_σ = β_S · δ / c`. -/
theorem alphaOnLipschitzOn_C1_of_IFT_bound
    {K_d c L_VT_sens L_VS_sens : ℝ}
    (hc_pos : 0 < c)
    (hL_VT_nn : 0 ≤ L_VT_sens) (hL_VS_nn : 0 ≤ L_VS_sens)
    {α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ}
    (h_IFT : AlphaOnC1IFTBound α_on_C1 c L_VT_sens L_VS_sens) :
    AlphaOnLipschitzOn_C1 α_on_C1 (L_VT_sens / c) (L_VS_sens / c) := by
  intro V_T V_T' V_S V_S' x hx
  have h_bound := h_IFT V_T V_T' V_S V_S' x hx
  -- h_bound : c · |α - α'| ≤ L_VT_sens · c1dist V_T V_T' + L_VS_sens · c1dist V_S V_S'.
  -- Divide both sides by c (positive).
  have h_div : |α_on_C1 V_T V_S x - α_on_C1 V_T' V_S' x|
        ≤ (L_VT_sens * C1Val.c1dist V_T V_T'
            + L_VS_sens * C1Val.c1dist V_S V_S') / c := by
    rw [le_div_iff₀ hc_pos]
    linarith
  calc |α_on_C1 V_T V_S x - α_on_C1 V_T' V_S' x|
      ≤ (L_VT_sens * C1Val.c1dist V_T V_T'
          + L_VS_sens * C1Val.c1dist V_S V_S') / c := h_div
    _ = (L_VT_sens / c) * C1Val.c1dist V_T V_T'
        + (L_VS_sens / c) * C1Val.c1dist V_S V_S' := by
        field_simp

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
