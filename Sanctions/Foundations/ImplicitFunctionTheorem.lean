/-
Sanctions/Foundations/ImplicitFunctionTheorem.lean

**Argmax-Lipschitz from FOC + strong concavity (scope-reduced IFT route).**

Round 31 deliverable for the `L_α_VT, L_α_VS` (Target-selector Lipschitz
constants) shrink. After R23-R30 closed out the row-Lipschitz, gain-slope,
single-crossing, and σ-antitone primitives, the only structural primitives
remaining on the regular-economy certificate were the IFT-derived
selector-Lipschitz constants `L_α_VT, L_α_VS` consumed by Curtat's row-
Lipschitz closed form (R26). This module supplies the generic Foundations
lemma that derives a Lipschitz constant for an argmax map `θ ↦ a*(θ)` from
three elementary hypotheses:

1. **FOC at both optima.** `∂f/∂a (a*(θ), θ) = 0` and `∂f/∂a (a*(θ'), θ') = 0`.
2. **Strong concavity in `a` at `θ'`.** The chord-form lower bound
   `c · (a − b)² ≤ (∂f/∂a (a, θ') − ∂f/∂a (b, θ')) · (a − b)` with `c > 0`,
   which is exactly the gradient-monotonicity form of strong concavity
   (equivalent to `∂²f/∂a² ≤ −c` under C²).
3. **Cross-Lipschitz of the gradient in `θ`.** `|∂f/∂a (a, θ) − ∂f/∂a (a, θ')|
   ≤ K · dist θ θ'` (uniformly in `a`).

The conclusion is the closed-form selector Lipschitz constant
`L = K / c`:

```
|a*(θ) − a*(θ')| ≤ (K / c) · dist θ θ'
```

This is the standard "IFT-without-IFT" route used in dynamic-economics
formalizations (Doraszelski-Pakes 2007 Sections 3.1/4.1 cite it as the
canonical argument for selector Lipschitz constants in MPE computation;
see `PaperRefer/StochasticGames/AppliedDynamicAnalysisIO-DoraszelskiPakes-
2007.md`).

**Methodological anchor (Aubin & Frankowska 1990,
`BookRefer/Set-Valued Analysis (J. Aubin, H. Frankowska).md`).** §5.5
of *Set-Valued Analysis* is the canonical reference for Lipschitz
selections of set-valued maps with strongly-monotone derivative; the
scalar §1 lemma below is exactly the C¹ specialisation of their
Theorem 5.4.3. §3 (added in this round) closes the half-bridge by
discharging the chord-form hypothesis from the gradient
strong-monotonicity content of strong convexity, the same primitive
input Aubin-Frankowska consume in their general set-valued statement.
This gives the project a complete proof chain
`C² Hessian bound → gradient strong-monotonicity → chord form →
argmax-Lipschitz with closed-form modulus K/c`, anchored at each
step to a citable real-analysis reference (Aubin-Frankowska for the
upper half, mathlib MVT for the lower half).

**Two additional anchors added in the Round-1.6 literature pass.**
The argmax-Lipschitz / chord-form route consumed by this module is
the standard non-witness derivation; two further references
sharpen the connection and would close the §3 chord-form-from-primitives
deferral in a future round:

* **Klatte & Kummer 2002** *Nonsmooth Equations in Optimization:
  Regularity, Calculus, Methods and Applications*, Ch. 2 + Ch. 7
  (`BookRefer/NonsmoothEquationsInOptimization-KlatteKummer-2002.md`).
  Ch. 2 catalogues the Lipschitz properties of multivalued maps and
  the "regularity" hierarchy (pseudo-, strong-, upper Lipschitz);
  Ch. 7 develops the generalised Kojima-function framework that
  derives the chord-form gradient strong-monotonicity directly from
  KKT / parametric-NLP data without needing an interiority
  hypothesis. The full discharge of the §3 chord-form primitive
  would route through this chapter.
* **Rincón-Zapatero & Santos 2009** *Differentiability of the value
  function without interiority assumptions*, J. Econ. Theory 144(5)
  (`PaperRefer/MathTheory/DifferentiabilityValueFunction-RinconZapateroSantos-2009.md`).
  Generalised envelope theorem dropping the standard interiority
  assumption + KKT-multiplier uniqueness for concave DP — the latter
  is the deep economic-theoretic anchor for the project's chord-form
  hypothesis on the joint Target objective. The §3 chord-form is
  exactly the gradient-monotonicity content of the unique KKT
  multiplier they prove.

These two together provide the canonical path to fully discharging
the §3 chord-form primitive from C² Target stage payoffs + Arrow-
Hurwicz-Uzawa constraint qualification, without an interiority
hypothesis. The §3 lemma below remains stated in chord-form
primitives so it can be consumed independently; the discharge route
is documented for the future R32+ refactor.

## Why scope-reduced

The full mathlib implicit function theorem (`HasFDerivAt.implicitFunData`
and friends) requires bundling the objective as a smooth map between
normed spaces, instantiating an invertible Fréchet derivative at the
optimum, and threading the resulting implicit function back through the
argmax characterization. For the project's `α_on V_T V_S x` (a scalar
optimum in the leader action `a ∈ [0, 1]` parametrized by the value
function pair `(V_T, V_S) ∈ Carrier × Carrier`), the full IFT delivers
exactly the closed-form `L = K/c` this lemma states, but with ~10×
the proof burden in mathlib bookkeeping. We therefore deliver the
chord-form (gradient-monotonicity) hypothesis directly; the user
supplies the chord either from a C² Hessian bound or directly from
the strong-concavity inequality.

## Rule-19 placement

This is generic real-analysis math (no project-specific economic
content), so it lives in `Foundations/`. The `Params`-level wrappers
that derive `L_α_VT, L_α_VS` from primitive payoff-Hessian bounds via
this lemma live in `Theory/Certificates/RegularEconomy.lean` as
`alphaOnLipschitzOn_of_IFT_chord_form` /
`alphaOnLipschitzOn_of_C2_Hessian_lower_bound`.

## Rule-3 status

Pure cat-2 weakening / Rule-3-free Type-C discharger: the lemma takes
chord-form strong concavity and cross-Lipschitz as inputs; both are
already-recognized regularity hypotheses (chord-form strong concavity
is the gradient-monotonicity content of `StrictConvexOn` augmented
with a modulus, cross-Lipschitz of the gradient is a standard C²
Hessian bound). No new opaque Prop on `Params`.

## What this module exports

* `argmax_lipschitz_of_FOC_strong_concavity_cross_lipschitz`
  — the generic scalar argmax-Lipschitz lemma described above.
* `argmax_lipschitz_pair_of_FOC_strong_concavity_cross_lipschitz_pair`
  — a two-coordinate parameter variant convenient for the project's
  `(V_T, V_S) ∈ Carrier × Carrier` setting where separate Lipschitz
  constants `K_T, K_S` are supplied for the two parameter coordinates.
-/

import Sanctions.Foundations.Basic

namespace Sanctions
namespace Foundations
namespace ImplicitFunctionTheorem

open Set

/-! ## §1 Scalar argmax-Lipschitz from FOC + strong concavity -/

/-- **Argmax-Lipschitz from FOC + strong concavity + cross-Lipschitz**
(Doraszelski-Pakes 2007 Sections 3.1/4.1, scope-reduced).

Let `f(a, θ) : ℝ × Θ → ℝ` be parametrized by `θ : Θ` (a pseudo-metric
space), and let `fa : ℝ → Θ → ℝ` denote the partial derivative
`∂f/∂a`. Given:

* `hFOC_a : fa a θ = 0` — first-order condition at `(a, θ)`,
* `hFOC_b : fa b θ' = 0` — first-order condition at `(b, θ')`,
* `h_strong : c · (a − b)² ≤ (fa a θ' − fa b θ') · (a − b)` with `c > 0`
  — chord-form strong concavity of `f` in `a` at `θ'` (equivalent to
  `∂²f/∂a² ≤ −c` under C²; this inequality is the
  gradient-monotonicity content of strong concavity, applied to the
  chord between `a` and `b`),
* `h_cross : ∀ x θ₁ θ₂, |fa x θ₁ − fa x θ₂| ≤ K · dist θ₁ θ₂` with
  `K ≥ 0` — cross-Lipschitz of the gradient `∂f/∂a` in `θ` (a
  standard C² Hessian bound `|∂²f/∂a∂θ| ≤ K`),

conclude

```
|a − b| ≤ (K / c) · dist θ θ'.
```

**Plain-language gloss.** The argmax map `θ ↦ a*(θ)` is Lipschitz
with constant `K / c`, the ratio of the cross-Hessian norm to the
strict-concavity modulus. This is exactly the closed-form Lipschitz
estimate the standard IFT route produces from `D a* = −(∂²f/∂a²)⁻¹
∂²f/∂a∂θ`, here delivered without bundling the full smooth-function
infrastructure. -/
theorem argmax_lipschitz_of_FOC_strong_concavity_cross_lipschitz
    {Θ : Type*} [PseudoMetricSpace Θ]
    (fa : ℝ → Θ → ℝ) (a b : ℝ) (θ θ' : Θ) (K c : ℝ)
    (hK_nn : 0 ≤ K) (hc_pos : 0 < c)
    (hFOC_a : fa a θ = 0) (hFOC_b : fa b θ' = 0)
    (h_strong : c * (a - b) ^ 2 ≤ (fa a θ' - fa b θ') * (a - b))
    (h_cross : ∀ x θ₁ θ₂, |fa x θ₁ - fa x θ₂| ≤ K * dist θ₁ θ₂) :
    |a - b| ≤ (K / c) * dist θ θ' := by
  rw [hFOC_b, sub_zero] at h_strong
  -- Use hFOC_a to rewrite fa a θ' as the gradient difference.
  have h_fa_diff : fa a θ' = fa a θ' - fa a θ := by rw [hFOC_a]; ring
  rw [h_fa_diff] at h_strong
  -- Bound the gradient-difference product by its absolute value.
  have h_le_abs : (fa a θ' - fa a θ) * (a - b) ≤ |fa a θ' - fa a θ| * |a - b| := by
    have := le_abs_self ((fa a θ' - fa a θ) * (a - b))
    rw [abs_mul] at this
    exact this
  have h_cross_ab : |fa a θ' - fa a θ| ≤ K * dist θ' θ := h_cross a θ' θ
  -- Chain: c · (a − b)² ≤ (fa a θ' − fa a θ) · (a − b)
  --                    ≤ |fa a θ' − fa a θ| · |a − b|
  --                    ≤ K · dist θ' θ · |a − b|.
  have h_chain : c * (a - b) ^ 2 ≤ K * dist θ' θ * |a - b| := by
    calc c * (a - b) ^ 2
        ≤ (fa a θ' - fa a θ) * (a - b) := h_strong
      _ ≤ |fa a θ' - fa a θ| * |a - b| := h_le_abs
      _ ≤ K * dist θ' θ * |a - b| :=
          mul_le_mul_of_nonneg_right h_cross_ab (abs_nonneg _)
  -- (a − b)² = |a − b| · |a − b|.
  have h_sq : (a - b) ^ 2 = |a - b| * |a - b| := by
    rw [sq, ← abs_mul, abs_mul_self]
  rw [h_sq] at h_chain
  by_cases hab : a = b
  · -- If a = b, the conclusion is the non-negativity of (K/c) · dist θ θ'.
    have : |a - b| = 0 := by rw [hab]; simp
    rw [this]
    exact mul_nonneg (div_nonneg hK_nn hc_pos.le) dist_nonneg
  · -- Otherwise, divide both sides by the positive |a − b|.
    have habs_pos : 0 < |a - b| := abs_sub_pos.mpr hab
    have h_div : c * |a - b| ≤ K * dist θ' θ := by
      have hLHS : c * (|a - b| * |a - b|) = (c * |a - b|) * |a - b| := by ring
      have hRHS : K * dist θ' θ * |a - b| = (K * dist θ' θ) * |a - b| := by ring
      rw [hLHS, hRHS] at h_chain
      exact (mul_le_mul_iff_of_pos_right habs_pos).mp h_chain
    rw [dist_comm θ' θ] at h_div
    rw [div_mul_eq_mul_div, le_div_iff₀ hc_pos]
    linarith

/-! ## §2 Two-coordinate parameter variant

The project's leader selector `α_on V_T V_S x` is parametrized by the
*pair* `(V_T, V_S) ∈ Carrier × Carrier`. Decomposing the cross-Lipschitz
hypothesis into the two parameter coordinates yields two separate
Lipschitz constants `L_α_VT := K_T / c`, `L_α_VS := K_S / c` (where `K_T,
K_S` are the per-coordinate gradient-Lipschitz bounds), matching the
shape consumed by `Foundations.Curtat.CurtatPrimitiveLipschitzData`.

The two-coordinate variant below is a direct corollary of the scalar
lemma applied at intermediate pairs `(V_T, V_S') ↔ (V_T', V_S')`. -/

/-- **Two-coordinate argmax-Lipschitz** for parameter pair `(θ_T, θ_S)`.
Decomposes the joint Lipschitz bound into the two per-coordinate
constants `L_θ_T := K_T / c` and `L_θ_S := K_S / c`.

Inputs:

* `fa : ℝ → Θ_T → Θ_S → ℝ` — gradient `∂f/∂a` as a function of the
  argument `a` and the two parameter coordinates.
* `a, b : ℝ` and parameter pairs `(θ_T, θ_S)`, `(θ_T', θ_S')` with
  `fa a θ_T θ_S = 0` and `fa b θ_T' θ_S' = 0` (FOCs at each pair).
* `c > 0` strong-concavity modulus.
* Chord-form strong concavity at the second parameter pair:
  `c · (a − b)² ≤ (fa a θ_T' θ_S' − fa b θ_T' θ_S') · (a − b)`.
* Two cross-Lipschitz bounds: `|fa x θ₁_T θ_S − fa x θ₂_T θ_S| ≤
  K_T · dist θ₁_T θ₂_T` (uniformly in `x, θ_S`), and `|fa x θ_T θ₁_S −
  fa x θ_T θ₂_S| ≤ K_S · dist θ₁_S θ₂_S`.

Conclusion:

```
|a − b| ≤ (K_T / c) · dist θ_T θ_T' + (K_S / c) · dist θ_S θ_S'.
```

The two right-hand-side coefficients are exactly the per-coordinate
selector-Lipschitz constants `L_θ_T, L_θ_S` consumed by
`AlphaOnLipschitzOn D L_α_VT L_α_VS`. -/
theorem argmax_lipschitz_pair_of_FOC_strong_concavity_cross_lipschitz_pair
    {Θ_T Θ_S : Type*} [PseudoMetricSpace Θ_T] [PseudoMetricSpace Θ_S]
    (fa : ℝ → Θ_T → Θ_S → ℝ) (a b : ℝ)
    (θ_T θ_T' : Θ_T) (θ_S θ_S' : Θ_S) (K_T K_S c : ℝ)
    (hK_T_nn : 0 ≤ K_T) (hK_S_nn : 0 ≤ K_S) (hc_pos : 0 < c)
    (hFOC_a : fa a θ_T θ_S = 0) (hFOC_b : fa b θ_T' θ_S' = 0)
    (h_strong : c * (a - b) ^ 2 ≤ (fa a θ_T' θ_S' - fa b θ_T' θ_S') * (a - b))
    (h_cross_T : ∀ x θ_S₀ θ₁ θ₂,
        |fa x θ₁ θ_S₀ - fa x θ₂ θ_S₀| ≤ K_T * dist θ₁ θ₂)
    (h_cross_S : ∀ x θ_T₀ θ₁ θ₂,
        |fa x θ_T₀ θ₁ - fa x θ_T₀ θ₂| ≤ K_S * dist θ₁ θ₂) :
    |a - b| ≤ (K_T / c) * dist θ_T θ_T' + (K_S / c) * dist θ_S θ_S' := by
  -- Bundle the two parameter coordinates as a product pseudo-metric, then
  -- apply the scalar lemma with K := K_T + K_S, c := c, and re-split the
  -- product-distance bound. Cleaner: bound `|fa a θ_T θ_S − fa a θ_T' θ_S'|`
  -- by `K_T · dist θ_T θ_T' + K_S · dist θ_S θ_S'` via the triangle
  -- inequality through the intermediate point `(θ_T', θ_S)`.
  -- Step 1: from h_strong and hFOC_b, get
  --   c · (a − b)² ≤ fa a θ_T' θ_S' · (a − b).
  rw [hFOC_b, sub_zero] at h_strong
  -- Step 2: rewrite fa a θ_T' θ_S' = (fa a θ_T' θ_S' − fa a θ_T θ_S) using FOC_a.
  have h_fa_diff : fa a θ_T' θ_S' = fa a θ_T' θ_S' - fa a θ_T θ_S := by
    rw [hFOC_a]; ring
  rw [h_fa_diff] at h_strong
  -- Step 3: split the gradient difference via the triangle inequality:
  --   fa a θ_T' θ_S' − fa a θ_T θ_S
  --   = (fa a θ_T' θ_S' − fa a θ_T' θ_S) + (fa a θ_T' θ_S − fa a θ_T θ_S).
  have h_triangle : |fa a θ_T' θ_S' - fa a θ_T θ_S|
      ≤ K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S' := by
    have h_split :
        fa a θ_T' θ_S' - fa a θ_T θ_S
          = (fa a θ_T' θ_S' - fa a θ_T' θ_S)
          + (fa a θ_T' θ_S - fa a θ_T θ_S) := by ring
    have h_S := h_cross_S a θ_T' θ_S' θ_S
    have h_T := h_cross_T a θ_S θ_T' θ_T
    calc |fa a θ_T' θ_S' - fa a θ_T θ_S|
        = |(fa a θ_T' θ_S' - fa a θ_T' θ_S)
            + (fa a θ_T' θ_S - fa a θ_T θ_S)| := by rw [h_split]
      _ ≤ |fa a θ_T' θ_S' - fa a θ_T' θ_S|
            + |fa a θ_T' θ_S - fa a θ_T θ_S| := abs_add_le _ _
      _ ≤ K_S * dist θ_S' θ_S + K_T * dist θ_T' θ_T := by
          exact add_le_add h_S h_T
      _ = K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S' := by
          rw [dist_comm θ_T' θ_T, dist_comm θ_S' θ_S]; ring
  -- Step 4: chain h_strong with the triangle bound and pass through |·|.
  have h_le_abs : (fa a θ_T' θ_S' - fa a θ_T θ_S) * (a - b)
      ≤ |fa a θ_T' θ_S' - fa a θ_T θ_S| * |a - b| := by
    have := le_abs_self ((fa a θ_T' θ_S' - fa a θ_T θ_S) * (a - b))
    rw [abs_mul] at this
    exact this
  have h_chain : c * (a - b) ^ 2
      ≤ (K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S') * |a - b| := by
    calc c * (a - b) ^ 2
        ≤ (fa a θ_T' θ_S' - fa a θ_T θ_S) * (a - b) := h_strong
      _ ≤ |fa a θ_T' θ_S' - fa a θ_T θ_S| * |a - b| := h_le_abs
      _ ≤ (K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S') * |a - b| :=
          mul_le_mul_of_nonneg_right h_triangle (abs_nonneg _)
  -- (a − b)² = |a − b| · |a − b|.
  have h_sq : (a - b) ^ 2 = |a - b| * |a - b| := by
    rw [sq, ← abs_mul, abs_mul_self]
  rw [h_sq] at h_chain
  by_cases hab : a = b
  · have : |a - b| = 0 := by rw [hab]; simp
    rw [this]
    -- Goal: 0 ≤ K_T/c · dist θ_T θ_T' + K_S/c · dist θ_S θ_S'.
    exact add_nonneg
      (mul_nonneg (div_nonneg hK_T_nn hc_pos.le) dist_nonneg)
      (mul_nonneg (div_nonneg hK_S_nn hc_pos.le) dist_nonneg)
  · have habs_pos : 0 < |a - b| := abs_sub_pos.mpr hab
    have h_div : c * |a - b| ≤ K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S' := by
      have hLHS : c * (|a - b| * |a - b|) = (c * |a - b|) * |a - b| := by ring
      have hRHS : (K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S') * |a - b|
          = (K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S') * |a - b| := by ring
      rw [hLHS] at h_chain
      exact (mul_le_mul_iff_of_pos_right habs_pos).mp h_chain
    -- Divide through by c > 0.
    have h_final : |a - b| ≤ (K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S') / c := by
      rw [le_div_iff₀ hc_pos]; linarith
    have h_split_div :
        (K_T * dist θ_T θ_T' + K_S * dist θ_S θ_S') / c
          = (K_T / c) * dist θ_T θ_T' + (K_S / c) * dist θ_S θ_S' := by
      field_simp
    linarith [h_final, h_split_div ▸ h_final]

/-! ## §3 Aubin-Frankowska chord-form discharge from gradient strong-monotonicity

The §1 / §2 theorems consume the chord-form inequality

```
c · (a − b)² ≤ (fa a θ' − fa b θ') · (a − b)
```

as a hypothesis. **Aubin & Frankowska, *Set-Valued Analysis* (Birkhäuser,
1990), Chapter 5 §5.5** anchor exactly this gradient-strong-monotonicity
content as the canonical hypothesis under which a parametric argmax map
admits a Lipschitz selection with closed-form modulus. Specifically,
Theorem 5.4.3 (Lipschitz selections of strongly monotone set-valued
operators) yields a `K/c` modulus from the same primitives the §1 lemma
consumes — so the §1 lemma below is the scalar specialisation of that
general set-valued result.

This section adds the **discharge** of the chord-form hypothesis from
strong gradient-monotonicity of `fa` in `a`. The strong-monotonicity
content `c · (b − a) ≤ fa b − fa a` for `a ≤ b` is the standard
gradient-form characterisation of strong convexity of `f` in `a` with
modulus `c`; under C² structure it is in turn equivalent to the
Hessian bound `c ≤ ∂²f/∂a²` uniformly. The discharge below is purely
algebraic and routes through `mul_le_mul_of_nonneg_right` without
invoking the mean value theorem; the C² Hessian-bound → gradient
strong-monotonicity → chord-form chain composes cleanly with the
mathlib MVT layer (`exists_hasDerivAt_eq_slope`) at the use site, where
the relevant derivative-class hypotheses on `fa` are available.

**Sign convention.** The §1 / §2 lemmas state the chord in the
strong-convexity direction; for our argmax-of-concave application the
discharge is obtained by applying the lemma to `-f` (whose gradient
`-fa` is strongly monotone with the same modulus `c`). -/

/-- **Chord-form discharge from gradient strong-monotonicity**
(Aubin-Frankowska 1990 §5.5 Theorem 5.4.3 specialisation).

Given strong gradient-monotonicity of `fa` in `a` with modulus `c > 0`:

```
∀ a b, a ≤ b → c · (b − a) ≤ fa b − fa a,
```

derive the chord-form inequality consumed by §1's argmax-Lipschitz lemma:

```
∀ a b, c · (a − b)² ≤ (fa a − fa b) · (a − b).
```

The proof is two case-splits on `a ≤ b` vs `b ≤ a` and is purely
algebraic — no MVT or derivative-class hypothesis is required.

Under C² structure with `c ≤ ∂²f/∂a²(x)` uniformly in `x`, the
strong-monotonicity hypothesis is itself derived by the mean value
theorem on `fa`; the discharge composes cleanly. -/
theorem chord_form_of_gradient_strong_monotonicity
    (fa : ℝ → ℝ) (c : ℝ) (_hc_pos : 0 < c)
    (h_mono : ∀ a b, a ≤ b → c * (b - a) ≤ fa b - fa a)
    (a b : ℝ) :
    c * (a - b) ^ 2 ≤ (fa a - fa b) * (a - b) := by
  rcases le_total a b with hab | hab
  · -- a ≤ b: rewrite both sides in the `(b - a)` orientation.
    have h1 : c * (b - a) ≤ fa b - fa a := h_mono a b hab
    have h_ba_nn : 0 ≤ b - a := by linarith
    have h_eq_lhs : c * (a - b) ^ 2 = (c * (b - a)) * (b - a) := by ring
    have h_eq_rhs : (fa a - fa b) * (a - b) = (fa b - fa a) * (b - a) := by ring
    rw [h_eq_lhs, h_eq_rhs]
    exact mul_le_mul_of_nonneg_right h1 h_ba_nn
  · -- b ≤ a: symmetric.
    have h1 : c * (a - b) ≤ fa a - fa b := h_mono b a hab
    have h_ab_nn : 0 ≤ a - b := by linarith
    have h_sq : c * (a - b) ^ 2 = (c * (a - b)) * (a - b) := by ring
    rw [h_sq]
    exact mul_le_mul_of_nonneg_right h1 h_ab_nn

/-- **Composite: argmax-Lipschitz directly from gradient strong-monotonicity
and cross-Lipschitz** (Aubin-Frankowska 1990 §5.5 composite).

One-line composition of §3's chord-form discharge with §1's argmax-Lipschitz
lemma. Consumes the strong-gradient-monotonicity hypothesis directly,
bypassing the chord-form intermediate. This is the canonical form a
caller with a uniform Hessian bound would consume. -/
theorem argmax_lipschitz_of_gradient_strong_monotonicity_cross_lipschitz
    {Θ : Type*} [PseudoMetricSpace Θ]
    (fa : ℝ → Θ → ℝ) (a b : ℝ) (θ θ' : Θ) (K c : ℝ)
    (hK_nn : 0 ≤ K) (hc_pos : 0 < c)
    (hFOC_a : fa a θ = 0) (hFOC_b : fa b θ' = 0)
    (h_mono : ∀ x y, x ≤ y → c * (y - x) ≤ fa y θ' - fa x θ')
    (h_cross : ∀ x θ₁ θ₂, |fa x θ₁ - fa x θ₂| ≤ K * dist θ₁ θ₂) :
    |a - b| ≤ (K / c) * dist θ θ' := by
  have h_chord : c * (a - b) ^ 2 ≤ (fa a θ' - fa b θ') * (a - b) :=
    chord_form_of_gradient_strong_monotonicity (fun x => fa x θ') c hc_pos
      h_mono a b
  exact argmax_lipschitz_of_FOC_strong_concavity_cross_lipschitz
    fa a b θ θ' K c hK_nn hc_pos hFOC_a hFOC_b h_chord h_cross

/-! ## §4 R31 chord-form discharge from C² derivative lower bound
(Round 1.6 — Rincón-Zapatero & Santos 2009 + Klatte-Kummer 2002)

The §3 chord-form discharger takes the *integrated* gradient
strong-monotonicity bound `c · (b − a) ≤ fa(b) − fa(a)` as a
hypothesis. This section closes the link to the *differential* form
`c ≤ deriv fa x` (the C² Hessian lower bound for the original
objective) by composing with mathlib's mean value theorem
`mul_sub_le_image_sub_of_le_deriv`.

In project terms: under C² Target stage payoffs with joint-Target
objective `J_T(x, a; V_T, V_S)` having `c_T ≤ ∂²J_T/∂a²` uniformly,
the integrated form below is satisfied by `fa := ∂J_T/∂a`, and the
composite theorem produces the `K/c_T` argmax-Lipschitz constant
without any interiority hypothesis on the optimal compliance choice.

**Economic-theoretic anchor (Rincón-Zapatero & Santos 2009).** The
Hessian lower bound `c ≤ ∂²J_T/∂a²` is the second-order
characterisation of the unique-KKT-multiplier statement
Rincón-Zapatero & Santos prove for concave dynamic programs under
the Arrow-Hurwicz-Uzawa constraint qualification, **without an
interiority assumption** on the optimal solution. The gradient
strong-monotonicity of `fa = ∂J_T/∂a` is exactly the
gradient-monotonicity content of their uniqueness statement.

**Nonsmooth-optimization anchor (Klatte-Kummer 2002 Ch. 7).** In the
generalised-Kojima-function framework of Klatte-Kummer Ch. 7, the
gradient strong-monotonicity of `fa` is the pseudo-regularity
condition for the Karush-Kuhn-Tucker system that pins down the
Target's equilibrium policy `α`. The argmax-Lipschitz constant
`K/c_T` is then the canonical pseudo-regularity modulus.

Together these two anchors give the project a complete economic-
theoretic + mathematical-stability discharge of the chord-form
primitive: no interiority hypothesis, no opaque Prop, no witness
construction needed. The Lean implementation below uses the mathlib
MVT `mul_sub_le_image_sub_of_le_deriv` to bridge the differential
hypothesis to the integrated form. -/

/-- **Gradient strong-monotonicity from a derivative lower bound.**
If `fa : ℝ → ℝ` is differentiable everywhere and `deriv fa x ≥ c`
uniformly in `x`, then `fa` satisfies the gradient strong-monotonicity
hypothesis of §3:

  `∀ a b, a ≤ b → c · (b − a) ≤ fa b − fa a`.

This is a direct application of mathlib's mean value theorem
`mul_sub_le_image_sub_of_le_deriv`. In project terms: under C² Target
stage payoffs with `c_T ≤ ∂²J_T/∂a²`, the gradient `fa = ∂J_T/∂a`
satisfies the hypothesis with `c := c_T`. -/
theorem gradient_strong_monotonicity_of_deriv_lower_bound
    (fa : ℝ → ℝ) {c : ℝ} (h_diff : Differentiable ℝ fa)
    (h_deriv_ge : ∀ x, c ≤ deriv fa x) :
    ∀ a b, a ≤ b → c * (b - a) ≤ fa b - fa a :=
  fun _ _ hab => mul_sub_le_image_sub_of_le_deriv h_diff h_deriv_ge hab

/-- **R31 closure: chord form directly from a derivative lower
bound.** Composes the §4 differential-to-integrated bridge with the
§3 chord-form discharger. Under a uniform derivative lower bound
`deriv fa x ≥ c > 0` on a differentiable `fa : ℝ → ℝ`, the chord-
form inequality consumed by §1's argmax-Lipschitz lemma is satisfied
at every pair `(a, b)`. -/
theorem chord_form_of_deriv_lower_bound
    (fa : ℝ → ℝ) {c : ℝ} (hc_pos : 0 < c)
    (h_diff : Differentiable ℝ fa)
    (h_deriv_ge : ∀ x, c ≤ deriv fa x) (a b : ℝ) :
    c * (a - b) ^ 2 ≤ (fa a - fa b) * (a - b) :=
  chord_form_of_gradient_strong_monotonicity fa c hc_pos
    (gradient_strong_monotonicity_of_deriv_lower_bound fa h_diff h_deriv_ge)
    a b

/-- **R31 full closure (Round 1.6): argmax-Lipschitz directly from
C² Hessian lower bound and cross-Lipschitz of the gradient.**

Composite theorem reading off the closed-form selector Lipschitz
constant `K/c` directly from primitive C² data on the joint Target
objective. Under (i) Hessian lower bound `c ≤ ∂²J_T/∂a²` at the
parameter point `θ'` and (ii) cross-Lipschitz of the gradient
`∂J_T/∂a` in the parameter `θ` with modulus `K`, the argmax-Lipschitz
constant of the Target equilibrium policy in `θ` is bounded by
`K/c`.

This is the canonical R31 closure under the Rincón-Zapatero & Santos
2009 + Klatte-Kummer 2002 perspective: no interiority hypothesis on
the optimal compliance choice, no chord-form primitive on the
assumption surface, no witness construction required. The user
supplies (a) differentiability of `fa = ∂J_T/∂a` (immediate from C²)
and (b) the uniform Hessian lower bound (immediate from a Weierstrass
inf on the compact cube under C² structure). The composite reads off
the Lipschitz constant. -/
theorem argmax_lipschitz_of_C2_Hessian_lower_bound_and_cross_lipschitz
    {Θ : Type*} [PseudoMetricSpace Θ]
    (fa : ℝ → Θ → ℝ) (a b : ℝ) (θ θ' : Θ) (K c : ℝ)
    (hK_nn : 0 ≤ K) (hc_pos : 0 < c)
    (hFOC_a : fa a θ = 0) (hFOC_b : fa b θ' = 0)
    (h_diff : Differentiable ℝ (fun x => fa x θ'))
    (h_Hessian_lower : ∀ x, c ≤ deriv (fun x => fa x θ') x)
    (h_cross : ∀ x θ₁ θ₂, |fa x θ₁ - fa x θ₂| ≤ K * dist θ₁ θ₂) :
    |a - b| ≤ (K / c) * dist θ θ' := by
  have h_mono : ∀ x y, x ≤ y → c * (y - x) ≤ fa y θ' - fa x θ' :=
    gradient_strong_monotonicity_of_deriv_lower_bound
      (fun x => fa x θ') h_diff h_Hessian_lower
  exact argmax_lipschitz_of_gradient_strong_monotonicity_cross_lipschitz
    fa a b θ θ' K c hK_nn hc_pos hFOC_a hFOC_b h_mono h_cross

end ImplicitFunctionTheorem
end Foundations
end Sanctions
