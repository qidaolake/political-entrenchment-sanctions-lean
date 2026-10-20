/-
Sanctions/Foundations/StokeyLucas.lean

**Stokey-Lucas-Prescott (1989) *Recursive Methods in Economic Dynamics*
— core dynamic-programming theorems.**

This module packages the abstract dynamic-programming results from
SLP 1989 that underlie our Bellman fixed-point constructions:

* **Theorem 3.2 (Banach contraction)** — directly mathlib's
  `ContractingWith.fixedPoint`; we expose it abstractly with the SLP
  naming.
* **Theorem 3.3 (Blackwell's sufficient conditions)** — monotonicity
  + discounting imply contraction on bounded functions.
* **Theorem 4.6 family — Bellman operator preservation:**
  the closed sub-set of monotone (resp. continuous, concave) functions
  is invariant under a Bellman operator that preserves the property;
  the Banach fixed point therefore inherits the property.
* **Theorem 4.7 (monotonicity preservation)** — the most relevant for
  our FD-wedge primitive reduction.

The application of these results to the abstract Target/Sender Bellman
operators `V_T`, `V_S` lives in `Sanctions.Theory.Bellman.BellmanT`
and `BellmanS`, parametric over `Sanctions.AbstractGame.Params`. This
module carries the abstract content.
-/

import Sanctions.Foundations.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Iterate
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Topology

namespace Sanctions
namespace StokeyLucas

/-! ## §3.1 Weierstrass — continuous function on a compact set is bounded
(SLP Theorem 3.1)

SLP 1989 Theorem 3.1 packages the classical Weierstrass extreme-value
theorem in the form most useful for dynamic-programming proofs: if
`f` is continuous on a compact set `K`, then `|f|` attains a finite
upper bound on `K`. This is the canonical economist convention behind
"all primitive payoffs are bounded on the unit cube." We expose the
generic statement (compact set in any topological space, real-valued
function) and a triple-cube corollary specialized to
`Icc 0 1 × Icc 0 1 × Icc 0 1`, which is what the abstract
`Params`-level Bellman-cube primitives consume.

Behind the proof: mathlib's `IsCompact.exists_bound_of_continuousOn`
yields some `C` with `‖f x‖ ≤ C` on `K`; we sharpen `C` to
`max C 0` so the witness is provably nonnegative, matching the
nonnegativity convention used by every downstream cube-bound
hypothesis in `Theory/Bellman/InvariantBall.lean`. -/

/-- **SLP Theorem 3.1 (continuous function on a compact set is
bounded).** On a topological space `α` and a compact set `K ⊆ α`,
every continuous real-valued function on `K` is bounded in absolute
value by some nonnegative constant `M`. The literature anchor is
SLP 1989 Theorem 3.1 (Weierstrass extreme-value theorem).

Building block for `Theory/Bellman/InvariantBall.cube_bound_U_T`
and `cube_bound_U_S`, which auto-discharge the `cube_T`,
`cube_S` sup-norm bounds on `|U_T|`, `|U_S|` from the
`Params.U_T_continuous` / `U_S_continuous` continuity fields
plus compactness of the unit cube. -/
theorem cube_bound_of_continuousOn
    {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K)
    {f : α → ℝ} (hf : ContinuousOn f K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x| ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have := hC x hx
  simp only [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- **Triple-cube corollary of Theorem 3.1.** Specialization of
`cube_bound_of_continuousOn` to the unit cube
`Icc 0 1 × Icc 0 1 × Icc 0 1 ⊆ ℝ × ℝ × ℝ`: every globally-continuous
real-valued function on `ℝ³` is bounded in absolute value on the unit
cube by some nonnegative constant `M`. This is the form consumed by
the `Params`-level wrappers `cube_bound_U_T` / `cube_bound_U_S` in
`Theory/Bellman/InvariantBall.lean`. -/
theorem cube_bound_unitCube_of_continuous
    {f : ℝ × ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ Set.Icc (0:ℝ) 1,
        ∀ s ∈ Set.Icc (0:ℝ) 1, |f (x, a, s)| ≤ M := by
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1
  have hK : IsCompact K :=
    (isCompact_Icc).prod ((isCompact_Icc).prod isCompact_Icc)
  obtain ⟨M, hM_nn, hM⟩ := cube_bound_of_continuousOn hK hf.continuousOn
  refine ⟨M, hM_nn, ?_⟩
  intro x hx a ha s hs
  exact hM (x, a, s) ⟨hx, ha, hs⟩

/-! ### Round 39 Phase 2 (signed) sup/inf on the unit cube

The R23 `cube_bound_*_of_continuous*` lemmas above give absolute-value
bounds `|f x| ≤ M`, which suffices for sup-norm Banach margins on the
payoff itself. For derivative sup-norms (Phase 2 of the symbol-economy
sweep), we need *signed* bounds: a concrete upper bound on `f` (for
sup `∂U/∂s` → `L_U` Lipschitz) and a concrete lower bound on `f` (for
inf `∂U/∂x` → `g_U` minimum upward slope). These follow from
`IsCompact.exists_isMaxOn` / `_isMinOn` (Weierstrass extreme-value
theorem in its attained-at-a-point form) applied to the unit cube.

Building blocks for the future Round 40+ wrappers that auto-derive
`L_U_S`, `c_T`, `g_U`, `L_U_a` from C¹ payoffs. -/

/-- **R39 Phase 2 Foundations: signed sup of continuous on the unit
    cube.** From continuity of `f : ℝ × ℝ × ℝ → ℝ`, the existence of a
    uniform upper bound `M` on `[0,1]³` follows from the
    `IsCompact.exists_isMaxOn` Weierstrass form. Unlike the
    absolute-value `cube_bound_unitCube_of_continuous`, this gives a
    *signed* bound suitable for deriving sup-derivative Lipschitz
    constants. -/
theorem cube_sup_unitCube_of_continuous
    {f : ℝ × ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ,
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ Set.Icc (0:ℝ) 1,
        ∀ s ∈ Set.Icc (0:ℝ) 1, f (x, a, s) ≤ M := by
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1
  have hK : IsCompact K :=
    (isCompact_Icc).prod ((isCompact_Icc).prod isCompact_Icc)
  have hKne : K.Nonempty :=
    ⟨(0, 0, 0), Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr zero_le_one,
        Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr zero_le_one,
                            Set.left_mem_Icc.mpr zero_le_one⟩⟩⟩
  obtain ⟨p, _hp_mem, hp_max⟩ := hK.exists_isMaxOn hKne hf.continuousOn
  refine ⟨f p, ?_⟩
  intro x hx a ha s hs
  exact hp_max (Set.mem_prod.mpr ⟨hx, Set.mem_prod.mpr ⟨ha, hs⟩⟩)

/-- **R39 Phase 2 Foundations: signed inf of continuous on the unit
    cube.** Dual of `cube_sup_unitCube_of_continuous`. Used to derive
    `g_U` (Target stage state-slope inf) from continuous `∂U_T/∂x`. -/
theorem cube_inf_unitCube_of_continuous
    {f : ℝ × ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∃ m : ℝ,
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ Set.Icc (0:ℝ) 1,
        ∀ s ∈ Set.Icc (0:ℝ) 1, m ≤ f (x, a, s) := by
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1
  have hK : IsCompact K :=
    (isCompact_Icc).prod ((isCompact_Icc).prod isCompact_Icc)
  have hKne : K.Nonempty :=
    ⟨(0, 0, 0), Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr zero_le_one,
        Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr zero_le_one,
                            Set.left_mem_Icc.mpr zero_le_one⟩⟩⟩
  obtain ⟨p, _hp_mem, hp_min⟩ := hK.exists_isMinOn hKne hf.continuousOn
  refine ⟨f p, ?_⟩
  intro x hx a ha s hs
  exact hp_min (Set.mem_prod.mpr ⟨hx, Set.mem_prod.mpr ⟨ha, hs⟩⟩)

/-- **R39 Phase 2 Foundations: non-negative sup of |·| on the unit
    cube.** Combines `cube_sup_unitCube_of_continuous` with the
    obvious lower bound 0 — useful when the user wants `L_U_S ≥ 0`
    for cone-Lipschitz arguments. -/
theorem cube_sup_nonneg_unitCube_of_continuous
    {f : ℝ × ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ Set.Icc (0:ℝ) 1,
        ∀ s ∈ Set.Icc (0:ℝ) 1, f (x, a, s) ≤ M := by
  obtain ⟨M, hM⟩ := cube_sup_unitCube_of_continuous hf
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx a ha s hs
  exact (hM x hx a ha s hs).trans (le_max_left _ _)

/-- **R44 Foundations: strict-positivity inf of continuous-positive
    on the unit cube.** Strengthens
    `cube_inf_unitCube_of_continuous`: if `f` is continuous on the
    cube and **strictly positive** at every point, then the infimum
    `m = f(p)` at the Weierstrass-attained minimizer `p` is itself
    **strictly positive**. Used to auto-derive the strong-concavity
    modulus `c_σ > 0` from a uniform strict-concavity hypothesis on
    `−∂²U_S/∂s²`. -/
theorem cube_inf_pos_unitCube_of_continuous_pos
    {f : ℝ × ℝ × ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ Set.Icc (0:ℝ) 1,
              ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < f (x, a, s)) :
    ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ Set.Icc (0:ℝ) 1,
        ∀ s ∈ Set.Icc (0:ℝ) 1, m ≤ f (x, a, s) := by
  set K : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1
  have hK : IsCompact K :=
    (isCompact_Icc).prod ((isCompact_Icc).prod isCompact_Icc)
  have hKne : K.Nonempty :=
    ⟨(0, 0, 0), Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr zero_le_one,
        Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr zero_le_one,
                            Set.left_mem_Icc.mpr zero_le_one⟩⟩⟩
  obtain ⟨p, hp_mem, hp_min⟩ := hK.exists_isMinOn hKne hf.continuousOn
  obtain ⟨hpx, hpax⟩ := Set.mem_prod.mp hp_mem
  obtain ⟨hpa, hps⟩ := Set.mem_prod.mp hpax
  refine ⟨f p, hpos p.1 hpx p.2.1 hpa p.2.2 hps, ?_⟩
  intro x hx a ha s hs
  exact hp_min (Set.mem_prod.mpr ⟨hx, Set.mem_prod.mpr ⟨ha, hs⟩⟩)

/-! ## §3.2 Banach contraction (SLP Theorem 3.2)

mathlib provides this directly as `ContractingWith.fixedPoint`. We
restate the SLP formulation for documentation. -/

/-- **SLP Theorem 3.2 (Banach contraction).** On a complete metric
space, every contracting map has a unique fixed point, and iterating
the map from any starting point converges geometrically to that fixed
point. This is `ContractingWith.fixedPoint` and
`ContractingWith.tendsto_iterate_fixedPoint` in mathlib. -/
theorem banach_contraction_fixedPoint
    {S : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
    {β : NNReal} (hβ : β < 1)
    (T : S → S) (hT : LipschitzWith β T) :
    ∃ v : S, T v = v ∧
      ∀ v₀ : S, Filter.Tendsto (fun n => T^[n] v₀) Filter.atTop (𝓝 v) := by
  have hcontr : ContractingWith β T := ⟨hβ, hT⟩
  refine ⟨hcontr.fixedPoint, hcontr.fixedPoint_isFixedPt, fun v₀ => ?_⟩
  exact hcontr.tendsto_iterate_fixedPoint v₀

/-! ## §3.3 Blackwell's sufficient conditions (SLP Theorem 3.3)

For an operator `T` on bounded functions with sup norm: if `T` is
*monotone* (`f ≤ g → T f ≤ T g`) and satisfies *discounting*
(`T (f + a) ≤ T f + β · a` for nonneg constants `a`), then `T` is a
β-contraction in the sup norm.

Through round AI the conditions were recorded here as documentation only:
the abstract Bellman operators in `Theory/Bellman/BellmanT.lean` and
`BellmanS.lean` prove contraction by direct estimation. Since round AJ
(2026-09-22; doc 98 J8, so that the formalization map's Stokey–Lucas row
reads true) the theorem itself is here, on bounded continuous functions
into `ℝ` with the sup norm: monotonicity and discounting give a
`β`-Lipschitz operator (`blackwell_lipschitz`), and with `β < 1` a
contraction, so `banach_contraction_fixedPoint` applies. Nothing in the
tree consumes it yet; it exists so that the citation is a theorem. -/

/-- **SLP Theorem 3.3 (Blackwell's sufficient conditions).** An operator on
bounded continuous real functions that is monotone and discounts constants
at rate `β` is `β`-Lipschitz in the sup norm. -/
theorem blackwell_lipschitz {X : Type*} [TopologicalSpace X]
    (T : BoundedContinuousFunction X ℝ → BoundedContinuousFunction X ℝ) {β : NNReal}
    (h_mono : ∀ f g : BoundedContinuousFunction X ℝ, f ≤ g → T f ≤ T g)
    (h_disc : ∀ (f : BoundedContinuousFunction X ℝ) (a : ℝ), 0 ≤ a →
      T (f + BoundedContinuousFunction.const X a)
        ≤ T f + BoundedContinuousFunction.const X ((β : ℝ) * a)) :
    LipschitzWith β T := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hfg : f ≤ g + BoundedContinuousFunction.const X ‖f - g‖ := by
    intro x
    change f x ≤ g x + ‖f - g‖
    have := (f - g).norm_coe_le_norm x
    rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply, Real.norm_eq_abs] at this
    linarith [le_abs_self (f x - g x)]
  have hgf : g ≤ f + BoundedContinuousFunction.const X ‖f - g‖ := by
    intro x
    change g x ≤ f x + ‖f - g‖
    have := (f - g).norm_coe_le_norm x
    rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply, Real.norm_eq_abs] at this
    linarith [neg_abs_le (f x - g x)]
  have h1 : T f ≤ T g + BoundedContinuousFunction.const X ((β : ℝ) * ‖f - g‖) :=
    le_trans (h_mono _ _ hfg) (h_disc g _ (norm_nonneg _))
  have h2 : T g ≤ T f + BoundedContinuousFunction.const X ((β : ℝ) * ‖f - g‖) :=
    le_trans (h_mono _ _ hgf) (h_disc f _ (norm_nonneg _))
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  have e1 : T f x ≤ T g x + (β : ℝ) * ‖f - g‖ := h1 x
  have e2 : T g x ≤ T f x + (β : ℝ) * ‖f - g‖ := h2 x
  rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **Blackwell's conditions give a contraction with a unique fixed point**
when `β < 1`: SLP Theorem 3.3 composed with Theorem 3.2. -/
theorem blackwell_fixedPoint {X : Type*} [TopologicalSpace X]
    (T : BoundedContinuousFunction X ℝ → BoundedContinuousFunction X ℝ) {β : NNReal}
    (hβ : β < 1)
    (h_mono : ∀ f g : BoundedContinuousFunction X ℝ, f ≤ g → T f ≤ T g)
    (h_disc : ∀ (f : BoundedContinuousFunction X ℝ) (a : ℝ), 0 ≤ a →
      T (f + BoundedContinuousFunction.const X a)
        ≤ T f + BoundedContinuousFunction.const X ((β : ℝ) * a)) :
    ∃ v, T v = v ∧ ∀ v₀, Filter.Tendsto (fun n => T^[n] v₀) Filter.atTop (𝓝 v) :=
  banach_contraction_fixedPoint hβ T (blackwell_lipschitz T h_mono h_disc)

/-! ## §4.6–4.7 Bellman operator preservation theorems

The standard SLP technique to show that the Bellman fixed point inherits
a property `P` (monotonicity, continuity, concavity) is:

1. Show the subset `{V : V satisfies P}` is closed in the BCF sup norm.
2. Show the Bellman operator `T` maps the subset into itself.
3. The Banach fixed point, being the limit of `T^n V₀` for `V₀` in the
   subset, lies in the (closed) subset.

mathlib provides the abstract lemma:
`ContractingWith.isFixedPt_mem_of_mapsTo` or via taking limits along a
closed set. We package the abstract step as a theorem here. -/

/-- **SLP Theorem 4.7 abstract form (preservation of a closed property
under Bellman operator).**

Given a complete metric space `S`, a closed subset `K ⊆ S`, a contracting
self-map `T : S → S` (Lipschitz constant `β < 1`), and the hypothesis
that `T` maps `K` into itself, the Banach fixed point of `T` lies in
`K`.

Application: for SLP §4.7 monotonicity preservation, take `S = BCF(X, ℝ)`
(bounded continuous functions on a compact `X`), `K = {V : V monotone}`
(closed in sup norm — pointwise limits of monotone are monotone),
`T = Bellman operator`. If `T` preserves monotonicity, the fixed point
is monotone.

For §4.8 continuity preservation: `K = {V : V continuous}` — already
the whole space in our setup (we work in BCF).

For §4.7 concavity preservation: `K = {V : V concave}` — closed in sup
norm by limit. -/
theorem fixedPoint_mem_of_mapsTo
    {S : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
    {β : NNReal} (hβ : β < 1)
    (T : S → S) (hT : LipschitzWith β T)
    (K : Set S) (hK_closed : IsClosed K) (hK_nonempty : K.Nonempty)
    (hT_mapsTo : Set.MapsTo T K K) :
    ∃ v : S, T v = v ∧ v ∈ K := by
  have hcontr : ContractingWith β T := ⟨hβ, hT⟩
  -- Pick a starting point `v₀ ∈ K`; iterate.
  obtain ⟨v₀, hv₀⟩ := hK_nonempty
  -- All iterates `T^[n] v₀` stay in `K` by `MapsTo`.
  have h_iter_in : ∀ n, T^[n] v₀ ∈ K := by
    intro n
    induction n with
    | zero => simpa using hv₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hT_mapsTo ih
  -- Iterates converge to the fixed point.
  have h_tendsto :
      Filter.Tendsto (fun n => T^[n] v₀) Filter.atTop (𝓝 hcontr.fixedPoint) :=
    hcontr.tendsto_iterate_fixedPoint v₀
  -- The limit of a sequence in a closed set is in the set.
  have h_fp_in : hcontr.fixedPoint ∈ K :=
    hK_closed.mem_of_tendsto h_tendsto (Filter.Eventually.of_forall h_iter_in)
  exact ⟨hcontr.fixedPoint, hcontr.fixedPoint_isFixedPt, h_fp_in⟩

/-- **SLP Corollary 1 to Theorem 3.2, both clauses** (round AJ, 2026-09-22; doc
98 J9). If `T` maps a closed nonempty `K` into a subset `K' ⊆ K`, then the
unique fixed point lies in `K'`. The second clause is what tightens every
carrier-derived constant to the *image* constant: a value in a carrier with
modulus `M` whose Bellman image has modulus `M' ≤ M` is itself `M'`-regular. -/
theorem fixedPoint_mem_image_of_mapsTo
    {S : Type*} [MetricSpace S] [CompleteSpace S] [Nonempty S]
    {β : NNReal} (hβ : β < 1)
    (T : S → S) (hT : LipschitzWith β T)
    (K K' : Set S) (hK_closed : IsClosed K) (hK_nonempty : K.Nonempty)
    (hT_mapsTo : Set.MapsTo T K K') (hK'K : K' ⊆ K) :
    ∃ v : S, T v = v ∧ v ∈ K' ∧ ∀ w : S, T w = w → w = v := by
  have hcontr : ContractingWith β T := ⟨hβ, hT⟩
  obtain ⟨v₀, hv₀⟩ := hK_nonempty
  have h_iter_in : ∀ n, T^[n] v₀ ∈ K := by
    intro n
    induction n with
    | zero => simpa using hv₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hK'K (hT_mapsTo ih)
  have h_tendsto :
      Filter.Tendsto (fun n => T^[n] v₀) Filter.atTop (𝓝 hcontr.fixedPoint) :=
    hcontr.tendsto_iterate_fixedPoint v₀
  have h_fp_in : hcontr.fixedPoint ∈ K :=
    hK_closed.mem_of_tendsto h_tendsto (Filter.Eventually.of_forall h_iter_in)
  refine ⟨hcontr.fixedPoint, hcontr.fixedPoint_isFixedPt, ?_, fun w hw => ?_⟩
  · have := hT_mapsTo h_fp_in
    rwa [hcontr.fixedPoint_isFixedPt.eq] at this
  · exact hcontr.fixedPoint_unique hw

/-! ## SLP Theorem 4.7 specialization: monotonicity preservation on BCF

If the Bellman operator on bounded continuous functions over a compact
metric space `X` maps non-decreasing functions to non-decreasing
functions, then the value function (Banach fixed point) is non-decreasing.

The set `{V : BoundedContinuousFunction (↥X) ℝ | V is non-decreasing on ↥X}` is closed in BCF
because sup-norm convergence is pointwise convergence on the compact
underlying space, and pointwise limits of non-decreasing functions are
non-decreasing.

The specialization to the abstract Target Bellman fixed point `V_T`
(where the underlying space is the compact subtype `↥S = ↥[0, 1]`)
lives in `Theory/Bellman/BellmanT.lean`. -/

/-- A function `f : ↥X → ℝ` (subtype of `ℝ`) is non-decreasing if
`x ≤ y` in the ambient `ℝ` implies `f x ≤ f y`. -/
def MonotoneOnSubtype {X : Set ℝ} (f : ↥X → ℝ) : Prop :=
  ∀ ⦃x y : ↥X⦄, (x : ℝ) ≤ (y : ℝ) → f x ≤ f y

/-- A function `f : ↥X → ℝ` on a subtype of `ℝ` is **non-increasing**: if
`x ≤ y` in the ambient `ℝ` then `f y ≤ f x`.  Order-dual of
`MonotoneOnSubtype`, and used for the same SLP §4.7 purpose on the other
side of the order: the *decreasing* carrier is also closed in sup-norm, so a
Banach iteration started inside it lands inside it.

Rule 14: the relation is written directly over `f`'s values, so no opaque
`Prop` is interposed between the carrier and the data. -/
def AntitoneOnSubtype {X : Set ℝ} (f : ↥X → ℝ) : Prop :=
  ∀ ⦃x y : ↥X⦄, (x : ℝ) ≤ (y : ℝ) → f y ≤ f x

/-- A function `f : ↥X → ℝ` is non-decreasing *on a basin* `B ⊆ ℝ`
if `f x ≤ f y` whenever `x.val, y.val ∈ B` and `x.val ≤ y.val`.
This is the basin-restricted version of `MonotoneOnSubtype`, useful
for value functions that are monotone only on a forward-invariant
high-basin region (e.g.\ a high-entrenchment interval `[x_lb, 1]` at a
concrete LQ instantiation). -/
def MonotoneOnBasin {X : Set ℝ} (B : Set ℝ) (f : ↥X → ℝ) : Prop :=
  ∀ ⦃x y : ↥X⦄, (x : ℝ) ∈ B → (y : ℝ) ∈ B → (x : ℝ) ≤ (y : ℝ) → f x ≤ f y

/-! ## SLP Theorem 4.7 — basin-restricted monotonicity preservation

When the per-stage objective is monotone in `x` only on a high-basin
region `B ⊆ ↥X` (not globally), the SLP §4.7 argument still applies if
restricted to `B`. The set of `MonotoneOnBasin B` BCFs is closed in BCF
sup-norm; preservation under a contraction Bellman operator that maps
the basin into itself transfers the property to the Banach fixed point.
-/

/-- The set of BCFs that are monotone on a basin `B` is **closed in the
BCF sup-norm topology**. -/
theorem isClosed_monotoneOnBasin {X : Set ℝ} {B : Set ℝ} :
    IsClosed {V : BoundedContinuousFunction (↥X) ℝ |
      MonotoneOnBasin B (fun x => V x)} := by
  rw [← isSeqClosed_iff_isClosed]
  intro V_seq V h_mono h_tend x y hx_B hy_B h_le
  have h_each : ∀ n, V_seq n x ≤ V_seq n y := fun n => h_mono n hx_B hy_B h_le
  have h_tend_x : Filter.Tendsto (fun n => V_seq n x) Filter.atTop (𝓝 (V x)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at x
  have h_tend_y : Filter.Tendsto (fun n => V_seq n y) Filter.atTop (𝓝 (V y)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at y
  exact le_of_tendsto_of_tendsto h_tend_x h_tend_y (Filter.Eventually.of_forall h_each)

/-- **SLP Theorem 4.7 (basin-restricted monotonicity preservation).**
If the Bellman contraction `T` maps the closed subset of `MonotoneOnBasin B`
BCFs into itself, the Banach fixed point is monotone on `B`. -/
theorem fixedPoint_monotoneOnBasin_of_mapsTo
    {X : Set ℝ} {B : Set ℝ}
    [Nonempty (BoundedContinuousFunction (↥X) ℝ)]
    {β : NNReal} (hβ : β < 1)
    (T : BoundedContinuousFunction (↥X) ℝ → BoundedContinuousFunction (↥X) ℝ)
    (hT : LipschitzWith β T)
    (V₀ : BoundedContinuousFunction (↥X) ℝ)
    (hV₀ : MonotoneOnBasin B (fun x => V₀ x))
    (hT_preserve : ∀ V : BoundedContinuousFunction (↥X) ℝ,
        MonotoneOnBasin B (fun x => V x) →
        MonotoneOnBasin B (fun x => T V x)) :
    ∃ V : BoundedContinuousFunction (↥X) ℝ, T V = V ∧
      MonotoneOnBasin B (fun x => V x) := by
  refine fixedPoint_mem_of_mapsTo hβ T hT
    {V : BoundedContinuousFunction (↥X) ℝ | MonotoneOnBasin B (fun x => V x)}
    isClosed_monotoneOnBasin
    ⟨V₀, hV₀⟩
    ?_
  intro V hV; exact hT_preserve V hV

/-! ## SLP Theorem 4.8 — concavity preservation

SLP §4.8: under strict concavity of the per-stage payoff `F` and
convexity of the feasibility correspondence `Γ`, the value function is
strictly concave (and the optimal policy is single-valued and
continuous).

The non-strict version (concave, not strictly): if the Bellman operator
maps concave-BCFs to concave-BCFs, the fixed point is concave. This is
an immediate corollary of `fixedPoint_mem_of_mapsTo` once we know the
concave subset is closed in BCF — which holds because the concavity
inequality `(1−θ)·f(x) + θ·f(y) ≤ f((1−θ)x + θy)` is preserved under
pointwise limits, and BCF sup-norm convergence on a compact subtype
implies pointwise convergence.

At a concrete LQ instantiation, the value function on a saturated
high basin is typically **linear** in the state (since the stage
payoff is linear-in-`x` plus quadratic-in-`a`, and on a saturated
region the Sender's projected response is constant), hence concave
but not *strictly* concave — so SLP §4.8's strict-concavity
conclusion is not load-bearing for the LQ chain; the FD-wedge
mechanism is the load-bearing route. -/

/-- A function `f : ↥X → ℝ` on a subtype of `ℝ` is **concave with respect
to ambient convex combinations**: whenever `x, y ∈ ↥X` and `z ∈ ↥X`
satisfies `z.val = (1 − θ) * x.val + θ * y.val` for some `θ ∈ [0, 1]`,
the standard concavity inequality holds:
`(1 − θ) * f(x) + θ * f(y) ≤ f(z)`. -/
def ConcaveOnSubtype {X : Set ℝ} (f : ↥X → ℝ) : Prop :=
  ∀ ⦃x y : ↥X⦄ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
    ∀ ⦃z : ↥X⦄, (z : ℝ) = (1 - θ) * (x : ℝ) + θ * (y : ℝ) →
      (1 - θ) * f x + θ * f y ≤ f z

/-- The set of concave BCFs on a subtype of `ℝ` is **closed in the BCF
sup-norm topology**.

Proof: BCF sup-norm convergence `Vₙ → V` implies pointwise convergence
`Vₙ(x) → V(x)` for every `x ∈ ↥X` (since `|Vₙ(x) − V(x)| ≤ ‖Vₙ − V‖`).
The concavity inequality `(1−θ) * Vₙ(x) + θ * Vₙ(y) ≤ Vₙ(z)` holds for
every `n`; taking the limit (using `Filter.Tendsto.add`,
`Filter.Tendsto.const_mul`, and `le_of_tendsto`) preserves the inequality. -/
theorem isClosed_concaveOnSubtype {X : Set ℝ} :
    IsClosed {V : BoundedContinuousFunction (↥X) ℝ | ConcaveOnSubtype (fun x => V x)} := by
  -- A set is closed iff it's sequentially closed (BCF is a metric space).
  rw [← isSeqClosed_iff_isClosed]
  intro V_seq V h_concave h_tend
  -- `h_concave n` : each `V_seq n` is concave-on-subtype.
  -- `h_tend` : `V_seq → V` in BCF sup norm.
  intro x y θ hθ_lo hθ_hi z hz
  -- For each n: `(1 - θ) * V_seq n x + θ * V_seq n y ≤ V_seq n z`.
  have h_each : ∀ n, (1 - θ) * V_seq n x + θ * V_seq n y ≤ V_seq n z :=
    fun n => h_concave n hθ_lo hθ_hi hz
  -- Pointwise convergence at x, y, z follows from sup-norm convergence.
  have h_tend_x : Filter.Tendsto (fun n => V_seq n x) Filter.atTop (𝓝 (V x)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at x
  have h_tend_y : Filter.Tendsto (fun n => V_seq n y) Filter.atTop (𝓝 (V y)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at y
  have h_tend_z : Filter.Tendsto (fun n => V_seq n z) Filter.atTop (𝓝 (V z)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at z
  -- LHS tendsto `(1 - θ) * V x + θ * V y`.
  have h_tend_lhs : Filter.Tendsto
      (fun n => (1 - θ) * V_seq n x + θ * V_seq n y) Filter.atTop
      (𝓝 ((1 - θ) * V x + θ * V y)) := by
    exact (h_tend_x.const_mul (1 - θ)).add (h_tend_y.const_mul θ)
  -- Limit of `≤` is `≤`.
  exact le_of_tendsto_of_tendsto h_tend_lhs h_tend_z (Filter.Eventually.of_forall h_each)

/-! ## SLP Theorem 4.7 — monotonicity preservation -/

/-- The set of monotone (non-decreasing) BCFs on a subtype of ℝ is
**closed in the BCF sup-norm topology**. Same proof structure as
`isClosed_concaveOnSubtype`. -/
theorem isClosed_monotoneOnSubtype {X : Set ℝ} :
    IsClosed {V : BoundedContinuousFunction (↥X) ℝ |
      MonotoneOnSubtype (fun x => V x)} := by
  rw [← isSeqClosed_iff_isClosed]
  intro V_seq V h_mono h_tend
  intro x y h_le
  have h_each : ∀ n, V_seq n x ≤ V_seq n y := fun n => h_mono n h_le
  have h_tend_x : Filter.Tendsto (fun n => V_seq n x) Filter.atTop (𝓝 (V x)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at x
  have h_tend_y : Filter.Tendsto (fun n => V_seq n y) Filter.atTop (𝓝 (V y)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at y
  exact le_of_tendsto_of_tendsto h_tend_x h_tend_y (Filter.Eventually.of_forall h_each)

/-- The set of **non-increasing** BCFs on a subtype of `ℝ` is **closed in the
BCF sup-norm topology**.  Order-dual of `isClosed_monotoneOnSubtype`, with the
same proof: sup-norm convergence on the subtype is pointwise convergence, and a
pointwise limit of non-increasing functions is non-increasing.

This is what licenses a Banach iteration to conclude that the *limit* of the
value iterates is non-increasing (SLP §4.7, decreasing side). -/
theorem isClosed_antitoneOnSubtype {X : Set ℝ} :
    IsClosed {V : BoundedContinuousFunction (↥X) ℝ |
      AntitoneOnSubtype (fun x => V x)} := by
  rw [← isSeqClosed_iff_isClosed]
  intro V_seq V h_anti h_tend x y h_le
  have h_each : ∀ n, V_seq n y ≤ V_seq n x := fun n => h_anti n h_le
  have h_tend_x : Filter.Tendsto (fun n => V_seq n x) Filter.atTop (𝓝 (V x)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at x
  have h_tend_y : Filter.Tendsto (fun n => V_seq n y) Filter.atTop (𝓝 (V y)) :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tend).tendsto_at y
  exact le_of_tendsto_of_tendsto h_tend_y h_tend_x (Filter.Eventually.of_forall h_each)

/-- **SLP Theorem 4.7 (monotonicity preservation).** If a contraction
`T` on `BoundedContinuousFunction (↥X) ℝ` maps the closed subset of
monotone BCFs into itself, the Banach fixed point is monotone on the
subtype. Specialization of `fixedPoint_mem_of_mapsTo` to the monotone
subset. -/
theorem fixedPoint_monotone_of_mapsTo
    {X : Set ℝ}
    [Nonempty (BoundedContinuousFunction (↥X) ℝ)]
    {β : NNReal} (hβ : β < 1)
    (T : BoundedContinuousFunction (↥X) ℝ → BoundedContinuousFunction (↥X) ℝ)
    (hT : LipschitzWith β T)
    (V₀ : BoundedContinuousFunction (↥X) ℝ)
    (hV₀ : MonotoneOnSubtype (fun x => V₀ x))
    (hT_preserve : ∀ V : BoundedContinuousFunction (↥X) ℝ,
        MonotoneOnSubtype (fun x => V x) →
        MonotoneOnSubtype (fun x => T V x)) :
    ∃ V : BoundedContinuousFunction (↥X) ℝ, T V = V ∧
      MonotoneOnSubtype (fun x => V x) := by
  refine fixedPoint_mem_of_mapsTo hβ T hT
    {V : BoundedContinuousFunction (↥X) ℝ | MonotoneOnSubtype (fun x => V x)}
    isClosed_monotoneOnSubtype
    ⟨V₀, hV₀⟩
    ?_
  intro V hV; exact hT_preserve V hV

/-- **SLP Theorem 4.8 (concavity preservation).** If a contraction `T`
on `BoundedContinuousFunction (↥X) ℝ` maps the closed subset of concave BCFs into itself, then
the Banach fixed point is concave on the subtype.

Specialization of `fixedPoint_mem_of_mapsTo` to the concave subset. -/
theorem fixedPoint_concave_of_mapsTo
    {X : Set ℝ}
    [Nonempty (BoundedContinuousFunction (↥X) ℝ)]
    {β : NNReal} (hβ : β < 1)
    (T : (BoundedContinuousFunction (↥X) ℝ) → (BoundedContinuousFunction (↥X) ℝ))
    (hT : LipschitzWith β T)
    (V₀ : BoundedContinuousFunction (↥X) ℝ) (hV₀ : ConcaveOnSubtype (fun x => V₀ x))
    (hT_preserve : ∀ V : BoundedContinuousFunction (↥X) ℝ,
        ConcaveOnSubtype (fun x => V x) →
        ConcaveOnSubtype (fun x => T V x)) :
    ∃ V : BoundedContinuousFunction (↥X) ℝ, T V = V ∧ ConcaveOnSubtype (fun x => V x) := by
  refine fixedPoint_mem_of_mapsTo hβ T hT
    {V : BoundedContinuousFunction (↥X) ℝ | ConcaveOnSubtype (fun x => V x)}
    isClosed_concaveOnSubtype
    ⟨V₀, hV₀⟩
    ?_
  intro V hV; exact hT_preserve V hV

/-! ## §6.1 Monotone convergence of a deterministic difference equation

SLP 1989 §6.1 establishes — as a worked example, never abstracted into a
named theorem — that the trajectory of a monotone one-dimensional policy
map converges monotonically to a steady state. We abstract that argument
here: a monotone continuous self-map of a closed interval has every orbit
converge to a fixed point.

This is the convergence backbone for the joint sanction-preference persistence result:
combined with forward-invariance of the trapping interval, it upgrades
"the sanctions orbit stays trapped" to "the sanctions orbit converges to
a permanent steady state". -/

/-- **Orbit-limit-is-fixed-point bridge.** If the orbit `n ↦ T^[n] x₀`
of a continuous map `T` converges to `L`, then `L` is a fixed point.

This is the small reusable step shared by SLP §6.1 (monotone convergence)
and SLP Lemma 6.2 (the Liapounov method). -/
theorem orbit_limit_isFixedPoint {T : ℝ → ℝ} (hT : Continuous T)
    {x₀ L : ℝ}
    (h_conv : Filter.Tendsto (fun n => T^[n] x₀) Filter.atTop (𝓝 L)) :
    T L = L := by
  -- `T (orbit n) → T L` by continuity.
  have h1 : Filter.Tendsto (fun n => T (T^[n] x₀)) Filter.atTop (𝓝 (T L)) :=
    (hT.tendsto L).comp h_conv
  -- `T (orbit n) = orbit (n+1) → L` (shift).
  have h2 : Filter.Tendsto (fun n => T (T^[n] x₀)) Filter.atTop (𝓝 L) := by
    have h_shift : Filter.Tendsto (fun n => T^[n + 1] x₀) Filter.atTop (𝓝 L) :=
      h_conv.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.iterate_succ_apply'] using h_shift
  exact tendsto_nhds_unique h1 h2

/-- **Monotone-iteration convergence** (SLP 1989 §6.1, abstracted).
A monotone, continuous self-map `T` of a nonempty closed bounded
interval `[a, b] ⊆ ℝ` has, for every starting point `x₀ ∈ [a, b]`, an
orbit `n ↦ T^[n] x₀` that converges to a fixed point of `T` inside
`[a, b]`.

The orbit is monotone (increasing from a post-fixed start `x₀ ≤ T x₀`,
decreasing from a pre-fixed start `T x₀ ≤ x₀`), bounded by the interval,
hence convergent; continuity of `T` then identifies the limit as a
fixed point. -/
theorem monotone_orbit_converges
    {T : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hT_mono : Monotone T) (hT_cont : Continuous T)
    (hT_maps : ∀ x ∈ Set.Icc a b, T x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    ∃ x_star ∈ Set.Icc a b, T x_star = x_star ∧
      Filter.Tendsto (fun n => T^[n] x₀) Filter.atTop (𝓝 x_star) := by
  -- The orbit stays in `[a, b]`.
  have h_orbit_mem : ∀ n, T^[n] x₀ ∈ Set.Icc a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [Function.iterate_succ']; exact hT_maps _ ih
  rcases le_total x₀ (T x₀) with h_pf | h_pf
  · -- Post-fixed start: the orbit is monotone increasing.
    have h_le_succ : ∀ n, T^[n] x₀ ≤ T^[n + 1] x₀ := by
      intro n
      have h := (hT_mono.iterate n) h_pf
      rwa [← Function.iterate_succ_apply] at h
    have h_mono : Monotone (fun n => T^[n] x₀) := monotone_nat_of_le_succ h_le_succ
    have h_bdd : BddAbove (Set.range (fun n => T^[n] x₀)) := by
      refine ⟨b, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (h_orbit_mem n).2
    set L := ⨆ n, T^[n] x₀ with hL
    have h_conv : Filter.Tendsto (fun n => T^[n] x₀) Filter.atTop (𝓝 L) :=
      tendsto_atTop_ciSup h_mono h_bdd
    have hL_mem : L ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · exact le_trans hx₀.1 (le_ciSup h_bdd 0)
      · exact ciSup_le (fun n => (h_orbit_mem n).2)
    exact ⟨L, hL_mem, orbit_limit_isFixedPoint hT_cont h_conv, h_conv⟩
  · -- Pre-fixed start: the orbit is monotone decreasing.
    have h_succ_le : ∀ n, T^[n + 1] x₀ ≤ T^[n] x₀ := by
      intro n
      have h := (hT_mono.iterate n) h_pf
      rwa [← Function.iterate_succ_apply] at h
    have h_anti : Antitone (fun n => T^[n] x₀) := antitone_nat_of_succ_le h_succ_le
    have h_bdd : BddBelow (Set.range (fun n => T^[n] x₀)) := by
      refine ⟨a, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (h_orbit_mem n).1
    set L := ⨅ n, T^[n] x₀ with hL
    have h_conv : Filter.Tendsto (fun n => T^[n] x₀) Filter.atTop (𝓝 L) :=
      tendsto_atTop_ciInf h_anti h_bdd
    have hL_mem : L ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · exact le_ciInf (fun n => (h_orbit_mem n).1)
      · exact le_trans (ciInf_le h_bdd 0) hx₀.2
    exact ⟨L, hL_mem, orbit_limit_isFixedPoint hT_cont h_conv, h_conv⟩

/-! ## §6 Theorem 6.3 (scalar case) — affine global stability dichotomy

SLP 1989 Theorem 6.3 characterises global convergence of a linear
difference equation by the spectral radius. In the scalar case the
system `xₜ₊₁ = λ·xₜ + c` converges globally to `x* = c/(1−λ)` when
`0 ≤ λ < 1`, and orbits diverge from `x*` when `λ > 1`. The same
dichotomy is the boundary-fixed-point stability split of the
Multistage-Games fishery model (§5.2, Lemmas 6–7). -/

/-- Closed-form `n`-th iterate of the affine map `x ↦ λ·x + c`:
`T^[n] x₀ = x* + λ^n · (x₀ − x*)` where `x* = c/(1−λ)`. -/
theorem affine_iterate_eq {lam c : ℝ} (h_ne : lam ≠ 1) (x₀ : ℝ) (n : ℕ) :
    (fun x => lam * x + c)^[n] x₀
      = c / (1 - lam) + lam ^ n * (x₀ - c / (1 - lam)) := by
  have h1 : (1 : ℝ) - lam ≠ 0 := sub_ne_zero.mpr (fun h => h_ne h.symm)
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    field_simp
    ring

/-- **SLP Theorem 6.3, scalar stable case.** For the affine map
`T x = λ·x + c` with `0 ≤ λ < 1`, every orbit converges to the unique
fixed point `x* = c/(1−λ)`. -/
theorem affine_orbit_converges {lam c : ℝ} (h_lam_nn : 0 ≤ lam) (h_lam_lt : lam < 1)
    (x₀ : ℝ) :
    Filter.Tendsto (fun n => (fun x => lam * x + c)^[n] x₀) Filter.atTop
      (𝓝 (c / (1 - lam))) := by
  have h_ne : lam ≠ 1 := ne_of_lt h_lam_lt
  have h_pow : Filter.Tendsto (fun n => lam ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h_lam_nn h_lam_lt
  have h_term : Filter.Tendsto
      (fun n => c / (1 - lam) + lam ^ n * (x₀ - c / (1 - lam)))
      Filter.atTop (𝓝 (c / (1 - lam) + 0 * (x₀ - c / (1 - lam)))) :=
    (tendsto_const_nhds.add (h_pow.mul_const _))
  simp only [zero_mul, add_zero] at h_term
  exact h_term.congr (fun n => (affine_iterate_eq h_ne x₀ n).symm)

/-! ## Hinderer 4.2(c) Benveniste-Scheinkman envelope: closed-form Lipschitz constant

Hinderer 4.2(c) (Benveniste-Scheinkman envelope theorem) gives a closed-form
Lipschitz constant for the Bellman fixed point under stage payoff
Lipschitz `L_U` and transition Lipschitz `γ`: when the contraction
margin `β·γ < 1` holds, the unique fixed point is Lipschitz with
constant `K := L_U / (1 − β·γ)`. The economic content is that the
state-derivative of the value function inherits the stage payoff's
state-derivative, deflated by the geometric series of the discounted
transition multiplier.

The single-line algebra step the project repeatedly uses is the
**cone-margin equality** `L_U + β·K·γ = K` when `K = L_U/(1 − β·γ)`.
With this equality in hand, the value-function Lipschitz preservation
chain (`bellmanBCF_preserves_lipschitz_cone` →
`bellmanBCF_iterate_zero_lipschitz` →
`valueLipschitzWith_of_tendsto`) collapses to the named closed-form
constant. We expose the algebra here so downstream files can cite the
Hinderer 4.2(c) result by name. -/

/-- **Hinderer 4.2(c) closed-form Lipschitz margin (algebra).** Given a stage
payoff Lipschitz constant `L_U ≥ 0`, a discount factor `β`, and a
transition Lipschitz `γ` with `β·γ < 1`, the closed-form Lipschitz
constant `K := L_U / (1 − β·γ)` is non-negative and satisfies the
cone-margin equality `L_U + β · K · γ = K`.

This is the algebra crux underlying Hinderer 4.2(c) (Benveniste-Scheinkman).
Downstream consumption: `Theory/Bellman/ValueLipschitz.lean`'s
`V_T_valueLipschitzWith_of_contraction` and
`V_S_valueLipschitzWith_of_contraction` apply this margin and the
Banach iteration limit (`fixedPoint_mem_of_mapsTo`) to land
`ValueLipschitzWith p.V_T K`.

We keep the lemma at the Foundations layer (no `Params`, no BCF
type) so it can be cited generically: any Bellman-style operator
with stage Lipschitz `L_U` and transition Lipschitz `γ` under a
β-contraction with `β·γ < 1` inherits the closed-form Lipschitz
constant. -/
theorem bellman_closed_form_lipschitz_margin
    {β γ L_U : ℝ}
    (hL_U_nn : 0 ≤ L_U) (_hβ_nn : 0 ≤ β) (_hγ_nn : 0 ≤ γ)
    (h_contract : β * γ < 1) :
    0 ≤ L_U / (1 - β * γ) ∧
      L_U + β * (L_U / (1 - β * γ)) * γ = L_U / (1 - β * γ) := by
  have h_denom_pos : 0 < 1 - β * γ := by linarith
  have h_denom_ne : (1 - β * γ) ≠ 0 := ne_of_gt h_denom_pos
  refine ⟨div_nonneg hL_U_nn (le_of_lt h_denom_pos), ?_⟩
  -- Algebra: L_U + β · (L_U/(1−β·γ)) · γ
  --   = (L_U · (1−β·γ) + β · L_U · γ) / (1−β·γ)
  --   = L_U / (1−β·γ).
  field_simp
  ring

/-- **Hinderer 4.2(c) closed-form Lipschitz constant (named).** The Bellman
fixed-point Lipschitz constant in closed form: `K := L_U/(1 − β·γ)`
under the standard Hinderer 4.2(c) hypotheses (stage Lipschitz `L_U`,
transition Lipschitz `γ`, contraction margin `β·γ < 1`). Helper
abbreviation so downstream consumers can write `bellmanLipConstant β γ L_U`
in place of the explicit fraction.

**Literature anchors (Lipschitz value-function family).** The closed
form here is the canonical envelope formula from
\citet[Hinderer 4.2(c)]{StokeyLucas1989}. The same recursion appears in modern
treatments and is the foundational anchor for every weighted-sup-norm
contraction argument used by this project's joint Bellman existence
chain:

* **Denardo 1967** (`PaperRefer/MathTheory/ContractionMappingsDP-Denardo-1967.md`)
  — the original abstract contraction + N-stage-contraction framework
  from which all modern weighted-sup-norm theorems descend.
* **Bertsekas-Tsitsiklis 1996** *Neuro-Dynamic Programming* Ch. 2
  Prop. 2.2 (`BookRefer/NDP.md`) — the canonical weighted-max-norm
  pseudo-contraction theorem; closed form matches the present one up
  to weighting.
* **Bertsekas 2012** *Weighted Sup-Norm Contractions in DP*
  (`PaperRefer/MathTheory/WeightedSupNormContractionsDP-Bertsekas-2012.md`)
  — modern refinement.
* **Hinderer 2005** *Lipschitz Continuity of Value Functions in MDPs*,
  Math. Methods Operations Research 62(1) — explicit closed-form
  Lipschitz constants for value functions in additive-separable MDPs
  (`r(s,a) = r_S(s) + r_A(a) + r_D(s,a)`); Theorem 4.1 specialises to
  the present formula when the transition kernel has Wasserstein-
  Lipschitz constant `γ` and the stage payoff has additive Lipschitz
  constant `L_U`. See `PaperRefer/MathTheory/LipschitzValueFunctionsMDP-Hinderer-2005.md`.
* **Stachurski 2008** *Continuous State DP via Nonexpansive
  Approximation*, Computational Economics 31 — continuous-state DP
  with nonexpansive function approximators; parallels the project's
  `valLipBall` carrier. See
  `PaperRefer/MathTheory/ContinuousStateDP-NonexpansiveApprox-Stachurski-2008.md`.
-/
def bellmanLipConstant (β γ L_U : ℝ) : ℝ := L_U / (1 - β * γ)

/-- Unfold lemma for `bellmanLipConstant`. -/
@[simp] theorem bellmanLipConstant_def (β γ L_U : ℝ) :
    bellmanLipConstant β γ L_U = L_U / (1 - β * γ) := rfl

/-- **SLP Theorem 6.3, scalar repelling case.** For the affine map
`T x = λ·x + c` with `λ > 1`, every orbit starting away from the fixed
point `x* = c/(1−λ)` diverges: `|T^[n] x₀ − x*| = λ^n·|x₀ − x*| → ∞`. -/
theorem affine_orbit_diverges {lam c : ℝ} (h_lam_gt : 1 < lam)
    {x₀ : ℝ} (h_ne_fp : x₀ ≠ c / (1 - lam)) :
    Filter.Tendsto (fun n => |(fun x => lam * x + c)^[n] x₀ - c / (1 - lam)|)
      Filter.atTop Filter.atTop := by
  have h_ne : lam ≠ 1 := ne_of_gt h_lam_gt
  have h_diff_pos : 0 < |x₀ - c / (1 - lam)| := abs_pos.mpr (sub_ne_zero.mpr h_ne_fp)
  have h_pow : Filter.Tendsto (fun n => lam ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h_lam_gt
  have h_eq : ∀ n, |(fun x => lam * x + c)^[n] x₀ - c / (1 - lam)|
      = lam ^ n * |x₀ - c / (1 - lam)| := by
    intro n
    rw [affine_iterate_eq h_ne x₀ n]
    rw [show c / (1 - lam) + lam ^ n * (x₀ - c / (1 - lam)) - c / (1 - lam)
          = lam ^ n * (x₀ - c / (1 - lam)) from by ring, abs_mul]
    congr 1
    exact abs_of_nonneg (pow_nonneg (by linarith) n)
  have h_prod : Filter.Tendsto (fun n => lam ^ n * |x₀ - c / (1 - lam)|)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const h_diff_pos h_pow
  exact h_prod.congr (fun n => (h_eq n).symm)

/-! ## Round-27 closed-form lower-slope constant (Hinderer 4.2(c), lower-slope side)

Locator note (round AI, 2026-09-22): through round AH this section and its
consumers cited "Hinderer 4.2(c) Benveniste–Scheinkman" and "Hinderer 4.2(c)". Read against
the held text: Benveniste–Scheinkman is SLP Theorem 4.10 and needs a
differentiable value; Theorem 4.11 is differentiability under an interior
policy, which fails at the corner witnesses; chapter 4 has sections 4.1–4.5
only; Hinderer 4.2(c) is the stochastic chapter's Bounded Returns. What is proved here is
the scalar recursion `α + γ·L ≤ L` of Hinderer (2005) Theorem 4.2(c), and the
carrier inheritance it feeds is SLP Theorem 4.6 with Corollary 1 to Theorem
3.2. The identifiers keep their names.

The Round-25 closed-form `bellmanLipConstant β γ L_U = L_U / (1 − β·γ)`
captures the **upper-bound** Lipschitz constant for the Bellman fixed point.
Round 27 ships its **lower-slope** analog by the same recursion (Hinderer
4.2(c); not an envelope theorem, no differentiability is used): the fixed point inherits a uniform
**lower** state-slope `g_T := g_U / (1 − β · γ_F)` from a primitive
stage-payoff lower state-slope `g_U` and the transition's coordinate
multiplier `γ_F`. Economically: if the stage payoff increases by at least
`g_U` per unit `x`, then the value function increases by at least
`g_T = g_U / (1 − β · γ_F)` per unit `x` — the geometric series of the
discounted transition coordinate amplification.

Two pieces ship at the Foundations layer:

* `bellman_closed_form_lowerSlope_margin` — the cone-margin algebraic
  identity `g_U + β · g_T · γ_F = g_T`, mirroring R25's
  `bellman_closed_form_lipschitz_margin`. With this identity, an inductive
  preservation chain (operator preserves the lower-slope cone, starting
  from a linear initial seed `V₀(y) = g_U · y`) collapses to a single
  named constant `g_T = bellmanLowerSlopeConstant β γ_F g_U`.
* `sSup_image_sub_sSup_image_lowerBound_of_pointwise` — the
  sup-difference lower bound (companion to `Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd`
  in `Foundations/SupDiff.lean`): if every member of the family of
  integrands satisfies `L ≤ f a − h a`, the `sSup` over `K` inherits the
  same lower bound `L ≤ sSup (f '' K) − sSup (h '' K)`.

Together these are the algebra crux behind the Target-side γ_σ envelope
companion (`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope` in
`Theory/Bellman/InvariantLipGainBall.lean`), which discharges the Target
value-gain condition `LowerSlopeOnValueOn` on the basin (until round BJ1.4,
2026-10-07, the core certificate's field `hV_T_gain_on_carrier`) from the
primitive payoff state-slope. -/

/-- **Hinderer-4.2(c) lower-slope closed-form lower-slope margin (algebra).**
Given a stage-payoff lower state-slope `g_U ≥ 0`, a discount factor `β`,
and a transition state multiplier `γ_F` with `β · γ_F < 1`, the
closed-form lower-slope constant `g_T := g_U / (1 − β · γ_F)` is
non-negative and satisfies the cone-margin identity
`g_U + β · g_T · γ_F = g_T`.

This is the algebra crux underlying Hinderer 4.2(c)
(Benveniste-Scheinkman envelope, lower-slope side). Downstream
consumption: `Theory/Bellman/InvariantLipGainBall.lean`'s
`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope` applies this margin
to derive a `LowerSlopeOnValueOn` bound on the joint Target Bellman
operator from the primitive payoff state-slope.

We keep the lemma at the Foundations layer (no `Params`, no BCF type) so
it can be cited generically: any Bellman-style operator with stage lower
state-slope `g_U` and transition multiplier `γ_F` under a β-contraction
with `β · γ_F < 1` inherits the closed-form lower state-slope. -/
theorem bellman_closed_form_lowerSlope_margin
    {β γ_F g_U : ℝ}
    (hg_U_nn : 0 ≤ g_U) (_hβ_nn : 0 ≤ β) (_hγ_F_nn : 0 ≤ γ_F)
    (h_contract : β * γ_F < 1) :
    0 ≤ g_U / (1 - β * γ_F) ∧
      g_U + β * (g_U / (1 - β * γ_F)) * γ_F = g_U / (1 - β * γ_F) := by
  have h_denom_pos : 0 < 1 - β * γ_F := by linarith
  refine ⟨div_nonneg hg_U_nn (le_of_lt h_denom_pos), ?_⟩
  field_simp
  ring

/-- **Hinderer-4.2(c) lower-slope closed-form lower-slope constant (named).**
The Bellman fixed-point lower state-slope in closed form:
`g_T := g_U / (1 − β · γ_F)` under the standard Hinderer 4.2(c) hypotheses
(stage state-slope `g_U`, transition multiplier `γ_F`, contraction margin
`β · γ_F < 1`). Mirrors `bellmanLipConstant` from Round 25. -/
def bellmanLowerSlopeConstant (β γ_F g_U : ℝ) : ℝ := g_U / (1 - β * γ_F)

/-- Unfold lemma for `bellmanLowerSlopeConstant`. -/
@[simp] theorem bellmanLowerSlopeConstant_def (β γ_F g_U : ℝ) :
    bellmanLowerSlopeConstant β γ_F g_U = g_U / (1 - β * γ_F) := rfl

/-! ## Closed-form **sup-norm radius** of a Bellman carrier ball

The two closed forms above pin the *slopes* of a Bellman fixed point:
the Hinderer-4.2(c) upper Lipschitz constant `L_U/(1 − β·γ)` and the Hinderer-4.2(c)
lower envelope slope `g_U/(1 − β·γ_F)`. A Banach carrier needs a third
magnitude — its **radius**: how large a sup-norm ball the Bellman
operator maps into itself.

That radius has the *same* geometric-series closed form, with transition
multiplier `1` rather than `γ`: the sup-norm of the continuation term is
not damped by the state map at all, only by the discount factor. So

  `M := M_U / (1 − β)`,  where `M_U` bounds the stage payoff in sup-norm.

Economically: a carrier radius is never a free design choice. It is the
discounted geometric sum `M_U · (1 + β + β² + …)` of the largest stage
payoff the players can ever collect, and any smaller ball is not
invariant while any larger one is slack. Shipping the radius as this
closed form is what removes hand-chosen carrier magnitudes from the
witnesses.

**Where `M_U` comes from, and why it is an argument.** SLP Theorem 3.1
(`cube_bound_unitCube_of_continuous` above) guarantees such an `M_U`
exists for any continuous stage payoff, but it is an *existence*
statement (`∃ M, 0 ≤ M ∧ …`), so it yields a bound only under `obtain`
— there is no `‖U‖_cube` term in this development to name. Consumers
therefore pass `M_U` in as an explicit scalar argument to the theorem.
That is a theorem-bound scalar, discharged at each call site by
arithmetic on the primitives; it is never a `Params` field and never
widens the assumption surface. -/

/-- **Closed-form sup-norm radius margin (algebra).** Given a stage-payoff
sup-norm bound `M_U ≥ 0` and a discount factor `β < 1`, the closed-form
carrier radius `M := M_U / (1 − β)` is non-negative and satisfies the
cone-margin identity `M_U + β · M = M`.

This is the radius analogue of `bellman_closed_form_lipschitz_margin`
(Hinderer-4.2(c) slope) and `bellman_closed_form_lowerSlope_margin` (Hinderer-4.2(c) lower-slope
slope). The identity is exactly what makes a sup-norm ball of radius `M`
*invariant* under a Bellman operator whose stage payoff is bounded by
`M_U`: the image is bounded by `M_U + β · M`, which the identity says is
again `M`. It is tight — no smaller radius is invariant.

Kept at the Foundations layer (no `Params`, no BCF type) so it can be
cited generically. -/
theorem bellman_closed_form_norm_margin
    {β M_U : ℝ}
    (hM_U_nn : 0 ≤ M_U) (_hβ_nn : 0 ≤ β) (h_contract : β < 1) :
    0 ≤ M_U / (1 - β) ∧ M_U + β * (M_U / (1 - β)) = M_U / (1 - β) := by
  have h_denom_pos : 0 < 1 - β := by linarith
  have h_denom_ne : (1 - β) ≠ 0 := ne_of_gt h_denom_pos
  refine ⟨div_nonneg hM_U_nn (le_of_lt h_denom_pos), ?_⟩
  field_simp
  ring

/-- **Closed-form sup-norm carrier radius (named).** The Bellman carrier
radius in closed form: `M := M_U / (1 − β)` from a stage-payoff sup-norm
bound `M_U` and discount factor `β < 1`. Mirrors `bellmanLipConstant`
(R25) and `bellmanLowerSlopeConstant` (R27); together the three closed
forms determine every magnitude of a slope-pinned carrier ball
`valLipGainBall M K g 0` from the primitives, with nothing left to
choose by hand. -/
def bellmanNormBound (β M_U : ℝ) : ℝ := M_U / (1 - β)

/-- Unfold lemma for `bellmanNormBound`. -/
@[simp] theorem bellmanNormBound_def (β M_U : ℝ) :
    bellmanNormBound β M_U = M_U / (1 - β) := rfl

/-- The radius closed form **is** the Hinderer 4.2(c) slope closed form evaluated at
transition multiplier `γ = 1`: sup-norm is transported by the state map
without contraction, so the geometric series is damped by `β` alone. -/
theorem bellmanNormBound_eq_bellmanLipConstant (β M_U : ℝ) :
    bellmanNormBound β M_U = bellmanLipConstant β 1 M_U := by
  simp only [bellmanNormBound, bellmanLipConstant, mul_one]

/-- The **upper** Lipschitz closed form and the **lower**
envelope-slope closed form are the same expression. On a slope-*pinned*
carrier — one that demands Lipschitz constant `K` and minimum upward
slope `g` with `K = g`, forcing its members to be exactly affine with
that slope — the two SLP constants therefore coincide, and a single
closed form fills both slots. -/
theorem bellmanLowerSlopeConstant_eq_bellmanLipConstant (β γ g : ℝ) :
    bellmanLowerSlopeConstant β γ g = bellmanLipConstant β γ g := rfl

/-- **Sup-difference lower bound for indexed families** (companion of
`Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd` in
`Foundations/SupDiff.lean`).

If `h` and `f` are real-valued families on a nonempty index set `K` with
both images `BddAbove`, and `L ≤ f a − h a` holds pointwise on `K`, then
the same lower bound transfers to the suprema:
`L ≤ sSup (f '' K) − sSup (h '' K)`.

Proof: for every `a ∈ K`, `h a ≤ f a − L ≤ sSup (f '' K) − L`. So
`sSup (h '' K) ≤ sSup (f '' K) − L`, i.e. `L ≤ sSup (f '' K) − sSup (h '' K)`.

Round 27 uses this lemma at the BCF level (`Theory/Bellman/InvariantLipGainBall.lean`)
to lift a uniform pointwise lower-slope on the integrand
`joint_T_integrand V_T V_S` to a lower slope on the joint Target Bellman
operator's value `sSup`-over-`a`. -/
theorem sSup_image_sub_sSup_image_lowerBound_of_pointwise
    {α : Type*} {f h : α → ℝ} {K : Set α}
    (hK : K.Nonempty) {L : ℝ}
    (h_point : ∀ a ∈ K, L ≤ f a - h a)
    (hf_bdd : BddAbove (f '' K)) :
    L ≤ sSup (f '' K) - sSup (h '' K) := by
  have step : ∀ a ∈ K, h a ≤ sSup (f '' K) - L := by
    intro a ha
    have h_f_le_sup : f a ≤ sSup (f '' K) :=
      le_csSup hf_bdd ⟨a, ha, rfl⟩
    have h_diff : L ≤ f a - h a := h_point a ha
    linarith
  have h_sup_h : sSup (h '' K) ≤ sSup (f '' K) - L := by
    apply csSup_le (hK.image h)
    rintro _ ⟨a, ha, rfl⟩
    exact step a ha
  linarith

/-! ## Cone preservation from a single joint chord

The abstract content shared by the Sender-side and Target-side lower-slope
preservation arguments. Both were written separately against the `Params`-level
objectives, and both reduce to the one inequality below.

**Why a joint chord and not a chord on the transition.** A slope floor
`g·(y₂−y₁) ≤ W y₂ − W y₁` with `g > 0` is *not* a closed convex cone property —
scaling `W` by a factor below one drops the floor — so the Smith–McCardle
metatheorem (*Structural Properties of Stochastic Dynamic Programs*, Operations
Research 50(5), 796–809, 2002) does not apply to it directly, and an argument
written naively needs a linear chord on the transition to compensate. But `W` has
lower slope `g` exactly when `W − g·id` is increasing, and monotonicity *is* a
cone property (their §6; classically Stokey–Lucas 1989, pp. 267–268). Translating
the recursion through that change of variable puts the transition inside a
modified reward, so the hypothesis becomes a single chord in which payoff and
transition appear together and neither is constrained alone.

Economically the joint form is also the weaker and more natural one: it lets the
stage payoff compensate wherever the transition is flat, which separate
conditions on each cannot express. -/

/-- **Pointwise cone step for an abstract Bellman integrand.**

For an integrand `x ↦ u x s + β · W (F x s)` at a fixed action `s`: if `W` has
lower slope `g` on `B`, the successor states stay in `B` and are ordered, and the
joint chord holds, then the integrand itself has lower slope `g` between `x₁` and
`x₂`.

No functional form is imposed on `F`. It appears only inside the joint chord and
through the ordering of successors — which, note, must be supplied rather than
derived whenever the action itself moves with the state. -/
theorem lowerSlope_integrand_of_joint_chord
    {u F : ℝ → ℝ → ℝ} {W : ℝ → ℝ} {β g : ℝ} {B : Set ℝ}
    (hβ : 0 ≤ β)
    {x₁ x₂ s : ℝ}
    (hF₁ : F x₁ s ∈ B) (hF₂ : F x₂ s ∈ B)
    (hFle : F x₁ s ≤ F x₂ s)
    (hW : ∀ y₁ ∈ B, ∀ y₂ ∈ B, y₁ ≤ y₂ → g * (y₂ - y₁) ≤ W y₂ - W y₁)
    (hchord :
      g * (x₂ - x₁) ≤ (u x₂ s - u x₁ s) + β * g * (F x₂ s - F x₁ s)) :
    g * (x₂ - x₁)
      ≤ (u x₂ s + β * W (F x₂ s)) - (u x₁ s + β * W (F x₁ s)) := by
  have hWc := hW _ hF₁ _ hF₂ hFle
  have hscaled : β * (g * (F x₂ s - F x₁ s))
      ≤ β * (W (F x₂ s) - W (F x₁ s)) :=
    mul_le_mul_of_nonneg_left hWc hβ
  nlinarith [hchord, hscaled]

end StokeyLucas
end Sanctions

end

#print axioms Sanctions.StokeyLucas.blackwell_lipschitz
#print axioms Sanctions.StokeyLucas.blackwell_fixedPoint
#print axioms Sanctions.StokeyLucas.fixedPoint_mem_image_of_mapsTo
