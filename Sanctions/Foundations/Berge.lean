/-
Sanctions/Foundations/Berge.lean

**Berge's Maximum Theorem (existence + uniqueness skeleton) for a
compact choice set and a strictly-concave-in-choice objective.**

Generic Foundations-layer module supporting Round 32's σ-quad shrink
on `AbstractGame.Params`. The application to `Params`
(`Params.ofStrictConcaveUS` — the alternative constructor that
replaces the four sigma-quad fields with a single optional
strict-concavity primitive on `U_S` in `s`) lives in
`Sanctions/Theory/Equilibrium/SigmaParamsRefactor.lean`.

## Literature anchors

* **Stokey-Lucas-Prescott 1989 §3.7** — for a continuous objective on a
  compact constraint set, the value function is continuous and the
  policy correspondence is non-empty and compact-valued; under strict
  concavity the policy correspondence is single-valued (a continuous
  selector).
* **Aliprantis-Border 2006 Theorem 17.31 (Berge's Maximum Theorem)** —
  general upper hemicontinuity / single-valuedness of the argmax
  correspondence over a continuous, compact-valued constraint.

The two results combined: a jointly-continuous objective that is
strictly concave in the choice variable, over a compact, convex,
non-empty constant choice set, has a *unique* maximizer at every
parameter point, and the resulting selector is continuous in the
parameter (the latter via the existing Berge-style argument in
`Theory/Equilibrium/BergeContinuity.lean`).

## Scope of this module

We expose the existence, uniqueness, and continuous-selector parts of
the generic Berge theorem:

* `Sanctions.Foundations.Berge.exists_unique_argmax_of_continuous_strictConcaveOn` —
  given a non-empty compact convex set `K ⊆ ℝ` and a continuous
  function `f : ℝ → ℝ` that is strictly concave on `K`, the maximizer
  on `K` exists and is unique (i.e. `∃! a ∈ K, IsMaxOn f K a`).
* `Sanctions.Foundations.Berge.argmax` — the parametric
  `Classical.choose` selector, carrying membership, maximality, and
  uniqueness specifications.
* `Sanctions.Foundations.Berge.argmax_continuous` — the generic
  continuous-selector conclusion for a jointly continuous family over a
  metric parameter space.

## Rule compliance

* **Rule 1.** No strategies. Pure analysis.
* **Rule 4.** Foundations-only mathematical content.
* **Rule 5.** Fully parametric over the objective and the parameter
  type.
* **Rule 8.** Plain-language docstrings on every declaration.
* **Rule 10.** Every new theorem is intended to be `#print axioms`
  clean (only `propext`, `Classical.choice`, `Quot.sound`).
* **Rule 19.** External theory (SLP §3.7 / Aliprantis-Border Berge)
  lives in `Foundations/`; Params-level wrappers live in
  `Theory/Equilibrium/SigmaParamsRefactor.lean`.
-/

import Sanctions.Foundations.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Strict

namespace Sanctions
namespace Foundations
namespace Berge

open Set Filter Topology

noncomputable section

/-! ## §1 Generic existence + uniqueness (single-objective form) -/

/-- **Strictly concave on a convex set ⇒ at most one maximizer.**

If `f : ℝ → ℝ` is strictly concave on a convex set `K`, then any two
`IsMaxOn`-witnesses on `K` must agree. Standard midpoint argument:
two distinct maximizers `s₁ ≠ s₂` would have midpoint in `K` by
convexity, with `f((s₁+s₂)/2) > (f s₁ + f s₂)/2 = f-max`, contradicting
maximality at the midpoint.

This is the scalar generic version of the existing project-specific
`Sanctions.AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn` in
`Theory/Equilibrium/ArgmaxUniquenessFromConcavity.lean` (which has the
same statement and proof but is structured as a `Params` namespace
method). The duplication is deliberate: this module is generic and
imports nothing from `AbstractGame`, while the project-specific
helper consumes the same lemma in Bellman contexts. -/
theorem isMaxOn_unique_of_strictConcaveOn
    {f : ℝ → ℝ} {K : Set ℝ}
    (hconc : StrictConcaveOn ℝ K f)
    {s₁ s₂ : ℝ}
    (hs₁ : s₁ ∈ K) (hs₂ : s₂ ∈ K)
    (h₁ : IsMaxOn f K s₁) (h₂ : IsMaxOn f K s₂) :
    s₁ = s₂ := by
  by_contra hne
  have hconv : Convex ℝ K := hconc.1
  have hmid_mem : ((1/2 : ℝ)) • s₁ + ((1/2 : ℝ)) • s₂ ∈ K :=
    hconv hs₁ hs₂ (by norm_num) (by norm_num) (by norm_num)
  have hstrict :
      ((1/2 : ℝ)) • f s₁ + ((1/2 : ℝ)) • f s₂
        < f (((1/2 : ℝ)) • s₁ + ((1/2 : ℝ)) • s₂) :=
    hconc.2 hs₁ hs₂ hne (by norm_num) (by norm_num) (by norm_num)
  have hmid_le_s₁ : f (((1/2 : ℝ)) • s₁ + ((1/2 : ℝ)) • s₂) ≤ f s₁ :=
    h₁ hmid_mem
  have hs₂_le_s₁ : f s₂ ≤ f s₁ := h₁ hs₂
  have hs₁_le_s₂ : f s₁ ≤ f s₂ := h₂ hs₁
  have heq : f s₁ = f s₂ := le_antisymm hs₁_le_s₂ hs₂_le_s₁
  have : ((1/2 : ℝ)) • f s₁ + ((1/2 : ℝ)) • f s₂ = f s₁ := by
    rw [heq]; simp; ring
  linarith [hstrict, hmid_le_s₁, this]

/-- **Berge skeleton (existence + uniqueness, scalar form).**

If `K ⊆ ℝ` is nonempty and compact, and `f : ℝ → ℝ` is continuous on
`K` and strictly concave on `K`, then there is a *unique* maximizer
of `f` on `K`. Combines Weierstrass (compact + continuous ⇒ max
attained, via `IsCompact.exists_isMaxOn`) and the midpoint uniqueness
lemma above.

The `ExistsUnique` packaging makes downstream `Classical.choose`-based
selectors automatically carry both the existence and the uniqueness
witness in one bundle. -/
theorem exists_unique_argmax_of_continuous_strictConcaveOn
    {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hfc : ContinuousOn f K) (hconc : StrictConcaveOn ℝ K f) :
    ∃! s ∈ K, IsMaxOn f K s := by
  obtain ⟨s, hs_mem, hs_max⟩ := hK.exists_isMaxOn hKne hfc
  refine ⟨s, ⟨hs_mem, hs_max⟩, ?_⟩
  intro s' hs'
  obtain ⟨hs'_mem, hs'_max⟩ := hs'
  exact (isMaxOn_unique_of_strictConcaveOn hconc hs'_mem hs_mem hs'_max hs_max)

/-! ## §2 Parametric Classical.choose-selector

The Round-32 σ-quad shrink consumes a Classical.choose-based selector
that, for every parameter `θ : Θ`, returns the unique maximizer of
the family member `f θ : ℝ → ℝ` on `K`. The selector is automatically
continuous in `θ` whenever `f` is jointly continuous (Berge's
continuous-selector half, proved below as `argmax_continuous`).
Project-specific continuity is delegated to
`Theory/Equilibrium/BergeContinuity.lean` (for the σ_dyn use case); the
σ-quad refactor, which took the selector's continuity as a local
hypothesis, now derives it from `argmax_continuous`
(`bergeSigma_continuous`, round BJ5.1). -/

/-- **Parametric Berge existence (pure existence form).**

For a parameter `θ` and a function `f θ : ℝ → ℝ` continuous on a
nonempty compact `K` and strictly concave on `K`, there exists a
unique maximizer. This is the per-`θ` instance of
`exists_unique_argmax_of_continuous_strictConcaveOn`, packaged so a
downstream `Classical.choose` can produce a function
`argmax : Θ → ℝ` together with the per-`θ` membership and
maximality specs. -/
theorem exists_unique_argmax_param
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K)
    (hconc : ∀ θ, StrictConcaveOn ℝ K (f θ)) (θ : Θ) :
    ∃! s ∈ K, IsMaxOn (f θ) K s :=
  exists_unique_argmax_of_continuous_strictConcaveOn hK hKne (hfc θ) (hconc θ)

/-- **Parametric Berge selector (Classical.choose form).**

The Classical.choose-built per-parameter argmax selector. By
construction, `argmax θ` is the unique maximizer of `f θ` on `K`.

The selector is `noncomputable` (it depends on `Classical.choose`).
Its membership and maximality specs are exposed as
`argmax_mem` and `argmax_isMaxOn`; uniqueness is exposed as
`argmax_eq_of_isMaxOn`. -/
noncomputable def argmax
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K)
    (hconc : ∀ θ, StrictConcaveOn ℝ K (f θ)) (θ : Θ) : ℝ :=
  Classical.choose ((exists_unique_argmax_param hK hKne hfc hconc θ).exists)

/-- **The parametric Berge selector lies in `K`.** -/
theorem argmax_mem
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K)
    (hconc : ∀ θ, StrictConcaveOn ℝ K (f θ)) (θ : Θ) :
    argmax hK hKne hfc hconc θ ∈ K := by
  have h :=
    Classical.choose_spec ((exists_unique_argmax_param hK hKne hfc hconc θ).exists)
  exact h.1

/-- **The parametric Berge selector is a maximizer of `f θ` on `K`.** -/
theorem argmax_isMaxOn
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K)
    (hconc : ∀ θ, StrictConcaveOn ℝ K (f θ)) (θ : Θ) :
    IsMaxOn (f θ) K (argmax hK hKne hfc hconc θ) := by
  have h :=
    Classical.choose_spec ((exists_unique_argmax_param hK hKne hfc hconc θ).exists)
  exact h.2

/-- **The parametric Berge selector is unique.** Any other
`IsMaxOn`-witness on `K` equals it (a one-line specialization of
`isMaxOn_unique_of_strictConcaveOn`). -/
theorem argmax_eq_of_isMaxOn
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K)
    (hconc : ∀ θ, StrictConcaveOn ℝ K (f θ)) (θ : Θ)
    {s : ℝ} (hs_mem : s ∈ K) (hs_max : IsMaxOn (f θ) K s) :
    s = argmax hK hKne hfc hconc θ :=
  isMaxOn_unique_of_strictConcaveOn (hconc θ) hs_mem
    (argmax_mem hK hKne hfc hconc θ) hs_max
    (argmax_isMaxOn hK hKne hfc hconc θ)

/-- **Continuous parametric Berge selector.** Let the parameter space be
metric, let the scalar choice set be nonempty and compact, and suppose the
objective is jointly continuous and strictly concave in the choice at every
parameter. Then the `Classical.choose` selector `argmax` defined above is
continuous in the parameter.

The proof is the sequential compactness argument behind Berge's maximum
theorem: any discontinuity sequence has an argmax subsequence converging in
the compact choice set; joint continuity makes its limit an argmax at the
limit parameter, and strict concavity identifies it with the unique selected
argmax, contradicting the alleged jump. -/
theorem argmax_continuous
    {Θ : Type*} [MetricSpace Θ] {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K)
    (hconc : ∀ θ, StrictConcaveOn ℝ K (f θ))
    (hjoint : Continuous (fun θa : Θ × ℝ => f θa.1 θa.2)) :
    Continuous (argmax hK hKne hfc hconc) := by
  rw [Metric.continuous_iff]
  intro θ₀ ε hε
  by_contra h_neg
  push Not at h_neg
  choose θ_seq h_close h_far using fun n : ℕ =>
    h_neg (1 / (n + 1)) (by positivity)
  have hθ_tendsto : Tendsto θ_seq atTop (𝓝 θ₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    calc dist (θ_seq n) θ₀
        < 1 / (n + 1) := h_close n
      _ ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < δ := hN
  set a_seq : ℕ → ℝ :=
    fun n => argmax hK hKne hfc hconc (θ_seq n) with ha_def
  have ha_mem : ∀ n, a_seq n ∈ K :=
    fun n => argmax_mem hK hKne hfc hconc _
  obtain ⟨aStar, haStar_mem, φ, hφ_mono, h_sub_tendsto⟩ :=
    hK.tendsto_subseq ha_mem
  have hθ_sub_tendsto : Tendsto (θ_seq ∘ φ) atTop (𝓝 θ₀) :=
    hθ_tendsto.comp hφ_mono.tendsto_atTop
  have h_a_max_sub : ∀ n, IsMaxOn
      (f (θ_seq (φ n))) K (a_seq (φ n)) :=
    fun n => argmax_isMaxOn hK hKne hfc hconc _
  have h_aStar_max : IsMaxOn (f θ₀) K aStar := by
    intro a' ha'
    have h_ptn : ∀ n,
        f (θ_seq (φ n)) a' ≤ f (θ_seq (φ n)) (a_seq (φ n)) :=
      fun n => h_a_max_sub n ha'
    have h_lhs := (hjoint.tendsto (θ₀, a')).comp
      (hθ_sub_tendsto.prodMk_nhds (tendsto_const_nhds (x := a')))
    have h_rhs := (hjoint.tendsto (θ₀, aStar)).comp
      (hθ_sub_tendsto.prodMk_nhds h_sub_tendsto)
    exact le_of_tendsto_of_tendsto' h_lhs h_rhs h_ptn
  have h_eq : aStar = argmax hK hKne hfc hconc θ₀ :=
    argmax_eq_of_isMaxOn hK hKne hfc hconc θ₀ haStar_mem h_aStar_max
  rw [h_eq] at h_sub_tendsto
  have h_far_sub : ∀ n,
      ε ≤ dist (a_seq (φ n)) (argmax hK hKne hfc hconc θ₀) := by
    intro n
    rw [ha_def]
    linarith [h_far (φ n)]
  have h_tendsto_zero :
      Tendsto (fun n => dist (a_seq (φ n))
        (argmax hK hKne hfc hconc θ₀)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = dist (argmax hK hKne hfc hconc θ₀)
        (argmax hK hKne hfc hconc θ₀) from (dist_self _).symm]
    exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp
      h_sub_tendsto
  have h_zero_ge_ε : ε ≤ 0 := by
    apply ge_of_tendsto h_tendsto_zero
    exact Filter.Eventually.of_forall h_far_sub
  linarith

end


/-! ## Sequential closed-graph of the argmax (Round E2)

Limit of maximizers is a maximizer: if `s n` maximizes `Φ (x n)` over
a fixed closed constraint set and `(x n, s n) → (x*, s*)` with `Φ`
jointly continuous, then `s*` maximizes `Φ x*`. The sequential form
of Berge upper hemicontinuity over a *fixed* constraint set — no
compactness needed, only continuity and closedness. Used to identify
the lock-in limit as an equilibrium-consistent steady state. -/

/-- **Limit of maximizers is a maximizer.** -/
theorem isMaxOn_of_tendsto_of_isMaxOn {X : Type*} [TopologicalSpace X]
    {Φ : X → ℝ → ℝ} (hΦ : Continuous fun q : X × ℝ => Φ q.1 q.2)
    {K : Set ℝ} (hK : IsClosed K)
    {x : ℕ → X} {s : ℕ → ℝ} {xs : X} {ss : ℝ}
    (hx : Filter.Tendsto x Filter.atTop (nhds xs))
    (hs : Filter.Tendsto s Filter.atTop (nhds ss))
    (hmem : ∀ n, s n ∈ K)
    (hmax : ∀ n, IsMaxOn (Φ (x n)) K (s n)) :
    ss ∈ K ∧ IsMaxOn (Φ xs) K ss := by
  have hssK : ss ∈ K :=
    hK.mem_of_tendsto hs (Filter.Eventually.of_forall hmem)
  refine ⟨hssK, fun y hy => ?_⟩
  have h1 : Filter.Tendsto (fun n => Φ (x n) y) Filter.atTop
      (nhds (Φ xs y)) := by
    have hcont : Continuous fun t : X => Φ t y :=
      hΦ.comp (continuous_id.prodMk continuous_const)
    exact (hcont.tendsto xs).comp hx
  have h2 : Filter.Tendsto (fun n => Φ (x n) (s n)) Filter.atTop
      (nhds (Φ xs ss)) := by
    have := hΦ.tendsto (xs, ss)
    exact this.comp (hx.prodMk_nhds hs)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun n => hmax n hy)

end Berge
end Foundations
end Sanctions
