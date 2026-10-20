/-
Sanctions/Foundations/BalbusReffettWozny.lean

**Balbus–Reffett–Woźny 2014 *JET* — supermodular-only existence of
extremal Nash equilibrium selectors over a compact lattice.**

Generic Foundations-layer module supporting Round 33's σ-quad shrink
on `AbstractGame.Params` along an alternative route to Round 32.
Where Round 32 (`Sanctions/Foundations/Berge.lean`) used **strict
concavity** in the choice variable to deliver a **unique** argmax
and hence the σ-quad's `σ_isMaxOn_U_S`/`σ_mem`/`σ_continuous` content
(the last a `Params` field until round BJ5.1, 2026-10-07, now the instance
`Params.StaticSelectorContinuous`), Round 33 uses **supermodularity + increasing differences**
only — no strict concavity — to deliver an *extremal* (greatest /
least) argmax selector via Weierstrass on the **closed sublattice
of maximizers**.

## Why "Path A" matters for this project

The minimal non-vacuity witness `polyComplianceParams`
(`Sanctions/Examples/StandardCompliancePolynomialSkeleton.lean`) uses
`U_S(x, a, s) = s` — **linear in `s`**. Linear functions are *not*
strictly concave on `[0, 1]`, so the Round-32 alternative
constructor `Params.ofStrictConcaveUS` does not apply at this
witness (the strict-concavity hypothesis fails). However, linear
functions *are* supermodular (and any one-dimensional function is
trivially supermodular), and `U_S = s` trivially has increasing
differences in `(s, a)` (it is constant in `a`). So a
**supermodular-only** σ-quad shrink route applies cleanly at
`polyComplianceParams` — recovering the 4-into-1 economy of
Round 32 along a route that handles linear `U_S` correctly.

## Literature anchor

* **Balbus, Reffett & Woźny 2014 *Journal of Economic Theory* 150,
  815–840 — "A constructive study of Markov equilibria in stochastic
  games with strategic complementarities"** (in
  `PaperRefer/MathTheory/ConstructiveMarkovEquilibria-BalbusReffettWozny-2013.md`).
  - **Theorem 3.1** (existence and approximation of stationary
    Markov Nash equilibria): under Assumptions 1 + 2
    (supermodularity + increasing differences + continuity +
    measurability of the transition), the auxiliary game has both a
    *greatest* and a *least* Nash equilibrium, both monotone in the
    continuation value.
  - **Lemma 5.1** (monotone Nash equilibria in `G_v^s`): for every
    state `s` and continuation `v`, the auxiliary game has the
    maximal Nash equilibrium `\bar a(v, s)` and the minimal Nash
    equilibrium `\underline a(v, s)`, both increasing in `v`.

The substantive structural input is **Topkis 1998 Theorem 2.7.1**
(argmax of a supermodular function on a lattice is a sublattice —
closed under `⊓` and `⊔`) plus **Tarski's fixed-point theorem**
(Topkis 1998 Corollary 2.5.1). The single-player single-choice
specialization we use here (one Sender choosing `s ∈ [0, 1]`)
collapses the supermodular-game lattice argument to the standard
"continuous function on compact interval has a greatest argmax"
construction, but the structural decomposition is identical — the
σ-quad shrink lands in `Theory/Equilibrium/SigmaParamsRefactor.lean`
via the same wrapper pattern as Round 32.

## Scope of this module

We expose the **extremal-selection** (greatest-argmax) half of BRW's
Theorem 3.1 + Lemma 5.1 specialized to a single-player choice on
a compact subset of `ℝ`:

* `Sanctions.Foundations.BalbusReffettWozny.argmax_set_isCompact` —
  the argmax set `{s ∈ K | IsMaxOn f K s}` of a continuous-on-`K`
  function on a compact `K ⊆ ℝ` is compact.
* `Sanctions.Foundations.BalbusReffettWozny.exists_isGreatest_argmax_of_continuous` —
  the argmax set has a *greatest* element under continuity alone (no
  strict concavity, no supermodularity); this is the **Path A
  existence half** for the σ-quad shrink.
* `Sanctions.Foundations.BalbusReffettWozny.exists_isLeast_argmax_of_continuous` —
  dual; the *least* argmax exists.
* `Sanctions.Foundations.BalbusReffettWozny.exists_isGreatest_argmax_param` —
  parametric form for a family `f : Θ → ℝ → ℝ` with `f θ`
  continuous on `K` for every `θ`, producing a per-`θ` greatest
  argmax.
* `Sanctions.Foundations.BalbusReffettWozny.greatestArgmax` — the
  `Classical.choose`-built per-parameter greatest-argmax selector;
  spec lemmas `greatestArgmax_mem`, `greatestArgmax_isMaxOn`,
  `greatestArgmax_greatest`.

The **continuity-of-selector** half (Berge's continuous-selector
output) is not delivered here: the greatest selector need not be continuous.
Since round BJ5.1 (2026-10-07) it is not needed to build a `Params` either; it
is the instance `Params.StaticSelectorContinuous`, supplied where it holds
(`ofSupermodularUSF_staticSelectorContinuous`). The
substantive shrink delivered here is the 4-into-1 collapse on the
σ-quad's **content** fields (Rule 1 + feasibility + extremality from
a supermodular structure rather than from a strict-concavity
uniqueness argument).

## Why one-dimensional choice is the right specialization

The full BRW 2014 Theorem 3.1 handles `n`-player stochastic games
with multidimensional action spaces `A_i ⊂ ℝ^{k_i}`. For this
project the Sender problem reduces to a single choice `s ∈ [0, 1]`
of a one-dimensional action against a fixed `(x, a)` pair, so the
supermodular-game lattice argument collapses: the argmax set is
trivially a sublattice of `ℝ` (any non-empty closed subset of `ℝ`
is a sublattice under `⊓ = min`, `⊔ = max`), and the greatest
element exists by Weierstrass applied to the identity function on
the (closed, bounded) argmax set. The "supermodular-only" framing
remains the economically correct generalization — for any future
multidimensional Sender problem the same wrapper pattern applies
with the genuine sublattice argument substituted; the structural
roles of the inputs (supermodularity in the choice variable,
increasing differences in the parameter) match BRW's signature
exactly.

## Rule compliance

* **Rule 1.** No strategies. Pure analysis.
* **Rule 4.** Foundations-only mathematical content (BRW 2014 +
  Topkis 1998 lattice machinery + mathlib's Weierstrass).
* **Rule 5.** Fully parametric over the objective and the parameter
  type.
* **Rule 8.** Plain-language docstrings on every declaration.
* **Rule 9.** RETIRED 2026-06-04; no witness obligation for this
  Foundations-layer module.
* **Rule 10.** Every new theorem is `#print axioms` clean (only
  `propext`, `Classical.choice`, `Quot.sound`).
* **Rule 19.** External theory (BRW 2014 / Topkis 1998) lives in
  `Foundations/` named after the source; Params-level wrappers
  live in `Theory/Equilibrium/SigmaParamsRefactor.lean` alongside the
  Round-32 strict-concavity wrappers.
-/

import Sanctions.Foundations.Basic
import Sanctions.Foundations.Topkis
import Mathlib.Topology.Order.Compact

namespace Sanctions
namespace Foundations
namespace BalbusReffettWozny

open Set

noncomputable section

/-! ## §1 Argmax set is compact (continuity-only structural fact) -/

/-- **The argmax set on a compact `K ⊆ ℝ` is compact.**

For any `f : ℝ → ℝ` continuous on a compact `K ⊆ ℝ`, the set of
maximizers `{s ∈ K | IsMaxOn f K s}` is compact: it equals
`K ∩ f ⁻¹' {M}` where `M := f x₀` is the common max value, hence
closed in `K` by `ContinuousOn.preimage_isClosed_of_isClosed`, hence
compact as a closed subset of the compact `K`.

This is the **continuity-only** structural fact that the
supermodular-only BRW Path A consumes: no concavity, no
supermodularity, no measurability is needed at this layer. -/
theorem argmax_set_isCompact
    {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hfc : ContinuousOn f K) :
    IsCompact {s : ℝ | s ∈ K ∧ IsMaxOn f K s} := by
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := hK.exists_isMaxOn hKne hfc
  -- The argmax set equals `K ∩ f ⁻¹' {f x₀}`.
  have h_eq :
      {s : ℝ | s ∈ K ∧ IsMaxOn f K s} = K ∩ f ⁻¹' {f x₀} := by
    ext s
    refine ⟨?_, ?_⟩
    · rintro ⟨hs_mem, hs_max⟩
      refine ⟨hs_mem, ?_⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact le_antisymm (hx₀_max hs_mem) (hs_max hx₀_mem)
    · rintro ⟨hs_mem, hs_val⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs_val
      refine ⟨hs_mem, fun y hy => ?_⟩
      have : f y ≤ f x₀ := hx₀_max hy
      rw [hs_val]; exact this
  have hKclosed : IsClosed K := hK.isClosed
  have hClosed : IsClosed ({s : ℝ | s ∈ K ∧ IsMaxOn f K s}) := by
    rw [h_eq]
    exact hfc.preimage_isClosed_of_isClosed (t := {f x₀}) hKclosed isClosed_singleton
  exact hK.of_isClosed_subset hClosed (fun s hs => hs.1)

/-! ## §2 Extremal (greatest / least) argmax selectors

The BRW Path A delivers a *greatest* and *least* argmax selector
from the sublattice structure of the argmax set under
supermodularity. In the one-dimensional choice specialization
(`K ⊆ ℝ`) the argmax set is already a sublattice (any closed
subset of `ℝ` is closed under `min`/`max`), so the greatest and
least elements exist by Weierstrass on the identity function. -/

/-- **Greatest argmax exists (BRW Path A, single-choice specialization).**

For `f : ℝ → ℝ` continuous on a nonempty compact `K ⊆ ℝ`, there is
a *greatest* maximizer: an `s* ∈ K` with `IsMaxOn f K s*` and
`∀ t ∈ K, IsMaxOn f K t → t ≤ s*`.

Proof: the argmax set is compact (by `argmax_set_isCompact`) and
non-empty (by Weierstrass), so applying Weierstrass again to the
identity function on the argmax set produces its maximum element —
which is the greatest maximizer of `f` on `K`. This is the
**Path A existence** the σ-quad shrink consumes when `U_S` is
*not* strictly concave (e.g. linear `U_S = s` at
`polyComplianceParams`). -/
theorem exists_isGreatest_argmax_of_continuous
    {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hfc : ContinuousOn f K) :
    ∃ s ∈ K, IsMaxOn f K s ∧ ∀ t ∈ K, IsMaxOn f K t → t ≤ s := by
  set S : Set ℝ := {s | s ∈ K ∧ IsMaxOn f K s}
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := hK.exists_isMaxOn hKne hfc
  have hSne : S.Nonempty := ⟨x₀, hx₀_mem, hx₀_max⟩
  have hS_compact : IsCompact S := argmax_set_isCompact hK hKne hfc
  obtain ⟨smax, hsmax_mem, hsmax_ismax⟩ :=
    hS_compact.exists_isMaxOn hSne continuousOn_id
  refine ⟨smax, hsmax_mem.1, hsmax_mem.2, ?_⟩
  intro t htK htMax
  exact hsmax_ismax ⟨htK, htMax⟩

/-- **Least argmax exists (BRW Path A, dual).**

Dual of `exists_isGreatest_argmax_of_continuous`: the *least*
maximizer exists by Weierstrass on the identity function (taken
with the dual order — equivalently, `-id`). -/
theorem exists_isLeast_argmax_of_continuous
    {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hfc : ContinuousOn f K) :
    ∃ s ∈ K, IsMaxOn f K s ∧ ∀ t ∈ K, IsMaxOn f K t → s ≤ t := by
  set S : Set ℝ := {s | s ∈ K ∧ IsMaxOn f K s}
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := hK.exists_isMaxOn hKne hfc
  have hSne : S.Nonempty := ⟨x₀, hx₀_mem, hx₀_max⟩
  have hS_compact : IsCompact S := argmax_set_isCompact hK hKne hfc
  -- Apply the dual (sInf form) — equivalently apply exists_isMaxOn to (fun x => -x).
  obtain ⟨smin, hsmin_mem, hsmin_ismin⟩ :=
    hS_compact.exists_isMinOn hSne continuousOn_id
  refine ⟨smin, hsmin_mem.1, hsmin_mem.2, ?_⟩
  intro t htK htMax
  exact hsmin_ismin ⟨htK, htMax⟩

/-! ## §3 Parametric Classical.choose selectors

For a family `f : Θ → ℝ → ℝ` continuous in the choice variable
for every parameter `θ`, the per-`θ` greatest argmax exists, and
Classical.choose produces a Skolemized selector
`greatestArgmax : Θ → ℝ`. This is the Path-A counterpart to the
Round-32 `Berge.argmax` selector (which assumed strict concavity
and produced a *unique* argmax). -/

/-- **Parametric Path-A existence (greatest form).**

The per-parameter version of `exists_isGreatest_argmax_of_continuous`:
for a family `f : Θ → ℝ → ℝ` with `f θ` continuous on `K` for every
`θ`, the greatest argmax exists for every `θ`. -/
theorem exists_isGreatest_argmax_param
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K) (θ : Θ) :
    ∃ s ∈ K, IsMaxOn (f θ) K s ∧ ∀ t ∈ K, IsMaxOn (f θ) K t → t ≤ s :=
  exists_isGreatest_argmax_of_continuous hK hKne (hfc θ)

/-- **The Path-A greatest-argmax Classical.choose selector.**

For a family `f : Θ → ℝ → ℝ` with `f θ` continuous on `K` for every
`θ`, returns the greatest maximizer of `f θ` on `K` (existence
guaranteed by `exists_isGreatest_argmax_param`). The selector is
`noncomputable`. Its membership, maximality, and greatest-element
specs are exposed as `greatestArgmax_mem`, `greatestArgmax_isMaxOn`,
and `greatestArgmax_greatest`. -/
noncomputable def greatestArgmax
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K) (θ : Θ) : ℝ :=
  Classical.choose (exists_isGreatest_argmax_param hK hKne hfc θ)

/-- **The Path-A greatest-argmax selector lies in `K`.** -/
theorem greatestArgmax_mem
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K) (θ : Θ) :
    greatestArgmax hK hKne hfc θ ∈ K := by
  have h := Classical.choose_spec (exists_isGreatest_argmax_param hK hKne hfc θ)
  exact h.1

/-- **The Path-A greatest-argmax selector is a maximizer of `f θ` on `K`.** -/
theorem greatestArgmax_isMaxOn
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K) (θ : Θ) :
    IsMaxOn (f θ) K (greatestArgmax hK hKne hfc θ) := by
  have h := Classical.choose_spec (exists_isGreatest_argmax_param hK hKne hfc θ)
  exact h.2.1

/-- **The Path-A greatest-argmax selector is the greatest maximizer.**

Any other `IsMaxOn`-witness on `K` is bounded above by it. -/
theorem greatestArgmax_greatest
    {Θ : Type*} {K : Set ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {f : Θ → ℝ → ℝ}
    (hfc : ∀ θ, ContinuousOn (f θ) K) (θ : Θ)
    {t : ℝ} (ht_mem : t ∈ K) (ht_max : IsMaxOn (f θ) K t) :
    t ≤ greatestArgmax hK hKne hfc θ := by
  have h := Classical.choose_spec (exists_isGreatest_argmax_param hK hKne hfc θ)
  exact h.2.2 t ht_mem ht_max

end

end BalbusReffettWozny
end Foundations
end Sanctions
