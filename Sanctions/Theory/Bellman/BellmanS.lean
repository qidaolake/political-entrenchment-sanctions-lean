/-
Sanctions/Theory/Bellman/BellmanS.lean

**Abstract scalar Sender Bellman fixed point on `AbstractGame.Params`.**

Given a Target policy `α : ℝ → ℝ` (continuous) and any
`Sanctions.AbstractGame.Params`, the Sender's Bellman operator is a
`β_S`-contraction on `(↥S →ᵇ ℝ)`; the Banach fixed point `V_S α`
exists and satisfies the abstract Bellman equation. The construction
parallels the Target side (`Theory/Bellman/BellmanT.lean`).

**Rule-1 compliance.** The Sender's stage payoff `U_S` is paired with
the abstract structure's σ via `σ_isMaxOn_U_S`. For the **dynamic**
Sender's value function (constructed here), the Sender chooses `s`
optimally; the static σ (myopic argmax) coincides only at `β_S = 0`.
Headline theorems should specify whether they use the static σ or the
dynamic Sender argmax `σ_dyn`.

**Rule-3 compliance.** Uses only structural hypotheses of
`AbstractGame.Params`. No new external hypothesis introduced.

**Rule-5 compliance.** Parametric over `(p, α)`. No witness specifics.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Domain.UnitIntervalProjection
import Sanctions.Foundations.SupDiff
import Sanctions.Foundations.StokeyLucas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Sender Bellman integrand on `(x, s)` -/

/-- The Sender Bellman integrand `U_S(x, α(x), s) + β_S · V(F(x, s))`,
uncurried as a function of `(x, s) : ℝ × ℝ`. -/
noncomputable def integrandS
    (α : ℝ → ℝ) (V : ↥(Sanctions.S : Set ℝ) → ℝ) (xs : ℝ × ℝ) : ℝ :=
  let x := xs.1
  let s := xs.2
  p.U_S x (α x) s + p.β_S * V (Sanctions.clipS' (p.F x s))

theorem integrandS_continuous
    {α : ℝ → ℝ} (hα : Continuous α)
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) :
    Continuous (p.integrandS α V) := by
  unfold integrandS
  -- U_S applied to (x, α(x), s) is continuous via abstract U_S_continuous and α continuous.
  have h_triple : Continuous
      (fun xs : ℝ × ℝ => (xs.1, α xs.1, xs.2)) := by
    refine .prodMk continuous_fst (.prodMk ?_ continuous_snd)
    exact hα.comp continuous_fst
  have hU_S_app : Continuous (fun xs : ℝ × ℝ => p.U_S xs.1 (α xs.1) xs.2) :=
    p.U_S_continuous.comp h_triple
  have hF : Continuous (fun xs : ℝ × ℝ => p.F xs.1 xs.2) := p.F_continuous
  have hclip : Continuous (Sanctions.clipS' : ℝ → ↥(Sanctions.S : Set ℝ)) :=
    Sanctions.clipS'_continuous
  exact hU_S_app.add (continuous_const.mul (hV.comp (hclip.comp hF)))

/-! ## Sender Bellman operator on `(↥S →ᵇ ℝ)` -/

noncomputable def bellmanS_at
    (α : ℝ → ℝ) (V : ↥(Sanctions.S : Set ℝ) → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun s => p.integrandS α V (x, s)) '' Sanctions.I)

theorem bellmanS_at_continuous
    {α : ℝ → ℝ} (hα : Continuous α)
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) :
    Continuous (p.bellmanS_at α V) := by
  unfold bellmanS_at
  have hI : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
  exact hI.continuous_sSup (p.integrandS_continuous hα hV)

noncomputable def bellmanS_onS
    (α : ℝ → ℝ) (V : ↥(Sanctions.S : Set ℝ) → ℝ) :
    ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => p.bellmanS_at α V x.val

theorem bellmanS_onS_continuous
    {α : ℝ → ℝ} (hα : Continuous α)
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) :
    Continuous (p.bellmanS_onS α V) := by
  unfold bellmanS_onS
  exact (p.bellmanS_at_continuous hα hV).comp continuous_subtype_val

noncomputable def bellmanS_BCF
    (α : ℝ → ℝ) (hα : Continuous α)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨p.bellmanS_onS α (fun x => V x),
     p.bellmanS_onS_continuous hα V.continuous⟩

/-- The Sender Bellman operator is unchanged when its policy functions
are equal.  The continuity proofs are propositionally irrelevant. -/
theorem bellmanS_BCF_congr_α {α₁ α₂ : ℝ → ℝ}
    (h : α₁ = α₂) (hα₁ : Continuous α₁) (hα₂ : Continuous α₂)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    p.bellmanS_BCF α₁ hα₁ V = p.bellmanS_BCF α₂ hα₂ V := by
  subst α₂
  rfl

/-! ## Contraction property -/

theorem integrandS_at_continuous
    {α : ℝ → ℝ} (hα : Continuous α)
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) (x : ℝ) :
    Continuous (fun s : ℝ => p.integrandS α V (x, s)) :=
  (p.integrandS_continuous hα hV).comp
    (Continuous.prodMk continuous_const continuous_id)

theorem integrandS_pointwise_diff
    (α : ℝ → ℝ)
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) (s : ℝ) :
    |p.integrandS α (fun y => V y) (x, s)
       - p.integrandS α (fun y => W y) (x, s)|
      ≤ p.β_S * dist V W := by
  unfold integrandS
  have hβ_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have heq : p.U_S x (α x) s + p.β_S * V (Sanctions.clipS' (p.F x s))
              - (p.U_S x (α x) s
                  + p.β_S * W (Sanctions.clipS' (p.F x s)))
            = p.β_S * (V (Sanctions.clipS' (p.F x s))
                       - W (Sanctions.clipS' (p.F x s))) := by ring
  rw [heq, abs_mul, abs_of_nonneg hβ_nn]
  have h_pt :
      dist (V (Sanctions.clipS' (p.F x s)))
           (W (Sanctions.clipS' (p.F x s)))
        ≤ dist V W :=
    BoundedContinuousFunction.dist_coe_le_dist _
  rw [Real.dist_eq] at h_pt
  exact mul_le_mul_of_nonneg_left h_pt hβ_nn

theorem integrandS_image_bddAbove
    {α : ℝ → ℝ} (hα : Continuous α)
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) (x : ℝ) :
    BddAbove ((fun s => p.integrandS α V (x, s)) '' Sanctions.I) :=
  (isCompact_Icc.image (p.integrandS_at_continuous hα hV x)).bddAbove

theorem bellmanS_BCF_pointwise_dist
    {α : ℝ → ℝ} (hα : Continuous α)
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (x : ↥(Sanctions.S : Set ℝ)) :
    dist (p.bellmanS_BCF α hα V x) (p.bellmanS_BCF α hα W x)
      ≤ p.β_S * dist V W := by
  change |p.bellmanS_BCF α hα V x - p.bellmanS_BCF α hα W x| ≤ p.β_S * dist V W
  have heq_V : p.bellmanS_BCF α hα V x =
      sSup ((fun s => p.integrandS α (fun y => V y) (x.val, s)) '' Sanctions.I) := rfl
  have heq_W : p.bellmanS_BCF α hα W x =
      sSup ((fun s => p.integrandS α (fun y => W y) (x.val, s)) '' Sanctions.I) := rfl
  rw [heq_V, heq_W]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := p.β_S * dist V W)
    (Bf := sSup ((fun s => p.integrandS α (fun y => V y) (x.val, s)) '' Sanctions.I))
    (Bg := sSup ((fun s => p.integrandS α (fun y => W y) (x.val, s)) '' Sanctions.I))
  · intro s _hs
    exact p.integrandS_pointwise_diff α V W x.val s
  · intro s hs
    exact le_csSup (p.integrandS_image_bddAbove hα V.continuous x.val) ⟨s, hs, rfl⟩
  · intro s hs
    exact le_csSup (p.integrandS_image_bddAbove hα W.continuous x.val) ⟨s, hs, rfl⟩

/-! ## Fixed-point existence -/

noncomputable def β_S_nnreal : NNReal := ⟨p.β_S, p.β_S_mem.1⟩

theorem β_S_nnreal_lt_one : p.β_S_nnreal < 1 := by
  change (p.β_S_nnreal : ℝ) < (1 : ℝ)
  exact p.β_S_mem.2

/-- **The Sender Bellman operator is a `β_S`-contraction on `↥S →ᵇ ℝ`.**

The single named contraction certificate for `bellmanS_BCF` at a fixed
continuous Target policy `α`.  The modulus is the Sender's discount factor
`β_S < 1` (`β_S_nnreal_lt_one`); the Lipschitz half is the operator-level
lift of the pointwise estimate `bellmanS_BCF_pointwise_dist` through
`Foundations/SupDiff.lipschitzWith_of_pointwise_dist_le`.

Every Banach appeal on the Sender side consumes exactly this fact — `V_S`'s
own definition, `ContractingWith.fixedPoint_unique`,
`ContractingWith.tendsto_iterate_fixedPoint`, and the cone-trapping route
`StokeyLucas.fixedPoint_mem_of_mapsTo`.  Before this lemma existed the proof
was re-inlined verbatim at eight sites.  Mirrors
`ShockedParams.bellmanS_shock_contracting` in `Theory/Shocked/ShockedBellman.lean`.

General in `F` (Rule 22): `bellmanS_BCF` reaches the transition only through
`integrandS`, which calls `p.F`; no affine form is used or assumed. -/
theorem bellmanS_BCF_contracting
    {α : ℝ → ℝ} (hα : Continuous α) :
    ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) := by
  refine ⟨p.β_S_nnreal_lt_one, ?_⟩
  apply lipschitzWith_of_pointwise_dist_le
  intro V W x
  have h := p.bellmanS_BCF_pointwise_dist hα V W x
  convert h using 2

/-- **Existence and uniqueness of the abstract Sender value function**
parameterized by the Target policy `α`. -/
noncomputable def V_S (α : ℝ → ℝ) (hα : Continuous α) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  ContractingWith.fixedPoint (p.bellmanS_BCF α hα) (p.bellmanS_BCF_contracting hα)

theorem V_S_isFixedPoint
    {α : ℝ → ℝ} (hα : Continuous α) :
    p.bellmanS_BCF α hα (p.V_S α hα) = p.V_S α hα := by
  unfold V_S
  exact ContractingWith.fixedPoint_isFixedPt _

theorem V_S_bellman_eq
    {α : ℝ → ℝ} (hα : Continuous α)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.V_S α hα x =
      sSup ((fun s => p.U_S x.val (α x.val) s
              + p.β_S * p.V_S α hα
                  (Sanctions.clipS' (p.F x.val s))) ''
              Sanctions.I) := by
  have h := p.V_S_isFixedPoint hα
  have hx : p.bellmanS_BCF α hα (p.V_S α hα) x = p.V_S α hα x := by rw [h]
  rw [← hx]
  rfl

theorem V_S_range_bdd
    {α : ℝ → ℝ} (hα : Continuous α) :
    Bornology.IsBounded (Set.range (p.V_S α hα)) := by
  apply IsCompact.isBounded
  apply isCompact_range
  exact (p.V_S α hα).continuous

/-! ## V_S monotonicity in x (cone preservation, audit #10 closure) -/

/-- **bellmanS_BCF preserves monotonicity in x** under the structural
hypothesis that `U_S(·, α(·), s)` is monotone non-decreasing in `x` at
every fixed `s ∈ I`. (Audit #10 closure at the abstract layer.)

Audit-28 #3 cleanup: `h_U_S_mono` is now restricted to *feasible* states
`x, y ∈ Sanctions.S`, since the cone-iteration argument only ever evaluates
the integrand at `x.val, y.val` for `x, y : ↥S`. -/
theorem bellmanS_BCF_preserves_monotone
    {α : ℝ → ℝ} (hα : Continuous α)
    (h_U_S_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (α x) s ≤ p.U_S y (α y) s)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_V_mono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => V x)) :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => p.bellmanS_BCF α hα V x) := by
  intro x y h_xy
  change p.bellmanS_onS α (fun z => V z) x ≤ p.bellmanS_onS α (fun z => V z) y
  unfold bellmanS_onS bellmanS_at
  have hβ_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have h_int_le : ∀ s ∈ Sanctions.I, p.integrandS α (fun z => V z) (x.val, s)
                            ≤ p.integrandS α (fun z => V z) (y.val, s) := by
    intro s hs
    unfold integrandS
    have h_U : p.U_S x.val (α x.val) s ≤ p.U_S y.val (α y.val) s :=
      h_U_S_mono s hs x.val x.property y.val y.property h_xy
    have hF_le : p.F x.val s ≤ p.F y.val s := p.F_mono_x s h_xy
    have hclip_le : (Sanctions.clipS' (p.F x.val s)).val
                      ≤ (Sanctions.clipS' (p.F y.val s)).val := by
      change max 0 (min 1 (p.F x.val s)) ≤ max 0 (min 1 (p.F y.val s))
      exact max_le_max le_rfl (min_le_min le_rfl hF_le)
    have h_V_le : V (Sanctions.clipS' (p.F x.val s))
                    ≤ V (Sanctions.clipS' (p.F y.val s)) :=
      h_V_mono hclip_le
    have h_β_V_le : p.β_S * V (Sanctions.clipS' (p.F x.val s))
                     ≤ p.β_S * V (Sanctions.clipS' (p.F y.val s)) :=
      mul_le_mul_of_nonneg_left h_V_le hβ_nn
    linarith
  apply csSup_le
  · refine ⟨p.integrandS α (fun z => V z) (x.val, 0), 0, ?_, rfl⟩
    simp [Sanctions.I]
  · rintro _ ⟨s, hs, rfl⟩
    calc p.integrandS α (fun z => V z) (x.val, s)
        ≤ p.integrandS α (fun z => V z) (y.val, s) := h_int_le s hs
      _ ≤ sSup ((fun s => p.integrandS α (fun z => V z) (y.val, s)) '' Sanctions.I) :=
          le_csSup (p.integrandS_image_bddAbove hα V.continuous y.val) ⟨s, hs, rfl⟩

/-- **V_S monotone non-decreasing in x under structural integrand
monotonicity.** Abstract version of the audit-#10 closure.

Audit-28 #3 cleanup: `h_U_S_mono` is now restricted to *feasible* states
`x, y ∈ Sanctions.S`. -/
theorem V_S_monotone_of_integrand_monotone
    {α : ℝ → ℝ} (hα : Continuous α)
    (h_U_S_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (α x) s ≤ p.U_S y (α y) s) :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => p.V_S α hα x) := by
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) :=
    p.bellmanS_BCF_contracting hα
  have h_eq : p.V_S α hα = hcontr.fixedPoint := by
    unfold V_S; congr
  have h_tend :
      Filter.Tendsto
        (fun n => (p.bellmanS_BCF α hα)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
        Filter.atTop (𝓝 (p.V_S α hα)) := by
    rw [h_eq]
    exact hcontr.tendsto_iterate_fixedPoint 0
  have h_zero_mono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) x) := by
    intro x y _; simp
  have h_iter_mono : ∀ n : ℕ, Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        ((p.bellmanS_BCF α hα)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) x) := by
    intro n
    induction n with
    | zero => simpa using h_zero_mono
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact p.bellmanS_BCF_preserves_monotone hα h_U_S_mono _ ih
  have h_iter_basin : ∀ n : ℕ, Sanctions.StokeyLucas.MonotoneOnBasin Set.univ
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        ((p.bellmanS_BCF α hα)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) x) := by
    intro n x y _ _ h_le
    exact h_iter_mono n h_le
  have h_closed := @Sanctions.StokeyLucas.isClosed_monotoneOnBasin
    (Sanctions.S : Set ℝ) Set.univ
  have h_fp_basin : Sanctions.StokeyLucas.MonotoneOnBasin Set.univ
      (fun x : ↥(Sanctions.S : Set ℝ) => p.V_S α hα x) :=
    h_closed.mem_of_tendsto h_tend (Filter.Eventually.of_forall h_iter_basin)
  intro x y h_le
  exact h_fp_basin (Set.mem_univ _) (Set.mem_univ _) h_le

/-! ## V_S anti-monotonicity in x (order-dual cone preservation)

The order-dual of the two theorems above. It is the input to the stage-ceiling
argument in `Theory/LockIn/DynamicStake.lean`: a Sender continuation value that
is **non-increasing** in the Target's political state cannot buy a sanction
above the Sender's one-period (stage) ceiling. -/

/-- **`bellmanS_BCF` preserves non-increasingness in the political state.**
Order-dual of `bellmanS_BCF_preserves_monotone`.

The hypothesis `h_U_S_anti` says: at every feasible sanction `s`, the Sender's
stage payoff read **along the Target's policy**, `y ↦ U_S(y, α y, s)`, is
non-increasing in the Target's political state — a more entrenched Target never
makes the Sender better off this period, once the compliance the Target actually
plays at that state is taken into account. This is the *composed* map, not the
raw partial `∂U_S/∂x` at fixed compliance; the two differ (see
`Sanctions.raw_chord_ne_composed_chord`).

Two `Params` fields are load-bearing here:

* `F_mono_x` — "inherited hardliner power persists": at every sanction, a higher
  political state today gives a weakly higher political state tomorrow. Used in
  the *same* direction as in the monotone original: a lower state today gives a
  lower successor, and a non-increasing continuation therefore returns a
  *higher* value there.
* `β_S_mem` — the Sender's discount factor is non-negative, so multiplying the
  continuation comparison by `β_S` preserves its direction. -/
theorem bellmanS_BCF_preserves_antitone
    {α : ℝ → ℝ} (hα : Continuous α)
    (h_U_S_anti : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S y (α y) s ≤ p.U_S x (α x) s)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_V_anti : Sanctions.StokeyLucas.AntitoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => V x)) :
    Sanctions.StokeyLucas.AntitoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => p.bellmanS_BCF α hα V x) := by
  intro x y h_xy
  change p.bellmanS_onS α (fun z => V z) y ≤ p.bellmanS_onS α (fun z => V z) x
  unfold bellmanS_onS bellmanS_at
  have hβ_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have h_int_le : ∀ s ∈ Sanctions.I, p.integrandS α (fun z => V z) (y.val, s)
                            ≤ p.integrandS α (fun z => V z) (x.val, s) := by
    intro s hs
    unfold integrandS
    have h_U : p.U_S y.val (α y.val) s ≤ p.U_S x.val (α x.val) s :=
      h_U_S_anti s hs x.val x.property y.val y.property h_xy
    have hF_le : p.F x.val s ≤ p.F y.val s := p.F_mono_x s h_xy
    have hclip_le : (Sanctions.clipS' (p.F x.val s)) ≤ (Sanctions.clipS' (p.F y.val s)) :=
      Sanctions.clipS'_mono hF_le
    have h_V_le : V (Sanctions.clipS' (p.F y.val s))
                    ≤ V (Sanctions.clipS' (p.F x.val s)) := h_V_anti hclip_le
    have h_β_V_le : p.β_S * V (Sanctions.clipS' (p.F y.val s))
                     ≤ p.β_S * V (Sanctions.clipS' (p.F x.val s)) :=
      mul_le_mul_of_nonneg_left h_V_le hβ_nn
    linarith
  apply csSup_le
  · refine ⟨p.integrandS α (fun z => V z) (y.val, 0), 0, ?_, rfl⟩
    simp [Sanctions.I]
  · rintro _ ⟨s, hs, rfl⟩
    calc p.integrandS α (fun z => V z) (y.val, s)
        ≤ p.integrandS α (fun z => V z) (x.val, s) := h_int_le s hs
      _ ≤ sSup ((fun s => p.integrandS α (fun z => V z) (x.val, s)) '' Sanctions.I) :=
          le_csSup (p.integrandS_image_bddAbove hα V.continuous x.val) ⟨s, hs, rfl⟩

/-- **The constructed Sender value function is non-increasing in the political
state** whenever the Sender's composed stage payoff `y ↦ U_S(y, α y, s)` is
non-increasing at every feasible sanction. Order-dual of
`V_S_monotone_of_integrand_monotone`.

Rule 15: the conclusion is about `p.V_S α hα`, the Banach fixed point *built*
above by `ContractingWith.fixedPoint`, reached here as the sup-norm limit of the
value iterates from `0` inside the closed non-increasing carrier
(`Sanctions.StokeyLucas.isClosed_antitoneOnSubtype`). Nothing is hypothesised
about the value function itself.

Rule 3: `h_U_S_anti` is theorem-bound and written directly over the existing
`U_S` and the existing policy `α`; it is the exact order-dual of the hypothesis
shape `bellmanS_BCF_preserves_monotone` already takes. No `Params` field, no
structure field, no new `Prop` on the assumption side. -/
theorem V_S_antitone_of_integrand_antitone
    {α : ℝ → ℝ} (hα : Continuous α)
    (h_U_S_anti : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S y (α y) s ≤ p.U_S x (α x) s) :
    Sanctions.StokeyLucas.AntitoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => p.V_S α hα x) := by
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) :=
    p.bellmanS_BCF_contracting hα
  have h_eq : p.V_S α hα = hcontr.fixedPoint := by
    unfold V_S; congr
  have h_tend :
      Filter.Tendsto
        (fun n => (p.bellmanS_BCF α hα)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
        Filter.atTop (𝓝 (p.V_S α hα)) := by
    rw [h_eq]
    exact hcontr.tendsto_iterate_fixedPoint 0
  have h_iter_anti : ∀ n : ℕ, Sanctions.StokeyLucas.AntitoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        ((p.bellmanS_BCF α hα)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) x) := by
    intro n
    induction n with
    | zero => intro x y _; simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact p.bellmanS_BCF_preserves_antitone hα h_U_S_anti _ ih
  exact (@Sanctions.StokeyLucas.isClosed_antitoneOnSubtype
    (Sanctions.S : Set ℝ)).mem_of_tendsto h_tend
    (Filter.Eventually.of_forall h_iter_anti)

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
