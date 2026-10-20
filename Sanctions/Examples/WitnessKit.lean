/-
Sanctions/Examples/WitnessKit.lean

**Witness-scaffolding kit** — parametric helper lemmas factored
(2026-07-07) from the certificate-witness family
(`EECertWitness`, `LowBasinCertWitness`, `QBCertWitness`, siblings).

Every certificate witness re-proves the same scaffolding steps from
scratch: pinning the dynamic Sender response at a corner from strict
monotonicity of the dynamic objective, evaluating a corner Bellman
image by `IsGreatest.csSup_eq`, deriving the constant leader policy
from a per-state argmax plus state-local uniqueness, and the decoupled
Schur row bounds. This file states each of those steps **once, in
fully parametric form** — over an arbitrary `Sanctions.AbstractGame.Params`
and an arbitrary `ValueClass2` — so that each witness instance becomes
a one-line application (Rule 5) and the shared-helper surface is
auditable in one place (Rule 13).

**Zero new assumptions**: every lemma here is proved from the existing
machinery (`σ_dyn`/`σ_dyn_top` selector specs, `targetArgmaxOnS`
plumbing, `bellmanS_BCF_pointwise_dist`, `IsGreatest.csSup_eq`,
`MilgromShannon.isMaxOn_unique_of_strictMonoOn`); no new `Prop`
primitives, no new structure fields, no witness constants.

Contents:
* **C5** — corner pinning of `σ_dyn` / `σ_dyn_top` from strict
  monotonicity (`= 1`) or strict antitonicity (`= 0`) of the Sender
  dynamic objective.
* **C6** — the clipped vertex `max 0 (min 1 t)` maximizes a concave
  parabola `C − k(s − t)²` on `[0,1]`.
* **C7** — `SingleCrossingOn` from per-state strict monotonicity
  (or antitonicity) of the objective in the sanction.
* **C1** — decoupled Sender Schur row (`L_ST = 0`) when the derived
  leader policy is the same fixed policy for every carrier pair
  (kit-local `bellmanS_BCF_congr_α` included).
* **C4** — corner Bellman-sup evaluation wrappers: the sSup collapses
  at an exhibited argmax (Sender side and joint-Target side).
* **C8** — defiance leader-policy plumbing: `α_on ≡ a✦` from a
  per-state `IsMaxOn` at `a✦`, plus `TargetArgmaxUnique` from strict
  antitonicity of the joint Target integrand.
* **C2** — decoupled Target Schur row (`L_TS = 0`) from a
  `V_S`-independent affine-in-`V_T` image closed form.
-/

import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Foundations.MilgromShannon

namespace Sanctions

namespace Examples

namespace WitnessKit

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params

variable {p : Sanctions.AbstractGame.Params}

/-! ## C5. Corner pinning of the dynamic Sender response

If the Sender dynamic objective
`s ↦ U_S(x,a,s) + β_S · V_S(clip(F(x,s)))` is strictly increasing on
`[0,1]`, both the `Classical.choose` selector `σ_dyn` and the
upper selector `σ_dyn_top` are pinned at the corner `1`; strictly
decreasing pins them at `0`. -/

/-- **`σ_dyn` pinned at `1` from strict monotonicity** of the Sender
dynamic objective on `I` (uniqueness of the argmax via
`MilgromShannon.isMaxOn_unique_of_strictMonoOn`). -/
theorem σ_dyn_eq_one_of_strictMonoOn {V_S : Val} {x a : ℝ}
    (hmono : StrictMonoOn
      (fun s => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I) :
    p.σ_dyn V_S x a = 1 := by
  have h1_mem : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hσ_mem := p.σ_dyn_mem V_S x a
  have hσ_isMaxOn := p.σ_dyn_isMaxOn V_S x a
  have h1_isMaxOn : IsMaxOn
      (fun s => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1_mem hlt)
  exact Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
    hmono hσ_mem h1_mem hσ_isMaxOn h1_isMaxOn

/-- **`σ_dyn_top` pinned at `1` from strict monotonicity** — the upper
selector (sup of the dynamic argmax set) coincides with the unique
argmax `1`. -/
theorem σ_dyn_top_eq_one_of_strictMonoOn {V_S : Val} {x a : ℝ}
    (hmono : StrictMonoOn
      (fun s => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I) :
    p.σ_dyn_top V_S x a = 1 := by
  obtain ⟨hmem, hisMax⟩ := p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
  have h1_mem : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have h1_isMaxOn : IsMaxOn
      (fun s => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1_mem hlt)
  exact Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
    hmono hmem h1_mem hisMax h1_isMaxOn

/-- **`σ_dyn` pinned at `0` from strict antitonicity** of the Sender
dynamic objective (the dovish / low-basin corner). -/
theorem σ_dyn_eq_zero_of_strictAntiOn {V_S : Val} {x a : ℝ}
    (hanti : StrictAntiOn
      (fun s => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I) :
    p.σ_dyn V_S x a = 0 := by
  have h0_mem : (0 : ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩
  have hσ_mem := p.σ_dyn_mem V_S x a
  have hσ_isMaxOn := p.σ_dyn_isMaxOn V_S x a
  by_contra hne
  have hσpos : 0 < p.σ_dyn V_S x a :=
    lt_of_le_of_ne hσ_mem.1 (Ne.symm hne)
  have hlt := hanti h0_mem hσ_mem hσpos
  exact absurd (hσ_isMaxOn h0_mem) (not_le.mpr hlt)

/-- **`σ_dyn_top` pinned at `0` from strict antitonicity**. -/
theorem σ_dyn_top_eq_zero_of_strictAntiOn {V_S : Val} {x a : ℝ}
    (hanti : StrictAntiOn
      (fun s => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I) :
    p.σ_dyn_top V_S x a = 0 := by
  have h0_mem : (0 : ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩
  obtain ⟨hσ_mem, hσ_isMaxOn⟩ := p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
  by_contra hne
  have hσpos : 0 < p.σ_dyn_top V_S x a :=
    lt_of_le_of_ne hσ_mem.1 (Ne.symm hne)
  have hlt := hanti h0_mem hσ_mem hσpos
  exact absurd (hσ_isMaxOn h0_mem) (not_le.mpr hlt)

/-! ## C6. Clipped-vertex maximizer of a concave parabola -/

/-- **The clipped vertex maximizes a concave parabola on `[0,1]`.**
For `U(s) = C − k(s − t)²` with `k > 0`, the point `max 0 (min 1 t)`
(the vertex `t` clipped into `[0,1]`) is a maximizer of `U` on
`[0,1]`. Three-way split on the vertex location. -/
theorem clipVertex_isMaxOn {k C t : ℝ} (hk : 0 < k) {U : ℝ → ℝ}
    (hU : ∀ s, U s = C - k * (s - t) ^ 2) :
    IsMaxOn U (Set.Icc (0 : ℝ) 1) (max 0 (min 1 t)) := by
  rw [isMaxOn_iff]
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  rw [hU s, hU (max 0 (min 1 t))]
  rcases le_total t 0 with ht | ht
  · -- vertex left of 0 ⇒ clip = 0
    rw [min_eq_right (le_trans ht (by norm_num : (0 : ℝ) ≤ 1)), max_eq_left ht]
    nlinarith [mul_nonneg hk.le (sq_nonneg s),
      mul_nonneg hk.le (mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ -t))]
  · rcases le_total t 1 with ht1 | ht1
    · -- vertex inside [0,1] ⇒ clip = t
      rw [min_eq_right ht1, max_eq_right ht]
      nlinarith [mul_nonneg hk.le (sq_nonneg (s - t))]
    · -- vertex right of 1 ⇒ clip = 1
      rw [min_eq_left ht1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      nlinarith [mul_nonneg hk.le
          (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)
            (by linarith : (0 : ℝ) ≤ t - 1)),
        mul_nonneg hk.le
          (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)
            (by linarith : (0 : ℝ) ≤ t - s))]

/-! ## C7. Single crossing from per-state strict monotonicity

When the objective is strictly monotone in the sanction at *every*
basin state, both single-crossing consequents hold unconditionally;
strict antitonicity refutes the antecedents, so single crossing holds
vacuously. Stated for arbitrary sets `S` (sanction domain) and `T`
(state basin). -/

/-- **`SingleCrossingOn` from per-state strict monotonicity**: if
`s ↦ f s t` is strictly increasing on `S` for every `t ∈ T`, then `f`
satisfies `SingleCrossingOn S T`. -/
theorem singleCrossingOn_of_strictMonoOn {S T : Set ℝ} {f : ℝ → ℝ → ℝ}
    (hmono : ∀ t ∈ T, StrictMonoOn (fun s => f s t) S) :
    Sanctions.MilgromShannon.SingleCrossingOn S T f := by
  intro s s' t t' hs hs' hss _ht ht' _htt
  constructor
  · intro _
    rcases eq_or_lt_of_le hss with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (hmono t' ht' hs hs' hlt)
  · intro hstrict
    rcases eq_or_lt_of_le hss with rfl | hlt
    · exact absurd hstrict (lt_irrefl _)
    · exact hmono t' ht' hs hs' hlt

/-- **`SingleCrossingOn` from per-state strict antitonicity**: if
`s ↦ f s t` is strictly decreasing on `S` for every `t ∈ T`, both
single-crossing antecedents are refuted (for `s < s'`), so the
crossing condition holds vacuously. -/
theorem singleCrossingOn_of_strictAntiOn {S T : Set ℝ} {f : ℝ → ℝ → ℝ}
    (hanti : ∀ t ∈ T, StrictAntiOn (fun s => f s t) S) :
    Sanctions.MilgromShannon.SingleCrossingOn S T f := by
  intro s s' t t' hs hs' hss ht _ht' _htt
  rcases eq_or_lt_of_le hss with rfl | hlt
  · exact ⟨fun _ => le_refl _, fun h => absurd h (lt_irrefl _)⟩
  · have hdec := hanti t ht hs hs' hlt
    exact ⟨fun h => absurd h (not_le.mpr hdec),
      fun h => absurd h (not_lt.mpr hdec.le)⟩

/-! ## C1. Decoupled Sender Schur row

When the derived leader policy `α_on` is the *same fixed policy* for
every carrier pair, the joint Sender operator is `V_T`-independent, so
its Schur row has cross coefficient `L_ST = 0` and self coefficient
`β_S` (from `bellmanS_BCF_pointwise_dist`). -/

/-- Policy-congruence lemma for `bellmanS_BCF` (the continuity
proofs are propositionally irrelevant). Canonical shared copy — the
original `EECertWitness` duplicate was removed 2026-07-08; every
witness uses this one. -/
theorem bellmanS_BCF_congr_α {α₁ α₂ : ℝ → ℝ}
    (h : α₁ = α₂) (hα₁ : Continuous α₁) (hα₂ : Continuous α₂) (V : Val) :
    p.bellmanS_BCF α₁ hα₁ V = p.bellmanS_BCF α₂ hα₂ V :=
  p.bellmanS_BCF_congr_α h hα₁ hα₂ V

/-- **Decoupled Sender Schur row at a fixed leader policy.** If the
derived leader policy `D.α_on V W` equals a fixed continuous policy
`α₀` for every carrier pair, the joint Sender operator is
`V_T`-independent and its row bound is `0 · dist V V' + β_S · dist W W'`. -/
theorem jointSenderOp_sub_dist_le_of_const_policy {D : p.ValueClass2}
    (h_inv : D.IsInvariant) {α₀ : ℝ → ℝ} (hα₀ : Continuous α₀)
    (hα : ∀ (V : D.CarrierT) (W : D.CarrierS), D.α_on V W = α₀)
    (V V' : D.CarrierT) (W W' : D.CarrierS) :
    dist (D.jointSenderOp_sub h_inv (V, W))
        (D.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + p.β_S * dist W W' := by
  rw [Subtype.dist_eq]
  change dist (p.bellmanS_BCF (D.α_on V W) (D.α_on_continuous V W) W.val)
        (p.bellmanS_BCF (D.α_on V' W') (D.α_on_continuous V' W') W'.val)
      ≤ 0 * dist V V' + p.β_S * dist W W'
  rw [bellmanS_BCF_congr_α (hα V W) (D.α_on_continuous V W) hα₀ W.val,
      bellmanS_BCF_congr_α (hα V' W') (D.α_on_continuous V' W') hα₀ W'.val,
      zero_mul, zero_add]
  rw [BoundedContinuousFunction.dist_le (mul_nonneg p.β_S_mem.1 dist_nonneg)]
  intro y
  have hp := p.bellmanS_BCF_pointwise_dist hα₀ W.val W'.val y
  rw [Subtype.dist_eq]
  exact hp

/-- **Decoupled Sender Schur row at the defiance policy `α ≡ 0`**
(the form the hardline witnesses use): one-line specialization of
`jointSenderOp_sub_dist_le_of_const_policy`. -/
theorem jointSenderOp_sub_dist_le_of_defiance {D : p.ValueClass2}
    (h_inv : D.IsInvariant)
    (hα0 : ∀ (V : D.CarrierT) (W : D.CarrierS),
      D.α_on V W = fun _ => (0 : ℝ))
    (V V' : D.CarrierT) (W W' : D.CarrierS) :
    dist (D.jointSenderOp_sub h_inv (V, W))
        (D.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + p.β_S * dist W W' :=
  jointSenderOp_sub_dist_le_of_const_policy h_inv continuous_const hα0 V V' W W'

/-! ## C4. Corner Bellman-sup evaluation wrappers

Both joint Bellman operators are defined as an `sSup` over the action
interval; when an argmax is exhibited, the `sSup` collapses to the
integrand value there (`IsGreatest.csSup_eq`). -/

/-- **Sender Bellman image at an exhibited argmax.** If `s✦ ∈ I`
maximizes the Sender integrand at state `y`, then
`bellmanS_BCF α hα W y` equals the integrand value at `s✦`. -/
theorem bellmanS_image_of_isMaxOn {α : ℝ → ℝ} (hα : Continuous α)
    (W : Val) (y : ↥(Sanctions.S : Set ℝ)) {sStar : ℝ}
    (hs : sStar ∈ Sanctions.I)
    (hmax : IsMaxOn
      (fun s => p.U_S y.val (α y.val) s
        + p.β_S * W (Sanctions.clipS' (p.F y.val s)))
      Sanctions.I sStar) :
    p.bellmanS_BCF α hα W y
      = p.U_S y.val (α y.val) sStar
        + p.β_S * W (Sanctions.clipS' (p.F y.val sStar)) := by
  have he : p.bellmanS_BCF α hα W y
      = sSup ((fun s => p.integrandS α (fun z => W z) (y.val, s))
          '' Sanctions.I) := rfl
  rw [he]
  have hgt : IsGreatest
      ((fun s => p.integrandS α (fun z => W z) (y.val, s)) '' Sanctions.I)
      (p.integrandS α (fun z => W z) (y.val, sStar)) := by
    constructor
    · exact ⟨sStar, hs, rfl⟩
    · rintro z ⟨s, hsI, rfl⟩
      change p.U_S y.val (α y.val) s
          + p.β_S * W (Sanctions.clipS' (p.F y.val s))
        ≤ p.U_S y.val (α y.val) sStar
          + p.β_S * W (Sanctions.clipS' (p.F y.val sStar))
      exact hmax hsI
  rw [hgt.csSup_eq]
  rfl

/-- **Joint Target Bellman image at an exhibited argmax.** If `a✦ ∈ I`
maximizes the joint Target integrand at state `y`, then
`jointTarget_BCF_on_S V_T V_S h_unique y` equals the integrand value
at `a✦`. General in `F`.

**Weakened hypothesis (plan item BJ4.3, 2026-10-08).** `h_unique` is the
compliance-local `DynamicArgmaxUniqueOnI V_S` (Sender argmax uniqueness only at
physical compliance `a ∈ [0,1]`), the form `jointTarget_BCF_on_S` now takes;
it used to be the all-real-`a` `DynamicArgmaxUnique V_S`. A caller holding
`h : DynamicArgmaxUnique V_S` passes `h.toOnI`. -/
theorem jointTarget_image_of_isMaxOn (V_T V_S : Val)
    (h_unique : p.DynamicArgmaxUniqueOnI V_S)
    (y : ↥(Sanctions.S : Set ℝ)) {aStar : ℝ} (ha : aStar ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a => p.joint_T_integrand V_T V_S y.val a)
      Sanctions.I aStar) :
    p.jointTarget_BCF_on_S V_T V_S h_unique y
      = p.joint_T_integrand V_T V_S y.val aStar := by
  rw [p.jointTarget_BCF_on_S_apply]
  have hgt : IsGreatest
      ((fun a => p.joint_T_integrand V_T V_S y.val a) '' Sanctions.I)
      (p.joint_T_integrand V_T V_S y.val aStar) := by
    constructor
    · exact ⟨aStar, ha, rfl⟩
    · rintro z ⟨a, haI, rfl⟩
      exact hmax haI
  exact hgt.csSup_eq

/-! ## C8. Constant leader-policy plumbing

The derived leader policy `α_on` (the state-clamped `Classical.choose`
selector `targetArgmaxOnS`) is pinned at a constant `a✦` whenever `a✦`
is a per-state argmax of the joint Target integrand — by state-local
Target argmax uniqueness (`D.target_unique_on`). -/

/-- **Derived leader policy pinned at a constant argmax.** If `a✦ ∈ I`
maximizes the joint Target integrand at every physical state, the
derived leader policy is the constant `a✦` (Rule 1: this *derives* the
policy as the argmax; nothing is assumed about it). -/
theorem α_on_eq_const_of_isMaxOn {D : p.ValueClass2}
    (V : D.CarrierT) (W : D.CarrierS) {aStar : ℝ} (ha : aStar ∈ Sanctions.I)
    (hmax : ∀ y : ↥(Sanctions.S : Set ℝ),
      IsMaxOn (fun a => p.joint_T_integrand V.val W.val y.val a)
        Sanctions.I aStar) :
    D.α_on V W = fun _ => aStar := by
  funext x
  have hmem := p.targetArgmaxOnS_mem V.val W.val
    (D.sender_unique_on W.val W.property) (Sanctions.clipS' x)
  have hmax' := p.targetArgmaxOnS_isMaxOn V.val W.val
    (D.sender_unique_on W.val W.property) (Sanctions.clipS' x)
  exact D.target_unique_on V.val V.property W.val W.property
    (Sanctions.clipS' x).val (Sanctions.clipS' x).property _ aStar hmem ha
    hmax' (hmax (Sanctions.clipS' x))

/-- **Defiance corner**: `α_on ≡ 0` when full defiance is a per-state
argmax of the joint Target integrand. -/
theorem α_on_eq_zero_of_zero_isMaxOn {D : p.ValueClass2}
    (V : D.CarrierT) (W : D.CarrierS)
    (hmax : ∀ y : ↥(Sanctions.S : Set ℝ),
      IsMaxOn (fun a => p.joint_T_integrand V.val W.val y.val a)
        Sanctions.I 0) :
    D.α_on V W = fun _ => (0 : ℝ) :=
  α_on_eq_const_of_isMaxOn V W ⟨le_refl 0, by norm_num⟩ hmax

/-- **`TargetArgmaxUnique` from strict antitonicity of the joint
Target integrand**: two mutually-dominating maximizers of a strictly
decreasing function must coincide. -/
theorem targetArgmaxUnique_of_strictAntiOn {V_T V_S : Val}
    (hanti : ∀ x ∈ Sanctions.S,
      StrictAntiOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I) :
    p.TargetArgmaxUnique V_T V_S := by
  intro x hx a₁ a₂ h1 h2 hm1 hm2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd (hm2 h1) (not_le.mpr (hanti x hx h1 h2 hlt))
  · exact absurd (hm1 h2) (not_le.mpr (hanti x hx h2 h1 hgt))

/-! ## C2. Decoupled Target Schur row

When the joint Target image has a `V_S`-independent closed form that
is affine in `V_T` with coefficient `β_T` (the corner-collapsed shape
`g(y) + β_T · V_T(clip(φ(y)))`), the Target Schur row has cross
coefficient `L_TS = 0` and self coefficient `β_T`. -/

/-- **Decoupled Target Schur row from an image closed form.** The
hypothesis `himg` says the joint Target Bellman image evaluates, at
every carrier pair and every state, to `g(y) + β_T · V_T(clip(φ(y)))`
— in particular it is `V_S`-independent. The row bound
`β_T · dist V V' + 0 · dist W W'` follows pointwise. -/
theorem jointTargetOp_sub_dist_le_of_image {D : p.ValueClass2}
    (h_inv : D.IsInvariant) {g φ : ℝ → ℝ}
    (himg : ∀ (V : D.CarrierT) (W : D.CarrierS)
      (y : ↥(Sanctions.S : Set ℝ)),
      p.jointTarget_BCF_on_S V.val W.val
          (D.sender_unique_on W.val W.property) y
        = g y.val + p.β_T * V.val (Sanctions.clipS' (φ y.val)))
    (V V' : D.CarrierT) (W W' : D.CarrierS) :
    dist (D.jointTargetOp_sub h_inv (V, W))
        (D.jointTargetOp_sub h_inv (V', W'))
      ≤ p.β_T * dist V V' + 0 * dist W W' := by
  have hβ : (0 : ℝ) ≤ p.β_T := p.β_T_mem.1
  rw [Subtype.dist_eq]
  change dist (p.jointTarget_BCF_on_S V.val W.val
          (D.sender_unique_on W.val W.property))
        (p.jointTarget_BCF_on_S V'.val W'.val
          (D.sender_unique_on W'.val W'.property))
      ≤ p.β_T * dist V V' + 0 * dist W W'
  have hnn : (0 : ℝ) ≤ p.β_T * dist V V' + 0 * dist W W' := by
    have h1 : (0 : ℝ) ≤ p.β_T * dist V V' := mul_nonneg hβ dist_nonneg
    linarith
  rw [BoundedContinuousFunction.dist_le hnn]
  intro y
  rw [Real.dist_eq, himg V W y, himg V' W' y]
  have hb : |V.val (Sanctions.clipS' (φ y.val))
      - V'.val (Sanctions.clipS' (φ y.val))| ≤ dist V V' := by
    rw [Subtype.dist_eq, ← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist _
  have hkey : (g y.val + p.β_T * V.val (Sanctions.clipS' (φ y.val)))
      - (g y.val + p.β_T * V'.val (Sanctions.clipS' (φ y.val)))
      = p.β_T * (V.val (Sanctions.clipS' (φ y.val))
        - V'.val (Sanctions.clipS' (φ y.val))) := by ring
  rw [hkey, abs_mul, abs_of_nonneg hβ]
  have hle := mul_le_mul_of_nonneg_left hb hβ
  linarith

end WitnessKit

end Examples

end Sanctions
