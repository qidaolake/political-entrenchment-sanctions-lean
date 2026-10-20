/-
Sanctions/Theory/Bellman/ValueLipschitz.lean

**Lipschitz discharge for the Target Bellman fixed point `V_T` from
primitive stage and transition Lipschitz constants.**

`Theory/Basin/PrimitiveHighBasin.lean` takes
`ValueLipschitzWith V K` as a primitive hypothesis on a generic value
function. This file discharges that primitive for the canonical
Banach fixed point `V_T` of `bellmanBCF` (the static-Sender Target
Bellman operator from `Theory/Bellman/BellmanT.lean`).

## Argument

Three ingredients on the abstract Bellman:

1. **Cone preservation.** If `V` is `K`-Lipschitz and the integrand
   pieces are Lipschitz with constants `L_U` (stage payoff
   `U_T(x, a, σ(x, a))` in `x` at fixed `a`) and `γ`
   (transition `F(x, a) = (1 - δ) x + δ σ(x, a)` in `x` at fixed `a`),
   then `bellmanBCF V` is `(L_U + β_T · K · γ)`-Lipschitz. The proof
   uses the sup-difference inequality
   (`abs_sSup_image_sub_sSup_image_le_of_bdd`) and the 1-Lipschitz
   property of `clipS'` (`clipS'_lipschitz_dist`).
2. **Closure of the Lipschitz cone under uniform convergence.** If
   each `V_n` is `K`-Lipschitz and `V_n → V` in sup norm, then `V` is
   `K`-Lipschitz. Standard 3-ε argument bounded via
   `BoundedContinuousFunction.dist_coe_le_dist`.
3. **Banach iteration limit.** `V_T = lim n→∞ bellmanBCF^[n] 0`
   (`ContractingWith.tendsto_iterate_fixedPoint`). Each iterate is
   `K`-Lipschitz by induction starting from the 0-Lipschitz zero
   function; the limit is `K`-Lipschitz by closure.

The natural margin condition is `L_U + β_T · K · γ ≤ K`, which
admits any `K ≥ L_U / (1 - β_T γ)` provided the contraction margin
`β_T γ < 1` holds.

## Rule compliance

**Rule 3.** No new `Params` fields. The Lipschitz constants `L_U`,
`γ`, `K` are local theorem-parameter primitives; `h_U_lip` and
`h_F_lip` are economically interpretable stage/transition regularity
hypotheses. (When `σ` is `L_σ`-Lipschitz in `x`, `γ = 1 - δ + δ L_σ`
gives the transition Lipschitz constant; for `L_σ ≤ 1` we get
`γ ≤ 1`.)

**Rule 5.** Fully parametric. The conclusion
`ValueLipschitzWith p.V_T K` is independent of any witness.

**Rule 22.** General in `F`: the transition enters only through the state
modulus `γ` in `h_F_lip`; no functional form is assumed.

**Round BJ1.2 (2026-10-07).** The chain no longer carries the sign binders
`0 ≤ γ` / `0 ≤ γ_F` (never read: the proofs scale the transition bound by `K`,
not by `γ`) or `0 ≤ L_U` (derived from the stage-payoff bound at the states
`0` and `1`). The Target chain gains the `_on` forms the Sender chain already
had (doc 68, L6): the stage-payoff and transition moduli are assumed on
feasible states only, which is all the Bellman operator reads; the global
forms are their specialisations.

**Round BJ5.1 (2026-10-07).** The Target chain (§2–§3: `bellmanBCF_*` and
`V_T_valueLipschitzWith_*`) is about the static-Sender operator `bellmanBCF`
and its fixed point `V_T`, which are built from the joint continuity of the
static selector `σ`; those theorems take `[p.StaticSelectorContinuous]`
(formerly the `Params` field `σ_continuous`). The Sender chain (`bellmanS_BCF_*`,
`V_S_*`) never reads it and is unchanged. General in `F`.
-/

import Sanctions.Theory.Bellman.BellmanT
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Domain.UnitIntervalProjection

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Cone closure under uniform convergence -/

/-- **Closure of the Lipschitz cone under sup-norm convergence.**
If each `V_n` is `K`-Lipschitz (in the `ValueLipschitzWith` sense) and
`V_n → V` in the BCF metric, then `V` is `K`-Lipschitz. Standard
3-ε argument using `BoundedContinuousFunction.dist_coe_le_dist`. -/
theorem valueLipschitzWith_of_tendsto
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {V_seq : ℕ → ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {K : ℝ}
    (_hK_nn : 0 ≤ K)
    (h_each : ∀ n, ValueLipschitzWith (V_seq n) K)
    (h_tendsto : Tendsto V_seq atTop (𝓝 V)) :
    ValueLipschitzWith V K := by
  intro y₁ y₂
  -- |V y₂ - V y₁| ≤ |V y₂ - V_seq n y₂| + |V_seq n y₂ - V_seq n y₁|
  --   + |V_seq n y₁ - V y₁| ≤ 2 ‖V_seq n - V‖ + K * dist y₁ y₂
  -- Take n → ∞.
  have h_bound : ∀ n,
      |V y₂ - V y₁|
        ≤ 2 * dist (V_seq n) V + K * dist y₁ y₂ := by
    intro n
    have h_pt₁ : |V_seq n y₁ - V y₁| ≤ dist (V_seq n) V := by
      have := BoundedContinuousFunction.dist_coe_le_dist (f := V_seq n) (g := V) y₁
      rwa [Real.dist_eq] at this
    have h_pt₂ : |V_seq n y₂ - V y₂| ≤ dist (V_seq n) V := by
      have := BoundedContinuousFunction.dist_coe_le_dist (f := V_seq n) (g := V) y₂
      rwa [Real.dist_eq] at this
    have h_mid : |V_seq n y₂ - V_seq n y₁| ≤ K * dist y₁ y₂ := h_each n y₁ y₂
    have h_tri :
        |V y₂ - V y₁|
          ≤ |V y₂ - V_seq n y₂| + |V_seq n y₂ - V_seq n y₁|
            + |V_seq n y₁ - V y₁| := by
      have : V y₂ - V y₁
              = (V y₂ - V_seq n y₂) + (V_seq n y₂ - V_seq n y₁)
                + (V_seq n y₁ - V y₁) := by ring
      calc |V y₂ - V y₁|
          = |(V y₂ - V_seq n y₂) + (V_seq n y₂ - V_seq n y₁)
              + (V_seq n y₁ - V y₁)| := by rw [this]
        _ ≤ |(V y₂ - V_seq n y₂) + (V_seq n y₂ - V_seq n y₁)|
              + |V_seq n y₁ - V y₁| := abs_add_le _ _
        _ ≤ |V y₂ - V_seq n y₂| + |V_seq n y₂ - V_seq n y₁|
              + |V_seq n y₁ - V y₁| := by
              gcongr
              exact abs_add_le _ _
    have h_swap₂ : |V y₂ - V_seq n y₂| = |V_seq n y₂ - V y₂| := abs_sub_comm _ _
    have h_swap₁ : |V y₂ - V_seq n y₂| ≤ dist (V_seq n) V := by
      rw [h_swap₂]; exact h_pt₂
    linarith [h_swap₁, h_pt₁, h_mid, h_tri]
  -- Take n → ∞: 2 dist (V_seq n) V → 0, so RHS → K * dist y₁ y₂.
  have h_lim_rhs :
      Tendsto (fun n => 2 * dist (V_seq n) V + K * dist y₁ y₂)
        atTop (𝓝 (K * dist y₁ y₂)) := by
    have h_dist_tendsto : Tendsto (fun n => dist (V_seq n) V) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = dist V V from (dist_self V).symm]
      exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp h_tendsto
    have h_mul : Tendsto (fun n => 2 * dist (V_seq n) V) atTop (𝓝 (2 * 0)) :=
      h_dist_tendsto.const_mul 2
    simpa using h_mul.add tendsto_const_nhds
  -- Use the two-tendsto comparison: constant LHS ≤ RHS pointwise → LHS ≤ limit.
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim_rhs h_bound

/-! ## 2. One-step Bellman cone preservation

If `V : Val` is `K`-Lipschitz and primitive Lipschitz constants
hold for the stage payoff (`L_U`) and the transition (`γ`), then
`bellmanBCF V` is `(L_U + β_T · K · γ)`-Lipschitz. Under the margin
hypothesis `L_U + β_T · K · γ ≤ K`, the cone `lipCone K` is
preserved. -/

/-- **Target Bellman pointwise Lipschitz bound in `x`, physical-state
hypotheses** (round BJ1.2, 2026-10-07; the Target analogue of doc 68, L6). The
stage-payoff and transition moduli are assumed on feasible inherited states
only; the two states compared are feasible, so nothing more is used. The
transition modulus `γ` needs no sign: it is never multiplied into an
inequality, only `K ≥ 0` is. General in `F`. -/
theorem bellmanBCF_pointwise_lipschitz_in_state_on [p.StaticSelectorContinuous]
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    |p.bellmanBCF V y₂ - p.bellmanBCF V y₁|
      ≤ (L_U + p.β_T * K * γ) * dist y₁ y₂ := by
  -- |sSup g₂(·) - sSup g₁(·)| ≤ sup_a |g₂(a) - g₁(a)|
  have heq₁ : p.bellmanBCF V y₁ =
      sSup ((fun a => p.integrand (fun y => V y) (y₁.val, a)) '' Sanctions.I) := rfl
  have heq₂ : p.bellmanBCF V y₂ =
      sSup ((fun a => p.integrand (fun y => V y) (y₂.val, a)) '' Sanctions.I) := rfl
  -- Pointwise integrand difference bound.
  have h_int_diff : ∀ a ∈ Sanctions.I,
      |p.integrand (fun y => V y) (y₂.val, a)
        - p.integrand (fun y => V y) (y₁.val, a)|
        ≤ (L_U + p.β_T * K * γ) * dist y₁ y₂ := by
    intro a ha
    unfold integrand
    -- Decompose: integrand(y₂,a) - integrand(y₁,a)
    --   = (U_T_at(y₂,a) - U_T_at(y₁,a))
    --     + β_T * (V(clipS' F(y₂,a)) - V(clipS' F(y₁,a)))
    have hdecomp :
        (p.U_T_at (y₂.val, a) + p.β_T * V (Sanctions.clipS' (p.F_pair (y₂.val, a))))
          - (p.U_T_at (y₁.val, a) + p.β_T * V (Sanctions.clipS' (p.F_pair (y₁.val, a))))
        = (p.U_T_at (y₂.val, a) - p.U_T_at (y₁.val, a))
          + p.β_T * (V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
                     - V (Sanctions.clipS' (p.F_pair (y₁.val, a)))) := by ring
    rw [hdecomp]
    have h_tri := abs_add_le (p.U_T_at (y₂.val, a) - p.U_T_at (y₁.val, a))
      (p.β_T * (V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
                - V (Sanctions.clipS' (p.F_pair (y₁.val, a)))))
    have h_U_step : |p.U_T_at (y₂.val, a) - p.U_T_at (y₁.val, a)|
                      ≤ L_U * |y₂.val - y₁.val| := h_U_lip _ y₁.property _ y₂.property a ha
    -- Continuation step: |β_T * (V_after - V_before)|
    --   = β_T * |V(clipS' F(y₂,a)) - V(clipS' F(y₁,a))|
    --   ≤ β_T * K * dist (clipS' F(y₂,a)) (clipS' F(y₁,a))
    --   ≤ β_T * K * γ * |y₂.val - y₁.val|
    have h_V_step :
        |V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
         - V (Sanctions.clipS' (p.F_pair (y₁.val, a)))|
          ≤ K * (γ * |y₂.val - y₁.val|) := by
      -- ValueLipschitzWith V K at the two clipped points.
      have h_V := h_V_lip (Sanctions.clipS' (p.F_pair (y₁.val, a)))
                          (Sanctions.clipS' (p.F_pair (y₂.val, a)))
      -- h_V : |V (clipS' …₂) - V (clipS' …₁)| ≤ K * dist (clipS' …₁) (clipS' …₂)
      have h_clip_lip :
          dist (Sanctions.clipS' (p.F_pair (y₁.val, a)))
                (Sanctions.clipS' (p.F_pair (y₂.val, a)))
            ≤ dist (p.F_pair (y₁.val, a)) (p.F_pair (y₂.val, a)) :=
        Sanctions.clipS'_lipschitz_dist _ _
      have h_F_step :
          dist (p.F_pair (y₁.val, a)) (p.F_pair (y₂.val, a))
            ≤ γ * |y₂.val - y₁.val| := by
        rw [Real.dist_eq]
        have h_lip := h_F_lip y₁.val y₁.property y₂.val y₂.property a ha
        have h_swap : |p.F_pair (y₁.val, a) - p.F_pair (y₂.val, a)|
                        = |p.F_pair (y₂.val, a) - p.F_pair (y₁.val, a)| :=
          abs_sub_comm _ _
        rw [h_swap]; exact h_lip
      have h_combined :
          dist (Sanctions.clipS' (p.F_pair (y₁.val, a)))
                (Sanctions.clipS' (p.F_pair (y₂.val, a)))
            ≤ γ * |y₂.val - y₁.val| := le_trans h_clip_lip h_F_step
      have h_K_combined :
          K * dist (Sanctions.clipS' (p.F_pair (y₁.val, a)))
                    (Sanctions.clipS' (p.F_pair (y₂.val, a)))
            ≤ K * (γ * |y₂.val - y₁.val|) :=
        mul_le_mul_of_nonneg_left h_combined hK_nn
      exact le_trans h_V h_K_combined
    have h_β_V_step :
        |p.β_T * (V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
                   - V (Sanctions.clipS' (p.F_pair (y₁.val, a))))|
          ≤ p.β_T * K * γ * |y₂.val - y₁.val| := by
      rw [abs_mul, abs_of_nonneg p.β_T_mem.1]
      have h_pos : 0 ≤ p.β_T := p.β_T_mem.1
      calc p.β_T * |V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
                    - V (Sanctions.clipS' (p.F_pair (y₁.val, a)))|
          ≤ p.β_T * (K * (γ * |y₂.val - y₁.val|)) :=
            mul_le_mul_of_nonneg_left h_V_step h_pos
        _ = p.β_T * K * γ * |y₂.val - y₁.val| := by ring
    have h_dist_eq : dist y₁ y₂ = |y₂.val - y₁.val| := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [h_dist_eq]
    calc
      |(p.U_T_at (y₂.val, a) - p.U_T_at (y₁.val, a))
        + p.β_T * (V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
                   - V (Sanctions.clipS' (p.F_pair (y₁.val, a))))|
        ≤ |p.U_T_at (y₂.val, a) - p.U_T_at (y₁.val, a)|
          + |p.β_T * (V (Sanctions.clipS' (p.F_pair (y₂.val, a)))
                       - V (Sanctions.clipS' (p.F_pair (y₁.val, a))))| := h_tri
      _ ≤ L_U * |y₂.val - y₁.val| + p.β_T * K * γ * |y₂.val - y₁.val| := by
            exact add_le_add h_U_step h_β_V_step
      _ = (L_U + p.β_T * K * γ) * |y₂.val - y₁.val| := by ring
  -- Apply sup-difference inequality.
  rw [heq₁, heq₂]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := (L_U + p.β_T * K * γ) * dist y₁ y₂)
    (Bf := sSup ((fun a => p.integrand (fun y => V y) (y₂.val, a)) '' Sanctions.I))
    (Bg := sSup ((fun a => p.integrand (fun y => V y) (y₁.val, a)) '' Sanctions.I))
  · intro a ha; exact h_int_diff a ha
  · intro a ha
    exact le_csSup (p.integrand_image_bddAbove V.continuous y₂.val) ⟨a, ha, rfl⟩
  · intro a ha
    exact le_csSup (p.integrand_image_bddAbove V.continuous y₁.val) ⟨a, ha, rfl⟩

/-- **Target Bellman pointwise Lipschitz bound in `x`.** The global-hypothesis
specialisation of `bellmanBCF_pointwise_lipschitz_in_state_on`. Round BJ1.2
(2026-10-07): the unread binder `0 ≤ γ` is deleted. General in `F`. -/
theorem bellmanBCF_pointwise_lipschitz_in_state [p.StaticSelectorContinuous]
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    |p.bellmanBCF V y₂ - p.bellmanBCF V y₁|
      ≤ (L_U + p.β_T * K * γ) * dist y₁ y₂ :=
  p.bellmanBCF_pointwise_lipschitz_in_state_on V hK_nn h_V_lip
    (fun x₁ _ x₂ _ a ha => h_U_lip x₁ x₂ a ha) (fun x₁ _ x₂ _ a ha => h_F_lip x₁ x₂ a ha) y₁ y₂

/-- **One-step Lipschitz-cone preservation under `bellmanBCF`, physical-state
hypotheses** (round BJ1.2, 2026-10-07; the Target analogue of doc 68, L6). If
`V` is `K`-Lipschitz, the stage payoff and the transition are Lipschitz in the
state on feasible states, and the margin `L_U + β_T · K · γ ≤ K` holds, then
`bellmanBCF V` is also `K`-Lipschitz. Only the two feasible states compared are
read, so nothing is assumed off `[0, 1]`; no sign of `γ` is needed. General in
`F`. -/
theorem bellmanBCF_preserves_lipschitz_cone_on [p.StaticSelectorContinuous]
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_T * K * γ ≤ K) :
    ValueLipschitzWith (p.bellmanBCF V) K := by
  intro y₁ y₂
  have h_step :=
    p.bellmanBCF_pointwise_lipschitz_in_state_on V hK_nn h_V_lip h_U_lip h_F_lip y₁ y₂
  have h_dist_nn : 0 ≤ dist y₁ y₂ := dist_nonneg
  calc |p.bellmanBCF V y₂ - p.bellmanBCF V y₁|
      ≤ (L_U + p.β_T * K * γ) * dist y₁ y₂ := h_step
    _ ≤ K * dist y₁ y₂ := mul_le_mul_of_nonneg_right h_margin h_dist_nn

/-- **One-step Lipschitz-cone preservation under `bellmanBCF`.** If
`V` is `K`-Lipschitz and the margin condition
`L_U + β_T · K · γ ≤ K` holds, then `bellmanBCF V` is also
`K`-Lipschitz. The global-hypothesis specialisation of
`bellmanBCF_preserves_lipschitz_cone_on`; round BJ1.2 (2026-10-07) deleted the
unread binder `0 ≤ γ`. General in `F`. -/
theorem bellmanBCF_preserves_lipschitz_cone [p.StaticSelectorContinuous]
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_T * K * γ ≤ K) :
    ValueLipschitzWith (p.bellmanBCF V) K :=
  p.bellmanBCF_preserves_lipschitz_cone_on V hK_nn h_V_lip
    (fun x₁ _ x₂ _ a ha => h_U_lip x₁ x₂ a ha) (fun x₁ _ x₂ _ a ha => h_F_lip x₁ x₂ a ha) h_margin

/-! ## 3. Iteration: all Bellman iterates are `K`-Lipschitz -/

/-- The zero function is trivially `K`-Lipschitz for any `K ≥ 0`. -/
theorem valueLipschitzWith_zero {K : ℝ} (hK_nn : 0 ≤ K) :
    ValueLipschitzWith (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) K := by
  intro y₁ y₂
  simp [mul_nonneg hK_nn dist_nonneg]

/-- **Iterated Bellman preserves the Lipschitz cone, physical-state
hypotheses** (round BJ1.2, 2026-10-07). Starting from the zero function, every
`bellmanBCF^[n] 0` is `K`-Lipschitz under the cone-preservation margin, with the
stage-payoff and transition moduli assumed on feasible states only and no sign
on `γ`. General in `F`. -/
theorem bellmanBCF_iterate_zero_lipschitz_on [p.StaticSelectorContinuous]
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_T * K * γ ≤ K) :
    ∀ n, ValueLipschitzWith (p.bellmanBCF^[n]
      (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) K := by
  intro n
  induction n with
  | zero => simpa using valueLipschitzWith_zero hK_nn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p.bellmanBCF_preserves_lipschitz_cone_on
      (p.bellmanBCF^[k] 0) hK_nn ih h_U_lip h_F_lip h_margin

/-- **Iterated Bellman preserves the Lipschitz cone.** Starting from
the zero function, every `bellmanBCF^[n] 0` is `K`-Lipschitz under
the cone-preservation margin condition. The global-hypothesis specialisation
of `bellmanBCF_iterate_zero_lipschitz_on`; round BJ1.2 (2026-10-07) deleted the
unread binder `0 ≤ γ`. General in `F`. -/
theorem bellmanBCF_iterate_zero_lipschitz [p.StaticSelectorContinuous]
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_T * K * γ ≤ K) :
    ∀ n, ValueLipschitzWith (p.bellmanBCF^[n]
      (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) K :=
  p.bellmanBCF_iterate_zero_lipschitz_on hK_nn
    (fun x₁ _ x₂ _ a ha => h_U_lip x₁ x₂ a ha) (fun x₁ _ x₂ _ a ha => h_F_lip x₁ x₂ a ha) h_margin

/-! ## 4. Banach limit: `V_T` is `K`-Lipschitz from primitives -/

/-- **Value-Lipschitz discharger for the Target Bellman fixed point, physical-
state hypotheses** (round BJ1.2, 2026-10-07; the Target analogue of doc 68,
L6). The canonical Banach fixed point `p.V_T` is `K`-Lipschitz whenever the
primitive Lipschitz constants `L_U` (stage payoff) and `γ` (transition), each
assumed on feasible states only, satisfy the cone-preservation margin
`L_U + p.β_T · K · γ ≤ K`. Only `K ≥ 0` is a sign hypothesis; `γ ≥ 0` is not
needed. General in `F`. -/
theorem V_T_valueLipschitzWith_of_primitive_margin_on [p.StaticSelectorContinuous]
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_T * K * γ ≤ K) :
    ValueLipschitzWith p.V_T K := by
  -- Each iterate is K-Lipschitz.
  have h_each := p.bellmanBCF_iterate_zero_lipschitz_on
    hK_nn h_U_lip h_F_lip h_margin
  -- The iterates converge to V_T in BCF metric.
  have h_contract : ContractingWith p.β_T_nnreal p.bellmanBCF := by
    refine ⟨p.β_T_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := p.bellmanBCF_pointwise_dist V W x
    convert h using 2
  have h_tendsto :
      Tendsto (fun n => p.bellmanBCF^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
              atTop (𝓝 (ContractingWith.fixedPoint p.bellmanBCF h_contract)) :=
    ContractingWith.tendsto_iterate_fixedPoint h_contract _
  -- Banach uniqueness: ContractingWith.fixedPoint = p.V_T.
  have h_V_T_fix : Function.IsFixedPt p.bellmanBCF p.V_T := by
    have h := p.V_T_isFixedPoint
    -- h : p.bellmanBCF p.V_T = p.V_T
    exact h
  have h_unique := ContractingWith.fixedPoint_unique h_contract h_V_T_fix
  -- h_unique : p.V_T = ContractingWith.fixedPoint p.bellmanBCF h_contract
  have h_tendsto' :
      Tendsto (fun n => p.bellmanBCF^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
              atTop (𝓝 p.V_T) := by
    rw [h_unique]; exact h_tendsto
  -- Apply closure under uniform convergence.
  exact valueLipschitzWith_of_tendsto hK_nn h_each h_tendsto'

/-- **Value-Lipschitz discharger for the Target Bellman fixed point.**
The canonical Banach fixed point `p.V_T` is `K`-Lipschitz whenever
the primitive Lipschitz constants `L_U` (stage payoff) and `γ`
(transition) satisfy the cone-preservation margin
`L_U + p.β_T · K · γ ≤ K`. The global-hypothesis specialisation of
`V_T_valueLipschitzWith_of_primitive_margin_on`; round BJ1.2 (2026-10-07)
deleted the unread binder `0 ≤ γ`. General in `F`. -/
theorem V_T_valueLipschitzWith_of_primitive_margin [p.StaticSelectorContinuous]
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_T * K * γ ≤ K) :
    ValueLipschitzWith p.V_T K :=
  p.V_T_valueLipschitzWith_of_primitive_margin_on hK_nn
    (fun x₁ _ x₂ _ a ha => h_U_lip x₁ x₂ a ha) (fun x₁ _ x₂ _ a ha => h_F_lip x₁ x₂ a ha) h_margin

/-- **Existence-of-K version, physical-state hypotheses** (round BJ1.2,
2026-10-07). Given `β_T γ < 1`, taking `K = L_U / (1 - β_T γ)` discharges the
margin `L_U + β_T K γ ≤ K`, so `V_T` is `K`-Lipschitz, with the stage-payoff and
transition moduli assumed on feasible states only.

No sign hypotheses: `0 ≤ γ` was never read, and `0 ≤ L_U` follows from the
stage-payoff bound itself, evaluated at the feasible states `0` and `1` (an
absolute value is at most `L_U · |1 − 0| = L_U`). General in `F`. -/
theorem V_T_valueLipschitzWith_of_contraction_on [p.StaticSelectorContinuous]
    {L_U γ : ℝ}
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_contract : p.β_T * γ < 1) :
    ValueLipschitzWith p.V_T (L_U / (1 - p.β_T * γ)) := by
  have hL_U_nn : 0 ≤ L_U := by
    have h := h_U_lip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ 0
      ⟨le_rfl, zero_le_one⟩
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  set K : ℝ := L_U / (1 - p.β_T * γ) with hK_def
  have h_denom_pos : 0 < 1 - p.β_T * γ := by linarith
  have hK_nn : 0 ≤ K := by
    rw [hK_def]; exact div_nonneg hL_U_nn (le_of_lt h_denom_pos)
  -- Margin: L_U + β_T K γ ≤ K iff L_U ≤ K (1 - β_T γ); at
  -- K = L_U / (1 - β_T γ) we have K(1 - β_T γ) = L_U exactly.
  have h_K_id : K * (1 - p.β_T * γ) = L_U := by
    rw [hK_def]
    field_simp
  have h_margin : L_U + p.β_T * K * γ ≤ K := by
    have h_eq : L_U + p.β_T * K * γ = K := by
      have h₁ : p.β_T * K * γ = K - K * (1 - p.β_T * γ) := by ring
      rw [h₁, h_K_id]; ring
    linarith
  exact p.V_T_valueLipschitzWith_of_primitive_margin_on hK_nn
    h_U_lip h_F_lip h_margin

/-- **Existence-of-K version.** Given `β_T γ < 1`, taking
`K = L_U / (1 - β_T γ)` discharges the margin
`L_U + β_T K γ ≤ K`, so `V_T` is `K`-Lipschitz. This is the natural
form when the user supplies primitive Lipschitz constants and wants
the minimal Lipschitz bound. The global-hypothesis specialisation of
`V_T_valueLipschitzWith_of_contraction_on`; round BJ1.2 (2026-10-07) deleted
`0 ≤ γ` (never read) and `0 ≤ L_U` (derived from `h_U_lip`). General in
`F`. -/
theorem V_T_valueLipschitzWith_of_contraction [p.StaticSelectorContinuous]
    {L_U γ : ℝ}
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.U_T_at (x₂, a) - p.U_T_at (x₁, a)| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ a ∈ Sanctions.I,
      |p.F_pair (x₂, a) - p.F_pair (x₁, a)| ≤ γ * |x₂ - x₁|)
    (h_contract : p.β_T * γ < 1) :
    ValueLipschitzWith p.V_T (L_U / (1 - p.β_T * γ)) :=
  p.V_T_valueLipschitzWith_of_contraction_on
    (fun x₁ _ x₂ _ a ha => h_U_lip x₁ x₂ a ha) (fun x₁ _ x₂ _ a ha => h_F_lip x₁ x₂ a ha)
    h_contract

/-! ## 5. Sender Bellman: symmetric Lipschitz discharge

Mirror of §§1-4 above for the Sender Bellman operator
`bellmanS_BCF α hα V_S` and its Banach fixed point
`p.V_S α hα`. The structural proof is identical; the only changes are
(i) the operator takes an additional leader policy α (whose Lipschitz
properties are folded into the stage payoff hypothesis `h_U_S_lip`);
(ii) the natural transition Lipschitz constant is `γ_S = 1 - δ`
(instead of `1 - δ + δ · L_σ` for the joint Target case), since the
Sender transition `s ↦ (1 - δ) x + δ s` is purely linear in `s` with
no σ-mediated x-dependence. -/

/-- **Sender Bellman pointwise Lipschitz bound in `x`, physical-state
hypotheses** (doc 68, L6). The stage-payoff and transition moduli are assumed on
feasible inherited states only; the two states compared are feasible, so nothing
more is used. Round BJ1.2 (2026-10-07): the unread binder `0 ≤ γ` is deleted.
General in `F`. -/
theorem bellmanS_BCF_pointwise_lipschitz_in_state_on
    {α : ℝ → ℝ} (hα : Continuous α)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V_S K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    |p.bellmanS_BCF α hα V_S y₂ - p.bellmanS_BCF α hα V_S y₁|
      ≤ (L_U + p.β_S * K * γ) * dist y₁ y₂ := by
  have heq₁ : p.bellmanS_BCF α hα V_S y₁ =
      sSup ((fun s => p.integrandS α (fun y => V_S y) (y₁.val, s)) ''
              Sanctions.I) := rfl
  have heq₂ : p.bellmanS_BCF α hα V_S y₂ =
      sSup ((fun s => p.integrandS α (fun y => V_S y) (y₂.val, s)) ''
              Sanctions.I) := rfl
  have h_int_diff : ∀ s ∈ Sanctions.I,
      |p.integrandS α (fun y => V_S y) (y₂.val, s)
        - p.integrandS α (fun y => V_S y) (y₁.val, s)|
        ≤ (L_U + p.β_S * K * γ) * dist y₁ y₂ := by
    intro s hs
    change |(p.U_S y₂.val (α y₂.val) s
            + p.β_S * V_S (Sanctions.clipS' (p.F y₂.val s)))
          - (p.U_S y₁.val (α y₁.val) s
              + p.β_S * V_S (Sanctions.clipS' (p.F y₁.val s)))|
        ≤ (L_U + p.β_S * K * γ) * dist y₁ y₂
    have hdecomp :
        (p.U_S y₂.val (α y₂.val) s
            + p.β_S * V_S (Sanctions.clipS' (p.F y₂.val s)))
          - (p.U_S y₁.val (α y₁.val) s
              + p.β_S * V_S (Sanctions.clipS' (p.F y₁.val s)))
        = (p.U_S y₂.val (α y₂.val) s - p.U_S y₁.val (α y₁.val) s)
          + p.β_S * (V_S (Sanctions.clipS' (p.F y₂.val s))
                     - V_S (Sanctions.clipS' (p.F y₁.val s))) :=
      by ring
    rw [hdecomp]
    have h_tri := abs_add_le
      (p.U_S y₂.val (α y₂.val) s - p.U_S y₁.val (α y₁.val) s)
      (p.β_S * (V_S (Sanctions.clipS' (p.F y₂.val s))
                - V_S (Sanctions.clipS' (p.F y₁.val s))))
    have h_U_step : |p.U_S y₂.val (α y₂.val) s - p.U_S y₁.val (α y₁.val) s|
                      ≤ L_U * |y₂.val - y₁.val| := h_U_lip _ y₁.property _ y₂.property s hs
    have h_V_step :
        |V_S (Sanctions.clipS' (p.F y₂.val s))
         - V_S (Sanctions.clipS' (p.F y₁.val s))|
          ≤ K * (γ * |y₂.val - y₁.val|) := by
      have h_V := h_V_lip (Sanctions.clipS' (p.F y₁.val s))
                          (Sanctions.clipS' (p.F y₂.val s))
      have h_clip_lip :
          dist (Sanctions.clipS' (p.F y₁.val s))
                (Sanctions.clipS' (p.F y₂.val s))
            ≤ dist (p.F y₁.val s) (p.F y₂.val s) :=
        Sanctions.clipS'_lipschitz_dist _ _
      have h_F_step :
          dist (p.F y₁.val s) (p.F y₂.val s)
            ≤ γ * |y₂.val - y₁.val| := by
        rw [Real.dist_eq]
        have h_lip := h_F_lip y₁.val y₁.property y₂.val y₂.property s hs
        have h_swap :
            |p.F y₁.val s - p.F y₂.val s|
              = |p.F y₂.val s - p.F y₁.val s| :=
          abs_sub_comm _ _
        rw [h_swap]; exact h_lip
      have h_combined :
          dist (Sanctions.clipS' (p.F y₁.val s))
                (Sanctions.clipS' (p.F y₂.val s))
            ≤ γ * |y₂.val - y₁.val| := le_trans h_clip_lip h_F_step
      have h_K_combined :
          K * dist (Sanctions.clipS' (p.F y₁.val s))
                    (Sanctions.clipS' (p.F y₂.val s))
            ≤ K * (γ * |y₂.val - y₁.val|) :=
        mul_le_mul_of_nonneg_left h_combined hK_nn
      exact le_trans h_V h_K_combined
    have h_β_V_step :
        |p.β_S * (V_S (Sanctions.clipS' (p.F y₂.val s))
                   - V_S (Sanctions.clipS' (p.F y₁.val s)))|
          ≤ p.β_S * K * γ * |y₂.val - y₁.val| := by
      rw [abs_mul, abs_of_nonneg p.β_S_mem.1]
      have h_pos : 0 ≤ p.β_S := p.β_S_mem.1
      calc p.β_S * |V_S (Sanctions.clipS' (p.F y₂.val s))
                    - V_S (Sanctions.clipS' (p.F y₁.val s))|
          ≤ p.β_S * (K * (γ * |y₂.val - y₁.val|)) :=
            mul_le_mul_of_nonneg_left h_V_step h_pos
        _ = p.β_S * K * γ * |y₂.val - y₁.val| := by ring
    have h_dist_eq : dist y₁ y₂ = |y₂.val - y₁.val| := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [h_dist_eq]
    calc
      |(p.U_S y₂.val (α y₂.val) s - p.U_S y₁.val (α y₁.val) s)
        + p.β_S * (V_S (Sanctions.clipS' (p.F y₂.val s))
                   - V_S (Sanctions.clipS' (p.F y₁.val s)))|
        ≤ |p.U_S y₂.val (α y₂.val) s - p.U_S y₁.val (α y₁.val) s|
          + |p.β_S * (V_S (Sanctions.clipS' (p.F y₂.val s))
                       - V_S (Sanctions.clipS' (p.F y₁.val s)))| :=
          h_tri
      _ ≤ L_U * |y₂.val - y₁.val| + p.β_S * K * γ * |y₂.val - y₁.val| := by
          exact add_le_add h_U_step h_β_V_step
      _ = (L_U + p.β_S * K * γ) * |y₂.val - y₁.val| := by ring
  rw [heq₁, heq₂]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := (L_U + p.β_S * K * γ) * dist y₁ y₂)
    (Bf := sSup ((fun s => p.integrandS α (fun y => V_S y) (y₂.val, s)) ''
                  Sanctions.I))
    (Bg := sSup ((fun s => p.integrandS α (fun y => V_S y) (y₁.val, s)) ''
                  Sanctions.I))
  · intro s hs; exact h_int_diff s hs
  · intro s hs
    exact le_csSup (p.integrandS_image_bddAbove hα V_S.continuous y₂.val)
      ⟨s, hs, rfl⟩
  · intro s hs
    exact le_csSup (p.integrandS_image_bddAbove hα V_S.continuous y₁.val)
      ⟨s, hs, rfl⟩

/-- **Sender Bellman pointwise Lipschitz bound in `x`.** Mirror of
`bellmanBCF_pointwise_lipschitz_in_state`. Round BJ1.2 (2026-10-07): the unread
binder `0 ≤ γ` is deleted. General in `F`. -/
theorem bellmanS_BCF_pointwise_lipschitz_in_state
    {α : ℝ → ℝ} (hα : Continuous α)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V_S K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    |p.bellmanS_BCF α hα V_S y₂ - p.bellmanS_BCF α hα V_S y₁|
      ≤ (L_U + p.β_S * K * γ) * dist y₁ y₂ :=
  p.bellmanS_BCF_pointwise_lipschitz_in_state_on hα V_S hK_nn h_V_lip
    (fun x₁ _ x₂ _ s hs => h_U_lip x₁ x₂ s hs) (fun x₁ _ x₂ _ s hs => h_F_lip x₁ x₂ s hs) y₁ y₂

/-- **One-step cone preservation, physical-state hypotheses** (doc 68, L6).
Round BJ1.2 (2026-10-07): the unread binder `0 ≤ γ` is deleted. General in
`F`. -/
theorem bellmanS_BCF_preserves_lipschitz_cone_on
    {α : ℝ → ℝ} (hα : Continuous α)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V_S K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_S * K * γ ≤ K) :
    ValueLipschitzWith (p.bellmanS_BCF α hα V_S) K := by
  intro y₁ y₂
  have h_step :=
    p.bellmanS_BCF_pointwise_lipschitz_in_state_on hα V_S hK_nn
      h_V_lip h_U_lip h_F_lip y₁ y₂
  have h_dist_nn : 0 ≤ dist y₁ y₂ := dist_nonneg
  calc |p.bellmanS_BCF α hα V_S y₂ - p.bellmanS_BCF α hα V_S y₁|
      ≤ (L_U + p.β_S * K * γ) * dist y₁ y₂ := h_step
    _ ≤ K * dist y₁ y₂ := mul_le_mul_of_nonneg_right h_margin h_dist_nn

/-- **Sender Bellman one-step Lipschitz-cone preservation.** Mirror of
`bellmanBCF_preserves_lipschitz_cone`. Round BJ1.2 (2026-10-07): the unread
binder `0 ≤ γ` is deleted. General in `F`. -/
theorem bellmanS_BCF_preserves_lipschitz_cone
    {α : ℝ → ℝ} (hα : Continuous α)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_V_lip : ValueLipschitzWith V_S K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_S * K * γ ≤ K) :
    ValueLipschitzWith (p.bellmanS_BCF α hα V_S) K :=
  p.bellmanS_BCF_preserves_lipschitz_cone_on hα V_S hK_nn h_V_lip
    (fun x₁ _ x₂ _ s hs => h_U_lip x₁ x₂ s hs) (fun x₁ _ x₂ _ s hs => h_F_lip x₁ x₂ s hs) h_margin

/-- **Iterated cone preservation, physical-state hypotheses** (doc 68, L6).
Round BJ1.2 (2026-10-07): the unread binder `0 ≤ γ` is deleted. General in
`F`. -/
theorem bellmanS_BCF_iterate_zero_lipschitz_on
    {α : ℝ → ℝ} (hα : Continuous α)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_S * K * γ ≤ K) :
    ∀ n, ValueLipschitzWith ((p.bellmanS_BCF α hα)^[n]
      (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) K := by
  intro n
  induction n with
  | zero => simpa using valueLipschitzWith_zero hK_nn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p.bellmanS_BCF_preserves_lipschitz_cone_on hα _ hK_nn ih
      h_U_lip h_F_lip h_margin

/-- **Iterated Sender Bellman preserves the Lipschitz cone.** Round BJ1.2
(2026-10-07): the unread binder `0 ≤ γ` is deleted. General in `F`. -/
theorem bellmanS_BCF_iterate_zero_lipschitz
    {α : ℝ → ℝ} (hα : Continuous α)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_S * K * γ ≤ K) :
    ∀ n, ValueLipschitzWith ((p.bellmanS_BCF α hα)^[n]
      (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) K :=
  p.bellmanS_BCF_iterate_zero_lipschitz_on hα hK_nn
    (fun x₁ _ x₂ _ s hs => h_U_lip x₁ x₂ s hs) (fun x₁ _ x₂ _ s hs => h_F_lip x₁ x₂ s hs) h_margin

/-- **Value-Lipschitz discharger, physical-state hypotheses** (doc 68, L6).
Round BJ1.2 (2026-10-07): the unread binder `0 ≤ γ` is deleted. General in
`F`. -/
theorem V_S_valueLipschitzWith_of_primitive_margin_on
    {α : ℝ → ℝ} (hα : Continuous α)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_S * K * γ ≤ K) :
    ValueLipschitzWith (p.V_S α hα) K := by
  have h_each := p.bellmanS_BCF_iterate_zero_lipschitz_on hα
    hK_nn h_U_lip h_F_lip h_margin
  have h_contract : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) :=
    p.bellmanS_BCF_contracting hα
  have h_tendsto :
      Tendsto (fun n => (p.bellmanS_BCF α hα)^[n]
                          (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
              atTop (𝓝 (ContractingWith.fixedPoint
                          (p.bellmanS_BCF α hα) h_contract)) :=
    ContractingWith.tendsto_iterate_fixedPoint h_contract _
  have h_V_S_fix : Function.IsFixedPt (p.bellmanS_BCF α hα) (p.V_S α hα) :=
    p.V_S_isFixedPoint hα
  have h_unique := ContractingWith.fixedPoint_unique h_contract h_V_S_fix
  have h_tendsto' :
      Tendsto (fun n => (p.bellmanS_BCF α hα)^[n]
                          (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
              atTop (𝓝 (p.V_S α hα)) := by
    rw [h_unique]; exact h_tendsto
  exact valueLipschitzWith_of_tendsto hK_nn h_each h_tendsto'

/-- **Value-Lipschitz discharger for the Sender Bellman fixed point.**
Mirror of `V_T_valueLipschitzWith_of_primitive_margin`. Round BJ1.2
(2026-10-07): the unread binder `0 ≤ γ` is deleted. General in `F`. -/
theorem V_S_valueLipschitzWith_of_primitive_margin
    {α : ℝ → ℝ} (hα : Continuous α)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + p.β_S * K * γ ≤ K) :
    ValueLipschitzWith (p.V_S α hα) K :=
  p.V_S_valueLipschitzWith_of_primitive_margin_on hα hK_nn
    (fun x₁ _ x₂ _ s hs => h_U_lip x₁ x₂ s hs) (fun x₁ _ x₂ _ s hs => h_F_lip x₁ x₂ s hs) h_margin

/-- **Existence-of-K discharger, physical-state hypotheses** (doc 68, L6).
Round BJ1.2 (2026-10-07): no sign hypotheses. `0 ≤ γ` was never read, and
`0 ≤ L_U` follows from the stage-payoff bound at the feasible states `0` and `1`
(an absolute value is at most `L_U · |1 − 0| = L_U`). General in `F`. -/
theorem V_S_valueLipschitzWith_of_contraction_on
    {α : ℝ → ℝ} (hα : Continuous α)
    {L_U γ : ℝ}
    (h_U_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_contract : p.β_S * γ < 1) :
    ValueLipschitzWith (p.V_S α hα) (L_U / (1 - p.β_S * γ)) := by
  have hL_U_nn : 0 ≤ L_U := by
    have h := h_U_lip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ 0
      ⟨le_rfl, zero_le_one⟩
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  set K : ℝ := L_U / (1 - p.β_S * γ) with hK_def
  have h_denom_pos : 0 < 1 - p.β_S * γ := by linarith
  have hK_nn : 0 ≤ K := by
    rw [hK_def]; exact div_nonneg hL_U_nn (le_of_lt h_denom_pos)
  have h_K_id : K * (1 - p.β_S * γ) = L_U := by
    rw [hK_def]
    field_simp
  have h_margin : L_U + p.β_S * K * γ ≤ K := by
    have h_eq : L_U + p.β_S * K * γ = K := by
      have h₁ : p.β_S * K * γ = K - K * (1 - p.β_S * γ) := by ring
      rw [h₁, h_K_id]; ring
    linarith
  exact p.V_S_valueLipschitzWith_of_primitive_margin_on hα hK_nn
    h_U_lip h_F_lip h_margin

/-- **Existence-of-K version for the Sender Bellman fixed point.**
Mirror of `V_T_valueLipschitzWith_of_contraction`. Round BJ1.2 (2026-10-07):
`0 ≤ γ` (never read) and `0 ≤ L_U` (derived from `h_U_lip`) are deleted.
General in `F`. -/
theorem V_S_valueLipschitzWith_of_contraction
    {α : ℝ → ℝ} (hα : Continuous α)
    {L_U γ : ℝ}
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.F x₂ s - p.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_contract : p.β_S * γ < 1) :
    ValueLipschitzWith (p.V_S α hα) (L_U / (1 - p.β_S * γ)) :=
  p.V_S_valueLipschitzWith_of_contraction_on hα
    (fun x₁ _ x₂ _ s hs => h_U_lip x₁ x₂ s hs) (fun x₁ _ x₂ _ s hs => h_F_lip x₁ x₂ s hs) h_contract

/-- **General-`F` closed-form Sender value regularity on the physical square**
(doc 68, L6). This is the form the manuscript's (F6-Q) states: the inherited-state
modulus `γ_F` is assumed for feasible inherited states only, and the stage payoff
along the leader policy is Lipschitz in the inherited state on the square.

Round BJ1.2 (2026-10-07, author-approved re-pin of evidence row 905): the sign
binders `0 ≤ L_U_S` and `0 ≤ γ_F` are deleted. The first is derived from the
stage-payoff bound at the states `0` and `1`; the second was never read. The
statement now asks for exactly what (F6-Q) states: a stage-payoff modulus, a
transition state modulus on the square, and `β_S · γ_F < 1`. -/
theorem V_S_valueLipschitzWith_of_transitionStateLipschitzOn
    {α : ℝ → ℝ} (hα : Continuous α)
    {L_U_S γ_F : ℝ}
    (h_U_S_lip : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U_S * |x₂ - x₁|)
    (h_F_state_lip : p.TransitionStateLipschitzOnWith γ_F)
    (h_discounted_persistence : p.β_S * γ_F < 1) :
    ValueLipschitzWith (p.V_S α hα) (L_U_S / (1 - p.β_S * γ_F)) :=
  p.V_S_valueLipschitzWith_of_contraction_on hα
    h_U_S_lip h_F_state_lip h_discounted_persistence

/-- **General-`F` closed-form Sender value regularity.**

This wrapper restates `V_S_valueLipschitzWith_of_contraction` using the
transparent, paper-facing transition condition
`TransitionStateLipschitzWith γ_F`. If the Sender's stage payoff along
the continuous leader policy is `L_U_S`-Lipschitz in the inherited
state and discounted transition persistence satisfies
`β_S * γ_F < 1`, then the constructed Sender Bellman fixed point is

`L_U_S / (1 - β_S * γ_F)`-Lipschitz.

The assumption is optional: it is used for this quantitative
closed-form route, not for the baseline qualitative general-`F`
results. Round BJ1.2 (2026-10-07): `0 ≤ L_U_S` (derived) and `0 ≤ γ_F` (never
read) are deleted. -/
theorem V_S_valueLipschitzWith_of_transitionStateLipschitz
    {α : ℝ → ℝ} (hα : Continuous α)
    {L_U_S γ_F : ℝ}
    (h_U_S_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U_S * |x₂ - x₁|)
    (h_F_state_lip : p.TransitionStateLipschitzWith γ_F)
    (h_discounted_persistence : p.β_S * γ_F < 1) :
    ValueLipschitzWith (p.V_S α hα) (L_U_S / (1 - p.β_S * γ_F)) :=
  p.V_S_valueLipschitzWith_of_transitionStateLipschitzOn hα
    (fun x₁ _ x₂ _ s hs => h_U_S_lip x₁ x₂ s hs) h_F_state_lip.toOn h_discounted_persistence

/-- **General-`F` Sender monotonicity from primitive state regularity
and the exact transition-adjusted sanction chord.**

The transition-state Lipschitz condition and discounted-persistence
margin first derive the closed-form Lipschitz bound on the constructed
Sender value. The exact sanction chord then compares the current
payoff gain from a higher sanction with the actual continuation-state
movement under `F`. Their composition makes the Sender's full dynamic
objective strictly increasing without imposing an affine transition or
a separate sanction-Lipschitz modulus. Round BJ1.2 (2026-10-07): the sign
binders `0 ≤ L_U_S` (derived) and `0 ≤ γ_F` (never read) are deleted. -/
theorem senderDynObjective_strictMono_of_transition_adjusted_chord_and_stateLipschitz
    {α : ℝ → ℝ} (hα : Continuous α)
    {x sbar L_U_S γ_F : ℝ}
    (h_U_S_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U_S * |x₂ - x₁|)
    (h_F_state_lip : p.TransitionStateLipschitzWith γ_F)
    (h_discounted_persistence : p.β_S * γ_F < 1)
    (h_transition_adjusted_chord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ < s₂ →
          p.β_S * (L_U_S / (1 - p.β_S * γ_F)) *
              dist (Sanctions.clipS' (p.F x s₁))
                   (Sanctions.clipS' (p.F x s₂))
            < p.U_S x (α x) s₂ - p.U_S x (α x) s₁) :
    StrictMonoOn
      (fun s => p.senderDynObjective (p.V_S α hα) x (α x) s)
      (Set.Icc (0 : ℝ) (max x sbar)) :=
  p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
    h_transition_adjusted_chord
    (p.V_S_valueLipschitzWith_of_transitionStateLipschitz hα
      h_U_S_lip h_F_state_lip h_discounted_persistence)

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
