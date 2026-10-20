/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.MechanismWitnessShockedUnconditional
import Sanctions.Theory.Basin.WeakFloorBasin

/-!
# P3 satisfies the weak sanction floor: an analytic Sender-spread bound

**Positive resolution (2026-07-29) of the off-corner persistence question.**

The strong ratchet floor `s(x) ≥ max{x, s̄}` forces `s(1) = 1`, and since
`F_diag` is a maintained field of the parameter structure the top state is then
absorbing, which switches off the Target's continuation channel there
(`Theory/Equilibrium/AbsorbingTopObstruction`).  The full-width `P₃` economy has
`s(1) < 1` for *every* equilibrium (`mwShockedOne_no_top_floor`), so by the
general lemma `Sanctions.no_upper_basin_floor_of_top_lt_one` it can never
satisfy the strong floor on *any* basin.

`Theory/Basin/WeakFloorBasin` supplies the weaker structure: a floor relative to
a fixed level, `s̄ ≤ s(x)`, which still yields basin invariance for a general
transition.  **This file proves that `P₃` satisfies it**, so the off-corner
economy does support persistence once "sanctions never fall" is relinquished.

## The bound, and why it had to be derived here

Everything reduces to one inequality.  The interior floor test is exact
(`x ≤ σ_dyn_top ↔ 2 + 10·α(x) ≤ 3x + Δ_S`, where `Δ_S := V_S(1) − V_S(0)`), so
the whole question is a **lower** bound on the Sender's endpoint spread.  The
repository had only *upper* bounds; a sweep of the local reference libraries
found no theorem giving a lower bound on a value-function endpoint spread, and
an online search added only negative results.  So the bound is derived from the
economy's own primitives.

Because the half-width-one smear is exactly affine
(`movAvgBCF_one_sub_eq`), subtracting the two Sender Bellman equations at the
endpoints yields an **identity**, not an inequality
(`mwSenderSpread_raw_identity`).  At the top state the Sender response *is* the
unclipped vertex (`mwTopResponse_eq`), so `α(1)` can be eliminated.

That elimination step is not new — earlier work along this route already used
the exact top response to bootstrap a bound of `22/15`.  **What is new here is
keeping the relation as an equation**, so that the `Δ_S · s₁` cross term cancels
identically rather than being bounded, leaving
`mwSenderSpread_reduced_identity`.  Its right-hand side decreases in `s₁` and
the `s₀` coefficients drop out, giving `Δ_S ≥ 11/7`
(`mwD_ge_eleven_sevenths`) with no appeal to the corner deficit.  The second new
ingredient is `mwAlphaOne_lb`: a lower bound on `α(1)` from an *upward* Target
deviation, using only the repository's existing cap `Δ_T ≤ 60/11`, giving
`α(1) ≥ 5/12` (`mwAlphaOne_ge_5_12`) and hence

  `mwD_ge_seventeen_tenths` : `17/10 ≤ V_S(1) − V_S(0)`

for **every** shocked equilibrium — no hypothesis beyond the equilibrium itself,
and no assumed numerical input.

## The route that does *not* close, and the exact status of that claim

The natural closing move is an *upper* bound on `α` at the pivot.  It is
derivable — `mwAlpha_le_at_pivot` gives `α(1/2) ≤ 37/160` — and it does **not
suffice**: the test needs `α(1/2) ≤ (2Δ_S − 1)/20`, and
`pivot_alpha_ceiling_gap` machine-checks that this is strictly below `37/160`
even at `Δ_S = 17/10`.

**Read that at its true strength.** `pivot_alpha_ceiling_gap` is an inequality
between two constants: it shows *this* derived ceiling misses *this* target.  It
is **not** an impossibility theorem, and it does not show that no `α`-ceiling
argument could work — a sharper ceiling from some other route is not excluded.
Note also that `mwAlpha_le_at_pivot` is itself read off the floor, so using it
to rule out an alternative derivation of the floor would be circular; it is
recorded as a diagnostic, not as an obstruction.

What closes the floor here is instead a *downward* Target deviation, which needs
no `α` bound at all.

## Rule 5: the floor is parametric

`mwWeakFloor_param` establishes the floor at **every** pivot/floor pair
satisfying `2/5 ≤ x̄ ≤ 1` and the single rational inequality
`41760·s̄ < 31530·x̄ + 5329`; `s̄ ≤ 1` is a consequence, not a hypothesis.  The
concrete pivots `(2/5, 5/12)` and `(1/2, 1/2)` are one-line corollaries, and
basin invariance at each follows by the general-`F` weak-floor step lemma
`weakFloor_dynamicTopStepF_mem_basin` — no affineness, no `s(x) ≥ x`, and not
even `top_rule_mono`.

## Rule 11: non-vacuity and an independent cross-check

Every statement here is quantified over
`(mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop`.  That type is
inhabited by the explicitly *constructed* `mwEqEquilibrium`, so nothing below is
vacuous.

There is no uniqueness theorem for that economy, so the constructed
equilibrium's pinned spread interval cannot serve an arbitrary equilibrium.  It
is used instead as a falsification test: `mwD_pin_at_constructed` recovers the
interval `[441/250, 17641/10000]` for the same object and
`taskB_bound_below_pin` checks `17/10 ≤ 441/250`.  Had the analytic route
produced anything above the pin, the two would be inconsistent.  They agree.
`taskB_bound_strictly_improves` records the ladder
`22/15 < 11/7 < 17/10 ≤ Δ_S`.

## Scope

The floor is established on `[x̄, 1]` for the pivots above; `mwWeakFloor_param`
delimits where the argument reaches.  Nothing here revives the strong ratchet
floor, which remains impossible at this economy — and nothing here bears on the
absorbing-boundary obstruction, which concerns the corner and is unaffected.

Two honest limits on the bound itself.  First, `17/10` is **load-bearing, not
slack**: the weaker `22/15` from the earlier route does *not* close the floor at
the `(1/2, 1/2)` pivot, so the improvement is doing work rather than decorating.
Second, `17/10` is short of the true spread, and that shortfall is a property of
the route rather than of the arithmetic — the bounding quadratic's exact root is
below the actual value, so no amount of tightening *within this argument* closes
the remaining gap.  It does not need to: the weak floor requires only
`Δ_S ≥ 4/5`.
-/

namespace Sanctions
namespace Examples
namespace P3WeakFloor

open Set Filter
open AbstractGame
open scoped NNReal Topology
open BoundedContinuousFunction

/-! ### §0.  `clip = max 0 ∘ min 1` is monotone and 1-Lipschitz. -/

theorem min_one_sub_le {u v : ℝ} (h : v ≤ u) : min 1 u - min 1 v ≤ u - v := by
  rcases min_cases (1:ℝ) u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
    rcases min_cases (1:ℝ) v with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;>
    rw [hu, hv] <;> linarith

theorem max_zero_sub_le {u v : ℝ} (h : v ≤ u) : max 0 u - max 0 v ≤ u - v := by
  rcases max_cases (0:ℝ) u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
    rcases max_cases (0:ℝ) v with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;>
    rw [hu, hv] <;> linarith

theorem clip_mono {u v : ℝ} (h : v ≤ u) :
    max 0 (min 1 v) ≤ max 0 (min 1 u) :=
  max_le_max_left _ (min_le_min_left _ h)

theorem clip_sub_le {u v : ℝ} (h : v ≤ u) :
    max 0 (min 1 u) - max 0 (min 1 v) ≤ u - v :=
  le_trans (max_zero_sub_le (min_le_min_left _ h)) (min_one_sub_le h)

/-! ### §1.  The repo's Sender endpoint cap, in closed form. -/

theorem mwD_le (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) ≤ 45 / 16 := by
  have h := mwShockedOne_sender_endpoint_spread_le E
  have ha1 := E.α_mem 1 (by norm_num)
  have ha0 := E.α_mem 0 (by norm_num)
  linarith [ha1.2, ha0.1]

/-! ### §2.  The Target endpoint spread is nonnegative. -/

theorem mwT_spread_nonneg
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    0 ≤ E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) := by
  have hx0val : ((Sanctions.clipS' (0:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 0 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hx1val : ((Sanctions.clipS' (1:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 1 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have ha0 : E.α 0 ∈ Sanctions.I := E.α_mem 0 (by norm_num)
  have hs0 : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs1 : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hbell0 := mwShockedOne_target_bellman_eq_at_alpha E (Sanctions.clipS' 0)
  have hbell1 := mwShockedOne_target_bellman_eq_at_alpha E (Sanctions.clipS' 1)
  rw [hx0val] at hbell0
  rw [hx1val] at hbell1
  have hopt1 := E.α_opt_shock 1 (by norm_num) ha0
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 0) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1) at hopt1
  have hvalue : E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) ≥
      mechanismWitnessParams.joint_T_top_integrand
          (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 0) -
        mechanismWitnessParams.joint_T_top_integrand
          (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 (E.α 0) := by
    rw [hbell0, hbell1]; linarith
  have hJ1 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 0)
      = mwU_T 1 (E.α 0)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0)))) := rfl
  have hJ0 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 (E.α 0)
      = mwU_T 0 (E.α 0)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 0
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)))) := rfl
  rw [hJ1, hJ0] at hvalue
  have hF0 : mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 0 _ (by norm_num) hs0
  have hF1 : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ (by norm_num) hs1
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))))
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0))))
  rw [Sanctions.clipS'_val_eq_of_mem hF0, Sanctions.clipS'_val_eq_of_mem hF1] at hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope hvalue
  unfold mwU_T at hvalue
  by_contra hcon
  rw [not_le] at hcon
  have hA : 0 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0)
      * E.α 0 := mul_nonneg hs1.1 ha0.1
  have hB : 0 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)
      * (1 - E.α 0) := mul_nonneg hs0.1 (sub_nonneg.mpr ha0.2)
  have hC : 0 ≤ (1 - (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 0)
        - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)))
      * (-(E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0))) :=
    mul_nonneg (by linarith [hs1.2, hs0.1]) (by linarith)
  nlinarith [hvalue, hslope, hA, hB, hC, ha0.1, hs0.1, hs1.1]

/-! ### §3.  Bottom-state compliance is exactly zero. -/

theorem mwAlphaZero
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.α 0 = 0 := by
  have hZ := mwT_spread_nonneg E
  have hDle := mwD_le E
  have ha0 : E.α 0 ∈ Sanctions.I := E.α_mem 0 (by norm_num)
  have h0S : (0:ℝ) ∈ Sanctions.S := by norm_num
  have hsa := mwSigmaDynTop_eq_clip_vertex_one E.V_S h0S (E.α 0)
  have hs0 := mwSigmaDynTop_eq_clip_vertex_one E.V_S h0S (0:ℝ)
  have hvle : mwSenderVertexOne E.V_S 0 (E.α 0) ≤ mwSenderVertexOne E.V_S 0 0 := by
    unfold mwSenderVertexOne; linarith [ha0.1]
  have hd_nonneg : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)
      ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 := by
    rw [hsa, hs0]; exact clip_mono hvle
  have hd_le : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)
      ≤ (5/12) * E.α 0 := by
    rw [hsa, hs0]
    have hcs := clip_sub_le hvle
    unfold mwSenderVertexOne at hcs ⊢
    linarith
  have hs0_le : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ≤ 13 / 384 := by
    rw [hs0]
    refine max_le (by norm_num) (le_trans (min_le_right _ _) ?_)
    unfold mwSenderVertexOne; linarith
  have hsa_le : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)
      ≤ 13 / 384 := le_trans hd_nonneg hs0_le
  have hsa_nonneg : 0 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0) :=
    (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _).1
  have hopt := E.α_opt_shock 0 h0S (show (0:ℝ) ∈ Sanctions.I by norm_num)
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 0 ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 (E.α 0) at hopt
  have hJa : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 (E.α 0)
      = mwU_T 0 (E.α 0)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 0
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)))) := rfl
  have hJ0 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 0
      = mwU_T 0 0 (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 0
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))) := rfl
  rw [hJa, hJ0] at hopt
  have hFa : mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 0 _ h0S
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hFb : mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 0 _ h0S
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)))
    (Sanctions.clipS' (mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))))
  rw [Sanctions.clipS'_val_eq_of_mem hFb, Sanctions.clipS'_val_eq_of_mem hFa] at hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope hopt
  unfold mwU_T at hopt
  refine le_antisymm ?_ ha0.1
  by_contra hpos
  rw [not_le] at hpos
  have hdZ : 0 ≤ (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0))
      * (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)) :=
    mul_nonneg (by linarith) hZ
  have hsaa : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 (E.α 0)
      * E.α 0 ≤ (13/384) * E.α 0 :=
    mul_le_mul_of_nonneg_right hsa_le ha0.1
  nlinarith [hopt, hslope, hdZ, hsaa, hd_le, ha0.1, hpos, sq_nonneg (E.α 0)]

/-! ### §4.  THE EXACT SENDER ENDPOINT IDENTITY, AND `Δ_S ≥ 11/7`.

Write `Δ := V_S(1) − V_S(0)`, `s₁ := σ(1, α(1))`, `s₀ := σ(0, 0)`.

**Raw identity.**  Both Sender Bellman values are *exactly* their dynamic
objectives at the greatest response, and at half-width one the smeared
continuation is *exactly affine* with slope `Δ/2`
(`movAvgBCF_one_sub_eq`).  Subtracting the two Bellman equations therefore
gives an EQUATION, not an inequality:

    Δ · (4/5 − (s₁ − s₀)/20)  =  stage gain.

**Reduced identity.**  At the top state the Sender response is the *unclipped*
quadratic vertex `s₁ = 25/24 + Δ/24 − (5/12)·α(1)`, so `α(1)` can be
*eliminated*: `α(1) = 5/2 + Δ/10 − (12/5)·s₁`.  Substituting kills the entire
`Δ·s₁` cross term and leaves

    Δ · (7/10 + s₀/20)  =  29/10 − (12/5)·s₁ + (3/5)·s₁² + (3/5)·s₀² + s₀/10.

**Bound.**  The right-hand side is *decreasing* in `s₁` on `[0,1]`, so it is
minimised at `s₁ = 1`, where it equals `11/10 + (3/5)s₀² + s₀/10`.  Hence
`Δ(14 + s₀) ≥ 22 + 2s₀ + 12s₀²`, and since the `s₀`-coefficients satisfy
`14·2 ≥ 22·1`, that forces `Δ ≥ 11/7` for EVERY `s₀ ≥ 0`. -/

/-- The purely arithmetic core: the reduced identity plus `s₁ ≤ 1`, `s₀ ≥ 0`
forces `11/7 ≤ Δ`.  No Lean-side model content. -/
theorem spread_lower_arith {D s1 s0 : ℝ}
    (hs1 : s1 ≤ 1) (hs0 : 0 ≤ s0)
    (heq : D * (7/10 + s0/20)
      = 29/10 - (12/5) * s1 + (3/5) * s1^2 + (3/5) * s0^2 + s0/10) :
    11/7 ≤ D := by
  nlinarith [heq, hs0, sq_nonneg s0,
    mul_nonneg (sub_nonneg.mpr hs1) (by linarith : (0:ℝ) ≤ 3 - s1)]

set_option maxHeartbeats 1600000 in
/-- **The exact Sender endpoint equation at P3** (raw form, before eliminating
`α(1)`).  `α(0) = 0` has been substituted. -/
theorem mwSenderSpread_raw_identity
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
      * (4/5 - (1/20) * (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
          - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))
      = E.α 1 * (1 - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) / 2)
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            * (5/4 - (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + 2/5
        + (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 ^ 2
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 10 := by
  have hx0val : ((Sanctions.clipS' (0:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 0 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hx1val : ((Sanctions.clipS' (1:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 1 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have h0S : (0:ℝ) ∈ Sanctions.S := by norm_num
  have h1S : (1:ℝ) ∈ Sanctions.S := by norm_num
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs0I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hbell0 := mwShockedOne_sender_bellman_eq_at_sigma E (Sanctions.clipS' 0)
  have hbell1 := mwShockedOne_sender_bellman_eq_at_sigma E (Sanctions.clipS' 1)
  rw [hx0val, mwAlphaZero E] at hbell0
  rw [hx1val] at hbell1
  have hO0 : mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S) 0 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
      = mwU_S 0 0 (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
        + (1/2) * Sanctions.movAvgBCF one_pos E.V_S
            (Sanctions.clipS' (mechanismWitnessParams.F 0
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))) := rfl
  have hO1 : mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S) 1 (E.α 1)
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      = mwU_S 1 (E.α 1) (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + (1/2) * Sanctions.movAvgBCF one_pos E.V_S
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)))) := rfl
  rw [hO0] at hbell0
  rw [hO1] at hbell1
  have hF0 : mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 0 _ h0S hs0I
  have hF1 : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S hs1I
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_S
    (Sanctions.clipS' (mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)))
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))))
  rw [Sanctions.clipS'_val_eq_of_mem hF0, Sanctions.clipS'_val_eq_of_mem hF1] at hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope hbell0 hbell1
  unfold mwU_S at hbell0 hbell1
  linear_combination hbell1 - hbell0 + (1/2) * hslope

/-- The stage gain on the right of the raw identity is at least `2/5`
(each summand is separately nonnegative on `[0,1]²`). -/
theorem mwSenderSpread_stage_ge
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (2:ℝ)/5 ≤
      E.α 1 * (1 - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) / 2)
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            * (5/4 - (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + 2/5
        + (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 ^ 2
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 10 := by
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs0I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have h1 : 0 ≤ E.α 1 *
      (1 - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) / 2) :=
    mul_nonneg ha1.1 (by linarith [hs1I.2])
  have h2 : 0 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      * (5/4 - (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)) :=
    mul_nonneg hs1I.1 (by linarith [hs1I.2])
  nlinarith [hs0I.1, sq_nonneg (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)]

/-- A crude but unconditional positivity: `Δ_S ≥ 8/17 > 0`.  The smear-chord
factor is at most `17/20` and the stage gain at least `2/5`. -/
theorem mwD_pos
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (8:ℝ)/17 ≤ E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) := by
  have heq := mwSenderSpread_raw_identity E
  have hstage := mwSenderSpread_stage_ge E
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs0I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  nlinarith [heq, hstage, hs1I.1, hs1I.2, hs0I.1, hs0I.2]

/-- **The top-state Sender response is the unclipped vertex.**  Positivity of
`Δ_S` puts the vertex above `0`; the proved top-state obstruction
`mwShockedOne_no_top_floor` puts it strictly below `1`. -/
theorem mwTopResponse_eq
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      = 25/24 + (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))/24
        - (5/12) * E.α 1 := by
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have hDpos := mwD_pos E
  have hdeficit : E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)
      < 10 * E.α 1 - 1 := by
    by_contra hcon
    exact mwShockedOne_no_top_floor E
      (le_of_eq ((mwSigmaDynTop_one_top_eq_one_iff E.V_S (E.α 1)).mpr (not_lt.mp hcon)).symm)
  rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S (by norm_num) (E.α 1)]
  have hvlt : mwSenderVertexOne E.V_S 1 (E.α 1) < 1 := by
    unfold mwSenderVertexOne; linarith
  have hvpos : (0:ℝ) < mwSenderVertexOne E.V_S 1 (E.α 1) := by
    unfold mwSenderVertexOne; linarith [ha1.2]
  rw [min_eq_right (le_of_lt hvlt), max_eq_right (le_of_lt hvpos)]
  unfold mwSenderVertexOne; ring

/-- **The reduced Sender endpoint identity.**  `α(1)` has been eliminated; the
`Δ·s₁` cross term cancels identically. -/
theorem mwSenderSpread_reduced_identity
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
      * (7/10 + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 20)
      = 29/10
        - (12/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
        + (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) ^ 2
        + (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 ^ 2
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 10 := by
  have heq := mwSenderSpread_raw_identity E
  have hs1 := mwTopResponse_eq E
  linear_combination heq
    + (12/5 - (6/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      * hs1

/-- **THE LOWER BOUND.**  `11/7 ≤ Δ_S` for every full-width P3 shocked
equilibrium.  No new hypothesis: the inputs are the two Bellman fixed points,
the exact affine smear at half-width one, the exact clipped-vertex Sender
selector, `α(0) = 0`, and the proved top-state obstruction. -/
theorem mwD_ge_eleven_sevenths
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (11:ℝ)/7 ≤ E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) :=
  spread_lower_arith
    (mechanismWitnessParams.σ_dyn_top_mem_I (mwSenderValueOne E.V_S) 1 (E.α 1)).2
    (mechanismWitnessParams.σ_dyn_top_mem_I (mwSenderValueOne E.V_S) 0 0).1
    (mwSenderSpread_reduced_identity E)

/-! ### §5.  Consequences: the top response and the Target spread. -/

theorem mwSigmaMono
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) := by
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S (by norm_num) 0,
    mwSigmaDynTop_eq_clip_vertex_one E.V_S (by norm_num) (E.α 1)]
  refine clip_mono ?_
  unfold mwSenderVertexOne; linarith [ha1.2]

/-- `s(1) ≥ 29/42`: the unclipped vertex at the top state, evaluated at the
worst feasible compliance `α(1) = 1` and the proved spread floor `11/7`. -/
theorem mwTopResponse_ge_29_42
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (29:ℝ)/42 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) := by
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  rw [mwTopResponse_eq E]
  linarith [mwD_ge_eleven_sevenths E, ha1.2]

set_option maxHeartbeats 1600000 in
/-- `Δ_T ≥ 1/2`.  Same exact-equation route on the Target side: with `α(0) = 0`
the bottom stage payoff is `−s(0)/2 ≤ 0`, at the top state the Target *likes*
the sanction (`∂U_T/∂s = 1/2 + a/2 > 0` there), so the stage gain is at least
`s(1)/2 ≥ 29/84`; dividing by the smear factor `16/25` gives `≥ 725/1344`. -/
theorem mwT_spread_ge_half
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (1:ℝ)/2 ≤ E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) := by
  have hx0val : ((Sanctions.clipS' (0:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 0 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hx1val : ((Sanctions.clipS' (1:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 1 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have h0S : (0:ℝ) ∈ Sanctions.S := by norm_num
  have h1S : (1:ℝ) ∈ Sanctions.S := by norm_num
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs0I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hbell0 := mwShockedOne_target_bellman_eq_at_alpha E (Sanctions.clipS' 0)
  have hbell1 := mwShockedOne_target_bellman_eq_at_alpha E (Sanctions.clipS' 1)
  rw [hx0val, mwAlphaZero E] at hbell0
  rw [hx1val] at hbell1
  have hJ1 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1)
      = mwU_T 1 (E.α 1)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)))) := rfl
  have hJ0 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 0
      = mwU_T 0 0 (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 0
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))) := rfl
  rw [hJ1] at hbell1
  rw [hJ0] at hbell0
  have hF0 : mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 0 _ h0S hs0I
  have hF1 : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S hs1I
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)))
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))))
  rw [Sanctions.clipS'_val_eq_of_mem hF0, Sanctions.clipS'_val_eq_of_mem hF1] at hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope hbell0 hbell1
  unfold mwU_T at hbell0 hbell1
  have heq : (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0))
      * (16/25 - (9/100) *
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))
      = (-(E.α 1)^2 + E.α 1
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            * (1/2 + E.α 1 / 2)
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 2) := by
    linear_combination hbell1 - hbell0 + (9/10) * hslope
  have hstage : 29/84 ≤
      (-(E.α 1)^2 + E.α 1
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            * (1/2 + E.α 1 / 2)
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 2) := by
    have h1 : 0 ≤ E.α 1 * (1 - E.α 1) := mul_nonneg ha1.1 (by linarith [ha1.2])
    have h2 : 0 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
        * E.α 1 := mul_nonneg hs1I.1 ha1.1
    nlinarith [mwTopResponse_ge_29_42 E, hs0I.1]
  have hprod : 0 ≤ (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
      * (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)) :=
    mul_nonneg (sub_nonneg.mpr (mwSigmaMono E)) (mwT_spread_nonneg E)
  linarith [heq, hstage, hprod]

/-! ### §6.  THE WEAK FLOOR AT THE PIVOT `x̄ = s̄ = 1/2`.

For every `x ∈ [1/2, 1]` the equilibrium realized sanction is at least `1/2`.
No `s(x) ≥ x` is used and no upper bound on `α` is assumed: the argument is a
*downward* Target deviation `a ↦ α(x) − 1/300`.  If the realized sanction were
below `1/2`, the Sender vertex would be strictly interior at both actions (so
the response moves with slope `5/12`), and the Target's own optimality then
caps `α(x)` below the level a sub-`1/2` sanction requires.  The margin at
`Δ_S ≥ 11/7`, `Δ_T ≥ 1/2` is `67/2100 > 0`; at the previously available
`Δ_S ≥ 22/15` the same pivot FAILS, which is what the sharpened bound buys. -/
set_option maxHeartbeats 1600000 in
theorem mwWeakFloor_half
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (1/2 : ℝ) 1) :
    (1:ℝ)/2 ≤ mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α x := by
  have hxS : x ∈ Sanctions.S := ⟨by linarith [hx.1], hx.2⟩
  have hax : E.α x ∈ Sanctions.I := E.α_mem x hxS
  have hDge := mwD_ge_eleven_sevenths E
  have hTge := mwT_spread_ge_half E
  have hrule : mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α x
      = max 0 (min 1 (mwSenderVertexOne E.V_S x (E.α x))) :=
    mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α x)
  rw [hrule]
  by_contra hcon
  rw [not_le] at hcon
  have hvpos : 0 < mwSenderVertexOne E.V_S x (E.α x) := by
    unfold mwSenderVertexOne; linarith [hax.2, hx.1]
  have hmin_pos : 0 < min 1 (mwSenderVertexOne E.V_S x (E.α x)) :=
    lt_min (by norm_num) hvpos
  rw [max_eq_right (le_of_lt hmin_pos)] at hcon
  have hvlt : mwSenderVertexOne E.V_S x (E.α x) < 1/2 := by
    rcases min_cases 1 (mwSenderVertexOne E.V_S x (E.α x)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hcon; linarith
    · rw [he] at hcon; exact hcon
  have halpha_lb : (1:ℝ)/300 < E.α x := by
    unfold mwSenderVertexOne at hvlt; linarith [hx.1]
  have ha'I : E.α x - 1/300 ∈ Sanctions.I := ⟨by linarith, by linarith [hax.2]⟩
  have hs_eq : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)
      = mwSenderVertexOne E.V_S x (E.α x) := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α x),
      min_eq_right (by linarith : mwSenderVertexOne E.V_S x (E.α x) ≤ 1),
      max_eq_right (le_of_lt hvpos)]
  have hv' : mwSenderVertexOne E.V_S x (E.α x - 1/300)
      = mwSenderVertexOne E.V_S x (E.α x) + 1/720 := by
    unfold mwSenderVertexOne; ring
  have hs'_eq : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x - 1/300)
      = mwSenderVertexOne E.V_S x (E.α x) + 1/720 := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α x - 1/300), hv',
      min_eq_right (by linarith), max_eq_right (by linarith)]
  have hopt := E.α_opt_shock x hxS ha'I
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x - 1/300) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x) at hopt
  have hJa : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x)
      = mwU_T x (E.α x)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F x
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)))) := rfl
  have hJa' : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x - 1/300)
      = mwU_T x (E.α x - 1/300)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x
            (E.α x - 1/300))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F x
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x
                (E.α x - 1/300)))) := rfl
  rw [hJa, hJa'] at hopt
  have hFs : mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem x _ hxS
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hFs' : mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x - 1/300))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem x _ hxS
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))))
    (Sanctions.clipS' (mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x - 1/300))))
  rw [Sanctions.clipS'_val_eq_of_mem hFs, Sanctions.clipS'_val_eq_of_mem hFs'] at hslope
  rw [hs_eq, hs'_eq] at hopt hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hopt hslope
  unfold mwU_T at hopt
  unfold mwSenderVertexOne at hopt hslope hvlt
  linarith [hopt, hslope, hvlt, hx.1, hDge, hTge]

theorem mwBasinInvariance_half
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ∀ x ∈ Set.Icc (1/2 : ℝ) 1,
      (1:ℝ)/2 ≤ mechanismWitnessParams.F x
        (mechanismWitnessParams.dynamicTopRealizedRule (mwSenderValueOne E.V_S) E.α x) :=
  fun _ hx =>
    (mechanismWitnessParams.weakFloor_dynamicTopStepF_mem_basin
      (mwSenderValueOne E.V_S) E.α
      (mechanismWitnessParams.corner_of_pivot_le_floor (le_refl (1/2 : ℝ)))
      (fun _ hy => mwWeakFloor_half E hy) hx).1

/-- The weak basin at the round pivot, packaged. -/
theorem mwWeakBasin_half_exists
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ∃ xbar sbar : ℝ, xbar < 1 ∧ 0 ≤ xbar ∧ xbar ≤ sbar ∧ sbar ∈ Sanctions.I ∧
      (∀ x ∈ Set.Icc xbar (1:ℝ),
        sbar ≤ mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne E.V_S) E.α x) ∧
      (∀ x ∈ Set.Icc xbar (1:ℝ),
        xbar ≤ mechanismWitnessParams.F x
          (mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne E.V_S) E.α x)) :=
  ⟨1/2, 1/2, by norm_num, by norm_num, le_rfl, ⟨by norm_num, by norm_num⟩,
    fun x hx => mwWeakFloor_half E hx, mwBasinInvariance_half E⟩

/-! ### §7.  SHARPENING.  A LOWER bound on top-state compliance, hence `Δ_S ≥ 17/10`.

The `11/7` bound of §4 is the limit of the identity route when the only
information about `α(1)` is the top-state obstruction `Δ_S < 10·α(1) − 1`
(which is exactly `s(1) < 1`, with no quantitative gap).  An *independent*
lower bound on `α(1)` closes that gap.  It comes from the Target's own
optimality at the top state, tested against an UPWARD deviation
`a ↦ α(1) + 1/100`: raising compliance costs `a² + a` in stage payoff but
buys a `(5/12)`-slope sanction reduction, which at `x = 1` the Target
*dislikes* losing (`∂U_T/∂s = 1/2 + a/2 > 0`), and costs continuation
`(9/100)·(1/240)·Δ_T`.  The only external input is the repo's Target
endpoint cap `Δ_T ≤ 60/11`.

Feeding `α(1) ≥ 15181/58300 + (12/53)·s(1)` back through
`s(1) = 25/24 + Δ_S/24 − (5/12)·α(1)` gives `s(1) ≤ 43523/51040 + (53/1392)·Δ_S`
— a strict gap below `1` — and the reduced identity of §4 then yields
`Δ_S ≥ 17/10`.  (The true value is `≈1.7641`; the exact root of the bounding
quadratic is `≈1.71099`, so `17/10` is the round rational just inside it.) -/

/-- The top-state response written in `mwSenderVertexOne` shape. -/
theorem mwTopVertex_eq
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      = mwSenderVertexOne E.V_S 1 (E.α 1) := by
  rw [mwTopResponse_eq E]; unfold mwSenderVertexOne; ring

set_option maxHeartbeats 1600000 in
/-- **Top-state compliance is bounded BELOW.**  `α(1) ≥ 15181/58300 + (12/53)·s(1)`
(numerically `≥ 0.2604 + 0.2264·s(1) ≈ 0.4672` at the proved `s(1) ≥ 29/42`).
Derived from the Target's argmax against an upward deviation of size `1/100`
plus the repo cap `Δ_T ≤ 60/11`; no new hypothesis. -/
theorem mwAlphaOne_lb
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    15181/58300
        + (12/53) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ≤ E.α 1 := by
  have h1S : (1:ℝ) ∈ Sanctions.S := by norm_num
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs1ge := mwTopResponse_ge_29_42 E
  have hTle := mwShockedOne_target_endpoint_spread_le E
  rcases le_or_gt (99/100 : ℝ) (E.α 1) with hbig | hsmall
  · -- no upward room: compliance is already near the corner, far above the bound
    linarith [hs1I.2]
  -- upward deviation of size `1/100` is feasible
  have ha'I : E.α 1 + 1/100 ∈ Sanctions.I := ⟨by linarith [ha1.1], by linarith⟩
  have hs_eq : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      = mwSenderVertexOne E.V_S 1 (E.α 1) := mwTopVertex_eq E
  have hvge : (29:ℝ)/42 ≤ mwSenderVertexOne E.V_S 1 (E.α 1) := by
    rw [← hs_eq]; exact hs1ge
  have hvle : mwSenderVertexOne E.V_S 1 (E.α 1) ≤ 1 := by
    rw [← hs_eq]; exact hs1I.2
  have hv' : mwSenderVertexOne E.V_S 1 (E.α 1 + 1/100)
      = mwSenderVertexOne E.V_S 1 (E.α 1) - 1/240 := by
    unfold mwSenderVertexOne; ring
  have hs'_eq : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1 + 1/100)
      = mwSenderVertexOne E.V_S 1 (E.α 1) - 1/240 := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S h1S (E.α 1 + 1/100), hv',
      min_eq_right (by linarith), max_eq_right (by linarith)]
  have hopt := E.α_opt_shock 1 h1S ha'I
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1 + 1/100) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1) at hopt
  have hJa : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1)
      = mwU_T 1 (E.α 1)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)))) := rfl
  have hJa' : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1 + 1/100)
      = mwU_T 1 (E.α 1 + 1/100)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1 + 1/100))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1
                (E.α 1 + 1/100)))) := rfl
  rw [hJa, hJa'] at hopt
  have hFs : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hFs' : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1 + 1/100))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))))
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1 + 1/100))))
  rw [Sanctions.clipS'_val_eq_of_mem hFs, Sanctions.clipS'_val_eq_of_mem hFs'] at hslope
  rw [hs_eq, hs'_eq] at hopt hslope
  rw [hs_eq]
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hopt hslope
  unfold mwU_T at hopt
  unfold mwSenderVertexOne at hopt hslope ⊢
  linarith [hopt, hslope, hTle]

set_option maxHeartbeats 1600000 in
/-- **THE SHARPENED LOWER BOUND: `17/10 ≤ Δ_S`.**  Same identity, with the
`α(1)` lower bound of `mwAlphaOne_lb` supplying the quantitative gap
`s(1) ≤ 43523/51040 + (53/1392)·Δ_S < 1`. -/
theorem mwD_ge_seventeen_tenths
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (17:ℝ)/10 ≤ E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) := by
  have hid := mwSenderSpread_reduced_identity E
  have hs1eq := mwTopResponse_eq E
  have halb := mwAlphaOne_lb E
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs0I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hDge := mwD_ge_eleven_sevenths E
  have hDle := mwD_le E
  -- the bottom-state response is tiny
  have hs0le : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ≤ 13 / 384 := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S (by norm_num) (0:ℝ)]
    refine max_le (by norm_num) (le_trans (min_le_right _ _) ?_)
    unfold mwSenderVertexOne; linarith
  -- the α(1) bound gives a STRICT gap for the top response
  have hU : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ≤ 43523/51040
        + (53/1392) * (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) := by
    linarith [halb, hs1eq]
  have hUle : (43523:ℝ)/51040
      + (53/1392) * (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) ≤ 1 := by
    linarith [hDle]
  -- the identity's right-hand side is decreasing in `s(1)` on `[0,1]`
  have hmono : 29/10
        - (12/5) * (43523/51040
            + (53/1392) * (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)))
        + (3/5) * (43523/51040
            + (53/1392) * (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))) ^ 2
      ≤ 29/10
        - (12/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
        + (3/5) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) ^ 2 := by
    nlinarith [hU, hUle, hs1I.1, hs1I.2]
  -- the `s(0)` cross term is negligible
  have hs0D : (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
      * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 20
      ≤ 39/8192 := by
    nlinarith [hDle, hDge, hs0I.1, hs0le]
  nlinarith [hid, hmono, hs0D, hs0I.1, hDge, hDle,
    sq_nonneg (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)]

/-! ### §8.  The α upper bound the floor DELIVERS (task item 3).

With the floor proved, the clipped-vertex selector runs backwards: `s(x) ≥ 1/2`
forces the vertex above `1/2`, which caps `α(x)`.  At the pivot, using the
repo's `Δ_S ≤ 45/16`, this gives `α(1/2) ≤ 37/160 = 0.23125`.

**This is NOT strong enough to re-derive the strong-floor test.**  The test
`x ≤ s(x)` at `x = 1/2` needs `α(1/2) ≤ (2·Δ_S − 1)/20`, i.e. `≤ 3/28 ≈ 0.107`
at `Δ_S = 11/7` (`≤ 0.12` even at `Δ_S = 17/10`).  So the α-upper-bound route
to the floor is genuinely blocked; the downward-deviation route of §6 is what
closes it. -/
theorem mwAlpha_le_at_pivot
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.α (1/2) ≤ 37/160 := by
  have hfloor := mwWeakFloor_half E (x := 1/2) ⟨le_rfl, by norm_num⟩
  have hDle := mwD_le E
  have hxS : (1/2 : ℝ) ∈ Sanctions.S := ⟨by norm_num, by norm_num⟩
  have hrule : mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α (1/2)
      = max 0 (min 1 (mwSenderVertexOne E.V_S (1/2) (E.α (1/2)))) :=
    mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α (1/2))
  rw [hrule] at hfloor
  have hmin : (1:ℝ)/2 ≤ min 1 (mwSenderVertexOne E.V_S (1/2) (E.α (1/2))) := by
    rcases max_cases (0:ℝ) (min 1 (mwSenderVertexOne E.V_S (1/2) (E.α (1/2)))) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hfloor; linarith
    · rw [he] at hfloor; exact hfloor
  have hv : (1:ℝ)/2 ≤ mwSenderVertexOne E.V_S (1/2) (E.α (1/2)) :=
    le_trans hmin (min_le_right _ _)
  unfold mwSenderVertexOne at hv
  linarith

/-- The gap, machine-checked: at `x = 1/2` the *strong* test `x ≤ s(x)` demands
`α(1/2) ≤ (2·Δ_S − 1)/20`, and even at `Δ_S = 17/10` that ceiling `12/100` is
strictly below the `37/160` that the weak floor delivers.  So no amount of
bookkeeping turns the §8 bound into the strong floor. -/
theorem pivot_alpha_ceiling_gap : (2 * (17/10 : ℝ) - 1)/20 < 37/160 := by norm_num

/-! ### §9.  THE PARAMETRIC WEAK-FLOOR FAMILY (Rule 5).

With `Δ_S ≥ 17/10` and `Δ_T ≥ 1/2` in hand, the downward-deviation argument of
§6 runs at EVERY admissible `(x̄, s̄)` pair, and the admissibility condition is a
single explicit rational inequality:

        `41760 · s̄  <  31530 · x̄ + 5329`,     with `2/5 ≤ x̄ ≤ 1`.

`x̄ ≥ 2/5` is what keeps the Sender vertex strictly positive at the worst
feasible compliance `α = 1`; the displayed inequality is the deviation margin.
(`s̄ ≤ 1` is NOT a hypothesis — it follows from the displayed inequality.)
The two named pivots are one-line corollaries:

  `(x̄, s̄) = (1/2, 1/2)`   → `20880 < 21094`   (margin `214`)
  `(x̄, s̄) = (2/5, 5/12)`  → `17400 < 17941`   (margin `541`)

The frontier is a genuine trade-off, not a single best point: a *lower* `x̄`
means a *larger* invariant basin but forces a *lower* floor `s̄`.  At `x̄ = 1/2`
the largest provable floor is `s̄ < 0.50513…`; at `x̄ = 2/5` it is
`s̄ < 0.42962…`.  Every pair also needs `x̄ ≤ s̄` for forward invariance. -/
set_option maxHeartbeats 1600000 in
theorem mwWeakFloor_param
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {xbar sbar : ℝ} (hxbar : 2/5 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hcond : 41760 * sbar < 31530 * xbar + 5329)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    sbar ≤ mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α x := by
  have hxS : x ∈ Sanctions.S := ⟨by linarith [hx.1], hx.2⟩
  have hax : E.α x ∈ Sanctions.I := E.α_mem x hxS
  have hDge := mwD_ge_seventeen_tenths E
  have hTge := mwT_spread_ge_half E
  have hrule : mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α x
      = max 0 (min 1 (mwSenderVertexOne E.V_S x (E.α x))) :=
    mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α x)
  rw [hrule]
  by_contra hcon
  rw [not_le] at hcon
  have hvpos : 0 < mwSenderVertexOne E.V_S x (E.α x) := by
    unfold mwSenderVertexOne; linarith [hax.2, hx.1]
  have hmin_pos : 0 < min 1 (mwSenderVertexOne E.V_S x (E.α x)) :=
    lt_min (by norm_num) hvpos
  rw [max_eq_right (le_of_lt hmin_pos)] at hcon
  have hvlt : mwSenderVertexOne E.V_S x (E.α x) < sbar := by
    rcases min_cases 1 (mwSenderVertexOne E.V_S x (E.α x)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hcon; linarith
    · rw [he] at hcon; exact hcon
  have halpha_lb : (1:ℝ)/300 < E.α x := by
    unfold mwSenderVertexOne at hvlt; linarith [hx.1]
  have ha'I : E.α x - 1/300 ∈ Sanctions.I := ⟨by linarith, by linarith [hax.2]⟩
  have hs_eq : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)
      = mwSenderVertexOne E.V_S x (E.α x) := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α x),
      min_eq_right (by linarith : mwSenderVertexOne E.V_S x (E.α x) ≤ 1),
      max_eq_right (le_of_lt hvpos)]
  have hv' : mwSenderVertexOne E.V_S x (E.α x - 1/300)
      = mwSenderVertexOne E.V_S x (E.α x) + 1/720 := by
    unfold mwSenderVertexOne; ring
  have hs'_eq : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x - 1/300)
      = mwSenderVertexOne E.V_S x (E.α x) + 1/720 := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S hxS (E.α x - 1/300), hv',
      min_eq_right (by linarith), max_eq_right (by linarith)]
  have hopt := E.α_opt_shock x hxS ha'I
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x - 1/300) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x) at hopt
  have hJa : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x)
      = mwU_T x (E.α x)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F x
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)))) := rfl
  have hJa' : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x - 1/300)
      = mwU_T x (E.α x - 1/300)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x
            (E.α x - 1/300))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F x
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x
                (E.α x - 1/300)))) := rfl
  rw [hJa, hJa'] at hopt
  have hFs : mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem x _ hxS
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hFs' : mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x - 1/300))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem x _ hxS
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))))
    (Sanctions.clipS' (mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x - 1/300))))
  rw [Sanctions.clipS'_val_eq_of_mem hFs, Sanctions.clipS'_val_eq_of_mem hFs'] at hslope
  rw [hs_eq, hs'_eq] at hopt hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hopt hslope
  unfold mwU_T at hopt
  unfold mwSenderVertexOne at hopt hslope hvlt
  linarith [hopt, hslope, hvlt, hx.1, hDge, hTge, hcond, hxbar]

/-- The `(2/5, 5/12)` pivot — larger basin, lower floor. -/
theorem mwWeakFloor_two_fifths
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ∀ x ∈ Set.Icc (2/5 : ℝ) 1,
      (5:ℝ)/12 ≤ mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne E.V_S) E.α x :=
  fun _ hx => mwWeakFloor_param E le_rfl (by norm_num) (by norm_num) hx

/-- The `(1/2, 1/2)` pivot, via the parametric family (independently proved in
§6 from the weaker `11/7`). -/
theorem mwWeakFloor_half' (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ∀ x ∈ Set.Icc (1/2 : ℝ) 1,
      (1:ℝ)/2 ≤ mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne E.V_S) E.α x :=
  fun _ hx => mwWeakFloor_param E (by norm_num) (by norm_num) (by norm_num) hx

/-- Basin invariance at `(2/5, 5/12)`: `2/5 ≤ 5/12` closes the corner. -/
theorem mwBasinInvariance_two_fifths
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ∀ x ∈ Set.Icc (2/5 : ℝ) 1,
      (2:ℝ)/5 ≤ mechanismWitnessParams.F x
        (mechanismWitnessParams.dynamicTopRealizedRule (mwSenderValueOne E.V_S) E.α x) :=
  fun x hx =>
    (mechanismWitnessParams.weakFloor_dynamicTopStepF_mem_basin
      (mwSenderValueOne E.V_S) E.α
      (mechanismWitnessParams.corner_of_pivot_le_floor
        (by norm_num : (2/5 : ℝ) ≤ 5/12))
      (fun y hy => mwWeakFloor_two_fifths E y hy) hx).1


/-! ### §10.  RULE-11 CHECKS: non-vacuity, and an INDEPENDENT cross-validation.

The repo's explicitly constructed equilibrium `mwEqEquilibrium`
(`MechanismWitnessShockedUnconditional.lean:988`) inhabits the type, so none of
the bounds above is vacuous.  More usefully, that equilibrium's endpoint spread
is pinned *independently* — by an intermediate-value argument on the quartic
`mwEqQuartic`, with no reference to any of the machinery here —
to `mwEqSenderSpread ∈ [441/250, 17641/10000]`.

That is a genuine falsification test for the analytic route: had the derivation
above produced anything above `17641/10000 = 1.7641`, the two would be
inconsistent and one of them would be wrong.  They agree:
`17/10 = 1.700 ≤ 441/250 = 1.764`.  Both the general bound and the pin are
derived here for the same object and the ordering is machine-checked. -/

theorem mwD_ge_nonvacuous :
    (17:ℝ)/10 ≤ mwEqEquilibrium.V_S (Sanctions.clipS' 1)
      - mwEqEquilibrium.V_S (Sanctions.clipS' 0) :=
  mwD_ge_seventeen_tenths mwEqEquilibrium

/-- The same object's spread, from the *independent* IVT pin. -/
theorem mwD_pin_at_constructed :
    (441:ℝ)/250 ≤ mwEqEquilibrium.V_S (Sanctions.clipS' 1)
      - mwEqEquilibrium.V_S (Sanctions.clipS' 0)
    ∧ mwEqEquilibrium.V_S (Sanctions.clipS' 1)
      - mwEqEquilibrium.V_S (Sanctions.clipS' 0) ≤ 17641/10000 := by
  have h : mwEqEquilibrium.V_S (Sanctions.clipS' 1)
      - mwEqEquilibrium.V_S (Sanctions.clipS' 0) = mwEqSenderSpread :=
    mwEqSenderValue_endpoint_spread
  rw [h]
  exact mwEqSenderSpread_bounds

/-- **The two derivations are consistent** — the general analytic bound does not
overshoot the independent pin. -/
theorem p3WeakFloor_bound_below_pin : (17:ℝ)/10 ≤ 441/250 := by norm_num

/-- The sharpened bound strictly improves on both previously available bounds:
`11/7` (§4 here) and `22/15` (the earlier route). -/
theorem p3WeakFloor_bound_strictly_improves :
    (22:ℝ)/15 < 11/7 ∧ (11:ℝ)/7 < 17/10 := by constructor <;> norm_num

/-- Top-state compliance is bounded below by `5/12` — the quantitative content
that the earlier `Δ_S < 10·α(1) − 1` obstruction alone could not deliver. -/
theorem mwAlphaOne_ge_5_12
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (5:ℝ)/12 ≤ E.α 1 := by
  have h := mwAlphaOne_lb E
  have hs := mwTopResponse_ge_29_42 E
  linarith

/-- Non-vacuity of the weak basin at the round pivot. -/
theorem mwWeakBasin_half_inhabited :
    ∃ E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
        (1:ℝ)/2 ≤ mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne E.V_S) E.α x)
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
        (1:ℝ)/2 ≤ mechanismWitnessParams.F x
          (mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne E.V_S) E.α x)) :=
  ⟨mwEqEquilibrium, fun x hx => mwWeakFloor_half mwEqEquilibrium hx,
    mwBasinInvariance_half mwEqEquilibrium⟩

/-! ### Rule-10 axiom hygiene. -/
#print axioms mwD_le
#print axioms mwT_spread_nonneg
#print axioms mwAlphaZero
#print axioms spread_lower_arith
#print axioms mwSenderSpread_raw_identity
#print axioms mwSenderSpread_stage_ge
#print axioms mwD_pos
#print axioms mwTopResponse_eq
#print axioms mwSenderSpread_reduced_identity
#print axioms mwD_ge_eleven_sevenths
#print axioms mwSigmaMono
#print axioms mwTopResponse_ge_29_42
#print axioms mwT_spread_ge_half
#print axioms mwWeakFloor_half
#print axioms mwBasinInvariance_half
#print axioms mwWeakBasin_half_exists
#print axioms mwTopVertex_eq
#print axioms mwAlphaOne_lb
#print axioms mwD_ge_seventeen_tenths
#print axioms mwAlpha_le_at_pivot
#print axioms pivot_alpha_ceiling_gap
#print axioms mwWeakFloor_param
#print axioms mwWeakFloor_two_fifths
#print axioms mwWeakFloor_half'
#print axioms mwBasinInvariance_two_fifths
#print axioms mwD_ge_nonvacuous
#print axioms mwD_pin_at_constructed
#print axioms p3WeakFloor_bound_below_pin
#print axioms p3WeakFloor_bound_strictly_improves
#print axioms mwAlphaOne_ge_5_12
#print axioms mwWeakBasin_half_inhabited

end P3WeakFloor
end Examples
end Sanctions
