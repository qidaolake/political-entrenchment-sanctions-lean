/-
Sanctions/Theory/Bridges/JETBridge.lean

**JET bridge: clean composition theorems chaining the existence,
high-basin, and lock-in / dominance layers.**

This file contains *no new hypotheses* relative to the existing
theorems. Every input is an existing theorem-parameter primitive
threaded through a composition of already-proved theorems:

* **Existence**: `ValueClass2.exists_feedbackStackelbergTop_of_jointFixedPoint`
  (`InvariantValueClass2`; the single-carrier `exists_feedbackStackelbergTop_from_valueClass`
  cited here before 2026-10-06 was a dead wrapper and was removed in renovation round BG-1).
* **High-basin discharge from primitive lower slopes**:
  `OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes`
  (`PrimitiveHighBasin`).
* **Single-crossing → monotone realized rule**:
  `dynamicTopRealizedRule_mono_of_singleCrossingOn`
  (`JointPreferenceBasin`).
* **Persistence (Goal 1)**:
  `equilibriumTop_oneSidedThresholds_long_run_nonDecreasing`
  (`JointPreferenceBasin`).
* **Temporary shock → permanent high (Goal 3)**:
  `equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high`
  (`JointPreferenceBasin`).
* **Different-α dynamic ≥ myopic (Goal 2) on basin**:
  `dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin`
  + `dynamicTop_rule_dominates_myopic_policy_from_primitives`
  (`DifferentPolicyComparator`).

The bridge theorems below are **pure composition wrappers** — they
introduce no new `Params` fields, no new `Prop`s, and no new
theorem-parameter primitives beyond what the underlying theorems
already consume. Per Rule 3, the assumption surface is unchanged.

## Rule compliance

**Rule 1.** All players' strategies are equilibrium-derived: the
Stackelberg leader α is the joint Bellman argmax via `α_on`
(carrier-restricted `targetArgmax`); the Sender response is the
forward-looking dynamic argmax `σ_dyn` / `σ_dyn_top`; the value
functions are Banach fixed points of the joint operator pair.
The myopic comparator's `M.α` is *independently* the stage Bellman
argmax (`MyopicFeedbackEquilibrium.α_opt`).

**Rule 2.** Lean-first composition. Paper updates against these
bridge theorems are a separate downstream item, *not* in scope here.

**Rule 3.** Zero new fields, no new load-bearing `Prop`s, no new
theorem-parameter primitives. Every hypothesis the bridge takes is
already consumed by one of the chained theorems.

**Rule 5.** Fully parametric over `(p, D, E, M)` and the primitive
constants. No witness specialization.
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Bellman.InvariantBall
import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Bellman.LipschitzPrimitives
import Sanctions.Theory.Bellman.OperatorRowLipschitz
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Bellman.ValueLipschitz
import Sanctions.Theory.Bellman.C1Val
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.Certificates.StandardComplianceBridges
import Mathlib.Analysis.Calculus.MeanValue

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Persistence (Goal 1) at the upper-selector equilibrium
from primitive lower slopes + single-crossing -/


/-- **Goal 2 (different-α dynamic ≥ myopic) composition from
primitive α-ordering and σ-monotonicity.** Composes:

* `dynamicTop_rule_dominates_myopic_policy_from_primitives` to
  discharge the cross-policy rule dominance from primitive
  α-ordering + σ-monotonicity in `a` + monotone `V_S`.
* `dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin`
  for the headline localized basin dominance.

The basin invariance hypotheses for both rules are kept as bridge
inputs since they depend on the specific equilibrium `E` and
comparator `M` (no generic discharger for them).

**⚠ AUDIT-48 LITERAL-COMPLIANCE DEPRECATION.** This Goal-2 bridge
uses `hα_order` (M.α ≤ E.α) and `hσ_monoOn_a` (`σ` monotone in `a`),
both sign-correct only under the resistance/noncompliance reading
of `a`. The audit-41 replacement is
`jet_dominance_at_equilibriumTop_audit41`, which takes
`hRuleDom_on_basin` directly. For literal compliance, prefer the
audit-46 floor/ceiling discharger via
`ruleDom_of_dynamic_floor_and_myopic_ceiling` or the canonical
route through the carrier-local
`StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts`. -/
theorem jet_dominance_at_equilibriumTop_from_static_order
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hα_order : ∀ x ∈ Sanctions.S, M.α x ≤ E.α x)
    (hσ_monoOn_a : ∀ x ∈ Sanctions.S,
      MonotoneOn (fun a => p.σ x a) Sanctions.I)
    {xbar x₀ : ℝ}
    -- Weakened 2026-09-01 (Rule 13.2, Q6 audit): was `xbar ∈ Sanctions.I`,
    -- a two-sided membership, but the proof consumes only the lower bound
    -- (to place `[xbar,1] ⊆ S`). The upper bound `xbar ≤ 1` was never used.
    (hxbar_nn : 0 ≤ xbar)
    (hMyo_basin :
      ∀ x ∈ Set.Icc xbar 1, p.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hDyn_basin :
      ∀ x ∈ Set.Icc xbar 1,
        p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc xbar 1)
    (hDynMonoOn :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc xbar 1))
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      p.ruleSanctions (fun x => p.σ x (M.α x)) x₀ n
        ≤
      p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  -- Discharge the cross-policy rule dominance via the primitive
  -- discharger; restrict from Sanctions.S to the basin.
  have h_dom_on_S :
      ∀ x ∈ Sanctions.S,
        p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    p.dynamicTop_rule_dominates_myopic_policy_from_primitives
      E M hV_S_mono hα_order hσ_monoOn_a
  have hRuleDom_on_basin :
      ∀ x ∈ Set.Icc xbar 1,
        p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
    intro x hx
    -- [xbar, 1] ⊆ I = S since 0 ≤ xbar ≤ x and x ≤ 1.
    have hxS : x ∈ Sanctions.S := by
      refine ⟨?_, hx.2⟩
      exact le_trans hxbar_nn hx.1
    exact h_dom_on_S x hxS
  exact p.dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin
    E M hMyo_basin hDyn_basin hDynMonoOn hRuleDom_on_basin hx₀

/-- **Audit-41 sign-corrected Goal-2 bridge.** Takes the
rule-dominance hypothesis `hRuleDom_on_basin` **directly** rather
than discharging it from the wrong-sign chain
`hα_order + hσ_monoOn_a`. The expected paper-facing route to
discharge `hRuleDom_on_basin` is the floor/ceiling discharger
`ruleDom_of_dynamic_floor_and_myopic_ceiling` in
`DifferentPolicyComparator.lean`. -/
theorem jet_dominance_at_equilibriumTop_audit41
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {xbar x₀ : ℝ}
    (hMyo_basin :
      ∀ x ∈ Set.Icc xbar 1, p.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hDyn_basin :
      ∀ x ∈ Set.Icc xbar 1,
        p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc xbar 1)
    (hDynMonoOn :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc xbar 1))
    (hRuleDom_on_basin :
      ∀ x ∈ Set.Icc xbar 1,
        p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      p.ruleSanctions (fun x => p.σ x (M.α x)) x₀ n
        ≤
      p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) x₀ n :=
  p.dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin
    E M hMyo_basin hDyn_basin hDynMonoOn hRuleDom_on_basin hx₀

/-! ## 3b. Audit-43 sign-correct persistence/shock bridges
(loss-offset Target route)

The §1-§2 persistence/shock bridges use `LowerSlopeOn` on the Target
stage payoff with positive `mT`, which requires `U_T` to be locally
*non-decreasing* in `s` on the high range — backwards under literal
compliance + standard sanctions (`U_T_s < 0`).

The audit-43 compliance route below uses the Phase-5/Item-1
discharger
`OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target`
instead: the Target stage payoff may decrease in `s` with bounded
rate `c`, offset by the continuation value gain `g · δ` (margin
`c ≤ β_T · g · δ`). Sender side unchanged.

These are the sign-correct paper-facing persistence and shock bridges
under literal compliance. -/


/-- **Bounded C¹ derivative ⇒ value Lipschitz on `↥S`.** For any
`V : C1Val K_d`, the underlying BCF value `V.V` is
`K_d`-Lipschitz on the unit interval (`Sanctions.S = [0, 1]`).

Proof: apply mathlib's `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`
to the canonical extension `bcfExtendToR V.V : ℝ → ℝ`, using the
within-set derivative `V.V'` and the uniform bound `|V.V' x| ≤ K_d` on
`Sanctions.S`. -/
theorem C1Val.valueLipschitzWith {K_d : ℝ} (V : C1Val K_d) :
    ValueLipschitzWith V.V K_d := by
  intro y₁ y₂
  -- bcfExtendToR V.V agrees with V.V on ↥S.
  have h_coe₁ : bcfExtendToR V.V y₁.val = V.V y₁ :=
    bcfExtendToR_coe V.V y₁
  have h_coe₂ : bcfExtendToR V.V y₂.val = V.V y₂ :=
    bcfExtendToR_coe V.V y₂
  -- HasDerivOnS gives the within-set derivative everywhere on S.
  have h_deriv : ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR V.V) (V.V' x) Sanctions.S x :=
    V.hasDeriv.hasDerivOnS
  -- Bound on |V.V' x| over S.
  have h_bound : ∀ x ∈ Sanctions.S, ‖V.V' x‖ ≤ K_d := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact V.hasDeriv.bound x hx
  -- S = [0, 1] is convex.
  have h_convex : Convex ℝ (Sanctions.S : Set ℝ) := convex_Icc 0 1
  -- Apply mathlib's mean-value Lipschitz lemma.
  have h_mvt :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_deriv h_bound h_convex y₁.property y₂.property
  -- h_mvt : ‖bcfExtendToR V.V y₂.val - bcfExtendToR V.V y₁.val‖ ≤ K_d · ‖y₂.val - y₁.val‖
  rw [h_coe₁, h_coe₂, Real.norm_eq_abs] at h_mvt
  -- Subtype distance: dist y₁ y₂ = |y₂.val - y₁.val| up to symmetry.
  have h_subtype_dist : dist y₁ y₂ = |y₂.val - y₁.val| := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
  rw [h_subtype_dist]
  exact_mod_cast h_mvt

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
