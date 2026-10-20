/-
Sanctions/Theory/Shocked/ShockedDominance.lean

**Step 5 (Goal-2, full): shocked dynamic-over-myopic Sender dominance.**

The forward-looking (shocked) Sender's realized sanction path pointwise dominates the
myopic Sender's, on the high political basin. This completes Goal-2 under the atomless
shock: it is no longer only the monotonicity of the dynamic rule (the Goal-2 *core*,
`dynamicTopRealizedRule_shock_monotoneOn_of_strong_rally`) but the pathwise comparison
of the two realized sanction sequences.

The assembly is sign-clean under literal compliance (`a=1` full compliance): the rule
dominance is `le_trans` of the myopic ceiling and the dynamic floor — it carries **no**
"`σ` monotone in the leader action" hypothesis, which is the source of the audit-41
sign error. The myopic side is **shock-invariant**: the myopic equilibrium optimizes
the pure stage payoff (`β=0`), so the smear never touches it. The dynamic side enters
only through `sp.smear V_S`, and its monotonicity is the already-proved shocked Goal-2
core. The whole thing routes through the bare two-rule comparator
`ruleSanctions_le_of_rule_le_and_upper_monoOn_basin` (generic over the lower/upper
rule), so no equilibrium wrapper is forced on the smeared continuation.

The general-`F` section below adds equilibrium-packaged weak and strict
siblings using `ruleSanctionsF`.  Their dynamic policy comes from an actual
`ShockedFeedbackStackelbergEquilibriumTop`; optional IDO wrappers derive the
needed rule monotonicity only after substituting that realized Target policy.
Like the affine wrapper, they take no sign condition on the basin floor: the
`0 ≤ xbar` they used to pass through to the general-`F` comparator was
dropped there on 2026-10-06 (BG2.1), and so was dropped here.

**Rule 1 / Rule 3.** Both `α` (the leader policy) and the continuation `V_S` are
equilibrium objects; the myopic comparator `M.α` is the stage best response. No new
assumption: the floor, ceiling, and myopic-basin inputs are the existing regime
conditions discharged for the deterministic certificate, carried across the smear by
the same `K_S, m_S` (the smear preserves the Lipschitz constant); a new theorem over
the existing surface is not a Rule-3 stop.
-/

import Sanctions.Theory.Shocked.ShockedSingleCrossing
import Sanctions.Theory.Shocked.ShockedEquilibrium
import Sanctions.Theory.LockIn.DifferentPolicyComparator

namespace Sanctions
namespace AbstractGame
namespace ShockedParams

open BoundedContinuousFunction Set

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Shocked dynamic-over-myopic Sender dominance on the basin (Goal-2, pathwise).**
For every period `n`, the realized sanction of the shocked forward-looking Sender
(greatest dynamic best response at the smeared continuation `sp.smear V_S` under leader
policy `α`) is at least that of the myopic Sender (stage best response under `M.α`),
along the basin trajectory from any basin start `x₀`.

Inputs, all honest regime conditions: the dynamic rule is monotone on the basin
(`hDynMonoOn`, discharged by the proved
`dynamicTopRealizedRule_shock_monotoneOn_of_strong_rally`); the myopic rule stays in
the basin (`hMyo_basin`, shock-invariant); the dynamic rule sits at/above the corner
`max x sbar` (`hDynFloor`); the myopic rule sits below it (`hMyoCeiling`). The rule
dominance is then `le_trans hMyoCeiling hDynFloor` — sign-clean. -/
theorem shocked_dynamicTopSanctions_ge_myopic_on_basin
    {V_S : SBCF} {α : ℝ → ℝ} {M : sp.toParams.MyopicFeedbackEquilibrium}
    {xbar sbar x₀ : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1, sp.toParams.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hDynMonoOn : MonotoneOn (sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α)
      (Set.Icc xbar 1))
    (hDynFloor : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤ sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α x)
    (hMyoCeiling : ∀ x ∈ Set.Icc xbar 1, sp.toParams.σ x (M.α x) ≤ max x sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, sp.toParams.ruleSanctions (fun x => sp.toParams.σ x (M.α x)) x₀ n
       ≤ sp.toParams.ruleSanctions
           (sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α) x₀ n := by
  -- Rule dominance: myopic ≤ corner ≤ dynamic (sign-clean transitivity).
  have hRuleDom : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ≤ sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α x :=
    fun x hx => le_trans (hMyoCeiling x hx) (hDynFloor x hx)
  -- Dynamic rule stays in the basin: floor gives ≥ xbar, σ_dyn_top ∈ I gives ≤ 1.
  have hDynBasin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α x ∈ Set.Icc xbar 1 := by
    intro x hx
    refine ⟨le_trans (le_trans hx.1 (le_max_left x sbar)) (hDynFloor x hx), ?_⟩
    exact (sp.toParams.σ_dyn_top_mem_I (sp.smear V_S) x (α x)).2
  exact sp.toParams.ruleSanctions_le_of_rule_le_and_upper_monoOn_basin
    hMyo_basin hDynBasin hDynMonoOn hRuleDom hx₀

/-- **Equilibrium-packaged general-`F` shocked dominance.**
For a genuine shocked feedback-Stackelberg equilibrium and an independently
optimal myopic feedback equilibrium, the shocked dynamic sanction sequence
weakly dominates the myopic sequence in every period.  Unlike the affine
wrapper above, the state path is generated by the maintained transition
`F(x,s)`.  General in `F`.  No `0 ≤ xbar`: it was only passed through to
`ruleSanctionsF_le_of_rule_le_and_upper_monoOn_basin`, which no longer
needs it (BG2.1). -/
theorem shockedFeedbackStackelbergTop_sanctionsF_ge_myopic_on_basin
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (M : sp.toParams.MyopicFeedbackEquilibrium)
    {xbar sbar x₀ : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hDynMonoOn : MonotoneOn
      (sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α)
      (Set.Icc xbar 1))
    (hDynFloor : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤
        sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x)
    (hMyoCeiling : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ≤ max x sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      sp.toParams.ruleSanctionsF (fun x => sp.toParams.σ x (M.α x)) x₀ n
        ≤ sp.toParams.ruleSanctionsF
          (sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α) x₀ n := by
  have hRuleDom : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ≤
        sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x :=
    fun x hx => le_trans (hMyoCeiling x hx) (hDynFloor x hx)
  have hDynBasin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x
        ∈ Set.Icc xbar 1 := by
    intro x hx
    refine ⟨le_trans (le_trans hx.1 (le_max_left x sbar))
      (hDynFloor x hx), ?_⟩
    exact (sp.toParams.σ_dyn_top_mem_I (sp.smear E.V_S) x (E.α x)).2
  exact sp.toParams.ruleSanctionsF_le_of_rule_le_and_upper_monoOn_basin
    hMyo_basin hDynBasin hDynMonoOn hRuleDom hx₀

/-- **Strict equilibrium-packaged general-`F` comparison.**
If the independently optimal myopic rule lies strictly below the regime
threshold while the shocked dynamic equilibrium rule lies weakly above it,
then the dynamic equilibrium realizes strictly higher sanctions in every
period, even though the two endogenous state paths generally differ.
General in `F`; no `0 ≤ xbar` (a pass-through, dropped in BG2.1). -/
theorem shockedFeedbackStackelbergTop_sanctionsF_gt_myopic_on_basin
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (M : sp.toParams.MyopicFeedbackEquilibrium)
    {xbar sbar x₀ : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hDynMonoOn : MonotoneOn
      (sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α)
      (Set.Icc xbar 1))
    (hDynFloor : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤
        sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x)
    (hMyoCeiling : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) < max x sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      sp.toParams.ruleSanctionsF (fun x => sp.toParams.σ x (M.α x)) x₀ n
        < sp.toParams.ruleSanctionsF
          (sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α) x₀ n := by
  have hRuleDom : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) <
        sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x :=
    fun x hx => lt_of_lt_of_le (hMyoCeiling x hx) (hDynFloor x hx)
  have hDynBasin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x
        ∈ Set.Icc xbar 1 := by
    intro x hx
    refine ⟨le_trans (le_trans hx.1 (le_max_left x sbar))
      (hDynFloor x hx), ?_⟩
    exact (sp.toParams.σ_dyn_top_mem_I (sp.smear E.V_S) x (E.α x)).2
  exact sp.toParams.ruleSanctionsF_lt_of_rule_lt_and_upper_monoOn_basin
    hMyo_basin hDynBasin hDynMonoOn hRuleDom hx₀

/-- IDO discharger for the weak equilibrium-packaged general-`F`
comparison.  Interval dominance is imposed only after substituting the
realized Target equilibrium policy and is used solely to derive monotonicity
of the Sender's upper dynamic argmax rule.  General in `F`; no `0 ≤ xbar`
(a pass-through, dropped in BG2.1). -/
theorem shockedFeedbackStackelbergTop_sanctionsF_ge_myopic_on_basin_of_IDO
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (M : sp.toParams.MyopicFeedbackEquilibrium)
    {xbar sbar x₀ : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
      Sanctions.I (Set.Icc xbar 1)
      (fun s x => sp.toParams.senderDynObjective
        (sp.smear E.V_S) x (E.α x) s))
    (hDynFloor : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤
        sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x)
    (hMyoCeiling : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ≤ max x sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      sp.toParams.ruleSanctionsF (fun x => sp.toParams.σ x (M.α x)) x₀ n
        ≤ sp.toParams.ruleSanctionsF
          (sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α) x₀ n := by
  exact sp.shockedFeedbackStackelbergTop_sanctionsF_ge_myopic_on_basin
    E M hMyo_basin
    (sp.toParams.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO)
    hDynFloor hMyoCeiling hx₀

/-- Strict general-`F` equilibrium comparison obtained from substituted-policy
interval dominance and a strict myopic ceiling.  General in `F`; no
`0 ≤ xbar` (a pass-through, dropped in BG2.1). -/
theorem shockedFeedbackStackelbergTop_sanctionsF_gt_myopic_on_basin_of_IDO
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (M : sp.toParams.MyopicFeedbackEquilibrium)
    {xbar sbar x₀ : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
      Sanctions.I (Set.Icc xbar 1)
      (fun s x => sp.toParams.senderDynObjective
        (sp.smear E.V_S) x (E.α x) s))
    (hDynFloor : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤
        sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α x)
    (hMyoCeiling : ∀ x ∈ Set.Icc xbar 1,
      sp.toParams.σ x (M.α x) < max x sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      sp.toParams.ruleSanctionsF (fun x => sp.toParams.σ x (M.α x)) x₀ n
        < sp.toParams.ruleSanctionsF
          (sp.toParams.dynamicTopRealizedRule (sp.smear E.V_S) E.α) x₀ n := by
  exact sp.shockedFeedbackStackelbergTop_sanctionsF_gt_myopic_on_basin
    E M hMyo_basin
    (sp.toParams.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO)
    hDynFloor hMyoCeiling hx₀

end ShockedParams
end AbstractGame
end Sanctions
