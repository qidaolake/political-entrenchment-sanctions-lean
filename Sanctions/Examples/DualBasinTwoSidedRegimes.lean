/-
Sanctions/Examples/DualBasinTwoSidedRegimes.lean

**One equilibrium, both regimes, both imposed episodes** — the two-threshold
general-`F` composition of `ReliefPersistence.lean` discharged at the
dual-basin economy `dualParams` (Rule 9: an existence certificate).

At `dualParams` the certified equilibrium's realised rule is `1` on the high
basin `[19/20, 1]` and `0` on the low basin `[0, 1/10]`
(`dbCert_highBasin_rule_eq_one`, `dbCert_lowBasin_rule_eq_zero`), which are
exactly the two level conditions with `s̄_hi = 1`, `s̄_low = 0`. With its strict
adjustment (`dbParams_strictAdjustment`) this gives, at one equilibrium and
from every feasible start:

* a full-sanction episode of length `fullShockEntryHorizon (19/20)` is followed
  by permanent residence in `[19/20, 1]`, with the sanction at `1` at every
  later date;
* a zero-sanction episode of length `fullReliefExitHorizon (1/10)` is followed
  by permanent residence in `[0, 1/10]`, with the sanction at `0` at every
  later date.

This closes, at one affine economy, the item the ceiling listed as
"one-equilibrium two-sided hysteresis": it is now witnessed. What it does
not show: that the two basins exhaust the state space (they do not — the
interval `(1/10, 19/20)` is between them), that the transition is non-affine
here (it is `(9x + s)/10`), or anything about other economies. The general
theorem is `two_sided_regimes_generalF_of_thresholds`; this file only inhabits
its hypotheses.
-/
import Sanctions.Examples.DualBasinSelectionWitness
import Sanctions.Theory.LockIn.ReliefPersistence
import Sanctions.Theory.LockIn.FiniteEpisodePersistence

namespace Sanctions
namespace Examples

open Set AbstractGame

/-- The dual-basin equilibrium with both level conditions in the exact form the
two-threshold theorem consumes. -/
theorem dualParams_exists_equilibrium_two_levels :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Set.Icc (19/20 : ℝ) 1,
        max x (1 : ℝ) ≤ dualParams.dynamicTopRealizedRule E.V_S E.α x) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1/10),
        dualParams.dynamicTopRealizedRule E.V_S E.α x ≤ min x (0 : ℝ)) := by
  obtain ⟨E, hVT, hVS, -, -, -⟩ := dbCert_three_goals_high
  refine ⟨E, fun x hx => ?_, fun x hx => ?_⟩
  · rw [dbCert_highBasin_rule_eq_one E hVT hVS hx]
    exact max_le hx.2 le_rfl
  · rw [dbCert_lowBasin_rule_eq_zero E hVS hx]
    exact le_min hx.1 le_rfl

/-- **Both regimes at one equilibrium, reached by imposed episodes in either
direction.** -/
theorem dualParams_two_sided_regimes :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
        (∀ n, dualParams.dynamicTopLockInPathF E.V_S E.α
            (dualParams.shockPathF x₀ (dualParams.fullShockEntryHorizon (19/20))) n
              ∈ Set.Icc (19/20 : ℝ) 1) ∧
        (∀ n, dualParams.dynamicTopLockInPathF E.V_S E.α
            (dualParams.reliefPathF x₀ (dualParams.fullReliefExitHorizon (1/10))) n
              ∈ Set.Icc (0 : ℝ) (1/10)) := by
  obtain ⟨E, hhi, hlo⟩ := dualParams_exists_equilibrium_two_levels
  exact ⟨E, fun x₀ hx₀ =>
    dualParams.two_sided_regimes_generalF_of_thresholds dbParams_strictAdjustment E.V_S E.α
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ hhi hlo hx₀⟩

/-- **The sanctions after each episode**, through the finite-episode splice:
after a full-sanction episode of at least the canonical length the resumed
equilibrium sanction is `1` at every later date; after a zero-sanction episode
of at least the canonical length it is `0`. -/
theorem dualParams_two_sided_episode_sanctions :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
        (∀ T, dualParams.fullShockEntryHorizon (19/20) ≤ T →
          ∀ n, dualParams.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n) = 1) ∧
        (∀ T, dualParams.fullReliefExitHorizon (1/10) ≤ T →
          ∀ n, dualParams.splicedSanction E.V_S E.α (fun _ => 0) T x₀ (T + n) = 0) := by
  obtain ⟨E, hVT, hVS, -, -, -⟩ := dbCert_three_goals_high
  have hhi : ∀ x ∈ Set.Icc (19/20 : ℝ) 1,
      max x (1 : ℝ) ≤ dualParams.dynamicTopRealizedRule E.V_S E.α x := by
    intro x hx
    rw [dbCert_highBasin_rule_eq_one E hVT hVS hx]
    exact max_le hx.2 le_rfl
  have hlo : ∀ x ∈ Set.Icc (0 : ℝ) (1/10),
      dualParams.dynamicTopRealizedRule E.V_S E.α x ≤ min x (0 : ℝ) := by
    intro x hx
    rw [dbCert_lowBasin_rule_eq_zero E hVS hx]
    exact le_min hx.1 le_rfl
  refine ⟨E, fun x₀ hx₀ => ⟨fun T hT n => ?_, fun T hT n => ?_⟩⟩
  · rw [dualParams.splicedSanction_add]
    unfold Params.dynamicTopLockInSanctionsF
    have hend : dualParams.episodePath (fun _ => 1) x₀ T ∈ Set.Icc (19/20 : ℝ) 1 := by
      rw [dualParams.episodePath_const_one]
      exact dualParams.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
        dbParams_strictAdjustment ⟨by norm_num, by norm_num⟩ x₀ hx₀ T hT
    exact dbCert_highBasin_rule_eq_one E hVT hVS
      (dualParams.dynamicTopLockInPathF_mem_basin E.V_S E.α hhi hend n)
  · rw [dualParams.splicedSanction_add]
    unfold Params.dynamicTopLockInSanctionsF
    have hend : dualParams.episodePath (fun _ => 0) x₀ T ∈ Set.Icc (0 : ℝ) (1/10) := by
      rw [dualParams.episodePath_const_zero]
      exact dualParams.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment
        dbParams_strictAdjustment ⟨by norm_num, by norm_num⟩ x₀ hx₀ T hT
    exact dbCert_lowBasin_rule_eq_zero E hVS
      (dualParams.dynamicTopLockInPathF_mem_low_basin E.V_S E.α (by norm_num) hlo hend n)

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.dualParams_two_sided_regimes
#print axioms Sanctions.Examples.dualParams_two_sided_episode_sanctions

end Examples
end Sanctions
