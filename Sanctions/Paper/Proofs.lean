/-
Sanctions/Paper/Proofs.lean

**Each statement of `Sanctions/Paper/Statements.lean` holds.** Every proof is the backing
declaration that the formal verification supplement names for the result, applied as is: the
statement and the declaration have the same type, so a reader who has checked a statement
against the paper needs only these one-line proofs to know it is proved. The round axiom scan
(`scripts/hpc-round-scan.txt`) prints the axioms of each theorem below.
-/
import Sanctions.Paper.Statements

namespace Sanctions
namespace Paper

/-- Proposition 2 (`prop:myopic-benchmark`). -/
theorem myopicBenchmark_holds : myopicBenchmark :=
  @Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage

/-- Theorem 3 (`thm:regime-separation`). -/
theorem regimeSeparation_holds : regimeSeparation :=
  @Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF

/-- Theorem 4 (`thm:dominance`). -/
theorem dominance_holds : dominance :=
  @Sanctions.AbstractGame.Params.theorem2_dynamic_dominates_myopic_at_same_alpha

/-- Proposition 5, no exit (`prop:lock-in`). -/
theorem lockInNoExit_holds : lockInNoExit :=
  @Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_sender_package

open Sanctions.AbstractGame in
/-- Proposition 5, entry (`prop:lock-in`). -/
theorem lockInEntry_holds : lockInEntry :=
  @Params.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent

/-- Proposition 6 (`prop:collapse-threshold`). -/
theorem collapseThreshold_holds : collapseThreshold :=
  @Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le

/-- Proposition 7 (i) (`prop:patience-existence`). -/
theorem patienceSlope_holds : patienceSlope :=
  @Sanctions.Examples.ChordEconomyRelief.balance_of_le_βT

/-- Proposition 7 (ii) (`prop:patience-existence`). -/
theorem patienceExistence_holds : patienceExistence :=
  @Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT

/-- Proposition 9 (`prop:welfare-nonidentification`). -/
theorem welfareNonidentification_holds : welfareNonidentification :=
  @Sanctions.Examples.ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking

/-- Proposition 10 (`prop:zero-sanction-planner`). -/
theorem zeroSanctionPlanner_holds : zeroSanctionPlanner :=
  @Sanctions.Welfare.zeroSanction_planner_optimal

/-- Proposition 11 (`prop:planner-efficient-persistence`). -/
theorem plannerEfficientPersistence_holds : plannerEfficientPersistence :=
  @Sanctions.Examples.ChordEconomy.planner_efficient_rep_at_policy_zero

/-- Theorem 12 (`thm:four-cells`). -/
theorem fourCases_holds : fourCases :=
  @Sanctions.Examples.ChordEconomyCs.four_cell_generalF'

end Paper
end Sanctions
