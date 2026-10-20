/-
Sanctions/Examples/PlacableSenderNoCycles.lean

**The four constructed readings do not cycle** (2026-10-08, record N180).

## What is here, in English

The four readings of one placable economy are each driven by a realized sanction rule
that does not fall when the political state rises: the rule is zero in the myopic
reading `00` and in the Sender-only reading `01`, it is the stage sanction `σ(x, 0)` in the
Target-only reading `10` (non-decreasing by the rally bound (S7)), and it is the
forward-looking response in reading `11` whenever that response is non-decreasing (as the
rally margin gives). So, by `rulePathF_no_cycles`
(`Theory/LockIn/NoCycles.lean`), in each reading the state path and the sanction path are
monotone in the same direction, and a path that returns to a state stays there: no
constructed reading produces a conflict cycle.

General in `F` and in the payoffs, on the class of `Examples/ChordEconomy.lean`, at the
hypotheses each reading is constructed under. **Rule 3:** no new assumption.
-/
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Theory.LockIn.NoCycles

open Set

namespace Sanctions
namespace Examples

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Reading `10` does not cycle.** Under the loss offset, the Target-only path and its
sanction path are monotone in the same direction, and a return is a rest point. -/
theorem targetOnly_no_cycles (hTM : E.LossOffset) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    let R := E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM)
    ((Monotone (E.toParams.rulePathF R x₀) ∧ Monotone (E.toParams.ruleSanctionsF R x₀)) ∨
      (Antitone (E.toParams.rulePathF R x₀) ∧ Antitone (E.toParams.ruleSanctionsF R x₀))) ∧
    (∀ n k : ℕ, 1 ≤ k → E.toParams.rulePathF R x₀ (n + k) = E.toParams.rulePathF R x₀ n →
      ∀ j, E.toParams.rulePathF R x₀ (n + j) = E.toParams.rulePathF R x₀ n) :=
  E.toParams.rulePathF_no_cycles (fun _ hx => E.targetOnlyRule_mem hTM hx)
    (E.targetOnlyRule_monotoneOn hTM) hx₀

/-- **Reading `11` does not cycle, given a non-decreasing response.** Under the loss
offset and a response at defiance non-decreasing in the state, the forward-looking path
and its sanction path are monotone in the same direction, and a return is a rest point. -/
theorem dynamicOf_no_cycles (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    let R := E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono)
    ((Monotone (E.toParams.rulePathF R x₀) ∧ Monotone (E.toParams.ruleSanctionsF R x₀)) ∨
      (Antitone (E.toParams.rulePathF R x₀) ∧ Antitone (E.toParams.ruleSanctionsF R x₀))) ∧
    (∀ n k : ℕ, 1 ≤ k → E.toParams.rulePathF R x₀ (n + k) = E.toParams.rulePathF R x₀ n →
      ∀ j, E.toParams.rulePathF R x₀ (n + j) = E.toParams.rulePathF R x₀ n) := by
  have hR : MonotoneOn (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono))
      Sanctions.I := by
    intro x hx y hy hxy
    rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx,
      E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hy]
    exact hmono hx hy hxy
  exact E.toParams.rulePathF_no_cycles (E.dynamicRule_mem_of_response_monotone hTM hmono)
    hR hx₀

end ChordEconomy

namespace ChordEconomyTwoSided

variable (E : ChordEconomyTwoSided)

/-- **Reading `11` does not cycle under the rally margin**, which makes the response
non-decreasing (`responsePath_monotoneOn_of_margin`). -/
theorem dynamic_no_cycles (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    let R := E.toParams.dynamicEquilibriumRule
      (E.equilibriumTop hTM (E.responsePath_monotoneOn_of_margin hmargin))
    ((Monotone (E.toParams.rulePathF R x₀) ∧ Monotone (E.toParams.ruleSanctionsF R x₀)) ∨
      (Antitone (E.toParams.rulePathF R x₀) ∧ Antitone (E.toParams.ruleSanctionsF R x₀))) ∧
    (∀ n k : ℕ, 1 ≤ k → E.toParams.rulePathF R x₀ (n + k) = E.toParams.rulePathF R x₀ n →
      ∀ j, E.toParams.rulePathF R x₀ (n + j) = E.toParams.rulePathF R x₀ n) :=
  E.dynamicOf_no_cycles hTM (E.responsePath_monotoneOn_of_margin hmargin) hx₀

end ChordEconomyTwoSided

namespace ChordEconomyRelief

variable (E : ChordEconomyRelief)

/-- **Reading `00` does not cycle.** The myopic rule is zero, so the path moves one way
only, and a return is a rest point. -/
theorem myopic_no_cycles (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    let R := E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP)
    ((Monotone (E.toParams.rulePathF R x₀) ∧ Monotone (E.toParams.ruleSanctionsF R x₀)) ∨
      (Antitone (E.toParams.rulePathF R x₀) ∧ Antitone (E.toParams.ruleSanctionsF R x₀))) ∧
    (∀ n k : ℕ, 1 ≤ k → E.toParams.rulePathF R x₀ (n + k) = E.toParams.rulePathF R x₀ n →
      ∀ j, E.toParams.rulePathF R x₀ (n + j) = E.toParams.rulePathF R x₀ n) := by
  refine E.toParams.rulePathF_no_cycles (fun x hx => ?_) (fun x hx y hy _ => ?_) hx₀
  · rw [E.myopicRule_eq_zero hInt hSR hP hx]; exact ⟨le_rfl, zero_le_one⟩
  · rw [E.myopicRule_eq_zero hInt hSR hP hx, E.myopicRule_eq_zero hInt hSR hP hy]

end ChordEconomyRelief

namespace ChordEconomyCs

variable (E : ChordEconomyCs)

/-- **Reading `01` does not cycle.** The Sender-only rule is zero, so the path moves one
way only, and a return is a rest point. -/
theorem senderOnly_no_cycles (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    let R := E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN)
    ((Monotone (E.toParams.rulePathF R x₀) ∧ Monotone (E.toParams.ruleSanctionsF R x₀)) ∨
      (Antitone (E.toParams.rulePathF R x₀) ∧ Antitone (E.toParams.ruleSanctionsF R x₀))) ∧
    (∀ n k : ℕ, 1 ≤ k → E.toParams.rulePathF R x₀ (n + k) = E.toParams.rulePathF R x₀ n →
      ∀ j, E.toParams.rulePathF R x₀ (n + j) = E.toParams.rulePathF R x₀ n) := by
  refine E.toParams.rulePathF_no_cycles (fun x hx => ?_) (fun x hx y hy _ => ?_) hx₀
  · rw [(E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx]; exact ⟨le_rfl, zero_le_one⟩
  · rw [(E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx,
      (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hy]

end ChordEconomyCs

end Examples
end Sanctions
