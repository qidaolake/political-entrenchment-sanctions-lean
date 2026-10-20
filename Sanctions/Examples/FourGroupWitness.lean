/-
Sanctions/Examples/FourGroupWitness.lean

**Four-group-derived witness `Params` + conditional persistence headline.**

A concrete `AbstractGame.Params` whose stage payoffs `U_S`, `U_T` are *derived*
from a Kaempfer-Lowenberg four-group interest-group polity (Grossman-Helpman
weighted-sum aggregation) over the strict rally-dominant region (R), rather than
hand-chosen as in the Eaton-Engers witness. The static Sender selector is the
clipped vertex (Rule-1 coupling, derived), and the transition is the affine law.

The coefficients are the numerically-verified base from `docs/archive/workflow-scratch/fourgroup_solver.py`
(`docs/archive/DESIGN-fourgroup.md`): on this region the forward-looking feedback-Stackelberg
value iteration converges to a **bistable** equilibrium (low start → wash-out,
high start → lock-in), with the three derived stage cross-partials carrying the
right signs.

This file mirrors `EatonEngersWitness.lean`: it discharges the stage-flip
complementarity inputs (`SenderStageID`/`TargetStageID`/`SenderActionDD` and the
strict variants + `SenderChordConcaveInS`) **unconditionally and from the group
primitives**, and states the headline *conditional on the value class* `C` — the
exact same conditional boundary the Eaton-Engers witness draws (the value-class
existence for this non-smooth flip equilibrium is the deferred Curtat-style round).
The advance over E-E: the stage complementarities are now *derived*, not asserted.
-/

import Sanctions.Theory.Microfoundations.FourGroupPolity
import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.StageFlipDischargers
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Examples.AffineInstance.ComplianceTower
import Sanctions.Examples.AffineInstance.Microfoundations

namespace Sanctions
namespace Examples

open KaempferLowenberg

/-- **Concrete four-group witness** in the strict rally-dominant region (R)
(numerically verified to give a bistable lock-in equilibrium). -/
noncomputable def fourGroupWitness : FourGroup where
  th0_JS := 1
  nu := 3
  g_J := 1
  th0_KS := 1
  q_K := 8 / 5
  kS := 1 / 2
  w_pl := 3 / 2
  base_S := 0
  th0_JT := 1
  rho := 6 / 5
  b_J := 1
  c_J := 1
  th0_KT := 1
  mu := 3 / 10
  b_K := 1
  c_K := 1
  kT := 1
  d_s := 0
  w_pl_nn := by norm_num
  kS_pos := by norm_num
  senderRally_pos := by norm_num
  rally_dom := by norm_num

/-- **The four-group-derived witness `Params`** (δ=1/5, β_T=9/10, β_S=1/2, as in
the Eaton-Engers witness), with `U_S`, `U_T` derived from `fourGroupWitness`. -/
noncomputable def fourGroupWitnessParams : Sanctions.AbstractGame.Params :=
  fourGroupWitness.toParams (1 / 5) (9 / 10) (1 / 2)
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (by constructor <;> norm_num)

/-! ## Derived stage-flip complementarity inputs (the certificate's basin inputs) -/

theorem fourGroupWitnessParams_SenderStageID :
    fourGroupWitnessParams.SenderStageID :=
  fun a _ => fourGroupWitness.U_S_senderStageID a

theorem fourGroupWitnessParams_TargetStageID :
    fourGroupWitnessParams.TargetStageID :=
  fun a _ => fourGroupWitness.U_T_targetStageID a

theorem fourGroupWitnessParams_SenderActionDD :
    fourGroupWitnessParams.SenderActionDD :=
  fun x _ => fourGroupWitness.U_S_senderActionDD x

theorem fourGroupWitnessParams_SenderStageIDStrict :
    fourGroupWitnessParams.SenderStageIDStrict :=
  fun a _ s₁ _ s₂ _ hs => fourGroupWitness.U_S_senderStageIDStrict a s₁ s₂ hs

theorem fourGroupWitnessParams_TargetStageIDStrict :
    fourGroupWitnessParams.TargetStageIDStrict :=
  fun a _ s₁ _ s₂ _ hs => fourGroupWitness.U_T_targetStageIDStrict a s₁ s₂ hs

theorem fourGroupWitnessParams_SenderChordConcaveInS :
    fourGroupWitnessParams.SenderChordConcaveInS :=
  fun x _ a _ s₁ s₂ c hc h1 hs h2 =>
    fourGroupWitness.U_S_senderChordConcaveInS x a s₁ s₂ c hc h1 hs h2

/-! ## Conditional three-goals headline (Rule 15) — long-run dominance/lock-in

Mirrors `eatonEngersParams_three_goals_conditional`: given a value-class
certificate `C` at `fourGroupWitnessParams` (the one piece left conditional, exactly
as for the Eaton-Engers witness — the Curtat-style value-class existence for this
non-smooth flip equilibrium), the headline dominance goal holds on the basin. The
difference from E-E: the stage complementarities feeding `C`'s basin are *derived*
from the four-group primitives (the theorems just above), not hand-chosen. -/

/-- **Conditional three-goals headline at the four-group witness.** On the basin,
the forward-looking realized sanction dominates the myopic stage response —
conditional on the value class `C`, with the stage-flip inputs derived from the
group primitives. -/
theorem fourGroupWitnessParams_three_goals_conditional
    (C : fourGroupWitnessParams.StandardComplianceLocalCoreCertificate) :
    ∃ E : fourGroupWitnessParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           fourGroupWitnessParams.σ x (C.M.α x)
             ≤ fourGroupWitnessParams.dynamicTopRealizedRule E.V_S E.α x) := by
  have hF : fourGroupWitnessParams.F
      = Sanctions.AbstractGame.affineF fourGroupWitnessParams.δ := rfl
  obtain ⟨E, hVT, hVS, _hGoal1, hGoal2, _hGoal3⟩ :=
    C.three_goals_local_uniform_starts (p := fourGroupWitnessParams) hF
  exact ⟨E, hVT, hVS, hGoal2⟩

end Examples
end Sanctions
