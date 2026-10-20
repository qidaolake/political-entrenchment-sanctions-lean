/-
Sanctions/Examples/PlacableSenderLowBasin.lean

**The low-basin level condition, regime by regime, on a chord economy**
(doc 70, L3; the reader's package `2026-09-07-round-DE-validation`, doc 01 §5;
on the abstract payoffs since round AV, 2026-09-25, doc 104).

`temporary_relief_post_relief_low_persistence_generalF` and its antitone
sibling take the low-basin level condition as an input: on `[0, x̄]` the
equilibrium's realised sanction rule lies at or below `min(x, s̄_low)`. The
hypothesis census once recorded that condition as "discharged at `dualParams`
only; open on every family". That is regime-blind. On a chord economy:

* in the constructed myopic (`00`) and Sender-only (`01`) regimes the realised
  rule is identically zero, so the condition holds with ceiling `0` on every
  `[0, x̄] ⊆ [0, 1]`, and the post-relief propositions follow outright
  (`myopic_post_relief_low_persistence`, `senderOnly_post_relief_low_persistence`);
* in the constructed Target-only (`10`) and forward-looking (`11`) regimes the
  rule at state `0` is at least the sanction floor `b = σ(0,0) > 0` (`u₀/q` on the
  quadratic–linear family), so no low basin containing `0`
  satisfies the condition (`targetOnly_no_lowBasin_containing_zero`,
  `dynamic_no_lowBasin_containing_zero`).

The obstructions concern the **constructed** rules, not every stationary
equilibrium of the same primitives; nothing here is "low-basin nonexistence
for the model". The dual-basin economy (`dualParams`) remains the example of
both basins under one equilibrium.

Renovation item BH3.3 (2026-10-06): the forward-looking obstruction is not special to
the constructed rule. It holds at every full-defiance equilibrium, with neither the
loss-offset margin nor the rally margin (`no_lowBasin_containing_zero_of_policy_zero`,
in `PlacableSenderDefianceEpisode.lean`), and `dynamic_no_lowBasin_containing_zero` is
re-derived from it there. It still says nothing about equilibria in which the Target
complies somewhere.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderRegime10
import Sanctions.Examples.PlacableSenderEpisode
import Sanctions.Theory.LockIn.ReliefPersistence

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.TransitionChords

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## `00`: the rule is zero, so the level condition holds with ceiling `0` -/


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- The myopic regime's realised rule satisfies the low-basin level condition
with ceiling `0` on every `[0, x̄] ⊆ [0, 1]`. -/
theorem myopic_lowBasin_level_condition (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    {xbar : ℝ} (hxbar : xbar ≤ 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      E.pM.dynamicTopRealizedRule (E.myopicEquilibriumTop hInt hSR hP).V_S (E.myopicEquilibriumTop
          hInt hSR hP).α x
        ≤ min x 0 := by
  intro x hx
  have hxI : x ∈ Sanctions.I := ⟨hx.1, le_trans hx.2 hxbar⟩
  change E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP) x ≤ min x 0
  rw [(E.myopicRule_eq_zero hInt hSR hP) hxI]
  exact le_min hx.1 le_rfl

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)


/-- Strict adjustment of the myopic view's transition (the same `F`). -/
theorem pM_strictAdjustment : E.pM.StrictAdjustment :=
  E.pM.strictAdjustment_of_sanctionLowerChord E.hdlo0 E.hSlo



end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **Post-relief persistence in the low basin, myopic regime**: after a
zero-sanction episode of the uniform exit horizon, the state stays in
`[0, x̄]` forever. The level condition is discharged, not assumed. -/
theorem myopic_post_relief_low_persistence (hInt : E.Interior) (hSR : E.StageRelief) (hP :
    E.Placable) {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, E.pM.dynamicTopLockInPathF (E.myopicEquilibriumTop hInt hSR hP).V_S
        (E.myopicEquilibriumTop hInt hSR hP).α
          (E.pM.reliefPathF x₀ (E.pM.fullReliefExitHorizon xbar)) n
        ∈ Set.Icc (0 : ℝ) xbar :=
  E.pM.temporary_relief_post_relief_low_persistence_generalF E.pM_strictAdjustment _ _ hxbar
    ((E.myopic_lowBasin_level_condition hInt hSR hP) hxbar.2) hx₀

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## `10` and `11`: the rule at state `0` is positive -/

/-- **No low basin containing `0` for the Target-only rule**: at state `0` the
rule is the sanction floor `b = σ(0,0) > 0`, while `min(0, s̄_low) ≤ 0`. -/
theorem targetOnly_no_lowBasin_containing_zero (hTM : E.LossOffset) {xbar : ℝ} (hxbar : 0 ≤ xbar) (sbar_low : ℝ) :
    ¬ ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      E.pT.dynamicTopRealizedRule (E.targetOnlyEquilibriumTop hTM).V_S (E.targetOnlyEquilibriumTop hTM).α x
        ≤ min x sbar_low := by
  intro h
  have h0 := h 0 ⟨le_rfl, hxbar⟩
  change E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) 0 ≤ min 0 sbar_low at h0
  rw [(E.targetOnlyRule_eq_stage hTM) zero_mem_I] at h0
  have hv : 0 < E.σ 0 0 := E.stage_argmax_pos zero_mem_I
  have : min (0 : ℝ) sbar_low ≤ 0 := min_le_left _ _
  linarith

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **No low basin containing `0` for the forward-looking rule** under the
rally margin: at state `0` the constructed rule is at least `b = σ(0,0) > 0`.
The form at every full-defiance equilibrium, without either margin, is
`no_lowBasin_containing_zero_of_policy_zero` (renovation item BH3.3). General in `F`;
on the two-sided extension since renovation item BJ3.1 (2026-10-07), as the rally margin
reads the two-sided curvature data. -/
theorem dynamic_no_lowBasin_containing_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {xbar : ℝ} (hxbar : 0 ≤ xbar) (sbar_low : ℝ) :
    ¬ ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      E.toParams.dynamicTopRealizedRule ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α x ≤ min x sbar_low := by
  intro h
  have h0 := h 0 ⟨le_rfl, hxbar⟩
  have hb := (E.dynamicRule_ge_sfloor hTM) hmargin zero_mem_I
  have hpos : 0 < E.sfloor := E.sfloor_pos
  have : min (0 : ℝ) sbar_low ≤ 0 := min_le_left _ _
  linarith

end ChordEconomyTwoSided

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## `01`: the rule is zero, so the level condition holds with ceiling `0` -/

/-- The Sender-only regime's realised rule satisfies the low-basin level
condition with ceiling `0` on every `[0, x̄] ⊆ [0, 1]`. -/
theorem senderOnly_lowBasin_level_condition (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {xbar : ℝ} (hxbar : xbar ≤ 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      E.pS.dynamicTopRealizedRule ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).V_S
        ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).α x ≤ min x 0 := by
  intro x hx
  have hxI : x ∈ Sanctions.I := ⟨hx.1, le_trans hx.2 hxbar⟩
  change E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN) x ≤ min x 0
  rw [(E.senderOnlyRule_eq_zero hInt hP) hrelief hN hxI]
  exact le_min hx.1 le_rfl

/-- Strict adjustment of the Sender-only view's transition (the same `F`). -/
theorem pS_strictAdjustment : E.pS.StrictAdjustment :=
  E.pS.strictAdjustment_of_sanctionLowerChord E.hdlo0 E.hSlo

/-- **Post-relief persistence in the low basin, Sender-only regime**: the
level condition is discharged by the zero rule. -/
theorem senderOnly_post_relief_low_persistence (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, E.pS.dynamicTopLockInPathF ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).V_S
          ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).α
          (E.pS.reliefPathF x₀ (E.pS.fullReliefExitHorizon xbar)) n
        ∈ Set.Icc (0 : ℝ) xbar :=
  E.pS.temporary_relief_post_relief_low_persistence_generalF E.pS_strictAdjustment _ _ hxbar
    ((E.senderOnly_lowBasin_level_condition hInt hP) hrelief hN hxbar.2) hx₀

end ChordEconomyCs

end

#print axioms Sanctions.Examples.ChordEconomyRelief.myopic_post_relief_low_persistence
#print axioms Sanctions.Examples.ChordEconomy.targetOnly_no_lowBasin_containing_zero
#print axioms Sanctions.Examples.ChordEconomyTwoSided.dynamic_no_lowBasin_containing_zero
#print axioms Sanctions.Examples.ChordEconomyCs.senderOnly_post_relief_low_persistence

end Examples
end Sanctions
