/-
Sanctions/Examples/PlacableSenderDefianceValues.lean

**Any full-defiance equilibrium has the constructed values** (round BB,
2026-09-28; doc 110, the value-fixing step R11c and G8b need).

If a top-selector feedback Stackelberg equilibrium of a chord economy has the
Target defying at every feasible state (`α ≡ 0` on `[0,1]`), then its Sender
value is the constructed `VSstar` (the unique fixed point of the Sender's
Bellman operator at defiance), its Target value is the constructed `VTdef` (the
unique fixed point of the Target operator at `VSstar`), and its realised
sanction rule is the constructed response. No margin, no class condition, no
monotonicity: the two fixed points are unique because both operators contract.

The argument was written inline in `unique_equilibrium_of_monotone_class`
(`PlacableSenderUniqueness.lean`, part (3)); it is extracted here unchanged so
that other results can quantify over every full-defiance equilibrium. Rule 22:
general in `F`. Rule 3: no hypothesis beyond the class.
-/
import Sanctions.Examples.PlacableSenderUniqueness

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **A full-defiance equilibrium has the constructed values and rule.** -/
theorem values_eq_of_policy_zero (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x := by
  have hVS : Eq.V_S = E.VSstar := by
    have hfix : E.toParams.bellmanS_BCF (fun _ => 0) continuous_const Eq.V_S = Eq.V_S := by
      rw [← E.toParams.bellmanS_BCF_congr_on Eq.hα continuous_const hα Eq.V_S]
      exact Eq.V_S_fix.symm
    have hcontr := E.toParams.bellmanS_BCF_contracting (α := fun _ => 0) continuous_const
    have h1 : Eq.V_S = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
    have h2 : E.VSstar = hcontr.fixedPoint := hcontr.fixedPoint_unique E.VSstar_fix
    rw [h1, h2]
  have hVT : Eq.V_T = E.VTdef := by
    have hfix : E.targetOp E.VSstar_mem Eq.V_T = Eq.V_T := by
      ext y
      rw [targetOp_apply, E.V_T_eq Eq y, rule, hα y.val y.property, hVS,
          ← E.response_eq_top E.VSstar_mem y.property 0]
      rfl
    have hcontr := E.targetOp_contracting E.VSstar_mem
    have h1 : Eq.V_T = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
    exact h1
  refine ⟨hVS, hVT, fun x hx => ?_⟩
  change E.toParams.σ_dyn_top Eq.V_S x (Eq.α x) = E.responsePath E.VSstar x
  rw [hα x hx, hVS, ← E.response_eq_top E.VSstar_mem hx 0]
  rfl

/-- The realised rule of a full-defiance equilibrium is positive at every
feasible state (the forward-looking response is, `responsePath_pos`). -/
theorem rule_pos_of_policy_zero (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.rule Eq x := by
  have h := (E.values_eq_of_policy_zero Eq hα).2.2 x hx
  rw [rule_eq, h]
  exact E.responsePath_pos E.VSstar_mem hx

end ChordEconomy

end

#print axioms Sanctions.Examples.ChordEconomy.values_eq_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomy.rule_pos_of_policy_zero

end Examples
end Sanctions
