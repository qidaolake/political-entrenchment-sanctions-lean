/-
Sanctions/Examples/PlacableSenderRegime10Core.lean

**The Target-only reading under the loss-offset condition alone** (round BB,
2026-09-28; doc 110, item R10(c)).

Row 37, `target_only_regime_generalF` (`PlacableSenderRegime10.lean`), takes two
premises: the loss-offset condition `LossOffset` and the rally margin. Its four
clauses are (i) the Target-only profile keeps the primitives; (ii) the Target
defies, uniquely, and the realised sanction is the stage selector at defiance;
(iii) the state washes in, above the approach to the floor, and converges to a
fixed point of the stage selector from every start; (iv) that limit is strictly
below the forward-looking limit from the same start.

Only clause (iv) reads the rally margin — it is where the forward-looking path
enters, through `targetOnly_limit_lt_dynamic_limit`, and the forward-looking
equilibrium is constructed only under the margin. Clauses (i)-(iii) are about
the Target-only equilibrium, which is constructed under `LossOffset` alone.
`target_only_regime_generalF_core` states (i)-(iii) under `LossOffset` alone,
one premise instead of two. It is a sub-conjunction of row 37, which is
untouched; clause (iv) stays available as the non-headline
`targetOnly_limit_lt_dynamic_limit` under the margin.

**Scope (Rule 9).** A statement about the constructed Target-only equilibrium
`targetOnlyEquilibriumTop` of every chord economy satisfying the loss-offset
condition; the uniqueness in (ii) is uniqueness of the Target's argmax at that
equilibrium's values, not uniqueness of equilibrium.

Rule 1: the Target policy is the unique argmax; the Sender rule is the stage
argmax (the Sender's discount is zero in this reading). Rule 22: general in `F`.
Rule 3: no new assumption — one premise fewer than row 37.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BJ3.1 (2026-10-07): the core stays on `ChordEconomy`; the margin form
`target_only_regime_generalF_of_core` is stated on `ChordEconomyTwoSided`.
-/
import Sanctions.Examples.PlacableSenderRegime10

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.TransitionChords
  Sanctions.GeometricApproach Sanctions.Mechanism

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **The Target-only reading under the loss-offset condition alone**, general
in `F` and in the payoffs, at the constructed Target-only equilibrium
`targetOnlyEquilibriumTop`: (i) the Target-only profile has the same payoffs and
transition; (ii) at every feasible state the Target defies, every Target
maximiser is defiance, and the realised sanction is the stage selector at
defiance; (iii) from every feasible start the state stays above the geometric
approach to the sanction floor and converges to a fixed point of the stage
selector at or above the floor. These are clauses (i)-(iii) of row 37
(`target_only_regime_generalF`) without its rally margin, which only clause (iv)
reads. -/
theorem target_only_regime_generalF_core (hTM : E.LossOffset) :
    (E.pT.U_T = E.toParams.U_T ∧ E.pT.U_S = E.toParams.U_S ∧ E.pT.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyEquilibriumTop hTM).α x = 0 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pT.joint_T_top_integrand (E.targetOnlyEquilibriumTop hTM).V_T
          (E.targetOnlyEquilibriumTop hTM).V_S x b) Sanctions.I a → a = 0) ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x = E.σ x 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, approach E.sfloor E.dlo t ≤ (E.targetOnlyPath hTM) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z)) :=
  ⟨⟨rfl, rfl, rfl⟩,
   fun _ hx => ⟨rfl, fun _ ha hmax => (E.targetOnlyEquilibriumTop_argmax_unique hTM) hx ha hmax,
     (E.targetOnlyRule_eq_stage hTM) hx⟩,
   fun _ hx₀ => ⟨(E.targetOnlyPath_ge_approach hTM) hx₀, (E.targetOnlyPath_tendsto hTM) hx₀⟩⟩

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **Row 37 is the core plus clause (iv).** The pinned statement follows from
the margin-free core and `targetOnly_limit_lt_dynamic_limit`, which is the only
place the rally margin enters. General in `F`. Under the stage appetite `u_hi < q`,
read only by clause (iv) (BH3.1, 2026-10-06: the binder was interiority `A < q`,
matching `target_only_regime_generalF`). On the two-sided extension since renovation item
BJ3.1 (2026-10-07), as the rally margin reads the two-sided curvature data. -/
theorem target_only_regime_generalF_of_core (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    (E.pT.U_T = E.toParams.U_T ∧ E.pT.U_S = E.toParams.U_S ∧ E.pT.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyEquilibriumTop hTM).α x = 0 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pT.joint_T_top_integrand (E.targetOnlyEquilibriumTop hTM).V_T
          (E.targetOnlyEquilibriumTop hTM).V_S x b) Sanctions.I a → a = 0) ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x = E.σ x 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, approach E.sfloor E.dlo t ≤ (E.targetOnlyPath hTM) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z)) :=
  let h := E.target_only_regime_generalF_core hTM
  ⟨h.1, h.2.1, h.2.2, fun _ hx₀ => (E.targetOnly_limit_lt_dynamic_limit hS hTM) hmargin hx₀⟩

end ChordEconomyTwoSided

end

#print axioms Sanctions.Examples.ChordEconomy.target_only_regime_generalF_core
#print axioms Sanctions.Examples.ChordEconomyTwoSided.target_only_regime_generalF_of_core

end Examples
end Sanctions
