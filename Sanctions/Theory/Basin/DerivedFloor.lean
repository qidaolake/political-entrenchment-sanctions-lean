/-
Sanctions/Theory/Basin/DerivedFloor.lean

**The basin's sanction floor as a derived object, not a chosen constant.**

Every basin certificate in this development carries a level floor `sbar` and
asks two things of the equilibrium sanction rule on the basin: that it stay
weakly above `sbar`, and that it stay weakly above the state. `sbar` is then
supplied by hand — `1/10` at the certificate witnesses, `2/5` at P3 — and a
reader has no way to tell whether the number means anything.

It does not have to be supplied. The greatest monotone minorant of the realized
rule over the basin, `Foundations/CrossOrderComparison.monotoneFloorOn`, *is* the
best available floor, and taking it in that role makes the level condition true
by construction. What remains is the ratchet `x ≤ R x` alone.

Three facts make this work, and all three are already general:

* the floor is below the rule everywhere on the basin (`monotoneFloorOn_le`);
* it is monotone **without any monotonicity of the rule** — which is what makes
  it usable here, since `dynamicTopRealizedRule` is a greatest-argmax selector
  composed with a Bellman-optimal policy and is upper semicontinuous at best;
* boundedness, which `sInf` needs, is free from feasibility
  (`σ_dyn_top_mem_I` puts the rule in `[0,1]`).

Nothing here is a new assumption. The content is that one existing assumption
was never needed in the form it was written.
-/

import Sanctions.Foundations.CrossOrderComparison
import Sanctions.Theory.Basin.WeakFloorBasin

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open Sanctions.CrossOrder

noncomputable section

/-! ## The derived floor of an arbitrary rule

Stated for a bare `R : ℝ → ℝ`: nothing in this section mentions the game, so
nothing here should. The equilibrium instances follow in the next section. -/

namespace Basin

/-! ## The derived floor -/

/-- **The derived sanction floor of a rule on a basin.**

The greatest monotone function lying below `R` on `[xbar, 1]`. Read at the
basin's left edge it is the infimum of the rule over the whole basin
(`monotoneFloorOn_Icc_left`) — the strongest uniform level floor the rule
actually supports. Read at a general basin state it is the infimum over the part
of the basin weakly above that state, which is the state-dependent floor. -/
def derivedSanctionFloor (R : ℝ → ℝ) (xbar : ℝ) : ℝ → ℝ :=
  monotoneFloorOn R (Icc xbar 1)

/-- A feasible rule is bounded below on the basin, so its floor is well defined.
Feasibility is the only input. -/
theorem bddBelow_rule_image {R : ℝ → ℝ} {xbar : ℝ}
    (hmem : ∀ x ∈ Icc xbar (1 : ℝ), R x ∈ Sanctions.I) :
    BddBelow (R '' Icc xbar 1) :=
  bddBelow_image_of_forall_le (fun x hx => (hmem x hx).1)

/-- **The floor lies below the rule.** True by construction, at every basin
state — this is the level condition, and it costs nothing. -/
theorem derivedSanctionFloor_le {R : ℝ → ℝ} {xbar x : ℝ}
    (hmem : ∀ y ∈ Icc xbar (1 : ℝ), R y ∈ Sanctions.I) (hx : x ∈ Icc xbar 1) :
    derivedSanctionFloor R xbar x ≤ R x :=
  monotoneFloorOn_le (bddBelow_rule_image hmem) hx

/-- **The floor is monotone, with no monotonicity assumed of the rule.**

The point of using a floor rather than the rule itself: a greatest-argmax
selector need not be monotone, and its floor is, unconditionally. -/
theorem derivedSanctionFloor_monotoneOn {R : ℝ → ℝ} {xbar : ℝ}
    (hmem : ∀ y ∈ Icc xbar (1 : ℝ), R y ∈ Sanctions.I) :
    MonotoneOn (derivedSanctionFloor R xbar) (Icc xbar 1) :=
  monotoneFloorOn_monotoneOn (bddBelow_rule_image hmem)

/-- **At the left edge the floor is the uniform infimum.** This is the number a
hand-picked `sbar` was always trying to approximate. -/
theorem derivedSanctionFloor_left {R : ℝ → ℝ} {xbar : ℝ} :
    derivedSanctionFloor R xbar xbar = sInf (R '' Icc xbar 1) :=
  monotoneFloorOn_Icc_left

/-! ## What it buys: the level condition disappears -/

/-- **The basin condition collapses to the ratchet.**

With the derived floor in the role of the level constant, the pair
`max x (floor x) ≤ R x` — level floor together with the order condition — holds
exactly when the ratchet `x ≤ R x` does. The level half is free.

So a certificate that carried a chosen `sbar` and asked for both conditions was
asking for one condition and a number. -/
theorem derivedFloor_condition_iff_ratchet {R : ℝ → ℝ} {xbar x : ℝ}
    (hmem : ∀ y ∈ Icc xbar (1 : ℝ), R y ∈ Sanctions.I) (hx : x ∈ Icc xbar 1) :
    max x (derivedSanctionFloor R xbar x) ≤ R x ↔ x ≤ R x :=
  floorOnIcc_le_iff_self_le (bddBelow_rule_image hmem) hx

end Basin

/-! ## The equilibrium instances

Here the rule is the realized equilibrium rule, its feasibility is automatic from
`σ_dyn_top_mem_I`, and so every side condition above discharges itself. -/

namespace AbstractGame
namespace Params

variable (p : Params)

open Sanctions.Basin

/-- The equilibrium rule is always feasible, so its floor always exists. -/
theorem bddBelow_dynamicTopRealizedRule_image
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (xbar : ℝ) :
    BddBelow (p.dynamicTopRealizedRule V_S α '' Icc xbar 1) :=
  bddBelow_rule_image (fun x _ => p.dynamicTopRealizedRule_mem V_S α x)

/-- The basin condition at the equilibrium rule collapses to the ratchet, with
no feasibility side condition left to supply. -/
theorem dynamicTopRealizedRule_derivedFloor_condition_iff
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar x : ℝ}
    (hx : x ∈ Icc xbar 1) :
    max x (derivedSanctionFloor (p.dynamicTopRealizedRule V_S α) xbar x)
        ≤ p.dynamicTopRealizedRule V_S α x
      ↔ x ≤ p.dynamicTopRealizedRule V_S α x :=
  Sanctions.Basin.derivedFloor_condition_iff_ratchet
    (fun y _ => p.dynamicTopRealizedRule_mem V_S α y) hx

/-- **The ratchet is exactly domination by the floor**, in cross-order form.

`crossOrderOn_iff_le_monotoneFloorOn` at `g₁ = id`. Stating the ratchet this way
makes the quantifier structure visible: it is not a pointwise condition on `R`
but a condition relating each basin state to the rule's behaviour everywhere
above it, and the floor is the object that packages the latter. -/
theorem ratchet_iff_le_derivedFloor {R : ℝ → ℝ} {xbar : ℝ}
    (hmem : ∀ y ∈ Icc xbar (1 : ℝ), R y ∈ Sanctions.I) :
    CrossOrderOn id R (Icc xbar 1) (Icc xbar 1) ↔
      ∀ x ∈ Icc xbar 1, x ≤ derivedSanctionFloor R xbar x :=
  crossOrderOn_iff_le_monotoneFloorOn (subset_refl _) (bddBelow_rule_image hmem)

/-- The corner condition at the derived floor. `corner_of_pivot_le_floor` reduces
`xbar ≤ F xbar sbar` to `xbar ≤ sbar`; with the derived floor in that role the
requirement becomes the ratchet at the left edge, read through the floor. -/
theorem corner_of_le_derivedFloor {R : ℝ → ℝ} {xbar : ℝ}
    (h : xbar ≤ Sanctions.Basin.derivedSanctionFloor R xbar xbar) :
    xbar ≤ p.F xbar (Sanctions.Basin.derivedSanctionFloor R xbar xbar) :=
  p.corner_of_pivot_le_floor h

end Params
end AbstractGame

end

end Sanctions
