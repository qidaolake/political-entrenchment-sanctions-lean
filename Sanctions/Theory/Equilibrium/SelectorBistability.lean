/-
Sanctions/Theory/Equilibrium/SelectorBistability.lean

**BRW 2013 Corollary 3.1 collapse-on-uniqueness, carrier-level form.**

This module is the JET-referee Issue 6 response on the Lean side. It
delivers two named results that ground the paper's selector-convention
discussion at the carrier-class level:

* `extremal_selectors_coincide_under_DynamicArgmaxUnique` —
  named `DynamicArgmaxUnique` hypothesis form of the per-`(x, a)`
  collapse lemma `extremal_selectors_coincide_at_unique_argmax`
  delivered in `SigmaDynComparison.lean`. Quantifies the collapse
  uniformly in `(x, a)`.

* `extremal_selectors_coincide_on_valueClass2_carrier` —
  the headline carrier-level corollary: on every value-class-2
  Sender carrier `D.carrier_S`, the extremal selectors agree at
  every member `V_S`, every physical state and every physical
  compliance level (since round BJ4.3, when the carrier's uniqueness
  became compliance-local). One-line proof via `D.sender_unique_on`.

The economic claim --- "the selector debate is structurally moot once
the value class is fixed because uniqueness is required to support a
Bellman fixed-point equilibrium" --- is the formal answer to the
referee's selector-convention critique. Bistability in this paper is
two BASINS on disjoint state ranges (`Theorem 1` and `Theorem 4`),
NOT two extremal selectors at the same equilibrium.

## Reference anchors

* **Vives 1990** Theorem 4.1, machine-checked at
  `Foundations/VivesLattice.lean`: greatest and least Nash equilibria
  exist on a lattice game. The greatest-selector convention used in
  this paper is a modelling convention: it is not shown to be the upper
  rationalizable bound of any game, nor `σ_dyn_bot` the lower one.

* **Milgrom-Roberts 1990** Theorem 5, fixed-point half only, also at
  `Foundations/VivesLattice.lean`: the greatest Nash equilibrium dominates
  every other in the lattice product order. It does not justify preferring
  `σ_dyn_top` over `σ_dyn_bot` where the dynamic argmax set is
  non-singleton; that preference is a convention.

* **Balbus-Reffett-Wozny 2013** Corollary 3.1, machine-checked at
  `Foundations/BalbusReffettWozny.lean`: extremal selectors collapse
  on the unique argmax. This is what gives the collapse-on-uniqueness
  result below its economic legitimacy.

## Rule compliance

**Rule 1** ✓ — no new strategies. `σ_dyn_top` and `σ_dyn_bot` are
both equilibrium-derived (extremal elements of the dynamic argmax
set); the collapse-on-uniqueness lemma is a derivation of their
*relative ordering*, not a hand-chosen sanction rule.

**Rule 3** ✓ — no new `Params` fields. The named `DynamicArgmaxUnique`
hypothesis is a pre-existing definition from `SelectionRobust.lean`;
this module just packages the collapse result against it.

**Rule 5** ✓ — fully parametric over `(p, D : ValueClass2, V_S)`. No
witness-specific content.

**Rule 8** ✓ — module header explains every introduced object in plain
English.

**Rule 10** — verified axiom-clean post-build.

**Rule 19** — this is *not* a Foundations module: the content depends
on `ValueClass2` (a project-specific carrier class). The abstract BRW
content lives at `Foundations/BalbusReffettWozny.lean`.
-/

import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.Equilibrium.SelectionRobust
import Sanctions.Theory.Bellman.InvariantValueClass2
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions

open BoundedContinuousFunction

namespace AbstractGame
namespace Params

variable (p : Params)

/-- **BRW 2013 Corollary 3.1 collapse-on-uniqueness (named form).**
On any `V_S` at which the dynamic argmax is uniformly unique in
`(x, a)`, the upper and lower extremal selectors agree pointwise.

Named form of `extremal_selectors_coincide_at_unique_argmax` (in
`SigmaDynComparison.lean`) that consumes the `DynamicArgmaxUnique V_S`
predicate (from `SelectionRobust.lean`). -/
theorem extremal_selectors_coincide_under_DynamicArgmaxUnique
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : p.DynamicArgmaxUnique V_S) :
    ∀ x ∈ Sanctions.S, ∀ a, p.σ_dyn_bot V_S x a = p.σ_dyn_top V_S x a := by
  intro x hx a
  exact p.extremal_selectors_coincide_at_unique_argmax V_S x a (h_unique x hx a)

/-- **Carrier-level corollary.** On every value-class-2 Sender carrier
`D.carrier_S`, the upper and lower extremal selectors agree at every
member `V_S`, every physical state `x` and every physical compliance level
`a ∈ [0,1]`. One-line consequence of `D.sender_unique_on`. General in `F`.

Plain English: in any value class supporting a Bellman fixed-point
equilibrium, the dynamic Sender argmax is required to be unique on
the carrier; therefore the extremal selectors coincide on the
carrier; therefore the paper's selector convention reduces to a
notation choice at the unique argmax. Bistability is two basins on
disjoint state ranges, not two extremal selectors at one state.

Round BJ4.3 (2026-10-08): `ValueClass2.sender_unique_on` now asks for
uniqueness only at physical compliance levels (`DynamicArgmaxUniqueOnI`), so
the coincidence is stated for `a ∈ I` instead of every real `a`. That covers
every compliance level the Target can choose; at a `V_S` with full
`DynamicArgmaxUnique` the all-`a` form is
`extremal_selectors_coincide_under_DynamicArgmaxUnique`. -/
theorem extremal_selectors_coincide_on_valueClass2_carrier
    (D : p.ValueClass2) :
    ∀ V_S ∈ D.carrier_S, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      p.σ_dyn_bot V_S x a = p.σ_dyn_top V_S x a := by
  intro V_S hV_S x hx a ha
  exact p.extremal_selectors_coincide_at_unique_argmax V_S x a
    (D.sender_unique_on V_S hV_S x hx a ha)

end Params
end AbstractGame
end Sanctions
