/-
Sanctions/Foundations/VivesLattice.lean

**Vives 1990 lattice-game existence and extremal equilibria (Tarski).**

External-theory Foundations module (Rule 19). What it proves: a monotone
joint best-response map on a product of complete lattices has a greatest
and a least fixed point, and these bound every other fixed point. It proves
nothing about rationalizability or about Blackwell optimality. The anchor
results it cites are:

* **Vives (1990, *Journal of Mathematical Economics* 19(3):305–321)
  Theorem 4.1.** A Nash equilibrium in a game with strategic
  complementarities exists, and the equilibrium set has a greatest and
  least element under the product order. The result requires only that
  the joint best-response correspondence be monotone-increasing on a
  product of complete lattices; quasiconcavity of payoffs is *not*
  required (Vives' main methodological contribution over the
  topological / Glicksberg–Kakutani route). The proof is Tarski's
  fixed-point theorem applied to the joint best-response map.
  `PaperRefer/MathTheory/NashEquilibriumStrategicComplementarities-Vives-1990.md`.

  Do **not** confuse this with Vives' **Theorem 3.1**, which the paper cites
  separately: that is a single-agent *lattice-programming* result (§3,
  monotonicity of the optimal solution of `max{g(x,t) : x ∈ S}`), not an
  equilibrium statement. Existence of the greatest maximiser there is his
  **Lemma 3.1**; monotonicity of that greatest selection is **Theorem
  3.1(ii)**. Equilibrium existence + extremal equilibria is Theorem 4.1,
  which is what this module formalises.

* **Milgrom & Roberts (1990, *Econometrica* 58(6):1255–1277) Theorem 5.**
  In a supermodular game, the extremal Nash equilibria are the upper and
  lower bounds of the rationalizable (serially undominated) strategy set.
  This module formalises only the fixed-point half of that statement: the
  greatest and least fixed points bound every other fixed point. The
  bound on rationalizable strategies, which need not be fixed points, is
  not formalised.
  `PaperRefer/MathTheory/RationalizabilityLearningEquilibrium-MilgromRoberts-1990.md`.

* **Puterman (1994, *Markov Decision Processes*) Chapter 10
  (Sensitive Discount Optimality).**
  `BookRefer/Markov Decision Processes Discrete Stochastic Dynamic
  Programming (Martin L. Puterman) 1994.md`. Background reading on
  selection among multiple optimal policies of a Markov decision process
  (Blackwell-optimal and `n`-discount-optimal policies). It is not used
  here. Nothing in the project shows that the top selector `σ_dyn_top`
  is Blackwell-optimal, and a greatest maximiser need not be
  Blackwell-optimal in general.

## Why this module is added in the current round

The project's `Foundations/TarskiMPE.lean` already exposes abstract
Tarski fixed-point existence on a product of complete lattices. The
new content in this Foundations module is the **theoretical
attribution and the extremal-equilibrium characterisation**:

* The Vives 1990 result is the canonical reference for "Nash equilibrium
  existence via Tarski on a lattice game"; the abstract Tarski statement
  in `TarskiMPE.lean` is exactly its statement, but lacks attribution.
  Citing Vives makes the result auditable against the published version
  with no proof rewrite.

* The extremal fixed points give the abstract counterpart of the
  project's convention of selecting extremal objects. They do not justify
  the `σ_dyn_top` greatest-selector convention: `σ_dyn_top` is the
  greatest maximiser of the Sender's dynamic objective in `s` at each
  `(x, a)`, a single-agent selection that remains a modelling convention.
  No theorem here links it to the rationalizable set of any game.

## Rule compliance

**Rule 19 placement.** Both theorems are external mathematical content
(generic lattice / order-theoretic statements applying to arbitrary
lattice games, not the sanctions model). They live in `Foundations/`,
with `Foundations/TarskiMPE.lean` reciting the existence corollary
specialised to the sanctions setting.

**Rule 3 status.** Pure cat-2 add: both theorems are abstract over
arbitrary complete lattices and joint best-response order-homs. No new
`Params` field, no new project-specific Prop. The Theory-side
specialisation to the feedback Stackelberg bilateral game would require
isotonicity of the joint Bellman operator in `(V_T, V_S)`, which is a
Rule-3 trigger and is deferred to a future round with proper
confirmation.

**Rule 5 parametric form.** Every theorem in this module is parametric
over the lattices `L_S, L_T` and the best-response maps `BR_S, BR_T`.
No witness-specific specialisation.

**Rule 10 axiom hygiene.** All declarations are expected to be
axiom-clean (`propext, Classical.choice, Quot.sound`) since they are
direct applications of mathlib's `OrderHom.lfp` / `OrderHom.gfp`.

## What this module exports

* `LatticeGame` — the abstract Vives lattice-game record: two complete
  lattices of policy spaces plus two monotone joint best-response maps.
* `LatticeGame.equilibrium` — the Nash equilibrium predicate.
* `LatticeGame.greatestEq_is_equilibrium`, `LatticeGame.leastEq_is_equilibrium`,
  `LatticeGame.exists_equilibrium` — Vives 1990 Theorem 4.1 (the greatest and
  least fixed points, via `OrderHom.gfp` / `OrderHom.lfp`, are equilibria).
* `LatticeGame.greatestEq_is_upper_bound`, `LatticeGame.leastEq_is_lower_bound`,
  `LatticeGame.equilibrium_extremal_characterisation` — the extremal
  equilibria bound every other equilibrium (fixed point). Rationalizable
  strategies are not covered.
-/

import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Order
import Mathlib.Order.CompleteLattice.Basic

namespace Sanctions
namespace Foundations
namespace VivesLattice

open OrderHom

/-! ## §1 Vives 1990 abstract lattice game

A *lattice game* (Vives 1990 §4) is two complete lattices `L_S, L_T` of
strategy spaces together with two monotone joint best-response maps
`BR_S : L_S × L_T →o L_S` and `BR_T : L_S × L_T →o L_T`. The Nash
equilibria of the game are the fixed points of the joint map
`(σ, α) ↦ (BR_S(σ, α), BR_T(σ, α))`.

The monotonicity hypothesis on `BR_S, BR_T` is Vives' standing
"strategic complementarities" condition: when one player's strategy
increases (in the lattice order), the other's best response weakly
increases. -/

/-- **Vives 1990 lattice game (abstract).**
Two complete lattices of strategy spaces plus two monotone joint
best-response maps. -/
structure LatticeGame where
  /-- Sender policy lattice. -/
  L_S : Type*
  /-- Target policy lattice. -/
  L_T : Type*
  /-- Complete-lattice instance on `L_S`. -/
  inst_S : CompleteLattice L_S
  /-- Complete-lattice instance on `L_T`. -/
  inst_T : CompleteLattice L_T
  /-- Sender best-response operator. Monotone in the product order. -/
  BR_S : (L_S × L_T) →o L_S
  /-- Target best-response operator. Monotone in the product order. -/
  BR_T : (L_S × L_T) →o L_T

namespace LatticeGame

variable (G : LatticeGame)

attribute [instance] LatticeGame.inst_S LatticeGame.inst_T

/-- Joint best-response map on the product lattice. -/
def jointBR : (G.L_S × G.L_T) →o (G.L_S × G.L_T) where
  toFun p := (G.BR_S p, G.BR_T p)
  monotone' _ _ hpq := ⟨G.BR_S.monotone hpq, G.BR_T.monotone hpq⟩

/-- A Nash equilibrium of the lattice game is a fixed point of the joint
best-response map. -/
def equilibrium (p : G.L_S × G.L_T) : Prop := G.jointBR p = p

/-- The greatest fixed point of the joint best-response map. By Tarski's
theorem applied to mathlib's `OrderHom.gfp`. This is the greatest
element of the equilibrium set in the product lattice order. -/
noncomputable def greatestEq : G.L_S × G.L_T :=
  OrderHom.gfp G.jointBR

/-- The least fixed point. Symmetric to `greatestEq`. -/
noncomputable def leastEq : G.L_S × G.L_T :=
  OrderHom.lfp G.jointBR

/-! ## §2 Vives 1990 Theorem 4.1 existence -/

/-- **Vives 1990 Theorem 4.1.** A lattice game has a Nash equilibrium.
The greatest fixed point `gfp(jointBR)` is one. -/
theorem greatestEq_is_equilibrium : G.equilibrium (G.greatestEq) := by
  unfold equilibrium greatestEq
  exact OrderHom.map_gfp G.jointBR

/-- **Vives 1990 Theorem 4.1 (least).** Symmetric. -/
theorem leastEq_is_equilibrium : G.equilibrium (G.leastEq) := by
  unfold equilibrium leastEq
  exact OrderHom.map_lfp G.jointBR

/-- **Vives 1990 Theorem 4.1 (combined corollary).** The equilibrium set
is non-empty. -/
theorem exists_equilibrium : ∃ p : G.L_S × G.L_T, G.equilibrium p :=
  ⟨G.greatestEq, G.greatestEq_is_equilibrium⟩

/-! ## §3 Extremal equilibria

The greatest Nash equilibrium dominates every other fixed point in the
lattice order, and the least is dominated by every fixed point. This is
the fixed-point half of Milgrom-Roberts 1990 Theorem 5. Their theorem also
bounds every rationalizable strategy profile; rationalizable profiles need
not be fixed points of the joint best response, and that bound is not
proved here. -/

/-- **Extremal equilibria (upper bound).** The greatest equilibrium
dominates every other equilibrium in the product order. It says nothing
about rationalizable strategies or about the `σ_dyn_top` selector. -/
theorem greatestEq_is_upper_bound (p : G.L_S × G.L_T) (hp : G.equilibrium p) :
    p ≤ G.greatestEq := by
  unfold greatestEq
  unfold equilibrium at hp
  -- A fixed point of `jointBR` is a post-fixed point (jointBR p ≤ p, ≥, =),
  -- hence ≤ gfp by the universal property of the greatest fixed point.
  apply le_gfp
  exact hp.ge

/-- **Extremal equilibria (lower bound).** Symmetric. The least
equilibrium is dominated by every other equilibrium. -/
theorem leastEq_is_lower_bound (p : G.L_S × G.L_T) (hp : G.equilibrium p) :
    G.leastEq ≤ p := by
  unfold leastEq
  unfold equilibrium at hp
  apply lfp_le
  exact hp.le

/-- **Combined characterisation.** The greatest equilibrium is the
maximum of the equilibrium set; the least equilibrium is the minimum.
Both exist by Tarski + Vives 1990 Theorem 4.1. -/
theorem equilibrium_extremal_characterisation :
    (∀ p : G.L_S × G.L_T, G.equilibrium p → p ≤ G.greatestEq) ∧
    (∀ p : G.L_S × G.L_T, G.equilibrium p → G.leastEq ≤ p) :=
  ⟨G.greatestEq_is_upper_bound, G.leastEq_is_lower_bound⟩

end LatticeGame

end VivesLattice
end Foundations
end Sanctions
