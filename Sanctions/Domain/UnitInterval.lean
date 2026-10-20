/-
Sanctions/Domain/UnitInterval.lean

**The state and action space.**

`[0,1]` is where every policy, sanction, and political state in this
development lives. It is not a piece of mathematics --- it is a modelling
choice, and it is the only one this layer contains.

Why it is a layer of its own, *below* `Foundations/` rather than above it:
twelve Foundations files are stated over `S` (the moving-average and box-transfer
kernels, the Kantorovich duals, the Feynman-Kac and Krylov-Bogolyubov results,
the semiconcave Riccati recursion). Those are reusable operator theory that
happens to be specialized to this interval, not domain adapters, and moving them
would put general mathematics into a domain layer. Naming the interval here and
importing it there records the specialization as a visible dependency instead of
an invisible one --- which is the auditable fact worth having.

What this does **not** claim: that the mathematics above has been generalized to
an arbitrary `Set.Icc l u`. It has not. Doing so would change theorem statements
and is a separate exercise; until then, "Foundations is specialized to `[0,1]`"
is a true statement about this tree, and this file is where that specialization
is declared.

Extracted 2026-08-27 from `Foundations/Basic.lean`, which mixed the shared
Mathlib import block with the domain definitions. Names are unchanged.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Image
import Mathlib.Tactic

noncomputable section
open Set Function
open scoped Topology

namespace Sanctions

/-- The unit interval `[0,1] ⊂ ℝ` is the action / state space throughout the paper. -/
abbrev I : Set ℝ := Set.Icc (0 : ℝ) 1

@[simp] lemma mem_I_iff {x : ℝ} : x ∈ I ↔ 0 ≤ x ∧ x ≤ 1 := Set.mem_Icc

/-- The scalar state space `S = [0, 1] ⊂ ℝ`, alias for the action interval `I`.
Used throughout the formalization as the domain of value functions
`V_T, V_S : ↥S →ᵇ ℝ`. -/
abbrev S : Set ℝ := I

end Sanctions

end
