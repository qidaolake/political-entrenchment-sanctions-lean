/-
Sanctions/Examples/CoupledRoute/LowDeltaLocalBranches.lean

Exact complete-square identities for the interior branch of the low-delta
coupled problem.

The constants `cS`, `cT` are affine-continuation intercepts and `dS`, `dT`
are affine-continuation slopes.  This file does not claim that an equilibrium
continuation is affine, that either displayed vertex is feasible, or that the
interior branch is selected.  It records only algebraic consequences of the
already-defined low-delta primitives, for later use inside a branch-separated
local certificate.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaWindowWitness

namespace Sanctions
namespace Examples

/-! ## Affine-continuation reductions -/

/-- An affine continuation with intercept `c` and slope `d`. -/
noncomputable def lowDeltaAffineContinuation (c d y : ℝ) : ℝ :=
  c + d * y

/-- The low-delta Sender objective on a no-clipping branch when its smeared
continuation is the affine function `cS + dS * y`. -/
noncomputable def lowDeltaSenderAffineObjective
    (cS dS x a s : ℝ) : ℝ :=
  lowDeltaParams.U_S x a s
    + lowDeltaParams.β_S
      * lowDeltaAffineContinuation cS dS (lowDeltaParams.F x s)

/-- The unconstrained Sender vertex under affine continuation slope `dS`. -/
noncomputable def lowDeltaSenderInteriorVertex (dS x a : ℝ) : ℝ :=
  (9 / 8) * x - 1 / 12 - (5 / 12) * a + dS / 240

/-- The part of the affine-continuation Sender vertex independent of the
Target action. -/
noncomputable def lowDeltaSenderInteriorBase (dS x : ℝ) : ℝ :=
  (9 / 8) * x - 1 / 12 + dS / 240

/-- Target action at which the affine-continuation Sender vertex reaches
zero. -/
noncomputable def lowDeltaSenderZeroBoundary (dS x : ℝ) : ℝ :=
  (12 / 5) * lowDeltaSenderInteriorBase dS x

/-- Target action at which the affine-continuation Sender vertex reaches
one. -/
noncomputable def lowDeltaSenderOneBoundary (dS x : ℝ) : ℝ :=
  (12 / 5) * (lowDeltaSenderInteriorBase dS x - 1)

/-- Exact weak branch condition: the unconstrained Sender vertex is feasible
exactly between the two Target-action thresholds. -/
theorem lowDelta_senderInteriorVertex_mem_Icc_iff (dS x a : ℝ) :
    lowDeltaSenderInteriorVertex dS x a ∈ Set.Icc 0 1 ↔
      a ∈ Set.Icc
        (lowDeltaSenderOneBoundary dS x)
        (lowDeltaSenderZeroBoundary dS x) := by
  simp only [Set.mem_Icc, lowDeltaSenderInteriorVertex,
    lowDeltaSenderOneBoundary, lowDeltaSenderZeroBoundary,
    lowDeltaSenderInteriorBase]
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith

/-- Exact strict branch condition used by a branch-separated local
certificate. -/
theorem lowDelta_senderInteriorVertex_mem_Ioo_iff (dS x a : ℝ) :
    lowDeltaSenderInteriorVertex dS x a ∈ Set.Ioo 0 1 ↔
      a ∈ Set.Ioo
        (lowDeltaSenderOneBoundary dS x)
        (lowDeltaSenderZeroBoundary dS x) := by
  simp only [Set.mem_Ioo, lowDeltaSenderInteriorVertex,
    lowDeltaSenderOneBoundary, lowDeltaSenderZeroBoundary,
    lowDeltaSenderInteriorBase]
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith

/-- Exact Sender complete-square identity.  The affine continuation intercept
cancels, while its slope shifts the static vertex by `dS / 240`. -/
theorem lowDelta_senderAffineObjective_gap (cS dS x a s : ℝ) :
    lowDeltaSenderAffineObjective cS dS x a
        (lowDeltaSenderInteriorVertex dS x a)
      - lowDeltaSenderAffineObjective cS dS x a s
        = (3 / 5) * (s - lowDeltaSenderInteriorVertex dS x a) ^ 2 := by
  simp only [lowDeltaSenderAffineObjective, lowDeltaAffineContinuation,
    lowDeltaSenderInteriorVertex, lowDeltaParams_U_S, lowDeltaParams_β_S,
    lowDeltaParams_F, mwU_S, Sanctions.AbstractGame.affineF]
  ring

/-- The low-delta Target objective after substituting the interior Sender
vertex, when the Target's smeared continuation is `cT + dT * y`. -/
noncomputable def lowDeltaTargetAffineObjective
    (cT dS dT x a : ℝ) : ℝ :=
  let s := lowDeltaSenderInteriorVertex dS x a
  lowDeltaParams.U_T x a s
    + lowDeltaParams.β_T
      * lowDeltaAffineContinuation cT dT (lowDeltaParams.F x s)

/-- The unconstrained Target vertex after substituting the interior Sender
response. -/
noncomputable def lowDeltaTargetInteriorVertex (dS dT x : ℝ) : ℝ :=
  (103 / 116) * x - 10 / 29 + dS / 1160 - (9 * dT) / 5800

/-- Exact Target complete-square identity after substituting the realized
interior Sender response.  The induced curvature is `29 / 24`. -/
theorem lowDelta_targetAffineObjective_gap (cT dS dT x a : ℝ) :
    lowDeltaTargetAffineObjective cT dS dT x
        (lowDeltaTargetInteriorVertex dS dT x)
      - lowDeltaTargetAffineObjective cT dS dT x a
        = (29 / 24) * (a - lowDeltaTargetInteriorVertex dS dT x) ^ 2 := by
  simp only [lowDeltaTargetAffineObjective, lowDeltaAffineContinuation,
    lowDeltaTargetInteriorVertex, lowDeltaSenderInteriorVertex,
    lowDeltaParams_U_T, lowDeltaParams_β_T, lowDeltaParams_F,
    mwU_T, Sanctions.AbstractGame.affineF]
  ring

end Examples
end Sanctions
