/-
Sanctions/Examples/OffCornerNonVacuity.lean

**Rule 9 evidence for the off-corner conditions.**

`Theory/LockIn/OffCornerResponse.lean` places every dynamic Sender maximizer
strictly between the state and the top, given two conditions on the complete
Sender objective. Those conditions are **not** a weakening of the corner route
that the broad persistence family uses — they are incompatible with it. If the
Sender's stage payoff is maximized at `s = 1` and the continuation is monotone,
as `σ_dyn_top_V_S_zero_eq_one_of_monotone` requires, then nothing interior can
beat `1` and `SenderInteriorBeatsBoundariesAt` is false.

So the off-corner theorem describes a *disjoint* region of the parameter space,
and without evidence that the region is inhabited it would be a theorem about
nothing. This file supplies that evidence at `niParams`, whose transition is
genuinely non-affine, so the class is certified inhabited **outside** the affine
case as well (Rule 9B).

## What this witness does and does not show

It shows the conditions are satisfiable at a constructed equilibrium, with an
interior rule `R x = (x+1)/2` — strictly above the state and strictly below one
at every state below one, and equal to one at the top, which is the shape the
theorem predicts and which no floor could avoid.

It does **not** exhibit the economic mechanism. Both of this economy's
equilibrium value functions are identically zero (`niV0 = 0`), so the
continuation channel contributes nothing and the interiority here comes entirely
from the curvature of the stage payoff around its ideal sanction. Per Rule 9A a
witness never supports a mechanism claim, and this one is not even positioned to
suggest one. The economy whose continuation channel is load-bearing is
`ceParams` in `Examples/ContinuationDrivenEscalation.lean`; its closed loop rests
at an interior state rather than climbing to the top, so it belongs to the
crossing theorem rather than this one.
-/

import Sanctions.Examples.NonAffineInteriorWitness
import Sanctions.Theory.LockIn.OffCornerResponse

namespace Sanctions
namespace Examples

open Set AbstractGame AbstractGame.Params

noncomputable section

/-- With the zero continuation, the Sender's complete objective is the stage
payoff alone: a strictly concave loss around the ideal sanction. -/
theorem ni_objective_eq (x a s : ℝ) :
    niParams.U_S x a s
        + niParams.β_S * niV0 (Sanctions.clipS' (niParams.F x s))
      = -(s - niIdeal x a) ^ 2 := by
  simp [niV0, niParams, niU_S]

/-- **Nothing at or below the state beats freezing.**

The ideal sanction sits strictly above the state, so moving down from the state
only moves further from the ideal, and a concave loss falls. -/
theorem ni_senderAboveDiagonal {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    niParams.SenderAboveDiagonalAt niV0 x (1 / 2) := by
  intro s _ hsx
  rw [ni_objective_eq, ni_objective_eq, niIdeal_at_half]
  have hxle : x ≤ (x + 1) / 2 := by linarith [hx.2]
  nlinarith [sq_nonneg (s - (x + 1) / 2), sq_nonneg (x - (x + 1) / 2)]

/-- **An interior sanction beats both freezing and maximum pressure.**

The ideal `(x+1)/2` is feasible and interior for every state below one, and it is
the unique global maximizer of a strictly concave loss, so it strictly beats both
endpoints. -/
theorem ni_senderInteriorBeatsBoundaries {x : ℝ} (hx1 : x < 1) :
    niParams.SenderInteriorBeatsBoundariesAt niV0 x (1 / 2) := by
  refine ⟨(x + 1) / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩ <;>
    rw [ni_objective_eq, ni_objective_eq, niIdeal_at_half] <;> nlinarith

/-- **Every dynamic maximizer is strictly interior**, at every state below the
top. No selection is used: the conclusion is about the argmax set. -/
theorem ni_every_argmax_mem_Ioo {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    {s : ℝ} (hs : s ∈ niParams.dynamicArgmaxSet niV0 x (1 / 2)) :
    s ∈ Ioo x 1 :=
  niParams.every_dynamic_argmax_mem_Ioo_self_one
    ⟨hx0, le_of_lt hx1⟩
    (ni_senderAboveDiagonal ⟨hx0, le_of_lt hx1⟩)
    (ni_senderInteriorBeatsBoundaries hx1) hs

/-- **The class is inhabited.** The two off-corner conditions hold simultaneously
at a constructed equilibrium of an economy with a non-affine transition. -/
theorem offCorner_conditions_nonvacuous :
    ∃ (p : AbstractGame.Params) (V_S : Val) (x a : ℝ),
      p.SenderAboveDiagonalAt V_S x a ∧ p.SenderInteriorBeatsBoundariesAt V_S x a :=
  ⟨niParams, niV0, 1 / 2, 1 / 2,
    ni_senderAboveDiagonal (by constructor <;> norm_num),
    ni_senderInteriorBeatsBoundaries (by norm_num)⟩

end

end Examples
end Sanctions
