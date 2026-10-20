/-
Sanctions/Examples/KaempferLowenbergContestWitness.lean

Concrete non-vacuity for the parametric Becker-contest microfoundation in
`Theory/Microfoundations/KaempferLowenbergContest.lean`. Keeping this
instantiation in `Examples/` preserves the package boundary

  Foundations → Postulates → Theory → Examples.

No declaration names changed when the witness moved here.
-/

import Sanctions.Theory.Microfoundations.KaempferLowenbergContest
import Sanctions.Examples.FourGroupWitness
-- `toPolity_inducedF_eq_affineF`.
import Sanctions.Examples.AffineInstance.Microfoundations

namespace Sanctions
namespace KaempferLowenberg

/-! ### Non-vacuity: the contest layer at the canonical four-group witness -/

/-- **Concrete contest witness** on top of `Examples.fourGroupWitness`
(th0_JT = 1, ρ = 6/5, b_J = 1, th0_KT = 1, μ = 3/10, b_K = 1) with contest
primitives `cp_J = cp_K = 1/2`, `iota_J = 0`, `iota_K = 1/10`. Exact values:
`p_J*(s) = 1 + (6/5)s`, `p_K*(s) = 1 + (1/5)s`, `beta1 = 1`, `beta0 = 0`,
`x*(s) = s`; (h1): `3/20 < 3/5`; (h2): `0 ≤ 1/20`
(verified in `docs/archive/workflow-scratch/w2_p10_contest_verify.py`, 30/30 exact checks).
Since BH6.2 (2026-10-07) the contest layer reads only the witness's coefficients
(`fourGroupWitness.toCoeffs`), not its region-(R) fields. -/
noncomputable def contestWitness : ContestPolity where
  toFourGroupCoeffs := Sanctions.Examples.fourGroupWitness.toCoeffs
  cp_J := 1 / 2
  cp_K := 1 / 2
  iota_J := 0
  iota_K := 1 / 10
  cp_J_pos := by norm_num
  cp_K_pos := by norm_num
  stakeJ_nn0 := by norm_num [Sanctions.Examples.fourGroupWitness]
  stakeJ_nn1 := by norm_num [Sanctions.Examples.fourGroupWitness]
  stakeK_nn0 := by norm_num [Sanctions.Examples.fourGroupWitness]
  stakeK_nn1 := by norm_num [Sanctions.Examples.fourGroupWitness]
  contestRally_dom := by norm_num [Sanctions.Examples.fourGroupWitness]
  incid_favors_J := by norm_num [Sanctions.Examples.fourGroupWitness]

/-- The witness's derived clearing slope is exactly `1` (`6/5 − 3/10 + 1/10`). -/
theorem contestWitness_beta1 : contestWitness.beta1 = 1 := by
  simp only [ContestPolity.beta1, contestWitness, FourGroup.toCoeffs,
    Sanctions.Examples.fourGroupWitness]
  norm_num

/-- The witness's derived clearing intercept is exactly `0`. -/
theorem contestWitness_beta0 : contestWitness.beta0 = 0 := by
  simp only [ContestPolity.beta0, contestWitness, FourGroup.toCoeffs,
    Sanctions.Examples.fourGroupWitness]
  norm_num

/-- **Non-vacuity of the derived lock-in**: the contest-microfounded polity at
the four-group witness is in the lock-in regime (one-line corollary of the
parametric machinery, Rule 5). -/
theorem contestWitness_lockIn : contestWitness.toPolity.LockIn :=
  contestWitness.toPolity_lockIn

/-- **The existing witness transition is contest-microfounded**: at `δ = 1/5`
the induced transition of the contest witness IS the affine law used by
`Examples.fourGroupWitnessParams` — zero change downstream. -/
theorem contestWitness_inducedF_eq_affineF :
    contestWitness.toPolity.inducedF (1 / 5)
      = Sanctions.AbstractGame.affineF (1 / 5) :=
  contestWitness.toPolity_inducedF_eq_affineF _

end KaempferLowenberg
end Sanctions
