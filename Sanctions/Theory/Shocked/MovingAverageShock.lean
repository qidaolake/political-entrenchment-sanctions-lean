/-
Sanctions/Theory/Shocked/MovingAverageShock.lean

**The parametric moving-average (uniform box-kernel) box-smear wiring layer,
and the `L_smVT` closed form.**

`Foundations/MovingAverage.lean` proves the moving-average smoothing operator
`movAvgBCF h` is nonexpansive (`movAvgBCF_dist_le`), linear (`movAvgBCF_sub`),
and state-Lipschitz with constant `‖V‖/h` (`movAvgBCF_lipschitz_state`) — but
nothing installed it as an actual `ShockedParams.smear`, so (a) the box kernel
was orphaned relative to every shocked theorem and (b) the `ShockedParams` class
had **no concrete witness**, leaving every shocked existence theorem conditional
on a possibly-empty class (a Rule-9 vacuity exposure: one cannot rule out
`example : False` from the hypotheses without an exhibited instance).

This file closes gap (a): it is the **parametric box-smear wiring layer**.

* `movAvgShockedParams p hh` realises the box smear as a genuine `ShockedParams`
  over any base `Params p` (parametric, Rule 5); its `smear_nonexpansive` field
  is the `∫κ = 1` property of the uniform density on `[-h,h]`.
* `movAvgShockedParams_smear_lipschitz` records that the box smear's
  state-Lipschitz constant is the **closed form** `‖V‖/h`. This is exactly the
  `hsmVT_lip` regularity (the `L_smVT` constant) consumed by
  `VTdyn_shock_lipschitz`, now supplied for free as a strict expression in
  existing quantities (`‖V‖`, the window `h`) rather than a new named primitive
  (Rule-3 symbol-economy clause).

Gap (b) is closed by the **concrete witness** `eatonEngersMovAvgShock` — the
Eaton-Engers witness shocked by the uniform kernel — which lives in
`Sanctions/Examples/MechanismWitnessShocked.lean`: it instantiates this file's
parametric constructor at an `Examples/` parameter point, so that the Theory
layer never imports `Examples/` (layering discipline).

This is the wiring layer for the general `Foundations/MovingAverage.lean`
machinery (Rule 19): the analytic content lives in `Foundations/`; here it is
specialised to a `Params`-level `ShockedParams`.
-/
import Sanctions.Foundations.MovingAverage
import Sanctions.Postulates.ShockedParams

namespace Sanctions
namespace AbstractGame

open BoundedContinuousFunction

noncomputable section

/-- **The moving-average (uniform box-kernel) shock as a concrete `ShockedParams`**
over any base `Params`. The smear is `movAvgBCF h`, whose sup-norm
nonexpansiveness (`movAvgBCF_dist_le`) is the `∫κ = 1` property of the uniform
density on `[-h,h]`. This realises the He–Sun atomless purification shock from a
genuine (uniform, atomless) kernel — no postulated `smear`. -/
def movAvgShockedParams (p : Params) {h : ℝ} (hh : 0 < h) : ShockedParams where
  toParams := p
  smear := Sanctions.movAvgBCF hh
  smear_nonexpansive := Sanctions.movAvgBCF_dist_le hh

@[simp] theorem movAvgShockedParams_smear (p : Params) {h : ℝ} (hh : 0 < h) :
    (movAvgShockedParams p hh).smear = Sanctions.movAvgBCF hh := rfl

@[simp] theorem movAvgShockedParams_toParams (p : Params) {h : ℝ} (hh : 0 < h) :
    (movAvgShockedParams p hh).toParams = p := rfl

/-- **`L_smVT` closed form.** The box smear is state-Lipschitz with the closed-form
constant `‖V‖/h` (no new named primitive). This is exactly the `hsmVT_lip`
hypothesis consumed by `VTdyn_shock_lipschitz`, here supplied for free at the
concrete kernel. -/
theorem movAvgShockedParams_smear_lipschitz (p : Params) {h : ℝ} (hh : 0 < h)
    (V : SBCF) (z z' : ↥(Sanctions.S : Set ℝ)) :
    |(movAvgShockedParams p hh).smear V z - (movAvgShockedParams p hh).smear V z'|
      ≤ (‖V‖ / h) * dist z z' := by
  simp only [movAvgShockedParams_smear]
  exact Sanctions.movAvgBCF_lipschitz_state hh V z z'

/-- **Linearity of the box smear** (`sm_sub`), at the concrete kernel. Needed so the
objective *difference* inherits a Lipschitz constant `∝ ‖V-W‖`. -/
theorem movAvgShockedParams_smear_sub (p : Params) {h : ℝ} (hh : 0 < h) (V W : SBCF) :
    (movAvgShockedParams p hh).smear (V - W)
      = (movAvgShockedParams p hh).smear V - (movAvgShockedParams p hh).smear W := by
  simp only [movAvgShockedParams_smear]
  exact Sanctions.movAvgBCF_sub hh V W

end -- noncomputable section
end AbstractGame
end Sanctions
