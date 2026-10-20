/-
Sanctions/Examples/HeSunShockWitness.lean

**The He–Sun kernel class is inhabited.**

## The hole this closes

`HeSunShockParams` (`Theory/Shocked/HeSunShock.lean:53`) is the model's concrete
shock layer: an economy together with an idiosyncratic state-shock kernel `κ` —
a probability measure on the shock `η`, so next period's state is
`clipS'(F(x,s) + η)`. The probability-measure condition `κ_prob` is what buys
nonexpansiveness of the smearing operator, and hence every contraction argument
above it.

Until now **the class had no inhabitant anywhere in the tree**. A search for
`HeSunShockParams` outside its defining file returned only two docstring
mentions in `Postulates/ShockedParams.lean` and a section variable in
`Theory/Shocked/HeSunShockExistence.lean`. So the smeared Bellman contraction,
`toShockedParams`, and the shocked corner equilibrium were all stated over a
class nobody had shown was non-empty — exactly the Rule-9B non-vacuity check
this project applies everywhere else.

`boxHeSunShockParams` closes that. It takes any economy `p` and any positive
width `h`, and supplies uniform noise on `[−h, h]`:
`Foundations/BoxTransfer.lean` already proves `boxNoise h` is a probability
measure for `h > 0` (`boxNoise_isProb`), which is precisely `κ_prob`.

## What this licenses — and what it does not (Rule 9A)

It licenses **exactly one sentence**: *the He–Sun kernel class is inhabited*, at
every economy and every positive box width. `heSunShockParams_nonempty` states
that and nothing more.

It does **not** license, and no reader may infer:

* **that the shocked layer's generality in `F` is witnessed.** No shocked
  theorem is discharged at this instance. Contrast
  `Examples/QuadBumpCertWitnessMS.lean`, where "generality witnessed" is backed
  by `qbCert_three_goals_generalF` actually *proving* the three goals at a
  transition refuted as affine at every weight. Nothing comparable happens here.
* **that the interior shocked existence route is inhabited.** That route needs
  strong concavity of the Target's dynamic objective, a leader-selector
  maximality condition, and a cross-difference bound supplied at the instance.
  None is supplied here, and the last of those is a standing open primitive.
* **anything about atomlessness.** The He–Sun narrative reads `κ` as atomless
  and uses that for purification. Uniform box noise happens to be atomless, but
  the structure's formal requirement is only `IsProbabilityMeasure`, and no
  proof in this development consumes atomlessness. Do not cite this witness for
  a purification claim.

## Rule 9B does not apply here

The per-witness opaque-`Prop` vacuity check has no target on this structure:
`κ` is a `Measure` and `κ_prob` is a structure, so neither is a bare `Prop`
field whose only tie to the data is its name. A probe of the form
`example : w.κ_prob = True := rfl` is ill-typed and would "fail" for the wrong
reason, proving nothing. The clause is inapplicable, not skipped.

## Rule 19

A witness, so `Examples/`. It is placed here rather than beside the structure
deliberately: `Theory/Shocked/HeSunShock.lean` runs measure-theoretic instance
search, and `boxNoise_isProb` is an `instance` carrying an un-synthesizable
hypothesis `0 < h`, so importing `BoxTransfer` there would add a
never-applicable instance to that search. Keeping the witness in `Examples/`
costs nothing and leaves the `Theory/` import graph untouched.
-/

import Sanctions.Theory.Shocked.HeSunShock
import Sanctions.Foundations.BoxTransfer

namespace Sanctions.Examples

open Sanctions Sanctions.AbstractGame

/-- **The He–Sun kernel class, inhabited at uniform box noise.**

Any economy `p`, any positive width `h`: take the shock to be uniform on
`[−h, h]`. The probability-measure obligation is discharged by
`Sanctions.boxNoise_isProb`. -/
noncomputable def boxHeSunShockParams (p : Sanctions.AbstractGame.Params)
    {h : ℝ} (hh : 0 < h) : Sanctions.AbstractGame.HeSunShockParams where
  toParams := p
  κ := Sanctions.boxNoise h
  κ_prob := Sanctions.boxNoise_isProb h hh

/-- **The non-vacuity statement.** The He–Sun kernel class is not empty. -/
theorem heSunShockParams_nonempty (p : Sanctions.AbstractGame.Params) :
    Nonempty Sanctions.AbstractGame.HeSunShockParams :=
  ⟨boxHeSunShockParams p one_pos⟩

/-- The underlying economy is the one supplied — the witness adds a shock and
changes nothing else. -/
theorem boxHeSunShockParams_toParams (p : Sanctions.AbstractGame.Params)
    {h : ℝ} (hh : 0 < h) :
    (boxHeSunShockParams p hh).toParams = p := rfl

end Sanctions.Examples
