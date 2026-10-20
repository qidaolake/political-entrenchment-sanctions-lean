/-
Sanctions/Postulates/ShockedParams.lean

**`Params` + an abstract nonexpansive continuation transform — the operative
form of an atomless purification shock on the state transition.**

This is the He–Sun (JET 2017) purification device, realized at the level of
its operative consequence: a *smoothing operator* `smear` on continuation
values. Economically, the political-state transition carries idiosyncratic
noise, `x' = clipS'(F(x,s) + η)` with `η ~ κ` an atomless smooth density; the
continuation value the players carry forward is then the **expectation**
`(smear V)(y) = E_η[V(clipS'(y + η))]` rather than the point value `V(y)`.
Formally the structure carries only the transform and its nonexpansiveness;
the expectation, atomlessness and smoothing readings are properties of the
concrete kernel instance (`HeSunShockParams`), not of this structure (wording
corrected 2026-09-15, the reader's S2).

The single structural property of `smear` postulated here is
`smear_nonexpansive` — a *concrete inequality over the data* (Rule 14: no
opaque-`Prop` laundering) — which is exactly what a probability
kernel delivers (`∫κ = 1`): averaging against a probability density is
sup-norm nonexpansive (1-Lipschitz; the strict factor of the value
operators is the discount). (Atomlessness itself is the He–Sun narrative
interpretation; no proof in the tree consumes it — `∫κ = 1` is the
entire formal load.) This is what keeps the Sender/Target Bellman operators
`β_S`/`β_T`-contractions *after* the shock (the deterministic contraction is
unaffected), and it is **derivable from a concrete He–Sun kernel** (see
`HeSunShockParams`, where `smear V (y) = ∫ V(clipS'(y+η)) ∂κ` and
`smear_nonexpansive` is proved from `∫κ = 1`). The shocked Bellman fixed
points and the corner shocked equilibrium need *only* this property; the
interior shocked existence (headline row 6 through round U; retired from the
headline set in round V, 2026-09-15, the theorem unchanged) adds its own regularity and margin
hypotheses (wording corrected 2026-09-11, round Q1).

The *regularization* property the shock additionally buys — convolution
against a `C¹` density maps any bounded `V` to a **Lipschitz** function of the
state (mollifier smoothing), which upgrades the argmaxes from Hölder-½ to
Lipschitz in `V` and makes the *slaved* (policy-varying) operator a contraction
— is **not** part of this structure: it is needed only for the *interior*
(non-corner) leader case and will be introduced there as a separate
kernel-regularity property, to keep this structure minimal and kernel-derivable.

**Rule-3 status.** `smear`, with its one proof field `smear_nonexpansive`, is a
NEW assumption — the atomless shock — approved as the interior-existence
primitive on 2026-06-19. The structure asserts nothing else: no measure, no
normalisation, no linearity, no constant preservation, no smoothing (the
identity and the negation map are both nonexpansive, and so is the pointwise
positive part `V ↦ max(V, 0)`, which is nonlinear and fixes the constant one;
a probability kernel preserves constants, but nonexpansiveness alone does not
imply it, and `HeSunShockParams` is where the kernel reading is derived, not
here). The deterministic model (`Params`) is the `κ → δ₀` (Dirac)
limit and is left entirely untouched: this structure is purely additive
(`extends Params`), so no existing witness instance is affected. Interior
existence by the *Banach* route is conditional on the shock: in the
deterministic model the Hölder-½ selector obstructs a linear sensitivity
estimate from sup-norm value perturbations alone
(`Theory/Bellman/StrongConcaveHolder`), which blocks that route and the joint
lattice route (`Examples/DeterministicInteriorObstruction`); it is not a
nonexistence theorem — `Examples/NonAffineInteriorWitness` constructs a
deterministic `FeedbackStackelbergEquilibriumTop` with an interior Target
action — and the active, fully forward-looking interior-Target extension is a
separate problem (held; doc 81 §2.5). Corrected 2026-09-11 (the reader's
C01–C02): the earlier text counted "two properties" and called the
deterministic interior case "provably blocked".
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Domain.UnitIntervalProjection
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions
namespace AbstractGame

open scoped NNReal
open BoundedContinuousFunction

/-- Abbreviation for the Sender value space: bounded continuous functions on the
sanction state space `↥S`. -/
abbrev SBCF := (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)

/-- **`Params` with an abstract nonexpansive continuation transform** `smear`,
the operative form of an atomless purification shock; the probabilistic and
smoothing readings belong to the concrete kernel instance. See the module
docstring. -/
structure ShockedParams extends Params where
  /-- Shock-smoothed continuation operator: `(smear V)(y) = E_η[V(clipS'(y+η))]`. -/
  smear : SBCF → SBCF
  /-- Averaging against a probability density is sup-norm nonexpansive
  (`∫κ = 1`). Keeps the Bellman operators `β_S`/`β_T`-contractions after the
  shock. Derivable from a concrete He–Sun kernel (`HeSunShockParams`). -/
  smear_nonexpansive : ∀ V W : SBCF, dist (smear V) (smear W) ≤ dist V W

end AbstractGame
end Sanctions
