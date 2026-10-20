/-
Sanctions/Theory/Bellman/LipschitzPrimitives.lean

**Carrier-restricted Lipschitz primitives for σ_dyn and α_on.**

Closes the architectural part of audit-33 Gaps 2 + 3 remainders by
introducing two theorem-parameter primitives that capture, at the
abstract layer, the IFT-derived Lipschitz constants the row-Lipschitz
chain consumes:

* **`SigmaDynLipschitzOn D L_σ`** — the dynamic Sender argmax
  `σ_dyn V_S x a` is `L_σ`-Lipschitz in `V_S` *on the value-class
  carrier* (sup-norm distance).

* **`AlphaOnLipschitzOn D L_α_VT L_α_VS`** — the carrier-restricted
  leader selector `D.α_on V W x` is jointly `(L_α_VT, L_α_VS)`-
  Lipschitz in `(V_T, V_S) ∈ D.Carrier × D.Carrier`.

Both are stated on the single-carrier `ValueClass` and at every real state
(and action). Their **two-carrier, feasible-state forms**
`ValueClass2.SigmaDynLipschitzOn` and `ValueClass2.AlphaOnLipschitzOn`
(round BH1.2, 2026-10-06) ask for the same bounds only over the carrier each
value lives in and only at feasible states `x ∈ S` (and actions `a ∈ I`),
which is all the operator row bounds ever read. Each single-carrier form
implies the two-carrier one at the homogeneous bridge
`ValueClass.toValueClass2`.

## Why these are taken as primitives (Rule-3 register entry)

Substantive derivation of both Props from primitive payoff
regularity (uniform strict concavity + smoothness) requires
mathlib's implicit function theorem in a smooth-function subspace of
`Val = ↥S →ᵇ ℝ`. Concretely:

* **σ_dyn-Lipschitz needs differentiability of V_S in `s`** to apply
  the standard IFT-via-FOC argument
  (`c |σ - σ'| ≤ L_grad · dist V_S V_S'` where `L_grad` bounds the
  V_S-induced change in `∂f/∂s`). For general BCF `V_S` (just
  bounded continuous), σ_dyn is only **Hölder-1/2** in V_S, NOT
  Lipschitz; Lipschitz fails on the BCF space and requires a smooth
  subspace (e.g. `C¹` on `↥S`).

* **C¹ on `↥S` is not closed in the BCF sup-norm topology**, so
  building a `ValueClass.carrier` inside C¹ would break the
  `isClosed` field's role in `IsClosed.completeSpace_coe`. A
  Rule-1-compliant derivation therefore requires a parallel layer
  with the C¹ norm replacing the BCF sup-norm throughout — a
  multi-month mathlib infrastructure project.

The two Props are taken at this layer as **theorem-parameter
primitives** (no `Params` fields, no Postulates). At a future
concrete payoff class (quadratic-quadratic, LQ, etc.), the Lipschitz
constants are computed by direct calculation, discharging the Props
without any IFT machinery.

## Rule compliance

**Rule 1.** σ_dyn and α_on are equilibrium-derived (the Sender
forward-looking argmax and the leader joint-Bellman argmax,
respectively). The Lipschitz Props are *quantitative regularity*
statements about these equilibrium objects, not strategy
re-definitions.

**Rule 3.** Both Props are category-(3) per the audit's register —
new structural Props taken as input to load-bearing theorems.
Confirmed by the user's "substantive closure" choice (revised to
the only Rule-1-compliant deliverable: architectural closure adding
exactly these two Props).

**Rule 5.** Fully parametric over `(p, D)`.
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Bellman.InvariantValueClass2

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## `SigmaDynLipschitzOn`: σ_dyn-Lipschitz-in-V_S on the carrier -/

/-- **Carrier-restricted Lipschitz primitive for `σ_dyn` in V_S.**
The forward-looking Sender argmax `σ_dyn V_S x a` is `L_σ`-Lipschitz
in `V_S` when `V_S` is restricted to the value-class carrier
`D.carrier`. The distance on the left is the absolute value (since
`σ_dyn` is real-valued); the distance on the right is the inherited
subtype metric (= BCF sup-norm between `V_S.val` and `V_S'.val`).

**Discharge** (deferred): at any concrete payoff class with strictly
concave `U_S` in `s`, smooth in `(x, s)`, and `V_S` restricted to a
differentiable subspace, this constant is computed via the IFT-at-FOC
argument with `L_σ = (β_S · δ · L_d) / c` where `c` is the
uniform strict-concavity modulus and `L_d` is the V_S-induced
sensitivity of the FOC. -/
def SigmaDynLipschitzOn (D : p.ValueClass) (L_σ : ℝ) : Prop :=
  ∀ V_S V_S' : D.Carrier, ∀ x a : ℝ,
    |p.σ_dyn V_S.val x a - p.σ_dyn V_S'.val x a| ≤ L_σ * dist V_S V_S'

/-! ## `AlphaOnLipschitzOn`: α_on-Lipschitz-in-(V_T, V_S) on the carrier -/

/-- **Carrier-restricted Lipschitz primitive for the leader selector
`α_on`.** The leader joint-Bellman argmax `α_on V_T V_S x` is jointly
`(L_α_VT, L_α_VS)`-Lipschitz in `(V_T, V_S) ∈ D.Carrier × D.Carrier`.

**Discharge** (deferred): under uniform strict concavity of the
leader joint-Bellman integrand in the leader action `a`, mediated by
the same IFT-at-FOC argument as for `SigmaDynLipschitzOn`. The
constants `L_α_VT, L_α_VS` decompose as the V_T- and V_S-induced
sensitivities of the leader FOC. -/
def AlphaOnLipschitzOn (D : p.ValueClass) (L_α_VT L_α_VS : ℝ) : Prop :=
  ∀ V_T V_T' V_S V_S' : D.Carrier, ∀ x : ℝ,
    |D.α_on V_T V_S x - D.α_on V_T' V_S' x|
      ≤ L_α_VT * dist V_T V_T' + L_α_VS * dist V_S V_S'

/-! ## Two-carrier forms on `ValueClass2` (round BH1.2, 2026-10-06)

The two predicates above make every value obey one carrier and quantify over
every real state `x` (and, for `σ_dyn`, every real action `a`). The operator
row bounds read them only at a feasible state `x ∈ S` and a feasible Target
action `a ∈ I`, and only for a Sender value in the Sender carrier (for `σ_dyn`)
or a value pair in `carrier_T × carrier_S` (for `α_on`). The forms below say
exactly that, on the asymmetric class `ValueClass2`. Both are general in `F`:
the transition enters only through the Bellman objects of `p`. -/

namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-- **`σ_dyn` Lipschitz in `V_S` over the Sender carrier, at feasible states
and actions (round BH1.2, 2026-10-06).** For Sender values `V_S, V_S'` in
`carrier_S`, a feasible state `x ∈ S` and a feasible Target action `a ∈ I`, the
Sender's forward-looking best response moves by at most `L_σ` times the
sup-norm distance between the two values.

Plain language: a small change in the Sender's continuation value moves the
sanction it picks only a little, and this is asked only where the model lives.
Compared with the single-carrier `SigmaDynLipschitzOn`, it drops the bound at
infeasible states and actions, and the Sender carrier it ranges over need not
be the Target's. General in `F`. -/
def SigmaDynLipschitzOn (L_σ : ℝ) : Prop :=
  ∀ V_S V_S' : D.CarrierS, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
    |p.σ_dyn V_S.val x a - p.σ_dyn V_S'.val x a| ≤ L_σ * dist V_S V_S'

/-- **The leader selector Lipschitz in `(V_T, V_S)` over
`carrier_T × carrier_S`, at feasible states (round BH1.2, 2026-10-06).** For
Target values in `carrier_T`, Sender values in `carrier_S` and a feasible state
`x ∈ S`, the carrier selector `D.α_on` moves by at most `L_α_VT` times the
Target-value distance plus `L_α_VS` times the Sender-value distance.

Plain language: the Target's compliance choice responds smoothly to both
governments' continuation values. Compared with the single-carrier
`AlphaOnLipschitzOn`, the two values may live in different carriers and the
bound is asked only at feasible states. General in `F`. -/
def AlphaOnLipschitzOn (L_α_VT L_α_VS : ℝ) : Prop :=
  ∀ (V_T V_T' : D.CarrierT) (V_S V_S' : D.CarrierS), ∀ x ∈ Sanctions.S,
    |D.α_on V_T V_S x - D.α_on V_T' V_S' x|
      ≤ L_α_VT * dist V_T V_T' + L_α_VS * dist V_S V_S'

end ValueClass2

section ToValueClass2

variable {p}

/-- **The single-carrier `σ_dyn` primitive gives the two-carrier one (round
BH1.2, 2026-10-06).** At the homogeneous bridge `D.toValueClass2` both carriers
are `D.carrier`, and restricting the bound to feasible states and actions only
weakens it. General in `F`. -/
theorem SigmaDynLipschitzOn.toValueClass2 {D : p.ValueClass} {L_σ : ℝ}
    (h : p.SigmaDynLipschitzOn D L_σ) :
    D.toValueClass2.SigmaDynLipschitzOn L_σ :=
  fun V_S V_S' x _ a _ => h V_S V_S' x a

/-- **The single-carrier leader-selector primitive gives the two-carrier one
(round BH1.2, 2026-10-06).** Same transport as
`SigmaDynLipschitzOn.toValueClass2`: the selectors of `D` and
`D.toValueClass2` agree by definition, and the bound is only restricted to
feasible states. General in `F`. -/
theorem AlphaOnLipschitzOn.toValueClass2 {D : p.ValueClass}
    {L_α_VT L_α_VS : ℝ} (h : p.AlphaOnLipschitzOn D L_α_VT L_α_VS) :
    D.toValueClass2.AlphaOnLipschitzOn L_α_VT L_α_VS :=
  fun V_T V_T' V_S V_S' x _ => h V_T V_T' V_S V_S' x

end ToValueClass2

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
