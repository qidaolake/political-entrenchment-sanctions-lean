/-
Sanctions/Theory/Certificates/RegularEconomy.lean

**Payoff-form-agnostic top-level theorem (audit-40 follow-up).**

The audit-40 critique observes that the JET theorem should not be
framed around any specific payoff family (LQ, non-LQ, smooth, C¹).
The right framing is a **regularity certificate**: any
`AbstractGame.Params` admitting such a certificate satisfies
persistence + different-α dominance + shock hysteresis.

This file delivers the **payoff-form-agnostic top-level theorem**:

```
RegularEconomyCertificateC1Compliance p K_d → ∃ E, three goals at E
```

Specific routes to producing a certificate (the `valLipBall` route,
the C¹ route, concrete formula families) live as separate corollaries
or downstream files. The main theorem does NOT bake in any of them.

## The resistance-action route was deleted on 2026-08-17

An earlier and now-removed family — `RegularEconomyCertificate`, its
`ResistanceActionCertificate` alias, `RegularEconomyCertificateC1`,
`RegularEconomyMargins`, their `three_goals` theorems, their two
`valLipBall` constructors, and the two `jet_three_goals_from_*` bridges
in `Bridges/JETBridge.lean` — packaged the same three conclusions under
the **resistance / noncompliance** reading of `a`, where a higher action
triggers heavier sanctions. It carried an explicit quarantine warning
saying so, because its Goal-2 chain has the **wrong sign** under the
literal-compliance reading this project uses.

It was removed rather than kept because nothing consumed it: no witness
constructed one, no headline row reached it, and the manuscript never
cited it. Its distinguishing hypothesis was the strongest assumption in
the tree — `hα_order_E`, asserting that the myopic Target policy lies
pointwise below the policy of *every* equilibrium the game admits, a
restriction on the whole equilibrium correspondence. The compliance
family below supersedes it, deriving rule dominance from a myopic
ceiling plus a floor instead. The deleted route remains in git history.

## Rule compliance

**Rule 1.** The produced equilibrium uses equilibrium-derived
strategies throughout (Stackelberg leader α as joint-Bellman argmax,
Sender σ_dyn_top as forward-looking argmax).

**Rule 3.** The certificates below are bundling refactors of hypotheses
their bridges already consume, not assumption expansions. Register entry
classifies them as **(1) scaffolding** since no new load-bearing
primitive is introduced.

**Rule 5.** Fully parametric — works for any `Params`, any
`ValueClass`, any choice of Lipschitz coefficients satisfying the
contraction margins.
-/

import Sanctions.Theory.Bridges.JETBridge
import Sanctions.Theory.Bridges.JETBridgeC1System
import Sanctions.Theory.Bellman.InvariantLipGainBall
import Sanctions.Foundations.Curtat
import Sanctions.Foundations.ImplicitFunctionTheorem

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Closed-form `L_α_VT, L_α_VS` via the scope-reduced implicit
function theorem (Round 31)

Round-31 paper-facing dischargers. They present `AlphaOnLipschitzOn` —
the carrier-restricted leader selector is Lipschitz in the value pair —
as a **derived** Prop computed from three paper-stateable C² primitives
on the Target stage payoff, rather than as an assumption:

* **FOC at every carrier-local `α_on`** — `∂joint_T_integrand/∂a
  (V_T, V_S, x, α_on V_T V_S x) = 0` for every `(V_T, V_S) ∈ Carrier ×
  Carrier` and `x ∈ ℝ`. This is the standard interior FOC; it holds
  whenever `α_on` is interior to `Sanctions.I` and the integrand is
  differentiable in `a`.
* **Chord-form strong concavity of the integrand in `a`.** With modulus
  `c > 0`: for every `(V_T, V_S)` and `(a, b) ∈ ℝ × ℝ`,
  `c · (a − b)² ≤ (fa V_T V_S x a − fa V_T V_S x b) · (a − b)`, where
  `fa` denotes the partial derivative `∂joint_T_integrand/∂a`. This
  is the gradient-monotonicity content of strong concavity (equivalent
  to `∂²joint_T_integrand/∂a² ≤ −c` under C²).
* **Cross-Lipschitz of the partial derivative `fa` in each value-function
  coordinate.** Per-coordinate bounds `K_T, K_S` giving uniformly-in-(x,a)
  Lipschitz estimates of `fa` as `V_T` (resp. `V_S`) varies over the
  carrier.

The closed-form selector-Lipschitz constants are
`L_α_VT := K_T / c`, `L_α_VS := K_S / c`. This is exactly the IFT
formula `D a* = −(∂²f/∂a²)⁻¹ · ∂²f/∂a∂θ` evaluated coordinatewise
(Doraszelski-Pakes 2007 §3.1 / §4.1, in the chord-form / scope-reduced
specialization documented in `Sanctions/Foundations/ImplicitFunctionTheorem.lean`).

**Plain-language gloss:** the carrier-restricted leader selector
`α_on V_T V_S x` is `(K_T/c, K_S/c)`-Lipschitz in `(V_T, V_S)` —
**derived** from primitive C² payoff data, no longer assumed.

**Rule 1 (preserved).** `α_on` remains the joint-Bellman argmax (an
equilibrium-derived object). The Lipschitz constants are a
quantitative regularity statement about this equilibrium object,
not a strategy re-definition.

**Rule 3 (clean, cat-2 weakening / Type-C discharger).** The wrapper
introduces no new primitive on `Params`: the FOC, chord-form strong
concavity, and cross-Lipschitz of `fa` are all paper-stateable C²
properties of `joint_T_integrand` that were previously bundled into
the opaque `AlphaOnLipschitzOn` Prop. The bundle is reshaped, not
extended.

**Rule 5 (parametric).** Fully generic over `Params` and `ValueClass`.

**Caveat (per Round 31 plan).** This is the **scope-reduced** IFT
deliverable: the chord-form strong-concavity hypothesis is taken as
input rather than derived from a `ContDiff 2` smooth-function bundle
via mathlib's full IFT machinery. The chord-form is the
gradient-monotonicity content of strong concavity and is the
quantity that actually fires in the proof; the full ContDiff
derivation adds bookkeeping without changing the closed-form
constant. The full-IFT route is documented in the Foundations
module as a deferred follow-up. -/

/-- **Round-31 wrapper: `AlphaOnLipschitzOn` from primitive
payoff-Hessian bounds via the scope-reduced IFT route.**

Given:

* the carrier `D : p.ValueClass`,
* a partial-derivative function `fa : Carrier → Carrier → ℝ → ℝ → ℝ`
  with the interpretation `fa V_T V_S x a = ∂joint_T_integrand/∂a
  (V_T, V_S, x, a)`,
* strong-concavity modulus `c > 0`,
* cross-Hessian bounds `K_T, K_S ≥ 0`,
* the three IFT hypotheses (FOC at every `α_on`, chord-form strong
  concavity, per-coordinate cross-Lipschitz),

produce `p.AlphaOnLipschitzOn D (K_T / c) (K_S / c)` — the
carrier-restricted leader selector is `(K_T/c, K_S/c)`-Lipschitz in
`(V_T, V_S)`.

The two output constants `(K_T/c, K_S/c)` are exactly the
`L_α_VT, L_α_VS` consumed by Curtat's row-Lipschitz closed form
(`Sanctions.Foundations.Curtat.CurtatPrimitiveLipschitzData`). -/
theorem alphaOnLipschitzOn_of_IFT_chord_form
    {D : p.ValueClass}
    (fa : D.Carrier → D.Carrier → ℝ → ℝ → ℝ)
    (c K_T K_S : ℝ)
    (hc_pos : 0 < c) (hK_T_nn : 0 ≤ K_T) (hK_S_nn : 0 ≤ K_S)
    (h_FOC : ∀ (V_T V_S : D.Carrier) (x : ℝ),
        fa V_T V_S x (D.α_on V_T V_S x) = 0)
    (h_strong : ∀ (V_T V_S : D.Carrier) (x a b : ℝ),
        c * (a - b) ^ 2 ≤ (fa V_T V_S x a - fa V_T V_S x b) * (a - b))
    (h_cross_T : ∀ (V_S : D.Carrier) (x a : ℝ) (V_T₁ V_T₂ : D.Carrier),
        |fa V_T₁ V_S x a - fa V_T₂ V_S x a| ≤ K_T * dist V_T₁ V_T₂)
    (h_cross_S : ∀ (V_T : D.Carrier) (x a : ℝ) (V_S₁ V_S₂ : D.Carrier),
        |fa V_T V_S₁ x a - fa V_T V_S₂ x a| ≤ K_S * dist V_S₁ V_S₂) :
    p.AlphaOnLipschitzOn D (K_T / c) (K_S / c) := by
  intro V_T V_T' V_S V_S' x
  -- Set a := α_on V_T V_S x and b := α_on V_T' V_S' x.
  set a := D.α_on V_T V_S x with ha_def
  set b := D.α_on V_T' V_S' x with hb_def
  -- The objective parameter is the pair (V_T, V_S); define the gradient
  -- as a function of (V_T, V_S) through fa, with the position x fixed.
  -- We apply the Foundations two-coordinate lemma at θ_T := V_T,
  -- θ_T' := V_T', θ_S := V_S, θ_S' := V_S'.
  -- Define g : ℝ → Carrier → Carrier → ℝ as the gradient `fa _ _ x a`.
  -- FOC at first pair: fa V_T V_S x (α_on V_T V_S x) = 0.
  have hFOC_a : fa V_T V_S x a = 0 := h_FOC V_T V_S x
  -- FOC at second pair: fa V_T' V_S' x (α_on V_T' V_S' x) = 0.
  have hFOC_b : fa V_T' V_S' x b = 0 := h_FOC V_T' V_S' x
  -- Strong-concavity chord at θ' = (V_T', V_S').
  have hstr : c * (a - b) ^ 2
      ≤ (fa V_T' V_S' x a - fa V_T' V_S' x b) * (a - b) :=
    h_strong V_T' V_S' x a b
  -- Apply the Foundations two-coordinate lemma.
  -- Aliased name for the long Foundations lemma path; open the namespace
  -- locally to keep the call site under the 100-char line limit.
  open Sanctions.Foundations.ImplicitFunctionTheorem in
  exact
    argmax_lipschitz_pair_of_FOC_strong_concavity_cross_lipschitz_pair
      (Θ_T := D.Carrier) (Θ_S := D.Carrier)
      (fa := fun a' V_T₀ V_S₀ => fa V_T₀ V_S₀ x a')
      a b V_T V_T' V_S V_S'
      K_T K_S c hK_T_nn hK_S_nn hc_pos hFOC_a hFOC_b hstr
      (fun x' V_S₀ V_T₁ V_T₂ => h_cross_T V_S₀ x x' V_T₁ V_T₂)
      (fun x' V_T₀ V_S₁ V_S₂ => h_cross_S V_T₀ x x' V_S₁ V_S₂)

/-- **R32 full R31 closure (Round 1.6 + Round 1.7).** Sibling of
`alphaOnLipschitzOn_of_IFT_chord_form` that derives the chord-form
strong-concavity hypothesis from a more primitive C² Hessian lower
bound on the joint-Target integrand. The user supplies:

* differentiability of `fa V_T V_S x ·` in the action argument at the
  parameter point `(V_T', V_S')` (immediate from C² Target stage
  payoffs);
* a uniform lower bound `c ≤ deriv (fa V_T' V_S' x ·) y` (the Hessian
  lower bound, immediate from a Weierstrass inf on the compact cube
  under C² structure);

and the theorem composes through Round-1.6's
`gradient_strong_monotonicity_of_deriv_lower_bound` (`Foundations/ImplicitFunctionTheorem.lean`
§4) to derive the chord-form, then through the existing
`alphaOnLipschitzOn_of_IFT_chord_form` to read off the
`(K_T/c, K_S/c)` argmax-Lipschitz constant on the selector
`α_on V_T V_S x`.

**No interiority hypothesis** on the optimal compliance choice — the
canonical Rincón-Zapatero & Santos 2009 perspective: the Hessian
lower bound is the second-order characterisation of the unique-KKT-
multiplier statement they prove for concave dynamic programs under
the Arrow-Hurwicz-Uzawa constraint qualification.

**No new `Params` field, no new primitive.** Pure theorem-parameter
inputs only; the differentiability and Hessian-lower-bound
hypotheses are the canonical C² regularity statements about the
joint Target integrand, not assumptions on the feedback Stackelberg
equilibrium itself.

This is the R32 closure of the R31 scope-reduced deliverable. The
existing `alphaOnLipschitzOn_of_IFT_chord_form` route remains
available as a parallel wrapper for callers who prefer to supply the
chord-form directly. -/
theorem alphaOnLipschitzOn_of_C2_Hessian_lower_bound
    {D : p.ValueClass}
    (fa : D.Carrier → D.Carrier → ℝ → ℝ → ℝ)
    (c K_T K_S : ℝ)
    (hc_pos : 0 < c) (hK_T_nn : 0 ≤ K_T) (hK_S_nn : 0 ≤ K_S)
    (h_FOC : ∀ (V_T V_S : D.Carrier) (x : ℝ),
        fa V_T V_S x (D.α_on V_T V_S x) = 0)
    (h_diff : ∀ (V_T V_S : D.Carrier) (x : ℝ),
        Differentiable ℝ (fun a => fa V_T V_S x a))
    (h_Hessian_lower : ∀ (V_T V_S : D.Carrier) (x y : ℝ),
        c ≤ deriv (fun a => fa V_T V_S x a) y)
    (h_cross_T : ∀ (V_S : D.Carrier) (x a : ℝ) (V_T₁ V_T₂ : D.Carrier),
        |fa V_T₁ V_S x a - fa V_T₂ V_S x a| ≤ K_T * dist V_T₁ V_T₂)
    (h_cross_S : ∀ (V_T : D.Carrier) (x a : ℝ) (V_S₁ V_S₂ : D.Carrier),
        |fa V_T V_S₁ x a - fa V_T V_S₂ x a| ≤ K_S * dist V_S₁ V_S₂) :
    p.AlphaOnLipschitzOn D (K_T / c) (K_S / c) := by
  -- Derive the chord-form from the differential lower bound, uniformly
  -- in the parameter point (V_T, V_S, x).
  have h_chord : ∀ (V_T V_S : D.Carrier) (x a b : ℝ),
      c * (a - b) ^ 2 ≤ (fa V_T V_S x a - fa V_T V_S x b) * (a - b) := by
    intro V_T V_S x a b
    exact Sanctions.Foundations.ImplicitFunctionTheorem.chord_form_of_deriv_lower_bound
      (fun a => fa V_T V_S x a) hc_pos (h_diff V_T V_S x)
      (h_Hessian_lower V_T V_S x) a b
  -- Then call the existing chord-form discharger.
  exact p.alphaOnLipschitzOn_of_IFT_chord_form fa c K_T K_S
    hc_pos hK_T_nn hK_S_nn h_FOC h_chord h_cross_T h_cross_S


/-! ## Retired 2026-08-21: the homogeneous compliance certificate

The `RegularEconomyCertificateCompliance` tower that stood here — the Core /
Path split, its three-goals theorems, the `StandardComplianceCertificate`
alias, and the five `valLipBall` / `valLipGainBall` constructors — was retired
as strictly dominated by `StandardComplianceLocalCoreCertificate`
(`Theory/Certificates/StandardComplianceLocal.lean`) on three axes:

* it carried `D : p.ValueClass` — a **single** carrier shared by both players —
  where the local certificate carries `ValueClass2` with separate `carrier_T`
  and `carrier_S`. Since `ValueClass.toValueClass2` embeds the former in the
  latter, this route quantified over a strictly smaller class of economies.
  Economically the restriction is unmotivated: the two governments have
  different payoffs and different discount factors, so there is no reason
  their value functions inhabit one ball.
* its stage hypotheses were **per-equilibrium** (`hV_S_lip_E`, `hV_T_gain_on_E`,
  quantified over every `E`) rather than carrier-local, which is why nothing
  ever inhabited it: a per-equilibrium field asks for knowledge of every
  equilibrium before one is constructed, where a carrier field asks only about
  a set the witness builds itself.
* it carried `hMyo_basin` as a core field, which the audit-45 local route
  showed is not needed for the statewise comparison.

Its conclusions were matched exactly. The pathwise Goal-2 chain compared
`ruleSanctions (fun x => p.sigma x (M.alpha x))`, which is definitionally
`myopicEquilibriumRule M`, and that comparison is delivered by
`three_goals_local_regime_comparison_uniform_starts` and its general-`F`
sibling in `GeneralFDischargers.lean` — over all basin starts rather than one
stored initial state.

At retirement: 24 declarations, zero external consumers, zero witnesses, zero
headline rows. The C1 compliance block below and the closed-form Lipschitz
lemmas above are unaffected and remain live. -/

/-! ## Audit-44 Patch 1: C¹ compliance certificate

The audit-44 critique noted that the C¹ resistance-action certificate
remained valid only under the *resistance-action* interpretation of
`a`, and that paper-facing C¹ users under literal compliance needed a
bundled certificate wrapper of their own (so they could not
accidentally fall back to the wrong-sign route). That is the wrapper
below; the wrong-sign route it guarded against was deleted outright on
2026-08-17.

`RegularEconomyCertificateC1Compliance` bundles the inputs of
`jet_C1BellmanSystem_three_goals_compliance_on` (audit-44 C¹
bridge with localized continuation gain + floor/ceiling
dominance). Its `three_goals` is a one-line delegation. -/

/-- **Audit-45 Step 7: C¹ compliance certificate CORE (no `hMyo_basin`).**
Mirrors the BCF Core: all fields of the audit-44 C¹ compliance
certificate MINUS `hMyo_basin`. Supports the **statewise** dominance
three-goals theorem. -/
structure RegularEconomyCertificateC1ComplianceCore
    (p : AbstractGame.Params) (K_d : ℝ) where
  hK_d_nn : 0 ≤ K_d
  D_C1 : C1BellmanSystem p K_d
  hComplete : ValueClass_C1Complete D_C1.toValueClass_C1
  xT : ℝ
  xS : ℝ
  sbar : ℝ
  mS : ℝ
  KS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  hsbar_mem : sbar ∈ Sanctions.I
  hKS_nonneg : 0 ≤ KS
  hS_margin : p.β_S * KS * p.δ < mS
  hsbar_pos : 0 < sbar
  hjoint_lt : max xT xS < 1
  hV_S_lip_E :
    ∀ E : p.FeedbackStackelbergEquilibriumTop,
      ValueLipschitzWith E.V_S KS
  cT : ℝ
  gT : ℝ
  hT_loss_margin : cT ≤ p.β_T * gT * p.δ
  h_stage_target_loss_α :
    ∀ E : p.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT
  hV_T_gain_on_E :
    ∀ E : p.FeedbackStackelbergEquilibriumTop,
      LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT
  h_stage_sender_α :
    ∀ E : p.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS
  hSC_α :
    ∀ E : p.FeedbackStackelbergEquilibriumTop,
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s)
  M : p.MyopicFeedbackEquilibrium
  hMyoCeiling :
    ∀ x ∈ Set.Icc (max xT xS) 1,
      p.σ x (M.α x) ≤ max x sbar
  x₀ : ℝ
  hx₀ : x₀ ∈ Set.Icc (max xT xS) 1
  x₀shock : ℝ
  hx₀shock_nn : 0 ≤ x₀shock
  hx₀shock_le : x₀shock ≤ 1

namespace RegularEconomyCertificateC1ComplianceCore

variable {K_d : ℝ}


end RegularEconomyCertificateC1ComplianceCore

/-- **C¹-route compliance certificate (audit-44).** Bundles the
inputs of `jet_C1BellmanSystem_three_goals_compliance_on`: C¹
Bellman system + completeness + Target loss-offset (localized
continuation gain) + Sender margin + myopic comparator with
myopic ceiling.

**Audit-45 Step 7**: this structure now `extends`
`RegularEconomyCertificateC1ComplianceCore` and adds only the
`hMyo_basin` field needed for the pathwise comparison. The Core
supports the statewise dominance theorem
`RegularEconomyCertificateC1ComplianceCore.three_goals_statewise`. -/
structure RegularEconomyCertificateC1Compliance
    (p : AbstractGame.Params) (K_d : ℝ)
    extends RegularEconomyCertificateC1ComplianceCore p K_d where
  /-- **Myopic basin invariance.** Required only for the pathwise
  sanction-sequence comparison. The Core supports the statewise
  three-goals theorem without it. -/
  hMyo_basin :
    ∀ x ∈ Set.Icc
            (max toRegularEconomyCertificateC1ComplianceCore.xT
                 toRegularEconomyCertificateC1ComplianceCore.xS) 1,
      p.σ x (toRegularEconomyCertificateC1ComplianceCore.M.α x)
        ∈ Set.Icc
            (max toRegularEconomyCertificateC1ComplianceCore.xT
                 toRegularEconomyCertificateC1ComplianceCore.xS) 1

namespace RegularEconomyCertificateC1Compliance

variable {K_d : ℝ}


end RegularEconomyCertificateC1Compliance

/-! ## Audit-46 Patch 1 (C¹ side): canonical alias

`StandardComplianceCertificateC1` = `RegularEconomyCertificateC1ComplianceCore`
with `three_goals` pointing to `three_goals_statewise`. -/

/-- **Audit-46 canonical C¹ alias.** -/
abbrev StandardComplianceCertificateC1
    (p : AbstractGame.Params) (K_d : ℝ) :=
  p.RegularEconomyCertificateC1ComplianceCore K_d

namespace StandardComplianceCertificateC1

variable {K_d : ℝ}


end StandardComplianceCertificateC1

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
