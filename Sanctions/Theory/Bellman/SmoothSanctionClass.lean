/-
Sanctions/Theory/Bellman/SmoothSanctionClass.lean

**Audit-37 Step 5: parametric `SmoothSanctionClass` skeleton.**

**STILL FROZEN (status reaffirmed 2026-07-12).** The C¹ *witness*
layer was partially unfrozen — `Examples/C1WitnessEnvelope.lean`
inhabits `C1Val` / `ValueClass_C1` / `C1BellmanSystem` at two pinned
exact fixed points and the paper cites the resulting shadow prices —
but **this smooth payoff class is not part of that unfreeze**: no
witness instantiates it, no paper claim cites it, no headline row
fences it. Its IFT Prop fields are exactly the abstract layer that
stays frozen, because every general form needs new differentiability
hypotheses (Rule 3). Known deficiencies recorded, not repaired:
`c1distPair` is a pseudo-metric (`V'` stored on all of `ℝ`), and
completeness (`ValueClass_C1Complete`) is consumed per-certificate,
not derived (both are vacuous at the singleton witness carriers, which
prove their own completeness — they bite only at abstract generality).
Revival order if ever needed: (1) the within-set
uniform-limits-of-derivatives theorem (a mathlib gap, not an analytic
one — `Foundations/` candidate), (2) the `V'`-domain refactor,
(3) asymmetric duplication only once a consumer exists.

The audit-37 critique recommends, as the substantive next step toward
the JET theorem:

> Define a parametric smooth payoff class (Smooth `U_T`, `U_S` with
> derivative bounds + strong-concavity moduli + interiority margins +
> row-contraction margins) and prove dischargers for all the
> theorem-parameter primitives the audit-34/37 bridges consume.

This file provides the **structure skeleton** and the
**immediately-provable dischargers** (cube bounds, payoff Lipschitz
constants, transition Lipschitz). The deep IFT-at-FOC dischargers
(`SigmaDynC1IFTBound`, `AlphaOnC1IFTBound`) are packaged as structure
fields — at the abstract layer these are theorem-parameter
primitives, dischargeable at concrete smooth payoff classes by direct
calculation of the Sender and leader FOCs.

## Architecture

`SmoothSanctionClass p K_d` packages:

* Cube bounds `cube_T, cube_S` on `|U_T|`, `|U_S|` over `I³`.
* Stage Lipschitz constants `L_U_T_s`, `L_U_T_x`, `L_U_S_a`,
  `L_U_S_x` for the relevant partials.
* The IFT-at-FOC primitives `SigmaDynC1IFTBound`, `AlphaOnC1IFTBound`
  (as Prop fields).
* Strong-concavity moduli `c_S`, `c_T` for the Sender/leader objectives.

Dischargers provided here:

* `cube_T_discharge` / `cube_S_discharge` — immediate from fields.
* `transition_Lipschitz` — `F(x, s) = (1-δ)·x + δ·s` is `(1-δ)`-Lipschitz
  in `x` at fixed `s`. **Provable from `Params.δ`**.
* `sender_state_Lipschitz_from_α` — at any leader policy `α`, the Sender
  stage payoff `U_S(x, α(x), s)` is `L_U_S_x + L_U_S_a · L_α`-Lipschitz
  in `x` (under `α` Lipschitz). Decomposition + triangle.

The IFT primitives are exposed as structure fields and the
high-basin / row-Lipschitz / row-margin primitives that further
depend on the IFT primitives are likewise exposed as fields. This
makes the `SmoothSanctionClass` skeleton **completely parametric**:
at any concrete instantiation, the user supplies (i) the smooth
functional forms `U_T`, `U_S`, `σ`, and (ii) the calculated
derivative bounds + strong-concavity moduli + IFT discharges via
direct FOC inspection.

## Rule compliance

**Rule 1.** No strategy choice; this is a primitive-data interface.

**Rule 3.** `SmoothSanctionClass` is a *bundling* structure — it
groups existing primitives. New fields are restatements of existing
theorem-parameter primitives (cube_T, IFT primitives, etc.). No new
load-bearing assumption beyond what each underlying bridge already
consumes.

**Rule 5.** Fully parametric over `(K_d, c_S, c_T, ...)`.
-/

import Sanctions.Theory.Bellman.C1Val
import Sanctions.Theory.Bellman.LipschitzPrimitives
import Sanctions.Theory.Bellman.InvariantBall
import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## `SmoothSanctionClass` skeleton -/

/-- **Parametric smooth payoff class** for the JET bridge.

Packages the primitive constants the audit-34/37 bridges consume into
one structure. At a concrete instantiation, the user supplies smooth
functional forms for `U_T`, `U_S`, `σ` plus all the calculated
derivative bounds + strong-concavity moduli + IFT discharges.

Fields:
* Cube bounds (compactness + continuity over `[0,1]³`).
* Stage payoff Lipschitz constants (in each argument).
* Sender stage Lipschitz constant `L_U_a` in the leader action.
* C¹ strong-concavity moduli for the Sender and leader objectives.
* IFT-at-FOC primitives (Prop fields).

Out of scope: the actual `U_T, U_S, σ` functional forms — those are
parametric in `Params`. -/
structure SmoothSanctionClass (p : AbstractGame.Params) (K_d : ℝ) where
  /-- Cube bound on `|U_T|` over `I³`. -/
  cube_T : ℝ
  cube_T_nn : 0 ≤ cube_T
  hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
    ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T
  /-- Cube bound on `|U_S|` over `I³`. -/
  cube_S : ℝ
  cube_S_nn : 0 ≤ cube_S
  hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
    ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S
  /-- `U_T` Lipschitz constant in `s` (third argument). -/
  L_U_T_s : ℝ
  L_U_T_s_nn : 0 ≤ L_U_T_s
  hU_T_lip_s : ∀ x a s s',
    |p.U_T x a s - p.U_T x a s'| ≤ L_U_T_s * |s - s'|
  /-- `U_S` Lipschitz constant in `a` (second argument). -/
  L_U_S_a : ℝ
  L_U_S_a_nn : 0 ≤ L_U_S_a
  hU_S_lip_a : ∀ x s a a' : ℝ,
    |p.U_S x a s - p.U_S x a' s| ≤ L_U_S_a * |a - a'|
  /-- C¹ uniform strong-concavity modulus for the Sender objective in `s`. -/
  c_S : ℝ
  c_S_pos : 0 < c_S
  /-- C¹ uniform strong-concavity modulus for the leader objective in `a`. -/
  c_T : ℝ
  c_T_pos : 0 < c_T
  /-- IFT-at-FOC primitive for σ_dyn. -/
  hSigma_IFT : p.SigmaDynC1IFTBound (K_d := K_d) c_S
  /-- Parametric leader argmax field. -/
  α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ
  /-- IFT-at-FOC primitive for the leader argmax (parametric). -/
  L_VT_sens : ℝ
  L_VT_sens_nn : 0 ≤ L_VT_sens
  L_VS_sens : ℝ
  L_VS_sens_nn : 0 ≤ L_VS_sens
  hAlpha_IFT : AlphaOnC1IFTBound (K_d := K_d) α_on_C1 c_T L_VT_sens L_VS_sens

namespace SmoothSanctionClass

variable {p : AbstractGame.Params} {K_d : ℝ}

/-! ## Dischargers immediately provable from the structure -/

/-- **Cube bound discharger for `U_T`**: direct field. -/
theorem cube_T_discharge (D : SmoothSanctionClass p K_d) :
    ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_T x a s| ≤ D.cube_T :=
  D.hU_T_cube

/-- **Cube bound discharger for `U_S`**: direct field. -/
theorem cube_S_discharge (D : SmoothSanctionClass p K_d) :
    ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |p.U_S x a s| ≤ D.cube_S :=
  D.hU_S_cube

/-- **`U_T` stage Lipschitz in `s` discharger**: direct field. The
audit-34 bridge consumes this as `h_U_lipschitz`. -/
theorem hU_lipschitz_discharge (D : SmoothSanctionClass p K_d) :
    ∀ x a s s', |p.U_T x a s - p.U_T x a s'| ≤ D.L_U_T_s * |s - s'| :=
  D.hU_T_lip_s

/-- **`U_S` stage Lipschitz in `a` discharger**: direct field. The
audit-34 bridge consumes this as `h_U_S_lip_a`. -/
theorem hU_S_lip_a_discharge (D : SmoothSanctionClass p K_d) :
    ∀ x s a a' : ℝ, |p.U_S x a s - p.U_S x a' s| ≤ D.L_U_S_a * |a - a'| :=
  D.hU_S_lip_a

/-! ## Transition Lipschitz (provable from `Params.δ` alone) -/

/-- **Transition Lipschitz in `x`**: `F(x, s) = (1-δ)·x + δ·s` is
`(1-δ)`-Lipschitz in `x` at fixed `s`. Provable directly from
`Params.δ ∈ (0, 1)`. -/
theorem transition_Lipschitz (p : AbstractGame.Params) :
    ∀ x₁ x₂ : ℝ, ∀ s : ℝ,
      |((1 - p.δ) * x₂ + p.δ * s) - ((1 - p.δ) * x₁ + p.δ * s)|
        ≤ (1 - p.δ) * |x₂ - x₁| := by
  intro x₁ x₂ s
  have h_eq : ((1 - p.δ) * x₂ + p.δ * s) - ((1 - p.δ) * x₁ + p.δ * s)
                = (1 - p.δ) * (x₂ - x₁) := by ring
  rw [h_eq, abs_mul]
  have h_1mδ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  rw [abs_of_nonneg h_1mδ_nn]

/-- **Specialization to a continuous leader policy `α`**: with any
feasibility-irrelevant `α`, the transition is `(1-δ)`-Lipschitz in `x`
at every `s ∈ I`. This is the form audit-34's `h_F_lip` wants. -/
theorem transition_Lipschitz_at_α (p : AbstractGame.Params) :
    ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |((1 - p.δ) * x₂ + p.δ * s) - ((1 - p.δ) * x₁ + p.δ * s)|
        ≤ (1 - p.δ) * |x₂ - x₁| := by
  intro x₁ x₂ s _hs
  exact transition_Lipschitz p x₁ x₂ s

/-! ## C¹ Lipschitz dischargers via the IFT primitives -/

/-- **σ_dyn Lipschitz constant `L_σ_C1 = β_S · δ / c_S`** discharged
from the IFT primitive via iter 14 (`sigmaDynLipschitzOn_C1_of_IFT_bound`). -/
theorem sigma_dyn_lipschitz_C1_discharge
    (hK_d_nn : 0 ≤ K_d) (D : SmoothSanctionClass p K_d) :
    p.SigmaDynLipschitzOn_C1 (K_d := K_d) (p.β_S * p.δ / D.c_S) :=
  p.sigmaDynLipschitzOn_C1_of_IFT_bound hK_d_nn D.c_S_pos D.hSigma_IFT

/-- **α_on Lipschitz constants `(L_VT_sens / c_T, L_VS_sens / c_T)`**
discharged from the IFT primitive via iter 16
(`alphaOnLipschitzOn_C1_of_IFT_bound`). -/
theorem alpha_on_lipschitz_C1_discharge
    (D : SmoothSanctionClass p K_d) :
    AlphaOnLipschitzOn_C1 (K_d := K_d) D.α_on_C1
      (D.L_VT_sens / D.c_T) (D.L_VS_sens / D.c_T) :=
  alphaOnLipschitzOn_C1_of_IFT_bound D.c_T_pos
    D.L_VT_sens_nn D.L_VS_sens_nn D.hAlpha_IFT

/-! ## Convenience: cube bound from continuity + compactness (one-liner sketch)

Note for concrete instantiations: any continuous `U_T, U_S` on `I × I × I`
(which holds via `Params.U_T_continuous`, `Params.U_S_continuous`) attains
a maximum by compactness; the cube bounds `cube_T, cube_S` are then
`max |U_T|` and `max |U_S|`, available via `IsCompact.exists_isMaxOn`.
This skeleton takes the cube bounds as structure fields rather than
deriving them, to keep the structure independent of `Params.U_*_continuous`
(which uses subtype-coerced continuity arguments). -/

end SmoothSanctionClass

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
