/-
Sanctions/Theory/Equilibrium/EpsilonIsolation.lean

**Wave-6 P7: scoped ε-isolation of carrier equilibria (parametric layer).**

Within-carrier uniqueness (`PerovExistence.lean`, Round R-UNIQ) pins the
equilibrium *given* carrier membership. This file upgrades that to
**ε-neighborhood isolation in value space**: any equilibrium whose value
pair lies within `ε` of the carrier fixed point in sup-norm — and which
carries the carrier's *shape pins* as hypotheses — must coincide with the
fixed point. In plain language: **the certified equilibria are locally
isolated in value space — no distinct equilibrium with the same selector
convention and the same carrier shape exists within `ε` in sup-norm.**

## The precise scope (what ε-closeness does and does not buy)

Sup-norm ε-closeness discharges exactly ONE component of enlarged-carrier
membership: the **norm** component (`‖V‖ ≤ M + ε` by the triangle
inequality from `‖V*‖ ≤ M` and `dist V V* ≤ ε`). It provably CANNOT
discharge the **shape** components (the Sender Lipschitz bound, the Target
monotonicity / slope-window pins): an ε-amplitude **sawtooth** added to
the fixed point is ε-close in sup-norm, non-monotone, and of unbounded
Lipschitz constant (probe exhibit: at sup-distance `≤ 1/100` and tooth
width `1/10000`, the perturbed Sender value has a chord slope
`16/3 − 200 < 0`, destroying both the Lipschitz window and the lower
slope pin). Hence the shape pins are **irreducible hypotheses on the
candidate equilibrium** at this layer. The pin-free variant (regenerating
the pins from the candidate's own Bellman equations) would require
invariance hypotheses quantified over bare norm-ball inputs — a strictly
WIDER hypothesis shape than the accepted `h_invT`/`h_invS`, i.e. a Rule-3
stop, deliberately not taken here.

## Honest classification

This is the scoped Doraszelski–Escobar-style local-regularity statement
(isolation of equilibria) available WITHOUT differentiability machinery:
no manifold structure, no Jacobian nondegeneracy, no genericity claim.
Full genericity (finiteness/oddness of the equilibrium set, regular-value
arguments) stays out of scope.

## Structure of the file

1. **Norm membership from ε-closeness** (`norm_le_enlarged_of_dist_le`,
   `mem_enlarged_of_dist_le`): the triangle-inequality step, over an
   arbitrary normed group, against an abstract shape pin.
2. **Two Schur fixed points coincide** (`fixedPoint_unique_of_schur_rows`):
   the uniqueness half of the Perov 2×2 principle, elementarily — row
   Lipschitz estimates + the Schur margin force any two fixed points of
   the joint operator to coincide (no completeness, no nonemptiness).
3. **The abstract ε-isolation core** (`epsIsolation_of_schur_rows`):
   norm ε-closeness + shape pins ⇒ enlarged-carrier membership;
   Bellman-fixedness of the member pair + the Schur margin ⇒ the
   candidate IS the fixed point.
4. **The equilibrium wrapper** (`ValueClass2.epsilonIsolation_feedbackStackelbergTop_schur`):
   specializes the core to a `FeedbackStackelbergEquilibriumTop` with
   selector coincidence, via the existing parametric bridge
   `fixedPoint_of_bellman_fixed_of_selector_coincidence`.
5. **The ε-enlarged chain constants** (`EpsilonChain`): the row-Lipschitz
   chain factors as closed-form functions of the enlarged carrier bounds
   `M_T' = M_T + ε`, `M_S' = M_S + ε`, `K' = K(M_S')`, and the
   margin-survival condition as an explicit inequality
   (`schurMargin_pos_iff`) — the slack of the shipped witnesses is
   consumed quantifiably as ε grows.

## Rule compliance

**Rule 3** ✓ — zero new assumptions: every hypothesis is an existing
accepted shape (row-Lipschitz estimates, Schur margin, carrier
membership/decomposition, Bellman fixed-point fields, selector
coincidence); the chain items are plain `def`s. **Rule 5** ✓ — fully
parametric; witnesses (`Examples/EpsilonIsolationWitness.lean`) are
instantiations. **Rule 15** ✓ — the reference fixed point is consumed as
an explicit hypothesis (`hz : T z = z`); at the witnesses it is supplied
by the constructed Perov/closed-form fixed points, never assumed.
-/

import Sanctions.Theory.Equilibrium.PerovExistence

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

/-! ## §1–§3: moved to Foundations (2026-07-24 Rule-19 sweep)

The generic content formerly here — the enlarged-norm/membership
triangle lemmas (`norm_le_enlarged_of_dist_le`,
`mem_enlarged_of_dist_le`), the Schur fixed-point uniqueness lemma
(`fixedPoint_unique_of_schur_rows`), and the abstract ε-isolation core
(`epsIsolation_of_schur_rows`) — is fully generic metric-space material
and now lives in `Foundations/PerovContraction.lean`, still at the
`Sanctions` root namespace, so every fully-qualified name is unchanged
and the witness files compile untouched. One disclosed signature
change: `fixedPoint_unique_of_schur_rows` dropped its never-consumed
`_ha_lt : a < 1` hypothesis. A second followed on 2026-10-06 (round BG1.1):
`epsIsolation_of_schur_rows` and the wrapper below dropped their
never-consumed `β_T < 1`. -/

/-! ## §4 The equilibrium wrapper (ValueClass2 form) -/

namespace AbstractGame
namespace Params
namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-- **ε-isolation of the carrier equilibrium (parametric capstone).**
Let `D` be the (enlarged) carrier value class with the Schur package
(row-Lipschitz estimates + margin — the same hypothesis shapes as
`feedbackStackelbergTop_unique_in_carrier_schur`), and let `z` be a
fixed point of the joint subtype operator with exact norm anchors
`‖z.1‖ ≤ M_T`, `‖z.2‖ ≤ M_S`. Then any top-selector feedback
Stackelberg equilibrium `E` whose values are within `(ε_T, ε_S)` of the
fixed point in sup-norm, which carries the carrier **shape pins** as
hypotheses, and whose policy coincides with the carrier selector, has
exactly the fixed point's value pair.

Plain language: **the certified equilibrium is locally isolated in
value space** — no distinct equilibrium with the same selector
convention and the same carrier shape exists within ε in sup-norm.
The shape pins on `E` are irreducible at this layer: an ε-amplitude
sawtooth added to the fixed point is ε-close but breaks every slope
pin (file header), and bootstrapping the pins from `E`'s own Bellman
equations would demand invariance over bare norm balls — a strictly
wider hypothesis shape than the accepted `h_inv` (a Rule-3 stop,
not taken).

2026-10-06 (round BG1.1): the never-consumed Target diagonal bound
`β_T < 1` was dropped from the signature. The proof only uses `β_S < 1` and
the Schur margin (through `epsIsolation_of_schur_rows`), and with the two
cross-constant signs those already imply `β_T < 1`. General in `F`: the
transition enters only through the Bellman operators of `p`. -/
theorem epsilonIsolation_feedbackStackelbergTop_schur
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S))
    (z : D.CarrierT × D.CarrierS)
    (hz : (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z) = z)
    {M_T M_S ε_T ε_S : ℝ}
    (hz_T_norm : ‖z.1.val‖ ≤ M_T) (hz_S_norm : ‖z.2.val‖ ≤ M_S)
    {shape_T shape_S : Set (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    (h_decomp_T : ∀ V, ‖V‖ ≤ M_T + ε_T → V ∈ shape_T → V ∈ D.carrier_T)
    (h_decomp_S : ∀ V, ‖V‖ ≤ M_S + ε_S → V ∈ shape_S → V ∈ D.carrier_S)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hd_T : dist E.V_T z.1.val ≤ ε_T) (hd_S : dist E.V_S z.2.val ≤ ε_S)
    (hsh_T : E.V_T ∈ shape_T) (hsh_S : E.V_S ∈ shape_S)
    (hα : ∀ (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S),
      E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) :
    E.V_T = z.1.val ∧ E.V_S = z.2.val :=
  epsIsolation_of_schur_rows
    (T := fun w : D.CarrierT × D.CarrierS =>
      (D.jointTargetOp_sub h_inv w, D.jointSenderOp_sub h_inv w))
    hL_TS_nn hL_ST_nn
    (fun w w' => hT_T w.1 w'.1 w.2 w'.2)
    (fun w w' => hT_S w.1 w'.1 w.2 w'.2)
    hβ_S_lt hSchur z hz hz_T_norm hz_S_norm
    h_decomp_T h_decomp_S hd_T hd_S hsh_T hsh_S
    (fun hWT hWS =>
      D.fixedPoint_of_feedbackStackelbergTop_of_selector_coincidence
        h_inv E hWT hWS (hα hWT hWS))

end ValueClass2
end Params
end AbstractGame

/-! ## §5 The ε-enlarged chain constants and margin survival

The row-Lipschitz constants of the coupled chain, as closed-form
functions of the **enlarged** carrier bounds. Enlarging the Target norm
radius to `M_T' = M_T + ε` and the Sender norm radius to
`M_S' = M_S + ε` shifts the chain factors as follows (each a plain
`def`; the witness file instantiates them at exact rationals and
discharges every margin inequality by `norm_num`):

* `KS M_S'` — the Sender-carrier Lipschitz constant
  `K'(ε) = L_Ux + β_S·(M_S'/h)·(1−δ)` (the `lowDelta_chain_KS` formula
  re-centered at the enlarged radius; the enlarged Lipschitz ball
  `valLipBall M_S' (KS M_S')` is the natural invariant candidate).
* `cS M_S'` — the smeared-Sender concavity modulus falls affinely in
  the Sender radius: `c_S(ε) = c_stage − κ₂·M_S'`.
* `Lσ c` — the Sender-selector Lipschitz constant in the Sender value
  scales as `1/c_S`: `Lσ = 2·β_S·(1/h)·δ/c`.
* `κa c` — the argmax-core sensitivity `κ_a = 2·|∂²U_S/∂s∂a|/c`
  (robust repo factor-2 convention).
* `G M_T'` — the Target-row stage-plus-continuation factor rises
  affinely in the Target radius: `G = L_UT + β_T·(M_T'/h)·δ`.
* `L_TS = G·Lσ`, `L_ST = L_Ua·(2/c_T)·κ_a·β_T·δ·(1/h)` — the two cross
  constants.
* `schurMargin` — the Schur margin of the row matrix
  `[[β_T, L_TS], [L_ST, b_S]]`; **margin survival at enlargement ε is
  the explicit inequality `0 < schurMargin β_T (b_S ε) (L_TS ε)
  (L_ST ε)`** (equivalently `L_TS(ε)·L_ST(ε) < (1−β_T)·(1−b_S(ε))`,
  `schurMargin_pos_iff`). -/

namespace EpsilonChain

/-- Enlarged Sender-carrier Lipschitz constant
`K'(M_S') = L_Ux + β_S·(M_S'/h)·(1−δ)` — the chain creation-bound
formula (`lowDelta_chain_KS` shape) at the enlarged Sender norm
radius `M_S'`. -/
def KS (L_Ux β_S h δ M_S' : ℝ) : ℝ := L_Ux + β_S * (M_S' / h) * (1 - δ)

/-- Enlarged smeared-Sender concavity modulus
`c_S(M_S') = c_stage − κ₂·M_S'` (affine fall in the Sender radius;
coupled witness: `c_stage = 6/5`, `κ₂ = 1/200`). -/
def cS (c_stage κ₂ M_S' : ℝ) : ℝ := c_stage - κ₂ * M_S'

/-- Sender-selector Lipschitz constant in the Sender value:
`Lσ(c) = 2·β_S·(1/h)·δ/c`. -/
def Lσ (β_S h δ c : ℝ) : ℝ := 2 * β_S * (1 / h) * δ / c

/-- Argmax-core sensitivity `κ_a(c) = 2·D_sa/c` where
`D_sa = |∂²U_S/∂s∂a|` (robust repo factor-2 convention). -/
def κa (D_sa c : ℝ) : ℝ := 2 * D_sa / c

/-- Enlarged Target-row stage-plus-continuation factor
`G(M_T') = L_UT + β_T·(M_T'/h)·δ`. -/
def G (L_UT β_T h δ M_T' : ℝ) : ℝ := L_UT + β_T * (M_T' / h) * δ

/-- Target-row cross constant `L_TS = G(M_T')·Lσ(c_S(M_S'))`: the
Sender value moves the Target row through the selector channel. -/
def L_TS (L_UT β_T β_S h δ M_T' c : ℝ) : ℝ :=
  G L_UT β_T h δ M_T' * Lσ β_S h δ c

/-- Sender-row cross constant
`L_ST = L_Ua·(2/c_T)·κ_a·β_T·δ·(1/h)`: the Target value moves the
Sender row through the leader-policy (κ_a) channel. -/
def L_ST (L_Ua c_T D_sa β_T h δ c : ℝ) : ℝ :=
  L_Ua * (2 / c_T) * (κa D_sa c * β_T * δ * (1 / h))

/-- The Schur margin of the row matrix `[[β_T, L_TS], [L_ST, b_S]]`. -/
def schurMargin (β_T b_S lTS lST : ℝ) : ℝ :=
  (1 - β_T) * (1 - b_S) - lTS * lST

/-- **Margin survival as an explicit inequality**: positivity of the
Schur margin at the ε-shifted constants is exactly the Schur condition
the Perov layer consumes. -/
theorem schurMargin_pos_iff (β_T b_S lTS lST : ℝ) :
    0 < schurMargin β_T b_S lTS lST ↔ lTS * lST < (1 - β_T) * (1 - b_S) := by
  unfold schurMargin
  constructor <;> intro h <;> linarith

/-- Margin positivity delivers the Schur hypothesis shape consumed by
`epsIsolation_of_schur_rows` and the Perov existence layer. -/
theorem schur_lt_of_margin_pos {β_T b_S lTS lST : ℝ}
    (h : 0 < schurMargin β_T b_S lTS lST) :
    lTS * lST < (1 - β_T) * (1 - b_S) :=
  (schurMargin_pos_iff β_T b_S lTS lST).mp h

end EpsilonChain

end -- noncomputable section

end Sanctions
