/-
Sanctions/Theory/Bellman/OperatorRowLipschitz.lean

**Gap 3 discharge (audit-33 follow-up): operator-level row-Lipschitz
bounds for the joint Bellman operator pair on the carrier subtype.**

**Where the Target row actually lives (corrected 2026-08-30).** This header
previously credited `JointLipschitz.lean` with the pointwise Target
row-Lipschitz bound. That file contains **no declarations at all**; the
bound had been moved and the prose was left behind. The Target row is:

* **general in `F`** — `Theory/Bellman/GeneralFOperatorRow.lean`, both the
  pointwise bound and its operator-level lift, with the affine hypothesis
  replaced by a sanction upper chord;
* **affine-restricted** — `Examples/AffineInstance/Bridges.lean`, which
  carries `hF : p.F = affineF p.δ` and currently has no consumers.

This file therefore holds the **Sender** side only.

**Two carriers, local hypotheses (round BH1.2, 2026-10-06).** Both Sender-row
theorems below now have their primary form on the two-carrier class
`ValueClass2` (`ValueClass2.jointSenderOp_sub_row_lipschitz_of_pointwise` and
`ValueClass2.jointSenderOp_sub_row_lipschitz_of_alphaOn`). The second asks for
the leader selector to be Lipschitz only over `carrier_T × carrier_S` at
feasible states (`ValueClass2.AlphaOnLipschitzOn`) and for the Sender stage
payoff to be Lipschitz in the Target action only on `S × I × I × I`. The
original single-carrier statements are unchanged corollaries through
`ValueClass.toValueClass2`. The Target-row counterpart is
`ValueClass2.jointTargetOp_sub_row_lipschitz_generalF` in
`Theory/Bellman/GeneralFOperatorRow.lean`. All of it is general in `F`.

For the Sender side, two tiers:

* **Tier (i) — at fixed leader α**: lifting
  `bellmanS_BCF_pointwise_dist` to BCF metric is a one-line standard
  application of `BoundedContinuousFunction.norm_le` and gives the
  pure `β_S`-contraction in `V_S` at fixed `α`.

* **Tier (ii) — full `jointSenderOp_sub` row-Lipschitz** (with α
  varying as `α_on(V_T, V_S)`) requires additional α-Lipschitz
  primitives `L_α_VT`, `L_α_VS` (Berge / IFT-style constants), which
  the audit identifies as deeper open content. The version below
  consumes those constants as theorem-parameter primitives, so the
  user can plug in any concrete discharge.

## Rule compliance

**Rule 1.** All inputs are equilibrium-derived value functions and
the joint operators consume the project's equilibrium-derived `α_on`
selector.

**Rule 3.** No new `Params` fields. The Lipschitz constants `L_σ`,
`L_U`, `K_V` (and optional `L_α_*`) are theorem-parameter primitives,
classified (3) in `ASSUMPTION-SURFACE-REGISTER.md` (Lipschitz
primitives that admit concrete discharge per payoff class).

**Rule 5.** Fully parametric.
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Bellman.LipschitzPrimitives
import Sanctions.Theory.Equilibrium.JointLipschitz
import Sanctions.Theory.Bellman.BellmanS

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Operator-level row-Lipschitz of `jointTargetOp_sub`

**Empty by design (documented 2026-08-30).** This section header had no content
under it. The Target row is not in this file: see
`Theory/Bellman/GeneralFOperatorRow.lean` for the general-`F` form and
`Examples/AffineInstance/Bridges.lean` for the affine-restricted one. -/


/-- **Sender Bellman BCF-metric `β_S`-Lipschitz bound at fixed α.**
Operator-level lift of `bellmanS_BCF_pointwise_dist`. -/
theorem bellmanS_BCF_dist_le
    {α : ℝ → ℝ} (hα : Continuous α)
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    dist (p.bellmanS_BCF α hα V) (p.bellmanS_BCF α hα W)
      ≤ p.β_S * dist V W := by
  have h_rhs_nn : 0 ≤ p.β_S * dist V W :=
    mul_nonneg p.β_S_mem.1 dist_nonneg
  rw [BoundedContinuousFunction.dist_le h_rhs_nn]
  intro x
  exact p.bellmanS_BCF_pointwise_dist hα V W x

/-! ## 3. Sender operator row-Lipschitz on the subtype (with α varying)

For the full `jointSenderOp_sub` row-Lipschitz with α changing as
`α_on(V_T, V_S)`, the user must supply α-Lipschitz primitives
(IFT-style constants `L_α_VT`, `L_α_VS`). These are listed as open
in the assumption surface register; the theorem below consumes them
parametrically. The proof composes:

* α change in V_T contributes `L_α_VT · L_U_a` to `L_ST` (via
  Sender stage payoff Lipschitz in the leader action).
* α change in V_S contributes `L_α_VS · L_U_a` to the V_S-row coefficient.
* Direct V_S change contributes the `β_S` of the standard contraction.

We package the row-Lipschitz statement with three explicit primitive
inputs:

* `L_α_VT, L_α_VS` — α-Lipschitz constants (BCF norm).
* `L_U_a` — Sender stage payoff Lipschitz in the leader action `a`.
* `R_S` — uniform sup-norm bound on V_S on the carrier (from
  `InvariantBall`) needed to absorb the V_T-mediated α-change through
  the V_S Bellman contraction.

The theorem below is stated **conditionally**: users supply the
above-listed primitives plus the corresponding pointwise bound. The
operator-level lift is then a routine `dist_eq_norm` +
`norm_le` + `bellmanS_BCF_pointwise_dist`-style application.

NOTE: This is the **simplest packaging** that preserves the audit's
"thread existing primitives" principle. A fully-discharged
`jointSenderOp_sub` row-Lipschitz from primitives requires the
α-Lipschitz primitives; their concrete derivation (IFT + strict
concavity) is the remaining JET-facing open item. -/

namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-- **Conditional Sender row on the two-carrier class (round BH1.2,
2026-10-06).** Given a pointwise row-Lipschitz bound on the Sender Bellman
update at the carrier selector, for Target values in `carrier_T` and Sender
values in `carrier_S`, the subtype-valued Sender operator satisfies the same
bound in the sup-norm.

Plain language: the operator-level bound is the pointwise bound taken uniformly
over states. Compared with the single-carrier
`Params.jointSenderOp_sub_row_lipschitz_of_pointwise`, which it implies through
`ValueClass.toValueClass2`, the Target and Sender values may live in different
carriers. The bound has the shape `exists_fixedPoint_in_carrier_schur`
consumes. General in `F`. -/
theorem jointSenderOp_sub_row_lipschitz_of_pointwise
    (h_inv : D.IsInvariant)
    {L_ST β_S_eff : ℝ}
    (hL_ST_nn : 0 ≤ L_ST) (hβ_S_eff_nn : 0 ≤ β_S_eff)
    (h_pt : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
        ∀ x : ↥(Sanctions.S : Set ℝ),
        |(p.bellmanS_BCF (D.α_on V W) (D.α_on_continuous V W) W.val) x
          - (p.bellmanS_BCF (D.α_on V' W') (D.α_on_continuous V' W') W'.val) x|
          ≤ L_ST * dist V V' + β_S_eff * dist W W')
    (V V' : D.CarrierT) (W W' : D.CarrierS) :
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ L_ST * dist V V' + β_S_eff * dist W W' := by
  have h_dist_subtype :
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        = dist (D.jointSenderOp_sub h_inv (V, W)).val
                (D.jointSenderOp_sub h_inv (V', W')).val := by
    rw [Subtype.dist_eq]
  rw [h_dist_subtype]
  change dist (p.bellmanS_BCF (D.α_on V W) (D.α_on_continuous V W) W.val)
              (p.bellmanS_BCF (D.α_on V' W') (D.α_on_continuous V' W') W'.val)
          ≤ _
  have h_rhs_nn : 0 ≤ L_ST * dist V V' + β_S_eff * dist W W' :=
    add_nonneg (mul_nonneg hL_ST_nn dist_nonneg)
      (mul_nonneg hβ_S_eff_nn dist_nonneg)
  rw [BoundedContinuousFunction.dist_le h_rhs_nn]
  intro x
  rw [Real.dist_eq]
  exact h_pt V V' W W' x

end ValueClass2

/-- **Conditional `jointSenderOp_sub` operator-level row-Lipschitz.**
Given a pointwise row-Lipschitz hypothesis on the Sender integrand
under varying `(V_T, V_S)`, lifts to BCF metric. The pointwise
hypothesis itself is the irreducible primitive — at a concrete
payoff class, it is discharged from `L_α_VT, L_α_VS, L_U_a` via
direct algebraic decomposition (cf. `JointLipschitz` for the Target
template).

Since round BH1.2 (2026-10-06) a corollary of the two-carrier form
`ValueClass2.jointSenderOp_sub_row_lipschitz_of_pointwise` at the homogeneous
bridge `D.toValueClass2`. Statement unchanged. General in `F`. -/
theorem jointSenderOp_sub_row_lipschitz_of_pointwise
    {D : p.ValueClass} (h_inv : D.IsInvariant)
    {L_ST β_S_eff : ℝ}
    (hL_ST_nn : 0 ≤ L_ST) (hβ_S_eff_nn : 0 ≤ β_S_eff)
    (h_pt : ∀ V W V' W' : D.Carrier, ∀ x : ↥(Sanctions.S : Set ℝ),
        |(p.bellmanS_BCF (D.α_on V W) (D.α_on_continuous V W) W.val) x
          - (p.bellmanS_BCF (D.α_on V' W') (D.α_on_continuous V' W') W'.val) x|
          ≤ L_ST * dist V V' + β_S_eff * dist W W')
    (V W V' W' : D.Carrier) :
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ L_ST * dist V V' + β_S_eff * dist W W' :=
  D.toValueClass2.jointSenderOp_sub_row_lipschitz_of_pointwise
    (D.toValueClass2_IsInvariant h_inv) hL_ST_nn hβ_S_eff_nn
    (fun V₁ V₂ W₁ W₂ x => h_pt V₁ W₁ V₂ W₂ x) V V' W W'

/-! ## 4. Carrier-closed dischargers via `SigmaDynLipschitzOn` /
`AlphaOnLipschitzOn`

The Phase 1 (`jointTargetOp_sub_row_lipschitz`) theorem takes the
σ_dyn-Lipschitz hypothesis in the global form
`∀ V_S V_S' : Val, ...`. With `SigmaDynLipschitzOn D L_σ`
(`LipschitzPrimitives`) restricting the Lipschitz constraint to the
value-class carrier, we get a strictly **weaker** input requirement
on the user — exactly what the audit's Rule-3 "weakening refactor"
category calls for.

The companion Sender-side theorem
`jointSenderOp_sub_row_lipschitz_of_alphaOn` discharges the
previously-conditional `jointSenderOp_sub_row_lipschitz_of_pointwise`
hypothesis from `AlphaOnLipschitzOn D L_α_VT L_α_VS` plus a primitive
Lipschitz constant `L_U_a` for the Sender stage payoff in the leader
action `a`.

Since round BH1.2 (2026-10-06) the primary forms are on `ValueClass2`, with the
selector bound over `carrier_T × carrier_S` at feasible states and the stage
bound on `S × I × I × I`; the Target-side carrier form with `σ_dyn` Lipschitz
over `carrier_S` on `S × I` is
`ValueClass2.jointTargetOp_sub_row_lipschitz_generalF`. -/


namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-- **Sender row on the two-carrier class from a leader-selector Lipschitz
bound, with local hypotheses (round BH1.2, 2026-10-06).**

```
dist (jointSenderOp_sub (V, W)) (jointSenderOp_sub (V', W'))
  ≤ (L_U_a · L_α_VT) · dist V V' + (L_U_a · L_α_VS + β_S) · dist W W'
```

for Target values `V, V'` in `carrier_T` and Sender values `W, W'` in
`carrier_S`.

Plain language: the Sender's Bellman update responds to the Target's value only
through the Target's compliance choice, which moves by at most `L_α_VT` per unit
of Target-value change, and each unit of compliance moves the Sender's stage
payoff by at most `L_U_a`; it responds to its own value through the same channel
plus the direct discounted continuation `β_S`. The inputs are asked only where
they are read: the leader selector Lipschitz over `carrier_T × carrier_S` at
feasible states (`ValueClass2.AlphaOnLipschitzOn`), and the Sender stage payoff
Lipschitz in the Target action on `S × I × I × I` (state, sanction and both
actions feasible; the selector takes values in `I`). Compared with the
single-carrier `Params.jointSenderOp_sub_row_lipschitz_of_alphaOn`, which it
implies through `ValueClass.toValueClass2`, it drops the selector bound at
infeasible states, the stage bound off `S × I × I × I`, and the requirement
that both values share one carrier. General in `F`. -/
theorem jointSenderOp_sub_row_lipschitz_of_alphaOn
    (h_inv : D.IsInvariant)
    {L_α_VT L_α_VS L_U_a : ℝ}
    (hL_U_a_nn : 0 ≤ L_U_a)
    (hL_α_VT_nn : 0 ≤ L_α_VT) (hL_α_VS_nn : 0 ≤ L_α_VS)
    (h_α_lip : D.AlphaOnLipschitzOn L_α_VT L_α_VS)
    (h_U_S_lip_a : ∀ x ∈ Sanctions.S, ∀ s ∈ Sanctions.I,
        ∀ a ∈ Sanctions.I, ∀ a' ∈ Sanctions.I,
          |p.U_S x a s - p.U_S x a' s| ≤ L_U_a * |a - a'|)
    (V V' : D.CarrierT) (W W' : D.CarrierS) :
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ (L_U_a * L_α_VT) * dist V V'
        + (L_U_a * L_α_VS + p.β_S) * dist W W' := by
  apply D.jointSenderOp_sub_row_lipschitz_of_pointwise h_inv
    (mul_nonneg hL_U_a_nn hL_α_VT_nn)
    (add_nonneg (mul_nonneg hL_U_a_nn hL_α_VS_nn) p.β_S_mem.1)
  intro V V' W W' x
  have hβS_nn : 0 ≤ p.β_S := p.β_S_mem.1
  -- BCF apply at x.
  have h_apply_VW :
      p.bellmanS_BCF (D.α_on V W) (D.α_on_continuous V W) W.val x =
        sSup ((fun s => p.integrandS (D.α_on V W) (fun y => W.val y)
                          (x.val, s)) '' Sanctions.I) := rfl
  have h_apply_V'W' :
      p.bellmanS_BCF (D.α_on V' W') (D.α_on_continuous V' W') W'.val x =
        sSup ((fun s => p.integrandS (D.α_on V' W') (fun y => W'.val y)
                          (x.val, s)) '' Sanctions.I) := rfl
  -- Pointwise integrand bound, read only at the feasible state `x` and
  -- sanctions `s ∈ I`.
  have h_int_diff : ∀ s ∈ Sanctions.I,
      |p.integrandS (D.α_on V W) (fun y => W.val y) (x.val, s)
        - p.integrandS (D.α_on V' W') (fun y => W'.val y) (x.val, s)|
        ≤ (L_U_a * L_α_VT) * dist V V'
          + (L_U_a * L_α_VS + p.β_S) * dist W W' := by
    intro s hs
    simp only [integrandS]
    have hdecomp :
        (p.U_S x.val (D.α_on V W x.val) s
            + p.β_S * W.val (Sanctions.clipS' (p.F x.val s)))
          - (p.U_S x.val (D.α_on V' W' x.val) s
              + p.β_S * W'.val (Sanctions.clipS' (p.F x.val s)))
        = (p.U_S x.val (D.α_on V W x.val) s
            - p.U_S x.val (D.α_on V' W' x.val) s)
          + p.β_S * (W.val (Sanctions.clipS' (p.F x.val s))
                     - W'.val (Sanctions.clipS' (p.F x.val s))) :=
      by ring
    rw [hdecomp]
    -- U_S-Lipschitz in the Target action, at feasible arguments.
    have h_U_step :
        |p.U_S x.val (D.α_on V W x.val) s
          - p.U_S x.val (D.α_on V' W' x.val) s|
          ≤ L_U_a * |D.α_on V W x.val - D.α_on V' W' x.val| :=
      h_U_S_lip_a x.val x.property s hs
        (D.α_on V W x.val) (D.α_on_mem V W x.val)
        (D.α_on V' W' x.val) (D.α_on_mem V' W' x.val)
    -- Selector Lipschitz over the two carriers, at the feasible state.
    have h_α_step :
        |D.α_on V W x.val - D.α_on V' W' x.val|
          ≤ L_α_VT * dist V V' + L_α_VS * dist W W' :=
      h_α_lip V V' W W' x.val x.property
    have h_U_combined :
        |p.U_S x.val (D.α_on V W x.val) s
          - p.U_S x.val (D.α_on V' W' x.val) s|
          ≤ L_U_a * (L_α_VT * dist V V' + L_α_VS * dist W W') := by
      calc |p.U_S x.val (D.α_on V W x.val) s
              - p.U_S x.val (D.α_on V' W' x.val) s|
          ≤ L_U_a * |D.α_on V W x.val - D.α_on V' W' x.val| := h_U_step
        _ ≤ L_U_a * (L_α_VT * dist V V' + L_α_VS * dist W W') :=
            mul_le_mul_of_nonneg_left h_α_step hL_U_a_nn
    -- β_S * V_S diff: bound by β_S * dist W W' via BCF pointwise.
    have h_V_step :
        |W.val (Sanctions.clipS' (p.F x.val s))
          - W'.val (Sanctions.clipS' (p.F x.val s))|
          ≤ dist W W' := by
      have h_BCF :=
        BoundedContinuousFunction.dist_coe_le_dist (f := W.val) (g := W'.val)
          (Sanctions.clipS' (p.F x.val s))
      rw [Real.dist_eq] at h_BCF
      have hd_W : dist W.val W'.val = dist W W' := by rw [Subtype.dist_eq]
      rw [hd_W] at h_BCF
      exact h_BCF
    have h_βV_step :
        |p.β_S * (W.val (Sanctions.clipS' (p.F x.val s))
                   - W'.val (Sanctions.clipS' (p.F x.val s)))|
          ≤ p.β_S * dist W W' := by
      rw [abs_mul, abs_of_nonneg hβS_nn]
      exact mul_le_mul_of_nonneg_left h_V_step hβS_nn
    calc |(p.U_S x.val (D.α_on V W x.val) s
            - p.U_S x.val (D.α_on V' W' x.val) s)
          + p.β_S * (W.val (Sanctions.clipS' (p.F x.val s))
                     - W'.val (Sanctions.clipS' (p.F x.val s)))|
        ≤ |p.U_S x.val (D.α_on V W x.val) s
            - p.U_S x.val (D.α_on V' W' x.val) s|
          + |p.β_S * (W.val (Sanctions.clipS' (p.F x.val s))
                       - W'.val (Sanctions.clipS' (p.F x.val s)))| :=
            abs_add_le _ _
      _ ≤ L_U_a * (L_α_VT * dist V V' + L_α_VS * dist W W')
          + p.β_S * dist W W' := by
            exact add_le_add h_U_combined h_βV_step
      _ = (L_U_a * L_α_VT) * dist V V'
          + (L_U_a * L_α_VS + p.β_S) * dist W W' := by ring
  -- Convert pointwise to sup-difference at BCF level.
  rw [h_apply_VW, h_apply_V'W']
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := (L_U_a * L_α_VT) * dist V V'
            + (L_U_a * L_α_VS + p.β_S) * dist W W')
    (Bf := sSup ((fun s => p.integrandS (D.α_on V W) (fun y => W.val y)
                            (x.val, s)) '' Sanctions.I))
    (Bg := sSup ((fun s => p.integrandS (D.α_on V' W') (fun y => W'.val y)
                            (x.val, s)) '' Sanctions.I))
  · intro s hs; exact h_int_diff s hs
  · intro s hs
    exact le_csSup
      (p.integrandS_image_bddAbove (D.α_on_continuous V W) W.val.continuous x.val)
      ⟨s, hs, rfl⟩
  · intro s hs
    exact le_csSup
      (p.integrandS_image_bddAbove (D.α_on_continuous V' W') W'.val.continuous x.val)
      ⟨s, hs, rfl⟩

end ValueClass2

/-- **`jointSenderOp_sub` row-Lipschitz from `AlphaOnLipschitzOn` + a
Sender stage payoff Lipschitz primitive in the leader action `a`.**
Discharges `jointSenderOp_sub_row_lipschitz_of_pointwise`'s pointwise
hypothesis by direct algebraic decomposition:

```
|integrandS (α_on V W) V x s - integrandS (α_on V' W') W' x s|
  ≤ |U_S(x, α V W x, s) - U_S(x, α V' W' x, s)|
    + β_S · |V (clipS' F) - W' (clipS' F)|
  ≤ L_U_a · (L_α_VT · dist V V' + L_α_VS · dist W W')
    + β_S · dist W W'
  = (L_U_a · L_α_VT) · dist V V'
    + (L_U_a · L_α_VS + β_S) · dist W W'.
```

The lift to the BCF metric is by sup-difference (applied to the
sSup over `s ∈ I` of `integrandS`).

`L_U_a` is the canonical Sender stage payoff Lipschitz constant in
`a`; at a concrete payoff class it is computed directly.

Since round BH1.2 (2026-10-06) a corollary of the two-carrier form
`ValueClass2.jointSenderOp_sub_row_lipschitz_of_alphaOn` at the homogeneous
bridge `D.toValueClass2`: the selector bound is transported by
`AlphaOnLipschitzOn.toValueClass2` and the stage bound is restricted to
`S × I × I × I`. Statement unchanged. General in `F`. -/
theorem jointSenderOp_sub_row_lipschitz_of_alphaOn
    {D : p.ValueClass} (h_inv : D.IsInvariant)
    {L_α_VT L_α_VS L_U_a : ℝ}
    (hL_U_a_nn : 0 ≤ L_U_a)
    (hL_α_VT_nn : 0 ≤ L_α_VT) (hL_α_VS_nn : 0 ≤ L_α_VS)
    (h_α_lip : p.AlphaOnLipschitzOn D L_α_VT L_α_VS)
    (h_U_S_lip_a : ∀ x s : ℝ, ∀ a a' : ℝ,
        |p.U_S x a s - p.U_S x a' s| ≤ L_U_a * |a - a'|)
    (V W V' W' : D.Carrier) :
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ (L_U_a * L_α_VT) * dist V V'
        + (L_U_a * L_α_VS + p.β_S) * dist W W' :=
  D.toValueClass2.jointSenderOp_sub_row_lipschitz_of_alphaOn
    (D.toValueClass2_IsInvariant h_inv) hL_U_a_nn hL_α_VT_nn hL_α_VS_nn
    h_α_lip.toValueClass2 (fun x _ s _ a _ a' _ => h_U_S_lip_a x s a a')
    V V' W W'

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
