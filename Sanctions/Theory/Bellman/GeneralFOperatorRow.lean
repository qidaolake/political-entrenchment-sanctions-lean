/-
Sanctions/Theory/Bellman/GeneralFOperatorRow.lean

**The Target row of the joint row-Lipschitz matrix, general in the transition.**

## What was affine, and why

The coupled-contraction (Schur / Perov) argument needs a 2x2 matrix of
row-Lipschitz constants for the joint Bellman operator pair. Its **Sender** row
has been general in `F` for some time —
`Theory/Bellman/OperatorRowLipschitz.jointSenderOp_sub_row_lipschitz_of_alphaOn`
carries no affineness in its signature or its proof. Its **Target** row was not:
`Examples/AffineInstance/Bridges.jointTargetOp_sub_row_lipschitz` carries
`hF : p.F = affineF p.δ` and a bare `p.δ` in the bound, and has **no consumers**
tree-wide, precisely because everything downstream is trying to be general.

Inspecting that proof, `hF` does exactly one thing. The chain being bounded is:
a change in the Sender's value function moves its best response by at most
`L_σ`; that moves the Target's current payoff by at most `L_U`; and it moves
**next period's political state**, where `V_T` (state-Lipschitz with constant
`K_V`) is evaluated and discounted by `β_T`. Only the last link touches the
transition, and only through

    dist (clipS' (F x s)) (clipS' (F x s'))  ≤  δ · |s - s'|,

which under the affine law holds as an *equality*. Nothing in the argument uses
more than the `≤`.

## What replaces it

`SanctionUpperChord p.F d` — raising the sanction raises next period's
entrenchment by **at most** `d` times the increase — together with the maintained
primitive `Params.F_mono_s` that it never lowers it. Those two give the absolute
bound (`TransitionChords.abs_sub_le_of_upperChord`), and the rate `d` replaces
`p.δ` in the conclusion.

**Only the ceiling is needed here.** `TransitionChords.dist_le_of_chords` requires
both chords because, without monotonicity, a two-sided bound needs a floor too;
`F_mono_s` supplies the floor for free. And `0 ≤ d` need not be assumed — it is
read off the unit square (`sanctionUpperChord_nonneg`).

## Rule 3 — the assumption surface, stated

This **deletes** `hF` and **adds** `SanctionUpperChord p.F d`. Counted in symbols
that is a swap; measured against what it assumes it is a **net weakening**, which
is Rule 13's de-affining clause: the affine law implies the chord at rate `δ`
(`Examples/AffineInstance/Certificates` already discharges exactly that), and the
converse fails — `quadBumpF`, `ratchetF` and `wobbleF` all satisfy chords without
being affine. So these theorems hold at strictly more economies than the affine
ones, and the drift fence must not revert them on the symbol count.

Economically the chord says: *the political technology's responsiveness to
sanctions has a finite ceiling.* One extra unit of pressure cannot shift
entrenchment by more than `d`. It rules out a knife-edge transition — a threshold
at which entrenchment jumps discontinuously — but imposes no functional form:
diminishing returns, increasing returns and plateaus all survive under the
ceiling.

## Two carriers and local hypotheses (round BH1.2, 2026-10-06)

The pointwise bound and its operator lift were first stated with every
hypothesis global: the Sender's best response `σ_dyn` Lipschitz in its value
at every real state and action and for every bounded continuous value, the
Target's stage payoff Lipschitz in the sanction on all of `ℝ⁴`, and one
carrier for both values.
The argument reads none of that outside the model. It evaluates `σ_dyn` only
at a feasible state `x ∈ S` and a feasible Target action `a ∈ I`, for Sender
values in the carrier, and it evaluates `U_T` only at `x ∈ S`, `a ∈ I` and
sanctions `s, s' ∈ I` (both best responses lie in `I`).

So the primary forms are now:

* `joint_T_integrand_pointwise_row_lipschitz_generalF_local` — the pointwise
  bound with the `σ_dyn` bound at the one `(x, a)` it is used at and `U_T`
  Lipschitz on feasible sanctions at that `(x, a)`;
* `ValueClass2.jointTargetOp_sub_row_lipschitz_generalF` — the Target row on
  the two-carrier class `ValueClass2`, with `σ_dyn` Lipschitz over
  `carrier_S` on `S × I` (`ValueClass2.SigmaDynLipschitzOn`), `U_T` Lipschitz
  on `S × I × I × I`, and the state-Lipschitz bound only for Target values in
  `carrier_T`.

The original single-carrier, global statements are kept unchanged as
corollaries, as is the affine row in `Examples/AffineInstance/Bridges.lean`,
which is now an instance of these.

## Rule 22

General in `F`. The affine law is one instance of the hypothesis, not a
hypothesis.
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Equilibrium.JointExistenceFromPrimitives
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.SupDiff
import Sanctions.Theory.Bellman.LipschitzPrimitives

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Pointwise Target row-Lipschitz, general in `F` -/

/-- **Pointwise row-Lipschitz of the joint Target integrand, general in `F`,
with local hypotheses (round BH1.2, 2026-10-06).**

At a feasible state `x ∈ S` and a Target action `a`, the joint Target integrand
moves by at most `β_T` times the change in the Target value plus
`L_σ · (L_U + β_T · K_V · d)` times the change in the Sender value, where `d` is
the sanction upper-chord rate of the transition.

Plain language: a change in the Sender's value function moves its sanction by at
most `L_σ` per unit; that sanction change moves the Target's stage payoff by at
most `L_U` per unit and next period's state by at most `d` per unit, where the
Target value is `K_V`-Lipschitz. The hypotheses are asked only where they are
used. The `σ_dyn` bound is needed at this one `(x, a)`, and the stage payoff
`U_T x a ·` need only be `L_U`-Lipschitz on feasible sanctions `I`, since both
best responses lie there. Compared with
`joint_T_integrand_pointwise_row_lipschitz_generalF`, which it implies, this
drops the `σ_dyn` bound at every other state, action and value, and the stage
Lipschitz bound off `{x} × {a} × I × I`. General in `F`. -/
theorem joint_T_integrand_pointwise_row_lipschitz_generalF_local
    {d : ℝ} (hchord : Sanctions.TransitionChords.SanctionUpperChord p.F d)
    (V_T V_S V_T' V_S' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ)
    (h_σ_lipschitz : |p.σ_dyn V_S x a - p.σ_dyn V_S' x a|
                              ≤ L_σ * dist V_S V_S')
    (h_U_lipschitz : ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I,
        |p.U_T x a s - p.U_T x a s'| ≤ L_U * |s - s'|)
    (h_V_T_lipschitz : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
        |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂) :
    |p.joint_T_integrand V_T V_S x a - p.joint_T_integrand V_T' V_S' x a|
      ≤ p.β_T * dist V_T V_T'
        + L_σ * (L_U + p.β_T * K_V * d) * dist V_S V_S' := by
  have hd_nn : 0 ≤ d :=
    Sanctions.TransitionChords.sanctionUpperChord_nonneg hchord p.F_mono_s
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  simp only [joint_T_integrand]
  set s := p.σ_dyn V_S x a with hs_def
  set s' := p.σ_dyn V_S' x a with hs'_def
  set y := Sanctions.clipS' (p.F x s) with hy_def
  set y' := Sanctions.clipS' (p.F x s') with hy'_def
  -- Split the difference into stage and continuation parts.
  have h_decomp :
      |p.U_T x a s + p.β_T * V_T y - (p.U_T x a s' + p.β_T * V_T' y')|
        ≤ |p.U_T x a s - p.U_T x a s'| + p.β_T * |V_T y - V_T' y'| := by
    have h_eq : p.U_T x a s + p.β_T * V_T y - (p.U_T x a s' + p.β_T * V_T' y')
              = (p.U_T x a s - p.U_T x a s') + p.β_T * (V_T y - V_T' y') := by
      ring
    rw [h_eq]
    calc |(p.U_T x a s - p.U_T x a s') + p.β_T * (V_T y - V_T' y')|
        ≤ |p.U_T x a s - p.U_T x a s'| + |p.β_T * (V_T y - V_T' y')| :=
            abs_add_le _ _
      _ = |p.U_T x a s - p.U_T x a s'| + p.β_T * |V_T y - V_T' y'| := by
            rw [abs_mul, abs_of_nonneg hβ_T_nn]
  -- Stage part: both best responses are feasible sanctions.
  have h_U_bound : |p.U_T x a s - p.U_T x a s'| ≤ L_U * L_σ * dist V_S V_S' := by
    calc |p.U_T x a s - p.U_T x a s'|
        ≤ L_U * |s - s'| :=
          h_U_lipschitz s (p.σ_dyn_mem V_S x a) s' (p.σ_dyn_mem V_S' x a)
      _ ≤ L_U * (L_σ * dist V_S V_S') :=
          mul_le_mul_of_nonneg_left h_σ_lipschitz hL_U_nn
      _ = L_U * L_σ * dist V_S V_S' := by ring
  -- Continuation part: this is the only step that touches the transition.
  have h_dist_y : dist y y' ≤ d * |s - s'| := by
    calc dist y y'
        ≤ |p.F x s - p.F x s'| := Sanctions.clipS'_lipschitz_dist _ _
      _ ≤ d * |s - s'| :=
          Sanctions.TransitionChords.abs_sub_le_of_upperChord hchord p.F_mono_s
            hx (p.σ_dyn_mem V_S x a) (p.σ_dyn_mem V_S' x a)
  have h_V_T_bound : |V_T y - V_T' y'|
      ≤ K_V * d * L_σ * dist V_S V_S' + dist V_T V_T' := by
    have h_tri : |V_T y - V_T' y'| ≤ |V_T y - V_T y'| + |V_T y' - V_T' y'| := by
      calc |V_T y - V_T' y'|
          = |V_T y - V_T y' + (V_T y' - V_T' y')| := by ring_nf
        _ ≤ |V_T y - V_T y'| + |V_T y' - V_T' y'| := abs_add_le _ _
    have h_V_T_part : |V_T y - V_T y'| ≤ K_V * dist y y' := h_V_T_lipschitz y y'
    have h_BCF_part : |V_T y' - V_T' y'| ≤ dist V_T V_T' := by
      have := BoundedContinuousFunction.dist_coe_le_dist (f := V_T) (g := V_T') y'
      rwa [Real.dist_eq] at this
    have h_K_V_part : K_V * dist y y' ≤ K_V * d * L_σ * dist V_S V_S' := by
      calc K_V * dist y y'
          ≤ K_V * (d * |s - s'|) := mul_le_mul_of_nonneg_left h_dist_y hK_V_nn
        _ = K_V * d * |s - s'| := by ring
        _ ≤ K_V * d * (L_σ * dist V_S V_S') := by
            apply mul_le_mul_of_nonneg_left h_σ_lipschitz
            exact mul_nonneg hK_V_nn hd_nn
        _ = K_V * d * L_σ * dist V_S V_S' := by ring
    linarith
  calc |p.U_T x a s + p.β_T * V_T y - (p.U_T x a s' + p.β_T * V_T' y')|
      ≤ |p.U_T x a s - p.U_T x a s'| + p.β_T * |V_T y - V_T' y'| := h_decomp
    _ ≤ L_U * L_σ * dist V_S V_S'
        + p.β_T * (K_V * d * L_σ * dist V_S V_S' + dist V_T V_T') := by
          exact add_le_add h_U_bound
            (mul_le_mul_of_nonneg_left h_V_T_bound hβ_T_nn)
    _ = p.β_T * dist V_T V_T'
        + L_σ * (L_U + p.β_T * K_V * d) * dist V_S V_S' := by ring

/-- **Pointwise row-Lipschitz of the joint Target integrand, general in `F`.**

The general-`F` sibling of
`Examples/AffineInstance/Bridges.joint_T_integrand_pointwise_row_lipschitz`,
with `hF : p.F = affineF p.δ` replaced by an upper sanction chord at rate `d`,
and `p.δ` replaced by `d` in the bound.

One hypothesis is genuinely new relative to the affine statement: `hx`, that the
state is feasible. The affine bound held at every real `x` because the affine
identity does; a chord is a statement about the feasible square, so the general
form is stated there. That is where the model lives in any case.

Since round BH1.2 (2026-10-06) a corollary of
`joint_T_integrand_pointwise_row_lipschitz_generalF_local`, which asks for the
`σ_dyn` bound only at `(x, a)` and the stage Lipschitz bound only on feasible
sanctions there. Statement unchanged. General in `F`. -/
theorem joint_T_integrand_pointwise_row_lipschitz_generalF
    {d : ℝ} (hchord : Sanctions.TransitionChords.SanctionUpperChord p.F d)
    (V_T V_S V_T' V_S' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V)
    (h_σ_lipschitz : ∀ x a, |p.σ_dyn V_S x a - p.σ_dyn V_S' x a|
                              ≤ L_σ * dist V_S V_S')
    (h_U_lipschitz : ∀ x a s s', |p.U_T x a s - p.U_T x a s'|
                                    ≤ L_U * |s - s'|)
    (h_V_T_lipschitz : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
        |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    |p.joint_T_integrand V_T V_S x a - p.joint_T_integrand V_T' V_S' x a|
      ≤ p.β_T * dist V_T V_T'
        + L_σ * (L_U + p.β_T * K_V * d) * dist V_S V_S' :=
  p.joint_T_integrand_pointwise_row_lipschitz_generalF_local hchord
    V_T V_S V_T' V_S' hL_U_nn hK_V_nn hx a (h_σ_lipschitz x a)
    (fun s _ s' _ => h_U_lipschitz x a s s') h_V_T_lipschitz

/-! ## 2. Operator-level Target row-Lipschitz, general in `F`

Lifted to the BCF metric by the sup-difference inequality, exactly as the affine
sibling. This is the second row of the Schur matrix; with
`jointSenderOp_sub_row_lipschitz_of_alphaOn` supplying the first, both rows are
now available without an affine transition.

The primary form (round BH1.2, 2026-10-06) is on the two-carrier class
`ValueClass2`, with every hypothesis asked only where it is read; the original
single-carrier, global form follows as a corollary through
`ValueClass.toValueClass2`. -/

namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-- **Operator-level Target row-Lipschitz on the two-carrier class, general in
`F`, with local hypotheses (round BH1.2, 2026-10-06).**

```
dist (jointTargetOp_sub (V, W)) (jointTargetOp_sub (V', W'))
  ≤ β_T · dist V V' + L_σ · (L_U + β_T · K_V · d) · dist W W'
```

for Target values `V, V'` in `carrier_T` and Sender values `W, W'` in
`carrier_S`, with `d` the sanction upper-chord rate.

Plain language: the Target's Bellman update responds to its own continuation
value at the discount rate `β_T`, and to the Sender's value only through the
Sender's sanction choice, by at most `L_σ · (L_U + β_T · K_V · d)`. The three
regularity inputs are asked only where they are read: `σ_dyn` Lipschitz over
the Sender carrier at feasible states and Target actions
(`ValueClass2.SigmaDynLipschitzOn`), the Target stage payoff Lipschitz in the
sanction on `S × I × I × I`, and the state-Lipschitz bound for Target values in
`carrier_T` only. Compared with the single-carrier
`Params.jointTargetOp_sub_row_lipschitz_generalF`, it drops the `σ_dyn` bound
for values outside the Sender carrier and at infeasible states and actions, the
stage bound off `S × I × I × I`, and the requirement that both values share one
carrier. The bound has the shape `exists_fixedPoint_in_carrier_schur` consumes.
General in `F`. -/
theorem jointTargetOp_sub_row_lipschitz_generalF
    {d : ℝ} (hchord : Sanctions.TransitionChords.SanctionUpperChord p.F d)
    (h_inv : D.IsInvariant)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V) (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lip : D.SigmaDynLipschitzOn L_σ)
    (h_U_lipschitz : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I,
          |p.U_T x a s - p.U_T x a s'| ≤ L_U * |s - s'|)
    (h_V_T_lipschitz_carrier : ∀ V_T ∈ D.carrier_T,
        ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    (V V' : D.CarrierT) (W W' : D.CarrierS) :
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ p.β_T * dist V V'
        + L_σ * (L_U + p.β_T * K_V * d) * dist W W' := by
  have hd_nn : 0 ≤ d :=
    Sanctions.TransitionChords.sanctionUpperChord_nonneg hchord p.F_mono_s
  have hβT_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_dist_subtype :
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        = dist (D.jointTargetOp_sub h_inv (V, W)).val
                (D.jointTargetOp_sub h_inv (V', W')).val := by
    rw [Subtype.dist_eq]
  rw [h_dist_subtype]
  change dist (p.jointTarget_BCF_on_S V.val W.val
                (D.sender_unique_on W.val W.property))
              (p.jointTarget_BCF_on_S V'.val W'.val
                (D.sender_unique_on W'.val W'.property))
          ≤ _
  have h_rhs_nn :
      0 ≤ p.β_T * dist V V' + L_σ * (L_U + p.β_T * K_V * d) * dist W W' := by
    have h_coef_nn : 0 ≤ L_σ * (L_U + p.β_T * K_V * d) := by
      apply mul_nonneg hL_σ_nn
      have : 0 ≤ p.β_T * K_V * d := mul_nonneg (mul_nonneg hβT_nn hK_V_nn) hd_nn
      linarith
    exact add_nonneg (mul_nonneg hβT_nn dist_nonneg)
      (mul_nonneg h_coef_nn dist_nonneg)
  rw [BoundedContinuousFunction.dist_le h_rhs_nn]
  intro x
  rw [Real.dist_eq]
  have h_apply_V :
      p.jointTarget_BCF_on_S V.val W.val (D.sender_unique_on W.val W.property) x =
        sSup ((fun a => p.joint_T_integrand V.val W.val x.val a) '' Sanctions.I) :=
    p.jointTarget_BCF_on_S_apply V.val W.val
      (D.sender_unique_on W.val W.property) x
  have h_apply_V' :
      p.jointTarget_BCF_on_S V'.val W'.val
          (D.sender_unique_on W'.val W'.property) x =
        sSup ((fun a => p.joint_T_integrand V'.val W'.val x.val a) ''
                Sanctions.I) :=
    p.jointTarget_BCF_on_S_apply V'.val W'.val
      (D.sender_unique_on W'.val W'.property) x
  rw [h_apply_V, h_apply_V']
  -- Pointwise bound, read only at the feasible state `x` and actions `a ∈ I`.
  have h_pt : ∀ a ∈ Sanctions.I,
      |p.joint_T_integrand V.val W.val x.val a
        - p.joint_T_integrand V'.val W'.val x.val a|
        ≤ p.β_T * dist V V'
          + L_σ * (L_U + p.β_T * K_V * d) * dist W W' := by
    intro a ha
    have h_pointwise :=
      p.joint_T_integrand_pointwise_row_lipschitz_generalF_local hchord
        V.val W.val V'.val W'.val hL_U_nn hK_V_nn x.property a
        (h_σ_lip W W' x.val x.property a ha)
        (h_U_lipschitz x.val x.property a ha)
        (h_V_T_lipschitz_carrier V.val V.property)
    have hd_V : dist V.val V'.val = dist V V' := by rw [Subtype.dist_eq]
    have hd_W : dist W.val W'.val = dist W W' := by rw [Subtype.dist_eq]
    rw [hd_V, hd_W] at h_pointwise
    exact h_pointwise
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := p.β_T * dist V V'
            + L_σ * (L_U + p.β_T * K_V * d) * dist W W')
    (Bf := sSup ((fun a => p.joint_T_integrand V.val W.val x.val a) ''
                  Sanctions.I))
    (Bg := sSup ((fun a => p.joint_T_integrand V'.val W'.val x.val a) ''
                  Sanctions.I))
  · intro a ha; exact h_pt a ha
  · intro a ha
    -- Continuity in the compliance level on `I` (compliance-local uniqueness).
    have h_cont_V :
        ContinuousOn (fun a : ℝ => p.joint_T_integrand V.val W.val x.val a)
          Sanctions.I :=
      p.joint_T_integrand_continuousOn_I_of_unique_on V.val W.val
        (D.sender_unique_on W.val W.property) x.property
    have h_bdd_V :
        BddAbove ((fun a => p.joint_T_integrand V.val W.val x.val a) ''
                    Sanctions.I) :=
      (isCompact_Icc.image_of_continuousOn h_cont_V).bddAbove
    exact le_csSup h_bdd_V ⟨a, ha, rfl⟩
  · intro a ha
    have h_cont_V' :
        ContinuousOn (fun a : ℝ =>
          p.joint_T_integrand V'.val W'.val x.val a) Sanctions.I :=
      p.joint_T_integrand_continuousOn_I_of_unique_on V'.val W'.val
        (D.sender_unique_on W'.val W'.property) x.property
    have h_bdd_V' :
        BddAbove ((fun a => p.joint_T_integrand V'.val W'.val x.val a) ''
                    Sanctions.I) :=
      (isCompact_Icc.image_of_continuousOn h_cont_V').bddAbove
    exact le_csSup h_bdd_V' ⟨a, ha, rfl⟩

end ValueClass2

/-- **Operator-level row-Lipschitz of `jointTargetOp_sub`, general in `F`.**

```
dist (jointTargetOp_sub (V, W)) (jointTargetOp_sub (V', W'))
  ≤ β_T · dist V V' + L_σ · (L_U + β_T · K_V · d) · dist W W'
```

with `d` the sanction upper-chord rate. The affine sibling is the case
`F = affineF δ`, `d = δ`.

Since round BH1.2 (2026-10-06) a corollary of the two-carrier form
`ValueClass2.jointTargetOp_sub_row_lipschitz_generalF` at the homogeneous
bridge `D.toValueClass2`: the global `σ_dyn` and stage Lipschitz bounds are
restricted to the carrier and to `S × I` (and `S × I × I × I`) before use.
Statement unchanged. General in `F`. -/
theorem jointTargetOp_sub_row_lipschitz_generalF
    {d : ℝ} (hchord : Sanctions.TransitionChords.SanctionUpperChord p.F d)
    {D : p.ValueClass} (h_inv : D.IsInvariant)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V) (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lipschitz : ∀ V_S V_S' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, ∀ x a,
        |p.σ_dyn V_S x a - p.σ_dyn V_S' x a| ≤ L_σ * dist V_S V_S')
    (h_U_lipschitz : ∀ x a s s',
        |p.U_T x a s - p.U_T x a s'| ≤ L_U * |s - s'|)
    (h_V_T_lipschitz_carrier : ∀ V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
        V_T ∈ D.carrier →
        ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    (V W V' W' : D.Carrier) :
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ p.β_T * dist V V'
        + L_σ * (L_U + p.β_T * K_V * d) * dist W W' :=
  D.toValueClass2.jointTargetOp_sub_row_lipschitz_generalF hchord
    (D.toValueClass2_IsInvariant h_inv) hL_U_nn hK_V_nn hL_σ_nn
    (fun W₁ W₂ y _ b _ => h_σ_lipschitz W₁.val W₂.val y b)
    (fun y _ b _ s _ s' _ => h_U_lipschitz y b s s')
    h_V_T_lipschitz_carrier V V' W W'

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
