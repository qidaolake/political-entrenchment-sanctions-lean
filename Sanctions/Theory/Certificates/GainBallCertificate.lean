/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Bellman.GainBallInvariance
import Sanctions.Theory.Certificates.StandardComplianceLocalDischargers

/-!
# Gain-ball carriers whose invariance is derived, not assumed

## ⚠ DEPRECATED 2026-08-19 — superseded by the semiconcave cone

**This route has zero consumers and, on the evidence below, cannot acquire one.**
It is retained because it compiles, is axiom-clean, and records a real negative
result; it must not be cited as a live route, and new work should use the
semiconcave-cone family instead (`DAU_on_cone`,
`Examples/SymbolicCertifiedFamilyGeneralF.lean`).

Four rounds established the obstruction, each closing a different door:

1. *Not the transition's curvature.* At the non-affine `qbParams` the Sender
   Lipschitz margin forces `K_S ≥ 200/37` while the shipped carrier has `16/3` —
   failing by exactly `4/75` — and any admissible pair obeys
   `g_S + 7600/5513 ≤ K_S`, so the carrier is necessarily **loose**.
2. *Not the choice of economy.* Every `U_S` in the tree with a live Sender state
   stake has an `s`-dependent `x`-slope; the four-group microfoundation has no
   bare-`x` term; the public-choice literature supplies the interaction rather
   than separability. The whole-square-floor versus corner-ceiling mismatch is
   structural.
3. *Not wiring.* Every discharge at a loose carrier needs argmax uniqueness, and
   uniqueness cannot be bought from concavity of the carrier: a
   Lipschitz-plus-slope band bounds slope but never curvature, so it contains the
   kink `y ↦ g·y + (K−g)·max 0 (y−1/2)`, which defeats strict concavity of the
   dynamic objective for **any** finite stage curvature. Machine-checked.
4. *Not composable with the route that does work.* `DAU_on_cone` obtains loose-cone
   uniqueness from a curvature ceiling plus the `hCurv` margin — but
   `gainBallValueClass2` hard-codes `carrier_S := valLipGainBall M_S K_S g_S 0`
   and consumes `h_unique_S` quantified over *exactly that ball*. A carrier
   intersected with a curvature clause is strictly smaller and cannot discharge a
   hypothesis over the whole ball. The two designs do not compose.

**What is NOT deprecated.** The carrier `valLipGainBall` itself is live and widely
used (`eeCarrierS`, `eeCarrierT`, and `mem_valLipGainBall_bellman_chord`), as are
the membership splitter, the closedness and nonemptiness lemmas, and the two
carrier-geometry facts (`..._V_S_lipschitz`, `..._V_S_monotone`). Only the
*derived-invariance route* built on top of them is deprecated.

Every constructor of `StandardComplianceLocalCoreCertificate_MS` opens with the
same two inputs:

```
(D : p.ValueClass2) (h_inv : D.IsInvariant)
```

Both are *assumed*. The second is the existence crux (Rule 15): without carrier
invariance there is no Bellman fixed point, hence no equilibrium, so a
certificate that hypothesises it rests the whole construction on an unproved
premise about the object it constructs. The first quietly assumes a carrier
exists with the uniqueness properties the route needs.

This file supplies both from payoff and transition data.

## Why the two carriers must be allowed to differ

The first version of this file used **one** gain ball for both players, so a
single `(M, K, g)` had to serve the Target and the Sender at once. That shape
does not fit economies, and `chord_forces_zero_slope_of_flat_stage` says why:
whenever the Sender's stage payoff does not move with the political state along
the leader's response, the Sender-side joint chord forces `g = 0` — at any
transition, because discounting alone cannot bootstrap a positive slope floor out
of a flat stage payoff. A Target with a strictly positive value slope and a
Sender with a state-independent stage payoff cannot then share a `g`.

That is not a corner case. It is the shape of the one economy in the tree that
already carries a gain-ball carrier: `polyComplianceValueClass2Gain` pairs
`valLipGainBall 12 (20/3) (20/3) 0` on the Target with a Sender carrier whose
Lipschitz constant is **zero**. So the carriers here take independent radii,
Lipschitz ceilings and slope floors, and the symmetric case is the diagonal.

## What the gain ball buys over the Lipschitz ball

Two certificate fields become carrier geometry rather than hypotheses:

* `hV_S_lip_carrier` — the Sender value is `K_S`-Lipschitz. True on either ball.
* `hV_S_mono_carrier` — the Sender value is monotone in the political state.
  This one is **not** available on the Lipschitz ball; it is what the slope floor
  adds. At `g_S = 0` the floor *is* monotonicity, so on the Sender side the gain
  ball can be the Lipschitz ball plus monotonicity and nothing more — which is
  both what the certificate needs and what flat-stage-payoff economies can
  supply.

Both balls are zero-based, which makes the basin condition free: preserving
`[0,1]` is `Params.F_mem`, already a field of `Params`.

## Generality in `F` (Rule 22)

No `hF`. The transition enters through `F_mono_x`, `F_mem`, a state-Lipschitz
bound, and the two joint chords — all satisfied by the affine law, none requiring
it.

## Rule compliance

* Rule 1 — the leader selector is the carrier-local argmax `α_on`; no strategy is
  fixed.
* Rule 3 — pure composition. Every hypothesis already appears in the theorems
  being composed.
* Rule 5 — parametric in `p` and every scalar; no witness appears.
* Rule 15 — invariance derived, not consumed.
-/

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The asymmetric gain-ball value class -/

/-- **Two zero-based gain balls as an asymmetric value class.** The Target
carrier holds values bounded by `M_T`, responding to the political state at rate
at most `K_T`, and rising at rate at least `g_T` as the state deepens; the Sender
carrier imposes the same three constraints at its own constants. Nothing ties the
two triples together — see the module header for why they must be free.

Round BJ4.3 (2026-10-08): the value class keeps only the compliance-local part
of `h_unique_S` (`toOnI`), which is all `ValueClass2.sender_unique_on` asks
for; the constructor's hypotheses are unchanged. -/
noncomputable def gainBallValueClass2
    {M_T K_T g_T M_S K_S g_S : ℝ}
    (h_ne_T : (valLipGainBall M_T K_T g_T 0).Nonempty)
    (h_ne_S : (valLipGainBall M_S K_S g_S 0).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M_T K_T g_T 0,
        ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.TargetArgmaxUnique V_T V_S) :
    p.ValueClass2 where
  carrier_T := valLipGainBall M_T K_T g_T 0
  carrier_S := valLipGainBall M_S K_S g_S 0
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := valLipGainBall_isClosed _ _ _ _
  nonempty_T := h_ne_T
  nonempty_S := h_ne_S
  sender_unique_on := fun V_S hV_S => (h_unique_S V_S hV_S).toOnI
  target_unique_on := h_unique_T

/-- **Carrier invariance for the asymmetric gain-ball class, from primitives.**

Each side is the same two-plus-one split
(`mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope`): sup-norm radius and
Lipschitz constant come from the Lipschitz-ball layer, the slope floor from the
cone layer. Because the underlying estimates are stated per value pair with
independent constants, letting the two carriers differ costs nothing.

Reading the inputs in English:

* `hU_T_cube` / `hU_S_cube` — the two stage payoffs are bounded on the feasible
  cube;
* `h_integrand_lipschitz_at_carrier` — the Target's joint integrand is
  `K_T`-Lipschitz in the state, uniformly in the action, at every carrier pair;
* `h_integrand_lowerSlope_at_carrier` — a deeper state raises that integrand by
  at least `g_T` per unit;
* `h_U_S_lip_at_α` — the Sender stage payoff composed with the leader selector is
  `L_U_S`-Lipschitz in the state;
* `h_joint_state_chord_at_carrier` — a deeper state raises the Sender's stage
  payoff *plus* the discounted value of the induced rise in next period's state
  by at least `g_S` per unit. Both channels counted together, which is strictly
  weaker than asking each to clear a bar of its own;
* `h_F_lip` — the transition is `γ_F`-Lipschitz in the state;
* the three margins — neither operator inflates its radius, and the Sender
  operator does not inflate its Lipschitz constant. -/
theorem gainBallValueClass2_IsInvariant
    {M_T K_T g_T M_S K_S g_S cube_T cube_S L_U_S γ_F : ℝ}
    (_hM_T : 0 ≤ M_T) (_hK_T : 0 ≤ K_T) (_hg_T : 0 ≤ g_T)
    (_hM_S : 0 ≤ M_S) (hK_S : 0 ≤ K_S)
    (_hcube_T : 0 ≤ cube_T) (_hcube_S : 0 ≤ cube_S) (_hγ_F : 0 ≤ γ_F)
    (h_ne_T : (valLipGainBall M_T K_T g_T 0).Nonempty)
    (h_ne_S : (valLipGainBall M_S K_S g_S 0).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M_T K_T g_T 0,
        ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.TargetArgmaxUnique V_T V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T.val V_S.val x₂.val a
          - p.joint_T_integrand V_T.val V_S.val x₁.val a|
          ≤ K_T * dist x₁ x₂)
    (h_integrand_lowerSlope_at_carrier :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        y₁.val ∈ Set.Icc (0 : ℝ) 1 → y₂.val ∈ Set.Icc (0 : ℝ) 1 → y₁ ≤ y₂ →
        g_T * dist y₁ y₂ ≤
          p.joint_T_integrand V_T.val V_S.val y₂.val a
          - p.joint_T_integrand V_T.val V_S.val y₁.val a)
    (h_U_S_lip_at_α :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
              h_unique_T).α_on V_T V_S x₂) s
          - p.U_S x₁ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
              h_unique_T).α_on V_T V_S x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_joint_state_chord_at_carrier :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Set.Icc (0 : ℝ) 1,
        ∀ y₂ ∈ Set.Icc (0 : ℝ) 1, y₁ ≤ y₂ →
        g_S * (y₂ - y₁)
          ≤ (p.U_S y₂ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
                  h_unique_T).α_on V_T V_S y₂) s
              - p.U_S y₁ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
                  h_unique_T).α_on V_T V_S y₁) s)
            + p.β_S * g_S * (p.F y₂ s - p.F y₁ s))
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_T_norm_margin : cube_T + p.β_T * M_T ≤ M_T)
    (h_S_norm_margin : cube_S + p.β_S * M_S ≤ M_S)
    (h_lip_margin : L_U_S + p.β_S * K_S * γ_F ≤ K_S) :
    (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).IsInvariant := by
  intro V_T V_S
  refine ⟨?_, ?_⟩
  · -- Target side: radius and Lipschitz from the ball layer, floor from the cone.
    refine mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope.mpr ⟨?_, ?_⟩
    · exact p.jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz V_T.val V_S.val
        (h_unique_S V_S.val V_S.property) V_T.property.1 hU_T_cube h_T_norm_margin
        (h_integrand_lipschitz_at_carrier V_T V_S)
    · exact p.jointTarget_BCF_lowerSlope_of_integrand_lowerSlope V_T.val V_S.val
        (h_unique_S V_S.val V_S.property) (h_integrand_lowerSlope_at_carrier V_T V_S)
  · -- Sender side: the same split, at the Sender's own constants.
    refine mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope.mpr ⟨?_, ?_⟩
    · exact p.bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
        ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
            h_unique_T).α_on_continuous V_T V_S)
        (fun x => (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
            h_unique_T).α_on_mem V_T V_S x)
        V_S.val hK_S (valLipGainBall_subset_valLipBall _ _ _ _ V_S.property)
        hU_S_cube (h_U_S_lip_at_α V_T V_S) h_F_lip h_S_norm_margin h_lip_margin
    · exact p.bellmanS_BCF_preserves_lowerSlopeCone_generalF_on
        ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
            h_unique_T).α_on_continuous V_T V_S)
        subset_rfl (fun x hx s hs => p.F_mem x s hx hs)
        (h_joint_state_chord_at_carrier V_T V_S) V_S.property.2.2

/-! ## Carrier fields that stop being assumptions -/

/-- **Carrier Lipschitz bound on the Sender gain ball is automatic.** -/
theorem gainBallValueClass2_V_S_lipschitz
    {M_T K_T g_T M_S K_S g_S : ℝ}
    (h_ne_T : (valLipGainBall M_T K_T g_T 0).Nonempty)
    (h_ne_S : (valLipGainBall M_S K_S g_S 0).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M_T K_T g_T 0,
        ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.TargetArgmaxUnique V_T V_S) :
    ∀ V_S ∈ (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
                h_unique_T).carrier_S,
      ValueLipschitzWith V_S K_S :=
  fun _ hV_S => hV_S.2.1

/-- **Carrier monotonicity on the Sender gain ball is automatic.**

This is the field the Lipschitz ball cannot supply; it is what the slope floor
adds. On a zero-based ball the floor applies at every pair of states, so
`V y₂ − V y₁ ≥ g_S · dist y₁ y₂ ≥ 0`: the Sender values a deeper political state
weakly more. What used to be the assumption `hV_S_mono_carrier` is carrier
geometry — and it needs only `g_S ≥ 0`, so the permissive choice `g_S = 0`
already buys it. -/
theorem gainBallValueClass2_V_S_monotone
    {M_T K_T g_T M_S K_S g_S : ℝ} (hg_S : 0 ≤ g_S)
    (h_ne_T : (valLipGainBall M_T K_T g_T 0).Nonempty)
    (h_ne_S : (valLipGainBall M_S K_S g_S 0).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M_T K_T g_T 0,
        ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.TargetArgmaxUnique V_T V_S) :
    ∀ V_S ∈ (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
                h_unique_T).carrier_S,
      Monotone V_S :=
  fun _ hV_S => monotone_of_mem_valLipGainBall hg_S hV_S

/-! ## Pinning the magnitudes that carry a margin

`gainBallValueClass2_IsInvariant` above leaves the six carrier magnitudes free.
That is the right generality for a theorem, but it leaves a caller six numbers to
guess. Three of them can be removed.

`Foundations/StokeyLucas.lean` carries the SLP closed forms --- the sup-norm
radius `M_U/(1-β)`, the Hinderer-4.2(c) Lipschitz ceiling `L_U/(1-β·γ_F)`, and the Hinderer-4.2(c)
Benveniste--Scheinkman slope floor `g_U/(1-β·γ_F)` --- with a docstring saying
that together they leave "nothing to choose by hand". The corollary below
assembles the first two: at `M_T = cube_T/(1-β_T)`, `M_S = cube_S/(1-β_S)` and
`K_S = L_U_S/(1-β_S·γ_F)` all three invariance margins discharge, two of them
with equality, so those are the *minimal* invariant magnitudes rather than merely
sufficient ones.

**The third closed form is deliberately not assembled here.** An earlier draft of
this section claimed the two slope floors were likewise pinned, as
`g_U_T/(1-β_T·γ_F)` and its Sender twin, and called the resulting asymmetry
"derived". That claim outran the Lean, in two separate ways, and the correction
is worth stating because the same trap is easy to re-enter.

First, the stage-slope-to-value-floor step is proved only at the affine law for
this operator: `bellmanS_BCF_preserves_lowerSlopeCone` carries `hF`, *and* its
sub-solution hypothesis `g ≤ m + β_S·g·(1-δ)` hard-wires the affine displacement
factor in the statement, so deleting `hF` alone would not generalise it. The
general-`F` siblings earn their generality by discarding the closed form
altogether, taking instead a joint chord with `g` on both sides.

Second, the multiplier in that closed form must be a **lower** chord rate on the
transition, whereas the `γ_F` appearing in this file is an **upper** Lipschitz
modulus (`h_F_lip`). The two coincide at the affine law and nowhere else, which
is exactly why substituting one for the other reads as harmless until the affine
case is left behind. The tree does have a slope-floor closed form surviving a
provably non-affine transition --- `mem_valLipGainBall_bellman_chord`, carried at
`wobbleEconF` --- but its rate is the lower rate of a chord *band*, and the band
constrains `F` only along the corner section `F(·,1)`.

What does hold at a general transition is the negative direction:
`chord_forces_zero_slope_of_flat_stage` needs only feasibility, and says a Sender
whose stage payoff ignores the political state admits a floor of exactly zero,
however patient it is. That is enough to establish what this file needs --- that
the two players cannot share a floor --- without any claim about what the floors
equal.
-/

/-- The Sender Lipschitz margin holds with equality at the Hinderer 4.2(c) closed form
`K_S = L_U_S/(1 - β_S·γ_F)`: pushing the stage modulus through one Bellman step
reproduces exactly the same constant, which is what makes the ball invariant
rather than merely large. -/
theorem bellmanLipConstant_lip_margin_eq {L_U_S γ_F : ℝ}
    (hden : 0 < 1 - p.β_S * γ_F) :
    L_U_S + p.β_S * (Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S)
        * γ_F
      = Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S := by
  unfold Sanctions.StokeyLucas.bellmanLipConstant
  have hne : (1 - p.β_S * γ_F) ≠ 0 := ne_of_gt hden
  field_simp
  ring

/-- Nonnegativity of the Hinderer-4.2(c) closed-form slope floor. -/
theorem bellmanLowerSlopeConstant_nonneg {β γ_F g_U : ℝ}
    (hg_U : 0 ≤ g_U) (hden : 0 < 1 - β * γ_F) :
    0 ≤ Sanctions.StokeyLucas.bellmanLowerSlopeConstant β γ_F g_U := by
  unfold Sanctions.StokeyLucas.bellmanLowerSlopeConstant
  exact div_nonneg hg_U (le_of_lt hden)

/-- A stage payoff cannot rise faster than its own Lipschitz modulus, so the
closed-form floor never exceeds the closed-form ceiling.  This is the condition
that keeps each gain ball inhabited: a ball whose floor outran its ceiling would
be empty. -/
theorem bellmanLowerSlopeConstant_le_bellmanLipConstant {β γ_F g_U L_U : ℝ}
    (hgL : g_U ≤ L_U) (hden : 0 < 1 - β * γ_F) :
    Sanctions.StokeyLucas.bellmanLowerSlopeConstant β γ_F g_U
      ≤ Sanctions.StokeyLucas.bellmanLipConstant β γ_F L_U := by
  unfold Sanctions.StokeyLucas.bellmanLowerSlopeConstant
    Sanctions.StokeyLucas.bellmanLipConstant
  gcongr

/-- **Carrier invariance at the closed-form magnitudes.**

The abstract economic representation of the theorem above: instead of six numbers
chosen by hand, the carrier magnitudes that carry a margin are *equated to their
SLP closed forms in the primitives*, and the three margins then hold
automatically --- two of them with equality, which is what makes these the
*minimal* invariant magnitudes rather than merely sufficient ones.

* `M_T = cube_T/(1-β_T)` and `M_S = cube_S/(1-β_S)` --- the smallest radii a
  bounded stage payoff can be trapped in, by the geometric series of its own
  discounting;
* `K_S = L_U_S/(1-β_S·γ_F)` --- the Hinderer 4.2(c) ceiling: the stage payoff's state
  modulus amplified by the discounted transition multiplier.

**What this theorem does not pin.** `K_T`, `g_T` and `g_S` carry no margin, so
they stay free real variables here; they are constrained only by the carrier
hypotheses the caller supplies. In particular the two *slope floors* are not
determined by this theorem, and the reader should not infer a closed form for
them from the two that are.

That caveat is load-bearing, because the obvious closed form for a slope floor is
**not** available at a general transition for this operator. The Hinderer 4.2(c)
envelope `floor = stage state-slope / (1 - β·γ)` is proved in
`bellmanS_BCF_preserves_lowerSlopeCone`, and that theorem is affine twice over:
it carries `hF`, and its sub-solution hypothesis `g ≤ m + β_S·g·(1-δ)` hard-wires
the affine displacement factor in the *statement*. The general-`F` siblings
(`bellmanS_BCF_preserves_lowerSlopeCone_generalF`, and on the Target side
`joint_T_integrand_lowerSlope_of_joint_chord`) buy their generality precisely by
deleting that closed form: they take a single joint chord in which `g` appears on
both sides, so the caller must supply a floor that already solves its own fixed
point.

There is one route in the tree where a slope-floor closed form does survive a
genuinely non-affine transition — `mem_valLipGainBall_bellman_chord`
(`Theory/Bellman/ChordInvariance.lean`), carried non-vacuously at the non-affine
`wobbleEconF`. Two things about it matter here. It is *corner-pinned*: the chord
band constrains `F` only along the section `F(·,1)`, not on the whole square. And
its rate is the band's **lower** chord rate, not `γ_F`: the `γ_F` of this theorem
is an *upper* Lipschitz modulus (`h_F_lip`), and upper and lower moduli coincide
only at the affine law, which is exactly why conflating them is invisible until
someone leaves the affine case.

What does survive at general `F` is the negative direction.
`chord_forces_zero_slope_of_flat_stage` needs nothing but feasibility: a Sender
whose stage payoff ignores the political state admits a floor of exactly zero,
however patient it is. Discounting cannot manufacture a stake the stage payoff
does not pay. That is why the two carriers need independent floors — but the
*positive* statement, that each floor equals its own stage slope over its own
discounted multiplier, is currently an affine-or-corner-pinned claim and is not
asserted here. -/
theorem gainBallValueClass2_IsInvariant_closedForm
    {M_T K_T g_T M_S K_S g_S cube_T cube_S L_U_S γ_F : ℝ}
    (hK_T : 0 ≤ K_T) (hg_T : 0 ≤ g_T)
    (hcube_T : 0 ≤ cube_T) (hcube_S : 0 ≤ cube_S)
    (hL_U_S : 0 ≤ L_U_S) (hγ_F : 0 ≤ γ_F)
    (hden_S : 0 < 1 - p.β_S * γ_F)
    (hM_T_def : M_T = p.carrierMinNormT cube_T)
    (hM_S_def : M_S = p.carrierMinNormS cube_S)
    (hK_S_def : K_S = Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S)
    (h_ne_T : (valLipGainBall M_T K_T g_T 0).Nonempty)
    (h_ne_S : (valLipGainBall M_S K_S g_S 0).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M_T K_T g_T 0,
        ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, p.TargetArgmaxUnique V_T V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T.val V_S.val x₂.val a
          - p.joint_T_integrand V_T.val V_S.val x₁.val a|
          ≤ K_T * dist x₁ x₂)
    (h_integrand_lowerSlope_at_carrier :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        y₁.val ∈ Set.Icc (0 : ℝ) 1 → y₂.val ∈ Set.Icc (0 : ℝ) 1 → y₁ ≤ y₂ →
        g_T * dist y₁ y₂ ≤
          p.joint_T_integrand V_T.val V_S.val y₂.val a
          - p.joint_T_integrand V_T.val V_S.val y₁.val a)
    (h_U_S_lip_at_α :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
              h_unique_T).α_on V_T V_S x₂) s
          - p.U_S x₁ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
              h_unique_T).α_on V_T V_S x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_joint_state_chord_at_carrier :
      ∀ (V_T : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierT)
        (V_S : (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).CarrierS),
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Set.Icc (0 : ℝ) 1,
        ∀ y₂ ∈ Set.Icc (0 : ℝ) 1, y₁ ≤ y₂ →
        g_S * (y₂ - y₁)
          ≤ (p.U_S y₂ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
                  h_unique_T).α_on V_T V_S y₂) s
              - p.U_S y₁ ((p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S
                  h_unique_T).α_on V_T V_S y₁) s)
            + p.β_S * g_S * (p.F y₂ s - p.F y₁ s))
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|) :
    (p.gainBallValueClass2 h_ne_T h_ne_S h_unique_S h_unique_T).IsInvariant := by
  subst hM_T_def hM_S_def hK_S_def
  exact p.gainBallValueClass2_IsInvariant
    (p.carrierMinNormT_nonneg hcube_T) hK_T hg_T
    (p.carrierMinNormS_nonneg hcube_S)
    (p.hKS_nonneg_of_closed_form hL_U_S hden_S)
    hcube_T hcube_S hγ_F h_ne_T h_ne_S h_unique_S h_unique_T
    hU_T_cube hU_S_cube h_integrand_lipschitz_at_carrier
    h_integrand_lowerSlope_at_carrier h_U_S_lip_at_α
    h_joint_state_chord_at_carrier h_F_lip
    (p.carrierMinNormT_margin cube_T)
    (p.carrierMinNormS_margin cube_S)
    (p.bellmanLipConstant_lip_margin_eq hden_S).le

/-! ## Axiom hygiene (Rule 10) -/

#print axioms gainBallValueClass2_IsInvariant
#print axioms gainBallValueClass2_IsInvariant_closedForm
#print axioms gainBallValueClass2_V_S_lipschitz
#print axioms gainBallValueClass2_V_S_monotone
#print axioms bellmanLipConstant_lip_margin_eq
#print axioms bellmanLowerSlopeConstant_le_bellmanLipConstant

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
