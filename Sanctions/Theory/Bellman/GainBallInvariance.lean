/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Bellman.SenderLowerSlopeCone

/-!
# Carrier invariance for the gain ball, from primitives

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

`Theory/Bellman/InvariantLipGainBall.lean` builds the gain-restricted carrier
`valLipGainBall M K g xT` and the structural discharger
`ofLipGainBall_IsInvariant_of_preservation`, which turns two operator-preservation
facts into `IsInvariant`.  `Theory/Bellman/SenderLowerSlopeCone.lean` supplies the
Sender-side slope preservation at a general transition.  What was missing is the
join: nothing composed those pieces, so every user of the gain-ball carrier still
had to supply `IsInvariant` by hand, economy by economy — the same gap
`ofLipBall_IsInvariant_of_primitives` closed for the Lipschitz ball.

This file closes it.  The organising observation is
`mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope`: membership in the gain
ball is membership in the Lipschitz ball *plus* the minimum upward state slope.
So each operator has to be shown to preserve two things that the Lipschitz-ball
layer already handles (sup-norm radius, Lipschitz constant) and one thing that is
genuinely new (the slope floor).  Each preservation theorem below is exactly that
two-plus-one.

## What is proved

* `h_T_preserves_gain_of_integrand` — the joint Target operator keeps the gain
  ball, from an integrand Lipschitz bound and an integrand slope floor at the
  carrier.
* `h_S_preserves_gain_of_payoff` — the joint Sender operator keeps the gain ball,
  from a payoff Lipschitz bound at the leader selector and a joint state chord.
* `ofLipGainBall_IsInvariant_of_primitives` — the composition: carrier invariance
  for the gain-ball value class, assuming nothing about the Bellman operators.
* `ofLipGainBall_IsInvariant_of_chords` — the same, with the Target-side integrand
  slope floor itself derived from a joint chord on the Target's realised payoff.

## Generality in `F` (Rule 22)

No result here carries `hF`.  The transition enters only through
`Params.F_mono_x` (already a field), a state-Lipschitz bound `h_F_lip`, the basin
condition `hB_inv`, and the two joint chords — all of which the affine law
satisfies but none of which requires it.  The drift fence
`joint_state_chord_of_stage_chord_and_affine` records that the affine hypotheses
imply the general chord, so nothing that used to be provable stopped being so.

## Rule compliance

* Rule 1 — structural: no strategy is fixed anywhere; the leader selector is the
  carrier-local argmax `α_on`.
* Rule 3 — pure composition.  Every hypothesis below already appears in one of
  the constituent theorems; the assumption surface is their union, not a
  superset.
* Rule 5 — fully parametric in `p` and in every scalar; no witness appears.
* Rule 15 — invariance is *derived* here, not postulated, which is what makes the
  gain-ball fixed point a constructed object rather than an assumed one.
-/

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Target side -/

/-- **The joint Target operator keeps the gain ball.**

Discharges the Target-side hypothesis of
`ofLipGainBall_IsInvariant_of_preservation` from carrier-level primitives.
Reading the inputs in English:

* `hU_T_cube` — the Target stage payoff is bounded on the feasible cube;
* `h_norm_margin` — that bound plus the discounted radius stays inside the radius,
  so the operator cannot grow the value beyond `M`;
* `h_integrand_lipschitz_at_carrier` — at every carrier pair, the Target's joint
  integrand is `K`-Lipschitz in the state, uniformly in the action;
* `h_integrand_lowerSlope_at_carrier` — at every carrier pair, moving to a deeper
  state on the basin raises that same integrand by at least `g` per unit.

The first two plus the third give the Lipschitz-ball half; the fourth gives the
slope floor.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem h_T_preserves_gain_of_integrand
    {M K g xT cube_T : ℝ}
    (_hM_nn : 0 ≤ M) (_hK_nn : 0 ≤ K) (_hg_nn : 0 ≤ g)
    (_hcube_T_nn : 0 ≤ cube_T)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT, p.DynamicArgmaxUnique V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (h_norm_margin : cube_T + p.β_T * M ≤ M)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ K * dist x₁ x₂)
    (h_integrand_lowerSlope_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        y₁.val ∈ Set.Icc xT 1 → y₂.val ∈ Set.Icc xT 1 → y₁ ≤ y₂ →
        g * dist y₁ y₂ ≤
          p.joint_T_integrand V_T V_S y₂.val a
          - p.joint_T_integrand V_T V_S y₁.val a) :
    ∀ V_T V_S : Val,
      (hV_T : V_T ∈ valLipGainBall M K g xT) →
      (hV_S : V_S ∈ valLipGainBall M K g xT) →
      p.jointTarget_BCF_on_S V_T V_S (h_unique_S V_S hV_S).toOnI
        ∈ valLipGainBall M K g xT := by
  intro V_T V_S hV_T hV_S
  refine mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope.mpr ⟨?_, ?_⟩
  · exact p.jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz V_T V_S
      (h_unique_S V_S hV_S) hV_T.1 hU_T_cube h_norm_margin
      (h_integrand_lipschitz_at_carrier V_T hV_T V_S hV_S)
  · exact p.jointTarget_BCF_lowerSlope_of_integrand_lowerSlope V_T V_S
      (h_unique_S V_S hV_S) (h_integrand_lowerSlope_at_carrier V_T hV_T V_S hV_S)

/-! ## Sender side -/

/-- **The joint Sender operator keeps the gain ball.**

Discharges the Sender-side hypothesis of
`ofLipGainBall_IsInvariant_of_preservation`.  Reading the inputs in English:

* `hB_sub` is implicit in `hxT_nn` — the basin `[xT, 1]` sits inside the state
  space;
* `hB_inv` — from a basin state, every feasible sanction lands back in the basin.
  This is what lets the slope floor be carried on `[xT, 1]` rather than on all of
  `[0,1]`: the Bellman step only ever evaluates the incoming value at successor
  states, and `hB_inv` says those are covered;
* `hU_S_cube`, `h_norm_margin` — the Sender stage payoff is bounded and the
  radius is not inflated;
* `h_U_S_lip_at_α`, `h_F_lip`, `h_lip_margin` — the Sender payoff composed with
  the carrier-local leader selector is `L_U_S`-Lipschitz in the state, the
  transition is `γ_F`-Lipschitz, and together they do not inflate `K`;
* `h_joint_state_chord_at_carrier` — the substantive one: at every feasible
  sanction, a rise in the inherited state raises the Sender's stage payoff *plus*
  the discounted value of the induced rise in next period's state by at least `g`
  per unit.  Both channels counted together, which is strictly weaker than asking
  each to clear a bar of its own. -/
theorem h_S_preserves_gain_of_payoff
    {M K g xT cube_S L_U_S γ_F : ℝ}
    (_hM_nn : 0 ≤ M) (hK_nn : 0 ≤ K)
    (_hcube_S_nn : 0 ≤ cube_S) (_hγ_F_nn : 0 ≤ γ_F)
    (hxT_nn : 0 ≤ xT)
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT, p.TargetArgmaxUnique V_T V_S)
    (hB_inv : ∀ x ∈ Set.Icc xT (1 : ℝ), ∀ s ∈ Sanctions.I,
        p.F x s ∈ Set.Icc xT 1)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_U_S_lip_at_α :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂
            ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₂) s
          - p.U_S x₁
            ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_joint_state_chord_at_carrier :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Set.Icc xT (1 : ℝ),
        ∀ y₂ ∈ Set.Icc xT (1 : ℝ), y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂
                ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                    h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ y₂) s
              - p.U_S y₁
                ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                    h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_norm_margin : cube_S + p.β_S * M ≤ M)
    (h_lip_margin : L_U_S + p.β_S * K * γ_F ≤ K) :
    ∀ V_T V_S : Val,
      (hV_T : V_T ∈ valLipGainBall M K g xT) →
      (hV_S : V_S ∈ valLipGainBall M K g xT) →
      (ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
          h_unique_T).jointSender_BCF_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩
        ∈ valLipGainBall M K g xT := by
  intro V_T V_S hV_T hV_S
  set D := ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S h_unique_T
    with hD
  have hB_sub : Set.Icc xT (1 : ℝ) ⊆ Sanctions.I :=
    Set.Icc_subset_Icc hxT_nn le_rfl
  refine mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope.mpr ⟨?_, ?_⟩
  · -- Sup-norm radius and Lipschitz constant: the Lipschitz-ball estimate.
    exact p.bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
      (D.α_on_continuous ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩)
      (fun x => D.α_on_mem ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x)
      V_S hK_nn (valLipGainBall_subset_valLipBall M K g xT hV_S)
      hU_S_cube (h_U_S_lip_at_α V_T hV_T V_S hV_S) h_F_lip
      h_norm_margin h_lip_margin
  · -- Slope floor: the general-`F` Sender cone, on the basin.
    exact p.bellmanS_BCF_preserves_lowerSlopeCone_generalF_on
      (D.α_on_continuous ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩) hB_sub hB_inv
      (h_joint_state_chord_at_carrier V_T hV_T V_S hV_S) hV_S.2.2

/-! ## The composition -/

/-- **`IsInvariant` for `valLipGainBall` from primitives.**

Pure composition of `h_T_preserves_gain_of_integrand` and
`h_S_preserves_gain_of_payoff` through
`ofLipGainBall_IsInvariant_of_preservation`; the hypotheses are exactly the union
of what those two take, so nothing is assumed here that was not already assumed
there.

Why this matters beyond convenience: `IsInvariant` is the existence crux
(Rule 15).  Without it there is no fixed point and hence no equilibrium, so a
carrier whose invariance is *hypothesised* leaves the entire construction resting
on an unproved premise.  With this theorem the gain-ball route joins the sup-norm
ball (`ofBall_IsInvariant_of_cube_bounds`) and the Lipschitz ball
(`ofLipBall_IsInvariant_of_primitives`) in deriving invariance from payoff and
transition data alone.

The economic reading of the carrier it validates: values that are bounded, do not
respond too sharply to the political state, **and** strictly reward deeper
entrenchment on the basin.  The last of those is the political-economy condition
that used to be carried as the per-equilibrium hypothesis `hV_T_gain_on_E`; here
it is carrier geometry, preserved by both players' optimisation. -/
theorem ofLipGainBall_IsInvariant_of_primitives
    {M K g xT cube_T cube_S L_U_S γ_F : ℝ}
    (hM_nn : 0 ≤ M) (hK_nn : 0 ≤ K) (hg_nn : 0 ≤ g)
    (hcube_T_nn : 0 ≤ cube_T) (hcube_S_nn : 0 ≤ cube_S)
    (hγ_F_nn : 0 ≤ γ_F) (hxT_nn : 0 ≤ xT)
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT, p.TargetArgmaxUnique V_T V_S)
    (hB_inv : ∀ x ∈ Set.Icc xT (1 : ℝ), ∀ s ∈ Sanctions.I,
        p.F x s ∈ Set.Icc xT 1)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ K * dist x₁ x₂)
    (h_integrand_lowerSlope_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        y₁.val ∈ Set.Icc xT 1 → y₂.val ∈ Set.Icc xT 1 → y₁ ≤ y₂ →
        g * dist y₁ y₂ ≤
          p.joint_T_integrand V_T V_S y₂.val a
          - p.joint_T_integrand V_T V_S y₁.val a)
    (h_U_S_lip_at_α :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂
            ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₂) s
          - p.U_S x₁
            ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_joint_state_chord_at_carrier :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Set.Icc xT (1 : ℝ),
        ∀ y₂ ∈ Set.Icc xT (1 : ℝ), y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂
                ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                    h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ y₂) s
              - p.U_S y₁
                ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                    h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_T_norm_margin : cube_T + p.β_T * M ≤ M)
    (h_S_norm_margin : cube_S + p.β_S * M ≤ M)
    (h_lip_margin : L_U_S + p.β_S * K * γ_F ≤ K) :
    (ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
      h_unique_T).IsInvariant :=
  p.ofLipGainBall_IsInvariant_of_preservation h_nonempty h_unique_S h_unique_T
    (p.h_T_preserves_gain_of_integrand hM_nn hK_nn hg_nn hcube_T_nn h_unique_S
      hU_T_cube h_T_norm_margin h_integrand_lipschitz_at_carrier
      h_integrand_lowerSlope_at_carrier)
    (p.h_S_preserves_gain_of_payoff hM_nn hK_nn hcube_S_nn hγ_F_nn hxT_nn
      h_nonempty h_unique_S h_unique_T hB_inv hU_S_cube h_U_S_lip_at_α
      h_joint_state_chord_at_carrier h_F_lip h_S_norm_margin h_lip_margin)

/-- **`IsInvariant` for `valLipGainBall` from chords on both stage payoffs.**

The same composition, with the Target-side integrand slope floor no longer
assumed but derived from `joint_T_integrand_lowerSlope_of_joint_chord`.  What
replaces it:

* `hsucc_mono` — at the realised sanction, a deeper state produces a weakly
  deeper successor.  This is *not* implied by `F_mono_x` alone, because the
  Sender's response `σ_dyn` also moves with the state, and could in principle
  move against it hard enough to reverse the order.
* `h_joint_chord_T` — the Target analogue of the Sender chord: moving to a deeper
  state raises the Target's realised stage payoff plus the discounted successor
  state by at least `g` per unit, evaluated at the sanctions actually chosen.

With this, both slope obligations are chord conditions on the two stage payoffs,
which is as close to primitives as the route gets: no condition is imposed on the
value functions beyond carrier membership, and none on `F` beyond monotonicity,
a Lipschitz bound, and keeping the basin. -/
theorem ofLipGainBall_IsInvariant_of_chords
    {M K g xT cube_T cube_S L_U_S γ_F : ℝ}
    (hM_nn : 0 ≤ M) (hK_nn : 0 ≤ K) (hg_nn : 0 ≤ g)
    (hcube_T_nn : 0 ≤ cube_T) (hcube_S_nn : 0 ≤ cube_S)
    (hγ_F_nn : 0 ≤ γ_F) (hxT_nn : 0 ≤ xT)
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT, p.TargetArgmaxUnique V_T V_S)
    (hB_inv : ∀ x ∈ Set.Icc xT (1 : ℝ), ∀ s ∈ Sanctions.I,
        p.F x s ∈ Set.Icc xT 1)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ K * dist x₁ x₂)
    (hsucc_mono :
      ∀ (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ a ∈ Sanctions.I, ∀ x₁ ∈ Set.Icc xT (1 : ℝ),
        ∀ x₂ ∈ Set.Icc xT (1 : ℝ), x₁ ≤ x₂ →
          p.F x₁ (p.σ_dyn V_S x₁ a) ≤ p.F x₂ (p.σ_dyn V_S x₂ a))
    (h_joint_chord_T :
      ∀ (V_S : Val) (_hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ a ∈ Sanctions.I, ∀ x₁ ∈ Set.Icc xT (1 : ℝ),
        ∀ x₂ ∈ Set.Icc xT (1 : ℝ), x₁ ≤ x₂ →
          g * (x₂ - x₁)
            ≤ (p.U_T x₂ a (p.σ_dyn V_S x₂ a) - p.U_T x₁ a (p.σ_dyn V_S x₁ a))
              + p.β_T * g
                  * (p.F x₂ (p.σ_dyn V_S x₂ a) - p.F x₁ (p.σ_dyn V_S x₁ a)))
    (h_U_S_lip_at_α :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂
            ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₂) s
          - p.U_S x₁
            ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_joint_state_chord_at_carrier :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipGainBall M K g xT)
        (V_S : Val) (hV_S : V_S ∈ valLipGainBall M K g xT),
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Set.Icc xT (1 : ℝ),
        ∀ y₂ ∈ Set.Icc xT (1 : ℝ), y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂
                ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                    h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ y₂) s
              - p.U_S y₁
                ((ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
                    h_unique_T).α_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_T_norm_margin : cube_T + p.β_T * M ≤ M)
    (h_S_norm_margin : cube_S + p.β_S * M ≤ M)
    (h_lip_margin : L_U_S + p.β_S * K * γ_F ≤ K) :
    (ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
      h_unique_T).IsInvariant :=
  p.ofLipGainBall_IsInvariant_of_primitives hM_nn hK_nn hg_nn hcube_T_nn
    hcube_S_nn hγ_F_nn hxT_nn h_nonempty h_unique_S h_unique_T hB_inv
    hU_T_cube hU_S_cube h_integrand_lipschitz_at_carrier
    (fun _V_T hV_T V_S hV_S =>
      p.joint_T_integrand_lowerSlope_of_joint_chord hxT_nn hV_T.2.2 hB_inv
        (hsucc_mono V_S hV_S) (h_joint_chord_T V_S hV_S))
    h_U_S_lip_at_α h_joint_state_chord_at_carrier h_F_lip
    h_T_norm_margin h_S_norm_margin h_lip_margin

/-! ## Axiom hygiene (Rule 10) -/

#print axioms h_T_preserves_gain_of_integrand
#print axioms h_S_preserves_gain_of_payoff
#print axioms ofLipGainBall_IsInvariant_of_primitives
#print axioms ofLipGainBall_IsInvariant_of_chords

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
