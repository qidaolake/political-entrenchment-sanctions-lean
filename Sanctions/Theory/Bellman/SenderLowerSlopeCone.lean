/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Bellman.BellmanS
import Sanctions.Theory.Bellman.InvariantLipGainBall

/-!
# The Sender-side lower-slope cone

This file is the **Sender analogue** of the Target-side envelope result
`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope`
(`Theory/Bellman/InvariantLipGainBall.lean`), and the lower-slope analogue of
`bellmanS_BCF_preserves_monotone` / `V_S_monotone_of_integrand_monotone`
(`Theory/Bellman/BellmanS.lean`).  Where those preserve *monotonicity* (a
qualitative order property) this file preserves a **quantitative minimum
upward state-slope**: the property `LowerSlopeOnValueOn V (Icc 0 1) g`, i.e.
`V y₂ − V y₁ ≥ g · dist y₁ y₂` for `y₁ ≤ y₂`.

## What is proved

* `bellmanS_BCF_preserves_lowerSlopeCone` — if the Sender's **stage** payoff
  along the Target policy `α` rises in the political state at rate at least `m`
  (uniformly in the sanction), the transition is the affine law
  `F(x,s) = (1−δ)x + δs`, and the cone constant `g` satisfies the sub-solution
  inequality `g ≤ m + β_S·g·(1−δ)`, then the Sender Bellman operator
  `bellmanS_BCF` carries the cone `{V | V rises at rate at least g}` into
  itself.
* `V_S_mem_lowerSlopeCone` — hence the **constructed** Sender value
  (`V_S α hα`, the Banach fixed point of `bellmanS_BCF`, defined in
  `BellmanS.lean`) lies in the cone at the Benveniste–Scheinkman closed-form
  constant `bellmanLowerSlopeConstant β_S (1−δ) m = m / (1 − β_S(1−δ))`.
  Rule 15 is respected: nothing about existence is hypothesised; membership is
  *derived* by trapping the Banach iteration in a closed forward-invariant set
  (`Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo`,
  `Foundations/StokeyLucas.lean`) seeded by the linear function
  `linSeed g : y ↦ g·y`.
* `zero_not_mem_lowerSlopeCone`, `V_S_ne_zero_of_pos_state_slope` — a
  *strictly* positive cone constant excludes the zero value function, so an
  economy with a strictly positive primitive state chord cannot have
  `V_S = 0`.

  **Do not read this as removing the zero-continuation witness from the barrier
  `uniform_floor_iff_stage_floor` (`Theory/LockIn/PersistenceMargin.lean`).**  An
  earlier draft said so and it is false: that barrier quantifies over the
  *monotone* carrier, the zero function is monotone, and it remains in that
  carrier at every economy — including the witnesses here.  What the cone changes
  is the quantification: a floor demanded over the **cone** is not a floor
  demanded over the monotone carrier, and only the latter collapses to the stage
  argmax.  The barrier stands exactly as proved; the cone route goes around it
  rather than through it.

## Why here (Rule 19)

Every statement mentions `AbstractGame.Params` — the Sender stage payoff
`U_S`, the discount factor `β_S`, the transition `F` — so this is model
wiring and belongs in `Theory/`, not `Foundations/`.  The general
mathematics it consumes (a closed forward-invariant set traps the Banach
fixed point; the sup-difference lower bound) already lives in
`Foundations/StokeyLucas.lean` and is *used*, not restated.

It is a sibling file rather than an addition to `BellmanS.lean` or
`InvariantLipGainBall.lean` because it needs both: `LowerSlopeOnValueOn` and
its closedness come from the `InvariantLipGainBall` /
`TargetSanctionLossOffset` chain, while `bellmanS_BCF` and `V_S` come from
`BellmanS.lean`, and neither of those two files imports the other.  Putting
the content in either one would force a new import into a widely-depended-on
module for no mathematical gain.

## Rule compliance

* **Rule 1** — no strategy is fixed here.  `α` is an arbitrary continuous
  Target policy and the hypothesis is a chord condition on the *composed*
  stage payoff `y ↦ U_S(y, α y, s)`.  The consumers in
  `Theory/LockIn/PersistenceMargin.lean` instantiate it at an equilibrium
  policy.
* **Rule 3** — no new assumption surface.  `m` and `g` are theorem-bound
  scalars bounding the existing `U_S`; no `Params` field, no `Prop`
  definition, and no structure is added.
* **Rule 5** — fully parametric over `(p, α, m, g)`; the concrete economies
  live in `Examples/SenderConeWitness.lean`.
* **Rule 15** — `V_S` is constructed (Banach fixed point in `BellmanS.lean`),
  never consumed as a hypothesised value function.
-/

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Subtype-distance helpers -/

/-- Ordered subtype distance on the state space: for `y₁ ≤ y₂` in `↥S` the
metric distance is the plain difference of the underlying reals. -/
theorem dist_eq_sub_of_le {y₁ y₂ : ↥(Sanctions.S : Set ℝ)} (h : y₁ ≤ y₂) :
    dist y₁ y₂ = y₂.val - y₁.val := by
  have hval : (y₁ : ℝ) ≤ (y₂ : ℝ) := h
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hval)]

/-- `clipS'` moves distances exactly on `[0,1]`: for `z₁, z₂` in the physical
state interval, the subtype distance between the clipped points is `|z₁ − z₂|`.

A two-line consequence of `Sanctions.clipS'_val_eq_of_mem` (clipping is the
identity in value on `[0,1]`).

*Relocated (2026-07-31) from `Theory/LockIn/PersistenceMargin.lean`*, with the
statement, the proof and the fully-qualified name unchanged, so that both the
cone-preservation argument below and the two margin conversions there can
consume the same lemma instead of duplicating it. -/
theorem clipS'_dist_eq_of_mem {z₁ z₂ : ℝ}
    (h1 : z₁ ∈ Set.Icc (0:ℝ) 1) (h2 : z₂ ∈ Set.Icc (0:ℝ) 1) :
    dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = |z₁ - z₂| := by
  rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem h1,
    Sanctions.clipS'_val_eq_of_mem h2]

/-! ## The cone, its seed, and its closedness -/

/-- The linear seed `V₀(y) = g · y` of the lower-slope cone.  It is the
nonempty witness that starts the Banach iteration inside the cone. -/
def linSeed (g : ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => g * y.val, continuous_const.mul continuous_subtype_val⟩

@[simp] theorem linSeed_apply (g : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    linSeed g y = g * y.val := rfl

/-- The linear seed sits in the lower-slope cone with its own slope. -/
theorem linSeed_mem_lowerSlopeCone (g : ℝ) :
    LowerSlopeOnValueOn (linSeed g) (Set.Icc (0:ℝ) 1) g := by
  intro y₁ y₂ _ _ hle
  rw [dist_eq_sub_of_le hle, linSeed_apply, linSeed_apply]
  exact le_of_eq (by ring)

/-- **The linear seed lies in any gain ball wide enough to hold it.**

`ValueClass.ofLipGainBall` takes the carrier's nonemptiness as an explicit
hypothesis, and its docstring has always named this witness in prose — the linear
value `V(y) = g · y` meets all three constraints when `M ≥ g`, `K ≥ g`, `g ≥ 0` —
but the claim was never proved, so the only discharge in the tree was at a single
witness economy.  Here it is, parametric.

Economically the seed is the political economy's simplest possible value: worth
exactly `g` per unit of entrenchment, everywhere, with no curvature.  A gain ball
is asking for values bounded by `M`, no steeper than `K`, and no flatter than
`g`; the linear one is the extreme case of the last constraint, so it fits
whenever the first two leave room for it. -/
theorem linSeed_mem_valLipGainBall {M K g xT : ℝ}
    (hg_nn : 0 ≤ g) (hgM : g ≤ M) (hgK : g ≤ K) (hxT_nn : 0 ≤ xT) :
    linSeed g ∈ valLipGainBall M K g xT := by
  refine ⟨?_, ?_, ?_⟩
  · refine (BoundedContinuousFunction.norm_le (le_trans hg_nn hgM)).2 ?_
    intro y
    rw [linSeed_apply, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hg_nn y.property.1)]
    nlinarith [y.property.1, y.property.2]
  · intro y₁ y₂
    have hd : dist y₁ y₂ = |y₂.val - y₁.val| := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [hd, linSeed_apply, linSeed_apply, ← mul_sub, abs_mul,
      abs_of_nonneg hg_nn]
    exact mul_le_mul_of_nonneg_right hgK (abs_nonneg _)
  · exact LowerSlopeOnValueOn.mono_set (linSeed_mem_lowerSlopeCone g)
      (Set.Icc_subset_Icc hxT_nn le_rfl)

/-- **Gain-ball nonemptiness, parametric.** Discharges the `h_nonempty` input of
`ValueClass.ofLipGainBall` and of every constructor built on it, from three
inequalities among scalars already in play. -/
theorem valLipGainBall_nonempty {M K g xT : ℝ}
    (hg_nn : 0 ≤ g) (hgM : g ≤ M) (hgK : g ≤ K) (hxT_nn : 0 ≤ xT) :
    (valLipGainBall M K g xT).Nonempty :=
  ⟨linSeed g, linSeed_mem_valLipGainBall hg_nn hgM hgK hxT_nn⟩

/-- **The lower-slope cone on the whole state space is closed.**  A
specialisation of `lowerSlopeOnValueOn_isClosed` to the full range `[0,1]`. -/
theorem lowerSlopeCone_isClosed (g : ℝ) :
    IsClosed {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ |
      LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) g} :=
  Sanctions.AbstractGame.Params.lowerSlopeOnValueOn_isClosed (Set.Icc (0:ℝ) 1) g

/-- The Benveniste–Scheinkman cone-margin identity at the closed-form constant
`g = m / (1 − β_S(1−δ))`: it solves `m + β_S·g·(1−δ) = g` exactly.  No sign
restriction on the stage slope `m` is needed. -/
theorem lowerSlopeConstant_cone_identity (m : ℝ) :
    m + p.β_S * (Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S (1 - p.δ) m)
        * (1 - p.δ)
      = Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S (1 - p.δ) m := by
  have hpos := p.oneMinus_betaS_oneMinusDelta_pos
  rw [Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
  field_simp
  ring

/-! ## Cone preservation for the Sender Bellman operator -/


/-- **General-`F` Sender cone preservation.** If, at every feasible sanction, a
rise in the inherited state raises the Sender's stage payoff plus the discounted
value of the induced rise in next period's state by at least `g` per unit, then
`bellmanS_BCF` carries the lower-slope cone into itself.

No hypothesis constrains `F` on its own: the transition appears only inside the
joint chord and through `F_mono_x`, which `Params` already carries. Compare
`bellmanS_BCF_preserves_lowerSlopeCone`, which assumes the affine law.

Anchor: Smith–McCardle (2002) §6 via the `W = V − g·id` reduction of a slope
floor to monotonicity; see the section note above. -/
theorem bellmanS_BCF_preserves_lowerSlopeCone_generalF
    {α : ℝ → ℝ} (hα : Continuous α)
    {g : ℝ}
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) g) :
    LowerSlopeOnValueOn (p.bellmanS_BCF α hα V) (Set.Icc (0:ℝ) 1) g := by
  intro y₁ y₂ _ _ hle
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hd : dist y₁ y₂ = y₂.val - y₁.val := dist_eq_sub_of_le hle
  have hdiff_nn : (0:ℝ) ≤ y₂.val - y₁.val := by rw [← hd]; exact dist_nonneg
  have h_point : ∀ s ∈ Sanctions.I,
      g * dist y₁ y₂ ≤ p.integrandS α (fun z => V z) (y₂.val, s)
                        - p.integrandS α (fun z => V z) (y₁.val, s) := by
    intro s hs
    have hy₁ : y₁.val ∈ Sanctions.I := y₁.property
    have hy₂ : y₂.val ∈ Sanctions.I := y₂.property
    have hU := h_joint_state_chord s hs y₁.val y₁.property y₂.val y₂.property hle
    have hF₁ : p.F y₁.val s ∈ Set.Icc (0:ℝ) 1 := p.F_mem _ _ hy₁ hs
    have hF₂ : p.F y₂.val s ∈ Set.Icc (0:ℝ) 1 := p.F_mem _ _ hy₂ hs
    -- The only place the transition is used: it is monotone in the state.
    have hFle : p.F y₁.val s ≤ p.F y₂.val s := p.F_mono_x s hle
    have hord : Sanctions.clipS' (p.F y₁.val s) ≤ Sanctions.clipS' (p.F y₂.val s) :=
      Sanctions.clipS'_mono hFle
    have hVslope := hV (Sanctions.clipS' (p.F y₁.val s))
      (Sanctions.clipS' (p.F y₂.val s))
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) hord
    -- The affine displacement identity is replaced by the actual increment.
    have hdF : dist (Sanctions.clipS' (p.F y₁.val s))
        (Sanctions.clipS' (p.F y₂.val s)) = p.F y₂.val s - p.F y₁.val s := by
      rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hF₁ hF₂, abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [hdF] at hVslope
    have hVscaled : p.β_S * (g * (p.F y₂.val s - p.F y₁.val s))
        ≤ p.β_S * (V (Sanctions.clipS' (p.F y₂.val s))
            - V (Sanctions.clipS' (p.F y₁.val s))) :=
      mul_le_mul_of_nonneg_left hVslope hβ
    show g * dist y₁ y₂
      ≤ (p.U_S y₂.val (α y₂.val) s + p.β_S * V (Sanctions.clipS' (p.F y₂.val s)))
        - (p.U_S y₁.val (α y₁.val) s + p.β_S * V (Sanctions.clipS' (p.F y₁.val s)))
    rw [hd]
    nlinarith [hU, hVscaled]
  have hbdd := p.integrandS_image_bddAbove hα V.continuous y₂.val
  have hIne : (Sanctions.I : Set ℝ).Nonempty := ⟨0, by simp [Sanctions.I]⟩
  show g * dist y₁ y₂
      ≤ sSup ((fun s => p.integrandS α (fun z => V z) (y₂.val, s)) '' Sanctions.I)
        - sSup ((fun s => p.integrandS α (fun z => V z) (y₁.val, s)) '' Sanctions.I)
  exact Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise
    hIne h_point hbdd

/-- **General-`F` Sender cone preservation on a basin.** Domain-parametric form
of the theorem above: the cone is preserved on any set `B` the transition keeps.

The gain ball asks for the slope on `[xT, 1]`, not on all of `[0,1]`, and the
restriction runs the wrong way — a guarantee on `[0,1]` weakens to `[xT,1]`, but
the Bellman step needs the *hypothesis* on the same set it concludes on. What
makes the smaller domain work is `hB_inv`: from a basin state, any feasible
sanction lands back in the basin, so the cone is applied only at points it
covers. On `B = [0,1]` that is automatic from `F_mem`, which is why the unit
interval needed no such condition.

`hB_inv` is the same basin-preservation condition that
`joint_T_integrand_lowerSlope_of_joint_chord` takes on the Target side. -/
theorem bellmanS_BCF_preserves_lowerSlopeCone_generalF_on
    {α : ℝ → ℝ} (hα : Continuous α)
    {g : ℝ} {B : Set ℝ}
    (hB_sub : B ⊆ Sanctions.I)
    (hB_inv : ∀ x ∈ B, ∀ s ∈ Sanctions.I, p.F x s ∈ B)
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ B, ∀ y₂ ∈ B, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn V B g) :
    LowerSlopeOnValueOn (p.bellmanS_BCF α hα V) B g := by
  intro y₁ y₂ hy₁B hy₂B hle
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hd : dist y₁ y₂ = y₂.val - y₁.val := dist_eq_sub_of_le hle
  have hdiff_nn : (0:ℝ) ≤ y₂.val - y₁.val := by rw [← hd]; exact dist_nonneg
  have h_point : ∀ s ∈ Sanctions.I,
      g * dist y₁ y₂ ≤ p.integrandS α (fun z => V z) (y₂.val, s)
                        - p.integrandS α (fun z => V z) (y₁.val, s) := by
    intro s hs
    have hy₁ : y₁.val ∈ Sanctions.I := hB_sub hy₁B
    have hy₂ : y₂.val ∈ Sanctions.I := hB_sub hy₂B
    have hU := h_joint_state_chord s hs y₁.val hy₁B y₂.val hy₂B hle
    have hF₁B : p.F y₁.val s ∈ B := hB_inv y₁.val hy₁B s hs
    have hF₂B : p.F y₂.val s ∈ B := hB_inv y₂.val hy₂B s hs
    have hF₁ : p.F y₁.val s ∈ Set.Icc (0:ℝ) 1 := hB_sub hF₁B
    have hF₂ : p.F y₂.val s ∈ Set.Icc (0:ℝ) 1 := hB_sub hF₂B
    have hFle : p.F y₁.val s ≤ p.F y₂.val s := p.F_mono_x s hle
    have hord : Sanctions.clipS' (p.F y₁.val s) ≤ Sanctions.clipS' (p.F y₂.val s) :=
      Sanctions.clipS'_mono hFle
    have hVslope := hV (Sanctions.clipS' (p.F y₁.val s))
      (Sanctions.clipS' (p.F y₂.val s))
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁B)
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂B) hord
    have hdF : dist (Sanctions.clipS' (p.F y₁.val s))
        (Sanctions.clipS' (p.F y₂.val s)) = p.F y₂.val s - p.F y₁.val s := by
      rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hF₁ hF₂, abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [hdF] at hVslope
    have hVscaled : p.β_S * (g * (p.F y₂.val s - p.F y₁.val s))
        ≤ p.β_S * (V (Sanctions.clipS' (p.F y₂.val s))
            - V (Sanctions.clipS' (p.F y₁.val s))) :=
      mul_le_mul_of_nonneg_left hVslope hβ
    show g * dist y₁ y₂
      ≤ (p.U_S y₂.val (α y₂.val) s + p.β_S * V (Sanctions.clipS' (p.F y₂.val s)))
        - (p.U_S y₁.val (α y₁.val) s + p.β_S * V (Sanctions.clipS' (p.F y₁.val s)))
    rw [hd]
    nlinarith [hU, hVscaled]
  have hbdd := p.integrandS_image_bddAbove hα V.continuous y₂.val
  have hIne : (Sanctions.I : Set ℝ).Nonempty := ⟨0, by simp [Sanctions.I]⟩
  show g * dist y₁ y₂
      ≤ sSup ((fun s => p.integrandS α (fun z => V z) (y₂.val, s)) '' Sanctions.I)
        - sSup ((fun s => p.integrandS α (fun z => V z) (y₁.val, s)) '' Sanctions.I)
  exact Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise
    hIne h_point hbdd

/-- **What the joint state chord costs: a flat Sender stage payoff forces
`g = 0`.**

A Rule-11 diagnostic, and the reason the gain-ball carrier must be allowed to
differ between the two players.  If the Sender's stage payoff does not move with
the inherited political state once the leader's response is substituted, then the
joint state chord cannot carry any strictly positive slope floor --- whatever the
transition does.

The argument needs nothing about `F` beyond feasibility.  Evaluate the chord at
the two endpoints of the state space: the stage term vanishes by hypothesis, and
the discounted transition term is at most `β_S · g`, because `F` lands in `[0,1]`
so its endpoint displacement is at most one.  That leaves `g ≤ β_S · g`, and
`β_S < 1` closes it.

The economics: a slope floor says the Sender's *value* rises at rate at least `g`
as entrenchment deepens.  If deeper entrenchment pays the Sender nothing this
period, the only source of that rise is the continuation, which is discounted --
so the value can only rise strictly if the stage payoff does some of the work.
Discounting alone cannot bootstrap a positive floor out of nothing. -/
theorem chord_forces_zero_slope_of_flat_stage
    {α : ℝ → ℝ} {g : ℝ} (hg_nn : 0 ≤ g)
    (hU_flat : ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, ∀ s ∈ Sanctions.I,
      p.U_S y₂ (α y₂) s = p.U_S y₁ (α y₁) s)
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s)) :
    g = 0 := by
  have hβ0 : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hβ1 : p.β_S < 1 := p.β_S_mem.2
  have h0 : (0 : ℝ) ∈ Sanctions.S := by constructor <;> norm_num
  have h1 : (1 : ℝ) ∈ Sanctions.S := by constructor <;> norm_num
  -- The chord at the two endpoints of the state space, at zero sanction.
  have hc := h_joint_state_chord 0 h0 0 h0 1 h1 (by norm_num)
  rw [hU_flat 0 h0 1 h1 0 h0] at hc
  -- Feasibility of the transition bounds the endpoint displacement by one.
  have hF0 : p.F 0 0 ∈ Set.Icc (0 : ℝ) 1 := p.F_mem 0 0 h0 h0
  have hF1 : p.F 1 0 ∈ Set.Icc (0 : ℝ) 1 := p.F_mem 1 0 h1 h0
  have hdisp : p.F 1 0 - p.F 0 0 ≤ 1 := by linarith [hF0.1, hF1.2]
  have hstep : p.β_S * g * (p.F 1 0 - p.F 0 0) ≤ p.β_S * g :=
    le_of_le_of_eq
      (mul_le_mul_of_nonneg_left hdisp (mul_nonneg hβ0 hg_nn)) (mul_one _)
  -- g ≤ β_S · g with β_S < 1 and g ≥ 0.
  nlinarith [hc, hstep]

/-- **The obstruction is far sharper than flatness: ONE bad sanction suffices.**

`chord_forces_zero_slope_of_flat_stage` asks the composed Sender stage payoff to
be flat at every state pair and every sanction.  In fact a single sanction `s₀`
at which the composed payoff fails to rise between the two ENDPOINTS of the
state space already forces `g = 0`.  Same feasibility-only argument, same
generality in `F` (Rule 22): the transition's endpoint displacement is at most
one because `F` lands in `[0,1]`, leaving `g ≤ β_S · g` with `β_S < 1`.

Why this is the version that bites.  The cone hypothesis is quantified
`∀ s ∈ Sanctions.I`, so what it demands is the INFIMUM over sanctions of the
composed state chord, not its value at the equilibrium sanction.  Every
sender-side gain channel this project microfounds — the rally
`∂²U_S/∂s∂x = ν·g_J` and placation `∂²U_S/∂s∂a = −w_pl`
(`Theory/Microfoundations/FourGroupPolity.lean`) — is proportional to `s`, hence
worth exactly nothing at `s = 0`.  So `s₀ = 0` is the canonical instance and the
floor stands or falls on what the Sender earns when it is NOT sanctioning. -/
theorem chord_forces_zero_slope_of_one_nonpos_sanction
    {α : ℝ → ℝ} {g s₀ : ℝ} (hg_nn : 0 ≤ g) (hs₀ : s₀ ∈ Sanctions.I)
    (hU_nonpos : p.U_S 1 (α 1) s₀ - p.U_S 0 (α 0) s₀ ≤ 0)
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s)) :
    g = 0 := by
  have hβ0 : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hβ1 : p.β_S < 1 := p.β_S_mem.2
  have h0 : (0 : ℝ) ∈ Sanctions.S := by constructor <;> norm_num
  have h1 : (1 : ℝ) ∈ Sanctions.S := by constructor <;> norm_num
  have hc := h_joint_state_chord s₀ hs₀ 0 h0 1 h1 (by norm_num)
  have hF0 : p.F 0 s₀ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem 0 s₀ h0 hs₀
  have hF1 : p.F 1 s₀ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem 1 s₀ h1 hs₀
  have hdisp : p.F 1 s₀ - p.F 0 s₀ ≤ 1 := by linarith [hF0.1, hF1.2]
  have hstep : p.β_S * g * (p.F 1 s₀ - p.F 0 s₀) ≤ p.β_S * g :=
    le_of_le_of_eq
      (mul_le_mul_of_nonneg_left hdisp (mul_nonneg hβ0 hg_nn)) (mul_one _)
  nlinarith [hc, hstep, hU_nonpos]

/-! ## The constructed Sender value lies in the cone (Rule 15) -/


/-- **General-`F` version: the Sender Bellman fixed point inherits the joint
state chord.**  Same trapping argument as `V_S_mem_lowerSlopeCone` -- the cone is
closed, the linear seed `y ↦ g·y` is in it, and the operator preserves it, so
`Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo` places the Banach fixed point
inside it -- but with the affine law, the separated stage chord `m` and the
sub-solution inequality `g ≤ m + β_S·g·(1−δ)` all replaced by the single joint
chord of `bellmanS_BCF_preserves_lowerSlopeCone_generalF`.

What is lost relative to the affine version: the Benveniste–Scheinkman closed form
`bellmanLowerSlopeConstant β_S (1−δ) m = m/(1 − β_S(1−δ))`.  Here `g` is a
theorem-bound parameter constrained only by the joint chord, so no closed form is
available and none is claimed.  What is gained: no condition on `F` beyond
`F_mono_x`, which `Params` already carries.

Rule 15 is respected exactly as in the affine version: existence is *constructed*
(`p.V_S α hα` is by definition the Banach fixed point of `bellmanS_BCF`), never
hypothesised. -/
theorem V_S_mem_lowerSlopeCone_generalF
    {α : ℝ → ℝ} (hα : Continuous α)
    {g : ℝ}
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s)) :
    LowerSlopeOnValueOn (p.V_S α hα) (Set.Icc (0:ℝ) 1) g := by
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) := by
    refine ⟨p.β_S_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := p.bellmanS_BCF_pointwise_dist hα V W x
    convert h using 2
  have h_eq : p.V_S α hα = hcontr.fixedPoint := by
    unfold V_S; congr
  obtain ⟨W, hW_fix, hW_mem⟩ :=
    Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo p.β_S_nnreal_lt_one
      (p.bellmanS_BCF α hα) hcontr.2
      {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ | LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) g}
      (lowerSlopeCone_isClosed g) ⟨linSeed g, linSeed_mem_lowerSlopeCone g⟩
      (fun _ hW => p.bellmanS_BCF_preserves_lowerSlopeCone_generalF hα
        h_joint_state_chord hW)
  rw [h_eq, ← hcontr.fixedPoint_unique hW_fix]
  exact hW_mem

/-! ## A strictly positive cone excludes the zero continuation value -/

/-- **A strictly positive lower-slope cone excludes the zero value function.**
The chord condition evaluated between the endpoints `0` and `1` would read
`g ≤ 0`. -/
theorem zero_not_mem_lowerSlopeCone {g : ℝ} (hg : 0 < g) :
    ¬ LowerSlopeOnValueOn (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (Set.Icc (0:ℝ) 1) g := by
  intro h
  have h0 : (0:ℝ) ∈ (Sanctions.S : Set ℝ) := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ (Sanctions.S : Set ℝ) := ⟨zero_le_one, le_refl 1⟩
  have hle : (⟨0, h0⟩ : ↥(Sanctions.S : Set ℝ)) ≤ ⟨1, h1⟩ := by
    show (0:ℝ) ≤ 1
    norm_num
  have hkey := h ⟨0, h0⟩ ⟨1, h1⟩ ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ hle
  rw [dist_eq_sub_of_le hle] at hkey
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, sub_zero] at hkey
  norm_num at hkey
  linarith


#print axioms dist_eq_sub_of_le
#print axioms clipS'_dist_eq_of_mem
#print axioms linSeed_mem_lowerSlopeCone
#print axioms linSeed_mem_valLipGainBall
#print axioms valLipGainBall_nonempty
#print axioms chord_forces_zero_slope_of_flat_stage
#print axioms lowerSlopeCone_isClosed
#print axioms lowerSlopeConstant_cone_identity
#print axioms bellmanS_BCF_preserves_lowerSlopeCone_generalF
#print axioms bellmanS_BCF_preserves_lowerSlopeCone_generalF_on
#print axioms V_S_mem_lowerSlopeCone_generalF
#print axioms zero_not_mem_lowerSlopeCone

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
