/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.PersistenceMargin
import Sanctions.Theory.LockIn.ReliefExit

/-!
# Sign conditions do not imply perpetual sanctions (Rule-11 refutation)

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**This is a parametric refutation family, not a single counterexample.** The
probe economy is quantified over four free reals -- the adjustment rate, both
discount factors, and the rally slope -- so results such as
`probe_SenderStageIDStrict` hold for *every* strictly positive rally slope,
however small, and not merely at one calibration. A family of counterexamples is
strictly stronger evidence than one counterexample, and reading these as point
checks understates what the file settles.

It sits under `Examples/` because it fixes functional forms for the stage
payoffs (`probeU_S`, `probeU_T`), which Rule 19 keeps out of `Theory/`. That is
a statement about where the file belongs, not about the strength of its
conclusions.

The claim under test: *every* economy of the model class whose primitives
satisfy the project's sign conditions admits an equilibrium along which
sanctions are perpetual — above a positive floor and non-decreasing on a
non-degenerate high basin.

That claim is **false**, and this file proves it.

## Why the sign conditions cannot carry the claim

`SenderStageID` / `TargetStageID` (`Theory/Basin/StageFlip.lean`) and their
strict forms are *chord* (increasing-difference) conditions: they order the
cross-difference of a stage payoff in `(s, x)`.  They constrain how the Sender's
and the Target's marginal valuation of a sanction *moves with the political
state*.  They say nothing whatever about

* the **level** of the Sender's marginal payoff from sanctioning — the rally
  gain may be positive at every state and still be dominated at every state by
  the Sender's own cost of sanctioning; or
* the size of the **continuation** effect relative to that stage cost.

So the sign conditions are compatible with an economy whose Sender optimally
never sanctions.  The probe economy below is exactly that.

## The probe economy

For any adjustment rate `δ ∈ (0,1)`, any pair of discount factors in `[0,1)`,
and any rally slope `ε > 0`,

* `U_S(x, a, s) = (ε·x − 1)·s − s²/2` — the Sender's marginal value of
  sanctioning rises with the political state at rate `ε > 0` (strict
  complementarity, `probe_SenderStageIDStrict`) but starts from a unit marginal
  cost;
* `U_T(x, a, s) = s·x − (a − 1/2)²` — rally around the flag (strict
  complementarity, `probe_TargetStageIDStrict`) plus a strictly concave
  compliance term, so the Target's optimal action is a unique interior point;
* `F(x, s) = (1 − δ)·x + δ·s` — the canonical partial-adjustment transition,
  which satisfies strict directional adjustment. The transition is inessential:
  see "Any transition" below.

Every sign condition in the project holds at this economy, for every `ε > 0`:
`SenderStageIDStrict`, `TargetStageIDStrict`, their weak chord forms, the
compliance-placates condition `SenderActionDD`, and `StrictAdjustment`.

## The refutation

When the rally slope does not exceed the Sender's own marginal sanction cost
(`ε ≤ 1`):

* `probe_V_S_eq_zero` — **every** equilibrium of the economy has the zero
  Sender continuation value (the Bellman operator is a `β_S`-contraction whose
  fixed point is `0`);
* `probe_σ_dyn_top_eq_zero` — the Sender's forward-looking argmax is therefore
  the *unique* maximiser `s = 0`, at every feasible state and every action;
* `probe_sanctionsF_eq_zero` — so along the closed loop of **any** equilibrium,
  from **any** feasible initial state, the realised sanction is `0` at every
  date, and `probe_pathF_eq` / `probe_pathF_tendsto_zero` — the political state
  decays geometrically to `0`.  Nothing locks in.
* `probe_no_perpetual_sanctions_counterexample` — hence no equilibrium, no
  positive floor and no non-degenerate basin `[a,b] ⊆ [0,1]` can satisfy the
  perpetual-sanction conclusion;
* `sign_conditions_insufficient_counterexample` and its fully parametric
  sibling `sign_conditions_insufficient_on_parameter_range` package this as the
  negation of the universal claim.

`probeEquilibrium` shows the refutation is not vacuous: the economy *does* have
an equilibrium, with both value functions Bellman fixed points and the Target
policy the unique maximiser of its Bellman integrand.

## The salvage: which quantitative margin is needed

`probe_senderFloorFlipSet_eq_empty` locates the failure inside the project's own
vocabulary: the Sender flip set `senderFloorFlipSet 1 0` is **empty** — not one
state clears even the static (`m = 0`) flip level, let alone the dynamic wedge
level `m > β_S·K_S·δ`.  `probeSigma_pos_iff` gives the exact margin in existing
parameters: the equilibrium sanction is positive at a state exactly when
`1 < ε·x`, i.e. exactly when the rally slope times the state exceeds the
Sender's own marginal sanction cost.  A sign condition (`ε > 0`) never delivers
that; a magnitude condition does.

Parametrically, `Theory/LockIn/PersistenceMargin.lean` proves both halves over
an arbitrary economy: a positive equilibrium sanction *requires* the stage loss
from sanctioning to be covered by the discounted continuation gain
(`realizedRule_margin`, `margin_of_positive_floor`), and the strict failure of
that comparison forces the equilibrium sanction to zero
(`realizedRule_eq_zero_of_stage_loss_dominates`).  `probe_margin_fails` below
records that the probe economy satisfies the collapse hypothesis exactly.

That file also states the **repair** and proves it is the weakest one
available.  The *margin at level `c`* — there is a feasible sanction `s ≥ c`
such that no feasible deviation's stage gain covers the continuation value it
gives up — is *logically equivalent* to the floor `c ≤ R x` itself
(`realizedRule_ge_iff_margin`), and is the existing basin field
`sender_high_argmax_exists` rewritten in raw primitives
(`senderHighArgmax_iff_margin`), so it widens no assumption surface.
`probe_margin_fails_at_every_positive_level` below closes the loop: the probe
economy fails that condition at every feasible state and every positive level.

**What this does not amount to.**  That equivalence is a restatement, not a
repair: its reverse direction is witnessed by the realised rule itself, so
calling the margin "the weakest condition restoring perpetual sanctions" would
reduce to the tautology that the floor is the weakest condition implying the
floor.  Worse for using it as a repair, the condition refers to `V_S`, which is
endogenous rather than a primitive.  **Stating an informative sufficient
condition in primitives alone is open**, and is the sharpest question this
counterexample raises.  The substantive general statement here is
`realizedRule_eq_zero_of_stage_loss_dominates`, which converts a magnitude
failure into an actual collapse of the equilibrium sanction and so makes this
economy an instance of a theorem rather than an isolated artefact.

## Any transition (renovation item BH5.3, 2026-10-07)

The refutation never reads the transition. Every equilibrium has the zero Sender
value, so `F` enters the Sender's objective only inside a zero function, the
realised sanction is `0` whatever `F` is, and the sign conditions involve only
the stage payoffs. `probeOver p₀ ε` installs the probe stage payoffs on an
arbitrary economy `p₀`, keeping its transition, its discount factors and its
adjustment rate, and the whole refutation is proved there:

* `sign_conditions_insufficient_generalF` — for every economy `p₀` and every
  rally slope `ε ∈ (0, 1]`, the probe economy over `p₀` has `p₀`'s transition
  and discounts, satisfies every sign condition, adjusts strictly exactly when
  `p₀` does, has an equilibrium, never sanctions, and admits no perpetual
  sanctions. No hypothesis on `p₀`;
* `probeOver_pathF_eq_reliefPathF` — its closed loop is `p₀`'s imposed-relief
  path, and under strict adjustment of `p₀` it converges to `0`
  (`probeOver_pathF_tendsto_zero`);
* `sign_conditions_insufficient_over` — under strict adjustment of `p₀`, the
  existential form with `p.F = p₀.F`, `p.β_S = p₀.β_S`, `p.β_T = p₀.β_T`.

So no condition on the transition, added to the sign conditions, can deliver
perpetual sanctions. Every affine statement below keeps its name and statement.
`probe_StrictAdjustment`, the closed forms `probe_pathF_eq` and
`probe_pathF_tendsto_zero`, and the stage identity `probeSigma_pos_iff` keep
their own proofs; every other `probe_*` result and both packaged theorems are
now instances of the `probeOver` forms at `p₀ = probeParams …`.

## Rule compliance

**Rule 1.** No strategy is posited.  The Sender's sanction is
`dynamicTopRealizedRule` — the greatest element of its forward-looking argmax
set; the Target's action carries the equilibrium's Bellman-optimality field; the
static selector `probeSigma` is proved to be the Sender's stage argmax.

**Rule 3.** No new assumption surface: the economy is a plain `AbstractGame.Params`
instance with every field discharged, and every theorem below is proved from it.

**Rule 5.** The economy and every theorem are parametric in `(δ, β_S, β_T, ε)`,
and through `probeOver` in the transition itself; the packaged existential is a
one-line specialisation.

**Rule 11.** This is a disprove artifact with a salvage, not a proof attempt.

**Rule 19.** Witness content, hence `Examples/`; the parametric margin theorems
live in `Theory/LockIn/PersistenceMargin.lean`.

**Rule 22.** The `probeOver` family is general in `F`. `probeParams` and the
results stated over it are affine-restricted (`affineF δ`); only
`probe_StrictAdjustment` and the closed forms `probe_pathF_eq`,
`probe_pathF_tendsto_zero` read the affine law.

**Numerics.** All constants are exact rationals.
-/

namespace Sanctions
namespace Examples

open Set AbstractGame BoundedContinuousFunction

noncomputable section

/-! ## The probe economy's primitives -/

/-- Sender stage payoff of the probe economy: a linear rally term with slope
`ε` in the political state, against the Sender's own quadratic sanction cost
with unit marginal cost at `s = 0`. -/
def probeU_S (ε x _a s : ℝ) : ℝ := (ε * x - 1) * s - s ^ 2 / 2

/-- Target stage payoff of the probe economy: rally around the flag (`s · x`)
plus a strictly concave compliance term pinning a unique interior optimum. -/
def probeU_T (x a s : ℝ) : ℝ := s * x - (a - 1 / 2) ^ 2

/-- The Sender's static stage argmax: the unconstrained maximiser `ε·x − 1`
of the concave stage payoff, clamped to `[0,1]`. -/
def probeSigma (ε x _a : ℝ) : ℝ := min 1 (max 0 (ε * x - 1))

theorem probeSigma_mem (ε : ℝ) : ∀ x a, probeSigma ε x a ∈ Set.Icc (0 : ℝ) 1 := by
  intro x a
  constructor
  · exact le_min zero_le_one (le_max_left _ _)
  · exact min_le_left _ _

theorem probeSigma_continuous (ε : ℝ) :
    Continuous (fun (xa : ℝ × ℝ) => probeSigma ε xa.1 xa.2) := by
  unfold probeSigma; fun_prop

/-- **Rule-1 coupling.** The clamped selector is the Sender's stage argmax at
every state and action: the stage payoff is concave in `s`, so the constrained
maximiser is the clamp of the unconstrained one. -/
theorem probeSigma_isMaxOn (ε : ℝ) : ∀ x a,
    IsMaxOn (fun s => probeU_S ε x a s) (Set.Icc (0 : ℝ) 1) (probeSigma ε x a) := by
  intro x a
  rw [isMaxOn_iff]
  rintro s ⟨hs0, hs1⟩
  simp only [probeU_S, probeSigma]
  set c : ℝ := ε * x - 1 with hc
  rcases le_or_gt c 0 with hle | hpos
  · have h1 : max 0 c = 0 := max_eq_left hle
    have h2 : min (1 : ℝ) 0 = 0 := by norm_num
    rw [h1, h2]
    nlinarith
  · rcases le_or_gt c 1 with hc1 | hc1
    · have h1 : max 0 c = c := max_eq_right hpos.le
      have h2 : min (1 : ℝ) c = c := min_eq_right hc1
      rw [h1, h2]
      nlinarith [sq_nonneg (c - s)]
    · have h1 : max 0 c = c := max_eq_right hpos.le
      have h2 : min (1 : ℝ) c = 1 := min_eq_left hc1.le
      rw [h1, h2]
      nlinarith

theorem probeU_S_continuous (ε : ℝ) :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => probeU_S ε xas.1 xas.2.1 xas.2.2) := by
  unfold probeU_S; fun_prop

theorem probeU_T_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => probeU_T xas.1 xas.2.1 xas.2.2) := by
  unfold probeU_T; fun_prop

/-- With the rally slope at or below the Sender's marginal sanction cost, the
Sender's stage payoff from any positive sanction is a loss at every feasible
state. -/
theorem probeU_S_nonpos (ε : ℝ) (hε1 : ε ≤ 1) {x s a : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : 0 ≤ s) : probeU_S ε x a s ≤ 0 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hεx : ε * x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hx0]
  simp only [probeU_S]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hεx), sq_nonneg s]

/-- ... and only the zero sanction avoids that loss. -/
theorem probe_eq_zero_of_nonneg (ε : ℝ) (hε1 : ε ≤ 1) {x s a : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : 0 ≤ s) (h : 0 ≤ probeU_S ε x a s) : s = 0 := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hεx : ε * x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hx0]
  simp only [probeU_S] at h
  have hs2 : s ^ 2 ≤ 0 := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hεx)]
  have hle : s ≤ 0 := by nlinarith [hs2]
  linarith

/-- `rfl`-level restatement of the Sender Bellman operator (Rule 19 thin
wrapper: no content beyond unfolding `integrandS`). -/
theorem bellmanS_BCF_apply (p : AbstractGame.Params) (α : ℝ → ℝ) (hα : Continuous α)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) :
    p.bellmanS_BCF α hα V x
      = sSup ((fun s => p.U_S x.val (α x.val) s
          + p.β_S * V (Sanctions.clipS' (p.F x.val s))) '' Sanctions.I) := rfl

/-- **The probe economy.** Fully parametric in the adjustment rate `δ`, both
discount factors, and the rally slope `ε`. -/
def probeParams (δ βS βT ε : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβS : βS ∈ Set.Ico (0 : ℝ) 1) (hβT : βT ∈ Set.Ico (0 : ℝ) 1) :
    AbstractGame.Params where
  δ := δ
  δ_mem := hδ
  β_T := βT
  β_T_mem := hβT
  β_S := βS
  β_S_mem := hβS
  U_T := probeU_T
  U_S := probeU_S ε
  σ := probeSigma ε
  σ_mem := probeSigma_mem ε
  σ_isMaxOn_U_S := probeSigma_isMaxOn ε
  U_T_continuous := probeU_T_continuous
  U_S_continuous := probeU_S_continuous ε
  F := AbstractGame.affineF δ
  F_continuous := AbstractGame.affineF_continuous δ
  F_mono_x := AbstractGame.affineF_mono_x hδ
  F_mono_s := AbstractGame.affineF_mono_s hδ
  F_diag := AbstractGame.affineF_diag δ

/-- **`probeParams` has a continuous static Sender selector.** Affine-restricted: the
family has the affine transition `affineF δ`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance probeParams_staticSelectorContinuous (δ βS βT ε : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβS : βS ∈ Set.Ico (0 : ℝ) 1) (hβT : βT ∈ Set.Ico (0 : ℝ) 1) :
    (probeParams δ βS βT ε hδ hβS hβT).StaticSelectorContinuous where
  σ_continuous := probeSigma_continuous ε

section Projections

variable {δ βS βT ε : ℝ} {hδ : δ ∈ Set.Ioo (0 : ℝ) 1}
  {hβS : βS ∈ Set.Ico (0 : ℝ) 1} {hβT : βT ∈ Set.Ico (0 : ℝ) 1}

@[simp] theorem probeParams_U_S : (probeParams δ βS βT ε hδ hβS hβT).U_S = probeU_S ε := rfl
@[simp] theorem probeParams_U_T : (probeParams δ βS βT ε hδ hβS hβT).U_T = probeU_T := rfl
@[simp] theorem probeParams_σ : (probeParams δ βS βT ε hδ hβS hβT).σ = probeSigma ε := rfl
@[simp] theorem probeParams_F :
    (probeParams δ βS βT ε hδ hβS hβT).F = AbstractGame.affineF δ := rfl
@[simp] theorem probeParams_β_S : (probeParams δ βS βT ε hδ hβS hβT).β_S = βS := rfl
@[simp] theorem probeParams_β_T : (probeParams δ βS βT ε hδ hβS hβT).β_T = βT := rfl
@[simp] theorem probeParams_δ : (probeParams δ βS βT ε hδ hβS hβT).δ = δ := rfl

end Projections

/-! ## The probe economy over any transition (renovation item BH5.3)

The refutation never reads the transition: every equilibrium value is zero, so
`F` enters the objectives only inside a zero function. Everything in this
section is stated over `probeOver p₀ ε`, the probe stage payoffs installed on an
arbitrary economy `p₀`. General in `F`. -/

/-- **The probe economy over an arbitrary base economy** (renovation item BH5.3,
2026-10-07). Keeps the transition `F`, both discount factors and the adjustment
rate of `p₀`, and installs the probe stage payoffs `probeU_S ε`, `probeU_T` and
the static selector `probeSigma ε`. General in `F`: the transition is whatever
`p₀` carries, affine or not. At `p₀ = probeParams δ βS βT ε …` it is that
economy, field for field. -/
def probeOver (p₀ : AbstractGame.Params) (ε : ℝ) : AbstractGame.Params :=
  { p₀ with
    U_T := probeU_T
    U_S := probeU_S ε
    σ := probeSigma ε
    σ_mem := probeSigma_mem ε
    σ_isMaxOn_U_S := probeSigma_isMaxOn ε
    U_T_continuous := probeU_T_continuous
    U_S_continuous := probeU_S_continuous ε }

/-- **`probeOver` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance probeOver_staticSelectorContinuous (p₀ : AbstractGame.Params) (ε : ℝ) :
    (probeOver p₀ ε).StaticSelectorContinuous where
  σ_continuous := probeSigma_continuous ε

section OverAnyTransition

variable (p₀ : AbstractGame.Params) (ε : ℝ)

@[simp] theorem probeOver_U_S : (probeOver p₀ ε).U_S = probeU_S ε := rfl
@[simp] theorem probeOver_U_T : (probeOver p₀ ε).U_T = probeU_T := rfl
@[simp] theorem probeOver_σ : (probeOver p₀ ε).σ = probeSigma ε := rfl
@[simp] theorem probeOver_F : (probeOver p₀ ε).F = p₀.F := rfl
@[simp] theorem probeOver_β_S : (probeOver p₀ ε).β_S = p₀.β_S := rfl
@[simp] theorem probeOver_β_T : (probeOver p₀ ε).β_T = p₀.β_T := rfl
@[simp] theorem probeOver_δ : (probeOver p₀ ε).δ = p₀.δ := rfl

/-- **Strict adjustment is inherited exactly**: the probe economy over `p₀` has
`p₀`'s transition, so it moves strictly toward the sanction exactly when `p₀`
does. General in `F`. -/
theorem probeOver_strictAdjustment_iff :
    (probeOver p₀ ε).StrictAdjustment ↔ p₀.StrictAdjustment := Iff.rfl

/-- **Strict Sender stage complementarity**, over any transition, for every
strictly positive rally slope. General in `F` (the condition reads `U_S` only). -/
theorem probeOver_SenderStageIDStrict (hε : 0 < ε) :
    (probeOver p₀ ε).SenderStageIDStrict := by
  intro a _ha s₁ _hs₁ s₂ _hs₂ hs x hx y hy hxy
  simp only [probeOver_U_S, probeU_S]
  nlinarith [mul_pos hε (sub_pos.mpr hxy), sub_pos.mpr hs]

/-- **Strict Target stage complementarity** (rally around the flag), over any
transition. General in `F`. -/
theorem probeOver_TargetStageIDStrict : (probeOver p₀ ε).TargetStageIDStrict := by
  intro a _ha s₁ _hs₁ s₂ _hs₂ hs x hx y hy hxy
  simp only [probeOver_U_T, probeU_T]
  nlinarith [sub_pos.mpr hs, sub_pos.mpr hxy]

theorem probeOver_SenderStageID (hε : 0 < ε) : (probeOver p₀ ε).SenderStageID :=
  (probeOver_SenderStageIDStrict p₀ ε hε).toSenderStageID

theorem probeOver_TargetStageID : (probeOver p₀ ε).TargetStageID :=
  (probeOver_TargetStageIDStrict p₀ ε).toTargetStageID

/-- **Compliance placates** (chord form), over any transition. General in `F`. -/
theorem probeOver_SenderActionDD : (probeOver p₀ ε).SenderActionDD := by
  intro x _hx s s' a a' _ _ _ _ _ _
  simp only [probeOver_U_S, probeU_S]
  exact le_refl _

/-- **The Sender's continuation value is identically zero**, over any transition:
the zero function is a fixed point of the Sender Bellman operator at every Target
policy. General in `F`: `F` appears only as the argument of the zero value. -/
theorem probeOver_bellmanS_zero (hε1 : ε ≤ 1) (α : ℝ → ℝ) (hα : Continuous α) :
    (probeOver p₀ ε).bellmanS_BCF α hα 0 = 0 := by
  ext x
  rw [bellmanS_BCF_apply]
  have hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
  have hg : IsGreatest ((fun s => (probeOver p₀ ε).U_S x.val (α x.val) s
      + (probeOver p₀ ε).β_S
        * (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
            (Sanctions.clipS' ((probeOver p₀ ε).F x.val s)))
        '' Sanctions.I) 0 := by
    constructor
    · exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp [probeU_S]⟩
    · rintro y ⟨s, hs, rfl⟩
      simp only [probeOver_U_S, probeOver_β_S,
        BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero]
      exact probeU_S_nonpos ε hε1 hx hs.1
  rw [hg.csSup_eq]
  simp

/-- **Every equilibrium of the probe economy over `p₀` has the zero Sender value.**
The Bellman operator is a `β_S`-contraction (`β_S < 1` from `p₀.β_S_mem`) and zero
is one of its fixed points. General in `F`. -/
theorem probeOver_V_S_eq_zero (hε1 : ε ≤ 1) {α : ℝ → ℝ} (hα : Continuous α)
    {W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hW : W = (probeOver p₀ ε).bellmanS_BCF α hα W) : W = 0 := by
  have hT0 := probeOver_bellmanS_zero p₀ ε hε1 α hα
  have hβS := p₀.β_S_mem
  have hstep : dist W 0 ≤ p₀.β_S * dist W 0 := by
    calc dist W 0
        = dist ((probeOver p₀ ε).bellmanS_BCF α hα W)
            ((probeOver p₀ ε).bellmanS_BCF α hα 0) := by
          rw [← hW, hT0]
      _ ≤ p₀.β_S * dist W 0 := by
          refine (BoundedContinuousFunction.dist_le
            (mul_nonneg hβS.1 dist_nonneg)).mpr (fun x => ?_)
          exact (probeOver p₀ ε).bellmanS_BCF_pointwise_dist hα W 0 x
  have hnn : (0 : ℝ) ≤ dist W (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) := dist_nonneg
  have hle : dist W 0 ≤ 0 := by nlinarith [hβS.2]
  exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)

/-- **The Sender's forward-looking argmax is the zero sanction**, at every feasible
state and every Target action, over any transition. General in `F`. -/
theorem probeOver_σ_dyn_top_eq_zero (hε1 : ε ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    (probeOver p₀ ε).σ_dyn_top 0 x a = 0 := by
  have hset : (probeOver p₀ ε).dynamicArgmaxSet 0 x a = {0} := by
    ext s
    constructor
    · rintro ⟨hsI, hmax⟩
      have h0 : (0 : ℝ) ∈ Sanctions.I := ⟨le_refl 0, zero_le_one⟩
      have hcmp := hmax h0
      simp only [Set.mem_setOf_eq, probeOver_U_S, probeOver_β_S,
        BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero,
        probeU_S] at hcmp
      have : (0 : ℝ) ≤ probeU_S ε x a s := by simp only [probeU_S]; nlinarith
      exact probe_eq_zero_of_nonneg ε hε1 hx hsI.1 this
    · rintro rfl
      refine ⟨⟨le_refl 0, zero_le_one⟩, fun s hs => ?_⟩
      simp only [probeOver_U_S, probeOver_β_S,
        BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero]
      have := probeU_S_nonpos ε hε1 (a := a) hx hs.1
      simpa [probeU_S] using this
  unfold AbstractGame.Params.σ_dyn_top
  rw [hset, csSup_singleton]

/-- **An equilibrium of the probe economy over any transition.** The Target's
policy is the unique maximiser of its Bellman integrand; both value functions are
Bellman fixed points; the Sender's response is the greatest element of its
dynamic argmax. General in `F`. -/
def probeOverEquilibrium (hε1 : ε ≤ 1) :
    (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop where
  V_T := 0
  V_S := 0
  α := fun _ => 1 / 2
  hα := continuous_const
  α_mem := fun _ _ => ⟨by norm_num, by norm_num⟩
  V_S_fix := (probeOver_bellmanS_zero p₀ ε hε1 _ continuous_const).symm
  V_T_fix_top := by
    intro x
    have hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
    have hg : IsGreatest ((fun a => (probeOver p₀ ε).joint_T_top_integrand
        0 0 x.val a) '' Sanctions.I) 0 := by
      constructor
      · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        simp only [AbstractGame.Params.joint_T_top_integrand,
          probeOver_σ_dyn_top_eq_zero p₀ ε hε1 hx, probeOver_U_T, probeU_T]
        norm_num
      · rintro y ⟨a, ha, rfl⟩
        simp only [AbstractGame.Params.joint_T_top_integrand,
          probeOver_σ_dyn_top_eq_zero p₀ ε hε1 hx, probeOver_U_T, probeU_T]
        simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero]
        nlinarith [sq_nonneg (a - 1 / 2)]
    rw [hg.csSup_eq]
    simp
  α_opt_top := by
    intro x hx a ha
    simp only [AbstractGame.Params.joint_T_top_integrand,
      probeOver_σ_dyn_top_eq_zero p₀ ε hε1 hx, probeOver_U_T, probeU_T]
    simp only [Set.mem_setOf_eq, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      mul_zero, add_zero]
    nlinarith [sq_nonneg (a - 1 / 2)]

/-- **The realised equilibrium sanction is zero at every feasible state, in every
equilibrium**, over any transition. General in `F`. -/
theorem probeOver_realizedRule_eq_zero (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (probeOver p₀ ε).dynamicTopRealizedRule E.V_S E.α x = 0 := by
  have hV : E.V_S = 0 := probeOver_V_S_eq_zero p₀ ε hε1 E.hα E.V_S_fix
  change (probeOver p₀ ε).σ_dyn_top E.V_S x (E.α x) = 0
  rw [hV]
  exact probeOver_σ_dyn_top_eq_zero p₀ ε hε1 hx _

/-- **The closed loop is the imposed-relief path of the base economy.** With no
sanction ever imposed, the equilibrium state path from any feasible `x₀` is
`p₀`'s path under a forced zero sanction, `x ↦ F(x, 0)` iterated. General in `F`;
`probe_pathF_eq` is its affine closed form `(1 − δ)^n · x₀`. -/
theorem probeOver_pathF_eq_reliefPathF (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, (probeOver p₀ ε).dynamicTopLockInPathF E.V_S E.α x₀ n = p₀.reliefPathF x₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [AbstractGame.Params.dynamicTopLockInPathF_succ,
        AbstractGame.Params.reliefPathF_succ, ih]
      have h0 := probeOver_realizedRule_eq_zero p₀ ε hε1 E
        (p₀.reliefPathF_mem_Icc01 hx₀.1 hx₀.2 n)
      change (probeOver p₀ ε).F _ ((probeOver p₀ ε).dynamicTopRealizedRule E.V_S E.α _)
        = p₀.F _ 0
      rw [h0, probeOver_F]

/-- **No sanction is ever imposed, in any equilibrium, from any feasible initial
state**, over any transition. General in `F`. -/
theorem probeOver_sanctionsF_eq_zero (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, (probeOver p₀ ε).dynamicTopLockInSanctionsF E.V_S E.α x₀ n = 0 := by
  intro n
  change (probeOver p₀ ε).dynamicTopRealizedRule E.V_S E.α _ = 0
  rw [probeOver_pathF_eq_reliefPathF p₀ ε hε1 E hx₀ n]
  exact probeOver_realizedRule_eq_zero p₀ ε hε1 E (p₀.reliefPathF_mem_Icc01 hx₀.1 hx₀.2 n)

/-- **The state path converges to the zero state when the base transition adjusts
strictly**: there is no lock-in. Under strict adjustment of `p₀`, the imposed-relief
path enters `[0, x̄]` for every `x̄ ∈ (0, 1]` within
`fullReliefExitHorizon x̄` periods and stays there
(`reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment`). General in `F`;
the hypothesis is needed, since under the flat transition `F x s = x` the state
never moves. -/
theorem probeOver_pathF_tendsto_zero (hAdj : p₀.StrictAdjustment) (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto ((probeOver p₀ ε).dynamicTopLockInPathF E.V_S E.α x₀)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hxbar : min (η / 2) 1 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩
  refine ⟨p₀.fullReliefExitHorizon (min (η / 2) 1), fun n hn => ?_⟩
  have hmem :=
    p₀.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj hxbar x₀ hx₀ n hn
  rw [probeOver_pathF_eq_reliefPathF p₀ ε hε1 E hx₀ n, Real.dist_eq, sub_zero,
    abs_of_nonneg hmem.1]
  linarith [hmem.2, min_le_left (η / 2) 1]

/-- **REFUTATION, over any transition.** At the probe economy over `p₀` no
equilibrium exhibits perpetual sanctions: there is no equilibrium, positive
floor, and non-degenerate basin `[a,b] ⊆ [0,1]` along which the realised sanction
stays above the floor. General in `F`, with no hypothesis on `p₀`. -/
theorem probeOver_no_perpetual_sanctions (hε1 : ε ≤ 1) :
    ¬ ∃ (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop) (sbar a b : ℝ),
        0 < sbar ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
        ∀ x₀ ∈ Set.Icc a b,
          (∀ n, (probeOver p₀ ε).dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc a b)
          ∧ (∀ n, sbar ≤ (probeOver p₀ ε).dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
          ∧ Monotone ((probeOver p₀ ε).dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  rintro ⟨E, sbar, a, b, hsbar, ha0, hab, hb1, hall⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hb01 : b ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hb1⟩
  have hfloor := (hall b hb).2.1 0
  rw [probeOver_sanctionsF_eq_zero p₀ ε hε1 E hb01 0] at hfloor
  linarith

/-- No equilibrium keeps the realised sanction above any positive floor even at a
single feasible initial state, over any transition. General in `F`. -/
theorem probeOver_no_positive_floor (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {sbar x₀ : ℝ} (hsbar : 0 < sbar) (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ¬ ∀ n, sbar ≤ (probeOver p₀ ε).dynamicTopLockInSanctionsF E.V_S E.α x₀ n := by
  intro hall
  have := hall 0
  rw [probeOver_sanctionsF_eq_zero p₀ ε hε1 E hx₀ 0] at this
  linarith

/-- **The Sender flip set is empty**, over any transition: at every feasible state
the Sender's full sanction chord is a strict stage loss. General in `F` (the flip
set reads `U_S` only). -/
theorem probeOver_senderFloorFlipSet_eq_empty (hε1 : ε ≤ 1) :
    (probeOver p₀ ε).senderFloorFlipSet 1 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hxI, hx⟩
  have h := hx 0 ⟨le_refl 0, zero_le_one⟩ 0 ⟨le_refl 0, zero_le_one⟩ 1
    ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [probeOver_U_S, probeU_S] at h
  have := hxI.2
  have := hxI.1
  nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hxI.1]

/-- **The probe economy fails the parametric margin exactly**, over any
transition: every positive sanction's stage loss strictly exceeds the discounted
continuation gain it buys, which is zero. General in `F`. -/
theorem probeOver_margin_fails (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s ∈ Sanctions.I, 0 < s →
      (probeOver p₀ ε).β_S
          * (E.V_S (Sanctions.clipS' ((probeOver p₀ ε).F x s))
              - E.V_S (Sanctions.clipS' ((probeOver p₀ ε).F x 0)))
        < (probeOver p₀ ε).U_S x (E.α x) 0 - (probeOver p₀ ε).U_S x (E.α x) s := by
  intro s hs hs0
  have hV : E.V_S = 0 := probeOver_V_S_eq_zero p₀ ε hε1 E.hα E.V_S_fix
  have hεx : ε * x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hx.1, hx.2]
  rw [hV]
  simp only [probeOver_U_S, probeU_S, BoundedContinuousFunction.coe_zero,
    Pi.zero_apply, mul_zero, sub_self]
  nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hεx), mul_pos hs0 hs0]

/-- **The probe economy fails the salvage hypothesis at every positive level**,
over any transition: every equilibrium realises `R x = 0`, so the margin at level
`c > 0` fails at every feasible state. General in `F`. -/
theorem probeOver_margin_fails_at_every_positive_level (hε1 : ε ≤ 1)
    (E : (probeOver p₀ ε).FeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 < c) :
    ¬ ∃ s ∈ Sanctions.I, c ≤ s ∧ ∀ s' ∈ Sanctions.I,
        (probeOver p₀ ε).U_S x (E.α x) s' - (probeOver p₀ ε).U_S x (E.α x) s
          ≤ (probeOver p₀ ε).β_S
              * (E.V_S (Sanctions.clipS' ((probeOver p₀ ε).F x s))
                  - E.V_S (Sanctions.clipS' ((probeOver p₀ ε).F x s'))) := by
  intro h
  have hge := (probeOver p₀ ε).realizedRule_ge_of_margin E.V_S E.α h
  rw [probeOver_realizedRule_eq_zero p₀ ε hε1 E hx] at hge
  linarith

end OverAnyTransition

/-! ### The packaged refutation over any transition -/

/-- **Sign conditions do not imply perpetual sanctions, over any transition and
any discounts** (renovation item BH5.3, 2026-10-07).

For every economy `p₀` and every rally slope `ε ∈ (0, 1]`, the probe economy over
`p₀` has `p₀`'s transition and discount factors, adjusts strictly toward the
sanction exactly when `p₀` does, satisfies strict Sender and Target stage
complementarity, their weak forms and the compliance-placates condition, has an
equilibrium, never imposes a sanction in any equilibrium from any feasible
state, and admits no equilibrium sustaining sanctions above a positive floor on a
non-degenerate basin.

General in `F`, with no hypothesis on `p₀`: the affine transition, the adjustment
rate and the discount values that `sign_conditions_insufficient_on_parameter_range`
fixes are dropped. Strict adjustment, which that theorem asserts outright, appears
here as the equivalence with `p₀`'s, since it is a property of the transition
alone. -/
theorem sign_conditions_insufficient_generalF (p₀ : AbstractGame.Params) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let p := probeOver p₀ ε
    p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T
      ∧ (p.StrictAdjustment ↔ p₀.StrictAdjustment)
      ∧ p.SenderStageIDStrict ∧ p.TargetStageIDStrict
      ∧ p.SenderStageID ∧ p.TargetStageID
      ∧ p.SenderActionDD
      ∧ Nonempty p.FeedbackStackelbergEquilibriumTop
      ∧ (∀ (E : p.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ),
          x₀ ∈ Set.Icc (0 : ℝ) 1 →
          ∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n = 0)
      ∧ ¬ ∃ (E : p.FeedbackStackelbergEquilibriumTop) (sbar a b : ℝ),
          0 < sbar ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
          ∀ x₀ ∈ Set.Icc a b,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc a b)
            ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
            ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  ⟨rfl, rfl, rfl, probeOver_strictAdjustment_iff p₀ ε,
   probeOver_SenderStageIDStrict p₀ ε hε0,
   probeOver_TargetStageIDStrict p₀ ε,
   probeOver_SenderStageID p₀ ε hε0,
   probeOver_TargetStageID p₀ ε,
   probeOver_SenderActionDD p₀ ε,
   ⟨probeOverEquilibrium p₀ ε hε1⟩,
   fun E _ hx₀ => probeOver_sanctionsF_eq_zero p₀ ε hε1 E hx₀,
   probeOver_no_perpetual_sanctions p₀ ε hε1⟩

/-- **The existential form for any strictly adjusting transition.** For every
economy `p₀` whose transition moves strictly toward the sanction, there is an
economy with the same transition and the same two discount factors that satisfies
every sign condition the project states — including strict adjustment — possesses
an equilibrium, and in which no equilibrium sustains sanctions above any positive
floor on any non-degenerate basin.

General in `F`. The one hypothesis, strict adjustment of `p₀`, is used only for the
strict-adjustment conjunct (it is a property of `F` alone). The economy is the
probe economy over `p₀` at rally slope `1/2`. -/
theorem sign_conditions_insufficient_over (p₀ : AbstractGame.Params)
    (hAdj : p₀.StrictAdjustment) :
    ∃ p : AbstractGame.Params,
      p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T
      ∧ p.SenderStageIDStrict ∧ p.TargetStageIDStrict
      ∧ p.SenderStageID ∧ p.TargetStageID
      ∧ p.SenderActionDD ∧ p.StrictAdjustment
      ∧ Nonempty p.FeedbackStackelbergEquilibriumTop
      ∧ ¬ ∃ (E : p.FeedbackStackelbergEquilibriumTop) (sbar a b : ℝ),
          0 < sbar ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
          ∀ x₀ ∈ Set.Icc a b,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc a b)
            ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
            ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  ⟨probeOver p₀ (1 / 2), rfl, rfl, rfl,
   probeOver_SenderStageIDStrict p₀ _ (by norm_num),
   probeOver_TargetStageIDStrict p₀ _,
   probeOver_SenderStageID p₀ _ (by norm_num),
   probeOver_TargetStageID p₀ _,
   probeOver_SenderActionDD p₀ _,
   (probeOver_strictAdjustment_iff p₀ _).2 hAdj,
   ⟨probeOverEquilibrium p₀ _ (by norm_num)⟩,
   probeOver_no_perpetual_sanctions p₀ _ (by norm_num)⟩

/-! ## The probe economy satisfies every sign condition in the project

The affine economy `probeParams`. Since round BH-5 (renovation item BH5.3,
2026-10-07) each result here except `probe_StrictAdjustment` is the instance of
its `probeOver_*` form at `p₀ = probeParams …`, which is the same economy;
statements unchanged. -/

section SignConditions

variable (δ βS βT ε : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
  (hβS : βS ∈ Set.Ico (0 : ℝ) 1) (hβT : βT ∈ Set.Ico (0 : ℝ) 1)

/-- **Strict Sender stage complementarity** holds for every strictly positive
rally slope, however small. -/
theorem probe_SenderStageIDStrict (hε : 0 < ε) :
    (probeParams δ βS βT ε hδ hβS hβT).SenderStageIDStrict :=
  probeOver_SenderStageIDStrict (probeParams δ βS βT ε hδ hβS hβT) ε hε

/-- **Strict Target stage complementarity** (rally around the flag). -/
theorem probe_TargetStageIDStrict :
    (probeParams δ βS βT ε hδ hβS hβT).TargetStageIDStrict :=
  probeOver_TargetStageIDStrict (probeParams δ βS βT ε hδ hβS hβT) ε

theorem probe_SenderStageID (hε : 0 < ε) :
    (probeParams δ βS βT ε hδ hβS hβT).SenderStageID :=
  (probe_SenderStageIDStrict δ βS βT ε hδ hβS hβT hε).toSenderStageID

theorem probe_TargetStageID :
    (probeParams δ βS βT ε hδ hβS hβT).TargetStageID :=
  (probe_TargetStageIDStrict δ βS βT ε hδ hβS hβT).toTargetStageID

/-- **Compliance placates** (`∂²U_S/∂s∂a ≤ 0`, chord form): the Sender's
sanction chord does not rise with Target compliance. -/
theorem probe_SenderActionDD :
    (probeParams δ βS βT ε hδ hβS hβT).SenderActionDD :=
  probeOver_SenderActionDD (probeParams δ βS βT ε hδ hβS hβT) ε

/-- **Strict directional adjustment**: the state moves strictly toward the
current sanction. -/
theorem probe_StrictAdjustment :
    (probeParams δ βS βT ε hδ hβS hβT).StrictAdjustment :=
  AbstractGame.strictAdjustment_of_F_eq_affineF _ hδ rfl

end SignConditions

/-! ## The collapse branch: a rally slope below the Sender's own marginal cost

At the affine economy `probeParams`. Since round BH-5 (renovation item BH5.3,
2026-10-07) each result here except the closed forms `probe_pathF_eq`,
`probe_pathF_tendsto_zero` and the stage identity `probeSigma_pos_iff` is the
instance of its `probeOver_*` form at `p₀ = probeParams …`; statements
unchanged. -/

section Collapse

variable (δ βS βT ε : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
  (hβS : βS ∈ Set.Ico (0 : ℝ) 1) (hβT : βT ∈ Set.Ico (0 : ℝ) 1)

/-- **The Sender's continuation value is identically zero.**  The zero function
is a fixed point of the Sender Bellman operator at every Target policy. -/
theorem probe_bellmanS_zero (hε1 : ε ≤ 1) (α : ℝ → ℝ) (hα : Continuous α) :
    (probeParams δ βS βT ε hδ hβS hβT).bellmanS_BCF α hα 0 = 0 :=
  probeOver_bellmanS_zero (probeParams δ βS βT ε hδ hβS hβT) ε hε1 α hα

/-- **Every equilibrium of the probe economy has the zero Sender value.**  The
Bellman operator is a `β_S`-contraction and zero is one of its fixed points. -/
theorem probe_V_S_eq_zero (hε1 : ε ≤ 1) {α : ℝ → ℝ} (hα : Continuous α)
    {W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hW : W = (probeParams δ βS βT ε hδ hβS hβT).bellmanS_BCF α hα W) : W = 0 :=
  probeOver_V_S_eq_zero (probeParams δ βS βT ε hδ hβS hβT) ε hε1 hα hW

/-- **The Sender's forward-looking argmax is the zero sanction, at every
feasible state and every Target action.**  This is the equilibrium sanction:
`σ_dyn_top` is the greatest maximiser of the Sender's dynamic objective. -/
theorem probe_σ_dyn_top_eq_zero (hε1 : ε ≤ 1) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    (probeParams δ βS βT ε hδ hβS hβT).σ_dyn_top 0 x a = 0 :=
  probeOver_σ_dyn_top_eq_zero (probeParams δ βS βT ε hδ hβS hβT) ε hε1 hx a

/-! ### The equilibrium exists (the refutation is not vacuous) -/

/-- **An equilibrium of the probe economy.**  The Target's policy is the unique
maximiser of its Bellman integrand; both value functions are Bellman fixed
points; the Sender's response is the greatest element of its dynamic argmax. -/
def probeEquilibrium (hε1 : ε ≤ 1) :
    (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop :=
  probeOverEquilibrium (probeParams δ βS βT ε hδ hβS hβT) ε hε1

/-! ### The closed loop of every equilibrium -/

/-- **The realised equilibrium sanction is zero at every feasible state, in
every equilibrium of the probe economy.** -/
theorem probe_realizedRule_eq_zero (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (probeParams δ βS βT ε hδ hβS hβT).dynamicTopRealizedRule E.V_S E.α x = 0 :=
  probeOver_realizedRule_eq_zero (probeParams δ βS βT ε hδ hβS hβT) ε hε1 E hx

theorem probe_pow_mem' {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (1 - δ) ^ n * x₀ ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith [hδ.2]
  have h1 : (1 - δ) ≤ 1 := by linarith [hδ.1]
  have hp0 : (0 : ℝ) ≤ (1 - δ) ^ n := pow_nonneg h0 n
  have hp1 : (1 - δ) ^ n ≤ 1 := pow_le_one₀ h0 h1
  exact ⟨mul_nonneg hp0 hx₀.1, by nlinarith [hx₀.1, hx₀.2]⟩

/-- **The closed-loop state decays geometrically**: with no sanction ever
imposed, the political state is `(1 − δ)^n · x₀`. -/
theorem probe_pathF_eq (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, (probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInPathF E.V_S E.α x₀ n
      = (1 - δ) ^ n * x₀ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [AbstractGame.Params.dynamicTopLockInPathF_succ, ih]
      change (probeParams δ βS βT ε hδ hβS hβT).F _ _ = _
      rw [probe_realizedRule_eq_zero δ βS βT ε hδ hβS hβT hε1 E
        (probe_pow_mem' hδ hx₀ n)]
      change AbstractGame.affineF δ _ 0 = _
      simp only [AbstractGame.affineF]
      ring

/-- **No sanction is ever imposed, in any equilibrium, from any feasible
initial state.** -/
theorem probe_sanctionsF_eq_zero (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, (probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInSanctionsF E.V_S E.α x₀ n
      = 0 :=
  probeOver_sanctionsF_eq_zero (probeParams δ βS βT ε hδ hβS hβT) ε hε1 E hx₀

/-- The state path converges to the zero state: there is no lock-in. -/
theorem probe_pathF_tendsto_zero (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      ((probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInPathF E.V_S E.α x₀)
      Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => (1 - δ) ^ n * x₀) Filter.atTop (nhds (0 * x₀)) := by
    refine Filter.Tendsto.mul_const x₀ ?_
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hδ.2]) ?_
    linarith [hδ.1]
  rw [zero_mul] at h
  refine h.congr (fun n => ?_)
  exact (probe_pathF_eq δ βS βT ε hδ hβS hβT hε1 E hx₀ n).symm

/-! ### The headline refutation -/

/-- **REFUTATION.**  At the probe economy no equilibrium exhibits perpetual
sanctions: there is no equilibrium, positive floor, and non-degenerate basin
`[a,b] ⊆ [0,1]` along which the realised sanction stays above the floor. -/
theorem probe_no_perpetual_sanctions_counterexample (hε1 : ε ≤ 1) :
    ¬ ∃ (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
        (sbar a b : ℝ),
        0 < sbar ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
        ∀ x₀ ∈ Set.Icc a b,
          (∀ n, (probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInPathF
                  E.V_S E.α x₀ n ∈ Set.Icc a b)
          ∧ (∀ n, sbar ≤ (probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInSanctionsF
                  E.V_S E.α x₀ n)
          ∧ Monotone ((probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInSanctionsF
                  E.V_S E.α x₀) :=
  probeOver_no_perpetual_sanctions (probeParams δ βS βT ε hδ hβS hβT) ε hε1

/-- The same conclusion in the weakest form: no equilibrium keeps the realised
sanction above any positive floor even at a single feasible initial state. -/
theorem probe_no_positive_floor (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {sbar x₀ : ℝ} (hsbar : 0 < sbar) (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ¬ ∀ n, sbar ≤ (probeParams δ βS βT ε hδ hβS hβT).dynamicTopLockInSanctionsF
        E.V_S E.α x₀ n :=
  probeOver_no_positive_floor (probeParams δ βS βT ε hδ hβS hβT) ε hε1 E hsbar hx₀

/-! ### Where exactly the sign conditions fall short -/

/-- **The Sender flip set is empty.**  At every feasible state the Sender's
full sanction chord is a strict stage loss, so no state clears even the
`m = 0` (static) flip level — let alone the dynamic wedge level. -/
theorem probe_senderFloorFlipSet_eq_empty (hε1 : ε ≤ 1) :
    (probeParams δ βS βT ε hδ hβS hβT).senderFloorFlipSet 1 0 = ∅ :=
  probeOver_senderFloorFlipSet_eq_empty (probeParams δ βS βT ε hδ hβS hβT) ε hε1

/-- **The exact margin.**  The Sender's equilibrium stage sanction is strictly
positive at a state exactly when the rally slope times the state exceeds the
Sender's own marginal sanction cost at zero. -/
theorem probeSigma_pos_iff (x a : ℝ) : 0 < probeSigma ε x a ↔ 1 < ε * x := by
  simp only [probeSigma]
  constructor
  · intro h
    have h1 : 0 < max 0 (ε * x - 1) := lt_of_lt_of_le h (min_le_right _ _)
    rcases max_cases (0 : ℝ) (ε * x - 1) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h1; exact absurd h1 (lt_irrefl 0)
    · rw [he] at h1; linarith
  · intro h
    have he : max 0 (ε * x - 1) = ε * x - 1 := max_eq_right (by linarith)
    rw [he]
    exact lt_min zero_lt_one (by linarith)

/-- **The probe economy fails the parametric margin exactly.**  At every
feasible state, every positive sanction's stage loss strictly exceeds the
discounted continuation gain it buys — which is zero, since the equilibrium
Sender value is constant.  This is the hypothesis of
`realizedRule_eq_zero_of_stage_loss_dominates`, so the collapse is an instance
of the general margin theorem, not an artefact of the example. -/
theorem probe_margin_fails (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s ∈ Sanctions.I, 0 < s →
      (probeParams δ βS βT ε hδ hβS hβT).β_S
          * (E.V_S (Sanctions.clipS' ((probeParams δ βS βT ε hδ hβS hβT).F x s))
              - E.V_S (Sanctions.clipS' ((probeParams δ βS βT ε hδ hβS hβT).F x 0)))
        < (probeParams δ βS βT ε hδ hβS hβT).U_S x (E.α x) 0
            - (probeParams δ βS βT ε hδ hβS hβT).U_S x (E.α x) s :=
  probeOver_margin_fails (probeParams δ βS βT ε hδ hβS hβT) ε hε1 E hx

/-- **The probe economy fails the salvage hypothesis at every positive level.**

`Theory/LockIn/PersistenceMargin.lean` shows that the floor `c ≤ R x` on the
equilibrium-realised sanction is *logically equivalent* to the margin at level
`c` — "there is a feasible sanction at or above `c` from which no feasible
deviation pays for itself".  Here the contrapositive is exhibited: because
every equilibrium of the probe economy realises `R x = 0`, the margin fails at
**every** feasible state and **every** strictly positive level.

So the refutation is not a stray obstruction unrelated to the repair.  It is
precisely a failure of the salvage hypothesis, and the salvage hypothesis is
precisely what the sign conditions do not deliver. -/
theorem probe_margin_fails_at_every_positive_level (hε1 : ε ≤ 1)
    (E : (probeParams δ βS βT ε hδ hβS hβT).FeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 < c) :
    ¬ ∃ s ∈ Sanctions.I, c ≤ s ∧ ∀ s' ∈ Sanctions.I,
        (probeParams δ βS βT ε hδ hβS hβT).U_S x (E.α x) s'
            - (probeParams δ βS βT ε hδ hβS hβT).U_S x (E.α x) s
          ≤ (probeParams δ βS βT ε hδ hβS hβT).β_S
              * (E.V_S (Sanctions.clipS'
                    ((probeParams δ βS βT ε hδ hβS hβT).F x s))
                  - E.V_S (Sanctions.clipS'
                    ((probeParams δ βS βT ε hδ hβS hβT).F x s'))) :=
  probeOver_margin_fails_at_every_positive_level (probeParams δ βS βT ε hδ hβS hβT) ε hε1
    E hx hc

end Collapse

/-! ## The packaged refutation -/

/-- **Sign conditions do not imply perpetual sanctions.**

There is an economy of the model class that satisfies every sign condition the
project states — strict Sender and Target stage complementarity, their weak
(chord) forms, the compliance-placates cross-condition, and strict directional
adjustment — that possesses an equilibrium, and in which *no* equilibrium
sustains sanctions above any positive floor on any non-degenerate basin.

Since round BH-5 (renovation item BH5.3, 2026-10-07) a corollary of
`sign_conditions_insufficient_over`, whose economy keeps any strictly adjusting
transition; statement unchanged. -/
theorem sign_conditions_insufficient_counterexample :
    ∃ p : AbstractGame.Params,
      p.SenderStageIDStrict ∧ p.TargetStageIDStrict
      ∧ p.SenderStageID ∧ p.TargetStageID
      ∧ p.SenderActionDD ∧ p.StrictAdjustment
      ∧ Nonempty p.FeedbackStackelbergEquilibriumTop
      ∧ ¬ ∃ (E : p.FeedbackStackelbergEquilibriumTop) (sbar a b : ℝ),
          0 < sbar ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
          ∀ x₀ ∈ Set.Icc a b,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc a b)
            ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
            ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨p, -, -, -, h⟩ := sign_conditions_insufficient_over
    (probeParams (1/2) (1/2) (1/2) (1/2) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩)
    (probe_StrictAdjustment _ _ _ _ _ _ _)
  exact ⟨p, h⟩

/-- **The refutation is not a knife-edge.**  It holds at *every* adjustment
rate, *every* pair of discount factors admitted by the model class, and *every*
rally slope up to the Sender's own marginal sanction cost — a full-dimensional
region of the parameter space, not a tuned point.

Since round BH-5 (renovation item BH5.3, 2026-10-07) the instance of
`sign_conditions_insufficient_generalF` at `p₀ = probeParams …`, which drops the
affine transition and the parameter values; statement unchanged. -/
theorem sign_conditions_insufficient_on_parameter_range
    (δ βS βT ε : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβS : βS ∈ Set.Ico (0 : ℝ) 1) (hβT : βT ∈ Set.Ico (0 : ℝ) 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let p := probeParams δ βS βT ε hδ hβS hβT
    p.SenderStageIDStrict ∧ p.TargetStageIDStrict
      ∧ p.SenderStageID ∧ p.TargetStageID
      ∧ p.SenderActionDD ∧ p.StrictAdjustment
      ∧ Nonempty p.FeedbackStackelbergEquilibriumTop
      ∧ (∀ (E : p.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ),
          x₀ ∈ Set.Icc (0 : ℝ) 1 →
          ∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n = 0)
      ∧ ¬ ∃ (E : p.FeedbackStackelbergEquilibriumTop) (sbar a b : ℝ),
          0 < sbar ∧ 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
          ∀ x₀ ∈ Set.Icc a b,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc a b)
            ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
            ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨-, -, -, hAdj, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    sign_conditions_insufficient_generalF (probeParams δ βS βT ε hδ hβS hβT) ε hε0 hε1
  exact ⟨h1, h2, h3, h4, h5, hAdj.2 (probe_StrictAdjustment δ βS βT ε hδ hβS hβT), h6, h7, h8⟩

/-! ## Axiom hygiene (Rule 10) -/

#print axioms probe_no_perpetual_sanctions_counterexample
#print axioms sign_conditions_insufficient_on_parameter_range
#print axioms probe_margin_fails
#print axioms probe_margin_fails_at_every_positive_level
#print axioms probeEquilibrium
#print axioms probe_no_positive_floor
#print axioms probe_sanctionsF_eq_zero
#print axioms probe_senderFloorFlipSet_eq_empty
#print axioms probeSigma_pos_iff
#print axioms sign_conditions_insufficient_counterexample
#print axioms probeOverEquilibrium
#print axioms probeOver_pathF_tendsto_zero
#print axioms sign_conditions_insufficient_generalF
#print axioms sign_conditions_insufficient_over

end

end Examples
end Sanctions
