/-
Sanctions/Examples/StageFlipCertWitness.lean

**The FIRST witness economy inhabiting the paper-canonical stage-flip
certificate route (2026-07-08).**

`StageFlipInfeasibility.lean` kernel-checked that the high-basin
`of_stage_flip` constructor family is hypothesis-infeasible at ALL five
pre-existing complete-certificate economies: every one is a loss-offset
design whose Target stage sanction slope is strictly negative
everywhere, so the decisive boundary sign `h1_T : 1 ∈ targetFlipSet s̄`
fails below the degenerate floor. This file closes that non-vacuity gap
with a tuned economy `sfParams` whose **Target stage payoff genuinely
flips**: above the derived pivot, rally dominates sanction pain, so
being sanctioned more is a stage *gain* for the incumbent — exactly the
`k·(x − x̄_T)`-form s-coefficient the infeasibility file's
"Consequences" paragraph prescribes.

## The economy (four-group flavor, Kaempfer–Lowenberg rally)

* Target stage payoff `U_T(x,a,s) = 3x + 5sx − sa − s` — the reduced
  form of a genuine four-group aggregate
  `(2+3s)(2x−a) + (1+s)(−x+2a) − s` (an export-competing / hardline
  bloc whose political weight grows with the sanction, against a
  cosmopolitan bloc): the rally term `5sx` flips the incumbent's stage
  sanction slope `5x − a − 1` from strictly negative at `x = 0`
  (`≤ −1` at every feasible action) to `≥ 3` at `x = 1`. The derived
  flip set is EXACTLY `[2/5, 1]`.
* Sender stage payoff
  `U_S(x,a,s) = x + a + s − 2·max(s − clip(x), 0) − s²/4` — a kinked
  "calibrated-pressure" payoff: sanctions below the state's own level
  are cheap pressure (rising branch, slope `≥ 1/2`), overshooting the
  state triggers backlash (falling branch, slope `≤ −1`). The stage
  argmax is exactly the kink `σ(x,a) = clip(x)` — action-independent,
  which is what lets the canonical (`Classical.choose`) myopic
  comparator satisfy the ceiling `σ(x, M.α x) = x ≤ max(x, x̄)`
  without ever being evaluated. The Sender floor flip set at wedge
  level `m_S = 1/2` is EXACTLY `[1/2, 1]`.
* Discounts `δ = 1/2, β_T = 1/2, β_S = 9/10`; affine transition
  `F = affineF(1/2)`. The Sender's continuation boost
  `β_S·δ·(dV_S/dx) = 27/11` dominates the worst stage down-slope
  `3/2`, pinning the forward-looking Sender at the corner
  `σ_dyn ≡ 1` (implacable); the joint Target integrand then has
  `a`-slope `−1 < 0`, pinning the derived leader policy at the
  defiance corner `α_on ≡ 0`.
* Carriers are **singletons** at the EXACT affine fixed points of the
  corner-collapsed Bellman operators — `V_T0(x) = (32x+10)/3`,
  `V_S0(x) = (120x+265)/22` — so invariance is an exact computation
  and all four Schur row constants are `0` (subsingleton carriers).

## The witness over a general transition (round BH-5, item BH5.2, 2026-10-07)

Nothing above needs the affine law on the whole square. `sfParamsF F …` is the
same economy over a caller-supplied transition `F` (with its four structural
`Params` obligations), and `sfParams` is the member `F := affineF (1/2)`, by
definition. Every lemma is proved for the family; the literal names are
one-line instances. The transition enters at three places only, and two chord
conditions from `Foundations/TransitionChords.lean` cover them:

* **a sanction lower chord `d ≥ 11/36`** (`SanctionLowerChord F d`) — the
  continuation boost `β_S·d·(60/11) ≥ 3/2` covers the worst stage down-slope,
  and the stage curvature `−s²/4` makes the margin strict, so `σ_dyn ≡ 1` on
  the singleton carrier. With the corner fixed, this pins the Sender, the
  Target's defiance corner and the single crossing;
* **the corner section `F(y, 1) = y/2 + 1/2`** (`CornerSectionTop F (1/2)`) —
  the corner-collapsed Bellman images then have the same exact affine fixed
  points, so the singleton carriers stay invariant, and full-sanction ascent
  `x < F(x, 1)` on `[0, 1)` (the route's `hF_top`) follows.

The stage-only inputs (the two complementarities, the flip sets and pivots,
the diagonal residual, the myopic ceiling) never read `F`. `sfqbParams` is the
member at the quadratic-bump transition `quadBumpF` (lower chord `47/100`,
corner section `y/2 + 1/2`), the route's first non-affine member
(`sfqbCertificate`, `sfqbCert_three_goals_generalF`).

## What is delivered

* `sfCertificate` — the certificate produced BY the stage-flip
  constructor `StandardComplianceLocalCoreCertificate_MS.of_stage_flip`
  with derived pivots `x̄_T = targetFlipPivot(1/2) = 2/5` and
  `x̂_S = senderFlipPivot(1/2, 1/2) = 1/2` (closed forms proved via
  the flip-set interval characterizations + `csInf_Icc`); basin
  `[max(2/5, 1/2), 1] = [1/2, 1]`.
* `sfCert_three_goals_generalF` — the general-transition three-goals
  headline `standardCompliance_three_goals_from_stage_flip_generalF`
  fired at the witness (`hF_top` from the corner section), with the
  derived basin rewritten to its closed form `[1/2, 1]`.
* `sfCert_three_goals_dominance` — the MS three-goals dominance
  corollary via `three_goals_local_MS_generalF` (Goal 2 is
  transition-independent, so the statement is unchanged).
* Flip-genuineness pair: `sfParams_one_mem_targetFlipSet` (the top
  state clears the boundary sign every previous witness failed) and
  `sfParams_zero_not_mem_targetFlipSet` (the bottom state does not —
  interiority of the derived tipping threshold).
* (Round BH-1, item BH1.8) `sfPersistenceCertificate` — the persistence
  certificate produced BY `StandardCompliancePersistenceCertificate.of_stage_flip`
  at the same derived pivots, and
  `sfCert_three_goals_min_drift_shock_of_preBasinAscent` — the minimum-drift
  three goals through that route, on the basin `[1/2, 1]`. Together they show
  that the persistence route is inhabited. The route reads none of the
  Target-side inputs above; at this witness they hold anyway, so the witness
  does not separate the persistence route from the MS route.
* (Round BH-5, item BH5.2) the `sfF…` family of all of the above over any
  transition with the corner section and a lower chord `≥ 11/36`, and its
  quadratic-bump member `sfqbParams`.

Rule 3: NO new assumptions — this is an existence certificate (Rule
3's explicit exception); every input is proved from the payoffs.
Rule 5: witness-specific content is the allowed existence-certificate
case; all scaffolding lemmas here are local to this witness.
Rule 1: `σ` is the stage argmax (proved), `σ_dyn ≡ 1` and `α_on ≡ 0`
are *derived* corner argmaxes (strict monotonicity / strict
antitonicity), and the myopic comparator is the canonical
`Classical.choose` stage argmax — no fixed strategies anywhere.
-/

import Sanctions.Examples.WitnessKit
import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Theory.Basin.StageFlipCertificate
import Sanctions.Theory.Certificates.StandardComplianceSchur

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params
open Sanctions.TransitionChords (SanctionLowerChord CornerSectionTop)

noncomputable section

/-! ## 1. The payoffs and the clip helper -/

/-- Clip into `[0, 1]` (the Sender's calibrated-pressure anchor). -/
def sfClip (x : ℝ) : ℝ := max 0 (min 1 x)

theorem sfClip_mem (x : ℝ) : sfClip x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem sfClip_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    sfClip x = x := by
  unfold sfClip
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem sfClip_continuous : Continuous sfClip := by
  unfold sfClip
  fun_prop

theorem sfClip_mono {x y : ℝ} (h : x ≤ y) : sfClip x ≤ sfClip y :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- Target stage payoff: four-group reduced form `3x + 5sx − sa − s`.
Rally coefficient `∂²U_T/∂s∂x = 5 > 0`; stage sanction slope
`5x − a − 1` flips sign at the state `x = (a+1)/5`. -/
def sfU_T (x a s : ℝ) : ℝ := 3 * x + 5 * s * x - s * a - s

/-- Sender stage payoff: kinked calibrated pressure
`x + a + s − 2·(s − clip(x))₊ − s²/4`. Rising branch slope `1 − s/2`,
falling branch slope `−1 − s/2`; stage argmax exactly at the kink. -/
def sfU_S (x a s : ℝ) : ℝ :=
  x + a + s - 2 * max (s - sfClip x) 0 - 1/4 * s ^ 2

/-- Static Sender response: the kink `σ(x, a) = clip(x)` —
state-riding, action-independent. -/
def sfσ (x _a : ℝ) : ℝ := sfClip x

theorem sfσ_mem (x a : ℝ) : sfσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  sfClip_mem x

theorem sfσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => sfσ xa.1 xa.2) := by
  simp only [sfσ]
  exact sfClip_continuous.comp continuous_fst

/-- **Rule-1 coupling (tent/kink argmax — local scaffolding).** The
kink `clip(x)` maximizes the concave tent-plus-parabola `U_S(x,a,·)`
on `[0,1]`: chords to the left of the kink rise at rate
`1 − (c+s)/4 ≥ 1/2`, chords to the right fall at rate
`1 + (s+c)/4 ≥ 1`. Holds for ALL real `(x, a)` (the kink
`c = clip(x)` is always feasible; `a` is additive). -/
theorem sfσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => sfU_S x a s) (Set.Icc (0 : ℝ) 1) (sfσ x a) := by
  rw [isMaxOn_iff]
  intro s hs
  have hc := sfClip_mem x
  change sfU_S x a s ≤ sfU_S x a (sfσ x a)
  simp only [sfU_S, sfσ]
  rw [sub_self, max_self]
  rcases le_total s (sfClip x) with hsc | hsc
  · rw [max_eq_right (by linarith : s - sfClip x ≤ 0)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsc)
      (show (0 : ℝ) ≤ 1 - (sfClip x + s)/4 by linarith [hc.2, hs.2])]
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ s - sfClip x)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsc)
      (show (0 : ℝ) ≤ 1 + (s + sfClip x)/4 by linarith [hc.1, hs.1])]

/-- **The stage-flip economy over any transition** (round BH-5, item BH5.2,
2026-10-07). The four-group Target, the kinked calibrated-pressure Sender, the
discounts and the inert rate `δ` of the witness, with the transition `F` and its
four structural `Params` obligations supplied by the caller (the pattern of
`toParamsF` in `Theory/Microfoundations/FourGroupPolity.lean`). Rule 22: general
in `F`; no field outside the transition block mentions it. The witness
`sfParams` is the member `F := affineF (1/2)`, by definition. -/
def sfParamsF (F : ℝ → ℝ → ℝ)
    (hFc : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hFx : ∀ s, Monotone (fun x => F x s))
    (hFs : ∀ x, Monotone (fun s => F x s))
    (hFd : ∀ x, F x x = x) : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1/2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 9/10
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := sfU_T
  U_S := sfU_S
  σ := sfσ
  σ_mem := sfσ_mem
  σ_isMaxOn_U_S := sfσ_isMaxOn
  U_T_continuous := by unfold sfU_T; fun_prop
  U_S_continuous := by unfold sfU_S sfClip; fun_prop
  F := F
  F_continuous := hFc
  F_mono_x := hFx
  F_mono_s := hFs
  F_diag := hFd

/-- **`sfParamsF` has a continuous static Sender selector.** General in `F`: the
transition is the caller's, and the selector does not read it. The proof is the one that
was the economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition
left `Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance sfParamsF_staticSelectorContinuous (F : ℝ → ℝ → ℝ)
    (hFc : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hFx : ∀ s, Monotone (fun x => F x s))
    (hFs : ∀ x, Monotone (fun s => F x s))
    (hFd : ∀ x, F x x = x) :
    (sfParamsF F hFc hFx hFs hFd).StaticSelectorContinuous where
  σ_continuous := sfσ_continuous

/-- **The stage-flip witness `Params`** (four-group Target, kinked
calibrated-pressure Sender, affine transition at `δ = 1/2`): the member
`F := affineF (1/2)` of `sfParamsF`, by definition. Rule 22: affine-restricted,
and marked so; every result is proved for the general-`F` family. -/
def sfParams : AbstractGame.Params :=
  sfParamsF (AbstractGame.affineF (1/2)) (AbstractGame.affineF_continuous _)
    (AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩)
    (AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩)
    (AbstractGame.affineF_diag _)

/-- **`sfParams` has a continuous static Sender selector** (`sfσ_continuous`), as every
member of `sfParamsF` does; instance search does not unfold `sfParams`, so the member
carries its own instance. Affine-restricted: the member with `affineF (1/2)`; the selector
does not read the transition. Round BJ5.1 (2026-10-07): selector continuity left `Params`
for the class `Params.StaticSelectorContinuous`. -/
instance sfParams_staticSelectorContinuous : sfParams.StaticSelectorContinuous :=
  ⟨sfσ_continuous⟩

@[simp] theorem sfParams_U_S : sfParams.U_S = sfU_S := rfl
@[simp] theorem sfParams_U_T : sfParams.U_T = sfU_T := rfl
@[simp] theorem sfParams_δ : sfParams.δ = 1/2 := rfl
@[simp] theorem sfParams_β_S : sfParams.β_S = 9/10 := rfl
@[simp] theorem sfParams_β_T : sfParams.β_T = 1/2 := rfl

/-- Transition closed form: `F(x, s) = (x + s)/2`. -/
theorem sfParams_F (x s : ℝ) : sfParams.F x s = (x + s) / 2 := by
  change AbstractGame.affineF (1/2) x s = (x + s) / 2
  unfold AbstractGame.affineF
  ring

/-- The affine law at rate `1/2` has the corner section `y ↦ y/2 + 1/2`.
Affine-restricted (a fact about `affineF (1/2)`). -/
theorem sf_affineF_cornerSectionTop :
    CornerSectionTop (AbstractGame.affineF (1/2)) (1/2) := by
  intro y _
  unfold AbstractGame.affineF
  ring

/-- The affine law at rate `1/2` has the sanction lower chord `1/2`, at
equality. Affine-restricted (a fact about `affineF (1/2)`). -/
theorem sf_affineF_lowerChord :
    SanctionLowerChord (AbstractGame.affineF (1/2)) (1/2) := by
  intro x s₁ s₂ _ _ _ _
  unfold AbstractGame.affineF
  linarith

section Family

variable {F : ℝ → ℝ → ℝ} {hFc : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2)}
  {hFx : ∀ s, Monotone (fun x => F x s)} {hFs : ∀ x, Monotone (fun s => F x s)}
  {hFd : ∀ x, F x x = x} {d : ℝ}

@[simp] theorem sfParamsF_U_S : (sfParamsF F hFc hFx hFs hFd).U_S = sfU_S := rfl
@[simp] theorem sfParamsF_U_T : (sfParamsF F hFc hFx hFs hFd).U_T = sfU_T := rfl
@[simp] theorem sfParamsF_β_S : (sfParamsF F hFc hFx hFs hFd).β_S = 9/10 := rfl
@[simp] theorem sfParamsF_β_T : (sfParamsF F hFc hFx hFs hFd).β_T = 1/2 := rfl
@[simp] theorem sfParamsF_F : (sfParamsF F hFc hFx hFs hFd).F = F := rfl

/-! ## 2. Positive-part chord bounds (local scaffolding)

Finite-difference control of the kink term `(s − c)₊`: its sanction
chords are squeezed into `[0, s₂ − s₁]`, and (for `hID_S`) the chord
bracket is antitone in the anchor `c`. -/

/-- The positive-part chord is non-negative. -/
theorem pospart_diff_nonneg {c s₁ s₂ : ℝ} (h : s₁ ≤ s₂) :
    0 ≤ max (s₂ - c) 0 - max (s₁ - c) 0 :=
  sub_nonneg.mpr (max_le_max (by linarith) le_rfl)

/-- The positive-part chord is at most the sanction increment. -/
theorem pospart_diff_le {c s₁ s₂ : ℝ} (h : s₁ ≤ s₂) :
    max (s₂ - c) 0 - max (s₁ - c) 0 ≤ s₂ - s₁ := by
  rcases le_total (s₂ - c) 0 with h2 | h2
  · rw [max_eq_right h2, max_eq_right (by linarith : s₁ - c ≤ 0)]
    linarith
  · rw [max_eq_left h2]
    rcases le_total (s₁ - c) 0 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; linarith

/-- **The kink chord bracket is antitone in the anchor**: raising the
anchor from `x₁` to `x₂` weakly lowers the chord
`(s₂ − ·)₊ − (s₁ − ·)₊`. This is the case analysis behind the Sender
stage increasing differences (`hID_S`). -/
theorem pospart_bracket_antitone {s₁ s₂ x₁ x₂ : ℝ}
    (hs : s₁ ≤ s₂) (hx : x₁ ≤ x₂) :
    max (s₂ - x₂) 0 - max (s₁ - x₂) 0
      ≤ max (s₂ - x₁) 0 - max (s₁ - x₁) 0 := by
  rcases le_total (s₂ - x₂) 0 with h22 | h22
  · rw [max_eq_right h22, max_eq_right (by linarith : s₁ - x₂ ≤ 0)]
    have := pospart_diff_nonneg (c := x₁) hs
    linarith
  · rw [max_eq_left h22]
    rcases le_total (s₁ - x₂) 0 with h12 | h12
    · rw [max_eq_right h12,
          max_eq_left (by linarith : (0 : ℝ) ≤ s₂ - x₁)]
      rcases le_total (s₁ - x₁) 0 with h11 | h11
      · rw [max_eq_right h11]; linarith
      · rw [max_eq_left h11]; linarith
    · rw [max_eq_left h12,
          max_eq_left (by linarith : (0 : ℝ) ≤ s₂ - x₁),
          max_eq_left (by linarith : (0 : ℝ) ≤ s₁ - x₁)]
      linarith

/-! ## 3. Singleton carriers at the exact affine fixed points -/

/-- Affine BCF `y ↦ c·y + d` on the compact state space `↥S`. -/
def sfAffineBCF (c d : ℝ) : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk
      (fun y : ↥(Sanctions.S : Set ℝ) => c * y.val + d) (by fun_prop))

@[simp] theorem sfAffineBCF_apply (c d : ℝ)
    (y : ↥(Sanctions.S : Set ℝ)) :
    sfAffineBCF c d y = c * y.val + d := rfl

theorem sfAffineBCF_clip {c d z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    sfAffineBCF c d (Sanctions.clipS' z) = c * z + d := by
  have hval : (Sanctions.clipS' z).val = z := by
    change Sanctions.clipS z = z
    unfold Sanctions.clipS
    rw [min_eq_right hz.2, max_eq_right hz.1]
  rw [sfAffineBCF_apply, hval]

/-- The Target carrier value `V_T0(x) = (32x + 10)/3` — the EXACT
fixed point of the corner-collapsed Target Bellman operator
`V(x) = U_T(x, 0, 1) + (1/2)·V((x+1)/2)`. -/
def sfV_T : Val := sfAffineBCF (32/3) (10/3)

/-- The Sender carrier value `V_S0(x) = (120x + 265)/22` — the EXACT
fixed point of the corner-collapsed Sender Bellman operator
`V(x) = U_S(x, 0, 1) + (9/10)·V((x+1)/2)`. -/
def sfV_S : Val := sfAffineBCF (60/11) (265/22)

@[simp] theorem sfV_T_apply (y : ↥(Sanctions.S : Set ℝ)) :
    sfV_T y = 32/3 * y.val + 10/3 := rfl

@[simp] theorem sfV_S_apply (y : ↥(Sanctions.S : Set ℝ)) :
    sfV_S y = 60/11 * y.val + 265/22 := rfl

theorem sfV_T_clip {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    sfV_T (Sanctions.clipS' z) = 32/3 * z + 10/3 :=
  sfAffineBCF_clip hz

theorem sfV_S_clip {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    sfV_S (Sanctions.clipS' z) = 60/11 * z + 265/22 :=
  sfAffineBCF_clip hz

/-- Target carrier: the singleton `{V_T0}` (EE exact-fixed-point
device — invariance becomes an exact computation). -/
def sfCarrierT : Set Val := {sfV_T}

/-- Sender carrier: the singleton `{V_S0}`. -/
def sfCarrierS : Set Val := {sfV_S}

/-! ## 4. The dynamic Sender response is pinned at the corner

On the singleton carrier the Sender dynamic objective is strictly increasing in
the sanction at every physical state and EVERY real compliance level. Over a
transition with sanction lower chord `d ≥ 11/36`, the continuation boost
`β_S·d·(60/11) ≥ 3/2` covers the kink drop plus the rising-branch slope
(worst stage down-slope `3/2`), and the curvature `−s²/4` leaves the strict
margin `(s₂ − s₁)(1/2 − (s₁ + s₂)/4) > 0`. At the affine law (`d = 1/2`) the
boost is `27/11`: the forward-looking Sender is implacable. -/

/-- The Sender dynamic objective is strictly increasing in the sanction on
`[0,1]`, at every physical state and all real `a`, over any transition with a
sanction lower chord `d ≥ 11/36`. General in `F`; the corner section is not
used. -/
theorem sfF_senderObj_strictMonoOn
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    {V_S : Val} (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    StrictMonoOn
      (fun s => (sfParamsF F hFc hFx hFs hFd).U_S x a s
        + (sfParamsF F hFc hFx hFs hFd).β_S
          * V_S (Sanctions.clipS' ((sfParamsF F hFc hFx hFs hFd).F x s)))
      Sanctions.I := by
  obtain rfl : V_S = sfV_S := Set.mem_singleton_iff.mp hV_S
  intro s₁ hs₁ s₂ hs₂ hlt
  have hm₁ : F x s₁ ∈ Set.Icc (0 : ℝ) 1 := (sfParamsF F hFc hFx hFs hFd).F_mem x s₁ hx hs₁
  have hm₂ : F x s₂ ∈ Set.Icc (0 : ℝ) 1 := (sfParamsF F hFc hFx hFs hFd).F_mem x s₂ hx hs₂
  have hBu := pospart_diff_le (c := sfClip x) hlt.le
  have hch : d * (s₂ - s₁) ≤ F x s₂ - F x s₁ := hlo hx hs₁ hs₂ hlt.le
  have hd' : 11/36 * (s₂ - s₁) ≤ d * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right hd (by linarith)
  simp only [sfParamsF_U_S, sfU_S, sfParamsF_β_S, sfParamsF_F]
  rw [sfV_S_clip hm₁, sfV_S_clip hm₂]
  nlinarith [hBu, hch, hd', mul_pos (sub_pos.mpr hlt)
    (show (0 : ℝ) < 1/2 - (s₁ + s₂)/4 by linarith [hs₁.2, hs₂.2])]

/-- The Sender dynamic objective is strictly increasing in the
sanction on `[0,1]`, at every physical state and all real `a`. -/
theorem sf_senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    StrictMonoOn
      (fun s => sfParams.U_S x a s
        + sfParams.β_S * V_S (Sanctions.clipS' (sfParams.F x s)))
      Sanctions.I :=
  sfF_senderObj_strictMonoOn sf_affineF_lowerChord (by norm_num) hV_S hx a

/-- **`σ_dyn` pinned at the corner `1`** for the carrier `V_S`, at every
physical state and every real compliance level, over any transition with a
sanction lower chord `d ≥ 11/36`. General in `F`. -/
theorem sfF_σ_dyn_eq_one (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    {V_S : Val} (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    (sfParamsF F hFc hFx hFs hFd).σ_dyn V_S x a = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn
    (sfF_senderObj_strictMonoOn hlo hd hV_S hx a)

/-- **`σ_dyn` pinned at the corner `1`** for the carrier `V_S`, at
every physical state and every real compliance level. -/
theorem sf_σ_dyn_eq_one {V_S : Val} (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    sfParams.σ_dyn V_S x a = 1 :=
  sfF_σ_dyn_eq_one sf_affineF_lowerChord (by norm_num) hV_S hx a

/-! ## 5. State-local uniqueness (Sender + Target) -/

/-- **State-local `DynamicArgmaxUnique` on the Sender carrier**, over any
transition with a sanction lower chord `d ≥ 11/36`: the dynamic objective is
strictly increasing in the sanction (for all real `a` — DAU's quantifier), so
any two maximizers coincide. General in `F`. -/
theorem sfF_DAU_on_carrier (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    {V_S : Val} (hV_S : V_S ∈ sfCarrierS) :
    (sfParamsF F hFc hFx hFs hFd).DynamicArgmaxUnique V_S :=
  fun _x hx a _s₁ _s₂ hs₁ hs₂ h₁ h₂ =>
    Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
      (sfF_senderObj_strictMonoOn hlo hd hV_S hx a) hs₁ hs₂ h₁ h₂

/-- **State-local `DynamicArgmaxUnique` on the Sender carrier**: the
dynamic objective is strictly increasing in the sanction (for all
real `a` — DAU's quantifier), so any two maximizers coincide. -/
theorem sf_DAU_on_carrier {V_S : Val} (hV_S : V_S ∈ sfCarrierS) :
    sfParams.DynamicArgmaxUnique V_S :=
  sfF_DAU_on_carrier sf_affineF_lowerChord (by norm_num) hV_S

/-- **Joint Target integrand at physical states, over any transition** with a
sanction lower chord `d ≥ 11/36`. With `σ_dyn ≡ 1`:
`8x − a − 1 + (1/2)·V_T(clip(F(x, 1)))` — strictly decreasing in compliance `a`
(the defiance corner). General in `F`; the successor is left as `F(x, 1)`, so
the corner section is not used. -/
theorem sfF_joint_T_integrand_eq (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : Val) {V_S : Val} (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    (sfParamsF F hFc hFx hFs hFd).joint_T_integrand V_T V_S x a
      = 8 * x - a - 1 + 1/2 * V_T (Sanctions.clipS' (F x 1)) := by
  have hσ : (sfParamsF F hFc hFx hFs hFd).σ_dyn V_S x a = 1 :=
    sfF_σ_dyn_eq_one hlo hd hV_S hx a
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  simp only [sfParamsF_U_T, sfU_T, sfParamsF_β_T, sfParamsF_F]
  ring

/-- **Joint Target integrand in closed form at physical states.**
With `σ_dyn ≡ 1`: `8x − a − 1 + (1/2)·V_T(clip((x+1)/2))` — strictly
decreasing in compliance `a` (the defiance corner). -/
theorem sf_joint_T_integrand_eq (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    sfParams.joint_T_integrand V_T V_S x a
      = 8 * x - a - 1
        + 1/2 * V_T (Sanctions.clipS' ((x + 1)/2)) := by
  have h : sfParams.joint_T_integrand V_T V_S x a
      = 8 * x - a - 1 + 1/2 * V_T (Sanctions.clipS' (sfParams.F x 1)) :=
    sfF_joint_T_integrand_eq sf_affineF_lowerChord (by norm_num) V_T hV_S hx a
  rw [h, sfParams_F]

/-- **State-local `TargetArgmaxUnique` on the carriers**, over any transition
with a sanction lower chord `d ≥ 11/36`: the joint integrand has `a`-slope
`−1 < 0`. General in `F`. -/
theorem sfF_TAU_on_carriers (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : Val) {V_S : Val} (hV_S : V_S ∈ sfCarrierS) :
    (sfParamsF F hFc hFx hFs hFd).TargetArgmaxUnique V_T V_S :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn
    fun x hx a₁ ha₁ a₂ ha₂ hlt => by
      simp only [sfF_joint_T_integrand_eq hlo hd V_T hV_S hx]
      linarith

/-- **State-local `TargetArgmaxUnique` on the carriers**: the joint
integrand has `a`-slope `−1 < 0`. -/
theorem sf_TAU_on_carriers (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ sfCarrierS) :
    sfParams.TargetArgmaxUnique V_T V_S :=
  sfF_TAU_on_carriers sf_affineF_lowerChord (by norm_num) V_T hV_S

/-- **Full defiance is the Target argmax** at every physical state, over any
transition with a sanction lower chord `d ≥ 11/36` (compliance buys nothing
from the implacable Sender and costs `1` per unit). General in `F`. -/
theorem sfF_zero_isMaxOn_joint (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : Val) {V_S : Val} (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => (sfParamsF F hFc hFx hFs hFd).joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [sfF_joint_T_integrand_eq hlo hd V_T hV_S hx a,
      sfF_joint_T_integrand_eq hlo hd V_T hV_S hx 0]
  linarith [ha.1]

/-- **Full defiance is the Target argmax** at every physical state
(compliance buys nothing from the implacable Sender and costs `1`
per unit). -/
theorem sf_zero_isMaxOn_joint (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ sfCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => sfParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 :=
  sfF_zero_isMaxOn_joint sf_affineF_lowerChord (by norm_num) V_T hV_S hx

/-! ## 6. The value class -/

variable (F hFc hFx hFs hFd) in
/-- **The `ValueClass2` over any transition** with a sanction lower chord
`d ≥ 11/36`: singleton exact-fixed-point carriers with state-local
Sender/Target argmax uniqueness. General in `F`. -/
def sfFClass (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    (sfParamsF F hFc hFx hFs hFd).ValueClass2 where
  carrier_T := sfCarrierT
  carrier_S := sfCarrierS
  isClosed_T := isClosed_singleton
  isClosed_S := isClosed_singleton
  nonempty_T := Set.singleton_nonempty _
  nonempty_S := Set.singleton_nonempty _
  sender_unique_on := fun _ hV_S => (sfF_DAU_on_carrier hlo hd hV_S).toOnI
  target_unique_on := fun V_T _ _ hV_S => sfF_TAU_on_carriers hlo hd V_T hV_S

/-- **The `ValueClass2` at the witness**: singleton exact-fixed-point
carriers with state-local Sender/Target argmax uniqueness. -/
def sfClass : sfParams.ValueClass2 :=
  sfFClass _ _ _ _ _ sf_affineF_lowerChord (by norm_num)

/-- **The derived leader policy is the defiance corner `α_on ≡ 0`**, over any
transition with a sanction lower chord `d ≥ 11/36`. Rule 1: this is the
*derived* argmax of the joint dynamic objective, pinned by state-local
uniqueness — nothing is assumed. General in `F`. -/
theorem sfF_α_on_eq_zero (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierT)
    (V_S : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierS) :
    (sfFClass F hFc hFx hFs hFd hlo hd).α_on V_T V_S = fun _ => (0 : ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    sfF_zero_isMaxOn_joint hlo hd V_T.val V_S.property y.property

/-- **The derived leader policy is the defiance corner `α_on ≡ 0`.**
Rule 1: this is the *derived* argmax of the joint dynamic objective,
pinned by state-local uniqueness — nothing is assumed. -/
theorem sf_α_on_eq_zero (V_T : sfClass.CarrierT)
    (V_S : sfClass.CarrierS) :
    sfClass.α_on V_T V_S = fun _ => (0 : ℝ) :=
  sfF_α_on_eq_zero sf_affineF_lowerChord (by norm_num) V_T V_S

/-! ## 7. Bellman images in closed form and EXACT invariance -/

/-- **Target Bellman image**, over any transition with a sanction lower chord
`d ≥ 11/36`: the sSup collapses at the defiance corner `a = 0`, where
`U_T(x, 0, 1) = 8x − 1`; the successor is left as `F(y, 1)`. General in `F`. -/
theorem sfF_jointTarget_image (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierT)
    (V_S : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    (sfParamsF F hFc hFx hFs hFd).jointTarget_BCF_on_S V_T.val V_S.val
      ((sfFClass F hFc hFx hFs hFd hlo hd).sender_unique_on V_S.val V_S.property) y
      = 8 * y.val - 1 + 1/2 * V_T.val (Sanctions.clipS' (F y.val 1)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        ((sfFClass F hFc hFx hFs hFd hlo hd).sender_unique_on V_S.val V_S.property) y
        (⟨le_refl 0, by norm_num⟩ : (0 : ℝ) ∈ Sanctions.I)
        (sfF_zero_isMaxOn_joint hlo hd V_T.val V_S.property y.property),
      sfF_joint_T_integrand_eq hlo hd V_T.val V_S.property y.property 0]
  ring

/-- **Target Bellman image in closed form**: the sSup collapses at
the defiance corner `a = 0`, where `U_T(x, 0, 1) = 8x − 1`. -/
theorem sf_jointTarget_image (V_T : sfClass.CarrierT)
    (V_S : sfClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    sfParams.jointTarget_BCF_on_S V_T.val V_S.val
      (sfClass.sender_unique_on V_S.val V_S.property) y
      = 8 * y.val - 1
        + 1/2 * V_T.val (Sanctions.clipS' ((y.val + 1)/2)) := by
  have h : sfParams.jointTarget_BCF_on_S V_T.val V_S.val
      (sfClass.sender_unique_on V_S.val V_S.property) y
      = 8 * y.val - 1 + 1/2 * V_T.val (Sanctions.clipS' (sfParams.F y.val 1)) :=
    sfF_jointTarget_image sf_affineF_lowerChord (by norm_num) V_T V_S y
  rw [h, sfParams_F]

/-- **Sender Bellman image** at the defiance policy `α ≡ 0`, over any
transition with a sanction lower chord `d ≥ 11/36`: the sSup collapses at the
corner `s = 1`, where `U_S(x, 0, 1) = 3x − 5/4`; the successor is left as
`F(y, 1)`. General in `F`. -/
theorem sfF_bellmanS_image (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    {W : Val} (hW : W ∈ sfCarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    (sfParamsF F hFc hFx hFs hFd).bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3 * y.val - 5/4 + 9/10 * W (Sanctions.clipS' (F y.val 1)) := by
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmono : StrictMonoOn
      (fun s => (sfParamsF F hFc hFx hFs hFd).U_S y.val 0 s
        + (sfParamsF F hFc hFx hFs hFd).β_S
          * W (Sanctions.clipS' ((sfParamsF F hFc hFx hFs hFd).F y.val s)))
      Sanctions.I :=
    sfF_senderObj_strictMonoOn hlo hd hW y.property 0
  have hmax : IsMaxOn
      (fun s => (sfParamsF F hFc hFx hFs hFd).U_S y.val 0 s
        + (sfParamsF F hFc hFx hFs hFd).β_S
          * W (Sanctions.clipS' ((sfParamsF F hFc hFx hFs hFd).F y.val s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1I hlt)
  rw [WitnessKit.bellmanS_image_of_isMaxOn (p := sfParamsF F hFc hFx hFs hFd)
      continuous_const W y h1I hmax]
  simp only [sfParamsF_U_S, sfU_S, sfParamsF_β_S, sfParamsF_F]
  rw [sfClip_of_mem ⟨y.property.1, y.property.2⟩,
      max_eq_left (by linarith [y.property.2] : (0 : ℝ) ≤ 1 - y.val)]
  ring

/-- **Sender Bellman image in closed form** at the defiance policy
`α ≡ 0`: the sSup collapses at the corner `s = 1`, where
`U_S(x, 0, 1) = 3x − 5/4`. -/
theorem sf_bellmanS_image {W : Val} (hW : W ∈ sfCarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    sfParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3 * y.val - 5/4
        + 9/10 * W (Sanctions.clipS' ((y.val + 1)/2)) := by
  have h : sfParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3 * y.val - 5/4 + 9/10 * W (Sanctions.clipS' (sfParams.F y.val 1)) :=
    sfF_bellmanS_image sf_affineF_lowerChord (by norm_num) hW y
  rw [h, sfParams_F]

/-- **EXACT carrier invariance over any transition with the corner section
`F(y, 1) = y/2 + 1/2`** and a sanction lower chord `d ≥ 11/36`: both
corner-collapsed Bellman images coincide with the singleton carrier values —
`8x − 1 + (1/2)·V_T0(x/2 + 1/2) = (32x+10)/3` and
`3x − 5/4 + (9/10)·V_S0(x/2 + 1/2) = (120x+265)/22`. General in `F`; this is
where the corner section is read. -/
theorem sfFClass_IsInvariant (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    (sfFClass F hFc hFx hFs hFd hlo hd).IsInvariant := by
  intro V_T V_S
  have hVT : V_T.val = sfV_T := Set.mem_singleton_iff.mp V_T.property
  have hVS : V_S.val = sfV_S := Set.mem_singleton_iff.mp V_S.property
  refine ⟨?_, ?_⟩
  · -- Target image = V_T0 exactly.
    change (sfParamsF F hFc hFx hFs hFd).jointTarget_BCF_on_S V_T.val V_S.val
        ((sfFClass F hFc hFx hFs hFd hlo hd).sender_unique_on V_S.val V_S.property)
      = sfV_T
    ext y
    have hm : 1/2 * y.val + (1 - 1/2) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
    rw [sfF_jointTarget_image hlo hd V_T V_S y, hcorner y.val y.property, hVT,
        sfV_T_clip hm, sfV_T_apply]
    ring
  · -- Sender image = V_S0 exactly (at the derived α_on ≡ 0).
    change (sfParamsF F hFc hFx hFs hFd).bellmanS_BCF
        ((sfFClass F hFc hFx hFs hFd hlo hd).α_on V_T V_S)
        ((sfFClass F hFc hFx hFs hFd hlo hd).α_on_continuous V_T V_S) V_S.val
      ∈ sfCarrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (sfF_α_on_eq_zero hlo hd V_T V_S)
        ((sfFClass F hFc hFx hFs hFd hlo hd).α_on_continuous V_T V_S)
        continuous_const V_S.val]
    change (sfParamsF F hFc hFx hFs hFd).bellmanS_BCF (fun _ => (0 : ℝ))
        continuous_const V_S.val = sfV_S
    ext y
    have hm : 1/2 * y.val + (1 - 1/2) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
    rw [sfF_bellmanS_image hlo hd V_S.property y, hcorner y.val y.property, hVS,
        sfV_S_clip hm, sfV_S_apply]
    ring

/-- **EXACT carrier invariance**: both corner-collapsed Bellman
images coincide with the singleton carrier values — `V_T0` and
`V_S0` are exact fixed points (`8x − 1 + (1/2)·V_T0((x+1)/2) =
(32x+10)/3` and `3x − 5/4 + (9/10)·V_S0((x+1)/2) = (120x+265)/22`). -/
theorem sfClass_IsInvariant : sfClass.IsInvariant :=
  sfFClass_IsInvariant sf_affineF_cornerSectionTop sf_affineF_lowerChord (by norm_num)

/-! ## 8. Schur rows: all four constants are zero

The carriers are singletons, so the carrier subtypes are
subsingletons: any two operator images are equal and every row bound
holds with constants `(β_T, L_TS) = (β_S, L_ST) = (0, 0)`. -/

/-- **Target Schur row with zero constants** (subsingleton carriers), over any
transition with a sanction lower chord `d ≥ 11/36`. General in `F`. -/
theorem sfFClass_hT_T_op (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (h_inv : (sfFClass F hFc hFx hFs hFd hlo hd).IsInvariant)
    (V V' : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierT)
    (W W' : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierS) :
    dist ((sfFClass F hFc hFx hFs hFd hlo hd).jointTargetOp_sub h_inv (V, W))
          ((sfFClass F hFc hFx hFs hFd hlo hd).jointTargetOp_sub h_inv (V', W'))
      ≤ (0 : ℝ) * dist V V' + 0 * dist W W' := by
  have hV : V = V' := Subtype.ext
    ((Set.mem_singleton_iff.mp V.property).trans
      (Set.mem_singleton_iff.mp V'.property).symm)
  have hW : W = W' := Subtype.ext
    ((Set.mem_singleton_iff.mp W.property).trans
      (Set.mem_singleton_iff.mp W'.property).symm)
  subst hV
  subst hW
  simp

/-- **Target Schur row with zero constants** (subsingleton carriers). -/
theorem sfClass_hT_T_op (h_inv : sfClass.IsInvariant)
    (V V' : sfClass.CarrierT) (W W' : sfClass.CarrierS) :
    dist (sfClass.jointTargetOp_sub h_inv (V, W))
          (sfClass.jointTargetOp_sub h_inv (V', W'))
      ≤ (0 : ℝ) * dist V V' + 0 * dist W W' :=
  sfFClass_hT_T_op sf_affineF_lowerChord (by norm_num) h_inv V V' W W'

/-- **Sender Schur row with zero constants** (subsingleton carriers), over any
transition with a sanction lower chord `d ≥ 11/36`. General in `F`. -/
theorem sfFClass_hT_S_op (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (h_inv : (sfFClass F hFc hFx hFs hFd hlo hd).IsInvariant)
    (V V' : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierT)
    (W W' : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierS) :
    dist ((sfFClass F hFc hFx hFs hFd hlo hd).jointSenderOp_sub h_inv (V, W))
          ((sfFClass F hFc hFx hFs hFd hlo hd).jointSenderOp_sub h_inv (V', W'))
      ≤ (0 : ℝ) * dist V V' + 0 * dist W W' := by
  have hV : V = V' := Subtype.ext
    ((Set.mem_singleton_iff.mp V.property).trans
      (Set.mem_singleton_iff.mp V'.property).symm)
  have hW : W = W' := Subtype.ext
    ((Set.mem_singleton_iff.mp W.property).trans
      (Set.mem_singleton_iff.mp W'.property).symm)
  subst hV
  subst hW
  simp

/-- **Sender Schur row with zero constants** (subsingleton carriers). -/
theorem sfClass_hT_S_op (h_inv : sfClass.IsInvariant)
    (V V' : sfClass.CarrierT) (W W' : sfClass.CarrierS) :
    dist (sfClass.jointSenderOp_sub h_inv (V, W))
          (sfClass.jointSenderOp_sub h_inv (V', W'))
      ≤ (0 : ℝ) * dist V V' + 0 * dist W W' :=
  sfFClass_hT_S_op sf_affineF_lowerChord (by norm_num) h_inv V V' W W'

/-! ## 9. The two stage-complementarity primitives

Stage-only facts: they read `U_T` and `U_S`, never `F`, so each holds at every
member of the family (general in `F`, no chord hypothesis). -/

/-- **Target stage complementarity holds** at every member: the rally
cross-partial is `∂²U_T/∂s∂x = 5 > 0` (exact chord identity
`ΔΔ = 5(s₂−s₁)(x₂−x₁)`). General in `F`. -/
theorem sfF_targetStageID : (sfParamsF F hFc hFx hFs hFd).TargetStageID := by
  intro a _ s s' x x' _ _ hss _ _ hxx
  simp only [sfParamsF_U_T, sfU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hss) (sub_nonneg.mpr hxx)]

/-- **Target stage complementarity holds**: the rally cross-partial
is `∂²U_T/∂s∂x = 5 > 0` (exact chord identity
`ΔΔ = 5(s₂−s₁)(x₂−x₁)`). -/
theorem sfParams_targetStageID : sfParams.TargetStageID :=
  sfF_targetStageID

/-- **Sender stage complementarity holds** at every member: the only
`x`-dependence of the sanction chord is through the kink anchor `clip(x)`, whose
chord bracket is antitone in the anchor (`pospart_bracket_antitone`). General
in `F`. -/
theorem sfF_senderStageID : (sfParamsF F hFc hFx hFs hFd).SenderStageID := by
  intro a _ s s' x x' _ _ hss _ _ hxx
  have hbr := pospart_bracket_antitone hss (sfClip_mono hxx)
  simp only [sfParamsF_U_S, sfU_S]
  linarith

/-- **Sender stage complementarity holds**: the only `x`-dependence
of the sanction chord is through the kink anchor `clip(x)`, whose
chord bracket is antitone in the anchor
(`pospart_bracket_antitone`). -/
theorem sfParams_senderStageID : sfParams.SenderStageID :=
  sfF_senderStageID

/-! ## 10. The flip sets in closed form and the boundary signs

THE POINT of this witness: the Target boundary sign `h1_T` — refuted
at all five previous certificate economies
(`StageFlipInfeasibility.lean`) — HOLDS here, and the flip sets are
exactly the intervals `[2/5, 1]` (Target) and `[1/2, 1]` (Sender
floor at wedge level `1/2`). Stage-only, hence general in `F`. -/

/-- **Flip genuineness, top state**, at every member: at `x = 1` every
sanction chord in `[1/2, 1]` weakly raises the Target stage payoff, uniformly
over feasible actions (slope `4 − a ≥ 3 > 0`). General in `F`. -/
theorem sfF_one_mem_targetFlipSet :
    (1 : ℝ) ∈ (sfParamsF F hFc hFx hFs hFd).targetFlipSet (1/2) := by
  refine ⟨⟨zero_le_one, le_refl 1⟩,
    fun a ha s₁ _ s₂ _ hs => ?_⟩
  simp only [sfParamsF_U_T, sfU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs)
    (show (0 : ℝ) ≤ 4 - a by linarith [ha.2])]

/-- **Flip genuineness, top state (the sign every previous witness
failed).** At `x = 1` every sanction chord in `[1/2, 1]` weakly
raises the Target stage payoff, uniformly over feasible actions:
the chord slope is `4 − a ≥ 3 > 0`. Rally dominates pain at the top
state — the boundary sign `h1_T` of the stage-flip constructor. -/
theorem sfParams_one_mem_targetFlipSet :
    (1 : ℝ) ∈ sfParams.targetFlipSet (1/2) :=
  sfF_one_mem_targetFlipSet

/-- **The Target flip set is exactly `[2/5, 1]`** at every member. General in
`F`. -/
theorem sfF_targetFlipSet_eq :
    (sfParamsF F hFc hFx hFs hFd).targetFlipSet (1/2) = Set.Icc (2/5 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxI, hx⟩
    refine ⟨?_, hxI.2⟩
    have h := hx 1 ⟨zero_le_one, le_refl 1⟩
      (1/2) ⟨le_refl _, by norm_num⟩ 1 ⟨by norm_num, le_refl 1⟩
      (by norm_num)
    simp only [sfParamsF_U_T, sfU_T] at h
    linarith
  · rintro x ⟨hx1, hx2⟩
    refine ⟨⟨by linarith, hx2⟩, fun a ha s₁ _ s₂ _ hs => ?_⟩
    simp only [sfParamsF_U_T, sfU_T]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs)
      (show (0 : ℝ) ≤ 5 * x - a - 1 by linarith [ha.2])]

/-- **The Target flip set is exactly `[2/5, 1]`.** The chord identity
is `(s₂−s₁)(5x − a − 1)`; the worst feasible action is `a = 1`, so
the uniform flip condition is `5x − 2 ≥ 0`. -/
theorem sfParams_targetFlipSet_eq :
    sfParams.targetFlipSet (1/2) = Set.Icc (2/5 : ℝ) 1 :=
  sfF_targetFlipSet_eq

/-- **Flip genuineness, bottom state (interiority)**, at every member. General
in `F`. -/
theorem sfF_zero_not_mem_targetFlipSet :
    (0 : ℝ) ∉ (sfParamsF F hFc hFx hFs hFd).targetFlipSet (1/2) := by
  rw [sfF_targetFlipSet_eq]
  intro h
  exact absurd h.1 (by norm_num)

/-- **Flip genuineness, bottom state (interiority).** At `x = 0` the
Target stage sanction slope is `−1 − a ≤ −1` at EVERY feasible
action: the flip has genuinely not happened at the dovish corner —
the `h0_T` boundary sign that pins the derived pivot interior. -/
theorem sfParams_zero_not_mem_targetFlipSet :
    (0 : ℝ) ∉ sfParams.targetFlipSet (1/2) :=
  sfF_zero_not_mem_targetFlipSet

/-- **The derived Target tipping threshold is `2/5`** at every member. General
in `F`. -/
theorem sfF_targetFlipPivot :
    (sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2) = 2/5 := by
  change sInf ((sfParamsF F hFc hFx hFs hFd).targetFlipSet (1/2)) = 2/5
  rw [sfF_targetFlipSet_eq]
  exact csInf_Icc (by norm_num)

/-- **The derived Target tipping threshold is `2/5`.** -/
theorem sfParams_targetFlipPivot :
    sfParams.targetFlipPivot (1/2) = 2/5 :=
  sfF_targetFlipPivot

/-- **The Sender floor flip set at wedge level `1/2` is exactly `[1/2, 1]`** at
every member. General in `F`. -/
theorem sfF_senderFloorFlipSet_eq :
    (sfParamsF F hFc hFx hFs hFd).senderFloorFlipSet (1/2) (1/2)
      = Set.Icc (1/2 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxI, hx⟩
    refine ⟨?_, hxI.2⟩
    by_contra hcon
    rw [not_le] at hcon
    have h := hx 0 ⟨le_refl 0, zero_le_one⟩
      x ⟨hxI.1, hcon.le⟩ (1/2) ⟨by norm_num, le_refl _⟩ hcon.le
    simp only [sfParamsF_U_S, sfU_S] at h
    rw [sfClip_of_mem hxI, sub_self, max_self,
        max_eq_left (by linarith : (0 : ℝ) ≤ 1/2 - x)] at h
    nlinarith [h, mul_nonneg hxI.1
      (show (0 : ℝ) ≤ 1/2 - x by linarith)]
  · rintro x ⟨hx1, hx2⟩
    have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx1
    refine ⟨⟨hx0, hx2⟩, fun a _ s₁ hs₁ s₂ hs₂ hs => ?_⟩
    simp only [sfParamsF_U_S, sfU_S]
    rw [sfClip_of_mem ⟨hx0, hx2⟩,
        max_eq_right (by linarith [hs₂.2] : s₂ - x ≤ 0),
        max_eq_right (by linarith [hs₁.2] : s₁ - x ≤ 0)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs)
      (show (0 : ℝ) ≤ 1/2 - (s₁ + s₂)/4 by linarith [hs₁.2, hs₂.2])]

/-- **The Sender floor flip set at wedge level `1/2` is exactly
`[1/2, 1]`.** For `x ≥ 1/2` the floor range `[0, 1/2]` lies on the
rising branch (slope `1 − (s₁+s₂)/4 ≥ 3/4 ≥ 1/2`); for `x < 1/2` the
kink-crossing chord `[x, 1/2]` fails the wedge
(`x²/4 + (3/2)x − 13/16 < 0`). -/
theorem sfParams_senderFloorFlipSet_eq :
    sfParams.senderFloorFlipSet (1/2) (1/2) = Set.Icc (1/2 : ℝ) 1 :=
  sfF_senderFloorFlipSet_eq

/-- **The Sender boundary sign** `h1_S` at every member. General in `F`. -/
theorem sfF_one_mem_senderFloorFlipSet :
    (1 : ℝ) ∈ (sfParamsF F hFc hFx hFs hFd).senderFloorFlipSet (1/2) (1/2) := by
  rw [sfF_senderFloorFlipSet_eq]
  exact ⟨by norm_num, le_refl 1⟩

/-- **The Sender boundary sign** `h1_S`: the top state clears the
wedge level `1/2` on the whole floor range. -/
theorem sfParams_one_mem_senderFloorFlipSet :
    (1 : ℝ) ∈ sfParams.senderFloorFlipSet (1/2) (1/2) :=
  sfF_one_mem_senderFloorFlipSet

/-- **The derived Sender dynamic pivot is `1/2`** at every member. General in
`F`. -/
theorem sfF_senderFlipPivot :
    (sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2) = 1/2 := by
  change sInf ((sfParamsF F hFc hFx hFs hFd).senderFloorFlipSet (1/2) (1/2)) = 1/2
  rw [sfF_senderFloorFlipSet_eq]
  exact csInf_Icc (by norm_num)

/-- **The derived Sender dynamic pivot is `1/2`.** -/
theorem sfParams_senderFlipPivot :
    sfParams.senderFlipPivot (1/2) (1/2) = 1/2 :=
  sfF_senderFlipPivot

/-- Joint derived pivot `max(2/5, 1/2) = 1/2 < 1` at every member. General in
`F`. -/
theorem sfF_joint_pivot_lt_one :
    max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
      ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) < 1 := by
  rw [sfF_targetFlipPivot, sfF_senderFlipPivot]
  exact max_lt (by norm_num) (by norm_num)

/-- Joint derived pivot `max(2/5, 1/2) = 1/2 < 1` (basin
nondegeneracy input `hjoint_lt`). -/
theorem sfParams_joint_pivot_lt_one :
    max (sfParams.targetFlipPivot (1/2))
      (sfParams.senderFlipPivot (1/2) (1/2)) < 1 :=
  sfF_joint_pivot_lt_one

/-- Sanction floor below the joint pivot at every member. General in `F`. -/
theorem sfF_sbar_le_joint_pivot :
    (1/2 : ℝ) ≤ max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
      ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) := by
  rw [sfF_senderFlipPivot]
  exact le_max_right _ _

/-- Sanction floor below the joint pivot: `1/2 ≤ max(2/5, 1/2)`
(the MS ordering input `hsbar_le`, with equality). -/
theorem sfParams_sbar_le_joint_pivot :
    (1/2 : ℝ) ≤ max (sfParams.targetFlipPivot (1/2))
      (sfParams.senderFlipPivot (1/2) (1/2)) :=
  sfF_sbar_le_joint_pivot

/-! ## 11. The remaining constructor inputs -/

/-- **Above-floor diagonal residual (`h_diag_MS`)** over any transition with a
sanction lower chord `d ≥ 11/36` (the hypothesis only builds the class; the
residual reads `U_S` alone). General in `F`. -/
theorem sfF_h_diag_MS (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierT)
    (V_S : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierS) :
    ∀ x ∈ Set.Icc ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) (1 : ℝ),
      LowerSlopeOn (fun s => (sfParamsF F hFc hFx hFs hFd).U_S x
          ((sfFClass F hFc hFx hFs hFd hlo hd).α_on V_T V_S x) s)
        (Set.Icc (1/2 : ℝ)
          (max x (max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
            ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2))))) (1/2) := by
  simp only [sfF_targetFlipPivot, sfF_senderFlipPivot]
  intro x hx s₁ hs₁ s₂ hs₂ hs
  have hmax : max x (max (2/5 : ℝ) (1/2)) = x := by
    rw [max_eq_right (by norm_num : (2/5 : ℝ) ≤ 1/2)]
    exact max_eq_left hx.1
  rw [hmax] at hs₁ hs₂
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx.1
  have h1 : s₁ ≤ 1 := le_trans hs₁.2 hx.2
  have h2 : s₂ ≤ 1 := le_trans hs₂.2 hx.2
  simp only [sfParamsF_U_S, sfU_S]
  rw [sfClip_of_mem ⟨hx0, hx.2⟩,
      max_eq_right (by linarith [hs₂.2] : s₂ - x ≤ 0),
      max_eq_right (by linarith [hs₁.2] : s₁ - x ≤ 0)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs)
    (show (0 : ℝ) ≤ 1/2 - (s₁ + s₂)/4 by linarith)]

/-- **Above-floor diagonal residual (`h_diag_MS`)**: for basin states
`x ∈ [1/2, 1]`, the chords on `[1/2, max(x, joint pivot)] = [1/2, x]`
lie on the rising branch and clear the wedge slope `1/2` (binding
with equality in the trivial-chord limit at `x = 1`). Uniform in the
(derived) Target action — `U_S` is additive in `a`. -/
theorem sf_h_diag_MS (V_T : sfClass.CarrierT) (V_S : sfClass.CarrierS) :
    ∀ x ∈ Set.Icc (sfParams.senderFlipPivot (1/2) (1/2)) (1 : ℝ),
      LowerSlopeOn (fun s => sfParams.U_S x (sfClass.α_on V_T V_S x) s)
        (Set.Icc (1/2 : ℝ)
          (max x (max (sfParams.targetFlipPivot (1/2))
            (sfParams.senderFlipPivot (1/2) (1/2))))) (1/2) :=
  sfF_h_diag_MS sf_affineF_lowerChord (by norm_num) V_T V_S

/-- **Carrier `V_T` monotonicity on the basin range** (`g_T = 0` form) over any
transition with a sanction lower chord `d ≥ 11/36`. General in `F`. -/
theorem sfF_hV_T_mono_carrier (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    ∀ V_T ∈ (sfFClass F hFc hFx hFs hFd hlo hd).carrier_T,
      LowerSlopeOnValueOn V_T
        (Set.Icc ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2)) 1) 0 := by
  intro V_T hV_T
  obtain rfl : V_T = sfV_T := Set.mem_singleton_iff.mp hV_T
  intro y₁ y₂ _ _ hle
  have h := Subtype.coe_le_coe.mpr hle
  simp only [sfV_T_apply, zero_mul]
  linarith

/-- **Carrier `V_T` monotonicity on the basin range** (`g_T = 0`
form): `V_T0` has slope `32/3 > 0`. -/
theorem sf_hV_T_mono_carrier :
    ∀ V_T ∈ sfClass.carrier_T,
      LowerSlopeOnValueOn V_T
        (Set.Icc (sfParams.targetFlipPivot (1/2)) 1) 0 :=
  sfF_hV_T_mono_carrier sf_affineF_lowerChord (by norm_num)

/-- **Carrier `V_S` monotonicity** over any transition with a sanction lower
chord `d ≥ 11/36`: `V_S0` has slope `60/11 > 0`. General in `F`. -/
theorem sfF_hV_S_mono_carrier (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    ∀ V_S ∈ (sfFClass F hFc hFx hFs hFd hlo hd).carrier_S, Monotone V_S := by
  intro V_S hV_S
  obtain rfl : V_S = sfV_S := Set.mem_singleton_iff.mp hV_S
  intro y₁ y₂ hle
  have h := Subtype.coe_le_coe.mpr hle
  simp only [sfV_S_apply]
  linarith

/-- **Carrier `V_S` monotonicity**: `V_S0` has slope `60/11 > 0`. -/
theorem sf_hV_S_mono_carrier :
    ∀ V_S ∈ sfClass.carrier_S, Monotone V_S :=
  sfF_hV_S_mono_carrier sf_affineF_lowerChord (by norm_num)

/-- **Single crossing (trivial form)** over any transition with a sanction
lower chord `d ≥ 11/36`: the Sender dynamic objective is strictly increasing in
the sanction at every basin state, so both single-crossing consequents hold
unconditionally. General in `F`. -/
theorem sfF_hSC_on (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (V_T : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierT)
    (V_S : (sfFClass F hFc hFx hFs hFd hlo hd).CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn Sanctions.I
      (Set.Icc (max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
        ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2))) 1)
      (fun s x => (sfParamsF F hFc hFx hFs hFd).senderDynObjective V_S.val x
        ((sfFClass F hFc hFx hFs hFd hlo hd).α_on V_T V_S x) s) := by
  apply WitnessKit.singleCrossingOn_of_strictMonoOn
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := by
    have h1 : (0 : ℝ) ≤ max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
        ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) := by
      rw [sfF_senderFlipPivot]
      exact le_trans (by norm_num) (le_max_right _ _)
    linarith [ht.1]
  simp only [AbstractGame.Params.senderDynObjective]
  exact sfF_senderObj_strictMonoOn hlo hd V_S.property ⟨ht0, ht.2⟩ _

/-- **Single crossing (trivial form)**: the Sender dynamic objective
is strictly increasing in the sanction at every basin state, so both
single-crossing consequents hold unconditionally. -/
theorem sf_hSC_on (V_T : sfClass.CarrierT) (V_S : sfClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn Sanctions.I
      (Set.Icc (max (sfParams.targetFlipPivot (1/2))
        (sfParams.senderFlipPivot (1/2) (1/2))) 1)
      (fun s x => sfParams.senderDynObjective V_S.val x
        (sfClass.α_on V_T V_S x) s) :=
  sfF_hSC_on sf_affineF_lowerChord (by norm_num) V_T V_S

/-- **Myopic ceiling at the canonical comparator**, at every member: the static
Sender response is action-independent (`σ(x, a) = clip(x)`). General in `F`. -/
theorem sfF_hMyoCeiling :
    ∀ x ∈ Set.Icc (max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
        ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2))) 1,
      (sfParamsF F hFc hFx hFs hFd).σ x
          (((sfParamsF F hFc hFx hFs hFd).myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
            ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2))) := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := by
    have h1 : (0 : ℝ) ≤ max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
        ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) := by
      rw [sfF_senderFlipPivot]
      exact le_trans (by norm_num) (le_max_right _ _)
    linarith [hx.1]
  calc (sfParamsF F hFc hFx hFs hFd).σ x
        (((sfParamsF F hFc hFx hFs hFd).myopicFeedbackEquilibrium_canonical).α x)
      = sfClip x := rfl
    _ = x := sfClip_of_mem ⟨hx0, hx.2⟩
    _ ≤ max x (max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
          ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2))) := le_max_left _ _

/-- **Myopic ceiling at the canonical comparator.** The static
Sender response is action-independent (`σ(x, a) = clip(x)`), so the
canonical (`Classical.choose`) myopic Target policy is never
evaluated: `σ(x, M.α x) = x ≤ max(x, joint pivot)` on the basin. -/
theorem sf_hMyoCeiling :
    ∀ x ∈ Set.Icc (max (sfParams.targetFlipPivot (1/2))
        (sfParams.senderFlipPivot (1/2) (1/2))) 1,
      sfParams.σ x ((sfParams.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (sfParams.targetFlipPivot (1/2))
            (sfParams.senderFlipPivot (1/2) (1/2))) :=
  sfF_hMyoCeiling

/-- **Full-sanction ascent from the corner section**: `F(x, 1) = x/2 + 1/2 > x`
on `[0, 1)` — the route's `hF_top`. General in `F`; only the corner section is
read. -/
theorem sfF_hF_top (hcorner : CornerSectionTop F (1 / 2)) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, x < (sfParamsF F hFc hFx hFs hFd).F x 1 := by
  intro x hx
  rw [sfParamsF_F, hcorner x ⟨hx.1, hx.2.le⟩]
  linarith [hx.2]

/-! ## 12. THE CERTIFICATE — produced by the stage-flip constructor -/

variable (F hFc hFx hFs hFd) in
/-- **The stage-flip certificate over any transition with the corner section
`F(y, 1) = y/2 + 1/2` and a sanction lower chord `d ≥ 11/36`.** Produced BY the
constructor `StandardComplianceLocalCoreCertificate_MS.of_stage_flip` at the
derived pivots `x̄_T = 2/5`, `x̂_S = 1/2`, exactly as `sfCertificate`. General in
`F`: the two chord conditions are the only transition inputs. -/
noncomputable def sfFCertificate (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    (sfParamsF F hFc hFx hFs hFd).StandardComplianceLocalCoreCertificate_MS :=
  StandardComplianceLocalCoreCertificate_MS.of_stage_flip (sfParamsF F hFc hFx hFs hFd)
    (sfFClass F hFc hFx hFs hFd hlo hd) (sfFClass_IsInvariant hcorner hlo hd)
    (β_T := 0) (β_S := 0) (L_TS := 0) (L_ST := 0)
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
    (sfFClass_hT_T_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
    (sfFClass_hT_S_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
    (by norm_num) (by norm_num)
    (sbar := 1/2) (mS := 1/2)
    ⟨by norm_num, by norm_num⟩ (by norm_num)
    sfF_targetStageID sfF_senderStageID
    sfF_one_mem_targetFlipSet sfF_one_mem_senderFloorFlipSet
    sfF_zero_not_mem_targetFlipSet
    sfF_joint_pivot_lt_one sfF_sbar_le_joint_pivot
    (sfF_h_diag_MS hlo hd) (sfF_hV_T_mono_carrier hlo hd) (sfF_hV_S_mono_carrier hlo hd)
    (sfF_hSC_on hlo hd) sfF_hMyoCeiling

/-- **The first inhabitant of the stage-flip certificate route.**
Produced BY the constructor
`StandardComplianceLocalCoreCertificate_MS.of_stage_flip` (never
hand-built field-by-field): the basin pivots are the DERIVED tipping
thresholds `x̄_T = 2/5`, `x̂_S = 1/2` extracted from the two
stage-complementarity primitives plus boundary signs, and the entire
Target block is discharged by the constructor from flip-set
membership + carrier monotonicity. Closes the non-vacuity gap
recorded in `StageFlipInfeasibility.lean`. The member `F := affineF (1/2)` of
`sfFCertificate`. -/
noncomputable def sfCertificate :
    sfParams.StandardComplianceLocalCoreCertificate_MS :=
  sfFCertificate _ _ _ _ _ sf_affineF_cornerSectionTop sf_affineF_lowerChord (by norm_num)

/-! ## 13. Headline corollaries -/

/-- **The general-transition three goals from the stage flip, over any
transition with the corner section `F(y, 1) = y/2 + 1/2` and a sanction lower
chord `d ≥ 11/36`** — via `standardCompliance_three_goals_from_stage_flip_generalF`,
with the derived basin rewritten to its closed form `[1/2, 1]` and `hF_top`
from the corner section (`sfF_hF_top`). General in `F`. -/
theorem sfFCert_three_goals_generalF (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    ∃ E : (sfParamsF F hFc hFx hFs hFd).FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1) ∧
          (∀ n, (1/2 : ℝ)
                  ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone ((sfParamsF F hFc hFx hFs hFd).dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
           (sfParamsF F hFc hFx hFs hFd).σ x
              (((sfParamsF F hFc hFx hFs hFd).myopicFeedbackEquilibrium_canonical).α x)
              ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInPathF E.V_S E.α
                    ((sfParamsF F hFc hFx hFs hFd).shockPathF x₀shock N) n
                    ∈ Set.Icc (1/2 : ℝ) 1) ∧
            (∀ n, (1/2 : ℝ)
                    ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInSanctionsF E.V_S E.α
                        ((sfParamsF F hFc hFx hFs hFd).shockPathF x₀shock N) n)) := by
  have hpivot : max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
      ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) = (1/2 : ℝ) := by
    rw [sfF_targetFlipPivot, sfF_senderFlipPivot]
    exact max_eq_right (by norm_num)
  obtain ⟨E, hVT, hVS, hG1, hG2, hG3⟩ :=
    standardCompliance_three_goals_from_stage_flip_generalF (sfParamsF F hFc hFx hFs hFd)
      (sfFClass F hFc hFx hFs hFd hlo hd) (sfFClass_IsInvariant hcorner hlo hd)
      (β_T := 0) (β_S := 0) (L_TS := 0) (L_ST := 0)
      (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
      (sfFClass_hT_T_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
      (sfFClass_hT_S_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
      (by norm_num) (by norm_num)
      (sbar := 1/2) (mS := 1/2)
      ⟨by norm_num, by norm_num⟩ (by norm_num)
      sfF_targetStageID sfF_senderStageID
      sfF_one_mem_targetFlipSet sfF_one_mem_senderFloorFlipSet
      sfF_zero_not_mem_targetFlipSet
      sfF_joint_pivot_lt_one sfF_sbar_le_joint_pivot
      (sfF_h_diag_MS hlo hd) (sfF_hV_T_mono_carrier hlo hd) (sfF_hV_S_mono_carrier hlo hd)
      (sfF_hSC_on hlo hd) sfF_hMyoCeiling
      (sfF_hF_top hcorner)
  rw [hpivot] at hG1 hG2 hG3
  exact ⟨E, hVT, hVS, hG1, hG2, hG3⟩

/-- **The general-transition three-goals headline from the stage
flip, fired at the first flip-route witness** — via
`standardCompliance_three_goals_from_stage_flip_generalF`, with the
derived basin `[max(x̄_T, x̂_S), 1]` rewritten to its closed form
`[1/2, 1]` and the strict-ascent input `hF_top` discharged by the corner
section of the affine law. The member `F := affineF (1/2)` of
`sfFCert_three_goals_generalF`. -/
theorem sfCert_three_goals_generalF :
    ∃ E : sfParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, sfParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1) ∧
          (∀ n, (1/2 : ℝ)
                  ≤ sfParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (sfParams.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
           sfParams.σ x
              ((sfParams.myopicFeedbackEquilibrium_canonical).α x)
              ≤ sfParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, sfParams.dynamicTopLockInPathF E.V_S E.α
                    (sfParams.shockPathF x₀shock N) n
                    ∈ Set.Icc (1/2 : ℝ) 1) ∧
            (∀ n, (1/2 : ℝ)
                    ≤ sfParams.dynamicTopLockInSanctionsF E.V_S E.α
                        (sfParams.shockPathF x₀shock N) n)) :=
  sfFCert_three_goals_generalF sf_affineF_cornerSectionTop sf_affineF_lowerChord (by norm_num)

/-- **The MS three goals (dominance form) over any transition with the corner
section and a sanction lower chord `d ≥ 11/36`**, via
`three_goals_local_MS_generalF` on `sfFCertificate`. General in `F`. -/
theorem sfFCert_three_goals_dominance (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    ∃ E : (sfParamsF F hFc hFx hFs hFd).FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
          (sfParamsF F hFc hFx hFs hFd).σ x
              (((sfParamsF F hFc hFx hFs hFd).myopicFeedbackEquilibrium_canonical).α x)
            ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopRealizedRule E.V_S E.α x) := by
  have hpivot : max (sfFCertificate F hFc hFx hFs hFd hcorner hlo hd).xT
      (sfFCertificate F hFc hFx hFs hFd hcorner hlo hd).xS = (1/2 : ℝ) := by
    change max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
        ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) = (1/2 : ℝ)
    rw [sfF_targetFlipPivot, sfF_senderFlipPivot]
    exact max_eq_right (by norm_num)
  obtain ⟨E, hVT, hVS, _hG1, hG2, _hG3⟩ :=
    (sfFCertificate F hFc hFx hFs hFd hcorner hlo hd).three_goals_local_MS_generalF
      (p := sfParamsF F hFc hFx hFs hFd) (sfF_hF_top hcorner)
  rw [hpivot] at hG2
  exact ⟨E, hVT, hVS, hG2⟩

/-- **The MS three-goals (dominance form)** at the flip-route witness,
via the general-transition certificate headline
`three_goals_local_MS_generalF`: the canonical myopic realized sanction
is dominated by the forward-looking realized sanction on the whole
derived basin `[1/2, 1]`. Goal 2 names no trajectory, so the statement
is identical to the affine-routed version this replaces. -/
theorem sfCert_three_goals_dominance :
    ∃ E : sfParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
          sfParams.σ x
              ((sfParams.myopicFeedbackEquilibrium_canonical).α x)
            ≤ sfParams.dynamicTopRealizedRule E.V_S E.α x) :=
  sfFCert_three_goals_dominance sf_affineF_cornerSectionTop sf_affineF_lowerChord (by norm_num)

/-! ## 13b. The persistence route (round BH-1, item BH1.8) -/

variable (F hFc hFx hFs hFd) in
/-- **The stage-flip persistence certificate over any transition with the
corner section and a sanction lower chord `d ≥ 11/36`.** Produced BY
`StandardCompliancePersistenceCertificate.of_stage_flip` at the derived pivots,
as `sfPersistenceCertificate`. General in `F`. -/
noncomputable def sfFPersistenceCertificate (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    (sfParamsF F hFc hFx hFs hFd).StandardCompliancePersistenceCertificate :=
  StandardCompliancePersistenceCertificate.of_stage_flip (sfParamsF F hFc hFx hFs hFd)
    (sfFClass F hFc hFx hFs hFd hlo hd) (sfFClass_IsInvariant hcorner hlo hd)
    (β_T := 0) (β_S := 0) (L_TS := 0) (L_ST := 0)
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
    (sfFClass_hT_T_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
    (sfFClass_hT_S_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
    (by norm_num) (by norm_num)
    (sbar := 1/2) (mS := 1/2) (by norm_num)
    ((sfParamsF F hFc hFx hFs hFd).senderStageIDOn_of_senderStageID sfF_senderStageID
      (fun _ hs => ⟨hs.1, le_trans hs.2 (by norm_num)⟩))
    sfF_one_mem_senderFloorFlipSet
    (sfF_h_diag_MS hlo hd) (sfF_hV_S_mono_carrier hlo hd)
    (fun V_T V_S =>
      Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
        (sfF_hSC_on hlo hd V_T V_S))

/-- **The stage-flip persistence certificate at the witness.** Produced BY the
round BH-1 constructor `StandardCompliancePersistenceCertificate.of_stage_flip`
(never hand-built), at the same derived pivots `x̄_T = 2/5` and `x̂_S = 1/2`
as `sfCertificate`. The constructor reads none of the Target-side inputs that
`sfCertificate` needs (`sfParams_targetStageID`, the two Target boundary signs,
`sf_hV_T_mono_carrier`), nor `sfParams_joint_pivot_lt_one` and
`sfParams_sbar_le_joint_pivot`. It reads Sender stage complementarity on the
floor range `[0, 1/2]` only, and single crossing only through the interval
dominance it implies. Affine-restricted as an instance (the witness transition
is `affineF (1/2)`); the constructor itself is general in `F`, and the
general-`F` family is `sfFPersistenceCertificate`. -/
noncomputable def sfPersistenceCertificate :
    sfParams.StandardCompliancePersistenceCertificate :=
  sfFPersistenceCertificate _ _ _ _ _ sf_affineF_cornerSectionTop sf_affineF_lowerChord
    (by norm_num)

/-- **The minimum-drift three goals through the persistence route, over any
transition with the corner section `F(y, 1) = y/2 + 1/2` and a sanction lower
chord `d ≥ 11/36`**, on the basin `[1/2, 1]`; ascent at full sanction on
`[0, 1/2]` comes from the corner section (`sfF_hF_top`). General in `F`. -/
theorem sfFCert_three_goals_min_drift_shock_of_preBasinAscent
    (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    ∃ E : (sfParamsF F hFc hFx hFs hFd).FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1) ∧
          (∀ n, (1/2 : ℝ)
                  ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone ((sfParamsF F hFc hFx hFs hFd).dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
           (sfParamsF F hFc hFx hFs hFd).σ x
              (((sfParamsF F hFc hFx hFs hFd).myopicFeedbackEquilibrium_canonical).α x)
              ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (1/2),
            η = (sfParamsF F hFc hFx hFs hFd).fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (1/2), η ≤ (sfParamsF F hFc hFx hFs hFd).fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          (sfParamsF F hFc hFx hFs hFd).shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))
              ∈ Set.Icc (1/2 : ℝ) 1
          ∧ (∀ n, (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInPathF E.V_S E.α
                    ((sfParamsF F hFc hFx hFs hFd).shockPathF x₀shock
                      (Nat.ceil ((1/2 : ℝ) / η))) n
                    ∈ Set.Icc (1/2 : ℝ) 1)
          ∧ (∀ n, (1/2 : ℝ) ≤ (sfParamsF F hFc hFx hFs hFd).dynamicTopLockInSanctionsF
                    E.V_S E.α
                    ((sfParamsF F hFc hFx hFs hFd).shockPathF x₀shock
                      (Nat.ceil ((1/2 : ℝ) / η))) n) := by
  have hpivot : max ((sfParamsF F hFc hFx hFs hFd).targetFlipPivot (1/2))
      ((sfParamsF F hFc hFx hFs hFd).senderFlipPivot (1/2) (1/2)) = (1/2 : ℝ) := by
    rw [sfF_targetFlipPivot, sfF_senderFlipPivot]
    exact max_eq_right (by norm_num)
  have h :=
    standardCompliance_three_goals_from_stage_flip_generalF_min_drift_shock_of_preBasinAscent
      (sfParamsF F hFc hFx hFs hFd) (sfFClass F hFc hFx hFs hFd hlo hd)
      (sfFClass_IsInvariant hcorner hlo hd)
      (β_T := 0) (β_S := 0) (L_TS := 0) (L_ST := 0)
      (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
      (sfFClass_hT_T_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
      (sfFClass_hT_S_op hlo hd (sfFClass_IsInvariant hcorner hlo hd))
      (by norm_num) (by norm_num)
      (sbar := 1/2) (mS := 1/2) (by norm_num)
      ((sfParamsF F hFc hFx hFs hFd).senderStageIDOn_of_senderStageID sfF_senderStageID
        (fun _ hs => ⟨hs.1, le_trans hs.2 (by norm_num)⟩))
      sfF_one_mem_senderFloorFlipSet
      (sfF_h_diag_MS hlo hd) (sfF_hV_S_mono_carrier hlo hd)
      (fun V_T V_S =>
        Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
          (sfF_hSC_on hlo hd V_T V_S))
      sfF_hMyoCeiling
      ((sfParamsF F hFc hFx hFs hFd).preBasinAscent_of_hF_top
        (sfF_hF_top hcorner) sfF_joint_pivot_lt_one)
  rw [hpivot] at h
  exact h

/-- **The minimum-drift three goals at the flip-route witness, through the
persistence route.** Fires
`standardCompliance_three_goals_from_stage_flip_generalF_min_drift_shock_of_preBasinAscent`
at `sfParams`, with the derived basin rewritten to its closed form `[1/2, 1]`
and ascent at full sanction on `[0, 1/2]` discharged from the corner section of
the affine law (below the joint pivot `1/2 < 1`). There is an equilibrium in
the singleton carriers whose path persists in `[1/2, 1]` with non-decreasing
sanctions at least `1/2`, whose sanction dominates the myopic benchmark there,
and for which one full-sanction shock of `⌈(1/2)/η⌉` periods, with `η` the
attained minimum drift on `[0, 1/2]`, moves every initial state into the
basin. Non-vacuity of the persistence route; affine-restricted (the witness
transition is `affineF (1/2)`); the general-`F` family is
`sfFCert_three_goals_min_drift_shock_of_preBasinAscent`. -/
theorem sfCert_three_goals_min_drift_shock_of_preBasinAscent :
    ∃ E : sfParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, sfParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1) ∧
          (∀ n, (1/2 : ℝ)
                  ≤ sfParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (sfParams.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
           sfParams.σ x
              ((sfParams.myopicFeedbackEquilibrium_canonical).α x)
              ≤ sfParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (1/2), η = sfParams.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (1/2), η ≤ sfParams.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          sfParams.shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))
              ∈ Set.Icc (1/2 : ℝ) 1
          ∧ (∀ n, sfParams.dynamicTopLockInPathF E.V_S E.α
                    (sfParams.shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))) n
                    ∈ Set.Icc (1/2 : ℝ) 1)
          ∧ (∀ n, (1/2 : ℝ) ≤ sfParams.dynamicTopLockInSanctionsF E.V_S E.α
                    (sfParams.shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))) n) :=
  sfFCert_three_goals_min_drift_shock_of_preBasinAscent sf_affineF_cornerSectionTop
    sf_affineF_lowerChord (by norm_num)

/-! ## Within-carrier uniqueness (MS route, 2026-07-24) -/

variable (F hFc hFx hFs hFd) in
/-- Schur-form MS certificate over any transition with the corner section and a
sanction lower chord `d ≥ 11/36`, via the row-sum ⇒ Schur bridge. General in
`F`. -/
noncomputable def sfFCertificateSchurMS (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d) :
    (sfParamsF F hFc hFx hFs hFd).StandardComplianceLocalCoreCertificateSchur_MS :=
  StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS
    (sfParamsF F hFc hFx hFs hFd) (sfFCertificate F hFc hFx hFs hFd hcorner hlo hd)

/-- Schur-form MS certificate inhabitant at the stage-flip witness, via
the row-sum ⇒ Schur bridge (fully decoupled zero rows). -/
noncomputable def sfCertificateSchurMS :
    sfParams.StandardComplianceLocalCoreCertificateSchur_MS :=
  StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS
    sfParams sfCertificate

/-- **Within-carrier uniqueness over any transition with the corner section and
a sanction lower chord `d ≥ 11/36`**: two top-selector equilibria with carrier
values and selector-coinciding policies agree. General in `F`. -/
theorem sfFCert_unique_in_carrier (hcorner : CornerSectionTop F (1 / 2))
    (hlo : SanctionLowerChord F d) (hd : 11 / 36 ≤ d)
    (E E' : (sfParamsF F hFc hFx hFs hFd).FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ sfCarrierT) (hVS : E.V_S ∈ sfCarrierS)
    (hVT' : E'.V_T ∈ sfCarrierT) (hVS' : E'.V_S ∈ sfCarrierS)
    (hαE : E.α = (sfFClass F hFc hFx hFs hFd hlo hd).α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = (sfFClass F hFc hFx hFs hFd hlo hd).α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  (sfFCertificate F hFc hFx hFs hFd hcorner hlo hd).unique_in_carrier
    (p := sfParamsF F hFc hFx hFs hFd) E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Witness within-carrier uniqueness at the stage-flip economy.**
Any two top-selector feedback Stackelberg equilibria with carrier values
and selector-coinciding policies agree in both value functions and the
policy, via the MS-form certificate packaging
(`StandardComplianceLocalCoreCertificate_MS.unique_in_carrier`). At this
witness the carriers are singletons (`{sfV_T}` / `{sfV_S}`), so the
value-function clauses are pinned by carrier membership alone; the
policy clause is the substantive conjunct. All quantitative inputs are
machine-discharged by `sfCertificate` (fully decoupled zero rows). -/
theorem sfCert_unique_in_carrier
    (E E' : sfParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ sfCarrierT) (hVS : E.V_S ∈ sfCarrierS)
    (hVT' : E'.V_T ∈ sfCarrierT) (hVS' : E'.V_S ∈ sfCarrierS)
    (hαE : E.α = sfClass.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = sfClass.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  sfCertificate.unique_in_carrier (p := sfParams)
    E E' hVT hVS hVT' hVS' hαE hαE'

end Family

/-! ## 14. The quadratic-bump member (round BH-5, item BH5.2)

The route's first non-affine member: the transition
`F(x,s) = x/2 + s/2 + (1/100)(s − x)²(1 − s)` (`quadBumpF`), which is the
affine law at no rate (`quadBumpF_ne_affineF`). Its bump vanishes at full
sanction, so its corner section is `y/2 + 1/2`, and its sanction lower chord is
`47/100 ≥ 11/36` (`qbCert_hchord_lo`). Scope: the corner section is affine
(`quadBumpF_corner_isAffine`), so the realised corner recursion of this member
is the affine one; the non-affine curvature is load-bearing in the Sender's
incentive (`σ_dyn ≡ 1`, single crossing) at interior sanctions. -/

/-- **The stage-flip economy over the quadratic-bump transition**, the member
`F := quadBumpF` of `sfParamsF`. -/
def sfqbParams : AbstractGame.Params :=
  sfParamsF quadBumpF quadBumpF_continuous quadBumpF_mono_x quadBumpF_mono_s quadBumpF_diag

/-- **`sfqbParams` has a continuous static Sender selector** (`sfσ_continuous`), as every
member of `sfParamsF` does; the member carries its own instance because instance search
does not unfold `sfqbParams`. A concrete member with the non-affine transition
`quadBumpF`; the selector does not read the transition. Round BJ5.1 (2026-10-07). -/
instance sfqbParams_staticSelectorContinuous : sfqbParams.StaticSelectorContinuous :=
  ⟨sfσ_continuous⟩

/-- The member's transition is the affine law at no rate. -/
theorem sfqbParams_F_ne_affineF (δ : ℝ) : sfqbParams.F ≠ AbstractGame.affineF δ :=
  quadBumpF_ne_affineF δ

/-- The quadratic-bump transition has the corner section `y ↦ y/2 + 1/2` (its
bump vanishes at full sanction). -/
theorem sfqb_cornerSectionTop : CornerSectionTop quadBumpF (1/2) := by
  intro y _
  rw [quadBumpF_one]
  ring

/-- The quadratic-bump transition has the sanction lower chord `47/100`
(`qbCert_hchord_lo`). -/
theorem sfqb_lowerChord : SanctionLowerChord quadBumpF (47/100) :=
  qbCert_hchord_lo

/-- **The stage-flip certificate at the quadratic-bump member**: produced BY
`of_stage_flip` at the derived pivots `2/5` and `1/2`, over a transition that is
not affine at any rate. The member of `sfFCertificate` at `d = 47/100`. -/
noncomputable def sfqbCertificate :
    sfqbParams.StandardComplianceLocalCoreCertificate_MS :=
  sfFCertificate _ _ _ _ _ sfqb_cornerSectionTop sfqb_lowerChord (by norm_num)

/-- **The general-transition three goals from the stage flip at the
quadratic-bump member** (round BH-5, item BH5.2): an equilibrium in the
singleton carriers whose path persists in `[1/2, 1]` with non-decreasing
sanctions at least `1/2`, whose sanction dominates the myopic benchmark there,
and to which every initial state is moved by a finite full-sanction shock — at
a transition that is the affine law at no rate (`sfqbParams_F_ne_affineF`). The
member of `sfFCert_three_goals_generalF` at `d = 47/100`. -/
theorem sfqbCert_three_goals_generalF :
    ∃ E : sfqbParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ sfCarrierT
      ∧ E.V_S ∈ sfCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, sfqbParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1) ∧
          (∀ n, (1/2 : ℝ)
                  ≤ sfqbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (sfqbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (1/2 : ℝ) 1,
           sfqbParams.σ x
              ((sfqbParams.myopicFeedbackEquilibrium_canonical).α x)
              ≤ sfqbParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, sfqbParams.dynamicTopLockInPathF E.V_S E.α
                    (sfqbParams.shockPathF x₀shock N) n
                    ∈ Set.Icc (1/2 : ℝ) 1) ∧
            (∀ n, (1/2 : ℝ)
                    ≤ sfqbParams.dynamicTopLockInSanctionsF E.V_S E.α
                        (sfqbParams.shockPathF x₀shock N) n)) :=
  sfFCert_three_goals_generalF sfqb_cornerSectionTop sfqb_lowerChord (by norm_num)

end -- noncomputable section

#print axioms sfCertificate
#print axioms sfCert_three_goals_generalF
#print axioms sfCert_three_goals_dominance
#print axioms sfCert_unique_in_carrier
#print axioms sfCertificateSchurMS
#print axioms sfPersistenceCertificate
#print axioms sfCert_three_goals_min_drift_shock_of_preBasinAscent
#print axioms sfParams_one_mem_targetFlipSet
#print axioms sfParams_zero_not_mem_targetFlipSet
#print axioms sfFCertificate
#print axioms sfFCert_three_goals_generalF
#print axioms sfFCert_three_goals_min_drift_shock_of_preBasinAscent
#print axioms sfqbCertificate
#print axioms sfqbCert_three_goals_generalF

end Examples

end Sanctions
