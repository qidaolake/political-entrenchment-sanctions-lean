/-
Sanctions/Examples/QuadBumpCertWitnessMS.lean

**The FIRST non-affine-transition instantiation of the MS-form certificate
`StandardComplianceLocalCoreCertificate_MS` (MS Step-1, 2026-07-03).**

Until this file, the general-transition headline
`standardCompliance_three_goals_local_MS_generalF` had a single
instantiation (`eeCertCertificateMS`) whose transition IS the affine law —
so "general in `F`" was witnessed only at the affine point. This file
instantiates the MS certificate at the SAME stage economy (`eecU_S`,
`eecU_T`, `eecσ`, `β_S = 1/2`, `β_T = 9/10`, `δ = 1/2`) with the genuinely
non-affine transition

  `F(x,s) = x/2 + s/2 + κ·(s − x)²·(1 − s)`,   `κ = 1/100`

(clip-wrapped off the unit square for the global monotonicity fields).
The quadratic bump `κ(s−x)²(1−s)` is a sanction-transience curvature:
intermediate sanctions overshoot the affine blend (maximal political
entrenchment response at mid-range sanction gaps), while at full sanction
`s = 1` the bump vanishes.

## Design note (Rule-11 record, 2026-07-03)

The naive quadratic `F = (1−δ)x + δs + κ(s−x)²` is NOT certifiable on this
route: its Bellman fixed points are non-affine, forcing a loose gain-ball
carrier (`Lipschitz K > gain g`), and on a loose carrier
`DynamicArgmaxUnique` (which quantifies over ALL compliance levels
`a : ℝ`) is refutable — a carrier member whose slope tracks the stage
curvature on a width-`ε` window (available whenever `K − g > 0`) produces
a flat-top objective at mid-band `a`, so the Sender argmax is non-unique.
The vanishing-at-corner bump avoids the wall structurally: `F(·,1)` is
EXACTLY the affine `(x+1)/2`, so the corner-pinned Bellman images are the
affine ones, the slope-pinned carriers (`K = g`) remain invariant, and
every carrier member yields an explicit CUBIC sender objective with both
top coefficients negative — strictly concave for every `a : ℝ`, hence
argmax-unique. The non-affine curvature is fully load-bearing off the
corner: the σ_dyn argmax discharge, the interval-dominance field, and the
Target combined chord all quantify over interior sanctions where
`F ≠ affineF`.

Numeric probe (2026-07-03, exact rationals): at `κ = 1/100` the sender
strict-monotonicity chord factor is `≥ 4/75` and the Target combined
chord margin is `≥ 163/1000`-scale; `κ ≤ 1/16` is needed for cubic
concavity, `κ < 1/6` for the transition monotonicity margins — `1/100`
clears everything.

Rule 3: NO new assumptions — an existence certificate over the existing
surface (Rule 3's explicit exception; Rule 5's witness case).
-/

import Sanctions.Examples.EECertWitnessMS
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Bellman.ChordInvariance

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The quadratic-bump transition -/

/-- **The non-affine transition**: affine blend plus a sanction-transience
bump that vanishes at full sanction. Clip-wrapped so the `Params`
monotonicity fields (which are global on `ℝ`) hold; on the unit square the
clips are the identity and `F(x,s) = x/2 + s/2 + (1/100)(s−x)²(1−s)`. -/
def quadBumpF (x s : ℝ) : ℝ :=
  1/2 * x + 1/2 * s
    + 1/100 * (Sanctions.clipS s - Sanctions.clipS x)^2 * (1 - Sanctions.clipS s)

/-- `clipS` collapse on `[0,1]`. -/
theorem clipS_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Sanctions.clipS t = t := by
  unfold Sanctions.clipS
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- On-square closed form: the clips are inactive. -/
theorem quadBumpF_sq {x s : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) :
    quadBumpF x s = 1/2 * x + 1/2 * s + 1/100 * (s - x)^2 * (1 - s) := by
  unfold quadBumpF
  rw [clipS_of_mem hx, clipS_of_mem hs]

/-- **At full sanction the bump vanishes GLOBALLY**: `F(x,1) = (x+1)/2`
for every `x : ℝ` (the `(1 − clipS 1)` factor is zero). -/
theorem quadBumpF_one (x : ℝ) : quadBumpF x 1 = (x + 1)/2 := by
  unfold quadBumpF
  rw [show Sanctions.clipS 1 = 1 from clipS_of_mem ⟨by norm_num, le_refl 1⟩]
  ring

/-- **`quadBumpF` is not the affine law, for any adjustment weight.**

Rule 11 / Rule 9B: this witness's defining property — being non-affine — is
machine-checked here rather than asserted in a docstring. Two points settle it.
`F 0 1 = 1/2` forces `δ = 1/2`, and then `F 0 (1/2) = 1/4 + 1/800` misses
`affineF (1/2) 0 (1/2) = 1/4` by the bump's `1/800`. -/
theorem quadBumpF_ne_affineF (δ : ℝ) : quadBumpF ≠ AbstractGame.affineF δ := by
  intro h
  have h1 : quadBumpF 0 1 = AbstractGame.affineF δ 0 1 := by rw [h]
  have h2 : quadBumpF 0 (1/2) = AbstractGame.affineF δ 0 (1/2) := by rw [h]
  rw [quadBumpF_one] at h1
  rw [quadBumpF_sq (by norm_num) (by norm_num)] at h2
  unfold AbstractGame.affineF at h1 h2
  norm_num at h1 h2
  linarith

/-- **The honest limitation, in Lean rather than in prose: this witness's
CORNER SECTION is affine.**

The certified recursion is `x_{t+1} = F(x_t, 1)` — the Sender sits at the
sanction corner, so the corner section is the only slice of the transition that
ever executes. `quadBumpF`'s bump carries the transience factor `(1 − s)`, which
vanishes there, so the *realised* path at this witness is the affine one at
`δ = 1/2` even though `F` itself is not affine (`quadBumpF_ne_affineF`).

This witness therefore exercises the **incentive** layer under a non-affine
transition, not the realised **dynamics**. The transition that bends the corner
section too is `wobbleF` (`Examples/WobbleCornerCertWitness.lean`), whose
`wobbleF_corner_not_affine` is the exact negation of the statement below. -/
theorem quadBumpF_corner_isAffine :
    ∃ a b : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, quadBumpF y 1 = a * y + b :=
  ⟨1/2, 1/2, fun y _ => by rw [quadBumpF_one]; ring⟩

/-- Feasibility on the square: `F(x,s) ∈ [0,1]`. -/
theorem quadBumpF_mem : ∀ x s : ℝ, x ∈ Set.Icc (0:ℝ) 1 →
    s ∈ Set.Icc (0:ℝ) 1 → quadBumpF x s ∈ Set.Icc (0:ℝ) 1 := by
  intro x s hx hs
  rw [quadBumpF_sq hx hs]
  constructor
  · nlinarith [sq_nonneg (s - x), hx.1, hs.1, hs.2,
      mul_nonneg (sq_nonneg (s - x)) (sub_nonneg.mpr hs.2)]
  · have hsq1 : (s - x)^2 ≤ 1 := by nlinarith [hx.1, hx.2, hs.1, hs.2]
    nlinarith [hx.2, hs.2, sub_nonneg.mpr hs.2,
      mul_le_of_le_one_left (sub_nonneg.mpr hs.2) hsq1]

theorem quadBumpF_continuous :
    Continuous (fun (xs : ℝ × ℝ) => quadBumpF xs.1 xs.2) := by
  unfold quadBumpF Sanctions.clipS
  fun_prop

/-- Global monotonicity in the inherited state: the bump's `x`-chord is
dominated by the affine term (`|∂bump/∂x| ≤ 2κ = 1/50 < 1/2`). -/
theorem quadBumpF_mono_x : ∀ s : ℝ, Monotone (fun x => quadBumpF x s) := by
  intro s x₁ x₂ hle
  unfold quadBumpF
  set c₁ := Sanctions.clipS x₁ with hc₁
  set c₂ := Sanctions.clipS x₂ with hc₂
  set cs := Sanctions.clipS s with hcs
  have hc₁m : c₁ ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem x₁
  have hc₂m : c₂ ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem x₂
  have hcsm : cs ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem s
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ x₂ - x₁ := by
    have := Sanctions.clipS_lipschitz_abs x₂ x₁
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ x₂ - x₁)] at this
    linarith
  simp only
  -- bump x-difference identity + bounded bracket:
  -- (cs−c₂)²(1−cs) − (cs−c₁)²(1−cs) = −(c₂−c₁)·(1−cs)(2cs−c₁−c₂),
  -- and (1−cs)(2cs−c₁−c₂) ≤ 2.
  have hkeyx : (cs - c₂)^2 * (1 - cs) - (cs - c₁)^2 * (1 - cs)
      = -((c₂ - c₁) * ((1 - cs) * (2*cs - c₁ - c₂))) := by ring
  have hup : (1 - cs) * (2*cs - c₁ - c₂) ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcsm.2)
        (show (0:ℝ) ≤ 2 - 2*cs + c₁ + c₂ by
          linarith [hcsm.2, hc₁m.1, hc₂m.1]),
      hcsm.1, hcsm.2]
  have hprod : (c₂ - c₁) * ((1 - cs) * (2*cs - c₁ - c₂)) ≤ (c₂ - c₁) * 2 :=
    mul_le_mul_of_nonneg_left hup (by linarith)
  linarith [hkeyx, hprod, hclip]

/-- Global monotonicity in the sanction: the bump's `s`-chord is dominated
by the affine term (`|∂bump/∂s| ≤ 3κ = 3/100 < 1/2`). -/
theorem quadBumpF_mono_s : ∀ x : ℝ, Monotone (fun s => quadBumpF x s) := by
  intro x s₁ s₂ hle
  unfold quadBumpF
  set c₁ := Sanctions.clipS s₁ with hc₁
  set c₂ := Sanctions.clipS s₂ with hc₂
  set cx := Sanctions.clipS x with hcx
  have hc₁m : c₁ ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem s₁
  have hc₂m : c₂ ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem s₂
  have hcxm : cx ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem x
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ s₂ - s₁ := by
    have := Sanctions.clipS_lipschitz_abs s₂ s₁
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ - s₁)] at this
    linarith
  simp only
  -- bump s-difference identity + bracket ≥ −3:
  -- (c₂−cx)²(1−c₂) − (c₁−cx)²(1−c₁) = (c₂−c₁)·[(1−c₂)(c₂+c₁−2cx) − (c₁−cx)²]
  have hkey : (c₂ - cx)^2 * (1 - c₂) - (c₁ - cx)^2 * (1 - c₁)
      = (c₂ - c₁) * ((1 - c₂) * (c₂ + c₁ - 2*cx) - (c₁ - cx)^2) := by ring
  have h1 : (0:ℝ) ≤ (1 - c₂) * (c₂ + c₁ - 2*cx + 2) :=
    mul_nonneg (by linarith [hc₂m.2])
      (by linarith [hc₁m.1, hc₂m.1, hcxm.2])
  have h2 : (c₁ - cx)^2 ≤ 1 := by
    nlinarith [hc₁m.1, hc₁m.2, hcxm.1, hcxm.2]
  have hbr : (-3 : ℝ) ≤ (1 - c₂) * (c₂ + c₁ - 2*cx) - (c₁ - cx)^2 := by
    nlinarith [h1, h2, hc₂m.1, hc₂m.2]
  have hprod : (c₂ - c₁) * (-3 : ℝ)
      ≤ (c₂ - c₁) * ((1 - c₂) * (c₂ + c₁ - 2*cx) - (c₁ - cx)^2) :=
    mul_le_mul_of_nonneg_left hbr (by linarith)
  linarith [hkey, hprod, hclip]

theorem quadBumpF_diag : ∀ x : ℝ, quadBumpF x x = x := by
  intro x
  unfold quadBumpF
  ring

/-- **The non-affine-transition certificate witness `Params`**: the
Eaton-Engers stage economy of `eeCertParams` with the quadratic-bump
transition in place of the affine law. -/
def qbParams : AbstractGame.Params :=
  { eeCertParams with
    F := quadBumpF
    F_continuous := quadBumpF_continuous
    F_mono_x := quadBumpF_mono_x
    F_mono_s := quadBumpF_mono_s
    F_diag := quadBumpF_diag }

/-- **`qbParams` has a continuous static Sender selector**: its selector is
`eeCertParams`'s, unchanged by the swap of transition, so the instance is
`eeCertParams`'s. A concrete member with the non-affine transition `quadBumpF`; the
selector does not read the transition. Round BJ5.1 (2026-10-07): selector continuity
left `Params` for the class `Params.StaticSelectorContinuous`, and the myopic block below
reads it here. -/
instance qbParams_staticSelectorContinuous : qbParams.StaticSelectorContinuous :=
  ⟨eeCertParams.σ_continuous⟩

@[simp] theorem qbParams_U_S : qbParams.U_S = eecU_S := rfl
@[simp] theorem qbParams_U_T : qbParams.U_T = eecU_T := rfl
@[simp] theorem qbParams_β_S : qbParams.β_S = 1/2 := rfl
@[simp] theorem qbParams_β_T : qbParams.β_T = 9/10 := rfl
@[simp] theorem qbParams_F : qbParams.F = quadBumpF := rfl

/-- **The witness transition is genuinely non-affine**: at the interior
sanction `s = 1/2` from state `x = 0` it strictly overshoots the affine
law (`F(0, 1/2) = 1/4 + 1/800 ≠ 1/4`).

Rule 5 (2026-08-19): this is now the `δ = 1/2` corollary of the parametric
`quadBumpF_ne_affineF`, which refutes the affine law at **every** weight rather
than only at the one this economy's `δ` slot happens to hold. The weaker
single-weight form left open that `F = affineF δ` for some other `δ`. -/
theorem qbParams_F_ne_affine : qbParams.F ≠ AbstractGame.affineF (1/2) :=
  quadBumpF_ne_affineF (1/2)

/-- The high-basin quadratic-bump transition satisfies strict adjustment.
Its bump is too small to reverse the sign of the affine half-gap. -/
theorem qbParams_strictAdjustment : qbParams.StrictAdjustment := by
  constructor
  · intro x s hx hs hsx
    rw [qbParams_F, quadBumpF_sq hx hs]
    have hd0 : 0 ≤ x - s := le_of_lt (sub_pos.mpr hsx)
    have hd1 : x - s ≤ 1 := by linarith [hx.2, hs.1]
    have hr0 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    have hr1 : 1 - s ≤ 1 := by linarith [hs.1]
    have hprod : (x - s) * (1 - s) ≤ 1 := by
      calc
        (x - s) * (1 - s) ≤ 1 * (1 - s) :=
          mul_le_mul_of_nonneg_right hd1 hr0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hr1 zero_le_one
        _ = 1 := by ring
    have hb := mul_le_mul_of_nonneg_left hprod hd0
    nlinarith
  · intro x s hx hs hxs
    rw [qbParams_F, quadBumpF_sq hx hs]
    nlinarith [mul_nonneg (sq_nonneg (s - x)) (sub_nonneg.mpr hs.2)]

/-- The `s`-chord of the transition on the square: the non-affine chord
factor stays within `[47/100, 53/100]` at `κ = 1/100` — the load-bearing
lower bound for the σ_dyn corner and the Target combined chord. -/
theorem qbParams_F_s_chord {x s₁ s₂ : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1) (hs₂ : s₂ ∈ Set.Icc (0:ℝ) 1)
    (hle : s₁ ≤ s₂) :
    47/100 * (s₂ - s₁) ≤ qbParams.F x s₂ - qbParams.F x s₁
      ∧ qbParams.F x s₂ - qbParams.F x s₁ ≤ 53/100 * (s₂ - s₁) := by
  rw [qbParams_F, quadBumpF_sq hx hs₁, quadBumpF_sq hx hs₂]
  -- bump s-chord identity, with the bracket bounded in [−3, 2]:
  have hkey : (s₂ - x)^2 * (1 - s₂) - (s₁ - x)^2 * (1 - s₁)
      = (s₂ - s₁) * ((1 - s₂) * (s₂ + s₁ - 2*x) - (s₁ - x)^2) := by ring
  have h1 : (0:ℝ) ≤ (1 - s₂) * (s₂ + s₁ - 2*x + 2) :=
    mul_nonneg (by linarith [hs₂.2]) (by linarith [hs₁.1, hs₂.1, hx.2])
  have h2 : (s₁ - x)^2 ≤ 1 := by nlinarith [hs₁.1, hs₁.2, hx.1, hx.2]
  have hbr_lo : (-3 : ℝ) ≤ (1 - s₂) * (s₂ + s₁ - 2*x) - (s₁ - x)^2 := by
    nlinarith [h1, h2, hs₂.1, hs₂.2]
  have hup : (1 - s₂) * (s₂ + s₁ - 2*x) ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs₂.2)
        (show (0:ℝ) ≤ 2 - s₂ - s₁ + 2*x by linarith [hs₁.2, hs₂.2, hx.1]),
      hs₂.1, hs₂.2]
  have hbr_hi : (1 - s₂) * (s₂ + s₁ - 2*x) - (s₁ - x)^2 ≤ 2 := by
    nlinarith [hup, sq_nonneg (s₁ - x)]
  have hΔ : (0:ℝ) ≤ s₂ - s₁ := sub_nonneg.mpr hle
  constructor
  · have := mul_le_mul_of_nonneg_left hbr_lo hΔ
    linarith [hkey, this]
  · have := mul_le_mul_of_nonneg_left hbr_hi hΔ
    linarith [hkey, this]

/-! ## 2. The dynamic Sender response is pinned at the corner `σ_dyn ≡ 1`

On the slope-`16/3` carrier the objective's `s`-chord factor is at least
`−6/5 + (8/3)·(47/100) = 4/75 > 0`: the forward-looking Sender remains
implacable under the non-affine transition. -/

/-- The Sender dynamic objective is strictly increasing in the sanction on
`[0,1]`, at every physical state and feasible compliance. -/
theorem qbCert_senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => qbParams.U_S x a s
        + qbParams.β_S * V_S (Sanctions.clipS' (qbParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : qbParams.F x s₁ ∈ Set.Icc (0:ℝ) 1 :=
    qbParams.F_mem x s₁ hx hs₁
  have hmem₂ : qbParams.F x s₂ ∈ Set.Icc (0:ℝ) 1 :=
    qbParams.F_mem x s₂ hx hs₂
  have hdiff : V_S (Sanctions.clipS' (qbParams.F x s₂))
      - V_S (Sanctions.clipS' (qbParams.F x s₁))
      = (16/3) * (qbParams.F x s₂ - qbParams.F x s₁) :=
    gainBall_clip_diff (by norm_num) (mem_eeCarrierS_num hV_S) hmem₁ hmem₂
  have hchord := (qbParams_F_s_chord hx hs₁ hs₂ (le_of_lt hlt)).1
  simp only [qbParams_U_S, eecU_S, qbParams_β_S]
  -- stage chord factor ≥ −6/5; continuation ≥ (8/3)(47/100)(s₂−s₁)
  have hstage : (0:ℝ) < (s₂ - s₁) * (-(s₁ + s₂)/2 + 2 - 11/5 * a + x
      + 8/3 * (47/100)) := by
    nlinarith [ha.2, hx.1, hs₁.2, hs₂.2, sub_pos.mpr hlt]
  nlinarith [hdiff, hchord, sub_pos.mpr hlt]

/-- **`σ_dyn` pinned at the corner `1`** under the non-affine transition. -/
theorem qbCert_σ_dyn_eq_one {V_S : Val} (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    qbParams.σ_dyn V_S x a = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn
    (qbCert_senderObj_strictMonoOn hV_S hx ha)

/-! ## 3. State-local uniqueness (Sender + Target)

The pinned carrier keeps `DynamicArgmaxUnique` dischargeable at the
non-affine transition: with `V_S` affine of slope `16/3`, the objective is
an explicit CUBIC whose `s³` and `s²` coefficients are both negative
(`−2/75` and `−1/2 + (2/75)(1+2x) ≤ −1/2 + 6/75`), hence strictly concave
on `[0,1]` for EVERY compliance level `a : ℝ`. -/

theorem qbCert_DAU_on_carrier {V_S : Val} (hV_S : V_S ∈ eeCarrierS) :
    qbParams.DynamicArgmaxUnique V_S := by
  apply qbParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have hQ : ∀ s ∈ Sanctions.I,
      qbParams.U_S x a s
          + qbParams.β_S * V_S (Sanctions.clipS' (qbParams.F x s))
        = -(2/75) * s ^ 3 + (-(1/2) + 2/75 * (1 + 2 * x)) * s ^ 2
          + (2 - 11/5 * a + x + 4/3 - 2/75 * (2*x + x^2)) * s
          + (a + 3 * x + 1/2 * c₀ + 4/3 * x + 2/75 * x^2) := by
    intro s hs
    have hmem : qbParams.F x s ∈ Set.Icc (0:ℝ) 1 := qbParams.F_mem x s hx hs
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hdiff := gainBall_clip_diff (show (0:ℝ) ≤ 16/3 by norm_num)
      (mem_eeCarrierS_num hV_S) h0 hmem
    simp only [qbParams_U_S, eecU_S, qbParams_β_S] at *
    rw [hc₀]
    have hFsq : qbParams.F x s
        = 1/2 * x + 1/2 * s + 1/100 * (s - x)^2 * (1 - s) := by
      rw [qbParams_F]; exact quadBumpF_sq hx hs
    rw [hFsq] at hdiff ⊢
    linear_combination (1/2) * hdiff
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p q hp hq hpq
  have hq_eq : q = 1 - p := by linarith
  subst hq_eq
  have hmid : p * s₁ + (1 - p) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  simp only [smul_eq_mul, hQ s₁ hs₁, hQ s₂ hs₂, hQ _ hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  -- cubic-midpoint gap identity: with A = −2/75, B = −1/2 + (2/75)(1+2x),
  -- p·f(s₁) + q·f(s₂) − f(ps₁+qs₂)
  --   = pq(s₁−s₂)²·(A((1+p)s₁+(1+q)s₂) + B) < 0.
  have hbr : (0:ℝ) < 2/75 * ((1 + p) * s₁ + (2 - p) * s₂)
      + (1/2 - 2/75 * (1 + 2 * x)) := by
    have h1 : (0:ℝ) ≤ (1 + p) * s₁ :=
      mul_nonneg (by linarith [hp.le]) hs₁.1
    have h2 : (0:ℝ) ≤ (2 - p) * s₂ :=
      mul_nonneg (by linarith [hq.le]) hs₂.1
    nlinarith [hx.2, h1, h2]
  have hgap : p * (-(2/75) * s₁ ^ 3 + (-(1/2) + 2/75 * (1 + 2 * x)) * s₁ ^ 2
        + (2 - 11/5 * a + x + 4/3 - 2/75 * (2*x + x^2)) * s₁
        + (a + 3 * x + 1/2 * c₀ + 4/3 * x + 2/75 * x^2))
      + (1 - p) * (-(2/75) * s₂ ^ 3 + (-(1/2) + 2/75 * (1 + 2 * x)) * s₂ ^ 2
        + (2 - 11/5 * a + x + 4/3 - 2/75 * (2*x + x^2)) * s₂
        + (a + 3 * x + 1/2 * c₀ + 4/3 * x + 2/75 * x^2))
      - (-(2/75) * (p * s₁ + (1 - p) * s₂) ^ 3
        + (-(1/2) + 2/75 * (1 + 2 * x)) * (p * s₁ + (1 - p) * s₂) ^ 2
        + (2 - 11/5 * a + x + 4/3 - 2/75 * (2*x + x^2))
            * (p * s₁ + (1 - p) * s₂)
        + (a + 3 * x + 1/2 * c₀ + 4/3 * x + 2/75 * x^2))
      = -(p * (1 - p) * (s₁ - s₂)^2
          * (2/75 * ((1 + p) * s₁ + (2 - p) * s₂)
            + (1/2 - 2/75 * (1 + 2 * x)))) := by ring
  nlinarith [hgap, mul_pos (mul_pos (mul_pos hp hq) hsq) hbr]

/-- **Joint Target integrand in closed form at physical states**: since
`F(x,1) = (x+1)/2` exactly (the bump vanishes at the corner), the closed
form is IDENTICAL to the affine witness. -/
theorem qbCert_joint_T_integrand_eq (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    qbParams.joint_T_integrand V_T V_S x a
      = -(1/10) * a + 41/10 * x - 3
        + 9/10 * V_T (Sanctions.clipS' ((x + 1)/2)) := by
  have hσ := qbCert_σ_dyn_eq_one hV_S hx ha
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [show qbParams.F x 1 = (x + 1)/2 from quadBumpF_one x]
  simp only [qbParams_U_T, eecU_T, qbParams_β_T]
  ring

theorem qbCert_TAU_on_carriers (V_T V_S : Val) (hV_S : V_S ∈ eeCarrierS) :
    qbParams.TargetArgmaxUnique V_T V_S := by
  apply WitnessKit.targetArgmaxUnique_of_strictAntiOn
  intro x hx a₁ ha₁ a₂ ha₂ hlt
  change qbParams.joint_T_integrand V_T V_S x a₂
      < qbParams.joint_T_integrand V_T V_S x a₁
  rw [qbCert_joint_T_integrand_eq V_T hV_S hx ha₁,
      qbCert_joint_T_integrand_eq V_T hV_S hx ha₂]
  linarith

theorem qbCert_zero_isMaxOn_joint (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn (fun a => qbParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [qbCert_joint_T_integrand_eq V_T hV_S hx ha,
      qbCert_joint_T_integrand_eq V_T hV_S hx
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  linarith [ha.1]

/-! ## 4. The asymmetric value class -/

/-- **The `ValueClass2` at the non-affine witness**: the SAME slope-pinned
carriers as the affine witness (the corner-pinned Bellman images are the
affine ones, so the pinned carriers remain the right home). -/
def qbCertClass : qbParams.ValueClass2 where
  carrier_T := eeCarrierT
  carrier_S := eeCarrierS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := valLipGainBall_isClosed _ _ _ _
  nonempty_T := eeCarrierT_nonempty
  nonempty_S := eeCarrierS_nonempty
  sender_unique_on := fun _ hV_S => (qbCert_DAU_on_carrier hV_S).toOnI
  target_unique_on := fun V_T _ V_S hV_S => qbCert_TAU_on_carriers V_T V_S hV_S

/-- **The derived leader policy is the defiance corner `α_on ≡ 0`**
(Rule 1: derived as the joint Bellman argmax, pinned by uniqueness). -/
theorem qbCert_α_on_eq_zero (V_T : qbCertClass.CarrierT)
    (V_S : qbCertClass.CarrierS) :
    qbCertClass.α_on V_T V_S = fun _ => (0:ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S
    (fun y => qbCert_zero_isMaxOn_joint V_T.val V_S.property y.property)

/-! ## 5. Bellman images in closed form

`F(·,1) = (·+1)/2` exactly, so both corner-pinned Bellman images are
BYTE-IDENTICAL to the affine witness's. -/

/-- **Target Bellman image in closed form.** -/
theorem qbCert_jointTarget_image (V_T : qbCertClass.CarrierT)
    (V_S : qbCertClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    qbParams.jointTarget_BCF_on_S V_T.val V_S.val
      (qbCertClass.sender_unique_on V_S.val V_S.property) y
      = 41/10 * y.val - 3
        + 9/10 * V_T.val (Sanctions.clipS' ((y.val + 1)/2)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (qbCertClass.sender_unique_on V_S.val V_S.property) y
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)
        (qbCert_zero_isMaxOn_joint V_T.val V_S.property y.property),
      qbCert_joint_T_integrand_eq V_T.val V_S.property y.property
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  ring

/-- **Sender Bellman image in closed form** at `α ≡ 0`. -/
theorem qbCert_bellmanS_image {W : Val} (hW : W ∈ eeCarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    qbParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3/2 + 4 * y.val
        + 1/2 * W (Sanctions.clipS' ((y.val + 1)/2)) := by
  have h1I : (1:ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmono := qbCert_senderObj_strictMonoOn hW y.property
    (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)
  have h1max : IsMaxOn
      (fun s => qbParams.U_S y.val 0 s
        + qbParams.β_S * W (Sanctions.clipS' (qbParams.F y.val s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1I hlt)
  rw [WitnessKit.bellmanS_image_of_isMaxOn (α := fun _ => (0:ℝ))
        continuous_const W y h1I h1max,
      show qbParams.F y.val 1 = (y.val + 1)/2 from quadBumpF_one _]
  simp only [qbParams_U_S, eecU_S, qbParams_β_S]
  ring

/-! ## 6. Carrier invariance and Schur rows.

Invariance goes through `mem_valLipGainBall_bellman_chord`: the genuinely
non-affine `quadBumpF` enters only via `CornerStateChord qbParams.F glo ghi`,
discharged from `quadBumpF_one` at the degenerate band `glo = ghi = 1/2`.
The Schur rows still reuse the affine-witness arithmetic, because the corner
images coincide with the affine ones. -/

theorem qbCertClass_IsInvariant : qbCertClass.IsInvariant := by
  intro V_T V_S
  constructor
  · -- Target image ∈ eeCarrierT.
    show qbParams.jointTarget_BCF_on_S V_T.val V_S.val
        (qbCertClass.sender_unique_on V_S.val V_S.property) ∈ eeCarrierT
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := eeCertParams.β_T)
      (glo := 1 - eeCertParams.δ) (ghi := 1 - eeCertParams.δ)
      (c₀ := eeStageT 0) (L_U := eeStageSlopeT) (g_U := eeStageSlopeT)
      (M_U := eeStageNormT) (stage := fun y => eeStageSlopeT * y)
      (F := qbParams.F)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      ?_ ?_ ?_
      (fun y hy => qbParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩) ?_
      eeCarrierT_closedForm_radius.2 le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_T.property ?_
    · intro z hz
      simp only [eeStageT_eq, eeStageSlopeT_eq, eeStageNormT_eq]
      rw [abs_le]
      constructor <;> nlinarith [hz.1, hz.2]
    · intro y₁ _ y₂ _
      rw [show eeStageSlopeT * y₂ - eeStageSlopeT * y₁
          = eeStageSlopeT * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ eeStageSlopeT)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y₁ y₂ _ _ hle
      simp only [qbParams_F, quadBumpF_one, eeCertParams_δ]
      constructor <;> linarith
    · intro y
      rw [qbCert_jointTarget_image V_T V_S y,
        show qbParams.F y.val 1 = (y.val + 1)/2 from quadBumpF_one _]
      simp only [eeStageT_eq, eeStageSlopeT_eq, eeCertParams_β_T]
      ring
  · -- Sender image ∈ eeCarrierS.
    show qbParams.bellmanS_BCF (qbCertClass.α_on V_T V_S)
        (qbCertClass.α_on_continuous V_T V_S) V_S.val ∈ eeCarrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (qbCert_α_on_eq_zero V_T V_S)
        (qbCertClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := eeCertParams.β_S)
      (glo := 1 - eeCertParams.δ) (ghi := 1 - eeCertParams.δ)
      (c₀ := eeStageS 0) (L_U := eeStageSlopeS) (g_U := eeStageSlopeS)
      (M_U := eeStageNormS) (stage := fun y => eeStageSlopeS * y)
      (F := qbParams.F)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      ?_ ?_ ?_
      (fun y hy => qbParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩) ?_
      eeCarrierS_closedForm_radius.2 le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_S.property ?_
    · intro z hz
      simp only [eeStageS_eq, eeStageSlopeS_eq, eeStageNormS_eq]
      rw [abs_le]
      constructor <;> nlinarith [hz.1, hz.2]
    · intro y₁ _ y₂ _
      rw [show eeStageSlopeS * y₂ - eeStageSlopeS * y₁
          = eeStageSlopeS * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ eeStageSlopeS)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y₁ y₂ _ _ hle
      simp only [qbParams_F, quadBumpF_one, eeCertParams_δ]
      constructor <;> linarith
    · intro y
      rw [qbCert_bellmanS_image V_S.property y,
        show qbParams.F y.val 1 = (y.val + 1)/2 from quadBumpF_one _]
      simp only [eeStageS_eq, eeStageSlopeS_eq, eeCertParams_β_S]
      ring

/-- **Target-row Schur bound** (`β_T = 9/10`, `L_TS = 0`). -/
theorem qbCertClass_hT_T_op
    (h_inv : qbCertClass.IsInvariant)
    (V V' : qbCertClass.CarrierT) (W W' : qbCertClass.CarrierS) :
    dist (qbCertClass.jointTargetOp_sub h_inv (V, W))
          (qbCertClass.jointTargetOp_sub h_inv (V', W'))
      ≤ (9/10 : ℝ) * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun y => 41/10 * y - 3) (φ := fun y => (y + 1)/2)
    qbCert_jointTarget_image V V' W W'

/-- **Sender-row Schur bound** (`β_S = 1/2`, `L_ST = 0`). -/
theorem qbCertClass_hT_S_op
    (h_inv : qbCertClass.IsInvariant)
    (V V' : qbCertClass.CarrierT) (W W' : qbCertClass.CarrierS) :
    dist (qbCertClass.jointSenderOp_sub h_inv (V, W))
          (qbCertClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    qbCert_α_on_eq_zero V V' W W'

/-! ## 7. The myopic block (transition-independent: the stage economy is
unchanged, and the myopic comparator optimizes the pure stage). The floor
lemma `eeCert_myopic_argmax_floor` applies definitionally (`qbParams.U_T`
and `qbParams.σ` reduce to the same `eecU_T`, `eecσ`). -/

/-- **The MS myopic ceiling at the canonical comparator** under the
non-affine transition (the argmax-floor route, verbatim). -/
theorem qbCert_hMyoCeiling_MS :
    ∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
      qbParams.σ x
          ((qbParams.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (1/10 : ℝ) (1/10)) := by
  intro x hx
  have hx' : x ∈ Set.Icc (1/10 : ℝ) 1 := by rwa [max_self] at hx
  have hxS : x ∈ Sanctions.S := ⟨le_trans (by norm_num) hx'.1, hx'.2⟩
  have hmem :=
    (qbParams.myopicFeedbackEquilibrium_canonical).α_mem x hxS
  have hopt :=
    (qbParams.myopicFeedbackEquilibrium_canonical).α_opt x hxS
  have hfloor := eeCert_myopic_argmax_floor hx' hmem hopt
  have hanti :
      eecσ x ((qbParams.myopicFeedbackEquilibrium_canonical).α x)
        ≤ eecσ x (min 1 ((5 * x + 10)/11)) := eecσ_antitone hfloor
  have hτx : eecσ x (min 1 ((5 * x + 10)/11)) ≤ x := by
    rcases le_total ((5 * x + 10)/11) 1 with h1 | h1
    · rw [min_eq_right h1,
        show eecσ x ((5 * x + 10)/11) = 0 from by
          unfold eecσ
          rw [show x + 2 - 11/5 * ((5 * x + 10)/11) = 0 by ring,
              min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]]
      linarith [hx'.1]
    · have hx5 : (1/5 : ℝ) ≤ x := by linarith
      rw [min_eq_left h1,
        show eecσ x 1 = x - 1/5 from by
          unfold eecσ
          rw [show x + 2 - 11/5 * 1 = x - 1/5 by ring,
              min_eq_right (by linarith [hx'.2] : x - 1/5 ≤ 1),
              max_eq_right (by linarith : (0:ℝ) ≤ x - 1/5)]]
      linarith
  calc qbParams.σ x
          ((qbParams.myopicFeedbackEquilibrium_canonical).α x)
      = eecσ x ((qbParams.myopicFeedbackEquilibrium_canonical).α x) :=
        rfl
    _ ≤ eecσ x (min 1 ((5 * x + 10)/11)) := hanti
    _ ≤ x := hτx
    _ ≤ max x (max (1/10 : ℝ) (1/10)) := le_max_left _ _

/-! ## 8. Stage fields and the Target combined chord -/

/-- Stage Target loss bound at the non-affine witness on the MS chord
domain `[max(x, 1/10), 1]`. Transition-free: the stage payoff `eecU_T` and
the derived Target policy `α_on ≡ 0` are shared with `eeCertParams`, so the
proof body is the `eeCert_h_stage_target_loss_MS` body verbatim. -/
theorem qbCert_h_stage_target_loss_MS
    (V_T : qbCertClass.CarrierT) (V_S : qbCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerLossSlopeOn
        (fun s => qbParams.U_T x (qbCertClass.α_on V_T V_S x) s)
        (Set.Icc (max x (max (1/10 : ℝ) (1/10))) 1) (299/100) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [qbCert_α_on_eq_zero V_T V_S, qbParams_U_T, eecU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 1/10 * x - 1/100 by linarith [hx.1])]

/-- **The Target combined chord at the non-affine transition, through the
general-`F` converter** `Target_combined_chord_of_decomposition_lowerChord`.
The transition enters only through the sanction lower chord, here at rate
`d_lo = 47/100` (strictly below the affine `1/2`, as
`sanctionLowerChord_le_of_cornerSectionTop` forces for any non-affine law
sharing this corner section). The margin is
`(9/10)·(82/11)·(47/100) = 3.153… > 299/100`. -/
theorem qbCert_h_target_combined :
    qbParams.TargetCombinedChordOn qbCertClass (1/10)
      (max (1/10 : ℝ) (1/10)) :=
  qbParams.Target_combined_chord_of_decomposition_lowerChord
    ⟨by norm_num, by norm_num⟩
    (dlo := 47/100)
    (by intro x s₁ s₂ hx hs₁ hs₂ hle; exact (qbParams_F_s_chord hx hs₁ hs₂ hle).1)
    (by norm_num)
    (by simp only [qbParams_β_T]; norm_num)
    qbCert_h_stage_target_loss_MS
    eeCert_hV_T_gain

/-- Stage Sender lower slope at the derived policy (transition-free). -/
theorem qbCert_h_stage_sender
    (V_T : qbCertClass.CarrierT) (V_S : qbCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerSlopeOn
        (fun s => qbParams.U_S x (qbCertClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (1/2 : ℝ))) (8/5) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hmax : max x (1/2 : ℝ) ≤ x + 2/5 := by
    rcases max_cases x (1/2 : ℝ) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;>
      linarith [hx.1]
  simp only [qbCert_α_on_eq_zero V_T V_S, qbParams_U_S, eecU_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 2 + x - (s₁ + s₂)/2 - 8/5 by
      linarith [hs₁.2, hs₂.2, hmax])]

/-- **Stage Sender strict monotonicity** on the MS choice interval. -/
theorem qbCert_h_stage_sender_strictMono
    (V_T : qbCertClass.CarrierT) (V_S : qbCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      StrictMonoOn
        (fun s => qbParams.U_S x (qbCertClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (max (1/10 : ℝ) (1/10)))) := by
  intro x hx s₁ hs₁ s₂ hs₂ hlt
  have hsub : max x (max (1/10 : ℝ) (1/10)) ≤ max x (1/2 : ℝ) :=
    max_le_max le_rfl (by rw [max_self]; norm_num)
  have h := qbCert_h_stage_sender V_T V_S x hx
    s₁ ⟨hs₁.1, le_trans hs₁.2 hsub⟩
    s₂ ⟨hs₂.1, le_trans hs₂.2 hsub⟩ (le_of_lt hlt)
  have hpos : (0:ℝ) < 8/5 * (s₂ - s₁) :=
    mul_pos (by norm_num) (sub_pos.mpr hlt)
  simp only at h ⊢
  linarith

/-- **Single crossing (trivial form)** at the non-affine witness: the
Sender dynamic objective is strictly increasing in the sanction at every
basin state (through the non-affine chord factor `≥ 47/100`). -/
theorem qbCert_hSC (V_T : qbCertClass.CarrierT) (V_S : qbCertClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max (1/10 : ℝ) (1/10)) 1)
      (fun s x => qbParams.senderDynObjective V_S.val x
        (qbCertClass.α_on V_T V_S x) s) := by
  apply WitnessKit.singleCrossingOn_of_strictMonoOn
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans (by norm_num) (le_trans (le_max_left _ _) ht.1), ht.2⟩
  intro s₁ hs₁ s₂ hs₂ hlt
  simp only [qbCert_α_on_eq_zero V_T V_S,
    AbstractGame.Params.senderDynObjective]
  exact qbCert_senderObj_strictMonoOn V_S.property ht'
    (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I) hs₁ hs₂ hlt

/-! ## 9. THE NON-AFFINE MS CERTIFICATE -/

/-- **The first non-affine-transition
`StandardComplianceLocalCoreCertificate_MS` instance.** Same stage
economy, carriers, Schur block, and pivots as the affine
`eeCertCertificateMS`; the transition-facing fields (`σ_dyn` corner,
interval dominance, Target combined chord, Bellman invariance) are
re-derived through the quadratic-bump chord factor `≥ 47/100`. -/
noncomputable def qbCertCertificateMS :
    qbParams.StandardComplianceLocalCoreCertificate_MS where
  D := qbCertClass
  h_inv := qbCertClass_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := qbCertClass_hT_T_op qbCertClass_IsInvariant
  hT_S_op := qbCertClass_hT_S_op qbCertClass_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 1/10
  xS := 1/10
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hpivot_mem := by rw [max_self]; exact ⟨by norm_num, by norm_num⟩
  h_stage_sender_strictMono := qbCert_h_stage_sender_strictMono
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (qbCert_hSC V_T V_S)
  h_target_combined := qbCert_h_target_combined
  hV_S_mono_carrier := fun V_S hV_S =>
    monotone_of_mem_valLipGainBall (by norm_num)
      (mem_eeCarrierS_num hV_S)
  hMyoCeiling := qbCert_hMyoCeiling_MS

/-! ## 10. The headline corollaries -/

/-- Strict ascent at full sanction for the quadratic-bump transition:
`F(x,1) = (x+1)/2 > x` on `[0,1)` — the general-`F` route's `hF_top`. -/
theorem quadBumpF_hF_top :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, x < qbParams.F x 1 := by
  intro x hx
  rw [qbParams_F, quadBumpF_one]
  linarith [hx.2]

/-- **The general-transition three-goals headline at the first non-affine
transition witness**: persistence floor on the general-`F` trajectory +
dominance over the canonical myopic comparator, with the state evolved by
`quadBumpF`, which is not `affineF δ` for any `δ` (`quadBumpF_ne_affineF`).

**Scope (2026-08-19).** What this row certifies is the **incentive** layer
under a non-affine transition, not the realised **dynamics**. The certified
recursion is `x_{t+1} = F(x_t, 1)`, and `quadBumpF`'s bump carries a transience
factor `(1 − s)` that vanishes at full sanction, so its corner section is affine
at `δ = 1/2` (`quadBumpF_corner_isAffine`) and the realised path here is the
affine one. The rows that bend the realised dynamics too are
`lbLow_generalF_three_goals` (`quadBumpLowF_corner_not_affine`) and
`wobbleEconMS_three_goals_full` (`wobbleEconF10_corner_not_affine`). -/
theorem qbCertMS_generalF_three_goals :
    ∃ E : qbParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT ∧ E.V_S ∈ eeCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1, ∀ n,
          max (1/10 : ℝ) (1/10)
            ≤ qbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
          qbParams.σ x
              ((qbParams.myopicFeedbackEquilibrium_canonical).α x)
            ≤ qbParams.dynamicTopRealizedRule E.V_S E.α x) := by
  obtain ⟨E, hVT, hVS, hG1, hG2, _hG3⟩ :=
    qbCertCertificateMS.three_goals_local_MS_generalF (p := qbParams)
      quadBumpF_hF_top
  exact ⟨E, hVT, hVS, fun x₀ hx₀ n => (hG1 x₀ hx₀).2.1 n, hG2⟩

/-! ## Within-carrier uniqueness (MS route, 2026-07-24) -/

/-- **First Schur-form MS certificate inhabitant** (non-vacuity of the
Round-A2-ported `StandardComplianceLocalCoreCertificateSchur_MS`), via
the row-sum ⇒ Schur bridge at the decoupled rows. -/
noncomputable def qbCertCertificateSchurMS :
    qbParams.StandardComplianceLocalCoreCertificateSchur_MS :=
  StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS
    qbParams qbCertCertificateMS

/-- **Witness within-carrier uniqueness at the quad-bump economy — the
first uniqueness result at a NON-AFFINE transition.** Any two
top-selector feedback Stackelberg equilibria with carrier values and
selector-coinciding policies agree in both value functions and the
policy, via the MS-form certificate packaging
(`StandardComplianceLocalCoreCertificate_MS.unique_in_carrier`: the MS
row sums imply the Schur package). Every quantitative input is
machine-discharged by `qbCertCertificateMS` (decoupled rows, diagonals
`9/10`, `1/2`); the carriers are the shared slope-pinned gain balls
`eeCarrierT` / `eeCarrierS`. -/
theorem qbCert_unique_in_carrier
    (E E' : qbParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ eeCarrierT) (hVS : E.V_S ∈ eeCarrierS)
    (hVT' : E'.V_T ∈ eeCarrierT) (hVS' : E'.V_S ∈ eeCarrierS)
    (hαE : E.α = qbCertClass.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = qbCertClass.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  qbCertCertificateMS.unique_in_carrier (p := qbParams)
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Witness within-carrier uniqueness at the quad-bump economy, with no
selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`qbCert_unique_in_carrier` without `hαE`, `hαE'`: any two top-selector feedback
Stackelberg equilibria whose values lie in the shared gain-ball carriers share
both value functions, and their policies agree at every feasible state. Every
quantitative input is discharged by `qbCertCertificateMS`, through the MS-form
`unique_in_carrier_of_mem`. The economy runs the non-affine `quadBumpF`; the
theorem it instantiates is general in `F`. -/
theorem qbCert_unique_in_carrier_of_mem
    (E E' : qbParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ eeCarrierT) (hVS : E.V_S ∈ eeCarrierS)
    (hVT' : E'.V_T ∈ eeCarrierT) (hVS' : E'.V_S ∈ eeCarrierS) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  qbCertCertificateMS.unique_in_carrier_of_mem (p := qbParams)
    E E' hVT hVS hVT' hVS'

/-! ## 12. The FULL certificate at the non-affine transition (2026-08-21)

Rule 9B asks a class that generalises a named special case to be inhabited
*outside* that case. `StandardComplianceLocalCoreCertificate` became general in
`F` on 2026-08-20b, and until now every one of its five instances discharged the
sanction chords by rewriting `F` to `affineF` — so the class was certified
inhabited and not certified more general than its affine predecessor.

This section closes that. Everything below is the affine `eeCertCertificate`
with the transition-facing fields re-derived through the quadratic-bump chord,
and it is possible only because `qbParams = { eeCertParams with F := quadBumpF }`
— identical stage economy, identical carriers, identical Schur block. The two
chord rates come from `qbParams_F_s_chord`:

  47/100 · (s₂ − s₁)  ≤  F x s₂ − F x s₁  ≤  53/100 · (s₂ − s₁)

so `dlo = 47/100` and `d = 53/100`, and `dlo < d` **strictly** — which is the
signature of non-affineness, since a lower and an upper chord at the same rate
would force `F = affineF` on the nose.

Both margins still close at the wider rates, with room:

  Sender  β_S·K_S·d   = (1/2)(16/3)(53/100) = 106/75   < 8/5 = m_S
  Target  c_T = 299/100 ≤ (9/10)(82/11)(47/100) = 17343/5500,  slack 449/2750

(The Target break-even rate is `3289/7380 ≈ 0.4457`; the bump delivers `0.47`.)

Since round BJ1.4 (2026-10-07) the certificate carries only the Sender leg
(`d` and its chord): the Target lower chord at `dlo = 47/100` and the Target
margin left it, as no certificate theorem read them. Both stay proved here
as standalone lemmas (`qbCert_hchord_lo`, which other witnesses use, and
`qbCert_h_stage_target_loss`); the MS certificate's combined chord
`qbCert_h_target_combined` above runs on the same chord factor.

**Direction of dependence.** This witness *inhabits* the general theorems; it
does not support them. `three_goals_local_uniform_starts_generalF` is proved
abstractly over `d` with no numerals and no `hF`, and its proof is
untouched by anything here. Per Rule 9A the only things a witness licenses are
existence and refutation of a universal — and the numerals below stay in
`Examples/`, where Rule 22 wants them. -/

/-- Target stage-loss slope at the certificate's own floor `s̄ = 1/2`.
Identical to `qbCert_h_stage_target_loss_MS` but on the narrower chord domain
the full certificate uses; the bound never inspects the domain. -/
theorem qbCert_h_stage_target_loss
    (V_T : qbCertClass.CarrierT) (V_S : qbCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      AbstractGame.Params.LowerLossSlopeOn
        (fun s => qbParams.U_T x (qbCertClass.α_on V_T V_S x) s)
        (Set.Icc (max x (1/2 : ℝ)) 1) (299/100) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [qbCert_α_on_eq_zero V_T V_S, qbParams_U_T, eecU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 1/10 * x - 1/100 by linarith [hx.1])]

/-- **The Target-leg sanction lower chord at `d_lo = 47/100`.** Raising the
sanction by `Δ` raises next period's political state by at least `0.47·Δ`,
uniformly on the unit square. Strictly below the affine `1/2`. -/
theorem qbCert_hchord_lo :
    Sanctions.TransitionChords.SanctionLowerChord qbParams.F (47/100) :=
  fun _ _ _ hx hs₁ hs₂ hle => (qbParams_F_s_chord hx hs₁ hs₂ hle).1

/-- **The Sender-leg range-restricted sanction upper chord at `d = 53/100`.**
On the Sender's own comparison range the same move raises the state by at most
`0.53·Δ`. Strictly above the affine `1/2`: the gap `53/100 − 47/100` is exactly
the room the bump occupies. -/
theorem qbCert_hF_chord :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x (1/2 : ℝ)),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x (1/2 : ℝ)), s₁ ≤ s₂ →
          |qbParams.F x s₂ - qbParams.F x s₁| ≤ (53/100) * (s₂ - s₁) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hx01 : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hb : max x (1/2 : ℝ) ≤ 1 := max_le hx.2 (by norm_num)
  have h1 : s₁ ∈ Set.Icc (0:ℝ) 1 := ⟨hs₁.1, le_trans hs₁.2 hb⟩
  have h2 : s₂ ∈ Set.Icc (0:ℝ) 1 := ⟨hs₂.1, le_trans hs₂.2 hb⟩
  obtain ⟨_, hhi⟩ := qbParams_F_s_chord hx01 h1 h2 hle
  rw [abs_of_nonneg (by nlinarith [sub_nonneg.mpr hle])]
  exact hhi

/-- Myopic ceiling at the certificate's floor `s̄ = 1/2`, weakened from the
MS ceiling at the pivot `1/10` (`max x (1/10) ≤ max x (1/2)`). -/
theorem qbCert_hMyoCeiling :
    ∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
      qbParams.σ x ((qbParams.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (1/2 : ℝ) := fun x hx =>
  le_trans (qbCert_hMyoCeiling_MS x hx) (max_le_max le_rfl (by norm_num))

/-- **The first NON-AFFINE `StandardComplianceLocalCoreCertificate`.**

Field for field the affine `eeCertCertificate`, at the same stage economy,
carriers, Schur rows, basin `[1/10, 1]` and sanction floor `s̄ = 1/2` — with the
transition replaced by `quadBumpF`, which `quadBumpF_ne_affineF` refutes as
affine at **every** weight, not merely at the one this economy's `δ` slot holds.

The two transition-facing fields are the only ones that change: `d` and its
chord (until round BJ1.4 also `dlo` and the Target lower chord). Everything else
transfers because `qbParams` differs from `eeCertParams` in `F` alone. -/
noncomputable def qbCertificate :
    qbParams.StandardComplianceLocalCoreCertificate where
  D := qbCertClass
  h_inv := qbCertClass_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := qbCertClass_hT_T_op qbCertClass_IsInvariant
  hT_S_op := qbCertClass_hT_S_op qbCertClass_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 1/10
  xS := 1/10
  sbar := 1/2
  mS := 8/5
  KS := 16/3
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  d := 53/100
  hF_chord := qbCert_hF_chord
  hS_margin := by simp only [qbParams_β_S]; norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := fun _ hV_S => (mem_eeCarrierS_num hV_S).2.1
  h_stage_sender_on := qbCert_h_stage_sender
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (qbCert_hSC V_T V_S)
  M := qbParams.myopicFeedbackEquilibrium_canonical
  hMyoCeiling := qbCert_hMyoCeiling

/-- **The Schur form of the same non-affine certificate**, through the row-sum
bridge. `ofRowSum` carries `d` and the Sender chord verbatim, so this closes
the identical Rule-9B gap on `StandardComplianceLocalCoreCertificateSchur` at
no extra cost. -/
noncomputable def qbCertificateSchur :
    qbParams.StandardComplianceLocalCoreCertificateSchur :=
  StandardComplianceLocalCoreCertificateSchur.ofRowSum qbParams qbCertificate

/-- **HEADLINE — all three goals at full conclusion strength over a genuinely
non-affine transition.**

The strongest statement the certificate supports, at an economy where
`quadBumpF_ne_affineF` refutes the affine law at every weight. For every start
in the joint basin `[1/10, 1]`: the equilibrium state path never leaves it;
realised sanctions never fall below the certificate's own floor `s̄ = 1/2`, nor
below the basin pivot; they are monotone in time; and at every date the Target's
action maximises its own joint dynamic objective, so the path is
equilibrium-generated at every period rather than only at date 0 (Rule 1).
Statewise on the basin the dynamic Sender's realised sanction weakly dominates
the myopic one. And after any temporary full-sanction shock from any admissible
start there is a finite entry horizon past which all of it holds forever.

The transition enters only through the Sender chord rate `d = 53/100` (the
Target-leg rate `d_lo = 47/100` is no longer read since round BJ1.4); `hAdj` is
`qbParams_strictAdjustment`, the paper's ordinal condition, derived here rather
than assumed.

**What this licenses (Rule 9A).** Existence, and the refutation of "the
certificate route needs an affine transition". It is not evidence that the
mechanism is generic, and the constants `47/100`, `53/100` are properties of
this economy, not of the theory. -/
theorem qbCert_three_goals_generalF :
    ∃ E : qbParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT
      ∧ E.V_S ∈ eeCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
          (∀ n, qbParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) ∧
          (∀ n, (1/2 : ℝ) ≤ qbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          (∀ n, max (1/10 : ℝ) (1/10)
                  ≤ qbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (qbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => qbParams.joint_T_top_integrand E.V_T E.V_S
                        (qbParams.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (qbParams.dynamicTopLockInPathF E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
           qbParams.σ x ((qbParams.myopicFeedbackEquilibrium_canonical).α x)
             ≤ qbParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, qbParams.dynamicTopLockInPathF E.V_S E.α
                    (qbParams.shockPathF x₀shock N) n
                    ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) ∧
            (∀ n, (1/2 : ℝ) ≤ qbParams.dynamicTopLockInSanctionsF E.V_S E.α
                            (qbParams.shockPathF x₀shock N) n) ∧
            (∀ n, max (1/10 : ℝ) (1/10)
                    ≤ qbParams.dynamicTopLockInSanctionsF E.V_S E.α
                        (qbParams.shockPathF x₀shock N) n)) :=
  qbCertificate.three_goals_local_uniform_starts_generalF qbParams
    qbParams_strictAdjustment

end -- noncomputable section

#print axioms qbCertCertificateMS
#print axioms qbCertCertificateSchurMS
#print axioms qbCert_unique_in_carrier
#print axioms qbCert_unique_in_carrier_of_mem
#print axioms qbCertMS_generalF_three_goals
#print axioms qbParams_F_ne_affine
#print axioms qbCertificate
#print axioms qbCertificateSchur
#print axioms qbCert_three_goals_generalF

end Examples

end Sanctions
#print axioms Sanctions.Examples.quadBumpF_ne_affineF
#print axioms Sanctions.Examples.quadBumpF_corner_isAffine
