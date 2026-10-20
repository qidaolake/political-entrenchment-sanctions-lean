/-
Sanctions/Examples/LowBasinCertWitness.lean

**The FIRST witness for Theorem 4 (low political absorbing basin) —
the Hassler-bistability mirror — with a genuinely non-affine transition
(2026-07-03).**

Until this file, the low-basin headlines
`standardCompliance_three_goals_local_low_basin(_generalF)` had ZERO
instantiations: no equilibrium had ever been exhibited satisfying the
dual one-sided thresholds, so the appeasement side of the bistable
picture was purely conditional. This file constructs a **dovish-Sender
economy** — sanctions strictly hurt the Sender's stage payoff at every
low-basin state, and hurt the Target at stage level too — whose
forward-looking equilibrium locks into **permanently zero sanctions**
from every low political start, with the state trajectory evolved by
the genuinely non-affine transition

  `F(x,s) = x/2 + s/2 + κ·(s − x)²·s`,   `κ = 1/100`

(the LOW-mirror of the R-NA bump: the sanction-transience curvature
vanishes at the realized corner `s = 0`, so the corner section
`F(·,0) = x/2` is exactly affine and the pinned anti-monotone carriers
remain Bellman-invariant, while every off-corner chord obligation —
the σ_dyn ≡ 0 corner, the dual thresholds, argmax uniqueness — engages
the curvature).

## The dovish-mirror economy (δ = 1/2, β_S = 1/2, β_T = 9/10)

* `U_S(x,a,s) = a − s²/2 − s(2 + x − a) − 3x` — the Sender's stage
  payoff strictly DECREASES in the sanction (chord factor ≤ −1 on the
  cube): no domestic constituency demands harshness at low hardliner
  influence. Static response: `σ(x,a) = clip(a − 2 − x) = 0` on the
  feasible cube (the vertex is below zero).
* `U_T(x,a,s) = −a/5 − s(1 + x/10 + a/10) − 4x` — sanctions hurt the
  Target at stage level, and the Target incumbent values LOW-hardliner
  states (the `−4x` term).
* Value carriers: EXACT NEGATIVE slopes via reflection —
  `V ∈ carrier ⟺ −V ∈ valLipGainBall M c c 0` with `c_S = 4`
  (`V_S = −4x` is the Sender fixed point) and `c_T = 80/11`
  (`V_T = −(80/11)x`). Every carrier member is antitone: both players
  value low-hardliner continuation states.
* Corner pinning (Rule 1, derived): the Sender dynamic objective is
  strictly decreasing in `s` (stage ≤ −1 plus reinforcing anti-monotone
  continuation ≤ −0.94), so `σ_dyn ≡ 0` is the argmax; with `σ ≡ 0`
  the Target integrand strictly decreases in `a` (slope −1/5), so
  `α_on ≡ 0`.

Numeric probe (2026-07-03, exact rationals): σ_dyn≡0 chord margin
≤ −2.01, dual Target chord margin ≤ −1.27, A1* wedge strict on every
genuine chord, DAU cubic coefficients −1/50 and ≤ −23/50 (both
negative), image slopes exactly −4 and −80/11, norm legs 7 ≤ 8 and
76 ≤ 80.

Rule 3: NO new assumptions — an existence certificate over the existing
surface (the dual thresholds A1*/A2* were user-confirmed as
theorem-parameters in Round 47; this file discharges them at a concrete
constructed equilibrium). Rule 5: allowed witness-existence case.
-/

import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Certificates.StandardComplianceLowBasin
import Sanctions.Theory.LockIn.DynamicStake

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The dovish stage economy -/

/-- Dovish Sender stage payoff: strictly decreasing in the sanction on
the cube (`∂U_S/∂s = −s − (2 + x − a) ≤ −1`). -/
def lbU_S (x a s : ℝ) : ℝ := a - 1/2 * s ^ 2 - s * (2 + x - a) - 3 * x

/-- Dovish-mirror Target stage payoff: sanctions hurt (`∂U_T/∂s < 0`)
and the incumbent values low-hardliner states (`−4x`). -/
def lbU_T (x a s : ℝ) : ℝ :=
  -(1/5) * a - s * (1 + 1/10 * x + 1/10 * a) - 4 * x

/-- Static Sender response: the clipped vertex of the concave parabola
`U_S(x,a,·)`, `σ(x,a) = clip(a − 2 − x)` — identically `0` on the
feasible cube. -/
def lbσ (x a : ℝ) : ℝ := max 0 (min 1 (a - 2 - x))

theorem lbσ_mem (x a : ℝ) : lbσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem lbσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => lbσ xa.1 xa.2) := by
  unfold lbσ
  fun_prop

/-- **Rule-1 coupling**: the clipped vertex maximizes `U_S(x,a,·)` on
`[0,1]` (`U_S = C − ½(s − t)²` with `t = a − 2 − x`). -/
theorem lbσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => lbU_S x a s) (Set.Icc (0 : ℝ) 1) (lbσ x a) := by
  unfold lbσ
  exact WitnessKit.clipVertex_isMaxOn
    (C := a - 3 * x + 1/2 * (a - 2 - x) ^ 2)
    (by norm_num : (0:ℝ) < 1/2)
    (fun s => by unfold lbU_S; ring)

/-! ## 2. The low-mirror transition (bump vanishing at `s = 0`) -/

/-- **The low-mirror non-affine transition**: affine blend plus a
sanction-transience bump vanishing at ZERO sanction (clip-wrapped
off-square, exactly like `quadBumpF`; on the unit square
`F(x,s) = x/2 + s/2 + (1/100)(s−x)²·s`). -/
def quadBumpLowF (x s : ℝ) : ℝ :=
  1/2 * x + 1/2 * s
    + 1/100 * (Sanctions.clipS s - Sanctions.clipS x)^2 * Sanctions.clipS s

theorem quadBumpLowF_sq {x s : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) :
    quadBumpLowF x s = 1/2 * x + 1/2 * s + 1/100 * (s - x)^2 * s := by
  unfold quadBumpLowF
  rw [clipS_of_mem hx, clipS_of_mem hs]

/-- **At zero sanction the bump vanishes GLOBALLY**: `F(x,0) = x/2`. -/
theorem quadBumpLowF_zero (x : ℝ) : quadBumpLowF x 0 = x/2 := by
  unfold quadBumpLowF
  rw [show Sanctions.clipS 0 = 0 from clipS_of_mem ⟨le_refl 0, by norm_num⟩]
  ring

/-- Corner section on the square: the bump SURVIVES at full sanction, since its
factor is `s` rather than `(1 − s)`. -/
theorem quadBumpLowF_one {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    quadBumpLowF x 1 = 1/2 * x + 1/2 + 1/100 * (1 - x)^2 := by
  rw [quadBumpLowF_sq hx (by norm_num)]; ring

/-- **`quadBumpLowF`'s CORNER SECTION is not affine.**

Rule 11 / Rule 9B. Unlike `quadBumpF`, whose transience factor kills the bump at
`s = 1`, this transition's bump is carried by `s` and therefore survives exactly
where the certified recursion `x_{t+1} = F(x_t, 1)` runs. Three points refute
every affine fit: the section takes `51/100`, `1`, and `3/4 + 1/400` at
`y = 0, 1, 1/2`, while any affine map through the first two takes `151/200` at
the midpoint. So this witness bends the **realised dynamics**, not merely the
incentive layer. -/
theorem quadBumpLowF_corner_not_affine :
    ¬ ∃ a b : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, quadBumpLowF y 1 = a * y + b := by
  rintro ⟨a, b, h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hh := h (1/2) (by norm_num)
  rw [quadBumpLowF_one (by norm_num)] at h0
  rw [quadBumpLowF_one (by norm_num)] at h1
  rw [quadBumpLowF_one (by norm_num)] at hh
  norm_num at h0 h1 hh
  linarith

/-- **`quadBumpLowF` is not the affine law, for any adjustment weight.**
Immediate from the corner refutation, since `affineF δ y 1 = (1 − δ)·y + δ` is
an affine section. -/
theorem quadBumpLowF_ne_affineF (δ : ℝ) :
    quadBumpLowF ≠ AbstractGame.affineF δ := by
  intro h
  exact quadBumpLowF_corner_not_affine
    ⟨1 - δ, δ, fun y _ => by rw [h]; unfold AbstractGame.affineF; ring⟩

theorem quadBumpLowF_mem : ∀ x s : ℝ, x ∈ Set.Icc (0:ℝ) 1 →
    s ∈ Set.Icc (0:ℝ) 1 → quadBumpLowF x s ∈ Set.Icc (0:ℝ) 1 := by
  intro x s hx hs
  rw [quadBumpLowF_sq hx hs]
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (s - x)) hs.1, hx.1, hs.1]
  · rcases le_total x s with hxs | hxs
    · -- s ≥ x: (s−x)·s ≤ 1, so bump ≤ κ(s−x) ≤ κ(1−x) ≤ (1−x)/2.
      have h1 : (s - x) * s ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hxs) hs.1,
          mul_nonneg (sub_nonneg.mpr hs.2)
            (show (0:ℝ) ≤ 1 + s by linarith [hs.1]), hx.1]
      have hb : (s - x)^2 * s ≤ s - x := by
        nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hxs)]
      nlinarith [hb, hx.2, hs.2]
    · -- s ≤ x: (x−s)·s ≤ 1, so bump ≤ κ(x−s) ≤ κ(1−s) ≤ (1−s)/2.
      have h1 : (x - s) * s ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hxs) hs.1,
          mul_nonneg (sub_nonneg.mpr hs.2)
            (show (0:ℝ) ≤ 1 + s by linarith [hs.1]), hx.2, hs.1]
      have hb : (s - x)^2 * s ≤ x - s := by
        nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hxs)]
      nlinarith [hb, hx.2, hs.2, hs.1]

theorem quadBumpLowF_continuous :
    Continuous (fun (xs : ℝ × ℝ) => quadBumpLowF xs.1 xs.2) := by
  unfold quadBumpLowF Sanctions.clipS
  fun_prop

theorem quadBumpLowF_mono_x : ∀ s : ℝ, Monotone (fun x => quadBumpLowF x s) := by
  intro s x₁ x₂ hle
  unfold quadBumpLowF
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
  -- bump x-difference: (cs−c₂)²cs − (cs−c₁)²cs = −(c₂−c₁)·cs·(2cs−c₁−c₂),
  -- with cs·(2cs−c₁−c₂) ≤ 2.
  have hkeyx : (cs - c₂)^2 * cs - (cs - c₁)^2 * cs
      = -((c₂ - c₁) * (cs * (2*cs - c₁ - c₂))) := by ring
  have hup : cs * (2*cs - c₁ - c₂) ≤ 2 := by
    nlinarith [mul_nonneg hcsm.1
        (show (0:ℝ) ≤ 2 - 2*cs + c₁ + c₂ by
          linarith [hcsm.2, hc₁m.1, hc₂m.1]),
      hcsm.1, hcsm.2]
  have hprod : (c₂ - c₁) * (cs * (2*cs - c₁ - c₂)) ≤ (c₂ - c₁) * 2 :=
    mul_le_mul_of_nonneg_left hup (by linarith)
  linarith [hkeyx, hprod, hclip]

theorem quadBumpLowF_mono_s : ∀ x : ℝ, Monotone (fun s => quadBumpLowF x s) := by
  intro x s₁ s₂ hle
  unfold quadBumpLowF
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
  -- bump s-difference: (c₂−cx)²c₂ − (c₁−cx)²c₁
  --   = (c₂−c₁)·(c₂(c₂+c₁−2cx) + (c₁−cx)²), bracket ≥ −2.
  have hkey : (c₂ - cx)^2 * c₂ - (c₁ - cx)^2 * c₁
      = (c₂ - c₁) * (c₂ * (c₂ + c₁ - 2*cx) + (c₁ - cx)^2) := by ring
  have h1 : (0:ℝ) ≤ c₂ * (c₂ + c₁ - 2*cx + 2) :=
    mul_nonneg hc₂m.1 (by linarith [hc₁m.1, hc₂m.1, hcxm.2])
  have hbr : (-2 : ℝ) ≤ c₂ * (c₂ + c₁ - 2*cx) + (c₁ - cx)^2 := by
    nlinarith [h1, sq_nonneg (c₁ - cx), hc₂m.1, hc₂m.2]
  have hprod : (c₂ - c₁) * (-2 : ℝ)
      ≤ (c₂ - c₁) * (c₂ * (c₂ + c₁ - 2*cx) + (c₁ - cx)^2) :=
    mul_le_mul_of_nonneg_left hbr (by linarith)
  linarith [hkey, hprod, hclip]

theorem quadBumpLowF_diag : ∀ x : ℝ, quadBumpLowF x x = x := by
  intro x
  unfold quadBumpLowF
  ring

/-- **The low-basin witness `Params`.** -/
def lbParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 9/10
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := lbU_T
  U_S := lbU_S
  σ := lbσ
  σ_mem := lbσ_mem
  σ_isMaxOn_U_S := lbσ_isMaxOn
  U_T_continuous := by unfold lbU_T; fun_prop
  U_S_continuous := by unfold lbU_S; fun_prop
  F := quadBumpLowF
  F_continuous := quadBumpLowF_continuous
  F_mono_x := quadBumpLowF_mono_x
  F_mono_s := quadBumpLowF_mono_s
  F_diag := quadBumpLowF_diag

/-- **`lbParams` has a continuous static Sender selector.** A concrete member with the
non-affine transition `quadBumpLowF`; the selector itself does not read the transition.
The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance lbParams_staticSelectorContinuous :
    lbParams.StaticSelectorContinuous where
  σ_continuous := lbσ_continuous

@[simp] theorem lbParams_U_S : lbParams.U_S = lbU_S := rfl
@[simp] theorem lbParams_U_T : lbParams.U_T = lbU_T := rfl
@[simp] theorem lbParams_β_S : lbParams.β_S = 1/2 := rfl
@[simp] theorem lbParams_β_T : lbParams.β_T = 9/10 := rfl
@[simp] theorem lbParams_F : lbParams.F = quadBumpLowF := rfl

/-- The witness transition is genuinely non-affine
(`F(0, 1/2) = 1/4 + 1/800`).

Rule 5 (2026-08-19): now the `δ = 1/2` corollary of the parametric
`quadBumpLowF_ne_affineF`, which refutes the affine law at **every** weight.
Stronger still at this economy, the refutation is available on the corner
section alone (`quadBumpLowF_corner_not_affine`) — the slice the certified
recursion actually executes. -/
theorem lbParams_F_ne_affine : lbParams.F ≠ AbstractGame.affineF (1/2) :=
  quadBumpLowF_ne_affineF (1/2)

/-- The low-basin quadratic-bump transition satisfies strict adjustment.
Its bump is too small to reverse the sign of the affine half-gap. -/
theorem lbParams_strictAdjustment : lbParams.StrictAdjustment := by
  constructor
  · intro x s hx hs hsx
    rw [lbParams_F, quadBumpLowF_sq hx hs]
    have hd0 : 0 ≤ x - s := le_of_lt (sub_pos.mpr hsx)
    have hd1 : x - s ≤ 1 := by linarith [hx.2, hs.1]
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hprod : (x - s) * s ≤ 1 := by
      calc
        (x - s) * s ≤ 1 * s := mul_le_mul_of_nonneg_right hd1 hs0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hs1 zero_le_one
        _ = 1 := by ring
    have hb := mul_le_mul_of_nonneg_left hprod hd0
    nlinarith
  · intro x s hx hs hxs
    rw [lbParams_F, quadBumpLowF_sq hx hs]
    nlinarith [mul_nonneg (sq_nonneg (s - x)) hs.1]

/-- `s`-chord bounds on the square: factor in `[48/100, 53/100]`. -/
theorem lbParams_F_s_chord {x s₁ s₂ : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1) (hs₂ : s₂ ∈ Set.Icc (0:ℝ) 1)
    (hle : s₁ ≤ s₂) :
    48/100 * (s₂ - s₁) ≤ lbParams.F x s₂ - lbParams.F x s₁
      ∧ lbParams.F x s₂ - lbParams.F x s₁ ≤ 53/100 * (s₂ - s₁) := by
  rw [lbParams_F, quadBumpLowF_sq hx hs₁, quadBumpLowF_sq hx hs₂]
  have hkey : (s₂ - x)^2 * s₂ - (s₁ - x)^2 * s₁
      = (s₂ - s₁) * (s₂ * (s₂ + s₁ - 2*x) + (s₁ - x)^2) := by ring
  have h1 : (0:ℝ) ≤ s₂ * (s₂ + s₁ - 2*x + 2) :=
    mul_nonneg hs₂.1 (by linarith [hs₁.1, hs₂.1, hx.2])
  have hbr_lo : (-2 : ℝ) ≤ s₂ * (s₂ + s₁ - 2*x) + (s₁ - x)^2 := by
    nlinarith [h1, sq_nonneg (s₁ - x), hs₂.1, hs₂.2]
  have h2 : (s₁ - x)^2 ≤ 1 := by nlinarith [hs₁.1, hs₁.2, hx.1, hx.2]
  have hup : s₂ * (s₂ + s₁ - 2*x) ≤ 2 := by
    nlinarith [mul_nonneg hs₂.1
        (show (0:ℝ) ≤ 2 - s₂ - s₁ + 2*x by linarith [hs₁.2, hs₂.2, hx.1]),
      hs₂.1, hs₂.2]
  have hbr_hi : s₂ * (s₂ + s₁ - 2*x) + (s₁ - x)^2 ≤ 3 := by
    nlinarith [hup, h2]
  have hΔ : (0:ℝ) ≤ s₂ - s₁ := sub_nonneg.mpr hle
  constructor
  · have := mul_le_mul_of_nonneg_left hbr_lo hΔ
    linarith [hkey, this]
  · have := mul_le_mul_of_nonneg_left hbr_hi hΔ
    linarith [hkey, this]

/-! ## 3. Reflected (anti-monotone) carriers -/

/-- Sender carrier: reflections of the slope-`4` pinned gain ball —
every member has EXACT slope `−4` on the state space. -/
def lbCarrierS : Set Val := {V : Val | -V ∈ valLipGainBall 8 4 4 0}

/-- Target carrier: reflections of the slope-`80/11` pinned gain ball. -/
def lbCarrierT : Set Val := {V : Val | -V ∈ valLipGainBall 80 (80/11) (80/11) 0}

theorem lbCarrierS_isClosed : IsClosed lbCarrierS :=
  (valLipGainBall_isClosed _ _ _ _).preimage continuous_neg

theorem lbCarrierT_isClosed : IsClosed lbCarrierT :=
  (valLipGainBall_isClosed _ _ _ _).preimage continuous_neg

theorem lbCarrierS_nonempty : lbCarrierS.Nonempty := by
  refine ⟨-(affineBCF 4), ?_⟩
  show -(-(affineBCF 4)) ∈ valLipGainBall 8 4 4 0
  rw [neg_neg]
  exact affineBCF_mem_gainBall (by norm_num) (by norm_num)

theorem lbCarrierT_nonempty : lbCarrierT.Nonempty := by
  refine ⟨-(affineBCF (80/11)), ?_⟩
  show -(-(affineBCF (80/11))) ∈ valLipGainBall 80 (80/11) (80/11) 0
  rw [neg_neg]
  exact affineBCF_mem_gainBall (by norm_num) (by norm_num)

/-- Every carrier member is antitone: both players value low-hardliner
continuation states. -/
theorem antitone_of_mem_lbCarrier {M c : ℝ} (hc : 0 ≤ c) {V : Val}
    (hV : -V ∈ valLipGainBall M c c 0) : Antitone ⇑V := by
  have hmono : Monotone ⇑(-V) := monotone_of_mem_valLipGainBall hc hV
  intro y₁ y₂ hle
  have h := hmono hle
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply] at h
  linarith

/-- **Reflected affine extraction**: every carrier member satisfies
`V(clip z₂) − V(clip z₁) = −c·(z₂ − z₁)` on `[0,1]`. -/
theorem lbGainBall_clip_diff {c M : ℝ} (hc : 0 ≤ c) {V : Val}
    (hV : -V ∈ valLipGainBall M c c 0)
    {z₁ z₂ : ℝ} (h1 : z₁ ∈ Set.Icc (0:ℝ) 1) (h2 : z₂ ∈ Set.Icc (0:ℝ) 1) :
    V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) = -(c * (z₂ - z₁)) := by
  have h := gainBall_clip_diff hc hV h1 h2
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply] at h
  linarith

/-! ## 4. The dynamic Sender response is pinned at the corner `σ_dyn ≡ 0`

Stage chord factor ≤ −1 (dovish), continuation reinforces
(anti-monotone value composed with a rising transition): total chord
factor ≤ −1 − 2·(48/100) < 0. -/

theorem lbCert_senderObj_strictAntiOn {V_S : Val} (hV_S : V_S ∈ lbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictAntiOn
      (fun s => lbParams.U_S x a s
        + lbParams.β_S * V_S (Sanctions.clipS' (lbParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : lbParams.F x s₁ ∈ Set.Icc (0:ℝ) 1 := lbParams.F_mem x s₁ hx hs₁
  have hmem₂ : lbParams.F x s₂ ∈ Set.Icc (0:ℝ) 1 := lbParams.F_mem x s₂ hx hs₂
  have hdiff : V_S (Sanctions.clipS' (lbParams.F x s₂))
      - V_S (Sanctions.clipS' (lbParams.F x s₁))
      = -(4 * (lbParams.F x s₂ - lbParams.F x s₁)) :=
    lbGainBall_clip_diff (by norm_num) hV_S hmem₁ hmem₂
  have hchord := (lbParams_F_s_chord hx hs₁ hs₂ (le_of_lt hlt)).1
  simp only [lbParams_U_S, lbU_S, lbParams_β_S]
  -- stage chord factor ≤ −1; continuation ≤ −2·(48/100)·(s₂−s₁)
  have hstage : (0:ℝ) < (s₂ - s₁) * ((s₁ + s₂)/2 + (2 + x - a) - 2 * (48/100)
      + 2 * (48/100)) := by
    nlinarith [ha.2, hx.1, hs₁.1, hs₂.1, sub_pos.mpr hlt]
  nlinarith [hdiff, hchord, sub_pos.mpr hlt, ha.2, hx.1, hs₁.1, hs₂.1]

/-- **`σ_dyn_top` pinned at the corner `0`.** -/
theorem lbCert_σ_dyn_top_eq_zero {V_S : Val} (hV_S : V_S ∈ lbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lbParams.σ_dyn_top V_S x a = 0 :=
  WitnessKit.σ_dyn_top_eq_zero_of_strictAntiOn
    (lbCert_senderObj_strictAntiOn hV_S hx ha)

/-- **`σ_dyn` pinned at the corner `0`** (the selector used by the
value-class α machinery). -/
theorem lbCert_σ_dyn_eq_zero {V_S : Val} (hV_S : V_S ∈ lbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lbParams.σ_dyn V_S x a = 0 :=
  WitnessKit.σ_dyn_eq_zero_of_strictAntiOn
    (lbCert_senderObj_strictAntiOn hV_S hx ha)

/-! ## 5. State-local uniqueness -/

/-- **Sender argmax uniqueness on the carrier**: with `V_S` of exact
slope `−4`, the objective is an explicit cubic with `s³` coefficient
`−1/50` and `s²` coefficient `≤ −23/50` — strictly concave for every
compliance level `a : ℝ`. -/
theorem lbCert_DAU_on_carrier {V_S : Val} (hV_S : V_S ∈ lbCarrierS) :
    lbParams.DynamicArgmaxUnique V_S := by
  apply lbParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have hQ : ∀ s ∈ Sanctions.I,
      lbParams.U_S x a s
          + lbParams.β_S * V_S (Sanctions.clipS' (lbParams.F x s))
        = -(1/50) * s ^ 3 + (-(1/2) + 1/25 * x) * s ^ 2
          + (-(2 + x - a) - 1 - 1/50 * x^2) * s
          + (a - 4 * x + 1/2 * c₀) := by
    intro s hs
    have hmem : lbParams.F x s ∈ Set.Icc (0:ℝ) 1 := lbParams.F_mem x s hx hs
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hdiff := lbGainBall_clip_diff (show (0:ℝ) ≤ 4 by norm_num)
      hV_S h0 hmem
    simp only [lbParams_U_S, lbU_S, lbParams_β_S] at *
    rw [hc₀]
    have hFsq : lbParams.F x s
        = 1/2 * x + 1/2 * s + 1/100 * (s - x)^2 * s := by
      rw [lbParams_F]; exact quadBumpLowF_sq hx hs
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
  have hbr : (0:ℝ) < 1/50 * ((1 + p) * s₁ + (2 - p) * s₂)
      + (1/2 - 1/25 * x) := by
    have h1 : (0:ℝ) ≤ (1 + p) * s₁ :=
      mul_nonneg (by linarith [hp.le]) hs₁.1
    have h2 : (0:ℝ) ≤ (2 - p) * s₂ :=
      mul_nonneg (by linarith [hq.le]) hs₂.1
    nlinarith [hx.2, h1, h2]
  have hgap : p * (-(1/50) * s₁ ^ 3 + (-(1/2) + 1/25 * x) * s₁ ^ 2
        + (-(2 + x - a) - 1 - 1/50 * x^2) * s₁
        + (a - 4 * x + 1/2 * c₀))
      + (1 - p) * (-(1/50) * s₂ ^ 3 + (-(1/2) + 1/25 * x) * s₂ ^ 2
        + (-(2 + x - a) - 1 - 1/50 * x^2) * s₂
        + (a - 4 * x + 1/2 * c₀))
      - (-(1/50) * (p * s₁ + (1 - p) * s₂) ^ 3
        + (-(1/2) + 1/25 * x) * (p * s₁ + (1 - p) * s₂) ^ 2
        + (-(2 + x - a) - 1 - 1/50 * x^2) * (p * s₁ + (1 - p) * s₂)
        + (a - 4 * x + 1/2 * c₀))
      = -(p * (1 - p) * (s₁ - s₂)^2
          * (1/50 * ((1 + p) * s₁ + (2 - p) * s₂)
            + (1/2 - 1/25 * x))) := by ring
  nlinarith [hgap, mul_pos (mul_pos (mul_pos hp hq) hsq) hbr]

/-- **Joint Target integrand in closed form**: with `σ_dyn ≡ 0` and
`F(x,0) = x/2`, the integrand is `−a/5 − 4x + (9/10)·V_T(clip(x/2))` —
strictly decreasing in compliance. -/
theorem lbCert_joint_T_integrand_eq (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ lbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lbParams.joint_T_integrand V_T V_S x a
      = -(1/5) * a - 4 * x
        + 9/10 * V_T (Sanctions.clipS' (x/2)) := by
  have hσ := lbCert_σ_dyn_eq_zero hV_S hx ha
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [show lbParams.F x 0 = x/2 from quadBumpLowF_zero x]
  simp only [lbParams_U_T, lbU_T, lbParams_β_T]
  ring

theorem lbCert_TAU_on_carriers (V_T V_S : Val) (hV_S : V_S ∈ lbCarrierS) :
    lbParams.TargetArgmaxUnique V_T V_S :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn fun x hx a₁ ha₁ a₂ ha₂ hlt => by
    change lbParams.joint_T_integrand V_T V_S x a₂
        < lbParams.joint_T_integrand V_T V_S x a₁
    rw [lbCert_joint_T_integrand_eq V_T hV_S hx ha₂,
        lbCert_joint_T_integrand_eq V_T hV_S hx ha₁]
    linarith

theorem lbCert_zero_isMaxOn_joint (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ lbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn (fun a => lbParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [lbCert_joint_T_integrand_eq V_T hV_S hx ha,
      lbCert_joint_T_integrand_eq V_T hV_S hx
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  linarith [ha.1]

/-! ## 6. The asymmetric value class -/

def lbClass : lbParams.ValueClass2 where
  carrier_T := lbCarrierT
  carrier_S := lbCarrierS
  isClosed_T := lbCarrierT_isClosed
  isClosed_S := lbCarrierS_isClosed
  nonempty_T := lbCarrierT_nonempty
  nonempty_S := lbCarrierS_nonempty
  sender_unique_on := fun _ hV_S => (lbCert_DAU_on_carrier hV_S).toOnI
  target_unique_on := fun V_T _ V_S hV_S => lbCert_TAU_on_carriers V_T V_S hV_S

/-- **The derived leader policy is the defiance corner `α_on ≡ 0`**
(Rule 1: the joint Bellman argmax, pinned by uniqueness). -/
theorem lbCert_α_on_eq_zero (V_T : lbClass.CarrierT)
    (V_S : lbClass.CarrierS) :
    lbClass.α_on V_T V_S = fun _ => (0:ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    lbCert_zero_isMaxOn_joint V_T.val V_S.property y.property

/-! ## 7. Bellman images in closed form (both corners: `a = 0`, `s = 0`) -/

theorem lbCert_jointTarget_image (V_T : lbClass.CarrierT)
    (V_S : lbClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    lbParams.jointTarget_BCF_on_S V_T.val V_S.val
      (lbClass.sender_unique_on V_S.val V_S.property) y
      = -4 * y.val + 9/10 * V_T.val (Sanctions.clipS' (y.val/2)) := by
  have h0I : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (lbClass.sender_unique_on V_S.val V_S.property) y h0I
        (lbCert_zero_isMaxOn_joint V_T.val V_S.property y.property),
      lbCert_joint_T_integrand_eq V_T.val V_S.property y.property h0I]
  ring

theorem lbCert_bellmanS_image {W : Val} (hW : W ∈ lbCarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    lbParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = -3 * y.val + 1/2 * W (Sanctions.clipS' (y.val/2)) := by
  have h0I : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩
  have hanti := lbCert_senderObj_strictAntiOn hW y.property h0I
  have hmax : IsMaxOn
      (fun s => lbParams.U_S y.val 0 s
        + lbParams.β_S * W (Sanctions.clipS' (lbParams.F y.val s)))
      Sanctions.I 0 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.1 with heq | hlt
    · rw [← heq]
    · exact le_of_lt (hanti h0I hs hlt)
  rw [WitnessKit.bellmanS_image_of_isMaxOn (α := fun _ => (0:ℝ))
        continuous_const W y h0I hmax,
      show lbParams.F y.val 0 = y.val/2 from quadBumpLowF_zero _]
  simp only [lbParams_U_S, lbU_S, lbParams_β_S]
  ring

/-! ## 8. Carrier invariance (reflected legs: the negated images are
slope-pinned members of the ordinary gain balls). -/

theorem lbClass_IsInvariant : lbClass.IsInvariant := by
  intro V_T V_S
  have hm : ∀ y : ↥(Sanctions.S : Set ℝ), y.val/2 ∈ Set.Icc (0:ℝ) 1 :=
    fun y => ⟨by nlinarith [y.property.1], by nlinarith [y.property.2]⟩
  constructor
  · -- Target image ∈ lbCarrierT: show the NEGATED image is in the
    -- ordinary slope-(80/11) pinned ball.
    show lbParams.jointTarget_BCF_on_S V_T.val V_S.val
        (lbClass.sender_unique_on V_S.val V_S.property) ∈ lbCarrierT
    show -(lbParams.jointTarget_BCF_on_S V_T.val V_S.val
        (lbClass.sender_unique_on V_S.val V_S.property))
      ∈ valLipGainBall 80 (80/11) (80/11) 0
    refine ⟨?_, ?_, ?_⟩
    · -- norm ≤ 80
      rw [norm_neg,
        BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 80)]
      intro y
      rw [lbCert_jointTarget_image V_T V_S y, Real.norm_eq_abs]
      have hVb := BoundedContinuousFunction.norm_coe_le_norm V_T.val
        (Sanctions.clipS' (y.val/2))
      rw [Real.norm_eq_abs] at hVb
      have hVn : ‖V_T.val‖ ≤ 80 := by
        have := (V_T.property : -V_T.val ∈ valLipGainBall 80 (80/11) (80/11) 0).1
        rwa [norm_neg] at this
      have := abs_le.mp (le_trans hVb hVn)
      rw [abs_le]
      constructor <;> nlinarith [y.property.1, y.property.2, this.1, this.2]
    · -- Lipschitz 80/11 (exact reflected slope)
      intro y₁ y₂
      have hdiff := lbGainBall_clip_diff (show (0:ℝ) ≤ 80/11 by norm_num)
        V_T.property (hm y₁) (hm y₂)
      simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]
      rw [lbCert_jointTarget_image V_T V_S y₁,
          lbCert_jointTarget_image V_T V_S y₂,
          Subtype.dist_eq, Real.dist_eq]
      have hkey : -((-4) * y₂.val + 9/10 * V_T.val (Sanctions.clipS' (y₂.val/2)))
          - -((-4) * y₁.val + 9/10 * V_T.val (Sanctions.clipS' (y₁.val/2)))
          = 80/11 * (y₂.val - y₁.val) := by
        linear_combination (-(9:ℝ)/10) * hdiff
      rw [hkey, abs_mul, show |(80:ℝ)/11| = 80/11 by norm_num,
          abs_sub_comm y₁.val y₂.val]
    · -- min-slope 80/11 (exact reflected slope)
      intro y₁ y₂ _ _ hle
      have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
      have hdiff := lbGainBall_clip_diff (show (0:ℝ) ≤ 80/11 by norm_num)
        V_T.property (hm y₁) (hm y₂)
      simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]
      rw [lbCert_jointTarget_image V_T V_S y₁,
          lbCert_jointTarget_image V_T V_S y₂,
          Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
      nlinarith [hdiff]
  · -- Sender image ∈ lbCarrierS.
    show lbParams.bellmanS_BCF (lbClass.α_on V_T V_S)
        (lbClass.α_on_continuous V_T V_S) V_S.val ∈ lbCarrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (lbCert_α_on_eq_zero V_T V_S)
        (lbClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    show -(lbParams.bellmanS_BCF (fun _ => 0) continuous_const V_S.val)
      ∈ valLipGainBall 8 4 4 0
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_neg,
        BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 8)]
      intro y
      rw [lbCert_bellmanS_image V_S.property y, Real.norm_eq_abs]
      have hVb := BoundedContinuousFunction.norm_coe_le_norm V_S.val
        (Sanctions.clipS' (y.val/2))
      rw [Real.norm_eq_abs] at hVb
      have hVn : ‖V_S.val‖ ≤ 8 := by
        have := (V_S.property : -V_S.val ∈ valLipGainBall 8 4 4 0).1
        rwa [norm_neg] at this
      have := abs_le.mp (le_trans hVb hVn)
      rw [abs_le]
      constructor <;> nlinarith [y.property.1, y.property.2, this.1, this.2]
    · intro y₁ y₂
      have hdiff := lbGainBall_clip_diff (show (0:ℝ) ≤ 4 by norm_num)
        V_S.property (hm y₁) (hm y₂)
      simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]
      rw [lbCert_bellmanS_image V_S.property y₁,
          lbCert_bellmanS_image V_S.property y₂,
          Subtype.dist_eq, Real.dist_eq]
      have hkey : -((-3) * y₂.val + 1/2 * V_S.val (Sanctions.clipS' (y₂.val/2)))
          - -((-3) * y₁.val + 1/2 * V_S.val (Sanctions.clipS' (y₁.val/2)))
          = 4 * (y₂.val - y₁.val) := by
        linear_combination (-(1:ℝ)/2) * hdiff
      rw [hkey, abs_mul, show |(4:ℝ)| = 4 by norm_num,
          abs_sub_comm y₁.val y₂.val]
    · intro y₁ y₂ _ _ hle
      have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
      have hdiff := lbGainBall_clip_diff (show (0:ℝ) ≤ 4 by norm_num)
        V_S.property (hm y₁) (hm y₂)
      simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]
      rw [lbCert_bellmanS_image V_S.property y₁,
          lbCert_bellmanS_image V_S.property y₂,
          Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
      nlinarith [hdiff]

/-! ## 9. Schur row bounds (decoupled: `σ_dyn ≡ 0`, `α_on ≡ 0`) -/

theorem lbClass_hT_T_op
    (h_inv : lbClass.IsInvariant)
    (V V' : lbClass.CarrierT) (W W' : lbClass.CarrierS) :
    dist (lbClass.jointTargetOp_sub h_inv (V, W))
          (lbClass.jointTargetOp_sub h_inv (V', W'))
      ≤ (9/10 : ℝ) * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun y => -4 * y) (φ := fun y => y / 2)
    (fun V W y => lbCert_jointTarget_image V W y) V V' W W'

theorem lbClass_hT_S_op
    (h_inv : lbClass.IsInvariant)
    (V V' : lbClass.CarrierT) (W W' : lbClass.CarrierS) :
    dist (lbClass.jointSenderOp_sub h_inv (V, W))
          (lbClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    (fun V W => lbCert_α_on_eq_zero V W) V V' W W'

/-! ## 10. THE LOW-BASIN HEADLINE at the constructed equilibrium

Existence via the generic value-class Banach machinery; the dual
one-sided thresholds discharged through the stage-preference bridge
(`of_stage_preferences_low`) with antitone carriers; the top-rule
monotonicity trivial at the pinned corner (`rule ≡ 0`). Low basin
`[0, 9/10]`, sanction ceiling `s̄* = 1/10` (the realized sanctions are
identically zero). -/

/-- **Theorem 4 fired at the first low-basin witness (general-`F`
trajectory)**: from every low political start, the equilibrium state
path (evolved by the genuinely NON-AFFINE transition) stays in the low
basin, realized sanctions are bounded by `1/10` (indeed by the basin
pivot), and the sanction sequence is non-increasing — the appeasement
mirror of the high-basin persistence result. -/
theorem lbLow_generalF_three_goals :
    ∃ E : lbParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ lbCarrierT ∧ E.V_S ∈ lbCarrierS
      ∧ ∀ x₀ ∈ Set.Icc (0:ℝ) (min (9/10 : ℝ) (9/10)),
          (∀ n, lbParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (0:ℝ) (min (9/10 : ℝ) (9/10)))
          ∧ (∀ n, lbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n
                  ≤ 1/10)
          ∧ (∀ n, lbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n
                  ≤ min (9/10 : ℝ) (9/10))
          ∧ Antitone (lbParams.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨E, hVT, hVS, hα⟩ :=
    lbClass.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      lbClass_IsInvariant
      (by norm_num) (by norm_num) (le_refl 0) (le_refl 0)
      (lbClass_hT_T_op lbClass_IsInvariant)
      (lbClass_hT_S_op lbClass_IsInvariant)
      (by norm_num) (by norm_num)
  have hα0 : E.α = fun _ => (0:ℝ) := by
    rw [hα]; exact lbCert_α_on_eq_zero ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩
  -- The dual one-sided thresholds, via the stage-preference bridge.
  have hOne : lbParams.OneSidedSanctionLowBasinPreferenceThresholds
      E.V_T E.V_S E.α (9/10) (9/10) (1/10) := by
    rw [hα0]
    refine OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low
      (p := lbParams)
      (antitone_of_mem_lbCarrier (by norm_num) hVT)
      (antitone_of_mem_lbCarrier (by norm_num) hVS)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ?_ ?_
    · -- stage Sender strictly decreasing in s (dovish wedge)
      intro x hx s₁ hs₁ s₂ hs₂ hlt
      have hs₁0 : (0:ℝ) ≤ s₁ :=
        le_trans (le_min hx.1 (by norm_num)) hs₁.1
      have hs₂0 : (0:ℝ) ≤ s₂ :=
        le_trans (le_min hx.1 (by norm_num)) hs₂.1
      simp only [lbParams_U_S, lbU_S]
      nlinarith [hx.1, sub_pos.mpr hlt,
        mul_pos (sub_pos.mpr hlt)
          (show (0:ℝ) < (s₁ + s₂)/2 + (2 + x - 0) by
            nlinarith [hx.1, hs₁0, hs₂0])]
    · -- stage Target non-increasing in s
      intro x hx s₁ hs₁ s₂ hs₂ hle
      simp only [lbParams_U_T, lbU_T]
      nlinarith [hx.1, sub_nonneg.mpr hle,
        mul_nonneg (sub_nonneg.mpr hle)
          (show (0:ℝ) ≤ 1 + 1/10 * x + 1/10 * 0 by nlinarith [hx.1])]
  -- Top-rule monotonicity: the realized rule is identically 0.
  have hrule : ∀ x ∈ Set.Icc (0:ℝ) (min (9/10 : ℝ) (9/10)),
      lbParams.dynamicTopRealizedRule E.V_S E.α x = 0 := by
    intro x hx
    show lbParams.σ_dyn_top E.V_S x (E.α x) = 0
    have hxI : x ∈ Set.Icc (0:ℝ) 1 :=
      ⟨hx.1, le_trans hx.2 (by rw [min_self]; norm_num)⟩
    have haI : E.α x ∈ Sanctions.I := by
      rw [hα0]; exact ⟨le_refl 0, by norm_num⟩
    exact lbCert_σ_dyn_top_eq_zero hVS hxI haI
  have hTopMono : MonotoneOn (lbParams.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc (0 : ℝ) (min (9/10 : ℝ) (9/10))) := by
    intro y hy z hz _
    rw [hrule y hy, hrule z hz]
  refine ⟨E, hVT, hVS, fun x₀ hx₀ => ?_⟩
  exact lbParams.standardCompliance_three_goals_local_low_basin_generalF
    E hOne hTopMono hx₀

/-! ## Within-carrier uniqueness (direct Schur route, 2026-07-24) -/

/-- **Witness within-carrier uniqueness at the low-basin witness.** Any
two top-selector feedback Stackelberg equilibria with carrier values and
selector-coinciding policies agree in both value functions and the
policy. The low-basin witness builds no core certificate (its headline
fires existence directly at `lbClass`), so this applies the headline
`ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` directly at
the decoupled rows (`9/10`, `0` / `0`, `1/2`); the Schur margin
`0 < (1/10)·(1/2)` is `norm_num`. -/
theorem lbCert_unique_in_carrier
    (E E' : lbParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ lbCarrierT) (hVS : E.V_S ∈ lbCarrierS)
    (hVT' : E'.V_T ∈ lbCarrierT) (hVS' : E'.V_S ∈ lbCarrierS)
    (hαE : E.α = lbClass.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = lbClass.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  lbClass.feedbackStackelbergTop_unique_in_carrier_schur
    lbClass_IsInvariant
    (lbClass_hT_T_op lbClass_IsInvariant)
    (lbClass_hT_S_op lbClass_IsInvariant)
    (by norm_num) (by norm_num) (by norm_num)
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Witness within-carrier uniqueness at the low-basin witness, with no
selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`lbCert_unique_in_carrier` without `hαE`, `hαE'`: any two top-selector feedback
Stackelberg equilibria whose values lie in the carriers share both value
functions, and their policies agree at every feasible state. The headline
`ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` is applied
directly at the decoupled rows (`9/10`, `0` / `0`, `1/2`); the Target diagonal
bound is not supplied, since the Schur margin implies it. The economy runs the
non-affine `quadBumpLowF`; the theorem it instantiates is general in `F`. -/
theorem lbCert_unique_in_carrier_of_mem
    (E E' : lbParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ lbCarrierT) (hVS : E.V_S ∈ lbCarrierS)
    (hVT' : E'.V_T ∈ lbCarrierT) (hVS' : E'.V_S ∈ lbCarrierS) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  lbClass.feedbackStackelbergTop_unique_in_carrier_schur_of_mem
    lbClass_IsInvariant
    (le_refl 0) (le_refl 0)
    (lbClass_hT_T_op lbClass_IsInvariant)
    (lbClass_hT_S_op lbClass_IsInvariant)
    (by norm_num) (by norm_num)
    E E' hVT hVS hVT' hVS'

/-! ## DYNAMIC-STAKE: the fence bites on `lbParams`

`lbParams` is an economy whose Sender is strictly **hurt** by the Target's
entrenchment along the policy the certificate *derives* as the Target's optimum.
DYNAMIC-STAKE's contrapositive therefore forbids it from ever acquiring a
dynamic sanction floor at that policy. -/

/-- The composed Sender state chord at the derived defiance-corner policy
`α ≡ 0` (`lbCert_α_on_eq_zero`) is `−(3 + s) ≤ −3 < 0`: at every feasible
sanction, a more entrenched Target strictly hurts this Sender. -/
theorem lb_state_chord_nonpos :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      lbParams.U_S y₂ ((fun _ => (0:ℝ)) y₂) s - lbParams.U_S y₁ ((fun _ => (0:ℝ)) y₁) s
        ≤ (-3 : ℝ) * (y₂ - y₁) := by
  intro s hs y₁ _ y₂ _ hle
  show lbU_S y₂ 0 s - lbU_S y₁ 0 s ≤ (-3 : ℝ) * (y₂ - y₁)
  unfold lbU_S
  nlinarith [hs.1, sub_nonneg.mpr hle]

/-- **DYNAMIC-STAKE forbids `lbParams` from acquiring a dynamic floor at the
derived policy.** At `α ≡ 0` the greatest forward-looking Sender maximiser is at
most the greatest stage maximiser at every state, against the constructed Sender
Bellman fixed point. (Consistent with the economy's own `σ_dyn ≡ 0`.)

Scope: this is a statement about the composed chord at *this* policy. It says
nothing about `lbParams` under a different Target policy, and — because the
chord hypothesis is global — nothing basin-local. -/
theorem lb_no_dynamic_floor (x : ℝ) :
    lbParams.dynamicTopRealizedRule
        (lbParams.V_S (fun _ => (0:ℝ)) continuous_const) (fun _ => (0:ℝ)) x
      ≤ lbParams.stageTopRule (fun _ => (0:ℝ)) x :=
  lbParams.no_dynamic_floor_of_nonpos_chord continuous_const
    (by norm_num : (-3:ℝ) ≤ 0) lb_state_chord_nonpos x

end -- noncomputable section

#print axioms lbLow_generalF_three_goals
#print axioms lbCert_unique_in_carrier
#print axioms lbCert_unique_in_carrier_of_mem
#print axioms lbParams_F_ne_affine
#print axioms lb_state_chord_nonpos
#print axioms lb_no_dynamic_floor

end Examples

end Sanctions
#print axioms Sanctions.Examples.quadBumpLowF_corner_not_affine
#print axioms Sanctions.Examples.quadBumpLowF_ne_affineF
