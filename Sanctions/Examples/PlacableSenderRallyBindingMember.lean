/-
Sanctions/Examples/PlacableSenderRallyBindingMember.lean

**A non-affine member with concave state sections at which the rally margin holds
with equality and its left-hand side is strictly positive** (round J, doc 77 K3;
the reader's package `suggestions/2026-09-09-round-I-validation/`, doc 01 §2).

The composed equilibrium of the placable family (`equilibriumTop_of_margin`) and
the four-cell theorem take the rally margin

    β_S·(σ_C·g_hi·d_hi + (K_S + 2σ_C)·M_mix) ≤ r,

whose left side vanishes wherever the state-section modulus `M_cx` and the mixed
modulus `M_mix` are zero — at the affine law and at `quadDiagF`, whose state
sections are convex (`margin_of_flat`). Doc 76 Q1.4 asked whether the margin
ever binds on a member where it is not empty. This file answers yes. The
transition is `quadDiagF` with its arguments swapped,

    quadDiagFSwap x s = quadDiagF s x
                      = (x + s)/2 + ((x − x²) − (s − s²))/10   on the square,

so its state sections are concave bumps — semiconvex with modulus `1/5`, and
**not** with modulus `0`: at `s = 0` the section exceeds its chord by `1/40` at
`x = 1/2` (`quadDiagFSwap_state_not_convex`) — its sanction sections are convex
dips (modulus `0`), and its mixed chord is zero. It is not the affine law at any
rate. With `β_S = β_T = 1/2`, `σ_V = 1` and

    (q, u₀, k, r, w, ℓ, c, n, v) = (3, 1, 3, 9/278, 1, 1, 4, 1/100, 20),

`K_S = 205/139`, `σ_C = 25/139`, and the margin's left side is
`β_S·σ_C·g_hi·d_hi = 9/278 = r`: the margin holds with equality and is strictly
positive. Every other family field and both relief forms hold, so the composed
equilibrium and all four cells are instances of the generic theorems.

Rule 9: an existence certificate. It licenses "the rally margin holds and binds
on a non-affine member whose state sections are not convex" and nothing else —
not typicality, not a neighbourhood (perturbing `r` by −5 % breaks the margin,
which is what binding means), not a bifurcation of the response at the binding
point, and nothing about the mixed term, which is zero here. Rule 9C: located
and checked in exact rational arithmetic before any Lean was written
(`docs/archive/workflow-scratch/round_J_stage0_check.py`). Rule 22: general in
`F`; the transition is proved non-affine. Rule 3: no new assumption.
Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and
stage relief fields (only the sign field `hcn : n < c`). The member's interiority is the
lemma `placableRallyBindingBase_interior` (chord forms `placableRallyBinding_chordInterior`,
`placableRallyBinding_chordLossOffset`), and the myopic cell's stage relief margin comes from
the sharp relief margin (`stageRelief_of_reliefSharp`, BG3.2;
`placableRallyBinding_chordStageRelief`); the statements below are unchanged up to these proof
terms.
-/
import Sanctions.Examples.PlacableSenderRegime01

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords

noncomputable section

/-! ## 1. The swapped transition -/

/-- `quadDiagF` with its arguments swapped: concave state sections, convex
sanction sections, the diagonal fixed. -/
def quadDiagFSwap (x s : ℝ) : ℝ := quadDiagF s x

theorem quadDiagFSwap_sq {x s : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    quadDiagFSwap x s = 1/2 * x + 1/2 * s + 1/10 * ((x - x ^ 2) - (s - s ^ 2)) := by
  unfold quadDiagFSwap
  rw [quadDiagF_sq hs hx]
  ring

theorem quadDiagFSwap_mem : ∀ x s : ℝ, x ∈ Icc (0:ℝ) 1 → s ∈ Icc (0:ℝ) 1 →
    quadDiagFSwap x s ∈ Icc (0:ℝ) 1 :=
  fun x s hx hs => quadDiagF_mem s x hs hx

theorem quadDiagFSwap_continuous : Continuous (fun p : ℝ × ℝ => quadDiagFSwap p.1 p.2) := by
  unfold quadDiagFSwap
  exact quadDiagF_continuous.comp continuous_swap

theorem quadDiagFSwap_mono_x : ∀ s : ℝ, Monotone (fun x => quadDiagFSwap x s) :=
  fun s => quadDiagF_mono_s s

theorem quadDiagFSwap_mono_s : ∀ x : ℝ, Monotone (fun s => quadDiagFSwap x s) :=
  fun x => quadDiagF_mono_x x

theorem quadDiagFSwap_diag : ∀ x : ℝ, quadDiagFSwap x x = x :=
  fun x => quadDiagF_diag x

/-- **Not the affine law at any rate** (two exact section values at `s = 0`:
`23/160` at `x = 1/4` and `11/40` at `x = 1/2` would force two different
rates). -/
theorem quadDiagFSwap_ne_affineF (δ : ℝ) : quadDiagFSwap ≠ AbstractGame.affineF δ := by
  intro h
  have h1 := congrFun (congrFun h (1/4)) 0
  have h2 := congrFun (congrFun h (1/2)) 0
  rw [quadDiagFSwap_sq (by norm_num) (by norm_num)] at h1 h2
  simp only [AbstractGame.affineF] at h1 h2
  norm_num at h1 h2
  linarith

/-- State band `[2/5, 3/5]`: the state secant is `1/2 + (1 − y₁ − y₂)/10`. -/
theorem quadDiagFSwap_bandAll : StateChordBandAll quadDiagFSwap (2/5) (3/5) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  show 2/5 * (y₂ - y₁) ≤ quadDiagFSwap y₂ s - quadDiagFSwap y₁ s
    ∧ quadDiagFSwap y₂ s - quadDiagFSwap y₁ s ≤ 3/5 * (y₂ - y₁)
  rw [quadDiagFSwap_sq hy₁ hs, quadDiagFSwap_sq hy₂ hs]
  have hd : 0 ≤ y₂ - y₁ := by linarith
  have h1 := mul_nonneg hd hy₁.1
  have h2 := mul_nonneg hd hy₂.1
  have h3 := mul_nonneg hd (sub_nonneg.mpr hy₁.2)
  have h4 := mul_nonneg hd (sub_nonneg.mpr hy₂.2)
  constructor <;> nlinarith [h1, h2, h3, h4]

/-- Sanction lower chord `2/5`: the sanction secant is `2/5 + (s₁ + s₂)/10`. -/
theorem quadDiagFSwap_lo : SanctionLowerChord quadDiagFSwap (2/5) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  rw [quadDiagFSwap_sq hx hs₁, quadDiagFSwap_sq hx hs₂]
  have hd : 0 ≤ s₂ - s₁ := by linarith
  have h1 := mul_nonneg hd hs₁.1
  have h2 := mul_nonneg hd hs₂.1
  have h3 := mul_nonneg hd (sub_nonneg.mpr hs₁.2)
  have h4 := mul_nonneg hd (sub_nonneg.mpr hs₂.2)
  nlinarith [h1, h2, h3, h4]

/-- Sanction upper chord `3/5`. -/
theorem quadDiagFSwap_hi : SanctionUpperChord quadDiagFSwap (3/5) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  rw [quadDiagFSwap_sq hx hs₁, quadDiagFSwap_sq hx hs₂]
  have hd : 0 ≤ s₂ - s₁ := by linarith
  have h1 := mul_nonneg hd hs₁.1
  have h2 := mul_nonneg hd hs₂.1
  have h3 := mul_nonneg hd (sub_nonneg.mpr hs₁.2)
  have h4 := mul_nonneg hd (sub_nonneg.mpr hs₂.2)
  nlinarith [h1, h2, h3, h4]

/-- Joint chord semiconcavity: the state bump is concave (modulus `0`), the
sanction dip is `1/5`-semiconcave, there is no cross term. The chord defect is
exactly `t(1−t)·((s₁ − s₂)² − (x₁ − x₂)²)/10`. -/
theorem quadDiagFSwap_jsc :
    JointSemiconcaveOn quadDiagFSwap (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) 0 0 (-(1/5 : ℝ)) := by
  intro x₁ hx₁ x₂ hx₂ s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hxm : t * x₁ + (1 - t) * x₂ ∈ Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hx₁.1, hx₂.1], by nlinarith [hx₁.2, hx₂.2]⟩
  have hsm : t * s₁ + (1 - t) * s₂ ∈ Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hs₂.1], by nlinarith [hs₁.2, hs₂.2]⟩
  show t * quadDiagFSwap x₁ s₁ + (1 - t) * quadDiagFSwap x₂ s₂
      - quadDiagFSwap (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂)
    ≤ t * (1 - t) / 2
        * (0 * (x₁ - x₂) ^ 2 + 2 * 0 * |x₁ - x₂| * |s₁ - s₂| - (-(1/5 : ℝ)) * (s₁ - s₂) ^ 2)
  rw [quadDiagFSwap_sq hx₁ hs₁, quadDiagFSwap_sq hx₂ hs₂, quadDiagFSwap_sq hxm hsm]
  have hP : 0 ≤ t * (1 - t) * (x₁ - x₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith [hP]

/-- The state sections are concave bumps `(x − x²)/10`, above their chords by
exactly `(1/10)·t(1−t)·Δx²`: semiconvex with modulus `1/5` (the field `hFcx`). -/
theorem quadDiagFSwap_cx : ∀ s ∈ Icc (0:ℝ) 1,
    SemiconvexOnSet (fun y => quadDiagFSwap y s) (Icc (0:ℝ) 1) (1/5) := by
  intro s hs y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hm := mem_Icc_convexComb hy₁ hy₂ ht0 ht1
  show quadDiagFSwap (t * y₁ + (1 - t) * y₂) s
      - (t * quadDiagFSwap y₁ s + (1 - t) * quadDiagFSwap y₂ s)
    ≤ 1/5 / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)
  rw [quadDiagFSwap_sq hm hs, quadDiagFSwap_sq hy₁ hs, quadDiagFSwap_sq hy₂ hs]
  have hT : 0 ≤ t * (1 - t) * (y₁ - y₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith [hT]

/-- The sanction sections are convex dips `−(s − s²)/10`, so they have zero
semiconvexity defect (the subclass field `hFcs`). -/
theorem quadDiagFSwap_cs : ∀ x ∈ Icc (0:ℝ) 1,
    SemiconvexOnSet (fun s => quadDiagFSwap x s) (Icc (0:ℝ) 1) 0 := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hm := mem_Icc_convexComb hs₁ hs₂ ht0 ht1
  show quadDiagFSwap x (t * s₁ + (1 - t) * s₂)
      - (t * quadDiagFSwap x s₁ + (1 - t) * quadDiagFSwap x s₂)
    ≤ 0 / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
  rw [quadDiagFSwap_sq hx hm, quadDiagFSwap_sq hx hs₁, quadDiagFSwap_sq hx hs₂]
  have hT : 0 ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith [hT]

/-- Additively separable, so the mixed chord is identically zero. -/
theorem quadDiagFSwap_mix : MixedChordBound quadDiagFSwap 0 := by
  intro x₁ x₂ s₁ s₂ _ _ _ _
  have h : (quadDiagFSwap x₂ s₂ - quadDiagFSwap x₁ s₂)
      - (quadDiagFSwap x₂ s₁ - quadDiagFSwap x₁ s₁) = 0 := by
    unfold quadDiagFSwap quadDiagF; ring
  rw [h]; simp

/-- **The state sections are not `0`-semiconvex**: at `s = 0` and `x = 1/2` the
section `11/40` exceeds the chord value `1/4` by `1/40`. So the modulus `1/5`
supplied below is genuine curvature, not a loose certificate on a flat map. -/
theorem quadDiagFSwap_state_not_convex :
    ¬ SemiconvexOnSet (fun y => quadDiagFSwap y 0) (Icc (0:ℝ) 1) 0 := by
  intro h
  have h' := h 0 (by norm_num) 1 (by norm_num) (1/2) (by norm_num) (by norm_num)
  have e1 : quadDiagFSwap (1/2 * 0 + (1 - 1/2) * 1) 0 = 11/40 := by
    rw [quadDiagFSwap_sq (by norm_num) (by norm_num)]; norm_num
  have e2 : quadDiagFSwap 0 0 = 0 := by
    rw [quadDiagFSwap_sq (by norm_num) (by norm_num)]; norm_num
  have e3 : quadDiagFSwap 1 0 = 1/2 := by
    rw [quadDiagFSwap_sq (by norm_num) (by norm_num)]; norm_num
  simp only [e1, e2, e3] at h'
  norm_num at h'

/-! ## 2. The member -/

/-- The base member at the swapped transition, with the rally-binding
coefficients. -/
def placableRallyBindingBase : PlacableEconomyF where
  F := quadDiagFSwap
  F_continuous := quadDiagFSwap_continuous
  F_mono_x := quadDiagFSwap_mono_x
  F_mono_s := quadDiagFSwap_mono_s
  F_diag := quadDiagFSwap_diag
  glo := 2/5
  ghi := 3/5
  dlo := 2/5
  dhi := 3/5
  Mx := 0
  Mm := 0
  Ms := 1/5
  hbandAll := quadDiagFSwap_bandAll
  hSlo := quadDiagFSwap_lo
  hShi := quadDiagFSwap_hi
  hFjsc := quadDiagFSwap_jsc
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  hMx0 := by norm_num
  hMm0 := by norm_num
  hMs0 := by norm_num
  Mcx := 1/5
  hMcx0 := by norm_num
  hFcx := quadDiagFSwap_cx
  Mmix := 0
  hFmix := quadDiagFSwap_mix
  δ := 1/2
  βS := 1/2
  βT := 1/2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  q := 3
  u₀ := 1
  k := 3
  r := 9/278
  w := 1
  ℓ := 1
  c := 4
  n := 1/100
  v := 20
  hu₀ := by norm_num
  hr := by norm_num
  hw := by norm_num
  hℓ := by norm_num
  hn := by norm_num
  SigV := 1
  hCurv := by norm_num [plKS]
  hSigV := by norm_num [plSigImg, plSig, plRho, plMu, plKS]
  hk := by norm_num
  hv := by norm_num
  hcn := by norm_num

/-- Placability at `placableRallyBindingBase` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableRallyBindingBase_placable : placableRallyBindingBase.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableRallyBindingBase]

/-- The loss-offset margin at `placableRallyBindingBase` (a hypothesis since round AP). -/
theorem placableRallyBindingBase_margin : placableRallyBindingBase.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableRallyBindingBase]

/-- Interiority at `placableRallyBindingBase` (a field of the family until renovation item
BJ2.3, 2026-10-07, now a hypothesis). At the non-affine transition `quadDiagFSwap`. -/
theorem placableRallyBindingBase_interior : placableRallyBindingBase.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableRallyBindingBase]

/-- The enriched member: the sanction sections are convex, so the subclass
modulus is `0`. -/
def placableRallyBinding : PlacableEconomyFcs where
  toPlacableEconomyF := placableRallyBindingBase
  Mcs := 0
  hMcs0 := by norm_num
  hFcs := quadDiagFSwap_cs

theorem placableRallyBinding_base :
    placableRallyBinding.toPlacableEconomyF = placableRallyBindingBase := rfl

/-- The member's interiority in the chord form (renovation item BJ2.3). At the
non-affine transition `quadDiagFSwap`. -/
theorem placableRallyBinding_chordInterior : placableRallyBinding.toChordCs.Interior :=
  placableRallyBinding.toChordCs_interior placableRallyBindingBase_interior

/-- The member's loss-offset margin in the chord form; the floor condition `u₀ ≤ q`
comes from interiority (renovation item BJ2.3). At the non-affine transition
`quadDiagFSwap`. -/
theorem placableRallyBinding_chordLossOffset : placableRallyBindingBase.toChord.LossOffset :=
  placableRallyBindingBase.toChord_lossOffset
    (placableRallyBindingBase.u₀_le_q placableRallyBindingBase_interior)
    placableRallyBindingBase_margin

/-- `K_S = (r + w)/(1 − β_S·g_hi) = (287/278)/(7/10) = 205/139`. -/
theorem placableRallyBinding_KS : placableRallyBinding.KS = 205 / 139 := by
  unfold PlacableEconomyF.KS plKS
  norm_num [placableRallyBinding, placableRallyBindingBase]

/-- `σ_C = β_S·K_S·M_cx/(1 − β_S·g_hi²) = 25/139`. -/
theorem placableRallyBinding_SigC : placableRallyBinding.SigC = 25 / 139 := by
  unfold PlacableEconomyF.SigC plSigC PlacableEconomyF.KS plKS
  norm_num [placableRallyBinding, placableRallyBindingBase]

/-- **The rally margin binds:** its left side `β_S·σ_C·g_hi·d_hi = 9/278`
equals `r`. -/
theorem placableRallyBinding_margin_eq :
    placableRallyBinding.βS * (placableRallyBinding.SigC * placableRallyBinding.ghi
        * placableRallyBinding.dhi
      + (placableRallyBinding.KS + 2 * placableRallyBinding.SigC) * placableRallyBinding.Mmix)
      = placableRallyBinding.r := by
  rw [placableRallyBinding_SigC, placableRallyBinding_KS]
  norm_num [placableRallyBinding, placableRallyBindingBase]

/-- **The left side is strictly positive**: the margin is not empty here. -/
theorem placableRallyBinding_margin_pos :
    0 < placableRallyBinding.βS * (placableRallyBinding.SigC * placableRallyBinding.ghi
        * placableRallyBinding.dhi
      + (placableRallyBinding.KS + 2 * placableRallyBinding.SigC) * placableRallyBinding.Mmix) := by
  rw [placableRallyBinding_margin_eq]
  norm_num [placableRallyBinding, placableRallyBindingBase]

/-- The rally margin, as the composed equilibrium and the four-cell theorem take it. -/
theorem placableRallyBinding_margin :
    placableRallyBinding.βS * (placableRallyBinding.SigC * placableRallyBinding.ghi
        * placableRallyBinding.dhi
      + (placableRallyBinding.KS + 2 * placableRallyBinding.SigC) * placableRallyBinding.Mmix)
      ≤ placableRallyBinding.r :=
  le_of_eq placableRallyBinding_margin_eq

/-- `M_tot = q + β_S·(σ_C·d_hi² + K_S·M_cs) = 3 + (1/2)(25/139)(9/25) = 843/278`. -/
theorem placableRallyBinding_Mtot : placableRallyBinding.toChordCs.Mtot = 843 / 278 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableRallyBinding,
    placableRallyBindingBase]

/-- The sharp relief margin: `ℓ·M_tot = 843/278 < 1197/100 = k(c − n)`. -/
theorem placableRallyBinding_relief_sharp :
    placableRallyBinding.ℓ * placableRallyBinding.toChordCs.Mtot
      < placableRallyBinding.k * (placableRallyBinding.c - placableRallyBinding.n) := by
  rw [placableRallyBinding_Mtot]
  norm_num [placableRallyBinding, placableRallyBindingBase]

/-- The member's stage relief margin in the chord form, from the sharp relief margin
(`stageRelief_of_reliefSharp`, BG3.2; renovation item BJ2.3: no longer a field). At the
non-affine transition `quadDiagFSwap`. -/
theorem placableRallyBinding_chordStageRelief : placableRallyBindingBase.toChord.StageRelief :=
  placableRallyBinding.toChordCs.stageRelief_of_reliefSharp placableRallyBinding_relief_sharp

/-- The member's transition is not the affine law at any rate. -/
theorem placableRallyBinding_F_ne_affineF (δ : ℝ) :
    placableRallyBinding.F ≠ AbstractGame.affineF δ :=
  quadDiagFSwap_ne_affineF δ

/-- The member's state sections are not convex (the modulus `M_cx = 1/5` is
genuine). -/
theorem placableRallyBinding_state_not_convex :
    ¬ SemiconvexOnSet (fun y => placableRallyBinding.F y 0) (Icc (0:ℝ) 1) 0 :=
  quadDiagFSwap_state_not_convex

/-- **The four cells at the rally-binding member**, through the family theorem
with the binding margin supplied as an equality, in closed form. -/
theorem placableRallyBinding_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableRallyBindingBase.toChord.myopicPath
        placableRallyBinding_chordInterior placableRallyBinding_chordStageRelief
      (placableRallyBindingBase.toChord_placable placableRallyBindingBase_placable)) x₀) atTop
      (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableRallyBinding.toChordCs.senderOnlyPath'
        placableRallyBinding_chordInterior
      (placableRallyBindingBase.toChord_placable placableRallyBindingBase_placable))
      placableRallyBinding_relief_sharp placableRallyBindingBase.toChord_zeroSanctionNeutral x₀)
      atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (placableRallyBindingBase.toChord.targetOnlyPath
      placableRallyBinding_chordLossOffset x₀) atTop
      (𝓝 placableRallyBindingBase.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableRallyBindingBase.toChord.responsePath placableRallyBindingBase.toChord.VSstar z = z ∧
      placableRallyBindingBase.steady10 < z ∧
      Tendsto (placableRallyBindingBase.toChord.dynamicPath
        placableRallyBinding_chordLossOffset
        (placableRallyBindingBase.toChord_margin placableRallyBinding_margin) x₀)
        atTop (𝓝 z)) ∧
    0 < placableRallyBindingBase.steady10 :=
  placableRallyBinding.four_cell_closedForm placableRallyBindingBase_interior
    placableRallyBindingBase_margin
    placableRallyBindingBase_placable placableRallyBinding_margin placableRallyBinding_relief_sharp

/-- **Non-vacuity of the binding rally margin** (Rule 9A): there is a member of
the enriched subclass, not the affine law at any rate and with non-convex state
sections, at which the rally margin holds with equality, its left side is
strictly positive, and the sharp relief margin holds — so the composed
equilibrium and all four cells are the generic theorems' instances there.
Existence, and nothing more. -/
theorem exists_binding_rally_member :
    ∃ E : PlacableEconomyFcs,
      (∀ δ, E.F ≠ AbstractGame.affineF δ) ∧
      ¬ SemiconvexOnSet (fun y => E.F y 0) (Icc (0:ℝ) 1) 0 ∧
      0 < E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ∧
      E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) = E.r ∧
      E.ℓ * E.toChordCs.Mtot < E.k * (E.c - E.n) :=
  ⟨placableRallyBinding, placableRallyBinding_F_ne_affineF,
    placableRallyBinding_state_not_convex, placableRallyBinding_margin_pos,
    placableRallyBinding_margin_eq, placableRallyBinding_relief_sharp⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.placableRallyBinding_four_cells
#print axioms Sanctions.Examples.exists_binding_rally_member

end Examples
end Sanctions
