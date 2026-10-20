/-
Sanctions/Examples/PlacableSenderWitnesses.lean

**Non-vacuity and generality witnesses for the placable-Sender family
(Rule 9B).**

Two members of `PlacableEconomyF`, both located and perturbed in exact rational
arithmetic before any Lean was written
(`docs/archive/workflow-scratch/rung2/placable_family_feasibility_v3.py`):

* `placableAffine` — the affine law at rate `1/2`, at the coefficient point
  `(β_S, β_T, q, u₀, k, r, w, ℓ, c, n, v) = (1/2, 1/2, 3, 1, 3, 1/2, 1, 1, 4, 0, 30)`
  with supplied carrier modulus `SigV = 1`. The script certifies an open ball
  of relative radius one-tenth around it inside the family, so the affine
  member is not a knife edge.
* `placableQuadDiag` — the same coefficients at the **non-affine** transition
  `quadDiagF`, which carries quadratic curvature in both arguments along the
  diagonal and is proved unequal to `affineF δ` for every `δ`. This is the
  Rule 9B generality witness: the class is inhabited *outside* the special
  case it generalises (Rule 22).

## What the vacuity check looks like here

`PlacableEconomyF` has no field of type `Prop`: every proposition-valued field
is a specific relation over the structure's own data (a chord on `F`, a sign, an
inequality among coefficients), so nothing can be set to `True` (Rule 14). The
opaque-`Prop` probe of Rule 9B is therefore vacuous by construction, and the
non-vacuity content is that the two members below elaborate. Joint
satisfiability of the margins is what the members *are*.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BJ2.3 (2026-10-07): the family dropped its interiority and stage relief
fields for the sign field `hcn : n < c`. Each member below now proves interiority and the
stage relief margin as lemmas (`placableAffine_interior`, `placableAffine_stageRelief`,
and the same for `placableQuadDiag`), and their chord forms
(`placableAffine_chordInterior`, `placableAffine_chordStageRelief`,
`placableAffine_chordLossOffset`) feed the chord-economy theorems; the statements of the
results below are unchanged up to these proof-term arguments.
-/
import Sanctions.Examples.PlacableSenderEquilibrium
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Examples.PlacableSenderFamilyF

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords

noncomputable section

/-! ## 1. The affine member -/

theorem affineF_half_bandAll : StateChordBandAll (AbstractGame.affineF (1/2)) (1/2) (1/2) := by
  intro s _ y₁ _ y₂ _ hle
  simp only [AbstractGame.affineF]
  constructor <;> linarith

theorem affineF_half_lo : SanctionLowerChord (AbstractGame.affineF (1/2)) (1/2) := by
  intro x s₁ s₂ _ _ _ hle
  simp only [AbstractGame.affineF]
  linarith

theorem affineF_half_hi : SanctionUpperChord (AbstractGame.affineF (1/2)) (1/2) := by
  intro x s₁ s₂ _ _ _ hle
  simp only [AbstractGame.affineF]
  linarith

theorem affineF_half_jsc :
    JointSemiconcaveOn (AbstractGame.affineF (1/2)) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
      0 0 (-(0 : ℝ)) := by
  intro x₁ _ x₂ _ s₁ _ s₂ _ t _ _
  simp only [AbstractGame.affineF]
  ring_nf
  simp

/-- Affine state sections have zero chord defect (Rung 3 field). -/
theorem affineF_half_cx : ∀ s ∈ Icc (0:ℝ) 1,
    SemiconvexOnSet (fun y => AbstractGame.affineF (1/2) y s) (Icc (0:ℝ) 1) 0 := by
  intro s _
  exact (semiconvexOnSet_affine (A := Icc (0:ℝ) 1) (1/2 : ℝ) (1/2 * s)).congr
    (fun y _ => by unfold AbstractGame.affineF; ring)

/-- Affine sanction sections have zero chord defect (doc 63 field). -/
theorem affineF_half_cs : ∀ x ∈ Icc (0:ℝ) 1,
    SemiconvexOnSet (fun s => AbstractGame.affineF (1/2) x s) (Icc (0:ℝ) 1) 0 := by
  intro x _
  exact (semiconvexOnSet_affine (A := Icc (0:ℝ) 1) (1/2 : ℝ) (1/2 * x)).congr
    (fun s _ => by unfold AbstractGame.affineF; ring)

/-- The affine law has no mixed curvature (Rung 3 field). -/
theorem affineF_half_mix : MixedChordBound (AbstractGame.affineF (1/2)) 0 := by
  intro x₁ x₂ s₁ s₂ _ _ _ _
  have h : (AbstractGame.affineF (1/2) x₂ s₂ - AbstractGame.affineF (1/2) x₁ s₂)
      - (AbstractGame.affineF (1/2) x₂ s₁ - AbstractGame.affineF (1/2) x₁ s₁) = 0 := by
    unfold AbstractGame.affineF; ring
  rw [h]; simp

/-- **The affine member.** -/
def placableAffine : PlacableEconomyF where
  F := AbstractGame.affineF (1/2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _
  glo := 1/2
  ghi := 1/2
  dlo := 1/2
  dhi := 1/2
  Mx := 0
  Mm := 0
  Ms := 0
  hbandAll := affineF_half_bandAll
  hSlo := affineF_half_lo
  hShi := affineF_half_hi
  hFjsc := affineF_half_jsc
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  hMx0 := by norm_num
  hMm0 := by norm_num
  hMs0 := by norm_num
  Mcx := 0
  hMcx0 := by norm_num
  hFcx := affineF_half_cx
  Mmix := 0
  hFmix := affineF_half_mix
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
  r := 1/2
  w := 1
  ℓ := 1
  c := 4
  n := 0
  v := 30
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

/-- Placability at `placableAffine` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableAffine_placable : placableAffine.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableAffine]

/-- The loss-offset margin at `placableAffine` (a hypothesis since round AP). -/
theorem placableAffine_margin : placableAffine.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableAffine]

/-- Interiority at `placableAffine`: the appetite `A = 1 + 1/2 + (1/2)·2·(1/2) = 2` is
below `q = 3` (a field of the family until renovation item BJ2.3, now a hypothesis).
Affine-restricted (the member's transition is `affineF (1/2)`). -/
theorem placableAffine_interior : placableAffine.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableAffine]

/-- The stage relief margin at `placableAffine`: `ℓ·q = 3 < k·(c − n) = 12` (a field of
the family until renovation item BJ2.3, now a hypothesis). Affine-restricted. -/
theorem placableAffine_stageRelief : placableAffine.StageRelief := by
  unfold PlacableEconomyF.StageRelief
  norm_num [placableAffine]

/-- The affine member satisfies the stage flip `ℓq < u₀(c − n)` (`3 < 4`), the
hypothesis of the activation results since round Q2. -/
theorem placableAffine_flip :
    placableAffine.ℓ * placableAffine.q < placableAffine.u₀ * (placableAffine.c - placableAffine.n) := by
  norm_num [placableAffine]

/-! ## 2. The non-affine member: quadratic curvature along the diagonal -/

/-- `quadDiagF x s = x/2 + s/2 + (φ(s) − φ(x))/10` with `φ(u) = u − u²`, arguments
clipped into `[0,1]` so the transition is globally monotone. On the square it is
the affine law at rate `1/2` plus a concave bump in the sanction and a convex
dip in the state, with the diagonal fixed. -/
def quadDiagF (x s : ℝ) : ℝ :=
  1/2 * x + 1/2 * s
    + 1/10 * ((Sanctions.clipS s - (Sanctions.clipS s) ^ 2)
        - (Sanctions.clipS x - (Sanctions.clipS x) ^ 2))

theorem clipS_of_mem' {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : Sanctions.clipS t = t := by
  unfold Sanctions.clipS
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem quadDiagF_sq {x s : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    quadDiagF x s = 1/2 * x + 1/2 * s + 1/10 * ((s - s ^ 2) - (x - x ^ 2)) := by
  unfold quadDiagF
  rw [clipS_of_mem' hx, clipS_of_mem' hs]

theorem quadDiagF_mem : ∀ x s : ℝ, x ∈ Icc (0:ℝ) 1 → s ∈ Icc (0:ℝ) 1 →
    quadDiagF x s ∈ Icc (0:ℝ) 1 := by
  intro x s hx hs
  rw [quadDiagF_sq hx hs]
  have h1 := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have h2 := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2, h1, h2]

theorem quadDiagF_continuous : Continuous (fun p : ℝ × ℝ => quadDiagF p.1 p.2) := by
  unfold quadDiagF Sanctions.clipS
  fun_prop

theorem quadDiagF_mono_x : ∀ s : ℝ, Monotone (fun x => quadDiagF x s) := by
  intro s x₁ x₂ hle
  unfold quadDiagF
  set c₁ := Sanctions.clipS x₁ with hc₁
  set c₂ := Sanctions.clipS x₂ with hc₂
  have hc₁m : c₁ ∈ Icc (0:ℝ) 1 := Sanctions.clipS_mem x₁
  have hc₂m : c₂ ∈ Icc (0:ℝ) 1 := Sanctions.clipS_mem x₂
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ x₂ - x₁ := by
    have := Sanctions.clipS_lipschitz_abs x₂ x₁
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ x₂ - x₁)] at this
    linarith
  simp only
  have hkey : (c₂ - c₂ ^ 2) - (c₁ - c₁ ^ 2) = (c₂ - c₁) * (1 - c₁ - c₂) := by ring
  have hbr : (c₂ - c₁) * (1 - c₁ - c₂) ≤ (c₂ - c₁) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith [hc₁m.1, hc₂m.1]) (by linarith)
  nlinarith [hkey, hbr, hclip]

theorem quadDiagF_mono_s : ∀ x : ℝ, Monotone (fun s => quadDiagF x s) := by
  intro x s₁ s₂ hle
  unfold quadDiagF
  set c₁ := Sanctions.clipS s₁ with hc₁
  set c₂ := Sanctions.clipS s₂ with hc₂
  have hc₁m : c₁ ∈ Icc (0:ℝ) 1 := Sanctions.clipS_mem s₁
  have hc₂m : c₂ ∈ Icc (0:ℝ) 1 := Sanctions.clipS_mem s₂
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ s₂ - s₁ := by
    have := Sanctions.clipS_lipschitz_abs s₂ s₁
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ - s₁)] at this
    linarith
  simp only
  have hkey : (c₂ - c₂ ^ 2) - (c₁ - c₁ ^ 2) = (c₂ - c₁) * (1 - c₁ - c₂) := by ring
  have hbr : (c₂ - c₁) * (-1 : ℝ) ≤ (c₂ - c₁) * (1 - c₁ - c₂) :=
    mul_le_mul_of_nonneg_left (by linarith [hc₁m.2, hc₂m.2]) (by linarith)
  nlinarith [hkey, hbr, hclip]

theorem quadDiagF_diag : ∀ x : ℝ, quadDiagF x x = x := by
  intro x
  unfold quadDiagF
  ring

/-- **`quadDiagF` is not the affine law at any rate** (Rule 9B generality
witness; Rule 22). -/
theorem quadDiagF_ne_affineF (δ : ℝ) : quadDiagF ≠ AbstractGame.affineF δ := by
  intro h
  have h1 := congrFun (congrFun h (1/4)) 0
  have h2 := congrFun (congrFun h (1/2)) 0
  rw [quadDiagF_sq (by norm_num) (by norm_num)] at h1 h2
  simp only [AbstractGame.affineF] at h1 h2
  norm_num at h1 h2
  linarith

theorem quadDiagF_bandAll : StateChordBandAll quadDiagF (2/5) (3/5) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  show 2/5 * (y₂ - y₁) ≤ quadDiagF y₂ s - quadDiagF y₁ s
    ∧ quadDiagF y₂ s - quadDiagF y₁ s ≤ 3/5 * (y₂ - y₁)
  rw [quadDiagF_sq hy₁ hs, quadDiagF_sq hy₂ hs]
  have hd : 0 ≤ y₂ - y₁ := by linarith
  have h1 := mul_nonneg hd hy₁.1
  have h2 := mul_nonneg hd hy₂.1
  have h3 := mul_nonneg hd (sub_nonneg.mpr hy₁.2)
  have h4 := mul_nonneg hd (sub_nonneg.mpr hy₂.2)
  constructor <;> nlinarith [h1, h2, h3, h4]

theorem quadDiagF_lo : SanctionLowerChord quadDiagF (2/5) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  rw [quadDiagF_sq hx hs₁, quadDiagF_sq hx hs₂]
  have hd : 0 ≤ s₂ - s₁ := by linarith
  have h1 := mul_nonneg hd hs₁.1
  have h2 := mul_nonneg hd hs₂.1
  have h3 := mul_nonneg hd (sub_nonneg.mpr hs₁.2)
  have h4 := mul_nonneg hd (sub_nonneg.mpr hs₂.2)
  nlinarith [h1, h2, h3, h4]

theorem quadDiagF_hi : SanctionUpperChord quadDiagF (3/5) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  rw [quadDiagF_sq hx hs₁, quadDiagF_sq hx hs₂]
  have hd : 0 ≤ s₂ - s₁ := by linarith
  have h1 := mul_nonneg hd hs₁.1
  have h2 := mul_nonneg hd hs₂.1
  have h3 := mul_nonneg hd (sub_nonneg.mpr hs₁.2)
  have h4 := mul_nonneg hd (sub_nonneg.mpr hs₂.2)
  nlinarith [h1, h2, h3, h4]

/-- Joint chord semiconcavity: the state dip is `1/5`-semiconcave, the
sanction bump is concave, there is no cross term. -/
theorem quadDiagF_jsc :
    JointSemiconcaveOn quadDiagF (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) (1/5) 0 (-(0 : ℝ)) := by
  intro x₁ hx₁ x₂ hx₂ s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hxm : t * x₁ + (1 - t) * x₂ ∈ Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hx₁.1, hx₂.1], by nlinarith [hx₁.2, hx₂.2]⟩
  have hsm : t * s₁ + (1 - t) * s₂ ∈ Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hs₂.1], by nlinarith [hs₁.2, hs₂.2]⟩
  show t * quadDiagF x₁ s₁ + (1 - t) * quadDiagF x₂ s₂
      - quadDiagF (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂)
    ≤ t * (1 - t) / 2
        * (1/5 * (x₁ - x₂) ^ 2 + 2 * 0 * |x₁ - x₂| * |s₁ - s₂| - (-(0:ℝ)) * (s₁ - s₂) ^ 2)
  rw [quadDiagF_sq hx₁ hs₁, quadDiagF_sq hx₂ hs₂, quadDiagF_sq hxm hsm]
  have hP : 0 ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith [hP]

/-- The sanction sections of `quadDiagF` are concave bumps `(s − s²)/10`, above
their chords by exactly `(1/10)·t(1−t)·Δs²`: semiconvex with modulus `1/5`
(doc 63 field). -/
theorem quadDiagF_cs : ∀ x ∈ Icc (0:ℝ) 1,
    SemiconvexOnSet (fun s => quadDiagF x s) (Icc (0:ℝ) 1) (1/5) := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hm := mem_Icc_convexComb hs₁ hs₂ ht0 ht1
  simp only [quadDiagF]
  rw [clipS_of_mem' hx, clipS_of_mem' hs₁, clipS_of_mem' hs₂, clipS_of_mem' hm]
  have hT : 0 ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith [hT]

/-- The state sections of `quadDiagF` are convex on `[0,1]` — the dip
`+(1/10)·x²` — so they have zero semiconvexity defect (Rung 3 field). -/
theorem quadDiagF_cx : ∀ s ∈ Icc (0:ℝ) 1,
    SemiconvexOnSet (fun y => quadDiagF y s) (Icc (0:ℝ) 1) 0 := by
  intro s _ y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hm := mem_Icc_convexComb hy₁ hy₂ ht0 ht1
  simp only [quadDiagF]
  rw [clipS_of_mem' hy₁, clipS_of_mem' hy₂, clipS_of_mem' hm]
  have hT : 0 ≤ t * (1 - t) * (y₁ - y₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith [hT]

/-- `quadDiagF` is additively separable, so its mixed chord is identically zero
(Rung 3 field). -/
theorem quadDiagF_mix : MixedChordBound quadDiagF 0 := by
  intro x₁ x₂ s₁ s₂ _ _ _ _
  have h : (quadDiagF x₂ s₂ - quadDiagF x₁ s₂) - (quadDiagF x₂ s₁ - quadDiagF x₁ s₁) = 0 := by
    unfold quadDiagF; ring
  rw [h]; simp

/-- **The non-affine member.** Same coefficients as the affine member, at the
transition `quadDiagF` with its exact chord constants
`glo = dlo = 2/5`, `ghi = dhi = 3/5`, `Mx = 1/5`, `Mm = Ms = 0`. -/
def placableQuadDiag : PlacableEconomyF where
  F := quadDiagF
  F_continuous := quadDiagF_continuous
  F_mono_x := quadDiagF_mono_x
  F_mono_s := quadDiagF_mono_s
  F_diag := quadDiagF_diag
  glo := 2/5
  ghi := 3/5
  dlo := 2/5
  dhi := 3/5
  Mx := 1/5
  Mm := 0
  Ms := 0
  hbandAll := quadDiagF_bandAll
  hSlo := quadDiagF_lo
  hShi := quadDiagF_hi
  hFjsc := quadDiagF_jsc
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  hMx0 := by norm_num
  hMm0 := by norm_num
  hMs0 := by norm_num
  Mcx := 0
  hMcx0 := by norm_num
  hFcx := quadDiagF_cx
  Mmix := 0
  hFmix := quadDiagF_mix
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
  r := 1/2
  w := 1
  ℓ := 1
  c := 4
  n := 0
  v := 30
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

/-- Placability at `placableQuadDiag` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableQuadDiag_placable : placableQuadDiag.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableQuadDiag]

/-- The loss-offset margin at `placableQuadDiag` (a hypothesis since round AP). -/
theorem placableQuadDiag_margin : placableQuadDiag.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableQuadDiag]

/-- Interiority at `placableQuadDiag`: the appetite `A = 15/7` is below `q = 3` (a field
of the family until renovation item BJ2.3, now a hypothesis). At the non-affine
transition `quadDiagF`. -/
theorem placableQuadDiag_interior : placableQuadDiag.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableQuadDiag]

/-- The stage relief margin at `placableQuadDiag`: `3 < 12` (a field of the family until
renovation item BJ2.3, now a hypothesis). At the non-affine transition `quadDiagF`. -/
theorem placableQuadDiag_stageRelief : placableQuadDiag.StageRelief := by
  unfold PlacableEconomyF.StageRelief
  norm_num [placableQuadDiag]

/-- The non-affine member satisfies the stage flip (`3 < 4`). -/
theorem placableQuadDiag_flip :
    placableQuadDiag.ℓ * placableQuadDiag.q
      < placableQuadDiag.u₀ * (placableQuadDiag.c - placableQuadDiag.n) := by
  norm_num [placableQuadDiag]

/-- The non-affine member's transition is not the affine law at any rate. -/
theorem placableQuadDiag_F_ne_affineF (δ : ℝ) :
    placableQuadDiag.F ≠ AbstractGame.affineF δ :=
  quadDiagF_ne_affineF δ

/-- **The discriminant condition at the affine member** (round M, doc 82 P2):
`Q = 3`, `L = 5/2`, `N = 1/4`, `D = 1/8`; the supplied `σ_V = 1` and the vertex
`L/(2D) = 10` both certify. -/
theorem placableAffine_riccati_feasible :
    0 < plRicQ placableAffine.βS placableAffine.q placableAffine.KS placableAffine.Ms ∧
    0 < plRicL placableAffine.βS placableAffine.q placableAffine.r placableAffine.ghi
        placableAffine.dhi placableAffine.KS placableAffine.Mx placableAffine.Mm placableAffine.Ms ∧
    plRicL placableAffine.βS placableAffine.q placableAffine.r placableAffine.ghi
        placableAffine.dhi placableAffine.KS placableAffine.Mx placableAffine.Mm placableAffine.Ms
      < 2 * plRicQ placableAffine.βS placableAffine.q placableAffine.KS placableAffine.Ms ∧
    4 * plRicD placableAffine.βS placableAffine.dhi
        * plRicN placableAffine.βS placableAffine.q placableAffine.r placableAffine.KS
            placableAffine.Mx placableAffine.Mm placableAffine.Ms
      ≤ plRicL placableAffine.βS placableAffine.q placableAffine.r placableAffine.ghi
          placableAffine.dhi placableAffine.KS placableAffine.Mx placableAffine.Mm
          placableAffine.Ms ^ 2 := by
  norm_num [plRicQ, plRicL, plRicN, plRicD, plRicA, plRicB, plRicC, plRicH,
    PlacableEconomyF.KS, plKS, placableAffine]

/-- **The discriminant condition at the non-affine member**: `Q = 3`,
`L = 1623/700`, `N = 25/28`, `D = 9/50`. -/
theorem placableQuadDiag_riccati_feasible :
    0 < plRicQ placableQuadDiag.βS placableQuadDiag.q placableQuadDiag.KS placableQuadDiag.Ms ∧
    0 < plRicL placableQuadDiag.βS placableQuadDiag.q placableQuadDiag.r placableQuadDiag.ghi
        placableQuadDiag.dhi placableQuadDiag.KS placableQuadDiag.Mx placableQuadDiag.Mm
        placableQuadDiag.Ms ∧
    plRicL placableQuadDiag.βS placableQuadDiag.q placableQuadDiag.r placableQuadDiag.ghi
        placableQuadDiag.dhi placableQuadDiag.KS placableQuadDiag.Mx placableQuadDiag.Mm
        placableQuadDiag.Ms
      < 2 * plRicQ placableQuadDiag.βS placableQuadDiag.q placableQuadDiag.KS placableQuadDiag.Ms ∧
    4 * plRicD placableQuadDiag.βS placableQuadDiag.dhi
        * plRicN placableQuadDiag.βS placableQuadDiag.q placableQuadDiag.r placableQuadDiag.KS
            placableQuadDiag.Mx placableQuadDiag.Mm placableQuadDiag.Ms
      ≤ plRicL placableQuadDiag.βS placableQuadDiag.q placableQuadDiag.r placableQuadDiag.ghi
          placableQuadDiag.dhi placableQuadDiag.KS placableQuadDiag.Mx placableQuadDiag.Mm
          placableQuadDiag.Ms ^ 2 := by
  norm_num [plRicQ, plRicL, plRicN, plRicD, plRicA, plRicB, plRicC, plRicH,
    PlacableEconomyF.KS, plKS, placableQuadDiag]

/-! ## 3. What the members deliver

The members are quadratic–linear coefficient points; every result below reads
them as chord economies through the smart constructor `toChord` (round AU), so
each is a one-line instance of the abstract theorem. The member-level forms of
the three hypotheses translate once: the loss-offset margin by
`toChord_lossOffset`, placability by `Iff.rfl`, the stage flip by
`toChord_flip_iff`. Since renovation item BJ2.3 (2026-10-07) interiority and the stage
relief margin translate the same way (`toChord_interior`, `toChord_stageRelief`), and the
loss-offset margin and the flip read the floor condition `u₀ ≤ q`, which interiority
gives (`u₀_le_q`); the chord forms are the `…_chord…` lemmas below. -/

/-- The affine member's stage flip in the chord form `ℓ_hi < b·p_lo`. -/
theorem placableAffine_chordFlip :
    placableAffine.toChord.ℓhi < placableAffine.toChord.sfloor * placableAffine.toChord.plo :=
  (placableAffine.toChord_flip_iff (placableAffine.u₀_le_q placableAffine_interior)).2
    placableAffine_flip

/-- The non-affine member's stage flip in the chord form. -/
theorem placableQuadDiag_chordFlip :
    placableQuadDiag.toChord.ℓhi
      < placableQuadDiag.toChord.sfloor * placableQuadDiag.toChord.plo :=
  (placableQuadDiag.toChord_flip_iff (placableQuadDiag.u₀_le_q placableQuadDiag_interior)).2
    placableQuadDiag_flip

/-- The affine member's interiority in the chord form (renovation item BJ2.3).
Affine-restricted. -/
theorem placableAffine_chordInterior : placableAffine.toChord.Interior :=
  placableAffine.toChord_interior placableAffine_interior

/-- The non-affine member's interiority in the chord form (renovation item BJ2.3). -/
theorem placableQuadDiag_chordInterior : placableQuadDiag.toChord.Interior :=
  placableQuadDiag.toChord_interior placableQuadDiag_interior

/-- The affine member's stage relief margin in the chord form (renovation item BJ2.3).
Affine-restricted. -/
theorem placableAffine_chordStageRelief : placableAffine.toChord.StageRelief :=
  placableAffine.toChord_stageRelief placableAffine_stageRelief

/-- The non-affine member's stage relief margin in the chord form (renovation item
BJ2.3). -/
theorem placableQuadDiag_chordStageRelief : placableQuadDiag.toChord.StageRelief :=
  placableQuadDiag.toChord_stageRelief placableQuadDiag_stageRelief

/-- The affine member's loss-offset margin in the chord form; the floor condition
`u₀ ≤ q` comes from interiority (renovation item BJ2.3). Affine-restricted. -/
theorem placableAffine_chordLossOffset : placableAffine.toChord.LossOffset :=
  placableAffine.toChord_lossOffset (placableAffine.u₀_le_q placableAffine_interior)
    placableAffine_margin

/-- The non-affine member's loss-offset margin in the chord form (renovation item
BJ2.3). -/
theorem placableQuadDiag_chordLossOffset : placableQuadDiag.toChord.LossOffset :=
  placableQuadDiag.toChord_lossOffset (placableQuadDiag.u₀_le_q placableQuadDiag_interior)
    placableQuadDiag_margin

/-- At the affine member, the Sender channel is active at the constructed
equilibrium value at every state. -/
theorem placableAffine_sender_channel_active :
    ∀ x ∈ Sanctions.I,
      placableAffine.toChord.toParams.ContinuationChangesSenderChoiceAt
        placableAffine.toChord.VSstar x 0 :=
  fun _ hx => placableAffine.toChord.sender_channel_active
    (placableAffine.toChord.uhi_lt_q placableAffine_chordInterior) hx

/-- At the non-affine member, the Sender channel is active at the constructed
equilibrium value at every state. -/
theorem placableQuadDiag_sender_channel_active :
    ∀ x ∈ Sanctions.I,
      placableQuadDiag.toChord.toParams.ContinuationChangesSenderChoiceAt
        placableQuadDiag.toChord.VSstar x 0 :=
  fun _ hx => placableQuadDiag.toChord.sender_channel_active
    (placableQuadDiag.toChord.uhi_lt_q placableQuadDiag_chordInterior) hx

/-- At the non-affine member, the Target channel is active at every carrier
pair and every state. -/
theorem placableQuadDiag_target_channel_active {V_T : ChordEconomy.Val}
    (hV_T : V_T ∈ placableQuadDiag.toChord.carrierT) {V_S : ChordEconomy.Val}
    (hV_S : V_S ∈ placableQuadDiag.toChord.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    placableQuadDiag.toChord.toParams.ContinuationChangesTargetChoiceAt
      (fun y b => placableQuadDiag.toChord.response V_S y b) V_T x :=
  placableQuadDiag.toChord.target_channel_active_on_carriers
    placableQuadDiag_chordLossOffset placableQuadDiag_placable
    placableQuadDiag_chordFlip hV_T hV_S hx

end

/-! ## 4. Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomy.sender_channel_active
#print axioms Sanctions.Examples.ChordEconomyRelief.target_channel_active_on_carriers
#print axioms Sanctions.Examples.ChordEconomy.VSstar_fix
#print axioms Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_response_monotone
#print axioms Sanctions.Examples.placableAffine_sender_channel_active
#print axioms Sanctions.Examples.placableQuadDiag_sender_channel_active
#print axioms Sanctions.Examples.placableQuadDiag_F_ne_affineF

/-! ## Rung 3: the composed equilibrium, unconditional at both members

Both members are *flat* — affine state sections or convex ones, no mixed
curvature, and the family's stage payoff is affine in the state — so the margin
is `0 ≤ r_lo` and the composed top-selector equilibrium carries no hypothesis at
all. -/

/-- **The affine member has the composed top-selector equilibrium**, with both
continuation channels active, unconditionally. -/
noncomputable def placableAffine_equilibriumTop :
    placableAffine.toChord.toParams.FeedbackStackelbergEquilibriumTop :=
  placableAffine.toChord.equilibriumTop_of_flat
    placableAffine_chordLossOffset rfl rfl rfl

theorem placableAffine_both_channels_active :
    ∀ x ∈ Sanctions.I,
      placableAffine.toChord.toParams.ContinuationChangesSenderChoiceAt
        placableAffine_equilibriumTop.V_S x (placableAffine_equilibriumTop.α x)
      ∧ placableAffine.toChord.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => placableAffine.toChord.response placableAffine_equilibriumTop.V_S y b)
          placableAffine_equilibriumTop.V_T x :=
  placableAffine.toChord.both_channels_active_of_flat
    (placableAffine.toChord.uhi_lt_q placableAffine_chordInterior)
    placableAffine_chordLossOffset placableAffine_placable
    placableAffine_chordFlip rfl rfl rfl

/-- **The non-affine member has the composed top-selector equilibrium**, with
both continuation channels active, unconditionally — at a transition that is
not the affine law at any rate. -/
noncomputable def placableQuadDiag_equilibriumTop :
    placableQuadDiag.toChord.toParams.FeedbackStackelbergEquilibriumTop :=
  placableQuadDiag.toChord.equilibriumTop_of_flat
    placableQuadDiag_chordLossOffset rfl rfl rfl

theorem placableQuadDiag_both_channels_active :
    ∀ x ∈ Sanctions.I,
      placableQuadDiag.toChord.toParams.ContinuationChangesSenderChoiceAt
        placableQuadDiag_equilibriumTop.V_S x (placableQuadDiag_equilibriumTop.α x)
      ∧ placableQuadDiag.toChord.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => placableQuadDiag.toChord.response placableQuadDiag_equilibriumTop.V_S y b)
          placableQuadDiag_equilibriumTop.V_T x :=
  placableQuadDiag.toChord.both_channels_active_of_flat
    (placableQuadDiag.toChord.uhi_lt_q placableQuadDiag_chordInterior)
    placableQuadDiag_chordLossOffset placableQuadDiag_placable
    placableQuadDiag_chordFlip rfl rfl rfl

#print axioms Sanctions.Examples.ChordEconomyTwoSided.responsePath_monotoneOn_of_margin
#print axioms Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin
#print axioms Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_stage
#print axioms Sanctions.Examples.placableAffine_both_channels_active
#print axioms Sanctions.Examples.placableQuadDiag_both_channels_active

/-! ## Rung 5: the re-solved regime separation at both members, and the closed
loop as a contraction at the affine one

Both members are flat, so the composed forward-looking equilibrium carries no
hypothesis, and the capstone `myopic_dynamic_equilibrium_separation_generalF`
instantiates at each with none either. What each instantiation licenses (Rule
9A): the class is inhabited, at an affine and at a proved non-affine
transition; nothing about typicality. -/

/-- The affine member's margin, discharged by flatness. -/
theorem placableAffine_rallyMargin :
    placableAffine.toChord.β_S * (placableAffine.toChord.SigC * placableAffine.toChord.ghi
        * placableAffine.toChord.dhi
      + (placableAffine.toChord.KS + 2 * placableAffine.toChord.SigC)
        * placableAffine.toChord.Mmix) ≤ placableAffine.toChord.rlo :=
  placableAffine.toChord.margin_of_flat rfl rfl rfl

/-- The non-affine member's margin, discharged by flatness. -/
theorem placableQuadDiag_rallyMargin :
    placableQuadDiag.toChord.β_S * (placableQuadDiag.toChord.SigC * placableQuadDiag.toChord.ghi
        * placableQuadDiag.toChord.dhi
      + (placableQuadDiag.toChord.KS + 2 * placableQuadDiag.toChord.SigC)
        * placableQuadDiag.toChord.Mmix) ≤ placableQuadDiag.toChord.rlo :=
  placableQuadDiag.toChord.margin_of_flat rfl rfl rfl

/-- The affine member's sanction floor `b = σ(0,0) = u₀/q = 1/3`. -/
theorem placableAffine_sfloor : placableAffine.toChord.sfloor = 1/3 := by
  rw [PlacableEconomyF.toChord_sfloor _ (placableAffine.u₀_le_q placableAffine_interior)]
  norm_num [placableAffine]

/-- The non-affine member's sanction floor `1/3`. -/
theorem placableQuadDiag_sfloor : placableQuadDiag.toChord.sfloor = 1/3 := by
  rw [PlacableEconomyF.toChord_sfloor _ (placableQuadDiag.u₀_le_q placableQuadDiag_interior)]
  norm_num [placableQuadDiag]

/-- The affine member's sanction cap `A/q = 2/3`. -/
theorem placableAffine_cap : placableAffine.toChord.cap = 2/3 := by
  norm_num [ChordEconomy.cap, ChordEconomy.A, ChordEconomy.KS, chKS, PlacableEconomyF.toChord,
    placableAffine]

/-- The non-affine member's sanction cap `A/q = 5/7`. -/
theorem placableQuadDiag_cap : placableQuadDiag.toChord.cap = 5/7 := by
  norm_num [ChordEconomy.cap, ChordEconomy.A, ChordEconomy.KS, chKS, PlacableEconomyF.toChord,
    placableQuadDiag]

/-- **Regime separation at the affine member.** Myopic partial compliance in
`(0,1)` with a zero sanction and wash-out to `0`; forward-looking full defiance
with the state strictly above the myopic state at every positive date from a
common start, converging to a steady state `z = ρ(z) ∈ (1/3, 2/3]`. -/
theorem placableAffine_regime_separation :
    (∀ x ∈ Sanctions.I,
      (placableAffine.toChord.myopicEquilibriumTop placableAffine_chordInterior
          placableAffine_chordStageRelief
        placableAffine_placable).α x ∈ Ioo (0 : ℝ) 1 ∧
      placableAffine.toChord.pM.dynamicEquilibriumRule
        (placableAffine.toChord.myopicEquilibriumTop placableAffine_chordInterior
            placableAffine_chordStageRelief
        placableAffine_placable) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I,
      Tendsto ((placableAffine.toChord.myopicPath placableAffine_chordInterior
          placableAffine_chordStageRelief
        placableAffine_placable) x₀) atTop (𝓝 0)) ∧
    (∀ x ∈ Sanctions.I, placableAffine_equilibriumTop.α x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t, 1 ≤ t →
      (placableAffine.toChord.myopicPath placableAffine_chordInterior
          placableAffine_chordStageRelief
        placableAffine_placable) x₀ t
        < placableAffine.toChord.dynamicPath
            placableAffine_chordLossOffset placableAffine_rallyMargin
            x₀ t) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableAffine.toChord.responsePath placableAffine.toChord.VSstar z = z ∧ 1/3 < z ∧
        z ≤ 2/3 ∧
      Tendsto (placableAffine.toChord.dynamicPath
        placableAffine_chordLossOffset placableAffine_rallyMargin x₀)
        atTop (𝓝 z)) := by
  obtain ⟨_, h2, h3, h4, h5⟩ :=
    placableAffine.toChord.myopic_dynamic_equilibrium_separation_generalF
      placableAffine_chordInterior placableAffine_chordStageRelief
      placableAffine_chordLossOffset placableAffine_placable
      placableAffine_rallyMargin
  refine ⟨fun x hx => ⟨(h2 x hx).1, (h2 x hx).2.2⟩, fun x₀ hx₀ => (h3 x₀ hx₀).2,
    fun x hx => (h4 x hx).1, fun x₀ hx₀ => (h5 x₀ hx₀).2.1, fun x₀ hx₀ => ?_⟩
  obtain ⟨z, hz, hfix, hlo, hhi, htend⟩ := (h5 x₀ hx₀).2.2
  refine ⟨z, hz, hfix, ?_, ?_, htend⟩
  · rw [placableAffine_sfloor] at hlo; exact hlo
  · rw [placableAffine_cap] at hhi; exact hhi

/-- **Regime separation at the non-affine member**, at a transition proved not
affine at any rate: the steady state lies in `(1/3, 5/7]`. -/
theorem placableQuadDiag_regime_separation :
    (∀ x ∈ Sanctions.I,
      (placableQuadDiag.toChord.myopicEquilibriumTop placableQuadDiag_chordInterior
          placableQuadDiag_chordStageRelief
        placableQuadDiag_placable).α x
        ∈ Ioo (0 : ℝ) 1 ∧
      placableQuadDiag.toChord.pM.dynamicEquilibriumRule
        (placableQuadDiag.toChord.myopicEquilibriumTop placableQuadDiag_chordInterior
            placableQuadDiag_chordStageRelief
        placableQuadDiag_placable) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I,
      Tendsto ((placableQuadDiag.toChord.myopicPath placableQuadDiag_chordInterior
          placableQuadDiag_chordStageRelief
        placableQuadDiag_placable) x₀) atTop
        (𝓝 0)) ∧
    (∀ x ∈ Sanctions.I, placableQuadDiag_equilibriumTop.α x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t, 1 ≤ t →
      (placableQuadDiag.toChord.myopicPath placableQuadDiag_chordInterior
          placableQuadDiag_chordStageRelief
        placableQuadDiag_placable) x₀ t
        < placableQuadDiag.toChord.dynamicPath
            placableQuadDiag_chordLossOffset
            placableQuadDiag_rallyMargin x₀ t) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableQuadDiag.toChord.responsePath placableQuadDiag.toChord.VSstar z = z ∧ 1/3 < z ∧
        z ≤ 5/7 ∧
      Tendsto (placableQuadDiag.toChord.dynamicPath
        placableQuadDiag_chordLossOffset
        placableQuadDiag_rallyMargin x₀) atTop (𝓝 z)) := by
  obtain ⟨_, h2, h3, h4, h5⟩ :=
    placableQuadDiag.toChord.myopic_dynamic_equilibrium_separation_generalF
      placableQuadDiag_chordInterior placableQuadDiag_chordStageRelief
      placableQuadDiag_chordLossOffset placableQuadDiag_placable
      placableQuadDiag_rallyMargin
  refine ⟨fun x hx => ⟨(h2 x hx).1, (h2 x hx).2.2⟩, fun x₀ hx₀ => (h3 x₀ hx₀).2,
    fun x hx => (h4 x hx).1, fun x₀ hx₀ => (h5 x₀ hx₀).2.1, fun x₀ hx₀ => ?_⟩
  obtain ⟨z, hz, hfix, hlo, hhi, htend⟩ := (h5 x₀ hx₀).2.2
  refine ⟨z, hz, hfix, ?_, ?_, htend⟩
  · rw [placableQuadDiag_sfloor] at hlo; exact hlo
  · rw [placableQuadDiag_cap] at hhi; exact hhi

/-- **The affine member's closed loop is a `43/46`-contraction**: `K_S = 2`,
`μ = 23/8`, `L_resp = 5/8`, `Lip(ρ) ≤ 20/23`, `Lip(G) ≤ 1/2 + (1/2)(20/23)`. -/
theorem placableAffine_Lloop : placableAffine.toChord.Lloop = 43/46 := by
  norm_num [ChordEconomyTwoSided.Lloop, ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp,
    ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, ChordEconomyTwoSided.SigC, chSigC,
    PlacableEconomyF.toChord, placableAffine]

/-- **The non-affine member's factor-four closed-loop constant is `277/235`**, not
below one: the factor-four route is inconclusive there (Rule 9D — not evidence
of two basins, only of an upper bound that does not close). The sharp constant
closes it: `35/47` (`placableQuadDiag_LloopSharp`, round L). -/
theorem placableQuadDiag_Lloop : placableQuadDiag.toChord.Lloop = 277/235 := by
  norm_num [ChordEconomyTwoSided.Lloop, ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp,
    ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, ChordEconomyTwoSided.SigC, chSigC,
    PlacableEconomyF.toChord, placableQuadDiag]

/-- **The affine member's closed loop at the sharp constant**: `14/23` (round L,
doc 80 M1). -/
theorem placableAffine_LloopSharp : placableAffine.toChord.LloopSharp = 14/23 := by
  norm_num [ChordEconomyTwoSided.LloopSharp, ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp,
    ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, ChordEconomyTwoSided.SigC, chSigC,
    PlacableEconomyF.toChord, placableAffine]

/-- **The non-affine member's closed loop contracts at the sharp constant**:
`35/47 < 1`, where the factor-four constant is `277/235` (round L, doc 80 M1; the
reader's round-K validation package, document 01). -/
theorem placableQuadDiag_LloopSharp : placableQuadDiag.toChord.LloopSharp = 35/47 := by
  norm_num [ChordEconomyTwoSided.LloopSharp, ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp,
    ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, ChordEconomyTwoSided.SigC, chSigC,
    PlacableEconomyF.toChord, placableQuadDiag]

/-- **One globally attracting steady state at the affine member**: unique in
`[0,1]`, with sanction equal to state in `(1/3, 2/3]`, and every feasible start's
forward-looking path converges to it. Both channels are active there
(`placableAffine_both_channels_active`) and there is no same-equilibrium
hysteresis: this is the scope certificate of doc 53 §8. Affine-restricted (the
member's transition is `affineF (1/2)`). A pinned headline, kept verbatim; since
renovation item BH3.5 (2026-10-06) the instance of the class theorem
`ChordEconomyRelief.unique_attracting_state_of_sharp_lt_one` at the sharp constant
`14/23` (`placableAffine_LloopSharp`). It was proved through the factor-four constant
`43/46` (`placableAffine_Lloop`), which still holds. -/
theorem placableAffine_unique_attracting_state :
    ∃ z ∈ Sanctions.I, placableAffine.toChord.responsePath placableAffine.toChord.VSstar z = z ∧
      1/3 < z ∧ z ≤ 2/3 ∧
      (∀ y ∈ Sanctions.I, placableAffine.toChord.closedLoop y = y → y = z) ∧
      ∀ x₀ ∈ Sanctions.I,
        Tendsto (placableAffine.toChord.dynamicPath
          (placableAffine.toChord_lossOffset (placableAffine.u₀_le_q placableAffine_interior)
            placableAffine_margin) placableAffine_rallyMargin x₀)
          atTop (𝓝 z) := by
  obtain ⟨z, hz, hfix, hlo, hhi, huniq, hpath⟩ :=
    placableAffine.toChord.unique_attracting_state_of_sharp_lt_one
      (placableAffine.toChord.uhi_lt_q placableAffine_chordInterior)
      placableAffine_chordLossOffset placableAffine_rallyMargin
      (by rw [placableAffine_LloopSharp]; norm_num)
  rw [placableAffine_sfloor] at hlo
  rw [placableAffine_cap] at hhi
  exact ⟨z, hz, hfix, hlo, hhi, huniq, hpath⟩

/-- **Finite shocks are asymptotically irrelevant at the affine member**: two
paths resuming the same equilibrium at states `x` and `y` are within
`(43/46)^n·|x − y|` after `n` periods. -/
theorem placableAffine_finite_shock_asymptotic_irrelevance :
    ∀ x ∈ Sanctions.I, ∀ y ∈ Sanctions.I, ∀ n : ℕ,
      |placableAffine.toChord.closedLoop^[n] x - placableAffine.toChord.closedLoop^[n] y|
        ≤ (43/46 : ℝ) ^ n * |x - y| := by
  intro x hx y hy n
  have h := placableAffine.toChord.closedLoop_iterate_dist_le hx hy n
  rwa [placableAffine_Lloop] at h

/-- **Finite shocks are asymptotically irrelevant at the affine member, at the
sharp rate** `(14/23)^n` (round L). -/
theorem placableAffine_finite_shock_asymptotic_irrelevance_sharp :
    ∀ x ∈ Sanctions.I, ∀ y ∈ Sanctions.I, ∀ n : ℕ,
      |placableAffine.toChord.closedLoop^[n] x - placableAffine.toChord.closedLoop^[n] y|
        ≤ (14/23 : ℝ) ^ n * |x - y| := by
  intro x hx y hy n
  have h := placableAffine.toChord.closedLoop_iterate_dist_le_sharp hx hy n
  rwa [placableAffine_LloopSharp] at h

/-- **One globally attracting steady state at the non-affine member** (round L,
doc 80 M1): at `quadDiagF`, not affine at any rate, the forward-looking closed
loop is a `35/47`-contraction, so its steady state is unique in `[0,1]`, lies in
`(1/3, 5/7]`, has sanction equal to state, and every feasible start's
forward-looking path converges to it. Both channels are active there
(`placableQuadDiag_both_channels_active`): behavioural activation without
same-equilibrium hysteresis, at a member whose transition is not affine. Since
renovation item BH3.5 (2026-10-06) the instance of the class theorem
`ChordEconomyRelief.unique_attracting_state_of_sharp_lt_one`, with its statement
unchanged (since renovation item BJ2.3, up to the loss-offset proof-term argument
`placableQuadDiag_chordLossOffset`). -/
theorem placableQuadDiag_unique_attracting_state :
    ∃ z ∈ Sanctions.I,
      placableQuadDiag.toChord.responsePath placableQuadDiag.toChord.VSstar z = z ∧
      1/3 < z ∧ z ≤ 5/7 ∧
      (∀ y ∈ Sanctions.I, placableQuadDiag.toChord.closedLoop y = y → y = z) ∧
      ∀ x₀ ∈ Sanctions.I,
        Tendsto (placableQuadDiag.toChord.dynamicPath
          (placableQuadDiag.toChord_lossOffset (placableQuadDiag.u₀_le_q placableQuadDiag_interior)
            placableQuadDiag_margin)
          placableQuadDiag_rallyMargin x₀) atTop (𝓝 z) := by
  obtain ⟨z, hz, hfix, hlo, hhi, huniq, hpath⟩ :=
    placableQuadDiag.toChord.unique_attracting_state_of_sharp_lt_one
      (placableQuadDiag.toChord.uhi_lt_q placableQuadDiag_chordInterior)
      placableQuadDiag_chordLossOffset
      placableQuadDiag_rallyMargin (by rw [placableQuadDiag_LloopSharp]; norm_num)
  rw [placableQuadDiag_sfloor] at hlo
  rw [placableQuadDiag_cap] at hhi
  exact ⟨z, hz, hfix, hlo, hhi, huniq, hpath⟩

/-- **Finite shocks are asymptotically irrelevant at the non-affine member**: two
paths resuming the same equilibrium at states `x` and `y` are within
`(35/47)^n·|x − y|` after `n` periods (round L). -/
theorem placableQuadDiag_finite_shock_asymptotic_irrelevance :
    ∀ x ∈ Sanctions.I, ∀ y ∈ Sanctions.I, ∀ n : ℕ,
      |placableQuadDiag.toChord.closedLoop^[n] x - placableQuadDiag.toChord.closedLoop^[n] y|
        ≤ (35/47 : ℝ) ^ n * |x - y| := by
  intro x hx y hy n
  have h := placableQuadDiag.toChord.closedLoop_iterate_dist_le_sharp hx hy n
  rwa [placableQuadDiag_LloopSharp] at h

/-! ## The two members of the enriched subclass (doc 65)

The base members above are what rows 39 and 42 hash. The subclass members
carry the sanction-section modulus that only the reading `01` consumes:
`0` under the affine law, `1/5` at `quadDiagF`. -/

/-- The affine member with its sanction-section modulus `0`. -/
noncomputable def placableAffineCs : PlacableEconomyFcs where
  toPlacableEconomyF := placableAffine
  Mcs := 0
  hMcs0 := by norm_num
  hFcs := affineF_half_cs

/-- The non-affine member with its sanction-section modulus `1/5`. -/
noncomputable def placableQuadDiagCs : PlacableEconomyFcs where
  toPlacableEconomyF := placableQuadDiag
  Mcs := 1/5
  hMcs0 := by norm_num
  hFcs := quadDiagF_cs

theorem placableAffineCs_base : placableAffineCs.toPlacableEconomyF = placableAffine := rfl
theorem placableQuadDiagCs_base :
    placableQuadDiagCs.toPlacableEconomyF = placableQuadDiag := rfl

#print axioms Sanctions.Examples.placableAffine_regime_separation
#print axioms Sanctions.Examples.placableQuadDiag_regime_separation
#print axioms Sanctions.Examples.placableAffine_unique_attracting_state
#print axioms Sanctions.Examples.placableAffine_finite_shock_asymptotic_irrelevance
#print axioms Sanctions.Examples.placableQuadDiag_Lloop
#print axioms Sanctions.Examples.placableAffine_riccati_feasible
#print axioms Sanctions.Examples.placableQuadDiag_riccati_feasible
#print axioms Sanctions.Examples.placableAffine_LloopSharp
#print axioms Sanctions.Examples.placableQuadDiag_LloopSharp
#print axioms Sanctions.Examples.placableAffine_finite_shock_asymptotic_irrelevance_sharp
#print axioms Sanctions.Examples.placableQuadDiag_unique_attracting_state
#print axioms Sanctions.Examples.placableQuadDiag_finite_shock_asymptotic_irrelevance

/-! ## 9. Certificate existence is not certificate interchangeability (round P;
the reader's 2026-09-11 package, document 03 §6)

`sigV_feasible_iff` says a modulus satisfying curvature and closure exists iff
the discriminant condition holds, and the vertex `L/(2D)` certifies. At the
affine member the vertex is `σ_V = 10`, and it does pass both inequalities; but
the sharp loop constant of `closedLoop_unique_attracting_of_sharp_lt_one` is
then exactly `1`, where the supplied `σ_V = 1` gives `14/23`
(`placableAffine_LloopSharp`). Every quantitative bound must use one
consistently chosen modulus; a feasible modulus certifies existence and nothing
else. Rule 9C: the vertex is `(5/2)/(2·(1/8)) = 10` and the loop constant
`1/2 + (1/2)·(7/4)/(7/4)` in exact arithmetic, checked here by `norm_num`. -/

/-- The affine member re-certified at the Riccati vertex `σ_V = 10`: every
other field is `placableAffine`'s; curvature reads `5/4 < 3` and closure
`3 ≤ 10`. -/
noncomputable def placableAffineVertex : PlacableEconomyF :=
  { placableAffine with
    SigV := 10
    hCurv := by norm_num [plKS, placableAffine]
    hSigV := by norm_num [plSigImg, plSig, plRho, plMu, plKS, placableAffine] }

/-- **At the vertex modulus the sharp loop constant is one**, so the contraction
route is unavailable there although the certificate is feasible. -/
theorem placableAffineVertex_LloopSharp : placableAffineVertex.toChord.LloopSharp = 1 := by
  norm_num [ChordEconomyTwoSided.LloopSharp, ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp,
    ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, ChordEconomyTwoSided.SigC, chSigC,
    PlacableEconomyF.toChord, placableAffineVertex, placableAffine]

#print axioms Sanctions.Examples.placableAffineVertex_LloopSharp

end Examples
end Sanctions
