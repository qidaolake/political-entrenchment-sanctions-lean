/-
Sanctions/Examples/QuadBumpTransitionChords.lean

**The transition-chord bundle discharged at a genuinely non-affine law.**

`Foundations/TransitionChords.lean` states four sanction-side regularity
predicates over a bare `F : ℝ → ℝ → ℝ`, and `Theory/Basin/TransitionChords.lean`
names them at `Params` and discharges all four *at the affine law*. That left
the curvature predicate in a compromised position: `SanctionSemiconcave` was
witnessed only at `M = 0`, the value the affine law takes, so nothing ruled out
the reading "the predicate is affine-only dressed up as regularity."

This file closes that gap at `quadBumpF`, the quadratic-bump transition of
`QuadBumpCertWitnessMS.lean`

  `F(x,s) = x/2 + s/2 + κ·(s − x)²·(1 − s)`,   `κ = 1/100`

which `qbParams_F_ne_affine` already proves is not the affine law. All four
predicates hold at `qbParams`, with a **strictly positive** curvature modulus:

  lower chord `47/100`, upper chord `53/100`, corner section `γ = 1/2`,
  curvature modulus `M = 3/50`.

## The modulus is 3/50, and it is sharp

For fixed `x`, the on-square section `s ↦ F(x,s)` is a cubic whose chord defect
has an exact closed form (`quadBumpF_chord_defect`):

  `t·F(x,s₁) + (1−t)·F(x,s₂) − F(x, t·s₁+(1−t)·s₂)`
      `= t(1−t)(s₁−s₂)² · κ·[ (1 + 2x) − ((1+t)s₁ + (2−t)s₂) ]`

The bracket is bounded above by `1 + 2x ≤ 3` (the subtracted term is a
nonnegative combination of nonnegative sanctions), so the defect is at most
`3κ · t(1−t)(s₁−s₂)²`, i.e. semiconcavity with modulus `M = 6κ = 3/50`. The
matching second-derivative reading, `∂²F/∂s² = 2κ(1 + 2x − 3s)`, peaks at
`(x,s) = (1,0)` at exactly `6κ`.

The constant is not slack: `quadBumpF_semiconcave_modulus_sharp` shows any
admissible modulus is at least `3/50`, by driving `s₂ → 0` from `x = 1`. In
particular `quadBumpF_not_sanctionSemiconcave_zero` — the affine modulus `0`
is refuted — so the curvature predicate now separates this law from the affine
reference point rather than being satisfied by both at the same constant.

Rule 3: no new assumptions. Every statement is a property of an already-defined
transition, proved from the existing surface (Rule 5's witness-corollary case,
Rule 9A existence certificates).
-/

import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Theory.Basin.TransitionChords

namespace Sanctions

namespace Examples

open Set

noncomputable section

/-! ## 1. The exact chord defect of the quadratic-bump section -/

/-- **Exact chord-defect identity.** On the feasible square the affine part of
`quadBumpF` contributes nothing to a chord defect (it is linear in `s`), so the
whole defect is carried by the bump and factors as a nonnegative weight times a
bracket that is linear in the data.

Economically: the only way the transition can bulge upward along a sanction
chord is through the transience bump, and the size of that bulge is governed by
`(1 + 2x) − ((1+t)s₁ + (2−t)s₂)` — largest at a maximal state with minimal
sanctions, which is exactly the corner where the curvature ceiling binds. -/
theorem quadBumpF_chord_defect {x s₁ s₂ t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * quadBumpF x s₁ + (1 - t) * quadBumpF x s₂
        - quadBumpF x (t * s₁ + (1 - t) * s₂)
      = (t * (1 - t) * (s₁ - s₂) ^ 2)
          * (1/100 * ((1 + 2 * x) - ((1 + t) * s₁ + (2 - t) * s₂))) := by
  have hmid : t * s₁ + (1 - t) * s₂ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have h1 : 0 ≤ t * s₁ := mul_nonneg ht0 hs₁.1
      have h2 : 0 ≤ (1 - t) * s₂ := mul_nonneg (by linarith) hs₂.1
      linarith
    · have h1 : t * s₁ ≤ t * 1 := mul_le_mul_of_nonneg_left hs₁.2 ht0
      have h2 : (1 - t) * s₂ ≤ (1 - t) * 1 :=
        mul_le_mul_of_nonneg_left hs₂.2 (by linarith)
      linarith
  rw [quadBumpF_sq hx hs₁, quadBumpF_sq hx hs₂, quadBumpF_sq hx hmid]
  ring

/-! ## 2. The curvature discharge, and its sharpness -/

/-- **Sanction-side curvature ceiling at `M = 3/50`.** For every physical state
in `[0,1]`, the sanction section of the quadratic-bump transition is semiconcave
on `[0,1]` with modulus `3/50 = 6κ`.

This is the first non-affine discharge of `SanctionSemiconcave`: the affine law
takes `M = 0`, and `quadBumpF_not_sanctionSemiconcave_zero` shows `quadBumpF`
does not. -/
theorem quadBumpF_sanctionSemiconcave :
    Sanctions.TransitionChords.SanctionSemiconcave quadBumpF (3/50) := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hid := quadBumpF_chord_defect hx hs₁ hs₂ ht0 ht1
  have hW : (0:ℝ) ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  -- The bracket never exceeds `3κ`: the subtracted sanction combination is
  -- nonnegative, and `1 + 2x ≤ 3` on the feasible state range.
  have hB : 1/100 * ((1 + 2 * x) - ((1 + t) * s₁ + (2 - t) * s₂)) ≤ 3/100 := by
    have h1 : (0:ℝ) ≤ (1 + t) * s₁ := mul_nonneg (by linarith) hs₁.1
    have h2 : (0:ℝ) ≤ (2 - t) * s₂ := mul_nonneg (by linarith) hs₂.1
    linarith [hx.2]
  have hmul : (t * (1 - t) * (s₁ - s₂) ^ 2)
        * (1/100 * ((1 + 2 * x) - ((1 + t) * s₁ + (2 - t) * s₂)))
      ≤ (t * (1 - t) * (s₁ - s₂) ^ 2) * (3/100) :=
    mul_le_mul_of_nonneg_left hB hW
  simp only
  linarith [hid, hmul]

/-- **The modulus `3/50` is sharp.** Any modulus for which the quadratic-bump
transition is sanction-semiconcave is at least `3/50`.

The witness direction is the corner: from the maximal state `x = 1` with
`s₁ = 0` and `s₂ → 0⁺`, the normalised chord defect tends to `3κ = 3/100`, so
no smaller ceiling survives. Recorded so that no later round "improves" the
constant. -/
theorem quadBumpF_semiconcave_modulus_sharp {M : ℝ}
    (h : Sanctions.TransitionChords.SanctionSemiconcave quadBumpF M) :
    3/50 ≤ M := by
  by_contra hcon
  rw [not_le] at hcon
  set d : ℝ := 3/50 - M with hd
  have hdpos : 0 < d := by simp only [hd]; linarith
  set σ : ℝ := min 1 d with hσ
  have hσpos : 0 < σ := lt_min one_pos hdpos
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσd : σ ≤ d := min_le_right _ _
  have hinst := h 1 ⟨zero_le_one, le_refl 1⟩ 0 ⟨le_refl 0, zero_le_one⟩
      σ ⟨hσpos.le, hσ1⟩ (1/2) (by norm_num) (by norm_num)
  have hid := quadBumpF_chord_defect (x := 1) (s₁ := 0) (s₂ := σ) (t := 1/2)
      ⟨zero_le_one, le_refl 1⟩ ⟨le_refl 0, zero_le_one⟩ ⟨hσpos.le, hσ1⟩
      (by norm_num) (by norm_num)
  simp only at hinst
  rw [hid] at hinst
  have hsq : (0:ℝ) < σ ^ 2 := pow_pos hσpos 2
  nlinarith [hinst, hsq, hσd, hσpos]

/-- **The affine curvature value is refuted.** `quadBumpF` is *not*
semiconcave in the sanction with modulus `0` — so the curvature predicate is
not silently affine-only, and the non-affine discharge above carries real
content. -/
theorem quadBumpF_not_sanctionSemiconcave_zero :
    ¬ Sanctions.TransitionChords.SanctionSemiconcave quadBumpF 0 := by
  intro h
  have := quadBumpF_semiconcave_modulus_sharp h
  norm_num at this

/-! ## 3. The `Params`-level bundle at `qbParams` -/

/-- Curvature ceiling at the witness `Params`. -/
theorem qbParams_sanctionSemiconcave :
    qbParams.SanctionSemiconcaveWith (3/50) :=
  quadBumpF_sanctionSemiconcave

/-- **Lower chord at rate `47/100`**: a unit of extra sanction moves next
period's political state up by at least `0.47`. Below the affine `δ = 1/2`, as
`sanctionLowerChord_le_of_cornerSectionTop` forces for any non-affine law
sharing this corner section. -/
theorem qbParams_sanctionLowerChord :
    qbParams.SanctionLowerChordWith (47/100) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  exact (qbParams_F_s_chord hx hs₁ hs₂ hle).1

/-- **Upper chord at rate `53/100`**: the matching ceiling on the same
movement. -/
theorem qbParams_sanctionUpperChord :
    qbParams.SanctionUpperChordWith (53/100) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  exact (qbParams_F_s_chord hx hs₁ hs₂ hle).2

/-- **Corner section at `γ = 1/2`**: along full sanctions the bump vanishes and
the law is exactly the normalised affine map `y ↦ y/2 + 1/2`. -/
theorem qbParams_cornerSectionTop :
    qbParams.CornerSectionTopWith (1/2) := by
  intro y _
  change quadBumpF y 1 = 1/2 * y + (1 - 1/2)
  rw [quadBumpF_one]; ring

/-- **The whole chord bundle at a provably non-affine transition.** The
non-affine counterpart of `Params.affine_transitionChordPack`, which discharges
the same four predicates at `(δ, δ, 1 − δ, 0)`. Here the curvature slot is
`3/50 > 0` and the chord rates straddle the affine `1/2` rather than coinciding
with it. -/
theorem qbParams_transitionChordPack :
    qbParams.SanctionLowerChordWith (47/100)
      ∧ qbParams.SanctionUpperChordWith (53/100)
      ∧ qbParams.CornerSectionTopWith (1/2)
      ∧ qbParams.SanctionSemiconcaveWith (3/50) :=
  ⟨qbParams_sanctionLowerChord, qbParams_sanctionUpperChord,
   qbParams_cornerSectionTop, qbParams_sanctionSemiconcave⟩

/-- Consistency check against `Foundations`: the chord rate `47/100` respects
the corner-section cap `d ≤ 1 − γ = 1/2`, so the bundle is internally
coherent. -/
theorem qbParams_chord_le_cornerCap : (47/100 : ℝ) ≤ 1 - 1/2 :=
  qbParams.sanctionLowerChord_le_of_cornerSectionTop
    qbParams_cornerSectionTop qbParams_sanctionLowerChord

end

end Examples

end Sanctions
