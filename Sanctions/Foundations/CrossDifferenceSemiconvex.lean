/-
Sanctions/Foundations/CrossDifferenceSemiconvex.lean

**A value with curvature bounded on both sides, composed with a chord-regular
transition, has a mixed second difference bounded below.**

External mathematics over abstract `v : ℝ → ℝ` and `F : ℝ → ℝ → ℝ`; nothing here
mentions the sanctions model (Rule 19).

*The question.* Write `Φ(x, s) := v (F x s)`. When is
`[Φ(x₂,s₂) − Φ(x₂,s₁)] − [Φ(x₁,s₂) − Φ(x₁,s₁)]` bounded below by a multiple of
`(x₂ − x₁)(s₂ − s₁)`? In the smooth case the cross-partial is
`v″(F)·F_x·F_s + v′(F)·F_xs`, so a *lower* bound on `v″` — semiconvexity — and
bounds on the chords of `F` give it. This file proves the chord-form version,
with no derivative taken anywhere.

*The route.* `W := v + (σ_C/2)·y²` is convex on `[0,1]` when `v` is
`σ_C`-semiconvex (`convexOn_of_semiconvexOnSet`). A convex function has secant
slopes monotone in both endpoints (`convexOn_secant_le_secant_of_le`, two
applications of mathlib `ConvexOn.secant_mono`), so its equal-step increments
are monotone in the base point (`convexOn_incr_le_incr_of_le`). At the four
successor states `D ≤ B`, `D ≤ C`, `B ≤ A`, `C ≤ A` this bounds the
`W`-cross-difference by the Lipschitz cost of the *unequal* steps, which the
mixed chord of `F` controls; converting back from `W` to `v` costs the quadratic
correction, which the state and sanction chords control.

*The constant.* The smooth calculus gives `σ_C·ghi·dhi + K·M`; the chord proof
pays a further `2·σ_C·M` from the cross term of the quadratic correction. The two
coincide when the mixed chord vanishes (`M = 0`) — the affine law, and every
additively separable transition.

*What is not assumed* (round BG-1, 2026-10-06, item BG1.6). The value need not be
monotone: where the earlier proof used monotonicity of `W` for one leftover step,
the Lipschitz bound on `v` prices that step at `K·M·Δx·Δs`, inside the constant
already claimed. The signs `0 ≤ K`, `0 ≤ dhi`, `0 ≤ ghi` and `0 ≤ M` are derived
from the Lipschitz bound, the chord pairs and the mixed chord, not assumed.
Everything stays general in `F`.
-/
import Sanctions.Foundations.SemiconcaveSup
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.SemiconcaveRiccati
import Sanctions.Foundations.SemiconcaveJointComposition

open Set
open Sanctions.Semiconcave Sanctions.TransitionChords

namespace Sanctions

/-- **Two-sided mixed chord.** The state increment of `F` changes by at most
`M·|Δx|·|Δs|` across a sanction increment — a chord-form bound on the mixed
second difference `F_xs`, with no functional form. Zero for the affine law and
for every additively separable transition. -/
def MixedChordBound (F : ℝ → ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ ⦃x₁ x₂ s₁ s₂ : ℝ⦄, x₁ ∈ Icc (0 : ℝ) 1 → x₂ ∈ Icc (0 : ℝ) 1 →
    s₁ ∈ Icc (0 : ℝ) 1 → s₂ ∈ Icc (0 : ℝ) 1 →
    |(F x₂ s₂ - F x₁ s₂) - (F x₂ s₁ - F x₁ s₁)| ≤ M * |x₂ - x₁| * |s₂ - s₁|

/-- **The mixed modulus is nonnegative.** At the corners `(0,0)` and `(1,1)` the
bound reads `|…| ≤ M` (round P, 2026-09-11; the reader's R4). The placable
family's raw-data constructor fills its `hMmix0` field with this lemma. This
argument is specific to the *absolute* mixed bound: a one-sided chord
convention could admit a negative modulus. -/
theorem MixedChordBound.nonneg {F : ℝ → ℝ → ℝ} {M : ℝ}
    (h : MixedChordBound F M) : 0 ≤ M := by
  have h01 := h (x₁ := 0) (x₂ := 1) (s₁ := 0) (s₂ := 1) ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  simp only [sub_zero, abs_one, mul_one] at h01
  exact le_trans (abs_nonneg _) h01

/-! ## Chord-form semiconvexity is convexity of the quadratically corrected function -/

/-- **`σ`-semiconvex in chord form means `v + (σ/2)·y²` is convex.** The identity
`t·y₁² + (1−t)·y₂² − (t·y₁ + (1−t)·y₂)² = t(1−t)(y₁ − y₂)²` turns the chord
defect cap into the convexity inequality. -/
theorem convexOn_of_semiconvexOnSet {v : ℝ → ℝ} {c : ℝ}
    (h : SemiconvexOnSet v (Icc (0 : ℝ) 1) c) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun y => v y + c / 2 * y ^ 2) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hd := h y₁ hy₁ y₂ hy₂ a ha (by linarith)
  have hid : c / 2 * (a * y₁ + (1 - a) * y₂) ^ 2
      = c / 2 * (a * y₁ ^ 2 + (1 - a) * y₂ ^ 2)
        - c / 2 * (a * (1 - a) * (y₁ - y₂) ^ 2) := by ring
  simp only [smul_eq_mul]
  linarith [hd, hid]

/-! ## Secant slopes of a convex function are monotone in both endpoints -/

/-- **Both endpoints to the right, the secant slope rises.** Two applications of
mathlib `ConvexOn.secant_mono`: first the right endpoint moves with the left
fixed, then the left endpoint moves with the right fixed (read from the right
endpoint, which flips both signs). -/
theorem convexOn_secant_le_secant_of_le {W : ℝ → ℝ} {S : Set ℝ} (hW : ConvexOn ℝ S W)
    {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : x₁ ∈ S) (hy₁ : y₁ ∈ S) (hx₂ : x₂ ∈ S) (hy₂ : y₂ ∈ S)
    (h₁ : x₁ < y₁) (h₂ : x₂ < y₂) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    (W y₁ - W x₁) / (y₁ - x₁) ≤ (W y₂ - W x₂) / (y₂ - x₂) := by
  have hx₁y₂ : x₁ < y₂ := lt_of_lt_of_le h₁ hy
  have hA : (W y₁ - W x₁) / (y₁ - x₁) ≤ (W y₂ - W x₁) / (y₂ - x₁) :=
    hW.secant_mono hx₁ hy₁ hy₂ (ne_of_gt h₁) (ne_of_gt hx₁y₂) hy
  have hB : (W x₁ - W y₂) / (x₁ - y₂) ≤ (W x₂ - W y₂) / (x₂ - y₂) :=
    hW.secant_mono hy₂ hx₁ hx₂ (ne_of_lt hx₁y₂) (ne_of_lt h₂) hx
  have e1 : (W x₁ - W y₂) / (x₁ - y₂) = (W y₂ - W x₁) / (y₂ - x₁) := by
    rw [← neg_sub (W y₂) (W x₁), ← neg_sub y₂ x₁, neg_div_neg_eq]
  have e2 : (W x₂ - W y₂) / (x₂ - y₂) = (W y₂ - W x₂) / (y₂ - x₂) := by
    rw [← neg_sub (W y₂) (W x₂), ← neg_sub y₂ x₂, neg_div_neg_eq]
  rw [e1, e2] at hB
  exact hA.trans hB

/-- **Equal-step increments of a convex function are monotone in the base
point.** For `a ≤ b` and a common step `h ≥ 0`,
`W(a + h) − W(a) ≤ W(b + h) − W(b)`. -/
theorem convexOn_incr_le_incr_of_le {W : ℝ → ℝ} {S : Set ℝ} (hW : ConvexOn ℝ S W)
    {a b h : ℝ} (ha : a ∈ S) (hah : a + h ∈ S) (hb : b ∈ S) (hbh : b + h ∈ S)
    (hab : a ≤ b) (hh : 0 ≤ h) :
    W (a + h) - W a ≤ W (b + h) - W b := by
  rcases hh.eq_or_lt with rfl | hpos
  · simp
  have hs := convexOn_secant_le_secant_of_le hW ha hah hb hbh (by linarith) (by linarith) hab
    (by linarith)
  have e1 : a + h - a = h := by ring
  have e2 : b + h - b = h := by ring
  rw [e1, e2] at hs
  rwa [div_le_div_iff_of_pos_right hpos] at hs

/-! ## The mixed second difference -/

/-- **The mixed second difference of `v ∘ F` is bounded below** (general in
`F`). For `v` `K`-Lipschitz and `σ_C`-semiconvex on `[0,1]`, and `F` with state
band `[glo, ghi]`, sanction chords `[dlo, dhi]` and mixed chord `M`:
for `x₁ ≤ x₂` and `s₁ ≤ s₂`,

    [v(F x₂ s₂) − v(F x₂ s₁)] − [v(F x₁ s₂) − v(F x₁ s₁)]
        ≥ −(σ_C·ghi·dhi + (K + 2σ_C)·M) · (x₂ − x₁) · (s₂ − s₁).

This is what makes a forward-looking objective `stage + β·v(F x s)` have
increasing differences in (sanction, state) once the stage complementarity
covers the constant: saturation of the continuation (`σ_C`) and
cross-effectiveness of the transition (`M`) are the two forces it must
outweigh.

Since BG1.6 (2026-10-06) `v` need not be monotone: the one step that used it is
priced by the Lipschitz bound instead, at no cost to the constant. `0 ≤ K`,
`0 ≤ dhi` and `0 ≤ M` are derived (from `hlip`, the chord pair with `0 ≤ dlo`,
and `MixedChordBound.nonneg`), not assumed. -/
theorem crossDiff_comp_ge_of_semiconvex
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σC K glo ghi dlo dhi M : ℝ}
    (hσ : 0 ≤ σC) (hglo : 0 ≤ glo) (hdlo : 0 ≤ dlo)
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hscx : SemiconvexOnSet v (Icc (0 : ℝ) 1) σC)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hband : StateChordBandAll F glo ghi)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi)
    (hmix : MixedChordBound F M)
    {x₁ x₂ s₁ s₂ : ℝ} (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hx : x₁ ≤ x₂) (hs : s₁ ≤ s₂) :
    -((σC * ghi * dhi + (K + 2 * σC) * M) * (x₂ - x₁) * (s₂ - s₁))
      ≤ (v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁)) := by
  -- The three signs, read off the hypotheses that imply them.
  have hK : 0 ≤ K := SemiconcaveComposition.nonneg_of_lipschitz_Icc hlip
  have hdhi : 0 ≤ dhi := hdlo.trans (sanctionChord_rates_le hlo hhi)
  have hM : 0 ≤ M := hmix.nonneg
  -- Collect every fact about the four successor states, then forget `F`.
  have hDI := hFmaps x₁ hx₁ s₁ hs₁
  have hBI := hFmaps x₂ hx₂ s₁ hs₁
  have hCI := hFmaps x₁ hx₁ s₂ hs₂
  have hAI := hFmaps x₂ hx₂ s₂ hs₂
  have hBD := hband s₁ hs₁ x₁ hx₁ x₂ hx₂ hx
  have hAC := hband s₂ hs₂ x₁ hx₁ x₂ hx₂ hx
  simp only at hBD hAC
  obtain ⟨hBD1, hBD2⟩ := hBD
  obtain ⟨hAC1, hAC2⟩ := hAC
  have hAB1 := hlo hx₂ hs₁ hs₂ hs
  have hAB2 := hhi hx₂ hs₁ hs₂ hs
  have hCD1 := hlo hx₁ hs₁ hs₂ hs
  have hCD2 := hhi hx₁ hs₁ hs₂ hs
  have hmixed := hmix hx₁ hx₂ hs₁ hs₂
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x₂ - x₁),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₂ - s₁)] at hmixed
  have hre : (F x₂ s₂ - F x₁ s₂) - (F x₂ s₁ - F x₁ s₁)
      = (F x₂ s₂ - F x₂ s₁) - (F x₁ s₂ - F x₁ s₁) := by ring
  rw [hre] at hmixed
  obtain ⟨hmix1, hmix2⟩ := abs_le.mp hmixed
  generalize F x₁ s₁ = D at *
  generalize F x₂ s₁ = B at *
  generalize F x₁ s₂ = C at *
  generalize F x₂ s₂ = A at *
  -- The corrected function `W` and its two properties on `[0,1]`.
  have hWconv := convexOn_of_semiconvexOnSet hscx
  have hWlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      (v y₂ + σC / 2 * y₂ ^ 2) - (v y₁ + σC / 2 * y₁ ^ 2) ≤ (K + σC) * (y₂ - y₁) := by
    intro y₁ hy₁ y₂ hy₂ hle
    have h1 := hlip y₂ hy₂ y₁ hy₁
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₂ - y₁)] at h1
    have h2 := le_abs_self (v y₂ - v y₁)
    have h3 : y₂ ^ 2 - y₁ ^ 2 ≤ 2 * (y₂ - y₁) := by
      have := mul_le_mul_of_nonneg_left (by linarith [hy₁.2, hy₂.2] : y₂ + y₁ ≤ 2)
        (by linarith : (0 : ℝ) ≤ y₂ - y₁)
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ σC / 2)
    linarith
  have hdx : 0 ≤ x₂ - x₁ := by linarith
  have hds : 0 ≤ s₂ - s₁ := by linarith
  have hdlods := mul_nonneg hdlo hds
  have hglodx := mul_nonneg hglo hdx
  have hAB0 : 0 ≤ A - B := by linarith
  have hCD0 : 0 ≤ C - D := by linarith
  have hDB : D ≤ B := by linarith
  -- The `W`-cross-difference is bounded by the Lipschitz cost of the unequal steps.
  have hWcross : -((K + σC) * (M * (x₂ - x₁) * (s₂ - s₁)))
      ≤ ((v A + σC / 2 * A ^ 2) - (v B + σC / 2 * B ^ 2))
        - ((v C + σC / 2 * C ^ 2) - (v D + σC / 2 * D ^ 2)) := by
    have hKσM : 0 ≤ (K + σC) * (M * (x₂ - x₁) * (s₂ - s₁)) :=
      mul_nonneg (by linarith) (mul_nonneg (mul_nonneg hM hdx) hds)
    rcases le_total (C - D) (A - B) with hle | hlt
    · -- equal step `C − D` from `D` and from `B`; then `B + (C − D) ≤ A`, and the
      -- leftover step up to `A` loses at most its Lipschitz price `K·M·Δx·Δs`.
      have hPI : B + (C - D) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hBI.1], by linarith [hAI.2]⟩
      have hCI' : D + (C - D) ∈ Icc (0 : ℝ) 1 := by
        rw [show D + (C - D) = C by ring]; exact hCI
      have hstep := convexOn_incr_le_incr_of_le hWconv hDI hCI' hBI hPI hDB hCD0
      simp only at hstep
      rw [show D + (C - D) = C by ring] at hstep
      have hPA : B + (C - D) ≤ A := by linarith
      have hlipPA := hlip A hAI _ hPI
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ A - (B + (C - D)))] at hlipPA
      have hvPA := neg_abs_le (v A - v (B + (C - D)))
      have hsqPA : 0 ≤ σC / 2 * (A ^ 2 - (B + (C - D)) ^ 2) :=
        mul_nonneg (by linarith) (by nlinarith [hPI.1, hAI.1])
      have hgap : A - (B + (C - D)) ≤ M * (x₂ - x₁) * (s₂ - s₁) := by linarith
      have hKgap := mul_le_mul_of_nonneg_left hgap hK
      have hσMg := mul_nonneg hσ (mul_nonneg (mul_nonneg hM hdx) hds)
      linarith
    · -- equal step `A − B` from `D` and from `B`; the leftover `C − (D + (A − B))` is Lipschitz.
      have hQI : D + (A - B) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hDI.1], by linarith [hCI.2]⟩
      have hAI' : B + (A - B) ∈ Icc (0 : ℝ) 1 := by
        rw [show B + (A - B) = A by ring]; exact hAI
      have hstep := convexOn_incr_le_incr_of_le hWconv hDI hQI hBI hAI' hDB hAB0
      simp only at hstep
      rw [show B + (A - B) = A by ring] at hstep
      have hlipQ := hWlip _ hQI _ hCI (by linarith)
      have hgap : (C - (D + (A - B))) ≤ M * (x₂ - x₁) * (s₂ - s₁) := by linarith
      have := mul_le_mul_of_nonneg_left hgap (by linarith : (0 : ℝ) ≤ K + σC)
      linarith
  -- The quadratic correction.
  have hsum : 0 ≤ A + B - C - D := by linarith
  have hsum2 : A + B - C - D ≤ 2 * ghi * (x₂ - x₁) := by linarith
  have ht1 : (A - B) * (A + B - C - D) ≤ (dhi * (s₂ - s₁)) * (2 * ghi * (x₂ - x₁)) :=
    mul_le_mul hAB2 hsum2 hsum (mul_nonneg hdhi hds)
  have hCDsum : C + D ≤ 2 := by linarith [hCI.2, hDI.2]
  have hCDnn : 0 ≤ C + D := by linarith [hCI.1, hDI.1]
  have ht2 : ((A - B) - (C - D)) * (C + D) ≤ (M * (x₂ - x₁) * (s₂ - s₁)) * 2 := by
    calc ((A - B) - (C - D)) * (C + D) ≤ |(A - B) - (C - D)| * (C + D) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hCDnn
      _ ≤ (M * (x₂ - x₁) * (s₂ - s₁)) * 2 :=
          mul_le_mul hmixed hCDsum hCDnn (mul_nonneg (mul_nonneg hM hdx) hds)
  have hQ : A ^ 2 - B ^ 2 - C ^ 2 + D ^ 2
      = (A - B) * (A + B - C - D) + ((A - B) - (C - D)) * (C + D) := by ring
  have hQle : σC / 2 * (A ^ 2 - B ^ 2 - C ^ 2 + D ^ 2)
      ≤ σC / 2 * ((dhi * (s₂ - s₁)) * (2 * ghi * (x₂ - x₁))
          + (M * (x₂ - x₁) * (s₂ - s₁)) * 2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [hQ]; linarith
  linarith [hWcross, hQle]

/-! ## The semiconcave mirror, and the two-sided bound

The lower bound above used semiconvexity. Semiconcavity gives the upper bound by
the mirror argument — `W := v − (σ_V/2)y²` is concave, so its equal-step
increments are *antitone* in the base point — and the two together bound the
absolute cross-difference by the larger modulus. That absolute bound is what
makes the state-perturbation of a forward-looking objective Lipschitz in the
sanction, hence (with strong concavity) the argmax Lipschitz in the state. -/

/-- **`σ`-semiconcave in chord form means `v − (σ/2)·y²` is concave.** -/
theorem concaveOn_of_semiconcaveOnSet {v : ℝ → ℝ} {c : ℝ}
    (h : SemiconcaveOnSet v (Icc (0 : ℝ) 1) c) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun y => v y - c / 2 * y ^ 2) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hd := h y₁ hy₁ y₂ hy₂ a ha (by linarith)
  have hid : c / 2 * (a * y₁ + (1 - a) * y₂) ^ 2
      = c / 2 * (a * y₁ ^ 2 + (1 - a) * y₂ ^ 2)
        - c / 2 * (a * (1 - a) * (y₁ - y₂) ^ 2) := by ring
  simp only [smul_eq_mul]
  linarith [hd, hid]

/-- **The mixed second difference of `v ∘ F` is bounded above** when `v` is
`σ_V`-semiconcave (general in `F`): the mirror of
`crossDiff_comp_ge_of_semiconvex`, with the same constant in `σ_V`. No
monotonicity of `v` is needed on this side. Since BG1.6 (2026-10-06) `0 ≤ K`,
`0 ≤ dhi` and `0 ≤ M` are derived, not assumed. -/
theorem crossDiff_comp_le_of_semiconcave
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV K glo ghi dlo dhi M : ℝ}
    (hσ : 0 ≤ σV) (hglo : 0 ≤ glo) (hdlo : 0 ≤ dlo)
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hband : StateChordBandAll F glo ghi)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi)
    (hmix : MixedChordBound F M)
    {x₁ x₂ s₁ s₂ : ℝ} (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hx : x₁ ≤ x₂) (hs : s₁ ≤ s₂) :
    (v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁))
      ≤ (σV * ghi * dhi + (K + 2 * σV) * M) * (x₂ - x₁) * (s₂ - s₁) := by
  have hK : 0 ≤ K := SemiconcaveComposition.nonneg_of_lipschitz_Icc hlip
  have hdhi : 0 ≤ dhi := hdlo.trans (sanctionChord_rates_le hlo hhi)
  have hM : 0 ≤ M := hmix.nonneg
  have hDI := hFmaps x₁ hx₁ s₁ hs₁
  have hBI := hFmaps x₂ hx₂ s₁ hs₁
  have hCI := hFmaps x₁ hx₁ s₂ hs₂
  have hAI := hFmaps x₂ hx₂ s₂ hs₂
  have hBD := hband s₁ hs₁ x₁ hx₁ x₂ hx₂ hx
  have hAC := hband s₂ hs₂ x₁ hx₁ x₂ hx₂ hx
  simp only at hBD hAC
  obtain ⟨hBD1, hBD2⟩ := hBD
  obtain ⟨hAC1, hAC2⟩ := hAC
  have hAB1 := hlo hx₂ hs₁ hs₂ hs
  have hAB2 := hhi hx₂ hs₁ hs₂ hs
  have hCD1 := hlo hx₁ hs₁ hs₂ hs
  have hCD2 := hhi hx₁ hs₁ hs₂ hs
  have hmixed := hmix hx₁ hx₂ hs₁ hs₂
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x₂ - x₁),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₂ - s₁)] at hmixed
  have hre : (F x₂ s₂ - F x₁ s₂) - (F x₂ s₁ - F x₁ s₁)
      = (F x₂ s₂ - F x₂ s₁) - (F x₁ s₂ - F x₁ s₁) := by ring
  rw [hre] at hmixed
  obtain ⟨hmix1, hmix2⟩ := abs_le.mp hmixed
  generalize F x₁ s₁ = D at *
  generalize F x₂ s₁ = B at *
  generalize F x₁ s₂ = C at *
  generalize F x₂ s₂ = A at *
  have hWconc := concaveOn_of_semiconcaveOnSet hsc
  have hWconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun y => -(v y - σV / 2 * y ^ 2)) := hWconc.neg
  have hsq : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      0 ≤ y₂ ^ 2 - y₁ ^ 2 ∧ y₂ ^ 2 - y₁ ^ 2 ≤ 2 * (y₂ - y₁) := by
    intro y₁ hy₁ y₂ hy₂ hle
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hle) (add_nonneg hy₁.1 hy₂.1)]
    · have := mul_le_mul_of_nonneg_left (by linarith [hy₁.2, hy₂.2] : y₂ + y₁ ≤ 2)
        (by linarith : (0 : ℝ) ≤ y₂ - y₁)
      linarith
  have hWup : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      (v y₂ - σV / 2 * y₂ ^ 2) - (v y₁ - σV / 2 * y₁ ^ 2) ≤ (K + σV) * (y₂ - y₁) := by
    intro y₁ hy₁ y₂ hy₂ hle
    have h1 := hlip y₂ hy₂ y₁ hy₁
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₂ - y₁)] at h1
    have h2 := le_abs_self (v y₂ - v y₁)
    obtain ⟨h3, -⟩ := hsq y₁ hy₁ y₂ hy₂ hle
    have h4 := mul_nonneg (by linarith : (0 : ℝ) ≤ σV / 2) h3
    nlinarith
  have hWdown : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      (v y₁ - σV / 2 * y₁ ^ 2) - (v y₂ - σV / 2 * y₂ ^ 2) ≤ (K + σV) * (y₂ - y₁) := by
    intro y₁ hy₁ y₂ hy₂ hle
    have h1 := hlip y₁ hy₁ y₂ hy₂
    rw [abs_of_nonpos (by linarith : y₁ - y₂ ≤ 0)] at h1
    have h2 := le_abs_self (v y₁ - v y₂)
    obtain ⟨-, h3⟩ := hsq y₁ hy₁ y₂ hy₂ hle
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ σV / 2)
    nlinarith
  have hdx : 0 ≤ x₂ - x₁ := by linarith
  have hds : 0 ≤ s₂ - s₁ := by linarith
  have hdlods := mul_nonneg hdlo hds
  have hglodx := mul_nonneg hglo hdx
  have hAB0 : 0 ≤ A - B := by linarith
  have hCD0 : 0 ≤ C - D := by linarith
  have hDB : D ≤ B := by linarith
  have hWcross : ((v A - σV / 2 * A ^ 2) - (v B - σV / 2 * B ^ 2))
        - ((v C - σV / 2 * C ^ 2) - (v D - σV / 2 * D ^ 2))
      ≤ (K + σV) * (M * (x₂ - x₁) * (s₂ - s₁)) := by
    rcases le_total (A - B) (C - D) with hle | hle
    · have hQI : D + (A - B) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hDI.1], by linarith [hCI.2]⟩
      have hAI' : B + (A - B) ∈ Icc (0 : ℝ) 1 := by
        rw [show B + (A - B) = A by ring]; exact hAI
      have hstep := convexOn_incr_le_incr_of_le hWconv hDI hQI hBI hAI' hDB hAB0
      simp only at hstep
      rw [show B + (A - B) = A by ring] at hstep
      have hlipQ := hWdown _ hQI _ hCI (by linarith)
      have hgap : (C - (D + (A - B))) ≤ M * (x₂ - x₁) * (s₂ - s₁) := by linarith
      have := mul_le_mul_of_nonneg_left hgap (by linarith : (0 : ℝ) ≤ K + σV)
      linarith
    · have hPI : B + (C - D) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hBI.1], by linarith [hAI.2]⟩
      have hCI' : D + (C - D) ∈ Icc (0 : ℝ) 1 := by
        rw [show D + (C - D) = C by ring]; exact hCI
      have hstep := convexOn_incr_le_incr_of_le hWconv hDI hCI' hBI hPI hDB hCD0
      simp only at hstep
      rw [show D + (C - D) = C by ring] at hstep
      have hlipP := hWup _ hPI _ hAI (by linarith)
      have hgap : (A - (B + (C - D))) ≤ M * (x₂ - x₁) * (s₂ - s₁) := by linarith
      have := mul_le_mul_of_nonneg_left hgap (by linarith : (0 : ℝ) ≤ K + σV)
      linarith
  have hsum : 0 ≤ A + B - C - D := by linarith
  have hsum2 : A + B - C - D ≤ 2 * ghi * (x₂ - x₁) := by linarith
  have ht1 : (A - B) * (A + B - C - D) ≤ (dhi * (s₂ - s₁)) * (2 * ghi * (x₂ - x₁)) :=
    mul_le_mul hAB2 hsum2 hsum (mul_nonneg hdhi hds)
  have hCDsum : C + D ≤ 2 := by linarith [hCI.2, hDI.2]
  have hCDnn : 0 ≤ C + D := by linarith [hCI.1, hDI.1]
  have ht2 : ((A - B) - (C - D)) * (C + D) ≤ (M * (x₂ - x₁) * (s₂ - s₁)) * 2 := by
    calc ((A - B) - (C - D)) * (C + D) ≤ |(A - B) - (C - D)| * (C + D) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hCDnn
      _ ≤ (M * (x₂ - x₁) * (s₂ - s₁)) * 2 :=
          mul_le_mul hmixed hCDsum hCDnn (mul_nonneg (mul_nonneg hM hdx) hds)
  have hQ : A ^ 2 - B ^ 2 - C ^ 2 + D ^ 2
      = (A - B) * (A + B - C - D) + ((A - B) - (C - D)) * (C + D) := by ring
  have hQle : σV / 2 * (A ^ 2 - B ^ 2 - C ^ 2 + D ^ 2)
      ≤ σV / 2 * ((dhi * (s₂ - s₁)) * (2 * ghi * (x₂ - x₁))
          + (M * (x₂ - x₁) * (s₂ - s₁)) * 2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [hQ]; linarith
  linarith [hWcross, hQle]

/-- **Two-sided curvature bounds the absolute mixed second difference**, in the
ordered form, by the larger modulus `max σ_V σ_C` (general in `F`). Since BG1.6
(2026-10-06) `v` need not be monotone, and `0 ≤ K`, `0 ≤ ghi`, `0 ≤ dhi` and
`0 ≤ M` are derived from the Lipschitz bound, the two bands and the mixed chord,
not assumed. -/
theorem abs_crossDiff_le_of_twoSided_ordered
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV σC K glo ghi dlo dhi M : ℝ}
    (hσV : 0 ≤ σV) (hσC : 0 ≤ σC) (hglo : 0 ≤ glo) (hdlo : 0 ≤ dlo)
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hscx : SemiconvexOnSet v (Icc (0 : ℝ) 1) σC)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hband : StateChordBandAll F glo ghi)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi)
    (hmix : MixedChordBound F M)
    {x₁ x₂ s₁ s₂ : ℝ} (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hx : x₁ ≤ x₂) (hs : s₁ ≤ s₂) :
    |(v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁))|
      ≤ (max σV σC * ghi * dhi + (K + 2 * max σV σC) * M) * (x₂ - x₁) * (s₂ - s₁) := by
  have hghi : 0 ≤ ghi := hglo.trans hband.rates_le
  have hdhi : 0 ≤ dhi := hdlo.trans (sanctionChord_rates_le hlo hhi)
  have hM : 0 ≤ M := hmix.nonneg
  have hlo' := crossDiff_comp_ge_of_semiconvex hσC hglo hdlo hlip hscx
    hFmaps hband hlo hhi hmix hx₁ hx₂ hs₁ hs₂ hx hs
  have hup := crossDiff_comp_le_of_semiconcave hσV hglo hdlo hlip hsc
    hFmaps hband hlo hhi hmix hx₁ hx₂ hs₁ hs₂ hx hs
  have hdx : 0 ≤ x₂ - x₁ := by linarith
  have hds : 0 ≤ s₂ - s₁ := by linarith
  have hgd := mul_nonneg hghi hdhi
  have hmono_const : ∀ σ : ℝ, σ ≤ max σV σC →
      (σ * ghi * dhi + (K + 2 * σ) * M) * (x₂ - x₁) * (s₂ - s₁)
        ≤ (max σV σC * ghi * dhi + (K + 2 * max σV σC) * M) * (x₂ - x₁) * (s₂ - s₁) := by
    intro σ hσ
    apply mul_le_mul_of_nonneg_right _ hds
    apply mul_le_mul_of_nonneg_right _ hdx
    have h1 := mul_le_mul_of_nonneg_right hσ hgd
    have h2 := mul_le_mul_of_nonneg_right hσ hM
    nlinarith
  rw [abs_le]
  constructor
  · linarith [hmono_const σC (le_max_right _ _)]
  · linarith [hmono_const σV (le_max_left _ _)]

/-- **Two-sided curvature bounds the absolute mixed second difference**, for
states and sanctions in any order (general in `F`): the cross-difference is
antisymmetric under swapping the two states or the two sanctions. Since BG1.6
(2026-10-06) `v` need not be monotone, and `0 ≤ K`, `0 ≤ ghi`, `0 ≤ dhi` and
`0 ≤ M` are derived, not assumed. -/
theorem abs_crossDiff_le_of_twoSided
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV σC K glo ghi dlo dhi M : ℝ}
    (hσV : 0 ≤ σV) (hσC : 0 ≤ σC) (hglo : 0 ≤ glo) (hdlo : 0 ≤ dlo)
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hscx : SemiconvexOnSet v (Icc (0 : ℝ) 1) σC)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hband : StateChordBandAll F glo ghi)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi)
    (hmix : MixedChordBound F M)
    {x₁ x₂ s₁ s₂ : ℝ} (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    |(v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁))|
      ≤ (max σV σC * ghi * dhi + (K + 2 * max σV σC) * M) * |x₂ - x₁| * |s₂ - s₁| := by
  rcases le_total x₁ x₂ with hx | hx <;> rcases le_total s₁ s₂ with hs | hs
  · rw [abs_of_nonneg (sub_nonneg.2 hx), abs_of_nonneg (sub_nonneg.2 hs)]
    exact abs_crossDiff_le_of_twoSided_ordered hσV hσC hglo hdlo hlip
      hsc hscx hFmaps hband hlo hhi hmix hx₁ hx₂ hs₁ hs₂ hx hs
  · rw [abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm s₂ s₁, abs_of_nonneg (sub_nonneg.2 hs)]
    have e : (v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁))
        = -((v (F x₂ s₁) - v (F x₂ s₂)) - (v (F x₁ s₁) - v (F x₁ s₂))) := by ring
    rw [e, abs_neg]
    exact abs_crossDiff_le_of_twoSided_ordered hσV hσC hglo hdlo hlip
      hsc hscx hFmaps hband hlo hhi hmix hx₁ hx₂ hs₂ hs₁ hx hs
  · rw [abs_sub_comm x₂ x₁, abs_of_nonneg (sub_nonneg.2 hx), abs_of_nonneg (sub_nonneg.2 hs)]
    have e : (v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁))
        = -((v (F x₁ s₂) - v (F x₁ s₁)) - (v (F x₂ s₂) - v (F x₂ s₁))) := by ring
    rw [e, abs_neg]
    exact abs_crossDiff_le_of_twoSided_ordered hσV hσC hglo hdlo hlip
      hsc hscx hFmaps hband hlo hhi hmix hx₂ hx₁ hs₁ hs₂ hx hs
  · rw [abs_sub_comm x₂ x₁, abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm s₂ s₁,
      abs_of_nonneg (sub_nonneg.2 hs)]
    have e : (v (F x₂ s₂) - v (F x₂ s₁)) - (v (F x₁ s₂) - v (F x₁ s₁))
        = (v (F x₁ s₁) - v (F x₁ s₂)) - (v (F x₂ s₁) - v (F x₂ s₂)) := by ring
    rw [e]
    exact abs_crossDiff_le_of_twoSided_ordered hσV hσC hglo hdlo hlip
      hsc hscx hFmaps hband hlo hhi hmix hx₂ hx₁ hs₂ hs₁ hx hs

end Sanctions
