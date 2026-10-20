/-
Sanctions/Foundations/SemiconvexComposition.lean

**Semiconvexity survives composition with a chord-regular map and survives a
supremum.**

External mathematics over abstract functions; nothing here mentions the
sanctions model (Rule 19). The mirror of `SemiconcaveJointComposition` and
`SemiconcaveSup`, for the *lower* curvature cap — with one asymmetry that is the
whole point: a supremum of `c`-semiconvex functions is `c`-semiconvex with **no
Schur term**, because the sup of convex functions is convex. The semiconcave
side needed strong concavity in the maximised variable to pay for the moving
argmax; the semiconvex side needs nothing.

Two-sided carriers are built from both: the semiconcave leg through the sup
lemma with its action-curvature price, the semiconvex leg through the one here
for free. What a two-sided carrier buys is in `CrossDifferenceSemiconvex`.
-/
import Sanctions.Foundations.SemiconcaveSup
import Sanctions.Foundations.SemiconcaveJointComposition

open Set
open Sanctions.Semiconcave Sanctions.TransitionChords

namespace Sanctions

/-! ## Small facts about the chord-form cap -/

/-- A larger modulus is a weaker cap. -/
theorem Semiconcave.SemiconvexOnSet.mono {g : ℝ → ℝ} {A : Set ℝ} {c c' : ℝ}
    (h : SemiconvexOnSet g A c) (hcc : c ≤ c') : SemiconvexOnSet g A c' := by
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hT : 0 ≤ t * (1 - t) * (y₁ - y₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have := h y₁ hy₁ y₂ hy₂ t ht0 ht1
  have := mul_nonneg (sub_nonneg.2 hcc) hT
  linarith

/-- A convex function is `0`-semiconvex: it never rises above its chords. -/
theorem semiconvexOnSet_of_convexOn {g : ℝ → ℝ} {A : Set ℝ}
    (h : ConvexOn ℝ A g) : SemiconvexOnSet g A 0 := by
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have := h.2 hy₁ hy₂ ht0 (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
  simp only [smul_eq_mul] at this
  simp only [zero_div, zero_mul]
  linarith

/-- Semiconvexity adds: the caps sum. -/
theorem Semiconcave.SemiconvexOnSet.add {g₁ g₂ : ℝ → ℝ} {A : Set ℝ} {c₁ c₂ : ℝ}
    (h₁ : SemiconvexOnSet g₁ A c₁) (h₂ : SemiconvexOnSet g₂ A c₂) :
    SemiconvexOnSet (fun y => g₁ y + g₂ y) A (c₁ + c₂) := by
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have e₁ := h₁ y₁ hy₁ y₂ hy₂ t ht0 ht1
  have e₂ := h₂ y₁ hy₁ y₂ hy₂ t ht0 ht1
  simp only
  linarith

/-- Semiconvexity scales by a nonnegative constant. -/
theorem Semiconcave.SemiconvexOnSet.const_mul {g : ℝ → ℝ} {A : Set ℝ} {c β : ℝ}
    (h : SemiconvexOnSet g A c) (hβ : 0 ≤ β) :
    SemiconvexOnSet (fun y => β * g y) A (β * c) := by
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have e := mul_le_mul_of_nonneg_left (h y₁ hy₁ y₂ hy₂ t ht0 ht1) hβ
  simp only
  linarith

/-- An affine function on a set has zero chord defect. -/
theorem semiconvexOnSet_affine {A : Set ℝ} (m b : ℝ) :
    SemiconvexOnSet (fun y => m * y + b) A 0 := by
  intro y₁ _ y₂ _ t _ _
  simp only
  have : m * (t * y₁ + (1 - t) * y₂) + b - (t * (m * y₁ + b) + (1 - t) * (m * y₂ + b)) = 0 := by
    ring
  rw [this]
  simp

/-- Semiconvexity transfers along pointwise equality on the set. -/
theorem Semiconcave.SemiconvexOnSet.congr {g g₂ : ℝ → ℝ} {c : ℝ}
    (h : SemiconvexOnSet g (Icc (0 : ℝ) 1) c) (hgg : ∀ y ∈ Icc (0 : ℝ) 1, g y = g₂ y) :
    SemiconvexOnSet g₂ (Icc (0 : ℝ) 1) c := by
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hmid := mem_Icc_convexComb hy₁ hy₂ ht0 ht1
  rw [← hgg y₁ hy₁, ← hgg y₂ hy₂, ← hgg _ hmid]
  exact h y₁ hy₁ y₂ hy₂ t ht0 ht1

/-! ## Composition with one chord-regular state section -/

/-- **Semiconvexity composes through a Lipschitz section** (general in the
section `G`; round BG-1, 2026-10-06, item BG1.3). If `v` is monotone,
`K`-Lipschitz and `σ_C`-semiconvex on `[0,1]`, and `G` maps `[0,1]` into itself,
moves by at most `ghi` per unit in absolute value, and has its own
semiconvexity `Mcx`, then `v ∘ G` is `(σ_C·ghi² + K·Mcx)`-semiconvex.

Against `semiconvexOnSet_comp_of_stateChord` it drops the chord band
`[glo, ghi]` with `0 ≤ glo` in favour of the absolute bound it implies (`glo`
never reaches the conclusion), and `0 ≤ K` (the Lipschitz bound on `v` gives
it). Monotonicity of `v` stays: it signs the `G`-defect branch. -/
theorem semiconvexOnSet_comp_of_lipschitz {v G : ℝ → ℝ} {σC K ghi Mcx : ℝ}
    (hσ : 0 ≤ σC) (hMcx : 0 ≤ Mcx)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hscx : SemiconvexOnSet v (Icc (0 : ℝ) 1) σC)
    (hGmaps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hGlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |G y₁ - G y₂| ≤ ghi * |y₁ - y₂|)
    (hGcx : SemiconvexOnSet G (Icc (0 : ℝ) 1) Mcx) :
    SemiconvexOnSet (fun y => v (G y)) (Icc (0 : ℝ) 1) (σC * ghi ^ 2 + K * Mcx) := by
  have hK : 0 ≤ K := SemiconcaveComposition.nonneg_of_lipschitz_Icc hlip
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hmid := mem_Icc_convexComb hy₁ hy₂ ht0 ht1
  simp only
  have hG₁ := hGmaps y₁ hy₁
  have hG₂ := hGmaps y₂ hy₂
  have hGm := hGmaps _ hmid
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  have hT : 0 ≤ t * (1 - t) * (y₁ - y₂) ^ 2 := mul_nonneg (mul_nonneg ht0 ht1') (sq_nonneg _)
  have hGcI : t * G y₁ + (1 - t) * G y₂ ∈ Icc (0 : ℝ) 1 := by
    simpa [smul_eq_mul] using convex_Icc (0 : ℝ) 1 hG₁ hG₂ ht0 ht1' (by ring)
  have hv := hscx (G y₁) hG₁ (G y₂) hG₂ t ht0 ht1
  have hGd := hGcx y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hGsq : (G y₁ - G y₂) ^ 2 ≤ ghi ^ 2 * (y₁ - y₂) ^ 2 := by
    have h := hGlip y₁ hy₁ y₂ hy₂
    calc (G y₁ - G y₂) ^ 2 = |G y₁ - G y₂| ^ 2 := (sq_abs _).symm
      _ ≤ (ghi * |y₁ - y₂|) ^ 2 := by gcongr
      _ = ghi ^ 2 * (y₁ - y₂) ^ 2 := by rw [mul_pow, sq_abs]
  have hfirst : v (G (t * y₁ + (1 - t) * y₂)) - v (t * G y₁ + (1 - t) * G y₂)
      ≤ K * (Mcx / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)) := by
    have hnn : 0 ≤ K * (Mcx / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)) :=
      mul_nonneg hK (mul_nonneg (by linarith) hT)
    rcases le_total (G (t * y₁ + (1 - t) * y₂)) (t * G y₁ + (1 - t) * G y₂) with hle | hlt
    · have := hmono hGm hGcI hle
      linarith
    · have h := hlip _ hGm _ hGcI
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ G (t * y₁ + (1 - t) * y₂)
        - (t * G y₁ + (1 - t) * G y₂))] at h
      have h2 := le_abs_self (v (G (t * y₁ + (1 - t) * y₂)) - v (t * G y₁ + (1 - t) * G y₂))
      have h3 := mul_le_mul_of_nonneg_left hGd hK
      linarith
  have hσterm : σC / 2 * (t * (1 - t) * (G y₁ - G y₂) ^ 2)
      ≤ σC / 2 * (t * (1 - t) * (ghi ^ 2 * (y₁ - y₂) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact mul_le_mul_of_nonneg_left hGsq (mul_nonneg ht0 ht1')
  linarith [hv, hfirst, hσterm]

/-- **Semiconvexity composes through a state section** (general in the section
`G`). If `v` is monotone, `K`-Lipschitz and `σ_C`-semiconvex on `[0,1]`, and `G`
maps `[0,1]` into itself with chord band `[glo, ghi]` and its own semiconvexity
`Mcx`, then `v ∘ G` is `(σ_C·ghi² + K·Mcx)`-semiconvex. The `v`-cap pays for the
image chord, the `G`-cap pays through the Lipschitz constant, and monotonicity
of `v` signs the `G`-defect branch.

Since BG1.3 (2026-10-06) this is a wrapper of
`semiconvexOnSet_comp_of_lipschitz`, with its statement unchanged: the band
enters only through `abs_sub_le_of_stateBand`, and `0 ≤ K` (now `_hK`) is not
used. -/
theorem semiconvexOnSet_comp_of_stateChord {v G : ℝ → ℝ} {σC K glo ghi Mcx : ℝ}
    (hσ : 0 ≤ σC) (_hK : 0 ≤ K) (hglo : 0 ≤ glo) (hMcx : 0 ≤ Mcx)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hscx : SemiconvexOnSet v (Icc (0 : ℝ) 1) σC)
    (hGmaps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hband : StateChordBand G glo ghi)
    (hGcx : SemiconvexOnSet G (Icc (0 : ℝ) 1) Mcx) :
    SemiconvexOnSet (fun y => v (G y)) (Icc (0 : ℝ) 1) (σC * ghi ^ 2 + K * Mcx) :=
  semiconvexOnSet_comp_of_lipschitz hσ hMcx hmono hlip hscx hGmaps
    (fun _ hy₁ _ hy₂ => abs_sub_le_of_stateBand hglo hband hy₁ hy₂) hGcx

/-! ## Through the supremum, with no Schur term -/

/-- **A supremum of `c`-semiconvex functions is `c`-semiconvex.** At the
midpoint the maximiser `s*` is attained; the chord cap of `Φ(·, s*)` transfers
to `v` because `Φ(x₁, s*) ≤ v x₁` and `Φ(x₂, s*) ≤ v x₂`. No curvature in the
maximised variable is needed. -/
theorem sup_semiconvexOnSet {Φ : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hΦ : ∀ s ∈ A, SemiconvexOnSet (fun x => Φ x s) (Icc (0 : ℝ) 1) c)
    (hv : ∀ x ∈ Icc (0 : ℝ) 1, IsGreatest (Φ x '' A) (v x)) :
    SemiconvexOnSet v (Icc (0 : ℝ) 1) c := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  have hmid := mem_Icc_convexComb hx₁ hx₂ ht0 ht1
  obtain ⟨s, hs, hΦs⟩ := (hv _ hmid).1
  have h1 : Φ x₁ s ≤ v x₁ := (hv x₁ hx₁).2 ⟨s, hs, rfl⟩
  have h2 : Φ x₂ s ≤ v x₂ := (hv x₂ hx₂).2 ⟨s, hs, rfl⟩
  have hd := hΦ s hs x₁ hx₁ x₂ hx₂ t ht0 ht1
  simp only at hd
  rw [← hΦs]
  have := mul_le_mul_of_nonneg_left h1 ht0
  have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - t)
  linarith

end Sanctions
