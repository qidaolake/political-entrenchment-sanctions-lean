/-
Sanctions/Foundations/SemiconvexArgmaxShift.lean

**A lower bound on how far a maximiser moves under a linear perturbation**,
derivative-free.

`Foundations/StrongConcaveArgmaxStability` bounds the movement of the
maximiser of a strongly concave function *from above* under a perturbation.
The reading `01` of the placable class needs the opposite bound: when the
Target complies a little more, the Sender's sanction must fall by *at least*
a proportional amount, or the Target could not be sure that compliance buys
relief. That is a lower bound on the argmax shift, and it needs the objective
to be not too concave — semiconvex with modulus `M` — rather than strongly
concave.

The statement: let `ψ` be `M`-semiconvex on `[0,1]` with an *interior*
maximiser `s'`, and let `s` maximise `ψ + λ·u` for `λ > 0`. Then
`s − s' ≥ min(λ/(2M), (1 − s')/2)`. Interiority is essential: at a boundary
maximiser with negative slope a small `λ` moves nothing.

Chord-form proof. For `ε ∈ [0, 1 − s']` and `η ∈ (0, s']`, the chord of `ψ`
through `s' − η` and `s' + ε` passes over `s'`, and semiconvexity plus
`ψ(s' − η) ≤ ψ(s')` give `ψ(s' + ε) ≥ ψ(s') − (M/2)ε(ε + η)`. Optimality of
`s` against `s' + ε`, with `ψ(s) ≤ ψ(s')`, gives
`λ(s − s') ≥ λε − (M/2)ε(ε + η)`; let `η → 0` and choose
`ε = min(λ/M, 1 − s')`.
-/
import Sanctions.Foundations.SemiconcaveSup

namespace Sanctions
namespace SemiconvexArgmaxShift

open Set Sanctions.Semiconcave

/-- The chord inequality at an interior maximiser of a semiconvex function. -/
theorem le_of_semiconvex_interior_max {ψ : ℝ → ℝ} {M s' ε η : ℝ}
    (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M) (hmax : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hs'0 : 0 < s') (hε0 : 0 ≤ ε) (hε1 : s' + ε ≤ 1) (hη0 : 0 < η) (hη : η ≤ s') :
    ψ s' - M / 2 * (ε * (ε + η)) ≤ ψ (s' + ε) := by
  have hu₁ : s' - η ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hu₂ : s' + ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hε1⟩
  have hden : 0 < ε + η := by linarith
  set t := ε / (ε + η) with ht
  have ht0 : 0 ≤ t := div_nonneg hε0 hden.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
  have h1t_pos : 0 < 1 - t := by
    rw [ht, sub_pos, div_lt_one hden]; linarith
  have hconv : t * (s' - η) + (1 - t) * (s' + ε) = s' := by
    rw [ht]; field_simp; ring
  have h := hψ (s' - η) hu₁ (s' + ε) hu₂ t ht0 ht1
  rw [hconv] at h
  have hψ₁ : ψ (s' - η) ≤ ψ s' := hmax hu₁
  have hsq : ((s' - η) - (s' + ε)) ^ 2 = (ε + η) ^ 2 := by ring
  rw [hsq] at h
  have ht_mul : t * (ε + η) ^ 2 = ε * (ε + η) := by rw [ht]; field_simp
  have key : (1 - t) * (ψ s' - ψ (s' + ε)) ≤ (1 - t) * (M / 2 * (t * (ε + η) ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hψ₁ ht0
    nlinarith [h, this]
  have h2 : ψ s' - ψ (s' + ε) ≤ M / 2 * (t * (ε + η) ^ 2) :=
    le_of_mul_le_mul_left key h1t_pos
  rw [ht_mul] at h2
  linarith

/-- **The argmax moves at least proportionally under a linear perturbation.**
`ψ` is `M`-semiconvex on `[0,1]` with interior maximiser `s'`; `s` maximises
`ψ + λ·u` with `λ > 0`. Then `s − s' ≥ min(λ/(2M), (1 − s')/2)`. -/
theorem argmax_shift_ge_of_semiconvex_linear {ψ : ℝ → ℝ} {M lam s s' : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hs'0 : 0 < s') (hs'1 : s' < 1) (hmax' : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hlam : 0 < lam) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun u => ψ u + lam * u) (Icc (0 : ℝ) 1) s) :
    min (lam / (2 * M)) ((1 - s') / 2) ≤ s - s' := by
  set ε := min (lam / M) (1 - s') with hε
  have hε0 : 0 < ε := lt_min (div_pos hlam hM) (by linarith)
  have hε1 : s' + ε ≤ 1 := by
    have := min_le_right (lam / M) (1 - s'); linarith
  have hstep : ∀ η, 0 < η → η ≤ s' →
      lam * ε - M / 2 * (ε * (ε + η)) ≤ lam * (s - s') := by
    intro η hη0 hη
    have hv := le_of_semiconvex_interior_max hψ hmax' hs'0 hε0.le hε1 hη0 hη
    have hopt : ψ (s' + ε) + lam * (s' + ε) ≤ ψ s + lam * s :=
      hmax (show s' + ε ∈ Icc (0 : ℝ) 1 from ⟨by linarith, hε1⟩)
    have hψs : ψ s ≤ ψ s' := hmax' hs
    linarith
  have hlim : lam * ε - M / 2 * (ε * ε) ≤ lam * (s - s') := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hMε : 0 < M * ε := mul_pos hM hε0
    set η := min s' (2 * δ / (M * ε)) with hη
    have hη0 : 0 < η := lt_min hs'0 (div_pos (by linarith) hMε)
    have hηs : η ≤ s' := min_le_left _ _
    have hηδ : M / 2 * (ε * η) ≤ δ := by
      have hle : η ≤ 2 * δ / (M * ε) := min_le_right _ _
      calc M / 2 * (ε * η) = (M * ε) * η / 2 := by ring
        _ ≤ (M * ε) * (2 * δ / (M * ε)) / 2 := by gcongr
        _ = δ := by field_simp
    have := hstep η hη0 hηs
    nlinarith [this, hηδ]
  rcases le_or_gt (lam / M) (1 - s') with hcase | hcase
  · have hεeq : ε = lam / M := min_eq_left hcase
    have hbound : lam / (2 * M) ≤ s - s' := by
      rw [hεeq] at hlim
      have heq : lam * (lam / M) - M / 2 * (lam / M * (lam / M)) = lam * (lam / (2 * M)) := by
        field_simp; ring
      rw [heq] at hlim
      exact le_of_mul_le_mul_left hlim hlam
    exact le_trans (min_le_left _ _) hbound
  · have hεeq : ε = 1 - s' := min_eq_right hcase.le
    have hMε : M * ε ≤ lam := by
      rw [hεeq]
      have := (lt_div_iff₀ hM).1 hcase
      linarith
    have hbound : (1 - s') / 2 ≤ s - s' := by
      have h1 : M / 2 * (ε * ε) ≤ lam / 2 * ε := by nlinarith [hMε, hε0]
      have h2 : lam * (ε / 2) ≤ lam * (s - s') := by linarith
      have := le_of_mul_le_mul_left h2 hlam
      rw [hεeq] at this
      linarith
    exact le_trans (min_le_right _ _) hbound

/-! ## The sharp form (round I, doc 75 R1)

The coarse bound above loses a factor of two twice: once in the chord (it
evaluates the objective at `s' + ε` for one chosen `ε`) and once in the
truncation. Both losses go away once the chord inequality is read as a
**quadratic lower support** at the interior maximiser:
`ψ(y) ≥ ψ(s') − (M/2)(y − s')²` for every feasible `y`, on both sides of `s'`.
The right side is the existing chord with `η → 0`; the left side is the same
statement for the reflected function `u ↦ ψ(1 − u)`. Applying the support to
`ψ` at `s'` and to `ψ + λu` at `s`, each evaluated at the other maximiser, and
adding, gives `λ(s − s') ≤ M(s − s')²`, hence `s − s' ≥ λ/M` whenever the new
maximiser is interior; at the boundary `s = 1` the shift is `1 − s'`. So

    s − s' ≥ min(λ/M, 1 − s'),

and the quadratic `−(M/2)(u − z)²` attains it, so nothing sharper holds on the
class. Interiority of the *old* maximiser is still essential
(`ψ(u) = −u − u²/2`, tilt `1/2`: both maximisers are `0`). No differentiability,
no continuity, and no hypothesis beyond the coarse theorem's enter. -/

/-- Reflection `u ↦ 1 − u` preserves semiconvexity on `[0,1]`. -/
theorem semiconvexOnSet_reflect {ψ : ℝ → ℝ} {M : ℝ}
    (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M) :
    SemiconvexOnSet (fun u => ψ (1 - u)) (Icc (0 : ℝ) 1) M := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  have h₁ : 1 - x₁ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx₁.2], by linarith [hx₁.1]⟩
  have h₂ : 1 - x₂ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx₂.2], by linarith [hx₂.1]⟩
  have h := hψ (1 - x₁) h₁ (1 - x₂) h₂ t ht0 ht1
  have hc : t * (1 - x₁) + (1 - t) * (1 - x₂) = 1 - (t * x₁ + (1 - t) * x₂) := by ring
  have hsq : (1 - x₁ - (1 - x₂)) ^ 2 = (x₁ - x₂) ^ 2 := by ring
  rw [hc, hsq] at h
  show ψ (1 - (t * x₁ + (1 - t) * x₂)) - (t * ψ (1 - x₁) + (1 - t) * ψ (1 - x₂))
      ≤ M / 2 * (t * (1 - t) * (x₁ - x₂) ^ 2)
  exact h

/-- Adding a linear function preserves semiconvexity with the same modulus. -/
theorem semiconvexOnSet_add_linear {ψ : ℝ → ℝ} {M lam : ℝ}
    (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M) :
    SemiconvexOnSet (fun u => ψ u + lam * u) (Icc (0 : ℝ) 1) M := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  have h := hψ x₁ hx₁ x₂ hx₂ t ht0 ht1
  show ψ (t * x₁ + (1 - t) * x₂) + lam * (t * x₁ + (1 - t) * x₂)
      - (t * (ψ x₁ + lam * x₁) + (1 - t) * (ψ x₂ + lam * x₂))
      ≤ M / 2 * (t * (1 - t) * (x₁ - x₂) ^ 2)
  nlinarith [h]

/-- **Quadratic lower support, right side.** At an interior maximiser `s'` of an
`M`-semiconvex `ψ`, every feasible `y ≥ s'` has `ψ(y) ≥ ψ(s') − (M/2)(y − s')²`.
The chord inequality with `η → 0`. -/
theorem quadratic_support_right_of_semiconvex_interior_max {ψ : ℝ → ℝ} {M s' y : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hmax : IsMaxOn ψ (Icc (0 : ℝ) 1) s') (hs'0 : 0 < s') (hy : s' ≤ y) (hy1 : y ≤ 1) :
    ψ s' - M / 2 * (y - s') ^ 2 ≤ ψ y := by
  rcases eq_or_lt_of_le hy with hey | hlt
  · subst hey; simp
  have hε0 : 0 < y - s' := by linarith
  have hε1 : s' + (y - s') ≤ 1 := by linarith
  have hy' : y = s' + (y - s') := by ring
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hMε : 0 < M * (y - s') := mul_pos hM hε0
  set η := min s' (2 * δ / (M * (y - s'))) with hη
  have hη0 : 0 < η := lt_min hs'0 (div_pos (by linarith) hMε)
  have hηs : η ≤ s' := min_le_left _ _
  have hηδ : M / 2 * ((y - s') * η) ≤ δ := by
    have hle : η ≤ 2 * δ / (M * (y - s')) := min_le_right _ _
    calc M / 2 * ((y - s') * η) = (M * (y - s')) * η / 2 := by ring
      _ ≤ (M * (y - s')) * (2 * δ / (M * (y - s'))) / 2 := by gcongr
      _ = δ := by field_simp
  have h := le_of_semiconvex_interior_max hψ hmax hs'0 hε0.le hε1 hη0 hηs
  rw [← hy'] at h
  nlinarith [h, hηδ]

/-- **Quadratic lower support, left side**, by reflection. -/
theorem quadratic_support_left_of_semiconvex_interior_max {ψ : ℝ → ℝ} {M s' y : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hmax : IsMaxOn ψ (Icc (0 : ℝ) 1) s') (hs'1 : s' < 1) (hy0 : 0 ≤ y) (hy : y ≤ s') :
    ψ s' - M / 2 * (s' - y) ^ 2 ≤ ψ y := by
  have hψ' := semiconvexOnSet_reflect hψ
  have hmax' : IsMaxOn (fun u => ψ (1 - u)) (Icc (0 : ℝ) 1) (1 - s') := by
    intro u hu
    have hu' : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have := hmax hu'
    simpa using this
  have h := quadratic_support_right_of_semiconvex_interior_max hM hψ' hmax'
    (by linarith) (y := 1 - y) (by linarith) (by linarith)
  simp only [sub_sub_cancel] at h
  have hsq : (1 - y - (1 - s')) ^ 2 = (s' - y) ^ 2 := by ring
  rw [hsq] at h
  exact h

/-- **The sharp shift, interior case:** `λ/M ≤ s − s'` when the new maximiser is
interior. -/
theorem argmax_shift_ge_linear_of_semiconvex_interior {ψ : ℝ → ℝ} {M lam s s' : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hs'0 : 0 < s') (hs'1 : s' < 1) (hmax' : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hlam : 0 < lam) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun u => ψ u + lam * u) (Icc (0 : ℝ) 1) s) (hs1 : s < 1) :
    lam / M ≤ s - s' := by
  have hcoarse := argmax_shift_ge_of_semiconvex_linear hM hψ hs'0 hs'1 hmax' hlam hs hmax
  have hd : 0 < s - s' := by
    have : 0 < min (lam / (2 * M)) ((1 - s') / 2) :=
      lt_min (div_pos hlam (by linarith)) (by linarith)
    linarith
  have h1 := quadratic_support_right_of_semiconvex_interior_max hM hψ hmax' hs'0
    (by linarith) hs.2
  have hψ' := semiconvexOnSet_add_linear (lam := lam) hψ
  have h2 := quadratic_support_left_of_semiconvex_interior_max hM hψ' hmax hs1 hs'0.le
    (by linarith)
  simp only at h2
  have hkey : lam * (s - s') ≤ (M * (s - s')) * (s - s') := by nlinarith [h1, h2]
  have hle : lam ≤ M * (s - s') := le_of_mul_le_mul_right hkey hd
  rw [div_le_iff₀ hM]
  linarith

/-- **The sharp shift:** `s − s' ≥ min(λ/M, 1 − s')`, under exactly the coarse
theorem's hypotheses. Attained by `ψ(u) = −(M/2)(u − z)²`. -/
theorem argmax_shift_ge_of_semiconvex_linear_sharp {ψ : ℝ → ℝ} {M lam s s' : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hs'0 : 0 < s') (hs'1 : s' < 1) (hmax' : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hlam : 0 < lam) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun u => ψ u + lam * u) (Icc (0 : ℝ) 1) s) :
    min (lam / M) (1 - s') ≤ s - s' := by
  rcases lt_or_ge s 1 with hs1 | hs1
  · exact le_trans (min_le_left _ _)
      (argmax_shift_ge_linear_of_semiconvex_interior hM hψ hs'0 hs'1 hmax' hlam hs hmax hs1)
  · have h1 : s = 1 := le_antisymm hs.2 hs1
    rw [h1]
    exact min_le_right _ _

/-! ## Nonlinear tilts (round AT, 2026-09-25; doc 104 §7, item 1)

The theorems above take the perturbation to be *linear*, `ψ + λ·u`. A general
payoff perturbs by a function `h − ψ` whose increments are only bounded below,
`(h − ψ)(u₂) − (h − ψ)(u₁) ≥ λ(u₂ − u₁)` for `u₁ ≤ u₂`. The coarse proof reads
the tilt only through that inequality between the new maximiser and one chosen
point; the sharp proof reads it between the two maximisers, together with the
quadratic supports of `ψ` and of `h` (so `h` must be `M`-semiconvex too, as
`ψ + λ·u` is). Both survive with the same constants, and the linear theorems are
the special case `h = ψ + λ·u`. -/

/-- **Coarse shift under a nonlinear tilt.** `ψ` is `M`-semiconvex on `[0,1]`
with interior maximiser `s'`; `s` maximises `h`, and `h − ψ` rises at least at
rate `λ > 0`. Then `s − s' ≥ min(λ/(2M), (1 − s')/2)`. -/
theorem argmax_shift_ge_of_semiconvex_tilt {ψ h : ℝ → ℝ} {M lam s s' : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hs'0 : 0 < s') (hs'1 : s' < 1) (hmax' : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hlam : 0 < lam) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn h (Icc (0 : ℝ) 1) s)
    (htilt : ∀ u₁ ∈ Icc (0 : ℝ) 1, ∀ u₂ ∈ Icc (0 : ℝ) 1, u₁ ≤ u₂ →
      lam * (u₂ - u₁) ≤ (h u₂ - ψ u₂) - (h u₁ - ψ u₁)) :
    min (lam / (2 * M)) ((1 - s') / 2) ≤ s - s' := by
  set ε := min (lam / M) (1 - s') with hε
  have hε0 : 0 < ε := lt_min (div_pos hlam hM) (by linarith)
  have hε1 : s' + ε ≤ 1 := by
    have := min_le_right (lam / M) (1 - s'); linarith
  have hyI : s' + ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hε1⟩
  have hstep : ∀ η, 0 < η → η ≤ s' →
      lam * ε - M / 2 * (ε * (ε + η)) ≤ lam * (s - s') := by
    intro η hη0 hη
    have hMe : 0 ≤ M / 2 * (ε * (ε + η)) := by positivity
    rcases le_or_gt (s' + ε) s with hfar | hnear
    · have : lam * ε ≤ lam * (s - s') := mul_le_mul_of_nonneg_left (by linarith) hlam.le
      linarith
    · have hv := le_of_semiconvex_interior_max hψ hmax' hs'0 hε0.le hε1 hη0 hη
      have hopt : h (s' + ε) ≤ h s := hmax hyI
      have ht := htilt s hs (s' + ε) hyI hnear.le
      have hψs : ψ s ≤ ψ s' := hmax' hs
      nlinarith
  have hlim : lam * ε - M / 2 * (ε * ε) ≤ lam * (s - s') := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hMε : 0 < M * ε := mul_pos hM hε0
    set η := min s' (2 * δ / (M * ε)) with hη
    have hη0 : 0 < η := lt_min hs'0 (div_pos (by linarith) hMε)
    have hηs : η ≤ s' := min_le_left _ _
    have hηδ : M / 2 * (ε * η) ≤ δ := by
      have hle : η ≤ 2 * δ / (M * ε) := min_le_right _ _
      calc M / 2 * (ε * η) = (M * ε) * η / 2 := by ring
        _ ≤ (M * ε) * (2 * δ / (M * ε)) / 2 := by gcongr
        _ = δ := by field_simp
    have := hstep η hη0 hηs
    nlinarith [this, hηδ]
  rcases le_or_gt (lam / M) (1 - s') with hcase | hcase
  · have hεeq : ε = lam / M := min_eq_left hcase
    have hbound : lam / (2 * M) ≤ s - s' := by
      rw [hεeq] at hlim
      have heq : lam * (lam / M) - M / 2 * (lam / M * (lam / M)) = lam * (lam / (2 * M)) := by
        field_simp; ring
      rw [heq] at hlim
      exact le_of_mul_le_mul_left hlim hlam
    exact le_trans (min_le_left _ _) hbound
  · have hεeq : ε = 1 - s' := min_eq_right hcase.le
    have hMε : M * ε ≤ lam := by
      rw [hεeq]
      have := (lt_div_iff₀ hM).1 hcase
      linarith
    have hbound : (1 - s') / 2 ≤ s - s' := by
      have h1 : M / 2 * (ε * ε) ≤ lam / 2 * ε := by nlinarith [hMε, hε0]
      have h2 : lam * (ε / 2) ≤ lam * (s - s') := by linarith
      have := le_of_mul_le_mul_left h2 hlam
      rw [hεeq] at this
      linarith
    exact le_trans (min_le_right _ _) hbound

/-- **Sharp shift under a nonlinear tilt, interior case.** As the coarse theorem,
with `h` also `M`-semiconvex and the new maximiser interior (`s < 1`): then
`λ/M ≤ s − s'`. The quadratic supports of `ψ` at `s'` and of `h` at `s`, each
evaluated at the other maximiser, add up to `λ(s − s') ≤ M(s − s')²`. -/
theorem argmax_shift_ge_tilt_of_semiconvex_interior {ψ h : ℝ → ℝ} {M lam s s' : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hh : SemiconvexOnSet h (Icc (0 : ℝ) 1) M)
    (hs'0 : 0 < s') (hs'1 : s' < 1) (hmax' : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hlam : 0 < lam) (hs : s ∈ Icc (0 : ℝ) 1) (hs1 : s < 1)
    (hmax : IsMaxOn h (Icc (0 : ℝ) 1) s)
    (htilt : ∀ u₁ ∈ Icc (0 : ℝ) 1, ∀ u₂ ∈ Icc (0 : ℝ) 1, u₁ ≤ u₂ →
      lam * (u₂ - u₁) ≤ (h u₂ - ψ u₂) - (h u₁ - ψ u₁)) :
    lam / M ≤ s - s' := by
  have hs'I : s' ∈ Icc (0 : ℝ) 1 := ⟨hs'0.le, hs'1.le⟩
  have hlt : s' < s := by
    have hc := argmax_shift_ge_of_semiconvex_tilt hM hψ hs'0 hs'1 hmax' hlam hs hmax htilt
    have : 0 < min (lam / (2 * M)) ((1 - s') / 2) :=
      lt_min (div_pos hlam (by linarith)) (by linarith)
    linarith
  have hsupR := quadratic_support_right_of_semiconvex_interior_max hM hψ hmax' hs'0
    (y := s) hlt.le hs.2
  have hsupL := quadratic_support_left_of_semiconvex_interior_max hM hh hmax hs1
    hs'0.le hlt.le
  have ht := htilt s' hs'I s hs hlt.le
  have hd : 0 < s - s' := by linarith
  rw [div_le_iff₀ hM]
  have hk : lam * (s - s') ≤ M * (s - s') ^ 2 := by nlinarith
  nlinarith

/-- **Sharp shift under a nonlinear tilt:** `s − s' ≥ min(λ/M, 1 − s')`, the
interior case above or the ceiling. -/
theorem argmax_shift_ge_of_semiconvex_tilt_sharp {ψ h : ℝ → ℝ} {M lam s s' : ℝ}
    (hM : 0 < M) (hψ : SemiconvexOnSet ψ (Icc (0 : ℝ) 1) M)
    (hh : SemiconvexOnSet h (Icc (0 : ℝ) 1) M)
    (hs'0 : 0 < s') (hs'1 : s' < 1) (hmax' : IsMaxOn ψ (Icc (0 : ℝ) 1) s')
    (hlam : 0 < lam) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn h (Icc (0 : ℝ) 1) s)
    (htilt : ∀ u₁ ∈ Icc (0 : ℝ) 1, ∀ u₂ ∈ Icc (0 : ℝ) 1, u₁ ≤ u₂ →
      lam * (u₂ - u₁) ≤ (h u₂ - ψ u₂) - (h u₁ - ψ u₁)) :
    min (lam / M) (1 - s') ≤ s - s' := by
  rcases lt_or_ge s 1 with hs1 | hs1
  · exact le_trans (min_le_left _ _)
      (argmax_shift_ge_tilt_of_semiconvex_interior hM hψ hh hs'0 hs'1 hmax' hlam hs hs1
        hmax htilt)
  · have h1 : s = 1 := le_antisymm hs.2 hs1
    rw [h1]
    exact min_le_right _ _

end SemiconvexArgmaxShift
end Sanctions

#print axioms Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_of_semiconvex_tilt
#print axioms Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_tilt_of_semiconvex_interior
#print axioms Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_of_semiconvex_tilt_sharp
