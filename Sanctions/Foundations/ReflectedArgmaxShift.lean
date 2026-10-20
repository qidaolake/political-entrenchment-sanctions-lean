/-
Sanctions/Foundations/ReflectedArgmaxShift.lean

**Three order facts about maximisers on `[0,1]`, the mirror images of existing ones**
(step 2, target 2b, 2026-10-10: the sign of the Sender's stake as a parameter).

1. `sSup_image_sub_sSup_image_upperBound_of_pointwise` — if `f − h ≤ U` pointwise on a
   nonempty set, then `sup f − sup h ≤ U`. The upper sibling of
   `Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise`.
2. `argmax_le_max_zero_shifted_of_semiconvex` — let `g` be `M`-semiconvex on `[0,1]` with a
   maximiser `v ∈ [0,1)`, and let `H` *fall* by at least `L > 0` per unit. Then every
   maximiser of `g + H` on `[0,1]` is at most `max 0 (v − L/M)`. The order dual of
   `Sanctions.Foundations.QuadraticArgmax.min_one_shifted_argmax_le_of_semiconvex`, proved
   from it by the reflection `s ↦ 1 − s` (`semiconvexOnSet_reflect`). The clip is now at
   `0`, not at `1`.
3. `min_one_floor_shifted_le_of_isMaxOn` — if `g` rises at least as fast as the chord
   `(s − t)(u − M(s + t)/2)` and `H` falls at most at rate `L`, every maximiser of `g + H`
   is at least `min 1 ((u − L)/M)`. The chord-form floor with an adverse tilt.

Rule 19: nothing here names a game; the applications are in
`Theory/Bellman/SenderUpperSlopeCone.lean` and `Theory/LockIn/SenderStakeSign.lean`.
Rule 3: no assumption is introduced; every hypothesis is a theorem binder over the
displayed functions.
-/
import Sanctions.Foundations.QuadraticArgmaxLowerBound

namespace Sanctions
namespace Foundations
namespace ReflectedArgmax

open Set

/-- **Upper bound on a difference of suprema from a pointwise bound.** If `f a − h a ≤ U`
at every point of a nonempty set `K` and `h` is bounded above on `K`, then
`sSup (f '' K) − sSup (h '' K) ≤ U`. The sibling of
`Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise`; used to show that
a Bellman image falls at least as fast as its integrand.
Scope: general class (real analysis; no economic hypothesis). -/
theorem sSup_image_sub_sSup_image_upperBound_of_pointwise {α : Type*} {f h : α → ℝ}
    {K : Set α} (hK : K.Nonempty) {U : ℝ} (h_point : ∀ a ∈ K, f a - h a ≤ U)
    (hh_bdd : BddAbove (h '' K)) :
    sSup (f '' K) - sSup (h '' K) ≤ U := by
  have step : ∀ a ∈ K, f a ≤ sSup (h '' K) + U := by
    intro a ha
    have h1 : h a ≤ sSup (h '' K) := le_csSup hh_bdd ⟨a, ha, rfl⟩
    linarith [h_point a ha]
  have hsup : sSup (f '' K) ≤ sSup (h '' K) + U := by
    apply csSup_le (hK.image f)
    rintro _ ⟨a, ha, rfl⟩
    exact step a ha
  linarith

/-- **The reflected shifted-argmax bound.** Let `g` be `M`-semiconvex on `[0,1]` with a
maximiser `v ∈ [0,1)`, and let `H` fall by at least `L > 0` per unit:
`H s₂ − H s₁ ≤ −L·(s₂ − s₁)` for `s₁ ≤ s₂`. Then every maximiser of `g + H` on `[0,1]` is
at most `max 0 (v − L/M)`. Proof: apply `min_one_shifted_argmax_le_of_semiconvex` to
`u ↦ g (1 − u)` and `u ↦ H (1 − u)`, whose maximiser is `1 − v > 0`.
Scope: general class (real analysis; no economic hypothesis). -/
theorem argmax_le_max_zero_shifted_of_semiconvex {g H : ℝ → ℝ} {M L v : ℝ} (hM : 0 < M)
    (hg : Sanctions.Semiconcave.SemiconvexOnSet g (Icc (0 : ℝ) 1) M) (hv0 : 0 ≤ v)
    (hv1 : v < 1) (hvmax : IsMaxOn g (Icc (0 : ℝ) 1) v) (hL : 0 < L)
    (hH : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      H s₂ - H s₁ ≤ -(L * (s₂ - s₁)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun u => g u + H u) (Icc (0 : ℝ) 1) s) :
    s ≤ max 0 (v - L / M) := by
  have hrefl := Sanctions.SemiconvexArgmaxShift.semiconvexOnSet_reflect hg
  have hrefl_mem : ∀ u ∈ Icc (0 : ℝ) 1, 1 - u ∈ Icc (0 : ℝ) 1 :=
    fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hv' : IsMaxOn (fun u => g (1 - u)) (Icc (0 : ℝ) 1) (1 - v) := by
    intro u hu
    simp only [mem_setOf_eq, sub_sub_cancel]
    exact hvmax (hrefl_mem u hu)
  have hH' : ∀ u₁ ∈ Icc (0 : ℝ) 1, ∀ u₂ ∈ Icc (0 : ℝ) 1, u₁ ≤ u₂ →
      L * (u₂ - u₁) ≤ H (1 - u₂) - H (1 - u₁) := by
    intro u₁ hu₁ u₂ hu₂ hle
    have := hH (1 - u₂) (hrefl_mem u₂ hu₂) (1 - u₁) (hrefl_mem u₁ hu₁) (by linarith)
    linarith
  have hmax' : IsMaxOn (fun u => g (1 - u) + H (1 - u)) (Icc (0 : ℝ) 1) (1 - s) := by
    intro u hu
    simp only [mem_setOf_eq, sub_sub_cancel]
    exact hmax (hrefl_mem u hu)
  have h := Sanctions.Foundations.QuadraticArgmax.min_one_shifted_argmax_le_of_semiconvex
    (g := fun u => g (1 - u)) (H := fun u => H (1 - u)) hM hrefl (by linarith)
    (by linarith) hv' hL hH' (hrefl_mem s hs) hmax'
  rcases le_total 1 (1 - v + L / M) with h1 | h1
  · rw [min_eq_left h1] at h
    exact le_trans (by linarith) (le_max_left _ _)
  · rw [min_eq_right h1] at h
    exact le_trans (by linarith) (le_max_right _ _)

/-- **The chord-form floor against an adverse tilt.** If `g` rises at least as fast as
the chord `(s − t)·(u − M(s + t)/2)` on `[0,1]` (`M > 0`) and `H` falls at most at rate `L`
(`H s − H t ≥ −L·(s − t)` for `t ≤ s`), then every maximiser of `g + H` on `[0,1]` is at
least `min 1 ((u − L)/M)`. If a maximiser lay below that level, moving up to it would gain
at least `(M/2)·(distance)² > 0`.
Scope: general class (real analysis; no economic hypothesis). -/
theorem min_one_floor_shifted_le_of_isMaxOn {g H : ℝ → ℝ} {M u L : ℝ} (hM : 0 < M)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
      (s - t) * (u - M * (s + t) / 2) ≤ g s - g t)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s → -(L * (s - t)) ≤ H s - H t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun v => g v + H v) (Icc (0 : ℝ) 1) s) :
    min 1 ((u - L) / M) ≤ s := by
  by_contra hlt
  have hst : s < min 1 ((u - L) / M) := not_le.mp hlt
  set t := min 1 ((u - L) / M) with ht
  have ht1 : t ≤ 1 := min_le_left _ _
  have htq : t ≤ (u - L) / M := min_le_right _ _
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], ht1⟩
  have hMt : M * t ≤ u - L := by
    have := mul_le_mul_of_nonneg_left htq hM.le
    rwa [mul_div_cancel₀ _ hM.ne'] at this
  have hopt : g t + H t ≤ g s + H s := hmax htI
  have hgts := hg s hs t htI hst.le
  have hHts := hH s hs t htI hst.le
  have hd : 0 < t - s := by linarith
  have h1 : (t - s) * (M * t) ≤ (t - s) * (u - L) := mul_le_mul_of_nonneg_left hMt hd.le
  have hsq : 0 < M / 2 * (t - s) ^ 2 := by positivity
  nlinarith [hopt, hgts, hHts, h1, hsq]

end ReflectedArgmax
end Foundations
end Sanctions
