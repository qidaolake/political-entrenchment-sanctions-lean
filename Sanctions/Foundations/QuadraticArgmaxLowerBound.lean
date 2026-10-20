/-
Sanctions/Foundations/QuadraticArgmaxLowerBound.lean

**A lower bound on the maximiser of a concave quadratic plus a term with a lower
slope** (round AB, 2026-09-19; the reader's family-welfare challenge of
2026-09-19, node P1).

Let `q > 0` and let `H` rise by at least `L` per unit on `[0,1]`:
`L·(s₂ − s₁) ≤ H s₂ − H s₁` for `s₁ ≤ s₂`. Then every maximiser on `[0,1]` of

  `s ↦ −(q/2)·s² + p·s + H s`

is at least `min 1 ((p + L)/q)`: the vertex `p/q` of the quadratic, shifted up by
`L/q`, clipped at the ceiling. The clip is essential — at a ceiling the unclipped
shift is false — and the statement has no differentiability, no concavity of `H`
and no uniqueness of the maximiser.

Proof. If a maximiser `s` lay below `t := min 1 ((p+L)/q)`, moving to `t` would
gain at least `(t − s)·[(p + L) − (q/2)(t + s)] ≥ (q/2)(t − s)² > 0`, because
`q·t ≤ p + L`.

Rule 19: no `Params`, no project structure; the Sender–Target application is in
`Examples/PlacableSenderWedge.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.LocalExtr
import Sanctions.Foundations.SemiconvexArgmaxShift

namespace Sanctions
namespace Foundations
namespace QuadraticArgmax

open Set

/-- **The shifted-vertex lower bound.** See the module docstring. -/
theorem min_one_shifted_vertex_le_of_isMaxOn {q p L : ℝ} (hq : 0 < q) {H : ℝ → ℝ}
    (hH : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      L * (s₂ - s₁) ≤ H s₂ - H s₁)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun t => -(q / 2) * t ^ 2 + p * t + H t) (Icc (0 : ℝ) 1) s) :
    min 1 ((p + L) / q) ≤ s := by
  by_contra hlt
  have hst : s < min 1 ((p + L) / q) := not_le.mp hlt
  set t := min 1 ((p + L) / q) with ht
  have ht1 : t ≤ 1 := min_le_left _ _
  have htq : t ≤ (p + L) / q := min_le_right _ _
  have htmem : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], ht1⟩
  have hqt : q * t ≤ p + L := by
    have := mul_le_mul_of_nonneg_left htq hq.le
    rwa [mul_div_cancel₀ _ hq.ne'] at this
  have hval : -(q / 2) * t ^ 2 + p * t + H t ≤ -(q / 2) * s ^ 2 + p * s + H s := hmax htmem
  have hslope : L * (t - s) ≤ H t - H s := hH s hs t htmem hst.le
  have hd : 0 < t - s := by linarith
  have h1 : (t - s) * (q * t) ≤ (t - s) * (p + L) := mul_le_mul_of_nonneg_left hqt hd.le
  have hsq : 0 < q / 2 * (t - s) ^ 2 := mul_pos (half_pos hq) (pow_pos hd 2)
  nlinarith [hval, hslope, h1, hsq]

/-- The unclipped form, when the maximiser is known to lie strictly below the
ceiling: `(p + L)/q ≤ s`. -/
theorem shifted_vertex_le_of_isMaxOn_of_lt_one {q p L : ℝ} (hq : 0 < q) {H : ℝ → ℝ}
    (hH : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      L * (s₂ - s₁) ≤ H s₂ - H s₁)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs1 : s < 1)
    (hmax : IsMaxOn (fun t => -(q / 2) * t ^ 2 + p * t + H t) (Icc (0 : ℝ) 1) s) :
    (p + L) / q ≤ s := by
  have h := min_one_shifted_vertex_le_of_isMaxOn hq hH hs hmax
  rcases min_le_iff.mp h with h1 | h2
  · exact absurd h1 (not_le.mpr hs1)
  · exact h2

/-! ## The semiconvex form (round AT, 2026-09-25; doc 104 §7, item 3)

The theorem above needs the base objective to be the exact quadratic
`−(q/2)t² + p·t`. What its proof uses is weaker: the base objective has a
maximiser `v` and its curvature is bounded *above* by `M`. For an `M`-semiconvex
`g` with a maximiser `v > 0`, the function `g + (M/2)(· − v)²` is convex with its
minimum at `v` (the quadratic lower support at an interior maximiser), hence
nondecreasing to the right of `v`; that monotonicity replaces the explicit
quadratic, and the bound reads `min 1 (v + L/M)`. The quadratic case is
`g = −(q/2)t² + p·t`, `M = q`, `v = p/q`. The curvature that enters is the
*upper* one, `M`: a shift bounded from below needs a ceiling on how fast the base
objective can fall away from its peak. -/

/-- **The semiconvex shifted-argmax bound.** Let `g` be `M`-semiconvex on `[0,1]`
with a maximiser `v ∈ (0,1]`, and let `H` rise by at least `L > 0` per unit.
Then every maximiser of `g + H` on `[0,1]` is at least `min 1 (v + L/M)`. -/
theorem min_one_shifted_argmax_le_of_semiconvex {g H : ℝ → ℝ} {M L v : ℝ}
    (hM : 0 < M) (hg : Sanctions.Semiconcave.SemiconvexOnSet g (Icc (0 : ℝ) 1) M)
    (hv0 : 0 < v) (hv1 : v ≤ 1) (hvmax : IsMaxOn g (Icc (0 : ℝ) 1) v)
    (hL : 0 < L)
    (hH : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      L * (s₂ - s₁) ≤ H s₂ - H s₁)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun u => g u + H u) (Icc (0 : ℝ) 1) s) :
    min 1 (v + L / M) ≤ s := by
  by_contra hlt
  have hst : s < min 1 (v + L / M) := not_le.mp hlt
  set t := min 1 (v + L / M) with ht
  have ht1 : t ≤ 1 := min_le_left _ _
  have htq : t ≤ v + L / M := min_le_right _ _
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hv0.le, hv1⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], ht1⟩
  have hopt : g t + H t ≤ g s + H s := hmax htI
  rcases lt_or_ge s v with hsv | hvs
  · -- Below the old maximiser: moving up to `v` gains at least `L·(v − s) > 0`.
    have hopt' : g v + H v ≤ g s + H s := hmax hvI
    have hgv : g s ≤ g v := hvmax hs
    have hHv := hH s hs v hvI hsv.le
    have : 0 < L * (v - s) := mul_pos hL (by linarith)
    linarith
  · -- Between `v` and `t`: `g + (M/2)(· − v)²` is nondecreasing there.
    have htv : v < t := lt_of_le_of_lt hvs hst
    have hd : 0 < t - v := by linarith
    have he : 0 < t - s := by linarith
    set lam := (t - s) / (t - v) with hlam_def
    have hlam0 : 0 ≤ lam := div_nonneg he.le hd.le
    have hlam1 : lam ≤ 1 := by rw [hlam_def, div_le_one hd]; linarith
    have hl : lam * (t - v) = t - s := by rw [hlam_def]; field_simp
    have hcomb : lam * v + (1 - lam) * t = s := by
      have : lam * v + (1 - lam) * t = t - lam * (t - v) := by ring
      rw [this, hl]; ring
    have hchord := hg v hvI t htI lam hlam0 hlam1
    rw [hcomb] at hchord
    have hsupp := Sanctions.SemiconvexArgmaxShift.quadratic_support_right_of_semiconvex_interior_max
      hM hg hvmax hv0 htv.le ht1
    -- `λ·(M/2)(t − v)² = (M/2)(t − s)(t − v)` and `λ(1 − λ)(v − t)² = (t − s)(s − v)`.
    have h1 : lam * (1 - lam) * (v - t) ^ 2 = (t - s) * (s - v) := by
      have e : lam * (1 - lam) * (v - t) ^ 2
          = (lam * (t - v)) * ((t - v) - lam * (t - v)) := by ring
      rw [e, hl]; ring
    have h2 : lam * (M / 2 * (t - v) ^ 2) = M / 2 * ((t - s) * (t - v)) := by
      have e : lam * (M / 2 * (t - v) ^ 2) = M / 2 * ((lam * (t - v)) * (t - v)) := by ring
      rw [e, hl]
    rw [h1] at hchord
    have hsupp' : lam * g v ≤ lam * g t + M / 2 * ((t - s) * (t - v)) := by
      have := mul_le_mul_of_nonneg_left hsupp hlam0
      rw [mul_sub, h2] at this
      linarith
    -- So `g s ≤ g t + (M/2)(t − s)(t − v + s − v)`.
    have hgs : g s ≤ g t + M / 2 * ((t - s) * (t - v)) + M / 2 * ((t - s) * (s - v)) := by
      nlinarith [hchord, hsupp']
    have hHt := hH s hs t htI hst.le
    have hMt : M * (t - v) ≤ L := by
      have h3 : t - v ≤ L / M := by linarith
      have := mul_le_mul_of_nonneg_left h3 hM.le
      rwa [mul_div_cancel₀ _ hM.ne'] at this
    have hk : (t - s) * (M * (t - v)) ≤ (t - s) * L := mul_le_mul_of_nonneg_left hMt he.le
    have hsq : 0 < M / 2 * (t - s) ^ 2 := by positivity
    nlinarith [hopt, hgs, hHt, hk, hsq]

end QuadraticArgmax
end Foundations
end Sanctions

#print axioms Sanctions.Foundations.QuadraticArgmax.min_one_shifted_vertex_le_of_isMaxOn
#print axioms Sanctions.Foundations.QuadraticArgmax.shifted_vertex_le_of_isMaxOn_of_lt_one
#print axioms Sanctions.Foundations.QuadraticArgmax.min_one_shifted_argmax_le_of_semiconvex
