/-
Sanctions/Foundations/DiagonalMonotone.lean

**A monotone map that fixes its diagonal never leaves the interval between its
arguments.**

External mathematics, stated over an abstract `f : ℝ → ℝ → ℝ`: nothing here
mentions the sanctions model, and the file is placed in `Foundations/`
accordingly (Rule 19).

The content is one short observation with a long reach. If `f` is non-decreasing
in each argument separately and satisfies `f t t = t`, then

    f x s  lies between  x  and  s

for every pair — with no continuity, no convexity, no functional form, and no
Lipschitz bound. The proof is two applications of monotonicity against the
diagonal, and it is worth isolating because the hypothesis is *ordinal* while
the conclusion is a *metric* bracket: it converts an order assumption into a
quantitative statement about how far the map can move a point.

Downstream that bracket is what turns "`V` is Lipschitz" into a bound on how far
the composite `s ↦ V (f x s)` can travel *from its diagonal reading* `V x` — a
bound with no curvature in it at all.

**The bound is radial, and only radial.** Every estimate below is anchored at the
first argument: `|f x s - x| ≤ |s - x|` measures the displacement from `x`, the
point `f` fixes. Nothing here bounds `|f x s - f x t|` by `|s - t|`, and no such
bound follows: internality leaves `f x s` anywhere in `[x, s]`, so two nearby
sanctions either side of a steep stretch can be answered far apart.
`Examples/GeneralFNonLipschitzCounterexample.lean` exhibits a transition
satisfying every hypothesis here whose answers to two sanctions `1/4` apart are
`5/16` apart, and refutes every finite modulus besides.

Identified as a consequence of the project's transition hypotheses in the
2026-08-25 reference round; the sanctions-side corollaries live in
`Theory/`.
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Sanctions

/-! ## Internality -/

/-- **Internality, lower half.** A map non-decreasing in each argument and
fixing its diagonal answers `(x, s)` with at least `min x s`. -/
theorem min_le_of_mono_of_diag {f : ℝ → ℝ → ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t) (x s : ℝ) :
    min x s ≤ f x s := by
  rcases le_total s x with h | h
  · -- `s ≤ x`: push the first argument down to `s` and land on the diagonal.
    have := hx s h
    simp only at this
    rw [hd s] at this
    simpa [min_eq_right h] using this
  · have := hs x h
    simp only at this
    rw [hd x] at this
    simpa [min_eq_left h] using this

/-- **Internality, upper half.** The same map answers `(x, s)` with at most
`max x s`. -/
theorem le_max_of_mono_of_diag {f : ℝ → ℝ → ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t) (x s : ℝ) :
    f x s ≤ max x s := by
  rcases le_total s x with h | h
  · have := hs x h
    simp only at this
    rw [hd x] at this
    simpa [max_eq_left h] using this
  · have := hx s h
    simp only at this
    rw [hd s] at this
    simpa [max_eq_right h] using this

/-- **Internality.** `f x s` lies in the closed interval spanned by `x` and `s`.

The two halves together. No continuity, no curvature, no functional form: the
whole content is monotonicity in each argument plus a fixed diagonal. -/
theorem mem_uIcc_of_mono_of_diag {f : ℝ → ℝ → ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t) (x s : ℝ) :
    f x s ∈ Set.uIcc x s := by
  have h1 := min_le_of_mono_of_diag hx hs hd x s
  have h2 := le_max_of_mono_of_diag hx hs hd x s
  rw [Set.mem_uIcc]
  rcases le_total x s with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact Or.inl ⟨h1, h2⟩
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    exact Or.inr ⟨h1, h2⟩

/-- **Feasibility from monotonicity and the diagonal** (round P, 2026-09-11; the
reader's R1). A map monotone in each argument that fixes the diagonal sends the
unit square into `[0,1]`, because `f x s` lies between `x` and `s` and `[0,1]` is
order-convex. The `Params`-level record of the same fact is
`AbstractGame.Params.F_mem_derived`; the placable family's raw-data constructor
fills its `F_mem` field with this lemma. -/
theorem mem_Icc_of_mono_of_diag {f : ℝ → ℝ → ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t) {x s : ℝ} (hxI : x ∈ Set.Icc (0 : ℝ) 1)
    (hsI : s ∈ Set.Icc (0 : ℝ) 1) : f x s ∈ Set.Icc (0 : ℝ) 1 := by
  have h := mem_uIcc_of_mono_of_diag hx hs hd x s
  rw [Set.mem_uIcc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans hxI.1 h1, le_trans h2 hsI.2⟩
  · exact ⟨le_trans hsI.1 h1, le_trans h2 hxI.2⟩

/-- **The displacement is bounded by the argument gap.** An immediate metric
consequence of internality: the map moves `x` by at most `|s - x|`. -/
theorem dist_le_of_mono_of_diag {f : ℝ → ℝ → ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t) (x s : ℝ) :
    |f x s - x| ≤ |s - x| := by
  have h1 := min_le_of_mono_of_diag hx hs hd x s
  have h2 := le_max_of_mono_of_diag hx hs hd x s
  rcases le_total s x with h | h
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **A Lipschitz function composed with such a map stays near its diagonal
reading.**

This is the payoff of internality: a continuation value read through the map
departs from `V x` by at most the value's own Lipschitz constant times the
sanction's distance from `x`, with nothing assumed about the map beyond order.
It is the curvature-free substitute for a bound that would otherwise need a
derivative of `f`.

Radial, not pairwise: the left side is anchored at `V x`. This does **not** say
`s ↦ V (f x s)` is `L`-Lipschitz, and that statement is false in general — see
the file header. -/
theorem lipschitz_comp_le_of_mono_of_diag {f : ℝ → ℝ → ℝ} {V : ℝ → ℝ} {L : ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t)
    (hV : ∀ y z, |V y - V z| ≤ L * |y - z|) (x s : ℝ) :
    |V (f x s) - V x| ≤ L * |s - x| := by
  -- The Lipschitz hypothesis already forces `0 ≤ L`: read it at two points a
  -- unit apart and compare with `abs_nonneg`.
  have hL : 0 ≤ L := by
    have h := hV 1 0
    have h1 : |(1:ℝ) - 0| = 1 := by norm_num
    rw [h1, mul_one] at h
    linarith [abs_nonneg (V 1 - V 0)]
  exact (hV (f x s) x).trans
    (mul_le_mul_of_nonneg_left (dist_le_of_mono_of_diag hx hs hd x s) hL)

/-- **A monotone value read through the map stays between its two readings.** The
order-theoretic companion of `mem_uIcc_of_mono_of_diag`. -/
theorem monotone_comp_mem_uIcc_of_mono_of_diag {f : ℝ → ℝ → ℝ} {V : ℝ → ℝ}
    (hx : ∀ s, Monotone (fun x => f x s)) (hs : ∀ x, Monotone (fun s => f x s))
    (hd : ∀ t, f t t = t) (hV : Monotone V) (x s : ℝ) :
    V (f x s) ∈ Set.uIcc (V x) (V s) := by
  have h1 := min_le_of_mono_of_diag hx hs hd x s
  have h2 := le_max_of_mono_of_diag hx hs hd x s
  rw [Set.mem_uIcc]
  rcases le_total x s with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact Or.inl ⟨hV h1, hV h2⟩
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    exact Or.inr ⟨hV h1, hV h2⟩

end Sanctions
