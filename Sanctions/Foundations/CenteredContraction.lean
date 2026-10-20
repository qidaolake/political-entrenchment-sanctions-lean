/-
Sanctions/Foundations/CenteredContraction.lean

**A centred geometric error bound for a diagonal-fixing transition driven by an
affine rule** (doc 68, item L4).

External mathematics over an abstract `F : ℝ → ℝ → ℝ`; no game is named, and
nothing is affine in `F`. If `F` is coordinatewise nondecreasing on the unit
square, diagonal-fixing on `[0,1]`, and has a lower sanction chord of rate `d`,
and a rule value `R` sits on the line through the centre `z` with slope
`c₀ ∈ [0,1]` — `R − z = c₀·(x − z)` — then one step of the closed loop
`x ↦ F(x, R)` contracts the distance to `z` by the factor `θ = 1 − d·(1 − c₀)`:

    |F(x, R) − z| ≤ θ · |x − z|.

Iterating a rule that is affine about `z` on `[0,1]` gives
`|x_t − z| ≤ θ^t · |x₀ − z|`.

Two cases, symmetric. Below the centre, `x ≤ R ≤ z`; internality places
`F(x,R)` between `x` and `R`, and the lower chord from `x` to `R` moves it up by
at least `d·(R − x) = d(1 − c₀)(z − x)`. Above the centre the same with the
signs reversed.

**What is not assumed** (round BG-1, 2026-10-06, item BG1.5). The rate `d` may
have either sign: for `d ≤ 0` the factor `θ` is at least `1` and internality
alone gives the bound. `d ≤ 1` is never assumed — the lower chord on a map of
the square into itself forces it. The centre `z` need not lie in `[0,1]`. That
`F` maps the square into `[0,1]` is not assumed either: monotonicity and the
fixed diagonal give it (`mem_Icc_of_monotoneOn_of_diag`). In the sandwich form
`0 ≤ c₀` is read off the distance bound; in the exact-line form it stays a
hypothesis, because a rule on the line with negative slope satisfies all the
others.

**Scope.** This is a *centred* bound toward the particular point `z`, which is
what a geometric convergence rate needs. It is **not** a pairwise contraction of
the map: nothing here compares two arbitrary starts, and no `ContractingWith`
instance follows from it.
-/
import Sanctions.Foundations.TransitionChords
import Mathlib.Tactic

namespace Sanctions
namespace CenteredContraction

open Set Sanctions.TransitionChords

variable {F : ℝ → ℝ → ℝ}

/-- **Internality on the unit square** (general in `F`). A map that is
nondecreasing in each argument on `[0,1]` and fixes the diagonal sends the
square into `[0,1]`: `F y s` lies between `y` and `s`. This is the local
(`MonotoneOn`) form of `DiagonalMonotone.mem_Icc_of_mono_of_diag`; it is what
lets the iteration below drop the separate maps-into hypothesis (BG1.5). -/
theorem mem_Icc_of_monotoneOn_of_diag
    (hFx : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun y => F y s) (Icc (0 : ℝ) 1))
    (hFs : ∀ y ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F y s) (Icc (0 : ℝ) 1))
    (hdiag : ∀ y ∈ Icc (0 : ℝ) 1, F y y = y)
    {y s : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    F y s ∈ Icc (0 : ℝ) 1 := by
  rcases le_total y s with h | h
  · have h1 : F y y ≤ F y s := hFs y hy hy hs h
    have h2 : F y s ≤ F s s := hFx s hs hy hs h
    rw [hdiag y hy] at h1
    rw [hdiag s hs] at h2
    exact ⟨le_trans hy.1 h1, le_trans h2 hs.2⟩
  · have h1 : F s s ≤ F y s := hFx s hs hs hy h
    have h2 : F y s ≤ F y y := hFs y hy hs hy h
    rw [hdiag s hs] at h1
    rw [hdiag y hy] at h2
    exact ⟨le_trans hs.1 h1, le_trans h2 hy.2⟩

/-! ## The sandwich form (round AT, 2026-09-25; doc 104 §7, item 2)

The rule value need not sit *on* the line through the centre,
`R − z = c₀·(x − z)`. The proof uses only that `R` lies on the same side of `z`
as `x` and within the fraction `c₀` of the distance, so that `R` is between `x`
and `z` and has closed at least the fraction `1 − c₀` of the gap. A rule that is
merely Lipschitz about its fixed point with constant `c₀` and order-preserving
toward it — the stage argmax of a general payoff, for instance — satisfies
exactly that. The exact-line forms `step_abs_le` and `iterate_abs_le` below are
corollaries. -/

/-- **One step toward the centre, sandwich form** (general in `F`).

If `R` is on the same side of `z` as `x` and at most `c₀` times as far from it,
one step of `x ↦ F(x, R)` shrinks the distance to `z` by `θ = 1 − d(1 − c₀)`.
Since BG1.5 the rate `d` may have any sign (for `d ≤ 0` the factor is at least
`1`, and internality alone gives the bound), and the centre `z` need not lie in
`[0,1]`; both `0 ≤ d` and `z ∈ [0,1]` were hypotheses before. -/
theorem step_abs_le_of_sandwich {d c₀ z x R : ℝ}
    (hFx : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun y => F y s) (Icc (0 : ℝ) 1))
    (hFs : ∀ y ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F y s) (Icc (0 : ℝ) 1))
    (hdiag : ∀ y ∈ Icc (0 : ℝ) 1, F y y = y)
    (hlo : SanctionLowerChord F d)
    (hc₀1 : c₀ ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hR : R ∈ Icc (0 : ℝ) 1)
    (hside : 0 ≤ (R - z) * (x - z)) (hdist : |R - z| ≤ c₀ * |x - z|) :
    |F x R - z| ≤ (1 - d * (1 - c₀)) * |x - z| := by
  rcases lt_trichotomy x z with hxz | hxz | hzx
  · -- below the centre: x ≤ R ≤ z and R − x ≥ (1 − c₀)(z − x)
    have hzx0 : 0 < z - x := by linarith
    have hRle : R ≤ z := by
      by_contra hcon
      have : 0 < (R - z) * (z - x) := mul_pos (by linarith [not_le.mp hcon]) hzx0
      nlinarith
    have habs : |R - z| = z - R := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have habx : |x - z| = z - x := by rw [abs_sub_comm, abs_of_nonneg hzx0.le]
    rw [habs, habx] at hdist
    have hxR : x ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hc₀1 hzx0.le]
    have hRx : (1 - c₀) * (z - x) ≤ R - x := by nlinarith
    have h1 : x ≤ F x R := by
      have := hFs x hx hx hR hxR
      simpa [hdiag x hx] using this
    have h2 : F x R ≤ z := by
      have := hFx R hR hx hR hxR
      simp only at this
      rw [hdiag R hR] at this
      exact le_trans this hRle
    have hchord := hlo hx hx hR hxR
    rw [hdiag x hx] at hchord
    have key : d * (1 - c₀) * (z - x) ≤ F x R - x := by
      rcases le_total 0 d with hd0 | hd0
      · have := mul_le_mul_of_nonneg_left hRx hd0
        nlinarith
      · -- a nonpositive rate: the left side is `≤ 0`, and internality gives `x ≤ F x R`
        have : 0 ≤ (-d) * ((1 - c₀) * (z - x)) :=
          mul_nonneg (by linarith) (mul_nonneg (by linarith) hzx0.le)
        linarith
    rw [abs_sub_comm (F x R) z, abs_of_nonneg (by linarith), habx]
    nlinarith
  · -- at the centre: R = z and the step stays there
    subst hxz
    have hR0 : R = x := by
      have : |R - x| ≤ 0 := by simpa using hdist
      have := abs_nonpos_iff.mp this
      linarith
    subst hR0
    rw [hdiag R hR]; simp
  · -- above the centre: z ≤ R ≤ x and x − R ≥ (1 − c₀)(x − z)
    have hxz0 : 0 < x - z := by linarith
    have hRge : z ≤ R := by
      by_contra hcon
      have : (R - z) * (x - z) < 0 := mul_neg_of_neg_of_pos (by linarith [not_le.mp hcon]) hxz0
      linarith
    have habs : |R - z| = R - z := abs_of_nonneg (by linarith)
    have habx : |x - z| = x - z := abs_of_nonneg hxz0.le
    rw [habs, habx] at hdist
    have hRx' : R ≤ x := by nlinarith [mul_le_mul_of_nonneg_right hc₀1 hxz0.le]
    have hxR : (1 - c₀) * (x - z) ≤ x - R := by nlinarith
    have h1 : F x R ≤ x := by
      have := hFs x hx hR hx hRx'
      simpa [hdiag x hx] using this
    have h2 : z ≤ F x R := by
      have := hFx R hR hR hx hRx'
      simp only at this
      rw [hdiag R hR] at this
      exact le_trans hRge this
    have hchord := hlo hx hR hx hRx'
    rw [hdiag x hx] at hchord
    have key : d * (1 - c₀) * (x - z) ≤ x - F x R := by
      rcases le_total 0 d with hd0 | hd0
      · have := mul_le_mul_of_nonneg_left hxR hd0
        nlinarith
      · -- a nonpositive rate: the left side is `≤ 0`, and internality gives `F x R ≤ x`
        have : 0 ≤ (-d) * ((1 - c₀) * (x - z)) :=
          mul_nonneg (by linarith) (mul_nonneg (by linarith) hxz0.le)
        linarith
    rw [abs_of_nonneg (by linarith), habx]
    nlinarith

/-- **Iterating a rule sandwiched toward the centre** (general in `F`): the path
stays feasible and the distance to `z` decays geometrically at rate
`θ = 1 − d(1 − c₀)`.

Since BG1.5 five hypotheses are gone. Two are dropped outright: `0 ≤ d` (for
`d ≤ 0` the rate is at least `1` and the bound is internality) and `z ∈ [0,1]`.
Three are derived: that `F` maps the square into `[0,1]`
(`mem_Icc_of_monotoneOn_of_diag`), `d ≤ 1` (the lower chord on such a map,
`sanctionLowerChord_rate_le_one`), and `0 ≤ c₀` (the distance bound at whichever
endpoint of `[0,1]` differs from `z`). -/
theorem iterate_abs_le_of_sandwich {d c₀ z : ℝ} {R : ℝ → ℝ}
    (hFx : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun y => F y s) (Icc (0 : ℝ) 1))
    (hFs : ∀ y ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F y s) (Icc (0 : ℝ) 1))
    (hdiag : ∀ y ∈ Icc (0 : ℝ) 1, F y y = y)
    (hlo : SanctionLowerChord F d)
    (hc₀1 : c₀ ≤ 1)
    (hRmem : ∀ x ∈ Icc (0 : ℝ) 1, R x ∈ Icc (0 : ℝ) 1)
    (hside : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (R x - z) * (x - z))
    (hdist : ∀ x ∈ Icc (0 : ℝ) 1, |R x - z| ≤ c₀ * |x - z|)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) :
    ∀ n : ℕ, (fun x => F x (R x))^[n] x₀ ∈ Icc (0 : ℝ) 1 ∧
      |(fun x => F x (R x))^[n] x₀ - z| ≤ (1 - d * (1 - c₀)) ^ n * |x₀ - z| := by
  have hFmem : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1 :=
    fun y hy s hs => mem_Icc_of_monotoneOn_of_diag hFx hFs hdiag hy hs
  have hd1 : d ≤ 1 := sanctionLowerChord_rate_le_one hFmem hlo
  -- `0 ≤ c₀`: at `x = 0` and `x = 1` the distances to `z` sum to at least `1`.
  have hc₀0 : 0 ≤ c₀ := by
    have h0 := hdist 0 ⟨le_rfl, zero_le_one⟩
    have h1 := hdist 1 ⟨zero_le_one, le_rfl⟩
    have hS : (1 : ℝ) ≤ |0 - z| + |1 - z| := by
      linarith [neg_abs_le (0 - z), le_abs_self (1 - z)]
    by_contra hneg
    have hneg' : c₀ < 0 := lt_of_not_ge hneg
    nlinarith [abs_nonneg (R 0 - z), abs_nonneg (R 1 - z)]
  have hθ0 : 0 ≤ 1 - d * (1 - c₀) := by
    rcases le_total 0 d with hd0 | hd0 <;> nlinarith
  intro n
  induction n with
  | zero => exact ⟨hx₀, by simp⟩
  | succ k ih =>
    obtain ⟨hmem, hbound⟩ := ih
    rw [Function.iterate_succ_apply']
    set y := (fun x => F x (R x))^[k] x₀ with hy
    refine ⟨hFmem y hmem (R y) (hRmem y hmem), ?_⟩
    have hstep := step_abs_le_of_sandwich hFx hFs hdiag hlo hc₀1 hmem (hRmem y hmem)
      (hside y hmem) (hdist y hmem)
    calc |F y (R y) - z| ≤ (1 - d * (1 - c₀)) * |y - z| := hstep
      _ ≤ (1 - d * (1 - c₀)) * ((1 - d * (1 - c₀)) ^ k * |x₀ - z|) :=
          mul_le_mul_of_nonneg_left hbound hθ0
      _ = (1 - d * (1 - c₀)) ^ (k + 1) * |x₀ - z| := by ring

/-! ## The exact-line form

A rule value on the line through the centre, `R − z = c₀·(x − z)` with
`0 ≤ c₀`, is sandwiched: `(R − z)(x − z) = c₀(x − z)² ≥ 0` and
`|R − z| = c₀|x − z|`. So the exact-line statements are corollaries of the
sandwich ones. They keep `0 ≤ c₀`, which a rule on the line cannot supply. -/

/-- **One step toward the centre** (general in `F`), for a rule value on the
line through the centre. A corollary of `step_abs_le_of_sandwich` since BG1.5;
the hypothesis `z ∈ [0,1]` was never used and is gone. -/
theorem step_abs_le {d c₀ z x R : ℝ}
    (hFx : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun y => F y s) (Icc (0 : ℝ) 1))
    (hFs : ∀ y ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F y s) (Icc (0 : ℝ) 1))
    (hdiag : ∀ y ∈ Icc (0 : ℝ) 1, F y y = y)
    (hlo : SanctionLowerChord F d)
    (hc₀0 : 0 ≤ c₀) (hc₀1 : c₀ ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hR : R ∈ Icc (0 : ℝ) 1)
    (hRz : R - z = c₀ * (x - z)) :
    |F x R - z| ≤ (1 - d * (1 - c₀)) * |x - z| :=
  step_abs_le_of_sandwich hFx hFs hdiag hlo hc₀1 hx hR
    (by rw [hRz, mul_assoc]; exact mul_nonneg hc₀0 (mul_self_nonneg _))
    (by rw [hRz, abs_mul, abs_of_nonneg hc₀0])

/-- **Iterating a rule affine about the centre** (general in `F`): the path stays
feasible and the distance to `z` decays geometrically at rate
`θ = 1 − d(1 − c₀)`. A corollary of `iterate_abs_le_of_sandwich` since BG1.5:
the maps-into hypothesis and `d ≤ 1` are derived, and `0 ≤ d` and `z ∈ [0,1]`
are dropped. `0 ≤ c₀` stays. -/
theorem iterate_abs_le {d c₀ z : ℝ} {R : ℝ → ℝ}
    (hFx : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun y => F y s) (Icc (0 : ℝ) 1))
    (hFs : ∀ y ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F y s) (Icc (0 : ℝ) 1))
    (hdiag : ∀ y ∈ Icc (0 : ℝ) 1, F y y = y)
    (hlo : SanctionLowerChord F d)
    (hc₀0 : 0 ≤ c₀) (hc₀1 : c₀ ≤ 1)
    (hRmem : ∀ x ∈ Icc (0 : ℝ) 1, R x ∈ Icc (0 : ℝ) 1)
    (hRz : ∀ x ∈ Icc (0 : ℝ) 1, R x - z = c₀ * (x - z))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) :
    ∀ n : ℕ, (fun x => F x (R x))^[n] x₀ ∈ Icc (0 : ℝ) 1 ∧
      |(fun x => F x (R x))^[n] x₀ - z| ≤ (1 - d * (1 - c₀)) ^ n * |x₀ - z| :=
  iterate_abs_le_of_sandwich hFx hFs hdiag hlo hc₀1 hRmem
    (fun x hx => by rw [hRz x hx, mul_assoc]; exact mul_nonneg hc₀0 (mul_self_nonneg _))
    (fun x hx => by rw [hRz x hx, abs_mul, abs_of_nonneg hc₀0]) hx₀

end CenteredContraction
end Sanctions

#print axioms Sanctions.CenteredContraction.step_abs_le_of_sandwich
#print axioms Sanctions.CenteredContraction.iterate_abs_le_of_sandwich
