/-
Sanctions/Foundations/StrongConcaveArgmaxStability.lean

**The maximiser of a strongly concave objective moves at most `L/μ` under an
`L`-Lipschitz perturbation — from chords, with no derivatives.**

## Why it is needed

An interior best response is an argmax that depends on a parameter — here the
inherited political state, entering the Sender's objective through the stage
payoff and through the transition inside the continuation. To carry a Lipschitz
or lower-slope bound on the *Target's* value through its Bellman operator one
needs the Sender's realised sanction to be Lipschitz in the state. The implicit
function theorem gives that with derivatives (`Foundations/ImplicitFunctionTheorem`),
but the value functions on the project's carriers are only Lipschitz and
semiconcave, so a first-order condition is unavailable. This is the
derivative-free substitute.

## The argument

Let `f` be `μ`-strongly concave on a convex set `X`, in chord form
(`SemiconcaveOnSet f X (−μ)`), with maximiser `a`; let `g = f + h` with `h`
`L`-Lipschitz, with maximiser `b`; write `d = |a − b|`. Two chords.

1. *Quadratic gap at the maximiser* (`quadratic_gap_of_strongConcave_max`).
   The chord of `f` at `t·b + (1−t)·a` and optimality of `a` give
   `f a − f b ≥ (μ/2)(1 − t)d²` for every `t ∈ (0,1)`; hence
   `f a − f b ≥ (μ/2)d²`.
2. *The perturbed maximiser.* The chord at `z_t = t·a + (1−t)·b` and step 1
   put `f z_t − f b ≥ (μ/2)t(2 − t)d²`; optimality of `b` for `g` and the
   Lipschitz bound on `h` put `f z_t − f b ≤ L·t·d`. Dividing by `t` and
   letting `t ↓ 0`: `μd² ≤ Ld`, i.e. `|a − b| ≤ L/μ`.

The passage to the limit is the elementary `le_of_forall_pos_lt_one` (a
quantity bounded by `B + t·C` for every `t ∈ (0,1)` is bounded by `B`); no
topology enters.

## The constant

`L/μ` is sharp: on `[0,1]` with `f x = −μx²/2` and `h x = L·x`, for
`0 < L ≤ μ`, the maximisers are `0` and `L/μ`, attaining the bound (a larger
tilt is clipped at the endpoint `1`; range added 2026-09-11, the reader's C09).
A nonsmooth perturbation does not defeat it either:
`f x = −(x − 1/2)²/2`, `h x = |x − 1/2|/5` has two perturbed maxima, `3/10` and
`7/10`, each at distance exactly `L/μ = 1/5` from `1/2`, so uniqueness of the
perturbed maximiser is not hidden in the proof. Until round L (2026-09-10) this
file shipped the midpoint chord alone, which gives `4L/μ` with no limit
argument, and its header called `2L/μ` the sharp constant; the reader's
round-K validation package (document 01) corrected both. The `4L/μ` theorem
(`argmax_dist_le_of_strongConcave_lipschitz_perturbation`) keeps its original
statement, now as a corollary of the sharp one, because the interior-Sender
family and the headline snapshot cite it under that name; the sharp siblings
(`responsePath_lipschitz_sharp`, `LloopSharp`) are what turn the non-affine
member's closed-loop constant from `277/235` into `35/47`.

Nothing here mentions `Params` (Rule 19); every hypothesis is a chord or
Lipschitz inequality over abstract data.
-/
import Sanctions.Foundations.SemiconcaveSup

noncomputable section
open Set

namespace Sanctions.Semiconcave

/-- **Passage to the limit `t ↓ 0` without topology**: a quantity bounded by
`B + t·C` for every `t ∈ (0, 1)` is bounded by `B`. -/
theorem le_of_forall_pos_lt_one {A B C : ℝ}
    (h : ∀ t : ℝ, 0 < t → t < 1 → A ≤ B + t * C) : A ≤ B := by
  by_contra hlt
  have hlt : B < A := not_le.mp hlt
  rcases le_or_gt C 0 with hC | hC
  · have := h (1 / 2) (by norm_num) (by norm_num)
    nlinarith
  · have hpos : 0 < (A - B) / (2 * C) := div_pos (by linarith) (by linarith)
    set t := min (1 / 2 : ℝ) ((A - B) / (2 * C)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) hpos
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have htC : t * C ≤ (A - B) / 2 := by
      have hle : t ≤ (A - B) / (2 * C) := min_le_right _ _
      calc t * C ≤ (A - B) / (2 * C) * C := mul_le_mul_of_nonneg_right hle hC.le
        _ = (A - B) / 2 := by field_simp
    have := h t ht0 ht1
    linarith

/-- **Quadratic gap at the maximiser of a strongly concave function.** If `f` is
`μ`-strongly concave on the convex set `X` in chord form and `a` maximises `f`
on `X`, then `f a − f b ≥ (μ/2)(a − b)²` for every `b ∈ X`: the chord at
`t·b + (1−t)·a`, optimality of `a`, and `t ↓ 0`. -/
theorem quadratic_gap_of_strongConcave_max
    {f : ℝ → ℝ} {X : Set ℝ} {μ a b : ℝ}
    (hX : Convex ℝ X)
    (hf : SemiconcaveOnSet f X (-μ))
    (ha : a ∈ X) (hb : b ∈ X) (hmax : IsMaxOn f X a) :
    μ / 2 * (a - b) ^ 2 ≤ f a - f b := by
  apply le_of_forall_pos_lt_one (C := μ / 2 * (a - b) ^ 2)
  intro t ht0 ht1
  have hm : t * b + (1 - t) * a ∈ X := hX hb ha ht0.le (by linarith) (by ring)
  have hchord := hf b hb a ha t ht0.le ht1.le
  have hle : f (t * b + (1 - t) * a) ≤ f a := hmax hm
  have hsq : (b - a) ^ 2 = (a - b) ^ 2 := by ring
  rw [hsq] at hchord
  -- `t·((f b − f a) + (μ/2)(1 − t)(a − b)²) ≤ 0`, and `t > 0`.
  have hkey : t * ((f b - f a) + μ / 2 * (1 - t) * (a - b) ^ 2) ≤ 0 := by
    nlinarith [hchord, hle]
  have hbr : (f b - f a) + μ / 2 * (1 - t) * (a - b) ^ 2 ≤ 0 := by
    by_contra hpos
    have := mul_pos ht0 (not_le.mp hpos)
    linarith
  nlinarith [hbr]

/-- **Argmax stability under a Lipschitz perturbation of a strongly concave
objective, sharp form** (round L). `f` is `μ`-strongly concave on the convex set
`X` in chord form, `g − f` is `L`-Lipschitz on `X`, `a` maximises `f` and `b`
maximises `g` on `X`. Then `|a − b| ≤ L/μ`, and the constant is attained
(`f x = −μx²/2`, `h x = L·x`). The chord at `t·a + (1−t)·b`, the quadratic gap at
`a`, and `t ↓ 0`. -/
theorem argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp
    {f g : ℝ → ℝ} {X : Set ℝ} {μ L a b : ℝ}
    (hX : Convex ℝ X) (hμ : 0 < μ) (hL : 0 ≤ L)
    (hf : SemiconcaveOnSet f X (-μ))
    (hpert : ∀ u ∈ X, ∀ w ∈ X, |(g u - f u) - (g w - f w)| ≤ L * |u - w|)
    (ha : a ∈ X) (hb : b ∈ X)
    (hfa : IsMaxOn f X a) (hgb : IsMaxOn g X b) :
    |a - b| ≤ L / μ := by
  have hgap := quadratic_gap_of_strongConcave_max hX hf ha hb hfa
  have hsq : (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs (a - b)).symm
  rw [hsq] at hgap
  -- `μ·|a−b|² ≤ L·|a−b|`, from the chords at `t·a + (1−t)·b` for every small `t`.
  have hkey : μ * |a - b| ^ 2 ≤ L * |a - b| := by
    apply le_of_forall_pos_lt_one (C := μ / 2 * |a - b| ^ 2)
    intro t ht0 ht1
    have hm : t * a + (1 - t) * b ∈ X := hX ha hb ht0.le (by linarith) (by ring)
    have hchord := hf a ha b hb t ht0.le ht1.le
    rw [hsq] at hchord
    have hgm : g (t * a + (1 - t) * b) ≤ g b := hgb hm
    have hp := hpert b hb _ hm
    have hp' : (g b - f b) - (g (t * a + (1 - t) * b) - f (t * a + (1 - t) * b))
        ≤ L * |b - (t * a + (1 - t) * b)| :=
      (le_abs_self _).trans hp
    have hbm : |b - (t * a + (1 - t) * b)| = t * |a - b| := by
      rw [show b - (t * a + (1 - t) * b) = -t * (a - b) by ring, abs_mul, abs_neg,
        abs_of_pos ht0]
    rw [hbm] at hp'
    have h1 : t * (μ / 2 * |a - b| ^ 2) ≤ t * (f a - f b) :=
      mul_le_mul_of_nonneg_left hgap ht0.le
    -- `t·(μ|a−b|² − L|a−b| − t·(μ/2)|a−b|²) ≤ 0`, and `t > 0`.
    have hkey' : t * (μ * |a - b| ^ 2 - L * |a - b| - t * (μ / 2 * |a - b| ^ 2)) ≤ 0 := by
      nlinarith [hchord, hgm, hp', h1]
    have hbr : μ * |a - b| ^ 2 - L * |a - b| - t * (μ / 2 * |a - b| ^ 2) ≤ 0 := by
      by_contra hpos
      have := mul_pos ht0 (not_le.mp hpos)
      linarith
    linarith
  rcases eq_or_lt_of_le (abs_nonneg (a - b)) with h0 | hpos
  · rw [← h0]
    positivity
  · rw [le_div_iff₀ hμ]
    have : μ * |a - b| * |a - b| ≤ L * |a - b| := by nlinarith [hkey]
    nlinarith [this, hpos]

/-- **Argmax stability under a Lipschitz perturbation of a strongly concave
objective.** `f` is `μ`-strongly concave on the convex set `X` in chord form,
`g − f` is `L`-Lipschitz on `X`, `a` maximises `f` and `b` maximises `g` on `X`.
Then `|a − b| ≤ 4L/μ`. The original (round-D) statement, kept under its name
for the family and the headline snapshot; since round L a corollary of the sharp
form `|a − b| ≤ L/μ`. -/
theorem argmax_dist_le_of_strongConcave_lipschitz_perturbation
    {f g : ℝ → ℝ} {X : Set ℝ} {μ L a b : ℝ}
    (hX : Convex ℝ X) (hμ : 0 < μ) (hL : 0 ≤ L)
    (hf : SemiconcaveOnSet f X (-μ))
    (hpert : ∀ u ∈ X, ∀ w ∈ X, |(g u - f u) - (g w - f w)| ≤ L * |u - w|)
    (ha : a ∈ X) (hb : b ∈ X)
    (hfa : IsMaxOn f X a) (hgb : IsMaxOn g X b) :
    |a - b| ≤ 4 * L / μ := by
  have h := argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp hX hμ hL hf hpert
    ha hb hfa hgb
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right hμ]
  linarith

/-- **Argmax stability under a uniformly small perturbation, sharp form.** With
`f` `μ`-strongly concave and `|g − f| ≤ ε` on `X`, the maximisers satisfy
`μ·|a − b|² ≤ 4·ε`: the quadratic gap at the maximiser
(`quadratic_gap_of_strongConcave_max`) gives `(μ/2)(a − b)² ≤ f a − f b`, and
optimality of `b` for `g` with the two endpoint errors gives
`f a − f b ≤ 2ε`. No sign of `μ` enters the squared inequality (a sign is needed
only to read it as a distance bound). The constant `4` is attained on `[0,1]`
by `f x = −x²/2`, `g ≡ −1/4`, `a = 0`, `b = 1`, `μ = 1`, `ε = 1/4` (ties in `g`
are allowed by the signature). The exponent stays one half: a sup-norm
perturbation gives Hölder-½ and not Lipschitz sensitivity. Statement and proof
from the reader's 2026-09-12 Lean-and-archive package
(`UniformPerturbationCandidate.lean`), elaborated against the tree before being
ported here (round S, 2026-09-15). -/
theorem argmax_sq_dist_le_of_strongConcave_uniform_perturbation_sharp
    {f g : ℝ → ℝ} {X : Set ℝ} {μ ε a b : ℝ}
    (hX : Convex ℝ X)
    (hf : SemiconcaveOnSet f X (-μ))
    (hclose : ∀ u ∈ X, |g u - f u| ≤ ε)
    (ha : a ∈ X) (hb : b ∈ X)
    (hfa : IsMaxOn f X a) (hgb : IsMaxOn g X b) :
    μ * (a - b) ^ 2 ≤ 4 * ε := by
  have hgap := quadratic_gap_of_strongConcave_max hX hf ha hb hfa
  have horder : g a ≤ g b := hgb ha
  have hlow : -ε ≤ g a - f a := (abs_le.mp (hclose a ha)).1
  have hupp : g b - f b ≤ ε := (abs_le.mp (hclose b hb)).2
  nlinarith

/-- **Argmax stability under a uniformly small perturbation** (the round-D
statement, kept under its name): with `f` `μ`-strongly concave and
`|g − f| ≤ ε` on `X`, the maximisers satisfy `μ·|a − b|² ≤ 16·ε`. Since round S
(2026-09-15) a corollary of the sharp form `4ε` above, using `ε ≥ 0` from the
perturbation bound at `a`; the positivity of `μ` is unused and retained for the
signature. Hölder-½, not Lipschitz: enough for continuity of an interior best
response in its parameter, with no regularity of the perturbation beyond its
size. -/
theorem argmax_sq_dist_le_of_strongConcave_uniform_perturbation
    {f g : ℝ → ℝ} {X : Set ℝ} {μ ε a b : ℝ}
    (hX : Convex ℝ X) (_hμ : 0 < μ)
    (hf : SemiconcaveOnSet f X (-μ))
    (hclose : ∀ u ∈ X, |g u - f u| ≤ ε)
    (ha : a ∈ X) (hb : b ∈ X)
    (hfa : IsMaxOn f X a) (hgb : IsMaxOn g X b) :
    μ * (a - b) ^ 2 ≤ 16 * ε := by
  have h := argmax_sq_dist_le_of_strongConcave_uniform_perturbation_sharp hX hf hclose ha hb
    hfa hgb
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hclose a ha)
  linarith

/-- **Argmax cap for a strongly concave stage plus a Lipschitz continuation**
(Rung 5). If `g` on `[0,1]` has chords `g t − g s ≥ (s − t)·(q(s + t)/2 − L₀)`
for `t ≤ s` — the chord form of "`q`-strongly concave with initial slope at
most `L₀`", which a quadratic `−(q/2)s² + L·s` with `L ≤ L₀` satisfies
exactly — and `h` is `L`-Lipschitz, then every maximiser of `g + h` on
`[0,1]` lies at or below `(L₀ + L)/q`. No derivative, no interior
first-order condition: the comparison action `t = (L₀ + L)/q` beats any
`s > t` by at least `q(s − t)²/2`. -/
theorem argmax_le_cap_of_chord_slope_lipschitz
    {g h : ℝ → ℝ} {q L₀ L : ℝ} (hq : 0 < q) (hL : 0 ≤ L₀ + L)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
      (s - t) * (q * (s + t) / 2 - L₀) ≤ g t - g s)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, |h t - h s| ≤ L * |t - s|)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (fun u => g u + h u) (Icc (0 : ℝ) 1) s) :
    s ≤ (L₀ + L) / q := by
  by_contra hlt
  have hlt : (L₀ + L) / q < s := lt_of_not_ge hlt
  set t := (L₀ + L) / q with ht
  have hqt : q * t = L₀ + L := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := div_nonneg hL hq.le
  have ht_mem : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, by linarith [hs.2]⟩
  have hts : t ≤ s := hlt.le
  have h1 := hg t ht_mem s hs hts
  have h2 := hh t ht_mem s hs
  rw [abs_of_nonpos (by linarith : t - s ≤ 0)] at h2
  have h2' : -(L * (s - t)) ≤ h t - h s := by
    have := (abs_le.mp h2).1; linarith
  have hgap : (s - t) * (q * (s + t) / 2 - L₀) - L * (s - t) = q / 2 * (s - t) ^ 2 := by
    linear_combination (s - t) * hqt
  have hpos : 0 < q / 2 * (s - t) ^ 2 := by
    have : 0 < s - t := by linarith
    positivity
  have hmax_t : g t + h t ≤ g s + h s := hmax ht_mem
  linarith

end Sanctions.Semiconcave

end
