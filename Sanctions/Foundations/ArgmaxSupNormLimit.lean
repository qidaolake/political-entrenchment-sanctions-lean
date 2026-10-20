/-
Sanctions/Foundations/ArgmaxSupNormLimit.lean

**Why `ArgmaxSensitivity` needs a slope bound and not a sup-norm bound.**

External theory (Rule 19): convex analysis about real functions on a convex
subset of `ℝ`. Nothing here mentions `Params`, a sanction, or a transition.

`ArgmaxSensitivity.lean` proves the estimate the Perov/Schur existence route
needs: under strong concavity with modulus `c`, the selected maximizer moves
*linearly* in the coordinate change,

  `|select(x,y) - select(x',y')| ≤ (2/c) · (Lx·d(x,x') + Ly·d(y,y'))`.

That theorem carries one hypothesis, `hdiff`, which is easy to read past:

  `|(f a - g a) - (f b - g b)| ≤ (Lx·dx + Ly·dy) · |a - b|`.

This is *not* a statement that `f` and `g` are close. It says the difference
`f - g` varies slowly **in the action** -- a bound on the perturbation's slope,
proportional to `|a - b|`. This file exists to show that the distinction is
load-bearing rather than technical convenience: with only sup-norm closeness the
same argument yields a square root, and the square root is attained.

**The contrast, on the same proof.** Both estimates run through the quadratic
deviation at a maximizer, `f b ≤ f a - (c/4)(a-b)²`. What differs is the bound
placed on `f a - f b` from the other side:

* slope control (`hdiff`) gives `f a - f b ≤ K·|a - b|`, and one factor of
  `|a - b|` cancels, leaving `|a - b| ≤ (4/c)·K` -- linear;
* sup-norm control gives only `f a - f b ≤ 2ε`, a constant, and nothing
  cancels, leaving `(c/4)(a - b)² ≤ 2ε` -- square root.

**The upper bound alone proves nothing negative**, which is the point of the
second half of the file. `argmax_sq_dist_le_of_sup_close` says the displacement
is *at most* of order `√ε`; on its own that is consistent with the displacement
always being `O(ε)` and the bound merely being slack. What rules that out is a
family in which the `√ε` rate is *attained*, and `sqrt_rate_is_attained` exhibits
one: a fixed strongly-concave `f` on a fixed interval, and a perturbation of
sup-norm size exactly `ε` that moves the maximizer by exactly `√ε / 2`.

**A defect this file used to have, recorded because it is instructive.** The
original witness took `f s = -s²` and `g s = -s² + 2εs` on `[-1,1]`, and the
docstring claimed it exhibited the square-root law. It does not. Its two
maximizers are `0` and `ε`, and its sup-norm gap is `sup |2εs| = 2ε` -- so the
displacement is `½‖f-g‖∞`, which is *linear*, and the witness is an instance of
the bound being slack rather than tight. The error was in the accounting: the
docstring measured the perturbation by how far the objective fell *at the old
maximizer* (`ε²`) rather than by its sup norm over the domain (`2ε`). Those two
quantities are the same order only for perturbations whose slope is controlled
-- which is precisely the hypothesis this file exists to say is missing. A
smooth perturbation of a strongly concave function cannot do better: to move the
argmax by `√ε` on an `ε` budget the perturbation must be *localised*, rising by
`ε` across a window of width `√ε` and flat outside it. That is what
`clampedRamp` is.

**Scope of the negative claim.** What is established is that *strong concavity
of `f` plus a sup-norm bound on `f - g`* does not yield a Lipschitz argmax
estimate: no constant `L` makes `|a - b| ≤ L·ε` hold across the family below,
for any modulus `c`, since the family can be run at fixed `c = 2`. It is **not**
claimed that no linear estimate exists for a more structured class of
perturbations -- indeed `ArgmaxSensitivity.lean` proves one, under slope
control, and that is the whole contrast being drawn.

**Why this matters for the existence route.** A Schur/Perov contraction needs
genuine Lipschitz constants for its cross rows. `√ε` is not `L·ε` for any finite
`L` as `ε → 0`, so a carrier that controls continuation values only in sup norm
cannot deliver those constants, however strongly concave the stage payoff is.
Controlling the slope of the perturbation is what a `C¹` carrier provides and a
sup-norm ball of bounded continuous functions does not. That is the reason
`Theory/Bellman/C1Val.lean` and the `C1BellmanSystem` machinery exist, and it is
recorded here as a theorem instead of an intuition.

## Where the evidence lives

The square-root rate below is attained, not merely an upper bound. The family
attaining it is in `Examples/Sharpness/ArgmaxSupNorm.lean`, moved there
2026-08-27 so that this file states the bound and nothing constructs it.
-/

import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic

namespace Sanctions
namespace ArgmaxSupNormLimit

open Set

/-! ## The upper bound: sup-norm closeness controls the argmax to `√ε` -/

/-- **Quadratic deviation at a maximizer.** If `f` is strongly concave with
modulus `c` and `aMax` maximizes it, then `f` falls off at least quadratically
away from `aMax`. This is the step that turns curvature into a statement about
*locations* rather than values.

(The same fact is proved privately in `ArgmaxSensitivity.lean`; it is restated
here so this file stands alone and the contrast below can be read in one place.)
-/
theorem deviation_at_maximizer
    {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hA : Convex ℝ A) (hf : StrongConcaveOn A c f)
    {aMax a : ℝ} (haMax : aMax ∈ A) (ha : a ∈ A)
    (hmax : IsMaxOn f A aMax) :
    f a ≤ f aMax - (c / 4) * (aMax - a) ^ 2 := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  unfold StrongConcaveOn UniformConcaveOn at hf
  have hsc := hf.2 haMax ha hhalf hhalf hsum
  dsimp only at hsc
  have hnorm : ‖aMax - a‖ ^ 2 = (aMax - a) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm] at hsc
  have hmem : (1 / 2 : ℝ) • aMax + (1 / 2 : ℝ) • a ∈ A :=
    hA haMax ha hhalf hhalf hsum
  have hle : f ((1 / 2 : ℝ) • aMax + (1 / 2 : ℝ) • a) ≤ f aMax := hmax hmem
  simp only [smul_eq_mul] at hsc hle
  have hchain := le_trans hsc hle
  have hcompute :
      (1 / 2 : ℝ) * (1 / 2) * (c / 2 * (aMax - a) ^ 2)
        = c / 8 * (aMax - a) ^ 2 := by
    ring
  rw [hcompute] at hchain
  nlinarith

/-- **Sup-norm closeness controls the argmax only to a square root.**

`a` maximizes `f`, `b` maximizes `g`, the two objectives agree to within `ε`
everywhere on `A`, and `f` is strongly concave with modulus `c`. Then

  `(c/4) · (a - b)² ≤ 2ε`.

Compare `argmax_lipschitz_two_coordinates_of_strongConcave`, which reaches
`|a - b| ≤ (2/c)·K` from a hypothesis bounding the same objective gap by
`K·|a - b|`. The proofs agree up to that one substitution, and the exponent is
the whole difference between them: raising `c` improves the constant here and
never the rate -- see `sqrt_rate_is_attained`, which runs at fixed `c = 2` and
still forces `√ε`. -/
theorem argmax_sq_dist_le_of_sup_close
    {A : Set ℝ} (hA : Convex ℝ A) {f g : ℝ → ℝ} {c ε : ℝ}
    (hf : StrongConcaveOn A c f)
    {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A)
    (hfa : IsMaxOn f A a) (hgb : IsMaxOn g A b)
    (hclose : ∀ z ∈ A, |f z - g z| ≤ ε) :
    c / 4 * (a - b) ^ 2 ≤ 2 * ε := by
  have hdev : f b ≤ f a - (c / 4) * (a - b) ^ 2 :=
    deviation_at_maximizer hA hf ha hb hfa
  -- `b` is at least as good as `a` for `g`, so the whole gap is paid by `ε`
  have hga : g a ≤ g b := hgb ha
  have h1 : f a - g a ≤ ε := (abs_le.mp (hclose a ha)).2
  have h2 : g b - f b ≤ ε := by
    have := (abs_le.mp (hclose b hb)).1
    linarith
  linarith

end ArgmaxSupNormLimit
end Sanctions
