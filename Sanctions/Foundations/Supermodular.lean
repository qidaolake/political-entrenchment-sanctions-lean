/-
Sanctions/Supermodular.lean

Appendix A of the paper: supermodular games, lattice of equilibria
(Topkis, Tarski), parametric monotone comparative statics, and
convergence of best responses.

These are abstract order-theoretic results that reduce to mathlib's
existing `OrderHom.lfp` / `OrderHom.gfp` machinery (Knaster–Tarski).
We package the paper's Appendix A statements as concrete corollaries
of the mathlib infrastructure where possible.
-/

import Sanctions.Foundations.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Lattice

noncomputable section
open Set Function

namespace Sanctions
namespace Supermodular

/-! ## A.1 Static supermodular games

A static supermodular game has player strategy sets that are complete
lattices, and payoff functions that are quasisupermodular in own strategy
and have increasing differences in (own, opponents). The set of pure
Nash equilibria is a non-empty complete lattice (Topkis, Zhou 1994).
We package this at the abstract `CompleteLattice` level. -/

/-- **Best responses in supermodular games (`lem:app_best_responses`).**
On a complete lattice `L`, an order-preserving self-map `BR : L → L`
(intended: the best-response correspondence reduced to a single-valued
order-preserving function in a supermodular game) has both a least and
a greatest fixed point. -/
theorem best_responses_in_supermodular_games
    {L : Type*} [CompleteLattice L] (BR : L →o L) :
    ∃ x : L, BR x = x :=
  ⟨OrderHom.lfp BR, OrderHom.map_lfp BR⟩

/-- **Lattice of equilibria (`thm:app_equilibria_lattice`).**
The set of fixed points of an order-preserving self-map on a complete
lattice contains both a least and a greatest element. This is
**Knaster-Tarski**, supplied by mathlib's `OrderHom.lfp` / `OrderHom.gfp`.

**Attribution corrected 2026-07-28.** The previous docstring credited this
to Zhou (1994); that is wrong in two ways, and the correction matters
because it fixes what a future round may and may not claim.

* Zhou's Theorem 1 proves the fixed-point set `E` is itself a *complete
  lattice*. His Remark 1 states explicitly that this is **strictly
  stronger** than "`E` nonempty, with its meet and join lying in `E`" --
  which is the least/greatest statement proved here. Topkis (1978)
  already had least/greatest elements; the lattice structure was the
  open question Zhou closed. So lfp/gfp is not "the full Zhou result".
* Zhou's theorem is for an **ascending correspondence**, not an
  `OrderHom`. His "ascending" is definitionally
  `Sanctions.Topkis.StrongSetOrder` (`Foundations/Topkis.lean`), which
  for singleton-valued maps collapses to `Monotone`. It is therefore
  *stronger* than the `OrderHom` hypothesis used here, not weaker --
  so Zhou cannot be invoked to relax this theorem's hypothesis.

Source: `PaperRefer/MathTheory/SupermodularNashCompleteLattice-Zhou-1994.md`. -/
theorem lattice_of_equilibria
    {L : Type*} [CompleteLattice L] (BR : L →o L) :
    (OrderHom.lfp BR ≤ OrderHom.gfp BR) ∧
    BR (OrderHom.lfp BR) = OrderHom.lfp BR ∧
    BR (OrderHom.gfp BR) = OrderHom.gfp BR := by
  refine ⟨?_, OrderHom.map_lfp BR, OrderHom.map_gfp BR⟩
  -- lfp ≤ gfp: gfp is a post-fixed point (BR (gfp) ≤ gfp by equality),
  -- so lfp ≤ gfp by the universal property of lfp.
  exact OrderHom.lfp_le BR (le_of_eq (OrderHom.map_gfp BR))

/-- **Parametric monotone comparative statics (`thm:app_param_MCS`).**
Given a family of order-preserving self-maps `BR_t : L → L` parameterized
by `t : T` (a preorder), where `BR_·` is itself order-preserving in `t`
(in the sense that `t ≤ t' → BR_t ≤ BR_{t'}` pointwise), the least
fixed point is monotone in `t`. -/
theorem parametric_MCS_in_t
    {L T : Type*} [CompleteLattice L] [Preorder T]
    (BR : T → (L →o L))
    (hBR_mono : ∀ t t', t ≤ t' → ∀ x, BR t x ≤ BR t' x) :
    Monotone (fun t => OrderHom.lfp (BR t)) := by
  intro t t' htt'
  -- Show: lfp (BR t) ≤ lfp (BR t').
  -- Since lfp = inf of post-fixed points, suffices to show
  -- BR t (lfp BR_{t'}) ≤ lfp BR_{t'}, which follows because
  -- BR t ≤ BR_{t'} pointwise and BR_{t'}(lfp BR_{t'}) = lfp BR_{t'}.
  apply OrderHom.lfp_le
  calc BR t (OrderHom.lfp (BR t'))
      ≤ BR t' (OrderHom.lfp (BR t')) := hBR_mono t t' htt' _
    _ = OrderHom.lfp (BR t')        := OrderHom.map_lfp _

/-- **Monotone best-response convergence (`thm:app_BR_convergence`).**
For an order-preserving self-map on a complete lattice, the iterated
best-response sequence starting from the bottom is monotone increasing
and bounded above by the least fixed point. (Full mathlib convergence
in the sense of "iterates reach the fixed point" requires additional
continuity hypotheses captured by `OmegaCompletePartialOrder`.) -/
theorem monotone_BR_convergence
    {L : Type*} [CompleteLattice L] (BR : L →o L) :
    ∀ n : ℕ, BR^[n] ⊥ ≤ OrderHom.lfp BR := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ k ih =>
      have hstep : BR (BR^[k] ⊥) ≤ BR (OrderHom.lfp BR) := BR.monotone ih
      have : BR^[k+1] ⊥ = BR (BR^[k] ⊥) := Function.iterate_succ_apply' BR k ⊥
      rw [this]
      calc BR (BR^[k] ⊥) ≤ BR (OrderHom.lfp BR) := hstep
        _ = OrderHom.lfp BR := OrderHom.map_lfp BR

end Supermodular
end Sanctions

end
