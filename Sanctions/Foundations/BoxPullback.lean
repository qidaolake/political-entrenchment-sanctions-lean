/-
Sanctions/Foundations/BoxPullback.lean

**The box-shock dual pullback operator and its `(1−δ)`-contraction property.**

This connects the abstract dual-Kantorovich contraction machinery
(`Foundations/DualKantorovich.lean`) to the concrete box kernel. The dual (Koopman /
transfer-adjoint) operator on test functions is

  `(boxPullback δ h f)(x) = movAvgReal h f ((1−δ)·x + δ)`
      `= (1/2h) ∫_{−h}^{h} f(clipS'((1−δ)x + δ + η)) dη`,

i.e. the smear of `f` evaluated along the closed loop `x ↦ (1−δ)x + δ`. This is exactly
the `S` for which the transfer operator `T*` satisfies the adjoint identity
`∫ f d(T*μ) = ∫ (S f) dμ`.

`boxPullback_lipschitz` proves it maps 1-Lipschitz test functions to `(1−δ)`-Lipschitz
ones — exactly the `hS` hypothesis the abstract `dualKR_le_of_adjoint_lipschitz`
consumes — discharged directly from `movAvgReal_affine_lipschitz_contraction`. With this
`S` and the (standard, measure-bind) adjoint identity, the box transfer operator is a
`(1−δ)`-contraction in `dualKR`, hence (with `Foundations/DualKantorovichS.lean`'s
separation) the box-smeared closed-loop chain has a *unique* invariant distribution with
geometric convergence. The transfer operator `T*` and this adjoint identity are now
**constructed** in `Foundations/BoxTransfer.lean` — as the pushforward of the product
`μ ⊗ (uniform box noise)` under the closed-loop-plus-noise map, with the adjoint proved
from `integral_map` + Bochner Fubini `integral_prod` (mathlib lacks a Bochner
`integral_bind`, so the product-pushforward route is used instead). Uniqueness and
geometric convergence are therefore unconditional on the adjoint, and *existence* of the
invariant law is constructed in `Foundations/KrylovBogolyubov.lean` (Cesàro-average
fixed point; mathlib has no Krylov–Bogolyubov / Schauder, so the assembly lemma is
proved there).
-/

import Sanctions.Foundations.MovingAverage
import Sanctions.Foundations.DualKantorovich

open BoundedContinuousFunction

namespace Sanctions

/-- **Box-shock dual pullback** on test functions over `↥S`:
`(boxPullback δ h f)(x) = movAvgReal h f ((1−δ)·x + δ)`. -/
noncomputable def boxPullback (δ h : ℝ) (hh : 0 < h) (f : ↥(Sanctions.S) →ᵇ ℝ) :
    ↥(Sanctions.S) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Sanctions.movAvgReal h f ((1 - δ) * x.val + δ),
     (Sanctions.movAvgReal_continuous hh f).comp (by fun_prop)⟩

@[simp] theorem boxPullback_apply (δ h : ℝ) (hh : 0 < h) (f : ↥(Sanctions.S) →ᵇ ℝ)
    (x : ↥(Sanctions.S)) :
    boxPullback δ h hh f x = Sanctions.movAvgReal h f ((1 - δ) * x.val + δ) := rfl

/-- **The box pullback maps 1-Lipschitz test functions to `(1−δ)`-Lipschitz ones** — the
`hS` hypothesis of `dualKR_le_of_adjoint_lipschitz`, discharged from
`movAvgReal_affine_lipschitz_contraction` (the moving average preserves the Lipschitz
constant; the affine closed loop contracts it by `1−δ`). -/
theorem boxPullback_lipschitz (δ h : ℝ) (hh : 0 < h) (hδ : δ ≤ 1)
    (f : ↥(Sanctions.S) →ᵇ ℝ) (hf : LipschitzWith 1 f) :
    LipschitzWith (Real.toNNReal (1 - δ)) (boxPullback δ h hh f) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [boxPullback_apply, boxPullback_apply, Real.dist_eq,
      Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - δ), Subtype.dist_eq, Real.dist_eq]
  have hfK : ∀ z₁ z₂ : ↥(Sanctions.S), |f z₂ - f z₁| ≤ (1:ℝ) * dist z₁ z₂ := by
    intro z₁ z₂
    have h := hf.dist_le_mul z₁ z₂
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
    rw [one_mul, abs_sub_comm]; exact h
  have hc := Sanctions.movAvgReal_affine_lipschitz_contraction hh hδ f (by norm_num) hfK x.val y.val
  simpa [mul_one] using hc

end Sanctions
