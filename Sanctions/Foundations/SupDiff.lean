/-
Sanctions/SupDiff.lean

Sup-difference inequality: `|sSup (f '' K) - sSup (g '' K)| ≤ M` whenever the
families `f, g : α → ℝ` differ pointwise by at most `M` on `K`. This is the
algebraic core of the Bellman operator's β-Lipschitz property.

Mathlib (v4.29.1) does not ship this lemma directly — we build it from
`csSup_le` and `le_csSup`.
-/

import Sanctions.Foundations.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

noncomputable section
open Set BoundedContinuousFunction

namespace Sanctions

/-- Sup-difference inequality for indexed families over a nonempty set with a
uniform absolute-difference bound. -/
theorem abs_sSup_image_sub_sSup_image_le
    {α : Type*} {f g : α → ℝ} {K : Set α}
    (hK : K.Nonempty) {M : ℝ}
    (h : ∀ a ∈ K, |f a - g a| ≤ M)
    (hf_bdd : BddAbove (f '' K)) (hg_bdd : BddAbove (g '' K)) :
    |sSup (f '' K) - sSup (g '' K)| ≤ M := by
  -- (1) For each `a ∈ K`, `f a ≤ sSup (g '' K) + M`.
  have step_f : ∀ a ∈ K, f a ≤ sSup (g '' K) + M := by
    intro a ha
    have h_diff := abs_sub_le_iff.mp (h a ha)
    have h_g_le_sup : g a ≤ sSup (g '' K) :=
      le_csSup hg_bdd ⟨a, ha, rfl⟩
    linarith [h_diff.1]
  -- (2) Symmetrically, `g a ≤ sSup (f '' K) + M`.
  have step_g : ∀ a ∈ K, g a ≤ sSup (f '' K) + M := by
    intro a ha
    have h_diff := abs_sub_le_iff.mp (h a ha)
    have h_f_le_sup : f a ≤ sSup (f '' K) :=
      le_csSup hf_bdd ⟨a, ha, rfl⟩
    linarith [h_diff.2]
  -- (3) Lift to the suprema.
  have h_sup_f : sSup (f '' K) ≤ sSup (g '' K) + M := by
    apply csSup_le (hK.image f)
    rintro _ ⟨a, ha, rfl⟩
    exact step_f a ha
  have h_sup_g : sSup (g '' K) ≤ sSup (f '' K) + M := by
    apply csSup_le (hK.image g)
    rintro _ ⟨a, ha, rfl⟩
    exact step_g a ha
  -- (4) Combine via `abs_sub_le_iff`.
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- A common specialization: if every value in `f '' K` and `g '' K` is
bounded in absolute value by some `B`, then both images are `BddAbove`, and
the sup-difference bound applies. -/
theorem abs_sSup_image_sub_sSup_image_le_of_bdd
    {α : Type*} {f g : α → ℝ} {K : Set α}
    (hK : K.Nonempty) {M : ℝ} (h : ∀ a ∈ K, |f a - g a| ≤ M)
    {Bf Bg : ℝ} (hf_bdd : ∀ a ∈ K, f a ≤ Bf) (hg_bdd : ∀ a ∈ K, g a ≤ Bg) :
    |sSup (f '' K) - sSup (g '' K)| ≤ M :=
  abs_sSup_image_sub_sSup_image_le hK h
    ⟨Bf, by rintro _ ⟨a, ha, rfl⟩; exact hf_bdd a ha⟩
    ⟨Bg, by rintro _ ⟨a, ha, rfl⟩; exact hg_bdd a ha⟩

/-! ## LipschitzWith bridge for self-maps on `α →ᵇ ℝ`

A common pattern: prove a self-map `T` on bounded continuous real-valued
functions is `β`-Lipschitz by establishing a pointwise estimate
`|T V x - T W x| ≤ β · dist V W` for every `x`. The lemma below packages the
lift from "pointwise distance bound at every point" to the full `LipschitzWith`
statement.
-/

/-- If a self-map on `α →ᵇ ℝ` satisfies a pointwise sup-norm Lipschitz bound,
it is `LipschitzWith β`. The hypothesis says: for every pair `V, W` and every
point `x`, the pointwise distance after applying `T` is at most `β · dist V W`. -/
theorem lipschitzWith_of_pointwise_dist_le
    {α : Type*} [TopologicalSpace α] {β : NNReal}
    (T : (α →ᵇ ℝ) → (α →ᵇ ℝ))
    (h : ∀ V W : α →ᵇ ℝ, ∀ x : α,
      dist (T V x) (T W x) ≤ (β : ℝ) * dist V W) :
    LipschitzWith β T := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  have h_nn : (0 : ℝ) ≤ (β : ℝ) * dist V W :=
    mul_nonneg β.coe_nonneg dist_nonneg
  exact (dist_le h_nn).mpr (h V W)

end Sanctions

end
