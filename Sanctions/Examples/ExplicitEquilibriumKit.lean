/-
Sanctions/Examples/ExplicitEquilibriumKit.lean

**Tools for explicit, closed-form equilibria** (round BE, 2026-10-03).

Four small facts used by the explicit constructions of round BE (the affine window
continuum and its exact boundaries, the defiance-core witness outside the chord
class, and the strict interior-compliance equilibrium):

1. `quadBCF a b c`: the quadratic `x ↦ a·x² + b·x + c` as a bounded continuous
   function on the state set.
2. `σ_dyn_top_eq_clip`: if the Sender's forward-looking objective is a concave
   parabola `C − k(s − v)²` on `[0,1]` (`k > 0`), its greatest maximiser is the
   clipped vertex `max 0 (min 1 v)`. The maximiser of a strictly concave function on
   an interval is unique, and that is what pins the upper selector; nothing is
   assumed about it.
3. `eq_zero_of_eq_mul_comp`: a bounded function with `D y = β·D(φ y)` and
   `0 ≤ β < 1` vanishes. It identifies the values of any equilibrium with a given
   policy, through the uniqueness of the fixed point of a discounted linear
   recursion along a self-map of the state set.
4. `V_S_eq_at_top`: at any top-selector equilibrium, the Sender's value at a state
   is its objective at the realised (upper-selector) sanction.

**Rule 3.** No assumption is introduced: these are lemmas over arbitrary `Params`.
**Rule 22.** General in `F`.
-/
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Foundations.DiscountedExtremum
import Sanctions.Theory.Equilibrium.CertifiedEquilibria

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-- The quadratic `x ↦ a·x² + b·x + c` on the state set. -/
def quadBCF (a b c : ℝ) : ChordEconomy.Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => a * y.val ^ 2 + b * y.val + c)
      (by fun_prop))

@[simp] theorem quadBCF_apply (a b c : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    quadBCF a b c y = a * y.val ^ 2 + b * y.val + c := rfl

/-- **The upper selector of a concave-parabola objective is its clipped vertex.**
If, on `[0,1]`, the Sender's forward-looking objective at `(x, a)` is
`C − k·(s − v)²` with `k > 0`, then `σ_dyn_top V_S x a = max 0 (min 1 v)`. -/
theorem σ_dyn_top_eq_clip (p : Params) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a k C v : ℝ}
    (hk : 0 < k)
    (hU : ∀ s ∈ Sanctions.I,
      p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)) = C - k * (s - v) ^ 2) :
    p.σ_dyn_top V_S x a = max 0 (min 1 v) := by
  set u := p.σ_dyn_top V_S x a with hu
  have huI : u ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x a
  have hcI : max 0 (min 1 v) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hmax := p.σ_dyn_top_isMaxOn V_S x a hcI
  simp only [Set.mem_setOf_eq] at hmax
  rw [← hu, hU _ hcI, hU _ huI] at hmax
  have hk' : k * (u - v) ^ 2 ≤ k * (max 0 (min 1 v) - v) ^ 2 := by linarith
  have hsq : (u - v) ^ 2 ≤ (max 0 (min 1 v) - v) ^ 2 := le_of_mul_le_mul_left hk' hk
  obtain ⟨hu0, hu1⟩ := huI
  rcases le_total v 0 with hv | hv
  · rw [min_eq_right (by linarith : v ≤ 1), max_eq_left hv] at hsq ⊢
    have : u ≤ 0 := by nlinarith [mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ -v)]
    linarith
  · rcases le_total v 1 with hv1 | hv1
    · rw [min_eq_right hv1, max_eq_right hv] at hsq ⊢
      have : (u - v) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    · rw [min_eq_left hv1, max_eq_right zero_le_one] at hsq ⊢
      have h1 : (0 : ℝ) ≤ 1 - u := by linarith
      have h2 : (0 : ℝ) ≤ v - 1 := by linarith
      have : 1 ≤ u := by nlinarith [mul_nonneg h1 h2]
      linarith

/-- **A bounded solution of a discounted linear recursion along a self-map vanishes.**
If `|D i| ≤ M` and `D i = β·D(φ i)` for every `i`, with `0 ≤ β < 1`, then `D = 0`. -/
theorem eq_zero_of_eq_mul_comp {ι : Type*} {D : ι → ℝ} {φ : ι → ι} {β M : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hM : ∀ i, |D i| ≤ M) (h : ∀ i, D i = β * D (φ i))
    (i : ι) : D i = 0 := by
  have hbdd : BddBelow (Set.range D) :=
    ⟨-M, by rintro _ ⟨j, rfl⟩; linarith [(abs_le.mp (hM j)).1]⟩
  have hbdd' : BddBelow (Set.range (fun j => -D j)) :=
    ⟨-M, by rintro _ ⟨j, rfl⟩; linarith [(abs_le.mp (hM j)).2]⟩
  have h1 := Foundations.DiscountedExtremum.nonneg_of_mul_comp_le hβ0 hβ1 hbdd
    (fun j => (h j).symm.le) i
  have h2 := Foundations.DiscountedExtremum.nonneg_of_mul_comp_le (f := fun j => -D j)
    hβ0 hβ1 hbdd' (fun j => by change β * -D (φ j) ≤ -D j; rw [h j]; exact le_of_eq (by ring)) i
  simp only at h2
  linarith

/-- **The Sender's value is its objective at the realised sanction**, at every
top-selector equilibrium and every feasible state. -/
theorem V_S_eq_at_top (p : Params) (Q : p.FeedbackStackelbergEquilibriumTop)
    (y : ↥(Sanctions.S : Set ℝ)) :
    Q.V_S y = p.U_S y.val (Q.α y.val) (p.σ_dyn_top Q.V_S y.val (Q.α y.val))
      + p.β_S * Q.V_S (Sanctions.clipS' (p.F y.val (p.σ_dyn_top Q.V_S y.val (Q.α y.val)))) := by
  have hgt : IsGreatest ((fun s => p.integrandS Q.α (fun z => Q.V_S z) (y.val, s)) '' Sanctions.I)
      (p.U_S y.val (Q.α y.val) (p.σ_dyn_top Q.V_S y.val (Q.α y.val))
        + p.β_S * Q.V_S (Sanctions.clipS'
            (p.F y.val (p.σ_dyn_top Q.V_S y.val (Q.α y.val))))) := by
    refine ⟨⟨_, p.σ_dyn_top_mem_I Q.V_S y.val (Q.α y.val), rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact p.σ_dyn_top_isMaxOn Q.V_S y.val (Q.α y.val) hs
  have hsup : Q.V_S y = sSup ((fun s => p.integrandS Q.α (fun z => Q.V_S z)
      (y.val, s)) '' Sanctions.I) := by
    have h := congrArg (fun V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ => V y) Q.V_S_fix
    exact h
  rw [hsup, hgt.csSup_eq]

end

end Examples
end Sanctions
