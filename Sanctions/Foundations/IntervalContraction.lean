/-
Sanctions/Foundations/IntervalContraction.lean

**A contraction of a compact interval: one fixed point, every orbit converges to
it, and two orbits approach each other geometrically.**

The closed loop of an equilibrium is a self-map `G` of the state interval. When
it is `L`-Lipschitz with `L < 1` — which the placable family's affine member
is, with `L = 43/46` (Rung 5, docs 53/55) — the interval has exactly one steady
state, every start converges to it, and two paths that resume the same rule
after a finite shock are within `L^n` of their distance at resumption after `n`
periods. The last statement is the honest scope of a hysteresis narrative on
such a member: finite shocks have transient effects and no asymptotic ones.

Everything is stated for a real function on `[a, b]` with no mention of a
transition or a policy (Rule 19). The proof passes through the subtype `Icc a b`,
which is complete, and mathlib's `ContractingWith`.
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Instances.Real.Lemmas

namespace Sanctions
namespace IntervalContraction

open Filter Topology
open scoped NNReal

variable {G : ℝ → ℝ} {a b L : ℝ}

/-- Two orbits of an `L`-Lipschitz self-map of `[a, b]` are within `L^n` of
their initial distance after `n` steps. -/
theorem iterate_dist_le (hL0 : 0 ≤ L)
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hG_lip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |G x - G y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    ∀ n : ℕ, |G^[n] x - G^[n] y| ≤ L ^ n * |x - y| := by
  have hmem : ∀ z ∈ Set.Icc a b, ∀ n, G^[n] z ∈ Set.Icc a b := by
    intro z hz n
    induction n with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hG_maps _ ih
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc |G (G^[k] x) - G (G^[k] y)| ≤ L * |G^[k] x - G^[k] y| :=
          hG_lip _ (hmem x hx k) _ (hmem y hy k)
      _ ≤ L * (L ^ k * |x - y|) := mul_le_mul_of_nonneg_left ih hL0
      _ = L ^ (k + 1) * |x - y| := by ring

/-- **Interval contraction.** An `L`-Lipschitz self-map of `[a, b]` with
`0 ≤ L < 1` has exactly one fixed point in `[a, b]`, and every orbit from
`[a, b]` converges to it. -/
theorem exists_unique_fixedPoint_and_tendsto (hab : a ≤ b) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hG_lip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |G x - G y| ≤ L * |x - y|) :
    ∃ z ∈ Set.Icc a b, G z = z ∧ (∀ y ∈ Set.Icc a b, G y = y → y = z) ∧
      ∀ x ∈ Set.Icc a b, Tendsto (fun n => G^[n] x) atTop (𝓝 z) := by
  -- The subtype self-map.
  let K : Set ℝ := Set.Icc a b
  haveI : Nonempty K := ⟨⟨a, Set.left_mem_Icc.mpr hab⟩⟩
  haveI : CompleteSpace K := isClosed_Icc.completeSpace_coe
  let T : K → K := fun x => ⟨G x.val, hG_maps x.val x.property⟩
  have hT : LipschitzWith ⟨L, hL0⟩ T := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := hG_lip _ x.property _ y.property
    simp only [T, Subtype.dist_eq, Real.dist_eq, NNReal.coe_mk]
    exact h
  have hcontr : ContractingWith ⟨L, hL0⟩ T := ⟨by exact_mod_cast hL1, hT⟩
  let z : K := hcontr.fixedPoint
  have hzfix : T z = z := hcontr.fixedPoint_isFixedPt
  refine ⟨z.val, z.property, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hzfix
  · intro y hy hfix
    have hyfix : Function.IsFixedPt T ⟨y, hy⟩ := Subtype.ext hfix
    have := hcontr.fixedPoint_unique hyfix
    exact congrArg Subtype.val this
  · intro x hx
    have h := hcontr.tendsto_iterate_fixedPoint ⟨x, hx⟩
    have hiter : ∀ n, (T^[n] ⟨x, hx⟩).val = G^[n] x := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    have h' := (continuous_subtype_val.tendsto z).comp h
    simpa [Function.comp_def, hiter] using h'

end IntervalContraction
end Sanctions
