/-
Sanctions/Foundations/QuadraticGrowthPerturbation.lean

Generic value-loss bound for a Lipschitz perturbation of an objective with
quadratic growth at a maximizer.

If `f(a₀) - f(a) ≥ m |a-a₀|²` and the perturbation changes by at most
`L |a-a₀|`, completing the square shows that the perturbed optimum exceeds
the value at `a₀` by at most `L²/(4m)`.  This is generic real analysis; no
project-specific economics or assumption structure appears here.
-/

import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic

namespace Sanctions

open Set

/-- Pointwise completed-square bound for a Lipschitz perturbation of an
objective with quadratic growth at `a₀`. -/
theorem quadraticGrowth_add_perturbation_pointwise_le
    {K : Set ℝ} {f g : ℝ → ℝ} {a₀ m L : ℝ}
    (hm : 0 < m)
    (hgrowth : ∀ a ∈ K, m * (a - a₀) ^ 2 ≤ f a₀ - f a)
    (hperturb : ∀ a ∈ K, |g a - g a₀| ≤ L * |a - a₀|)
    {a : ℝ} (ha : a ∈ K) :
    f a + g a ≤ f a₀ + g a₀ + L ^ 2 / (4 * m) := by
  have hgap := hgrowth a ha
  have hpert := hperturb a ha
  have hpert' : g a - g a₀ ≤ L * |a - a₀| :=
    (le_abs_self (g a - g a₀)).trans hpert
  let d : ℝ := |a - a₀|
  have hsq : d ^ 2 = (a - a₀) ^ 2 := by
    simpa only [d] using sq_abs (a - a₀)
  have hquad :
      -m * d ^ 2 + L * d ≤ L ^ 2 / (4 * m) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * m)).2
    nlinarith [sq_nonneg (2 * m * d - L)]
  have hfg :
      (f a + g a) - (f a₀ + g a₀) ≤
        -m * d ^ 2 + L * d := by
    dsimp only [d]
    nlinarith
  linarith

/-- Supremum form of the completed-square perturbation bound.  Feasibility of
`a₀` supplies both nonemptiness and the matching lower bound. -/
theorem abs_sSup_add_perturbation_sub_base_le
    {K : Set ℝ} {f g : ℝ → ℝ} {a₀ m L : ℝ}
    (ha₀ : a₀ ∈ K) (hm : 0 < m)
    (hgrowth : ∀ a ∈ K, m * (a - a₀) ^ 2 ≤ f a₀ - f a)
    (hperturb : ∀ a ∈ K, |g a - g a₀| ≤ L * |a - a₀|) :
    |sSup ((fun a => f a + g a) '' K) - (f a₀ + g a₀)| ≤
      L ^ 2 / (4 * m) := by
  let B : ℝ := L ^ 2 / (4 * m)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hpoint :
      ∀ a ∈ K, f a + g a ≤ f a₀ + g a₀ + B := by
    intro a ha
    simpa only [B] using
      quadraticGrowth_add_perturbation_pointwise_le
        hm hgrowth hperturb ha
  have hbdd : BddAbove ((fun a => f a + g a) '' K) := by
    refine ⟨f a₀ + g a₀ + B, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hpoint a ha
  have hne : ((fun a => f a + g a) '' K).Nonempty :=
    ⟨f a₀ + g a₀, ⟨a₀, ha₀, rfl⟩⟩
  have hupper :
      sSup ((fun a => f a + g a) '' K) ≤
        f a₀ + g a₀ + B :=
    csSup_le hne (by
      rintro _ ⟨a, ha, rfl⟩
      exact hpoint a ha)
  have hlower :
      f a₀ + g a₀ ≤
        sSup ((fun a => f a + g a) '' K) :=
    le_csSup hbdd ⟨a₀, ha₀, rfl⟩
  rw [abs_le]
  constructor <;> dsimp only [B] at *
  · linarith
  · linarith

/-- Supremum residual bound when the perturbed objective is known only through
an affine error envelope around the quadratic-growth reference objective.

The uniform part `A` is paid once, while the action-dependent part is absorbed
by completing the square, giving `L²/(4m)`. -/
theorem abs_sSup_sub_quadraticGrowth_base_le_of_affine_error
    {K : Set ℝ} {f J : ℝ → ℝ} {a₀ m A L c : ℝ}
    (ha₀ : a₀ ∈ K) (hm : 0 < m) (hL : 0 ≤ L)
    (hgrowth : ∀ a ∈ K, m * (a - a₀) ^ 2 ≤ f a₀ - f a)
    (hclose : ∀ a ∈ K,
      |J a - (f a + c)| ≤ A + L * |a - a₀|) :
    |sSup (J '' K) - (f a₀ + c)| ≤ A + L ^ 2 / (4 * m) := by
  have hquad :
      ∀ a ∈ K, f a + L * |a - a₀| ≤
        f a₀ + L ^ 2 / (4 * m) := by
    intro a ha
    have h :=
      quadraticGrowth_add_perturbation_pointwise_le
        (K := K) (f := f) (g := fun z : ℝ => L * |z - a₀|)
        (a₀ := a₀) (m := m) (L := L)
        hm hgrowth (fun z _hz => by
          simp [abs_mul, abs_of_nonneg hL]) ha
    simpa using h
  have hpoint :
      ∀ a ∈ K, J a ≤
        f a₀ + c + (A + L ^ 2 / (4 * m)) := by
    intro a ha
    have hclosea := hclose a ha
    have hupper :
        J a - (f a + c) ≤ A + L * |a - a₀| :=
      (le_abs_self (J a - (f a + c))).trans hclosea
    have hqa := hquad a ha
    linarith
  have hbdd : BddAbove (J '' K) := by
    refine ⟨f a₀ + c + (A + L ^ 2 / (4 * m)), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hpoint a ha
  have hne : (J '' K).Nonempty := ⟨J a₀, ⟨a₀, ha₀, rfl⟩⟩
  have hupper :
      sSup (J '' K) ≤
        f a₀ + c + (A + L ^ 2 / (4 * m)) :=
    csSup_le hne (by
      rintro _ ⟨a, ha, rfl⟩
      exact hpoint a ha)
  have hclose₀ := hclose a₀ ha₀
  have hbaseLower :
      f a₀ + c - A ≤ J a₀ := by
    have h := (abs_le.mp hclose₀).1
    simp only [sub_self, abs_zero, mul_zero, add_zero] at h
    linarith
  have hsupLower : J a₀ ≤ sSup (J '' K) :=
    le_csSup hbdd ⟨a₀, ha₀, rfl⟩
  have hquadNonneg : 0 ≤ L ^ 2 / (4 * m) := by positivity
  rw [abs_le]
  constructor <;> linarith

end Sanctions
