/-
Sanctions/Theory/LockIn/NoCycles.lean

**No conflict cycles under a non-decreasing sanction rule** (2026-10-08, record N180).

## What is here, in English

Fix any realized sanction rule `R` that keeps sanctions in `[0,1]` and does not fall when
the political state rises. The state path it drives under the maintained transition,
`x_{t+1} = F(x_t, R x_t)`, then moves in one direction only:

* **§1. Monotone paths.** The state path is monotone in time: non-decreasing if the
  first step goes up, non-increasing if it goes down. The sanction path `R(x_t)` moves in
  the same direction. So the conflict escalates or de-escalates steadily; it never
  escalates, eases and escalates again.
* **§2. Convergence.** Both paths converge (bounded monotone sequences); no continuity of
  the rule is needed for this.
* **§3. No cycles.** A path that returns to a state it visited before stays there from
  then on. In particular a periodic path is constant: the only cycles are rest points.
* **§4. Equilibria.** Every top-selector equilibrium whose realized rule is
  non-decreasing in the state has these properties.

Only the transition's two monotonicity fields `F_mono_x`, `F_mono_s` and `F_mem` are read
(general in `F`, Rule 22). **Rule 3:** no new assumption; the rule's monotonicity is a
hypothesis of each statement, and it is exactly what the identification result
(`unique_equilibrium_of_rule_monotone`) and the constructed readings supply. Cycles
therefore need a rule that falls with the state somewhere, or a model outside this one.
-/
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.SigmaDynComparison

open Filter Topology

namespace Sanctions
noncomputable section
namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Monotone paths -/

/-- One step of the closed loop preserves order on `[0,1]` under a non-decreasing rule. -/
theorem ruleStepF_le_of_le {R : ℝ → ℝ} (hR_mono : MonotoneOn R Sanctions.I)
    {x y : ℝ} (hx : x ∈ Sanctions.I) (hy : y ∈ Sanctions.I) (hxy : x ≤ y) :
    p.ruleStepF R x ≤ p.ruleStepF R y :=
  le_trans (p.F_mono_s x (hR_mono hx hy hxy)) (p.F_mono_x (R y) hxy)

/-- **The state path is monotone in time.** Under a feasible non-decreasing rule the path
from any feasible start is non-decreasing (if the first step goes up) or non-increasing
(if it goes down). General in `F`. -/
theorem rulePathF_monotone_or_antitone {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Monotone (p.rulePathF R x₀) ∨ Antitone (p.rulePathF R x₀) := by
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  have e : ∀ k, p.rulePathF R x₀ (k + 1) = p.ruleStepF R (p.rulePathF R x₀ k) :=
    fun k => p.rulePathF_succ R x₀ k
  rcases le_total x₀ (p.rulePathF R x₀ 1) with h | h
  · left
    refine monotone_nat_of_le_succ fun n => ?_
    induction n with
    | zero => simpa using h
    | succ k ih =>
      rw [e (k + 1)]
      conv_lhs => rw [e k]
      exact p.ruleStepF_le_of_le hR_mono (hmem k) (hmem (k + 1)) ih
  · right
    refine antitone_nat_of_succ_le fun n => ?_
    induction n with
    | zero => simpa using h
    | succ k ih =>
      rw [e (k + 1)]
      conv_rhs => rw [e k]
      exact p.ruleStepF_le_of_le hR_mono (hmem (k + 1)) (hmem k) ih

/-- **State and sanction move together.** The sanction path `R(x_t)` is monotone in the
same direction as the state path. General in `F`. -/
theorem rulePathF_ruleSanctionsF_monotone_or_antitone {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    (Monotone (p.rulePathF R x₀) ∧ Monotone (p.ruleSanctionsF R x₀)) ∨
      (Antitone (p.rulePathF R x₀) ∧ Antitone (p.ruleSanctionsF R x₀)) := by
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  rcases p.rulePathF_monotone_or_antitone hR_mem hR_mono hx₀ with h | h
  · exact Or.inl ⟨h, fun m n hmn => hR_mono (hmem m) (hmem n) (h hmn)⟩
  · exact Or.inr ⟨h, fun m n hmn => hR_mono (hmem n) (hmem m) (h hmn)⟩

/-! ## 2. Convergence -/

/-- **Both paths converge**, to a state and a sanction in `[0,1]`. Bounded monotone
sequences converge; no continuity of the rule is used. General in `F`. -/
theorem rulePathF_ruleSanctionsF_tendsto {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    (∃ z ∈ Sanctions.I, Tendsto (p.rulePathF R x₀) atTop (𝓝 z)) ∧
      (∃ s ∈ Sanctions.I, Tendsto (p.ruleSanctionsF R x₀) atTop (𝓝 s)) := by
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  have hsmem : ∀ n, p.ruleSanctionsF R x₀ n ∈ Sanctions.I := fun n => hR_mem _ (hmem n)
  have lim : ∀ f : ℕ → ℝ, (∀ n, f n ∈ Sanctions.I) → (Monotone f ∨ Antitone f) →
      ∃ z ∈ Sanctions.I, Tendsto f atTop (𝓝 z) := by
    intro f hf hdir
    have hup : BddAbove (Set.range f) := ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).2⟩
    have hdn : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hf n).1⟩
    rcases hdir with hm | ha
    · have ht := tendsto_atTop_ciSup hm hup
      exact ⟨_, isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall hf), ht⟩
    · have ht := tendsto_atTop_ciInf ha hdn
      exact ⟨_, isClosed_Icc.mem_of_tendsto ht (Eventually.of_forall hf), ht⟩
  rcases p.rulePathF_ruleSanctionsF_monotone_or_antitone hR_mem hR_mono hx₀ with h | h
  · exact ⟨lim _ hmem (Or.inl h.1), lim _ hsmem (Or.inl h.2)⟩
  · exact ⟨lim _ hmem (Or.inr h.1), lim _ hsmem (Or.inr h.2)⟩

/-! ## 3. No cycles -/

/-- **A return is a rest point.** If the path revisits a state, `x_{n+k} = x_n` with
`k ≥ 1`, it stays at that state from date `n` on. General in `F`. -/
theorem rulePathF_const_of_return {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {n k : ℕ} (hk : 1 ≤ k) (hret : p.rulePathF R x₀ (n + k) = p.rulePathF R x₀ n) :
    ∀ j, p.rulePathF R x₀ (n + j) = p.rulePathF R x₀ n := by
  set x := p.rulePathF R x₀ with hx
  have h1 : x (n + 1) = x n := by
    rcases p.rulePathF_monotone_or_antitone hR_mem hR_mono hx₀ with h | h
    · exact le_antisymm (le_trans (h (by omega : n + 1 ≤ n + k)) hret.le) (h (by omega))
    · exact le_antisymm (h (by omega : n ≤ n + 1))
        (le_trans hret.symm.le (h (by omega : n + 1 ≤ n + k)))
  intro j
  induction j with
  | zero => rfl
  | succ i ih =>
    have e : ∀ m, x (m + 1) = p.ruleStepF R (x m) := fun m => p.rulePathF_succ R x₀ m
    calc x (n + (i + 1)) = x (n + i + 1) := by rw [Nat.add_succ]
      _ = p.ruleStepF R (x (n + i)) := e (n + i)
      _ = p.ruleStepF R (x n) := by rw [ih]
      _ = x (n + 1) := (e n).symm
      _ = x n := h1

/-- **The only cycles are rest points.** A periodic path, `x_{m+k} = x_m` for every `m`
with `k ≥ 1`, is constant. General in `F`. -/
theorem rulePathF_periodic_const {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {k : ℕ} (hk : 1 ≤ k) (hper : ∀ m, p.rulePathF R x₀ (m + k) = p.rulePathF R x₀ m) :
    ∀ m, p.rulePathF R x₀ m = x₀ := by
  intro m
  have h := p.rulePathF_const_of_return hR_mem hR_mono hx₀ (n := 0) hk (by simpa using hper 0) m
  simpa using h

/-- **No cycles, in one statement.** Under a feasible non-decreasing rule the state and
sanction paths are monotone in the same direction, and a path that returns to a state it
visited before stays there. General in `F`. -/
theorem rulePathF_no_cycles {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ((Monotone (p.rulePathF R x₀) ∧ Monotone (p.ruleSanctionsF R x₀)) ∨
      (Antitone (p.rulePathF R x₀) ∧ Antitone (p.ruleSanctionsF R x₀))) ∧
    (∀ n k : ℕ, 1 ≤ k → p.rulePathF R x₀ (n + k) = p.rulePathF R x₀ n →
      ∀ j, p.rulePathF R x₀ (n + j) = p.rulePathF R x₀ n) :=
  ⟨p.rulePathF_ruleSanctionsF_monotone_or_antitone hR_mem hR_mono hx₀,
    fun _ _ hk hret => p.rulePathF_const_of_return hR_mem hR_mono hx₀ hk hret⟩

/-! ## 4. Equilibria with a non-decreasing realized rule -/

/-- **No conflict cycles in equilibrium.** In every top-selector equilibrium whose
realized sanction rule is non-decreasing in the state on `[0,1]`, from every feasible
start: the state and sanction paths are monotone in the same direction; both converge;
and a path that returns to a state it visited before stays there. General in `F`. -/
theorem equilibrium_no_cycles (E : p.FeedbackStackelbergEquilibriumTop)
    (hmono : MonotoneOn (p.dynamicEquilibriumRule E) Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ((Monotone (p.rulePathF (p.dynamicEquilibriumRule E) x₀) ∧
        Monotone (p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀)) ∨
      (Antitone (p.rulePathF (p.dynamicEquilibriumRule E) x₀) ∧
        Antitone (p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀))) ∧
    (∃ z ∈ Sanctions.I, Tendsto (p.rulePathF (p.dynamicEquilibriumRule E) x₀) atTop (𝓝 z)) ∧
    (∀ n k : ℕ, 1 ≤ k →
      p.rulePathF (p.dynamicEquilibriumRule E) x₀ (n + k) =
        p.rulePathF (p.dynamicEquilibriumRule E) x₀ n →
      ∀ j, p.rulePathF (p.dynamicEquilibriumRule E) x₀ (n + j) =
        p.rulePathF (p.dynamicEquilibriumRule E) x₀ n) := by
  have hR_mem : ∀ x ∈ Sanctions.I, p.dynamicEquilibriumRule E x ∈ Sanctions.I :=
    fun x _ => p.σ_dyn_top_mem_I E.V_S x (E.α x)
  exact ⟨p.rulePathF_ruleSanctionsF_monotone_or_antitone hR_mem hmono hx₀,
    (p.rulePathF_ruleSanctionsF_tendsto hR_mem hmono hx₀).1,
    fun n k hk hret => p.rulePathF_const_of_return hR_mem hmono hx₀ hk hret⟩

end Params
end AbstractGame
end
end Sanctions
