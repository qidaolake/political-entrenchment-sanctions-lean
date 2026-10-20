/-
Sanctions/Theory/Bellman/Verification.lean

**Abstract verification theorems for the Target Bellman value.**

The Rule-1 verification content (one-shot deviation principle) at the
abstract layer, parametric over `Sanctions.AbstractGame.Params`.

Two distinct theorems:

* `bellman_integrand_le_value` — pure Bellman inequality: for any
  state and any feasible action, the Bellman integrand is at most
  `V_T x`. Uses ONLY the fixed-point equation; takes no α-policy.

* `verification_target_one_shot_deviation` — the α-form one-shot
  deviation: given a Target policy α attaining the Bellman fixed-point
  equation at every state, any single-period deviation is weakly worse
  than α. Internally combines `bellman_integrand_le_value` with the
  α-attainment hypothesis.

`verification_target_exists` packages compactness + continuity into
existence of an α-attainment witness, supplying the hypothesis the
deviation form consumes.

**Rule-1 compliance.** Theorems with α take a Bellman-attainment
hypothesis and never plug in a fixed action.

**Rule-3 compliance.** Uses only structural hypotheses of
`AbstractGame.Params`. No new external assumption.

**Round BJ5.1 (2026-10-07).** All three theorems are about `V_T`, the Target's
value against the static Sender selector, and so take
`[p.StaticSelectorContinuous]` (joint continuity of `σ`, formerly the `Params`
field `σ_continuous`). General in `F`. The condition moved from every `Params`
to these binders; the statements are otherwise unchanged.

**Rule-5 compliance.** Parametric over `(p, α)`. No witness specifics.
-/

import Sanctions.Theory.Bellman.BellmanT

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Pure Bellman inequality for the Target value function**
(abstract). For any state `x` and any feasible action `a ∈ I`, the
Bellman integrand at `(x, a)` is at most `V_T x`. Uses only the
Bellman fixed-point equation; takes no α-policy. -/
theorem bellman_integrand_le_value [p.StaticSelectorContinuous] :
    ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      p.U_T x.val a (p.σ x.val a)
        + p.β_T * p.V_T (Sanctions.clipS'
            (p.F x.val (p.σ x.val a)))
        ≤ p.V_T x := by
  intro x a ha
  rw [p.V_T_bellman_eq x]
  apply le_csSup
  · have hσ_x : Continuous (fun b : ℝ => p.σ x.val b) :=
      p.σ_continuous.comp (Continuous.prodMk continuous_const continuous_id)
    have h_triple : Continuous (fun b : ℝ => (x.val, b, p.σ x.val b)) := by
      refine .prodMk continuous_const (.prodMk continuous_id ?_)
      exact hσ_x
    have hU : Continuous (fun b => p.U_T x.val b (p.σ x.val b)) :=
      p.U_T_continuous.comp h_triple
    have hF : Continuous (fun b => Sanctions.clipS'
          (p.F x.val (p.σ x.val b))) := by
      have h : Continuous (fun b => p.F x.val (p.σ x.val b)) :=
        p.F_continuous.comp (Continuous.prodMk continuous_const hσ_x)
      exact Sanctions.clipS'_continuous.comp h
    have h_cont :
        Continuous (fun b => p.U_T x.val b (p.σ x.val b)
              + p.β_T * p.V_T (Sanctions.clipS'
                  (p.F x.val (p.σ x.val b)))) :=
      hU.add (continuous_const.mul (p.V_T.continuous.comp hF))
    exact (isCompact_Icc.image_of_continuousOn h_cont.continuousOn).bddAbove
  · exact ⟨a, ha, rfl⟩

/-- **One-shot deviation principle for the Target** (abstract). Given
a Target policy `α` attaining the Bellman fixed-point equation at every
state, any single-period deviation is weakly worse than `α`.

The `_h_α_mem` hypothesis is bound (not used directly) so the theorem
signature documents the feasibility constraint on `α`; the substantive
content rides on `h_α_attains` + the pure Bellman inequality. -/
theorem verification_target_one_shot_deviation [p.StaticSelectorContinuous]
    (α : ℝ → ℝ)
    (_h_α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (h_α_attains : ∀ x : ↥(Sanctions.S : Set ℝ),
      p.V_T x =
        p.U_T x.val (α x.val) (p.σ x.val (α x.val))
          + p.β_T * p.V_T (Sanctions.clipS'
              (p.F x.val (p.σ x.val (α x.val))))) :
    ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      p.U_T x.val a (p.σ x.val a)
        + p.β_T * p.V_T (Sanctions.clipS'
            (p.F x.val (p.σ x.val a)))
        ≤ p.U_T x.val (α x.val) (p.σ x.val (α x.val))
            + p.β_T * p.V_T (Sanctions.clipS'
                (p.F x.val (p.σ x.val (α x.val)))) := by
  intro x a ha
  have h_ineq := p.bellman_integrand_le_value x a ha
  have h_eq := h_α_attains x
  linarith

/-- **Existence of a Target-optimal action at each state** (abstract).
By compactness of `I` and continuity of the Bellman integrand, the
supremum in the Bellman equation is attained at some `a ∈ I`. This
delivers the per-state attainment that
`verification_target_one_shot_deviation` consumes. -/
theorem verification_target_exists [p.StaticSelectorContinuous]
    (x : ↥(Sanctions.S : Set ℝ)) :
    ∃ a ∈ Sanctions.I,
      p.U_T x.val a (p.σ x.val a)
        + p.β_T * p.V_T (Sanctions.clipS'
            (p.F x.val (p.σ x.val a)))
        = p.V_T x := by
  have hσ_x : Continuous (fun a : ℝ => p.σ x.val a) :=
    p.σ_continuous.comp (Continuous.prodMk continuous_const continuous_id)
  have h_triple : Continuous (fun a : ℝ => (x.val, a, p.σ x.val a)) := by
    refine .prodMk continuous_const (.prodMk continuous_id ?_)
    exact hσ_x
  have hU : Continuous (fun a => p.U_T x.val a (p.σ x.val a)) :=
    p.U_T_continuous.comp h_triple
  have hF : Continuous (fun a => Sanctions.clipS'
        (p.F x.val (p.σ x.val a))) := by
    have h : Continuous (fun a => p.F x.val (p.σ x.val a)) :=
      p.F_continuous.comp (Continuous.prodMk continuous_const hσ_x)
    exact Sanctions.clipS'_continuous.comp h
  have h_cont :
      ContinuousOn (fun a => p.U_T x.val a (p.σ x.val a)
            + p.β_T * p.V_T (Sanctions.clipS'
                (p.F x.val (p.σ x.val a)))) Sanctions.I :=
    (hU.add (continuous_const.mul (p.V_T.continuous.comp hF))).continuousOn
  obtain ⟨a, ha, h_max⟩ :=
    isCompact_Icc.exists_isMaxOn (s := (Sanctions.I : Set ℝ))
      ⟨0, by simp [Sanctions.I]⟩ h_cont
  refine ⟨a, ha, ?_⟩
  rw [p.V_T_bellman_eq x]
  set f : ℝ → ℝ := fun b => p.U_T x.val b (p.σ x.val b)
            + p.β_T * p.V_T (Sanctions.clipS'
                (p.F x.val (p.σ x.val b))) with hf
  have h_image_ne : (f '' Sanctions.I).Nonempty := ⟨f a, a, ha, rfl⟩
  have h_image_bdd : BddAbove (f '' Sanctions.I) :=
    (isCompact_Icc.image_of_continuousOn h_cont).bddAbove
  apply le_antisymm
  · exact le_csSup h_image_bdd ⟨a, ha, rfl⟩
  · apply csSup_le h_image_ne
    rintro _ ⟨a', ha', rfl⟩
    exact h_max ha'

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
