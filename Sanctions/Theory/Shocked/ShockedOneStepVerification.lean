/-
Sanctions/Theory/Shocked/ShockedOneStepVerification.lean

The strongest verification consequences available for an abstract
`ShockedParams` without adding kernel assumptions.

Both equilibrium rows are exposed in one-step Bellman form.  The Target policy
attains its shocked leader objective against every feasible Target deviation,
and the upper Sender selector attains its shocked follower objective against
every feasible Sender deviation.  These are genuine two-sided, endogenous
optimality statements.

They are deliberately called one-step consequences.  Turning them into an
infinite expected-payoff comparison requires a probability-kernel semantics
for `smear` (at least order and constant preservation, plus a path/iterated
expectation construction).  `ShockedParams` currently supplies only
nonexpansiveness; `Foundations/ShockedVerificationBoundary.lean` proves that
this is insufficient for lifetime verification.
-/

import Sanctions.Theory.Shocked.ShockedEquilibrium
import Sanctions.Foundations.ShockedVerificationBoundary

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame

/-- **Formal boundary witness, not an economic shock.** Every base `Params`
can be extended to a syntactically valid `ShockedParams` by taking `smear V =
-V`.  Negation is nonexpansive, so this satisfies the only abstract shock
field, even though it is not a probability expectation.  This construction is
used solely to prove that `smear_nonexpansive` cannot support lifetime-payoff
semantics on its own. -/
noncomputable def nonexpectationalShockedParamsCounterexample
    (p : Params) : ShockedParams where
  toParams := p
  smear := fun V => -V
  smear_nonexpansive := by
    intro V W
    rw [dist_neg_neg]

@[simp] theorem nonexpectationalShockedParamsCounterexample_smear
    (p : Params) (V : SBCF) :
    (nonexpectationalShockedParamsCounterexample p).smear V = -V := rfl

/-- The formal counterexample fails constant preservation on the actual
bounded-continuous-function value space. -/
theorem nonexpectationalShockedParamsCounterexample_not_preserves_one
    (p : Params) :
    (nonexpectationalShockedParamsCounterexample p).smear (1 : SBCF) ≠
      (1 : SBCF) := by
  intro h
  have hx := congrArg (fun V : SBCF => V (Sanctions.clipS' 0)) h
  norm_num at hx

namespace ShockedParams

/-- A feasible maximizer realizes the supremum of the objective image. -/
private theorem sSup_image_eq_of_mem_isMaxOn
    {f : ℝ → ℝ} {K : Set ℝ} {a : ℝ}
    (ha : a ∈ K) (h : IsMaxOn f K a) :
    sSup (f '' K) = f a := by
  have hbdd : BddAbove (f '' K) := by
    refine ⟨f a, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact h hz
  have hne : (f '' K).Nonempty := ⟨f a, ⟨a, ha, rfl⟩⟩
  apply le_antisymm
  · exact csSup_le hne (by
      rintro _ ⟨z, hz, rfl⟩
      exact h hz)
  · exact le_csSup hbdd ⟨a, ha, rfl⟩

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- The equilibrium-derived upper Sender response attains the shocked Sender
Bellman row at every feasible state. -/
theorem sender_shocked_bellman_eq_at_top_response
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    E.V_S ⟨x, hx⟩ =
      sp.toParams.U_S x (E.α x)
          (sp.toParams.σ_dyn_top (sp.smear E.V_S) x (E.α x)) +
        sp.toParams.β_S * (sp.smear E.V_S)
          (Sanctions.clipS' (sp.toParams.F x
            (sp.toParams.σ_dyn_top (sp.smear E.V_S) x (E.α x)))) := by
  have hfix : E.V_S ⟨x, hx⟩ =
      sp.toParams.bellmanS_BCF
        E.α E.hα (sp.smear E.V_S) ⟨x, hx⟩ := by
    have h := congrArg (fun V : SBCF => V ⟨x, hx⟩) E.V_S_fix_shock
    simpa [bellmanS_shock] using h
  rw [hfix]
  change sSup ((fun s =>
      sp.toParams.integrandS
        E.α (fun y => (sp.smear E.V_S) y) (x, s)) '' Sanctions.I) =
    sp.toParams.integrandS
      E.α (fun y => (sp.smear E.V_S) y)
      (x, sp.toParams.σ_dyn_top (sp.smear E.V_S) x (E.α x))
  exact sSup_image_eq_of_mem_isMaxOn
    (sp.toParams.σ_dyn_top_mem_I
      (sp.smear E.V_S) x (E.α x))
    (sp.toParams.σ_dyn_top_isMaxOn
      (sp.smear E.V_S) x (E.α x))

/-- Every feasible Sender action has shocked one-period objective no larger
than the Sender equilibrium value. -/
theorem sender_shocked_bellman_le
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    {x s : ℝ} (hx : x ∈ Sanctions.S) (hs : s ∈ Sanctions.I) :
    sp.toParams.U_S x (E.α x) s +
        sp.toParams.β_S * (sp.smear E.V_S)
          (Sanctions.clipS' (sp.toParams.F x s)) ≤
      E.V_S ⟨x, hx⟩ := by
  rw [sp.sender_shocked_bellman_eq_at_top_response E hx]
  exact sp.toParams.σ_dyn_top_isMaxOn
    (sp.smear E.V_S) x (E.α x) hs

/-- The equilibrium Target policy attains the shocked Target Bellman row at
every feasible state, after substituting the Sender's endogenous response. -/
theorem target_shocked_bellman_eq_at_policy
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    E.V_T ⟨x, hx⟩ =
      sp.toParams.joint_T_top_integrand
        (sp.smear E.V_T) (sp.smear E.V_S) x (E.α x) := by
  calc
    E.V_T ⟨x, hx⟩ =
        sSup ((fun a => sp.toParams.joint_T_top_integrand
          (sp.smear E.V_T) (sp.smear E.V_S) x a) ''
            Sanctions.I) :=
      E.V_T_fix_shock ⟨x, hx⟩
    _ = sp.toParams.joint_T_top_integrand
          (sp.smear E.V_T) (sp.smear E.V_S) x (E.α x) :=
      sSup_image_eq_of_mem_isMaxOn
        (E.α_mem x hx) (E.α_opt_shock x hx)

/-- Every feasible Target action has shocked reduced objective no larger than
the Target equilibrium value, after substituting the Sender's endogenous upper
best response to that action. -/
theorem target_shocked_bellman_le
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    sp.toParams.joint_T_top_integrand
        (sp.smear E.V_T) (sp.smear E.V_S) x a ≤
      E.V_T ⟨x, hx⟩ := by
  rw [sp.target_shocked_bellman_eq_at_policy E hx]
  exact E.α_opt_shock x hx ha

end ShockedParams
end AbstractGame

end

end Sanctions
