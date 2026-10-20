/-
Sanctions/Theory/Equilibrium/BranchInvarianceParams.lean

**On the defiance branch the equilibrium path does not depend on the Target's
payoff, for any two economies and any two full-defiance equilibria** (round BB,
2026-09-28; doc 110, item R10(a)).

Take two economies `p₁ p₂ : Params` that agree on three things only:

* the transition on the square, `F₁(x, s) = F₂(x, s)` for `x, s ∈ [0,1]`;
* the Sender's discount factor, `β_S₁ = β_S₂`;
* the **defiance section of the Sender's payoff**, `U_S₁(x, 0, s) = U_S₂(x, 0, s)`
  for `x, s ∈ [0,1]` (the form row 49 states).

Nothing else is required to agree: the Target's payoff and discount factor, and
the Sender's payoff away from defiance, are free. Take any top-selector
feedback Stackelberg equilibrium `E₁` of `p₁` and any `E₂` of `p₂` in which the
Target defies at every feasible state (`Eᵢ.α x = 0` on `[0,1]`). Then

* the two Sender values coincide (`senderValue_eq_of_defiance_section_eq`):
  each is a fixed point of its own economy's Sender Bellman operator at its own
  policy; the operator reads the policy only on the state set
  (`bellmanS_BCF_congr_on`), so each is a fixed point of the operator at the
  constant defiance policy; the two economies' operators at that policy are the
  same map (`bellmanS_BCF_zero_eq_of_defiance_section_eq`), and it is a
  contraction of the ambient space of bounded continuous values
  (`bellmanS_BCF_contracting`), whose fixed point is unique;
* the two realised sanction rules coincide at every feasible state
  (`equilibriumRule_eq_of_defiance_section_eq`): each is the supremum of the
  Sender's dynamic argmax set at defiance, and the two argmax sets are the same
  set, because the two dynamic objectives agree on `[0,1]`
  (`dynamicArgmaxSet_zero_eq_of_defiance_section_eq`). **No argmax uniqueness is
  used**: the top selector is the supremum of identical sets;
* the two equilibrium state paths, and the sanctions realised along them,
  coincide from every feasible start (`equilibriumPath_eq_of_defiance_section_eq`,
  `equilibriumSanction_eq_of_defiance_section_eq`), by induction, since the paths
  stay in `[0,1]` and the transitions agree there.

`defiance_branch_invariance_generalF` bundles the three.

**Scope (Rule 9).** This is a universal statement over every pair of
full-defiance equilibria of every pair of economies with the stated agreement.
It is *conditional on the two equilibria existing*: it constructs nothing, and
says nothing about economies that have no full-defiance equilibrium, or about
equilibria in which the Target complies somewhere. It says nothing about the
Target's value (which does change with the Target's payoff), nor about the
Sender's off-path responses to compliance `a ≠ 0` (which change with the
Sender's payoff away from defiance). The chord-family instance, including the
existing row 49 as a corollary, is in
`Examples/PlacableSenderBranchInvarianceParams.lean`.

**Rule 1.** Both equilibria are arbitrary `FeedbackStackelbergEquilibriumTop`s:
the Target's policy is its Bellman argmax, the Sender's rule is the top
selector of its dynamic argmax. The premise `α ≡ 0` restricts which
equilibria the statement is about; it does not impose a strategy.

**Rule 22.** General in `F`: the transition enters only through `p.F`, and the
hypothesis is agreement of the two transitions on the square, with no
functional form. General in the payoffs: `U_S` and `U_T` are the abstract
`Params` payoffs.

**Rule 3.** No new assumption. The premises are the three agreement conditions
of row 49 (with the transition agreement weakened from equality of functions to
agreement on the square) and the class restriction `α ≡ 0` on each equilibrium.
No margin, no argmax uniqueness, no carrier. Rule 19: the file mentions
`Params`, so it lives in `Theory/`; it uses no external theory beyond the
Banach fixed point already wired in `BellmanS.lean`.
-/
import Sanctions.Theory.Equilibrium.CertifiedEquilibria
import Sanctions.Theory.LockIn.DifferentPolicyComparator

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

noncomputable section

/-- **The Sender Bellman operators at defiance coincide.** If two economies have
the same transition on the square, the same Sender discount factor and the same
Sender payoff at defiance, then their Sender Bellman operators at the constant
defiance policy are the same map on bounded continuous values. General in `F`. -/
theorem bellmanS_BCF_zero_eq_of_defiance_section_eq {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    p₁.bellmanS_BCF (fun _ => 0) continuous_const V
      = p₂.bellmanS_BCF (fun _ => 0) continuous_const V := by
  ext y
  change sSup ((fun s => p₁.integrandS (fun _ => 0) (fun x => V x) (y.val, s)) '' Sanctions.I)
    = sSup ((fun s => p₂.integrandS (fun _ => 0) (fun x => V x) (y.val, s)) '' Sanctions.I)
  congr 1
  refine Set.image_congr fun s hs => ?_
  simp only [integrandS]
  rw [hUS y.val y.property s hs, hF y.val y.property s hs, hβS]

/-- **A full-defiance equilibrium's Sender value is a fixed point of the Sender
operator at defiance.** The equilibrium's own operator reads the policy only on
the state set, where the policy is zero. General in `F`. -/
theorem FeedbackStackelbergEquilibriumTop.isFixedPt_bellmanS_zero_of_policy_zero {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, E.α x = 0) :
    Function.IsFixedPt (p.bellmanS_BCF (fun _ => 0) continuous_const) E.V_S := by
  change p.bellmanS_BCF (fun _ => 0) continuous_const E.V_S = E.V_S
  rw [← p.bellmanS_BCF_congr_on E.hα continuous_const hα E.V_S]
  exact E.V_S_fix.symm

/-- **A full-defiance equilibrium's Sender value is the abstract Sender value at
the defiance policy**, `p.V_S (fun _ => 0)`: the unique fixed point of the
contracting Sender operator at defiance. General in `F`. -/
theorem FeedbackStackelbergEquilibriumTop.V_S_eq_V_S_zero_of_policy_zero {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, E.α x = 0) :
    E.V_S = p.V_S (fun _ => 0) continuous_const :=
  (p.bellmanS_BCF_contracting continuous_const).fixedPoint_unique
    (E.isFixedPt_bellmanS_zero_of_policy_zero hα)

/-- **The Sender values of any two full-defiance equilibria coincide**, for two
economies with the same transition on the square, the same Sender discount
factor and the same Sender payoff at defiance. Both values are fixed points of
one contraction of the ambient value space. No margin, no uniqueness of the
Sender's argmax, and nothing about the Target's payoff. General in `F`. -/
theorem senderValue_eq_of_defiance_section_eq {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (E₁ : p₁.FeedbackStackelbergEquilibriumTop) (E₂ : p₂.FeedbackStackelbergEquilibriumTop)
    (hα₁ : ∀ x ∈ Sanctions.I, E₁.α x = 0) (hα₂ : ∀ x ∈ Sanctions.I, E₂.α x = 0) :
    E₁.V_S = E₂.V_S := by
  have h₁ := E₁.isFixedPt_bellmanS_zero_of_policy_zero hα₁
  have h₂ : Function.IsFixedPt (p₁.bellmanS_BCF (fun _ => 0) continuous_const) E₂.V_S := by
    change p₁.bellmanS_BCF (fun _ => 0) continuous_const E₂.V_S = E₂.V_S
    rw [bellmanS_BCF_zero_eq_of_defiance_section_eq hF hβS hUS]
    exact E₂.isFixedPt_bellmanS_zero_of_policy_zero hα₂
  exact (p₁.bellmanS_BCF_contracting (α := fun _ => 0) continuous_const).fixedPoint_unique' h₁ h₂

/-- **The Sender's dynamic argmax sets at defiance coincide** at every feasible
state and every continuation value, for two economies with the same transition
on the square, the same Sender discount factor and the same Sender payoff at
defiance: the two dynamic objectives agree on `[0,1]`. General in `F`. -/
theorem dynamicArgmaxSet_zero_eq_of_defiance_section_eq {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} (hx : x ∈ Sanctions.I) :
    p₁.dynamicArgmaxSet V x 0 = p₂.dynamicArgmaxSet V x 0 := by
  have hobj : ∀ s ∈ Sanctions.I,
      p₁.U_S x 0 s + p₁.β_S * V (Sanctions.clipS' (p₁.F x s))
        = p₂.U_S x 0 s + p₂.β_S * V (Sanctions.clipS' (p₂.F x s)) := fun s hs => by
    rw [hUS x hx s hs, hF x hx s hs, hβS]
  ext s
  simp only [dynamicArgmaxSet, Set.mem_setOf_eq]
  refine and_congr_right fun hs => ?_
  simp only [isMaxOn_iff]
  refine forall₂_congr fun s' hs' => ?_
  rw [hobj s hs, hobj s' hs']

/-- **The realised sanction rules of any two full-defiance equilibria coincide**
at every feasible state. Each rule is the top selector — the supremum of the
Sender's dynamic argmax set at defiance and at the equilibrium's own Sender
value — and the two sets are the same set. No argmax uniqueness is used.
General in `F`. -/
theorem equilibriumRule_eq_of_defiance_section_eq {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (E₁ : p₁.FeedbackStackelbergEquilibriumTop) (E₂ : p₂.FeedbackStackelbergEquilibriumTop)
    (hα₁ : ∀ x ∈ Sanctions.I, E₁.α x = 0) (hα₂ : ∀ x ∈ Sanctions.I, E₂.α x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    p₁.dynamicEquilibriumRule E₁ x = p₂.dynamicEquilibriumRule E₂ x := by
  have hV := senderValue_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂
  change p₁.σ_dyn_top E₁.V_S x (E₁.α x) = p₂.σ_dyn_top E₂.V_S x (E₂.α x)
  rw [hα₁ x hx, hα₂ x hx, hV]
  unfold σ_dyn_top
  rw [dynamicArgmaxSet_zero_eq_of_defiance_section_eq hF hβS hUS E₂.V_S hx]

/-- **The equilibrium state paths of any two full-defiance equilibria coincide**
from every feasible start, at every date. The paths stay in `[0,1]`, where the
rules and the transitions agree. General in `F`. -/
theorem equilibriumPath_eq_of_defiance_section_eq {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (E₁ : p₁.FeedbackStackelbergEquilibriumTop) (E₂ : p₂.FeedbackStackelbergEquilibriumTop)
    (hα₁ : ∀ x ∈ Sanctions.I, E₁.α x = 0) (hα₂ : ∀ x ∈ Sanctions.I, E₂.α x = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, p₁.rulePathF (p₁.dynamicEquilibriumRule E₁) x₀ t
      = p₂.rulePathF (p₂.dynamicEquilibriumRule E₂) x₀ t := by
  intro t
  induction t with
  | zero => simp only [rulePathF_zero]
  | succ t ih =>
      have hy : p₁.rulePathF (p₁.dynamicEquilibriumRule E₁) x₀ t ∈ Sanctions.I :=
        p₁.rulePathF_mem_I (fun x _ => p₁.dynamicTopRealizedRule_mem E₁.V_S E₁.α x) hx₀ t
      rw [rulePathF_succ, rulePathF_succ, ruleStepF, ruleStepF, ← ih,
        equilibriumRule_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂ hy,
        hF _ hy (p₂.dynamicEquilibriumRule E₂ _) (p₂.dynamicTopRealizedRule_mem E₂.V_S E₂.α _)]

/-- **The sanctions realised along the two equilibrium paths coincide** from
every feasible start, at every date. General in `F`. -/
theorem equilibriumSanction_eq_of_defiance_section_eq {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (E₁ : p₁.FeedbackStackelbergEquilibriumTop) (E₂ : p₂.FeedbackStackelbergEquilibriumTop)
    (hα₁ : ∀ x ∈ Sanctions.I, E₁.α x = 0) (hα₂ : ∀ x ∈ Sanctions.I, E₂.α x = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    p₁.dynamicEquilibriumRule E₁ (p₁.rulePathF (p₁.dynamicEquilibriumRule E₁) x₀ t)
      = p₂.dynamicEquilibriumRule E₂ (p₂.rulePathF (p₂.dynamicEquilibriumRule E₂) x₀ t) := by
  have hy : p₁.rulePathF (p₁.dynamicEquilibriumRule E₁) x₀ t ∈ Sanctions.I :=
    p₁.rulePathF_mem_I (fun x _ => p₁.dynamicTopRealizedRule_mem E₁.V_S E₁.α x) hx₀ t
  rw [← equilibriumPath_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂ hx₀ t]
  exact equilibriumRule_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂ hy

/-- **Branch invariance, general in `F` and in the payoffs, over every pair of
full-defiance equilibria.** For two economies with the same transition on the
square, the same Sender discount factor and the same Sender payoff at defiance,
and for any full-defiance equilibrium of each: (i) the Sender values coincide;
(ii) the realised sanction rules coincide at every feasible state; (iii) from
every feasible start, the equilibrium state paths and the sanctions realised
along them coincide at every date. The Target's payoff and discount factor, and
the Sender's payoff away from defiance, are unrestricted. Conditional on the two
equilibria existing; no margin and no argmax uniqueness. -/
theorem defiance_branch_invariance_generalF {p₁ p₂ : Params}
    (hF : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s)
    (hβS : p₁.β_S = p₂.β_S)
    (hUS : ∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s)
    (E₁ : p₁.FeedbackStackelbergEquilibriumTop) (E₂ : p₂.FeedbackStackelbergEquilibriumTop)
    (hα₁ : ∀ x ∈ Sanctions.I, E₁.α x = 0) (hα₂ : ∀ x ∈ Sanctions.I, E₂.α x = 0) :
    E₁.V_S = E₂.V_S ∧
    (∀ x ∈ Sanctions.I, p₁.dynamicEquilibriumRule E₁ x = p₂.dynamicEquilibriumRule E₂ x) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t,
      p₁.rulePathF (p₁.dynamicEquilibriumRule E₁) x₀ t
          = p₂.rulePathF (p₂.dynamicEquilibriumRule E₂) x₀ t ∧
        p₁.dynamicEquilibriumRule E₁ (p₁.rulePathF (p₁.dynamicEquilibriumRule E₁) x₀ t)
          = p₂.dynamicEquilibriumRule E₂ (p₂.rulePathF (p₂.dynamicEquilibriumRule E₂) x₀ t)) :=
  ⟨senderValue_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂,
   fun _ hx => equilibriumRule_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂ hx,
   fun _ hx₀ t =>
     ⟨equilibriumPath_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂ hx₀ t,
      equilibriumSanction_eq_of_defiance_section_eq hF hβS hUS E₁ E₂ hα₁ hα₂ hx₀ t⟩⟩

end

#print axioms bellmanS_BCF_zero_eq_of_defiance_section_eq
#print axioms FeedbackStackelbergEquilibriumTop.isFixedPt_bellmanS_zero_of_policy_zero
#print axioms FeedbackStackelbergEquilibriumTop.V_S_eq_V_S_zero_of_policy_zero
#print axioms senderValue_eq_of_defiance_section_eq
#print axioms dynamicArgmaxSet_zero_eq_of_defiance_section_eq
#print axioms equilibriumRule_eq_of_defiance_section_eq
#print axioms equilibriumPath_eq_of_defiance_section_eq
#print axioms equilibriumSanction_eq_of_defiance_section_eq
#print axioms defiance_branch_invariance_generalF

end Params
end AbstractGame
end Sanctions
