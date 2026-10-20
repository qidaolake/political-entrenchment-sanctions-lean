/-
Sanctions/Theory/Equilibrium/CertifiedEquilibria.lean

**Every equilibrium whose Target policy satisfies a state chord has a Sender
value with a certified lower state slope** (round AM, 2026-09-22; doc 100 §3,
deliverable A, on the user's word).

The families construct one equilibrium and certify its Sender value by an
invariant carrier. This file turns the carrier argument into a statement about
*every* top-selector equilibrium, at the general `Params` level: the Sender's
Bellman operator at a continuous Target policy `α` is a contraction on the
whole value space (`bellmanS_BCF_contracting`), the lower-slope cone
`{V | LowerSlopeOnValueOn V [0,1] g}` is closed and nonempty, and it is
invariant whenever the policy satisfies the joint state chord that
`bellmanS_BCF_preserves_lowerSlopeCone_generalF` reads. So the operator's
unique fixed point lies in the cone (Stokey–Lucas Corollary 1 to Theorem 3.2,
`fixedPoint_mem_of_mapsTo`), and the Sender value of every equilibrium at such
a policy has state slope at least `g` (`senderValue_lowerSlope_of_policy_chord`,
`FeedbackStackelbergEquilibriumTop.V_S_lowerSlope_of_policy_chord`).

**What the chord says.** For states `y₁ ≤ y₂` and every sanction `s`,
`g·(y₂ − y₁) ≤ U_S(y₂, α(y₂), s) − U_S(y₁, α(y₁), s) + β_S·g·(F(y₂,s) − F(y₁,s))`:
the stage payoff along the policy, plus the discounted continuation at slope
`g`, rises at least at rate `g`. On the project's families it reduces to one
condition on the policy — compliance nonincreasing in the state — because the
stage payoff's state slope `w` and the transition's lower chord already give
the slope `g_S = w/(1 − β_S g_lo)` and the only term that can spoil it is
`−k·s·(α(y₂) − α(y₁))` (`Examples/PlacableSenderAllEquilibria.lean`).

**Scope (Rule 9).** This is a quantifier strengthening over the families'
constructions, scoped by the policy class; it says nothing about equilibria
whose policy violates the chord, and it does not assert that any equilibrium
other than the constructed one exists. Rule 19: general `Params` only; the
wiring is in `Examples/`.
-/
import Sanctions.Theory.Bellman.SenderLowerSlopeCone
import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions
namespace AbstractGame
namespace Params

open Set Filter Topology BoundedContinuousFunction

noncomputable section

variable (p : Params)

/-- The affine value `y ↦ g·y` on the state set, a member of every lower-slope
cone with slope `g`. -/
def slopeBCF (g : ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => g * y.val) (by fun_prop))

@[simp] theorem slopeBCF_apply (g : ℝ) (y : ↥(Sanctions.S : Set ℝ)) : slopeBCF g y = g * y.val :=
  rfl

theorem slopeBCF_mem_cone (g : ℝ) : LowerSlopeOnValueOn (slopeBCF g) (Icc (0 : ℝ) 1) g := by
  intro y₁ y₂ _ _ hle
  simp only [slopeBCF_apply]
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by exact sub_nonneg.mpr hle)]
  ring_nf
  exact le_rfl

/-- **The Sender's Bellman fixed point at a chord-satisfying policy lies in the
lower-slope cone.** -/
theorem senderValue_lowerSlope_of_policy_chord
    {α : ℝ → ℝ} (hα : Continuous α) {g : ℝ}
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (hfix : p.bellmanS_BCF α hα V = V) :
    LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g := by
  have hcontr := p.bellmanS_BCF_contracting hα
  obtain ⟨W, hW, hWmem⟩ := StokeyLucas.fixedPoint_mem_of_mapsTo hcontr.1 _ hcontr.2
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ | LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g}
    (lowerSlopeOnValueOn_isClosed _ _) ⟨slopeBCF g, slopeBCF_mem_cone g⟩
    (fun V hV => p.bellmanS_BCF_preserves_lowerSlopeCone_generalF hα h_joint_state_chord hV)
  have h1 : W = hcontr.fixedPoint := hcontr.fixedPoint_unique hW
  have h2 : V = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
  rw [h2, ← h1]
  exact hWmem

/-- **Every top-selector equilibrium whose Target policy satisfies the state
chord has a Sender value with lower state slope `g`.** -/
theorem FeedbackStackelbergEquilibriumTop.V_S_lowerSlope_of_policy_chord
    (Eq : p.FeedbackStackelbergEquilibriumTop) {g : ℝ}
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (Eq.α y₂) s - p.U_S y₁ (Eq.α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s)) :
    LowerSlopeOnValueOn Eq.V_S (Icc (0 : ℝ) 1) g :=
  p.senderValue_lowerSlope_of_policy_chord Eq.hα h_joint_state_chord Eq.V_S_fix.symm

end

#print axioms senderValue_lowerSlope_of_policy_chord
#print axioms FeedbackStackelbergEquilibriumTop.V_S_lowerSlope_of_policy_chord

noncomputable section

variable (p : Params)

/-! ## Round AR (2026-09-23): three general facts for the monotone-class uniqueness

* the greatest Sender selector is antitone in compliance under decreasing
  differences of the stage payoff, with no uniqueness (the Milgrom–Shannon
  set-valued conclusion applied to the greatest maximiser);
* an equilibrium's Target value equals its joint integrand at its own policy;
* the Sender Bellman operator reads the policy on the state set only. -/

/-- **The greatest Sender selector is antitone in compliance** whenever the stage
payoff has decreasing differences in `(s, a)`; the continuation is
`a`-independent, so the differences transfer. No uniqueness is used
(`σ_dyn_top_antitoneOn_a_of_SenderActionDD` is the strict form). -/
theorem σ_dyn_top_antitoneOn_a_of_DD (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ)
    (hDD : Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => p.U_S x a s)) :
    AntitoneOn (fun a => p.σ_dyn_top V_S x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hle
  show p.σ_dyn_top V_S x a₂ ≤ p.σ_dyn_top V_S x a₁
  have hDD' : Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))) := by
    intro s₁ s₂ t t' hs₁ hs₂ hss ht ht' htt
    have := hDD hs₁ hs₂ hss ht ht' htt
    simp only at this ⊢
    linarith
  have h := Sanctions.MilgromShannon.antitone_argmax_of_decreasingDifferencesOn hDD'
    (s := p.σ_dyn_top V_S x a₁) (s' := p.σ_dyn_top V_S x a₂) hle ha₁ ha₂
    (p.σ_dyn_top_mem_I V_S x a₁) (p.σ_dyn_top_mem_I V_S x a₂)
    (fun y hy => p.σ_dyn_top_isMaxOn V_S x a₁ hy)
    (fun y hy => p.σ_dyn_top_isMaxOn V_S x a₂ hy)
  -- `max s s'` is an `a₁`-maximiser, hence at most the greatest one, `s`.
  have hm₁ := p.σ_dyn_top_mem_I V_S x a₁
  have hm₂ := p.σ_dyn_top_mem_I V_S x a₂
  have hmem : max (p.σ_dyn_top V_S x a₁) (p.σ_dyn_top V_S x a₂) ∈ p.dynamicArgmaxSet V_S x a₁ :=
    ⟨⟨le_max_of_le_left hm₁.1, max_le hm₁.2 hm₂.2⟩, isMaxOn_iff.mpr h.1⟩
  have hle' := le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a₁) hmem
  exact le_trans (le_max_right _ _) hle'

/-- **An equilibrium's Target value is its joint integrand at its own policy**,
at every feasible state: the supremum in the Bellman equation is attained at
the policy (`α_opt_top`). -/
theorem FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy
    (Eq : p.FeedbackStackelbergEquilibriumTop) (y : ↥(Sanctions.S : Set ℝ)) :
    Eq.V_T y = p.joint_T_top_integrand Eq.V_T Eq.V_S y.val (Eq.α y.val) := by
  rw [Eq.V_T_fix_top y]
  have hgt : IsGreatest ((fun a => p.joint_T_top_integrand Eq.V_T Eq.V_S y.val a) '' Sanctions.I)
      (p.joint_T_top_integrand Eq.V_T Eq.V_S y.val (Eq.α y.val)) := by
    refine ⟨⟨_, Eq.α_mem y.val y.property, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Eq.α_opt_top y.val y.property ha
  exact hgt.csSup_eq

/-- The Sender Bellman operator reads the policy on the state set only. -/
theorem bellmanS_BCF_congr_on {α₁ α₂ : ℝ → ℝ} (hα₁ : Continuous α₁) (hα₂ : Continuous α₂)
    (h : ∀ x ∈ Sanctions.S, α₁ x = α₂ x) (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    p.bellmanS_BCF α₁ hα₁ V = p.bellmanS_BCF α₂ hα₂ V := by
  ext y
  change p.bellmanS_at α₁ (fun x => V x) y.val = p.bellmanS_at α₂ (fun x => V x) y.val
  unfold bellmanS_at integrandS
  simp only [h y.val y.property]

end

#print axioms σ_dyn_top_antitoneOn_a_of_DD
#print axioms FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy
#print axioms bellmanS_BCF_congr_on

end Params
end AbstractGame
end Sanctions
