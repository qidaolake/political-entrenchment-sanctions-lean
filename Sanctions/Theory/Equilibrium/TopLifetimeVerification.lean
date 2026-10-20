/-
Sanctions/Theory/Equilibrium/TopLifetimeVerification.lean

**Lifetime verification for the top-selector feedback Stackelberg equilibrium.**

`Foundations/InfiniteHorizonVerification` proves, for an abstract two-player
Stackelberg feedback equilibrium, that each player's discounted lifetime payoff
along the equilibrium equals its value, and that each player's equilibrium
policy beats every time-dependent Markov deviation — the leader against the
follower's fixed contingent response, the follower against the leader's fixed
policy. `Theory/Equilibrium/StackelbergFeedback` bridges the *ordinary*
equilibrium (choice selector `σ_dyn`) into that structure. Nothing bridged the
*top-selector* equilibrium `FeedbackStackelbergEquilibriumTop`, which is the
one every constructed equilibrium in this development inhabits, so the
strongest deviation statement available for it was the one-shot bound
(doc 52 §3.3). This file supplies the bridge and the four consequences.

**Rule 15.** Every theorem here *consumes* a supplied equilibrium `E` and is
named `_top`; none constructs one. What is derived is the lifetime content of
the Bellman equations `E` carries. The uniform bounds the generic library
needs are derived, not assumed: stage payoffs are continuous on the compact
cube, values are bounded continuous functions.

**Scope.** Sections 1–5: deviations are `MarkovPlan ↥S ↥I = ℕ → ↥S → ↥I`,
time-dependent Markov plans. Section 6 (round AE, 2026-09-20, doc 94 H3)
extends the two optimality statements to **pure history-dependent** deviations
`HistoryPlan ↥S ↥I = List (↥S × ↥I) → ↥S → ↥I`, and adds the Sender's node after
an arbitrary observed compliance, through the deterministic replay reduction of
`Foundations/HistoryDependentDeviations`. Nothing here quantifies over
randomised plans, nothing here characterises other equilibria that
history-dependent strategies might support, and the leader's deviation is a
unilateral change of its own actions against the follower's fixed contingent
response — not a commitment to a new stationary policy with a follower re-solve
(the SSSE distinction recorded in `JointPreferenceBasin`).
-/
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Equilibrium.StackelbergFeedback
import Sanctions.Foundations.InfiniteHorizonVerification
import Sanctions.Foundations.HistoryDependentDeviations

namespace Sanctions

open Set BoundedContinuousFunction
open Sanctions.InfiniteHorizonVerification
open Sanctions.MultistageGames.StackelbergFeedbackEquilibrium

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The Sender Bellman equation at the top selector -/

/-- **Sender Bellman equation evaluated at `α`, top selector.** The Sender's
value equals its stage payoff plus discounted continuation at the leader's
policy and the greatest forward-looking argmax `σ_dyn_top`. Mirror of
`FeedbackStackelbergEquilibrium.sender_value_at_alpha`. -/
theorem FeedbackStackelbergEquilibriumTop.sender_value_at_alpha_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) :
    ∀ x : ↥(Sanctions.S : Set ℝ),
      E.V_S x =
        p.U_S x.val (E.α x.val) (p.σ_dyn_top E.V_S x.val (E.α x.val))
        + p.β_S * E.V_S (Sanctions.clipS'
            (p.F x.val (p.σ_dyn_top E.V_S x.val (E.α x.val)))) := by
  intro x
  have h_fix : E.V_S x = p.bellmanS_BCF E.α E.hα E.V_S x := by
    rw [← E.V_S_fix]
  rw [h_fix]
  change sSup ((fun s => p.integrandS E.α (fun y => E.V_S y) (x.val, s))
                  '' Sanctions.I) = _
  apply le_antisymm
  · apply csSup_le
    · refine ⟨_, ⟨0, by simp [Sanctions.I], rfl⟩⟩
    · rintro y ⟨s, hs, rfl⟩
      have h_max := p.σ_dyn_top_isMaxOn E.V_S x.val (E.α x.val) hs
      change p.integrandS E.α (fun y => E.V_S y) (x.val, s) ≤ _
      unfold AbstractGame.Params.integrandS
      exact h_max
  · have h_bdd : BddAbove
        ((fun s => p.integrandS E.α (fun y => E.V_S y) (x.val, s))
            '' Sanctions.I) :=
      p.integrandS_image_bddAbove E.hα E.V_S.continuous x.val
    apply le_csSup h_bdd
    refine ⟨p.σ_dyn_top E.V_S x.val (E.α x.val),
            p.σ_dyn_top_mem_I E.V_S x.val (E.α x.val), ?_⟩
    rfl

/-! ## 2. The abstract data of the game, over the feasible subtypes -/

/-- The Target's stage payoff over feasible states and actions. -/
def topG₁ : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ℝ :=
  fun x a s => p.U_T x.val a.val s.val

/-- The Sender's stage payoff over feasible states and actions. -/
def topG₂ : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ℝ :=
  fun x a s => p.U_S x.val a.val s.val

/-- The transition over feasible states and actions: the general field `F`,
clipped back into the state set (the clip is the identity on feasible
successors, `clipS'_val_eq_of_mem`). Compliance does not enter it. -/
def topF : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.I : Set ℝ)
    → ↥(Sanctions.S : Set ℝ) :=
  fun x _ s => Sanctions.clipS' (p.F x.val s.val)

/-! ## 3. The bridge -/

/-- **Bridge: the top-selector equilibrium is a Krawczyk–Petkov abstract
Stackelberg feedback equilibrium.** Follower response `σ_dyn_top E.V_S`, leader
policy `E.α` on feasible states; the four abstract conditions are
`σ_dyn_top_isMaxOn`, `α_opt_top`, `target_value_at_alpha_top`, and
`sender_value_at_alpha_top`. -/
def FeedbackStackelbergEquilibriumTop.toAbstractStackelbergTop
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) :
    Sanctions.MultistageGames.StackelbergFeedbackEquilibrium
      p.topG₁ p.topG₂ p.topF p.β_T p.β_S where
  W₁ := fun x => E.V_T x
  W₂ := fun x => E.V_S x
  r  := fun x a => ⟨p.σ_dyn_top E.V_S x.val a.val, p.σ_dyn_top_mem_I E.V_S x.val a.val⟩
  α₁ := fun x => ⟨E.α x.val, E.α_mem x.val x.property⟩
  hr := by
    intro x u₁ u₂
    exact p.σ_dyn_top_isMaxOn E.V_S x.val u₁.val u₂.property
  hα := by
    intro x u₁
    exact E.α_opt_top x.val x.property u₁.property
  hW₁_bellman := by
    intro x
    exact E.target_value_at_alpha_top x
  hW₂_bellman := by
    intro x
    exact E.sender_value_at_alpha_top x

/-! ## 4. The uniform bounds, derived -/

/-- The Target's stage payoff is bounded on the feasible cube. -/
theorem exists_bound_U_T : ∃ M : ℝ, ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
    |p.U_T x a s| ≤ M := by
  have hK : IsCompact ((Sanctions.I : Set ℝ) ×ˢ ((Sanctions.I : Set ℝ) ×ˢ (Sanctions.I : Set ℝ))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn p.U_T_continuous.continuousOn
  refine ⟨M, fun x hx a ha s hs => ?_⟩
  have := hM (x, a, s) ⟨hx, ha, hs⟩
  simpa [Real.norm_eq_abs] using this

/-- The Sender's stage payoff is bounded on the feasible cube. -/
theorem exists_bound_U_S : ∃ M : ℝ, ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
    |p.U_S x a s| ≤ M := by
  have hK : IsCompact ((Sanctions.I : Set ℝ) ×ˢ ((Sanctions.I : Set ℝ) ×ˢ (Sanctions.I : Set ℝ))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn p.U_S_continuous.continuousOn
  refine ⟨M, fun x hx a ha s hs => ?_⟩
  have := hM (x, a, s) ⟨hx, ha, hs⟩
  simpa [Real.norm_eq_abs] using this

theorem topG₁_bound : ∃ M : ℝ, ∀ x a s, |p.topG₁ x a s| ≤ M := by
  obtain ⟨M, hM⟩ := p.exists_bound_U_T
  exact ⟨M, fun x a s => hM x.val x.property a.val a.property s.val s.property⟩

theorem topG₂_bound : ∃ M : ℝ, ∀ x a s, |p.topG₂ x a s| ≤ M := by
  obtain ⟨M, hM⟩ := p.exists_bound_U_S
  exact ⟨M, fun x a s => hM x.val x.property a.val a.property s.val s.property⟩

/-! ## 5. The four lifetime consequences -/

/-- **The Target's lifetime payoff along the equilibrium equals its value.** -/
theorem FeedbackStackelbergEquilibriumTop.leader_discountedPayoff_eq_value_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) (x₀ : ↥(Sanctions.S : Set ℝ)) :
    discountedPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T
        (stationaryPlan E.toAbstractStackelbergTop.α₁) x₀
      = E.V_T x₀ := by
  obtain ⟨M, hM⟩ := p.topG₁_bound
  exact leader_discountedPayoff_eq_value E.toAbstractStackelbergTop p.β_T_mem.1 p.β_T_mem.2
    M ‖E.V_T‖ hM (fun x => E.V_T.norm_coe_le_norm x) x₀

/-- **The Sender's lifetime payoff along the equilibrium equals its value.** -/
theorem FeedbackStackelbergEquilibriumTop.follower_discountedPayoff_eq_value_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) (x₀ : ↥(Sanctions.S : Set ℝ)) :
    discountedPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S
        (stationaryPlan fun x => E.toAbstractStackelbergTop.r x
          (E.toAbstractStackelbergTop.α₁ x)) x₀
      = E.V_S x₀ := by
  obtain ⟨M, hM⟩ := p.topG₂_bound
  exact follower_discountedPayoff_eq_value E.toAbstractStackelbergTop p.β_S_mem.1 p.β_S_mem.2
    M ‖E.V_S‖ hM (fun x => E.V_S.norm_coe_le_norm x) x₀

/-- **The Target's equilibrium policy beats every time-dependent Markov
deviation**, against the Sender's fixed contingent response `σ_dyn_top E.V_S`.
Conditional on the supplied equilibrium (Rule 15); no bound is assumed. -/
theorem FeedbackStackelbergEquilibriumTop.leader_optimal_against_markov_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    (π₁ : MarkovPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    discountedPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T π₁ x₀
      ≤ discountedPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T
        (stationaryPlan E.toAbstractStackelbergTop.α₁) x₀ := by
  obtain ⟨M, hM⟩ := p.topG₁_bound
  exact leader_optimal_against_markov_deviation E.toAbstractStackelbergTop p.β_T_mem.1
    p.β_T_mem.2 M ‖E.V_T‖ hM (fun x => E.V_T.norm_coe_le_norm x) π₁ x₀

/-- **The Sender's equilibrium response beats every time-dependent Markov
deviation**, with the Target held at its equilibrium policy. -/
theorem FeedbackStackelbergEquilibriumTop.follower_optimal_against_markov_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    (π₂ : MarkovPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    discountedPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S π₂ x₀
      ≤ discountedPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S
        (stationaryPlan fun x => E.toAbstractStackelbergTop.r x
          (E.toAbstractStackelbergTop.α₁ x)) x₀ := by
  obtain ⟨M, hM⟩ := p.topG₂_bound
  exact follower_optimal_against_markov_deviation E.toAbstractStackelbergTop p.β_S_mem.1
    p.β_S_mem.2 M ‖E.V_S‖ hM (fun x => E.V_S.norm_coe_le_norm x) π₂ x₀

/-! ## 6. Pure history-dependent deviations (round AE, doc 94 H3)

The conflict literature states its equilibria over strategies that condition on
the whole past. The game here is deterministic with perfect monitoring, so a
pure history-dependent deviation generates one action sequence from a given
start and is reproduced, state for state and payoff for payoff, by a dated plan
(`historyDiscountedPayoff_eq_replay`). The three statements below therefore
hold for **every** top-selector equilibrium, in particular for each of the four
constructed regimes. They say the supplied stationary profile is unimprovable
by such deviations; they do not say it is the only equilibrium. -/

/-- **The Target's equilibrium policy beats every pure history-dependent
deviation**, against the Sender's fixed contingent response `σ_dyn_top E.V_S`. -/
theorem FeedbackStackelbergEquilibriumTop.leader_optimal_against_history_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    (σ₁ : HistoryPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    historyDiscountedPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T σ₁ x₀
      ≤ discountedPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T
        (stationaryPlan E.toAbstractStackelbergTop.α₁) x₀ := by
  obtain ⟨M, hM⟩ := p.topG₁_bound
  exact leader_optimal_against_history_deviation E.toAbstractStackelbergTop p.β_T_mem.1
    p.β_T_mem.2 M ‖E.V_T‖ hM (fun x => E.V_T.norm_coe_le_norm x) σ₁ x₀

/-- **The Sender's equilibrium response beats every pure history-dependent
deviation**, with the Target held at its equilibrium policy. -/
theorem FeedbackStackelbergEquilibriumTop.follower_optimal_against_history_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    (σ₂ : HistoryPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    historyDiscountedPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S σ₂ x₀
      ≤ discountedPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S
        (stationaryPlan fun x => E.toAbstractStackelbergTop.r x
          (E.toAbstractStackelbergTop.α₁ x)) x₀ := by
  obtain ⟨M, hM⟩ := p.topG₂_bound
  exact follower_optimal_against_history_deviation E.toAbstractStackelbergTop p.β_S_mem.1
    p.β_S_mem.2 M ‖E.V_S‖ hM (fun x => E.V_S.norm_coe_le_norm x) σ₂ x₀

/-- **The Sender's node after an arbitrary observed compliance.** At every
feasible state and after every feasible compliance action — on or off the
equilibrium path — no current sanction followed by any pure history-dependent
continuation does better for the Sender than the equilibrium response followed
by equilibrium play. -/
theorem FeedbackStackelbergEquilibriumTop.follower_node_optimal_against_history_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    (x : ↥(Sanctions.S : Set ℝ)) (a s : ↥(Sanctions.I : Set ℝ))
    (σ₂ : HistoryPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ)) :
    p.topG₂ x a s + p.β_S * historyDiscountedPayoff
        (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S σ₂ (p.topF x a s)
      ≤ p.topG₂ x a (E.toAbstractStackelbergTop.r x a)
        + p.β_S * E.V_S (p.topF x a (E.toAbstractStackelbergTop.r x a)) := by
  obtain ⟨M, hM⟩ := p.topG₂_bound
  exact follower_node_optimal_against_history_deviation E.toAbstractStackelbergTop p.β_S_mem.1
    p.β_S_mem.2 M ‖E.V_S‖ hM (fun x => E.V_S.norm_coe_le_norm x) x a s σ₂

/-! ### Finite mixtures (round AJ, 2026-09-22; doc 98 B7)

An ex-ante lottery over finitely many pure history-dependent deviations has
expected payoff at most the stationary payoff, for either player, because each
pure deviation does. The statements concern finite ex-ante mixtures only, not
behaviour strategies or measures over plans. -/

/-- **The Target's equilibrium policy beats every finite mixture of pure
history-dependent deviations.** -/
theorem FeedbackStackelbergEquilibriumTop.leader_optimal_against_mixed_history_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (σs : Fin n → HistoryPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    mixedHistoryPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T w σs x₀
      ≤ discountedPayoff (leaderStage p.topG₁ E.toAbstractStackelbergTop.r)
        (leaderTransition p.topF E.toAbstractStackelbergTop.r) p.β_T
        (stationaryPlan E.toAbstractStackelbergTop.α₁) x₀ := by
  obtain ⟨M, hM⟩ := p.topG₁_bound
  exact leader_optimal_against_mixed_history_deviation E.toAbstractStackelbergTop p.β_T_mem.1
    p.β_T_mem.2 M ‖E.V_T‖ hM (fun x => E.V_T.norm_coe_le_norm x) w hw hw1 σs x₀

/-- **The Sender's equilibrium response beats every finite mixture of pure
history-dependent deviations.** -/
theorem FeedbackStackelbergEquilibriumTop.follower_optimal_against_mixed_history_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (σs : Fin n → HistoryPlan ↥(Sanctions.S : Set ℝ) ↥(Sanctions.I : Set ℝ))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    mixedHistoryPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S w σs x₀
      ≤ discountedPayoff (followerStage p.topG₂ E.toAbstractStackelbergTop.α₁)
        (followerTransition p.topF E.toAbstractStackelbergTop.α₁) p.β_S
        (stationaryPlan fun x => E.toAbstractStackelbergTop.r x
          (E.toAbstractStackelbergTop.α₁ x)) x₀ := by
  obtain ⟨M, hM⟩ := p.topG₂_bound
  exact follower_optimal_against_mixed_history_deviation E.toAbstractStackelbergTop
    p.β_S_mem.1 p.β_S_mem.2 M ‖E.V_S‖ hM (fun x => E.V_S.norm_coe_le_norm x) w hw hw1 σs x₀

#print axioms FeedbackStackelbergEquilibriumTop.leader_optimal_against_mixed_history_deviation_top
#print axioms FeedbackStackelbergEquilibriumTop.follower_optimal_against_mixed_history_deviation_top

end Params
end AbstractGame

end

end Sanctions
