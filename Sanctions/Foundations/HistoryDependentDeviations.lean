/-
Sanctions/Foundations/HistoryDependentDeviations.lean

**Pure history-dependent deviations in a deterministic discounted problem reduce
to dated plans** (round AE, 2026-09-20; doc 94, item H3).

`Foundations/InfiniteHorizonVerification` proves that a stationary Bellman
maximiser beats every *time-dependent Markov* plan `ℕ → X → A`. The conflict
literature this project is read against states its equilibria over strategies
that condition on the whole past (Powell 2004; Leventoğlu–Slantchev 2007;
Krainin–Wiseman 2016), so the natural question is whether a stationary
equilibrium survives such deviations. In a **deterministic** problem it does,
for a textbook reason (the sequence formulation of Stokey–Lucas–Prescott §4.1;
Light 2024, *The principle of optimality in dynamic programming*, §2): from a
given start a pure history-dependent plan generates one action sequence, and
the dated plan that replays that sequence — ignoring the state argument —
generates the same states, the same actions and the same payoff. Hence every
bound proved against dated plans holds against history-dependent plans.

What is here:

* `HistoryPlan X A := List (X × A) → X → A` — the action may depend on the full
  list of past (state, own action) pairs and on the current state;
* `historyRun`, `historyState`, `historyAction`, `historyDiscountedPayoff`;
* `replayPlan` and `historyDiscountedPayoff_eq_replay` — the reduction;
* `MarkovPlan.toHistoryPlan` and `historyState_toHistoryPlan` — dated plans are
  history plans, so the class is genuinely larger;
* `stationary_optimal_against_history_deviation_of_global_bounds`;
* for an abstract two-player Stackelberg feedback equilibrium: the leader against
  the follower's fixed contingent response, the follower against the leader's
  fixed policy, and the follower **at the node after an arbitrary observed
  leader action** (`follower_node_optimal_against_history_deviation`).

In the two-player game a player's information also contains the opponent's past
actions. With the opponent held at a feedback rule those are functions of the
recorded states and own actions, so conditioning on them adds nothing; this is
why the history type records own actions only.

**Finite mixtures** (round AJ, 2026-09-22; doc 98 B7, the reader's candidate
(e)). An ex-ante lottery with finitely many outcomes over pure history plans
has expected payoff `∑ᵢ wᵢ · (payoff of plan i)`; each term is at most the
stationary payoff, so the mixture is too
(`mixedHistoryPayoff_le_stationary_of_global_bounds`). This is the linear
consequence and nothing more: it does not concern behaviour strategies that
randomise at each date, arbitrary probability measures over plans, or any
stochastic equilibrium notion.

**Scope.** Pure strategies and their finite ex-ante mixtures, deterministic
transition, perfect monitoring. Nothing here characterises *other* equilibria
that history-dependent strategies may support: the statements say that a
given stationary profile is unimprovable by such deviations, not that it is
the only equilibrium (Rule 9 spirit: no universal is licensed).

Rule 19: no `Params`, no sanctions structure; the wiring to the top-selector
equilibrium is in `Theory/Equilibrium/TopLifetimeVerification.lean`.
-/
import Sanctions.Foundations.InfiniteHorizonVerification

noncomputable section

open Filter Finset
open scoped Topology

namespace Sanctions
namespace InfiniteHorizonVerification

/-- A pure history-dependent plan: the action depends on the list of past
(state, own action) pairs, oldest first, and on the current state. -/
abbrev HistoryPlan (X A : Type*) := List (X × A) → X → A

/-- The run of a history-dependent plan: the history so far and the current state. -/
def historyRun {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A) (x₀ : X) :
    ℕ → List (X × A) × X
  | 0 => ([], x₀)
  | n + 1 =>
      ((historyRun F σ x₀ n).1 ++
          [((historyRun F σ x₀ n).2, σ (historyRun F σ x₀ n).1 (historyRun F σ x₀ n).2)],
        F (historyRun F σ x₀ n).2 (σ (historyRun F σ x₀ n).1 (historyRun F σ x₀ n).2))

/-- The state at date `n` along the run. -/
def historyState {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A) (x₀ : X) (n : ℕ) : X :=
  (historyRun F σ x₀ n).2

/-- The action taken at date `n` along the run. -/
def historyAction {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A) (x₀ : X) (n : ℕ) : A :=
  σ (historyRun F σ x₀ n).1 (historyRun F σ x₀ n).2

@[simp] theorem historyState_zero {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A)
    (x₀ : X) : historyState F σ x₀ 0 = x₀ := rfl

@[simp] theorem historyState_succ {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A)
    (x₀ : X) (n : ℕ) :
    historyState F σ x₀ (n + 1) = F (historyState F σ x₀ n) (historyAction F σ x₀ n) := rfl

/-- The recorded history at date `n` has length `n`. -/
theorem historyRun_length {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A) (x₀ : X) :
    ∀ n, (historyRun F σ x₀ n).1.length = n
  | 0 => rfl
  | n + 1 => by
      change ((historyRun F σ x₀ n).1 ++ [_]).length = n + 1
      rw [List.length_append, historyRun_length F σ x₀ n]
      rfl

/-- The discounted payoff of a history-dependent plan. -/
def historyDiscountedPayoff {X A : Type*} (u : X → A → ℝ) (F : X → A → X) (β : ℝ)
    (σ : HistoryPlan X A) (x₀ : X) : ℝ :=
  ∑' n : ℕ, β ^ n * u (historyState F σ x₀ n) (historyAction F σ x₀ n)

/-- The dated plan that replays the run's own action sequence, whatever the state. -/
def replayPlan {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A) (x₀ : X) :
    MarkovPlan X A :=
  fun n _ => historyAction F σ x₀ n

/-- The replayed plan visits the run's states. -/
theorem statePath_replayPlan {X A : Type*} (F : X → A → X) (σ : HistoryPlan X A) (x₀ : X) :
    ∀ n, statePath F (replayPlan F σ x₀) x₀ n = historyState F σ x₀ n
  | 0 => rfl
  | n + 1 => by
      rw [statePath_succ, statePath_replayPlan F σ x₀ n, historyState_succ]
      rfl

/-- **The reduction.** A history-dependent plan and its replay have the same
discounted payoff. -/
theorem historyDiscountedPayoff_eq_replay {X A : Type*} (u : X → A → ℝ) (F : X → A → X)
    (β : ℝ) (σ : HistoryPlan X A) (x₀ : X) :
    historyDiscountedPayoff u F β σ x₀ = discountedPayoff u F β (replayPlan F σ x₀) x₀ := by
  unfold historyDiscountedPayoff discountedPayoff
  refine tsum_congr fun n => ?_
  unfold discountedStage
  rw [statePath_replayPlan]
  rfl

/-- A dated plan, read as a history-dependent plan (the date is the history's length). -/
def MarkovPlan.toHistoryPlan {X A : Type*} (π : MarkovPlan X A) : HistoryPlan X A :=
  fun h x => π h.length x

/-- Dated plans are history plans: the run of `π.toHistoryPlan` is the state path of `π`. -/
theorem historyState_toHistoryPlan {X A : Type*} (F : X → A → X) (π : MarkovPlan X A)
    (x₀ : X) : ∀ n, historyState F π.toHistoryPlan x₀ n = statePath F π x₀ n
  | 0 => rfl
  | n + 1 => by
      rw [historyState_succ, statePath_succ, ← historyState_toHistoryPlan F π x₀ n]
      change F _ (π (historyRun F π.toHistoryPlan x₀ n).1.length _) = _
      rw [historyRun_length]
      rfl

/-- **A stationary Bellman maximiser is optimal against every pure
history-dependent plan**, under global payoff and value bounds. -/
theorem stationary_optimal_against_history_deviation_of_global_bounds
    {X A : Type*}
    (u : X → A → ℝ) (F : X → A → X) (β : ℝ) (V : X → ℝ) (α : X → A)
    (hβ : 0 ≤ β) (hβ_lt : β < 1)
    (h_bellman : ∀ x : X, ∀ a : A, u x a + β * V (F x a) ≤ V x)
    (h_attains : ∀ x : X, u x (α x) + β * V (F x (α x)) = V x)
    (M_u M_V : ℝ)
    (h_u_bound : ∀ x : X, ∀ a : A, |u x a| ≤ M_u)
    (h_V_bound : ∀ x : X, |V x| ≤ M_V)
    (σ : HistoryPlan X A) (x₀ : X) :
    historyDiscountedPayoff u F β σ x₀ ≤
      discountedPayoff u F β (stationaryPlan α) x₀ := by
  rw [historyDiscountedPayoff_eq_replay]
  exact stationary_optimal_against_markov_deviation_of_global_bounds u F β V α hβ hβ_lt
    h_bellman h_attains M_u M_V h_u_bound h_V_bound (replayPlan F σ x₀) x₀

/-- A Bellman supersolution bounds the payoff of every pure history-dependent plan. -/
theorem historyDiscountedPayoff_le_value_of_global_bounds
    {X A : Type*}
    (u : X → A → ℝ) (F : X → A → X) (β : ℝ) (V : X → ℝ)
    (hβ : 0 ≤ β) (hβ_lt : β < 1)
    (h_bellman : ∀ x : X, ∀ a : A, u x a + β * V (F x a) ≤ V x)
    (M_u M_V : ℝ)
    (h_u_bound : ∀ x : X, ∀ a : A, |u x a| ≤ M_u)
    (h_V_bound : ∀ x : X, |V x| ≤ M_V)
    (σ : HistoryPlan X A) (x₀ : X) :
    historyDiscountedPayoff u F β σ x₀ ≤ V x₀ := by
  rw [historyDiscountedPayoff_eq_replay]
  exact discountedPayoff_le_value_of_uniform_bounds u F β V hβ hβ_lt h_bellman
    (replayPlan F σ x₀) x₀ M_u M_V (fun _ => h_u_bound _ _) (fun _ => h_V_bound _)

/-! ### Finite ex-ante mixtures of pure history-dependent plans -/

/-- The expected discounted payoff of an ex-ante lottery over finitely many pure
history-dependent plans, with weights `w`. -/
def mixedHistoryPayoff {X A : Type*} (u : X → A → ℝ) (F : X → A → X) (β : ℝ) {n : ℕ}
    (w : Fin n → ℝ) (σs : Fin n → HistoryPlan X A) (x₀ : X) : ℝ :=
  ∑ i, w i * historyDiscountedPayoff u F β (σs i) x₀

/-- **A finite mixture of pure history-dependent plans gains nothing over a
stationary Bellman maximiser**: its expected payoff is at most the stationary
payoff. -/
theorem mixedHistoryPayoff_le_stationary_of_global_bounds
    {X A : Type*}
    (u : X → A → ℝ) (F : X → A → X) (β : ℝ) (V : X → ℝ) (α : X → A)
    (hβ : 0 ≤ β) (hβ_lt : β < 1)
    (h_bellman : ∀ x : X, ∀ a : A, u x a + β * V (F x a) ≤ V x)
    (h_attains : ∀ x : X, u x (α x) + β * V (F x (α x)) = V x)
    (M_u M_V : ℝ)
    (h_u_bound : ∀ x : X, ∀ a : A, |u x a| ≤ M_u)
    (h_V_bound : ∀ x : X, |V x| ≤ M_V)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (σs : Fin n → HistoryPlan X A) (x₀ : X) :
    mixedHistoryPayoff u F β w σs x₀ ≤
      discountedPayoff u F β (stationaryPlan α) x₀ := by
  unfold mixedHistoryPayoff
  calc ∑ i, w i * historyDiscountedPayoff u F β (σs i) x₀
      ≤ ∑ i, w i * discountedPayoff u F β (stationaryPlan α) x₀ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (stationary_optimal_against_history_deviation_of_global_bounds u F β V α hβ hβ_lt
            h_bellman h_attains M_u M_V h_u_bound h_V_bound (σs i) x₀) (hw i)
    _ = discountedPayoff u F β (stationaryPlan α) x₀ := by
        rw [← Finset.sum_mul, hw1, one_mul]

/-- A Bellman supersolution bounds the expected payoff of every finite mixture. -/
theorem mixedHistoryPayoff_le_value_of_global_bounds
    {X A : Type*}
    (u : X → A → ℝ) (F : X → A → X) (β : ℝ) (V : X → ℝ)
    (hβ : 0 ≤ β) (hβ_lt : β < 1)
    (h_bellman : ∀ x : X, ∀ a : A, u x a + β * V (F x a) ≤ V x)
    (M_u M_V : ℝ)
    (h_u_bound : ∀ x : X, ∀ a : A, |u x a| ≤ M_u)
    (h_V_bound : ∀ x : X, |V x| ≤ M_V)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (σs : Fin n → HistoryPlan X A) (x₀ : X) :
    mixedHistoryPayoff u F β w σs x₀ ≤ V x₀ := by
  unfold mixedHistoryPayoff
  calc ∑ i, w i * historyDiscountedPayoff u F β (σs i) x₀
      ≤ ∑ i, w i * V x₀ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (historyDiscountedPayoff_le_value_of_global_bounds u F β V hβ hβ_lt h_bellman
            M_u M_V h_u_bound h_V_bound (σs i) x₀) (hw i)
    _ = V x₀ := by rw [← Finset.sum_mul, hw1, one_mul]

end InfiniteHorizonVerification

/-! ## The two players of an abstract Stackelberg feedback equilibrium -/

namespace MultistageGames.StackelbergFeedbackEquilibrium

open InfiniteHorizonVerification

/-- **The leader's equilibrium policy beats every pure history-dependent leader
deviation**, against the follower's fixed contingent response. -/
theorem leader_optimal_against_history_deviation
    {X A₁ A₂ : Type*}
    {g₁ g₂ : X → A₁ → A₂ → ℝ} {F : X → A₁ → A₂ → X} {β₁ β₂ : ℝ}
    (E : Sanctions.MultistageGames.StackelbergFeedbackEquilibrium g₁ g₂ F β₁ β₂)
    (hβ₁ : 0 ≤ β₁) (hβ₁_lt : β₁ < 1)
    (M_g₁ M_W₁ : ℝ)
    (h_g₁_bound : ∀ x : X, ∀ a₁ : A₁, ∀ a₂ : A₂, |g₁ x a₁ a₂| ≤ M_g₁)
    (h_W₁_bound : ∀ x : X, |E.W₁ x| ≤ M_W₁)
    (σ₁ : HistoryPlan X A₁) (x₀ : X) :
    historyDiscountedPayoff (leaderStage g₁ E.r) (leaderTransition F E.r) β₁ σ₁ x₀ ≤
      discountedPayoff (leaderStage g₁ E.r) (leaderTransition F E.r) β₁
        (stationaryPlan E.α₁) x₀ := by
  rw [historyDiscountedPayoff_eq_replay]
  exact leader_optimal_against_markov_deviation E hβ₁ hβ₁_lt M_g₁ M_W₁ h_g₁_bound h_W₁_bound
    (replayPlan (leaderTransition F E.r) σ₁ x₀) x₀

/-- **The follower's equilibrium response beats every pure history-dependent
follower deviation**, with the leader at its equilibrium feedback policy. -/
theorem follower_optimal_against_history_deviation
    {X A₁ A₂ : Type*}
    {g₁ g₂ : X → A₁ → A₂ → ℝ} {F : X → A₁ → A₂ → X} {β₁ β₂ : ℝ}
    (E : Sanctions.MultistageGames.StackelbergFeedbackEquilibrium g₁ g₂ F β₁ β₂)
    (hβ₂ : 0 ≤ β₂) (hβ₂_lt : β₂ < 1)
    (M_g₂ M_W₂ : ℝ)
    (h_g₂_bound : ∀ x : X, ∀ a₁ : A₁, ∀ a₂ : A₂, |g₂ x a₁ a₂| ≤ M_g₂)
    (h_W₂_bound : ∀ x : X, |E.W₂ x| ≤ M_W₂)
    (σ₂ : HistoryPlan X A₂) (x₀ : X) :
    historyDiscountedPayoff (followerStage g₂ E.α₁) (followerTransition F E.α₁) β₂ σ₂ x₀ ≤
      discountedPayoff (followerStage g₂ E.α₁) (followerTransition F E.α₁) β₂
        (stationaryPlan fun x => E.r x (E.α₁ x)) x₀ := by
  rw [historyDiscountedPayoff_eq_replay]
  exact follower_optimal_against_markov_deviation E hβ₂ hβ₂_lt M_g₂ M_W₂ h_g₂_bound h_W₂_bound
    (replayPlan (followerTransition F E.α₁) σ₂ x₀) x₀

/-- **The leader's equilibrium policy beats every finite mixture of pure
history-dependent leader deviations.** -/
theorem leader_optimal_against_mixed_history_deviation
    {X A₁ A₂ : Type*}
    {g₁ g₂ : X → A₁ → A₂ → ℝ} {F : X → A₁ → A₂ → X} {β₁ β₂ : ℝ}
    (E : Sanctions.MultistageGames.StackelbergFeedbackEquilibrium g₁ g₂ F β₁ β₂)
    (hβ₁ : 0 ≤ β₁) (hβ₁_lt : β₁ < 1)
    (M_g₁ M_W₁ : ℝ)
    (h_g₁_bound : ∀ x : X, ∀ a₁ : A₁, ∀ a₂ : A₂, |g₁ x a₁ a₂| ≤ M_g₁)
    (h_W₁_bound : ∀ x : X, |E.W₁ x| ≤ M_W₁)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (σs : Fin n → HistoryPlan X A₁) (x₀ : X) :
    mixedHistoryPayoff (leaderStage g₁ E.r) (leaderTransition F E.r) β₁ w σs x₀ ≤
      discountedPayoff (leaderStage g₁ E.r) (leaderTransition F E.r) β₁
        (stationaryPlan E.α₁) x₀ := by
  unfold mixedHistoryPayoff
  calc ∑ i, w i * historyDiscountedPayoff (leaderStage g₁ E.r) (leaderTransition F E.r) β₁
        (σs i) x₀
      ≤ ∑ i, w i * discountedPayoff (leaderStage g₁ E.r) (leaderTransition F E.r) β₁
        (stationaryPlan E.α₁) x₀ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (leader_optimal_against_history_deviation E hβ₁ hβ₁_lt
          M_g₁ M_W₁ h_g₁_bound h_W₁_bound (σs i) x₀) (hw i)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **The follower's equilibrium response beats every finite mixture of pure
history-dependent follower deviations.** -/
theorem follower_optimal_against_mixed_history_deviation
    {X A₁ A₂ : Type*}
    {g₁ g₂ : X → A₁ → A₂ → ℝ} {F : X → A₁ → A₂ → X} {β₁ β₂ : ℝ}
    (E : Sanctions.MultistageGames.StackelbergFeedbackEquilibrium g₁ g₂ F β₁ β₂)
    (hβ₂ : 0 ≤ β₂) (hβ₂_lt : β₂ < 1)
    (M_g₂ M_W₂ : ℝ)
    (h_g₂_bound : ∀ x : X, ∀ a₁ : A₁, ∀ a₂ : A₂, |g₂ x a₁ a₂| ≤ M_g₂)
    (h_W₂_bound : ∀ x : X, |E.W₂ x| ≤ M_W₂)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (σs : Fin n → HistoryPlan X A₂) (x₀ : X) :
    mixedHistoryPayoff (followerStage g₂ E.α₁) (followerTransition F E.α₁) β₂ w σs x₀ ≤
      discountedPayoff (followerStage g₂ E.α₁) (followerTransition F E.α₁) β₂
        (stationaryPlan fun x => E.r x (E.α₁ x)) x₀ := by
  unfold mixedHistoryPayoff
  calc ∑ i, w i * historyDiscountedPayoff (followerStage g₂ E.α₁)
        (followerTransition F E.α₁) β₂ (σs i) x₀
      ≤ ∑ i, w i * discountedPayoff (followerStage g₂ E.α₁) (followerTransition F E.α₁) β₂
        (stationaryPlan fun x => E.r x (E.α₁ x)) x₀ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (follower_optimal_against_history_deviation E hβ₂
          hβ₂_lt M_g₂ M_W₂ h_g₂_bound h_W₂_bound (σs i) x₀) (hw i)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **The follower's node after an arbitrary observed leader action.** Whatever
the leader has just played, on or off the equilibrium path, no current action
followed by any pure history-dependent continuation does better for the
follower than its equilibrium response followed by equilibrium play. -/
theorem follower_node_optimal_against_history_deviation
    {X A₁ A₂ : Type*}
    {g₁ g₂ : X → A₁ → A₂ → ℝ} {F : X → A₁ → A₂ → X} {β₁ β₂ : ℝ}
    (E : Sanctions.MultistageGames.StackelbergFeedbackEquilibrium g₁ g₂ F β₁ β₂)
    (hβ₂ : 0 ≤ β₂) (hβ₂_lt : β₂ < 1)
    (M_g₂ M_W₂ : ℝ)
    (h_g₂_bound : ∀ x : X, ∀ a₁ : A₁, ∀ a₂ : A₂, |g₂ x a₁ a₂| ≤ M_g₂)
    (h_W₂_bound : ∀ x : X, |E.W₂ x| ≤ M_W₂)
    (x : X) (a₁ : A₁) (a₂ : A₂) (σ₂ : HistoryPlan X A₂) :
    g₂ x a₁ a₂ + β₂ * historyDiscountedPayoff (followerStage g₂ E.α₁)
        (followerTransition F E.α₁) β₂ σ₂ (F x a₁ a₂)
      ≤ g₂ x a₁ (E.r x a₁) + β₂ * E.W₂ (F x a₁ (E.r x a₁)) := by
  have hcont : historyDiscountedPayoff (followerStage g₂ E.α₁) (followerTransition F E.α₁)
      β₂ σ₂ (F x a₁ a₂) ≤ E.W₂ (F x a₁ a₂) := by
    have h := follower_optimal_against_history_deviation E hβ₂ hβ₂_lt M_g₂ M_W₂ h_g₂_bound
      h_W₂_bound σ₂ (F x a₁ a₂)
    rw [follower_discountedPayoff_eq_value E hβ₂ hβ₂_lt M_g₂ M_W₂ h_g₂_bound h_W₂_bound] at h
    exact h
  have hnode : g₂ x a₁ a₂ + β₂ * E.W₂ (F x a₁ a₂)
      ≤ g₂ x a₁ (E.r x a₁) + β₂ * E.W₂ (F x a₁ (E.r x a₁)) := E.hr x a₁ a₂
  have := mul_le_mul_of_nonneg_left hcont hβ₂
  linarith

#print axioms leader_optimal_against_history_deviation
#print axioms follower_optimal_against_history_deviation
#print axioms follower_node_optimal_against_history_deviation

end MultistageGames.StackelbergFeedbackEquilibrium

namespace InfiniteHorizonVerification

#print axioms historyDiscountedPayoff_eq_replay
#print axioms historyState_toHistoryPlan
#print axioms stationary_optimal_against_history_deviation_of_global_bounds
#print axioms historyDiscountedPayoff_le_value_of_global_bounds
#print axioms mixedHistoryPayoff_le_stationary_of_global_bounds
#print axioms mixedHistoryPayoff_le_value_of_global_bounds

end InfiniteHorizonVerification

end Sanctions
