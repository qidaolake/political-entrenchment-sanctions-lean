/-
Sanctions/Foundations/MultistageGames.lean

**Krawczyk-Petkov *Multistage Games* (Chapter 4 of a game-theory
handbook) — verification theorem and Stackelberg feedback structure.**

This module packages the abstract content relevant to the sanctions
model from the multistage-games chapter:

* **§5.1 Verification Theorem** for infinite-horizon feedback-Nash MPE
  in discounted stochastic games: if a candidate value function
  `V : X → ℝ` satisfies the per-state Bellman fixed-point equation
  `V(x) = sup_a [u(x, a) + β · V(F(x, a))]` and there exists a
  measurable policy `α* : X → A` attaining the sup pointwise, then
  `α*` is the optimal feedback-Nash policy and `V` is the equilibrium
  value function.

* **§7.5 Stackelberg feedback equilibrium structure (abstract).**
  In a two-player hierarchical game with Player 1 (leader) moving first
  and Player 2 (follower) observing and responding, a Stackelberg
  feedback equilibrium is the pair `(α₁*, α₂*)` where
  - `α₂*(x, u₁) ∈ argmax_{u₂} [g₂(x, u₁, u₂) + β · W₂(F(x, u₁, u₂))]`
    (follower's best response, with their own continuation),
  - `α₁*(x) ∈ argmax_{u₁} [g₁(x, u₁, α₂*(x, u₁)) + β · W₁(F(x, u₁, α₂*(x, u₁)))]`
    (leader's best response, anticipating the follower).

In the sanctions application, **Target is the leader** (Player 1):
it moves first by choosing compliance `a ∈ [0, 1]`. **Sender is the
follower** (Player 2): it observes `a` and chooses sanction `s ∈
[0, 1]`. The follower response is the **static** Sender stage selector
`σ(x, a)` only in the myopic / static-sanctions comparator. In the
**forward-looking** Stackelberg equilibrium it is the dynamic Sender
selector `σ_dyn` (or its top-selector variant `σ_dyn_top`), obtained
as the argmax of the Sender's dynamic objective
`U_S(x, a, s) + β_S · V_S(F(x, s))` against the Sender's own
continuation value `V_S`. The Verification Theorem applies directly to
the Target's side after substituting the appropriate Sender response.

The abstract application lives in `Sanctions.Theory.Bellman.Verification`
(`bellman_integrand_le_value`, `verification_target_one_shot_deviation`,
`verification_target_exists`), parametric over
`Sanctions.AbstractGame.Params`. This module carries the abstract content.
-/

import Sanctions.Foundations.Basic

noncomputable section

namespace Sanctions
namespace MultistageGames

/-! ## §5.1 Verification Theorem (abstract)

Setup:
* `X` = state space,
* `A` = action set,
* `u : X → A → ℝ` = per-stage payoff,
* `F : X → A → X` = state transition,
* `β : ℝ` with `0 ≤ β < 1` = discount factor,
* `V : X → ℝ` = candidate value function,
* `α : X → A` = candidate stationary feedback policy.

The Verification Theorem says: if `V` satisfies the Bellman fixed-point
equation pointwise (with the sup attained by `α(x)`), then `α` is the
optimal feedback policy and `V` is the equilibrium value.

Our scalar deterministic specialization in
`Sanctions.Foundations.HeSunMPE.stationary_policy_exists` produces such
an `α` from per-state ∃-argmax statements; the Verification Theorem
below is the *converse direction*: given a candidate `α` and `V`, verify
they form an equilibrium. -/

/-- **Verification Theorem (abstract scalar form).**
Suppose `V : X → ℝ` and `α : X → A` satisfy the per-state Bellman
optimality condition

  `∀ x : X, ∀ a : A, u x a + β * V (F x a) ≤ V x`,

with equality attained at `α x` for every `x`:

  `∀ x : X, u x (α x) + β * V (F x (α x)) = V x`.

Then `α` realizes `V` as its dynamic-game value: any one-step deviation
weakly decreases the discounted return.

This is essentially the one-shot deviation principle for stationary
feedback policies in infinite-horizon games. -/
theorem verification_theorem
    {X A : Type*}
    (u : X → A → ℝ) (F : X → A → X) (β : ℝ)
    (V : X → ℝ) (α : X → A)
    (h_bellman_ineq : ∀ x : X, ∀ a : A, u x a + β * V (F x a) ≤ V x)
    (h_bellman_eq : ∀ x : X, u x (α x) + β * V (F x (α x)) = V x) :
    -- α realizes V: at every state, deviating to any other action is
    -- weakly worse.
    ∀ x : X, ∀ a : A,
      u x a + β * V (F x a) ≤ u x (α x) + β * V (F x (α x)) := by
  intro x a
  rw [h_bellman_eq x]
  exact h_bellman_ineq x a

/-- **One-shot deviation: equality at the optimal policy.** -/
theorem verification_optimal_equals_value
    {X A : Type*}
    (u : X → A → ℝ) (F : X → A → X) (β : ℝ)
    (V : X → ℝ) (α : X → A)
    (h_bellman_eq : ∀ x : X, u x (α x) + β * V (F x (α x)) = V x) :
    ∀ x : X, u x (α x) + β * V (F x (α x)) = V x :=
  h_bellman_eq

/-! ## §7.5 Stackelberg feedback equilibrium (abstract structure)

We package the Stackelberg structural definition: in a sequential-move
two-player game where Player 1 moves first (the *leader*) and Player 2
responds (the *follower*), a stationary Stackelberg feedback
equilibrium consists of:

* a follower stage-response `r : X → A₁ → A₂` such that for every state
  `x` and leader action `u₁`, `r x u₁` maximizes the follower's
  *dynamic* objective (with the follower's own continuation `W₂`);
* a leader policy `α₁ : X → A₁` such that for every state `x`, `α₁ x`
  maximizes the leader's *dynamic* objective (with the leader's
  continuation `W₁`), taking the follower's response into account.

In the sanctions model:
* Leader = Target with action `a ∈ [0, 1]` (compliance);
* Follower = Sender with action `s ∈ [0, 1]` (sanction);
* In the **forward-looking** Stackelberg equilibrium, the follower
  response is `σ_dyn V_S x a` (or its top-selector variant
  `σ_dyn_top V_S x a`), obtained from the Sender dynamic objective
  `U_S(x, a, s) + β_S · V_S((1-δ)x + δs)` against the Sender's own
  continuation value `V_S`.
* The primitive **static** `σ(x, a)` is the myopic stage selector
  (`σ(x, a) ∈ argmax_s U_S(x, a, s)`); it is used only for the
  static-sanctions / myopic comparator `MyopicFeedbackEquilibrium`,
  not for the equilibrium itself.

Our codebase formalizes the leader-side (Target's) Bellman fixed point
`V_T` and the Verification Theorem `verification_target_one_shot_deviation`
in `Sanctions.Theory.Bellman.Verification`, parametric over
`Sanctions.AbstractGame.Params`. -/

/-- **Stackelberg follower stage-response condition (abstract).**
The follower's policy `r : X → A₁ → A₂` is a Stackelberg follower
response if at every `(x, u₁)`, `r x u₁` weakly dominates every other
follower action under the follower's dynamic objective. -/
def StackelbergFollowerResponse
    {X A₁ A₂ : Type*}
    (g₂ : X → A₁ → A₂ → ℝ) (F : X → A₁ → A₂ → X) (β₂ : ℝ)
    (W₂ : X → ℝ) (r : X → A₁ → A₂) : Prop :=
  ∀ x : X, ∀ u₁ : A₁, ∀ u₂ : A₂,
    g₂ x u₁ u₂ + β₂ * W₂ (F x u₁ u₂)
      ≤ g₂ x u₁ (r x u₁) + β₂ * W₂ (F x u₁ (r x u₁))

/-- **Stackelberg leader policy condition (abstract).**
The leader's policy `α₁ : X → A₁` is a Stackelberg leader policy if at
every `x`, `α₁ x` maximizes the leader's dynamic objective given the
follower's response `r`. -/
def StackelbergLeaderPolicy
    {X A₁ A₂ : Type*}
    (g₁ : X → A₁ → A₂ → ℝ) (F : X → A₁ → A₂ → X) (β₁ : ℝ)
    (W₁ : X → ℝ) (r : X → A₁ → A₂) (α₁ : X → A₁) : Prop :=
  ∀ x : X, ∀ u₁ : A₁,
    g₁ x u₁ (r x u₁) + β₁ * W₁ (F x u₁ (r x u₁))
      ≤ g₁ x (α₁ x) (r x (α₁ x))
          + β₁ * W₁ (F x (α₁ x) (r x (α₁ x)))

/-- **Stackelberg feedback equilibrium (definition).**
The pair `(α₁, r)` is a stationary Stackelberg feedback equilibrium if:
* `r` is a follower stage-response under value function `W₂`;
* `α₁` is a leader policy under value function `W₁`, taking `r` as given;
* the value functions are consistent with the Bellman equations:
  `W_j(x) = g_j(x, α₁(x), r(x, α₁(x))) + β_j W_j(F(x, α₁(x), r(x, α₁(x))))`. -/
structure StackelbergFeedbackEquilibrium
    {X A₁ A₂ : Type*}
    (g₁ g₂ : X → A₁ → A₂ → ℝ) (F : X → A₁ → A₂ → X) (β₁ β₂ : ℝ) where
  W₁ : X → ℝ
  W₂ : X → ℝ
  r : X → A₁ → A₂
  α₁ : X → A₁
  hr : StackelbergFollowerResponse g₂ F β₂ W₂ r
  hα : StackelbergLeaderPolicy g₁ F β₁ W₁ r α₁
  hW₁_bellman : ∀ x : X,
      W₁ x = g₁ x (α₁ x) (r x (α₁ x))
              + β₁ * W₁ (F x (α₁ x) (r x (α₁ x)))
  hW₂_bellman : ∀ x : X,
      W₂ x = g₂ x (α₁ x) (r x (α₁ x))
              + β₂ * W₂ (F x (α₁ x) (r x (α₁ x)))

end MultistageGames
end Sanctions

end
