/-
Sanctions/Foundations/HistoryDependentSecurity.lean

**An open-loop saddle point is a saddle point in pure history-dependent
strategies** (round BD, 2026-10-01).

`Foundations/HistoryDependentDeviations.lean` handles one player's
history-dependent deviation against an opponent held at a feedback rule. Here
**both** players condition on the whole past. The setting is a deterministic
discounted game with perfect monitoring in which, every period, a *leader*
moves first (action in `A`), a *follower* observes it and moves (action in `B`),
the leader collects `u(x, a, b)`, and the state moves to `F(x, a, b)`.

* `LeaderPlan X A B := List (X × A × B) → X → A` — the leader's action depends on
  the list of past (state, leader action, follower action) triples, oldest first,
  and on the current state;
* `FollowerPlan X A B := List (X × A × B) → X → A → B` — the follower's action
  depends on the same history, the current state and the leader's current action.

A profile of pure plans generates one run (`jointRun`) and so one pair of action
sequences. The textbook reduction (the sequence formulation of
Stokey–Lucas–Prescott §4.1) is that the run's states and payoff are those of the
open-loop pair it realises (`jointState_eq_openLoopPath`,
`jointPayoff_eq_openLoopPayoff`), and that every open-loop sequence is a plan
(`LeaderPlan.ofSeq`, `FollowerPlan.ofSeq`). Hence:

**`isLeast_ceiling_history_of_openLoop_saddle` /
`isGreatest_floor_history_of_openLoop_saddle`.** Suppose a leader sequence `a₀`
secures `W` against every feasible follower sequence, and a follower sequence
`b₀` holds every feasible leader sequence to at most `W` (an open-loop pure saddle
value). Then `W` is the least payoff ceiling the follower can impose with a
feasible pure history-dependent plan, and the greatest payoff floor the leader can
guarantee with one: the leader's minmax and maxmin over pure history-dependent
strategies both equal `W`, attained by `a₀` and `b₀` read as plans.

Scope: pure plans, deterministic transition, perfect monitoring; a statement about
security levels, not about which equilibria exist. Payoffs are `tsum`s compared
through the hypotheses only, so no summability is assumed here. Rule 19: no
`Params`, no sanctions structure; the wiring is
`Examples/PlacableSenderSecurityHistory.lean`.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Sanctions
namespace HistoryDependentSecurity

/-- A pure history-dependent plan for the player who moves first each period. -/
abbrev LeaderPlan (X A B : Type*) := List (X × A × B) → X → A

/-- A pure history-dependent plan for the player who moves second each period,
after observing the first mover's current action. -/
abbrev FollowerPlan (X A B : Type*) := List (X × A × B) → X → A → B

variable {X A B : Type*}

/-- The run of a profile of pure plans: the recorded history and the current state. -/
def jointRun (F : X → A → B → X) (τ : LeaderPlan X A B) (σ : FollowerPlan X A B) (x₀ : X) :
    ℕ → List (X × A × B) × X
  | 0 => ([], x₀)
  | n + 1 =>
      ((jointRun F τ σ x₀ n).1 ++
          [((jointRun F τ σ x₀ n).2, τ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2,
            σ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2
              (τ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2))],
        F (jointRun F τ σ x₀ n).2 (τ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2)
          (σ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2
            (τ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2)))

/-- The state at date `n` of the run. -/
def jointState (F : X → A → B → X) (τ : LeaderPlan X A B) (σ : FollowerPlan X A B) (x₀ : X)
    (n : ℕ) : X :=
  (jointRun F τ σ x₀ n).2

/-- The leader's action at date `n` of the run. -/
def leaderAction (F : X → A → B → X) (τ : LeaderPlan X A B) (σ : FollowerPlan X A B) (x₀ : X)
    (n : ℕ) : A :=
  τ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2

/-- The follower's action at date `n` of the run. -/
def followerAction (F : X → A → B → X) (τ : LeaderPlan X A B) (σ : FollowerPlan X A B)
    (x₀ : X) (n : ℕ) : B :=
  σ (jointRun F τ σ x₀ n).1 (jointRun F τ σ x₀ n).2 (leaderAction F τ σ x₀ n)

@[simp] theorem jointState_zero (F : X → A → B → X) (τ : LeaderPlan X A B)
    (σ : FollowerPlan X A B) (x₀ : X) : jointState F τ σ x₀ 0 = x₀ := rfl

theorem jointState_succ (F : X → A → B → X) (τ : LeaderPlan X A B) (σ : FollowerPlan X A B)
    (x₀ : X) (n : ℕ) :
    jointState F τ σ x₀ (n + 1)
      = F (jointState F τ σ x₀ n) (leaderAction F τ σ x₀ n) (followerAction F τ σ x₀ n) :=
  rfl

/-- The recorded history at date `n` has length `n`. -/
theorem jointRun_length (F : X → A → B → X) (τ : LeaderPlan X A B) (σ : FollowerPlan X A B)
    (x₀ : X) : ∀ n, (jointRun F τ σ x₀ n).1.length = n
  | 0 => rfl
  | n + 1 => by
      change ((jointRun F τ σ x₀ n).1 ++ [_]).length = n + 1
      rw [List.length_append, jointRun_length F τ σ x₀ n]
      rfl

/-- The state path of an open-loop pair of action sequences. -/
def openLoopPath (F : X → A → B → X) (a : ℕ → A) (b : ℕ → B) (x₀ : X) : ℕ → X
  | 0 => x₀
  | n + 1 => F (openLoopPath F a b x₀ n) (a n) (b n)

/-- **The run visits the open-loop path of the actions it realises.** -/
theorem jointState_eq_openLoopPath (F : X → A → B → X) (τ : LeaderPlan X A B)
    (σ : FollowerPlan X A B) (x₀ : X) :
    ∀ n, jointState F τ σ x₀ n
      = openLoopPath F (leaderAction F τ σ x₀) (followerAction F τ σ x₀) x₀ n
  | 0 => rfl
  | n + 1 => by
      rw [jointState_succ, jointState_eq_openLoopPath F τ σ x₀ n]
      rfl

/-- The leader's discounted payoff along an open-loop pair. -/
noncomputable def openLoopPayoff (u : X → A → B → ℝ) (F : X → A → B → X) (β : ℝ)
    (a : ℕ → A) (b : ℕ → B) (x₀ : X) : ℝ :=
  ∑' n : ℕ, β ^ n * u (openLoopPath F a b x₀ n) (a n) (b n)

/-- The leader's discounted payoff from a profile of pure history-dependent plans. -/
noncomputable def jointPayoff (u : X → A → B → ℝ) (F : X → A → B → X) (β : ℝ)
    (τ : LeaderPlan X A B) (σ : FollowerPlan X A B) (x₀ : X) : ℝ :=
  ∑' n : ℕ, β ^ n * u (jointState F τ σ x₀ n) (leaderAction F τ σ x₀ n)
    (followerAction F τ σ x₀ n)

/-- **The reduction.** A profile's payoff is the open-loop payoff of the pair of
action sequences it realises. -/
theorem jointPayoff_eq_openLoopPayoff (u : X → A → B → ℝ) (F : X → A → B → X) (β : ℝ)
    (τ : LeaderPlan X A B) (σ : FollowerPlan X A B) (x₀ : X) :
    jointPayoff u F β τ σ x₀
      = openLoopPayoff u F β (leaderAction F τ σ x₀) (followerAction F τ σ x₀) x₀ := by
  unfold jointPayoff openLoopPayoff
  exact tsum_congr fun n => by rw [jointState_eq_openLoopPath]

/-- An open-loop leader sequence read as a plan: the date is the history's length. -/
def LeaderPlan.ofSeq (a : ℕ → A) : LeaderPlan X A B := fun h _ => a h.length

/-- An open-loop follower sequence read as a plan. -/
def FollowerPlan.ofSeq (b : ℕ → B) : FollowerPlan X A B := fun h _ _ => b h.length

theorem leaderAction_ofSeq (F : X → A → B → X) (a : ℕ → A) (σ : FollowerPlan X A B)
    (x₀ : X) (n : ℕ) : leaderAction F (LeaderPlan.ofSeq a) σ x₀ n = a n := by
  unfold leaderAction LeaderPlan.ofSeq
  rw [jointRun_length]

theorem followerAction_ofSeq (F : X → A → B → X) (τ : LeaderPlan X A B) (b : ℕ → B)
    (x₀ : X) (n : ℕ) : followerAction F τ (FollowerPlan.ofSeq b) x₀ n = b n := by
  unfold followerAction FollowerPlan.ofSeq
  rw [jointRun_length]

/-- **Minmax.** Under an open-loop pure saddle value `W`, the least payoff ceiling
the follower can impose on the leader with a feasible pure history-dependent plan
is `W`, attained by `b₀` read as a plan. -/
theorem isLeast_ceiling_history_of_openLoop_saddle {u : X → A → B → ℝ}
    {F : X → A → B → X} {β : ℝ} {x₀ : X} {SA : Set A} {SB : Set B} {W : ℝ}
    {a₀ : ℕ → A} {b₀ : ℕ → B} (ha₀ : ∀ n, a₀ n ∈ SA) (hb₀ : ∀ n, b₀ n ∈ SB)
    (hsec : ∀ b : ℕ → B, (∀ n, b n ∈ SB) → W ≤ openLoopPayoff u F β a₀ b x₀)
    (hpun : ∀ a : ℕ → A, (∀ n, a n ∈ SA) → openLoopPayoff u F β a b₀ x₀ ≤ W) :
    IsLeast {v : ℝ | ∃ σ : FollowerPlan X A B, (∀ h x a, σ h x a ∈ SB) ∧
        ∀ τ : LeaderPlan X A B, (∀ h x, τ h x ∈ SA) → jointPayoff u F β τ σ x₀ ≤ v} W := by
  refine ⟨⟨FollowerPlan.ofSeq b₀, fun h _ _ => hb₀ h.length, fun τ hτ => ?_⟩, ?_⟩
  · rw [jointPayoff_eq_openLoopPayoff]
    have hb : followerAction F τ (FollowerPlan.ofSeq b₀) x₀ = b₀ :=
      funext (followerAction_ofSeq F τ b₀ x₀)
    rw [hb]
    exact hpun _ fun n => hτ _ _
  · rintro v ⟨σ, hσ, hv⟩
    refine le_trans ?_ (hv (LeaderPlan.ofSeq a₀) fun h _ => ha₀ h.length)
    rw [jointPayoff_eq_openLoopPayoff]
    have ha : leaderAction F (LeaderPlan.ofSeq a₀) σ x₀ = a₀ :=
      funext (leaderAction_ofSeq F a₀ σ x₀)
    rw [ha]
    exact hsec _ fun n => hσ _ _ _

/-- **Maxmin.** Under an open-loop pure saddle value `W`, the greatest payoff floor
the leader can guarantee with a feasible pure history-dependent plan, against every
feasible pure history-dependent plan of the follower, is `W`, attained by `a₀` read
as a plan. -/
theorem isGreatest_floor_history_of_openLoop_saddle {u : X → A → B → ℝ}
    {F : X → A → B → X} {β : ℝ} {x₀ : X} {SA : Set A} {SB : Set B} {W : ℝ}
    {a₀ : ℕ → A} {b₀ : ℕ → B} (ha₀ : ∀ n, a₀ n ∈ SA) (hb₀ : ∀ n, b₀ n ∈ SB)
    (hsec : ∀ b : ℕ → B, (∀ n, b n ∈ SB) → W ≤ openLoopPayoff u F β a₀ b x₀)
    (hpun : ∀ a : ℕ → A, (∀ n, a n ∈ SA) → openLoopPayoff u F β a b₀ x₀ ≤ W) :
    IsGreatest {v : ℝ | ∃ τ : LeaderPlan X A B, (∀ h x, τ h x ∈ SA) ∧
        ∀ σ : FollowerPlan X A B, (∀ h x a, σ h x a ∈ SB) → v ≤ jointPayoff u F β τ σ x₀} W := by
  refine ⟨⟨LeaderPlan.ofSeq a₀, fun h _ => ha₀ h.length, fun σ hσ => ?_⟩, ?_⟩
  · rw [jointPayoff_eq_openLoopPayoff]
    have ha : leaderAction F (LeaderPlan.ofSeq a₀) σ x₀ = a₀ :=
      funext (leaderAction_ofSeq F a₀ σ x₀)
    rw [ha]
    exact hsec _ fun n => hσ _ _ _
  · rintro v ⟨τ, hτ, hv⟩
    refine le_trans (hv (FollowerPlan.ofSeq b₀) fun h _ _ => hb₀ h.length) ?_
    rw [jointPayoff_eq_openLoopPayoff]
    have hb : followerAction F τ (FollowerPlan.ofSeq b₀) x₀ = b₀ :=
      funext (followerAction_ofSeq F τ b₀ x₀)
    rw [hb]
    exact hpun _ fun n => hτ _ _

end HistoryDependentSecurity
end Sanctions

#print axioms Sanctions.HistoryDependentSecurity.jointState_eq_openLoopPath
#print axioms Sanctions.HistoryDependentSecurity.jointPayoff_eq_openLoopPayoff
#print axioms Sanctions.HistoryDependentSecurity.isLeast_ceiling_history_of_openLoop_saddle
#print axioms Sanctions.HistoryDependentSecurity.isGreatest_floor_history_of_openLoop_saddle
