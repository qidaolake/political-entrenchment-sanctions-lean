/-
Sanctions/Theory/Equilibrium/StackelbergFeedback.lean

**Sequential feedback Stackelberg equilibrium of the abstract sanctions
game** (Krawczyk-Petkov *Multistage Games* §7.5 eqs. (4.97)-(4.103);
Breton, Alj, Haurie 1988 Def. 3.1).

The dynamic political-economy game is a within-period sequential
Stackelberg game in the sense of Breton et al.:

* the Target (leader) chooses the compliance action `a in [0, 1]`,
* the Sender (follower) observes `a` and chooses the sanction
  `s in [0, 1]`,
* both players are forward-looking with discount factors
  `beta_T, beta_S in [0, 1)`,
* the state evolves as `x_{t+1} = (1 - delta) x_t + delta * s`.

The follower's forward-looking response is the dynamic argmax
`p.sigma_dyn V_S x a` (the Sender's argmax of
`U_S(x, a, s) + beta_S * V_S(F(x, s))`); the static argmax
`p.sigma` coincides with `sigma_dyn` only at `beta_S = 0`.

A **sequential feedback Stackelberg equilibrium** in this setup
consists of the leader value function `V_T`, the follower value
function `V_S`, and the leader policy `alpha`, all jointly satisfying:

* the Sender Bellman fixed point `V_S = bellmanS_BCF alpha V_S`
  (follower's `W_2` in K-P §7.5),
* the Target joint Bellman fixed point `V_T(x) = sSup over a of
  joint_T_integrand V_T V_S x a` (leader's `W_1` after substituting
  the follower's response),
* leader Bellman optimality of `alpha` at every state.

The corresponding K-P / Breton verification theorem (one-shot
deviation principle) follows directly from these fixed-point
equations; this module packages the definition and the verification
theorem, plus the **bridge** to the abstract
`Sanctions.MultistageGames.StackelbergFeedbackEquilibrium` structure
(over arbitrary state and action spaces) in
`Sanctions/Foundations/MultistageGames.lean`.

## Rule compliance

**Rule 1** (optimal strategies only). Every load-bearing strategy in
the structure is equilibrium-derived: `V_T` and `V_S` are Banach
Bellman fixed points; `alpha` is the leader's Bellman argmax;
`sigma_dyn V_S` (implicit follower response) is the
forward-looking Sender argmax via `Classical.choose`. No
hand-chosen rule appears.

**Rule 3** (no new assumption surface). The structure
`FeedbackStackelbergEquilibrium` is a *definition* whose fields are
facts we already prove parametrically (`V_S_fix` follows from
`V_S_isFixedPoint`; `V_T_fix` is the per-state Bellman equation
established in `JointMPE.T_T_joint`; `alpha_opt` is the leader's
argmax property). No new external hypothesis is introduced; the
existence-from-data theorem below is a constructor wrapper. An
**operator-level from-primitives existence theorem** is provided in
`Theory/Equilibrium/JointExistenceFromPrimitives.lean`
(`exists_feedbackStackelberg_from_selector_row_bounds`), which under
global Sender argmax uniqueness, a `DynamicTargetSelector`, and
explicit row-Lipschitz bounds returns a `Nonempty
FeedbackStackelbergEquilibrium` via the joint MPE Banach contraction.
What remains deferred is the *primitive* discharge of the
`DynamicTargetSelector` (continuous leader argmax), the global Sender
uniqueness (canonical sufficient: strict concavity of the complete
dynamic Sender objective in `s`, not merely of `U_S`),
and the row-Lipschitz constants from a concrete payoff class.

**Rule 5** (parametric over witness). Fully parametric over
`(p : Sanctions.AbstractGame.Params)`. No witness-specific content.
-/

import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.Equilibrium.BergeContinuity
import Sanctions.Theory.Bellman.Verification
import Sanctions.Foundations.MultistageGames

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Sequential feedback Stackelberg equilibrium (structure)

The four equilibrium objects are:

* `V_T : ↥S →ᵇ ℝ` — Target (leader) value function;
* `V_S : ↥S →ᵇ ℝ` — Sender (follower) value function;
* `α : ℝ → ℝ` — Target (leader) feedback policy;
* `σ_dyn V_S` (implicit) — Sender (follower) forward-looking
  argmax response, computed from `V_S` via
  `Sanctions.AbstractGame.Params.σ_dyn`.

The three fixed-point/optimality conditions are:

* `V_S_fix`: `V_S` is the Sender Bellman fixed point under α;
* `V_T_fix`: `V_T(x)` solves the Target joint Bellman equation
  against `σ_dyn V_S` at every state;
* `α_opt`: `α(x)` attains the Target's joint Bellman argmax at
  every state. -/

/-- **Sequential feedback Stackelberg equilibrium of the abstract
sanctions game.** Packages the four equilibrium objects together with
the three fixed-point / optimality conditions that constitute a
sequential Stackelberg equilibrium in the sense of Krawczyk-Petkov
§7.5 / Breton et al. 1988 Def. 3.1. -/
structure FeedbackStackelbergEquilibrium where
  /-- Target (leader) value function. -/
  V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- Sender (follower) value function. -/
  V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- Target (leader) feedback policy. -/
  α : ℝ → ℝ
  /-- Continuity of α, for `bellmanS_BCF` compatibility. -/
  hα : Continuous α
  /-- α is feasible at every state. -/
  α_mem : ∀ x : ℝ, α x ∈ Sanctions.I
  /-- **Follower fixed-point condition.** `V_S` is the Sender Bellman
  fixed point under leader policy α. -/
  V_S_fix : V_S = p.bellmanS_BCF α hα V_S
  /-- **Leader fixed-point condition.** `V_T(x)` solves the Target
  joint Bellman equation against the follower's `σ_dyn V_S` response
  at every state in `↥S`. -/
  V_T_fix : ∀ x : ↥(Sanctions.S : Set ℝ),
    V_T x = sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) '' Sanctions.I)
  /-- **Leader Bellman optimality.** α attains the joint Bellman
  argmax at every state. -/
  α_opt : ∀ x : ℝ,
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I (α x)

end Params
end AbstractGame

/-! ## Verification theorem (one-shot deviation for the leader)

The verification theorem says: at a sequential feedback Stackelberg
equilibrium, any one-step deviation by the leader from the policy α
weakly decreases the discounted return. This is the
Krawczyk-Petkov §5.1 verification theorem specialized to the leader
under the follower's forward-looking response.

The proof is mechanical: from `V_T_fix` (Bellman fixed point) and
`α_opt` (argmax property), the deviation value `joint_T_integrand
V_T V_S x a'` is dominated by the argmax value, which equals
`V_T x` by the fixed point. -/

namespace AbstractGame
namespace Params

/-- **One-shot deviation principle for the Target (leader).** At a
sequential feedback Stackelberg equilibrium, any deviation from the
leader policy α to any feasible action a' ∈ [0, 1] weakly decreases
the Target's discounted return measured by `V_T`. -/
theorem FeedbackStackelbergEquilibrium.target_one_shot_deviation
    {p : Params} (E : p.FeedbackStackelbergEquilibrium) :
    ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a' ∈ Sanctions.I,
      p.joint_T_integrand E.V_T E.V_S x.val a' ≤ E.V_T x := by
  intro x a' ha'
  rw [E.V_T_fix x]
  -- Need: joint_T_integrand E.V_T E.V_S x.val a'
  --         ≤ sSup ((fun a => joint_T_integrand E.V_T E.V_S x.val a) '' I)
  -- Argmax existence (from E.α_opt) implies the sSup is bounded above.
  -- The bound: every value in the image is ≤ the value at E.α x.val,
  -- which equals the sSup.
  have h_bdd : BddAbove
      ((fun a => p.joint_T_integrand E.V_T E.V_S x.val a) '' Sanctions.I) := by
    refine ⟨p.joint_T_integrand E.V_T E.V_S x.val (E.α x.val), ?_⟩
    rintro y ⟨a, ha, rfl⟩
    exact E.α_opt x.val ha
  exact le_csSup h_bdd ⟨a', ha', rfl⟩

/-- **Equality at the optimal policy.** The Target value function
agrees pointwise with the integrand evaluated at α. -/
theorem FeedbackStackelbergEquilibrium.target_value_at_alpha
    {p : Params} (E : p.FeedbackStackelbergEquilibrium) :
    ∀ x : ↥(Sanctions.S : Set ℝ),
      E.V_T x = p.joint_T_integrand E.V_T E.V_S x.val (E.α x.val) := by
  intro x
  rw [E.V_T_fix x]
  -- Show sSup of the image = value at E.α x.val.
  apply le_antisymm
  · -- sSup ≤ value at α x.val (E.α x.val is a maximizer)
    apply csSup_le
    · refine ⟨p.joint_T_integrand E.V_T E.V_S x.val 0, 0, by simp [Sanctions.I], rfl⟩
    · rintro y ⟨a, ha, rfl⟩
      exact E.α_opt x.val ha
  · -- value at α x.val ≤ sSup (it's in the image)
    have h_bdd : BddAbove
        ((fun a => p.joint_T_integrand E.V_T E.V_S x.val a) '' Sanctions.I) := by
      refine ⟨p.joint_T_integrand E.V_T E.V_S x.val (E.α x.val), ?_⟩
      rintro y ⟨a, ha, rfl⟩
      exact E.α_opt x.val ha
    exact le_csSup h_bdd
      ⟨E.α x.val, E.α_mem x.val, rfl⟩

end Params
end AbstractGame

/-! ## Sender-side Bellman equation at α

The Sender Bellman fixed point `V_S = bellmanS_BCF α hα V_S` gives
the sSup form `V_S x = sSup ((fun s => integrandS α V_S (x.val, s))
'' I)`. The lemma below shows this sSup is attained at the
forward-looking Sender argmax `σ_dyn V_S x.val (α x.val)`, giving
the Sender Bellman equation in evaluated form (the K-P §7.5
hW₂_bellman). -/

namespace AbstractGame
namespace Params

/-- **Sender Bellman equation evaluated at α.** The Sender's value
function equals its stage payoff plus discounted continuation,
evaluated at the leader's policy α and the follower's
forward-looking argmax `σ_dyn V_S`. -/
theorem FeedbackStackelbergEquilibrium.sender_value_at_alpha
    {p : Params} (E : p.FeedbackStackelbergEquilibrium) :
    ∀ x : ↥(Sanctions.S : Set ℝ),
      E.V_S x =
        p.U_S x.val (E.α x.val) (p.σ_dyn E.V_S x.val (E.α x.val))
        + p.β_S * E.V_S (Sanctions.clipS'
            (p.F x.val (p.σ_dyn E.V_S x.val (E.α x.val)))) := by
  intro x
  have h_fix : E.V_S x = p.bellmanS_BCF E.α E.hα E.V_S x := by
    rw [← E.V_S_fix]
  rw [h_fix]
  -- bellmanS_BCF α hα V_S x = sSup over s ∈ I of integrandS α V_S (x.val, s)
  change sSup ((fun s => p.integrandS E.α (fun y => E.V_S y) (x.val, s))
                  '' Sanctions.I) = _
  -- The sSup is attained at σ_dyn V_S x.val (α x.val), which is the argmax
  -- of the integrandS slice in s.
  apply le_antisymm
  · -- sSup ≤ value at σ_dyn (since σ_dyn maximizes)
    apply csSup_le
    · refine ⟨_, ⟨0, by simp [Sanctions.I], rfl⟩⟩
    · rintro y ⟨s, hs, rfl⟩
      -- σ_dyn_isMaxOn says s ↦ U_S(x.val, α x.val, s) + β_S V_S(clipS' ...)
      -- is maximized at σ_dyn V_S x.val (α x.val).
      -- This is exactly integrandS E.α V_S (x.val, s).
      have h_max := p.σ_dyn_isMaxOn E.V_S x.val (E.α x.val) hs
      -- h_max : (fun s' => U_S x.val (α x.val) s' + β_S V_S (clipS' ...)) s
      --         ≤ (fun s' => ...) (σ_dyn V_S x.val (α x.val))
      change p.integrandS E.α (fun y => E.V_S y) (x.val, s) ≤ _
      unfold AbstractGame.Params.integrandS
      exact h_max
  · -- value at σ_dyn is in image (since σ_dyn ∈ I), so ≤ sSup
    have h_bdd : BddAbove
        ((fun s => p.integrandS E.α (fun y => E.V_S y) (x.val, s))
            '' Sanctions.I) :=
      p.integrandS_image_bddAbove E.hα E.V_S.continuous x.val
    apply le_csSup h_bdd
    refine ⟨p.σ_dyn E.V_S x.val (E.α x.val),
            p.σ_dyn_mem E.V_S x.val (E.α x.val), ?_⟩
    -- integrandS E.α V_S (x.val, σ_dyn V_S x.val (α x.val))
    --   = U_S(...) + β_S V_S(clipS' ((1-δ) x.val + δ σ_dyn V_S x.val (α x.val)))
    rfl

end Params
end AbstractGame

/-! ## Bridge to the abstract Krawczyk-Petkov Stackelberg structure

Our project equilibrium `FeedbackStackelbergEquilibrium p` maps into
the abstract `Sanctions.MultistageGames.StackelbergFeedbackEquilibrium`
structure (over `X = ↥S`, `A₁ = A₂ = ↥I`) via:

* `W₁ := E.V_T`, `W₂ := E.V_S`,
* `r(x, a) := ⟨p.σ_dyn E.V_S x.val a.val, _⟩` (follower's
  forward-looking argmax, wrapped into `↥I` via `σ_dyn_mem`),
* `α₁(x) := ⟨E.α x.val, _⟩` (leader's policy, wrapped via `α_mem`),
* `g₁(x, a, s) := p.U_T x.val a.val s.val`,
  `g₂(x, a, s) := p.U_S x.val a.val s.val`,
* `F(x, a, s) := clipS' (p.F x.val s.val)` — the GENERAL transition
  field, not the affine law; compliance `a` does not enter it,
* `β₁ := p.β_T`, `β₂ := p.β_S`.

The four conditions of the abstract structure
(`StackelbergFollowerResponse`, `StackelbergLeaderPolicy`,
`hW₁_bellman`, `hW₂_bellman`) are discharged from our three concrete
conditions (`V_S_fix`, `V_T_fix`, `α_opt`) plus the two helper
lemmas (`target_value_at_alpha`, `sender_value_at_alpha`). -/

namespace AbstractGame
namespace Params

/-- **Bridge: our `FeedbackStackelbergEquilibrium` is a Krawczyk-Petkov
abstract Stackelberg feedback equilibrium.** The action sets are
lifted to `↥I = ↥(Sanctions.I : Set ℝ)` (subtype of feasible actions)
so the abstract structure's inequalities quantify exactly over the
feasible action set. -/
def FeedbackStackelbergEquilibrium.toAbstractStackelberg
    {p : Params} (E : p.FeedbackStackelbergEquilibrium) :
    Sanctions.MultistageGames.StackelbergFeedbackEquilibrium
      (X  := ↥(Sanctions.S : Set ℝ))
      (A₁ := ↥(Sanctions.I : Set ℝ))
      (A₂ := ↥(Sanctions.I : Set ℝ))
      (g₁ := fun x a s => p.U_T x.val a.val s.val)
      (g₂ := fun x a s => p.U_S x.val a.val s.val)
      (F  := fun x _a s => Sanctions.clipS'
                (p.F x.val s.val))
      (β₁ := p.β_T) (β₂ := p.β_S) where
  W₁ := fun x => E.V_T x
  W₂ := fun x => E.V_S x
  r  := fun x a => ⟨p.σ_dyn E.V_S x.val a.val,
                    p.σ_dyn_mem E.V_S x.val a.val⟩
  α₁ := fun x => ⟨E.α x.val, E.α_mem x.val⟩
  hr := by
    -- Follower stage-response: σ_dyn V_S x.val u₁.val is the argmax of
    -- s ↦ U_S(x.val, u₁.val, s) + β_S V_S(F(x.val, s)) on I,
    -- which means for any u₂ : ↥I (so u₂.val ∈ I),
    -- U_S(x.val, u₁.val, u₂.val) + β_S V_S(F(x.val, u₂.val))
    --   ≤ U_S(x.val, u₁.val, σ_dyn V_S x.val u₁.val)
    --     + β_S V_S(F(x.val, σ_dyn V_S x.val u₁.val)).
    intro x u₁ u₂
    exact p.σ_dyn_isMaxOn E.V_S x.val u₁.val u₂.property
  hα := by
    -- Leader argmax: α x.val is the argmax of joint_T_integrand V_T V_S x.val
    -- on I (per E.α_opt).
    -- We need: g₁(x, u₁, r(x, u₁)) + β₁ W₁(F(x, u₁, r(x, u₁)))
    --       ≤ g₁(x, α₁(x), r(x, α₁(x))) + β₁ W₁(F(x, α₁(x), r(x, α₁(x))))
    -- Both sides are joint_T_integrand evaluated at u₁.val and E.α x.val
    -- respectively. So this is E.α_opt at u₁.val ∈ I.
    intro x u₁
    have := E.α_opt x.val u₁.property
    -- this : joint_T_integrand E.V_T E.V_S x.val u₁.val
    --        ≤ joint_T_integrand E.V_T E.V_S x.val (E.α x.val)
    exact this
  hW₁_bellman := by
    -- W₁ x = g₁(x, α₁(x), r(x, α₁(x))) + β₁ W₁(F(x, α₁(x), r(x, α₁(x))))
    -- LHS = E.V_T x; RHS unfolds to joint_T_integrand E.V_T E.V_S x.val (E.α x.val).
    -- This is target_value_at_alpha.
    intro x
    exact E.target_value_at_alpha x
  hW₂_bellman := by
    -- W₂ x = g₂(x, α₁(x), r(x, α₁(x))) + β₂ W₂(F(x, α₁(x), r(x, α₁(x))))
    -- LHS = E.V_S x; RHS unfolds to the Sender Bellman equation at α.
    intro x
    exact E.sender_value_at_alpha x

end Params
end AbstractGame

/-! ## From-primitives existence (status: operator-level, conditional dischargers)

The operator-level from-primitives existence theorem
`exists_feedbackStackelberg_from_selector_row_bounds` is in
`Theory/Equilibrium/JointExistenceFromPrimitives.lean`. It assembles the
following ingredients:

1. **Joint operator packaging**: `jointTargetOp` (Target Bellman on
   `↥S →ᵇ ℝ × ↥S →ᵇ ℝ → ↥S →ᵇ ℝ`) and `jointSenderOp`, both
   packaged via `BoundedContinuousFunction.mkOfCompact` +
   `IsCompact.continuous_sSup`, with the requisite joint continuity
   discharged by `joint_T_integrand_continuous_jointly_of_unique` and
   `σ_dyn_continuous_of_unique` (`BergeContinuity`).
2. **Leader continuous selector**: packaged as the
   `DynamicTargetSelector` structure (continuity + feasibility +
   joint Bellman optimality). The from-uniqueness discharger EXISTS:
   `dynamicTargetSelector_of_unique`
   (`Theory/Equilibrium/TargetSelectorFromUnique.lean`, since audit-32)
   packages the `TargetArgmaxUnique` predicate through the same
   Berge sequential-continuity machinery as
   `σ_dyn_continuous_of_unique`.
3. **Joint MPE existence**: `joint_MPE_under_explicit_bounds` gives
   the fixed-point pair from the row-Lipschitz bounds.
4. **Consistency fixed point**: the leader policy α from
   `DynamicTargetSelector` evaluated at the joint MPE pair (`D.α z`)
   is automatically Bellman-optimal against `(V_T, V_S) = z` by
   construction (the `α_opt` field is required at every value pair).

What remains primitive in this operator-level theorem:

- **Global Sender uniqueness** `∀ V_S : Val, DynamicArgmaxUnique V_S`
  is currently asked over arbitrary bounded continuous `V_S`; the
  canonical economic sufficient condition is strict concavity of
  the complete dynamic Sender objective in `s`. Stage strict
  concavity of `U_S` does not by itself control the curvature of the
  continuation term. A restricted carrier on which the complete
  objective is strictly concave is the honest deferred follow-up.
- **Row-Lipschitz bounds** `β_T + L_TS < 1`, `β_S + L_ST < 1` are
  taken as primitive inputs; deriving them from primitive payoff
  Lipschitz constants is the topic of `JointLipschitz.lean` (witness
  case closed; general case open).
- **Value-Lipschitz constants** `K_T`, `K_S` used by
  `PrimitiveHighBasin.lean` are taken as primitive inputs;
  discharging them from primitive payoff Lipschitz + transition
  Lipschitz + contraction is a follow-up cone-iteration result.

For the immediate goal (justifying the paper's "Target is Stackelberg
leader" framing), the bridge `toAbstractStackelberg` plus the
constructor `ofData` plus the operator-level existence theorem are
sufficient.

The conditional existence theorem below reduces the question one
level: given a consistent (V_T, V_S, α) triple satisfying the joint
Bellman / argmax fixed-point conditions, the Stackelberg equilibrium
exists and embeds into the abstract Krawczyk-Petkov structure. -/

namespace AbstractGame
namespace Params

/-- **Constructor: feedback Stackelberg equilibrium from supplied
data.** Given the four equilibrium objects (`V_T`, `V_S`, `α`, `hα`)
and the three conditions (`V_S_fix`, `V_T_fix`, `α_opt`) all
discharged, package the `FeedbackStackelbergEquilibrium` structure. -/
def FeedbackStackelbergEquilibrium.ofData
    {p : Params}
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (hα : Continuous α)
    (α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (V_S_fix : V_S = p.bellmanS_BCF α hα V_S)
    (V_T_fix : ∀ x : ↥(Sanctions.S : Set ℝ),
        V_T x = sSup ((fun a => p.joint_T_integrand V_T V_S x.val a)
                        '' Sanctions.I))
    (α_opt : ∀ x : ℝ,
        IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a)
                Sanctions.I (α x)) :
    p.FeedbackStackelbergEquilibrium where
  V_T := V_T
  V_S := V_S
  α := α
  hα := hα
  α_mem := α_mem
  V_S_fix := V_S_fix
  V_T_fix := V_T_fix
  α_opt := α_opt

/-- **Conditional existence: from a consistent joint Bellman / argmax
triple to a Stackelberg feedback equilibrium.** Given any candidate
data `(V_T, V_S, α)` satisfying the three fixed-point / argmax
conditions, the existence of a `FeedbackStackelbergEquilibrium p` is
immediate (via `ofData`) and the abstract Krawczyk-Petkov
Stackelberg structure embeds via the bridge. -/
theorem feedbackStackelbergEquilibrium_exists_of_consistent_triple
    (p : Params)
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (hα : Continuous α)
    (α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (V_S_fix : V_S = p.bellmanS_BCF α hα V_S)
    (V_T_fix : ∀ x : ↥(Sanctions.S : Set ℝ),
        V_T x = sSup ((fun a => p.joint_T_integrand V_T V_S x.val a)
                        '' Sanctions.I))
    (α_opt : ∀ x : ℝ,
        IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a)
                Sanctions.I (α x)) :
    Nonempty p.FeedbackStackelbergEquilibrium :=
  ⟨FeedbackStackelbergEquilibrium.ofData V_T V_S α hα
    α_mem V_S_fix V_T_fix α_opt⟩

/-! ## Audit-49 follow-up Round 3 Optional-4.1: Sender response projection

The structure `FeedbackStackelbergEquilibrium` stores only
`(V_T, V_S, α)`; the Sender best response is implicit through the
selector `σ_dyn`. The projection `ρ` below exposes the Sender
response explicitly, so a paper-facing reader can write the
equilibrium tuple as `(V_T, V_S, α, ρ)` directly.

`ρ` is the classical-choice-based dynamic Sender argmax
`p.σ_dyn E.V_S x a`. Under the regular value class assumed by
`StandardComplianceLocalCertificate` (where
`p.DynamicArgmaxUnique E.V_S` holds), `ρ` coincides pointwise with
the upper-selector `p.σ_dyn_top E.V_S x a` (the Top-version `ρ`
defined in `JointPreferenceBasin.lean`). -/

/-- **Sender response projection** for the ordinary
`FeedbackStackelbergEquilibrium`. Exposes the implicit Sender
best response `p.σ_dyn E.V_S x a` as an accessible function. -/
noncomputable def FeedbackStackelbergEquilibrium.ρ
    {p : Params} (E : p.FeedbackStackelbergEquilibrium)
    (x a : ℝ) : ℝ :=
  p.σ_dyn E.V_S x a

/-- The Sender response projection lies in the feasible set
`[0, 1]` — `σ_dyn V_S x a ∈ Sanctions.I` by `σ_dyn_mem`. -/
theorem FeedbackStackelbergEquilibrium.ρ_mem
    {p : Params} (E : p.FeedbackStackelbergEquilibrium) (x a : ℝ) :
    E.ρ x a ∈ Sanctions.I :=
  p.σ_dyn_mem E.V_S x a

/-- **Sender best-response optimality at the equilibrium.** The
Sender response projection `E.ρ x a = p.σ_dyn E.V_S x a` is a
maximizer of the Sender dynamic objective at the equilibrium
continuation value `E.V_S`. Makes the Sender side of the
equilibrium visibly sequentially rational at every `(x, a)`. -/
theorem FeedbackStackelbergEquilibrium.ρ_isMaxOn
    {p : Params} (E : p.FeedbackStackelbergEquilibrium) (x a : ℝ) :
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * E.V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I (E.ρ x a) :=
  p.σ_dyn_isMaxOn E.V_S x a

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
