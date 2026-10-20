/-
Sanctions/Theory/Equilibrium/SelectionRobust.lean

**Robust selection layer for the abstract game.**

This file closes a referee-style objection against the upper-selector
top-line equilibrium API: that the top selector `σ_dyn_top` could
"cherry-pick" the favorable Sender maximizer. Two complementary
results are provided:

1. **Uniqueness bridge** (`FeedbackStackelbergEquilibrium.toTop_of_unique`).
   When the dynamic Sender argmax is unique at every (x, a), the
   ordinary (Berge-continuous) `σ_dyn` selector and the upper
   `σ_dyn_top` selector coincide, so a `FeedbackStackelbergEquilibrium`
   (ordinary) and a `FeedbackStackelbergEquilibriumTop` are the same
   object. This removes any selection artifact.

2. **Robust selection theorem**
   (`sender_any_argmax_high_of_strictMono_below_threshold`). If the
   Sender objective is strictly increasing below the basin threshold,
   then *every* Sender best response is at least the threshold — not
   only the upper-selector one.

3. **Every selection convention coincides under uniqueness** (round AJ,
   2026-09-22; doc 98 B6). `SigmaDynComparison` already has the lower
   selector `σ_dyn_bot` and the per-`(x, a)` collapse
   `extremal_selectors_coincide_at_unique_argmax`. Added here: under
   `DynamicArgmaxUnique`, *every* function that picks a maximiser at each
   `(x, a)` — greatest, least, leader-favourable, or any other — equals
   `σ_dyn_top` at every feasible state (`selector_eq_σ_dyn_top_of_unique`),
   the lower selector in particular (`σ_dyn_bot_eq_σ_dyn_top_of_unique`), and
   the argmax set is the singleton `{σ_dyn_top}`
   (`dynamicArgmaxSet_eq_singleton_of_unique`). This is the sentence that
   answers "the greatest selector is the leader-favourable one": on the
   delivered families the argmax is a singleton, so no convention selects
   anything.

4. **Compliance-local uniqueness** (round BJ4.3, 2026-10-08).
   `DynamicArgmaxUniqueOnI` asks for uniqueness only at physical compliance
   levels `a ∈ [0,1]`; `DynamicArgmaxUnique.toOnI` forgets the rest, and
   `joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI` is the matching
   integrand bridge. The value-class route consumes this weaker form.

All results are purely structural and add no new fields to
`AbstractGame.Params`; all hypotheses are theorem-parameter primitives
or recoverable from existing hypotheses.

This file does not depend on any concrete payoff form.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Equilibrium.StackelbergFeedback

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Uniqueness predicate

The natural uniqueness statement for the dynamic Sender argmax: at
every `(x, a)`, any two maximizers of the dynamic objective on the
feasible action set `Sanctions.I` coincide. This is exactly the
hypothesis form of `σ_dyn_continuous_of_unique` (`BergeContinuity`)
and a *uniform* strengthening of the per-`(x, a)` form used by
`σ_dyn_eq_σ_dyn_top_of_unique` (`SigmaDynComparison`). -/

/-- **Global uniqueness of the dynamic Sender argmax (all states).**
At every `(x, a)` with `x : ℝ` unrestricted, any two `IsMaxOn`-witnesses
of the dynamic Sender objective on `Sanctions.I` agree. This is the
legacy `∀ x : ℝ` form, retained for the *global* existence route where
Berge continuity must produce a selector continuous on all of `ℝ`. It is
genuinely stronger than `DynamicArgmaxUnique`: an economy with an
interior Sender argmax generally fails it at unphysical states `x ∉ [0,1]`
(a convex clip kink can create two equal maxima). -/
def DynamicArgmaxUniqueGlobal
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : Prop :=
  ∀ x a s₁ s₂,
    s₁ ∈ Sanctions.I →
    s₂ ∈ Sanctions.I →
    IsMaxOn
      (fun s' => p.U_S x a s'
        + p.β_S * V_S
          (Sanctions.clipS' (p.F x s')))
      Sanctions.I s₁ →
    IsMaxOn
      (fun s' => p.U_S x a s'
        + p.β_S * V_S
          (Sanctions.clipS' (p.F x s')))
      Sanctions.I s₂ →
    s₁ = s₂

/-- **State-local uniqueness of the dynamic Sender argmax (Design A).**
Uniqueness of the dynamic Sender argmax only at *physical* states
`x ∈ S = [0,1]` — the economically meaningful domain, since the clamped
dynamics (`clipS'`) never leave `[0,1]`. This is the canonical form:
the dynamic-programming literature poses argmax uniqueness on the state
space, not on all of `ℝ`. Discharged from strict concavity / strict
monotonicity of the Sender objective *on `S`*. The global existence
route consumes the stronger `DynamicArgmaxUniqueGlobal`; the certificate
and its interior-argmax witnesses consume this state-local form. -/
def DynamicArgmaxUnique
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : Prop :=
  ∀ x ∈ Sanctions.S, ∀ a s₁ s₂,
    s₁ ∈ Sanctions.I →
    s₂ ∈ Sanctions.I →
    IsMaxOn
      (fun s' => p.U_S x a s'
        + p.β_S * V_S
          (Sanctions.clipS' (p.F x s')))
      Sanctions.I s₁ →
    IsMaxOn
      (fun s' => p.U_S x a s'
        + p.β_S * V_S
          (Sanctions.clipS' (p.F x s')))
      Sanctions.I s₂ →
    s₁ = s₂

/-- Global uniqueness restricts to state-local uniqueness (trivial). -/
theorem dynamicArgmaxUnique_of_global
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h : p.DynamicArgmaxUniqueGlobal V_S) :
    p.DynamicArgmaxUnique V_S :=
  fun x _hx a s₁ s₂ hs₁ hs₂ h₁ h₂ => h x a s₁ s₂ hs₁ hs₂ h₁ h₂

/-- **Compliance-local uniqueness of the dynamic Sender argmax (round BJ4.3,
2026-10-08).** Uniqueness of the dynamic Sender argmax only at physical states
`x ∈ S` *and* at physical compliance levels `a ∈ I = [0,1]`. General in `F`.

`DynamicArgmaxUnique` quantifies over every real `a`, although the Target only
ever chooses `a ∈ [0,1]` and the joint Target Bellman operator only reads the
Sender's response there. On the symbolic corner family, whose Sender stage
payoff is affine in `a`, the stage tilt can be pushed arbitrarily far off
`[0,1]`, and a value function with a convex kink then gives two Sender
maximisers: there, uniqueness at every real `a` costs a curvature condition that
uniqueness at physical compliance does not. This predicate drops the
unphysical compliance levels: it is what the state-local value-class route
(`jointTarget_BCF_on_S`, `α_on_ext`, `ValueClass2.sender_unique_on`) consumes.
Every `DynamicArgmaxUnique` proof gives one (`DynamicArgmaxUnique.toOnI`). -/
def DynamicArgmaxUniqueOnI
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : Prop :=
  ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ∀ s₁ s₂,
    s₁ ∈ Sanctions.I →
    s₂ ∈ Sanctions.I →
    IsMaxOn
      (fun s' => p.U_S x a s'
        + p.β_S * V_S
          (Sanctions.clipS' (p.F x s')))
      Sanctions.I s₁ →
    IsMaxOn
      (fun s' => p.U_S x a s'
        + p.β_S * V_S
          (Sanctions.clipS' (p.F x s')))
      Sanctions.I s₂ →
    s₁ = s₂

/-- **State-local uniqueness restricts to compliance-local uniqueness (round
BJ4.3, trivial).** General in `F`. Forgets the compliance levels outside
`[0,1]`; this is how an existing `DynamicArgmaxUnique` discharger feeds the
compliance-local value-class route. -/
theorem DynamicArgmaxUnique.toOnI
    {p : Sanctions.AbstractGame.Params}
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h : p.DynamicArgmaxUnique V_S) :
    p.DynamicArgmaxUniqueOnI V_S :=
  fun x hx a _ha s₁ s₂ hs₁ hs₂ h₁ h₂ => h x hx a s₁ s₂ hs₁ hs₂ h₁ h₂

/-! ## 2. Bridge: top integrand ≡ ordinary integrand under uniqueness -/

/-- **Top vs ordinary joint Target integrand under uniqueness.**
At every `(x, a)`, the top-selector integrand equals the ordinary
`σ_dyn`-selector integrand. This is the load-bearing pointwise
identity used by the bridge `toTop_of_unique`. -/
theorem joint_T_top_integrand_eq_joint_T_integrand_of_unique
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_unique : p.DynamicArgmaxUnique V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    p.joint_T_top_integrand V_T V_S x a =
      p.joint_T_integrand V_T V_S x a := by
  have hσ : p.σ_dyn V_S x a = p.σ_dyn_top V_S x a :=
    p.σ_dyn_eq_σ_dyn_top_of_unique V_S x a
      (fun s₁ s₂ hs₁ hs₂ h₁ h₂ => h_unique x hx a s₁ s₂ hs₁ hs₂ h₁ h₂)
  unfold joint_T_top_integrand joint_T_integrand
  rw [← hσ]

/-- **Top vs ordinary joint Target integrand at physical compliance (round
BJ4.3, 2026-10-08).** Compliance-local sibling of
`joint_T_top_integrand_eq_joint_T_integrand_of_unique`. General in `F`. At a
physical state `x ∈ S` and a physical compliance level `a ∈ I`, the
top-selector integrand equals the ordinary `σ_dyn` integrand. Needs only
`DynamicArgmaxUniqueOnI`: uniqueness at compliance levels outside `[0,1]` is
dropped, at the price of reading the identity only at `a ∈ [0,1]`, which is
every compliance level the Target's Bellman problem evaluates. -/
theorem joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_unique : p.DynamicArgmaxUniqueOnI V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) {a : ℝ} (ha : a ∈ Sanctions.I) :
    p.joint_T_top_integrand V_T V_S x a =
      p.joint_T_integrand V_T V_S x a := by
  have hσ : p.σ_dyn V_S x a = p.σ_dyn_top V_S x a :=
    p.σ_dyn_eq_σ_dyn_top_of_unique V_S x a
      (fun s₁ s₂ hs₁ hs₂ h₁ h₂ => h_unique x hx a ha s₁ s₂ hs₁ hs₂ h₁ h₂)
  unfold joint_T_top_integrand joint_T_integrand
  rw [← hσ]

/-- **Top vs ordinary realized sanction rule under uniqueness.**
At any policy `α`, the upper-selector realized rule and the ordinary
`σ_dyn`-realized rule are pointwise equal. -/
theorem dynamicTopRealizedRule_eq_dynamicRealizedRule_of_unique
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    (h_unique : p.DynamicArgmaxUnique V_S) :
    Set.EqOn (p.dynamicTopRealizedRule V_S α)
      (p.dynamicRealizedRule V_S α) Sanctions.S := by
  intro x hx
  unfold dynamicTopRealizedRule dynamicRealizedRule
  exact (p.σ_dyn_eq_σ_dyn_top_of_unique V_S x (α x)
      (fun s₁ s₂ hs₁ hs₂ h₁ h₂ =>
        h_unique x hx (α x) s₁ s₂ hs₁ hs₂ h₁ h₂)).symm

/-! ## 3. Equilibrium bridge: ordinary ⇒ top under uniqueness -/

/-- **Ordinary feedback Stackelberg equilibrium lifts to the
top-selector equilibrium under argmax uniqueness.**

If a `FeedbackStackelbergEquilibrium` `E` satisfies
`DynamicArgmaxUnique E.V_S`, then the same data
`(V_T, V_S, α, hα)` is also a `FeedbackStackelbergEquilibriumTop`.
Operationally this says: the top-selector machinery in
`JointPreferenceBasin` is not a separate equilibrium concept; it
coincides with the ordinary Berge-continuous equilibrium whenever the
follower's argmax is unique. -/
noncomputable def FeedbackStackelbergEquilibrium.toTop_of_unique
    {p : Params}
    (E : p.FeedbackStackelbergEquilibrium)
    (h_unique : p.DynamicArgmaxUnique E.V_S) :
    p.FeedbackStackelbergEquilibriumTop where
  V_T := E.V_T
  V_S := E.V_S
  α := E.α
  hα := E.hα
  α_mem := fun x _hx => E.α_mem x
  V_S_fix := E.V_S_fix
  V_T_fix_top := by
    intro x
    have hfun :
        (fun a => p.joint_T_top_integrand E.V_T E.V_S x.val a) =
          (fun a => p.joint_T_integrand E.V_T E.V_S x.val a) := by
      funext a
      exact p.joint_T_top_integrand_eq_joint_T_integrand_of_unique
        h_unique x.property a
    rw [hfun]
    exact E.V_T_fix x
  α_opt_top := by
    intro x hx a ha
    have hbase := E.α_opt x ha
    change p.joint_T_top_integrand E.V_T E.V_S x a ≤
        p.joint_T_top_integrand E.V_T E.V_S x (E.α x)
    rw [p.joint_T_top_integrand_eq_joint_T_integrand_of_unique
          h_unique hx a,
        p.joint_T_top_integrand_eq_joint_T_integrand_of_unique
          h_unique hx (E.α x)]
    exact hbase

/-! ## 4. Robust selection: every Sender maximizer is high

The cleanest answer to the "the top selector might be cherry-picking"
objection. Under strict monotonicity of the dynamic Sender objective
below the basin threshold `max x sbar`, *any* `IsMaxOn` witness on
`Sanctions.I` is automatically at least `max x sbar`. The
`sender_high_argmax_exists_of_strictMono_below_threshold` lemma in
`JointPreferenceBasin` produces one such maximizer; this theorem
upgrades that to the much stronger universal statement. -/

/-- **Robust selection.** Under strict monotonicity of the dynamic
Sender objective on `[0, max x sbar]` at every basin state, every
dynamic Sender maximizer on `Sanctions.I` is at least the basin
threshold `max x sbar`. Hence the high-sanction conclusion is not an
artifact of choosing the upper maximizer. -/
theorem sender_any_argmax_high_of_strictMono_below_threshold
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xbar sbar : ℝ}
    (hxbar_nonneg : 0 ≤ xbar)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_strict : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      StrictMonoOn
        (fun s => p.senderDynObjective V_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∀ s ∈ Sanctions.I,
        IsMaxOn
          (fun s' => p.senderDynObjective V_S x (α x) s')
          Sanctions.I s →
        max x sbar ≤ s := by
  intro x hx s hsI hsMax
  by_contra hnot
  have hs_lt : s < max x sbar := not_le.mp hnot
  have hx_nonneg : (0 : ℝ) ≤ x := le_trans hxbar_nonneg hx.1
  have hthreshold_mem : max x sbar ∈ Sanctions.I := by
    refine ⟨?_, max_le hx.2 hsbar_mem.2⟩
    exact le_max_of_le_left hx_nonneg
  have hs_low : s ∈ Set.Icc (0 : ℝ) (max x sbar) :=
    ⟨hsI.1, le_of_lt hs_lt⟩
  have ht_low : max x sbar ∈ Set.Icc (0 : ℝ) (max x sbar) :=
    ⟨hthreshold_mem.1, le_rfl⟩
  have hlt :
      p.senderDynObjective V_S x (α x) s
        < p.senderDynObjective V_S x (α x) (max x sbar) :=
    h_strict x hx hs_low ht_low hs_lt
  have hmax :
      p.senderDynObjective V_S x (α x) (max x sbar)
        ≤ p.senderDynObjective V_S x (α x) s :=
    hsMax hthreshold_mem
  linarith

/-! ## 4. Every selection convention coincides under uniqueness (round AJ) -/

/-- **Every selector coincides with the upper selector under uniqueness.** Any
function that picks a maximiser of the dynamic Sender objective at each
feasible state and compliance equals `σ_dyn_top` there. -/
theorem selector_eq_σ_dyn_top_of_unique
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (h_unique : p.DynamicArgmaxUnique V_S)
    {σ' : ℝ → ℝ → ℝ} (hσ' : ∀ x ∈ Sanctions.S, ∀ a, σ' x a ∈ p.dynamicArgmaxSet V_S x a) :
    ∀ x ∈ Sanctions.S, ∀ a, σ' x a = p.σ_dyn_top V_S x a := by
  intro x hx a
  have h1 := hσ' x hx a
  have h2 := p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
  exact h_unique x hx a _ _ h1.1 h2.1 h1.2 h2.2

/-- **The pessimistic and the upper selector coincide under uniqueness**, at
every feasible state. -/
theorem σ_dyn_bot_eq_σ_dyn_top_of_unique
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (h_unique : p.DynamicArgmaxUnique V_S) :
    ∀ x ∈ Sanctions.S, ∀ a, p.σ_dyn_bot V_S x a = p.σ_dyn_top V_S x a :=
  p.selector_eq_σ_dyn_top_of_unique h_unique
    (fun x _ a => p.σ_dyn_bot_mem_dynamicArgmaxSet V_S x a)

/-- **The argmax set is a singleton under uniqueness**: it is `{σ_dyn_top}`. -/
theorem dynamicArgmaxSet_eq_singleton_of_unique
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (h_unique : p.DynamicArgmaxUnique V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    p.dynamicArgmaxSet V_S x a = {p.σ_dyn_top V_S x a} := by
  ext s
  constructor
  · intro hs
    have h2 := p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
    exact h_unique x hx a _ _ hs.1 h2.1 hs.2 h2.2
  · intro hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a

end Params
end AbstractGame

end

#print axioms Sanctions.AbstractGame.Params.selector_eq_σ_dyn_top_of_unique
#print axioms Sanctions.AbstractGame.Params.σ_dyn_bot_eq_σ_dyn_top_of_unique
#print axioms Sanctions.AbstractGame.Params.dynamicArgmaxSet_eq_singleton_of_unique

end Sanctions
