/-
Sanctions/Theory/Equilibrium/LeaderArgmaxOrderRefutation.lean

**Parametric refutation of the POINTWISE-ORDER monotone comparative
static for the leader's joint-Bellman argmax.**

The dual-Tarski route to from-primitives equilibrium existence
(`Foundations/TarskiMPE.joint_value_fixedPoint_via_dual`) needs
the joint value operator to be an order homomorphism on the dualized
value rectangle. Its load-bearing ingredient is that the leader's
joint-Bellman argmax be *antitone* in the Target continuation value
`V_T` under the **pointwise** order `V_T ≤ V_T' :⟺ ∀ y, V_T y ≤ V_T' y`.

This file shows the ingredient fails — and fails in *both* directions —
at **every** economy in which the leader's own action moves the
successor political state at a strictly positive rate. Nothing here is
witness-specific: the perturbations are constructed from the economy's
own successor states.

## The construction

Write `y(b) := clipS'(F(x, σ_dyn(V_S, x, b)))` for the political state
that follows leader action `b` once the Sender has best-responded. The
*placation channel* hypothesis is `κ * (b' − b) ≤ y(b) − y(b')` for
`b ≤ b'`: more compliance buys a strictly lower successor state, at
rate at least `κ > 0`.

Two one-sided ramps then do all the work, and both are **nonnegative**,
so both move the continuation value **up** in the pointwise order (`≤`,
which is all that order asks):

* `lowStateRamp c (y 0)` — pays `c · (y(0) − y)` for states below the
  defiance successor, i.e. rewards *low* continuation states. Adding it
  makes the leader integrand nondecreasing in compliance, so the argmax
  is driven to full compliance `a = 1`
  (`leaderArgmax_lowStateRamp_isMaxOn_one`).
* `highStateRamp c (y 1)` — pays `c · (y − y(1))` for states above the
  full-compliance successor, i.e. rewards *high* continuation states.
  Adding it makes the leader integrand nonincreasing in compliance, so
  the argmax is driven to full defiance `a = 0`
  (`leaderArgmax_highStateRamp_isMaxOn_zero`).

In both cases the required ramp height is the closed form
`c ≥ L / (β_T · κ)`, where `L` bounds the base integrand's variation in
compliance: the perturbation only has to out-earn the base integrand's
own slope through the discounted placation channel. No magnitude is
chosen; `c`, `κ`, `L` are symbolic and constrained by one strict
inequality.

## What this closes, and what it does not

**Closed.** The pointwise-order Tarski / order-homomorphism route: no
choice of pointwise-ordered value rectangle repairs the comparative
static, because for any base value the argmax can be driven to *either*
corner by a *nonnegative* increment. Both refutations below are
unconditional in the value function they perturb.

**Not closed.** The **slope-order** route of Curtat (1996). Curtat
orders continuation values by their derivatives — `∂v ≥ ∂w` iff
`∂v(u) ≥ ∂w(u)` a.e. (Curtat 1996, §4.1) — not pointwise, and his
Theorem 4.1 delivers a unique pure Nash equilibrium of the reduced game
that is increasing *in the state and in the slope* `∂ṽ`; existence of
the Markov equilibrium then comes from **Schauder's** theorem on a
compact convex set of increasing Lipschitz functions (Theorem 4.6), not
from Tarski, with the slope bounds computable from primitives. The
present refutation says nothing about that route:

* `lowStateRamp` is *antitone* in the state (`lowStateRamp_antitone`),
  hence not positive in the slope order at all; and
* `highStateRamp` is *monotone* (`highStateRamp_monotone`), hence
  positive in the slope order — but the argmax it moves is driven
  **down**, which is what Curtat's Theorem 4.1 predicts once the
  transition is *decreasing* in the leader's action. The placation
  hypothesis `κ * (b' − b) ≤ y(b) − y(b')` is exactly the negation of
  the stochastic-monotonicity input to Theorem 4.1, so an economy
  satisfying it is outside Curtat's supermodular class and cannot be a
  counterexample to his theorem.

So: pointwise-order Tarski is refuted here; slope-order + Schauder is
untouched and remains a live route.

**Rule 3.** No new `Params` field, no new structure field, and no new
`Prop` taken as a hypothesis of any load-bearing theorem. Every
hypothesis below (`0 < β_T`, the placation rate `κ`, the variation
bound `L`, the ramp height `c`) is a universally quantified scalar of a
*standalone conditional refutation*, discharged at the call site.

**Rule 5.** Fully parametric in `p : AbstractGame.Params`, in the
continuation values, in the state, and in the three scalars. The B2
numeric counterexample in `Examples/JointBellmanNotOrderHom.lean` is a
one-line specialization.
-/

import Sanctions.Theory.Equilibrium.JointMPE

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

/-! ## 1. One-sided ramps on the state space

Two nonnegative, Lipschitz, single-kink increments. They are the whole
perturbation vocabulary of this file: everything below is one of these
two added to an arbitrary continuation value. -/

/-- **Low-state ramp.** `lowStateRamp c t` pays `c · (t − y)` at states
`y` below the anchor `t` and nothing at or above it: a nonnegative
increment that rewards *low* political states. -/
def lowStateRamp (c t : ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk
      (fun y : ↥(Sanctions.S : Set ℝ) => c * max (t - y.val) 0)
      (by fun_prop))

@[simp] theorem lowStateRamp_apply (c t : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    lowStateRamp c t y = c * max (t - y.val) 0 := rfl

/-- **High-state ramp.** `highStateRamp c t` pays `c · (y − t)` at
states `y` above the anchor `t` and nothing at or below it: a
nonnegative increment that rewards *high* political states. -/
def highStateRamp (c t : ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk
      (fun y : ↥(Sanctions.S : Set ℝ) => c * max (y.val - t) 0)
      (by fun_prop))

@[simp] theorem highStateRamp_apply (c t : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    highStateRamp c t y = c * max (y.val - t) 0 := rfl

/-- The low-state ramp is nonnegative — adding it moves the
continuation value **up** in the pointwise order. -/
theorem lowStateRamp_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ)
    (y : ↥(Sanctions.S : Set ℝ)) : 0 ≤ lowStateRamp c t y :=
  mul_nonneg hc (le_max_right _ _)

/-- The high-state ramp is nonnegative — adding it moves the
continuation value **up** in the pointwise order. -/
theorem highStateRamp_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ)
    (y : ↥(Sanctions.S : Set ℝ)) : 0 ≤ highStateRamp c t y :=
  mul_nonneg hc (le_max_right _ _)

/-- The low-state ramp is **state-antitone**: it is *not* positive in
Curtat's slope order, so the refutation it powers bites only the
pointwise order. -/
theorem lowStateRamp_antitone {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    Antitone (fun y : ↥(Sanctions.S : Set ℝ) => lowStateRamp c t y) := by
  intro y₁ y₂ h
  simp only [lowStateRamp_apply]
  exact mul_le_mul_of_nonneg_left
    (max_le_max (by simpa using sub_le_sub_left (Subtype.coe_le_coe.mpr h) t)
      le_rfl) hc

/-- The high-state ramp is **state-monotone**: an increment positive in
Curtat's slope order. -/
theorem highStateRamp_monotone {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    Monotone (fun y : ↥(Sanctions.S : Set ℝ) => highStateRamp c t y) := by
  intro y₁ y₂ h
  simp only [highStateRamp_apply]
  exact mul_le_mul_of_nonneg_left
    (max_le_max (by simpa using sub_le_sub_right (Subtype.coe_le_coe.mpr h) t)
      le_rfl) hc

/-- The low-state ramp is `|c|`-Lipschitz in the state, so restricting
the value carriers to Lipschitz functions does not exclude it. -/
theorem lowStateRamp_lipschitz (c t : ℝ) (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    |lowStateRamp c t y₂ - lowStateRamp c t y₁| ≤ |c| * dist y₁ y₂ := by
  simp only [lowStateRamp_apply, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  refine (abs_max_sub_max_le_abs (t - y₂.val) (t - y₁.val) 0).trans ?_
  rw [Subtype.dist_eq, Real.dist_eq]
  exact le_of_eq (by rw [show t - y₂.val - (t - y₁.val) = y₁.val - y₂.val from by
    ring])

/-- The high-state ramp is `|c|`-Lipschitz in the state, so restricting
the value carriers to Lipschitz functions does not exclude it. -/
theorem highStateRamp_lipschitz (c t : ℝ) (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) :
    |highStateRamp c t y₂ - highStateRamp c t y₁| ≤ |c| * dist y₁ y₂ := by
  simp only [highStateRamp_apply, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  refine (abs_max_sub_max_le_abs (y₂.val - t) (y₁.val - t) 0).trans ?_
  rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm y₁.val y₂.val]
  apply le_of_eq
  congr 1
  ring

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 2. The leader's successor state, and additivity of the integrand -/

/-- **The leader's successor political state.** After the leader plays
compliance `a` at state `x` and the Sender best-responds with the
forward-looking argmax `σ_dyn V_S x a`, the economy moves to
`clipS'(F(x, σ_dyn V_S x a))`. This is a *derived* object: the sanction
entering it is the Sender's optimum, never a fixed rule (Rule 1). -/
def jointSucc (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    ↥(Sanctions.S : Set ℝ) :=
  Sanctions.clipS' (p.F x (p.σ_dyn V_S x a))

/-- The leader integrand rewritten through the successor state. -/
theorem joint_T_integrand_eq_succ
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.joint_T_integrand V_T V_S x a
      = p.U_T x a (p.σ_dyn V_S x a) + p.β_T * V_T (p.jointSucc V_S x a) :=
  rfl

/-- **Additivity of the leader integrand in the Target continuation
value.** Perturbing `V_T` by `W` shifts the leader's payoff at action
`a` by exactly the discounted increment evaluated at that action's
successor state — the Sender's response, and hence the successor state
itself, do not move, because `σ_dyn` depends only on `V_S`. This is the
engine of every refutation below. -/
theorem joint_T_integrand_add
    (V_T W V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.joint_T_integrand (V_T + W) V_S x a
      = p.joint_T_integrand V_T V_S x a
        + p.β_T * W (p.jointSucc V_S x a) := by
  rw [p.joint_T_integrand_eq_succ, p.joint_T_integrand_eq_succ]
  simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
  ring

/-! ## 3. Driving the leader argmax to either corner -/

/-- **A nonnegative low-state ramp drives the leader argmax to full
compliance.**

Hypotheses, in English:

* `hβ` — the Target discounts the future strictly (`0 < β_T`), so the
  continuation channel is live;
* `hplac` — *placation*: raising compliance from `b` to `b'` lowers the
  successor political state by at least `κ · (b' − b)`, `κ > 0`;
* `hvar` — the base leader integrand falls by at most `L · (b' − b)`
  when compliance rises from `b` to `b'` (a one-sided variation bound);
* `hgain` — the ramp is tall enough that its discounted placation gain
  `β_T · c · κ` covers that fall, `L ≤ β_T · c · κ`.

Conclusion: after adding `lowStateRamp c (y 0)` — a **nonnegative**
increment, so the continuation value has risen in the pointwise order —
full compliance `a = 1` maximizes the leader's integrand on `[0,1]`.

No magnitude is chosen: `c` is any height past the closed-form
threshold `L / (β_T · κ)`. -/
theorem leaderArgmax_lowStateRamp_isMaxOn_one
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ)
    {κ L c : ℝ} (hβ : 0 < p.β_T) (hκ : 0 < κ) (hc : 0 ≤ c)
    (hplac : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      κ * (b' - b)
        ≤ (p.jointSucc V_S x b).val - (p.jointSucc V_S x b').val)
    (hvar : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      p.joint_T_integrand V_T V_S x b - p.joint_T_integrand V_T V_S x b'
        ≤ L * (b' - b))
    (hgain : L ≤ p.β_T * c * κ) :
    IsMaxOn (fun b => p.joint_T_integrand
        (V_T + Sanctions.lowStateRamp c (p.jointSucc V_S x 0).val) V_S x b)
      Sanctions.I 1 := by
  have h0 : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  have hbc : 0 ≤ p.β_T * c := mul_nonneg hβ.le hc
  -- every successor sits weakly below the full-defiance successor
  have hbelow : ∀ b ∈ Sanctions.I,
      (p.jointSucc V_S x b).val ≤ (p.jointSucc V_S x 0).val := by
    intro b hb
    have hp := hplac 0 h0 b hb hb.1
    nlinarith [mul_nonneg hκ.le hb.1]
  rw [isMaxOn_iff]
  intro b hb
  have hb1 : b ≤ 1 := hb.2
  have hva := hvar b hb 1 h1 hb1
  have hpl := hplac b hb 1 h1 hb1
  rw [p.joint_T_integrand_add, p.joint_T_integrand_add]
  simp only [Sanctions.lowStateRamp_apply]
  rw [max_eq_left (by linarith [hbelow b hb] :
        (0:ℝ) ≤ (p.jointSucc V_S x 0).val - (p.jointSucc V_S x b).val),
      max_eq_left (by linarith [hbelow 1 h1] :
        (0:ℝ) ≤ (p.jointSucc V_S x 0).val - (p.jointSucc V_S x 1).val)]
  have step1 : L * (1 - b) ≤ p.β_T * c * κ * (1 - b) := by
    have hnn : (0:ℝ) ≤ 1 - b := by linarith
    nlinarith
  have step2 : p.β_T * c * (κ * (1 - b))
      ≤ p.β_T * c * ((p.jointSucc V_S x b).val
        - (p.jointSucc V_S x 1).val) :=
    mul_le_mul_of_nonneg_left hpl hbc
  nlinarith [step1, step2, hva]

/-- **A nonnegative high-state ramp drives the leader argmax to full
defiance.**

The mirror image of `leaderArgmax_lowStateRamp_isMaxOn_one`: same
placation hypothesis, the *other* one-sided variation bound (`hvar'`:
the base integrand rises by at most `L · (b' − b)` in compliance), and
the ramp anchored at the full-compliance successor `y 1`. After adding
`highStateRamp c (y 1)` — again a **nonnegative** increment, and this
one is also *state-monotone*, hence positive in Curtat's slope order —
full defiance `a = 0` maximizes the leader's integrand on `[0,1]`. -/
theorem leaderArgmax_highStateRamp_isMaxOn_zero
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ)
    {κ L c : ℝ} (hβ : 0 < p.β_T) (hκ : 0 < κ) (hc : 0 ≤ c)
    (hplac : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      κ * (b' - b)
        ≤ (p.jointSucc V_S x b).val - (p.jointSucc V_S x b').val)
    (hvar' : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      p.joint_T_integrand V_T V_S x b' - p.joint_T_integrand V_T V_S x b
        ≤ L * (b' - b))
    (hgain : L ≤ p.β_T * c * κ) :
    IsMaxOn (fun b => p.joint_T_integrand
        (V_T + Sanctions.highStateRamp c (p.jointSucc V_S x 1).val) V_S x b)
      Sanctions.I 0 := by
  have h0 : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  have hbc : 0 ≤ p.β_T * c := mul_nonneg hβ.le hc
  -- every successor sits weakly above the full-compliance successor
  have habove : ∀ b ∈ Sanctions.I,
      (p.jointSucc V_S x 1).val ≤ (p.jointSucc V_S x b).val := by
    intro b hb
    have hp := hplac b hb 1 h1 hb.2
    nlinarith [mul_nonneg hκ.le (by linarith [hb.2] : (0:ℝ) ≤ 1 - b)]
  rw [isMaxOn_iff]
  intro b hb
  have hb0 : 0 ≤ b := hb.1
  have hva := hvar' 0 h0 b hb hb0
  have hpl := hplac 0 h0 b hb hb0
  rw [p.joint_T_integrand_add, p.joint_T_integrand_add]
  simp only [Sanctions.highStateRamp_apply]
  rw [max_eq_left (by linarith [habove b hb] :
        (0:ℝ) ≤ (p.jointSucc V_S x b).val - (p.jointSucc V_S x 1).val),
      max_eq_left (by linarith [habove 0 h0] :
        (0:ℝ) ≤ (p.jointSucc V_S x 0).val - (p.jointSucc V_S x 1).val)]
  have step1 : L * (b - 0) ≤ p.β_T * c * κ * (b - 0) := by
    nlinarith
  have step2 : p.β_T * c * (κ * (b - 0))
      ≤ p.β_T * c * ((p.jointSucc V_S x 0).val
        - (p.jointSucc V_S x b).val) :=
    mul_le_mul_of_nonneg_left hpl hbc
  nlinarith [step1, step2, hva]

/-! ## 4. The two refutations -/

/-- **The leader's joint-Bellman argmax is NOT antitone in `V_T` under
the pointwise order** — parametrically, at every economy with a live
placation channel.

Given a base continuation value whose leader argmax `a` is anything
short of full compliance, the nonnegative low-state ramp raises the
continuation value pointwise and moves the argmax up to `1 > a`. Hence
the "D3b" ingredient of the dual-Tarski order-homomorphism route
(`TarskiMPE.joint_value_fixedPoint_via_dual`) cannot be instantiated on
any pointwise-ordered value rectangle containing these values. -/
theorem leaderArgmax_not_antitone_pointwise
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) (hx : x ∈ Sanctions.S)
    {κ L c a : ℝ} (hβ : 0 < p.β_T) (hκ : 0 < κ) (hc : 0 ≤ c)
    (hplac : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      κ * (b' - b)
        ≤ (p.jointSucc V_S x b).val - (p.jointSucc V_S x b').val)
    (hvar : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      p.joint_T_integrand V_T V_S x b - p.joint_T_integrand V_T V_S x b'
        ≤ L * (b' - b))
    (hgain : L ≤ p.β_T * c * κ)
    (ha : a ∈ Sanctions.I) (ha1 : a < 1)
    (hmax : IsMaxOn (fun b => p.joint_T_integrand V_T V_S x b)
      Sanctions.I a) :
    ¬ (∀ (W_T W_T' W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
        (∀ y, W_T y ≤ W_T' y) →
        ∀ z ∈ Sanctions.S, ∀ b b' : ℝ,
          b ∈ Sanctions.I → b' ∈ Sanctions.I →
          IsMaxOn (fun t => p.joint_T_integrand W_T W_S z t)
            Sanctions.I b →
          IsMaxOn (fun t => p.joint_T_integrand W_T' W_S z t)
            Sanctions.I b' →
          b' ≤ b) := by
  intro h
  have hord : ∀ y, V_T y
      ≤ (V_T + Sanctions.lowStateRamp c (p.jointSucc V_S x 0).val) y := by
    intro y
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    linarith [Sanctions.lowStateRamp_nonneg hc (p.jointSucc V_S x 0).val y]
  have h1max := p.leaderArgmax_lowStateRamp_isMaxOn_one V_T V_S x hβ hκ hc
    hplac hvar hgain
  have hcon := h V_T _ V_S hord x hx a 1 ha ⟨zero_le_one, le_refl 1⟩
    hmax h1max
  linarith

/-- **The leader's joint-Bellman argmax is NOT monotone in `V_T` under
the pointwise order either** — the mirror refutation.

Given a base continuation value whose leader argmax `a` is anything
short of full defiance, the nonnegative high-state ramp raises the
continuation value pointwise and moves the argmax **down** to `0 < a`.

Together with `leaderArgmax_not_antitone_pointwise` this says the
pointwise order on continuation values constrains the leader's argmax
in *neither* direction: a pointwise increase can push compliance to
either corner, depending only on which successor state the increment is
concentrated near. -/
theorem leaderArgmax_not_monotone_pointwise
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) (hx : x ∈ Sanctions.S)
    {κ L c a : ℝ} (hβ : 0 < p.β_T) (hκ : 0 < κ) (hc : 0 ≤ c)
    (hplac : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      κ * (b' - b)
        ≤ (p.jointSucc V_S x b).val - (p.jointSucc V_S x b').val)
    (hvar' : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
      p.joint_T_integrand V_T V_S x b' - p.joint_T_integrand V_T V_S x b
        ≤ L * (b' - b))
    (hgain : L ≤ p.β_T * c * κ)
    (ha : a ∈ Sanctions.I) (ha0 : 0 < a)
    (hmax : IsMaxOn (fun b => p.joint_T_integrand V_T V_S x b)
      Sanctions.I a) :
    ¬ (∀ (W_T W_T' W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
        (∀ y, W_T y ≤ W_T' y) →
        ∀ z ∈ Sanctions.S, ∀ b b' : ℝ,
          b ∈ Sanctions.I → b' ∈ Sanctions.I →
          IsMaxOn (fun t => p.joint_T_integrand W_T W_S z t)
            Sanctions.I b →
          IsMaxOn (fun t => p.joint_T_integrand W_T' W_S z t)
            Sanctions.I b' →
          b ≤ b') := by
  intro h
  have hord : ∀ y, V_T y
      ≤ (V_T + Sanctions.highStateRamp c (p.jointSucc V_S x 1).val) y := by
    intro y
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    linarith [Sanctions.highStateRamp_nonneg hc (p.jointSucc V_S x 1).val y]
  have h0max := p.leaderArgmax_highStateRamp_isMaxOn_zero V_T V_S x hβ hκ hc
    hplac hvar' hgain
  have hcon := h V_T _ V_S hord x hx a 0 ha ⟨le_refl 0, zero_le_one⟩
    hmax h0max
  linarith

end Params
end AbstractGame

end -- noncomputable section

#print axioms Sanctions.AbstractGame.Params.leaderArgmax_lowStateRamp_isMaxOn_one
#print axioms Sanctions.AbstractGame.Params.leaderArgmax_highStateRamp_isMaxOn_zero
#print axioms Sanctions.AbstractGame.Params.leaderArgmax_not_antitone_pointwise
#print axioms Sanctions.AbstractGame.Params.leaderArgmax_not_monotone_pointwise

end Sanctions
