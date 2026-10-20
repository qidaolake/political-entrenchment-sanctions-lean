/-
Sanctions/Foundations/SlopeOrder.lean

**The slope order on value functions, and the comparative static it carries.**

## Why this order and not the pointwise one

The project owns two refutations of the *pointwise* order route:
`Theory/Equilibrium/LeaderArgmaxOrderRefutation.leaderArgmax_not_antitone_pointwise`
and its monotone twin, which together show the leader's joint-Bellman argmax
moves in **neither** direction when the Target continuation is raised pointwise,
at every economy where the leader's action moves the successor state.

Neither touches this order. The reason is structural and worth stating plainly.
With a deterministic transition the continuation enters the leader's objective as
`V(y(a))` — a *value of `V` at a moving point* — so its dependence on `a` is
governed by the **slope** of `V`, on which the pointwise order imposes nothing at
all. A nonnegative pointwise increment may fall steeply (the `lowStateRamp` of
the refutation does exactly that), and that is what lets the argmax jump either
way. Ordering value functions by their *increments* instead removes precisely
that freedom.

This is Curtat's (1996) own choice: his Theorem 4.1 states increasing differences
in the action and `d v` — the derivative — never in `v` itself.

## What it buys, and what it does not

**Buys:** a genuine monotone comparative static (`isMaxOn_sup_of_increasingDiff`),
by Topkis, with no concavity, no uniqueness, no smoothness and no contraction.

**Does not buy: existence.** `SlopeLE` is a **preorder and not a partial order**
— `slopeLE_antisymm_sub_const` below shows two functions comparable both ways
differ by a constant. Nothing in this file constructs an equilibrium, and
Curtat uses the slope order for comparative statics and **Schauder**, not
Tarski, for existence. Anyone reaching for this file to get an equilibrium
should read that sentence twice.

**Correction (2026-08-31): failure of antisymmetry does not close the Tarski
route.** An earlier version of this header inferred from "preorder, not partial
order" that "there is no complete lattice here and Knaster–Tarski does not
apply." That inference is invalid. Mathlib at this project's pinned revision
carries `Mathlib/Order/Antisymmetrization.lean`, which quotients *any* preorder
by mutual comparability and equips the quotient with a `PartialOrder`; here that
quotient identifies value functions differing by an additive constant, which is
exactly what `slopeLE_antisymm_sub_const` describes. So antisymmetry is not the
obstruction.

What is actually open — and unproved either way — is a conjunction of four
things, none of which antisymmetrization supplies:

1. that some useful normalized or quotient slope carrier is a **complete
   lattice**;
2. that the coupled Bellman operator is **well-defined** on additive-constant
   classes;
3. that it is **monotone** for `SlopeLE`; and
4. that the carrier is **invariant** under it.

Until those are settled the slope-order Tarski route is *open*, not *closed* and
not *available*. Do not cite this file for either verdict.

## Rule 19

External theory: an order on real-valued functions and a Topkis-style argmax
comparison. No `Params`, no sanctions. The wiring to the leader's objective is
in `Theory/`.
-/

import Mathlib.Tactic

namespace Sanctions.SlopeOrder

open Set

variable {gamma : Type*}

/-! ## 1. The order -/

/-- **The slope order.** `SlopeLE V W` when `W - V` is nondecreasing — that is,
`W` grows at least as fast as `V` everywhere, regardless of their levels.

Economically, for two candidate Target value functions: `W` rewards political
entrenchment at least as strongly as `V` does, at every state. It says nothing
about which is larger. -/
def SlopeLE [Preorder gamma] (V W : gamma → ℝ) : Prop :=
  Monotone (fun y => W y - V y)

@[refl]
theorem slopeLE_refl [Preorder gamma] (V : gamma → ℝ) : SlopeLE V V := by
  simpa [SlopeLE] using (monotone_const : Monotone (fun _ : gamma => (0 : ℝ)))

theorem slopeLE_trans [Preorder gamma] {U V W : gamma → ℝ}
    (h₁ : SlopeLE U V) (h₂ : SlopeLE V W) : SlopeLE U W := by
  have : Monotone (fun y => (W y - V y) + (V y - U y)) := h₂.add h₁
  simpa [SlopeLE, sub_add_sub_cancel] using this

/-- **It is a preorder, not a partial order.** Two functions comparable in both
directions differ by a constant on any two comparable points — so the order
cannot separate levels, and the quotient it induces is by additive constants.

Note this is a statement about the *raw* function order only. It does not
close an order-theoretic fixed-point route: the induced quotient by additive
constants is a partial order (Mathlib's `Antisymmetrization`). See the
correction in this file's header for what remains genuinely open. -/
theorem slopeLE_antisymm_sub_const [Preorder gamma] {V W : gamma → ℝ}
    (h₁ : SlopeLE V W) (h₂ : SlopeLE W V) {y₁ y₂ : gamma} (hy : y₁ ≤ y₂) :
    W y₁ - V y₁ = W y₂ - V y₂ := by
  have hle : W y₁ - V y₁ ≤ W y₂ - V y₂ := h₁ hy
  have hge : V y₁ - W y₁ ≤ V y₂ - W y₂ := h₂ hy
  linarith

/-! ## 2. Increasing differences of the composed objective

The leader's objective is a stage payoff plus a discounted continuation
evaluated at the successor state that the action induces. Under the slope order
the continuation's contribution is monotone in the action, in whichever
direction the successor map runs. -/

/-- **Composition with a monotone successor map.**

If raising the action raises the successor state, and `W` outgrows `V` in slope,
then the leader's objective built on `W` has **increasing differences** in the
action relative to the one built on `V`.

Here `u` is the stage payoff, `beta >= 0` the discount factor, and `y` the
successor-state map. Nothing is assumed about `u` — it cancels — and nothing
about concavity, continuity, or uniqueness. -/
theorem increasingDiff_of_slopeLE_of_monotone
    {A : Type*} [Preorder A] [Preorder gamma]
    {V W : gamma → ℝ} (hVW : SlopeLE V W)
    {y : A → gamma} (hy : Monotone y)
    (u : A → ℝ) {beta : ℝ} (hbeta : 0 ≤ beta)
    {a a' : A} (haa : a ≤ a') :
    (u a' + beta * V (y a')) - (u a + beta * V (y a))
      ≤ (u a' + beta * W (y a')) - (u a + beta * W (y a)) := by
  have hmono : W (y a) - V (y a) ≤ W (y a') - V (y a') := hVW (hy haa)
  nlinarith [mul_le_mul_of_nonneg_left hmono hbeta]

/-- **Composition with an antitone successor map.**

The project's placation channel runs the other way: *more compliance buys a
lower* successor state, so `y` is antitone in compliance. Then the comparison
reverses — the `V`-objective has the increasing differences — which is the same
statement read in defiance `d = 1 - a`. -/
theorem increasingDiff_of_slopeLE_of_antitone
    {A : Type*} [Preorder A] [Preorder gamma]
    {V W : gamma → ℝ} (hVW : SlopeLE V W)
    {y : A → gamma} (hy : Antitone y)
    (u : A → ℝ) {beta : ℝ} (hbeta : 0 ≤ beta)
    {a a' : A} (haa : a ≤ a') :
    (u a' + beta * W (y a')) - (u a + beta * W (y a))
      ≤ (u a' + beta * V (y a')) - (u a + beta * V (y a)) := by
  have hmono : W (y a') - V (y a') ≤ W (y a) - V (y a) := hVW (hy haa)
  nlinarith [mul_le_mul_of_nonneg_left hmono hbeta]

/-! ## 3. The comparative static

Topkis's two-point argument, stated for a bare pair of objectives with
increasing differences. Nothing here knows about value functions, so it applies
to either orientation above. -/

/-- **Topkis, two points.** If `g` has increasing differences over `f`, and `a`
maximizes `f` while `a'` maximizes `g` on the same set, then the **larger** of
the two maximizes `g`.

No concavity, no uniqueness, no topology — only the order and the increment
comparison. -/
theorem isMaxOn_sup_of_increasingDiff
    {A : Set ℝ} {f g : ℝ → ℝ}
    (hID : ∀ b b' : ℝ, b ≤ b' → g b' - g b ≥ f b' - f b)
    {a a' : ℝ} (ha' : a' ∈ A)
    (hfa : IsMaxOn f A a) (hga' : IsMaxOn g A a') :
    IsMaxOn g A (max a a') := by
  rcases le_total a a' with h | h
  · simpa [max_eq_right h] using hga'
  · -- `a' ≤ a`; show `a` is also a `g`-maximizer.
    have hfge : f a' ≤ f a := (isMaxOn_iff.mp hfa) a' ha'
    have hID' := hID a' a h
    have hgge : g a' ≤ g a := by linarith
    rw [max_eq_left h]
    refine isMaxOn_iff.mpr ?_
    intro b hb
    exact le_trans ((isMaxOn_iff.mp hga') b hb) hgge

/-- **The dual half.** The **smaller** of the two maximizes `f`. Together with
`isMaxOn_sup_of_increasingDiff` this is the statement that the argmax
correspondence rises in the strong set order. -/
theorem isMaxOn_inf_of_increasingDiff
    {A : Set ℝ} {f g : ℝ → ℝ}
    (hID : ∀ b b' : ℝ, b ≤ b' → g b' - g b ≥ f b' - f b)
    {a a' : ℝ} (ha : a ∈ A)
    (hfa : IsMaxOn f A a) (hga' : IsMaxOn g A a') :
    IsMaxOn f A (min a a') := by
  rcases le_total a a' with h | h
  · simpa [min_eq_left h] using hfa
  · -- `a' ≤ a`; show `a'` is also an `f`-maximizer.
    have hgge : g a ≤ g a' := (isMaxOn_iff.mp hga') a ha
    have hID' := hID a' a h
    have hfge : f a ≤ f a' := by linarith
    rw [min_eq_right h]
    refine isMaxOn_iff.mpr ?_
    intro b hb
    exact le_trans ((isMaxOn_iff.mp hfa) b hb) hfge

end Sanctions.SlopeOrder
