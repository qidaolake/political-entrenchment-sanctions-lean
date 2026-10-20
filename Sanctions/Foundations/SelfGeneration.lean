/-
Sanctions/Foundations/SelfGeneration.lean

**Abreu–Pearce–Stacchetti self-generation: Tarski on SETS.**

## Why this route survives what killed the others

The project's standing obstruction to equilibrium existence with a forward-looking
Sender is that there is no single operator to contract, and that the joint value
operator is not isotone. Both halves are now proved, not conjectured:

* not a contraction — `Examples/JointIterationCycleWitness.jointIteration_two_cycle`
  exhibits an exact rational period-2 orbit of the joint Bellman iteration;
* not isotone — `Theory/Equilibrium/LeaderArgmaxOrderRefutation` shows the leader's
  argmax moves in **neither** direction when the Target continuation rises
  pointwise, at every economy where the leader's action moves the successor state.

Every one of those results is about an operator on **value functions**, ordered
pointwise. Abreu–Pearce–Stacchetti (1990) work one level up: with a set-valued
operator on *sets of payoffs*, ordered by inclusion. Monotonicity in that order
is not a hypothesis to be checked against the economics — for an operator built
from a support relation it is **free** (`genOp_monotone` below: enlarging the
pool of available continuations cannot destroy a plan that was already feasible).
`Set W` is a complete lattice for any `W` whatever, so Knaster–Tarski applies with
no contraction, no topology, no concavity, no uniqueness, and no continuity.

That is the whole point of the route, and it is why none of the refutations above
touch it.

## What this file does and does not deliver

**Delivers**, from primitives, and constructively in the Tarski sense:
* the largest self-generating set (`largestSelfGenerating`), which exists for
  every monotone `B`;
* the APS characterization — a payoff is in it **iff** it lies in *some*
  self-generating set (`mem_largest_iff_exists_selfGenerating`);
* a **sound outer approximation** `gfp B ⊆ B^[n] univ` for every `n`, and hence
  a *nonexistence* instrument (`largest_eq_empty_of_iterate_empty`): if any
  finite iterate from the top is empty, the greatest fixed point is empty — a
  proof, not a failed search. Cf. Judd–Yeltekin–Conklin (2003) on inner/outer
  approximation.

  **Corrected 2026-08-31.** This was written as "the project's *first* genuine
  nonexistence instrument." It is not first, and the superlative was false when
  written: `Theory/Equilibrium/AbsorbingTopObstruction.lean` already carried
  `no_equilibrium_of_slope_and_top_gain`, which derives a contradiction from a
  supplied `FeedbackStackelbergEquilibriumTop` under a Sender top-slope
  condition. Note also what this operator is and is not tied to: nothing below
  connects `gfp B` to the sanctions game's equilibrium payoff set, so the
  "equilibrium payoff set is empty" reading is not yet available here (Rule 15).

**Does not deliver**: an equilibrium for the sanctions game. That needs the
support relation of *this* model — which plans generate which payoffs under which
continuations — instantiated at `Params`, and that instantiation is deliberately
not attempted here. Nothing in this file should be cited as existence for the
Sender-forward regimes. Under Rule 15 a construction counts only once its inputs
are the model's own primitives.

## Rule 19

External theory: order-theoretic fixed points on a powerset lattice. No `Params`,
no sanctions, no value functions.
-/

import Mathlib.Order.FixedPoints
import Mathlib.Tactic

namespace Sanctions.SelfGeneration

open Set

variable {W : Type*}

/-! ## 1. Self-generation -/

/-- **A self-generating set.** Every payoff in `S` can be supported using
continuation payoffs drawn from `S` itself — the set vouches for its own members.

This is the APS notion. Note it is an inclusion, not an equality: `S` need not be
everything the operator produces. -/
def SelfGenerating (B : Set W → Set W) (S : Set W) : Prop := S ⊆ B S

/-- **The largest self-generating set**, as the greatest fixed point of `B` on
the powerset lattice. Exists for **every** monotone `B`, by Knaster–Tarski. -/
def largestSelfGenerating (B : Set W →o Set W) : Set W := OrderHom.gfp B

/-- The largest self-generating set is a fixed point: it generates exactly
itself. -/
theorem largest_fixed (B : Set W →o Set W) :
    B (largestSelfGenerating B) = largestSelfGenerating B :=
  OrderHom.map_gfp B

/-- It is itself self-generating. -/
theorem largest_selfGenerating (B : Set W →o Set W) :
    SelfGenerating B (largestSelfGenerating B) :=
  le_of_eq (largest_fixed B).symm

/-- **Self-generation implies supportability** — the APS verification theorem.
Any set that vouches for its own members is contained in the largest one, so
exhibiting *any* self-generating set is enough to certify every payoff in it. -/
theorem selfGenerating_subset_largest (B : Set W →o Set W) {S : Set W}
    (hS : SelfGenerating B S) : S ⊆ largestSelfGenerating B :=
  OrderHom.le_gfp B hS

/-- **The characterization.** A payoff lies in the largest self-generating set
exactly when some self-generating set contains it. -/
theorem mem_largest_iff_exists_selfGenerating (B : Set W →o Set W) (w : W) :
    w ∈ largestSelfGenerating B ↔ ∃ S, SelfGenerating B S ∧ w ∈ S :=
  ⟨fun hw => ⟨largestSelfGenerating B, largest_selfGenerating B, hw⟩,
   fun ⟨_, hS, hw⟩ => selfGenerating_subset_largest B hS hw⟩

/-! ## 2. Monotonicity is free for an operator built from a support relation

This is the structural contrast with the value-function operator. There,
isotonicity is a substantive claim about the economics and is **false** here.
Here it is a two-line consequence of the shape of the definition. -/

/-- **The operator induced by a family of plans.**

`I` indexes plans. A plan `i` generates the payoff `gen i`, and is feasible only
when every continuation value it relies on — the set `uses i` — is available.
`genOp gen uses S` is then the set of payoffs generated by plans whose
continuation requirements all lie in `S`.

In the sanctions game a "plan" would be a current action pair together with the
continuation values promised after each successor state; `uses i` collects those
promised values, and `gen i` is the resulting current-period payoff pair. -/
def genOp {I : Type*} (gen : I → W) (uses : I → Set W) : Set W → Set W :=
  fun S => {w | ∃ i, gen i = w ∧ uses i ⊆ S}

/-- **Monotonicity, for free.** Enlarging the pool of available continuation
payoffs cannot make a previously feasible plan infeasible.

No order on `W` is used — only inclusion on sets. That is precisely why this
route is untouched by the pointwise-order refutations. -/
theorem genOp_monotone {I : Type*} (gen : I → W) (uses : I → Set W) :
    Monotone (genOp gen uses) := by
  intro S S' hSS' w hw
  obtain ⟨i, hgen, huses⟩ := hw
  exact ⟨i, hgen, huses.trans hSS'⟩

/-- The bundled order homomorphism, ready for `largestSelfGenerating`. -/
def genOpHom {I : Type*} (gen : I → W) (uses : I → Set W) : Set W →o Set W :=
  ⟨genOp gen uses, genOp_monotone gen uses⟩

/-! ## 3. Outer approximation, and a sound nonexistence instrument

Iterating from the top is *sound in the exclusion direction*: every iterate
contains the answer. So an empty iterate is a proof that the answer is empty.

This is the direction the project has lacked. `Foundations/ValidatedLocalPerov`
supplies inclusion certificates — evidence that a fixed point *is* somewhere.
Nothing until now supplied exclusion, and without it a failed search could never
be upgraded into a theorem (Rule 9D, clause 1: non-convergence is never evidence
of nonexistence). This closes that gap for the set-valued route. -/

/-- **Every finite iterate from the top is an outer bound.**

`gfp B ⊆ B^[n] univ` for all `n`, by induction on `n` using only monotonicity of
`B` and the fixed-point identity. -/
theorem largest_subset_iterate (B : Set W →o Set W) (n : ℕ) :
    largestSelfGenerating B ⊆ (⇑B)^[n] univ := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc largestSelfGenerating B
          = B (largestSelfGenerating B) := (largest_fixed B).symm
        _ ⊆ B ((⇑B)^[k] univ) := B.monotone ih

/-- **A sound nonexistence certificate.** If any finite iterate from the top is
empty, the largest self-generating set is empty — so *no* payoff is supportable.

Unlike a failed numerical search, this is a proof, and it is the exclusion dual
of an inclusion certificate.

**Corrected 2026-08-31.** This previously read "the only instrument in the tree
that can turn 'we could not find one' into 'there is none'." That was false:
`Theory/Equilibrium/AbsorbingTopObstruction.lean.no_equilibrium_of_slope_and_top_gain`
predates it and does the same job at the model level, which this theorem — being
about an abstract complete-lattice operator with no bridge to the sanctions
equilibrium concept — does not yet do. -/
theorem largest_eq_empty_of_iterate_empty (B : Set W →o Set W) {n : ℕ}
    (h : (⇑B)^[n] univ = ∅) : largestSelfGenerating B = ∅ :=
  eq_empty_of_subset_empty (h ▸ largest_subset_iterate B n)

/-- **Monotone decrease of the outer approximations.** Successive iterates from
the top shrink, so the bounds improve monotonically and a computation may stop as
soon as an iterate is empty. -/
theorem iterate_antitone_of_le_univ (B : Set W →o Set W) (n : ℕ) :
    (⇑B)^[n + 1] univ ⊆ (⇑B)^[n] univ := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : (⇑B)^[k + 1 + 1] univ = B ((⇑B)^[k + 1] univ) :=
        Function.iterate_succ_apply' _ _ _
      have h2 : (⇑B)^[k + 1] univ = B ((⇑B)^[k] univ) :=
        Function.iterate_succ_apply' _ _ _
      rw [h1]
      calc B ((⇑B)^[k + 1] univ) ⊆ B ((⇑B)^[k] univ) := B.monotone ih
        _ = (⇑B)^[k + 1] univ := h2.symm

end Sanctions.SelfGeneration
