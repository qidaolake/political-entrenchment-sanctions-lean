/-
Sanctions/Theory/LockIn/DynamicStake.lean

**DYNAMIC-STAKE — a dynamic sanction floor requires a Sender stake in the
Target's entrenchment, read along the Target's policy.**

## What is actually proved

One implication, in two equivalent directions:

* `no_dynamic_floor_of_antitone_state_chord` — if the Sender's stage payoff,
  read **along the Target's policy**, is non-increasing in the Target's
  political state, then at every state the greatest forward-looking Sender
  maximiser is at most the greatest **stage** maximiser. The continuation
  channel buys nothing.
* `dynamic_stake` — its exact contrapositive, hence nothing weaker (proved by
  `by_contra` and `push_neg`, not by a `not_imp_not` rewrite):
  if at some state the greatest forward-looking maximiser strictly exceeds the
  greatest stage maximiser, then there exist feasible states `y₁ ≤ y₂` and a
  feasible sanction `s` with `U_S(y₁, α y₁, s) < U_S(y₂, α y₂, s)`.

No numerical constant occurs in either statement; both are universal in the
economy `p`, in the Target policy `α`, and in the state `x`, with the only
existential quantifier in `dynamic_stake`'s conclusion.

## Six scope limits. None of them is optional reading.

**(1) The rise is along the COMPOSED map, not the raw partial.** The conclusion
is about `y ↦ U_S(y, α y, s)` — the Sender's stage payoff *after* substituting
the compliance the Target actually plays at each state. It is **not** about
`∂U_S/∂x` at fixed compliance. `raw_chord_ne_composed_chord` (below) proves
these are different objects: `U(x,a,s) = a − x` with `α y = 2y` is
non-increasing in the state at every fixed compliance and strictly increasing
along the policy.

*Consequence — the live open refutation route.* An economy whose Sender
dislikes entrenchment **per se** (`∂U_S/∂x < 0` everywhere), but where more
entrenched states buy enough extra compliance that the composed map rises, is
**not excluded by anything in this file**. Such an economy could carry a
genuine dynamic floor while the paper's informal reading ("the Sender profits
from the Target's defiance") is false of it. Constructing one, or proving none
exists, is open.

**(2) The conclusion is EXISTENTIAL, not a uniform chord.** What is delivered
is "there exist `y₁ ≤ y₂` and a feasible `s` at which the composed payoff
rises". It is **not** a uniform positive lower chord `m > 0`, and therefore not
the kind of hypothesis `V_S_free_sanction_floor`'s `h_state_slope` consumes.
`existential_rise_does_not_give_uniform_chord` separates the two: a payoff can
be flat on part of the state space and rise on the rest.

**(3) The conclusion is `x`-FREE.** The hypothesis is a dynamic floor at a
*single* state `x`; the conclusion quantifies over all of `Sanctions.S` with no
link back to `x` (`dynamic_stake_conclusion_is_x_free` records this by
discharging `x` existentially with no loss). A floor at `x = 0` licenses only
"the composed payoff rises **somewhere** in `[0,1]`", possibly nowhere near `0`
— and possibly at states where the payoff is locally *falling*. This is not
hypothetical: at `ceParams` a floor holds at **every** feasible state, yet the
composed payoff strictly falls between `3/4` and `1`
(`Examples.ce_composed_chord_negative_somewhere`). So do **not** read this
result as "the Sender has a positive stake in the basin", or at the floor
state, or anywhere in particular.

**(4) This is NOT the converse of `V_S_free_sanction_floor`.** That theorem
consumes a *lower* chord (`m·(y₂−y₁) ≤ U_S y₂ … − U_S y₁ …`, with `m > 0`);
`chord_pos_of_equilibrium_dynamic_floor` concludes about an *upper* chord
(`U_S y₂ … − U_S y₁ … ≤ cS·(y₂−y₁)`, forcing `cS > 0`). Lower bound and upper
bound are different objects, so the two results are **not** a
necessary-and-sufficient pair and must never be cited as one.

**(5) The bare `dynamic_stake` says nothing about Target optimality.** Its only
hypothesis on `α` is `Continuous α`: no `α_mem` (feasibility of the compliance
level), and no Target best-response condition. It is a lemma about the Sender's
problem at an arbitrary continuous policy. The Rule-1-clean instance — the one
that may be read as a statement about equilibrium behaviour — is
`dynamic_stake_equilibrium`, which takes a constructed
`FeedbackStackelbergEquilibriumTop` and uses Banach uniqueness to identify its
Sender value with the constructed fixed point.

**(6) The BASIN-LOCAL version is OPEN.** `dynamic_stake` is global: the antitone
hypothesis it contraposes is required on all of `Sanctions.S`. Whether a
*basin-local* version holds — a floor at `x` in a high basin `[x̄, 1]` forcing a
composed rise inside that basin — is **not settled here**, in either direction.
The route in this file does not localise, because
`realizedRule_le_stageTopRule_of_successor_antitone` needs the continuation
value to be non-increasing along the successor range at `x`, and the successor
range at a basin point need not stay inside the basin. No obstruction theorem
and no counterexample is offered; the case is simply open.

## Rule compliance

* **Rule 1** — every strategic object is an optimisation result. `stageTopRule`
  is the supremum of the Sender's *stage argmax set*; `dynamicTopRealizedRule`
  is the supremum of its forward-looking argmax set. The ceiling proof
  contradicts the *optimality* of the forward-looking maximiser; no action is
  posited.
* **Rule 3** — no new assumption. Every hypothesis is theorem-bound and written
  directly over existing primitives (`U_S`, `F`, `β_S`, `σ`) and an existing
  policy `α`. No `Params` field, no structure field, no new `Prop` on any
  assumption side.
* **Rule 5** — every statement is parametric in `p : AbstractGame.Params`, and
  the witness instances live in `Sanctions/Examples/`.  Several of those are
  short computations rather than literal one-liners (`jp_stageTopRule_eq_one`,
  `ce_upper_chord`, `lb_state_chord_nonpos`): the parametric theorem supplies the
  argument, but discharging its hypotheses at a named economy still takes work.
* **Rule 15** — the Sender value is `p.V_S α hα`, the Banach fixed point
  constructed in `Theory/Bellman/BellmanS.lean`, never a hypothesised value
  function.
* **Rule 19** — with one acknowledged deviation.  The two counterexample
  separators at the end (`raw_chord_ne_composed_chord`,
  `existential_rise_does_not_give_uniform_chord`) mention no `Params` and are
  pure statements about real-valued functions, so by the letter of the rule they
  belong in `Foundations/`.  They are kept here because they exist only to fence
  the claim above and would be misleading as free-standing library lemmas.  This
  is a deviation, not compliance; if either is ever reused, move it.

## Two `Params` transition fields are load-bearing

Both directions of the transition monotonicity are used, and the English of the
result must name both:

* `F_mono_x` — a higher political state today gives a weakly higher political
  state tomorrow, at every sanction. Used inside
  `V_S_antitone_of_integrand_antitone` (via `bellmanS_BCF_preserves_antitone`)
  to carry non-increasingness through the Bellman iteration.
* `F_mono_s` — a higher sanction gives a weakly higher political state
  tomorrow, at every state. Used in `realizedRule_le_stageTopRule_of_antitone`
  to push the global order fact onto the successor range at `x`. Without it the
  global route does not run: `realizedRule_le_stageTopRule_of_successor_antitone`
  would have to be fed directly.
-/

import Sanctions.Theory.LockIn.PersistenceMargin

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The greatest STAGE maximiser -/

/-- The Sender's **stage** argmax set at `(x, α x)`: the maximisers of the
one-period payoff `U_S(x, α x, ·)` over the feasible sanction interval `[0,1]`,
with every continuation ignored. -/
def stageArgmaxSet (α : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {s | s ∈ Sanctions.I ∧ IsMaxOn (fun s' => p.U_S x (α x) s') Sanctions.I s}

theorem stageArgmaxSet_bddAbove (α : ℝ → ℝ) (x : ℝ) :
    BddAbove (p.stageArgmaxSet α x) := ⟨1, fun _ hs => hs.1.2⟩

/-- Non-empty by Weierstrass: the stage payoff is continuous in the sanction
(`U_S_continuous`) and `[0,1]` is compact. The proof takes the maximiser from
`dynamicArgmaxSet_nonempty` at the zero continuation value, where
`dynamicArgmaxSet_zero` identifies the dynamic argmax with the stage argmax.
General in `F`. Since BG1.10 (2026-10-06) the `Params` selector `σ`
(`σ`, `σ_mem`, `σ_isMaxOn_U_S`), which this proof used to read only to exhibit
some maximiser, is no longer used; the statement is unchanged. -/
theorem stageArgmaxSet_nonempty (α : ℝ → ℝ) (x : ℝ) :
    (p.stageArgmaxSet α x).Nonempty := by
  have h := p.dynamicArgmaxSet_nonempty 0 x (α x)
  rwa [p.dynamicArgmaxSet_zero] at h

/-- The **greatest stage maximiser** — the myopic counterpart of
`dynamicTopRealizedRule`. Rule 1: an argmax object, not a posited level. -/
def stageTopRule (α : ℝ → ℝ) : ℝ → ℝ :=
  fun x => sSup (p.stageArgmaxSet α x)

/-- **`stageTopRule` is the tree's own stage line, not a new one (i).** It is
literally the sanction the Sender would choose with the continuation channel
switched off, `V := 0`. -/
theorem stageTopRule_eq_zeroValue_rule (α : ℝ → ℝ) (x : ℝ) :
    p.stageTopRule α x = p.dynamicTopRealizedRule 0 α x := by
  unfold stageTopRule stageArgmaxSet dynamicTopRealizedRule σ_dyn_top
  rw [p.dynamicArgmaxSet_zero]

/-- **`stageTopRule` is the tree's own stage line, not a new one (ii).** It is
the right-hand side of `uniform_floor_iff_stage_floor` — the barrier theorem
saying that a floor demanded uniformly over the monotone carrier is exactly a
myopic floor. -/
theorem stageTopRule_eq_tree_line (α : ℝ → ℝ) (x c : ℝ) :
    (∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, Monotone V →
        c ≤ p.dynamicTopRealizedRule V α x)
      ↔ c ≤ p.stageTopRule α x :=
  p.uniform_floor_iff_stage_floor α x c

/-- **The greatest myopic best response lies weakly below the greatest
forward-looking one**, under a monotone Sender value: for every Target policy
`α` and state `x`, `stageTopRule α x ≤ dynamicTopRealizedRule V_S α x`.
Economically: a Sender that values the Target's future entrenchment
(monotone `V_S`) never sanctions below the harshest sanction it would choose
myopically against the same compliance. No reference to the `Params` selector
`σ`: this is the selection-free form of the dominance comparison
`σ_dyn_top_ge_sigma`, and the pointwise companion of
`stage_max_le_σ_dyn_top` at the greatest stage maximiser.

Rule 22: general in `F` (only `F_mono_s`, through `σ_dyn_top`'s comparison).
No hypothesis is added: it is the `←` direction of `stageTopRule_eq_tree_line`
at `c := stageTopRule α x` (BH6.8, 2026-10-07). -/
theorem stageTopRule_le_dynamicTopRealizedRule
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (hV : Monotone V_S) (α : ℝ → ℝ) (x : ℝ) :
    p.stageTopRule α x ≤ p.dynamicTopRealizedRule V_S α x :=
  (p.stageTopRule_eq_tree_line α x _).mpr le_rfl V_S hV

/-- **At `β_S = 0` the forward-looking top rule is the stage top rule**, for
every continuation value `V_S` and with no uniqueness hypothesis:
`dynamicTopRealizedRule V_S α x = stageTopRule α x`. Economically: a Sender
that puts zero weight on the future plays its harshest myopic best response,
whatever value it attaches to future states.

Rule 22: general in `F`. The rule form of
`σ_dyn_top_eq_sSup_stageArgmax_of_βS_zero` (`SigmaDynComparison.lean`) at
`a := α x`; no hypothesis is added (BH6.8, 2026-10-07). -/
theorem dynamicTopRealizedRule_eq_stageTopRule_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) :
    p.dynamicTopRealizedRule V_S α x = p.stageTopRule α x :=
  p.σ_dyn_top_eq_sSup_stageArgmax_of_βS_zero hβ V_S x (α x)

/-! ## 2. The ceiling: a non-increasing continuation cannot buy a floor -/

/-- **The minimal form, and the honest one.** Only *local* information about the
continuation value is consumed: that `V` is non-increasing along the **successor
range at `x`**, `{clipS' (F x s) : s ∈ [0,1]}`. Nothing global about `V`, and
nothing at all about `α` beyond the point value `α x`.

Isolating this makes the remaining gap auditable: the global chord hypothesis is
consumed **only** to obtain this from primitives, which is exactly why the
basin-local version does not follow (scope limit 6 in the file header) — the
successor range at a basin point need not stay inside the basin.

Rule 1: `dynamicTopRealizedRule V α x` is the greatest element of the Sender's
forward-looking argmax set and `m` is a stage argmax; the proof contradicts the
*optimality* of the former, never a posited level.

General in `F`. Since BG1.10 (2026-10-06) the stage maximiser `m` comes from
`stageArgmaxSet_nonempty` (Weierstrass) rather than from the `Params` selector
`σ`, which was read only to show that a maximiser exists. Statement
unchanged. -/
theorem realizedRule_le_stageTopRule_of_successor_antitone
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ)
    (hV : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      V (Sanctions.clipS' (p.F x s₂)) ≤ V (Sanctions.clipS' (p.F x s₁))) :
    p.dynamicTopRealizedRule V α x ≤ p.stageTopRule α x := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hbdd := p.stageArgmaxSet_bddAbove α x
  -- any stage maximiser will do; Weierstrass supplies one
  obtain ⟨m, hm_mem⟩ := p.stageArgmaxSet_nonempty α x
  set r : ℝ := p.dynamicTopRealizedRule V α x with hr
  have hrI : r ∈ Sanctions.I := p.dynamicTopRealizedRule_mem V α x
  have hrmem : r ∈ p.dynamicArgmaxSet V x (α x) :=
    p.σ_dyn_top_mem_dynamicArgmaxSet V x (α x)
  -- `r` strictly exceeds the stage ceiling, so `r` is not a stage maximiser
  have hrnot : ¬ IsMaxOn (fun s' => p.U_S x (α x) s') Sanctions.I r := fun h =>
    absurd (le_csSup hbdd ⟨hrI, h⟩) (not_le.mpr hcon)
  -- hence the stage optimum `m` strictly beats `r` at the stage
  have hstageStrict : p.U_S x (α x) r < p.U_S x (α x) m := by
    by_contra hle
    rw [not_lt] at hle
    exact hrnot fun s' hs' => le_trans (hm_mem.2 hs') hle
  -- and `m` lies weakly below `r`, so the continuation weakly prefers it
  have hmle : m ≤ r := le_trans (le_csSup hbdd hm_mem) hcon.le
  have hVle := hV _ hm_mem.1 r hrI hmle
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hβV := mul_le_mul_of_nonneg_left hVle hβ
  -- contradiction with the *optimality* of `r` in the forward-looking problem
  have hdyn : p.U_S x (α x) m + p.β_S * V (Sanctions.clipS' (p.F x m))
      ≤ p.U_S x (α x) r + p.β_S * V (Sanctions.clipS' (p.F x r)) :=
    hrmem.2 hm_mem.1
  linarith

/-- **A non-increasing continuation value cannot buy a sanction above the stage
ceiling.** If the Sender's continuation value is non-increasing in the Target's
political state, then the greatest forward-looking Sender maximiser never
exceeds the greatest stage maximiser.

`F_mono_s` — a higher sanction gives a weakly higher political state tomorrow,
at every state — is load-bearing here: it is what turns the *global* order fact
about `V` into the *successor-range* fact
`realizedRule_le_stageTopRule_of_successor_antitone` needs. -/
theorem realizedRule_le_stageTopRule_of_antitone
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hV : Sanctions.StokeyLucas.AntitoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => V z)) (x : ℝ) :
    p.dynamicTopRealizedRule V α x ≤ p.stageTopRule α x :=
  p.realizedRule_le_stageTopRule_of_successor_antitone V α x
    (fun _ _ _ _ h => hV (Sanctions.clipS'_mono (p.F_mono_s x h)))

/-- The ceiling binds **every** dynamic maximiser, not only the greatest
selector: in particular the project's `Classical.choose`-defined `σ_dyn` sits at
or below the greatest stage maximiser once the continuation value is
non-increasing. -/
theorem dynamicArgmax_le_stageTopRule_of_antitone
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hV : Sanctions.StokeyLucas.AntitoneOnSubtype
      (fun z : ↥(Sanctions.S : Set ℝ) => V z)) {x s : ℝ}
    (hs : s ∈ p.dynamicArgmaxSet V x (α x)) :
    s ≤ p.stageTopRule α x :=
  le_trans (le_csSup (p.dynamicArgmaxSet_bddAbove V x (α x)) hs)
    (p.realizedRule_le_stageTopRule_of_antitone V α hV x)

/-! ## 3. A CORNER stage ceiling excludes the hypothesis, with no chord content

This is a feasibility artefact, recorded here so that no witness row can be
mistaken for a chord discrimination. It uses **only** that the realised rule
lies in `[0,1]`; the antitone machinery of §2 plays no part. -/

/-- **A corner stage ceiling makes the dynamic-floor hypothesis unsatisfiable.**
If the greatest stage maximiser at `x` is already at (or above) the top of the
feasible sanction interval, then no continuation value whatsoever can push the
forward-looking maximiser past it — simply because the forward-looking maximiser
is itself feasible (`dynamicTopRealizedRule_mem`).

Note what this does **not** say: it makes no reference to the Sender's state
chord, so an economy excluded this way is excluded as a *corner artefact*, not
because its Sender has zero stake in the Target's entrenchment. -/
theorem realizedRule_le_stageTopRule_of_corner
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ)
    (hcorner : (1 : ℝ) ≤ p.stageTopRule α x) :
    p.dynamicTopRealizedRule V α x ≤ p.stageTopRule α x :=
  le_trans (p.dynamicTopRealizedRule_mem V α x).2 hcorner

/-- Contrapositive packaging of `realizedRule_le_stageTopRule_of_corner`: at a
corner stage ceiling, `dynamic_stake`'s hypothesis is false for **every**
continuation value and every Target policy. -/
theorem corner_stage_ceiling_excludes_dynamic_floor
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ)
    (hcorner : (1 : ℝ) ≤ p.stageTopRule α x) :
    ¬ (p.stageTopRule α x < p.dynamicTopRealizedRule V α x) :=
  not_lt.mpr (p.realizedRule_le_stageTopRule_of_corner V α x hcorner)

/-! ## 4. DYNAMIC-STAKE — the contrapositive (economically readable) form -/

/-- **No dynamic floor without a Sender state stake.** If the Sender's stage
payoff, read along the Target's policy, is non-increasing in the Target's
political state, then at **every** state the greatest forward-looking sanction
is at most the greatest **stage** maximiser: the continuation channel buys
nothing, anywhere.

This is DYNAMIC-STAKE in contrapositive form, and it is the economically
readable one: *a Sender that gains nothing (along the policy) from the Target's
entrenchment sanctions myopically.*

Both transition-monotonicity fields are consumed: `F_mono_x` (a higher state
today gives a weakly higher state tomorrow, at every sanction) inside the
Bellman preservation step, and `F_mono_s` (a higher sanction gives a weakly
higher state tomorrow, at every state) in the ceiling step.

Rule 15: the value function is the constructed Banach fixed point `p.V_S α hα`.
Rule 3: `h_U_S_anti` is theorem-bound and written directly over the existing
`U_S` and the existing policy `α` — the order-dual of the shape
`V_S_free_sanction_floor`'s `h_state_slope` already takes, with the inequality
direction reversed and the constant `m` removed. No `Params` field, no
structure field, no new `Prop` on the assumption side. -/
theorem no_dynamic_floor_of_antitone_state_chord
    {α : ℝ → ℝ} (hα : Continuous α)
    (h_U_S_anti : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S y (α y) s ≤ p.U_S x (α x) s) (x : ℝ) :
    p.dynamicTopRealizedRule (p.V_S α hα) α x ≤ p.stageTopRule α x :=
  p.realizedRule_le_stageTopRule_of_antitone (p.V_S α hα) α
    (p.V_S_antitone_of_integrand_antitone hα h_U_S_anti) x

/-! ## 5. DYNAMIC-STAKE — the forward form -/

/-- **DYNAMIC-STAKE.** If at some state the greatest maximiser of the Sender's
forward-looking objective against the *constructed* Bellman fixed point strictly
exceeds the greatest maximiser of its *stage* payoff, then the Sender's stage
payoff, read **along the Target's policy**, must strictly **rise** in the
Target's political state somewhere: there are feasible states `y₁ ≤ y₂` and a
feasible sanction `s` with `U_S(y₁, α y₁, s) < U_S(y₂, α y₂, s)`.

This is the exact `not_imp_not` of `no_dynamic_floor_of_antitone_state_chord`,
so it ships nothing weaker than it consumes. No numerical constant occurs in the
statement.

**Read this statement only as far as it goes.** Four limits, each with a
theorem attached; the file header states them in full.

* *Composed, not raw.* The rise is along `y ↦ U_S(y, α y, s)`, never
  `∂U_S/∂x` at fixed compliance (`raw_chord_ne_composed_chord`). An economy
  whose Sender dislikes entrenchment per se, but where entrenched states buy
  more compliance, is **not** excluded by this theorem — that is the live open
  refutation route.
* *Existential, not uniform.* "Rises somewhere", not a uniform positive lower
  chord `m > 0` (`existential_rise_does_not_give_uniform_chord`).
* *`x`-free.* The floor is at one state; the conclusion names no state at all
  (`dynamic_stake_conclusion_is_x_free`). This is not a statement that the
  Sender has a stake near `x`, or in any basin.
* *Not about Target optimality.* The only hypothesis on `α` here is
  `Continuous α` — no feasibility of the compliance level, no best-response
  condition. As a statement about equilibrium behaviour, cite
  `dynamic_stake_equilibrium` instead.

Both transition-monotonicity fields of `Params` are load-bearing: `F_mono_x`
(a higher political state today gives a weakly higher political state tomorrow,
at every sanction) inside the Bellman preservation step, and `F_mono_s`
(a higher sanction gives a weakly higher political state tomorrow, at every
state) in the ceiling step.

Rule 15: `p.V_S α hα` is the Banach fixed point of `bellmanS_BCF`
(`Theory/Bellman/BellmanS.lean`), not a hypothesised value function. -/
theorem dynamic_stake
    {α : ℝ → ℝ} (hα : Continuous α) (x : ℝ)
    (hdyn : p.stageTopRule α x < p.dynamicTopRealizedRule (p.V_S α hα) α x) :
    ∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
      y₁ ≤ y₂ ∧ p.U_S y₁ (α y₁) s < p.U_S y₂ (α y₂) s := by
  by_contra hcon
  push Not at hcon
  exact absurd (p.no_dynamic_floor_of_antitone_state_chord hα
    (fun s hs y₁ hy₁ y₂ hy₂ hle => hcon s hs y₁ hy₁ y₂ hy₂ hle) x) (not_le.mpr hdyn)

/-- **DYNAMIC-STAKE at a constructed feedback Stackelberg equilibrium — the
Rule-1-clean instance.** Same conclusion with the equilibrium's *own* Sender
value in place of the constructed one: Banach uniqueness
(`equilibrium_V_S_eq_constructed`) identifies the two, so no side hypothesis is
needed.

This, and not the bare `dynamic_stake`, is the form that may be read as a
statement about equilibrium play: `E` carries the Target's optimality and
feasibility fields, whereas `dynamic_stake` imposes only continuity on `α`.

The scope limits of `dynamic_stake` carry over verbatim: composed map, not the
raw partial; existential rise, not a uniform chord; and no localisation of the
rise to the state carrying the floor. -/
theorem dynamic_stake_equilibrium
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ)
    (hdyn : p.stageTopRule E.α x < p.dynamicTopRealizedRule E.V_S E.α x) :
    ∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
      y₁ ≤ y₂ ∧ p.U_S y₁ (E.α y₁) s < p.U_S y₂ (E.α y₂) s := by
  refine p.dynamic_stake E.hα x ?_
  rwa [← p.equilibrium_V_S_eq_constructed E]

/-- **Floor form.** Any floor `c` on the forward-looking sanction that strictly
exceeds the greatest stage maximiser — i.e. a floor genuinely *bought by the
continuation channel* rather than already implied by the stage payoff — forces
the same conclusion. -/
theorem dynamic_stake_of_floor
    {α : ℝ → ℝ} (hα : Continuous α) {x c : ℝ}
    (hstage : p.stageTopRule α x < c)
    (hfloor : c ≤ p.dynamicTopRealizedRule (p.V_S α hα) α x) :
    ∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
      y₁ ≤ y₂ ∧ p.U_S y₁ (α y₁) s < p.U_S y₂ (α y₂) s :=
  p.dynamic_stake hα x (lt_of_lt_of_le hstage hfloor)

/-- **SCOPE — the conclusion is `x`-free, stated as a theorem so it cannot be
lost from a docstring.** The state carrying the dynamic floor can be discharged
existentially with **no loss whatsoever**: `dynamic_stake` maps a floor at any
one state to a conclusion that mentions no state.

So a floor at `x = 0` licenses exactly "the composed payoff rises **somewhere**
in `[0,1]`" — nothing about the neighbourhood of `0`, nothing about any basin,
and in particular nothing that rules out the payoff *falling* at `0` itself.
Do not gloss the result as "the Sender has a positive stake in the basin".

The in-tree instance is `Examples.ce_composed_chord_negative_somewhere`, and it
should be cited for what it actually shows: at `ceParams` a dynamic floor holds
at *every* feasible state, while the composed payoff strictly **falls** between
`3/4` and `1`.  So the rise the conclusion asserts genuinely need not occur where
the floor does.  (An earlier draft of this docstring cited it for a floor at
`x = 0` with the payoff falling at `0`; that is not the configuration that
theorem exhibits.) -/
theorem dynamic_stake_conclusion_is_x_free
    {α : ℝ → ℝ} (hα : Continuous α)
    (hdyn : ∃ x : ℝ, p.stageTopRule α x < p.dynamicTopRealizedRule (p.V_S α hα) α x) :
    ∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
      y₁ ≤ y₂ ∧ p.U_S y₁ (α y₁) s < p.U_S y₂ (α y₂) s := by
  obtain ⟨x, hx⟩ := hdyn
  exact p.dynamic_stake hα x hx

/-! ## 6. The chord-constant form — `c_S > 0` literally

`c_S` here is an **upper** chord constant on the composed state payoff. Read it
as the *least* upper chord and the theorems below are DYNAMIC-STAKE verbatim.
They are **not** the converse of `V_S_free_sanction_floor`, whose `h_state_slope`
is a *lower* chord `m·(y₂−y₁) ≤ U_S y₂ … − U_S y₁ …`; substituting one for the
other is a constant-substitution error, and the pair is not
necessary-and-sufficient. -/

/-- **A non-positive Sender state chord kills every dynamic floor.** If `cS` is
any **upper** chord bound on the Sender's composed stage state payoff and
`cS ≤ 0`, the greatest forward-looking sanction is at most the greatest stage
maximiser at every state. -/
theorem no_dynamic_floor_of_nonpos_chord
    {α : ℝ → ℝ} (hα : Continuous α) {cS : ℝ} (hcS : cS ≤ 0)
    (hchord : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s ≤ cS * (y₂ - y₁)) (x : ℝ) :
    p.dynamicTopRealizedRule (p.V_S α hα) α x ≤ p.stageTopRule α x := by
  refine p.no_dynamic_floor_of_antitone_state_chord hα ?_ x
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have h := hchord s hs y₁ hy₁ y₂ hy₂ hle
  nlinarith [mul_nonneg (neg_nonneg.mpr hcS) (sub_nonneg.mpr hle)]

/-- **`c_S > 0`, for an upper chord.** At an equilibrium carrying a dynamic
floor, *every* admissible **upper** chord constant on the Sender's composed
state payoff is strictly positive.

The reading that makes this DYNAMIC-STAKE verbatim is `cS` = the least upper
chord.  Under a *greatest lower* chord reading the statement is a different one,
and **this file does not prove it false at any economy** —
`existential_rise_does_not_give_uniform_chord` separates the two notions for a
bare `f : ℝ → ℝ` with no economy, no equilibrium and no dynamic floor, so it
cannot settle the economic claim either way.  What is certain is only that the
two readings are different objects, and that the lower-chord constant is exactly
what `V_S_free_sanction_floor` consumes — so this theorem is **not** its
converse.

Non-vacuity: `Examples.ce_chord_pos` exhibits an economy at a **constructed**
equilibrium satisfying both hypotheses at once (`ceParams` with the upper chord
`11/8`). -/
theorem chord_pos_of_equilibrium_dynamic_floor
    (E : p.FeedbackStackelbergEquilibriumTop) {cS x : ℝ}
    (hchord : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ (E.α y₂) s - p.U_S y₁ (E.α y₁) s ≤ cS * (y₂ - y₁))
    (hdyn : p.stageTopRule E.α x < p.dynamicTopRealizedRule E.V_S E.α x) :
    0 < cS := by
  by_contra hcon
  rw [not_lt] at hcon
  have hfix : p.dynamicTopRealizedRule (p.V_S E.α E.hα) E.α x
      = p.dynamicTopRealizedRule E.V_S E.α x := by
    rw [p.equilibrium_V_S_eq_constructed E]
  have := p.no_dynamic_floor_of_nonpos_chord E.hα hcon hchord x
  rw [hfix] at this
  linarith

/-- **The three refutation criteria are jointly contradictory.**  A counterexample
to DYNAMIC-STAKE would need, jointly: (i) a constructed equilibrium, (ii) a
dynamic floor strictly above the greatest stage maximiser, (iii) a non-positive
**upper** chord on the composed Sender state payoff.

Read this as a convenience restatement, not as independent evidence.  Its proof
is one `absurd` step against `chord_pos_of_equilibrium_dynamic_floor`, so it
carries exactly that theorem's content rearranged; it is not a second,
independent check that the refutation route is closed, and citing it as a
"Rule-11 record" alongside its own parent would double-count one argument.

It also says nothing about the routes left open by the scope limits — in
particular, an economy with a negative *raw* partial `∂U_S/∂x` and a positive
composed chord is consistent with everything here. -/
theorem dynamic_stake_refutation_target_is_empty
    (E : p.FeedbackStackelbergEquilibriumTop) {cS x : ℝ}
    (h_iii : cS ≤ 0)
    (hchord : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ (E.α y₂) s - p.U_S y₁ (E.α y₁) s ≤ cS * (y₂ - y₁))
    (h_ii : p.stageTopRule E.α x < p.dynamicTopRealizedRule E.V_S E.α x) : False :=
  absurd (p.chord_pos_of_equilibrium_dynamic_floor E hchord h_ii) (not_lt.mpr h_iii)

end Params
end AbstractGame

/-! ## 7. The scope separators, as theorems

Stated as theorems rather than docstrings so the scope cannot be lost. They
mention no `Params`; they are kept here rather than in `Foundations/` because
they exist only to fence the claim above, not as reusable mathematics. -/

/-- **SEPARATOR 1 — the raw partial chord is NOT the composed chord.** A stage
payoff that is non-increasing in the political state at *every fixed* compliance
level can still be strictly increasing along the Target's policy. Witness:
`U(x,a,s) = a − x` with `α y = 2y`.

Consequence, and this is the live open refutation route for DYNAMIC-STAKE: its
conclusion is "the Sender's payoff rises in the state **along the Target's
policy**", never "`∂U_S/∂x > 0`". An economy whose Sender dislikes entrenchment
per se, but where entrenched states buy enough extra compliance, is **not**
excluded by anything proved in this file, and could carry a genuine dynamic
floor while the informal reading of the result is false of it. -/
theorem raw_chord_ne_composed_chord :
    ∃ (U : ℝ → ℝ → ℝ → ℝ) (α : ℝ → ℝ),
      (∀ a s : ℝ, ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → U y₂ a s ≤ U y₁ a s)
      ∧ ¬ (∀ s : ℝ, ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → U y₂ (α y₂) s ≤ U y₁ (α y₁) s) := by
  refine ⟨fun x a _ => a - x, fun y => 2 * y, ?_, ?_⟩
  · intro a s y₁ y₂ h; simpa using by linarith
  · intro h
    have := h 0 0 1 zero_le_one
    norm_num at this

/-- **SEPARATOR 2 — an existential rise is NOT a uniform positive chord.**
DYNAMIC-STAKE concludes that the composed state payoff rises strictly
*somewhere*. That is strictly weaker than the uniform **lower** chord `m > 0`
that `V_S_free_sanction_floor`'s `h_state_slope` consumes: a payoff can be flat
on part of the state space and rise on the rest.

So DYNAMIC-STAKE is **not** the converse of the `V_S`-free floor theorem. The
two speak about different objects — an upper chord bound versus a lower chord
bound — and must not be cited as a necessary-and-sufficient pair. At most,
DYNAMIC-STAKE is a converse of the *qualitative sign* of that hypothesis, never
of its rate. -/
theorem existential_rise_does_not_give_uniform_chord :
    ∃ f : ℝ → ℝ,
      (∃ y₁ y₂ : ℝ, y₁ ≤ y₂ ∧ f y₁ < f y₂)
      ∧ ∀ m : ℝ, 0 < m →
          ¬ (∀ y₁ ∈ Set.Icc (0:ℝ) 1, ∀ y₂ ∈ Set.Icc (0:ℝ) 1, y₁ ≤ y₂ →
              m * (y₂ - y₁) ≤ f y₂ - f y₁) := by
  refine ⟨fun y => max 0 (y - 1/2), ⟨0, 1, by norm_num, by norm_num⟩, ?_⟩
  intro m hm h
  have := h 0 (by norm_num) (1/2) (by norm_num) (by norm_num)
  norm_num at this
  linarith

/-! ## Axiom hygiene (Rule 10) -/

section AxiomCheck
open Sanctions.AbstractGame.Params

#print axioms Sanctions.AbstractGame.Params.stageTopRule_eq_zeroValue_rule
#print axioms Sanctions.AbstractGame.Params.stageTopRule_eq_tree_line
#print axioms Sanctions.AbstractGame.Params.stageTopRule_le_dynamicTopRealizedRule
#print axioms Sanctions.AbstractGame.Params.dynamicTopRealizedRule_eq_stageTopRule_of_βS_zero
#print axioms Sanctions.AbstractGame.Params.realizedRule_le_stageTopRule_of_successor_antitone
#print axioms Sanctions.AbstractGame.Params.realizedRule_le_stageTopRule_of_antitone
#print axioms Sanctions.AbstractGame.Params.dynamicArgmax_le_stageTopRule_of_antitone
#print axioms Sanctions.AbstractGame.Params.realizedRule_le_stageTopRule_of_corner
#print axioms Sanctions.AbstractGame.Params.corner_stage_ceiling_excludes_dynamic_floor
#print axioms Sanctions.AbstractGame.Params.no_dynamic_floor_of_antitone_state_chord
#print axioms Sanctions.AbstractGame.Params.dynamic_stake
#print axioms Sanctions.AbstractGame.Params.dynamic_stake_equilibrium
#print axioms Sanctions.AbstractGame.Params.dynamic_stake_of_floor
#print axioms Sanctions.AbstractGame.Params.dynamic_stake_conclusion_is_x_free
#print axioms Sanctions.AbstractGame.Params.no_dynamic_floor_of_nonpos_chord
#print axioms Sanctions.AbstractGame.Params.chord_pos_of_equilibrium_dynamic_floor
#print axioms Sanctions.AbstractGame.Params.dynamic_stake_refutation_target_is_empty
/-- **SEPARATOR 1a — the same separation, with a FEASIBLE policy, and the price
of it.**

Separator 1's witness policy `α y = 2y` sends `y = 1` to compliance `2 ∉ [0,1]`,
so it separates the two objects as functions but exhibits no Target policy.  The
separation survives feasibility — but only by paying an explicit price, and the
price is the whole content of the composed-channel question.

Here `U` is strictly DECREASING in the action.  That is not incidental.  Writing
the composed increment as the raw increment plus a compliance-substitution term,
the substitution term has sign `∂U_S/∂a · α′`; so a composed rise from an
antitone policy `α` requires the Sender to be strictly harmed by compliance —
at the sanction where the chord binds, which for the cone is `s = 0`.

Consequence for the open route flagged in limit (1) of this file's header: that
route is real but it is not free.  An economy whose Sender dislikes entrenchment
per se and whose entrenched states buy extra compliance can only carry a
positive composed chord if it also has a Sender that dislikes COMPLIANCE at zero
sanction.  See `KaempferLowenberg.FourGroup.composed_antitone_story_forces_zero_slope`
for the machine-checked form of that trade-off inside the microfoundation. -/
theorem raw_chord_ne_composed_chord_feasible :
    ∃ (U : ℝ → ℝ → ℝ → ℝ) (α : ℝ → ℝ),
      (∀ y, y ∈ Sanctions.S → α y ∈ Sanctions.I)
      ∧ (∀ a s : ℝ, ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → U y₂ a s ≤ U y₁ a s)
      ∧ (∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
           (1/2 : ℝ) * (y₂ - y₁) ≤ U y₂ (α y₂) 0 - U y₁ (α y₁) 0) := by
  refine ⟨fun x a _ => -a - (1/2) * x, fun y => 1 - y, ?_, ?_, ?_⟩
  · rintro y ⟨h0, h1⟩; exact ⟨by linarith, by linarith⟩
  · intro a s y₁ y₂ h; simp only; linarith
  · intro y₁ _ y₂ _ h; simp only; linarith

#print axioms Sanctions.raw_chord_ne_composed_chord
#print axioms Sanctions.existential_rise_does_not_give_uniform_chord

end AxiomCheck

end -- noncomputable section

end Sanctions
