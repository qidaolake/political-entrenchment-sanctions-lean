/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.LockIn.DynamicTopLockIn
import Sanctions.Theory.Basin.WeakFloorBasin
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.Bellman.SenderLowerSlopeCone
import Sanctions.Theory.Equilibrium.AbsorbingTopObstruction

/-!
# The quantitative margin behind a positive equilibrium sanction

The project's sign conditions (`SenderStageID`, `TargetStageID`, and their
strict forms in `Theory/Basin/StageFlip.lean`) are *chord* conditions: they
order the cross-differences of the stage payoffs in `(s, x)` and say nothing
about the size of either the rally effect or the Sender's own sanction cost.
`Examples/SignConditionsInsufficient.lean` exhibits an economy where every sign
condition holds and every equilibrium sanctions at zero forever.

This file isolates the magnitude comparison that the sign conditions leave
free, over an arbitrary `Params`, an arbitrary continuation value, and an
arbitrary Target policy.  Both directions are proved:

* `realizedRule_margin` — **necessity**.  Because the realised rule is the
  greatest maximiser of the Sender's forward-looking objective, its stage loss
  relative to *any* comparison sanction is covered by the discounted
  continuation gain.  Nothing but argmax optimality is used.
* `realizedRule_eq_zero_of_stage_loss_dominates` — **sufficiency of the
  failure**.  If at a state every positive sanction's stage loss strictly
  exceeds the discounted continuation gain it buys, the equilibrium sanction at
  that state is exactly zero, so the state cannot be held up by sanctions.

Together: a positive equilibrium sanction is *equivalent* to a magnitude
condition on primitives, not to any sign condition on them.

## What this file does and does not establish

The refutation in `Examples/SignConditionsInsufficient.lean` kills one conjunct
of the perpetual-sanction claim — the **positive floor** — and the collapse
theorem above says why in general: the floor is a magnitude condition, and no
sign condition implies a magnitude.

Call the following the **margin at level `c` and state `x`**:

> there is a feasible sanction `s ≥ c` such that for every feasible `s'`,
> `U_S(x, α x, s') − U_S(x, α x, s) ≤ β_S·(V_S(F(x,s)) − V_S(F(x,s')))`,

i.e. *no feasible deviation's stage gain covers the continuation value it
gives up*.  `realizedRule_ge_iff_margin` shows this is logically equivalent to
the floor `c ≤ R x` itself.

**That equivalence is a restatement, not a repair, and it is important not to
oversell it.**  The reverse direction is witnessed by the realised rule itself,
so the content is "the greatest maximiser clears `c` iff some maximiser clears
`c`".  In particular the equivalence does *not* license the claim that the
margin is "the weakest condition that restores perpetual sanctions": since the
margin and the floor are the same condition, that claim reduces to the
tautology that the floor is the weakest condition implying the floor.  An
economically informative repair has to be stated *without* reference to `V_S`,
which is itself endogenous.  The final section of this file now supplies one;
what follows states exactly how much of the open question that closes.

## Status of the `V_S`-free question (updated 2026-07-31)

**What is now closed.**  `V_S_free_sanction_floor` is a sufficient condition
for the floor `c ≤ R x` **none of whose hypotheses mentions any continuation
value**.  Its three inputs are the Sender's stage state chord `m` (the Sender's
stage payoff rises in the political state at rate at least `m`), the Sender's
stage sanction-loss rate `cS` (its stage payoff falls in its own sanction at
rate at most `cS`), and the margin `cS · (1 − β_S(1−δ)) ≤ β_S · m · δ` — all
written in `U_S`, `β_S`, `δ` and the affine transition.  `V_S` occurs only in
the *conclusion*, and there only as the **constructed** Banach fixed point of
`bellmanS_BCF` (`Theory/Bellman/BellmanS.lean`), so Rule 15 is met: the value
function is built, not assumed, and its membership in the lower-slope cone the
argument needs is *derived* by `V_S_mem_lowerSlopeCone`
(`Examples/AffineInstance/ComplianceTower.lean:1977`; its general-transition
sibling `V_S_mem_lowerSlopeCone_generalF` is at
`Theory/Bellman/SenderLowerSlopeCone.lean:444`), not hypothesised.

The condition is also **strictly stronger** than the floor it certifies, so it
is informative and not another restatement.  `Examples/SenderConeWitness.lean`
exhibits an economy (`qParams`) at which the floor `1 ≤ R 1` holds while *no*
admissible pair `(m, cS)` satisfies the margin (`q_condition_fails`), together
with the admissible pair that makes that universal quantification non-vacuous
(`q_state_slope_witness`, `q_sanction_loss_witness`).

The barrier below is defeated on its own terms rather than evaded.
`uniform_floor_iff_stage_floor` proves that a floor demanded uniformly over the
*monotone* continuation carrier is exactly a floor on the greatest **stage**
maximiser — the zero continuation value is in that carrier and kills the
forward-looking channel outright.  The route above never quantifies over a
carrier: it pins the one continuation value the economy actually has, and
`V_S_ne_zero_of_pos_state_slope` shows that at a strictly positive state chord
that value cannot be `0`.  At the witness economy `wParams` the myopic stage
floor is `0` while the certified floor is `1` (`w_barrier_defeated`).

**What remains open — three things, none of them cosmetic.**

1. *No interior floor.*  Every discharged instance in the tree lands at
   `c = 1`.  Nothing exhibits a level `0 < c < 1` that is simultaneously
   interior and tight, and the corner-only route below
   (`realizedRule_eq_one_of_primitive_corner_margin`) has the same defect: it
   fires **only at the ceiling sanction `s = 1`** and concludes **only**
   `R x = 1`.  The general two-branch form that would reach the interior (one
   branch for downward deviations, one for upward) remains *unwitnessed*: at
   the project's own `eeCertParams` its upward hypothesis is unsatisfiable at
   every `s < 1` for every carrier constant the downward hypothesis admits.
   See `audit-notes/2026-07-30-parametric-algebraic-existence-budget.md`.
2. *No non-degenerate economy.*  Both witness economies — `wParams`, which
   satisfies the condition, and `qParams`, which separates it from the floor —
   make `U_S` independent of the Target's action, so the Target's action moves
   no Sender payoff, no Sender best response and no transition, and each object
   is a single-agent dynamic program rather than a game.  This is proved, not
   conceded — see `Examples/SenderConeWitness.lean`, `w_not_a_game` and
   `q_not_a_game`, both by `rfl`.  The condition is satisfiable; **no
   non-degenerate economy satisfying it has been exhibited.**
3. *`V_S`-free is not primitive-free in the strong sense.*  Both chord
   hypotheses are stated over the *composed* map `y ↦ U_S(y, α y, s)`.  At a
   joint MPE the Target policy `α` is itself endogenous (derived from `V_T`).
   The condition is `V_S`-free, which is what the open question asked for; it is
   not `α`-free, and it should never be described as "primitive-only" without
   that caveat.

There is also a structural price, proved rather than conceded — but read the
theorem, not this paragraph's ambition.
`no_top_gain_equilibrium_of_V_S_free_floor_condition` shows that at a
non-negative state chord `m ≥ 0`, the floor condition's hypotheses **together
with one further input the floor condition does not itself supply** — a
sanction-loss bound at the top state for a *deviation* action `E.α 1 + t`, which
is off-policy — discharge the hypotheses of
`AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain`
(`Theory/Equilibrium/AbsorbingTopObstruction.lean`), so that a feedback
Stackelberg equilibrium at which the Target strictly gains at the top state,
`U_T 1 (α 1) 1 < U_T 1 (α 1 + t) 1`, yields `False`.

Three qualifications, all of which an earlier draft of this header omitted.

* The off-policy bound is a genuine extra hypothesis.  It is *not* true that the
  condition's own hypotheses discharge everything.
* The theorem is **vacuous at both witness economies**: the top-gain hypothesis
  `hgain` is unsatisfiable at `wParams` and at `qParams`.  So it is a real
  theorem about the model class and says nothing about the exhibited witnesses.
* Consequently it does **not** explain why those witnesses have `U_S`
  independent of the Target's action.  That degeneracy
  (`w_not_a_game`, `q_not_a_game`) is a property of how the witnesses were
  built, and whether it is *forced* is open.

What survives is the qualitative echo of the `ratchet_dichotomy` already in
`AbsorbingTopObstruction.lean`: conditions strong enough to pin a sanction floor
sit in tension with an active Target channel.  That tension is now visible at two
places in the development rather than one, which is worth recording; it is not
yet a theorem that the tension is unavoidable.

What the equivalence is good for is bookkeeping.  `senderHighArgmax_iff_margin`
shows the margin is not a new assumption: it is the existing structure field
`JointPreferenceBasinTop.sender_high_argmax_exists` written over the raw
primitives `U_S`, `β_S`, `V_S`, `F` instead of over `IsMaxOn`, so
`ratchet_margin_of_jointPreferenceBasinTop` and `weak_margin_of_weakFloorBasinTop`
discharge it from either basin structure with no side condition.  Two
consumers, `perpetual_sanctions_of_margin` and
`perpetual_monotone_sanctions_of_ratchet_margin`, then package invariance plus
a positive (respectively non-decreasing) sanction path.  Both are reachable
from the basin structures directly; they are stated here only so that the
hypothesis can be checked against primitives.

The division of labour is what the counterexample predicts.  The sign
conditions buy the *monotonicity* input, via
`dynamicTopRealizedRule_mono_of_IDOFamilyOn`, from an interval-dominance /
single-crossing hypothesis.  They never buy the *floor*.

## Rule compliance

**Rule 3.** No new assumption surface: both theorems consume only existing
`Params` data and the existing selector `σ_dyn_top`; the margin hypothesis of
the second is a hypothesis of that theorem, written directly over `U_S`,
`β_S`, `V_S` and `F`, not a new structure field or opaque `Prop`.

**Rule 1.** The sanction whose size is being characterised is
`dynamicTopRealizedRule` — the greatest element of the Sender's dynamic argmax
set — not a posited constant.

**Rule 5.** Parametric over `(p, V_S, α, x)`; the witness application lives in
`Examples/SignConditionsInsufficient.lean`.

**Rule 19.** Model wiring (it mentions `Params`), hence `Theory/`.
-/

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **The margin is necessary.**  The realised equilibrium sanction beats every
feasible comparison sanction `s₀`, so its stage-payoff loss relative to `s₀` is
at most the discounted continuation gain it buys.  Pure argmax optimality:
no monotonicity, no functional form, no sign condition. -/
theorem realizedRule_margin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Sanctions.I) :
    p.U_S x (α x) s₀ - p.U_S x (α x) (p.dynamicTopRealizedRule V_S α x)
      ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x (p.dynamicTopRealizedRule V_S α x)))
          - V_S (Sanctions.clipS' (p.F x s₀))) := by
  have h := p.σ_dyn_top_isMaxOn V_S x (α x) hs₀
  simp only [Set.mem_setOf_eq] at h
  change p.U_S x (α x) s₀ - p.U_S x (α x) (p.σ_dyn_top V_S x (α x))
      ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x (α x))))
          - V_S (Sanctions.clipS' (p.F x s₀)))
  linarith [h]

/-- **The margin at the zero-sanction deviation.**  Specialising the comparison
sanction to `s₀ = 0`: whatever stage loss the Sender takes by sanctioning at
all is covered by the discounted continuation gain. -/
theorem realizedRule_margin_zero
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) :
    p.U_S x (α x) 0 - p.U_S x (α x) (p.dynamicTopRealizedRule V_S α x)
      ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x (p.dynamicTopRealizedRule V_S α x)))
          - V_S (Sanctions.clipS' (p.F x 0))) :=
  p.realizedRule_margin V_S α x ⟨le_refl 0, zero_le_one⟩

/-- **Failure of the margin collapses the sanction to zero.**  If at the state
`x` every positive feasible sanction costs the Sender more in stage payoff than
the discounted continuation gain it buys, then the equilibrium sanction at `x`
is exactly zero — irrespective of every sign condition the primitives satisfy.

This is the quantitative condition the sign conditions leave free: it is stated
entirely in existing parameters (`U_S`, `β_S`, `F`, and the equilibrium
continuation value `V_S`), and adding its negation on a basin is what a
perpetual-sanction claim actually needs. -/
theorem realizedRule_eq_zero_of_stage_loss_dominates
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ)
    (h : ∀ s ∈ Sanctions.I, 0 < s →
      p.β_S * (V_S (Sanctions.clipS' (p.F x s)) - V_S (Sanctions.clipS' (p.F x 0)))
        < p.U_S x (α x) 0 - p.U_S x (α x) s) :
    p.dynamicTopRealizedRule V_S α x = 0 := by
  set r := p.dynamicTopRealizedRule V_S α x with hr
  have hmem : r ∈ Sanctions.I := p.dynamicTopRealizedRule_mem V_S α x
  rcases eq_or_lt_of_le hmem.1 with heq | hpos
  · exact heq.symm
  · exact absurd (h r hmem hpos) (not_lt.mpr (p.realizedRule_margin_zero V_S α x))

/-- **A positive floor on a basin forces the margin on that basin.**  If the
realised equilibrium sanction stays above a positive floor on a set of states,
then at every one of those states the Sender's stage loss from sanctioning is
covered by its discounted continuation gain — the magnitude condition is not
optional. -/
theorem margin_of_positive_floor
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {B : Set ℝ} {sbar : ℝ}
    (hsbar : 0 < sbar)
    (hfloor : ∀ x ∈ B, sbar ≤ p.dynamicTopRealizedRule V_S α x) :
    ∀ x ∈ B, 0 < p.dynamicTopRealizedRule V_S α x ∧
      p.U_S x (α x) 0 - p.U_S x (α x) (p.dynamicTopRealizedRule V_S α x)
        ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x (p.dynamicTopRealizedRule V_S α x)))
            - V_S (Sanctions.clipS' (p.F x 0))) :=
  fun x hx => ⟨lt_of_lt_of_le hsbar (hfloor x hx), p.realizedRule_margin_zero V_S α x⟩

/-! ## The margin is exactly the floor — a restatement, not a repair

`realizedRule_margin` above compares the realised sanction against one
deviation.  Quantifying that comparison over *all* deviations, at a
sanction that clears a level `c`, turns out to be **equivalent** to the
floor `c ≤ R x` itself.

Do not read that equivalence as "the margin is the weakest condition
restoring a positive equilibrium sanction".  Since the margin and the floor
are the *same* condition, that reading reduces to the tautology that the
floor is the weakest condition implying the floor; and the reverse direction
is witnessed by the realised rule itself, so the equivalence is
near-definitional.  See the header for the full statement of what is and is
not established here. -/

/-- **The margin is sufficient for the floor.**  If at the state `x` there
is a feasible sanction `s ≥ c` no feasible deviation from which pays for
itself — the deviation's stage gain never covers the continuation value it
gives up — then the equilibrium-realised sanction is at least `c`.

Only argmax optimality is used: `s` is exhibited as a maximiser of the
Sender's forward-looking objective and the realised rule is the *greatest*
maximiser, so it lies at or above `s`.

**Not new content.**  This is `JointPreferenceBasinTop.level_dyn_top`
(`Theory/Basin/JointPreferenceBasin.lean`) with the `IsMaxOn` hypothesis
rearranged arithmetically — `a - b ≤ c - d` in place of `a + d ≤ b + c` — and
the proof is the same `le_csSup` step against `dynamicArgmaxSet_bddAbove`.  It
is kept only so that this file's statements can be read entirely in raw
primitives; anything downstream should prefer the basin version, which carries
the ratchet level `max x s̄` rather than a bare constant. -/
theorem realizedRule_ge_of_margin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x c : ℝ}
    (h : ∃ s ∈ Sanctions.I, c ≤ s ∧ ∀ s' ∈ Sanctions.I,
      p.U_S x (α x) s' - p.U_S x (α x) s
        ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
            - V_S (Sanctions.clipS' (p.F x s')))) :
    c ≤ p.dynamicTopRealizedRule V_S α x := by
  obtain ⟨s, hsI, hcs, hmargin⟩ := h
  have hsSet : s ∈ p.dynamicArgmaxSet V_S x (α x) := by
    refine ⟨hsI, ?_⟩
    intro s' hs'
    have h := hmargin s' hs'
    have hexp : p.β_S * (V_S (Sanctions.clipS' (p.F x s))
        - V_S (Sanctions.clipS' (p.F x s')))
      = p.β_S * V_S (Sanctions.clipS' (p.F x s))
        - p.β_S * V_S (Sanctions.clipS' (p.F x s')) := by ring
    rw [hexp] at h
    change p.U_S x (α x) s' + p.β_S * V_S (Sanctions.clipS' (p.F x s'))
        ≤ p.U_S x (α x) s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
    linarith
  unfold dynamicTopRealizedRule σ_dyn_top
  exact le_trans hcs (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x (α x)) hsSet)

/-- **The margin is necessary for the floor.**  Conversely, if the
equilibrium-realised sanction clears `c`, then it is itself the witness:
it is feasible, it clears `c`, and by `realizedRule_margin` no feasible
deviation from it pays for itself. -/
theorem margin_of_realizedRule_ge
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x c : ℝ}
    (h : c ≤ p.dynamicTopRealizedRule V_S α x) :
    ∃ s ∈ Sanctions.I, c ≤ s ∧ ∀ s' ∈ Sanctions.I,
      p.U_S x (α x) s' - p.U_S x (α x) s
        ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
            - V_S (Sanctions.clipS' (p.F x s'))) :=
  ⟨p.dynamicTopRealizedRule V_S α x, p.dynamicTopRealizedRule_mem V_S α x, h,
    fun _ hs' => p.realizedRule_margin V_S α x hs'⟩

/-- **The floor and the margin are the same condition.**

Read this as a *restatement*, not as a discovery, and in particular not as a
"weakest possible repair" result.  The reverse direction is witnessed by the
realised rule itself (`margin_of_realizedRule_ge` instantiates the existential
at `R x`), so the equivalence is near-definitional: it says that the greatest
maximiser clears `c` exactly when *some* maximiser clears `c`.  Calling the
margin "the weakest condition implying the floor" would therefore be a
tautology dressed as a finding — the floor is trivially the weakest condition
implying the floor.

What the equivalence is actually good for is bookkeeping: it lets a floor
hypothesis be checked against raw primitives (`U_S`, `β_S`, `F`) plus the
equilibrium continuation value, without first exhibiting an `IsMaxOn` witness.
The substantive direction of this file is the *other* one —
`realizedRule_eq_zero_of_stage_loss_dominates`, which converts a failure of the
margin into an actual collapse of the equilibrium sanction, and which is what
makes the sign-condition counterexample an instance of a general theorem rather
than an artefact of one economy. -/
theorem realizedRule_ge_iff_margin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x c : ℝ) :
    c ≤ p.dynamicTopRealizedRule V_S α x
      ↔ ∃ s ∈ Sanctions.I, c ≤ s ∧ ∀ s' ∈ Sanctions.I,
          p.U_S x (α x) s' - p.U_S x (α x) s
            ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
                - V_S (Sanctions.clipS' (p.F x s'))) :=
  ⟨fun h => p.margin_of_realizedRule_ge V_S α h,
   fun h => p.realizedRule_ge_of_margin V_S α h⟩

/-! ## The salvage, part 2: no new assumption surface

The margin is not a new hypothesis axis.  It is the existing Sender field
of the project's two basin structures, written over the raw primitives
rather than over `IsMaxOn`. -/

/-- **The margin *is* `sender_high_argmax_exists`.**  "There is a feasible
maximiser of the Sender's forward-looking objective at or above `c`" and
"there is a feasible `s ≥ c` from which no feasible deviation pays for
itself" are the same statement, unfolded. -/
theorem senderHighArgmax_iff_margin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x c : ℝ) :
    (∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s
        ∧ c ≤ s)
      ↔ (∃ s ∈ Sanctions.I, c ≤ s ∧ ∀ s' ∈ Sanctions.I,
          p.U_S x (α x) s' - p.U_S x (α x) s
            ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
                - V_S (Sanctions.clipS' (p.F x s')))) := by
  have hexp : ∀ s s' : ℝ, p.β_S * (V_S (Sanctions.clipS' (p.F x s))
        - V_S (Sanctions.clipS' (p.F x s')))
      = p.β_S * V_S (Sanctions.clipS' (p.F x s))
        - p.β_S * V_S (Sanctions.clipS' (p.F x s')) := by
    intro s s'; ring
  constructor
  · rintro ⟨s, hsI, hsMax, hcs⟩
    refine ⟨s, hsI, hcs, fun s' hs' => ?_⟩
    have h : p.U_S x (α x) s' + p.β_S * V_S (Sanctions.clipS' (p.F x s'))
        ≤ p.U_S x (α x) s + p.β_S * V_S (Sanctions.clipS' (p.F x s)) := hsMax hs'
    rw [hexp s s']
    linarith
  · rintro ⟨s, hsI, hcs, hmargin⟩
    refine ⟨s, hsI, ?_, hcs⟩
    intro s' hs'
    have h := hmargin s' hs'
    rw [hexp s s'] at h
    change p.U_S x (α x) s' + p.β_S * V_S (Sanctions.clipS' (p.F x s'))
        ≤ p.U_S x (α x) s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
    linarith

/-- The strong (ratchet) basin structure discharges the ratchet margin, with
no side condition. -/
theorem ratchet_margin_of_jointPreferenceBasinTop
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I, max x sbar ≤ s ∧ ∀ s' ∈ Sanctions.I,
        p.U_S x (α x) s' - p.U_S x (α x) s
          ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
              - V_S (Sanctions.clipS' (p.F x s'))) := fun x hx =>
  (p.senderHighArgmax_iff_margin V_S α x (max x sbar)).mp
    (hB.sender_high_argmax_exists x hx)

/-- The weak-floor basin structure discharges the level margin, with no side
condition. -/
theorem weak_margin_of_weakFloorBasinTop
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I, sbar ≤ s ∧ ∀ s' ∈ Sanctions.I,
        p.U_S x (α x) s' - p.U_S x (α x) s
          ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
              - V_S (Sanctions.clipS' (p.F x s'))) := fun x hx =>
  (p.senderHighArgmax_iff_margin V_S α x sbar).mp
    (hB.sender_high_argmax_exists x hx)

/-! ## The salvage, part 3: perpetual sanctions restored -/

/-- **SALVAGE (never-ending sanctions).**  Add to the sign conditions the
margin at the level floor `sbar` on the basin `[xbar, 1]`, together with the
corner condition `xbar ≤ F xbar sbar` (free whenever `xbar ≤ sbar`, and for
an affine transition *equivalent* to it), and perpetual sanctions are
restored:

* the basin is forward invariant under the realised closed loop;
* the realised sanction is at least `sbar` at every date; and
* it is therefore **strictly positive at every date, forever**.

The failing conjunct of the refuted universal claim was exactly the floor,
and this is exactly what buys it back.  Both governments still optimise at
every date — `dynamicTopLockInSanctionsF` is the greatest maximiser of the
Sender's forward-looking objective along the realised path.

General in `F`, and for every basin floor `xbar`: the hypothesis
`0 ≤ xbar` was dropped on 2026-10-06 (BG2.1 made it unread, since the
weak-floor invariance it used to feed holds for every `xbar`; the binder
itself was removed in the follow-up round, together with the positional
argument at its one caller, `Examples/SenderConeWitness.lean`). -/
theorem perpetual_sanctions_of_margin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hsbar_pos : 0 < sbar)
    (hCorner : xbar ≤ p.F xbar sbar)
    (hMargin : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I, sbar ≤ s ∧ ∀ s' ∈ Sanctions.I,
        p.U_S x (α x) s' - p.U_S x (α x) s
          ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
              - V_S (Sanctions.clipS' (p.F x s'))))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1)
    ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n)
    ∧ (∀ n, 0 < p.dynamicTopLockInSanctionsF V_S α x₀ n) := by
  have hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      sbar ≤ p.dynamicTopRealizedRule V_S α x :=
    fun x hx => p.realizedRule_ge_of_margin V_S α (hMargin x hx)
  have hpath := p.weakFloor_dynamicTopPathF_mem_basin V_S α hCorner hWeak hx₀
  have hfloor : ∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n :=
    fun n => hWeak _ (hpath n)
  exact ⟨hpath, hfloor, fun n => lt_of_lt_of_le hsbar_pos (hfloor n)⟩

/-- **SALVAGE (never-ending *and* never de-escalating).**  Strengthen the
margin from the level `sbar` to the ratchet level `max x sbar` — at every
basin state some optimal sanction is at least as large as the state itself —
and add monotonicity of the realised rule on the basin.  Then, along the
realised equilibrium path from any basin start:

* the basin is forward invariant;
* the sanction is at least `sbar > 0` at every date;
* the political state path is non-decreasing; and
* the **sanction path is non-decreasing** — sanctions never de-escalate.

The two inputs are exactly the two things the counterexample separates.  The
rule-monotonicity hypothesis is what the project's sign conditions deliver
(`dynamicTopRealizedRule_mono_of_IDOFamilyOn`); the ratchet margin is the
magnitude condition they do not.

General in `F`.  No `0 ≤ xbar`: it was read only by the basin lemmas, which
no longer need it (dropped on 2026-10-06, BG2.1). -/
theorem perpetual_monotone_sanctions_of_ratchet_margin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hsbar_pos : 0 < sbar)
    (hMargin : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I, max x sbar ≤ s ∧ ∀ s' ∈ Sanctions.I,
        p.U_S x (α x) s' - p.U_S x (α x) s
          ≤ p.β_S * (V_S (Sanctions.clipS' (p.F x s))
              - V_S (Sanctions.clipS' (p.F x s'))))
    (hRuleMono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1)
    ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n)
    ∧ (∀ n, 0 < p.dynamicTopLockInSanctionsF V_S α x₀ n)
    ∧ Monotone (p.dynamicTopLockInPathF V_S α x₀)
    ∧ Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  have hLevel : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x :=
    fun x hx => p.realizedRule_ge_of_margin V_S α (hMargin x hx)
  have hpath := p.dynamicTopLockInPathF_mem_basin V_S α hLevel hx₀
  have hfloor := p.dynamicTopLockInSanctionsF_floor V_S α hLevel hx₀
  exact ⟨hpath, hfloor, fun n => lt_of_lt_of_le hsbar_pos (hfloor n),
    p.dynamicTopLockInPathF_mono V_S α hLevel hx₀,
    p.dynamicTopLockInSanctionsF_mono V_S α hLevel hRuleMono hx₀⟩

/-! ## A corner-only primitive route to the ceiling, and the barrier behind it

Everything above states the margin against the *endogenous* continuation value
`V_S`.  This section records a partial route that replaces `V_S` in the
hypothesis by primitives plus one carrier constant, and the barrier theorem
that bounds how far any such route can go.

**Scope, stated up front.**  The route below reaches only the ceiling.  Its
conclusion is `R x = 1`, not a floor `c ≤ R x` at an interior `c`, and its
hypothesis is a margin evaluated at `s = 1`.  The general two-branch version —
a downward branch converted by a minimum-upward-slope constant `g` and an
upward branch converted by a Lipschitz cap `K`, which together would reach an
interior sanction — is **deliberately absent**: it is unwitnessed.  At the
project's flagship witness `eeCertParams` the upward hypothesis has no solution
at any `s < 1` for any constant the downward hypothesis permits, so no economy
in the tree instantiates it and it is not stated here.  See
`audit-notes/2026-07-30-parametric-algebraic-existence-budget.md`.

**What the fragment does and does not buy.**  It is *not* correct to say the
ceiling is where the dynamic content vanishes, and an earlier draft of this
header said so on two mistaken grounds, both now checked and withdrawn.

First, the claim that at the project's witnesses the stage payoff is already
maximised at `1` is false: at `eeCertParams` with `x = 0`, `α ≡ 1` one has
`U_S 0 1 1 < U_S 0 1 0`, so the ceiling is *not* a stage maximiser there, and
the corner route still delivers `R x = 1`.  The slope constant is doing real
work at that point, not bookkeeping.

Second, the appeal to `σ_dyn_top_ge_sigma`
(`Theory/LockIn/SigmaDynComparison.lean`) was a misreading.  That theorem
concludes `σ x a ≤ σ_dyn_top V x a`, and the `Params` field `σ` is constrained
only by `σ_isMaxOn_U_S` — it is *some* stage maximiser, not the greatest.  So
"`1` belongs to the stage argmax set" does **not** give `σ x (α x) = 1` and does
not give `R x = 1`.  The monotone route does not subsume this one.

What remains true, and is the actual limitation, is narrower: the conclusion is
`R x = 1`, so the fragment certifies only the **ceiling** and says nothing about
any interior level `0 < c < 1`.  The open question in the header — a sufficient
condition for a positive equilibrium sanction stated without reference to `V_S`
— is therefore untouched by it.

`uniform_floor_iff_stage_floor` is the corresponding negative result and is the
substantive content of the section. -/

/-- **Downward branch of the primitive margin.**  Fix a state `x`, an action
`a := α x`, a reference sanction `s`, and a *lower* deviation `s' ≤ s`.  If the
Sender's stage gain from cutting the sanction to `s'` is at most `β_S · g`
times the drop in next-period state that the cut causes, then the same gain is
at most the discounted continuation loss measured against **any** continuation
value `V` whose minimum upward slope on the state space is `g`.

The point is that the hypothesis `hd` mentions no continuation value: it is an
inequality in `U_S`, `β_S`, `F` and the single constant `g`.  The conclusion is
the `V`-facing inequality that `realizedRule_ge_of_margin` above consumes.

Only the *downward* direction is covered here, and only because `F` is
monotone in `s`, so `s' ≤ s` gives `F x s' ≤ F x s` and the slope hypothesis
points the right way.  Upward deviations need the separate Lipschitz cap
below. -/
theorem margin_down_of_lowerSlope
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {g : ℝ}
    (hGain : AbstractGame.Params.LowerSlopeOnValueOn V (Set.Icc 0 1) g)
    {x a s : ℝ} (hx : x ∈ Sanctions.I) (hsI : s ∈ Sanctions.I)
    {s' : ℝ} (hs' : s' ∈ Sanctions.I) (hle : s' ≤ s)
    (hd : p.U_S x a s' - p.U_S x a s ≤ p.β_S * g * (p.F x s - p.F x s')) :
    p.U_S x a s' - p.U_S x a s
      ≤ p.β_S * (V (Sanctions.clipS' (p.F x s))
          - V (Sanctions.clipS' (p.F x s'))) := by
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hFs : p.F x s ∈ Set.Icc (0:ℝ) 1 := p.F_mem x s hx hsI
  have hFs' : p.F x s' ∈ Set.Icc (0:ℝ) 1 := p.F_mem x s' hx hs'
  have hFle : p.F x s' ≤ p.F x s := p.F_mono_s x hle
  have hord : Sanctions.clipS' (p.F x s') ≤ Sanctions.clipS' (p.F x s) :=
    Sanctions.clipS'_mono hFle
  have hslope := hGain _ _ (by rw [Sanctions.clipS'_val_eq_of_mem hFs']; exact hFs')
    (by rw [Sanctions.clipS'_val_eq_of_mem hFs]; exact hFs) hord
  rw [clipS'_dist_eq_of_mem hFs' hFs, abs_of_nonpos (by linarith)] at hslope
  have hslope' : g * (p.F x s - p.F x s')
      ≤ V (Sanctions.clipS' (p.F x s)) - V (Sanctions.clipS' (p.F x s')) := by
    linarith [hslope]
  nlinarith [mul_le_mul_of_nonneg_left hslope' hβ, hd]

/-- **Upward branch of the primitive margin.**  The mirror image: for an
*upper* deviation `s ≤ s'`, a stage gain bounded by `−β_S · K` times the rise
in next-period state is dominated by the discounted continuation loss against
any `K`-Lipschitz continuation value.

Again the hypothesis `hu` names no continuation value.  Note the sign: because
raising the sanction raises the next state, and a `K`-Lipschitz `V` can gain at
most `K` per unit of state, the primitive hypothesis has to demand that the
stage gain from raising the sanction be *negative* and at least as large in
magnitude as `β_S · K · (F x s' − F x s)`.  That is a demanding requirement.

**Do not read it as unsatisfiable.**  An earlier draft asserted that at
`eeCertParams` the hypothesis has no solution at any `s < 1`; that is false as
stated — at `K = 0` (a constant `V`, which is `0`-Lipschitz) the hypothesis
reduces to a bare stage inequality and is met.  The honest statement is weaker
and carries a condition: no economy in this tree has been exhibited meeting the
hypothesis away from the ceiling *at a Lipschitz constant large enough to also
satisfy the downward branch*, so the two branches have not been made to fire
together at an interior sanction.  That is an absence of a witness, not a proof
of impossibility, and per Rule 11 it is recorded here as such rather than as a
verdict — the quantitative claim that would make it a verdict is not currently
backed by any object in the tree. -/
theorem margin_up_of_lipschitz
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {K : ℝ}
    (hLip : AbstractGame.Params.ValueLipschitzWith V K)
    {x a s : ℝ} (hx : x ∈ Sanctions.I) (hsI : s ∈ Sanctions.I)
    {s' : ℝ} (hs' : s' ∈ Sanctions.I) (hle : s ≤ s')
    (hu : p.U_S x a s' - p.U_S x a s ≤ -(p.β_S * K * (p.F x s' - p.F x s))) :
    p.U_S x a s' - p.U_S x a s
      ≤ p.β_S * (V (Sanctions.clipS' (p.F x s))
          - V (Sanctions.clipS' (p.F x s'))) := by
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hFs : p.F x s ∈ Set.Icc (0:ℝ) 1 := p.F_mem x s hx hsI
  have hFs' : p.F x s' ∈ Set.Icc (0:ℝ) 1 := p.F_mem x s' hx hs'
  have hFle : p.F x s ≤ p.F x s' := p.F_mono_s x hle
  have hdd : dist (Sanctions.clipS' (p.F x s)) (Sanctions.clipS' (p.F x s'))
      = p.F x s' - p.F x s := by
    rw [clipS'_dist_eq_of_mem hFs hFs', abs_of_nonpos (by linarith)]; ring
  have habs := hLip (Sanctions.clipS' (p.F x s)) (Sanctions.clipS' (p.F x s'))
  rw [hdd] at habs
  have hhi : V (Sanctions.clipS' (p.F x s')) - V (Sanctions.clipS' (p.F x s))
      ≤ K * (p.F x s' - p.F x s) := (abs_le.mp habs).2
  nlinarith [mul_le_mul_of_nonneg_left hhi hβ, hu]

/-- **Corner-only primitive certificate.**  At the ceiling sanction `s = 1`
every feasible deviation is downward, so the upward branch is vacuous and the
Lipschitz cap is not needed.  If the Sender's stage gain from cutting from `1`
to any feasible `s'` is covered by `β_S · g` times the resulting drop in the
next state, then against *every* continuation value with minimum upward slope
`g` the equilibrium-realised sanction at `x` is exactly `1`.

**What this is not.**  It is not a primitive-only *floor* condition.  The
conclusion is the ceiling and only the ceiling: the hypothesis is evaluated at
`s = 1`, so the statement says nothing about any interior level, and the open
question this file's header records — a sufficient condition for a positive
equilibrium sanction stated without reference to `V_S` — is untouched by it.

**It is not subsumed by the monotone route.**  The hypothesis `hdown` asks that
no downward deviation from the ceiling pay for itself once the continuation
slope `g` is charged against it.  An earlier draft dismissed this as
bookkeeping, on the grounds that the stage payoff is already maximised at `1`
wherever the route fires, so that bare `Monotone V` would suffice.  Both halves
of that were wrong.  At `eeCertParams` with `x = 0` and `α ≡ 1`,
`U_S 0 1 1 < U_S 0 1 0`, so `1` is *not* a stage maximiser and the route still
concludes `R x = 1`; and `σ_dyn_top_ge_sigma` cannot deliver the conclusion in
any case, because the `Params` field `σ` is only *some* stage maximiser
(`σ_isMaxOn_U_S`), not the greatest.  The slope constant does real work.

The genuine limitation is the one stated above: the conclusion is the ceiling
`R x = 1`, so no interior floor follows.

Rule 1 is respected: `dynamicTopRealizedRule` is the greatest maximiser of the
Sender's forward-looking objective, not a posited sanction level. -/
theorem realizedRule_eq_one_of_primitive_corner_margin
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {g : ℝ}
    (hGain : AbstractGame.Params.LowerSlopeOnValueOn V (Set.Icc 0 1) g)
    {x : ℝ} (hx : x ∈ Sanctions.I)
    (hdown : ∀ s' ∈ Sanctions.I,
      p.U_S x (α x) s' - p.U_S x (α x) 1 ≤ p.β_S * g * (p.F x 1 - p.F x s')) :
    p.dynamicTopRealizedRule V α x = 1 := by
  have hone : (1:ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl _⟩
  refine le_antisymm (p.dynamicTopRealizedRule_mem V α x).2 ?_
  refine p.realizedRule_ge_of_margin V α ⟨1, hone, le_refl _, ?_⟩
  intro s' hs'
  exact p.margin_down_of_lowerSlope V hGain hx hone hs' hs'.2 (hdown s' hs')

/-- **The zero continuation value collapses the dynamic argmax to the stage
argmax.**  With `V_S = 0` the forward-looking term vanishes identically, so the
Sender's dynamic argmax set at `(x, a)` is literally the set of maximisers of
the *stage* payoff `U_S x a ·` on `[0,1]`.

Bookkeeping for the barrier below; `0` is a perfectly legitimate continuation
value (it is bounded, monotone, and `K`-Lipschitz for every `K ≥ 0`). -/
theorem dynamicArgmaxSet_zero (x a : ℝ) :
    p.dynamicArgmaxSet 0 x a
      = {s | s ∈ Sanctions.I ∧ IsMaxOn (fun s' => p.U_S x a s') Sanctions.I s} := by
  unfold Sanctions.AbstractGame.Params.dynamicArgmaxSet
  simp

/-- **BARRIER — a monotone-uniform floor is exactly a myopic floor.**  Demanding
the floor `c ≤ R x` for *every monotone* continuation value is logically
equivalent to demanding `c ≤ sSup` of the **stage** argmax set at `(x, α x)`.
The forward-looking channel contributes nothing.

The substantive direction is the forward one, and it is proved by exhibiting
the zero continuation value: `0` is monotone, so a floor uniform over the
monotone carrier must in particular hold at `0`, where by
`dynamicArgmaxSet_zero` the dynamic argmax *is* the stage argmax.  The reverse
direction is the routine argument that the greatest dynamic maximiser dominates
any stage maximiser once `V` is monotone, run at `max s₀ (σ_dyn_top V x (α x))`.

**Why this matters for the open question.**  The file header asks for a
sufficient condition for a positive equilibrium sanction stated in primitives,
without reference to the endogenous `V_S`.  The natural way to state such a
condition is to quantify over a carrier of admissible continuation values.  This
theorem says that if the carrier is only asked to be monotone, then whatever the
condition certifies, the myopic stage argmax already certified.  (Monotonicity
is not the weakest carrier the project uses — `valLipBall`
(`Theory/Bellman/InvariantLipBall.lean`) asks only for a sup-norm bound and a
Lipschitz constant, imposing no order restriction at all.  The point here is
not that monotonicity is weak in some ordering of carriers, but that the
monotone carrier *contains the zero function*, and the zero function kills the
forward-looking channel outright.)  So a `V_S`-free floor
with genuine dynamic content must restrict the carrier *quantitatively* (a
strictly positive minimum upward slope, say), and then the burden shifts to
showing that some equilibrium of the economy actually lands in that carrier.

**That burden is now discharged** — though *not* in this file, contrary to what
this sentence said before 2026-09-01: `V_S_free_sanction_floor` lives at
`Examples/AffineInstance/LockInShocked.lean:397`. It restricts the carrier by a
positive lower slope and obtains membership by *deriving* it
(`V_S_mem_lowerSlopeCone`, `Examples/AffineInstance/ComplianceTower.lean:1977`)
rather than assuming it, and `w_barrier_defeated` shows the resulting floor
exceeds the stage floor at a witness.  What remains open is narrower and is
listed in the header: no interior floor `0 < c < 1` has been certified, and no
non-degenerate economy satisfying the condition has been exhibited. -/
theorem uniform_floor_iff_stage_floor (α : ℝ → ℝ) (x c : ℝ) :
    (∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, Monotone V →
        c ≤ p.dynamicTopRealizedRule V α x)
      ↔ c ≤ sSup {s | s ∈ Sanctions.I ∧
            IsMaxOn (fun s' => p.U_S x (α x) s') Sanctions.I s} := by
  constructor
  · intro h
    have h0 : Monotone ((0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) := by
      intro y₁ y₂ _; simp
    have hz := h 0 h0
    have heq : p.dynamicTopRealizedRule 0 α x = sSup (p.dynamicArgmaxSet 0 x (α x)) :=
      rfl
    rw [heq, p.dynamicArgmaxSet_zero] at hz
    exact hz
  · intro h V hV
    refine le_trans h ?_
    -- A stage maximiser exists by Weierstrass: the dynamic argmax at the zero
    -- continuation value is non-empty and is the stage argmax. The `Params`
    -- selector `σ` is not read (BG1.10).
    have hne : {s | s ∈ Sanctions.I ∧
        IsMaxOn (fun s' => p.U_S x (α x) s') Sanctions.I s}.Nonempty := by
      have h := p.dynamicArgmaxSet_nonempty 0 x (α x)
      rwa [p.dynamicArgmaxSet_zero] at h
    refine csSup_le hne ?_
    rintro s₀ ⟨hs₀I, hs₀max⟩
    obtain ⟨hrI, hrmax⟩ := p.σ_dyn_top_mem_dynamicArgmaxSet V x (α x)
    set r := p.σ_dyn_top V x (α x) with hrdef
    have hmem : max s₀ r ∈ p.dynamicArgmaxSet V x (α x) := by
      rcases le_total s₀ r with hle | hle
      · rw [max_eq_right hle]; exact ⟨hrI, hrmax⟩
      · rw [max_eq_left hle]
        refine ⟨hs₀I, ?_⟩
        intro s' hs'
        have hstage : p.U_S x (α x) r ≤ p.U_S x (α x) s₀ := hs₀max hrI
        have hVle : V (Sanctions.clipS' (p.F x r))
            ≤ V (Sanctions.clipS' (p.F x s₀)) :=
          hV (Sanctions.clipS'_mono (p.F_mono_s x hle))
        have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
        have hr' : p.U_S x (α x) s' + p.β_S * V (Sanctions.clipS' (p.F x s'))
            ≤ p.U_S x (α x) r + p.β_S * V (Sanctions.clipS' (p.F x r)) := hrmax hs'
        have hmul := mul_le_mul_of_nonneg_left hVle hβ
        simp only [Set.mem_setOf_eq]
        linarith
    exact le_trans (le_max_left s₀ r)
      (le_csSup (p.dynamicArgmaxSet_bddAbove V x (α x)) hmem)

/-! ## The `V_S`-free floor

The route that closes the first half of the open question recorded in the
header.  It runs in three steps:

1. `senderDynObjective_monotoneOn_of_sanction_loss_offset` — the Sender mirror
   of the Target-side discharger
   `targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value_on`
   (`Examples/AffineInstance/Bridges.lean:948`; the `LowerSlopeOnValueOn`
   predicate it consumes is defined at
   `Theory/Certificates/TargetSanctionLossOffset.lean:108`).  A stage loss rate
   `cS` in the sanction is covered by the discounted continuation gain
   `β_S · g · δ` when the continuation value has minimum upward state-slope
   `g`, so the Sender's forward-looking objective is non-decreasing on `[0,c]`.
2. `realizedRule_ge_of_monotoneOn` — a forward-looking objective that is
   non-decreasing on `[0,c]` puts the *greatest* Sender maximiser at or above
   `c`.
3. `V_S_free_sanction_floor` (`Examples/AffineInstance/LockInShocked.lean:397`)
   — feeding the constructed value `V_S α hα` into
   (1) via `V_S_mem_lowerSlopeCone`
   (`Examples/AffineInstance/ComplianceTower.lean:1977`), which *derives* the required
   slope `g = m / (1 − β_S(1−δ))` from the primitive stage state chord `m`.
   The continuation value therefore never appears on the hypothesis side.

The last two theorems of the section record the price, as theorems rather than
as prose.

**Residence note (2026-09-01).** Of the three-step route above only step 2,
`realizedRule_ge_of_monotoneOn`, is still resident in this file (at `:790`).
Steps 1 and 3 live in `Examples/AffineInstance/`. That is a layering fact worth
knowing before citing this section: the parametric machinery it narrates sits
*below* the layer that narrates it, and `Theory/` cannot import `Examples/`. -/


/-- **A forward-looking objective non-decreasing on `[0,c]` puts the greatest
equilibrium sanction at or above `c`.**  If the greatest maximiser `R x` were
strictly below `c`, monotonicity would make `c` a maximiser too, contradicting
`R x = sSup` of the dynamic argmax set.

Rule 1: `dynamicTopRealizedRule` is the greatest element of the Sender's
dynamic argmax set, not a posited sanction level. -/
theorem realizedRule_ge_of_monotoneOn
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x c : ℝ}
    (hc : c ∈ Sanctions.I)
    (hmono : MonotoneOn (fun s => p.senderDynObjective V x (α x) s) (Set.Icc (0:ℝ) c)) :
    c ≤ p.dynamicTopRealizedRule V α x := by
  by_contra hcon
  rw [not_le] at hcon
  have hrI : p.dynamicTopRealizedRule V α x ∈ Sanctions.I :=
    p.dynamicTopRealizedRule_mem V α x
  have hr_mem : p.dynamicTopRealizedRule V α x ∈ Set.Icc (0:ℝ) c :=
    ⟨hrI.1, le_of_lt hcon⟩
  have hc_mem : c ∈ Set.Icc (0:ℝ) c := ⟨hc.1, le_refl c⟩
  have h1 := hmono hr_mem hc_mem (le_of_lt hcon)
  have hmax := p.σ_dyn_top_isMaxOn V x (α x)
  have hc_argmax : c ∈ p.dynamicArgmaxSet V x (α x) := by
    refine ⟨hc, ?_⟩
    intro s' hs'
    have h2 : p.U_S x (α x) s' + p.β_S * V (Sanctions.clipS' (p.F x s'))
        ≤ p.U_S x (α x) (p.σ_dyn_top V x (α x))
          + p.β_S * V (Sanctions.clipS' (p.F x (p.σ_dyn_top V x (α x)))) := hmax hs'
    have h1' : p.U_S x (α x) (p.σ_dyn_top V x (α x))
          + p.β_S * V (Sanctions.clipS' (p.F x (p.σ_dyn_top V x (α x))))
        ≤ p.U_S x (α x) c + p.β_S * V (Sanctions.clipS' (p.F x c)) := h1
    show p.U_S x (α x) s' + p.β_S * V (Sanctions.clipS' (p.F x s'))
      ≤ p.U_S x (α x) c + p.β_S * V (Sanctions.clipS' (p.F x c))
    linarith
  have hle : c ≤ p.dynamicTopRealizedRule V α x :=
    le_csSup (p.dynamicArgmaxSet_bddAbove V x (α x)) hc_argmax
  linarith


/-- **Any equilibrium's Sender value IS the constructed Banach fixed point.**
A feedback Stackelberg equilibrium carries the field
`V_S_fix : V_S = bellmanS_BCF α hα V_S`, and the Bellman operator is a
contraction, so Banach uniqueness identifies `E.V_S` with `p.V_S E.α E.hα`.
Nothing is assumed about the equilibrium's value beyond its own fixed-point
field. -/
theorem equilibrium_V_S_eq_constructed (E : p.FeedbackStackelbergEquilibriumTop) :
    E.V_S = p.V_S E.α E.hα := by
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF E.α E.hα) :=
    p.bellmanS_BCF_contracting E.hα
  have h_eq : p.V_S E.α E.hα = hcontr.fixedPoint := by
    unfold AbstractGame.Params.V_S; congr
  rw [h_eq]
  exact ContractingWith.fixedPoint_unique hcontr E.V_S_fix.symm


#print axioms realizedRule_margin
#print axioms realizedRule_margin_zero
#print axioms realizedRule_eq_zero_of_stage_loss_dominates
#print axioms margin_of_positive_floor
#print axioms realizedRule_ge_of_margin
#print axioms margin_of_realizedRule_ge
#print axioms realizedRule_ge_iff_margin
#print axioms senderHighArgmax_iff_margin
#print axioms ratchet_margin_of_jointPreferenceBasinTop
#print axioms weak_margin_of_weakFloorBasinTop
#print axioms perpetual_sanctions_of_margin
#print axioms perpetual_monotone_sanctions_of_ratchet_margin
#print axioms margin_down_of_lowerSlope
#print axioms margin_up_of_lipschitz
#print axioms realizedRule_eq_one_of_primitive_corner_margin
#print axioms dynamicArgmaxSet_zero
#print axioms uniform_floor_iff_stage_floor
#print axioms realizedRule_ge_of_monotoneOn
#print axioms equilibrium_V_S_eq_constructed

end Params
end AbstractGame

end

end Sanctions
