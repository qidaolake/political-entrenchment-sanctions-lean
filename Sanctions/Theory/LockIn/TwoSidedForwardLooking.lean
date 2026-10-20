/-
Sanctions/Theory/LockIn/TwoSidedForwardLooking.lean

**The Target-policy ordering without an argmax-uniqueness hypothesis.**

`DifferentPolicyComparator.lean` §10 already carries the compliance-direction
route from the total forward-looking wedge to cross-policy rule dominance:
`DynamicVsMyopicDecreasingDifferencesAt` gives `E.α x ≤ M.α x` through
`alpha_order_dynamic_le_myopic_of_decreasingDifferences`, and
`dynamicTop_rule_dominates_myopic_policy_audit41_compliance` composes that with
compliance-placates and a monotone Sender value to discharge `hRuleDom`. That
route is at the two equilibria's *own* Sender responses, not at a common one, so
it is already the honest cross-response comparison.

What it also carries is a hypothesis that is easy to grant without noticing:

  `h_myo_unique : ∀ a ∈ I, a ≠ M.α x → U_T(x,a,σ(x,a)) < U_T(x,M.α x,σ(x,M.α x))`

— the myopic Target's argmax is the *unique* maximizer at `x`. Its increasing-
differences sibling in §8 carries the mirror-image hypothesis on the dynamic
side. Both are there for the same structural reason: a weak wedge condition
cannot separate two argmaxes, so the argument closes by forcing an equality and
then contradicting uniqueness.

**Why the hypothesis is worth removing.** Uniqueness of a maximizer is not an
economic primitive; it is a regularity condition on the payoff, and where it
fails it fails exactly where the model is interesting — flat stretches of the
stage payoff, kinks at a corner, ties between compliance levels. Worse, a
conclusion that needs it is not selection-robust: it says something about the
particular `M.α` the equilibrium structure happens to carry, and nothing about
another equally valid selection from the same argmax correspondence. Since the
project's own equilibrium structures do not assert single-valuedness, a result
resting on uniqueness is weaker than it looks.

**What this file adds.** Strengthen the wedge condition from weakly to
*strictly* decreasing, and the uniqueness hypothesis disappears:

  strictly decreasing wedge  ⇒  `E.α x ≤ M.α x`, for *every* pair of maximizers.

Three lines, no concavity, no single crossing, no uniqueness anywhere. The
strictness does the separating work that uniqueness was doing, and it does it on
the hypothesis side where it has an economic reading — every extra unit of
compliance is *strictly* less attractive to a Target that looks ahead — rather
than on the regularity side where it has none. This is the same trade already
made on the common-response comparison in `TargetReluctance.lean`; here it is
made at the actual two Sender responses.

**Where the argument actually lives.** The ordering is not special to this pair
of objectives: it is an instance of a general fact about the maximizers of *two
different* optimization problems, which is stated and proved once in
`Foundations/BinaryComparativeStatics.lean` and instantiated here. Keeping it
there rather than inline makes the assumption surface visible — the general
theorem uses no continuity, concavity, compactness or uniqueness, so neither
does this one — and it is the layer split Rule 19 asks for, since the general
statement mentions nothing about sanctions.

**The objects, unabbreviated.** With `E : FeedbackStackelbergEquilibriumTop` the
forward-looking equilibrium and `M : MyopicFeedbackEquilibrium` the myopic one,
the Target maximises

* forward-looking (`FF`): `joint_T_top_integrand E.V_T E.V_S x a`
  `= U_T(x, a, σ_dyn_top E.V_S x a) + β_T · V_T(clip F(x, σ_dyn_top E.V_S x a))`
* myopic (`MM`): `U_T(x, a, σ(x, a))`

and `totalForwardWedge` is their difference. Both the continuation value and the
switch of Sender response sit inside it, which is what makes it the
cross-response object rather than the common-`ρ` one.

**Scope.** This compares two *given* equilibria; it does not construct them, and
it does not show the wedge is strictly decreasing at any economy. Strict
decrease is a hypothesis here, discharged neither from primitives nor by a
witness — the cross-response term
`U_T(x,a,σ_dyn_top V_S x a) - U_T(x,a,σ(x,a))` is a harder object than the
common-`ρ` wedge of `TargetReluctance.lean`, and controlling it is the open
step. Nor does the conclusion assert a *strict* policy gap: `E.α x ≤ M.α x` is
consistent with the two policies coinciding, so nothing here shows the Target
channel is behaviourally active at any economy.

General in the transition: `F` enters only through `joint_T_top_integrand`, and
`p.δ` is never read.
-/

import Sanctions.Foundations.BinaryComparativeStatics
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.LockIn.TargetReluctance
import Sanctions.Foundations.SelfSustainingSet
import Sanctions.Foundations.ArgmaxSensitivity

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The total forward-looking wedge, named -/

/-- **The total forward-looking wedge at a state `x`.** The gap between what the
Target gets from compliance `a` when both it and the Sender look ahead, and what
it gets when neither does. Both the continuation value and the switch of Sender
response are inside this difference.

`DynamicVsMyopicDecreasingDifferencesAt` and
`DynamicVsMyopicIncreasingDifferencesAt` write this expression out inline; the
name is introduced so the strict condition below reads as a monotonicity
statement about one object rather than an inequality between four terms. -/
noncomputable def totalForwardWedge
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) : ℝ :=
  p.joint_T_top_integrand E.V_T E.V_S x a - p.U_T x a (p.σ x a)

/-- **Strictly decreasing total wedge at `x`.** Every extra unit of compliance
is *strictly* less attractive under the fully forward-looking regime than under
the fully myopic one. The strict form of
`DynamicVsMyopicDecreasingDifferencesAt`. -/
def DynamicVsMyopicStrictDecreasingDifferencesAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ < a₂ →
    p.totalForwardWedge E x a₂ < p.totalForwardWedge E x a₁

/-- The strict condition implies the existing weak one, so anything proved from
`DynamicVsMyopicDecreasingDifferencesAt` remains available on this route. -/
theorem DynamicVsMyopicStrictDecreasingDifferencesAt.toDecreasing
    {p : Sanctions.AbstractGame.Params}
    {E : p.FeedbackStackelbergEquilibriumTop} {x : ℝ}
    (h : p.DynamicVsMyopicStrictDecreasingDifferencesAt E x) :
    p.DynamicVsMyopicDecreasingDifferencesAt E x := by
  intro a₁ h₁ a₂ h₂ hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq; exact le_rfl
  · exact le_of_lt (h a₁ h₁ a₂ h₂ hlt)

/-! ## 2. The α-ordering, with no uniqueness hypothesis -/

/-- **A forward-looking Target complies no more than a myopic one — for every
selection from either argmax correspondence.**

`E.α x` maximises the fully forward-looking Target objective against the dynamic
Sender selector; `M.α x` maximises the fully myopic one against the static
Sender response. If the total wedge between them is *strictly* decreasing in
compliance, then `E.α x ≤ M.α x`.

**What is gained over
`alpha_order_dynamic_le_myopic_of_decreasingDifferences`.** That theorem reaches
the same conclusion from the weak wedge condition, at the cost of `h_myo_unique`
— the myopic maximizer must be unique at `x`. Strictness here replaces
uniqueness, so the conclusion holds for *any* maximizers `E.α x` and `M.α x`,
not just for a distinguished pair. Where the argmax correspondences are in fact
single-valued the two theorems say the same thing; where they are not, only this
one says anything.

**The argument.** Suppose `M.α x < E.α x`. The wedge is strictly smaller at the
higher action, `M.α x` beats `E.α x` on the myopic objective, and `E.α x` beats
`M.α x` on the forward-looking one. Adding the first two contradicts the third.
No concavity, no single crossing, no ties to break.

Rule 1: `E.α` and `M.α` are the equilibrium structures' own optimality fields
(`α_opt_top`, `α_opt`); no policy is posited. -/
theorem alpha_order_dynamic_le_myopic_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (h_dec : p.DynamicVsMyopicStrictDecreasingDifferencesAt E x) :
    E.α x ≤ M.α x :=
  -- Routed through the general binary comparison in
  -- `Foundations/BinaryComparativeStatics.lean`. The statement is unchanged;
  -- only the proof moved, so that the ordering is visibly an instance of a
  -- general principle about two objectives rather than a bespoke argument
  -- about this pair. `totalForwardWedge` is by definition the gap between the
  -- forward-looking and myopic Target objectives, so the strictly-decreasing
  -- wedge hypothesis IS the cardinal sufficient condition of that principle,
  -- and the two equilibria's own optimality fields supply the maximizers.
  Sanctions.BinaryComparativeStatics.argmax_le_of_strictSCLowerOn
    (Sanctions.BinaryComparativeStatics.strictSCLowerOn_of_gap_strictAnti h_dec)
    (E.α_mem x hx) (M.α_mem x hx) (E.α_opt_top x hx) (M.α_opt x hx)

/-- **The strict cross-response ordering: the forward-looking Target complies
strictly less than the myopic one.**

Every ordering in this area concludes `≤`, which is consistent with the two
equilibria choosing the same compliance — so none of them, alone, shows the
Target channel is ever behaviourally active. Strictness cannot follow from the
wedge condition alone: if the myopic Target already sits at full defiance, no
wedge can push the forward-looking one lower. The extra input is one chord
inequality, the cross-response twin of
`target_dynamic_complies_lt_myopic_at_same_response`:

  `MM(M.α x) - MM(a') < Δ(a') - Δ(M.α x)`

with `MM(a) = U_T(x, a, σ(x,a))` the fully myopic objective and `Δ` the total
forward-looking wedge. The left side is the stage payoff the myopic Target gives
up by backing off from its own choice `M.α x` to some lower `a'`; the right side
is how much more the forward-looking regime is worth at `a'` than at `M.α x`.
When the second exceeds the first, `M.α x` is not optimal for the fully
forward-looking Target, so its maximizer lies strictly below.

No uniqueness of either argmax is used, here or in the weak ordering it builds
on, so the conclusion holds for every selection from either correspondence.

Rule 3 symbol economy: a strict inequality among existing quantities; no margin
scalar is named and no lower bound on `M.α x - E.α x` is asserted. -/
theorem alpha_order_dynamic_lt_myopic_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x a' : ℝ} (hx : x ∈ Sanctions.S) (ha'_mem : a' ∈ Sanctions.I)
    (h_dec : p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (h_chord : p.U_T x (M.α x) (p.σ x (M.α x)) - p.U_T x a' (p.σ x a')
                 < p.totalForwardWedge E x a' - p.totalForwardWedge E x (M.α x)) :
    E.α x < M.α x := by
  have hle : E.α x ≤ M.α x :=
    p.alpha_order_dynamic_le_myopic_of_strictDecreasingDifferences E M hx h_dec
  simp only [totalForwardWedge] at h_chord
  -- `a'` strictly beats `M.α x` on the forward-looking objective
  have hbeat : p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
                 < p.joint_T_top_integrand E.V_T E.V_S x a' := by linarith
  -- and `E.α x` is at least as good as `a'`
  have hbest : p.joint_T_top_integrand E.V_T E.V_S x a'
                 ≤ p.joint_T_top_integrand E.V_T E.V_S x (E.α x) :=
    E.α_opt_top x hx ha'_mem
  have hne : E.α x ≠ M.α x := by
    intro heq
    rw [heq] at hbest
    linarith
  exact lt_of_le_of_ne hle hne


/-! ## 3. A *strict* ordering that needs no wedge condition at all -/

/-- **The forward-looking Target complies strictly less — established from the
myopic objective alone.**

Every other strictness route in this development runs through the wedge: assume
the forward-looking-minus-myopic gap falls in compliance, then conclude. That
route is blocked at its root, because
`Examples/SenderSwitchSignUndetermined.lean` proves the Sender-response-switch
half of that wedge has no sign determined by the model's primitives. Assuming
the wedge condition would therefore be assuming precisely what cannot be
derived.

This theorem takes the other road and asks nothing about the wedge. It looks
only at the **myopic** objective `a ↦ U_T(x, a, σ(x,a))` and where it sits
relative to the forward-looking equilibrium's own action:

* `h_best_below` — among actions weakly *below* `E.α x`, none is myopically
  better than `E.α x` itself;
* `h_better` — some feasible action is myopically *strictly* better.

Then every myopic equilibrium complies strictly more: `E.α x < M.α x`.

**Economically.** The forward-looking incumbent stops short of what the stage
payoff alone would recommend, because complying further would cost it political
ground next period. The two hypotheses say exactly that the myopic incumbent has
somewhere strictly better to go and no reason to retreat below the
forward-looking action — so it goes up, and the gap between the regimes is the
reluctance the continuation value buys.

**What it does not assume.** No wedge condition, no single crossing, no
decreasing differences, no concavity, no interiority, no argmax uniqueness, and
nothing whatever about `E`'s optimality — `E.α x` enters only as a real number.
The conclusion holds for *every* myopic equilibrium, so it is a statement about
the myopic argmax correspondence rather than about a convenient selection.

**Where the content lives.** The argument is a pure order fact and is proved once
in `Foundations/BinaryComparativeStatics.lean` as `lt_argmax_of_improves_above`;
this is its instantiation at the Target's myopic objective (Rule 19).

Rule 1: `M.α` is the myopic equilibrium structure's own optimality field
(`α_opt`); no policy is posited. -/
theorem alpha_lt_myopic_of_myopic_improves_above
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x a' : ℝ} (hx : x ∈ Sanctions.S) (ha'_mem : a' ∈ Sanctions.I)
    (h_best_below : ∀ a ∈ Sanctions.I, a ≤ E.α x →
      p.U_T x a (p.σ x a) ≤ p.U_T x (E.α x) (p.σ x (E.α x)))
    (h_better : p.U_T x (E.α x) (p.σ x (E.α x)) < p.U_T x a' (p.σ x a')) :
    E.α x < M.α x :=
  Sanctions.BinaryComparativeStatics.lt_argmax_of_improves_above
    h_best_below ha'_mem h_better (M.α_mem x hx) (M.α_opt x hx)

/-! ## 4. Composition to cross-policy rule dominance, uniqueness-free

`dynamicTop_rule_dominates_myopic_policy_audit41_compliance` already composes the
weak route to `hRuleDom` on `Sanctions.S`. The versions below do the same on the
strict route, and over an arbitrary region `B ⊆ Sanctions.S` rather than all of
`Sanctions.S`, so a basin-local caller need not supply the hypotheses off the
basin. -/

/-- **Rule dominance from Target reluctance and a placating Sender rule, on a
region.**

Given the reluctance ordering `E.α ≤ M.α` on `B`, plus a Sender stage rule that
is non-increasing in compliance (placation) and a monotone Sender continuation
value, the myopic realised sanction is pointwise dominated by the upper-dynamic
realised sanction — exactly the `hRuleDom` hypothesis of
`dynamicTopSanctions_ge_myopicEquilibrium_different_alpha`.

Same content as
`myopicCeiling_from_alpha_order_dynamic_le_and_sigma_antitoneOn` followed by
`σ_dyn_top_ge_sigma`, with the quantifier over `B` instead of `Sanctions.S`.

The two channels reinforce here: reluctance *lowers* the Target's compliance and
so *raises* the sanction the Sender's static rule returns, and Sender investment
raises it again. -/
theorem ruleDom_on_of_reluctance_and_sigma_antitoneOn
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : Monotone E.V_S)
    (hα_reluctance : ∀ x ∈ B, E.α x ≤ M.α x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  intro x hx
  have hxS : x ∈ Sanctions.S := hB_subS hx
  have hMx : M.α x ∈ Sanctions.I := M.α_mem x hxS
  have hEx : E.α x ∈ Sanctions.I := E.α_mem x hxS
  have hceil : p.σ x (M.α x) ≤ p.σ x (E.α x) :=
    hσ_antiOn_a x hx hEx hMx (hα_reluctance x hx)
  exact le_trans hceil (p.σ_dyn_top_ge_sigma E.V_S hV_S_mono x (E.α x))

/-- **The full uniqueness-free chain, from the strict wedge to rule dominance.**

The selection-robust counterpart of
`dynamicTop_rule_dominates_myopic_policy_audit41_compliance`: same conclusion,
localized to a region `B`, and with the myopic-argmax uniqueness hypothesis
replaced by strictness of the wedge. Three inputs remain, each with a direct
economic reading:

* `h_dec` — looking ahead makes compliance strictly less attractive, wedge form;
* `hσ_antiOn_a` — compliance placates: the Sender's stage rule is non-increasing
  in the Target's compliance;
* `hV_S_mono` — the Sender values entrenchment, so its continuation value is
  non-decreasing in the political state. -/
theorem ruleDom_on_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hV_S_mono : Monotone E.V_S)
    (h_dec : ∀ x ∈ B, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
  p.ruleDom_on_of_reluctance_and_sigma_antitoneOn E M hB_subS hV_S_mono
    (fun x hx =>
      p.alpha_order_dynamic_le_myopic_of_strictDecreasingDifferences E M
        (hB_subS hx) (h_dec x hx))
    hσ_antiOn_a

/-! ## 5. The two channels the wedge splits into

§1 named the total forward-looking wedge as one object, which is what the
α-ordering needs: a single quantity whose strict decrease separates the two
argmaxes. But the paper does not describe it as one object. It describes two
distinct economic forces, and until now that split has lived only in prose.

This section names the three Target objectives and both channels, and proves the
split is **exact** — no residual, no cross term. The identity is one `ring` call
once the definitions are written down, and that is the point: the decomposition
is bookkeeping, and bookkeeping is exactly the sort of claim that should be
machine-checked rather than asserted in a paragraph.

The three objectives, at a fixed state `x`, as functions of compliance `a`:

* `targetMMObjective` — **both players myopic.** The Target's stage payoff when
  the Sender answers with its static best response `σ(x,a)`. This is what
  `M.α_opt` maximizes.
* `targetTMObjective` — **Target forward-looking, Sender myopic.** The same
  static Sender response, but the Target now also values the political state that
  response leads to. A proof device, not a third equilibrium concept: no
  maximizer of it is ever constructed below, and none is needed.
* `targetFFObjective` — **both forward-looking.** The Target values continuation
  *and* faces the forward-looking Sender response `σ_dyn_top`. Definitionally
  `joint_T_top_integrand`, so this is what `E.α_opt_top` maximizes.

The two channels are the two steps between them:

* `targetContinuationWedge` = TM − MM — the **Target-continuation** channel, or
  Target reluctance. What the incumbent's own political-survival motive adds,
  holding the Sender's behaviour fixed. `targetContinuationWedge_eq` identifies
  it as `β_T` times the `targetComplianceContinuation` of
  `TargetReluctance.lean`, which that file already signs from separated
  primitives.
* `senderSwitchWedge` = FF − TM — the **Sender-response-switch** channel. What
  changes for the Target purely because the Sender it faces looks ahead: the same
  compliance now draws `σ_dyn_top` instead of `σ`. This is the channel that
  `Examples/SenderSwitchSignUndetermined.lean` refutes any attempt to sign from
  the model's primitives alone.

Why the split earns its keep. A reader auditing the persistence claim wants to
know which part of the forward-looking wedge is the incumbent's own motive and
which part is the Sender's response — the two have different policy readings
and, as the refutation shows, different logical status. With the identity
proved, that reading is a theorem rather than a paragraph. It is also what a
margin route needs: bounding the two channels separately bounds the total, which
is what lets an *adverse* Sender-switch channel be tolerated rather than assumed
away. -/

/-- **Both players myopic.** The Target's stage payoff at compliance `a` when the
Sender answers with its static best response. `M.α_opt` is an `IsMaxOn` for
exactly this function. -/
noncomputable def targetMMObjective (x a : ℝ) : ℝ :=
  p.U_T x a (p.σ x a)

/-- **Target forward-looking, Sender myopic.** The static Sender response is
unchanged, but the Target now also values the political state that response
induces. A proof device: no maximizer of it is constructed anywhere below, and it
is not offered as an equilibrium concept. -/
noncomputable def targetTMObjective
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  p.U_T x a (p.σ x a)
    + p.β_T * p.targetComplianceContinuation p.σ V_T x a

/-- **Both players forward-looking.** Definitionally the equilibrium's own Target
Bellman integrand, so `E.α_opt_top` is an `IsMaxOn` for exactly this
function. -/
noncomputable def targetFFObjective
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) : ℝ :=
  p.joint_T_top_integrand E.V_T E.V_S x a

/-! ### The same objective, before there is an equilibrium

`targetFFObjective` reads its two value functions off an equilibrium structure.
That is convenient at the point of use and wrong as the primitive: the Target's
objective is a function of a *value pair*, and nothing in it needs the pair to
have come from a fixed point. Carrier-level results have to state the comparison
before any equilibrium exists — quantified over the members of a carrier, or at a
fixed point about to be constructed — and they cannot do that through a predicate
that takes an equilibrium as an argument.

So the objective and its ordinal comparison are restated at a bare value pair,
with the equilibrium forms recovered as definitional instances. Nothing changes
about what is assumed: `DirectTargetStrictSCLowerAt E x` unfolds to the
hypothesis already consumed by `alpha_order_dynamic_le_myopic_of_strictSC`, so
this is a re-indexing of the existing surface and not an addition to it
(Rule 3). -/

/-- **The Target's fully forward-looking objective at a value pair.** -/
noncomputable def targetFFObjectiveAtValues
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  p.joint_T_top_integrand V_T V_S x a

/-- The equilibrium form is this one at the equilibrium's own value pair. -/
@[simp] theorem targetFFObjective_eq_atValues
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) :
    p.targetFFObjective E x a = p.targetFFObjectiveAtValues E.V_T E.V_S x a :=
  rfl

/-- **The canonical ordinal comparison, at a value pair.**

Every maximizer of the fully forward-looking objective lies weakly below every
maximizer of the fully myopic one, and this is the weakest condition in the file
delivering that: no continuity, no concavity, no uniqueness, no cardinal
structure. The cardinal and two-leg conditions are *dischargers* of it, and the
arrows are named below so the hierarchy can be read off rather than
reconstructed. -/
def DirectTargetStrictSCLowerAtValues
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.StrictSCLowerOn
    (p.targetFFObjectiveAtValues V_T V_S x) (p.targetMMObjective x) Sanctions.I

/-- The weak form, which orders the two argmax *correspondences* rather than
forcing every forward-looking maximizer strictly below. -/
def DirectTargetSCLowerAtValues
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.SCLowerOn
    (p.targetFFObjectiveAtValues V_T V_S x) (p.targetMMObjective x) Sanctions.I

/-- The equilibrium wrapper: definitionally the value-pair form at `E`. -/
def DirectTargetStrictSCLowerAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  p.DirectTargetStrictSCLowerAtValues E.V_T E.V_S x

/-- The weak equilibrium wrapper. -/
def DirectTargetSCLowerAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  p.DirectTargetSCLowerAtValues E.V_T E.V_S x

/-- **The Target-continuation channel.** What the incumbent's own valuation of
the political state adds, holding the Sender's behaviour fixed at its static
response. -/
noncomputable def targetContinuationWedge
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  p.targetTMObjective V_T x a - p.targetMMObjective x a

/-- **The Sender-response-switch channel.** What changes for the Target purely
because the Sender it faces looks ahead — the same compliance now draws
`σ_dyn_top` rather than `σ`. -/
noncomputable def senderSwitchWedge
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) : ℝ :=
  p.targetFFObjective E x a - p.targetTMObjective E.V_T x a

/-- The total wedge of §1 is the FF-minus-MM gap, by definition. -/
theorem totalForwardWedge_eq_FF_sub_MM
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) :
    p.totalForwardWedge E x a
      = p.targetFFObjective E x a - p.targetMMObjective x a := rfl

/-- **The Target-continuation channel is `β_T` times the continuation wedge
`TargetReluctance.lean` signs from separated primitives**, evaluated at the
static Sender response.

This is the join between the two files: whatever makes
`targetComplianceContinuation` strictly fall in compliance — compliance strictly
placates, sanctions strictly raise the successor state, the Target strictly
values entrenchment — makes this channel strictly fall too, given `β_T > 0`. -/
theorem targetContinuationWedge_eq
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.targetContinuationWedge V_T x a
      = p.β_T * p.targetComplianceContinuation p.σ V_T x a := by
  unfold targetContinuationWedge targetTMObjective targetMMObjective
  ring

/-- **The decomposition is exact.**

    total forward wedge  =  Target-continuation channel  +  Sender-switch channel

No residual and no cross term. Everything the forward-looking regime does to the
Target's compliance incentive is one of these two effects, so a route that bounds
both bounds the total. -/
theorem totalForwardWedge_eq_targetContinuation_add_senderSwitch
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) :
    p.totalForwardWedge E x a
      = p.targetContinuationWedge E.V_T x a + p.senderSwitchWedge E x a := by
  unfold totalForwardWedge targetContinuationWedge senderSwitchWedge
    targetFFObjective targetTMObjective targetMMObjective
  ring

/-! ## 6. The ordinal entry points

§2 takes the *cardinal* condition — the whole wedge strictly falls. That is
usually what a model delivers, because a wedge is something one can bound channel
by channel. But it is not what the α-ordering needs. What the ordering needs is
the ordinal relation of `Foundations/BinaryComparativeStatics.lean`, and the
wedge condition is strictly stronger than it.

Exposing the ordinal form as its own entry point matters twice over. It is a
*selection-robust ordinal sufficient* condition — reusable, auditable, and
stated without reference to where the maximizers happen to sit — which is what
makes it the right thing for the paper to carry. It is **not** the weakest
possible hypothesis, and should not be described as one: two argmax sets can
happen to be ordered while the relation fails away from the maximizers. And it
composes: the relation is transitive, so the two channels of §5 can
be discharged one at a time against the intermediate objective — **without
anyone ever constructing a maximizer of that intermediate objective.**
`StrictSCLowerOn.trans` is the entire argument, and its one-line proof is the
reason the intermediate regime needs no equilibrium theory of its own. -/

/-- **A selection-robust ordinal condition under which a forward-looking Target
complies no more than a myopic one.**

Strict single-crossing lower dominance of the fully forward-looking objective
against the fully myopic one: whenever compliance does not become less attractive
to the forward-looking Target, it becomes *strictly* more attractive to the
myopic one. That is enough to order every pair of maximizers, and no continuity,
concavity, compactness, or uniqueness is used.

It is sufficient, not necessary. Two argmax sets can be ordered while the
relation fails somewhere away from the maximizers, so this is not the weakest
hypothesis delivering the conclusion — its value is that it is reusable and
independent of where the unknown maximizers sit.

`alpha_order_dynamic_le_myopic_of_strictDecreasingDifferences` is the cardinal
route to the same conclusion; this is the ordinal condition underneath it. -/
theorem alpha_order_dynamic_le_myopic_of_strictSC
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hsc : Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I) :
    E.α x ≤ M.α x :=
  Sanctions.BinaryComparativeStatics.argmax_le_of_strictSCLowerOn hsc
    (E.α_mem x hx) (M.α_mem x hx) (E.α_opt_top x hx) (M.α_opt x hx)

/-- **The canonical policy ordering, stated on the named ordinal condition.**

Identical in content to `alpha_order_dynamic_le_myopic_of_strictSC`; the point of
the separate name is that the hypothesis is now the *named* predicate, so every
route in this file terminates in a statement of the same shape and the hierarchy
is visible at a glance:

    net cardinal          ──▶ direct strict SC ──▶ αFF ≤ αMM
    weak switch + strict Target ──▶ direct strict SC
    two weak channels     ──▶ direct weak SC   ──▶ argmax correspondences ordered

Rule 1: both policies are the equilibrium structures' own optimality fields.
No uniqueness of either argmax is used, so the conclusion holds for every pair of
selections. -/
theorem alpha_order_dynamic_le_myopic_of_directStrictSC
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hSC : p.DirectTargetStrictSCLowerAt E x) :
    E.α x ≤ M.α x :=
  p.alpha_order_dynamic_le_myopic_of_strictSC E M hx hSC

/-- The cardinal condition of §1 implies the ordinal one of §6: a strictly
falling total wedge is strict single-crossing lower dominance. -/
theorem targetFF_strictSCLower_targetMM_of_totalWedge_strictAnti
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (h : p.DynamicVsMyopicStrictDecreasingDifferencesAt E x) :
    Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I :=
  Sanctions.BinaryComparativeStatics.strictSCLowerOn_of_gap_strictAnti
    (fun a₁ h₁ a₂ h₂ hlt => h a₁ h₁ a₂ h₂ hlt)

/-- **The Sender-switch leg, ordinally.** The forward-looking Target facing the
forward-looking Sender is strictly single-crossing lower than the same Target
facing the *static* Sender. This isolates what the switch of Sender response
alone does to compliance incentives, holding the Target's own continuation motive
fixed on both sides. -/
def SenderSwitchSCLowerAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.StrictSCLowerOn
    (p.targetFFObjective E x) (p.targetTMObjective E.V_T x) Sanctions.I

/-- **The Target-continuation leg, ordinally.** A Target that values the
political state is strictly single-crossing lower than one that does not, at the
*same* static Sender response. This is the channel `TargetReluctance.lean`
signs. -/
def TargetContinuationSCLowerAt
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.StrictSCLowerOn
    (p.targetTMObjective V_T x) (p.targetMMObjective x) Sanctions.I

/-- **The two legs compose.**

Discharge the Sender-switch leg and the Target-continuation leg separately and
the full FF-against-MM ordering follows. No maximizer of the intermediate
objective is constructed, and no quasi-supermodularity of it is needed —
transitivity of the relation carries the whole argument.

This is what makes the §5 decomposition usable rather than merely descriptive:
the two channels can now be attacked with different tools, at different levels of
strength, in different files. -/
theorem targetFF_strictSCLower_targetMM_of_two_legs
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hSwitch : p.SenderSwitchSCLowerAt E x)
    (hTarget : p.TargetContinuationSCLowerAt E.V_T x) :
    Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I :=
  Sanctions.BinaryComparativeStatics.StrictSCLowerOn.trans hSwitch hTarget

/-- **Arrow: the two-leg ordinal route discharges the direct condition.** -/
theorem directStrictSC_of_two_legs
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hSwitch : p.SenderSwitchSCLowerAt E x)
    (hTarget : p.TargetContinuationSCLowerAt E.V_T x) :
    p.DirectTargetStrictSCLowerAt E x :=
  p.targetFF_strictSCLower_targetMM_of_two_legs E hSwitch hTarget

/-- The α-ordering from the two legs, in one step. -/
theorem alpha_order_dynamic_le_myopic_of_two_legs
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hSwitch : p.SenderSwitchSCLowerAt E x)
    (hTarget : p.TargetContinuationSCLowerAt E.V_T x) :
    E.α x ≤ M.α x :=
  p.alpha_order_dynamic_le_myopic_of_strictSC E M hx
    (p.targetFF_strictSCLower_targetMM_of_two_legs E hSwitch hTarget)

/-! ## 7. Onward from rule dominance: paths and the self-sustaining set

`ruleDom_on_of_strictDecreasingDifferences` in §4 ends at a pointwise comparison
of the two realized sanction rules, and until now the chain stopped there — the
general-transition path comparators in `DifferentPolicyComparator.lean` take
exactly that hypothesis, and nothing composed the two.

This section closes the gap in both available directions.

**Paths.** Feeding rule dominance to the general-`F` comparators orders the state
paths and the sanction sequences from a common start, in every period. Both need
the upper rule monotone on the feasible region; that is the comparator's
requirement, not a new economic assumption.

**The self-sustaining set.** Rule dominance alone — with no monotonicity, no
invariance, no path argument — enlarges the set of states the rule does not pull
down, and therefore lowers its infimum. This is strictly cheaper than the path
result, and the two answer different questions: the path result says where a
given start goes, the set result says which starts hold.

The economic reading of `x ≤ R x` is supplied by
`le_ruleStepF_of_mem_selfSustainingSet` below, and it needs only two ordinal
facts about the transition that `Params` already carries — `F` non-decreasing in
the sanction and `F x x = x`. No affine law, no `δ` (Rule 22). That implication
runs one way only: membership is *sufficient* for the state not to fall, and the
converse would need strict monotonicity in the sanction, which the baseline does
not supply.

What is *not* claimed: that either infimum is a basin boundary.
`Examples/SelfSustainingInfNotCharacterizing.lean` refutes that reading with a
constant rule — monotone, continuous, feasibility-preserving — whose
self-sustaining set is bounded above. The inclusion is the result. -/

/-- **Self-sustaining is sufficient for the state not to fall, under a general
transition.**

If the rule answers `x` with at least `x`, the state does not fall in one step.
The proof is two ordinal facts: `F` is non-decreasing in the sanction, and
`F x x = x`. No functional form for `F`, and in particular no affine law.

One direction only. The converse — that a state which does not fall must be
answered with at least itself — needs `F` *strictly* increasing in the sanction,
which the baseline does not assume, so `selfSustainingSet` is a sufficient
condition for one-step persistence and not a characterization of it. -/
theorem le_ruleStepF_of_mem_selfSustainingSet
    {R : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Sanctions.selfSustainingSet Sanctions.I R) :
    x ≤ p.ruleStepF R x := by
  -- Ascribe the type so the `Monotone` application beta-reduces before `rw`.
  have h : p.F x x ≤ p.F x (R x) := p.F_mono_s x hx.2
  rw [p.F_diag x] at h
  exact h

/-- **Self-sustaining is also *necessary*, once the adjustment is strict.**

The companion to `le_ruleStepF_of_mem_selfSustainingSet`, and the reason that
theorem states one direction only. `Params.StrictAdjustment` says a sanction
strictly below the state strictly lowers it and a sanction strictly above
strictly raises it; under it, a rule answering below the state *must* pull the
state down, so "the state does not fall" and "the rule answers at least the
state" are the same condition.

The strictness is exactly what closes the gap the weak form leaves open. With
`F_mono_s` alone, `R x < x` yields only `F x (R x) ≤ F x x = x`, and the equality
case is a state that holds still under a rule sitting strictly beneath it —
admissible for the baseline, and ruled out here.

Both memberships are needed: `StrictAdjustment` is a statement about the feasible
square, so a rule answering outside `[0,1]` is outside its reach. No functional
form and no affine law (Rule 22); no new assumption, since `StrictAdjustment` is
an existing `Params` predicate carried by eight witnesses. -/
theorem le_rule_iff_le_ruleStepF_of_strictAdjustment
    (hAdj : p.StrictAdjustment) {R : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Sanctions.I) (hRx : R x ∈ Sanctions.I) :
    x ≤ R x ↔ x ≤ p.ruleStepF R x := by
  constructor
  · intro h
    exact p.le_ruleStepF_of_mem_selfSustainingSet ⟨hx, h⟩
  · intro hstep
    by_contra hnot
    have hfall : p.F x (R x) < x := hAdj.1 hx hRx (lt_of_not_ge hnot)
    have hge : x ≤ p.F x (R x) := hstep
    linarith

/-- **The self-sustaining set is exactly the non-falling set, under strict
adjustment.** The set form of the equivalence above. -/
theorem mem_selfSustainingSet_iff_le_ruleStepF_of_strictAdjustment
    (hAdj : p.StrictAdjustment) {R : ℝ → ℝ}
    (hR : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I) :
    Sanctions.selfSustainingSet Sanctions.I R
      = {x | x ∈ Sanctions.I ∧ x ≤ p.ruleStepF R x} := by
  ext x
  constructor
  · rintro ⟨hx, hle⟩
    exact ⟨hx, (p.le_rule_iff_le_ruleStepF_of_strictAdjustment hAdj hx
      (hR x hx)).1 hle⟩
  · rintro ⟨hx, hstep⟩
    exact ⟨hx, (p.le_rule_iff_le_ruleStepF_of_strictAdjustment hAdj hx
      (hR x hx)).2 hstep⟩

/-- **State paths are ordered from closed-loop monotonicity, general `F`.**
Sibling of `rulePathF_myopic_le_dynamicTop_of_strictDecreasingDifferences` with
`hDynMono` (the forward-looking realised rule is non-decreasing in the state)
replaced by `hDynStepMono`: the forward-looking *closed loop*
`x ↦ F(x, R_dyn x)` is non-decreasing on `[0,1]`. In plain terms: from a common
feasible start, the myopic regime's political state stays weakly below the
forward-looking one in every period, provided tomorrow's state under the
forward-looking policy preserves the order of today's states — the sanction rule
itself may move against the state wherever the transition does not respond.
Dropped: monotonicity of the rule, which the path comparison reads only through
the closed loop (`rulePathF_le_of_rule_le_and_closedLoop_mono`; strictly weaker
by `exists_closedLoopMono_without_monotone_rule`). General in `F` (BG1.8). -/
theorem rulePathF_myopic_le_dynamicTop_of_strictDecreasingDifferences_closedLoopMono
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hDynStepMono : MonotoneOn
      (p.ruleStepF (p.dynamicTopRealizedRule E.V_S E.α)) Sanctions.I)
    (h_dec : ∀ x ∈ Sanctions.I, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePathF (p.myopicEquilibriumRule M) x₀ n
          ≤ p.rulePathF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  refine p.rulePathF_le_of_rule_le_and_closedLoop_mono ?_ ?_ hDynStepMono ?_ hx₀
  · exact fun x _ => p.σ_mem x (M.α x)
  · exact fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x
  · exact p.ruleDom_on_of_strictDecreasingDifferences (B := Sanctions.I) E M
      Set.Subset.rfl hV_S_mono h_dec hσ_antiOn_a

/-- **State paths are ordered, general `F`.** From a common feasible start, the
myopic regime's political state stays weakly below the forward-looking one in
every period.

Inputs, in English: the Sender values entrenchment (`hV_S_mono`); the
forward-looking realized rule is non-decreasing in the state (`hDynMono`, the
comparator's own requirement); looking ahead makes compliance strictly less
attractive at every state of the region (`h_dec`); and compliance placates —
the Sender's stage rule is non-increasing in the Target's compliance
(`hσ_antiOn_a`). -/
theorem rulePathF_myopic_le_dynamicTop_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hDynMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (h_dec : ∀ x ∈ Sanctions.I, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePathF (p.myopicEquilibriumRule M) x₀ n
          ≤ p.rulePathF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  -- Statement unchanged; since BG1.8 a corollary of the closed-loop sibling.
  exact p.rulePathF_myopic_le_dynamicTop_of_strictDecreasingDifferences_closedLoopMono
    E M hV_S_mono (p.ruleStepF_monotoneOn_of_rule_monotoneOn hDynMono) h_dec
    hσ_antiOn_a hx₀

/-- **Sanction sequences are ordered, general `F`.** The same inputs, read on the
sanctions rather than the states: the myopic regime is sanctioned weakly less in
every period. -/
theorem ruleSanctionsF_myopic_le_dynamicTop_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hDynMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (h_dec : ∀ x ∈ Sanctions.I, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF (p.myopicEquilibriumRule M) x₀ n
          ≤ p.ruleSanctionsF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n :=
  p.dynamicTopSanctionsF_ge_myopicEquilibrium_different_alpha E M hDynMono
    (p.ruleDom_on_of_strictDecreasingDifferences (B := Sanctions.I) E M
      Set.Subset.rfl hV_S_mono h_dec hσ_antiOn_a)
    hx₀

/-- **The forward-looking regime sustains at least as many states.**

Every state the myopic sanction rule holds up, the forward-looking one holds up
too. Cheaper than the path result in a way worth noticing: no monotonicity of
either rule and no invariance is used — only the pointwise rule comparison. -/
theorem selfSustaining_myopic_subset_dynamicTop_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (h_dec : ∀ x ∈ Sanctions.I, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I) :
    Sanctions.selfSustainingSet Sanctions.I (p.myopicEquilibriumRule M)
      ⊆ Sanctions.selfSustainingSet Sanctions.I
          (p.dynamicTopRealizedRule E.V_S E.α) :=
  Sanctions.selfSustainingSet_mono_of_rule_le
    (p.ruleDom_on_of_strictDecreasingDifferences (B := Sanctions.I) E M
      Set.Subset.rfl hV_S_mono h_dec hσ_antiOn_a)

/-- **And it sustains from at least as low a state.**

The infimum ordering the inclusion gives, provided the myopic regime sustains
something at all. This is *not* a statement that either infimum is a basin
boundary — see `Examples/SelfSustainingInfNotCharacterizing.lean`, which refutes
that reading even for a monotone, continuous, feasibility-preserving rule. -/
theorem sInf_selfSustaining_dynamicTop_le_myopic_of_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (h_dec : ∀ x ∈ Sanctions.I, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hne : (Sanctions.selfSustainingSet Sanctions.I
              (p.myopicEquilibriumRule M)).Nonempty) :
    sInf (Sanctions.selfSustainingSet Sanctions.I
            (p.dynamicTopRealizedRule E.V_S E.α))
      ≤ sInf (Sanctions.selfSustainingSet Sanctions.I
                (p.myopicEquilibriumRule M)) :=
  Sanctions.sInf_selfSustainingSet_le_of_rule_le bddBelow_Icc
    (p.ruleDom_on_of_strictDecreasingDifferences (B := Sanctions.I) E M
      Set.Subset.rfl hV_S_mono h_dec hσ_antiOn_a)
    hne


/-! ## 8. One strict leg is enough

§6 composed the two channels with `StrictSCLowerOn.trans`, which forces **both**
legs to be strict. That is more than the economics supports. The
Sender-response-switch channel's sign is not determined by the primitives at all
(`Examples/SenderSwitchSignUndetermined.lean`), so demanding strictness of it is
demanding the most from the leg that can supply the least.

The weak relation of `Foundations/BinaryComparativeStatics.lean` fixes the
asymmetry. The canonical route is:

* the **Target-continuation** leg is *strict* — the incumbent's own valuation of
  the political state makes compliance strictly less attractive;
* the **Sender-switch** leg need only be *weak* — the switch to a forward-looking
  Sender must merely not reverse the comparison.

and the composition is strict, so the conclusion still orders **every** pair of
maximizers rather than only extremal ones. The mirror route, where the switch leg
supplies strictness and the Target leg is weak, is available too but is not the
preferred reading.

A caution that belongs with the weak relation: on its own it orders the argmax
*correspondences*, not arbitrary selections. Strictness on one leg is what
restores the selection-robust conclusion, and that is why one leg must carry
it. -/

/-- **The Sender-switch leg, weakly.** The forward-looking Target facing the
forward-looking Sender is *weakly* single-crossing lower than the same Target
facing the static Sender: the switch does not reverse the compliance comparison,
but it need not sharpen it. Compare `SenderSwitchSCLowerAt`, the strict form. -/
def SenderSwitchWeakSCLowerAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.SCLowerOn
    (p.targetFFObjective E x) (p.targetTMObjective E.V_T x) Sanctions.I

/-- **The Target-continuation leg, weakly.** Compare
`TargetContinuationSCLowerAt`, the strict form. -/
def TargetContinuationWeakSCLowerAt
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.SCLowerOn
    (p.targetTMObjective V_T x) (p.targetMMObjective x) Sanctions.I

/-- **The canonical mixed composition: weak switch, strict Target.**

The Sender-switch channel is only asked not to reverse the comparison; the
Target's own continuation motive supplies the strictness. The conclusion is the
strict relation, so it still orders every pair of maximizers. -/
theorem targetFF_strictSCLower_targetMM_of_switchWeak_targetStrict
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hSwitch : p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : p.TargetContinuationSCLowerAt E.V_T x) :
    Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I :=
  Sanctions.BinaryComparativeStatics.SCLowerOn.trans_strict hSwitch hTarget

/-- **The mirror composition: strict switch, weak Target.** Available, but not
the preferred reading — it asks strictness of the channel whose sign the
primitives do not fix. -/
theorem targetFF_strictSCLower_targetMM_of_switchStrict_targetWeak
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hSwitch : p.SenderSwitchSCLowerAt E x)
    (hTarget : p.TargetContinuationWeakSCLowerAt E.V_T x) :
    Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I :=
  Sanctions.BinaryComparativeStatics.StrictSCLowerOn.trans_weak hSwitch hTarget

/-- **The α-ordering from the canonical mixed route**, in one step, for every
pair of maximizers and with no uniqueness anywhere. -/
theorem alpha_order_dynamic_le_myopic_of_switchWeak_targetStrict
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hSwitch : p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : p.TargetContinuationSCLowerAt E.V_T x) :
    E.α x ≤ M.α x :=
  p.alpha_order_dynamic_le_myopic_of_strictSC E M hx
    (p.targetFF_strictSCLower_targetMM_of_switchWeak_targetStrict E hSwitch hTarget)

/-! ## 9. Local composite dischargers

The conditions above are stated on the objects the proof consumes. This section
supplies them from conditions stated on the *reached* ranges rather than
globally — which matters twice: a global statement assumes behaviour at states
and sanctions the equilibrium never visits, and clipping can destroy a strict
inequality at the boundary while leaving it intact everywhere the play actually
goes.

The Sender-side result is a genuine weakening of what the tree carried. Every
composition in §7 asks for `Monotone E.V_S` — the Sender values entrenchment at
*every* state of `[0,1]`. What the same-action comparison actually needs is that
the Sender's continuation term, read at the current state `x` as a function of
the sanction, does not fall. Global monotonicity of `V_S` plus the baseline
`F_mono_s` is then merely one way to get it. -/

/-- **The Target-continuation channel falls in compliance, at `x`.** Stated on
the composite the proof consumes rather than on its three components
separately. -/
def TargetContinuationAntitoneAt
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  AntitoneOn (p.targetContinuationWedge V_T x) Sanctions.I

/-- The strict form of `TargetContinuationAntitoneAt`. -/
def TargetContinuationStrictAntiAt
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  StrictAntiOn (p.targetContinuationWedge V_T x) Sanctions.I

/-- A falling Target-continuation channel gives the weak leg. -/
theorem targetContinuationWeakSCLower_of_antitone
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (h : p.TargetContinuationAntitoneAt V_T x) :
    p.TargetContinuationWeakSCLowerAt V_T x :=
  Sanctions.BinaryComparativeStatics.sCLowerOn_of_sub_antitoneOn h

/-- A strictly falling Target-continuation channel gives the strict leg — the
one the canonical mixed route needs. -/
theorem targetContinuationStrictSCLower_of_strictAnti
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (h : p.TargetContinuationStrictAntiAt V_T x) :
    p.TargetContinuationSCLowerAt V_T x :=
  Sanctions.BinaryComparativeStatics.strictSCLowerOn_of_sub_strictAntiOn h

/-- **The Sender's continuation term does not fall in the sanction, at `x`.**

Read at the current state only, and only over feasible sanctions. This is what
the same-action Sender-investment comparison needs; `Monotone V_S` is stronger
than necessary because it constrains states the play may never reach. -/
def SenderContinuationMonotoneAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  MonotoneOn (fun s => V_S (Sanctions.clipS' (p.F x s))) Sanctions.I

/-- Global Sender-value monotonicity discharges the local condition, through the
baseline `F_mono_s` and monotonicity of the clip. So the local form is a
weakening, not a different assumption. -/
theorem SenderContinuationMonotoneAt.of_valueMonotone
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (hV : Monotone V_S) (x : ℝ) :
    p.SenderContinuationMonotoneAt V_S x := by
  intro s₁ _ s₂ _ hle
  exact hV (Sanctions.clipS'_mono (p.F_mono_s x hle))

/-- **Every stage maximiser lies weakly below the greatest dynamic maximiser
at the same action — from the local condition only, selection-free.**

If `m ∈ [0, 1]` maximises the stage payoff `U_S(x, a, ·)` on `[0, 1]` and the
Sender's continuation term at `x` does not fall in the sanction
(`SenderContinuationMonotoneAt`), then `m ≤ σ_dyn_top V_S x a`. Economically:
the greatest forward-looking sanction is at least every myopic best response,
not only the one the `Params` selector `σ` picks, under a condition read at the
current state only.

Rule 22: general in `F` (the transition enters only through the continuation
term). The `m`-form of `sigma_dyn_top_ge_sigma_of_senderContinuationMonotoneAt`
(BH6.8, 2026-10-07): the selector `σ` is replaced by any stage maximiser `m`,
which is all that proof read from `σ` (`σ_mem`, `σ_isMaxOn_U_S`). No hypothesis
is added. The comparison stays against `σ_dyn_top`, the greatest dynamic
maximiser: against every dynamic maximiser it would be false.

The argument: suppose the greatest dynamic maximizer `d` sat strictly below
`m`. Stage optimality of `m` makes the stage payoff at `m` at least that at
`d`, and the local continuation condition makes the continuation term at `m`
at least that at `d` as well, so `m` does at least as well as `d` in the
*dynamic* problem. Dynamic optimality of `d` then forces a tie, making `m` a
dynamic maximizer too — and `d`, being the greatest one, must dominate it.
Contradiction. -/
theorem stage_max_le_σ_dyn_top_of_senderContinuationMonotoneAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (hloc : p.SenderContinuationMonotoneAt V_S x) {a m : ℝ}
    (hm_mem : m ∈ Sanctions.I)
    (hmax : IsMaxOn (fun s => p.U_S x a s) Sanctions.I m) :
    m ≤ p.σ_dyn_top V_S x a := by
  set d := p.σ_dyn_top V_S x a with hd
  by_contra hcon
  have hlt : d < m := lt_of_not_ge hcon
  have hd_mem : d ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x a
  -- Abbreviate the continuation term the Sender reads.
  set W : ℝ → ℝ := fun s => V_S (Sanctions.clipS' (p.F x s)) with hW
  -- Stage optimality of the stage maximiser, evaluated at `d`.
  have hstage : p.U_S x a d ≤ p.U_S x a m := hmax hd_mem
  -- Local continuation monotonicity across `d ≤ m`.
  have hcont : W d ≤ W m := hloc hd_mem hm_mem hlt.le
  have hcontβ : p.β_S * W d ≤ p.β_S * W m := by
    exact mul_le_mul_of_nonneg_left hcont p.β_S_mem.1
  -- So `m` does at least as well as `d` in the dynamic problem ...
  have hge : p.U_S x a d + p.β_S * W d ≤ p.U_S x a m + p.β_S * W m := by linarith
  -- ... while dynamic optimality of `d` gives the reverse.
  have hle : p.U_S x a m + p.β_S * W m ≤ p.U_S x a d + p.β_S * W d :=
    p.σ_dyn_top_isMaxOn V_S x a hm_mem
  have heq : p.U_S x a m + p.β_S * W m = p.U_S x a d + p.β_S * W d :=
    le_antisymm hle hge
  -- Hence `m` is itself a dynamic maximizer.
  have hm_max : m ∈ p.dynamicArgmaxSet V_S x a := by
    refine ⟨hm_mem, ?_⟩
    intro y hy
    have h1 : p.U_S x a y + p.β_S * W y ≤ p.U_S x a d + p.β_S * W d :=
      p.σ_dyn_top_isMaxOn V_S x a hy
    show p.U_S x a y + p.β_S * W y ≤ p.U_S x a m + p.β_S * W m
    linarith
  -- The greatest dynamic maximizer therefore dominates it, contradicting `d < m`.
  exact absurd (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a) hm_max) (not_le_of_gt hlt)

/-- **The forward-looking Sender sanctions at least as hard as the static one,
at the same action — from the local condition only.**

Weakens `σ_dyn_top_ge_sigma`, which asks `Monotone V_S` globally. §10 weakens it
again, to a condition read only at the two responses themselves.

General in `F`. Since BH6.8 (2026-10-07) a one-line σ-instance of the
selection-free `stage_max_le_σ_dyn_top_of_senderContinuationMonotoneAt`
(`m := p.σ x a`); statement unchanged. -/
theorem sigma_dyn_top_ge_sigma_of_senderContinuationMonotoneAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (hloc : p.SenderContinuationMonotoneAt V_S x) (a : ℝ) :
    p.σ x a ≤ p.σ_dyn_top V_S x a :=
  p.stage_max_le_σ_dyn_top_of_senderContinuationMonotoneAt V_S hloc (p.σ_mem x a)
    (p.σ_isMaxOn_U_S x a)

/-! ## 10. The weakest same-action Sender condition

§9 replaced global `Monotone V_S` with a condition read at the current state
only. It is still more than the proof consumes. `sigma_dyn_top_ge_sigma` is
established by refuting `d < m`, so the only comparison the argument ever makes
is between the continuation values *at the two responses themselves*, and only in
the branch where the dynamic response sits below the static one.

The condition below says exactly that and nothing more, giving a three-rung
ladder from the global assumption to the pairwise-local one:

    Monotone V_S                        (every state of `[0,1]`)
      → SenderContinuationMonotoneAt    (every feasible sanction at `x`)
        → SenderContinuationOrderAtResponses   (the two responses at `(x,a)`)

Each rung is strictly weaker than the one above, and each implication is proved
below, so nothing that used to be dischargeable stops being so. -/

/-- **The Sender's continuation term does not prefer the dynamic response to the
static one, when the dynamic one is the lower of the two.**

Read at a single state-action pair, and only along the branch the proof of
`sigma_dyn_top_ge_sigma_of_responsePairContinuationOrder` actually examines. This
is the weakest form of the same-action Sender condition in the tree.

The implication is vacuous whenever the conclusion being sought already holds —
which is the point: it constrains the model only in the case that would refute
the comparison. -/
def SenderContinuationOrderAtResponses
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : Prop :=
  p.σ_dyn_top V_S x a ≤ p.σ x a →
    V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)))
      ≤ V_S (Sanctions.clipS' (p.F x (p.σ x a)))

/-- The state-local condition discharges the response-pair one: if the
continuation term is non-decreasing over *all* feasible sanctions at `x`, it is
in particular non-decreasing between the two responses. -/
theorem SenderContinuationOrderAtResponses.of_localMonotone
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x : ℝ}
    (hloc : p.SenderContinuationMonotoneAt V_S x) (a : ℝ) :
    p.SenderContinuationOrderAtResponses V_S x a :=
  fun hle => hloc (p.σ_dyn_top_mem_I V_S x a) (p.σ_mem x a) hle

/-- Global Sender-value monotonicity discharges the response-pair condition too,
through the state-local rung. Stated separately so the ladder's top and bottom
are directly connected. -/
theorem SenderContinuationOrderAtResponses.of_valueMonotone
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (hV : Monotone V_S) (x a : ℝ) :
    p.SenderContinuationOrderAtResponses V_S x a :=
  SenderContinuationOrderAtResponses.of_localMonotone p
    (SenderContinuationMonotoneAt.of_valueMonotone p hV x) a

/-- **The forward-looking Sender sanctions at least as hard as the static one,
at the same action — from the response-pair condition alone.**

The weakest same-action Sender-investment result in the tree. Weakens both
`σ_dyn_top_ge_sigma` (which asks `Monotone V_S` globally) and
`sigma_dyn_top_ge_sigma_of_senderContinuationMonotoneAt` (which asks
monotonicity over every feasible sanction at `x`).

The argument: suppose the greatest dynamic maximizer `d` sat strictly below the
static maximizer `m`. Static optimality makes the stage payoff at `m` at least
that at `d`, and the response-pair condition — whose hypothesis is exactly
`d ≤ m`, now available — makes the continuation term at `m` at least that at `d`.
So `m` does at least as well as `d` in the *dynamic* problem. Dynamic optimality
of `d` then forces a tie, making `m` a dynamic maximizer too, and `d`, being the
greatest one, must dominate it. Contradiction.

Non-negativity of the Sender's discount factor is read off `Params` rather than
taken as an argument: `β_S ∈ [0,1)` is already a field. -/
theorem sigma_dyn_top_ge_sigma_of_responsePairContinuationOrder
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a : ℝ}
    (hpair : p.SenderContinuationOrderAtResponses V_S x a) :
    p.σ x a ≤ p.σ_dyn_top V_S x a := by
  by_contra hcon
  have hlt : p.σ_dyn_top V_S x a < p.σ x a := lt_of_not_ge hcon
  have hm_mem : p.σ x a ∈ Sanctions.I := p.σ_mem x a
  have hd_mem : p.σ_dyn_top V_S x a ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x a
  set W : ℝ → ℝ := fun s => V_S (Sanctions.clipS' (p.F x s)) with hW
  -- Stage optimality of the static response, evaluated at the dynamic one.
  have hstage : p.U_S x a (p.σ_dyn_top V_S x a) ≤ p.U_S x a (p.σ x a) :=
    p.σ_isMaxOn_U_S x a hd_mem
  -- The response-pair condition, on the branch it is stated for.
  have hcont : W (p.σ_dyn_top V_S x a) ≤ W (p.σ x a) := hpair hlt.le
  have hcontβ : p.β_S * W (p.σ_dyn_top V_S x a) ≤ p.β_S * W (p.σ x a) :=
    mul_le_mul_of_nonneg_left hcont p.β_S_mem.1
  have hge : p.U_S x a (p.σ_dyn_top V_S x a) + p.β_S * W (p.σ_dyn_top V_S x a)
      ≤ p.U_S x a (p.σ x a) + p.β_S * W (p.σ x a) := by linarith
  have hle : p.U_S x a (p.σ x a) + p.β_S * W (p.σ x a)
      ≤ p.U_S x a (p.σ_dyn_top V_S x a)
        + p.β_S * W (p.σ_dyn_top V_S x a) :=
    p.σ_dyn_top_isMaxOn V_S x a hm_mem
  -- Hence the static response is itself a dynamic maximizer ...
  have hm_max : p.σ x a ∈ p.dynamicArgmaxSet V_S x a := by
    refine ⟨hm_mem, fun y hy => ?_⟩
    have h1 : p.U_S x a y + p.β_S * W y
        ≤ p.U_S x a (p.σ_dyn_top V_S x a)
          + p.β_S * W (p.σ_dyn_top V_S x a) := p.σ_dyn_top_isMaxOn V_S x a hy
    change p.U_S x a y + p.β_S * W y ≤ p.U_S x a (p.σ x a) + p.β_S * W (p.σ x a)
    linarith
  -- ... and the greatest one dominates it, contradicting `d < m`.
  exact absurd (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a) hm_max)
    (not_le_of_gt hlt)

/-- **Same-α pathwise Goal 2 from the response-pair condition, general in `F`**
(BH2.9, 2026-10-06). If at every feasible state the Sender's continuation term
does not prefer the dynamic response to the static one when the dynamic one is
the lower of the two (`SenderContinuationOrderAtResponses` at `(x, α x)`), and
the forward-looking realised rule is monotone on `[0, 1]`, then from every
feasible start the forward-looking sanction sequence weakly dominates, in every
period, the sequence of the static Sender rule `x ↦ σ(x, α x)` against the same
Target policy `α`, both evolved by `p.F`.

Sharper than `dynamicTopSanctionsF_ge_realizedRule_same_alpha`
(`DifferentPolicyComparator.lean` §11): global `Monotone V_S` is weakened to the
response-pair condition, read only at the two responses and only on `[0, 1]`
(`SenderContinuationOrderAtResponses.of_valueMonotone` recovers that form; see
the `example` below). Nothing is added. Same-α scope as there. -/
theorem dynamicTopSanctionsF_ge_realizedRule_same_alpha_of_responsePair
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {x₀ : ℝ}
    (hpair : ∀ x ∈ Sanctions.I, p.SenderContinuationOrderAtResponses V_S x (α x))
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule V_S α) Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF (p.realizedRule α) x₀ n
        ≤ p.ruleSanctionsF (p.dynamicTopRealizedRule V_S α) x₀ n :=
  p.ruleSanctionsF_le_of_rule_le_and_upper_mono
    (fun x _ => p.realizedRule_mem α x) (fun x _ => p.dynamicTopRealizedRule_mem V_S α x)
    hTopMonoI
    (fun x hx => p.sigma_dyn_top_ge_sigma_of_responsePairContinuationOrder V_S (hpair x hx))
    hx₀

/-- Rule-13 check: the `Monotone V_S` form
(`dynamicTopSanctionsF_ge_realizedRule_same_alpha`) is the response-pair form at
`SenderContinuationOrderAtResponses.of_valueMonotone`. -/
example {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {x₀ : ℝ}
    (hV : Monotone V_S)
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule V_S α) Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF (p.realizedRule α) x₀ n
        ≤ p.ruleSanctionsF (p.dynamicTopRealizedRule V_S α) x₀ n :=
  p.dynamicTopSanctionsF_ge_realizedRule_same_alpha_of_responsePair
    (fun x _ => SenderContinuationOrderAtResponses.of_valueMonotone p hV x (α x))
    hTopMonoI hx₀

/-! ## 11. The mixed route, all the way to paths

§8 stopped at the Target-policy ordering. This section carries the same
weak-switch / strict-Target route through the rest of the chain — realized rule,
state path, sanction path, self-sustaining set — so that the preferred
composition has direct consumers rather than having to be routed through the
older total-wedge condition of §7.

Two assumption-surface differences from §7 are worth naming, because they are
the reason for the duplication rather than incidental to it:

* the ordinal channel conditions replace the cardinal `strictly falling total
  wedge`, so the Sender-switch channel need only *not reverse* the comparison;
* the response-pair condition of §10 replaces global `Monotone V_S`.

Everything else — placation, the comparator's own rule-monotonicity requirement,
invariance — is unchanged, and the general-`F` path comparators are reused rather
than re-derived. -/

/-- **Rule dominance from a Target-policy ordering and the response-pair Sender
condition.**

The `Monotone V_S`-free counterpart of
`ruleDom_on_of_reluctance_and_sigma_antitoneOn`. Two steps: compliance placates,
so the myopic Target's higher compliance draws a weakly lower static sanction
than the forward-looking Target's; and at the forward-looking Target's own
action, the forward-looking Sender sanctions at least as hard as the static
one. -/
theorem ruleDom_on_of_reluctance_and_localSender
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hα_reluctance : ∀ x ∈ B, E.α x ≤ M.α x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSenderPair : ∀ x ∈ B,
      p.SenderContinuationOrderAtResponses E.V_S x (E.α x)) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  intro x hx
  have hxS : x ∈ Sanctions.S := hB_subS hx
  have hceil : p.σ x (M.α x) ≤ p.σ x (E.α x) :=
    hσ_antiOn_a x hx (E.α_mem x hxS) (M.α_mem x hxS) (hα_reluctance x hx)
  exact le_trans hceil
    (p.sigma_dyn_top_ge_sigma_of_responsePairContinuationOrder E.V_S
      (hSenderPair x hx))

/-- **The canonical mixed route to rule dominance.**

Four inputs, each with a direct economic reading:

* `hSwitch` — the Sender-response switch does not *reverse* the Target's
  compliance comparison (weak);
* `hTarget` — the Target's own valuation of the political state makes compliance
  strictly less attractive (strict);
* `hσ_antiOn_a` — compliance placates: the Sender's stage rule is non-increasing
  in the Target's compliance;
* `hSenderPair` — at the forward-looking Target's own action, the Sender's
  continuation term does not prefer the lower of the two responses.

Nothing here asks for uniqueness of any argmax, for a cardinal wedge bound, or
for global monotonicity of the Sender value. -/
theorem ruleDom_on_of_switchWeak_targetStrict_and_localSender
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hSwitch : ∀ x ∈ B, p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : ∀ x ∈ B, p.TargetContinuationSCLowerAt E.V_T x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSenderPair : ∀ x ∈ B,
      p.SenderContinuationOrderAtResponses E.V_S x (E.α x)) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
  p.ruleDom_on_of_reluctance_and_localSender E M hB_subS
    (fun x hx =>
      p.alpha_order_dynamic_le_myopic_of_switchWeak_targetStrict E M
        (hB_subS hx) (hSwitch x hx) (hTarget x hx))
    hσ_antiOn_a hSenderPair

/-- **State paths are ordered on the mixed route, general `F`.** From a common
feasible start, the myopic regime's political state stays weakly below the
forward-looking one in every period.

`hDynMono` is the general-`F` comparator's own requirement — the forward-looking
realized rule is non-decreasing in the state — and is not supplied by the channel
conditions. -/
theorem rulePathF_myopic_le_dynamicTop_of_switchWeak_targetStrict_localSender
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hDynMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (hSwitch : ∀ x ∈ Sanctions.I, p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : ∀ x ∈ Sanctions.I, p.TargetContinuationSCLowerAt E.V_T x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSenderPair : ∀ x ∈ Sanctions.I,
      p.SenderContinuationOrderAtResponses E.V_S x (E.α x))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePathF (p.myopicEquilibriumRule M) x₀ n
          ≤ p.rulePathF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  refine p.rulePathF_le_of_rule_le_and_upper_mono ?_ ?_ hDynMono ?_ hx₀
  · exact fun x _ => p.σ_mem x (M.α x)
  · exact fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x
  · exact p.ruleDom_on_of_switchWeak_targetStrict_and_localSender
      (B := Sanctions.I) E M Set.Subset.rfl hSwitch hTarget hσ_antiOn_a
      hSenderPair

/-- **Sanction sequences are ordered on the mixed route, general `F`.** The same
inputs, read on the sanctions rather than the states. -/
theorem ruleSanctionsF_myopic_le_dynamicTop_of_switchWeak_targetStrict_localSender
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hDynMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (hSwitch : ∀ x ∈ Sanctions.I, p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : ∀ x ∈ Sanctions.I, p.TargetContinuationSCLowerAt E.V_T x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSenderPair : ∀ x ∈ Sanctions.I,
      p.SenderContinuationOrderAtResponses E.V_S x (E.α x))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF (p.myopicEquilibriumRule M) x₀ n
          ≤ p.ruleSanctionsF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n :=
  p.dynamicTopSanctionsF_ge_myopicEquilibrium_different_alpha E M hDynMono
    (p.ruleDom_on_of_switchWeak_targetStrict_and_localSender (B := Sanctions.I)
      E M Set.Subset.rfl hSwitch hTarget hσ_antiOn_a hSenderPair)
    hx₀

/-- **The forward-looking regime sustains at least as many states**, on the mixed
route. No monotonicity of either rule and no invariance is used — only the
pointwise rule comparison. -/
theorem selfSustaining_myopic_subset_dynamicTop_of_switchWeak_targetStrict_localSender
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hSwitch : ∀ x ∈ Sanctions.I, p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : ∀ x ∈ Sanctions.I, p.TargetContinuationSCLowerAt E.V_T x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.I, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hSenderPair : ∀ x ∈ Sanctions.I,
      p.SenderContinuationOrderAtResponses E.V_S x (E.α x)) :
    Sanctions.selfSustainingSet Sanctions.I (p.myopicEquilibriumRule M)
      ⊆ Sanctions.selfSustainingSet Sanctions.I
          (p.dynamicTopRealizedRule E.V_S E.α) :=
  Sanctions.selfSustainingSet_mono_of_rule_le
    (p.ruleDom_on_of_switchWeak_targetStrict_and_localSender (B := Sanctions.I)
      E M Set.Subset.rfl hSwitch hTarget hσ_antiOn_a hSenderPair)

/-! ## 12. Curvature as an optional route to the Sender-switch leg

The two channel conditions of §8 are ordinal, and the Target-continuation one is
signed by `TargetReluctance.lean` from separated primitives. The Sender-switch
one is not signed by the baseline primitives at all
(`Examples/SenderSwitchSignUndetermined.lean`), so it needs a route of its own.

This section supplies one, and it is worth being precise about what it delivers
and what it does not.

**What the mechanism is.** When the Sender's stage payoff is a loss read off the
displacement from its static response, the objects
`Foundations/ArgmaxSensitivity.lean` compares are exactly the Sender's two
responses: the *centre* is the static response `σ(x,a)` and the *maximizer* is
the forward-looking response `σ_dyn_top(x,a)`. The perturbation between them is
the composite continuation term `s ↦ β_S · V_S(F(x,s))`, and its curvature bounds
how far the forward-looking response moves when compliance moves the static one.

**What it does not deliver.** Three separate things, each of which was over-stated
in this tree before the 2026-08-25 audit and is now stated carefully:

* it is *sufficient*, in both directions, and neither converse is proved. A gap
  that fails to widen does not force convexity;
* the curvature required is that of the **composite** `s ↦ β_S · V_S(F(x,s))`,
  not of `V_S` or of `F(x,·)` separately. Curvature of one factor says nothing
  about the composite without a matching monotonicity of the other, and this
  section deliberately states the condition on the composite so the question
  cannot be begged;
* the response gap is **not** the switch channel. The gap is one of five inputs
  to `switchWedge_antitoneOn_of_gap_and_shapeOn`; the other four are shape
  conditions on the Target's complete sanction payoff. A theorem about the gap is
  not a sign theorem for the channel, and only the assembled result at the end of
  this section reaches `SenderSwitchWeakSCLowerAt`.

**Which direction helps.** Placation makes the static response *fall* in
compliance, so rising compliance *lowers* the centre. Reading the Foundations
results at that orientation: a **convex** composite continuation makes the gap
non-increasing in compliance, which is the direction
`switchWedge_antitoneOn_of_gap_and_shapeOn` consumes; a **concave** one makes it
non-decreasing, which is the adverse case.

**Chords, not curvature.** The primitive form of the condition is the *chord*
one, and the curvature form is a discharger for it. That ordering is not
cosmetic. What the argument consumes is a single four-point inequality — one
chord of the composite, compared against the same chord translated along the
sanction axis — and stating it that way has three consequences the curvature
form obscures:

* it constrains `V_S` only at the states `F x ·` can actually produce, so it is
  genuinely weaker than convexity of `V_S`;
* equal steps in the sanction need not be equal steps in the successor state, so
  even on the reachable set it is not the same condition as convexity of `V_S`
  there;
* it is an order condition, which is the idiom the rest of this development
  already runs on.

Imposed on every feasible chord of a continuous composite, it *is* equivalent to
convexity of the composite — no weakening is claimed in that regime. The
weakening is available because the comparison visits only the chords its own two
responses generate. -/

/-- **The Sender's composite continuation term at a state**, as a function of the
sanction: the discounted value of the political state that sanction induces. The
curvature conditions below are stated on this object rather than on `V_S` and
`F` separately, precisely so that no inference from one factor to the composite
is smuggled in. -/
noncomputable def senderContinuationTerm
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : ℝ → ℝ :=
  fun s => p.β_S * V_S (Sanctions.clipS' (p.F x s))

/-- The composite Sender continuation term is convex in the sanction, over
feasible sanctions at `x`. The favourable curvature case. -/
def SenderContinuationConvexAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ConvexOn ℝ Sanctions.I (p.senderContinuationTerm V_S x)

/-- The composite Sender continuation term is concave in the sanction, over
feasible sanctions at `x`. The adverse curvature case. -/
def SenderContinuationConcaveAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ConcaveOn ℝ Sanctions.I (p.senderContinuationTerm V_S x)

/-- **The Sender's composite continuation term has increasing translated
chords at `x`.**

The primitive form of the favourable condition: across feasible sanctions, the
increment of the composite over a chord of any fixed length does not fall as the
chord moves right. `SenderContinuationConvexAt` discharges it, and is strictly
stronger. -/
def SenderContinuationIncreasingChordsAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  Sanctions.IncreasingChordsOn (p.senderContinuationTerm V_S x) Sanctions.I

/-- **The Sender's composite continuation term has decreasing translated chords
at `x`.** The primitive form of the adverse condition; discharged by
`SenderContinuationConcaveAt`. -/
def SenderContinuationDecreasingChordsAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  Sanctions.DecreasingChordsOn (p.senderContinuationTerm V_S x) Sanctions.I

/-- Convexity of the composite discharges the increasing-chord condition. -/
theorem SenderContinuationIncreasingChordsAt.of_convex
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x : ℝ}
    (h : p.SenderContinuationConvexAt V_S x) :
    p.SenderContinuationIncreasingChordsAt V_S x :=
  Sanctions.ConvexOn.increasingChordsOn h

/-- Concavity of the composite discharges the decreasing-chord condition. -/
theorem SenderContinuationDecreasingChordsAt.of_concave
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x : ℝ}
    (h : p.SenderContinuationConcaveAt V_S x) :
    p.SenderContinuationDecreasingChordsAt V_S x :=
  Sanctions.ConcaveOn.decreasingChordsOn h

/-- **An affine composite satisfies both chord conditions**, with equality — the
knife edge, at which the response gap is exactly constant in compliance
(`responseGap_eq_of_senderContinuationChords`).

Stated on the composite `s ↦ β_S · V_S (F (x, s))`, so it covers every economy
whose Sender value and transition compose to an affine function of the sanction
over the feasible sanctions `[0,1]`, however either factor is individually
shaped. General in `F`.

Restated on `[0,1]` in BG1.9 (2026-10-06). The hypothesis used to ask the
composite to be affine on all of `ℝ`; because `V_S` is bounded, that forced
`c = 0`, so the old lemma covered only constant composites. Only the values at
the four feasible chord endpoints are read, so affinity on `[0,1]` suffices. -/
theorem senderContinuationChords_of_affine
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x c b : ℝ}
    (h : ∀ s ∈ Sanctions.I, p.senderContinuationTerm V_S x s = c * s + b) :
    p.SenderContinuationIncreasingChordsAt V_S x
      ∧ p.SenderContinuationDecreasingChordsAt V_S x := by
  constructor
  · intro u v k hu hv huk hvk _ _
    rw [h u hu, h v hv, h _ huk, h _ hvk]
    exact le_of_eq (by ring)
  · intro u v k hu hv huk hvk _ _
    rw [h u hu, h v hv, h _ huk, h _ hvk]
    exact le_of_eq (by ring)

/-- **The Sender's stage payoff is a translated loss at `x`.**

There is a fixed `g` such that the Sender's stage payoff at compliance `a` is
`g` evaluated at the displacement of the sanction from the static response. This
is a genuine restriction on the model class — it says the Sender's compliance
only *relocates* its stage problem without reshaping it — and it is a hypothesis
of the optional route below, never a `Params` field. `g` is arbitrary: no
functional form, no smoothness, and no concavity is assumed of it, and it may
depend on `x`.

Compliance is quantified over `[0,1]` rather than over `ℝ`, which is all the
proof reads and is not a cosmetic restriction: when the static response is a
clipped ideal point — the usual case — the identity fails outside the feasible
range, so the unrestricted form would be unsatisfiable for models this route is
meant to cover. -/
def TranslatedLossSenderAt (x : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a ∈ Sanctions.I, ∀ s, p.U_S x a s = g (s - p.σ x a)

/-- **The Sender's stage payoff has translated-loss *differences* at `x`.**

The weakening the exchange argument actually needs. Only *differences* of the
Sender's stage payoff across two feasible sanctions are pinned to `g`, so an
arbitrary compliance-dependent level `C(x,a)` is admitted and cancels from every
comparison. Two things are relaxed at once relative to
`TranslatedLossSenderAt`: the level, and the range of sanctions, which is now the
feasible interval rather than all of `ℝ`.

The level matters economically. A Sender whose payoff is a displacement loss
*plus* a compliance-dependent benefit — the usual way a model records that
compliance is worth something in itself — satisfies this and not the exact-level
form. Nothing in the response comparison can see that benefit, because it is the
same at every sanction.

Every theorem below consumes this form; `TranslatedLossSenderAt.toDifferences`
converts, so nothing that discharged the stronger version is lost. -/
def TranslatedLossSenderDifferencesAt (x : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I,
    p.U_S x a s₂ - p.U_S x a s₁ = g (s₂ - p.σ x a) - g (s₁ - p.σ x a)

/-- The exact-level form implies the difference form, so the weakening costs
nothing downstream. -/
theorem TranslatedLossSenderAt.toDifferences {p : Sanctions.AbstractGame.Params}
    {x : ℝ} {g : ℝ → ℝ} (h : p.TranslatedLossSenderAt x g) :
    p.TranslatedLossSenderDifferencesAt x g := by
  intro a ha s₁ _ s₂ _
  rw [h a ha s₁, h a ha s₂]

/-- **The re-centred stage objective has the same maximisers as the real one.**

The bridge that makes the difference form usable: on the feasible interval the
Sender's true objective and the `g`-written one differ by a constant in the
sanction, so they are maximised at exactly the same points. This is the only
place the translated-loss hypothesis is consumed, and it is consumed as an
`IsMaxOn` transfer rather than as an equality of functions — which is precisely
why the level may be left free. -/
theorem isMaxOn_translated_iff_of_differences
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    {a : ℝ} (ha : a ∈ Sanctions.I) {y : ℝ} (hy : y ∈ Sanctions.I) :
    IsMaxOn (fun s => g (s - p.σ x a) + p.senderContinuationTerm V_S x s)
        Sanctions.I y
      ↔ IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) Sanctions.I y := by
  constructor
  · intro h s hs
    have hd := hform a ha y hy s hs
    have hmax : g (s - p.σ x a) + p.senderContinuationTerm V_S x s
        ≤ g (y - p.σ x a) + p.senderContinuationTerm V_S x y := h hs
    show p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
      ≤ p.U_S x a y + p.β_S * V_S (Sanctions.clipS' (p.F x y))
    simp only [senderContinuationTerm] at hmax
    linarith
  · intro h s hs
    have hd := hform a ha y hy s hs
    have hmax : p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
        ≤ p.U_S x a y + p.β_S * V_S (Sanctions.clipS' (p.F x y)) := h hs
    show g (s - p.σ x a) + p.senderContinuationTerm V_S x s
      ≤ g (y - p.σ x a) + p.senderContinuationTerm V_S x y
    simp only [senderContinuationTerm]
    linarith

/-- **The shift-translated response candidates stay feasible at `x`.**

The exchange argument offers each response, translated by the movement of the
static response, as a candidate in the other compliance's problem. This says
those two translates remain in `[0,1]`. It is a real hypothesis and not free —
a response sitting at a boundary can have its translate pushed outside. -/
def ResponseTranslatesFeasibleAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ ≤ a₂ →
    p.σ_dyn_top V_S x a₂ + (p.σ x a₁ - p.σ x a₂) ∈ Sanctions.I ∧
      p.σ_dyn_top V_S x a₁ - (p.σ x a₁ - p.σ x a₂) ∈ Sanctions.I

/-- **Increasing chords of the composite keep the response gap from widening in
compliance.** The favourable direction, in its primitive form, and the one
`switchWedge_antitoneOn_of_gap_and_shapeOn` consumes.

Sufficient only: nothing here says a non-widening gap forces the chord
condition. -/
theorem responseGap_antitoneOn_of_senderContinuationIncreasingChordsAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hconv : p.SenderContinuationIncreasingChordsAt V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x) :
    AntitoneOn (fun a => p.σ_dyn_top V_S x a - p.σ x a) Sanctions.I := by
  intro a₁ h₁ a₂ h₂ hle
  have hm : p.σ x a₂ ≤ p.σ x a₁ := hσ_anti h₁ h₂ hle
  obtain ⟨hsh₁, hsh₂⟩ := hfeas a₁ h₁ a₂ h₂ hle
  have hmax₁ : IsMaxOn (fun s => g (s - p.σ x a₂)
      + p.senderContinuationTerm V_S x s) Sanctions.I
      (p.σ_dyn_top V_S x a₂) :=
    (p.isMaxOn_translated_iff_of_differences V_S hform h₂
      (p.σ_dyn_top_mem_I V_S x a₂)).2 (p.σ_dyn_top_isMaxOn V_S x a₂)
  have hmax₂ : IsMaxOn (fun s => g (s - p.σ x a₁)
      + p.senderContinuationTerm V_S x s) Sanctions.I
      (p.σ_dyn_top V_S x a₁) :=
    (p.isMaxOn_translated_iff_of_differences V_S hform h₁
      (p.σ_dyn_top_mem_I V_S x a₁)).2 (p.σ_dyn_top_isMaxOn V_S x a₁)
  have hgreat : ∀ y ∈ Sanctions.I,
      IsMaxOn (fun s => g (s - p.σ x a₁)
        + p.senderContinuationTerm V_S x s) Sanctions.I y →
      y ≤ p.σ_dyn_top V_S x a₁ := by
    intro y hy hmax
    exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a₁)
      ⟨hy, (p.isMaxOn_translated_iff_of_differences V_S hform h₁ hy).1 hmax⟩
  have hge := Sanctions.argmax_shift_ge_of_increasingChords_of_upperGreatest
    hconv (p.σ_dyn_top_mem_I V_S x a₂) (p.σ_dyn_top_mem_I V_S x a₁) hm hsh₁ hsh₂
    hmax₁ hmax₂ hgreat
  simp only
  linarith

/-- **Decreasing chords of the composite make the response gap widen in
compliance.** The adverse direction: the forward-looking Sender's extra bite
grows precisely where the Target is complying more.

Sufficient only, and — like its mirror — a statement about the *gap*, not about
the sign of the Sender-switch channel. -/
theorem responseGap_monotoneOn_of_senderContinuationDecreasingChordsAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hconc : p.SenderContinuationDecreasingChordsAt V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x) :
    MonotoneOn (fun a => p.σ_dyn_top V_S x a - p.σ x a) Sanctions.I := by
  intro a₁ h₁ a₂ h₂ hle
  have hm : p.σ x a₂ ≤ p.σ x a₁ := hσ_anti h₁ h₂ hle
  obtain ⟨hsh₁, hsh₂⟩ := hfeas a₁ h₁ a₂ h₂ hle
  have hmax₁ : IsMaxOn (fun s => g (s - p.σ x a₂)
      + p.senderContinuationTerm V_S x s) Sanctions.I
      (p.σ_dyn_top V_S x a₂) :=
    (p.isMaxOn_translated_iff_of_differences V_S hform h₂
      (p.σ_dyn_top_mem_I V_S x a₂)).2 (p.σ_dyn_top_isMaxOn V_S x a₂)
  have hmax₂ : IsMaxOn (fun s => g (s - p.σ x a₁)
      + p.senderContinuationTerm V_S x s) Sanctions.I
      (p.σ_dyn_top V_S x a₁) :=
    (p.isMaxOn_translated_iff_of_differences V_S hform h₁
      (p.σ_dyn_top_mem_I V_S x a₁)).2 (p.σ_dyn_top_isMaxOn V_S x a₁)
  have hgreat : ∀ y ∈ Sanctions.I,
      IsMaxOn (fun s => g (s - p.σ x a₂)
        + p.senderContinuationTerm V_S x s) Sanctions.I y →
      y ≤ p.σ_dyn_top V_S x a₂ := by
    intro y hy hmax
    exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a₂)
      ⟨hy, (p.isMaxOn_translated_iff_of_differences V_S hform h₂ hy).1 hmax⟩
  have hle := Sanctions.argmax_shift_le_of_decreasingChords_of_lowerGreatest
    hconc (p.σ_dyn_top_mem_I V_S x a₂) (p.σ_dyn_top_mem_I V_S x a₁) hm hsh₁ hsh₂
    hmax₁ hmax₂ hgreat
  simp only
  linarith

/-- The curvature form of the favourable route, as a corollary of the chord
form. Kept because convexity is often the premise in hand. -/
theorem responseGap_antitoneOn_of_senderContinuationConvexAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hconv : p.SenderContinuationConvexAt V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x) :
    AntitoneOn (fun a => p.σ_dyn_top V_S x a - p.σ x a) Sanctions.I :=
  p.responseGap_antitoneOn_of_senderContinuationIncreasingChordsAt V_S hform
    (SenderContinuationIncreasingChordsAt.of_convex p hconv) hσ_anti hfeas

/-- The curvature form of the adverse route, as a corollary of the chord
form. -/
theorem responseGap_monotoneOn_of_senderContinuationConcaveAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hconc : p.SenderContinuationConcaveAt V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x) :
    MonotoneOn (fun a => p.σ_dyn_top V_S x a - p.σ x a) Sanctions.I :=
  p.responseGap_monotoneOn_of_senderContinuationDecreasingChordsAt V_S hform
    (SenderContinuationDecreasingChordsAt.of_concave p hconc) hσ_anti hfeas

/-- **The knife edge: both chord conditions pin the response gap.** If the
composite continuation term has both increasing and decreasing translated
chords at `x` — every chord of a given length has the same increment, as for a
composite affine on `[0,1]` — then the dynamic-versus-static response gap
`σ_dyn_top − σ` takes the same value at every pair of feasible compliance
levels. In plain terms: when the Sender's continuation stake responds to the
sanction at a constant rate, compliance shifts the forward-looking and the
static responses by exactly the same amount, so the extra bite from looking
ahead neither widens nor narrows.

Both directions of the chord comparison, composed; sufficient only. General in
`F`: no transition form is assumed, only the chord conditions on the composite.
The affine instance (`Examples/AffineChordKnifeEdge.lean`,
`affine_responseGap_constant`) is a corollary (BG1.9, 2026-10-06). -/
theorem responseGap_eq_of_senderContinuationChords
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hinc : p.SenderContinuationIncreasingChordsAt V_S x)
    (hdec : p.SenderContinuationDecreasingChordsAt V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x)
    {a₁ a₂ : ℝ} (h₁ : a₁ ∈ Sanctions.I) (h₂ : a₂ ∈ Sanctions.I) :
    p.σ_dyn_top V_S x a₂ - p.σ x a₂ = p.σ_dyn_top V_S x a₁ - p.σ x a₁ := by
  have key : ∀ b₁ ∈ Sanctions.I, ∀ b₂ ∈ Sanctions.I, b₁ ≤ b₂ →
      p.σ_dyn_top V_S x b₂ - p.σ x b₂ = p.σ_dyn_top V_S x b₁ - p.σ x b₁ := by
    intro b₁ hb₁ b₂ hb₂ hle
    have hup :=
      p.responseGap_antitoneOn_of_senderContinuationIncreasingChordsAt V_S hform
        hinc hσ_anti hfeas hb₁ hb₂ hle
    have hdown :=
      p.responseGap_monotoneOn_of_senderContinuationDecreasingChordsAt V_S hform
        hdec hσ_anti hfeas hb₁ hb₂ hle
    simp only at hup hdown
    linarith
  rcases le_total a₁ a₂ with hle | hle
  · exact key a₁ h₁ a₂ h₂ hle
  · exact (key a₂ h₂ a₁ h₁ hle).symm

/-- **The Sender-switch channel is a switch wedge in the abstract sense**, with
the Target's complete sanction payoff as the payoff and the two Sender responses
as the two selections. Definitional; recorded so the Foundations shape theorem
applies without any further bookkeeping. -/
theorem senderSwitchWedge_eq_switchWedge
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) :
    p.senderSwitchWedge E x a
      = Sanctions.BinaryComparativeStatics.switchWedge
          (p.targetSanctionObjective E.V_T x) (p.σ x)
          (fun a' => p.σ_dyn_top E.V_S x a') a := rfl

/-- **A falling Sender-switch channel gives the weak leg.** One step, through the
gap form of single-crossing lower dominance. -/
theorem senderSwitchWeakSCLower_of_wedge_antitone
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (h : AntitoneOn (p.senderSwitchWedge E x) Sanctions.I) :
    p.SenderSwitchWeakSCLowerAt E x :=
  Sanctions.BinaryComparativeStatics.sCLowerOn_of_sub_antitoneOn h

/-- **The complete optional route to the weak Sender-switch leg.**

Assembles the two halves. From the gap side: a translated-loss Sender stage
payoff, a convex composite continuation, placation, and translated-candidate
feasibility give a non-widening response gap. From the Target side: the complete
sanction payoff is non-decreasing in the sanction, convex in it in chord form,
and has decreasing differences against compliance — all three confined to
feasible sanctions.

Together with `σ ≤ σ_dyn_top` (which §10 supplies from the response-pair
condition) these give a falling switch wedge and hence the weak leg that the
canonical mixed composition of §8 consumes.

The assumptions are substantive and are meant to stay visible. This is one
sufficient route among possible others, not a derivation of the channel's sign
from the baseline primitives — which `Examples/SenderSwitchSignUndetermined.lean`
shows is impossible. -/
theorem senderSwitchWeakSCLower_of_convexContinuation_and_targetShape
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hconv : p.SenderContinuationIncreasingChordsAt E.V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt E.V_S x)
    (hmd : ∀ a ∈ Sanctions.I, p.σ x a ≤ p.σ_dyn_top E.V_S x a)
    (hQ_mono : ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I,
      s₁ ≤ s₂ → p.targetSanctionObjective E.V_T x a s₁
        ≤ p.targetSanctionObjective E.V_T x a s₂)
    (hQ_chord : ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I,
      ∀ t, s₁ ≤ s₂ → 0 ≤ t → s₁ + t ∈ Sanctions.I → s₂ + t ∈ Sanctions.I →
      p.targetSanctionObjective E.V_T x a s₂
          - p.targetSanctionObjective E.V_T x a s₁
        ≤ p.targetSanctionObjective E.V_T x a (s₂ + t)
          - p.targetSanctionObjective E.V_T x a (s₁ + t))
    (hQ_dd : ∀ aL ∈ Sanctions.I, ∀ aH ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I,
      ∀ s₂ ∈ Sanctions.I, aL ≤ aH → s₁ ≤ s₂ →
      p.targetSanctionObjective E.V_T x aH s₂
          - p.targetSanctionObjective E.V_T x aH s₁
        ≤ p.targetSanctionObjective E.V_T x aL s₂
          - p.targetSanctionObjective E.V_T x aL s₁) :
    p.SenderSwitchWeakSCLowerAt E x := by
  have hgap :=
    p.responseGap_antitoneOn_of_senderContinuationIncreasingChordsAt E.V_S
      hform hconv hσ_anti hfeas
  refine p.senderSwitchWeakSCLower_of_wedge_antitone E ?_
  intro aL haL aH haH hle
  have := Sanctions.BinaryComparativeStatics.switchWedge_antitoneOn_of_gap_and_shapeOn
    (Q := p.targetSanctionObjective E.V_T x) (m := p.σ x)
    (d := fun a' => p.σ_dyn_top E.V_S x a') (A := Sanctions.I) (S := Sanctions.I)
    Set.ordConnected_Icc
    (fun a _ => p.σ_mem x a) (fun a _ => p.σ_dyn_top_mem_I E.V_S x a)
    hQ_mono hQ_chord hQ_dd
    (fun a₁ h₁ a₂ h₂ h => hσ_anti h₁ h₂ h) hmd
    (fun a₁ h₁ a₂ h₂ h => hgap h₁ h₂ h)
    haL haH hle
  simpa only [p.senderSwitchWedge_eq_switchWedge E x] using this

/-! ## 13. The ordinal route to a non-widening response gap

§12 signs the response gap from a *chord* condition on the Sender's composite
continuation term. That condition is cardinal — it compares differences — and
this section replaces it with an ordinal one, which is strictly weaker and is
the idiom the rest of the development runs on.

**The idea.** Re-centre the Sender's problem on its own static response. Writing
`z = s - σ(x,a)`, the dynamic objective becomes

    Ψ(a, z)  =  U_S(x, a, σ(x,a) + z)  +  β_S · V_S(F(x, σ(x,a) + z))

and the response gap at compliance `a` is exactly the maximiser `z*(a)`. So the
gap fails to widen precisely when `z*` is antitone in compliance — a monotone
comparative-statics question, for which `Foundations/BinaryComparativeStatics`
already supplies the argmax half (`greatest_argmax_le_of_sCLowerOn`). What is
needed is single-crossing lower dominance of the re-centred objective, and
nothing cardinal.

**Why this is a weakening and not a relabelling.** Increasing chords of the
composite imply *decreasing differences* of `Ψ` in `(a, z)`, which imply
single-crossing differences; neither converse holds, since single crossing
survives an arbitrary strictly increasing transformation of `Ψ` and decreasing
differences does not. `recentredSCLowerAt_of_increasingChords` below proves the
first implication, so nothing that discharged the §12 condition stops working.

Two things are worth stating precisely, because both are easy to get wrong.

*The stage payoff does not drop out by itself.* Single-crossing differences are
not preserved by adding a function of `z` alone, so the condition has to be
stated on the whole re-centred objective rather than on the continuation term.
What the translated-loss hypothesis buys is that in the *cardinal* difference
`Ψ(aH, ·) - Ψ(aL, ·)` the stage terms cancel exactly, which is what makes the
bridge from chords go through.

*The two compliance levels do not maximise over the same set.* The feasible
displacements at `a` are `[-σ(x,a), 1 - σ(x,a)]`, which moves with `a`. The
comparison therefore runs on the common window `responseWindow`, and the fact
that both re-centred responses land inside it is supplied by
`ResponseTranslatesFeasibleAt` — the *same* hypothesis §12 already carries, with
no new feasibility assumption. `responseGap_mem_responseWindow` is that
accounting.

Dekel, Quah and Sinander (*Econometrica* 2025) put the underlying point well:
monotonicity-type conditions govern the **direction** of adjustment, curvature
governs its **speed**. The comparison here is a direction result, so it should
not be resting on a curvature condition. -/

/-- **The Sender's dynamic objective, re-centred on its static response.**

`z` is the displacement of the sanction from the static best response, so the
response gap at compliance `a` is the maximiser of `recentredSenderObjective` in
`z`. Definitionally the §12 objective evaluated at `s = σ(x,a) + z`. -/
noncomputable def recentredSenderObjective
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a z : ℝ) : ℝ :=
  p.U_S x a (p.σ x a + z)
    + p.senderContinuationTerm V_S x (p.σ x a + z)

/-- **The displacement window common to two compliance levels.**

`[-σ(x,aH), 1 - σ(x,aL)]`. When compliance placates — so `σ(x,aH) ≤ σ(x,aL)` —
this sits inside the feasible displacement range of *both* levels, which is what
lets a single monotone-comparative-statics argument see both problems at once. -/
def responseWindow (x aL aH : ℝ) : Set ℝ :=
  Set.Icc (-(p.σ x aH)) (1 - p.σ x aL)

/-- Every displacement in the common window is feasible at both compliance
levels. Placation is the whole input. -/
theorem responseWindow_shift_mem {x aL aH : ℝ} (hσ : p.σ x aH ≤ p.σ x aL)
    {z : ℝ} (hz : z ∈ p.responseWindow x aL aH) :
    p.σ x aL + z ∈ Sanctions.I ∧ p.σ x aH + z ∈ Sanctions.I := by
  obtain ⟨hz0, hz1⟩ := hz
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **Both re-centred responses lie in the common window** — and the two
non-trivial bounds are exactly the two clauses of `ResponseTranslatesFeasibleAt`.

No new feasibility hypothesis is needed for the ordinal route: the condition
§12 already carries says precisely that the up-translate of the higher-compliance
response and the down-translate of the lower-compliance one stay feasible, and
those are the same two inequalities. -/
theorem responseGap_mem_responseWindow
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x aL aH : ℝ}
    (hL : aL ∈ Sanctions.I) (hH : aH ∈ Sanctions.I) (hle : aL ≤ aH)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x) :
    p.σ_dyn_top V_S x aH - p.σ x aH ∈ p.responseWindow x aL aH
      ∧ p.σ_dyn_top V_S x aL - p.σ x aL ∈ p.responseWindow x aL aH := by
  obtain ⟨h1, h2⟩ := hfeas aL hL aH hH hle
  have hHmem := p.σ_dyn_top_mem_I V_S x aH
  have hLmem := p.σ_dyn_top_mem_I V_S x aL
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := hHmem.1; linarith
  · have := h1.2; linarith
  · have := h2.1; linarith
  · have := hLmem.2; linarith

/-- **The ordinal Sender-side condition.**

At two compliance levels, the re-centred dynamic objective at the *higher* level
is single-crossing lower than at the lower one, over the window they share.
Ordinal, and strictly weaker than the chord condition of §12. -/
def RecentredSCLowerAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x aL aH : ℝ) : Prop :=
  Sanctions.BinaryComparativeStatics.SCLowerOn
    (p.recentredSenderObjective V_S x aH)
    (p.recentredSenderObjective V_S x aL)
    (p.responseWindow x aL aH)

/-! ### The full-objective discharger

The condition above is ordinal, which is the right level for a *direction*
result. But a model rarely delivers an ordinal fact directly; what it delivers
is a cardinal one — a difference with a sign. The two theorems here are that
bridge, and they are the whole of what `suggestions/27` calls the
"total-difference route": they are corollaries of the cardinal-to-ordinal
lemmas already in `Foundations/BinaryComparativeStatics.lean`.

What matters is *which* object carries the condition. It is the **difference of
the two complete re-centred objectives** — stage payoff and continuation
together — and not either piece separately. That restriction is not fastidious.
Single crossing is not preserved by addition: Quah and Strulovici (*Econometrica*
2012) study exactly when aggregation is safe and exhibit the failures otherwise.
So a proof that signed the re-centred stage payoff and the re-centred
continuation one at a time, and then added them, would not be a proof. -/

/-- **The re-centred difference is non-increasing ⟹ the ordinal condition.**

`D(z) = Ψ_{aH}(z) − Ψ_{aL}(z)`, the amount by which the higher-compliance
problem prefers displacement `z` over what the lower-compliance problem does. If
raising the displacement never raises `D`, the higher-compliance problem is
single-crossing lower, and the response gap does not widen.

Stated on the full objectives; no decomposition, no curvature, and no
translated-loss equality. -/
def RecentredTotalDifferenceAntitoneAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x aL aH : ℝ) : Prop :=
  AntitoneOn
    (fun z => p.recentredSenderObjective V_S x aH z
      - p.recentredSenderObjective V_S x aL z)
    (p.responseWindow x aL aH)

/-- The strict sibling: a strictly falling difference gives the strict order. -/
def RecentredTotalDifferenceStrictAntiAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x aL aH : ℝ) : Prop :=
  StrictAntiOn
    (fun z => p.recentredSenderObjective V_S x aH z
      - p.recentredSenderObjective V_S x aL z)
    (p.responseWindow x aL aH)

/-- **Weak discharge.** The cardinal condition implies the ordinal one. -/
theorem recentredSCLowerAt_of_totalDifferenceAntitone
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x aL aH : ℝ}
    (h : p.RecentredTotalDifferenceAntitoneAt V_S x aL aH) :
    p.RecentredSCLowerAt V_S x aL aH :=
  Sanctions.BinaryComparativeStatics.sCLowerOn_of_sub_antitoneOn h

/-- **Strict discharge.** A strictly falling difference gives the strict
relation, which is what a *strictly* non-widening gap needs. -/
theorem recentredStrictSCLowerAt_of_totalDifferenceStrictAnti
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x aL aH : ℝ}
    (h : p.RecentredTotalDifferenceStrictAntiAt V_S x aL aH) :
    Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.recentredSenderObjective V_S x aH)
      (p.recentredSenderObjective V_S x aL)
      (p.responseWindow x aL aH) :=
  Sanctions.BinaryComparativeStatics.strictSCLowerOn_of_sub_strictAntiOn h

/-- The strict route also delivers the weak condition, so a model supplying the
strict difference need not supply the weak one separately. -/
theorem recentredSCLowerAt_of_totalDifferenceStrictAnti
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x aL aH : ℝ}
    (h : p.RecentredTotalDifferenceStrictAntiAt V_S x aL aH) :
    p.RecentredSCLowerAt V_S x aL aH :=
  (p.recentredStrictSCLowerAt_of_totalDifferenceStrictAnti h).toSCLowerOn

/-- **The chord inequality the exchange argument actually generates.**

`SenderContinuationIncreasingChordsAt` quantifies over *every* translated chord
of the composite continuation in `[0,1]`. The proof below reads far less: only
chords based at the two static responses `σ(x,aL)` and `σ(x,aH)`, and only shifts
inside the response window that the two compliance levels generate. This
predicate says exactly that.

Two restrictions relative to the all-chord form, and it is worth being exact
about which one does the work, because the obvious answer is wrong. The base
points are a *pair* rather than every ordered pair in `[0,1]`, and the increments
range over the response window rather than over every feasible shift. Neither is
finiteness — the window is an interval, so the family is a continuum.

Unfolding says what the condition is. Write `sH = σ(x,aH)`, `sL = σ(x,aL)`, and
`Δ = sL - sH ≥ 0` for the placation gap, and substitute `u = sH + z`. As `z`
ranges over the window, `u` ranges over `[0, 1-Δ]`, and the inequality becomes

    T(u + Δ) - T(u)  ≤  T(u' + Δ) - T(u')     for u ≤ u' in [0, 1-Δ],

that is: **the `Δ`-difference of the continuation term is non-decreasing**. One
lag, and that lag is the placation gap the two compliance levels generate.
`IncreasingChordsOn` quantifies over *every* lag, which for a continuous function
on an interval is convexity. So the weakening is a restriction from all lags to
one, and not a restriction of the affine group at all.

That correction matters for how a separating witness is built. Tabor and Tabor
(*Studia Math.* 192 (2009), 29--37, Theorem 2) show that a linear inequality
valid for all convex functions and closed under affine reparametrisation
characterises convexity, so the all-chord condition on a continuous composite is
*equivalent* to convexity and cannot be weakened while keeping the whole group.
Their Remark 2 exhibits the escape — a function satisfying the sub-mean-value
inequality for every affine *similarity* while failing convexity — but that
example is `g(x₁,x₂) = x₁² - x₂²` on `ℝ²`, and it works because `g` is harmonic.
It does not transplant here: in one dimension the corresponding inequality is
midpoint convexity, and a continuous midpoint-convex function on an interval is
convex. The single-lag reading is the one that gives room, and a `Δ`-periodic
continuation term is the cheapest way to use it, since its `Δ`-difference
vanishes identically.

**Witnessed as strictly weaker** (Rule 9B).
`Sanctions/Examples/GeneratedChordStrictlyWeaker.lean` exhibits an economy whose
continuation term satisfies this condition while failing the all-chord condition
of §12, so the implication below does not reverse and the ladder rung is a real
weakening rather than a restatement. -/
def SenderContinuationGeneratedChordAt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x aL aH : ℝ) : Prop :=
  ∀ z ∈ p.responseWindow x aL aH, ∀ z' ∈ p.responseWindow x aL aH, z ≤ z' →
    p.senderContinuationTerm V_S x (p.σ x aH + z')
        - p.senderContinuationTerm V_S x (p.σ x aH + z)
      ≤ p.senderContinuationTerm V_S x (p.σ x aL + z')
        - p.senderContinuationTerm V_S x (p.σ x aL + z)

/-- **What the generated condition actually says: one lag, and it is the
placation gap.**

The docstring above reads the definition; this proves the reading. Substituting
`u = σ(x,aH) + z` carries the response window bijectively onto `[0, 1 - Δ]`,
where `Δ = σ(x,aL) - σ(x,aH)` is the gap between the two static responses, and
carries the second base point to `u + Δ`. The condition becomes: the
`Δ`-difference of the composite continuation term is non-decreasing.

That is the whole content of the weakening. `SenderContinuationIncreasingChordsAt`
asks the same of *every* lag `h`, which for a continuous function on an interval
is convexity; the generated condition asks it of the single lag the two
compliance levels themselves generate. So what buys the weakening is the
restriction from all lags to one — not, as one might expect from
`TaborTabor2009`, a restriction of the group of affine reparametrisations.

The equivalence needs no sign on the gap: it is a bijective reindexing, and
placation is what makes the window non-degenerate, not what makes the two
readings agree. Stating it with a placation hypothesis would have implied
otherwise (Rule 13: an unconsumed hypothesis is a misdescription).

The practical consequence is that a continuation term periodic with period `Δ`
satisfies the condition with a vanishing difference, however far from convex it
is. `Sanctions/Examples/GeneratedChordStrictlyWeaker.lean` is that witness. -/
theorem senderContinuationGeneratedChordAt_iff_lag
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x aL aH : ℝ} :
    p.SenderContinuationGeneratedChordAt V_S x aL aH
      ↔ ∀ u ∈ Set.Icc (0 : ℝ) (1 - (p.σ x aL - p.σ x aH)),
          ∀ u' ∈ Set.Icc (0 : ℝ) (1 - (p.σ x aL - p.σ x aH)), u ≤ u' →
            p.senderContinuationTerm V_S x (u + (p.σ x aL - p.σ x aH))
                - p.senderContinuationTerm V_S x u
              ≤ p.senderContinuationTerm V_S x (u' + (p.σ x aL - p.σ x aH))
                - p.senderContinuationTerm V_S x u' := by
  constructor
  · -- Given the generated form, feed it `z = u - σ(x,aH)`.
    intro h u hu u' hu' huu'
    have hz : u - p.σ x aH ∈ p.responseWindow x aL aH := by
      refine ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hz' : u' - p.σ x aH ∈ p.responseWindow x aL aH := by
      refine ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    have := h _ hz _ hz' (by linarith)
    rw [show p.σ x aH + (u - p.σ x aH) = u from by ring,
      show p.σ x aH + (u' - p.σ x aH) = u' from by ring,
      show p.σ x aL + (u - p.σ x aH) = u + (p.σ x aL - p.σ x aH) from by ring,
      show p.σ x aL + (u' - p.σ x aH) = u' + (p.σ x aL - p.σ x aH) from by ring]
      at this
    linarith
  · -- Given the lag form, feed it `u = σ(x,aH) + z`.
    intro h z hz z' hz' hzz'
    have hu : p.σ x aH + z ∈ Set.Icc (0 : ℝ) (1 - (p.σ x aL - p.σ x aH)) := by
      refine ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hu' : p.σ x aH + z' ∈ Set.Icc (0 : ℝ) (1 - (p.σ x aL - p.σ x aH)) := by
      refine ⟨by linarith [hz'.1], by linarith [hz'.2]⟩
    have := h _ hu _ hu' (by linarith)
    rw [show p.σ x aH + z + (p.σ x aL - p.σ x aH) = p.σ x aL + z from by ring,
      show p.σ x aH + z' + (p.σ x aL - p.σ x aH) = p.σ x aL + z' from by ring]
      at this
    linarith

/-- **The all-chord condition generates the pair condition.** The ladder rung
that keeps the weakening honest: anything discharging §12's chord hypothesis
discharges this one, so nothing built on the stronger form is lost. -/
theorem senderContinuationGeneratedChord_of_increasingChords
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x aL aH : ℝ}
    (hchord : p.SenderContinuationIncreasingChordsAt V_S x)
    (hσ : p.σ x aH ≤ p.σ x aL) :
    p.SenderContinuationGeneratedChordAt V_S x aL aH := by
  intro z hz z' hz' hzz
  obtain ⟨hzL, hzH⟩ := p.responseWindow_shift_mem hσ hz
  obtain ⟨hzL', hzH'⟩ := p.responseWindow_shift_mem hσ hz'
  have huh : p.σ x aH + z + (z' - z) ∈ Sanctions.I := by
    rw [show p.σ x aH + z + (z' - z) = p.σ x aH + z' from by ring]; exact hzH'
  have hvh : p.σ x aL + z + (z' - z) ∈ Sanctions.I := by
    rw [show p.σ x aL + z + (z' - z) = p.σ x aL + z' from by ring]; exact hzL'
  have hc := hchord hzH hzL huh hvh (by linarith) (by linarith : (0 : ℝ) ≤ z' - z)
  rw [show p.σ x aH + z + (z' - z) = p.σ x aH + z' from by ring,
    show p.σ x aL + z + (z' - z) = p.σ x aL + z' from by ring] at hc
  exact hc

/-- **The generated chord condition discharges the ordinal condition.**

The real content of the route, now stated on the inequality the exchange argument
consumes rather than on the whole chord family. Under the translated-loss
*difference* form the stage terms move by `g z' - g z` at both compliance levels
and cancel exactly, leaving one generated chord of the composite. -/
theorem recentredSCLowerAt_of_generatedChord
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x aL aH : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hL : aL ∈ Sanctions.I) (hH : aH ∈ Sanctions.I)
    (hgen : p.SenderContinuationGeneratedChordAt V_S x aL aH)
    (hσ : p.σ x aH ≤ p.σ x aL) :
    p.RecentredSCLowerAt V_S x aL aH := by
  refine Sanctions.BinaryComparativeStatics.sCLowerOn_of_sub_antitoneOn ?_
  intro z hz z' hz' hzz
  obtain ⟨hzL, hzH⟩ := p.responseWindow_shift_mem hσ hz
  obtain ⟨hzL', hzH'⟩ := p.responseWindow_shift_mem hσ hz'
  -- The stage terms move by `g z' - g z` at *both* compliance levels, so they
  -- cancel from the difference; what is left is one generated chord.
  have dH : p.recentredSenderObjective V_S x aH z'
      - p.recentredSenderObjective V_S x aH z
      = (g z' - g z)
        + (p.senderContinuationTerm V_S x (p.σ x aH + z')
           - p.senderContinuationTerm V_S x (p.σ x aH + z)) := by
    have h := hform aH hH _ hzH _ hzH'
    rw [show p.σ x aH + z' - p.σ x aH = z' from by ring,
      show p.σ x aH + z - p.σ x aH = z from by ring] at h
    change p.U_S x aH (p.σ x aH + z')
        + p.senderContinuationTerm V_S x (p.σ x aH + z')
      - (p.U_S x aH (p.σ x aH + z)
        + p.senderContinuationTerm V_S x (p.σ x aH + z)) = _
    linarith
  have dL : p.recentredSenderObjective V_S x aL z'
      - p.recentredSenderObjective V_S x aL z
      = (g z' - g z)
        + (p.senderContinuationTerm V_S x (p.σ x aL + z')
           - p.senderContinuationTerm V_S x (p.σ x aL + z)) := by
    have h := hform aL hL _ hzL _ hzL'
    rw [show p.σ x aL + z' - p.σ x aL = z' from by ring,
      show p.σ x aL + z - p.σ x aL = z from by ring] at h
    change p.U_S x aL (p.σ x aL + z')
        + p.senderContinuationTerm V_S x (p.σ x aL + z')
      - (p.U_S x aL (p.σ x aL + z)
        + p.senderContinuationTerm V_S x (p.σ x aL + z)) = _
    linarith
  have hc := hgen z hz z' hz' hzz
  simp only
  linarith [dH, dL, hc]

/-- **Increasing chords discharge the ordinal condition.**

The ladder rung that keeps the ordinal route from being a new assumption:
anything that discharged §12's condition discharges this one. Under the
translated-loss form the stage terms cancel exactly from the difference of the
two re-centred objectives, leaving a chord of the composite continuation term. -/
theorem recentredSCLowerAt_of_increasingChords
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x aL aH : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hL : aL ∈ Sanctions.I) (hH : aH ∈ Sanctions.I)
    (hchord : p.SenderContinuationIncreasingChordsAt V_S x)
    (hσ : p.σ x aH ≤ p.σ x aL) :
    p.RecentredSCLowerAt V_S x aL aH :=
  p.recentredSCLowerAt_of_generatedChord V_S hform hL hH
    (p.senderContinuationGeneratedChord_of_increasingChords V_S hchord hσ) hσ

/-- **The ordinal condition gives the non-widening gap, at one pair of
compliance levels.**

Runs entirely on `greatest_argmax_le_of_sCLowerOn`: the greatest maximiser of
the re-centred objective at the higher compliance sits below the one at the
lower. Greatestness over the window follows from greatestness of `σ_dyn_top`
over all feasible sanctions, because the window is contained in them. -/
theorem responseGap_le_of_recentredSCLower
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x aL aH : ℝ}
    (hL : aL ∈ Sanctions.I) (hH : aH ∈ Sanctions.I) (hle : aL ≤ aH)
    (hσ : p.σ x aH ≤ p.σ x aL)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x)
    (hSC : p.RecentredSCLowerAt V_S x aL aH) :
    p.σ_dyn_top V_S x aH - p.σ x aH ≤ p.σ_dyn_top V_S x aL - p.σ x aL := by
  obtain ⟨hmemH, hmemL⟩ :=
    p.responseGap_mem_responseWindow V_S hL hH hle hfeas
  -- The re-centred objective at `a`, evaluated at the re-centred response, is
  -- the dynamic objective at `σ_dyn_top`.
  have hcH : p.σ x aH + (p.σ_dyn_top V_S x aH - p.σ x aH)
      = p.σ_dyn_top V_S x aH := by ring
  have hcL : p.σ x aL + (p.σ_dyn_top V_S x aL - p.σ x aL)
      = p.σ_dyn_top V_S x aL := by ring
  have hmaxH : IsMaxOn (p.recentredSenderObjective V_S x aH)
      (p.responseWindow x aL aH) (p.σ_dyn_top V_S x aH - p.σ x aH) := by
    intro y hy
    have hfy := (p.responseWindow_shift_mem hσ hy).2
    have hobj : p.U_S x aH (p.σ x aH + y)
        + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ x aH + y)))
        ≤ p.U_S x aH (p.σ_dyn_top V_S x aH)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x aH))) :=
      p.σ_dyn_top_isMaxOn V_S x aH hfy
    change p.U_S x aH (p.σ x aH + y)
        + p.senderContinuationTerm V_S x (p.σ x aH + y)
      ≤ p.U_S x aH (p.σ x aH + (p.σ_dyn_top V_S x aH - p.σ x aH))
        + p.senderContinuationTerm V_S x
            (p.σ x aH + (p.σ_dyn_top V_S x aH - p.σ x aH))
    rw [hcH]
    exact hobj
  have hmaxL : IsMaxOn (p.recentredSenderObjective V_S x aL)
      (p.responseWindow x aL aH) (p.σ_dyn_top V_S x aL - p.σ x aL) := by
    intro y hy
    have hfy := (p.responseWindow_shift_mem hσ hy).1
    have hobj : p.U_S x aL (p.σ x aL + y)
        + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ x aL + y)))
        ≤ p.U_S x aL (p.σ_dyn_top V_S x aL)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x aL))) :=
      p.σ_dyn_top_isMaxOn V_S x aL hfy
    change p.U_S x aL (p.σ x aL + y)
        + p.senderContinuationTerm V_S x (p.σ x aL + y)
      ≤ p.U_S x aL (p.σ x aL + (p.σ_dyn_top V_S x aL - p.σ x aL))
        + p.senderContinuationTerm V_S x
            (p.σ x aL + (p.σ_dyn_top V_S x aL - p.σ x aL))
    rw [hcL]
    exact hobj
  -- A window maximiser at the lower compliance is a full dynamic maximiser, so
  -- the greatest dynamic response dominates it.
  have hgreat : ∀ y ∈ p.responseWindow x aL aH,
      IsMaxOn (p.recentredSenderObjective V_S x aL)
        (p.responseWindow x aL aH) y →
      y ≤ p.σ_dyn_top V_S x aL - p.σ x aL := by
    intro y hy hmax
    have hfy := (p.responseWindow_shift_mem hσ hy).1
    have h1 : p.recentredSenderObjective V_S x aL
        (p.σ_dyn_top V_S x aL - p.σ x aL)
      ≤ p.recentredSenderObjective V_S x aL y := hmax hmemL
    have e : p.recentredSenderObjective V_S x aL
        (p.σ_dyn_top V_S x aL - p.σ x aL)
      = p.U_S x aL (p.σ_dyn_top V_S x aL)
        + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x aL))) := by
      change p.U_S x aL (p.σ x aL + (p.σ_dyn_top V_S x aL - p.σ x aL))
          + p.senderContinuationTerm V_S x
              (p.σ x aL + (p.σ_dyn_top V_S x aL - p.σ x aL)) = _
      rw [hcL]
      rfl
    have e2 : p.recentredSenderObjective V_S x aL y
        = p.U_S x aL (p.σ x aL + y)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ x aL + y))) := rfl
    rw [e, e2] at h1
    have hmem : p.σ x aL + y ∈ p.dynamicArgmaxSet V_S x aL := by
      refine ⟨hfy, fun w hw => ?_⟩
      have hw2 : p.U_S x aL w + p.β_S * V_S (Sanctions.clipS' (p.F x w))
          ≤ p.U_S x aL (p.σ_dyn_top V_S x aL)
            + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x aL))) :=
        p.σ_dyn_top_isMaxOn V_S x aL hw
      change p.U_S x aL w + p.β_S * V_S (Sanctions.clipS' (p.F x w))
        ≤ p.U_S x aL (p.σ x aL + y)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ x aL + y)))
      linarith
    have hsup : p.σ x aL + y ≤ p.σ_dyn_top V_S x aL :=
      le_csSup (p.dynamicArgmaxSet_bddAbove V_S x aL) hmem
    linarith
  exact Sanctions.BinaryComparativeStatics.greatest_argmax_le_of_sCLowerOn
    hSC hmemH hmemL hmaxH hmaxL hgreat

/-- **The ordinal route, over the whole feasible compliance range.**

The §12 conclusion, from an ordinal hypothesis. `hSC` is asked only for ordered
pairs of feasible compliance levels, which is all the antitonicity statement
quantifies over. -/
theorem responseGap_antitoneOn_of_recentredSCLower
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ}
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x)
    (hSC : ∀ aL ∈ Sanctions.I, ∀ aH ∈ Sanctions.I, aL ≤ aH →
      p.RecentredSCLowerAt V_S x aL aH) :
    AntitoneOn (fun a => p.σ_dyn_top V_S x a - p.σ x a) Sanctions.I := by
  intro aL hL aH hH hle
  exact p.responseGap_le_of_recentredSCLower V_S hL hH hle
    (hσ_anti hL hH hle) hfeas (hSC aL hL aH hH hle)

/-- **The chord route factors through the ordinal one.**

Recorded so the ladder is visible in the tree rather than only in prose:
curvature discharges chords, chords discharge single crossing, and single
crossing carries the comparison. Same conclusion as
`responseGap_antitoneOn_of_senderContinuationIncreasingChordsAt`, reached the
ordinal way. -/
theorem responseGap_antitoneOn_of_increasingChords_via_ordinal
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} {g : ℝ → ℝ}
    (hform : p.TranslatedLossSenderDifferencesAt x g)
    (hchord : p.SenderContinuationIncreasingChordsAt V_S x)
    (hσ_anti : AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hfeas : p.ResponseTranslatesFeasibleAt V_S x) :
    AntitoneOn (fun a => p.σ_dyn_top V_S x a - p.σ x a) Sanctions.I :=
  p.responseGap_antitoneOn_of_recentredSCLower V_S hσ_anti hfeas
    (fun _aL hL _aH hH hle =>
      p.recentredSCLowerAt_of_increasingChords V_S hform hL hH hchord
        (hσ_anti hL hH hle))


/-! ## 14. The exact net-channel condition

§8 asks each channel to behave: the Sender-switch channel must not reverse the
comparison, the Target-continuation channel must strictly sharpen it. That is a
*channel-by-channel* discipline, and it is stronger than what the ordering needs.
The decomposition of §5 is exact, so the α-ordering never sees the channels
separately — only their sum. A switch channel that moves the wrong way is
harmless provided the Target channel outruns it.

This section states that directly. `NetChannelDominanceAt` says: across any rise
in compliance, whatever the switch channel adds is strictly less than what the
Target channel gives up. It is **equivalent** to the cardinal condition §1
already consumes, which is the point — the tree was always net; the two-leg
reading was a sufficient special case that hid the trade-off.

**What this is not.** The ordinal mixed route of §8 (`SCLowerOn` on each leg) is
*not* comparable to this condition and does not imply it: single-crossing is
ordinal and survives monotone transformation, while this is a cardinal inequality
on differences. The corollaries below therefore run from the *cardinal* channel
conditions — the switch wedge weakly falls, the Target wedge strictly falls —
which is the two-leg reading stated on the wedges rather than on the objectives.

Rule 3: no new assumption surface. `NetChannelDominanceAt` is proved equal to
`DynamicVsMyopicStrictDecreasingDifferencesAt`, an existing consumed condition,
so nothing downstream may assume more than it already did. Rule 22: general in
`F`; nothing here mentions `affineF` or `δ`. -/

/-- **The exact net-channel condition at `x`.**

For every rise in compliance from `aL` to `aH`, the Sender-response-switch
channel's increase is strictly smaller than the Target-continuation channel's
decrease. Neither channel is signed on its own: the switch channel may rise —
that is, work against the ordering — so long as the Target channel falls by
strictly more.

Equivalently (`netChannelDominanceAt_iff_strictDecreasingDifferences`), the total
forward wedge is strictly decreasing in compliance. -/
def NetChannelDominanceAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  ∀ aL ∈ Sanctions.I, ∀ aH ∈ Sanctions.I, aL < aH →
    p.senderSwitchWedge E x aH - p.senderSwitchWedge E x aL
      < p.targetContinuationWedge E.V_T x aL - p.targetContinuationWedge E.V_T x aH

/-- **The net-channel condition is exactly the strictly-falling total wedge.**

An accounting identity, not an economic assumption: the two sides are the same
inequality rearranged across the exact decomposition
`totalForwardWedge = targetContinuationWedge + senderSwitchWedge`.

Reading it left to right says the ordering needs only the *net* movement, and
so permits an adverse switch channel. Reading it right to left says nothing
downstream has been weakened: every theorem consuming the strict wedge condition
consumes exactly this. -/
theorem netChannelDominanceAt_iff_strictDecreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ} :
    p.NetChannelDominanceAt E x
      ↔ p.DynamicVsMyopicStrictDecreasingDifferencesAt E x := by
  constructor
  · intro h aL hL aH hH hlt
    have hnet := h aL hL aH hH hlt
    rw [p.totalForwardWedge_eq_targetContinuation_add_senderSwitch E x aH,
      p.totalForwardWedge_eq_targetContinuation_add_senderSwitch E x aL]
    linarith
  · intro h aL hL aH hH hlt
    have hw := h aL hL aH hH hlt
    rw [p.totalForwardWedge_eq_targetContinuation_add_senderSwitch E x aH,
      p.totalForwardWedge_eq_targetContinuation_add_senderSwitch E x aL] at hw
    linarith

/-- **The α-ordering from net-channel dominance.**

The most permissive cardinal route to `E.α x ≤ M.α x`: the forward-looking
Target complies no more than the myopic one whenever the Target-continuation
channel strictly outruns the Sender-response-switch channel — whichever way the
latter happens to move.

Rule 1: both policies are the equilibrium structures' own optimality fields; no
strategy is posited. No uniqueness of either argmax is used, so the conclusion
holds for every pair of selections. -/
theorem alpha_order_dynamic_le_myopic_of_netChannelDominance
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hnet : p.NetChannelDominanceAt E x) :
    E.α x ≤ M.α x :=
  p.alpha_order_dynamic_le_myopic_of_strictDecreasingDifferences E M hx
    ((p.netChannelDominanceAt_iff_strictDecreasingDifferences E).1 hnet)

/-- **Net dominance implies the ordinal condition — the arrow, named.**

The composition was already available (`netChannelDominanceAt_iff_…` then
`targetFF_strictSCLower_targetMM_of_totalWedge_strictAnti`) and is used inside
the proof of the α-ordering above, but it had no name of its own, which made the
hierarchy hard to read off and left room for the manuscript to describe the two
conditions as incomparable. They are not: the net condition is an accounting
restatement of a strictly falling total wedge, and a strictly falling gap *is*
the cardinal sufficient condition for single-crossing lower dominance.

The converse fails, so the arrow runs one way only:
`exists_strictSCLowerOn_without_gap_strictAnti` in
`Foundations/BinaryComparativeStatics.lean` exhibits two objectives standing in
the ordinal relation whose gap is not strictly decreasing. Single crossing
survives an arbitrary strictly increasing transformation; a difference condition
does not.

Rule 3: no new assumption. Both inputs are existing theorems. -/
theorem directStrictSC_of_netChannelDominance
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hnet : p.NetChannelDominanceAt E x) :
    Sanctions.BinaryComparativeStatics.StrictSCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I :=
  p.targetFF_strictSCLower_targetMM_of_totalWedge_strictAnti E
    ((p.netChannelDominanceAt_iff_strictDecreasingDifferences E).1 hnet)

/-- **The cardinal two-leg route is a special case.**

If the Sender-switch wedge merely does not rise, and the Target-continuation
wedge strictly falls, then the net condition holds — the switch channel
contributes at most zero to a difference the Target channel already makes
strictly negative. This is §8's discipline stated on the *wedges*; it is
strictly stronger than net dominance, since it forbids the adverse switch that
net dominance tolerates. -/
theorem netChannelDominanceAt_of_switchAntitoneOn_targetStrictAntiOn
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hSwitch : AntitoneOn (p.senderSwitchWedge E x) Sanctions.I)
    (hTarget : StrictAntiOn (p.targetContinuationWedge E.V_T x) Sanctions.I) :
    p.NetChannelDominanceAt E x := by
  intro aL hL aH hH hlt
  have h1 := hSwitch hL hH hlt.le
  have h2 := hTarget hL hH hlt
  linarith

/-- **And the Target leg can be read off the separated primitives.**

`targetContinuationWedge_eq` writes the Target channel as `β_T` times the
compliance continuation that `TargetReluctance.lean` signs from separated
primitives — compliance placates, sanctions raise the successor state, the
incumbent values entrenchment. So whatever makes that object strictly fall makes
the Target leg strictly fall, provided the Target is not fully myopic.

`hβ_T` (`0 < p.β_T`, the Target discounts the future but does not ignore it) is
theorem-local and not derivable from `β_T ∈ [0,1)`, which admits `β_T = 0`: a
Target that places no weight on tomorrow has no continuation channel to supply
the strictness, and the ordering must then come from elsewhere. -/
theorem netChannelDominanceAt_of_switchAntitoneOn_continuationStrictAntiOn
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hβ_T : 0 < p.β_T)
    (hSwitch : AntitoneOn (p.senderSwitchWedge E x) Sanctions.I)
    (hCont : StrictAntiOn
      (p.targetComplianceContinuation p.σ E.V_T x) Sanctions.I) :
    p.NetChannelDominanceAt E x := by
  refine p.netChannelDominanceAt_of_switchAntitoneOn_targetStrictAntiOn E
    hSwitch ?_
  intro aL hL aH hH hlt
  rw [p.targetContinuationWedge_eq E.V_T x aH,
    p.targetContinuationWedge_eq E.V_T x aL]
  exact mul_lt_mul_of_pos_left (hCont hL hH hlt) hβ_T


/-! ## 15. Both channels weak, and what an extremal selection buys

§8 keeps one leg strict, and §14 shows the cardinal route needs only the *net*
movement. Both still ask something the primitives may not deliver. This section
records what survives when **neither** channel can be signed strictly.

The composition is then weak, and by §6's caution a weak relation orders the
argmax *correspondences* rather than arbitrary selections — two constant
objectives satisfy it with every action maximising both, so no theorem ordering
arbitrary pairs can follow. What the correspondences being ordered does give is
their **extremal** elements, and that is enough whenever one of the two policies
is known to sit at an end of its own argmax set.

`Foundations/BinaryComparativeStatics.lean` proves both halves already; what
follows is the wiring, so the equilibrium structures' own optimality fields
supply the maximisers. Note the asymmetry each theorem exploits: only *one* of
the two selections has to be extremal, and it is a different one in each case.

The extremality hypothesis is a statement about **which maximiser was selected**,
not about the model. `FeedbackStackelbergEquilibriumTop.α_opt_top` certifies only
that `E.α x` is *a* maximiser, so a development wanting these conclusions must
either carry the extremality separately or prove the argmax is a singleton.
Rule 3: no new assumption surface — the hypothesis is theorem-local and about the
selection.

A warning that belongs with them, from `Examples/SenderSwitchSignUndetermined.lean`:
the pointwise extremal selections need not be continuous in the state, so these
theorems must not be fed into the Bellman construction without a separate
continuity result. -/

/-- **Two weak channels compose to the weak relation.** The all-weak counterpart
of `targetFF_strictSCLower_targetMM_of_switchWeak_targetStrict`: neither the
Sender-response-switch channel nor the Target-continuation channel is asked to
sharpen the comparison, only not to reverse it. -/
theorem targetFF_sCLower_targetMM_of_twoWeakChannels
    (E : p.FeedbackStackelbergEquilibriumTop) {x : ℝ}
    (hSwitch : p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : p.TargetContinuationWeakSCLowerAt E.V_T x) :
    Sanctions.BinaryComparativeStatics.SCLowerOn
      (p.targetFFObjective E x) (p.targetMMObjective x) Sanctions.I :=
  Sanctions.BinaryComparativeStatics.SCLowerOn.trans hSwitch hTarget

/-- **A least forward-looking compliance lies below every myopic one.**

With both channels weak, the forward-looking Target complies no more than the
myopic one *provided its own policy is the least maximiser of its objective*.
The myopic selection is arbitrary: `M.α x` may be any maximiser.

Economically, the forward-looking Target is being read at its most defiant
optimal action, and even that is no more compliant than anything the myopic
Target might choose. -/
theorem alpha_leastFF_le_anyMM_of_twoWeakChannels
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hSwitch : p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : p.TargetContinuationWeakSCLowerAt E.V_T x)
    (hE_least : ∀ y ∈ Sanctions.I,
      IsMaxOn (p.targetFFObjective E x) Sanctions.I y → E.α x ≤ y) :
    E.α x ≤ M.α x :=
  Sanctions.BinaryComparativeStatics.least_argmax_le_of_sCLowerOn
    (p.targetFF_sCLower_targetMM_of_twoWeakChannels E hSwitch hTarget)
    (E.α_mem x hx) (M.α_mem x hx) (E.α_opt_top x hx) (M.α_opt x hx) hE_least

/-- **Every forward-looking compliance lies below a greatest myopic one.**

The dual, and the one that costs less where it matters: here the *myopic*
selection carries the extremality and the forward-looking selection is arbitrary.
Since the myopic equilibrium is the comparison object rather than the
constructed one, pinning its selection is usually the cheaper of the two. -/
theorem alpha_anyFF_le_greatestMM_of_twoWeakChannels
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (hSwitch : p.SenderSwitchWeakSCLowerAt E x)
    (hTarget : p.TargetContinuationWeakSCLowerAt E.V_T x)
    (hM_greatest : ∀ y ∈ Sanctions.I,
      IsMaxOn (p.targetMMObjective x) Sanctions.I y → y ≤ M.α x) :
    E.α x ≤ M.α x :=
  Sanctions.BinaryComparativeStatics.greatest_argmax_le_of_sCLowerOn
    (p.targetFF_sCLower_targetMM_of_twoWeakChannels E hSwitch hTarget)
    (E.α_mem x hx) (M.α_mem x hx) (E.α_opt_top x hx) (M.α_opt x hx) hM_greatest


/-! ## 16. Path comparison without permanent residence

§11 compares the two regimes' state paths over the whole feasible interval. A
region-local version has to say something about where the myopic path goes, and
the tempting form — assume the region is invariant under both rules — commits to
a permanent property of the dynamics that a bistable economy will not have.

The stopped form asks only what a particular run exhibits: through whatever
horizon the myopic path has in fact stayed in the region, the comparison holds
there. Nothing is claimed about later periods, and the region need not be
invariant, closed, or an interval. `DifferentPolicyComparator.lean` carries the
general statement; this is the wiring at the two equilibria.

Rule 3: no new assumption surface. `hstay` is a fact about the trajectory that
was run, checkable by inspection, not a standing hypothesis about the model. -/

/-- **Stopped path order from closed-loop monotonicity.** Sibling of
`rulePathF_myopic_le_dynamicTop_stopped` with `hDynMono` replaced by
`hDynStepMono`: the forward-looking closed loop `x ↦ F(x, R_dyn x)`, not the
rule, is non-decreasing on `[0,1]`. In plain terms: as long as the myopic path
has in fact stayed in the region where looking ahead makes compliance strictly
less attractive, the myopic state stays weakly below the forward-looking one,
provided the forward-looking policy's next-state map preserves order. Dropped:
monotonicity of the forward-looking rule
(`rulePathF_le_of_rule_le_on_stopped_closedLoopMono`). General in `F` (BG1.8). -/
theorem rulePathF_myopic_le_dynamicTop_stopped_closedLoopMono
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hDynStepMono : MonotoneOn
      (p.ruleStepF (p.dynamicTopRealizedRule E.V_S E.α)) Sanctions.I)
    {B : Set ℝ} (hB_subS : B ⊆ Sanctions.S)
    (h_dec : ∀ x ∈ B, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {n : ℕ}
    (hstay : ∀ k, k ≤ n → p.rulePathF (p.myopicEquilibriumRule M) x₀ k ∈ B) :
    p.rulePathF (p.myopicEquilibriumRule M) x₀ n
      ≤ p.rulePathF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n :=
  p.rulePathF_le_of_rule_le_on_stopped_closedLoopMono
    (fun x _ => p.σ_mem x (M.α x))
    (fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x)
    hDynStepMono
    (p.ruleDom_on_of_strictDecreasingDifferences E M hB_subS hV_S_mono h_dec
      hσ_antiOn_a)
    hx₀ hstay

/-- **The myopic state path stays below the forward-looking one for as long as it
stays in the region.**

Inputs, in English: the Sender values entrenchment (`hV_S_mono`); the
forward-looking realised rule is non-decreasing in the state on the whole
feasible interval (`hDynMono` — a global regularity property, and the only global
hypothesis here); looking ahead makes compliance strictly less attractive at
every state *of the region* (`h_dec`); compliance placates there
(`hσ_antiOn_a`); and the myopic path has in fact remained in the region through
period `n` (`hstay`).

The conclusion is at the single horizon `n`, which is the honest scope: it is a
statement about the run, not a claim that the run must continue. -/
theorem rulePathF_myopic_le_dynamicTop_stopped
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hDynMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    {B : Set ℝ} (hB_subS : B ⊆ Sanctions.S)
    (h_dec : ∀ x ∈ B, p.DynamicVsMyopicStrictDecreasingDifferencesAt E x)
    (hσ_antiOn_a : ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {n : ℕ}
    (hstay : ∀ k, k ≤ n → p.rulePathF (p.myopicEquilibriumRule M) x₀ k ∈ B) :
    p.rulePathF (p.myopicEquilibriumRule M) x₀ n
      ≤ p.rulePathF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n :=
  -- Statement unchanged; since BG1.8 a corollary of the closed-loop sibling.
  p.rulePathF_myopic_le_dynamicTop_stopped_closedLoopMono E M hV_S_mono
    (p.ruleStepF_monotoneOn_of_rule_monotoneOn hDynMono) hB_subS h_dec
    hσ_antiOn_a hx₀ hstay

end Params
end AbstractGame
end Sanctions
