/-
Sanctions/Foundations/BinaryComparativeStatics.lean

**Comparing the maximizers of two different objectives.**

Monotone comparative statics in the Milgrom-Shannon tradition asks how
`arg max_a f(a, t)` moves when a *parameter* `t` moves inside one family of
objectives. The question here is different and is the one this project actually
needs: given **two distinct optimization problems** `f` and `g` on a common
feasible set, when is every maximizer of `f` below every maximizer of `g`?

That is a binary comparison, not a parametric one. Nothing here mentions the
sanctions game, so by Rule 19 it lives in `Foundations/`; the wiring that
instantiates it at the Target's forward-looking and myopic objectives lives in
`Theory/LockIn/`.

## The relation

`StrictSCLowerOn f g A` says: whenever `f` weakly rises from a lower feasible
action to a higher one, `g` strictly rises. Read `f` as the objective whose
maximizers should be *lower* — the orientation is not symmetric and is easy to
invert by accident, so it is fixed once here and never re-derived downstream.

The economic reading in this project's use: `f` is the fully forward-looking
Target objective and `g` the fully myopic one. If looking ahead ever makes a
larger compliance weakly attractive, then to a Target that ignores the future it
must be strictly attractive — the forward-looking regime is the one that drags
compliance down.

## What it costs, which is the point

`argmax_le_of_strictSCLowerOn` assumes **no** continuity, differentiability,
concavity, quasi-supermodularity, compactness, or uniqueness. It does not even
need the maximizers to exist — they are supplied. The proof is three lines of
order reasoning, and every hypothesis in it is used.

That matters because the sanctions application cannot supply most of those
properties: the value functions come from a bounded-continuous-function carrier
with no derivative control, the action correspondence can be multivalued, and
the transition is a general monotone `F` rather than an affine law.

The relation is also transitive (`StrictSCLowerOn.trans`), which is what lets a
comparison be routed through an intermediate objective that is never optimized
and whose maximizers are never constructed.

## Relation to the literature

This is the binary-comparison question studied by Amir and Rietzke, *A Comment
on "Monotone Comparative Statics"* (Econometrica, 2025), and the two-leg route
through an auxiliary problem is their method. Nothing below is imported from
that paper — the statements here are elementary and self-contained — and the
citation is recorded so the methodological debt is visible. Note that the paper
is **not** currently in this project's local reference library, so it has not
been read against; treat the attribution as provisional until it is.

`Foundations/MilgromShannon.lean` remains the right tool for the *parametric*
question (one family, a moving parameter, strong-set-order conclusions). This
file does not replace it and does not depend on it.

## Where the evidence lives

The cardinal-to-ordinal arrow `strictSCLowerOn_of_sub_strictAntiOn` does not
reverse, and the pair that stops it is in
`Examples/Math/BinaryComparativeStaticsStrictness.lean`. Moved there 2026-08-27:
a witness certifies this file and so does not belong inside it.

## Generality, witnessed

The ordinal relations here are stated over arbitrary ordered types rather than
over `ℝ`. Rule 9B asks a class that generalizes a named special case to exhibit
a member outside it: `Examples/Order/IntegerChain.lean` instantiates the
relation and the argmax theorem on an integer chain with integer values, at a
pair for which the single-crossing premise genuinely filters.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

namespace Sanctions
namespace BinaryComparativeStatics

open Set

/-! ### Carrier types

The relations below are **ordinal**: their statements mention only `<` and `≤`,
never subtraction, absolute value or a metric. So they are stated over arbitrary
ordered types, and each declaration asks for exactly the structure its proof
consumes -- `Preorder` where a comparison suffices, `LinearOrder` where the proof
does a trichotomy or takes a `min`/`max`, `PartialOrder` on the codomain where it
needs antisymmetry.

The real-valued dischargers later in this file (the gap conditions, the switch
wedge) stay over `ℝ`: they are about a *difference* `f - g`, which is not an
ordinal object. Generalizing those would be architectural symmetry rather than
generality, and is deliberately not done. -/

variable {α β : Type*}

/-- **Strict single-crossing lower dominance of `f` against `g` on `A`.**

Whenever `f` does not fall from a lower feasible point to a higher one, `g`
strictly rises. The orientation is chosen so that `f` is the objective whose
maximizers are the *lower* ones. -/
def StrictSCLowerOn [Preorder α] [Preorder β] (f g : α → β) (A : Set α) : Prop :=
  ∀ ⦃aL aH : α⦄, aL ∈ A → aH ∈ A → aL < aH → f aL ≤ f aH → g aL < g aH

/-- **Every maximizer of `f` is weakly below every maximizer of `g`.**

No continuity, concavity, compactness, or uniqueness: the two maximizers are
supplied, and the conclusion holds for *every* such pair, so it is a statement
about the argmax correspondences rather than about a chosen selection. -/
theorem argmax_le_of_strictSCLowerOn [LinearOrder α] [Preorder β]
    {f g : α → β} {A : Set α} {aF aG : α}
    (hsc : StrictSCLowerOn f g A)
    (haF : aF ∈ A) (haG : aG ∈ A)
    (hF : IsMaxOn f A aF) (hG : IsMaxOn g A aG) :
    aF ≤ aG := by
  by_contra hcon
  -- Suppose the `f`-maximizer sits strictly above the `g`-maximizer.
  have hlt : aG < aF := lt_of_not_ge hcon
  -- `aF` maximizes `f`, so `f` does not fall from `aG` up to `aF` ...
  have hf : f aG ≤ f aF := hF haG
  -- ... so single crossing makes `g` strictly rise across the same step ...
  have hg : g aG < g aF := hsc haG haF hlt hf
  -- ... contradicting optimality of `aG` for `g`.
  exact absurd (hG haF) (not_le_of_gt hg)

/-- The relation is transitive.

This is what licenses the two-leg route: compare `f` to an intermediate
objective `h`, and `h` to `g`, and conclude about `f` against `g` — **without
ever constructing a maximizer of `h`**. No quasi-supermodularity of the
intermediate objective is needed; the one-line proof below is the whole
argument. -/
theorem StrictSCLowerOn.trans [Preorder α] [Preorder β] {f h g : α → β} {A : Set α}
    (hfh : StrictSCLowerOn f h A) (hhg : StrictSCLowerOn h g A) :
    StrictSCLowerOn f g A := by
  intro aL aH haL haH hlt hf
  exact hhg haL haH hlt (hfh haL haH hlt hf).le

/-- **A strictly falling gap gives the relation.**

If the wedge `f - g` is strictly decreasing on `A` then `f` is strictly
single-crossing lower than `g`. This is the cardinal sufficient condition for
the ordinal hypothesis above: it is strictly stronger, and it is usually what a
model delivers, because a wedge is something one can bound channel by channel. -/
theorem strictSCLowerOn_of_sub_strictAntiOn {f g : ℝ → ℝ} {A : Set ℝ}
    (hΔ : StrictAntiOn (fun a => f a - g a) A) :
    StrictSCLowerOn f g A := by
  intro aL aH haL haH hlt hf
  have hgap := hΔ haL haH hlt
  linarith

/-- The same statement with the gap given pointwise rather than as a
`StrictAntiOn` bundle, which is the shape a `Prop`-valued project condition
usually has. -/
theorem strictSCLowerOn_of_gap_strictAnti {f g : ℝ → ℝ} {A : Set ℝ}
    (hΔ : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ < a₂ → f a₂ - g a₂ < f a₁ - g a₁) :
    StrictSCLowerOn f g A :=
  strictSCLowerOn_of_sub_strictAntiOn (fun a₁ h₁ a₂ h₂ h => hΔ a₁ h₁ a₂ h₂ h)

/-! ## Locating a maximizer strictly above a reference point

The comparison above orders two objectives. This section answers a different and
more elementary question with the same flavour: given **one** objective `g` and a
reference point `c`, when is every maximizer of `g` strictly above `c`?

The answer needs exactly two facts, and neither is a regularity condition: `c`
must be the best point among those weakly below it, and *some* feasible point
above `c` must strictly beat it. The first alone leaves the maximizer at `c`; the
second alone is consistent with the maximizer sitting below `c` at a still higher
value. Together they force it up.

This is what turns a weak policy ordering into a strict one without assuming
uniqueness, interiority, differentiability, or a first-order condition — the
route Edlin and Shannon (1998) take through derivatives, in the form available
when no derivative exists. -/

/-- **Every maximizer of `g` lies strictly above `c`.**

`c` is the best feasible point among those weakly below it, and some feasible
`a'` strictly beats it. Then no maximizer can be at or below `c`.

Four lines, no continuity, no concavity, no uniqueness, and the maximizer is
supplied rather than constructed.

**`a'` is not assumed to lie above `c`.** That hypothesis was written into the
first draft and the unused-variable linter rejected it, which is the Rule 13
unused-hypothesis audit doing its job: if `a'` were at or below `c`, then
`h_best_below` would give `g a' ≤ g c`, contradicting `ha'_better` outright. So
`c < a'` is implied by the other two hypotheses rather than needed alongside
them, and carrying it would have overstated what the theorem requires. -/
theorem lt_argmax_of_improves_above [LinearOrder α] [Preorder β]
    {g : α → β} {A : Set α} {c aG a' : α}
    (h_best_below : ∀ a ∈ A, a ≤ c → g a ≤ g c)
    (ha'_mem : a' ∈ A) (ha'_better : g c < g a')
    (haG : aG ∈ A) (hG : IsMaxOn g A aG) :
    c < aG := by
  by_contra hcon
  -- if the maximizer sat at or below `c`, it could do no better than `c` ...
  have hle : aG ≤ c := not_lt.mp hcon
  have h1 : g aG ≤ g c := h_best_below aG haG hle
  -- ... but `a'` is feasible and beats `c`, so it beats the maximizer.
  have h2 : g a' ≤ g aG := hG ha'_mem
  -- `g c < g a' ≤ g aG ≤ g c`; order-only, so no arithmetic is needed.
  exact absurd (h2.trans h1) (not_le_of_gt ha'_better)


/-- **Every maximizer of `g` lies strictly below `c`** — the order dual.

`c` is the best feasible point among those weakly *above* it, and some feasible
`a'` strictly beats it. Mirror image of `lt_argmax_of_improves_above`, proved
the same way; `a'` is again not assumed to lie below `c`, for the same reason. -/
theorem argmax_lt_of_improves_below [LinearOrder α] [Preorder β]
    {g : α → β} {A : Set α} {c aG a' : α}
    (h_best_above : ∀ a ∈ A, c ≤ a → g a ≤ g c)
    (ha'_mem : a' ∈ A) (ha'_better : g c < g a')
    (haG : aG ∈ A) (hG : IsMaxOn g A aG) :
    aG < c := by
  by_contra hcon
  have hle : c ≤ aG := not_lt.mp hcon
  have h1 : g aG ≤ g c := h_best_above aG haG hle
  have h2 : g a' ≤ g aG := hG ha'_mem
  exact absurd (h2.trans h1) (not_le_of_gt ha'_better)

/-- **Boundary exclusion: every maximizer is off both ends.**

The conjunction of the two halves above, at a single interior improver `a'` that
beats both endpoints. Nothing here is a regularity condition: no continuity, no
concavity, no differentiability, no uniqueness, and — the point — the conclusion
is about *every* maximizer rather than a selected one, so no selection principle
is smuggled in.

Note what is **not** a hypothesis. One does not assume `lo < hi`, nor that `a'`
lies between them, nor that either endpoint is feasible. Each is implied: if
`hi ≤ lo` then `h_best_below` and `h_best_above` together would force
`g a' ≤ g lo` and `g a' ≤ g hi`, contradicting the two improvement clauses. -/
theorem argmax_mem_Ioo_of_improves_inward [LinearOrder α] [Preorder β]
    {g : α → β} {A : Set α} {lo hi aG a' : α}
    (h_best_below : ∀ a ∈ A, a ≤ lo → g a ≤ g lo)
    (h_best_above : ∀ a ∈ A, hi ≤ a → g a ≤ g hi)
    (ha'_mem : a' ∈ A) (hlo : g lo < g a') (hhi : g hi < g a')
    (haG : aG ∈ A) (hG : IsMaxOn g A aG) :
    aG ∈ Set.Ioo lo hi :=
  ⟨lt_argmax_of_improves_above h_best_below ha'_mem hlo haG hG,
   argmax_lt_of_improves_below h_best_above ha'_mem hhi haG hG⟩

/-- **The unit-interval instance**, with the upper clause discharged.

On `[0,1]` the hypothesis "`1` is best among feasible points weakly above `1`"
is free, because the only such point is `1` itself. So the usable form asks only
for the two economically meaningful facts: nothing weakly below `lo` beats `lo`,
and some feasible action beats both `lo` and the top.

`lo ∈ [0,1)` is **not** required. It was in the first draft and the
unused-variable linter rejected it — the same Rule 13 audit that trimmed
`lt_argmax_of_improves_above`. Feasibility of `a'` and the two improvements
already place every maximizer strictly inside. -/
theorem argmax_mem_Ioo_top_of_improves_inward {g : ℝ → ℝ} {lo aG a' : ℝ}
    (h_best_below : ∀ a ∈ Set.Icc (0:ℝ) 1, a ≤ lo → g a ≤ g lo)
    (ha'_mem : a' ∈ Set.Icc (0:ℝ) 1) (hlo : g lo < g a') (htop : g 1 < g a')
    (haG : aG ∈ Set.Icc (0:ℝ) 1) (hG : IsMaxOn g (Set.Icc (0:ℝ) 1) aG) :
    aG ∈ Set.Ioo lo 1 :=
  argmax_mem_Ioo_of_improves_inward h_best_below
    (fun _ ha h1a => le_of_eq (congrArg g (le_antisymm ha.2 h1a)))
    ha'_mem hlo htop haG hG


/-! ## The switch wedge: a payoff read between two moving selections

The two sections above compare maximizers. This one is about a different object
that the sanctions application forces on us, and that the standard
monotone-comparative-statics toolkit does **not** reach.

Given a payoff `Q a s` and two selections `m ≤ d` of some *other* agent's
response, the **switch wedge** `Q a (d a) - Q a (m a)` measures what the first
agent gains from facing the second selection rather than the first. It is not
the value of any optimization problem — it is one agent's argmax fed into
another agent's payoff — so envelope theorems and Topkis-style argmax
monotonicity say nothing about it directly, and its sign in `a` is genuinely
undetermined by the sign conditions one would expect to settle it. (A
counterexample is `Examples/SenderSwitchSignUndetermined.lean`.)

What *does* settle it is four shape facts, and the theorem below is the exact
accounting. Two are about the payoff — non-decreasing and convex in the second
argument, and decreasing differences across the two — and two are about the
selections: both fall in `a`, and the **gap between them does not widen**. The
gap condition is the substantive one, and it is not free: it is a statement
about the relative responsiveness of two argmaxes. It is not, however, beyond
ordinal methods: `Theory/LockIn/TwoSidedForwardLooking.lean` proves it from a
recentred single-crossing hypothesis on ordered pairs of feasible compliance
levels (`responseGap_antitoneOn_of_recentredSCLower`, the ordinal route of its
§12); the cardinal route through rates is one discharge, not the only one
(wording corrected round AI, 2026-09-22). -/

/-- **The switch wedge**: what an agent with payoff `Q` gains from facing
selection `d` rather than `m`, as a function of its own action. -/
def switchWedge (Q : ℝ → ℝ → ℝ) (m d : ℝ → ℝ) (a : ℝ) : ℝ :=
  Q a (d a) - Q a (m a)

/-- **The switch wedge falls when the gap does not widen and the payoff has the
right shape.**

* `hQ_mono` — the payoff is non-decreasing in the second argument;
* `hQ_chord` — equal-width chords of `Q a ·` shift weakly up when translated
  right (convexity, in the form that is actually consumed);
* `hQ_dd` — decreasing differences: a chord in the second argument is weakly
  smaller at a higher first argument;
* `hm_anti`, `hmd` — the lower selection falls in `a`, and `m ≤ d`;
* `hgap` — the gap `d - m` does not widen in `a`.

The three selection hypotheses are **region-scoped** to `A`, and deliberately so:
in the sanctions application the action set is `[0,1]`, and the relation `m ≤ d`
is a theorem there (`σ_dyn_top_ge_sigma`) rather than an identity on all of `ℝ`.
Stating them globally would assume strictly more than any instance can supply --
the same over-assumption the 2026-08-22 audit flagged as global-`ℝ` drift.

The proof is three steps and uses each hypothesis exactly once: decreasing
differences moves the comparison to a common `a`; monotonicity widens the lower
chord to the width of the upper one; convexity translates it right. No
derivatives, no continuity, no concavity, and nothing about where the selections
came from. -/
theorem switchWedge_antitoneOn_of_gap_and_shape
    {Q : ℝ → ℝ → ℝ} {m d : ℝ → ℝ} {A : Set ℝ}
    (hQ_mono : ∀ a s₁ s₂, s₁ ≤ s₂ → Q a s₁ ≤ Q a s₂)
    (hQ_chord : ∀ a s₁ s₂ t, s₁ ≤ s₂ → 0 ≤ t →
      Q a s₂ - Q a s₁ ≤ Q a (s₂ + t) - Q a (s₁ + t))
    (hQ_dd : ∀ aL aH s₁ s₂, aL ≤ aH → s₁ ≤ s₂ →
      Q aH s₂ - Q aH s₁ ≤ Q aL s₂ - Q aL s₁)
    (hm_anti : ∀ aL ∈ A, ∀ aH ∈ A, aL ≤ aH → m aH ≤ m aL)
    (hmd : ∀ a ∈ A, m a ≤ d a)
    (hgap : ∀ aL ∈ A, ∀ aH ∈ A, aL ≤ aH → d aH - m aH ≤ d aL - m aL)
    {aL aH : ℝ} (haL : aL ∈ A) (haH : aH ∈ A) (hle : aL ≤ aH) :
    switchWedge Q m d aH ≤ switchWedge Q m d aL := by
  set mL := m aL; set dL := d aL; set mH := m aH; set dH := d aH
  have hmHmL : mH ≤ mL := hm_anti aL haL aH haH hle
  have hmHdH : mH ≤ dH := hmd aH haH
  have hmLdL : mL ≤ dL := hmd aL haL
  have hgap' : dH - mH ≤ dL - mL := hgap aL haL aH haH hle
  -- 1. decreasing differences brings both chords to the lower action
  have h1 : Q aH dH - Q aH mH ≤ Q aL dH - Q aL mH := hQ_dd aL aH mH dH hle hmHdH
  -- 2. widen the chord from `dH - mH` out to the full width `dL - mL`
  have h2 : Q aL dH - Q aL mH ≤ Q aL (mH + (dL - mL)) - Q aL mH := by
    have : dH ≤ mH + (dL - mL) := by linarith
    linarith [hQ_mono aL dH (mH + (dL - mL)) this]
  -- 3. translate that equal-width chord right, onto `[mL, dL]`
  have h3 : Q aL (mH + (dL - mL)) - Q aL mH ≤ Q aL dL - Q aL mL := by
    have hw : mH ≤ mH + (dL - mL) := by linarith
    have ht : (0 : ℝ) ≤ mL - mH := by linarith
    have := hQ_chord aL mH (mH + (dL - mL)) (mL - mH) hw ht
    have e1 : mH + (dL - mL) + (mL - mH) = dL := by ring
    have e2 : mH + (mL - mH) = mL := by ring
    rw [e1, e2] at this
    exact this
  simp only [switchWedge]
  linarith


/-- **The switch wedge falls — with every payoff-shape hypothesis confined to a
sanction region `S`.**

The same accounting as `switchWedge_antitoneOn_of_gap_and_shape`, with the three
payoff hypotheses restricted from all of `ℝ` to a set `S` that both selections
land in. That restriction is the point: a global hypothesis asserts payoff
geometry at sanctions the play never reaches, and the version above asks for it
on all of `ℝ` while asking for the *selection* facts only on `A` — an asymmetry
with no justification beyond convenience.

`S` is required order-connected, which is how the one translated endpoint the
proof needs, `m aH + (d aL - m aL)`, is shown to stay inside `S`: it lies between
`m aH` and `d aL`, both of which are selection images. So no extra membership
hypothesis is needed, and an interval is order-connected. -/
theorem switchWedge_antitoneOn_of_gap_and_shapeOn
    {Q : ℝ → ℝ → ℝ} {m d : ℝ → ℝ} {A S : Set ℝ}
    (hS : S.OrdConnected)
    (hm_mem : ∀ a ∈ A, m a ∈ S) (hd_mem : ∀ a ∈ A, d a ∈ S)
    (hQ_mono : ∀ a ∈ A, ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≤ s₂ → Q a s₁ ≤ Q a s₂)
    (hQ_chord : ∀ a ∈ A, ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ t, s₁ ≤ s₂ → 0 ≤ t →
      s₁ + t ∈ S → s₂ + t ∈ S →
      Q a s₂ - Q a s₁ ≤ Q a (s₂ + t) - Q a (s₁ + t))
    (hQ_dd : ∀ aL ∈ A, ∀ aH ∈ A, ∀ s₁ ∈ S, ∀ s₂ ∈ S, aL ≤ aH → s₁ ≤ s₂ →
      Q aH s₂ - Q aH s₁ ≤ Q aL s₂ - Q aL s₁)
    (hm_anti : ∀ aL ∈ A, ∀ aH ∈ A, aL ≤ aH → m aH ≤ m aL)
    (hmd : ∀ a ∈ A, m a ≤ d a)
    (hgap : ∀ aL ∈ A, ∀ aH ∈ A, aL ≤ aH → d aH - m aH ≤ d aL - m aL)
    {aL aH : ℝ} (haL : aL ∈ A) (haH : aH ∈ A) (hle : aL ≤ aH) :
    switchWedge Q m d aH ≤ switchWedge Q m d aL := by
  have hmL : m aL ∈ S := hm_mem aL haL
  have hdL : d aL ∈ S := hd_mem aL haL
  have hmH : m aH ∈ S := hm_mem aH haH
  have hdH : d aH ∈ S := hd_mem aH haH
  have hmHmL : m aH ≤ m aL := hm_anti aL haL aH haH hle
  have hmHdH : m aH ≤ d aH := hmd aH haH
  have hmLdL : m aL ≤ d aL := hmd aL haL
  have hgap' : d aH - m aH ≤ d aL - m aL := hgap aL haL aH haH hle
  -- The single translated endpoint, and why it stays inside `S`.
  have hmid : m aH + (d aL - m aL) ∈ S :=
    hS.out hmH hdL ⟨by linarith, by linarith⟩
  -- 1. decreasing differences brings both chords to the lower action
  have h1 : Q aH (d aH) - Q aH (m aH) ≤ Q aL (d aH) - Q aL (m aH) :=
    hQ_dd aL haL aH haH _ hmH _ hdH hle hmHdH
  -- 2. widen the chord from `d aH - m aH` out to the full width `d aL - m aL`
  have h2 : Q aL (d aH) - Q aL (m aH)
      ≤ Q aL (m aH + (d aL - m aL)) - Q aL (m aH) := by
    have hlt : d aH ≤ m aH + (d aL - m aL) := by linarith
    linarith [hQ_mono aL haL _ hdH _ hmid hlt]
  -- 3. translate that equal-width chord right, onto `[m aL, d aL]`
  have h3 : Q aL (m aH + (d aL - m aL)) - Q aL (m aH)
      ≤ Q aL (d aL) - Q aL (m aL) := by
    have hw : m aH ≤ m aH + (d aL - m aL) := by linarith
    have ht : (0 : ℝ) ≤ m aL - m aH := by linarith
    have e1 : m aH + (d aL - m aL) + (m aL - m aH) = d aL := by ring
    have e2 : m aH + (m aL - m aH) = m aL := by ring
    have h := hQ_chord aL haL _ hmH _ hmid (m aL - m aH) hw ht
      (by rw [e2]; exact hmL) (by rw [e1]; exact hdL)
    rw [e1, e2] at h
    exact h
  simp only [switchWedge]
  linarith


/-! ## The weak relation, and what it does and does not order

`StrictSCLowerOn` orders *every* pair of maximizers, and that strength has a
price: routing a comparison through an intermediate objective forces **both**
legs to be strict. Only one of them needs to be.

The weak relation below carries two clauses — a weak rise in `f` forces a weak
rise in `g`, and a strict rise forces a strict rise — and that is exactly what a
mixed composition needs. It is genuinely weaker, and its conclusion is
correspondingly weaker: it orders the argmax *correspondences* in the strong set
order, hence their extremal elements, but **not** an arbitrary selection from
each. That distinction is not a technicality. Two constant objectives satisfy the
weak relation with every point of `A` maximizing both, so no theorem ordering
arbitrary selections can follow from it; there is deliberately no such theorem
here.

The economic reading of the split: the Sender-response-switch leg is allowed to
be weakly neutral or weakly favourable, and the Target's own continuation motive
supplies the strictness. That is the asymmetry the model actually has, since the
switch channel's sign is not determined by the primitives at all. -/

/-- **Weak single-crossing lower dominance of `f` against `g` on `A`.**

Two clauses: `f` not falling forces `g` not to fall, and `f` strictly rising
forces `g` strictly to rise. Same orientation as `StrictSCLowerOn` — `f` is the
objective whose maximizers should be the lower ones. -/
def SCLowerOn [Preorder α] [Preorder β] (f g : α → β) (A : Set α) : Prop :=
  ∀ ⦃aL aH : α⦄, aL ∈ A → aH ∈ A → aL < aH →
    (f aL ≤ f aH → g aL ≤ g aH) ∧ (f aL < f aH → g aL < g aH)

/-- The strict relation implies the weak one, so nothing is lost by stating a
theorem against `SCLowerOn` where the weak form suffices. -/
theorem StrictSCLowerOn.toSCLowerOn [Preorder α] [Preorder β] {f g : α → β} {A : Set α}
    (h : StrictSCLowerOn f g A) : SCLowerOn f g A := by
  refine fun aL aH haL haH hlt => ⟨fun hf => (h haL haH hlt hf).le, fun hf => ?_⟩
  exact h haL haH hlt hf.le

/-- **The weak relation orders the argmax correspondences in the strong set
order.**

`min aF aG` is still an `f`-maximizer and `max aF aG` is still a `g`-maximizer.
No closure or compactness hypothesis on `A` is needed: on a linear order the
meet and the join are each *one of the two supplied points*, so both are already
known to be feasible.

This is the whole conclusion available from the weak relation. It does **not**
say `aF ≤ aG`; see the extremal corollaries below for what does. -/
-- `LinearOrder β`, not `PartialOrder β`: the tie argument below turns
-- `¬ (f aG < f aF)` into `f aF ≤ f aG`, which is totality and is false in a
-- general partial order. The two extremal corollaries inherit it from here.
theorem argmax_meet_join_of_sCLowerOn [LinearOrder α] [LinearOrder β]
    {f g : α → β} {A : Set α} {aF aG : α}
    (hsc : SCLowerOn f g A)
    (haF : aF ∈ A) (haG : aG ∈ A)
    (hF : IsMaxOn f A aF) (hG : IsMaxOn g A aG) :
    IsMaxOn f A (min aF aG) ∧ IsMaxOn g A (max aF aG) := by
  rcases le_total aF aG with hle | hle
  · -- Already ordered: the meet is `aF` and the join is `aG`.
    rw [min_eq_left hle, max_eq_right hle]
    exact ⟨hF, hG⟩
  · rcases eq_or_lt_of_le hle with heq | hlt
    · -- The two coincide.
      subst heq
      rw [min_self, max_self]
      exact ⟨hF, hG⟩
    · -- The interesting case: `aG < aF`. Both points turn out to be tied.
      rw [min_eq_right hle, max_eq_left hle]
      -- `aF` maximizes `f`, so `f` does not fall from `aG` up to `aF` ...
      have hf_le : f aG ≤ f aF := hF haG
      -- ... so the weak clause makes `g` not fall either ...
      have hg_le : g aG ≤ g aF := (hsc haG haF hlt).1 hf_le
      -- ... while `aG` maximizes `g`, giving the reverse.
      have hg_ge : g aF ≤ g aG := hG haF
      have hg_eq : g aF = g aG := le_antisymm hg_ge hg_le
      -- The strict clause now rules out a strict rise in `f`, so `f` is tied too.
      have hf_eq : f aG = f aF := by
        refine le_antisymm hf_le (le_of_not_gt fun hgt => ?_)
        exact absurd ((hsc haG haF hlt).2 hgt) (not_lt_of_ge hg_ge)
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · exact hf_eq ▸ hF hy
      · exact hg_eq ▸ hG hy

/-- **A least `f`-maximizer lies below every `g`-maximizer.**

The meet is an `f`-maximizer, so a least one sits below it, and the meet sits
below `aG`. Only `aF` needs to be extremal. -/
theorem least_argmax_le_of_sCLowerOn [LinearOrder α] [LinearOrder β]
    {f g : α → β} {A : Set α} {aF aG : α}
    (hsc : SCLowerOn f g A)
    (haF : aF ∈ A) (haG : aG ∈ A)
    (hF : IsMaxOn f A aF) (hG : IsMaxOn g A aG)
    (hF_least : ∀ y ∈ A, IsMaxOn f A y → aF ≤ y) :
    aF ≤ aG := by
  have hmem : min aF aG ∈ A := by
    rcases le_total aF aG with h | h
    · rw [min_eq_left h]; exact haF
    · rw [min_eq_right h]; exact haG
  exact le_trans
    (hF_least _ hmem (argmax_meet_join_of_sCLowerOn hsc haF haG hF hG).1)
    (min_le_right aF aG)

/-- **Every `f`-maximizer lies below a greatest `g`-maximizer.**

Dual to the previous: the join is a `g`-maximizer, so a greatest one dominates
it, and `aF` sits below the join. Only `aG` needs to be extremal. -/
theorem greatest_argmax_le_of_sCLowerOn [LinearOrder α] [LinearOrder β]
    {f g : α → β} {A : Set α} {aF aG : α}
    (hsc : SCLowerOn f g A)
    (haF : aF ∈ A) (haG : aG ∈ A)
    (hF : IsMaxOn f A aF) (hG : IsMaxOn g A aG)
    (hG_greatest : ∀ y ∈ A, IsMaxOn g A y → y ≤ aG) :
    aF ≤ aG := by
  have hmem : max aF aG ∈ A := by
    rcases le_total aF aG with h | h
    · rw [max_eq_right h]; exact haG
    · rw [max_eq_left h]; exact haF
  exact le_trans (le_max_left aF aG)
    (hG_greatest _ hmem (argmax_meet_join_of_sCLowerOn hsc haF haG hF hG).2)

/-- **A weakly falling gap gives the weak relation.** The cardinal sufficient
condition, matching `strictSCLowerOn_of_sub_strictAntiOn` one strictness level
down. -/
theorem sCLowerOn_of_sub_antitoneOn {f g : ℝ → ℝ} {A : Set ℝ}
    (hΔ : AntitoneOn (fun a => f a - g a) A) :
    SCLowerOn f g A := by
  intro aL aH haL haH hlt
  have hgap := hΔ haL haH hlt.le
  simp only at hgap
  exact ⟨fun hf => by linarith, fun hf => by linarith⟩

/-! ### The weak relation is exactly the two-point strong set order

`argmax_meet_join_of_sCLowerOn` shows the weak relation is *sufficient* for the
strong set order. It is also *necessary*, and on a linearly ordered choice space
the whole content is visible on two-point sets: the relation says no more and no
less than that the argmaxes are strong-set ordered whenever the feasible set is a
pair.

This is Amir and Rietzke (Econometrica 93 (2025), 1481--1490) Theorem 1(i),
specialised to `X = ℝ`. Their theorem characterises the strong set order by
*quasisupermodular* dominance, and their §2 records that on `ℝ` quasisupermodular
dominance and single-crossing dominance coincide — every subset of a linear order
is a sublattice, so the quasisupermodularity half of Milgrom--Shannon is vacuous
here. What is left is exactly `SCLowerOn`.

The practical value is that it fixes how much can be asked of the weak leg. It is
not merely one sufficient condition among others that a cleverer argument might
weaken: any hypothesis delivering the strong set order over all ordered pairs of
feasible sets delivers this one too. -/

/-- **Weak dominance, characterised by the strong set order on pairs.**

Read the right-hand side as the strong set order on `{aL, aH}`. `f aL ≤ f aH`
says `aH` maximises `f` there; `g aH ≤ g aL` says `aL` maximises `g`. Veinott's
order then demands that the meet `aL` maximise `f` — that is `f aH ≤ f aL` — and
that the join `aH` maximise `g` — that is `g aL ≤ g aH`. Those two conclusions
are the right-hand side.

Necessity is the direction the development did not have. It says the weak
relation is not a convenience: it is what the strong-set conclusion *is*. -/
theorem sCLowerOn_iff_pairwise_meet_join [Preorder α] [LinearOrder β]
    {f g : α → β} {A : Set α} :
    SCLowerOn f g A ↔
      ∀ ⦃aL aH : α⦄, aL ∈ A → aH ∈ A → aL < aH →
        f aL ≤ f aH → g aH ≤ g aL → (g aL ≤ g aH ∧ f aH ≤ f aL) := by
  constructor
  · intro hsc aL aH haL haH hlt hf hg
    refine ⟨(hsc haL haH hlt).1 hf, ?_⟩
    by_contra hnot
    have hflt : f aL < f aH := lt_of_not_ge hnot
    have hglt := (hsc haL haH hlt).2 hflt
    exact absurd hglt (not_lt_of_ge hg)
  · intro h aL aH haL haH hlt
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · rcases le_or_gt (g aH) (g aL) with hg | hg
      · exact (h haL haH hlt hf hg).1
      · exact hg.le
    · by_contra hnot
      have hg : g aH ≤ g aL := le_of_not_gt hnot
      have hfle := (h haL haH hlt hf.le hg).2
      exact absurd hfle (not_le_of_gt hf)

/-! ### Transitivity, in all three strictness combinations

The mixed forms are what the two-leg route runs on. Each uses the strict clause
only on the leg that has it, which is the point: the composition is strict as
soon as **one** leg is. -/

/-- Weak against weak composes to weak. -/
theorem SCLowerOn.trans [Preorder α] [Preorder β] {f h g : α → β} {A : Set α}
    (hfh : SCLowerOn f h A) (hhg : SCLowerOn h g A) :
    SCLowerOn f g A := by
  refine fun aL aH haL haH hlt => ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (hhg haL haH hlt).1 ((hfh haL haH hlt).1 hf)
  · exact (hhg haL haH hlt).2 ((hfh haL haH hlt).2 hf)

/-- **Strict first leg, weak second leg, strict conclusion.**

A weak rise in `f` is turned into a *strict* middle rise by the strict relation,
and the weak relation's strict clause carries it the rest of the way.

Which leg is which is fixed by the argument order and nothing else: `hfh` relates
`f` to the intermediate `h`, so it is the leg whose strictness is being assumed
here. The economic reading of the two legs belongs at the point of use, not in
this file. -/
theorem StrictSCLowerOn.trans_weak [Preorder α] [Preorder β] {f h g : α → β} {A : Set α}
    (hfh : StrictSCLowerOn f h A) (hhg : SCLowerOn h g A) :
    StrictSCLowerOn f g A := by
  intro aL aH haL haH hlt hf
  exact (hhg haL haH hlt).2 (hfh haL haH hlt hf)

/-- **Weak first leg, strict second leg, strict conclusion.**

The mirror image: the weak relation's weak clause carries a weak `f` rise to a
weak middle rise, and the strict second relation finishes. Here it is `hhg`,
relating the intermediate `h` to `g`, that carries the strictness. -/
theorem SCLowerOn.trans_strict [Preorder α] [Preorder β] {f h g : α → β} {A : Set α}
    (hfh : SCLowerOn f h A) (hhg : StrictSCLowerOn h g A) :
    StrictSCLowerOn f g A := by
  intro aL aH haL haH hlt hf
  exact hhg haL haH hlt ((hfh haL haH hlt).1 hf)

end BinaryComparativeStatics
end Sanctions
