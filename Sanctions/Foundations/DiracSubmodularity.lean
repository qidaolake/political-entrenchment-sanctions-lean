/-
Sanctions/Foundations/DiracSubmodularity.lean

**A deterministic transition strictly increasing in both arguments induces no
submodular kernel** — the lattice fact behind Amir (2002, §2.2), stated
parametrically.

The strictness is load-bearing and is *not* a technicality: the unqualified
claim — that no deterministic law has submodular threshold CDFs — is **false**,
and `Examples/MinLawSubmodularityWitness.lean` refutes it by machine at
`f x a = min x a`. See the 2026-08-31 correction below.

## What this closes

Curtat's (1996) stochastic-complementarity assumption (A8) requires, in one
dimension, that the transition's cumulative kernel `Phi(y | x, a)` be
**submodular** in the pair (current state, action) for each threshold `y`. It is
the load-bearing hypothesis of the constructive existence results for stochastic
games with strategic complementarities — Curtat 1996 Thm 4.5/4.6, and Amir 2002
which reviews the scope of the route.

For a *deterministic* law `x' = f(x, a)` the kernel is an indicator,

    Phi(y | x, a) = 1  if  f x a <= y,   0  otherwise,

so its sublevel set `L y = {(x,a) | f x a <= y}` is downward closed, and
submodularity of an indicator is a purely order-theoretic condition on that set.
The content below is that submodularity fails as soon as `f` genuinely increases
in *both* arguments: put the threshold at a corner, `y := f x1 a1`, and the
cross-difference is already violated at that quadruple.

## Why this is parametric and not a witness (Rule 5)

Amir's own argument is an informal graphical one inside a "scope and
limitations" discussion, and it is hedged — it carries the exception *"unless f
is actually independent of one of the arguments."* What follows makes both
halves exact and quantifier-free in the economy:

* `not_submodularAt_cdf_of_strict` — failure at **every** `f` and **every**
  quadruple where `f` strictly increases in each argument separately. No economy
  is fixed, no parameter is named, and the threshold is constructed from the
  data rather than chosen.
* `submodular_cdf_of_indep_fst` / `submodular_cdf_of_indep_snd` — degeneracy in
  one coordinate is *sufficient* for the condition to hold, and there the
  indicator is not merely submodular but **modular** (the cross-difference is an
  equality).

## Correction (2026-08-31): degeneracy is sufficient, not necessary

An earlier version of this header composed the two bullets above into an *iff* —
"(A8) holds iff the law is degenerate in one of its two arguments." **That is
false.** The two theorems do not compose that way: the first is quantified at a
quadruple where `f` strictly increases in each argument, and the negation of
that is not degeneracy.

The counterexample is `f x a = min x a`, and it is **proved**, not asserted:
`Examples/MinLawSubmodularityWitness.lean` shows `minLaw` is continuous,
monotone in each argument, diagonal-fixed, and nonconstant in each coordinate
(`minLaw_nonconstant_fst` / `_snd`), yet at every ordered rectangle
`x1 ≤ x2`, `a1 ≤ a2`,

    min x1 a1 = min (min x1 a2) (min x2 a1)   -- `minLaw_rectangle`

so no threshold ever violates the cross-difference and every threshold CDF is
submodular — `minLaw_submodular (y : ℝ) : Submodular (cdf minLaw y)`, for all
`y`. That theorem is the exact boundary on the ones proved below.

The exact condition, for a law nondecreasing in each argument, is the
**rectangle-min identity**. Writing `p = f x1 a1`, `q = f x1 a2`, `r = f x2 a1`,
every threshold CDF is submodular at that rectangle iff `p = min q r`: the only
order-compatible binary pattern violating the cross-difference is `(1,0,0,0)`,
and a threshold realizing it exists exactly when `p < q` and `p < r`. On domains
with top elements this globalizes to a **min-separable** law
`f x a = min (f x ⊤) (f ⊤ a)`, of which coordinate degeneracy is one special case.

This classification is elementary but it is **not** in Curtat or Amir and must
not be attributed to them. **Both halves are now formalized** (2026-09-01), in §3
below: `forall_threshold_submodularAt_iff_rectangle_min` at one rectangle and
`forall_threshold_submodular_iff_rectangle_min` quantified over the product
order. This paragraph is therefore no longer prose ahead of the proof. One
correction it needed: the equivalence requires monotonicity along **all four**
edges of the rectangle, not just the two at the lower corner — with only the
lower two it is false.

**What this changes for this project: nothing about the verdict.** The
transitions used here strictly increase in both arguments — `affineF δ` with
`δ ∈ (0,1)` has `p < q` and `p < r` at every non-degenerate rectangle — so
`not_submodularAt_cdf_of_strict` still applies and (A8) still fails for them.
What was overstated was the *general characterization*, not the conclusion for
this model.

## Rule 19

External theory: this is a fact about indicators of downward-closed sets in a
product order. It mentions no `Params`, no sanctions, and no value function. The
`Params`-level consequence is wired separately in `Theory/`.
-/

import Mathlib.Tactic

namespace Sanctions.DiracKernel

open Set

variable {alpha beta : Type*}

/-! ## 1. The kernel of a deterministic law, and submodularity at a quadruple -/

/-- **The cumulative kernel of a deterministic transition.**

`cdf f y x a` is the probability that next period's state is at most `y`, when
the law is the deterministic `f` — so it is `1` when `f x a <= y` and `0`
otherwise. This is the Dirac (atomic) kernel written as a CDF, which is the form
Curtat's assumption (A8) constrains. -/
noncomputable def cdf (f : alpha → beta → ℝ) (y : ℝ) (x : alpha) (a : beta) : ℝ :=
  if f x a ≤ y then 1 else 0

/-- **Submodularity of `g` in its two arguments, at one quadruple.**

The cross-difference inequality `g x2 a2 + g x1 a1 <= g x1 a2 + g x2 a1`, which
for `x1 <= x2` and `a1 <= a2` is submodularity on the product order: raising
both coordinates together buys no more than raising each alone. -/
def SubmodularAt (g : alpha → beta → ℝ) (x₁ x₂ : alpha) (a₁ a₂ : beta) : Prop :=
  g x₂ a₂ + g x₁ a₁ ≤ g x₁ a₂ + g x₂ a₁

/-- **Submodularity, quantified over the product order.** -/
def Submodular [Preorder alpha] [Preorder beta] (g : alpha → beta → ℝ) : Prop :=
  ∀ x₁ x₂ a₁ a₂, x₁ ≤ x₂ → a₁ ≤ a₂ → SubmodularAt g x₁ x₂ a₁ a₂

/-! ## 2. The lattice fact

An indicator fails submodularity exactly where two points sit outside the set
while their meet sits inside. For a downward-closed set that is the only way it
can fail, and it is how it fails here. -/

/-- **An indicator is not submodular where the meet is in and both joins-of-one
are out.**

Nothing is assumed about `L` — not downward closure, not monotonicity, not even
an order on the two domains. The three hypotheses *are* the failure. -/
theorem not_submodularAt_indicator
    {L : alpha → beta → Prop} [∀ x a, Decidable (L x a)]
    {x₁ x₂ : alpha} {a₁ a₂ : beta}
    (hmeet : L x₁ a₁) (h12 : ¬ L x₁ a₂) (h21 : ¬ L x₂ a₁) :
    ¬ SubmodularAt (fun x a => if L x a then (1 : ℝ) else 0) x₁ x₂ a₁ a₂ := by
  simp only [SubmodularAt]
  rw [if_pos hmeet, if_neg h12, if_neg h21]
  split_ifs <;> norm_num

/-! ## 3. The theorem

A deterministic law that strictly increases in each argument separately has,
at that very quadruple, a threshold whose kernel is not submodular. -/

/-- **Amir (2002) §2.2, exactly.** At any quadruple where the deterministic law
`f` strictly increases in each argument separately, the kernel at threshold
`f x₁ a₁` violates submodularity.

The threshold is *constructed from the data* — it is the value of `f` at the
lower corner — so no threshold has to be searched for and no economy is fixed.

Economically: put the cutoff exactly at the entrenchment the low state and the
low sanction produce. Then raising *either* the state or the sanction alone
already pushes next period's entrenchment above the cutoff, so both single
deviations read `0` while the corner reads `1`, and the cross-difference has the
wrong sign. -/
theorem not_submodularAt_cdf_of_strict
    (f : alpha → beta → ℝ) {x₁ x₂ : alpha} {a₁ a₂ : beta}
    (hx : f x₁ a₁ < f x₂ a₁) (ha : f x₁ a₁ < f x₁ a₂) :
    ¬ SubmodularAt (cdf f (f x₁ a₁)) x₁ x₂ a₁ a₂ := by
  have h := not_submodularAt_indicator
    (L := fun x a => f x a ≤ f x₁ a₁) (x₁ := x₁) (x₂ := x₂) (a₁ := a₁) (a₂ := a₂)
    le_rfl (not_le.mpr ha) (not_le.mpr hx)
  simpa [cdf] using h

/-- **The quantified form.** Under the same strictness, submodularity fails on
the product order — so assumption (A8) is unavailable at this threshold. -/
theorem not_submodular_cdf_of_strict [Preorder alpha] [Preorder beta]
    (f : alpha → beta → ℝ) {x₁ x₂ : alpha} {a₁ a₂ : beta}
    (hx12 : x₁ ≤ x₂) (ha12 : a₁ ≤ a₂)
    (hx : f x₁ a₁ < f x₂ a₁) (ha : f x₁ a₁ < f x₁ a₂) :
    ¬ Submodular (cdf f (f x₁ a₁)) :=
  fun h => not_submodularAt_cdf_of_strict f hx ha (h x₁ x₂ a₁ a₂ hx12 ha12)

/-- **Some threshold always fails**, given one quadruple of strict increase.
This is the form to cite: the route is closed for the law, not merely for a
threshold someone happened to pick. -/
theorem exists_threshold_not_submodular [Preorder alpha] [Preorder beta]
    (f : alpha → beta → ℝ) {x₁ x₂ : alpha} {a₁ a₂ : beta}
    (hx12 : x₁ ≤ x₂) (ha12 : a₁ ≤ a₂)
    (hx : f x₁ a₁ < f x₂ a₁) (ha : f x₁ a₁ < f x₁ a₂) :
    ∃ y : ℝ, ¬ Submodular (cdf f y) :=
  ⟨f x₁ a₁, not_submodular_cdf_of_strict f hx12 ha12 hx ha⟩

/-! ## 4. The exception, made exact

Amir's hedge — *"unless `f` is actually independent of one of the arguments"* —
is the whole of the escape, and in that case the indicator is **modular**: the
cross-difference is an equality, not merely an inequality. -/

/-- **Degenerate in the state.** If the law ignores the current state, every
threshold's kernel is modular, hence submodular. -/
theorem submodular_cdf_of_indep_fst [Preorder alpha] [Preorder beta]
    {f : alpha → beta → ℝ} {g : beta → ℝ} (hf : ∀ x a, f x a = g a) (y : ℝ) :
    Submodular (cdf f y) := by
  intro x₁ x₂ a₁ a₂ _ _
  simp only [SubmodularAt, cdf, hf]
  exact le_of_eq (by ring)

/-- **Degenerate in the action.** If the law ignores the action — so the sanction
does not move the political state at all — every threshold's kernel is modular. -/
theorem submodular_cdf_of_indep_snd [Preorder alpha] [Preorder beta]
    {f : alpha → beta → ℝ} {g : alpha → ℝ} (hf : ∀ x a, f x a = g x) (y : ℝ) :
    Submodular (cdf f y) := by
  intro x₁ x₂ a₁ a₂ _ _
  simp only [SubmodularAt, cdf, hf]
  exact le_of_eq (by ring)

/-! ## 3. The exact boundary: the rectangle-min identity

The two directions above are a *sufficient* failure condition (strict increase
in both arguments) and a *sufficient* success condition (degeneracy in one
coordinate). Neither is necessary, and the header's 2026-08-31 correction
records that composing them into an `iff` is false — `min` is the standing
counterexample.

What follows is the exact condition, closing that open target. For a law
nondecreasing on the rectangle, submodularity of *every* threshold kernel at
that rectangle is equivalent to the **rectangle-min identity**: the lower corner
equals the minimum of the two cross corners. -/

/-- **The exact boundary at one rectangle.**

Write `p = f x₁ a₁` (lower corner), `q = f x₁ a₂` and `r = f x₂ a₁` (the two
cross corners), `s = f x₂ a₂` (upper corner). Assuming the law is nondecreasing
along all four edges of the rectangle, *every* threshold's kernel is submodular
there **iff** `p = min q r`.

Both directions are elementary once the right pattern is isolated. Forward: if
`p` is not the min it is strictly below both cross corners, and putting the
threshold at `p` itself realises the pattern `(1, 0, 0, ·)`, which violates the
cross-difference whatever the upper corner does. Backward: the min is attained
at one of the two cross corners, and monotonicity along the *opposite* upper
edge forces that corner's indicator to fire whenever the upper corner's does.

**All four monotonicity hypotheses are load-bearing.** With only the two lower
edges (`hq`, `hr`) the statement is FALSE: taking a threshold `y` with
`f x₂ a₂ ≤ y < f x₂ a₁` — possible only if the law *decreases* in the action at
`x₂` — gives `1 + 1 ≤ 1 + 0`. The upper-edge hypotheses `hs` and `ht` are what
exclude it. This was found by the compiler after the two-hypothesis version was
attempted, and is recorded because the informal phrase "nondecreasing in each
argument" supplies four corner facts, not two. -/
theorem forall_threshold_submodularAt_iff_rectangle_min
    (f : alpha → beta → ℝ) {x₁ x₂ : alpha} {a₁ a₂ : beta}
    (hq : f x₁ a₁ ≤ f x₁ a₂) (hr : f x₁ a₁ ≤ f x₂ a₁)
    (hs : f x₁ a₂ ≤ f x₂ a₂) (ht : f x₂ a₁ ≤ f x₂ a₂) :
    (∀ y : ℝ, SubmodularAt (cdf f y) x₁ x₂ a₁ a₂)
      ↔ f x₁ a₁ = min (f x₁ a₂) (f x₂ a₁) := by
  constructor
  · intro h
    refine le_antisymm (le_min hq hr) ?_
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ¬ (f x₁ a₂ ≤ f x₁ a₁) := by
      have := lt_of_lt_of_le hlt (min_le_left (f x₁ a₂) (f x₂ a₁)); linarith
    have h2 : ¬ (f x₂ a₁ ≤ f x₁ a₁) := by
      have := lt_of_lt_of_le hlt (min_le_right (f x₁ a₂) (f x₂ a₁)); linarith
    have hsub := h (f x₁ a₁)
    simp only [SubmodularAt, cdf, if_pos (le_refl (f x₁ a₁)), if_neg h1,
      if_neg h2] at hsub
    split_ifs at hsub <;> linarith
  · intro hmin y
    simp only [SubmodularAt, cdf]
    rcases min_cases (f x₁ a₂) (f x₂ a₁) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at hmin <;> split_ifs <;> linarith

/-- **The exact boundary, quantified.** For a law nondecreasing in each argument
separately, every threshold kernel is submodular on the whole product order iff
the rectangle-min identity holds at every ordered rectangle.

This is the statement the header's correction describes in prose; degeneracy in
one coordinate (`submodular_cdf_of_indep_fst` / `_snd`) and the `min` law
(`Examples/MinLawSubmodularityWitness.lean`) are both special cases of the
right-hand side, and a law strictly increasing in both arguments at some
rectangle violates it there. -/
theorem forall_threshold_submodular_iff_rectangle_min
    [Preorder alpha] [Preorder beta] (f : alpha → beta → ℝ)
    (hmono_fst : ∀ a, Monotone (fun x => f x a))
    (hmono_snd : ∀ x, Monotone (fun a => f x a)) :
    (∀ y : ℝ, Submodular (cdf f y))
      ↔ ∀ x₁ x₂ a₁ a₂, x₁ ≤ x₂ → a₁ ≤ a₂ →
          f x₁ a₁ = min (f x₁ a₂) (f x₂ a₁) := by
  constructor
  · intro h x₁ x₂ a₁ a₂ hx ha
    exact (forall_threshold_submodularAt_iff_rectangle_min f
      (hmono_snd x₁ ha) (hmono_fst a₁ hx) (hmono_fst a₂ hx)
      (hmono_snd x₂ ha)).mp (fun y => h y x₁ x₂ a₁ a₂ hx ha)
  · intro h y x₁ x₂ a₁ a₂ hx ha
    exact (forall_threshold_submodularAt_iff_rectangle_min f
      (hmono_snd x₁ ha) (hmono_fst a₁ hx) (hmono_fst a₂ hx)
      (hmono_snd x₂ ha)).mpr (h x₁ x₂ a₁ a₂ hx ha) y

end Sanctions.DiracKernel
