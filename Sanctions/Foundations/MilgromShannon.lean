/-
Sanctions/Foundations/MilgromShannon.lean

**Milgrom-Shannon (1994) Theorem 4 — abstract lattice form + scalar
specialization.**

The classic Topkis monotone-selection theorem says: if `f(x, t)` is
*supermodular* in `x` and has *increasing differences* in `(x, t)`, then
`arg max_x f(x, t)` is monotone non-decreasing in `t`. Milgrom-Shannon
*Monotone Comparative Statics* (Econometrica 1994) Theorem 4 strengthens
the conclusion to an iff: the argmax is monotone in the strong-set order
iff `f` is *quasi-supermodular* in `x` AND has the *single-crossing
property* in `(x; t)`.

This module formalizes both the abstract lattice-form Theorem 4
*sufficient direction* and the scalar specialization used downstream:

* §1 (scalar primitives) — scalar `SingleCrossing` and
  `IncreasingDifferences` on `ℝ → ℝ → ℝ`, and the strictly-weaker
  implication `IncreasingDifferences → SingleCrossing`.

* §2 (abstract lattice Theorem 4 sufficient direction) — over any
  `Lattice X`, `Preorder T`, `Preorder Payoff`: if
  `QuasiSupermodularComparisons f` and `SingleCrossingComparisons f`
  hold, then the argmax correspondence is monotone in the strong-set
  order (`ArgmaxMonotone f`).

* §3 (scalar bridges) — on `ℝ` (or any chain), quasi-supermodularity is
  automatic, and the scalar `SingleCrossing` of §1 implies the
  lattice-form `SingleCrossingComparisons` of §2.

* §4 (scalar consumer wrappers) — `monotone_argmax_of_singleCrossing`
  and `argmax_le_of_singleCrossing_strict`, derived via §2 + §3 with
  the two-point sublattice `{x, x'} ⊆ ℝ`. These are the scalar
  conclusions used throughout
  `Theory/Basin/JointPreferenceBasin.lean`.

The whole development is self-contained — it does not depend on any
external "MathTheory" library; we cite Milgrom-Shannon (1994) directly.
-/

import Sanctions.Foundations.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace Sanctions
namespace MilgromShannon

/-! ## §1 Scalar primitives -/

/-- **Single-crossing property** (scalar version of Milgrom-Shannon).
For `x ≤ y` and `t ≤ t'`:

* (weak)   `f(x, t) ≤ f(y, t)  →  f(x, t') ≤ f(y, t')`,
* (strict) `f(x, t) < f(y, t)  →  f(x, t') < f(y, t')`.

Interpretation: the preference for higher `x` (weakly) increases as `t`
increases — the difference `f(y, ·) − f(x, ·)` crosses zero at most once
and never crosses back. -/
def SingleCrossing (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃x y t t' : ℝ⦄, x ≤ y → t ≤ t' →
    (f x t ≤ f y t → f x t' ≤ f y t') ∧
    (f x t < f y t → f x t' < f y t')

/-- **Increasing differences** (the stronger Topkis-style condition).
For `x ≤ y` and `t ≤ t'`:  `f(y, t) − f(x, t) ≤ f(y, t') − f(x, t')`. -/
def IncreasingDifferences (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃x y t t' : ℝ⦄, x ≤ y → t ≤ t' →
    f y t - f x t ≤ f y t' - f x t'

/-- **Increasing differences is a stronger condition than single crossing.**
This is the key reason Milgrom-Shannon Theorem 4 is a *strict* generalization
of the Topkis sufficient condition: the iff condition for monotone argmax
is single-crossing, not increasing differences. -/
theorem IncreasingDifferences.toSingleCrossing
    {f : ℝ → ℝ → ℝ} (hID : IncreasingDifferences f) :
    SingleCrossing f := by
  intro x y t t' hxy htt
  have h := hID hxy htt
  refine ⟨fun h_weak => ?_, fun h_strict => ?_⟩
  · linarith
  · linarith

/-! ## §2 Abstract lattice-form Theorem 4 (sufficient direction)

Verbatim formalization of Milgrom-Shannon (1994), *Econometrica*,
Theorem 4, sufficient half: on a `Lattice` choice space, quasi-
supermodularity in the choice combined with single-crossing in the
parameter implies strong-set-order monotonicity of the argmax
correspondence. -/

section Abstract

variable {X : Type*} [Lattice X] {T : Type*} [Preorder T]
         {Payoff : Type*} [Preorder Payoff]

/-- **Argmax correspondence** at parameter `t` over feasible set `S`. -/
def Argmax (S : Set X) (f : X → T → Payoff) (t : T) : Set X :=
  {x | x ∈ S ∧ ∀ y ∈ S, f y t ≤ f x t}

/-- **Strong set order**. `StrongSetLe A B` means: for every `a ∈ A` and
`b ∈ B`, the meet `a ⊓ b` lies in the lower set `A`, and the join
`a ⊔ b` lies in the higher set `B`. -/
def StrongSetLe (A B : Set X) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → a ⊓ b ∈ A ∧ a ⊔ b ∈ B

/-- **Argmax monotonicity** in the strong-set order: for every pair of
feasible sets `S, S'` with `S ≤ₛ S'` and parameters `t ≤ t'`, the
argmax sets satisfy `Argmax S f t ≤ₛ Argmax S' f t'`. -/
def ArgmaxMonotone (f : X → T → Payoff) : Prop :=
  ∀ S S' t t', StrongSetLe S S' → t ≤ t' →
    StrongSetLe (Argmax S f t) (Argmax S' f t')

/-- **Quasi-supermodularity comparisons** (lattice form). For all
`x, y, t`:

* if the value at the meet weakly dominates the value at `x`, then
  the value at `y` is weakly dominated by the value at the join;
* if the value at the join weakly dominates the value at `y`, then
  the value at `x` is weakly dominated by the value at the meet.

This is the comparison form of quasi-supermodularity used in the
sufficient half of MS Theorem 4. -/
def QuasiSupermodularComparisons (f : X → T → Payoff) : Prop :=
  ∀ x y t,
    (f (x ⊓ y) t ≤ f x t → f y t ≤ f (x ⊔ y) t) ∧
    (f (x ⊔ y) t ≤ f y t → f x t ≤ f (x ⊓ y) t)

/-- **Single-crossing comparisons** (lattice form). For all `x, y, t, t'`
with `t ≤ t'`:

* (weak)   `f(y, t) ≤ f(x ⊔ y, t)  →  f(y, t') ≤ f(x ⊔ y, t')`,
* (reverse) `f(x ⊔ y, t') ≤ f(y, t')  →  f(x ⊔ y, t) ≤ f(y, t)`.

The "reverse" clause supplies the contrapositive form used in the
meet branch of MS Theorem 4. -/
def SingleCrossingComparisons (f : X → T → Payoff) : Prop :=
  ∀ x y t t', t ≤ t' →
    (f y t ≤ f (x ⊔ y) t → f y t' ≤ f (x ⊔ y) t') ∧
    (f (x ⊔ y) t' ≤ f y t' → f (x ⊔ y) t ≤ f y t)

/-- **Milgrom-Shannon Theorem 4 (sufficient direction), lattice form.**

On any lattice choice space `X` with preordered parameter `T` and
preordered payoff, if `f` is quasi-supermodular in the choice
(`QuasiSupermodularComparisons f`) and satisfies single-crossing in
the parameter (`SingleCrossingComparisons f`), then the argmax
correspondence is monotone in the strong-set order. -/
theorem argmax_monotone_of_quasiSupermodular_singleCrossing
    {f : X → T → Payoff}
    (hqsm : QuasiSupermodularComparisons f)
    (hsc : SingleCrossingComparisons f) :
    ArgmaxMonotone f := by
  intro S S' t t' hS htt x hx y hy
  obtain ⟨hxS, hxopt⟩ := hx
  obtain ⟨hyS', hyopt⟩ := hy
  obtain ⟨hmeetS, hjoinS'⟩ := hS hxS hyS'
  refine ⟨⟨hmeetS, ?_⟩, ⟨hjoinS', ?_⟩⟩
  · -- ∀ z ∈ S, f z t ≤ f (x ⊓ y) t
    intro z hzS
    -- Step 1: y is t'-optimal on S' and x ⊔ y ∈ S', so f (x⊔y) t' ≤ f y t'.
    have hjoin_le_y_t' : f (x ⊔ y) t' ≤ f y t' := hyopt _ hjoinS'
    -- Step 2: SCC (reverse) lifts the t'-comparison back to t.
    have hjoin_le_y_t : f (x ⊔ y) t ≤ f y t :=
      (hsc x y t t' htt).2 hjoin_le_y_t'
    -- Step 3: QSM (second conjunct) gives the meet-side comparison.
    have hx_le_meet : f x t ≤ f (x ⊓ y) t := (hqsm x y t).2 hjoin_le_y_t
    -- Chain: f z t ≤ f x t ≤ f (x⊓y) t.
    exact le_trans (hxopt z hzS) hx_le_meet
  · -- ∀ z ∈ S', f z t' ≤ f (x ⊔ y) t'
    intro z hzS'
    -- Step 1: x is t-optimal on S and x ⊓ y ∈ S, so f (x⊓y) t ≤ f x t.
    have hmeet_le_x_t : f (x ⊓ y) t ≤ f x t := hxopt _ hmeetS
    -- Step 2: QSM (first conjunct) gives the join-side comparison at t.
    have hy_le_join_t : f y t ≤ f (x ⊔ y) t := (hqsm x y t).1 hmeet_le_x_t
    -- Step 3: SCC (weak) lifts the t-comparison forward to t'.
    have hy_le_join_t' : f y t' ≤ f (x ⊔ y) t' :=
      (hsc x y t t' htt).1 hy_le_join_t
    -- Chain: f z t' ≤ f y t' ≤ f (x⊔y) t'.
    exact le_trans (hyopt z hzS') hy_le_join_t'

end Abstract

/-! ## §3 Scalar bridges on ℝ

The choice space `ℝ` is a chain, so:

* meet and join collapse to one of the two arguments;
  quasi-supermodularity (`QuasiSupermodularComparisons`) is therefore
  automatic;
* the scalar `SingleCrossing` of §1 implies the lattice-form
  `SingleCrossingComparisons` of §2 (with respect to the standard
  order on the parameter `T = ℝ`).

These let us derive the scalar consumer wrappers in §4 from the
abstract Theorem 4 of §2. -/

/-- On `ℝ` (a chain), quasi-supermodularity is automatic: meet and join
collapse to the inputs themselves, so the QSM implications hold by
reflexivity. -/
theorem quasiSupermodular_real (f : ℝ → ℝ → ℝ) :
    QuasiSupermodularComparisons f := by
  intro x y t
  rcases le_total x y with hxy | hxy
  · -- x ≤ y ⇒ x ⊓ y = x, x ⊔ y = y; both conclusions become `_ ≤ _` reflexivity
    have hmin : x ⊓ y = x := min_eq_left hxy
    have hmax : x ⊔ y = y := max_eq_right hxy
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hmax]
    · rw [hmin]
  · -- y ≤ x ⇒ x ⊓ y = y, x ⊔ y = x; both implications collapse to identity
    have hmin : x ⊓ y = y := min_eq_right hxy
    have hmax : x ⊔ y = x := max_eq_left hxy
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hmin] at h; rw [hmax]; exact h
    · rw [hmax] at h; rw [hmin]; exact h

/-- The scalar `SingleCrossing` of §1 implies the lattice-form
`SingleCrossingComparisons` of §2 on `ℝ` (with the standard order on
both the choice and parameter axes).

The lattice form quantifies over the join `x ⊔ y`; case-splitting on
`x ≤ y` versus `y ≤ x`:

* if `x ≤ y` then `x ⊔ y = y` and both clauses are tautologies;
* if `y ≤ x` then `x ⊔ y = x`, and the weak clause becomes the scalar
  weak SC with `(y, x)` as the choice pair, while the reverse clause
  is the contrapositive of the strict scalar SC. -/
theorem singleCrossingComparisons_of_scalar
    {f : ℝ → ℝ → ℝ} (hSC : SingleCrossing f) :
    SingleCrossingComparisons f := by
  intro x y t t' htt
  rcases le_total x y with hxy | hxy
  · -- x ⊔ y = y, both clauses become tautologies of the form `f y _ ≤ f y _`
    have hmax : x ⊔ y = y := max_eq_right hxy
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rw [hmax]
  · -- x ⊔ y = x; weak clause uses (y, x) weak SC; reverse uses strict SC contrapositive
    have hmax : x ⊔ y = x := max_eq_left hxy
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hmax] at h ⊢
      exact (hSC hxy htt).1 h
    · rw [hmax] at h ⊢
      by_contra h'
      push Not at h'
      -- h' : f y t < f x t ⇒ strict SC ⇒ f y t' < f x t', contradicts h.
      exact absurd ((hSC hxy htt).2 h') (not_lt.mpr h)

/-! ## §4 Scalar consumer wrappers

The two scalar lemmas consumed by `Theory/Basin/JointPreferenceBasin`
and elsewhere. Both are derived from the abstract Theorem 4 of §2 via
the bridges of §3, applied to the two-point sublattice `{x, x'} ⊆ ℝ`.

On the chain `ℝ`, any two-element set is closed under `min` and `max`
(since both collapse to one of the two inputs), so `{x, x'}` is
automatically a sublattice — no extra hypothesis on the consumer's
feasible set `S` is required. -/

/-- The two-point set `{x, x'} ⊆ ℝ` is closed under `min` and `max`. -/
private lemma pair_strongSetLe (x x' : ℝ) :
    StrongSetLe ({x, x'} : Set ℝ) ({x, x'} : Set ℝ) := by
  intro a ha b hb
  refine ⟨?_, ?_⟩
  · -- a ⊓ b = min a b is in {x, x'} since min picks one of the inputs
    rcases min_choice a b with h | h
    · rw [show a ⊓ b = min a b from rfl, h]; exact ha
    · rw [show a ⊓ b = min a b from rfl, h]; exact hb
  · -- a ⊔ b = max a b is in {x, x'} since max picks one of the inputs
    rcases max_choice a b with h | h
    · rw [show a ⊔ b = max a b from rfl, h]; exact ha
    · rw [show a ⊔ b = max a b from rfl, h]; exact hb

/-- **Milgrom-Shannon Theorem 4 (scalar form).**

Suppose `f : ℝ → ℝ → ℝ` has the single-crossing property (§1),
`S ⊆ ℝ` is any feasible set, and `x, x'` are respective
`t`-maximizers and `t'`-maximizers on `S` with `t ≤ t'`. Then:

* `min x x'` weakly dominates every `S`-element at parameter `t`;
* `max x x'` weakly dominates every `S`-element at parameter `t'`.

(On the chain `ℝ`, `min x x'` and `max x x'` are always one of
`x, x'`, so we do not need `S` itself to be a sublattice — the
abstract Theorem 4 of §2 is applied to the two-point sublattice
`{x, x'}` and the conclusion is then chained with the original
`S`-optimality of `x` and `x'`.)

This is the form consumed by
`dynamicTopRealizedRule_mono_of_singleCrossing` in
`Theory/Basin/JointPreferenceBasin.lean`. -/
theorem monotone_argmax_of_singleCrossing
    {f : ℝ → ℝ → ℝ} (hSC : SingleCrossing f)
    {S : Set ℝ}
    {x x' t t' : ℝ}
    (htt : t ≤ t')
    (hx_in : x ∈ S) (hx'_in : x' ∈ S)
    (hx_max : ∀ y ∈ S, f y t ≤ f x t)
    (hx'_max : ∀ y ∈ S, f y t' ≤ f x' t') :
    (∀ y ∈ S, f y t ≤ f (min x x') t) ∧
    (∀ y ∈ S, f y t' ≤ f (max x x') t') := by
  -- Apply the abstract Theorem 4 (§2) to the two-point sublattice {x, x'}.
  -- On {x, x'}: x is a t-maximizer (f x' t ≤ f x t follows from hx_max);
  -- x' is a t'-maximizer (f x t' ≤ f x' t' follows from hx'_max).
  have hx_arg : x ∈ Argmax ({x, x'} : Set ℝ) f t := by
    refine ⟨Or.inl rfl, ?_⟩
    intro y hy
    rcases hy with rfl | rfl
    · exact le_refl _
    · exact hx_max _ hx'_in
  have hx'_arg : x' ∈ Argmax ({x, x'} : Set ℝ) f t' := by
    refine ⟨Or.inr rfl, ?_⟩
    intro y hy
    rcases hy with rfl | rfl
    · exact hx'_max _ hx_in
    · exact le_refl _
  -- Abstract Theorem 4 + scalar bridges, applied to S = S' = {x, x'}.
  have hlat := argmax_monotone_of_quasiSupermodular_singleCrossing
    (quasiSupermodular_real f)
    (singleCrossingComparisons_of_scalar hSC)
    ({x, x'} : Set ℝ) ({x, x'} : Set ℝ) t t'
    (pair_strongSetLe x x') htt hx_arg hx'_arg
  obtain ⟨⟨_, hmin_dom⟩, ⟨_, hmax_dom⟩⟩ := hlat
  -- hmin_dom : ∀ z ∈ {x, x'}, f z t ≤ f (x ⊓ x') t  (with ⊓ = min on ℝ)
  -- hmax_dom : ∀ z ∈ {x, x'}, f z t' ≤ f (x ⊔ x') t' (with ⊔ = max on ℝ)
  refine ⟨?_, ?_⟩
  · intro y hy
    calc f y t ≤ f x t := hx_max y hy
      _ ≤ f (x ⊓ x') t := hmin_dom x (Or.inl rfl)
      _ = f (min x x') t := rfl
  · intro y hy
    calc f y t' ≤ f x' t' := hx'_max y hy
      _ ≤ f (x ⊔ x') t' := hmax_dom x' (Or.inr rfl)
      _ = f (max x x') t' := rfl

/-- **Corollary: single-valued argmax is monotone non-decreasing.**
If the argmax is single-valued at both `t` and `t'`, the conclusion of
`monotone_argmax_of_singleCrossing` collapses to `x ≤ x'`. -/
theorem argmax_le_of_singleCrossing_strict
    {f : ℝ → ℝ → ℝ} (hSC : SingleCrossing f)
    {S : Set ℝ}
    {x x' t t' : ℝ}
    (htt : t ≤ t')
    (hx_in : x ∈ S) (hx'_in : x' ∈ S)
    (hx_max : ∀ y ∈ S, y ≠ x → f y t < f x t)
    (hx'_max : ∀ y ∈ S, y ≠ x' → f y t' < f x' t') :
    x ≤ x' := by
  by_contra h_lt
  push Not at h_lt
  -- Have `x' < x`. Apply the monotone-argmax conclusion in weak form.
  have hx_max_weak : ∀ y ∈ S, f y t ≤ f x t := by
    intro y hy
    by_cases hyx : y = x
    · rw [hyx]
    · exact le_of_lt (hx_max y hy hyx)
  have hx'_max_weak : ∀ y ∈ S, f y t' ≤ f x' t' := by
    intro y hy
    by_cases hyx : y = x'
    · rw [hyx]
    · exact le_of_lt (hx'_max y hy hyx)
  have ⟨h_min_max, _⟩ :=
    monotone_argmax_of_singleCrossing hSC htt hx_in hx'_in hx_max_weak hx'_max_weak
  -- `min x x' = x'` since `x' < x`, so `x'` is a (weak) `t`-maximizer.
  rw [min_eq_right (le_of_lt h_lt)] at h_min_max
  have h_x_le_x' : f x t ≤ f x' t := h_min_max x hx_in
  -- For `y = x' ∈ S` with `x' ≠ x`, strict `t`-optimality of `x` gives
  -- `f x' t < f x t`. Combined with `f x t ≤ f x' t`, contradiction.
  have h_x_ne_x' : x ≠ x' := ne_of_gt h_lt
  have h_x'_lt_x_at_t : f x' t < f x t := hx_max x' hx'_in h_x_ne_x'.symm
  linarith

/-! ## §4b Localized single crossing (audit-28 #1)

The `SingleCrossing` predicate of §1 quantifies the choice and parameter
inequalities over all of `ℝ`. Project consumers only ever apply it on the
feasible choice set `Sanctions.I = [0,1]` and on a basin parameter set
`[xbar, 1]`. The audit recommends exposing a *localized* version that
quantifies only on those sets, since the global form is strictly stronger
than what the comparative-statics step needs.

`SingleCrossingOn S T f` requires the single-crossing implications only
when both choices lie in `S` and both parameters in `T`. A bridge
`SingleCrossing.toSingleCrossingOn` lets a caller with the global form
specialize to any pair `(S, T)`; the localized consumer
`monotone_argmax_of_singleCrossingOn` is the basin-restricted analogue of
`monotone_argmax_of_singleCrossing` used by
`Theory/Basin/JointPreferenceBasin.lean`. -/

/-- **Localized single crossing.** `SingleCrossingOn S T f` requires the
single-crossing implications only when both choices `x, y` lie in `S` and
both parameters `t, t'` lie in `T`. Strictly weaker than `SingleCrossing f`
(which corresponds to `S = T = Set.univ`); the bridge
`SingleCrossing.toSingleCrossingOn` discharges the localized form from the
global one for any pair `(S, T)`. -/
def SingleCrossingOn (S T : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃x y t t' : ℝ⦄, x ∈ S → y ∈ S → x ≤ y → t ∈ T → t' ∈ T → t ≤ t' →
    (f x t ≤ f y t → f x t' ≤ f y t') ∧
    (f x t < f y t → f x t' < f y t')

/-- **Bridge: global single crossing implies the localized form.** Any
pair of sets `(S, T)` admits the localized version as an immediate
specialization. -/
theorem SingleCrossing.toSingleCrossingOn
    {f : ℝ → ℝ → ℝ} (hSC : SingleCrossing f) (S T : Set ℝ) :
    SingleCrossingOn S T f := by
  intro x y t t' _ _ hxy _ _ htt
  exact hSC hxy htt

/-- **Localized analogue of `monotone_argmax_of_singleCrossing`.**
Same conclusion (the meet/join of two maximizers is a maximizer at the
lower/higher parameter respectively) but the single-crossing hypothesis is
only required on `S × T`, where `S` contains the maximizers and `T`
contains the two parameter values.

This is the form consumed by
`dynamicTopRealizedRule_mono_of_singleCrossingOn` in
`Theory/Basin/JointPreferenceBasin.lean`. -/
theorem monotone_argmax_of_singleCrossingOn
    {f : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hSC : SingleCrossingOn S T f)
    {x x' t t' : ℝ}
    (htt : t ≤ t') (ht_in : t ∈ T) (ht'_in : t' ∈ T)
    (hx_in : x ∈ S) (hx'_in : x' ∈ S)
    (hx_max : ∀ y ∈ S, f y t ≤ f x t)
    (hx'_max : ∀ y ∈ S, f y t' ≤ f x' t') :
    (∀ y ∈ S, f y t ≤ f (min x x') t) ∧
    (∀ y ∈ S, f y t' ≤ f (max x x') t') := by
  -- Mirror of `monotone_argmax_of_singleCrossing` with all SC applications
  -- restricted to the pair `(S, T)` via the localized predicate. The
  -- abstract Theorem 4 (§2) is generic in its lattice / parameter
  -- structure, so we cannot reuse it directly with a set-localized SC.
  -- Instead we case-split on whether `x ≤ x'` (the "right" order, trivial)
  -- or `x' ≤ x` (the swap, requiring the SC lift).
  rcases le_total x x' with hxx | hxx
  · -- Case x ≤ x': min x x' = x, max x x' = x'; the maximizer claims are
    -- the input hypotheses applied refl.
    refine ⟨?_, ?_⟩
    · intro y hy; rw [min_eq_left hxx]; exact hx_max y hy
    · intro y hy; rw [max_eq_right hxx]; exact hx'_max y hy
  · -- Case x' ≤ x: min x x' = x', max x x' = x.
    -- Apply the localized SC at (a := x', b := x, t ≤ t'), both choices in S.
    have hSC_pair := hSC hx'_in hx_in hxx ht_in ht'_in htt
    -- x-optimality at t gives `f x' t ≤ f x t`; lift via SC to
    -- `f x' t' ≤ f x t'`. Combined with x'-optimality at t', `f x t' ≤ f x' t'`.
    have h_at_t : f x' t ≤ f x t := hx_max x' hx'_in
    have h_at_t' : f x' t' ≤ f x t' := hSC_pair.1 h_at_t
    have h_eq_t' : f x t' ≤ f x' t' := hx'_max x hx_in
    -- The strict SC clause closes equality at `t`: if `f x' t < f x t` then
    -- `f x' t' < f x t'`, contradicting `f x t' ≤ f x' t'`.
    have h_eq_at_t : f x' t = f x t := by
      by_contra h_ne
      have h_lt : f x' t < f x t := lt_of_le_of_ne h_at_t h_ne
      have h_strict_t' : f x' t' < f x t' := hSC_pair.2 h_lt
      linarith
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [min_eq_right hxx]
      have := hx_max y hy
      linarith [h_eq_at_t]
    · intro y hy
      rw [max_eq_left hxx]
      have := hx'_max y hy
      linarith

/-! ## §5 Boundary-argmax: StrictMonoOn ⇒ unique maximizer

Milgrom-Shannon Theorem 4 covers the *order*-monotonicity of the argmax
correspondence under single crossing. A *separate* but related fact —
also discussed in MS §4 in the strict-monotonicity / boundary-argmax
discussion — is that a *strictly monotone* function on a non-empty
totally-ordered domain has its set of maximizers reduced to a unique
boundary point.

The Round-24 use case: the `polyComplianceParams` witness in
`Sanctions/Examples/StandardCompliancePolynomialSkeleton.lean` has a
*linear* Sender per-period payoff `U_S(x, a, s) = s`, which is **not
strictly concave** in `s` — the strict-concavity discharger
`dynamicArgmaxUnique_of_strictConcaveOn` therefore cannot apply. But
linear `s ↦ s` *is* strictly monotone increasing on `[0, 1]`, and its
unique maximizer is the upper boundary `s = 1`. The lemma below
captures this generic uniqueness fact independently of any concavity
hypothesis, so it can serve as the discharger basis for both the
Sender and Target uniqueness predicates in the linear-payoff
witness. -/

/-- **Strictly monotone-on ⇒ at most one maximizer.** A strictly
monotone function `f` on any set `S` (in a linearly-ordered domain)
has the property that any two `IsMaxOn`-witnesses agree. The proof is
the standard antisymmetry argument: if `s₁ ≠ s₂`, WLOG `s₁ < s₂`,
strict monotonicity gives `f s₁ < f s₂`, but `s₁` being a max-witness
gives `f s₂ ≤ f s₁`, contradicting strict inequality.

Note this is for *strictly increasing* `f`; a strictly decreasing
companion would just swap the roles of `s₁, s₂`. Both are unified by
applying this lemma to either `f` or `-f` as appropriate. -/
theorem isMaxOn_unique_of_strictMonoOn
    {α β : Type*} [LinearOrder α] [Preorder β]
    {f : α → β} {S : Set α}
    (hmono : StrictMonoOn f S)
    {s₁ s₂ : α}
    (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S)
    (h₁ : IsMaxOn f S s₁) (h₂ : IsMaxOn f S s₂) :
    s₁ = s₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- s₁ < s₂: strict mono ⇒ f s₁ < f s₂; max-at-s₁ ⇒ f s₂ ≤ f s₁; contradiction.
    have h_lt : f s₁ < f s₂ := hmono hs₁ hs₂ hlt
    have h_le : f s₂ ≤ f s₁ := h₁ hs₂
    exact lt_irrefl (f s₁) (lt_of_lt_of_le h_lt h_le)
  · -- s₁ > s₂: symmetric.
    have h_lt : f s₂ < f s₁ := hmono hs₂ hs₁ hgt
    have h_le : f s₁ ≤ f s₂ := h₂ hs₁
    exact lt_irrefl (f s₂) (lt_of_lt_of_le h_lt h_le)

/-! ## Provenance and connection to the rest of the project

* §1 (scalar SC + ID) and §4 (scalar consumer wrappers) are the API
  consumed by `Theory/Basin/JointPreferenceBasin.lean`
  (`dynamicTopRealizedRule_mono_of_singleCrossing`,
  `oneSidedThresholds_long_run_nonDecreasing_of_singleCrossing` and
  siblings, `equilibriumTop_oneSidedThresholds_*_of_singleCrossing`).
  The signatures of §4 are unchanged from earlier revisions; only the
  *proofs* now route through the abstract Theorem 4 of §2.

* §2 is the *full* Milgrom-Shannon (1994) Theorem 4 sufficient
  direction at the abstract `Lattice` level. It is self-contained — no
  external library dependency — and may be reused in any future
  multi-dimensional comparative-statics step.

* The implication `IncreasingDifferences → SingleCrossing` (§1)
  records that MS Theorem 4 is a *strict* generalization of the
  Topkis sufficient condition for monotone argmax.

For scalar `x`, the existing `Foundations/Supermodular.lean` and
`Foundations/TopkisDD.lean` infrastructure proves DD/ID preservation
under abstract complete-lattice operators; this file's §4 is the
scalar comparative-statics conclusion under the weaker single-crossing
condition. -/

/-! ## §6 Dual antitone-selection (Round-28: decreasing differences ⇒ antitone argmax)

Round 28 adds the **dual** of §1–§4: the *decreasing*-differences /
*antitone*-argmax direction of Milgrom-Shannon / Topkis. The reading is:

* If `f(s, a)` has *decreasing differences* in `(s, a)` — i.e. the
  marginal gain from raising `s` is non-increasing in the parameter `a`
  — then the argmax in `s` is *antitone* in `a` (more parameter ⇒
  smaller maximizer).

Economic use (Sanctions Round-28): with `f(s, a) := U_S(x, a, s)` — the
Sender's stage payoff as a function of sanction-realization `s` at fixed
target compliance `a` — decreasing cross-differences `∂²U_S/∂s∂a ≤ 0`
(the marginal Sender gain from more sanctions falls as the Target
complies more) yield σ-antitone-in-`a`, the cross-policy myopic-ceiling
sub-primitive of the four-primitive `myopicCeiling_of_alpha_floor_and_
sigma_antitoneOn` decomposition.

Reference: Milgrom-Shannon (1994), *Econometrica*, Theorem 4' (Monotone
Selection, dual statement) + Topkis (1998) *Supermodularity and
Complementarity*, dual Monotonicity Theorem.

The proof is the antitone-mirror of §4: we reduce to §2's abstract
Theorem 4 by passing through the order-reversal `t ↦ -t` on the
parameter axis. For scalar choice / parameter on `ℝ` this is a direct
swap, and we present it as a self-contained derivation. -/

/-- **Decreasing differences** (scalar dual of `IncreasingDifferences`).
For `x ≤ y` and `t ≤ t'`:  `f(y, t') − f(x, t') ≤ f(y, t) − f(x, t)`.

The "preference for higher `x` weakens as `t` rises" reading is dual to
the §1 ID condition. C² form: `∂²f/∂x∂t ≤ 0`. -/
def DecreasingDifferences (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃x y t t' : ℝ⦄, x ≤ y → t ≤ t' →
    f y t' - f x t' ≤ f y t - f x t

/-- **Localized decreasing differences.** Same as `DecreasingDifferences`
but quantifies only over `x, y ∈ S` and `t, t' ∈ T`. Strictly weaker than
the global form (which corresponds to `S = T = Set.univ`); the bridge
`DecreasingDifferences.toDecreasingDifferencesOn` discharges the
localized form from the global one for any pair `(S, T)`. -/
def DecreasingDifferencesOn (S T : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃x y t t' : ℝ⦄, x ∈ S → y ∈ S → x ≤ y → t ∈ T → t' ∈ T → t ≤ t' →
    f y t' - f x t' ≤ f y t - f x t

/-- **Bridge: global decreasing differences implies the localized form.** -/
theorem DecreasingDifferences.toDecreasingDifferencesOn
    {f : ℝ → ℝ → ℝ} (hDD : DecreasingDifferences f) (S T : Set ℝ) :
    DecreasingDifferencesOn S T f := by
  intro x y t t' _ _ hxy _ _ htt
  exact hDD hxy htt

/-- **Argmax antitone selection from localized decreasing differences.**
The dual of `monotone_argmax_of_singleCrossingOn`. Under
`DecreasingDifferencesOn S T f`, for two parameters `t ≤ t'` in `T` and
two `S`-maximizers `s` (at `t`) and `s'` (at `t'`):

* `max s s'` is also a `t`-maximizer on `S` (the *larger* `s` is
  preferred at the *smaller* parameter);
* `min s s'` is also a `t'`-maximizer on `S` (the *smaller* `s` is
  preferred at the *larger* parameter).

This is the antitone-argmax conclusion: parameter ↑ ⇒ maximizer ↓ (in
the strong-set order). -/
theorem antitone_argmax_of_decreasingDifferencesOn
    {f : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hDD : DecreasingDifferencesOn S T f)
    {s s' t t' : ℝ}
    (htt : t ≤ t') (ht_in : t ∈ T) (ht'_in : t' ∈ T)
    (hs_in : s ∈ S) (hs'_in : s' ∈ S)
    (hs_max : ∀ y ∈ S, f y t ≤ f s t)
    (hs'_max : ∀ y ∈ S, f y t' ≤ f s' t') :
    (∀ y ∈ S, f y t ≤ f (max s s') t) ∧
    (∀ y ∈ S, f y t' ≤ f (min s s') t') := by
  -- Direct antitone-selection argument, mirroring the structure of
  -- `monotone_argmax_of_singleCrossingOn` but with `max`/`min` roles
  -- swapped. Case-split on the order of `s` vs `s'`.
  rcases le_total s s' with hss | hss
  · -- Case s ≤ s': max s s' = s', min s s' = s. We need to show
    --   (a) s' is also a t-maximizer (challenging direction — needs DD lift),
    --   (b) s is also a t'-maximizer (challenging direction — needs DD lift).
    -- Apply DD at (s, s', t, t'): f s' t' - f s t' ≤ f s' t - f s t.
    have hDD_pair := hDD hs_in hs'_in hss ht_in ht'_in htt
    -- s-optimality at t: f s' t ≤ f s t.
    have h_at_t : f s' t ≤ f s t := hs_max s' hs'_in
    -- s'-optimality at t': f s t' ≤ f s' t'.
    have h_at_t' : f s t' ≤ f s' t' := hs'_max s hs_in
    -- From DD: f s' t' - f s t' ≤ f s' t - f s t ≤ 0 (by h_at_t), so
    -- f s' t' ≤ f s t', combined with h_at_t' gives equality at t'.
    -- Symmetrically: f s' t' - f s t' ≤ f s' t - f s t and f s t' ≤ f s' t'
    -- gives f s' t - f s t ≥ f s' t' - f s t' ≥ 0, so f s' t ≥ f s t,
    -- combined with h_at_t gives equality at t.
    have h_eq_at_t : f s' t = f s t := by
      have h1 : f s t - f s' t ≤ f s t' - f s' t' := by linarith
      have h2 : f s t' - f s' t' ≤ 0 := by linarith [h_at_t']
      have h3 : f s t - f s' t ≤ 0 := le_trans h1 h2
      have h4 : f s t ≤ f s' t := by linarith
      exact le_antisymm h_at_t h4
    have h_eq_at_t' : f s t' = f s' t' := by
      have h1 : f s' t - f s t ≤ f s' t' - f s t' := by
        -- This is the *opposite* direction from DD; instead use the
        -- equality at t and rearrange DD directly.
        have := hDD_pair  -- f s' t' - f s t' ≤ f s' t - f s t = 0
        rw [h_eq_at_t] at this
        linarith
      have h2 : f s' t' ≤ f s t' := by linarith [h_eq_at_t]
      exact le_antisymm h_at_t' h2
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [max_eq_right hss]
      have := hs_max y hy
      linarith [h_eq_at_t]
    · intro y hy
      rw [min_eq_left hss]
      have := hs'_max y hy
      linarith [h_eq_at_t']
  · -- Case s' ≤ s: max s s' = s, min s s' = s'. Both conclusions are
    -- direct applications of the input maximizer hypotheses.
    refine ⟨?_, ?_⟩
    · intro y hy; rw [max_eq_left hss]; exact hs_max y hy
    · intro y hy; rw [min_eq_right hss]; exact hs'_max y hy

/-- **Antitone selector from decreasing differences + strict uniqueness.**
Pointwise antitone direct corollary: if `f` has decreasing differences
on `S × T`, both `t`-maximizer `s` and `t'`-maximizer `s'` are *strictly
unique* on `S`, and `t ≤ t'`, then `s' ≤ s`.

This is the direct form consumed by the Sanctions Round-28 wrapper
`sigma_antitoneOn_a_of_U_S_decreasing_differences`: the Sender selector
`σ(x, a)` is a strict argmax, so under DD of `U_S(x, ·, ·)` in `(s, a)`
we get `σ(x, a₂) ≤ σ(x, a₁)` for `a₁ ≤ a₂` directly. -/
theorem argmax_antitone_of_decreasingDifferencesOn_strict
    {f : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hDD : DecreasingDifferencesOn S T f)
    {s s' t t' : ℝ}
    (htt : t ≤ t') (ht_in : t ∈ T) (ht'_in : t' ∈ T)
    (hs_in : s ∈ S) (hs'_in : s' ∈ S)
    (hs_max : ∀ y ∈ S, y ≠ s → f y t < f s t)
    (hs'_max : ∀ y ∈ S, y ≠ s' → f y t' < f s' t') :
    s' ≤ s := by
  by_contra h_lt
  push Not at h_lt
  -- Have `s < s'`. Apply the set-valued antitone conclusion in weak form.
  have hs_max_weak : ∀ y ∈ S, f y t ≤ f s t := by
    intro y hy
    by_cases hys : y = s
    · rw [hys]
    · exact le_of_lt (hs_max y hy hys)
  have hs'_max_weak : ∀ y ∈ S, f y t' ≤ f s' t' := by
    intro y hy
    by_cases hys : y = s'
    · rw [hys]
    · exact le_of_lt (hs'_max y hy hys)
  have ⟨h_max_dom, _⟩ :=
    antitone_argmax_of_decreasingDifferencesOn hDD htt ht_in ht'_in
      hs_in hs'_in hs_max_weak hs'_max_weak
  -- `max s s' = s'` since `s < s'`, so `s'` is a (weak) `t`-maximizer.
  rw [max_eq_right (le_of_lt h_lt)] at h_max_dom
  have h_s_le_s' : f s t ≤ f s' t := h_max_dom s hs_in
  -- For `y = s' ∈ S` with `s' ≠ s`, strict `t`-optimality of `s` gives
  -- `f s' t < f s t`. Combined with `f s t ≤ f s' t`, contradiction.
  have h_s_ne_s' : s ≠ s' := ne_of_lt h_lt
  have h_strict : f s' t < f s t := hs_max s' hs'_in h_s_ne_s'.symm
  linarith

/-! ## §7 Smooth cross-partial discharger (Round-29)

Milgrom-Shannon (1994) Theorem 6 + Topkis (1998) Theorem 2.6.1 / Curtat
(1996) Lemma 1: a C¹ function `f : ℝ → ℝ → ℝ` on a rectangle `S × T`
has *increasing differences* whenever the partial derivative
`∂f/∂x(s, x) := f_x s x` is **non-decreasing in `s`** on the rectangle.

Equivalently for C² functions: `∂²f/∂s∂x ≥ 0` on the rectangle implies
ID. This is the canonical "smooth" route to the Spence-Mirrlees / single-
crossing condition: one need only check the sign of a single cross-
partial, not chord-style comparisons.

In §7 we:

* introduce a localized predicate `IncreasingDifferencesOn S T f`
  (mirror of `SingleCrossingOn`);
* bridge it to `SingleCrossingOn` (ID ⇒ SC, the §1 analogue);
* prove the smooth discharger
  `IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on` —
  whenever `(fun x => f s x)` is C¹ on `T` with derivative `f_x s ·`
  for every `s ∈ S`, and `(fun s => f_x s x)` is non-decreasing on
  `S` for every `x ∈ T`, then `IncreasingDifferencesOn S T f`.

The discharger is the Sanctions Round-29 entry point for the carrier-
local single-crossing primitive `hSC_on` (the cross-partial criterion
for the Sender dynamic objective under the saturated-α regime).

### Mathematical reading

Set `g(x) := f s' x − f s x` for `s ≤ s'`. We want `g` non-decreasing
on `T`. Its derivative is `g'(x) = f_x s' x − f_x s x ≥ 0` by the
monotonicity hypothesis on `f_x ·  x`. The MVT lemma
`Convex.mul_sub_le_image_sub_of_le_deriv` with constant `C := 0`
then yields `g(x') − g(x) ≥ 0`, which is `IncreasingDifferences`. -/

/-- **Localized increasing differences.** `IncreasingDifferencesOn S T f`
requires the chord inequality only when both first-argument values
`s, s'` lie in `S` and both second-argument values `x, x'` lie in `T`.
Strictly weaker than `IncreasingDifferences f` (which corresponds to
`S = T = Set.univ`); the bridge
`IncreasingDifferences.toIncreasingDifferencesOn` discharges the
localized form from the global one for any pair `(S, T)`. -/
def IncreasingDifferencesOn (S T : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃s s' x x' : ℝ⦄, s ∈ S → s' ∈ S → s ≤ s' → x ∈ T → x' ∈ T → x ≤ x' →
    f s' x - f s x ≤ f s' x' - f s x'

/-- **Bridge: global increasing differences implies the localized form.** -/
theorem IncreasingDifferences.toIncreasingDifferencesOn
    {f : ℝ → ℝ → ℝ} (hID : IncreasingDifferences f) (S T : Set ℝ) :
    IncreasingDifferencesOn S T f := by
  intro s s' x x' _ _ hss _ _ hxx
  exact hID hss hxx

/-- **Bridge: localized increasing differences implies localized single
crossing.** Same direction as the global `IncreasingDifferences.toSingleCrossing`,
restricted to the rectangle `S × T`.

Note the argument-order convention: `SingleCrossingOn S T f` treats
`f : ℝ → ℝ → ℝ` as `f x t`, with `x` ranging in `S` and `t` in `T`
(this is the convention used by `senderDynObjective`-style consumers).
`IncreasingDifferencesOn S T f` uses the same convention. -/
theorem IncreasingDifferencesOn.toSingleCrossingOn
    {f : ℝ → ℝ → ℝ} {S T : Set ℝ} (hID : IncreasingDifferencesOn S T f) :
    SingleCrossingOn S T f := by
  intro x y t t' hx hy hxy ht ht' htt
  have h := hID hx hy hxy ht ht' htt
  refine ⟨fun h_weak => ?_, fun h_strict => ?_⟩
  · linarith
  · linarith

/-- **Smooth cross-partial discharger for localized increasing differences
(Milgrom-Shannon 1994 Theorem 6 / Topkis 1998 Theorem 2.6.1 / Curtat 1996
Lemma 1).**

If `f : ℝ → ℝ → ℝ` is C¹ in its second argument (the parameter `x`) on
a convex set `T ⊆ ℝ`, with partial derivative function
`f_x : ℝ → ℝ → ℝ` such that
`HasDerivAt (fun x => f s x) (f_x s x) x` for every `s ∈ S, x ∈ T`,
and the cross-partial monotonicity
`∀ x ∈ T, ∀ s ≤ s' in S, f_x s x ≤ f_x s' x` holds
(equivalently `∂²f/∂s∂x ≥ 0`), then `f` has localized increasing
differences on `S × T`.

This is the **paper-stateable C² primitive** that replaces the chord
hypothesis. For LQ payoffs `f(s, x) = U(x, a₀, s) + β·V(F(x,s))` with
saturated leader action `a₀`, the cross-partial reduces to
`∂²U/∂s∂x(x, a₀, s) + β·V''(F(x,s))·δ(1-δ)`, whose sign is
straightforward to check.

The proof: fix `s ≤ s'` in `S`. Set `g(x) := f s' x - f s x`. Then `g`
is differentiable on `T` with `g'(x) = f_x s' x - f_x s x ≥ 0` by the
cross-partial monotonicity hypothesis. The MVT lemma
`Convex.mul_sub_le_image_sub_of_le_deriv` at `C := 0` yields
`g x' - g x ≥ 0` for `x ≤ x'` in `T`, which rearranges to the ID
chord. -/
theorem IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on
    {f : ℝ → ℝ → ℝ} {S T : Set ℝ} {f_x : ℝ → ℝ → ℝ}
    (hT : Convex ℝ T)
    (h_diff : ∀ s ∈ S, ∀ x ∈ T, HasDerivAt (fun y => f s y) (f_x s x) x)
    (h_cross :
      ∀ x ∈ T, ∀ s ∈ S, ∀ s' ∈ S, s ≤ s' → f_x s x ≤ f_x s' x) :
    IncreasingDifferencesOn S T f := by
  intro s s' x x' hs hs' hss hx hx' hxx
  -- g(y) := f s' y - f s y; want g x ≤ g x'.
  set g : ℝ → ℝ := fun y => f s' y - f s y
  -- Pointwise derivative of g on T: g'(y) = f_x s' y - f_x s y.
  have hg_diff : ∀ y ∈ T, HasDerivAt g (f_x s' y - f_x s y) y := by
    intro y hy
    exact (h_diff s' hs' y hy).sub (h_diff s hs y hy)
  have hg_contOn : ContinuousOn g T :=
    fun y hy => (hg_diff y hy).continuousAt.continuousWithinAt
  have hg_diffOn : DifferentiableOn ℝ g (interior T) := by
    intro y hy
    exact (hg_diff y (interior_subset hy)).differentiableAt.differentiableWithinAt
  -- The supplied derivative equals mathlib's `deriv g` on the interior.
  have hg_deriv_eq : ∀ y ∈ interior T, deriv g y = f_x s' y - f_x s y := by
    intro y hy
    exact (hg_diff y (interior_subset hy)).deriv
  -- Lower bound on `deriv g` on the interior: 0 ≤ deriv g y.
  have h_deriv_ge : ∀ y ∈ interior T, (0 : ℝ) ≤ deriv g y := by
    intro y hy
    rw [hg_deriv_eq y hy]
    have := h_cross y (interior_subset hy) s hs s' hs' hss
    linarith
  -- MVT-style consequence: 0 * (x' - x) ≤ g x' - g x, i.e. g x ≤ g x'.
  have hmvt : (0 : ℝ) * (x' - x) ≤ g x' - g x :=
    hT.mul_sub_le_image_sub_of_le_deriv
      hg_contOn hg_diffOn h_deriv_ge x hx x' hx' hxx
  -- Unfold g and rearrange to the ID chord.
  simp only [g, zero_mul] at hmvt
  linarith


/-! ## Round E4 — two-point discount-weight comparative static

Milgrom-Shannon Theorem 5 read with the discount weight as the
parameter: if the addend `h` is antitone on the choice set, attaching
it with any non-negative weight `β` moves the (unique-base) argmax
weakly DOWN. The derivative-free two-point form of "the myopic agent
chooses a weakly larger action than the forward-looking agent" when
the continuation channel is antitone in the action. -/

/-- **Adding an antitone term moves the argmax down (two-point
chord Topkis).** If `a₀` is the unique maximizer of `g` on `S` and
`a₁` maximizes `g + β·h` with `β ≥ 0` and `h` antitone on `S`, then
`a₁ ≤ a₀`. -/
theorem argmax_le_of_add_antitone {g h : ℝ → ℝ} {S : Set ℝ} {β : ℝ}
    (hβ : 0 ≤ β) (hh_anti : AntitoneOn h S)
    {a₀ a₁ : ℝ} (ha₀ : a₀ ∈ S) (ha₁ : a₁ ∈ S)
    (hmax₀ : ∀ y ∈ S, g y ≤ g a₀)
    (huniq₀ : ∀ y ∈ S, (∀ z ∈ S, g z ≤ g y) → y = a₀)
    (hmax₁ : ∀ y ∈ S, g y + β * h y ≤ g a₁ + β * h a₁) :
    a₁ ≤ a₀ := by
  by_contra hcon
  have hlt : a₀ < a₁ := lt_of_not_ge hcon
  have hanti : h a₁ ≤ h a₀ := hh_anti ha₀ ha₁ (le_of_lt hlt)
  have h1 : g a₀ + β * h a₀ ≤ g a₁ + β * h a₁ := hmax₁ a₀ ha₀
  have h2 : g a₁ ≤ g a₀ := hmax₀ a₁ ha₁
  have hβh : β * (h a₁ - h a₀) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  have h3 : g a₀ ≤ g a₁ := by nlinarith
  have hmax_a₁ : ∀ z ∈ S, g z ≤ g a₁ := fun z hz =>
    le_trans (hmax₀ z hz) h3
  exact absurd (huniq₀ a₁ ha₁ hmax_a₁) (ne_of_gt hlt)


/-! ## Greatest-selector antitonicity, without argmax uniqueness

`antitone_argmax_of_decreasingDifferencesOn` above delivers the strong-set-order
conclusion: at the lower parameter the *larger* of two maximizers is also
optimal, and at the higher parameter the *smaller* one is. That orders the argmax
**correspondence**, and it does not by itself order an arbitrary selection from
it — the standard gap between Topkis-style comparative statics and a statement
about a particular policy function.

The gap closes for one distinguished selection. If the selector always returns
the **greatest** maximizer, the strong-set order collapses to an ordinary
antitone function, with no uniqueness hypothesis anywhere. The argument is a
single step: `max s s'` is optimal at the lower parameter, and the greatest
maximizer there dominates it, so `s' ≤ max s s' ≤ s`.

This is why an extremal selector is worth constructing rather than assuming
single-valuedness. Uniqueness is a regularity condition that fails exactly where
the payoff is flat — ties between choices, kinks, corner plateaus — whereas a
greatest maximizer exists whenever the argmax set is compact and nonempty, which
Weierstrass already supplies. A conclusion resting on uniqueness is also not
selection-robust: it describes the one selection the structure happens to carry
and says nothing about another equally valid one. The greatest-selector route has
neither defect. -/

/-- **The greatest maximizer is antitone in the parameter under decreasing
differences — no uniqueness required.**

`s` is a *greatest* `S`-maximizer at parameter `t`, and `s'` is *any*
`S`-maximizer at the higher parameter `t'`; then `s' ≤ s`. Only `s` is required
to be greatest, so the conclusion also reads as a ceiling on every maximizer at
the higher parameter, not merely on the greatest one. -/
theorem greatest_argmax_antitone_of_decreasingDifferencesOn
    {f : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hDD : DecreasingDifferencesOn S T f)
    {s s' t t' : ℝ}
    (htt : t ≤ t') (ht_in : t ∈ T) (ht'_in : t' ∈ T)
    (hs_in : s ∈ S) (hs'_in : s' ∈ S)
    (hs_max : ∀ y ∈ S, f y t ≤ f s t)
    (hs'_max : ∀ y ∈ S, f y t' ≤ f s' t')
    (hs_greatest : ∀ y ∈ S, (∀ z ∈ S, f z t ≤ f y t) → y ≤ s) :
    s' ≤ s := by
  -- `max s s'` lies in `S`: it is literally one of the two.
  have hmax_mem : max s s' ∈ S := by
    rcases le_total s s' with h | h
    · rw [max_eq_right h]; exact hs'_in
    · rw [max_eq_left h]; exact hs_in
  -- Strong set order: the larger of the two is also optimal at the lower `t`.
  have hmax_opt : ∀ y ∈ S, f y t ≤ f (max s s') t :=
    (antitone_argmax_of_decreasingDifferencesOn hDD htt ht_in ht'_in hs_in hs'_in
      hs_max hs'_max).1
  -- Greatness of `s` at `t` caps it, and `s'` sits below the max.
  exact le_trans (le_max_right s s') (hs_greatest _ hmax_mem hmax_opt)

end MilgromShannon
end Sanctions

end
