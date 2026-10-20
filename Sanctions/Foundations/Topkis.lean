/-
Sanctions/Foundations/Topkis.lean

**Topkis (1998) *Supermodularity and Complementarity*, Chapter 2 — core
lattice and supermodular-argmax theorems.**

This module collects the lattice-theoretic results from Topkis 1998
Chapter 2 that are relevant to monotone comparative statics in the
sanctions model. The earlier `Foundations.Supermodular` and
`Foundations.TopkisDD` modules cover the abstract complete-lattice
Tarski machinery and DD/ID preservation arithmetic; this module adds:

* the **strong set order** (Topkis §2.4) — the natural comparison on
  argmax correspondences;
* **argmax of supermodular function is a sublattice** (Theorem 2.7.1);
* **monotone selection from increasing correspondence** (Theorem 2.4.3
  scalar / linear-order version);
* **supermodular argmax preservation** (Theorem 2.7.6 scalar
  specialization) — the sup of a supermodular function over a
  parameter-dependent sublattice is supermodular in the parameter.

The Milgrom-Shannon scalar argmax-monotonicity Theorem 4 already lives
in `Foundations.MilgromShannon`; this module provides the underlying
Topkis machinery on which Milgrom-Shannon builds.
-/

import Sanctions.Foundations.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLatticeIntervals

noncomputable section

namespace Sanctions
namespace Topkis

/-! ## §2.4 Induced Set Ordering (strong set order) -/

/-- **Strong set order** (Topkis 1998 §2.4). For sets `A B : Set α` in a
lattice, `A ≤ₛₛₒ B` means: for every `a ∈ A` and `b ∈ B`,
`a ⊓ b ∈ A` and `a ⊔ b ∈ B`.

This is the standard induced set order used in monotone comparative
statics: a correspondence `t ↦ S(t)` is increasing iff `t ≤ t'` implies
`S(t) ≤ₛₛₒ S(t')`. -/
def StrongSetOrder {α : Type*} [Lattice α] (A B : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → a ⊓ b ∈ A ∧ a ⊔ b ∈ B

/-- Reflexivity of the strong set order at a sublattice. -/
theorem StrongSetOrder.refl_of_sublattice
    {α : Type*} [Lattice α] {A : Set α}
    (h_meet : ∀ a ∈ A, ∀ b ∈ A, a ⊓ b ∈ A)
    (h_join : ∀ a ∈ A, ∀ b ∈ A, a ⊔ b ∈ A) :
    StrongSetOrder A A := by
  intro a ha b hb
  exact ⟨h_meet a ha b hb, h_join a ha b hb⟩

/-! ## §2.7 Maximizing a Supermodular Function -/

/-- **Supermodular function** (Topkis 1998 Definition 2.6.1) on a
lattice `α`. -/
def Supermodular {α : Type*} [Lattice α] (f : α → ℝ) : Prop :=
  ∀ x y : α, f x + f y ≤ f (x ⊓ y) + f (x ⊔ y)

/-- **Theorem 2.7.1** (Topkis 1998). The argmax of a supermodular
function on a lattice is a sublattice: closed under `⊓` and `⊔`.

Proof: for any two maximizers `x', x'' ∈ argmax f`,
supermodularity gives `f x' + f x'' ≤ f (x' ⊓ x'') + f (x' ⊔ x'')`.
Since each of `f (x' ⊓ x''), f (x' ⊔ x'')` is at most the max value `M`,
and the LHS equals `2M`, both must equal `M`. -/
theorem supermodular_argmax_is_sublattice
    {α : Type*} [Lattice α] {f : α → ℝ}
    (h_sm : Supermodular f) {X : Set α}
    {M : ℝ} (h_max : ∀ x ∈ X, f x ≤ M)
    (h_meet_in_X : ∀ a ∈ X, ∀ b ∈ X, a ⊓ b ∈ X)
    (h_join_in_X : ∀ a ∈ X, ∀ b ∈ X, a ⊔ b ∈ X)
    {x y : α} (hx_in : x ∈ X) (hy_in : y ∈ X)
    (hx_max : f x = M) (hy_max : f y = M) :
    f (x ⊓ y) = M ∧ f (x ⊔ y) = M := by
  have h_meet_in : x ⊓ y ∈ X := h_meet_in_X x hx_in y hy_in
  have h_join_in : x ⊔ y ∈ X := h_join_in_X x hx_in y hy_in
  have h_meet_le : f (x ⊓ y) ≤ M := h_max _ h_meet_in
  have h_join_le : f (x ⊔ y) ≤ M := h_max _ h_join_in
  have h_sm_xy := h_sm x y
  -- 2M = f x + f y ≤ f (x ⊓ y) + f (x ⊔ y) ≤ 2M, so both = M.
  refine ⟨?_, ?_⟩ <;> linarith

/-! ## §2.4.3 Monotone selection from increasing correspondence

For a linearly-ordered (or lattice) state space, an increasing
correspondence `t ↦ S(t)` (in the strong-set order) admits an
increasing selection: at each `t`, pick the greatest (or least) element
of `S(t)`, and the resulting selection is monotone.
-/

/-- **Theorem 2.4.3 (Topkis 1998, scalar greatest-element form).**
If `S : T → Set α` (with `α` a lattice and `T` a preorder) is increasing
in the strong-set order, and each `S t` admits a greatest element
`g(t)`, then `g` is increasing as a function of `t`. -/
theorem monotone_greatest_of_strongSetOrder
    {α : Type*} [Lattice α]
    {T : Type*} [Preorder T]
    {S : T → Set α} (g : T → α)
    (hg_in : ∀ t, g t ∈ S t)
    (hg_greatest : ∀ t (x : α), x ∈ S t → x ≤ g t)
    (hS_mono : ∀ ⦃t t' : T⦄, t ≤ t' → StrongSetOrder (S t) (S t')) :
    Monotone g := by
  intro t t' htt
  have h_join_in := (hS_mono htt (hg_in t) (hg_in t')).2
  -- `g t ⊔ g t' ∈ S t'`, so `g t ⊔ g t' ≤ g t'`.
  have h_le : g t ⊔ g t' ≤ g t' := hg_greatest t' _ h_join_in
  -- And `g t ≤ g t ⊔ g t'` by definition of join.
  exact le_trans le_sup_left h_le

/-- **Theorem 2.4.3 (Topkis 1998, scalar least-element form).**
Dual: if each `S t` has a least element `ℓ(t)`, then `ℓ` is increasing. -/
theorem monotone_least_of_strongSetOrder
    {α : Type*} [Lattice α]
    {T : Type*} [Preorder T]
    {S : T → Set α} (ℓ : T → α)
    (hℓ_in : ∀ t, ℓ t ∈ S t)
    (hℓ_least : ∀ t (x : α), x ∈ S t → ℓ t ≤ x)
    (hS_mono : ∀ ⦃t t' : T⦄, t ≤ t' → StrongSetOrder (S t) (S t')) :
    Monotone ℓ := by
  intro t t' htt
  have h_meet_in := (hS_mono htt (hℓ_in t) (hℓ_in t')).1
  -- `ℓ t ⊓ ℓ t' ∈ S t`, so `ℓ t ≤ ℓ t ⊓ ℓ t'`.
  have h_le : ℓ t ≤ ℓ t ⊓ ℓ t' := hℓ_least t _ h_meet_in
  -- And `ℓ t ⊓ ℓ t' ≤ ℓ t'` by definition of meet.
  exact le_trans h_le inf_le_right

/-! ## §2.7.6 Supermodularity preservation under maximization

Topkis 1998 Theorem 2.7.6: if `f(x, t)` is supermodular jointly in
`(x, t)` on a sublattice `S ⊆ X × T`, and `g(t) := sup_{x ∈ S_t} f(x, t)`
is finite (i.e., the sup is attained for every `t`), then `g` is
supermodular on `proj_T(S)`.

We formalize the version where the maximizer is given explicitly as a
function `m : β → α` (Skolemization of the per-parameter ∃-argmax). The
proof uses joint supermodularity of `f` together with the sublattice
property of `S` to bound `g(t₁) + g(t₂)` above by
`g(t₁ ⊓ t₂) + g(t₁ ⊔ t₂)`:

  g(t₁) + g(t₂)
    = f(m t₁, t₁) + f(m t₂, t₂)                                  -- m maximizes
    ≤ f(m t₁ ⊓ m t₂, t₁ ⊓ t₂) + f(m t₁ ⊔ m t₂, t₁ ⊔ t₂)         -- joint sm
    ≤ g(t₁ ⊓ t₂) + g(t₁ ⊔ t₂)                                    -- m maximizes again,
                                                                  -- using sublattice. -/

/-- **Theorem 2.7.6 (Topkis 1998).** The value function `g(t) = sup f(·, t)`
of a jointly supermodular function `f` over a sublattice `S ⊆ α × β` is
supermodular in the parameter `t`.

The hypotheses bundle the standard preconditions:
* `h_sublattice` — `S` is closed under componentwise `⊓` and `⊔`;
* `h_joint_sm` — `f` is supermodular on `S` jointly in `(x, t)`;
* `h_m_in_S` — the chosen maximizer `m` sends each `t` to a feasible
  pair `(m t, t) ∈ S`;
* `h_g_eq` — `g` attains its sup at `m`: `g(t) = f(m t, t)`;
* `h_g_upper_bound` — `g(t)` is an upper bound on `f` over the `t`-slice
  of `S`. -/
theorem supermodular_value_function
    {α β : Type*} [Lattice α] [Lattice β]
    (f : α → β → ℝ)
    (S : Set (α × β))
    (h_sublattice : ∀ p ∈ S, ∀ q ∈ S,
        (p.1 ⊓ q.1, p.2 ⊓ q.2) ∈ S ∧ (p.1 ⊔ q.1, p.2 ⊔ q.2) ∈ S)
    (h_joint_sm : ∀ p ∈ S, ∀ q ∈ S,
        f p.1 p.2 + f q.1 q.2
          ≤ f (p.1 ⊓ q.1) (p.2 ⊓ q.2) + f (p.1 ⊔ q.1) (p.2 ⊔ q.2))
    (g : β → ℝ) (m : β → α)
    (h_m_in_S : ∀ t : β, (m t, t) ∈ S)
    (h_g_eq : ∀ t : β, g t = f (m t) t)
    (h_g_upper_bound : ∀ p ∈ S, f p.1 p.2 ≤ g p.2) :
    Supermodular g := by
  intro t₁ t₂
  -- (m t₁, t₁), (m t₂, t₂) ∈ S.
  have h1 : ((m t₁, t₁) : α × β) ∈ S := h_m_in_S t₁
  have h2 : ((m t₂, t₂) : α × β) ∈ S := h_m_in_S t₂
  -- Sublattice closure of S delivers the meet/join points.
  obtain ⟨h_meet, h_join⟩ := h_sublattice _ h1 _ h2
  -- Joint supermodularity of f.
  have h_sm := h_joint_sm _ h1 _ h2
  -- Each meet/join evaluation of f is bounded by g at the corresponding t.
  have h_meet_bound : f (m t₁ ⊓ m t₂) (t₁ ⊓ t₂) ≤ g (t₁ ⊓ t₂) :=
    h_g_upper_bound _ h_meet
  have h_join_bound : f (m t₁ ⊔ m t₂) (t₁ ⊔ t₂) ≤ g (t₁ ⊔ t₂) :=
    h_g_upper_bound _ h_join
  -- Chain the inequalities; substitute g(t) = f(m t, t).
  rw [h_g_eq t₁, h_g_eq t₂]
  linarith

/-- **Corollary: when `S = α × β` (no feasibility restriction).**
If `f : α × β → ℝ` is jointly supermodular and `g(t) := f(m t, t)` for
some maximizer-function `m` (with `g` upper-bounding `f(·, t)` for each
`t`), then `g` is supermodular. -/
theorem supermodular_value_function_unconstrained
    {α β : Type*} [Lattice α] [Lattice β]
    (f : α → β → ℝ)
    (h_joint_sm : ∀ x₁ x₂ : α, ∀ t₁ t₂ : β,
        f x₁ t₁ + f x₂ t₂
          ≤ f (x₁ ⊓ x₂) (t₁ ⊓ t₂) + f (x₁ ⊔ x₂) (t₁ ⊔ t₂))
    (g : β → ℝ) (m : β → α)
    (h_g_eq : ∀ t : β, g t = f (m t) t)
    (h_g_upper_bound : ∀ x : α, ∀ t : β, f x t ≤ g t) :
    Supermodular g :=
  supermodular_value_function f Set.univ
    (fun p _ q _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)
    (fun p _ q _ => h_joint_sm p.1 q.1 p.2 q.2)
    g m (fun _ => Set.mem_univ _) h_g_eq
    (fun p _ => h_g_upper_bound p.1 p.2)

/-! ## §2.5 Fixed Points — Tarski's theorem

Topkis 1998 §2.5. **Corollary 2.5.1 (Tarski's fixed-point theorem):**
an increasing self-map `f` of a nonempty complete lattice has a nonempty
*complete lattice* of fixed points; the greatest fixed point is
`sup {x | x ≤ f x}` and the least fixed point is `inf {x | f x ≤ x}`.

We wrap mathlib's Knaster–Tarski development (`OrderHom.lfp`,
`OrderHom.gfp`) rather than re-prove it. Topkis applies §2.5 only to
game equilibria (Chapter 4); the sanctions project additionally uses it
for dynamic-system fixed points (the joint sanction-preference steady state), which is a
legitimate further use of the same theorem. -/

/-- **Tarski's fixed-point theorem, existence form** (Topkis 1998
Corollary 2.5.1(a)). An increasing self-map of a complete lattice has a
fixed point. -/
theorem tarski_fixedPoint {α : Type*} [CompleteLattice α]
    (f : α → α) (hf : Monotone f) : ∃ x, f x = x :=
  ⟨OrderHom.lfp ⟨f, hf⟩, OrderHom.map_lfp ⟨f, hf⟩⟩

/-- **Tarski's least fixed point** (Topkis 1998 Corollary 2.5.1). The
least fixed point of an increasing self-map `f` of a complete lattice
is `OrderHom.lfp ⟨f, hf⟩`; it is the least element of the fixed-point
set, and is characterised as `inf {a | f a ≤ a}`. -/
theorem tarski_isLeast_fixedPoint {α : Type*} [CompleteLattice α]
    (f : α → α) (hf : Monotone f) :
    IsLeast {x | f x = x} (OrderHom.lfp ⟨f, hf⟩) := by
  constructor
  · exact OrderHom.map_lfp ⟨f, hf⟩
  · intro x hx
    exact OrderHom.lfp_le ⟨f, hf⟩ (le_of_eq hx)

/-- **Tarski's greatest fixed point** (Topkis 1998 Corollary 2.5.1).
Dual of `tarski_isLeast_fixedPoint`; characterised as `sup {a | a ≤ f a}`. -/
theorem tarski_isGreatest_fixedPoint {α : Type*} [CompleteLattice α]
    (f : α → α) (hf : Monotone f) :
    IsGreatest {x | f x = x} (OrderHom.gfp ⟨f, hf⟩) := by
  constructor
  · exact OrderHom.map_gfp ⟨f, hf⟩
  · intro x hx
    exact OrderHom.le_gfp ⟨f, hf⟩ (ge_of_eq hx)

/-- **Tarski on a closed real interval.** A monotone self-map of a
nonempty closed bounded interval `[a, b] ⊆ ℝ` has a fixed point in
`[a, b]` — no continuity or contraction hypothesis required. This is the
form used to guarantee a steady state inside a forward-invariant
trapping region. -/
theorem tarski_fixedPoint_Icc (T : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hT_mono : Monotone T)
    (hT_maps : ∀ x ∈ Set.Icc a b, T x ∈ Set.Icc a b) :
    ∃ x ∈ Set.Icc a b, T x = x := by
  haveI : Fact (a ≤ b) := ⟨hab⟩
  -- Restrict `T` to the subtype `↥(Set.Icc a b)`, a complete lattice.
  let T' : Set.Icc a b → Set.Icc a b := fun x => ⟨T x.1, hT_maps x.1 x.2⟩
  have hT'_mono : Monotone T' := by
    intro x y hxy
    exact hT_mono hxy
  obtain ⟨x, hx⟩ := tarski_fixedPoint T' hT'_mono
  refine ⟨x.1, x.2, ?_⟩
  have := congrArg Subtype.val hx
  simpa [T'] using this

/-! ## §2.5 Corollary 2.5.2 — parametric monotone fixed points

Topkis 1998 Corollary 2.5.2 (Milgrom–Roberts 1994): if `f(·, t)` is an
increasing function of the parameter `t` (i.e. `t ≤ t'` implies
`f(·, t) ≤ f(·, t')` pointwise), then the least and greatest fixed
points are increasing in `t`. This is the comparative-statics tool for
steady states: how the fixed point moves when a primitive shifts. -/

/-- **Corollary 2.5.2 (least fixed point is monotone in the parameter).**
For an increasing family `F : T → (α →o α)` of monotone self-maps of a
complete lattice, the least fixed point `t ↦ lfp (F t)` is monotone. -/
theorem lfp_monotone_in_param {α T : Type*} [CompleteLattice α] [Preorder T]
    (F : T → (α →o α)) (hF : Monotone F) :
    Monotone (fun t => OrderHom.lfp (F t)) :=
  OrderHom.lfp.monotone.comp hF

/-- **Corollary 2.5.2 (greatest fixed point is monotone in the parameter).** -/
theorem gfp_monotone_in_param {α T : Type*} [CompleteLattice α] [Preorder T]
    (F : T → (α →o α)) (hF : Monotone F) :
    Monotone (fun t => OrderHom.gfp (F t)) :=
  OrderHom.gfp.monotone.comp hF

/-! ## Composition rule: convex ∘ supermodular is supermodular

Topkis (1998), *Supermodularity and Complementarity*, §2.6: composing a
supermodular map with an increasing convex transform preserves supermodularity.
Stated here in scalar chord form on `Icc lo 1`, which is the shape the dynamic
single-crossing arguments consume.

The economic use is the continuation term of a Bellman objective. If the value
function is convex and non-decreasing along the reachable range, and the
transition has increasing differences in `(state, action)`, then the composite
`value ∘ transition` has increasing differences too — so the continuation channel
cannot destroy complementarity that the transition supplies.

An affine transition is *modular* — its cross-difference is zero — so it is the
degenerate case where the two chords have equal width and the monotonicity
hypothesis is not needed. That is why arguments written against an affine law
never had to assume the value function increasing. -/

/-- **Chord shift for a convex function on `Icc lo 1`.** Equal-width chords move
up as they slide right: for `lo ≤ y₁ ≤ y₂` and a shift `t ≥ 0` staying below `1`,
`g y₂ − g y₁ ≤ g (y₂+t) − g (y₁+t)`.

The scalar core of the "nondecreasing increments" characterisation of convexity;
mathlib carries the slope-monotonicity form but not this one. -/
theorem convexOn_chord_shift {g : ℝ → ℝ} {lo : ℝ}
    (hg : ConvexOn ℝ (Set.Icc lo (1 : ℝ)) g) {y₁ y₂ t : ℝ}
    (hy₁lo : lo ≤ y₁) (hy : y₁ ≤ y₂) (ht : 0 ≤ t) (htop : y₂ + t ≤ 1) :
    g y₂ - g y₁ ≤ g (y₂ + t) - g (y₁ + t) := by
  rcases lt_or_ge 0 (y₂ - y₁ + t) with htot | htot
  · -- Nondegenerate: read both interior points as convex combinations of the
    -- endpoints `y₁` and `y₂ + t`, at complementary weights.
    have mem₁ : y₁ ∈ Set.Icc lo (1 : ℝ) := ⟨hy₁lo, by linarith⟩
    have mem₂ : y₂ + t ∈ Set.Icc lo (1 : ℝ) := ⟨by linarith, htop⟩
    have hμ_nn : 0 ≤ t / (y₂ - y₁ + t) := div_nonneg ht htot.le
    have hμ_le : t / (y₂ - y₁ + t) ≤ 1 := by
      rw [div_le_one htot]; linarith
    have hb_nn : 0 ≤ 1 - t / (y₂ - y₁ + t) := by linarith
    have hab : t / (y₂ - y₁ + t) + (1 - t / (y₂ - y₁ + t)) = 1 := by ring
    have hba : (1 - t / (y₂ - y₁ + t)) + t / (y₂ - y₁ + t) = 1 := by ring
    have hc₁ := hg.2 mem₁ mem₂ hμ_nn hb_nn hab
    have hc₂ := hg.2 mem₁ mem₂ hb_nn hμ_nn hba
    simp only [smul_eq_mul] at hc₁ hc₂
    have hne : y₂ - y₁ + t ≠ 0 := htot.ne'
    have e₁ : t / (y₂ - y₁ + t) * y₁
        + (1 - t / (y₂ - y₁ + t)) * (y₂ + t) = y₂ := by
      field_simp
      ring
    have e₂ : (1 - t / (y₂ - y₁ + t)) * y₁
        + t / (y₂ - y₁ + t) * (y₂ + t) = y₁ + t := by
      field_simp
      ring
    rw [e₁] at hc₁
    rw [e₂] at hc₂
    linarith
  · -- Degenerate: zero width and zero shift.
    have h1 : y₂ = y₁ := by linarith
    have h2 : t = 0 := by linarith
    rw [h1, h2]
    simp

/-- **Topkis composition in chord form.** Let `g` be convex and non-decreasing on
`Icc lo 1`, and let four points satisfy the supermodular ordering
`b − a ≤ d − c` with `a ≤ b`, `c ≤ d`, `a ≤ c`. Then `g b − g a ≤ g d − g c`.

Reading `a = F(x,s₁)`, `b = F(x,s₂)`, `c = F(x',s₁)`, `d = F(x',s₂)`: the
hypothesis is that the transition has increasing differences in state and
sanction, and the conclusion is that the composite `g ∘ F` does too.

Convexity alone handles the equal-width case; the extra width `(d−c) − (b−a)`
that a genuinely supermodular transition creates is absorbed by monotonicity.
Under an affine transition that extra width is zero, which is why the affine
argument needs no monotonicity hypothesis. -/
theorem chord_le_chord_of_convexOn_monotoneOn
    {g : ℝ → ℝ} {lo : ℝ}
    (hg : ConvexOn ℝ (Set.Icc lo (1 : ℝ)) g)
    (hmono : MonotoneOn g (Set.Icc lo (1 : ℝ)))
    {a b c d : ℝ}
    (halo : lo ≤ a) (hab : a ≤ b) (hac : a ≤ c)
    (hsuper : b - a ≤ d - c) (hcd : c ≤ d) (hd1 : d ≤ 1) :
    g b - g a ≤ g d - g c := by
  have ht : (0 : ℝ) ≤ c - a := by linarith
  have hbt : b + (c - a) ≤ d := by linarith
  have htop : b + (c - a) ≤ 1 := le_trans hbt hd1
  have h1 : g b - g a ≤ g (b + (c - a)) - g (a + (c - a)) :=
    convexOn_chord_shift hg halo hab ht htop
  have hrw : a + (c - a) = c := by ring
  rw [hrw] at h1
  have hmem1 : b + (c - a) ∈ Set.Icc lo (1 : ℝ) := ⟨by linarith, htop⟩
  have hmemd : d ∈ Set.Icc lo (1 : ℝ) := ⟨by linarith, hd1⟩
  have h2 : g (b + (c - a)) ≤ g d := hmono hmem1 hmemd hbt
  linarith

end Topkis
end Sanctions

end
