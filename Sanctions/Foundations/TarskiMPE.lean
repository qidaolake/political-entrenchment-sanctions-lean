/-
Sanctions/Foundations/TarskiMPE.lean

Coupled Markov-perfect equilibrium (MPE) existence via Tarski's
fixed-point theorem on the product lattice of monotone policy pairs.

This module formalizes the AES-style monotone-lattice route (paper
`prop:AES_existence` in Appendix C, route R2) at an abstract level:
given two complete lattices `L_S, L_T` of policies and an order-preserving
joint best-response map `BR : (L_S × L_T) →o (L_S × L_T)`, Tarski's
theorem (mathlib's `OrderHom.lfp` / `OrderHom.map_lfp`) gives a joint
fixed point.

**Canonical theoretical anchor (added in the current round).** The
existence and extremal-equilibrium structure of this abstract setup
is exactly **Vives 1990** Theorem 4.1 (Nash equilibrium in lattice
games with strategic complementarities, existence + greatest /
least element) and **Milgrom-Roberts 1990** Theorem 5 (the greatest
Nash equilibrium of a supermodular game is the upper rationalizable
bound, the least is the lower bound). The proofs of those classical
results are restated in `Sanctions/Foundations/VivesLattice.lean` with
full attribution; this file's `joint_MPE_exists` is the dynamic-game
specialisation of that classical statement, and the project's
`σ_dyn_top` greatest-selector convention now has the Milgrom-Roberts
1990 upper-rationalizable-bound justification rather than being a
nominal convention.

The Theory-side bilateral specialisation discussed below remains
deferred (it requires establishing isotonicity of the joint Bellman
operator in `(V_T, V_S)`, which would be a Rule-3 trigger for new
structural hypotheses on `Params`); the Foundations module above is
parametric over abstract complete lattices and does not commit to
the bilateral form.

For the bilateral specialization the user must provide:
* a complete-lattice structure on the policy spaces (e.g. monotone
  functions valued in `[0,1]` with pointwise order);
* the joint best-response map as a bundled `OrderHom` (which in
  particular packages the single-crossing / monotone-comparative-statics
  proofs);
* under these inputs, this module yields the joint MPE fixed point.

A concrete bilateral instantiation requires constructing the order-
preservation of the joint best-response — which in turn requires
Milgrom–Shannon single-crossing or Topkis monotone selection arguments
on the bilateral payoffs. We provide the abstract template and one
concrete instantiation skeleton; full instantiation is deferred to
future work and corresponds to formalizing the order-theoretic
argument behind paper `prop:AES_existence`.
-/

import Sanctions.Foundations.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Order
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.MetricSpace.Contracting

namespace Sanctions
namespace MPE

/-! ## Abstract joint MPE existence via Tarski -/

/-- **Joint MPE existence via Tarski (abstract).**
Given any order-preserving self-map `BR` on a complete lattice `L`,
the map has a fixed point (the least fixed point, by Tarski). -/
theorem joint_MPE_exists {L : Type*} [CompleteLattice L] (BR : L →o L) :
    ∃ x : L, BR x = x :=
  ⟨OrderHom.lfp BR, OrderHom.map_lfp BR⟩

/-- **Product version.** When the lattice is a product of two policy
spaces `L_S × L_T`, the joint best-response map has a joint fixed
point. This is the standard Tarski argument applied to the product
complete lattice. -/
theorem joint_MPE_exists_pair
    {L_S L_T : Type*} [CompleteLattice L_S] [CompleteLattice L_T]
    (BR : (L_S × L_T) →o (L_S × L_T)) :
    ∃ p : L_S × L_T, BR p = p :=
  joint_MPE_exists BR

/-- **Decomposed product version.** Given two coupled best-response
maps `BR_S : L_S × L_T → L_S` and `BR_T : L_S × L_T → L_T`, both
order-preserving (jointly in the product order), there exists a joint
fixed point `(σ*, α*)` with `BR_S (σ*, α*) = σ*` and `BR_T (σ*, α*) = α*`. -/
theorem joint_MPE_exists_decomposed
    {L_S L_T : Type*} [CompleteLattice L_S] [CompleteLattice L_T]
    (BR_S : (L_S × L_T) →o L_S) (BR_T : (L_S × L_T) →o L_T) :
    ∃ σ : L_S, ∃ α : L_T, BR_S (σ, α) = σ ∧ BR_T (σ, α) = α := by
  -- Bundle the two BR maps into a joint map on the product lattice.
  let BR : (L_S × L_T) →o (L_S × L_T) :=
    { toFun := fun p => (BR_S p, BR_T p)
      monotone' := fun p q hpq => ⟨BR_S.monotone hpq, BR_T.monotone hpq⟩ }
  obtain ⟨p, hp⟩ := joint_MPE_exists BR
  refine ⟨p.1, p.2, ?_, ?_⟩
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

/-! ## Two-player joint MPE structural template

A `BilateralMPEStructure` is a fully abstract record bundling the
two-player Sender + Target policy lattices and their joint
best-response maps; its `joint_MPE_exists` field follows from
`joint_MPE_exists_decomposed`. Both lattices and both BR maps are
abstract type parameters — the structure does NOT commit to any
specific bilateral instantiation. The name's "Bilateral" prefix
refers to the two-player game form (Sender + Target), not to the
deleted bilateral LQ specification. -/

/-- **Structural template for the two-player joint MPE.**
A `BilateralMPEStructure` packages:
* the lattices of Sender and Target policies (with complete-lattice
  instances);
* the joint best-response operators (as bundled `OrderHom`s);
* the conclusion follows from `joint_MPE_exists_decomposed`. -/
structure BilateralMPEStructure where
  /-- Lattice of Sender policies. -/
  L_S : Type
  /-- Lattice of Target policies. -/
  L_T : Type
  /-- Complete-lattice structure on Sender policies. -/
  inst_S : CompleteLattice L_S
  /-- Complete-lattice structure on Target policies. -/
  inst_T : CompleteLattice L_T
  /-- Sender best-response operator given a (σ, α) pair. -/
  BR_S : (L_S × L_T) →o L_S
  /-- Target best-response operator given a (σ, α) pair. -/
  BR_T : (L_S × L_T) →o L_T

/-- **Joint MPE existence for any `BilateralMPEStructure`.**
This is the direct concrete corollary of `joint_MPE_exists_decomposed`. -/
theorem BilateralMPEStructure.joint_MPE_exists (B : BilateralMPEStructure) :
    ∃ σ : B.L_S, ∃ α : B.L_T, B.BR_S (σ, α) = σ ∧ B.BR_T (σ, α) = α :=
  let _ : CompleteLattice B.L_S := B.inst_S
  let _ : CompleteLattice B.L_T := B.inst_T
  joint_MPE_exists_decomposed B.BR_S B.BR_T

/-! ## Unit interval as a scalar policy lattice

The closed unit interval `[0,1] ⊂ ℝ` is a complete lattice. Used by
the abstract state-dependent MPE layer and as a building block for
monotone-function policy spaces. We deliberately do NOT exhibit a
"sanity-check" `BilateralMPEStructure` populated with constant BR
maps: a constant function trivially has a fixed point and would not
exercise the framework's substantive content; more importantly,
labeling such a constant as "BR" violates Rule 1 (the project's
optimal-strategies-only discipline — a "best response" must be an
argmax / Bellman-optimal selection, not a hand-chosen constant).
-/

/-- The closed unit interval `[0,1] ⊂ ℝ` as a complete lattice. -/
abbrev UnitI : Type := ↥(Set.Icc (0:ℝ) 1)

noncomputable instance : CompleteLattice UnitI := by
  unfold UnitI
  infer_instance

/-! ## Notes on concrete instantiation to the bilateral

To instantiate `BilateralMPEStructure` for the bilateral model with the
actual bilateral payoffs:

1. **`L_S, L_T`**: take the lattice of monotone non-decreasing functions
   `ℝ × ℝ → UnitI` (or its bilateral specialization). Pointwise sup/inf
   preserve monotonicity, so this is a complete sublattice of
   `(ℝ × ℝ) → UnitI`. In Lean: `(ℝ × ℝ) →o UnitI` with the standard
   pointwise lattice operations.

2. **`BR_S, BR_T` as `OrderHom`**: the substantive content. The Sender
   BR at `(σ, α)` is the projection of `σ_raw + (continuation wedge
   from V_S given α)` onto `[0,1]`. The Target BR at `(σ, α)` is the
   argmax over `a` of `U_T(x, a, σ(x, a)) + β_T V_T(F)` where V_T is
   the Target Bellman fixed point given σ.

   The `monotone'` field requires proving the joint best-response map
   is order-preserving when each component policy increases. This
   reduces to:
   * `V_T(σ)` is monotone in σ (true: increasing σ raises the Bellman
     RHS pointwise).
   * `argmax_a R^dyn(x, a; V_T)` is monotone in V_T when `R^dyn`
     satisfies strict single-crossing (Milgrom–Shannon).
   * Symmetric statement for Sender.

3. The single-crossing properties for the bilateral payoffs are
   verified in paper `app:R2_AES` but their Lean encoding requires
   Milgrom–Shannon machinery beyond the current scope.

Once a concrete `BilateralMPEStructure` is constructed,
`BilateralMPEStructure.joint_MPE_exists` immediately gives joint MPE
existence.
-/

/-! ## Joint Banach alternative

The Tarski / Knaster-Tarski route above is the "Route R2" of paper
Appendix C. We also record the "joint Banach" route, which is a
specialization of the abstract Banach fixed-point theorem to a product
of complete metric spaces.

This route would require the joint Bellman operator
  `T(V_S, V_T) = (T_S(V_S, V_T), T_T(V_S, V_T))`
on bounded continuous functions to be a contraction with rate < 1.
Subtle obstacle: `T_T` depends on `V_S` via `σ^dyn`, whose
`V_S`-Lipschitz constant is *not* automatically less than 1 in the
sup norm — it can require additional smoothness or a `C^1` norm to
control. Hence joint Banach is less robust than Tarski here. We
record the abstract template for completeness.
-/

/-- **Joint Banach fixed point.** If `T` is a `ContractingWith` self-map
on a product of complete metric spaces, it has a fixed point. -/
theorem joint_MPE_via_Banach
    {E_S E_T : Type*}
    [MetricSpace E_S] [CompleteSpace E_S] [Nonempty E_S]
    [MetricSpace E_T] [CompleteSpace E_T] [Nonempty E_T]
    {β : NNReal}
    (T : (E_S × E_T) → (E_S × E_T))
    (hT : ContractingWith β T) :
    ∃ p : E_S × E_T, T p = p :=
  ⟨ContractingWith.fixedPoint T hT, ContractingWith.fixedPoint_isFixedPt hT⟩

/-! ## Strategic-substitutes route: dual-Tarski

The bilateral sanctions game has **strategic substitutes** structure:
* Target's best response `BR_T(σ)` is decreasing in σ (more sanctions →
  less compliance, given the negative cross-partial `U_T_sa = -ω_T`).
* Sender's best response `BR_S(α)` is decreasing in α (more compliance →
  less sanction, given the negative cross-partial `U_S_sa < 0`).

Direct Tarski doesn't apply to a joint best-response with both
substitute components. The standard workaround is to dualize one or
both lattice orders, restoring monotonicity in the dualized product.
-/

open OrderDual

/-- **Joint MPE existence under strategic substitutes** via OrderDual.
Given best-response operators whose joint map is order-preserving on
the dualized product `L_Sᵒᵈ × L_T`, Tarski yields a joint fixed point
that is a true MPE in the original lattices. -/
theorem joint_MPE_substitutes_via_dual
    {L_S L_T : Type*} [CompleteLattice L_S] [CompleteLattice L_T]
    (BR : (L_Sᵒᵈ × L_T) →o (L_Sᵒᵈ × L_T)) :
    ∃ p : L_Sᵒᵈ × L_T, BR p = p :=
  joint_MPE_exists BR

/-- **Decomposed dual version.** Given coupled best-response operators
`BR_S : L_Sᵒᵈ × L_T → L_Sᵒᵈ` and `BR_T : L_Sᵒᵈ × L_T → L_T`, both
order-preserving in the dualized product, there is a joint fixed point. -/
theorem joint_MPE_substitutes_decomposed
    {L_S L_T : Type*} [CompleteLattice L_S] [CompleteLattice L_T]
    (BR_S : (L_Sᵒᵈ × L_T) →o L_Sᵒᵈ) (BR_T : (L_Sᵒᵈ × L_T) →o L_T) :
    ∃ α : L_Sᵒᵈ, ∃ σ : L_T, BR_S (α, σ) = α ∧ BR_T (α, σ) = σ :=
  joint_MPE_exists_decomposed BR_S BR_T

/-! ## High-rectangle witness status

Earlier drafts of this module carried a collapsed high-rectangle
``concrete MPE'' with constant policies (`α = 0`, `σ = 1`) packaged as
`highRect_BR_T`, `highRect_BR_S`, `highRect_jointBR`,
`highRect_MPE_exists`, and `highRect_MPE_concrete`. That material was
deleted (2026-05-24) as a Rule-1 hygiene fix: the ``best-response''
maps were literally constant functions ignoring their input — they did
not derive from any payoff, argmax, or Bellman optimality, so applying
Tarski to them produced only the trivial fact that constants have
fixed points. Per the project's Rule 1 (optimal-strategies-only), a
high-rectangle joint-MPE claim is admissible only after the constant
policies are recovered as actual best responses from concrete payoff
primitives at a future `Sanctions/Examples/` instantiation. The
abstract Tarski templates above (`joint_MPE_exists`,
`joint_MPE_substitutes_via_dual`, `joint_MPE_via_Banach`, and
`BilateralMPEStructure`) remain available for that instantiation.
-/

/-! ## Monotone policy lattices for the bilateral specification

`OrderHom (ℝ × ℝ) UnitI` is the type of monotone non-decreasing
functions from the bilateral state space `ℝ × ℝ` (product order) to
`UnitI = ↥[0,1]`. By `OrderHom.instCompleteLattice` (mathlib), this is
a complete lattice with pointwise sup and inf, and is therefore a
valid policy lattice for `joint_MPE_exists_decomposed` /
`BilateralMPEStructure`.

We do not define abbreviations because `abbrev` triggers Lean's
type-class inference into a path through `OrderHom.instPreorder` that
conflicts with `CompleteLattice.toOmegaCompletePartialOrder.toPreorder`,
causing instance-search failures downstream. Users instantiating to
monotone policies should use the full type `(ℝ × ℝ) →o UnitI` (or
similar) directly when applying `joint_MPE_exists_decomposed`.

Once the user supplies a joint best-response map as an `OrderHom` on
the product lattice, `joint_MPE_exists_decomposed` immediately yields a
joint MPE fixed point. The substantive (non-Lean) work is to verify
that the bilateral best-response map is order-preserving via
Milgrom–Shannon single-crossing on the bilateral payoffs.
-/

/-! ### State-dependent monotone-policy MPE: the diamond is resolved

Earlier drafts of this module documented a typeclass-instance diamond on
`(ℝ × ℝ) →o UnitI` — `Preorder ((ℝ × ℝ) →o UnitI)` reachable via both
`OrderHom.instPreorder` and a `CompleteLattice`-derived chain, claimed
non-defeq — said to block running Knaster-Tarski on the monotone-policy
product lattice.

**As of the project's pinned mathlib that diamond is stale (re-verified
this round).** The constant the old note named as one horn of the diamond,
`CompleteLattice.toOmegaCompletePartialOrder.toPreorder`, no longer exists;
`OmegaCompletePartialOrder` now derives *from* `CompleteLattice` via
`ChainCompletePartialOrder`, and the two `Preorder` routes on
`(ℝ × ℝ) →o UnitI` and on the product `((ℝ × ℝ) →o UnitI)²` are now
definitionally equal (`rfl` succeeds). `OrderHom.lfp` / `OrderHom.map_lfp`
compose with zero errors and axiom-clean both on the monotone-policy
product lattice and on the value-rectangle `(Set.Icc)ᵒᵈ × Set.Icc`. The
abstract templates above (`joint_MPE_exists`, `joint_MPE_substitutes_via_dual`,
`joint_MPE_via_Banach`) therefore apply directly; no `~100-line bespoke
instance` and no mathlib PR is needed.

The value-rectangle specialization below records the dual-Tarski step
concretely: the strategic-substitute sign flip (`T_S` antitone in `V_T`)
is absorbed by carrying the Target value factor in `OrderDual`, so the
joint value operator becomes an order-preserving self-map of
`(Set.Icc mT MT)ᵒᵈ × Set.Icc mS MS`. -/

/-- **Joint value fixed point via one-sided dual Tarski (value rectangle).**
Given the two Bellman value operators as bundled `OrderHom`s on the
dualized product of two closed value intervals — the Target value factor
in `OrderDual` to absorb the strategic-substitute sign flip — Knaster-Tarski
yields a joint fixed point.

This is *conditional on the supplied monotone operators* (Rule 14/15): it
consumes `T_T, T_S` as `OrderHom`s — their monotonicity in the dualized
product order is the economic input the supplier must establish — and
constructs only the fixed point, exactly as `joint_MPE_substitutes_via_dual`
does on abstract lattices, here specialized to the value lattice. It is
*not* an unconditional existence theorem for the sanctions game; for the
deterministic-`F` game the constructed route is the basin-corner
single-agent value fixed point (`Theory/Equilibrium/BasinCornerExistence.lean`). -/
theorem joint_value_fixedPoint_via_dual
    (mT MT mS MS : ℝ) [Fact (mT ≤ MT)] [Fact (mS ≤ MS)]
    (T_T : ((Set.Icc mT MT)ᵒᵈ × Set.Icc mS MS) →o (Set.Icc mT MT)ᵒᵈ)
    (T_S : ((Set.Icc mT MT)ᵒᵈ × Set.Icc mS MS) →o Set.Icc mS MS) :
    ∃ vT : (Set.Icc mT MT)ᵒᵈ, ∃ vS : Set.Icc mS MS,
      T_T (vT, vS) = vT ∧ T_S (vT, vS) = vS := by
  let BR : (((Set.Icc mT MT)ᵒᵈ) × (Set.Icc mS MS)) →o
            (((Set.Icc mT MT)ᵒᵈ) × (Set.Icc mS MS)) :=
    { toFun := fun p => (T_T p, T_S p)
      monotone' := fun p q hpq => ⟨T_T.monotone hpq, T_S.monotone hpq⟩ }
  set q := OrderHom.lfp BR with hqdef
  have hq : BR q = q := OrderHom.map_lfp BR
  exact ⟨q.1, q.2, congrArg Prod.fst hq, congrArg Prod.snd hq⟩

end MPE

/-! ## State-dependent monotone-policy MPE templates

Absorbed from `Theory/Equilibrium/StateDependent.lean` (2026-07-24
Rule-19 move; the file was pure lattice machinery over an arbitrary
state type — the same content class as this module — and its only
importer was the `Theory` umbrella). Originally extracted from the
deleted bilateral concrete spec: the bilateral-specific
`staticSenderBR` / `staticTargetBR` / `staticJointBR` content was
removed with that spec; the parametric Tarski-style state-dependent
MPE existence templates below are what remains.

**Rule-1 compliance.** Parametric Tarski fixed point delivers the
equilibrium policy via lattice argmax, not via a fixed action.
**Rule-3 compliance.** No new hypothesis. **Rule-5.** Fully parametric. -/

namespace StateDependentMPE

/-- Policy type: plain functions from state space `α` to the unit interval. -/
abbrev StatePolicy (α : Type*) := α → Sanctions.MPE.UnitI

noncomputable instance instCompleteLatticeStatePolicy
    {α : Type*} : CompleteLattice (StatePolicy α) :=
  (inferInstance : CompleteLattice (α → Sanctions.MPE.UnitI))

/-- **State-dependent MPE existence** for a monotone best-response operator
on policies: Knaster–Tarski least fixed point. -/
theorem state_dependent_MPE_exists_lifted
    {α : Type*}
    (BR : StatePolicy α →o StatePolicy α) :
    ∃ p : StatePolicy α, BR p = p :=
  ⟨OrderHom.lfp BR, OrderHom.map_lfp BR⟩

/-- **Joint two-player state-dependent MPE existence** on the product
policy lattice. -/
theorem joint_state_dependent_MPE_exists
    {α β : Type*}
    (BR : (StatePolicy α × StatePolicy β) →o (StatePolicy α × StatePolicy β)) :
    ∃ p : StatePolicy α × StatePolicy β, BR p = p :=
  ⟨OrderHom.lfp BR, OrderHom.map_lfp BR⟩

/-- **Least-fixed-point induction** for properties preserved by the
best-response operator and closed under suprema. -/
theorem state_dependent_MPE_induction
    {α : Type*}
    (BR : StatePolicy α →o StatePolicy α)
    {P : StatePolicy α → Prop}
    (h_preserved : ∀ p, P p → p ≤ OrderHom.lfp BR → P (BR p))
    (h_sSup_closed : ∀ s : Set (StatePolicy α),
      (∀ p ∈ s, P p) → P (sSup s)) :
    P (OrderHom.lfp BR) :=
  OrderHom.lfp_induction BR h_preserved h_sSup_closed

end StateDependentMPE

end Sanctions
