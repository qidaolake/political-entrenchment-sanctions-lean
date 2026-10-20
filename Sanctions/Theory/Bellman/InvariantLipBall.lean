/-
Sanctions/Theory/Bellman/InvariantLipBall.lean

**Audit-37 Problem 3 closure: `valLipBall` carrier.**

The audit-37 critique flags `valBall M` (the BCF sup-norm ball) as too
broad a carrier for the JET bridge: it is *not* true that every
bounded continuous function in a sup-norm ball is uniformly Lipschitz
with a common constant. The audit-34 bridge takes
`h_V_T_lipschitz_carrier` as a hypothesis on top of `valBall M`
membership, but discharging that hypothesis at concrete payoff classes
requires a strictly narrower carrier.

This file introduces the narrower **Lipschitz-bounded ball**:

```lean
valLipBall M K := { V : Val | ‖V‖ ≤ M ∧ ValueLipschitzWith V K }
```

* `valLipBall_isClosed` — closed in BCF sup-norm (intersection of a
  closed ball with a closed Lipschitz set; the Lipschitz set is closed
  because pointwise inequalities are preserved by uniform limits).
* `valLipBall_nonempty` — the zero function is in `valLipBall M K` for
  `M ≥ 0` and `K ≥ 0`.
* `ValueClass.ofLipBall` — constructor of a `ValueClass` on
  `valLipBall M K`.
* `ofLipBall_V_T_lipschitz_carrier` — automatic discharge of
  `h_V_T_lipschitz_carrier` (the audit-34 bridge's category-(3)
  primitive) from the carrier definition itself.

The substantive `IsInvariant` discharge from primitive payoff
Lipschitz constants is left as an explicit theorem-parameter primitive
at the abstract layer (the Bellman operators preserve K-Lipschitz
under suitable margins `K ≥ L_U_x / (1 - β · γ_F)`); concrete
instantiations discharge it by direct calculation.

## Rule compliance

**Rule 1.** The carrier is a structural object; the dynamics use
existing equilibrium-derived operators (`jointTarget_BCF_on`,
`jointSender_BCF_on` from `InvariantValueClass.lean`).

**Rule 3.** No new `Params` fields. The Lipschitz constant `K` is a
theorem-parameter. The `IsInvariant` predicate remains as the
existing structural Prop; only the carrier is narrowed.

**Rule 5.** Fully parametric over `(M, K)`.
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Bellman.InvariantBall
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.Bellman.ValueLipschitz

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The Lipschitz-bounded ball -/

/-- **Lipschitz-bounded ball.** The set of bounded continuous functions
on `↥S` that lie in the sup-norm ball of radius `M` AND satisfy a
uniform Lipschitz bound with constant `K`. -/
def valLipBall (M K : ℝ) : Set Val :=
  {V : Val | ‖V‖ ≤ M ∧ ValueLipschitzWith V K}

/-- Membership unfold. -/
theorem mem_valLipBall_iff {M K : ℝ} {V : Val} :
    V ∈ valLipBall M K ↔ ‖V‖ ≤ M ∧ ValueLipschitzWith V K := Iff.rfl

/-! ## Closedness of `valLipBall` -/

/-- **The Lipschitz set in BCF is closed.** Uniform limits of
K-Lipschitz functions are K-Lipschitz: the pointwise inequality
`|V_n y₂ - V_n y₁| ≤ K · dist y₁ y₂` is preserved under uniform
convergence. -/
theorem valueLipschitz_isClosed (K : ℝ) :
    IsClosed {V : Val | ValueLipschitzWith V K} := by
  -- The set is the intersection over (y₁, y₂) of pointwise closed sets.
  rw [show {V : Val | ValueLipschitzWith V K}
        = ⋂ (y₁ : ↥(Sanctions.S : Set ℝ)) (y₂ : ↥(Sanctions.S : Set ℝ)),
            {V : Val | |V y₂ - V y₁| ≤ K * dist y₁ y₂} from ?_]
  · -- Each pointwise set is closed.
    apply isClosed_iInter; intro y₁
    apply isClosed_iInter; intro y₂
    -- {V | |V y₂ - V y₁| ≤ K * dist y₁ y₂} is closed: the map V ↦ |V y₂ - V y₁| is continuous.
    have h_eval₁ : Continuous (fun V : Val => V y₁) :=
      ContinuousEvalConst.continuous_eval_const y₁
    have h_eval₂ : Continuous (fun V : Val => V y₂) :=
      ContinuousEvalConst.continuous_eval_const y₂
    exact isClosed_le ((h_eval₂.sub h_eval₁).abs) continuous_const
  · -- Set equality.
    ext V
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h y₁ y₂; exact h y₁ y₂
    · intro h y₁ y₂; exact h y₁ y₂

/-- `valLipBall M K` is closed in BCF sup-norm: intersection of two
closed sets. -/
theorem valLipBall_isClosed (M K : ℝ) :
    IsClosed (valLipBall M K) := by
  unfold valLipBall
  rw [show {V : Val | ‖V‖ ≤ M ∧ ValueLipschitzWith V K}
        = {V : Val | ‖V‖ ≤ M} ∩ {V : Val | ValueLipschitzWith V K} from rfl]
  exact (isClosed_le continuous_norm continuous_const).inter
    (valueLipschitz_isClosed K)

/-! ## Nonemptiness of `valLipBall` (zero function) -/

theorem zero_mem_valLipBall {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (0 : Val) ∈ valLipBall M K := by
  refine ⟨?_, ?_⟩
  · show ‖(0 : Val)‖ ≤ M; simp [hM]
  · -- Zero function is 0-Lipschitz, hence K-Lipschitz for any K ≥ 0.
    intro y₁ y₂
    show |(0 : Val) y₂ - (0 : Val) y₁| ≤ K * dist y₁ y₂
    simp; exact mul_nonneg hK dist_nonneg

theorem valLipBall_nonempty {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (valLipBall M K).Nonempty := ⟨0, zero_mem_valLipBall hM hK⟩

/-- `valLipBall ⊆ valBall`. -/
theorem valLipBall_subset_valBall (M K : ℝ) :
    valLipBall M K ⊆ valBall M := by
  intro V hV
  exact hV.1

/-! ## `ValueClass.ofLipBall` constructor -/

namespace ValueClass

/-- Construct a `ValueClass` from the Lipschitz-bounded ball plus
uniqueness primitives restricted to that ball. The carrier is
`valLipBall M K`. This is strictly narrower than `ofBall` (since
`valLipBall ⊆ valBall`). -/
noncomputable def ofLipBall
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h_unique_S : ∀ V_S ∈ valLipBall M K, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipBall M K,
        ∀ V_S ∈ valLipBall M K, p.TargetArgmaxUnique V_T V_S) :
    p.ValueClass where
  carrier := valLipBall M K
  isClosed := valLipBall_isClosed M K
  nonempty := valLipBall_nonempty hM hK
  sender_unique_on := h_unique_S
  target_unique_on := h_unique_T

end ValueClass

/-! ## Automatic discharge of `h_V_T_lipschitz_carrier` -/

/-- **`h_V_T_lipschitz_carrier` is automatic on `valLipBall`.** The
carrier definition itself imposes the K-Lipschitz constraint on every
element. -/
theorem ofLipBall_V_T_lipschitz_carrier
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h_unique_S : ∀ V_S ∈ valLipBall M K, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipBall M K,
        ∀ V_S ∈ valLipBall M K, p.TargetArgmaxUnique V_T V_S) :
    ∀ V_T : Val,
      V_T ∈ (ValueClass.ofLipBall (p := p) hM hK h_unique_S h_unique_T).carrier →
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
        |V_T y₁ - V_T y₂| ≤ K * dist y₁ y₂ := by
  intro V_T hV_T y₁ y₂
  have h_lip : ValueLipschitzWith V_T K := hV_T.2
  -- ValueLipschitzWith : ∀ y₁ y₂, |V y₂ - V y₁| ≤ K * dist y₁ y₂.
  -- Apply with (y₁ := y₂, y₂ := y₁) to get |V y₁ - V y₂| ≤ K · dist y₂ y₁,
  -- then symmetrize the dist via dist_comm.
  have h := h_lip y₂ y₁
  rw [dist_comm] at h
  exact h

/-! ## Round-15 Priority 5: structural discharger for `IsInvariant` on `valLipBall`

The certificate's most opaque obligation is `D.IsInvariant` — the
joint Bellman operators preserve the carrier under iteration.
Priority 5 in the shrink plan aims to discharge this from primitive
payoff Lipschitz constants, building on:
* `bellmanBCF_preserves_lipschitz_cone` and
  `bellmanS_BCF_preserves_lipschitz_cone` (in
  `Theory/Bellman/ValueLipschitz.lean`) — single-operator Lipschitz
  cone preservation from primitive `(L_U, γ)` plus margin
  `L_U + β·K·γ ≤ K`.
* `ofBall_IsInvariant_of_cube_bounds` (in
  `Theory/Bellman/InvariantBall.lean`) — sup-norm cube-bound
  invariance from payoff cube bounds + SLP margins.

**Round-15 deliverable (this round):** the structural carrier-set
decomposition `mem_valLipBall_iff_mem_valBall_and_lipschitz` plus a
documented architecture for the full discharger. The actual
operator-level preservation hypotheses connecting `jointTarget_BCF`
and `jointSender_BCF_on` to `bellmanBCF` / `bellmanS_BCF` require
substantial intermediate work (notably Lipschitz analysis of the
carrier-local leader selector `α_on V_T V_S`) that is honestly
Round-16+ scope.

**Deferred to Round 16+:**
* `ofLipBall_IsInvariant_of_payoff_lipschitz` — full discharger from
  primitive payoff/transition Lipschitz constants. Requires
  (i) Lipschitz analysis of `α_on V_T V_S` from V_T/V_S Lipschitz,
  (ii) joint analog of `bellmanBCF_preserves_lipschitz_cone` for the
  carrier-local joint operator, (iii) Sender side via existing
  `bellmanS_BCF_preserves_lipschitz_cone` at the leader `α_on`.

## Rule compliance
* Rule 1: structural — no strategy fixings.
* Rule 3: no new fields; what lands here is a set-theoretic
  decomposition (`mem_valLipBall_iff_mem_valBall_and_lipschitz`).
* Rule 5: fully parametric over `(M, K)`.
* Rule 8: paraphrase above. -/

/-- **Round-15 Priority 5: structural decomposition of `valLipBall`
membership.** `V ∈ valLipBall M K ↔ V ∈ valBall M ∧ ValueLipschitzWith V K`.
A trivial restatement of the definition, exposed as a named lemma
because the Round-16 IsInvariant discharger consumes the two
component invariances separately (sup-norm cube invariance from
`ofBall_IsInvariant_of_cube_bounds` plus the Lipschitz-cone
invariance from a joint analog of `bellmanBCF_preserves_lipschitz_cone`).
The intersection of two invariant sets is invariant. -/
theorem mem_valLipBall_iff_mem_valBall_and_lipschitz
    {M K : ℝ} {V : Val} :
    V ∈ valLipBall M K ↔ V ∈ valBall M ∧ ValueLipschitzWith V K := by
  constructor
  · intro hV; exact ⟨hV.1, hV.2⟩
  · intro ⟨h_norm, h_lip⟩; exact ⟨h_norm, h_lip⟩

/-! ## Round-16 Priority 5 closure: structural `IsInvariant` discharger

The structural conditional discharger
`ofLipBall_IsInvariant_of_preservation` bridges
operator-level carrier-preservation facts to the
`ValueClass.IsInvariant` predicate the certificate consumes.

Given hypotheses that say:
* the joint Target Bellman operator `jointTarget_BCF V_T V_S _` sends
  `valLipBall × valLipBall` into `valLipBall`,
* the joint Sender Bellman operator (`jointSender_BCF_on V_T V_S`,
  evaluated against the carrier-local leader selector
  `D.α_on V_T V_S`) sends `valLipBall × valLipBall` into `valLipBall`,

produce `(ValueClass.ofLipBall hM hK h_unique_S h_unique_T).IsInvariant`.

The proof is a one-line bundling. The hypotheses are designed to be
provable in concrete instantiations via:
* `ofBall_IsInvariant_of_cube_bounds` (norm bound, from primitive
  cube bounds + sup-norm margin),
* `bellmanBCF_preserves_lipschitz_cone` (Target Lipschitz preservation
  at the joint integrand, from primitive payoff/transition Lipschitz —
  requires σ_dyn Lipschitz, hence "deeper" companion analysis),
* `bellmanS_BCF_preserves_lipschitz_cone` (Sender Lipschitz preservation
  at the leader α_on V_T V_S, from primitive payoff/transition Lipschitz).

## Rule compliance for Round 16
* Rule 1: structural — no strategies fixed.
* Rule 3: pure structural discharger; no new fields, no new
  assumptions added to the certificate. The user's two preservation
  hypotheses are scalar-checkable facts about the joint operators.
* Rule 5: fully parametric over `(M, K)`.
* Rule 8: paraphrase above.
* Rule 9: discharger is vacuous unless the user supplies the two
  preservation facts; witness deferred to concrete instantiation
  rounds where users construct `jointTarget_BCF` preservation from
  primitive payoff Lipschitz + σ_dyn Lipschitz hypothesis. -/

/-- **Round-16 Priority 5 structural discharger for `IsInvariant`
on `valLipBall`.**

From two operator-level carrier-preservation hypotheses — Target
joint Bellman preserves `valLipBall`; Sender joint Bellman
preserves `valLipBall` (evaluated at the carrier-local leader
selector) — produce `(ValueClass.ofLipBall ...).IsInvariant`.

The hypotheses are designed for direct supply via existing project
infrastructure (`ofBall_IsInvariant_of_cube_bounds` for norm bounds,
`bellmanBCF_preserves_lipschitz_cone` and
`bellmanS_BCF_preserves_lipschitz_cone` for Lipschitz preservation).
Bundling them through this discharger eliminates the certificate's
opaque `IsInvariant` Prop and replaces it with scalar-checkable
operator-level facts.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem ofLipBall_IsInvariant_of_preservation
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h_unique_S : ∀ V_S ∈ valLipBall M K, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipBall M K,
        ∀ V_S ∈ valLipBall M K, p.TargetArgmaxUnique V_T V_S)
    (h_T_preserves :
      ∀ V_T V_S : Val,
        (hV_T : V_T ∈ valLipBall M K) →
        (hV_S : V_S ∈ valLipBall M K) →
        p.jointTarget_BCF_on_S V_T V_S (h_unique_S V_S hV_S).toOnI ∈ valLipBall M K)
    (h_S_preserves :
      ∀ V_T V_S : Val,
        (hV_T : V_T ∈ valLipBall M K) →
        (hV_S : V_S ∈ valLipBall M K) →
        (ValueClass.ofLipBall (p := p) hM hK h_unique_S h_unique_T).jointSender_BCF_on
          ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ ∈ valLipBall M K) :
    (ValueClass.ofLipBall (p := p) hM hK h_unique_S h_unique_T).IsInvariant := by
  intro V_T V_S
  refine ⟨?_, ?_⟩
  · -- jointTarget_BCF_on V_T V_S ∈ valLipBall M K
    -- jointTarget_BCF_on unfolds to jointTarget_BCF V_T.val V_S.val _
    -- with the Sender uniqueness witness automatically lifted from
    -- the ofLipBall carrier membership.
    exact h_T_preserves V_T.val V_S.val V_T.property V_S.property
  · -- jointSender_BCF_on V_T V_S ∈ valLipBall M K
    exact h_S_preserves V_T.val V_S.val V_T.property V_S.property

/-! ## Round-16 Priority 5: Sender-side Lipschitz preservation from primitives

The Sender side of the IsInvariant discharger is straightforward:
`jointSender_BCF_on V_T V_S = bellmanS_BCF (α_on V_T V_S) ... V_S.val`,
so the existing `bellmanS_BCF_preserves_lipschitz_cone` (in
`Theory/Bellman/ValueLipschitz.lean`) gives the Lipschitz part
directly. The norm part is the standard SLP cube-bound argument.

The Target side requires Lipschitz analysis of `σ_dyn V_S x a` in
`x` — a companion result that's the canonical "γ_σ envelope
discharger" mentioned in the shrink plan. For paper-facing concrete
instantiations (e.g. LQ payoffs with closed-form σ_dyn), this is
provable directly; the general result is deferred. -/

/-- **Round-17 helper: `bellmanS_BCF` lands in `valLipBall` from
primitive cube + Lipschitz hypotheses.** A composite wrapper
combining the existing `bellmanS_BCF_norm_le` (sup-norm bound from
cube bounds + sup-norm margin) and `bellmanS_BCF_preserves_lipschitz_cone`
(Lipschitz-cone preservation from primitive payoff and transition
Lipschitz constants + margin), discharging
`bellmanS_BCF α hα V_S ∈ valLipBall M K` in one step.

Round 17 uses this at `α := D.α_on V_T V_S` to discharge the Sender
side of the `h_S_preserves` hypothesis of
`ofLipBall_IsInvariant_of_preservation` from primitive payoff
constants. The Target side requires the γ_σ envelope companion
(Round 18+).

## Rule compliance
* Rule 1: structural — no strategies fixed.
* Rule 3: pure composition of existing dischargers; no new
  assumptions.
* Rule 5: fully parametric over `(α, hα, V_S, M, K, cube_S, L_U_S, γ_F)`.
* Rule 8: paraphrase above.
* Rule 22: general in `F`; the transition enters only through the state
  modulus `γ_F` in `h_F_lip`.

Round BJ1.2 (2026-10-07): four sign binders are gone. `0 ≤ β_S` is the
`Params` field; `0 ≤ cube_S` and the radius sign `0 ≤ M` are derived inside the
sup-norm bound (from the cube bound at `(0, 0, 0)` and from `‖V_S‖ ≤ M`); and
`0 ≤ γ_F` was never read. -/
theorem bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
    {α : ℝ → ℝ} (hα : Continuous α)
    (α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (V_S : Val)
    {M K cube_S L_U_S γ_F : ℝ}
    (hK_nn : 0 ≤ K)
    (hV_S_mem : V_S ∈ valLipBall M K)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_U_S_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂ (α x₂) s - p.U_S x₁ (α x₁) s| ≤ L_U_S * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_norm_margin : cube_S + p.β_S * M ≤ M)
    (h_lip_margin : L_U_S + p.β_S * K * γ_F ≤ K) :
    p.bellmanS_BCF α hα V_S ∈ valLipBall M K := by
  -- valLipBall membership = (norm bound) ∧ (Lipschitz bound).
  refine ⟨?_, ?_⟩
  · -- ‖bellmanS_BCF α hα V_S‖ ≤ M.
    have h_norm_step :=
      p.bellmanS_BCF_norm_le hα α_mem V_S hV_S_mem.1 hU_S_cube
    -- h_norm_step : ‖bellmanS_BCF α hα V_S‖ ≤ cube_S + β_S * M
    -- h_norm_margin : cube_S + β_S * M ≤ M
    linarith
  · -- ValueLipschitzWith (bellmanS_BCF α hα V_S) K.
    exact p.bellmanS_BCF_preserves_lipschitz_cone hα V_S
      hK_nn hV_S_mem.2 h_U_S_lip h_F_lip h_lip_margin

/-! ## Round-20 γ_σ envelope companion: Target side

The Target-side analog of Round 17's Sender helpers. Where the
Sender-side `jointSender_BCF_on V_T V_S` unfolds to
`bellmanS_BCF α_on V_T V_S ... V_S.val` and inherits Lipschitz
preservation from `bellmanS_BCF_preserves_lipschitz_cone`, the
Target-side `jointTarget_BCF V_T V_S _` is the `sSup` over `a ∈ I`
of `joint_T_integrand V_T V_S x a`, which uses
`σ_dyn V_S x a` inside `U_T`. There is no direct off-the-shelf
"bellmanBCF preserves Lipschitz" wrapper that applies, because the
integrand's `x`-dependence chains through `σ_dyn`.

Round 20 takes the cleanest abstract interface: the user supplies
**the joint integrand's Lipschitz constant `L_int` in `x` directly
as a primitive** (incorporating any σ_dyn x-dependence), and the
wrapper handles the `sSup`-over-`a` preservation via the existing
`Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd` (in
`Foundations/SupDiff.lean`). Concrete instantiations with closed-form
σ_dyn (e.g. LQ, polynomial-quadratic) compute `L_int` directly. The
deeper question of deriving `L_int` from primitive payoff Lipschitz
constants plus a σ_dyn Lipschitz hypothesis `γ_σ` (the "γ_σ envelope
discharger" in the planning round) is a further refinement available
in C² settings via the envelope theorem.

## Rule compliance
* Rule 1: structural — no strategy fixings.
* Rule 3: pure composition. No new fields. The user-supplied
  primitive `h_integrand_lipschitz` is strictly weaker than the
  opaque `IsInvariant` Prop it replaces (one scalar Lipschitz
  bound + scalar margin in place of a structural preservation
  obligation).
* Rule 5: fully parametric over `(V_T, V_S, L_int, cube_T, M)`.
* Rule 8: paraphrase above. -/

/-- **Round-20 helper: `jointTarget_BCF V_T V_S _` is `L`-Lipschitz
from a pointwise integrand Lipschitz bound.**

From the pointwise-in-x bound `|joint_T_integrand V_T V_S x₂ a -
joint_T_integrand V_T V_S x₁ a| ≤ L · dist x₁ x₂` (uniform in
`a ∈ I`), conclude
`ValueLipschitzWith (jointTarget_BCF V_T V_S h_unique) L`.

The user supplies the pointwise integrand Lipschitz directly.

Round BJ1.2 (2026-10-07): the bound is the only hypothesis. The cube block
(`cube_T`, `R_T`, `‖V_T‖ ≤ R_T`, the cube bound and their signs) and `0 ≤ L`
were there only to make the integrand image bounded above, and that follows
from primitives: `cube_bound_U_T` bounds `|U_T|` on the feasible cube (the stage
payoff is continuous on a compact set), and `‖V_T‖` bounds the continuation, so
the integrand is at most `cube_T + β_T · ‖V_T‖`. `0 ≤ β_T` is the `Params` field.
General in `F`: the transition enters only through the integrand.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem jointTarget_BCF_lipschitz_of_integrand_lipschitz
    (V_T V_S : Val) (h_unique : p.DynamicArgmaxUnique V_S)
    {L : ℝ}
    (h_integrand_lipschitz :
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ L * dist x₁ x₂) :
    ValueLipschitzWith (p.jointTarget_BCF_on_S V_T V_S h_unique.toOnI) L := by
  intro y₁ y₂
  -- jointTarget_BCF V_T V_S _ y_i = sSup ((fun a => joint_T_integrand V_T V_S y_i.val a) '' I)
  rw [p.jointTarget_BCF_on_S_apply V_T V_S h_unique.toOnI y₁,
      p.jointTarget_BCF_on_S_apply V_T V_S h_unique.toOnI y₂]
  -- Apply the sup-difference lemma.
  -- Goal: |sSup (f y₂.val) - sSup (f y₁.val)| ≤ L * dist y₁ y₂.
  -- We need: pointwise difference + uniform abs bound.
  have h_pointwise :
      ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S y₂.val a
          - p.joint_T_integrand V_T V_S y₁.val a|
          ≤ L * dist y₁ y₂ := fun a ha =>
    h_integrand_lipschitz y₁ y₂ a ha
  -- Uniform pointwise bound on the integrand (for BddAbove), from the
  -- primitive cube bound on `U_T` and the sup norm of `V_T`.
  obtain ⟨cube_T, -, hU_T_cube⟩ := p.cube_bound_U_T
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_int_bound :
      ∀ y : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S y.val a| ≤ cube_T + p.β_T * ‖V_T‖ := by
    intro y a ha
    have hy_mem : y.val ∈ Sanctions.I := ⟨y.property.1, y.property.2⟩
    simp only [joint_T_integrand]
    have h_σ_mem : p.σ_dyn V_S y.val a ∈ Sanctions.I :=
      p.σ_dyn_mem V_S y.val a
    have h_U_bound :
        |p.U_T y.val a (p.σ_dyn V_S y.val a)| ≤ cube_T :=
      hU_T_cube y.val hy_mem a ha (p.σ_dyn V_S y.val a) h_σ_mem
    have h_V_bound :
        |V_T (Sanctions.clipS'
          (p.F y.val (p.σ_dyn V_S y.val a)))| ≤ ‖V_T‖ := by
      have := BoundedContinuousFunction.norm_coe_le_norm V_T
        (Sanctions.clipS' (p.F y.val (p.σ_dyn V_S y.val a)))
      rwa [Real.norm_eq_abs] at this
    calc |p.U_T y.val a (p.σ_dyn V_S y.val a)
            + p.β_T * V_T (Sanctions.clipS'
              (p.F y.val (p.σ_dyn V_S y.val a)))|
        ≤ |p.U_T y.val a (p.σ_dyn V_S y.val a)|
            + |p.β_T * V_T (Sanctions.clipS'
              (p.F y.val (p.σ_dyn V_S y.val a)))| := abs_add_le _ _
      _ = |p.U_T y.val a (p.σ_dyn V_S y.val a)|
            + p.β_T * |V_T (Sanctions.clipS'
              (p.F y.val (p.σ_dyn V_S y.val a)))| := by
            rw [abs_mul, abs_of_nonneg hβ_T_nn]
      _ ≤ cube_T + p.β_T * ‖V_T‖ := by gcongr
  have h_I_ne : (Sanctions.I : Set ℝ).Nonempty := ⟨0, by simp [Sanctions.I]⟩
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) h_I_ne (M := L * dist y₁ y₂)
    (Bf := cube_T + p.β_T * ‖V_T‖) (Bg := cube_T + p.β_T * ‖V_T‖)
  · intro a ha; exact h_pointwise a ha
  · intro a ha
    have := h_int_bound y₂ a ha
    exact le_of_abs_le this
  · intro a ha
    have := h_int_bound y₁ a ha
    exact le_of_abs_le this

/-- **Round-20 helper: `jointTarget_BCF V_T V_S _` lands in
`valLipBall` from primitive cube + integrand Lipschitz.**
Composes `jointTarget_BCF_norm_le` (existing, norm bound) with the
new `jointTarget_BCF_lipschitz_of_integrand_lipschitz` (Lipschitz
bound), discharging both halves of `valLipBall` membership in one
step.

Round BJ1.2 (2026-10-07): the four sign binders `0 ≤ M`, `0 ≤ K`,
`0 ≤ cube_T`, `0 ≤ β_T` are gone: the radius and cube signs are derived inside
the sup-norm bound, `0 ≤ β_T` is the `Params` field, and `0 ≤ K` was read only
by the (deleted) unused binder of the Lipschitz half. General in `F`.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz
    (V_T V_S : Val) (h_unique : p.DynamicArgmaxUnique V_S)
    {M K cube_T : ℝ}
    (hV_T_norm : ‖V_T‖ ≤ M)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (h_norm_margin : cube_T + p.β_T * M ≤ M)
    (h_integrand_lipschitz :
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ K * dist x₁ x₂) :
    p.jointTarget_BCF_on_S V_T V_S h_unique.toOnI ∈ valLipBall M K := by
  refine ⟨?_, ?_⟩
  · -- Norm bound: ‖jointTarget_BCF V_T V_S _‖ ≤ cube_T + β_T·M ≤ M.
    have h_norm_step :=
      p.jointTarget_BCF_norm_le V_T V_S h_unique hV_T_norm hU_T_cube
    linarith
  · -- Lipschitz bound: ValueLipschitzWith K.
    exact p.jointTarget_BCF_lipschitz_of_integrand_lipschitz V_T V_S h_unique
      h_integrand_lipschitz

/-- **Round-20 Target-side closure of `h_T_preserves`.**
Discharges the Target-side hypothesis of
`ofLipBall_IsInvariant_of_preservation` from primitive cube + a
per-`(V_T, V_S)` joint integrand Lipschitz constant.

The user supplies `h_integrand_lipschitz_at_carrier V_T hV_T V_S hV_S`
— the pointwise-in-x Lipschitz bound on the joint integrand
`joint_T_integrand V_T V_S x a` with constant `K` (matching the
carrier's Lipschitz constant), uniform in `a ∈ I`. This is provable
in concrete instantiations from primitive payoff Lipschitz constants
plus a σ_dyn Lipschitz hypothesis.

Round BJ1.2 (2026-10-07): the sign binders `0 ≤ M`, `0 ≤ K`, `0 ≤ cube_T` and
`0 ≤ β_T` are gone (derived or unread, as in
`jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz`). General in `F`.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem h_T_preserves_of_integrand_lipschitz
    {M K cube_T : ℝ}
    (h_unique_S : ∀ V_S ∈ valLipBall M K, p.DynamicArgmaxUnique V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (h_norm_margin : cube_T + p.β_T * M ≤ M)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipBall M K)
        (V_S : Val) (_hV_S : V_S ∈ valLipBall M K),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ K * dist x₁ x₂) :
    ∀ V_T V_S : Val,
      (hV_T : V_T ∈ valLipBall M K) →
      (hV_S : V_S ∈ valLipBall M K) →
      p.jointTarget_BCF_on_S V_T V_S (h_unique_S V_S hV_S).toOnI ∈ valLipBall M K := by
  intro V_T V_S hV_T hV_S
  exact p.jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz V_T V_S
    (h_unique_S V_S hV_S) hV_T.1 hU_T_cube h_norm_margin
    (h_integrand_lipschitz_at_carrier V_T hV_T V_S hV_S)

/-- **Round-17 Sender-side closure of `h_S_preserves`.**
Discharges the Sender-side hypothesis of
`ofLipBall_IsInvariant_of_preservation` from primitive cube +
payoff-Lipschitz-at-leader + transition Lipschitz + the two margins.

The user supplies `h_U_S_lip_at_α V_T hV_T V_S hV_S` — the
per-`(V_T, V_S)` Lipschitz constant of the composite
`s ↦ U_S(x, D.α_on V_T V_S x, s)` in `x`, which absorbs both
direct `x`-dependence and the chain via `α_on`.

Round BJ1.2 (2026-10-07): the sign binders `0 ≤ cube_S` (derived from the cube
bound), `0 ≤ γ_F` (never read) and `0 ≤ β_S` (the `Params` field) are gone.
`hM_nn` and `hK_nn` stay: the carrier `ofLipBall` in the statement needs them.
General in `F`. -/
theorem h_S_preserves_of_payoff_lipschitz
    {M K cube_S L_U_S γ_F : ℝ}
    (hM_nn : 0 ≤ M) (hK_nn : 0 ≤ K)
    (h_unique_S : ∀ V_S ∈ valLipBall M K, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipBall M K,
        ∀ V_S ∈ valLipBall M K, p.TargetArgmaxUnique V_T V_S)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_U_S_lip_at_α :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipBall M K)
        (V_S : Val) (hV_S : V_S ∈ valLipBall M K),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂
            ((ValueClass.ofLipBall (p := p) hM_nn hK_nn h_unique_S h_unique_T).α_on
                ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₂) s
          - p.U_S x₁
            ((ValueClass.ofLipBall (p := p) hM_nn hK_nn h_unique_S h_unique_T).α_on
                ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_norm_margin : cube_S + p.β_S * M ≤ M)
    (h_lip_margin : L_U_S + p.β_S * K * γ_F ≤ K) :
    ∀ V_T V_S : Val,
      (hV_T : V_T ∈ valLipBall M K) →
      (hV_S : V_S ∈ valLipBall M K) →
      (ValueClass.ofLipBall (p := p) hM_nn hK_nn h_unique_S h_unique_T).jointSender_BCF_on
        ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ ∈ valLipBall M K := by
  intro V_T V_S hV_T hV_S
  apply p.bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
    (M := M) (K := K) (cube_S := cube_S) (L_U_S := L_U_S) (γ_F := γ_F)
    ((ValueClass.ofLipBall (p := p) hM_nn hK_nn h_unique_S h_unique_T).α_on_continuous
        ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩)
    (fun x =>
      (ValueClass.ofLipBall (p := p) hM_nn hK_nn h_unique_S h_unique_T).α_on_mem
        ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x)
    V_S hK_nn hV_S hU_S_cube
    (h_U_S_lip_at_α V_T hV_T V_S hV_S) h_F_lip h_norm_margin h_lip_margin

/-! ## Carrier invariance for `valLipBall` from primitives alone

The two dischargers above supply exactly the two hypotheses that
`ofLipBall_IsInvariant_of_preservation` consumes, but the composition was
never written down, so every user of the Lipschitz-ball carrier still had to
supply `IsInvariant` by hand — economy by economy.

The theorem below closes that. It takes only payoff cube bounds, a state-
Lipschitz bound on the transition, the two Lipschitz-at-carrier estimates, and
three scalar margins, and returns carrier invariance. Nothing about the Bellman
operators is assumed; their behaviour is derived.

This matters beyond convenience. `IsInvariant` is the existence crux (Rule 15):
without it there is no fixed point and hence no equilibrium, so a carrier whose
invariance is *assumed* leaves the whole construction resting on an unproved
premise. With this composition the Lipschitz-ball route joins the sup-norm ball
route (`ofBall_IsInvariant_of_cube_bounds`) in deriving invariance rather than
postulating it. -/

/-- **`IsInvariant` for `valLipBall` from primitives.** Pure composition of
`h_T_preserves_of_integrand_lipschitz` and `h_S_preserves_of_payoff_lipschitz`
through `ofLipBall_IsInvariant_of_preservation`; the hypotheses are exactly the
union of what those two already take, so no assumption is added.

Reading the inputs in English:

* `hU_T_cube` / `hU_S_cube` — the two stage payoffs are bounded on the feasible
  cube;
* `h_integrand_lipschitz_at_carrier` — the Target's joint integrand is
  `K`-Lipschitz in the state, uniformly in the action, at every carrier pair;
* `h_U_S_lip_at_α` — the Sender stage payoff composed with the carrier-local
  leader selector is `L_U_S`-Lipschitz in the state;
* `h_F_lip` — the transition is `γ_F`-Lipschitz in the state;
* the three margins — the two sup-norm ones say each operator's output stays
  inside the radius `M`, and `L_U_S + β_S · K · γ_F ≤ K` says the Sender
  operator does not inflate the Lipschitz constant.

Round BJ1.2 (2026-10-07): `0 ≤ cube_T` and `0 ≤ cube_S` (each derived from its
cube bound) and `0 ≤ γ_F` (never read) are no longer hypotheses. `hM` and `hK`
stay: the carrier `ofLipBall` needs them. General in `F`. -/
theorem ofLipBall_IsInvariant_of_primitives
    {M K cube_T cube_S L_U_S γ_F : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h_unique_S : ∀ V_S ∈ valLipBall M K, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipBall M K,
        ∀ V_S ∈ valLipBall M K, p.TargetArgmaxUnique V_T V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (h_integrand_lipschitz_at_carrier :
      ∀ (V_T : Val) (_hV_T : V_T ∈ valLipBall M K)
        (V_S : Val) (_hV_S : V_S ∈ valLipBall M K),
      ∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        |p.joint_T_integrand V_T V_S x₂.val a
          - p.joint_T_integrand V_T V_S x₁.val a|
          ≤ K * dist x₁ x₂)
    (h_U_S_lip_at_α :
      ∀ (V_T : Val) (hV_T : V_T ∈ valLipBall M K)
        (V_S : Val) (hV_S : V_S ∈ valLipBall M K),
      ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.U_S x₂
            ((ValueClass.ofLipBall (p := p) hM hK h_unique_S h_unique_T).α_on
                ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₂) s
          - p.U_S x₁
            ((ValueClass.ofLipBall (p := p) hM hK h_unique_S h_unique_T).α_on
                ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩ x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
        |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_T_norm_margin : cube_T + p.β_T * M ≤ M)
    (h_S_norm_margin : cube_S + p.β_S * M ≤ M)
    (h_lip_margin : L_U_S + p.β_S * K * γ_F ≤ K) :
    (ValueClass.ofLipBall (p := p) hM hK h_unique_S h_unique_T).IsInvariant :=
  p.ofLipBall_IsInvariant_of_preservation hM hK h_unique_S h_unique_T
    (p.h_T_preserves_of_integrand_lipschitz
      h_unique_S hU_T_cube h_T_norm_margin h_integrand_lipschitz_at_carrier)
    (p.h_S_preserves_of_payoff_lipschitz hM hK
      h_unique_S h_unique_T hU_S_cube h_U_S_lip_at_α h_F_lip
      h_S_norm_margin h_lip_margin)

/-! ## Arbitrary-response Target rows

The joint-game helpers above specialize the Sender response to the model's
equilibrium selector. The following two lemmas expose the same norm and
state-Lipschitz estimates for `targetDynBCF` at any continuous feasible
response. This is useful when the equilibrium response is first constructed
and regularized outside the physical state interval. -/

/-- A generic sup-norm estimate for the Target Bellman operator at any
continuous feasible Sender response.

Round BJ1.2 (2026-10-07): the sign binders `0 ≤ cube` and `0 ≤ R` are derived,
from the cube bound at `(0, 0, 0)` and from `‖V‖ ≤ R`. General in `F`. -/
theorem targetDynBCF_norm_le_of_cube
    (ρ : ℝ → ℝ → ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (hρmem : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ρ x a ∈ Sanctions.I)
    (V : Val) {cube R : ℝ}
    (hV : ‖V‖ ≤ R)
    (hU : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube) :
    ‖p.targetDynBCF ρ hρc V‖ ≤ cube + p.β_T * R := by
  have hR : 0 ≤ R := (norm_nonneg V).trans hV
  have hcube : 0 ≤ cube := (abs_nonneg _).trans
    (hU 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩)
  have hbound : 0 ≤ cube + p.β_T * R :=
    add_nonneg hcube (mul_nonneg p.β_T_mem.1 hR)
  rw [BoundedContinuousFunction.norm_le hbound]
  intro x
  rw [p.targetDynBCF_apply ρ hρc V x]
  have hx : x.val ∈ Sanctions.I :=
    ⟨x.property.1, x.property.2⟩
  have hint : ∀ a ∈ Sanctions.I,
      |p.targetDynIntegrand ρ V x.val a|
        ≤ cube + p.β_T * R := by
    intro a ha
    have hρa := hρmem x.val hx a ha
    have hUa := hU x.val hx a ha (ρ x.val a) hρa
    have hVa :
        |V (Sanctions.clipS' (p.F x.val (ρ x.val a)))| ≤ ‖V‖ := by
      have h := BoundedContinuousFunction.norm_coe_le_norm V
        (Sanctions.clipS' (p.F x.val (ρ x.val a)))
      rwa [Real.norm_eq_abs] at h
    simp only [targetDynIntegrand]
    calc
      |p.U_T x.val a (ρ x.val a)
          + p.β_T * V (Sanctions.clipS' (p.F x.val (ρ x.val a)))|
          ≤ |p.U_T x.val a (ρ x.val a)|
              + |p.β_T
                * V (Sanctions.clipS' (p.F x.val (ρ x.val a)))| :=
            abs_add_le _ _
      _ = |p.U_T x.val a (ρ x.val a)|
              + p.β_T
                * |V (Sanctions.clipS' (p.F x.val (ρ x.val a)))| := by
            rw [abs_mul, abs_of_nonneg p.β_T_mem.1]
      _ ≤ cube + p.β_T * ‖V‖ :=
        add_le_add hUa
          (mul_le_mul_of_nonneg_left hVa p.β_T_mem.1)
      _ ≤ cube + p.β_T * R :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hV p.β_T_mem.1)
  have himage_ne :
      ((fun a => p.targetDynIntegrand ρ V x.val a)
        '' Sanctions.I).Nonempty :=
    ⟨_, ⟨0, by simp [Sanctions.I], rfl⟩⟩
  have himage_bdd :
      BddAbove ((fun a => p.targetDynIntegrand ρ V x.val a)
        '' Sanctions.I) := by
    refine ⟨cube + p.β_T * R, ?_⟩
    rintro y ⟨a, ha, rfl⟩
    exact le_trans (le_abs_self _) (hint a ha)
  have hupper :
      sSup ((fun a => p.targetDynIntegrand ρ V x.val a)
          '' Sanctions.I)
        ≤ cube + p.β_T * R := by
    apply csSup_le himage_ne
    rintro y ⟨a, ha, rfl⟩
    exact le_trans (le_abs_self _) (hint a ha)
  have hlower :
      -(cube + p.β_T * R) ≤
        sSup ((fun a => p.targetDynIntegrand ρ V x.val a)
          '' Sanctions.I) := by
    have hzero_mem :
        p.targetDynIntegrand ρ V x.val 0 ∈
          ((fun a => p.targetDynIntegrand ρ V x.val a)
            '' Sanctions.I) :=
      ⟨0, by simp [Sanctions.I], rfl⟩
    have hzero_le :
        p.targetDynIntegrand ρ V x.val 0 ≤
          sSup ((fun a => p.targetDynIntegrand ρ V x.val a)
            '' Sanctions.I) :=
      le_csSup himage_bdd hzero_mem
    have hzero_lower :
        -(cube + p.β_T * R)
          ≤ p.targetDynIntegrand ρ V x.val 0 :=
      (abs_le.mp (hint 0 (by simp [Sanctions.I]))).1
    exact hzero_lower.trans hzero_le
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Taking the supremum over Target actions preserves a common state
Lipschitz bound on the Target integrand. -/
theorem targetDynBCF_valueLipschitz_of_integrand
    (ρ : ℝ → ℝ → ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V : Val) {K : ℝ}
    (hint : ∀ x y : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      |p.targetDynIntegrand ρ V y.val a
        - p.targetDynIntegrand ρ V x.val a|
        ≤ K * dist x y) :
    ValueLipschitzWith (p.targetDynBCF ρ hρc V) K := by
  intro x y
  rw [p.targetDynBCF_apply ρ hρc V x,
    p.targetDynBCF_apply ρ hρc V y]
  simp only [targetDynBellmanOn]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := K * dist x y)
    (Bf := sSup
      ((fun a => p.targetDynIntegrand ρ V y.val a) '' Sanctions.I))
    (Bg := sSup
      ((fun a => p.targetDynIntegrand ρ V x.val a) '' Sanctions.I))
  · intro a ha
    exact hint x y a ha
  · intro a ha
    exact le_csSup
      (p.targetDynIntegrand_image_bddAbove ρ V hρc y.val)
      ⟨a, ha, rfl⟩
  · intro a ha
    exact le_csSup
      (p.targetDynIntegrand_image_bddAbove ρ V hρc x.val)
      ⟨a, ha, rfl⟩

/-! ## Round-25 Priority 6: closed-form Sender carrier Lipschitz constant

The `StandardComplianceLocalCoreCertificate` field `KS` is currently a
primitive scalar — the user must compute the Sender carrier Lipschitz
constant by hand and supply both `KS` and the Sender wedge
`β_S · KS · δ < mS`.

Hinderer 4.2(c) (Benveniste-Scheinkman envelope; see also project's
`ValueLipschitz.lean` lines 34-36 docstring) gives the closed form:
under a stage payoff Lipschitz constant `L_U_S` for the composite
`(s ↦ U_S(x, α(x), s))` in `x`, a transition Lipschitz constant
`γ_F` for `F(x, s) = (1-δ)x + δs` in `x` at fixed `s`, and the
contraction margin `β_S · γ_F < 1`, the Sender Bellman fixed point
is `K_S := L_U_S / (1 − β_S · γ_F)`-Lipschitz.

This wrapper packages that closed-form derivation as a per-`V_S`
discharger usable inside any `StandardComplianceLocalCoreCertificate`
build: the user supplies `(L_U_S, γ_F, 0 < 1 − β_S · γ_F,
β_S · L_U_S · δ < mS · (1 − β_S · γ_F))`, plus a per-`V_S` Lipschitz
hypothesis matching the closed-form constant, and the wrapper
produces both the original `hS_margin` form
`β_S · K_S · δ < mS` and the carrier-local Lipschitz field.

## Rule compliance

* Rule 1: structural — no strategy fixings.
* Rule 3: pure cat-2 weakening. No new certificate fields are
  added; the original `KS` scalar is now derived as
  `bellmanLipConstant p.β_S γ_F L_U_S` from
  `Foundations/StokeyLucas.lean`, and the original wedge is
  derived from the closed-form wedge by multiplying through the
  positive denominator.
* Rule 5: fully parametric over `(L_U_S, γ_F, mS)`.
* Rule 8: human-language paraphrase in this docstring and the paper.
* Rule 9: non-vacuity witness in `StandardCompliancePolynomialSkeleton.lean`. -/

/-- **Round-25 Hinderer 4.2(c) closed-form Sender wedge.** Given the
contraction margin `0 < 1 − β_S · γ_F` and the closed-form wedge
`β_S · L_U_S · δ < mS · (1 − β_S · γ_F)`, the original
`StandardComplianceLocalCoreCertificate.hS_margin` form
`β_S · (L_U_S / (1 − β_S · γ_F)) · δ < mS` holds.

Algebra: divide the closed-form wedge by the positive denominator
`(1 − β_S · γ_F)`. -/
theorem hS_margin_of_closed_form
    {L_U_S γ_F mS : ℝ}
    (h_denom_pos : 0 < 1 - p.β_S * γ_F)
    (h_wedge_closed : p.β_S * L_U_S * p.δ < mS * (1 - p.β_S * γ_F)) :
    p.β_S * (Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S) * p.δ < mS := by
  unfold Sanctions.StokeyLucas.bellmanLipConstant
  -- Goal: p.β_S * (L_U_S / (1 - p.β_S * γ_F)) * p.δ < mS
  -- Use the positive-denominator rewriting `a/d < b ↔ a < b · d` (when 0 < d).
  rw [show p.β_S * (L_U_S / (1 - p.β_S * γ_F)) * p.δ
        = (p.β_S * L_U_S * p.δ) / (1 - p.β_S * γ_F) from by ring]
  rw [div_lt_iff₀ h_denom_pos]
  exact h_wedge_closed

/-- **Round-25 Hinderer 4.2(c) closed-form `KS` nonnegativity.** Given a
stage payoff Lipschitz constant `L_U_S ≥ 0` and the contraction
margin `0 < 1 − β_S · γ_F`, the closed-form Sender Lipschitz
constant `K_S := L_U_S / (1 − β_S · γ_F)` is non-negative. -/
theorem hKS_nonneg_of_closed_form
    {L_U_S γ_F : ℝ}
    (hL_U_S_nn : 0 ≤ L_U_S)
    (h_denom_pos : 0 < 1 - p.β_S * γ_F) :
    0 ≤ Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S := by
  unfold Sanctions.StokeyLucas.bellmanLipConstant
  exact div_nonneg hL_U_S_nn (le_of_lt h_denom_pos)

/-! ## Round 38 — affine `γ_F = 1 − δ` compatibility helpers

The current `Params` structure carries a general transition `F`.  When a
consumer additionally identifies it with the affine instance
`F(x, s) = (1 − δ) · x + δ · s`, the fixed-sanction state modulus is
`γ_F = 1 − δ`.  The helpers below specialize the R25 / R27 closed-form
algebra to that affine modulus and auto-discharge
`0 < 1 − β · (1 − δ)` from the discount and adjustment-rate bounds.

These declarations do not assert that a general `p.F` is affine.  They
are compatibility helpers for affine-restricted consumers; the
transition-general value theorem instead carries an explicit
`TransitionStateLipschitzWith γ_F` hypothesis.
-/

/-- **Round 38: Sender-side affine contraction-margin positivity.**

    From `Params` constraints `β_S ∈ [0, 1)` and `δ ∈ (0, 1)`, the
    affine-specialization margin `1 − β_S · (1 − δ)` is strictly
    positive — no user-supplied hypothesis required. -/
theorem oneMinus_betaS_oneMinusDelta_pos :
    0 < 1 - p.β_S * (1 - p.δ) := by
  have hβS_lt : p.β_S < 1 := p.β_S_mem.2
  have hβS_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have hδ_pos : 0 < p.δ := p.δ_mem.1
  have hδ_lt : p.δ < 1 := p.δ_mem.2
  have h_one_sub_delta_le_one : 1 - p.δ ≤ 1 := by linarith
  have h_one_sub_delta_nn : 0 ≤ 1 - p.δ := by linarith
  have h_prod_le_betaS : p.β_S * (1 - p.δ) ≤ p.β_S := by
    calc p.β_S * (1 - p.δ)
        ≤ p.β_S * 1 := by gcongr
      _ = p.β_S := mul_one _
  linarith

/-- **Round 38: Target-side affine contraction-margin positivity.**

    From `Params` constraints `β_T ∈ [0, 1)` and `δ ∈ (0, 1)`, the
    affine-specialization margin `1 − β_T · (1 − δ)` is strictly
    positive — no user-supplied hypothesis required. -/
theorem oneMinus_betaT_oneMinusDelta_pos :
    0 < 1 - p.β_T * (1 - p.δ) := by
  have hβT_lt : p.β_T < 1 := p.β_T_mem.2
  have hβT_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have hδ_pos : 0 < p.δ := p.δ_mem.1
  have hδ_lt : p.δ < 1 := p.δ_mem.2
  have h_one_sub_delta_le_one : 1 - p.δ ≤ 1 := by linarith
  have h_one_sub_delta_nn : 0 ≤ 1 - p.δ := by linarith
  have h_prod_le_betaT : p.β_T * (1 - p.δ) ≤ p.β_T := by
    calc p.β_T * (1 - p.δ)
        ≤ p.β_T * 1 := by gcongr
      _ = p.β_T := mul_one _
  linarith

/-- **Round 38: Sender affine closed-form K_S non-negativity.**

    Specializes `hKS_nonneg_of_closed_form` (R25) to `γ_F := 1 − δ`
    and auto-discharges the contraction-margin hypothesis
    `0 < 1 − β_S · (1 − δ)` from `Params` constraints. The user
    supplies only `L_U_S ≥ 0`; no `γ_F`, no `h_denom_pos`.  This is
    algebraic specialization only; interpreting the result as a value
    modulus still requires an affine transition or an independently
    established state modulus `1 − δ`. -/
theorem hKS_nonneg_of_closed_form_canonical
    {L_U_S : ℝ} (hL_U_S_nn : 0 ≤ L_U_S) :
    0 ≤ Sanctions.StokeyLucas.bellmanLipConstant p.β_S (1 - p.δ) L_U_S :=
  p.hKS_nonneg_of_closed_form hL_U_S_nn (p.oneMinus_betaS_oneMinusDelta_pos)

/-- **Round 38: Sender affine margin discharge.**

    Specializes `hS_margin_of_closed_form` (R25) to `γ_F := 1 − δ`
    and auto-discharges the contraction-margin hypothesis. The user
    supplies only the affine-form wedge
    `β_S · L_U_S · δ < mS · (1 − β_S · (1 − δ))`. -/
theorem hS_margin_of_closed_form_canonical
    {L_U_S mS : ℝ}
    (h_wedge_canonical :
      p.β_S * L_U_S * p.δ < mS * (1 - p.β_S * (1 - p.δ))) :
    p.β_S *
      (Sanctions.StokeyLucas.bellmanLipConstant p.β_S (1 - p.δ) L_U_S) *
        p.δ < mS :=
  p.hS_margin_of_closed_form (p.oneMinus_betaS_oneMinusDelta_pos)
    h_wedge_canonical

/-! ## Round 39 Phase 1B — `R_T`, `R_S` carrier sup-norm elimination

The `valLipBall M K` carrier requires `M` to satisfy the sup-norm
Banach margin `cube + β · M ≤ M`, i.e. `M ≥ cube / (1 − β)`. The
minimal choice `M := cube / (1 − β)` makes this margin tight (equality)
and is fully determined by the existing primitive `cube` (R23
auto-discharged from `U_*_continuous`) together with the Params
discount factor. Round 39 Phase 1B provides this closed form and
proves the margin holds with equality, removing `R_T`, `R_S` as
free user-supplied scalars in canonical constructions.

## Rule compliance
* Rule 3 symbol-economy: `M` is identically `cube / (1 − β)` at the
  margin-tight minimum; carrying it as a free parameter widens the
  cognitive surface without adding modeling content.
* Rule 5: fully parametric in `(cube, p)`.
* Rule 8: human-language paraphrase below. -/

/-- **Round 39 Phase 1B: Sender-side canonical minimal carrier sup-norm.**

    The minimum carrier sup-norm `R_S` satisfying the Sender-side
    invariance margin `cube_S + β_S · R_S ≤ R_S`. Closed form
    `R_S := cube_S / (1 − β_S)`. The user supplies only the stage
    sup-bound `cube_S` (itself R23 auto-discharged from
    `U_S_continuous` on `[0,1]³`); `R_S` is derived. -/
def carrierMinNormS (cube_S : ℝ) : ℝ := cube_S / (1 - p.β_S)

/-- **Round 39 Phase 1B: Target-side canonical minimal carrier sup-norm.**

    Closed form `R_T := cube_T / (1 − β_T)`. -/
def carrierMinNormT (cube_T : ℝ) : ℝ := cube_T / (1 - p.β_T)

/-- **Round 39 Phase 1B: Sender canonical R_S non-negativity.**

    From `cube_S ≥ 0` and `β_S ∈ [0, 1)`, the closed-form
    `R_S := cube_S / (1 − β_S)` is non-negative. -/
theorem carrierMinNormS_nonneg {cube_S : ℝ} (hcube_S_nn : 0 ≤ cube_S) :
    0 ≤ p.carrierMinNormS cube_S := by
  unfold carrierMinNormS
  have hβS_lt : p.β_S < 1 := p.β_S_mem.2
  have h_denom_pos : 0 < 1 - p.β_S := by linarith
  exact div_nonneg hcube_S_nn (le_of_lt h_denom_pos)

/-- **Round 39 Phase 1B: Target canonical R_T non-negativity.** -/
theorem carrierMinNormT_nonneg {cube_T : ℝ} (hcube_T_nn : 0 ≤ cube_T) :
    0 ≤ p.carrierMinNormT cube_T := by
  unfold carrierMinNormT
  have hβT_lt : p.β_T < 1 := p.β_T_mem.2
  have h_denom_pos : 0 < 1 - p.β_T := by linarith
  exact div_nonneg hcube_T_nn (le_of_lt h_denom_pos)

/-- **Round 39 Phase 1B: Sender canonical margin (equality form).**

    At the minimal carrier sup-norm `R_S := cube_S / (1 − β_S)`, the
    invariance margin `cube_S + β_S · R_S = R_S` holds with equality.
    Algebra: `cube_S + β_S · cube_S/(1 − β_S) = cube_S · (1 − β_S + β_S)/(1 − β_S)
    = cube_S/(1 − β_S) = R_S`. -/
theorem carrierMinNormS_margin_eq (cube_S : ℝ) :
    cube_S + p.β_S * p.carrierMinNormS cube_S = p.carrierMinNormS cube_S := by
  unfold carrierMinNormS
  have hβS_lt : p.β_S < 1 := p.β_S_mem.2
  have h_denom_ne : (1 - p.β_S) ≠ 0 := by linarith
  field_simp
  ring

/-- **Round 39 Phase 1B: Target canonical margin (equality form).** -/
theorem carrierMinNormT_margin_eq (cube_T : ℝ) :
    cube_T + p.β_T * p.carrierMinNormT cube_T = p.carrierMinNormT cube_T := by
  unfold carrierMinNormT
  have hβT_lt : p.β_T < 1 := p.β_T_mem.2
  have h_denom_ne : (1 - p.β_T) ≠ 0 := by linarith
  field_simp
  ring

/-- **Round 39 Phase 1B: Sender canonical margin (inequality form
    for downstream consumers).**

    At the minimal `R_S`, the standard invariance inequality
    `cube_S + β_S · R_S ≤ R_S` holds (with equality). -/
theorem carrierMinNormS_margin (cube_S : ℝ) :
    cube_S + p.β_S * p.carrierMinNormS cube_S ≤ p.carrierMinNormS cube_S :=
  (p.carrierMinNormS_margin_eq cube_S).le

/-- **Round 39 Phase 1B: Target canonical margin (inequality form).** -/
theorem carrierMinNormT_margin (cube_T : ℝ) :
    cube_T + p.β_T * p.carrierMinNormT cube_T ≤ p.carrierMinNormT cube_T :=
  (p.carrierMinNormT_margin_eq cube_T).le

/-! ## Round 40 — C¹ payoff existence wrappers (Phase 2 completion)

The R39 Phase 2 Foundations (`cube_sup_unitCube_of_continuous`,
`cube_inf_unitCube_of_continuous`, `cube_sup_nonneg_unitCube_of_continuous`)
provide signed sup/inf over `[0,1]³`. Round 40 ships Theory-level
convenience wrappers that lift these to existence-of-bound certificates
for the named scalar `L_U_S` (Sender stage-payoff Lipschitz in `s`) and
`L_U_a` (action-coordinate Lipschitz).

These do not *eliminate* `L_U_S, L_U_a` as economic content — the user
still needs the numeric value to verify the wedge inequalities of
\Cref{ass:sender_pref} (e.g., `slope > β_S · K_S · δ`). What R40
provides is the **existence certificate**: under a C¹ stage payoff
with continuous partial derivative, a uniform Lipschitz bound exists
and is auto-derivable from the payoff structure, so the user does not
have to separately prove the bound for any individual continuous
payoff. This is the realistic R40 deliverable per the Round 39
honest-scope reassessment.

## Rule compliance
* Rule 3 symbol-economy: no new primitive introduced; existence
  certificates produced from existing continuity primitives only.
* Rule 5: fully parametric in the user's claimed partial-derivative
  function.
* Rule 8: human-language paraphrase below. -/

/-- **R40: existence of Sender stage-payoff Lipschitz constant
    `L_U_S` from a continuous claimed partial derivative `∂U_S/∂s`.**

    Under continuity of the user-claimed `∂U_S/∂s : ℝ → ℝ → ℝ → ℝ`
    on the unit cube `[0,1]³`, the existence of a non-negative
    Lipschitz bound `L_U_S ≥ 0` with
    `|∂U_S/∂s(x, a, s)| ≤ L_U_S` for all `(x, a, s) ∈ [0,1]³`
    follows from Weierstrass on the compact cube
    (R23's `cube_bound_unitCube_of_continuous`).

    Once obtained, `L_U_S` feeds into the R25 closed form
    `K_S := L_U_S / (1 − β_S · (1 − δ))` (and hence into the R37
    strict-slope wedge form of \Cref{ass:sender_pref}).

    The user-claimed derivative must additionally be verified as
    the actual partial derivative of `U_S` (e.g., via
    `HasDerivAt (fun s' => p.U_S x a s') (∂U_S/∂s x a s) s`) for
    the R13 chord-form discharger to apply downstream; that step
    is independent of this existence certificate. -/
theorem exists_L_U_S_from_continuous_partial_s
    (U_S_partial_s : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        U_S_partial_s xas.1 xas.2.1 xas.2.2)) :
    ∃ L_U_S : ℝ, 0 ≤ L_U_S ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, |U_S_partial_s x a s| ≤ L_U_S :=
  Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous h_continuous

/-- **R40: existence of Target action Lipschitz constant `L_U_a`
    from a continuous claimed partial derivative `∂U_T/∂a` (or
    `∂U_S/∂a` for the Sender side).**

    Used downstream by R26's Curtat row-Lipschitz closed form. -/
theorem exists_L_U_a_from_continuous_partial_a
    (U_partial_a : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        U_partial_a xas.1 xas.2.1 xas.2.2)) :
    ∃ L_U_a : ℝ, 0 ≤ L_U_a ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, |U_partial_a x a s| ≤ L_U_a :=
  Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous h_continuous

/-! ## Round 41 — C² payoff existence wrappers for IFT / curvature
    primitives

The R31 chord-form IFT and the R29 saturated-α cross-partial
discharger consume scalar primitives `c` (strong-concavity modulus
of the joint Target integrand in `a`), `K_T, K_S` (cross-Hessian
bounds on the joint Target integrand in `a` vs the value-function
coordinates), and `K_S''` (second-derivative bound on the Sender
carrier value `V_S`). Round 41 ships existence wrappers that lift
the R39 Phase 2 Foundations signed sup/inf lemmas to continuous
second-partial-derivative inputs.

As with R40, these are **existence certificates only** — the user
still needs the numeric values of `c, K_T, K_S, K_S''` to verify
the wedge inequalities of \Cref{ass:value_class_restrictions}
(Round 29 cross-partial sign, Round 31 IFT chord form). What R41
provides is the existence guarantee under C² smoothness: if the
user's payoff has continuous second partial derivatives, then
finite bounds on those partials exist on the compact unit cube.

## Rule compliance
* Rule 3 symbol-economy: no new primitives; existence certificates
  from continuity primitives only.
* Rule 5: parametric in the user's second partial functions.
* Rule 8: human-language paraphrase below. -/

/-- **R41: existence of strong-concavity modulus `c` from a
    continuous claimed second partial derivative `∂²U_joint/∂a²`.**

    The R31 chord-form IFT requires `c > 0` such that
    `-∂²(joint Target integrand)/∂a² ≥ c` (strict concavity of the
    Target integrand in `a` with modulus at least `c`). Under
    continuity of the user-claimed `-∂²/∂a²`, a finite lower bound
    `c` exists on the unit cube by R39's signed inf-on-compact.
    The user must additionally verify `c > 0` to apply R31; the
    R41 wrapper guarantees only the existence of *some* finite
    bound, not its strict positivity. -/
theorem exists_c_strongConcavity_from_continuous_neg_partial_aa
    (U_joint_neg_partial_aa : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        U_joint_neg_partial_aa xas.1 xas.2.1 xas.2.2)) :
    ∃ c : ℝ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          c ≤ U_joint_neg_partial_aa x a s :=
  Sanctions.StokeyLucas.cube_inf_unitCube_of_continuous h_continuous

/-- **R41: existence of cross-Hessian bound `K_T` from a continuous
    claimed cross partial `∂²(joint Target)/∂a∂V_T` (read as the
    `V_T`-coordinate of the joint integrand's sensitivity to action
    perturbations, projected to a scalar bound on the unit cube).**

    Used by the R31 chord-form IFT closed form
    `L_α_VT := K_T / c`. -/
theorem exists_K_T_from_continuous_cross_partial
    (cross_partial_aVT : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        cross_partial_aVT xas.1 xas.2.1 xas.2.2)) :
    ∃ K_T : ℝ, 0 ≤ K_T ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          |cross_partial_aVT x a s| ≤ K_T :=
  Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous h_continuous

/-- **R41: existence of cross-Hessian bound `K_S` (R31 IFT
    primitive, distinct from the Sender carrier Lipschitz `K_S`)
    from a continuous claimed cross partial.**

    Used by the R31 chord-form IFT closed form
    `L_α_VS := K_S / c`. The namespace collision with the carrier
    Lipschitz `K_S` is in the abstract IFT layer only; in concrete
    instantiations the two play distinct economic roles. -/
theorem exists_K_S_IFT_from_continuous_cross_partial
    (cross_partial_aVS : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        cross_partial_aVS xas.1 xas.2.1 xas.2.2)) :
    ∃ K_S_IFT : ℝ, 0 ≤ K_S_IFT ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          |cross_partial_aVS x a s| ≤ K_S_IFT :=
  Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous h_continuous

/-! ## Round 44 — Strict-concavity-of-`U_S`-in-`s` Theory wrapper

User-approved Rule-3 trade (2026-06-05): adopt uniform strict
concavity of the Sender stage payoff `U_S` in the sanction `s` as a
project-wide C² structural assumption. Economic content:
**diminishing returns to sanctioning** — each additional unit of
sanction extracts less marginal coercive value than the previous
one. Canonical sanctions-economics assumption (Kaempfer-Lowenberg
1988 implicit; Eaton 1992 explicit; satisfied by every standard
polynomial / logarithmic / exponential sanction-cost model).

The wrapper below derives the strong-concavity modulus `c_σ > 0`
from a uniform-strict-positivity hypothesis on the claimed
`−∂²U_S/∂s²` via Weierstrass on the compact unit cube. Combined
with R25's closed-form Sender carrier Lipschitz and the R44 Curtat
`ofCanonical` constructor in `Foundations/Curtat.lean`, the trade
eliminates the three Curtat primitives `(L_σ, L_U, K_V)` in favor
of `(L_U_T, c_σ)` plus the existing `L_U_S`.

## Rule compliance
* Rule 1: structural, no strategy fixings.
* Rule 3: user-approved structural assumption (strict concavity of
  U_S in s); the assumption surface widens by one C² structural
  primitive in exchange for eliminating two derived scalars `L_σ`
  and `K_V`. Net symbol-economy: `−1`.
* Rule 5: parametric.
* Rule 8: human-language paraphrase below. -/

/-- **R44: existence of the Sender strong-concavity-in-`s` modulus
    `c_σ > 0` from a uniformly-strictly-positive claimed
    `−∂²U_S/∂s² : ℝ → ℝ → ℝ → ℝ`.**

    Under continuity of the claimed `−∂²U_S/∂s²` plus uniform
    strict positivity on the unit cube `[0, 1]³`, Weierstrass-on-
    compact (R44 Foundations
    `cube_inf_pos_unitCube_of_continuous_pos`) produces a strictly
    positive infimum `c_σ` such that
    `c_σ ≤ −∂²U_S/∂s²(x, a, s)` for every `(x, a, s) ∈ [0, 1]³`.

    The user must additionally verify that the claimed
    `−∂²U_S/∂s²` is the actual second partial of `U_S` in `s`
    (via `HasDerivAt`-style witnesses) for downstream IFT and
    R31-style closed-form derivations to apply. -/
theorem exists_c_sigma_pos_from_continuous_strictly_pos_neg_partial_ss
    (U_S_neg_partial_ss : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        U_S_neg_partial_ss xas.1 xas.2.1 xas.2.2))
    (h_strictly_pos :
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          0 < U_S_neg_partial_ss x a s) :
    ∃ c_σ : ℝ, 0 < c_σ ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          c_σ ≤ U_S_neg_partial_ss x a s :=
  Sanctions.StokeyLucas.cube_inf_pos_unitCube_of_continuous_pos
    h_continuous h_strictly_pos

/-! ## Round 42 — Documentation block: canonical entry paths after
    the R37+R38+R39+R40+R41 symbol-economy sweep

This block does not introduce new code; it consolidates the
**canonical entry paths** for users constructing a
`StandardComplianceLocalCoreCertificate` after the sweep, and
documents the post-sweep paper-facing primitive surface.

### Affine compatibility Sender-side entry path

For the Sender preferences and Lipschitz scalars in
\Cref{ass:sender_pref}:

1. **Stage payoff**: supply `U_S` (already a `Params` field) plus
   continuity `U_S_continuous` (already a `Params` field).

2. **Stage Lipschitz `L_U_S`**: either supply a numeric scalar
   directly, or use R40
   `Sanctions.AbstractGame.Params.exists_L_U_S_from_continuous_partial_s`
   to obtain existence from a continuous partial-derivative
   function. Either way, the *value* of `L_U_S` must be known to
   verify the wedge inequality downstream.

3. **Carrier Lipschitz `K_S` under the affine transition**: do NOT
   supply; after establishing `F = affineF δ`, the R25 closed form
   `K_S := L_U_S / (1 − β_S · (1 − δ))` (via
   `Sanctions.StokeyLucas.bellmanLipConstant p.β_S (1 - p.δ) L_U_S`)
   computes this from `L_U_S` and the affine state modulus
   `γ_F = 1 − δ`.  For a general transition, use the explicit
   `γ_F` closed form and discharge `TransitionStateLipschitzWith γ_F`.

4. **Strict-slope wedge**: state as `slope > β_S · K_S · δ` (no
   `m_S` named); use R37 `with_strict_slope_wedge` or its R38
   composite `with_strict_slope_wedge_canonical` to thread the
   strict chord inequality plus a witnessed gap into the
   certificate's internal `m_S` and `hS_margin` fields.  For a general
   transition, prefer the exact transition-adjusted chord, which uses
   the realized distance `|F(x,s₂)-F(x,s₁)|`.

5. **Carrier sup-norm `R_S`**: do NOT supply; the R39 closed form
   `R_S := cube_S / (1 − β_S)` (via
   `Sanctions.AbstractGame.Params.carrierMinNormS p cube_S`)
   computes this from `cube_S` (itself R23 auto-discharged from
   `U_S_continuous`).

### Canonical Target-side entry path

Parallel to the Sender-side, mutatis mutandis:

1. Stage payoff `U_T` and continuity `U_T_continuous` (Params).
2. Stage state-slope `g_U`: numeric scalar or R40
   `exists_g_U_from_continuous_partial_x` (existence only;
   positivity is economic content).
3. Stage loss rate `c_T`: numeric scalar or R40
   `exists_c_T_from_continuous_partial_s`.
4. Carrier min-slope `g_T`: R27 closed form
   `g_T := g_U / (1 − β_T · (1 − δ))`.
5. Loss-offset margin: state as `c_T ≤ β_T · g_T · δ` (no
   intermediate named constants).
6. Carrier sup-norm `R_T`: R39 closed form
   `R_T := cube_T / (1 − β_T)`.

### Net post-sweep primitive surface

| Layer | Paper-facing primitives | Status |
|-------|--------------------------|--------|
| Discount + transition | `β_T, β_S, δ` | Required (irreducible) |
| Stage payoffs | `U_T, U_S` | Required (irreducible) |
| Preference thresholds | `x̄_T, x̄_S, s̄` | Required (irreducible) |
| Sender stage Lipschitz | `L_U_S` | Required (or existence via R40 wrapper) |
| Target stage rate | `c_T` | Required (or existence via R40 wrapper) |
| Target stage state-slope | `g_U` | Required (or existence via R40 wrapper) |
| Curtat row-Lipschitz | `L_σ, L_U, K_V, L_U_a` | Required (or existence via R40) |
| R31 IFT primitives | `c, K_T, K_S_IFT` | Required (or existence via R41) |
| R29 regime | `α_0` or `K_S''` | Required (only the relevant one) |
| Eliminated | `γ_F` (R38), `K_S` (R25), `g_T` (R27), `m_S` (R37), `R_T, R_S` (R39), `cube_T, cube_S` (R23) | Auto-derived |

The cumulative R23+R25+R27+R37+R38+R39+R40+R41 sweep eliminates
the **definitional / closed-form-derivable** scalars (8 in total),
leaving the **content-bearing Lipschitz / slope / curvature
bounds** on the user-input surface. The R40+R41 wrappers convert
the user's specification mode for those content-bearing scalars
from "supply a scalar plus prove a pointwise bound" to "supply a
continuous partial-derivative function" (with the existence
certificate as an inferred consequence).

This is the realistic end-state of the symbol-economy sweep per
the Round 39 honest-scope reassessment.
-/

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
