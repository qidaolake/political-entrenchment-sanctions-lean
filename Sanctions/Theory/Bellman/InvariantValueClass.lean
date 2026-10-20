/-
Sanctions/Theory/Bellman/InvariantValueClass.lean

**Invariant value-class refactor (audit-32 item 3):
loosen global Sender + Target argmax uniqueness to a closed invariant
subset of the BCF value space.**

The audit-32 follow-up patch's
`exists_feedbackStackelberg_from_uniqueness_row_bounds`
(`TargetSelectorFromUnique`) requires *global* uniqueness predicates:

```
h_unique_S_all : ∀ V_S : Val, p.DynamicArgmaxUnique V_S
h_unique_T_all : ∀ V_T V_S : Val, p.TargetArgmaxUnique V_T V_S
```

Economically this is excessive: uniqueness only needs to hold on the
`(V_T, V_S)` pairs that actually arise from Banach iteration (which
under suitable regularity form a closed invariant subset of `Val × Val`).
This file provides a `ValueClass` structure packaging:

* `carrier : Set Val` — a closed nonempty subset of `Val` containing
  every iterate of both V_T and V_S that the Banach iteration touches;
* `sender_unique_on` and `target_unique_on` — the two uniqueness
  primitives restricted to `carrier`.

Combined with an `IsInvariant` hypothesis (the joint Target / Sender
Bellman operators preserve `carrier`), the joint Banach step
`exists_fixedPoint_in_carrier` produces a fixed point on the complete
metric subtype `↥carrier × ↥carrier`. Mathlib's
`IsClosed.completeSpace_coe` provides the subtype completeness; the
generic `joint_contraction_from_row_bounds` (already parametric over
any complete metric space `E`) supplies the joint Banach step on
`E := ↥carrier`. The equilibrium packaging lives in
`InvariantValueClass2.lean` (round BG1.2, 2026-10-06): every `ValueClass`
induces a `ValueClass2`, and
`ValueClass2.exists_feedbackStackelbergTop_of_jointFixedPoint` turns a
joint carrier fixed point into a top-selector equilibrium.

The user need not exhibit global uniqueness — only uniqueness inside
the closed invariant class, which in practice (Sender Bellman
iteration with bounded payoffs) is the bounded ball
`{V : Val | ‖V‖ ≤ M}` for the natural sup-norm bound
`M := ‖U_S‖_∞ / (1 - β_S)`.

## Rule compliance

**Rule 1.** Every strategy is equilibrium-derived: V_T, V_S are the
Banach fixed point on the subtype; α is the leader argmax via
`targetArgmax`; σ_dyn is the Sender forward-looking argmax via
`Classical.choose`. No hand-chosen rule.

**Rule 3.** No new `Params` fields. `ValueClass` is a local
parametric structure. Loosens — does not widen — the assumption
surface: where the previous theorem took global uniqueness,
the present one takes restricted uniqueness on a closed invariant
class.

**Rule 5.** Fully parametric over `(p, D : ValueClass)`. No
witness specialization.
-/

import Sanctions.Theory.Equilibrium.TargetSelectorFromUnique

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Invariant value class -/

/-- **Invariant value class.** A closed nonempty subset of `Val` on
which both Sender and Target dynamic argmaxes are unique. Equilibrium
existence will be proved by Banach contraction on the complete metric
subtype `↥carrier × ↥carrier` provided the joint operators preserve
the carrier. -/
structure ValueClass where
  /-- Carrier set in the BCF value space. -/
  carrier : Set Val
  /-- Carrier is closed (so the subtype inherits completeness). -/
  isClosed : IsClosed carrier
  /-- Carrier is nonempty (so the subtype is nonempty). -/
  nonempty : carrier.Nonempty
  /-- Sender argmax uniqueness on the carrier. -/
  sender_unique_on : ∀ V_S ∈ carrier, p.DynamicArgmaxUnique V_S
  /-- Target argmax uniqueness for `(V_T, V_S)` pairs in the
  carrier-product. -/
  target_unique_on : ∀ V_T ∈ carrier, ∀ V_S ∈ carrier,
    p.TargetArgmaxUnique V_T V_S

namespace ValueClass

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass)

/-- The subtype of values in the carrier. -/
abbrev Carrier : Type := ↥D.carrier

instance instCompleteSpaceCarrier : CompleteSpace D.Carrier :=
  haveI : IsClosed D.carrier := D.isClosed
  inferInstance

instance instNonemptyCarrier : Nonempty D.Carrier :=
  D.nonempty.to_subtype

/-! ## Operators restricted to the carrier -/

/-- Joint Target Bellman operator restricted to the carrier — only
needs Sender uniqueness on this specific `V_S`. Since round BJ4.3 the state-local
operator reads only its compliance-local part (`toOnI`). -/
noncomputable def jointTarget_BCF_on
    (V_T V_S : D.Carrier) : Val :=
  p.jointTarget_BCF_on_S V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property).toOnI

/-- The continuous leader selector at `(V_T, V_S)` in the carrier — the
state-clamped extension `α_on_ext` (globally continuous, argmax on `S`). -/
noncomputable def α_on (V_T V_S : D.Carrier) : ℝ → ℝ :=
  p.α_on_ext V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property).toOnI

theorem α_on_continuous (V_T V_S : D.Carrier) :
    Continuous (D.α_on V_T V_S) :=
  p.α_on_ext_continuous V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property).toOnI
    (D.target_unique_on V_T.val V_T.property V_S.val V_S.property)

theorem α_on_mem (V_T V_S : D.Carrier) (x : ℝ) :
    D.α_on V_T V_S x ∈ Sanctions.I :=
  p.α_on_ext_mem V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property).toOnI x

theorem α_on_isMaxOn (V_T V_S : D.Carrier)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn (fun a => p.joint_T_integrand V_T.val V_S.val x a)
      Sanctions.I (D.α_on V_T V_S x) :=
  p.α_on_ext_isMaxOn_of_mem V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property).toOnI hx

/-- Joint Sender Bellman operator restricted to the carrier — uses
the leader selector at `(V_T, V_S)`. -/
noncomputable def jointSender_BCF_on
    (V_T V_S : D.Carrier) : Val :=
  p.bellmanS_BCF (D.α_on V_T V_S) (D.α_on_continuous V_T V_S) V_S.val

/-! ## Invariance hypothesis -/

/-- **Carrier invariance.** Both joint Bellman operators send a
carrier-pair `(V_T, V_S)` back into the carrier. This is the
economically interpretable invariant: the Banach iteration starting
from a point in the carrier stays in the carrier. -/
def IsInvariant : Prop :=
  ∀ V_T V_S : D.Carrier,
    D.jointTarget_BCF_on V_T V_S ∈ D.carrier
    ∧ D.jointSender_BCF_on V_T V_S ∈ D.carrier

/-! ## Subtype-valued joint operators

Under `IsInvariant`, the joint operators become subtype-valued and
the standard joint MPE Banach machinery applies on the complete
metric subtype `↥carrier × ↥carrier`. -/

/-- Subtype-valued joint Target operator. -/
noncomputable def jointTargetOp_sub
    (h_inv : D.IsInvariant) (z : D.Carrier × D.Carrier) : D.Carrier :=
  ⟨D.jointTarget_BCF_on z.1 z.2, (h_inv z.1 z.2).1⟩

/-- Subtype-valued joint Sender operator. -/
noncomputable def jointSenderOp_sub
    (h_inv : D.IsInvariant) (z : D.Carrier × D.Carrier) : D.Carrier :=
  ⟨D.jointSender_BCF_on z.1 z.2, (h_inv z.1 z.2).2⟩

/-! ## Existence on the subtype via `joint_contraction_from_row_bounds`

`joint_contraction_from_row_bounds` is generic over any
`{E : Type*} [MetricSpace E] [CompleteSpace E] [Nonempty E]`, so it
applies directly with `E := D.Carrier`. The row-Lipschitz bounds are
expressed in the subtype metric (which equals the ambient `Val`
metric by `Subtype.dist_eq`). -/

/-- **Banach fixed point on the carrier subtype.** Under invariance
of the carrier and row-Lipschitz contraction bounds with
`β_T + L_TS < 1` and `β_S + L_ST < 1`, there exists a fixed point of
the joint subtype operator pair. -/
theorem exists_fixedPoint_in_carrier
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ V W V' W' : D.Carrier,
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ V W V' W' : D.Carrier,
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1)
    (hsuff_S : β_S + L_ST < 1) :
    ∃ z : D.Carrier × D.Carrier,
      (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z) = z := by
  exact Sanctions.AbstractGame.JointMPE.joint_contraction_from_row_bounds
    (T₁ := D.jointTargetOp_sub h_inv)
    (T₂ := D.jointSenderOp_sub h_inv)
    hβ_T_nn hL_TS_nn hL_ST_nn hβ_S_nn hT_T hT_S
    (max_lt hsuff_T (by linarith))

/-! ## Equilibrium existence packaging — moved (round BG1.2, 2026-10-06)

The three single-carrier existence wrappers that used to sit here
(`exists_feedbackStackelbergTop_from_valueClass_with_membership`,
`exists_feedbackStackelberg_from_valueClass` and
`exists_feedbackStackelbergTop_from_valueClass`) had no consumers and were
deleted. Their 60-line construction duplicated the asymmetric one verbatim.
Every `ValueClass` induces a `ValueClass2` (`ValueClass.toValueClass2`, with
invariance transported by `toValueClass2_IsInvariant`), and the single
construction `ValueClass2.exists_feedbackStackelbergTop_of_jointFixedPoint` in
`InvariantValueClass2.lean` turns a joint carrier fixed point into a
top-selector equilibrium. No hypothesis changed anywhere. -/

end ValueClass

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
