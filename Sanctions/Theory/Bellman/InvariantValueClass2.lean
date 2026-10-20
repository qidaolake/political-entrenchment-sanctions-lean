/-
Sanctions/Theory/Bellman/InvariantValueClass2.lean

**Audit-49 Item 1: asymmetric value class with separate
`carrier_T` and `carrier_S`.**

The audit-48 critique observed that the single-carrier `ValueClass`
architecture (in `InvariantValueClass.lean`) forces every membership
condition on BOTH `V_T` and `V_S`. The audit-46 P4 constructor
`regularEconomyCertificateComplianceCore_of_lipGainBall_auto`
illustrated the cost: the `valLipGainBall` carrier requires
`LowerSlopeOnValueOn V (Icc xT 1) gT` — Target-style high-state gain
— and the single-carrier architecture imposes this on `V_S` too,
which is economically awkward if `V_S` represents Sender national or
trade welfare.

The audit-49 critique (Step 2) proposed an asymmetric refactor:
separate `carrier_T : Set Val` and `carrier_S : Set Val`, with
separate closure / nonemptiness / uniqueness predicates, and a
heterogeneous Bellman invariance:

```
∀ V_T : carrier_T, ∀ V_S : carrier_S,
  jointTarget_BCF (V_T, V_S) ∈ carrier_T
  ∧ jointSender_BCF (V_T, V_S) ∈ carrier_S
```

This file provides:

* `ValueClass2 p` — the asymmetric structure.
* `ValueClass2.IsInvariant` — heterogeneous Bellman invariance.
* `ValueClass2.jointTargetOp_sub` / `jointSenderOp_sub` — the
  heterogeneous subtype-valued operators.
* `ValueClass2.exists_feedbackStackelbergTop_of_jointFixedPoint` — the
  single construction turning a joint carrier fixed point into a
  top-selector equilibrium with `E.V_T ∈ carrier_T`, `E.V_S ∈ carrier_S`
  and α-coincidence (round BG1.2, 2026-10-06).
* `ValueClass2.exists_fixedPoint_in_carrier_schur` — the Perov/Schur-margin
  fixed point on the carrier product (moved here from
  `Theory/Equilibrium/PerovExistence.lean`, round BG1.2), and its row-sum
  corollary `ValueClass2.exists_fixedPoint_in_carrier`.
* `ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership`
  — the row-sum existence theorem, now a two-line corollary of the two
  results above. (The heterogeneous Banach template
  `joint_contraction_from_row_bounds_hetero` it used to call was retired
  in round BG1.2.)
* `ValueClass.toValueClass2` — the **homogeneous bridge**:
  every existing single-carrier `ValueClass D` induces a
  `ValueClass2` with `carrier_T = carrier_S = D.carrier`. This
  ensures no existing theorem regresses.

**Compliance-local Sender uniqueness (round BJ4.3, 2026-10-08).** The field
`sender_unique_on` asks for `DynamicArgmaxUniqueOnI` (uniqueness of the Sender's
dynamic argmax at physical states and physical compliance levels `a ∈ [0,1]`),
no longer `DynamicArgmaxUnique` (every real `a`). The carrier operators read the
Sender's response only at compliance levels the Target can choose, so nothing
else changes. An existing `DynamicArgmaxUnique` discharger `h` supplies the
field as `fun V hV => (h V hV).toOnI`.

## Rule compliance

* **Rule 1.** Every strategy is equilibrium-derived: `V_T`, `V_S`
  are the Banach fixed point on the heterogeneous subtype product;
  `α` is the leader argmax via `targetArgmax`; no hand-chosen rule.
* **Rule 3.** New cat-(3) structure: the asymmetric carriers are a
  genuine generalization of `ValueClass`. The homogeneous bridge
  `ValueClass.toValueClass2` keeps the existing single-carrier
  results unchanged — `ValueClass2` strictly *generalizes* the
  assumption surface (every `ValueClass` is a `ValueClass2`).
  Pre-confirmed by user directive "Yes, do all the rule 3 deferred
  ones" (2026-05-28).
* **Rule 5.** Fully parametric over `(p, D : ValueClass2)`.
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Foundations.PerovContraction

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Asymmetric (heterogeneous) value class -/

/-- **Asymmetric value class.** Two closed nonempty carriers
`carrier_T, carrier_S ⊆ Val` with separate uniqueness predicates.
Equilibrium existence is via Banach contraction on the heterogeneous
product `↥carrier_T × ↥carrier_S` — a complete metric space because
each component is a closed subset of complete `Val`. -/
structure ValueClass2 where
  /-- Target-side carrier (the equilibrium `V_T` lives here). -/
  carrier_T : Set Val
  /-- Sender-side carrier (the equilibrium `V_S` lives here). -/
  carrier_S : Set Val
  /-- Target carrier closed (so the subtype inherits completeness). -/
  isClosed_T : IsClosed carrier_T
  /-- Sender carrier closed. -/
  isClosed_S : IsClosed carrier_S
  /-- Target carrier nonempty. -/
  nonempty_T : carrier_T.Nonempty
  /-- Sender carrier nonempty. -/
  nonempty_S : carrier_S.Nonempty
  /-- Sender argmax uniqueness on the Sender carrier, at physical states and
  physical compliance levels `a ∈ [0,1]` (round BJ4.3, 2026-10-08; formerly
  `DynamicArgmaxUnique`, uniqueness at every real compliance level). -/
  sender_unique_on : ∀ V_S ∈ carrier_S, p.DynamicArgmaxUniqueOnI V_S
  /-- Target argmax uniqueness for `(V_T, V_S)` pairs with `V_T` in
  the Target carrier and `V_S` in the Sender carrier. -/
  target_unique_on : ∀ V_T ∈ carrier_T, ∀ V_S ∈ carrier_S,
    p.TargetArgmaxUnique V_T V_S

namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-- The Target-side subtype. -/
abbrev CarrierT : Type := ↥D.carrier_T

/-- The Sender-side subtype. -/
abbrev CarrierS : Type := ↥D.carrier_S

instance instCompleteSpaceCarrierT : CompleteSpace D.CarrierT :=
  haveI : IsClosed D.carrier_T := D.isClosed_T
  inferInstance

instance instCompleteSpaceCarrierS : CompleteSpace D.CarrierS :=
  haveI : IsClosed D.carrier_S := D.isClosed_S
  inferInstance

instance instNonemptyCarrierT : Nonempty D.CarrierT :=
  D.nonempty_T.to_subtype

instance instNonemptyCarrierS : Nonempty D.CarrierS :=
  D.nonempty_S.to_subtype

/-! ## Heterogeneous operators restricted to the carriers -/

/-- Joint Target Bellman operator on `(V_T, V_S)` with `V_T ∈
carrier_T` and `V_S ∈ carrier_S`. -/
noncomputable def jointTarget_BCF_on
    (V_T : D.CarrierT) (V_S : D.CarrierS) : Val :=
  p.jointTarget_BCF_on_S V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property)

/-- Continuous leader selector at `(V_T, V_S)` — the state-clamped
extension `α_on_ext` (globally continuous, the derived argmax on `S`). -/
noncomputable def α_on (V_T : D.CarrierT) (V_S : D.CarrierS) : ℝ → ℝ :=
  p.α_on_ext V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property)

theorem α_on_continuous (V_T : D.CarrierT) (V_S : D.CarrierS) :
    Continuous (D.α_on V_T V_S) :=
  p.α_on_ext_continuous V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property)
    (D.target_unique_on V_T.val V_T.property V_S.val V_S.property)

theorem α_on_mem (V_T : D.CarrierT) (V_S : D.CarrierS) (x : ℝ) :
    D.α_on V_T V_S x ∈ Sanctions.I :=
  p.α_on_ext_mem V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property) x

theorem α_on_isMaxOn (V_T : D.CarrierT) (V_S : D.CarrierS)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn (fun a => p.joint_T_integrand V_T.val V_S.val x a)
      Sanctions.I (D.α_on V_T V_S x) :=
  p.α_on_ext_isMaxOn_of_mem V_T.val V_S.val
    (D.sender_unique_on V_S.val V_S.property) hx

/-- Joint Sender Bellman operator on `(V_T, V_S)`. -/
noncomputable def jointSender_BCF_on
    (V_T : D.CarrierT) (V_S : D.CarrierS) : Val :=
  p.bellmanS_BCF (D.α_on V_T V_S) (D.α_on_continuous V_T V_S) V_S.val

/-! ## Heterogeneous invariance hypothesis -/

/-- **Heterogeneous carrier invariance.** The joint Target operator
sends `carrier_T × carrier_S` into `carrier_T`; the joint Sender
operator sends it into `carrier_S`. -/
def IsInvariant : Prop :=
  ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
    D.jointTarget_BCF_on V_T V_S ∈ D.carrier_T
    ∧ D.jointSender_BCF_on V_T V_S ∈ D.carrier_S

/-! ## Heterogeneous subtype-valued joint operators -/

/-- Heterogeneous subtype-valued joint Target operator. -/
noncomputable def jointTargetOp_sub
    (h_inv : D.IsInvariant)
    (z : D.CarrierT × D.CarrierS) : D.CarrierT :=
  ⟨D.jointTarget_BCF_on z.1 z.2, (h_inv z.1 z.2).1⟩

/-- Heterogeneous subtype-valued joint Sender operator. -/
noncomputable def jointSenderOp_sub
    (h_inv : D.IsInvariant)
    (z : D.CarrierT × D.CarrierS) : D.CarrierS :=
  ⟨D.jointSender_BCF_on z.1 z.2, (h_inv z.1 z.2).2⟩

/-! ### Row bounds without the invariance witness

The two operator row bounds are the Banach inputs of every certificate in the
project, and each is stated on the *subtype-valued* operators — which cannot even
be written down without a proof of `IsInvariant` in hand.  That forces any
constructor deriving invariance from primitives to spell the derivation out
inside its own hypotheses.

The subtype metric is the ambient metric on the underlying values, so the bound
is the same statement either way.  Stating it on the BCF-valued operators frees
it from the invariance witness, so a row bound can be assumed before invariance
is established and transported afterwards. -/

/-- The Target row bound on the BCF-valued operator transports to the
subtype-valued one. -/
theorem jointTargetOp_sub_rowBound_of_BCF
    (h_inv : D.IsInvariant) {b l : ℝ}
    (h : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTarget_BCF_on V W) (D.jointTarget_BCF_on V' W')
        ≤ b * dist V V' + l * dist W W') :
    ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ b * dist V V' + l * dist W W' := h

/-- The Sender row bound on the BCF-valued operator transports to the
subtype-valued one. -/
theorem jointSenderOp_sub_rowBound_of_BCF
    (h_inv : D.IsInvariant) {b l : ℝ}
    (h : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSender_BCF_on V W) (D.jointSender_BCF_on V' W')
        ≤ l * dist V V' + b * dist W W') :
    ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ l * dist V V' + b * dist W W' := h

/-! ## Joint fixed point ⇒ top-selector equilibrium (round BG1.2, 2026-10-06)

The construction that turns a fixed point of the heterogeneous joint subtype
operator into a top-selector feedback Stackelberg equilibrium used to appear
three times: in the single-carrier `ValueClass` existence theorem, in the
row-sum `ValueClass2` existence theorem below, and in the Schur-margin
existence theorem of `Theory/Equilibrium/PerovExistence.lean`. The copies
differed only in the theorem that produced the fixed point. The construction
now lives once, in `exists_feedbackStackelbergTop_of_jointFixedPoint`, which
takes the fixed point as its only input; the row-sum and Schur existence
theorems are two-line corollaries. The heterogeneous Banach template
`JointMPE.joint_contraction_from_row_bounds_hetero` is retired: the row-sum
fixed point is now the Schur fixed point at the margin the row sums imply
(`Foundations.Perov.NNMat2.schurDet_of_rowSums`). -/

/-- **A joint carrier fixed point is a top-selector equilibrium (round BG1.2,
2026-10-06).** If the heterogeneous joint subtype operator has a fixed point
in `carrier_T × carrier_S`, then that value pair belongs to a top-selector
feedback Stackelberg equilibrium whose leader policy is the carrier selector
`α_on` at the pair (α-coincidence), with both values in their carriers.

Plain language: once the Target and Sender value functions are mutually
consistent, each being the Bellman value given the other, the Target's carrier
selector and the Sender's greatest dynamic best response form an equilibrium.
No contraction hypothesis appears here. How the fixed point is obtained (row
sums, the Perov–Schur margin, or any other route) is left to the caller, so
this one theorem carries the construction that three existence theorems used
to repeat verbatim. General in `F`: the transition enters only through the
Bellman operators of `p`. -/
theorem exists_feedbackStackelbergTop_of_jointFixedPoint
    (h_inv : D.IsInvariant)
    (hfix : ∃ z : D.CarrierT × D.CarrierS,
      (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z) = z) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ∃ hVT : E.V_T ∈ D.carrier_T,
      ∃ hVS : E.V_S ∈ D.carrier_S,
        E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ := by
  -- Design A: the ValueClass2 operators are the state-local ones
  -- (`jointTarget_BCF_on_S`, `α_on_ext`), so the fixed point `z` yields
  -- a TOP equilibrium DIRECTLY (its leader fields are `∀ x ∈ S`, which
  -- the state-local uniqueness supports). The ordinary equilibrium
  -- (`α_opt : ∀ x : ℝ`) is not constructible from state-local data.
  obtain ⟨z, hz⟩ := hfix
  have hz_T : (D.jointTargetOp_sub h_inv z).val = z.1.val := by
    have h := congrArg Prod.fst hz
    exact congrArg Subtype.val h
  have hz_S : (D.jointSenderOp_sub h_inv z).val = z.2.val := by
    have h := congrArg Prod.snd hz
    exact congrArg Subtype.val h
  refine ⟨{
    V_T := z.1.val
    V_S := z.2.val
    α := D.α_on z.1 z.2
    hα := D.α_on_continuous z.1 z.2
    α_mem := fun x _hx => D.α_on_mem z.1 z.2 x
    V_S_fix := by
      have h_def :
          (D.jointSenderOp_sub h_inv z).val =
            p.bellmanS_BCF (D.α_on z.1 z.2) (D.α_on_continuous z.1 z.2)
              z.2.val := rfl
      rw [h_def] at hz_S
      exact hz_S.symm
    V_T_fix_top := by
      intro x
      have h_def :
          (D.jointTargetOp_sub h_inv z).val =
            p.jointTarget_BCF_on_S z.1.val z.2.val
              (D.sender_unique_on z.2.val z.2.property) := rfl
      rw [h_def] at hz_T
      have h_apply :
          (p.jointTarget_BCF_on_S z.1.val z.2.val
            (D.sender_unique_on z.2.val z.2.property)) x =
            sSup ((fun a => p.joint_T_integrand z.1.val z.2.val x.val a) ''
                    Sanctions.I) :=
        p.jointTarget_BCF_on_S_apply z.1.val z.2.val
          (D.sender_unique_on z.2.val z.2.property) x
      -- On `S × I`, top integrand ≡ ordinary integrand (compliance-local
      -- uniqueness); the supremum reads the integrands only on `I`.
      have hint :
          (fun a => p.joint_T_top_integrand z.1.val z.2.val x.val a) ''
              Sanctions.I =
            (fun a => p.joint_T_integrand z.1.val z.2.val x.val a) ''
              Sanctions.I :=
        Set.image_congr fun _a ha =>
          p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
            (D.sender_unique_on z.2.val z.2.property) x.property ha
      rw [hint]
      calc z.1.val x
          = (p.jointTarget_BCF_on_S z.1.val z.2.val
              (D.sender_unique_on z.2.val z.2.property)) x := by rw [hz_T]
        _ = sSup ((fun a => p.joint_T_integrand z.1.val z.2.val x.val a) ''
                    Sanctions.I) := h_apply
    α_opt_top := by
      intro x hx a ha
      show p.joint_T_top_integrand z.1.val z.2.val x a ≤
          p.joint_T_top_integrand z.1.val z.2.val x (D.α_on z.1 z.2 x)
      rw [p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
            (D.sender_unique_on z.2.val z.2.property) hx ha,
          p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
            (D.sender_unique_on z.2.val z.2.property) hx (D.α_on_mem z.1 z.2 x)]
      exact D.α_on_isMaxOn z.1 z.2 hx ha
  }, z.1.property, z.2.property, rfl⟩

/-! ## Heterogeneous existence on the asymmetric carrier subtype -/

/-- **Schur-margin fixed point on the heterogeneous carrier subtype (Round
E1).** Under heterogeneous invariance, row-Lipschitz bounds with nonnegative
coefficients, the Sender diagonal bound `β_S < 1` and the Schur margin
`L_TS · L_ST < (1 − β_T)(1 − β_S)`, the joint subtype operator has a fixed
point in `carrier_T × carrier_S`. The engine is the Foundations Perov 2×2 fixed
point (`Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint`).

Moved here from `Theory/Equilibrium/PerovExistence.lean` under the same name on
2026-10-06 (round BG1.2), so that the row-sum existence theorem below can be
its corollary without an import cycle. In the same round (BG1.1) the Target
diagonal bound `β_T < 1` was dropped: the signs, `β_S < 1` and the Schur margin
imply it (`Foundations.Perov.lt_one_of_schur_margin`). Plain language: the
mutual Bellman consistency of the two value functions has a solution in the
carriers once the Sender row contracts and the cross feedback is smaller than
the two own-discount slacks. General in `F`. -/
theorem exists_fixedPoint_in_carrier_schur
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)) :
    ∃ z : D.CarrierT × D.CarrierS,
      (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z) = z := by
  haveI : CompleteSpace D.CarrierT := D.isClosed_T.completeSpace_coe
  haveI : CompleteSpace D.CarrierS := D.isClosed_S.completeSpace_coe
  haveI : Nonempty D.CarrierT := D.nonempty_T.to_subtype
  haveI : Nonempty D.CarrierS := D.nonempty_S.to_subtype
  obtain ⟨z, hz, _⟩ :=
    Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint
      (T := fun z : D.CarrierT × D.CarrierS =>
        (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z))
      hβ_T_nn hL_TS_nn hL_ST_nn hβ_S_nn
      (fun z z' => hT_T z.1 z'.1 z.2 z'.2)
      (fun z z' => hT_S z.1 z'.1 z.2 z'.2)
      hβ_S_lt hSchur
  exact ⟨z, hz⟩

/-- **Banach fixed point on the heterogeneous carrier subtype.**
Under heterogeneous invariance and row-Lipschitz contraction bounds
with `β_T + L_TS < 1` and `β_S + L_ST < 1`, there exists a fixed
point of the heterogeneous joint subtype operator pair.

Since 2026-10-06 (round BG1.2) this is a corollary of
`exists_fixedPoint_in_carrier_schur`: the two row sums give `β_S < 1` and the
Schur margin (`Foundations.Perov.NNMat2.schurDet_of_rowSums`). The statement
is unchanged; only the proof route moved off the retired heterogeneous Banach
template. General in `F`. -/
theorem exists_fixedPoint_in_carrier
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1)
    (hsuff_S : β_S + L_ST < 1) :
    ∃ z : D.CarrierT × D.CarrierS,
      (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z) = z :=
  D.exists_fixedPoint_in_carrier_schur h_inv hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn
    hT_T hT_S (by linarith)
    (Sanctions.Foundations.Perov.NNMat2.schurDet_of_rowSums
      ⟨β_T, L_TS, L_ST, β_S, hβ_T_nn, hL_TS_nn, hL_ST_nn, hβ_S_nn⟩
      hsuff_T (by linarith : L_ST + β_S < 1))

/-! **Ordinary-equilibrium existence — DEMOTED (Design A).**
The former `exists_feedbackStackelberg_from_valueClass2_with_membership`
built an *ordinary* `FeedbackStackelbergEquilibrium`, whose leader field
`α_opt : ∀ x : ℝ` is **not constructible** under state-local uniqueness:
off `S = [0,1]` the ValueClass2 leader policy is the state-clamped
`α_on_ext`, which is the argmax at the *clamped* state, not at `x`. The
canonical existence is now the TOP form
`exists_feedbackStackelbergTop_from_valueClass2_with_membership` below
(whose `α_opt_top : ∀ x ∈ S` is state-local and supported). An economy
with genuine *global* uniqueness can still obtain the ordinary object via
the global route (`exists_feedbackStackelberg_from_uniqueness_row_bounds`
in `TargetSelectorFromUnique`). -/

/-- **Top-selector existence from a heterogeneous value class.**
Under the row-sum contraction bounds, returns a top-selector feedback
Stackelberg equilibrium with both values in their carriers, together with
the α-coincidence at the produced equilibrium:
`E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩` — this lets downstream
theorems instantiate carrier-local primitives at the produced
equilibrium.

Since 2026-10-06 (round BG1.2) a two-line corollary: the row-sum fixed point
`exists_fixedPoint_in_carrier` fed to the single construction
`exists_feedbackStackelbergTop_of_jointFixedPoint`. Statement unchanged.
General in `F`. -/
theorem exists_feedbackStackelbergTop_from_valueClass2_with_membership
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1)
    (hsuff_S : β_S + L_ST < 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ∃ hVT : E.V_T ∈ D.carrier_T,
      ∃ hVS : E.V_S ∈ D.carrier_S,
        E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ :=
  D.exists_feedbackStackelbergTop_of_jointFixedPoint h_inv
    (D.exists_fixedPoint_in_carrier h_inv hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn
      hT_T hT_S hsuff_T hsuff_S)

end ValueClass2

/-! ## Homogeneous bridge: every `ValueClass` is a `ValueClass2`.

This ensures all existing single-carrier results carry over: any
existing `D : p.ValueClass` induces a `D.toValueClass2 : p.ValueClass2`
with `carrier_T = carrier_S = D.carrier`. -/

namespace ValueClass

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass)

/-- **Homogeneous bridge.** Every single-carrier `ValueClass`
induces an asymmetric `ValueClass2` with both carriers equal to the
original carrier. Ensures no regression: every existing single-
carrier theorem composes with `toValueClass2` to give a
`ValueClass2`-version. Since round BJ4.3 the Sender field keeps only the
compliance-local part of the carrier's uniqueness (`toOnI`). -/
@[simps]
def toValueClass2 : p.ValueClass2 where
  carrier_T := D.carrier
  carrier_S := D.carrier
  isClosed_T := D.isClosed
  isClosed_S := D.isClosed
  nonempty_T := D.nonempty
  nonempty_S := D.nonempty
  sender_unique_on := fun V_S hV_S => (D.sender_unique_on V_S hV_S).toOnI
  target_unique_on := D.target_unique_on

/-- The homogeneous bridge preserves invariance. -/
theorem toValueClass2_IsInvariant
    (h_inv : D.IsInvariant) :
    D.toValueClass2.IsInvariant := by
  intro V_T V_S
  -- D.toValueClass2.CarrierT = D.CarrierS = ↥D.carrier
  refine ⟨?_, ?_⟩
  · -- jointTarget_BCF_on V_T V_S ∈ D.carrier
    exact (h_inv ⟨V_T.val, V_T.property⟩ ⟨V_S.val, V_S.property⟩).1
  · -- jointSender_BCF_on V_T V_S ∈ D.carrier
    -- Need to unfold α_on through both ValueClass and ValueClass2
    have h := (h_inv ⟨V_T.val, V_T.property⟩ ⟨V_S.val, V_S.property⟩).2
    -- The ValueClass.jointSender_BCF_on uses ValueClass.α_on;
    -- ValueClass2.jointSender_BCF_on uses ValueClass2.α_on.
    -- They're equal because both reduce to p.α_on_ext with a proof of the
    -- same compliance-local uniqueness (`(D.sender_unique_on _ _).toOnI` on
    -- both sides), and proofs of one proposition are definitionally equal.
    exact h

end ValueClass

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
