/-
Sanctions/Theory/Certificates/StandardComplianceLocal.lean

**Audit-49 Item 2: carrier-local (asymmetric) compliance certificate.**

The audit-49 critique (Step 3) observed that the existing
`RegularEconomyCertificateComplianceCore` quantifies its stage-bound
fields over **every** `E : FeedbackStackelbergEquilibriumTop`:

```
h_stage_target_loss_α :
  ∀ E : p.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Icc xT 1, …
```

This is wider than the proof needs. The proof only uses these
conditions for the **produced fixed-point equilibrium**. With the
audit-49 Item 1 asymmetric `ValueClass2` in place, we can localize:

```
h_stage_target_loss_on :
  ∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS, ∀ x ∈ Icc xT 1, …
```

(quantifying over carrier members rather than over every top
equilibrium). Since the produced fixed-point equilibrium has
`E.V_T ∈ D.carrier_T` and `E.V_S ∈ D.carrier_S` by construction, the
carrier-local form suffices. (Round BJ1.4, 2026-10-07, later deleted the Target
stage-loss field from `StandardComplianceLocalCoreCertificate` altogether; its
carrier-local form survives as an input of
`Target_combined_chord_of_decomposition_lowerChord`.)

The carrier-local form is more localized to the constructed value
class and avoids assumptions on equilibria outside the construction.
It is weaker in the intended *modeling* sense when the carrier is
chosen to reflect the regular class used for the fixed-point
argument — the certificate's primitives need only hold on the
specific value-class pairs the construction touches, not on every
possible top equilibrium of the model. It is **not** a purely formal
logical weakening: the per-E form quantifies over equilibria, while
the carrier-local form quantifies over carrier pairs, and these are
not directly nested as quantifiers (the carrier-local form may
require the primitive on carrier pairs that are not equilibria).

This file provides:

* `StandardComplianceLocalCoreCertificate p` — the **start-free**
  asymmetric carrier-local standard-compliance certificate, built on
  `ValueClass2`. Consumed by the **preferred** universal-start
  theorems.
* `StandardComplianceLocalCertificate p` — **fixed-start extension**
  of the core certificate, adding stored `x₀` / `x₀shock` for
  compatibility theorems.
* `three_goals_local_uniform_starts` — **preferred** universal-start
  three-goals theorem; consumes the core certificate; quantifies
  Goal 1 over every basin start `x₀ ∈ B` and Goal 3 over every shock
  initial state `x₀shock ∈ [0, 1]`.
* `three_goals_local_regime_comparison_uniform_starts` — **opt-in
  conditional** pathwise regime-comparison theorem (demoted from
  "preferred" 2026-07-03); consumes the core certificate plus the
  opt-in `hMyoBasin` hypothesis (myopic equilibrium rule preserves
  the basin); returns statewise + pathwise dynamic-over-myopic regime
  dominance from every basin start. `hMyoBasin` describes a
  both-regimes-lock-in region and is FALSE at the bistable witnesses
  (`eeCert_hMyoBasin_counterexample`) — there, use the statewise
  Goal 2 of `three_goals_local_uniform_starts`, or the ceiling/floor
  pathwise route `ruleSanctions_le_of_ceiling_and_path_floor`
  (instantiated at the witness by `eeCert_pathwise_dominance`).
* `three_goals_local` — fixed-start compatibility theorem; consumes
  the fixed-start extension `StandardComplianceLocalCertificate` and
  proves the three goals at the certificate's stored `C.x₀` /
  `C.x₀shock`.
* `three_goals_local_regime_comparison` — fixed-start compatibility
  regime-comparison theorem; same fixed-start consumption pattern.

## Rule compliance

* **Rule 1.** No strategy changes — the produced equilibrium's `α`
  is the leader argmax via `targetArgmax` (same as in
  `RegularEconomyCertificateComplianceCore`).
* **Rule 3.** Cat-(2)-style localization: replaces the per-E `∀ E`
  quantifier with the carrier-local `∀ V_T : CarrierT, ∀ V_S :
  CarrierS` quantifier. This is more localized to the constructed
  value class (the primitives need only hold on the carrier pairs
  the construction touches), but it is not a purely formal logical
  weakening — the two forms quantify over different families
  (equilibria vs carrier pairs). Pre-confirmed by user directive
  "Yes, do all the rule 3 deferred ones".
* **Rule 5.** Fully parametric over
  `(p, C : StandardComplianceLocalCoreCertificate)` for the preferred
  universal-start theorems; fixed-start compatibility theorems are
  parametric over `(p, C : StandardComplianceLocalCertificate)`.

**Round BJ5.1 (2026-10-07).** The MS certificate's myopic ceiling
`hMyoCeiling` is stated against `p.myopicFeedbackEquilibrium_canonical`, which
is built from the static selector's continuity. That condition, the joint
continuity of the static Sender selector `σ`, was the `Params` field
`σ_continuous`; it is now the class `Params.StaticSelectorContinuous`. The
certificate `StandardComplianceLocalCoreCertificate_MS` therefore takes
`[p.StaticSelectorContinuous]` as a structure parameter, and so does every
theorem about it. Its fields are unchanged; the condition moved from the
economy to the binder. General in `F`.
-/

import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Basin.RelevantActionRegion
import Sanctions.Theory.Certificates.StandardComplianceBridges
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Foundations.IntervalDominanceOrder
import Sanctions.Foundations.TransitionChords

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Carrier-local (asymmetric) compliance certificate

The audit-49 Item 2 / Step 3 cert. Differences vs.
`RegularEconomyCertificateComplianceCore`:

* `D : ValueClass2` (asymmetric — separate `carrier_T`, `carrier_S`).
* Row-contraction bounds and `IsInvariant` use the **heterogeneous**
  subtype-valued operators.
* All stage-bound / Sender-Lipschitz / single-crossing / V_T-gain
  fields are **carrier-local** — they quantify over `D.CarrierT`
  and `D.CarrierS` rather than over every
  `FeedbackStackelbergEquilibriumTop`.
* The myopic comparator + ceiling fields are unchanged (they live
  outside the value-class machinery).
-/

/-- **Audit-49 Item 2: carrier-local asymmetric compliance certificate.**

Parallel to `RegularEconomyCertificateComplianceCore` but built on
the asymmetric `ValueClass2` and with carrier-local stage-bound
primitives.

**Rule 9 — generality witnessed (2026-08-21).** The transition fields `d` and
`hF_chord` make this certificate general in `F`: nothing here requires
`p.F = affineF p.δ`, and all three goals are proved over the general-`F`
trajectory objects. That generality is *inhabited outside the affine case*,
which Rule 9B requires: `Sanctions.Examples.qbCertificate` builds it at
`quadBumpF`, a transition `quadBumpF_ne_affineF` refutes as affine at **every**
weight. Headline row 36 reads the three goals off it at full conclusion
strength.

The other five instances remain affine, and that is fine: affine is an
admissible instance (Rule 22), not the model.

**Round BJ1.4 (2026-10-07, author-approved; checklist 11).** The Target
loss-offset stack is deleted: `dlo`, `hchord_lo`, `cT`, `gT`, `hgT_nn`,
`hT_loss_margin`, `h_stage_target_loss_on`, `hV_T_gain_on_carrier`, and the
sanction-floor sign `hsbar_pos`. Since round BH1.5 no certificate theorem read
them: they fed only the Target combined chord (P4), which built the
Target-preference conjunct of the joint basin that every caller discarded, and
`hsbar_pos` fed only a positivity conjunct the affine shock routes discarded.
The certificate now asks for the Sender side (P1–P3, P5 in its stage-slope and
margin form) and the existence data, nothing about how the Target ranks sanction
levels. The one theorem that still certifies the Target-preference field,
`exists_equilibrium_basinTop_generalF`, takes the Target combined chord as an
explicit hypothesis instead. -/
structure StandardComplianceLocalCoreCertificate where
  D : p.ValueClass2
  h_inv : D.IsInvariant
  /-- Row contraction (heterogeneous). -/
  β_T : ℝ
  β_S : ℝ
  L_TS : ℝ
  L_ST : ℝ
  hβ_T_nn : 0 ≤ β_T
  hβ_S_nn : 0 ≤ β_S
  hL_TS_nn : 0 ≤ L_TS
  hL_ST_nn : 0 ≤ L_ST
  hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ β_T * dist V V' + L_TS * dist W W'
  hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ L_ST * dist V V' + β_S * dist W W'
  hsuff_T : β_T + L_TS < 1
  hsuff_S : β_S + L_ST < 1
  /-- High-basin geometry. -/
  xT : ℝ
  xS : ℝ
  sbar : ℝ
  mS : ℝ
  KS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  hsbar_mem : sbar ∈ Sanctions.I
  /-- **Transition entry point, Sender leg (Rule 22).** The rate of a
  range-restricted sanction *upper* chord on `F`. At the affine law this is
  `δ`; in general it is any rate the transition actually satisfies. -/
  d : ℝ
  /-- On the basin's sub-pivot sanction range, the state responds to a sanction
  increase by at most `d · Δ`. -/
  hF_chord :
    ∀ x ∈ Set.Icc xS (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ ≤ s₂ →
          |p.F x s₂ - p.F x s₁| ≤ d * (s₂ - s₁)
  hS_margin : p.β_S * KS * d < mS
  /-- Consumed only by the Goal-3 shock theorem. -/
  hjoint_lt : max xT xS < 1
  /-- **Carrier-local Sender Lipschitz.** Every `V_S` in the Sender
  carrier is `KS`-Lipschitz. -/
  hV_S_lip_carrier :
    ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS
  /-- **Carrier-local stage Sender slope.** For any `(V_T, V_S)` in
  the carriers and any `x ∈ [xS, 1]`, the stage Sender payoff
  evaluated at the leader selector `D.α_on V_T V_S` has minimum
  upward slope `mS` on `[0, max x sbar]`. -/
  h_stage_sender_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS
  /-- **Carrier-local interval dominance (B1).** For any `(V_T, V_S)`
  in the carriers, the Sender dynamic objective at `D.α_on V_T V_S`
  satisfies the Quah–Strulovici (2007) interval-dominance-order family
  condition on `[max xT xS, 1]`. This is strictly weaker than
  Milgrom-Shannon single crossing: every SCP discharge upcasts for
  free via `IDOFamilyOn.of_singleCrossingOn`. -/
  hIDO_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
  /-- Independent myopic comparator. -/
  M : p.MyopicFeedbackEquilibrium
  /-- Myopic ceiling on the basin. -/
  hMyoCeiling :
    ∀ x ∈ Set.Icc (max xT xS) 1,
      p.σ x (M.α x) ≤ max x sbar

/-- **`0 ≤ KS` is derived, not assumed.**

`KS` bounds how fast the Sender's continuation value can move as the political
state moves. A Lipschitz modulus is nonnegative by construction, and this
certificate already carries everything needed to see it: the Sender carrier is
inhabited (`D.nonempty_S`) and every value function in it is `KS`-Lipschitz
(`hV_S_lip_carrier`), so `ValueLipschitzWith.nonneg` — which instantiates the
Lipschitz bound at the state-space endpoints `0` and `1`, whose distance is
exactly `1`, and closes by `abs_nonneg` — finishes it.

Removing the field is a Rule-3 *reduction*, so it needs no authorization. It
touches no transition, so Rule 22 generality is untouched.

**Not every sibling can do this.** `StandardComplianceLocalCertificateC1` and
`RegularEconomyCertificateC1ComplianceCore` keep their `hKS_nonneg` fields: the
first quantifies its Lipschitz condition over a `C1BellmanSystem` carrier with
no nonemptiness field, the second over *equilibria* whose existence the
structure never asserts. Both companions may be vacuous, so no sign follows.
See `docs/NONNEGATIVITY-SWEEP-EXEMPTIONS.md`. -/
theorem StandardComplianceLocalCoreCertificate.hKS_nonneg
    {q : Sanctions.AbstractGame.Params}
    (C : q.StandardComplianceLocalCoreCertificate) : 0 ≤ C.KS := by
  obtain ⟨V, hV⟩ := C.D.nonempty_S
  exact (C.hV_S_lip_carrier V hV).nonneg

namespace StandardComplianceLocalCoreCertificate

/-! ### Recovering the affine-denominated margin

The certificate's Sender margin is denominated in the chord rate `d` rather
than in `δ`. At an affine economy the δ-denominated form is not lost — it is
**derived**, because the chord field pins `δ ≤ d`: `hF_chord` says
`|F(x,s₂) − F(x,s₁)| ≤ d·Δ`, which at `F = affineF δ` reads `δ·Δ ≤ d·Δ`. (Until
round BJ1.4 the certificate also carried a Target lower chord at rate `dlo`,
which pinned `dlo ≤ δ`; that field is gone with the rest of the Target
loss-offset stack.) -/


end StandardComplianceLocalCoreCertificate

/-- **Fixed-start extension of the core certificate.** Adds the stored
starting states `x₀` / `x₀shock` consumed by the fixed-start theorems
(`three_goals_local`, `three_goals_local_regime_comparison`,
`three_goals_local_weak_persistence`). The universal-start theorems
consume the start-free `StandardComplianceLocalCoreCertificate`
directly, so proving the uniform results does not require supplying
arbitrary stored starts. -/
structure StandardComplianceLocalCertificate extends
    StandardComplianceLocalCoreCertificate p where
  /-- Starting state. -/
  x₀ : ℝ
  hx₀ : x₀ ∈ Set.Icc (max xT xS) 1
  x₀shock : ℝ
  hx₀shock_nn : 0 ≤ x₀shock
  hx₀shock_le : x₀shock ≤ 1

/-! ## Round 45 — Combined chord canonical form for `\Cref{ass:target_pref}`

User-approved reformulation (2026-06-05): under the user's
non-monotone-payoff story (sanctions Laffer curve for the Target;
political-state Laffer curve at extreme rally), neither `c_T` (as a
strict lower bound on `−∂U_T/∂s`) nor `g_U` (as a strict lower bound
on `∂U_T/∂x`) can globally bind. The substantive economic content of
`\Cref{ass:target_pref}` is the **loss-offset margin**: the Target's
**joint dynamic payoff** (stage + discounted continuation) is
non-decreasing in `s` on the basin's high-sanction chord domain.
This is logically equivalent to the prior `(c_T, g_T, c_T ≤ β_T · g_T
· δ)` decomposition (when V_T is monotone non-decreasing on basin)
but does not introduce stage-only and continuation-only rate
constants, and is robust to non-monotone stage payoffs and
non-monotone value functions on the basin.

The Round 45 paper-facing canonical form is the **combined chord
inequality**:

```
U_T(x, α(x), s_1) + β_T · V_T(F(x, s_1))
  ≤ U_T(x, α(x), s_2) + β_T · V_T(F(x, s_2))
```

for every carrier pair `(V_T, V_S)`, every basin `x ∈ [x̄_T, 1]`,
every `s_1 ≤ s_2 ∈ [max(x, s̄), 1]`. The named scalars `c_T, g_U,
g_T` and the margin Prop `c_T ≤ β_T · g_T · δ` disappear from the
user-facing paper surface.

## Lean status

Until round BJ1.4 (2026-10-07) `StandardComplianceLocalCoreCertificate`
retained the `(c_T, g_T, hT_loss_margin, h_stage_target_loss_on,
hV_T_gain_on_carrier)` decomposition as **internal fields**. Round BJ1.4
deleted them: no certificate theorem read them once the goals were routed
through the Sender persistence basin (round BH1.5). The decomposition survives
as the standalone discharger `Target_combined_chord_of_decomposition_lowerChord`
(`GeneralFDischargers.lean`), which turns it into the combined chord below.
Round 45 provides:

1. The new `TargetCombinedChordOn` predicate codifying the canonical
   paper-facing form.
2. A backward-compatibility lemma showing the existing decomposition
   is a **sufficient encoding** of the combined chord
   (the affine combined-chord discharger, retired 2026-08-21 in favour of
   `Target_combined_chord_of_decomposition_lowerChord`).

Full elimination of `(c_T, g_T)` from the certificate structure
requires re-deriving the persistence proposition from the combined
chord directly — a substantial refactor of the joint-Bellman /
Target-monotone-step machinery. This is **deferred** beyond R45; the
paper-side win (canonical assumption surface no longer names `c_T`,
`g_U`) is the R45 deliverable. -/

/-- **R45 Target combined chord predicate.** Canonical paper-facing
    form of `\Cref{ass:target_pref}`: the Target's joint dynamic
    payoff (stage `U_T(x, α(x), s)` plus discounted continuation
    `β_T · V_T(F(x, s))`) is non-decreasing in `s` on the basin's
    high-sanction chord domain `[max(x, sbar), 1]` for every basin
    state `x ∈ [xT, 1]` and every carrier pair `(V_T, V_S)`.

    Captures the dynamic loss-offset content without naming a
    stage-only loss rate `c_T` or a continuation-only gain rate
    `g_T`. Both the canonical political-economy story (stage
    hurts, continuation gains under monotone `V_T`) and the
    non-monotone Laffer-curve story (rally at extreme sanction or
    extreme political state) are accommodated, as long as the
    joint dynamic preference favors higher sanctions on the basin's
    high-sanction chord. -/
def TargetCombinedChordOn
    (D : p.ValueClass2)
    (xT sbar : ℝ) : Prop :=
  ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
    ∀ x ∈ Set.Icc xT (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (max x sbar) (1 : ℝ),
      ∀ s₂ ∈ Set.Icc (max x sbar) (1 : ℝ),
      s₁ ≤ s₂ →
        p.U_T x (D.α_on V_T V_S x) s₁
            + p.β_T * V_T.val
                (Sanctions.clipS' (p.F x s₁))
          ≤ p.U_T x (D.α_on V_T V_S x) s₂
            + p.β_T * V_T.val
                (Sanctions.clipS' (p.F x s₂))

/-- **R45 follow-up: carrier-local-to-per-equilibrium bridge for the
    combined chord.**

    From the carrier-local `TargetCombinedChordOn` predicate and an
    equilibrium `E` whose value-function pair `(E.V_T, E.V_S)` lies in
    the carrier `D.carrier_T × D.carrier_S` with the α-coincidence
    `E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩` (both supplied by
    `exists_feedbackStackelbergTop_from_valueClass2_with_membership`),
    derive the per-equilibrium combined chord on the joint Target
    dynamic objective at `E.α`.

    The per-equilibrium chord is the input shape of the alternative
    persistence theorem
    `persistence_at_equilibriumTop_from_target_combined_chord_on`
    in `Theory/Certificates/StandardComplianceBridges.lean`. This bridge
    is the connecting tissue: certificate-level carrier-local
    primitive ⇒ per-equilibrium chord ⇒ persistence conclusions,
    bypassing the (c_T, g_T) decomposition entirely. -/
theorem TargetCombinedChordOn.at_equilibrium
    {D : p.ValueClass2} {xT sbar : ℝ}
    (h_combined : p.TargetCombinedChordOn D xT sbar)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S)
    (hα_eq : E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) :
    ∀ x ∈ Set.Icc xT (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (max x sbar) (1 : ℝ),
      ∀ s₂ ∈ Set.Icc (max x sbar) (1 : ℝ),
      s₁ ≤ s₂ →
        p.U_T x (E.α x) s₁
            + p.β_T * E.V_T
                (Sanctions.clipS' (p.F x s₁))
          ≤ p.U_T x (E.α x) s₂
            + p.β_T * E.V_T
                (Sanctions.clipS' (p.F x s₂)) := by
  intro x hx s₁ hs₁ s₂ hs₂ hs_le
  have h_chord :=
    h_combined ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ x hx s₁ hs₁ s₂ hs₂ hs_le
  -- Rewrite D.α_on at the equilibrium carrier pair back to E.α.
  rw [hα_eq]
  exact h_chord

/-! ## Round 1.11 — Slim Milgrom-Shannon-form core certificate

User-approved assumption-surface reduction following the Round-1.10
hands-on audit. The legacy `StandardComplianceLocalCoreCertificate`
above carried ~32 fields, of which ~15 were dischargeable via
existing infrastructure (it was ~34/~17 until 2026-08-17, when the
two Target sign fields `hcT_nn` / `hgT_nn` were deleted outright as
consumed by nothing; round BJ1.4, 2026-10-07, then deleted the
decomposition stack and `hsbar_pos` from it as well):
* the wedge stack `(mS, KS, hKS_nonneg, hS_margin, hV_S_lip_carrier,
  h_stage_sender_on)` discharged by the Round-1.9 MS-form bridge;
* the decomposition stack `(cT, gT, hT_loss_margin,
  h_stage_target_loss_on, hV_T_gain_on_carrier)` discharged by the
  R45 combined-chord form;
* the `sbar`-pivot bundle `(sbar, hsbar_mem, hsbar_pos)` collapsed
  to `max(xT, xS)` per R43;
* `M : MyopicFeedbackEquilibrium` constructible via
  `p.myopicFeedbackEquilibrium_canonical` (Berge's Maximum Theorem,
  R11 Priority 2).

This slim certificate consumes only the truly-primitive surface:
existence inputs + basin pivots + MS-form A1 hypotheses + R45
combined chord + canonical myopic ceiling.

## Rule compliance
* **Rule 1** ✓ no strategies; the slim form uses the same
  equilibrium-derived α_on selector.
* **Rule 3** ✓ no new structural primitives.
* **Rule 5** ✓ parametric.
* **Rule 11** ✓ no witness construction.
* **Rule 19** ✓ all dischargers route through `Sanctions/Foundations/`.
-/

/-- **Round 1.11 — slim MS-form core certificate.** Strictly slimmer
companion of `StandardComplianceLocalCoreCertificate` consuming only
irreducible primitives plus Milgrom-Shannon-form A1 and R45
combined-chord A2. The wedge / decomposition / `sbar` / `M` field
stacks of the legacy form are all dischargeable via existing
infrastructure. General in `F`. Since round BJ5.1 (2026-10-07) it takes
`[p.StaticSelectorContinuous]` (joint continuity of the static Sender selector,
formerly a `Params` field) because its myopic ceiling `hMyoCeiling` is stated
against the canonical myopic equilibrium; the fields are unchanged. -/
structure StandardComplianceLocalCoreCertificate_MS [p.StaticSelectorContinuous] where
  /-- Asymmetric value class (carrier choice). -/
  D : p.ValueClass2
  h_inv : D.IsInvariant
  /-- Row-sum contraction inputs (truly primitive at this layer).
  Note: `hsuff_T` / `hsuff_S` below are the legacy row sums
  `β + L < 1` — strictly STRONGER than the Schur margin
  `L_TS·L_ST < (1−β_T)(1−β_S)`. The Round-A2 Schur weakening *has* been
  ported to the MS/general-`F` route (2026-07-24):
  `StandardComplianceLocalCoreCertificateSchur_MS`
  (`StandardComplianceSchur.lean`) is this certificate with the row sums
  replaced by diagonal bounds `β_T, β_S < 1` and the Schur margin, with its
  own `three_goals_local_MS_generalF` (the same conclusion as this
  certificate's) and the bridge `ofRowSum_MS`. Round BB (2026-09-28) adds the
  Schur forms of row 2 and of the Goals-1–2 core
  (`Certificates/StandardComplianceLocalised.lean`).
  The row sums imply the Schur package, so this certificate gets
  `unique_in_carrier` via that implication. -/
  β_T : ℝ
  β_S : ℝ
  L_TS : ℝ
  L_ST : ℝ
  hβ_T_nn : 0 ≤ β_T
  hβ_S_nn : 0 ≤ β_S
  hL_TS_nn : 0 ≤ L_TS
  hL_ST_nn : 0 ≤ L_ST
  hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ β_T * dist V V' + L_TS * dist W W'
  hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ L_ST * dist V V' + β_S * dist W W'
  hsuff_T : β_T + L_TS < 1
  hsuff_S : β_S + L_ST < 1
  /-- High-basin pivots (truly primitive). -/
  xT : ℝ
  xS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  /-- Joint pivot strict interior: `max(xT, xS) ∈ (0, 1)`. -/
  hpivot_mem : max xT xS ∈ Set.Ioo (0 : ℝ) 1
  /-- **A1 MS-form: low-range strict monotonicity of stage Sender
  payoff.** Universal over the carrier. -/
  h_stage_sender_strictMono :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x (max xT xS)))
  /-- **A1 IDO-form: high-range interval dominance of dynamic Sender
  objective.** Universal over the carrier. The Quah–Strulovici (2007)
  interval-dominance-order family condition — strictly weaker than
  Milgrom-Shannon single crossing; every SCP discharge upcasts via
  `IDOFamilyOn.of_singleCrossingOn`. -/
  hIDO_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
  /-- **A2 combined-chord (R45 form, universal-over-carrier).** -/
  h_target_combined : p.TargetCombinedChordOn D xT (max xT xS)
  /-- **Carrier-local Sender monotonicity.** Required by the
  R1.9 MS-form persistence bridge. -/
  hV_S_mono_carrier :
    ∀ V_S ∈ D.carrier_S, Monotone V_S
  /-- **Myopic ceiling against the canonical myopic equilibrium.**
  Defaulted to `myopicFeedbackEquilibrium_canonical`. -/
  hMyoCeiling :
    ∀ x ∈ Set.Icc (max xT xS) 1,
      p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max xT xS)

namespace StandardComplianceLocalCertificate


end StandardComplianceLocalCertificate

/-! ## Core-namespace names for the universal-start theorems

The affine universal-start theorems consume `StandardComplianceLocalCoreCertificate`.
Since round BH1.7 (2026-10-06) the core-namespace names
`StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts` and
`…three_goals_local_regime_comparison_uniform_starts` carry the proofs (each an
instance of its general-`F` sibling in `GeneralFDischargers.lean`), and the
historical `StandardComplianceLocalCertificate` names are one-line aliases of
them. Both live in `Examples/AffineInstance/ComplianceTower.lean`, so callers
can write `C.three_goals_local_uniform_starts` when
`C : StandardComplianceLocalCoreCertificate`. -/

namespace StandardComplianceLocalCoreCertificate


end StandardComplianceLocalCoreCertificate

/-! ## Round 1.11 — Headline theorem for the slim MS-form certificate

Headline `standardCompliance_three_goals_local_MS` consumes the slim
`StandardComplianceLocalCoreCertificate_MS` plus a starting state
`x₀shock`, and produces the same three-goals conclusion as
`standardCompliance_three_goals_local_uniform_starts` —
universal-over-starting-state form of Goals 1, 2, 3.

The proof routes through:
* `exists_feedbackStackelbergTop_from_valueClass2_with_membership`
  (existence — same as legacy);
* `persistence_at_equilibriumTop_from_target_combined_chord_MS_form`
  (Goal 1, R1.9);
* `OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord`
  + `dynamicTopRealizedRule_mono_of_singleCrossingOn`
  + `JointPreferenceBasinTop.of_oneSidedThresholds`
  + `level_dyn_top` + `ruleDom_of_dynamic_floor_and_myopic_ceiling`
  (Goal 2);
* `shock_at_equilibriumTop_from_target_combined_chord_MS_form`
  (Goal 3, R1.11). -/

namespace StandardComplianceLocalCoreCertificate_MS

/-- **Round 1.11 — slim headline (universal-start form).**

Headline theorem consuming the slim MS-form core certificate. The
conclusion is the same universal-over-starting-state three-goals
form as `standardCompliance_three_goals_local_uniform_starts`, but
the hypothesis surface drops the legacy wedge / decomposition /
`sbar` / `M` field stacks. -/
theorem three_goals_local_MS [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) := by
  -- Step 1: produce equilibrium via existence from the row-sum contraction margins.
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  -- Step 2: lift MS-form primitives at the equilibrium.
  have hV_S_mono : Monotone E.V_S := C.hV_S_mono_carrier E.V_S hVS
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x (max C.xT C.xS))) := by
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_strictMono V_T_sub V_S_sub x hx
  have h_target_combined :=
    TargetCombinedChordOn.at_equilibrium p C.h_target_combined E hVT hVS hα_eq
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  -- Step 3: Goal 1 via the R1.9 MS-form persistence bridge,
  -- universally over starting states.
  have hGoal1 : ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
              ∈ Set.Icc (max C.xT C.xS) 1) ∧
      (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) := by
    intro x₀ hx₀
    have h_ms := p.persistence_at_equilibriumTop_from_target_combined_chord_MS_form
      E C.hxT_mem C.hxS_mem
      ⟨le_of_lt C.hpivot_mem.1, le_of_lt C.hpivot_mem.2⟩
      hV_S_mono h_stage_sender h_target_combined hIDO hx₀
    exact ⟨h_ms.1, h_ms.2.2.1, h_ms.2.2.2.1⟩
  -- Step 4: Goal 2 via floor + myopic ceiling.
  have hFloor : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      max x (max C.xT C.xS) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
    have hOne : p.OneSidedSanctionPreferenceThresholds
                  E.V_T E.V_S E.α C.xT C.xS (max C.xT C.xS) :=
      OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
        p hV_S_mono C.hxT_mem C.hxS_mem
        ⟨le_of_lt C.hpivot_mem.1, le_of_lt C.hpivot_mem.2⟩
        h_stage_sender h_target_combined
    have hTopMono :
        MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
          (Set.Icc (max C.xT C.xS) 1) :=
      p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
    have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := by
      intro x hx
      apply E.α_mem
      refine ⟨?_, hx.2⟩
      exact le_trans (le_max_of_le_left C.hxT_mem.1) hx.1
    have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
          Sanctions.I (E.α x) := by
      intro x hx
      apply E.α_opt_top
      refine ⟨?_, hx.2⟩
      exact le_trans (le_max_of_le_left C.hxT_mem.1) hx.1
    have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
    exact JointPreferenceBasinTop.level_dyn_top p hB
  have hGoal2 :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  -- Step 5: Goal 3 via the R1.11 MS-form shock bridge.
  have hGoal3 : ∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
      ∃ N : ℕ,
        (∀ n, p.dynamicTopLockInPath E.V_S E.α
                (p.shockPath x₀shock N) n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
        (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                (p.shockPath x₀shock N) n) := by
    intro x₀shock h_nn h_le
    have h_shock := p.shock_at_equilibriumTop_from_target_combined_chord_MS_form
      E C.hxT_mem C.hxS_mem
      ⟨le_of_lt C.hpivot_mem.1, le_of_lt C.hpivot_mem.2⟩
      C.hpivot_mem.1 C.hpivot_mem.2
      hV_S_mono h_stage_sender h_target_combined hIDO h_nn h_le
    obtain ⟨N, h1, _h2, h3, _, _, _⟩ := h_shock
    exact ⟨N, h1, h3⟩
  exact ⟨E, hVT, hVS, hGoal1, hGoal2, hGoal3⟩

/-- **General-`F` trajectory three goals (Option B, R-2026-06-22).**

Identical to `three_goals_local_MS` except the realized political-state
**trajectory** in Goals 1 and 3 is evolved by the abstract transition
`p.F` (`dynamicTopLockInPathF` / `shockPathF`) rather than the affine
law. Goal 2 (dynamic-over-myopic dominance) is transition-independent
and unchanged. This is the headline that makes the paper's §4
"the proofs use only (F2)–(F4), never the affine form" claim true at the
**state-evolution** level, not only the incentive level.

The single extra hypothesis beyond `three_goals_local_MS` is
`hF_top` — the strict-above-diagonal condition at full sanctions
(`∀ x ∈ [0,1), x < F x 1`) — consumed **only** by the Goal-3 shock
finite-entry step. The affine instance satisfies `hF_top` automatically
(`0 < δ(1−x)`), so `three_goals_local_MS`'s affine trajectory is the
`F := affineF δ` specialisation. The price of generality is the loss of
the closed-form shock horizon `N_*`; Goal 3 asserts only `∃ N`.

Round BB (2026-09-28): `hF_top` on all of `[0, 1)` is more than the Goal-3
step needs. The pre-basin ascent siblings (`…_of_preBasinAscent`,
`Certificates/StandardComplianceLocalised.lean`, e.g.
`standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent`) need
full-sanction ascent only on `[0, max xT xS]`, with the same conclusion. -/
theorem three_goals_local_MS_generalF [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) := by
  -- Step 1: produce equilibrium via existence from the row-sum contraction margins.
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  -- Step 2: lift MS-form primitives at the equilibrium.
  have hV_S_mono : Monotone E.V_S := C.hV_S_mono_carrier E.V_S hVS
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x (max C.xT C.xS))) := by
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_strictMono V_T_sub V_S_sub x hx
  have h_target_combined :=
    TargetCombinedChordOn.at_equilibrium p C.h_target_combined E hVT hVS hα_eq
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  -- Build the joint-preference basin data once (shared by Goals 1 and 3).
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α C.xT C.xS (max C.xT C.xS) :=
    OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
      p hV_S_mono C.hxT_mem C.hxS_mem
      ⟨le_of_lt C.hpivot_mem.1, le_of_lt C.hpivot_mem.2⟩
      h_stage_sender h_target_combined
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max C.xT C.xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    exact E.α_mem x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := by
    intro x hx
    exact E.α_opt_top x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
  -- Goal 1: general-`F` persistence, universally over basin starts.
  have hGoal1 : ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
              ∈ Set.Icc (max C.xT C.xS) 1) ∧
      (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
    intro x₀ hx₀
    have h := p.jointPreferenceBasinTopF_long_run_nonDecreasing hB hx₀
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  -- Goal 2: dynamic-over-myopic dominance (transition-independent).
  have hFloor : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      max x (max C.xT C.xS) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    JointPreferenceBasinTop.level_dyn_top p hB
  have hGoal2 :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  -- Goal 3: general-`F` temporary shock with finite entry (uses `hF_top`).
  have hGoal3 : ∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
      ∃ N : ℕ,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                (p.shockPathF x₀shock N) n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
        (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                (p.shockPathF x₀shock N) n) := by
    intro x₀shock h_nn h_le
    have h := p.jointPreferenceBasinTopF_temporary_shock_permanent_high
      hB hF_top C.hpivot_mem.2 C.hpivot_mem.1 h_nn h_le
    obtain ⟨N, h1, _h2, h3, _, _, _⟩ := h
    exact ⟨N, h1, h3⟩
  exact ⟨E, hVT, hVS, hGoal1, hGoal2, hGoal3⟩

/-- **General-`F` regime-comparison three-goals theorem (R-2026-07-08).**

General-`F` sibling of the affine
`StandardComplianceLocalCoreCertificate.three_goals_local_regime_comparison_uniform_starts`
(whose `StandardComplianceLocalCertificate` name is an alias since round BH1.7):
the pathwise dynamic-over-myopic comparison with **both** regimes'
realized trajectories evolved by the abstract transition `p.F` — the
dynamic path by `dynamicTopLockInPathF` and the two compared sanction
sequences by the general-`F` rule path `ruleSanctionsF` — with the
affine hypothesis `hF` deleted. Adds to
`three_goals_local_MS_generalF` a statewise Goal 2 in the
regime-rule alias form plus the pathwise Goal 2′, uniform over basin
starts (the MS-form base is universal-start; a fixed start is the
instantiation at that `x₀`).

Hypotheses beyond the MS core certificate are exactly the general-`F`
restatements of what the affine version carries:

* `hF_top` — the existing general-`F` base-package shock input
  (strict-above-diagonal at full sanctions), consumed only by Goal 3;
* `hMyoBasin` — the same myopic basin-preservation hypothesis as the
  affine version (the canonical myopic equilibrium's realized rule
  maps the basin into itself). Note the *rule-level* statement is
  transition-independent; under the general-`F` step it yields path
  confinement via `F_diag`/`F_mono_x`/`F_mono_s`
  (`rulePathF_le_of_rule_le_and_upper_monoOn_basin`). As in the
  affine case, when `hMyoBasin` is not economically warranted the
  statewise Goal 2 of `three_goals_local_MS_generalF` is the
  recommended comparison. -/
theorem three_goals_local_MS_regime_comparison_generalF [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical) x
          ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      -- Goal 1 (general-`F` persistence, uniform over basin starts):
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      -- Goal 2 (statewise regime comparison):
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical) x
             ≤ p.dynamicEquilibriumRule E x)
      -- Goal 2′ (pathwise general-`F` regime comparison, uniform over
      -- basin starts):
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctionsF
                  (p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical))
                  x₀ n
                  ≤ p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀ n)
      -- Goal 3 (general-`F` shock hysteresis, uniform over shock starts):
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) := by
  -- Step 1: produce equilibrium via existence from the row-sum contraction margins.
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  -- Step 2: lift MS-form primitives at the equilibrium.
  have hV_S_mono : Monotone E.V_S := C.hV_S_mono_carrier E.V_S hVS
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x (max C.xT C.xS))) := by
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_strictMono V_T_sub V_S_sub x hx
  have h_target_combined :=
    TargetCombinedChordOn.at_equilibrium p C.h_target_combined E hVT hVS hα_eq
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  -- Build the joint-preference basin data once (shared by all goals).
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α C.xT C.xS (max C.xT C.xS) :=
    OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
      p hV_S_mono C.hxT_mem C.hxS_mem
      ⟨le_of_lt C.hpivot_mem.1, le_of_lt C.hpivot_mem.2⟩
      h_stage_sender h_target_combined
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max C.xT C.xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    exact E.α_mem x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := by
    intro x hx
    exact E.α_opt_top x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
  -- Goal 1: general-`F` persistence, universally over basin starts.
  have hGoal1 : ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
              ∈ Set.Icc (max C.xT C.xS) 1) ∧
      (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
    intro x₀ hx₀
    have h := p.jointPreferenceBasinTopF_long_run_nonDecreasing hB hx₀
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  -- Goal 2: statewise dominance via floor + myopic ceiling
  -- (transition-independent).
  have hFloor : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      max x (max C.xT C.xS) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    JointPreferenceBasinTop.level_dyn_top p hB
  have hGoal2 :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  -- Goal 2′: the dynamic rule preserves the basin, so the localized
  -- general-`F` rule comparator applies.
  have hDyn_basin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc (max C.xT C.xS) 1 := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact le_trans hx.1 (le_trans (le_max_left _ _) (hFloor x hx))
    · exact (p.σ_dyn_top_mem_I E.V_S x (E.α x)).2
  have hPathwise :
      ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
        ∀ n, p.ruleSanctionsF
               (p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical))
               x₀ n
               ≤ p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀ n := by
    intro x₀ hx₀
    exact p.ruleSanctionsF_le_of_rule_le_and_upper_monoOn_basin
      hMyoBasin hDyn_basin hTopMono hGoal2 hx₀
  -- Goal 3: general-`F` temporary shock with finite entry (uses `hF_top`).
  have hGoal3 : ∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
      ∃ N : ℕ,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                (p.shockPathF x₀shock N) n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
        (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                (p.shockPathF x₀shock N) n) := by
    intro x₀shock h_nn h_le
    have h := p.jointPreferenceBasinTopF_temporary_shock_permanent_high
      hB hF_top C.hpivot_mem.2 C.hpivot_mem.1 h_nn h_le
    obtain ⟨N, h1, _h2, h3, _, _, _⟩ := h
    exact ⟨N, h1, h3⟩
  exact ⟨E, hVT, hVS, hGoal1, hGoal2, hPathwise, hGoal3⟩

end StandardComplianceLocalCoreCertificate_MS

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
