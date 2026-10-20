/-
Sanctions/Theory/Certificates/StandardComplianceSchur.lean

**Round A2 (post-sweep): the Schur-form compliance certificate —
row-sum conditions retired end-to-end.**

`StandardComplianceLocalCoreCertificateSchur` mirrors the carrier-local
compliance certificate field-for-field, with the two row-sum
contraction conditions `β_T + L_TS < 1`, `β_S + L_ST < 1` replaced by
the strictly weaker package: diagonal bounds `β_T, β_S < 1` (derived
from the legacy row sums via `ofRowSum`, or equal to the `Params`
discount bounds at the canonical `β := p.β_*` instantiation) plus the
**Schur margin** `L_TS · L_ST < (1 − β_T)(1 − β_S)`. Its three-goals
theorem routes Step 1 (equilibrium existence) through the Round-E1
Perov existence layer
(`exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur`);
every later step is identical to the row-sum proof, which consumed the
row sums only at Step 1.

Rule 3: no new surface — strictly weaker hypotheses than the legacy
certificate. Rule 13: fully additive; the legacy certificate and its
theorems are untouched.

**2026-07-23 gap-closure round.** Two additions, zero new assumptions:

* `ofRowSum` — every legacy row-sum certificate downgrades to a
  Schur-form certificate (the diagonal bounds and the Schur margin are
  *derived* from the row sums by arithmetic), so the Schur certificate
  is inhabited at every shipped row-sum witness and its `hβ_T_lt` /
  `hβ_S_lt` fields are no longer free scalars in practice.
* `unique_in_carrier` (both certificate forms) — the certificate-level
  packaging of the headline within-carrier uniqueness theorem
  `ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur`, with
  every quantitative input supplied by certificate fields.
* `unique_in_carrier_of_mem` (all four certificate forms, round BH1.1,
  2026-10-06) — the same uniqueness without the selector-coincidence
  binders: carrier membership alone pins both value functions, and the
  policies agree on the state set.

**Round BJ5.1 (2026-10-07).** The Schur MS certificate's myopic ceiling is
stated against `p.myopicFeedbackEquilibrium_canonical`, built from the static
selector's continuity. That condition, the joint continuity of the static
Sender selector `σ`, was the `Params` field `σ_continuous`; it is now the
class `Params.StaticSelectorContinuous`. The certificate
`StandardComplianceLocalCoreCertificateSchur_MS` takes
`[p.StaticSelectorContinuous]` as a structure parameter, and so does every
theorem about it or about the MS certificate (`unique_in_carrier`,
`unique_in_carrier_of_mem`, `ofRowSum_MS`, `three_goals_local_MS_generalF`).
The row-sum and Schur certificates without a myopic ceiling are unchanged.
General in `F`.
-/

import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Equilibrium.PerovExistence

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Schur-form carrier-local compliance certificate (Round A2).**
Field-for-field the carrier-local certificate, with the row-sum
conditions replaced by diagonal bounds + the Schur margin.

**Rule 9 — generality witnessed (2026-08-21).** As for the core certificate:
`Sanctions.Examples.qbCertificateSchur` inhabits this class at `quadBumpF` via
the row-sum bridge `ofRowSum`, which carries `d` and the Sender chord
verbatim. `quadBumpF_ne_affineF` refutes the affine law at every weight, so the
Schur form is certified inhabited *outside* the affine case and not merely
inhabited.

**Round BJ1.4 (2026-10-07, author-approved).** As in the core certificate, the
Target loss-offset stack (`dlo`, `hchord_lo`, `cT`, `gT`, `hgT_nn`,
`hT_loss_margin`, `h_stage_target_loss_on`, `hV_T_gain_on_carrier`) and the
floor sign `hsbar_pos` are deleted: no theorem over this certificate read them
once the goals ran through the Sender persistence basin (round BH1.5). -/
structure StandardComplianceLocalCoreCertificateSchur where
  D : p.ValueClass2
  h_inv : D.IsInvariant
  /-- Row contraction (heterogeneous), Schur form. -/
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
  /-- Diagonal bounds. Never free in practice: `ofRowSum` derives them
  from the legacy row sums, and at the canonical instantiation where the
  row diagonals are the discount factors (`β_T := p.β_T`, `β_S := p.β_S`)
  they are exactly `p.β_T_mem.2` / `p.β_S_mem.2`. -/
  hβ_T_lt : β_T < 1
  hβ_S_lt : β_S < 1
  /-- **The Schur margin** — strictly weaker than the legacy row sums. -/
  hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)
  /-- High-basin geometry (identical to the legacy certificate). -/
  xT : ℝ
  xS : ℝ
  sbar : ℝ
  mS : ℝ
  KS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  hsbar_mem : sbar ∈ Sanctions.I
  /-- Sender-leg sanction upper-chord rate (Rule 22). `δ` at the affine law. -/
  d : ℝ
  hF_chord :
    ∀ x ∈ Set.Icc xS (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ ≤ s₂ →
          |p.F x s₂ - p.F x s₁| ≤ d * (s₂ - s₁)
  hS_margin : p.β_S * KS * d < mS
  /-- Consumed only by the Goal-3 shock theorem. -/
  hjoint_lt : max xT xS < 1
  hV_S_lip_carrier :
    ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS
  h_stage_sender_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS
  /-- **Carrier-local interval dominance (B1).** The Quah–Strulovici
  (2007) interval-dominance-order family condition on the Sender
  dynamic objective — strictly weaker than Milgrom-Shannon single
  crossing; every SCP discharge upcasts via
  `IDOFamilyOn.of_singleCrossingOn`. -/
  hIDO_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
  M : p.MyopicFeedbackEquilibrium
  hMyoCeiling :
    ∀ x ∈ Set.Icc (max xT xS) 1,
      p.σ x (M.α x) ≤ max x sbar

namespace StandardComplianceLocalCoreCertificateSchur

/-! ### Recovering the affine-denominated margin (Schur sibling)

Mirrors the core certificate: the Sender chord field pins `δ ≤ d` at an affine
economy, so the δ-denominated Sender margin is derived rather than assumed.
(The Target lower chord at rate `dlo`, which pinned `dlo ≤ δ`, was deleted with
the rest of the Target loss-offset stack in round BJ1.4.) -/


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
theorem hKS_nonneg
    {q : Sanctions.AbstractGame.Params}
    (C : q.StandardComplianceLocalCoreCertificateSchur) : 0 ≤ C.KS := by
  obtain ⟨V, hV⟩ := C.D.nonempty_S
  exact (C.hV_S_lip_carrier V hV).nonneg

/-- **Row-sum ⇒ Schur bridge (2026-07-23 gap-closure).** Every legacy
row-sum certificate is a Schur-form certificate: with nonnegative row
entries, the row sums `β_T + L_TS < 1` and `β_S + L_ST < 1` imply the
diagonal bounds `β_T < 1`, `β_S < 1` and the Schur margin
`L_TS · L_ST < (1 − β_T)(1 − β_S)` through the generic Foundations
theorem `NNMat2.schurDet_of_rowSums`. Consequently every shipped row-sum
witness (eeCert, qbCert, b2, fourGroupCert, lbCert, …) inhabits the Schur
certificate, and the Schur diagonal bounds are *derived*, not free
scalars. All non-contraction fields carry over verbatim. -/
def ofRowSum (C : p.StandardComplianceLocalCoreCertificate) :
    p.StandardComplianceLocalCoreCertificateSchur where
  D := C.D
  h_inv := C.h_inv
  β_T := C.β_T
  β_S := C.β_S
  L_TS := C.L_TS
  L_ST := C.L_ST
  hβ_T_nn := C.hβ_T_nn
  hβ_S_nn := C.hβ_S_nn
  hL_TS_nn := C.hL_TS_nn
  hL_ST_nn := C.hL_ST_nn
  hT_T_op := C.hT_T_op
  hT_S_op := C.hT_S_op
  hβ_T_lt := by linarith [C.hsuff_T, C.hL_TS_nn]
  hβ_S_lt := by linarith [C.hsuff_S, C.hL_ST_nn]
  hSchur := by
    let A : Sanctions.Foundations.Perov.NNMat2 :=
      { a := C.β_T
        b := C.L_TS
        c := C.L_ST
        d := C.β_S
        ha_nn := C.hβ_T_nn
        hb_nn := C.hL_TS_nn
        hc_nn := C.hL_ST_nn
        hd_nn := C.hβ_S_nn }
    exact A.schurDet_of_rowSums C.hsuff_T
      (by simpa [A, add_comm] using C.hsuff_S)
  xT := C.xT
  xS := C.xS
  sbar := C.sbar
  mS := C.mS
  KS := C.KS
  hxT_mem := C.hxT_mem
  hxS_mem := C.hxS_mem
  hsbar_mem := C.hsbar_mem
  d := C.d
  hF_chord := C.hF_chord
  hS_margin := C.hS_margin
  hjoint_lt := C.hjoint_lt
  hV_S_lip_carrier := C.hV_S_lip_carrier
  h_stage_sender_on := C.h_stage_sender_on
  hIDO_on := C.hIDO_on
  M := C.M
  hMyoCeiling := C.hMyoCeiling

/-- **Within-carrier equilibrium uniqueness at a Schur certificate
(2026-07-23 gap-closure).** Any two top-selector feedback Stackelberg
equilibria whose value pairs lie in the certificate's carriers and whose
policies coincide with the carrier selector agree in both value
functions and in the policy — the certificate-level packaging of the
headline `ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur`,
with every quantitative input (row bounds, diagonal bounds, Schur
margin, carrier invariance) supplied by the certificate's own fields.
Only the carrier/selector memberships remain as hypotheses. The selector
part is read only for the off-`S` part of `E.α = E'.α`:
`unique_in_carrier_of_mem` below drops it and concludes agreement of the
policies on the state set (round BH1.1). This theorem makes no global
equilibrium-uniqueness claim; bistability concerns state-path selection
under a single equilibrium. -/
theorem unique_in_carrier
    (C : p.StandardComplianceLocalCoreCertificateSchur)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S)
    (hαE : E.α = C.D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = C.D.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  C.D.feedbackStackelbergTop_unique_in_carrier_schur C.h_inv
    C.hT_T_op C.hT_S_op C.hβ_T_lt C.hβ_S_lt C.hSchur E E' hVT hVS hVT' hVS' hαE
    hαE'

/-- **Within-carrier equilibrium uniqueness at a Schur certificate, with no
selector hypothesis (round BH1.1, 2026-10-06).** Sibling of `unique_in_carrier`
with the two selector-coincidence binders `hαE`, `hαE'` dropped. Carrier
membership of the two value pairs alone pins both value functions, and the two
policies agree at every feasible state: an equilibrium with carrier values
already plays the carrier selector on `S`
(`ValueClass2.α_eqOn_α_on_of_feedbackStackelbergTop`). Every quantitative
input comes from the certificate's own fields through
`ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem`; the
diagonal bound `hβ_T_lt` is not read. The policy conclusion is agreement on the
state set, which is all a policy is ever evaluated on. It makes no global
equilibrium-uniqueness claim. General in `F`. -/
theorem unique_in_carrier_of_mem
    (C : p.StandardComplianceLocalCoreCertificateSchur)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  C.D.feedbackStackelbergTop_unique_in_carrier_schur_of_mem C.h_inv
    C.hL_TS_nn C.hL_ST_nn C.hT_T_op C.hT_S_op
    C.hβ_S_lt C.hSchur E E' hVT hVS hVT' hVS'

end StandardComplianceLocalCoreCertificateSchur

namespace StandardComplianceLocalCoreCertificate

/-- **Within-carrier equilibrium uniqueness at a legacy row-sum
certificate (2026-07-23 gap-closure).** One-line corollary via the
`ofRowSum` bridge: the row sums already imply the Schur package, so
every row-sum certificate pins its equilibrium uniquely within the
carrier/selector class. -/
theorem unique_in_carrier
    (C : p.StandardComplianceLocalCoreCertificate)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S)
    (hαE : E.α = C.D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = C.D.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  StandardComplianceLocalCoreCertificateSchur.unique_in_carrier p
    (StandardComplianceLocalCoreCertificateSchur.ofRowSum p C)
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Within-carrier equilibrium uniqueness at a legacy row-sum certificate,
with no selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`unique_in_carrier` without `hαE`, `hαE'`: one-line corollary of the Schur
form's `unique_in_carrier_of_mem` through the `ofRowSum` bridge. Any two
equilibria with carrier values share both value functions, and their policies
agree at every feasible state. General in `F`. -/
theorem unique_in_carrier_of_mem
    (C : p.StandardComplianceLocalCoreCertificate)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  StandardComplianceLocalCoreCertificateSchur.unique_in_carrier_of_mem p
    (StandardComplianceLocalCoreCertificateSchur.ofRowSum p C)
    E E' hVT hVS hVT' hVS'

end StandardComplianceLocalCoreCertificate

namespace StandardComplianceLocalCoreCertificate_MS

/-- **Within-carrier equilibrium uniqueness at a slim MS-form certificate
(2026-07-24, MS parity closure).** The MS-form certificate carries the
legacy row-sum contraction fields (`hsuff_T`, `hsuff_S`), which imply
the Schur package (diagonal bounds by `linarith`, the margin via the
generic `NNMat2.schurDet_of_rowSums`), so it too pins its equilibrium
uniquely within the carrier/selector class — the same packaging as the
legacy and Schur forms, closing the parity gap on the MS/general-`F`
route. -/
theorem unique_in_carrier [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S)
    (hαE : E.α = C.D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = C.D.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  C.D.feedbackStackelbergTop_unique_in_carrier_schur C.h_inv
    C.hT_T_op C.hT_S_op
    (by linarith [C.hsuff_T, C.hL_TS_nn])
    (by linarith [C.hsuff_S, C.hL_ST_nn])
    (by
      let A : Sanctions.Foundations.Perov.NNMat2 :=
        { a := C.β_T
          b := C.L_TS
          c := C.L_ST
          d := C.β_S
          ha_nn := C.hβ_T_nn
          hb_nn := C.hL_TS_nn
          hc_nn := C.hL_ST_nn
          hd_nn := C.hβ_S_nn }
      exact A.schurDet_of_rowSums C.hsuff_T
        (by simpa [A, add_comm] using C.hsuff_S))
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Within-carrier equilibrium uniqueness at a slim MS-form certificate, with
no selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`unique_in_carrier` without `hαE`, `hαE'`. The certificate's row sums give the
Sender diagonal bound and the Schur margin exactly as there; carrier membership
of the two value pairs then pins both value functions, and the two policies
agree at every feasible state. General in `F`. -/
theorem unique_in_carrier_of_mem [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  C.D.feedbackStackelbergTop_unique_in_carrier_schur_of_mem C.h_inv
    C.hL_TS_nn C.hL_ST_nn C.hT_T_op C.hT_S_op
    (by linarith [C.hsuff_S, C.hL_ST_nn])
    (by
      let A : Sanctions.Foundations.Perov.NNMat2 :=
        { a := C.β_T
          b := C.L_TS
          c := C.L_ST
          d := C.β_S
          ha_nn := C.hβ_T_nn
          hb_nn := C.hL_TS_nn
          hc_nn := C.hL_ST_nn
          hd_nn := C.hβ_S_nn }
      exact A.schurDet_of_rowSums C.hsuff_T
        (by simpa [A, add_comm] using C.hsuff_S))
    E E' hVT hVS hVT' hVS'

end StandardComplianceLocalCoreCertificate_MS

/-! ## Schur-form slim MS certificate (2026-07-24: Round-A2 port to the
MS/general-`F` route, user-approved)

Field-for-field the slim MS-form certificate
(`StandardComplianceLocalCoreCertificate_MS`), with the legacy row-sum
conditions `β_T + L_TS < 1`, `β_S + L_ST < 1` replaced by the strictly
weaker package: diagonal bounds `β_T, β_S < 1` plus the Schur margin
`L_TS·L_ST < (1−β_T)(1−β_S)`. Rule 3: no new surface — strictly weaker
hypotheses. Every row-sum MS witness inhabits it via `ofRowSum_MS`
(non-vacuity), and the preferred general-`F` engine is ported with
Step 1 routed through the Perov/Schur existence; every later step is
the MS row-sum proof verbatim (the row sums were consumed only at
Step 1). -/

/-- **Schur-form slim MS core certificate.** General in `F`. It takes
`[p.StaticSelectorContinuous]` (round BJ5.1, 2026-10-07: joint continuity of the
static Sender selector, formerly a `Params` field) because its myopic ceiling is
stated against the canonical myopic equilibrium; the fields are unchanged. -/
structure StandardComplianceLocalCoreCertificateSchur_MS [p.StaticSelectorContinuous] where
  D : p.ValueClass2
  h_inv : D.IsInvariant
  /-- Row contraction (heterogeneous), Schur form. -/
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
  /-- Diagonal bounds (derived from the row sums via `ofRowSum_MS`, or
  the discount-range projections at the canonical instantiation). -/
  hβ_T_lt : β_T < 1
  hβ_S_lt : β_S < 1
  /-- **The Schur margin** — strictly weaker than the MS row sums. -/
  hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)
  /-- High-basin pivots (identical to the row-sum MS certificate). -/
  xT : ℝ
  xS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  hpivot_mem : max xT xS ∈ Set.Ioo (0 : ℝ) 1
  h_stage_sender_strictMono :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x (max xT xS)))
  hIDO_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
  h_target_combined : p.TargetCombinedChordOn D xT (max xT xS)
  hV_S_mono_carrier :
    ∀ V_S ∈ D.carrier_S, Monotone V_S
  hMyoCeiling :
    ∀ x ∈ Set.Icc (max xT xS) 1,
      p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max xT xS)

namespace StandardComplianceLocalCoreCertificateSchur_MS

/-- **Row-sum ⇒ Schur bridge for the MS form.** Every row-sum MS
certificate is a Schur-form MS certificate (diagonals by `linarith`,
margin via `NNMat2.schurDet_of_rowSums`); all non-contraction fields
carry over verbatim, so every shipped MS witness inhabits the Schur
form. -/
def ofRowSum_MS [p.StaticSelectorContinuous] (C : p.StandardComplianceLocalCoreCertificate_MS) :
    p.StandardComplianceLocalCoreCertificateSchur_MS where
  D := C.D
  h_inv := C.h_inv
  β_T := C.β_T
  β_S := C.β_S
  L_TS := C.L_TS
  L_ST := C.L_ST
  hβ_T_nn := C.hβ_T_nn
  hβ_S_nn := C.hβ_S_nn
  hL_TS_nn := C.hL_TS_nn
  hL_ST_nn := C.hL_ST_nn
  hT_T_op := C.hT_T_op
  hT_S_op := C.hT_S_op
  hβ_T_lt := by linarith [C.hsuff_T, C.hL_TS_nn]
  hβ_S_lt := by linarith [C.hsuff_S, C.hL_ST_nn]
  hSchur := by
    let A : Sanctions.Foundations.Perov.NNMat2 :=
      { a := C.β_T
        b := C.L_TS
        c := C.L_ST
        d := C.β_S
        ha_nn := C.hβ_T_nn
        hb_nn := C.hL_TS_nn
        hc_nn := C.hL_ST_nn
        hd_nn := C.hβ_S_nn }
    exact A.schurDet_of_rowSums C.hsuff_T
      (by simpa [A, add_comm] using C.hsuff_S)
  xT := C.xT
  xS := C.xS
  hxT_mem := C.hxT_mem
  hxS_mem := C.hxS_mem
  hpivot_mem := C.hpivot_mem
  h_stage_sender_strictMono := C.h_stage_sender_strictMono
  hIDO_on := C.hIDO_on
  h_target_combined := C.h_target_combined
  hV_S_mono_carrier := C.hV_S_mono_carrier
  hMyoCeiling := C.hMyoCeiling

/-- **Within-carrier equilibrium uniqueness at a Schur-form MS
certificate.** Direct application of the headline
`ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` with every
quantitative input supplied by certificate fields. -/
theorem unique_in_carrier [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S)
    (hαE : E.α = C.D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = C.D.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  C.D.feedbackStackelbergTop_unique_in_carrier_schur C.h_inv
    C.hT_T_op C.hT_S_op C.hβ_T_lt C.hβ_S_lt C.hSchur E E' hVT hVS hVT' hVS' hαE
    hαE'

/-- **Within-carrier equilibrium uniqueness at a Schur-form MS certificate,
with no selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`unique_in_carrier` without `hαE`, `hαE'`: carrier membership of the two value
pairs pins both value functions, and the two policies agree at every feasible
state. Every quantitative input is a certificate field; `hβ_T_lt` is not read.
General in `F`. -/
theorem unique_in_carrier_of_mem [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ C.D.carrier_T) (hVS : E.V_S ∈ C.D.carrier_S)
    (hVT' : E'.V_T ∈ C.D.carrier_T) (hVS' : E'.V_S ∈ C.D.carrier_S) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  C.D.feedbackStackelbergTop_unique_in_carrier_schur_of_mem C.h_inv
    C.hL_TS_nn C.hL_ST_nn C.hT_T_op C.hT_S_op
    C.hβ_S_lt C.hSchur E E' hVT hVS hVT' hVS'

/-- **General-`F` three-goals theorem from the Schur-form MS certificate
(Round-A2 port, 2026-07-24).** Identical conclusion to
`StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS_generalF`;
Step 1 routes through the Perov/Schur existence
(`exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur`),
the remainder is the MS row-sum proof verbatim (the row sums were
consumed only at Step 1). The affine trajectory is the `F := affineF δ`
specialisation via `affineF_hF_top`. -/
theorem three_goals_local_MS_generalF [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
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
  -- Step 1 (Schur form): produce equilibrium via the Perov existence.
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur
      C.h_inv C.hT_T_op C.hT_S_op C.hβ_T_lt C.hβ_S_lt C.hSchur
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
  have hGoal1 : ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
              ∈ Set.Icc (max C.xT C.xS) 1) ∧
      (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
    intro x₀ hx₀
    have h := p.jointPreferenceBasinTopF_long_run_nonDecreasing hB hx₀
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  have hFloor : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      max x (max C.xT C.xS) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    JointPreferenceBasinTop.level_dyn_top p hB
  have hGoal2 :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
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

end StandardComplianceLocalCoreCertificateSchur_MS

end Params
end AbstractGame

end

end Sanctions
