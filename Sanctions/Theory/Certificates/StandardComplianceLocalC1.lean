/-
Sanctions/Theory/Certificates/StandardComplianceLocalC1.lean

**Audit-49 Item 5: carrier-local compliance certificate (C¹ track).**

**PARTIALLY UNFROZEN (2026-07-12; supersedes the 2026-07-04 A6 freeze
for the witness layer only).** This certificate is now *inhabited*:
`Examples/C1WitnessEnvelope.lean` builds `eeC1Certificate` and
`fgcC1Certificate` at the two pinned exact Bellman fixed points, and
`three_goals_local_C1` fires at both. Crucially, the `hComplete` field
is *discharged* there (`eeC1Class_complete` / `fgcC1Class_complete` —
a singleton carrier is trivially complete) and the system's `T` is
`id`, so the `c1distPair`-fixed point is a genuine fixed point: no
assumed-completeness postulate and no pseudo-metric artefact enters
any shipped result. The paper's shadow-price passage cites the
resulting equilibrium slopes. No headline row fences the C¹ layer.

The *abstract* layer STAYS FROZEN: each general form (the
`SmoothSanctionClass` IFT Prop fields, an abstract
`ValueClass_C1Complete` derivation, general-`F` RZS-style statements)
would need new differentiability hypotheses (Rule 3). Both structural
deficiencies persist at abstract generality: `c1distPair` is a
pseudo-metric (`V'` stored on all of `ℝ`), and completeness
(`ValueClass_C1Complete`) is consumed per-certificate, not derived. Revival order if ever needed: (1) the within-set
uniform-limits-of-derivatives theorem (a mathlib gap, not an analytic
one — `Foundations/` candidate), (2) the `V'`-domain refactor,
(3) the asymmetric `ValueClass2_C1` duplication mentioned below —
only once a consumer exists.

Parallel of `StandardComplianceLocal.lean` (audit-49 Item 2) for the
C¹ Bellman-system track. The C¹ track uses a single-carrier
`C1BellmanSystem` (no asymmetric `ValueClass2_C1` yet — adding the
asymmetric C¹ structure would require duplicating the iter-15..21
pipeline). The localization here therefore targets the per-E
universal quantifier, replacing it with a carrier-local
quantifier over `z : D_C1.carrier`.

Differences vs `RegularEconomyCertificateC1ComplianceCore`:

* All stage-bound / Sender-Lipschitz / single-crossing / V_T-gain
  fields are **carrier-local on `D_C1`**: they quantify over
  `z : D_C1.carrier` (each `z` is a pair `(V_T, V_S)` of C¹ values
  in the C¹ Bellman-system carrier) rather than over every
  `FeedbackStackelbergEquilibriumTop`.

This file provides:

* `StandardComplianceLocalCertificateC1 p K_d` — the carrier-local
  C¹ Core certificate.
* `three_goals_local_C1` — the statewise three-goals theorem at the
  produced fixed-point equilibrium.

**P9 unfreeze note (2026-07-12).** `C1BellmanSystem`'s α fields were
carrier-localized (see the Rule-13 disclosure in
`Theory/Bellman/C1BellmanSystem.lean`); the proof body of
`three_goals_local_C1` was adapted mechanically
(`α_cont/α_mem/α_isMaxOn` applications `z.val.1 z.val.2 ↦ z`). No
statement in this file changed.

## Rule compliance

* **Rule 1.** No strategy changes — the produced equilibrium's `α`
  is the C¹ Bellman-system's `α_on_C1` evaluated at the C¹
  fixed-point (the same as in
  `RegularEconomyCertificateC1ComplianceCore`).
* **Rule 3.** Cat-(2) localization: replaces assumptions over all top
  equilibria (`∀ E : FeedbackStackelbergEquilibriumTop`) with
  assumptions over the C¹ carrier `D_C1.carrier` used by the
  fixed-point construction. This avoids assumptions on equilibria
  outside the construction, but it is not a pure logical weakening:
  the two forms quantify over different families (equilibria vs.
  carrier pairs). Pre-confirmed by user directive.
* **Rule 5.** Fully parametric over `(p, K_d, C : StandardComplianceLocalCertificateC1)`.
-/

import Sanctions.Theory.Certificates.RegularEconomy
import Sanctions.Theory.Bridges.JETBridgeC1System
import Sanctions.Theory.Certificates.StandardComplianceBridges

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Carrier-local C¹ compliance certificate -/

/-- **Audit-49 Item 5: carrier-local C¹ compliance certificate.**

The C¹-track analog of `StandardComplianceLocalCertificate`. The
single-carrier structure of `C1BellmanSystem` is retained (the C¹
track does not yet support asymmetric carriers), but per-E
quantifiers are replaced with carrier-local quantifiers on
`D_C1.carrier`. -/
structure StandardComplianceLocalCertificateC1 (K_d : ℝ) where
  hK_d_nn : 0 ≤ K_d
  D_C1 : C1BellmanSystem p K_d
  hComplete : ValueClass_C1Complete D_C1.toValueClass_C1
  /-- High-basin geometry. -/
  xT : ℝ
  xS : ℝ
  sbar : ℝ
  mS : ℝ
  KS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  hsbar_mem : sbar ∈ Sanctions.I
  hKS_nonneg : 0 ≤ KS
  hS_margin : p.β_S * KS * p.δ < mS
  hsbar_pos : 0 < sbar
  hjoint_lt : max xT xS < 1
  /-- **Carrier-local Sender Lipschitz.** Every `V_S` whose `C1Val`
  appears as `z.val.2` for some `z : D_C1.carrier` is
  `KS`-Lipschitz (after BCF projection). -/
  hV_S_lip_carrier :
    ∀ z : D_C1.carrier, ValueLipschitzWith z.val.2.V KS
  /-- Target loss-offset bounds (audit-43). -/
  cT : ℝ
  gT : ℝ
  hT_loss_margin : cT ≤ p.β_T * gT * p.δ
  /-- **Carrier-local stage Target loss.** For every `z` in
  `D_C1.carrier` and every `x ∈ [xT, 1]`, the stage Target payoff
  evaluated at the leader selector `D_C1.α_on_C1 z.val.1 z.val.2`
  has bounded downward slope `cT` on `[max x sbar, 1]`. -/
  h_stage_target_loss_carrier :
    ∀ z : D_C1.carrier,
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn
          (fun s => p.U_T x (D_C1.α_on_C1 z.val.1 z.val.2 x) s)
          (Set.Icc (max x sbar) 1) cT
  /-- **Carrier-local V_T high-state gain.** Every `V_T` arising as
  the BCF projection of `z.val.1` for some `z : D_C1.carrier` has
  minimum upward slope `gT` on `[xT, 1]`. -/
  hV_T_gain_on_carrier :
    ∀ z : D_C1.carrier,
      LowerSlopeOnValueOn z.val.1.V (Set.Icc xT 1) gT
  /-- **Carrier-local stage Sender slope.** For every `z` in
  `D_C1.carrier` and every `x ∈ [xS, 1]`, the stage Sender payoff
  evaluated at the leader selector has minimum upward slope `mS`
  on `[0, max x sbar]`. -/
  h_stage_sender_carrier :
    ∀ z : D_C1.carrier,
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (D_C1.α_on_C1 z.val.1 z.val.2 x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS
  /-- **Carrier-local single crossing.** For every `z` in
  `D_C1.carrier`, the Sender dynamic objective at the leader
  selector has Milgrom-Shannon single crossing on `[max xT xS, 1]`. -/
  hSC_carrier :
    ∀ z : D_C1.carrier,
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective z.val.2.V x
                      (D_C1.α_on_C1 z.val.1 z.val.2 x) s)
  /-- Independent myopic comparator. -/
  M : p.MyopicFeedbackEquilibrium
  /-- Myopic ceiling on the basin. -/
  hMyoCeiling :
    ∀ x ∈ Set.Icc (max xT xS) 1,
      p.σ x (M.α x) ≤ max x sbar
  /-- Starting state. -/
  x₀ : ℝ
  hx₀ : x₀ ∈ Set.Icc (max xT xS) 1
  x₀shock : ℝ
  hx₀shock_nn : 0 ≤ x₀shock
  hx₀shock_le : x₀shock ≤ 1

namespace StandardComplianceLocalCertificateC1

variable {K_d : ℝ}


end StandardComplianceLocalCertificateC1

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
