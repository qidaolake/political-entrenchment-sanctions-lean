/-
Sanctions.lean — root module.

Formalization of

  "Entrenchment and the Persistence of Sanctions"
  (Xiaofeng Gong; titled "Why Do Sanctions Persist? A Dynamic
  Political-Economy Model with Forward-Looking Governments" until 2026-09-21).

Build everything with `lake build`.

## Architecture (post-2026-05-23 abstract-only)

The codebase is organized by **role** (postulates vs. theory) rather
than by topic, to make the assumption surface visible to auditors:

* `Sanctions/Domain/` — the state and action space `[0,1]` and the
  projection onto it (`I`, `S`, `clipS`, `clipS'`, and the
  derivative-on-`S` primitives). Split out of `Foundations/Basic.lean`
  on 2026-08-27 so the modelling choice is declared in one place. It
  sits *below* Foundations: twelve Foundations modules are stated over
  `S`, so the interval is a base layer, not a superstructure.
* `Sanctions/Foundations/` — math utilities (no project economics):
  Banach contraction, Topkis lattice machinery, Milgrom–Shannon
  monotone-argmax, Stokey–Lucas–Prescott Bellman preservation,
  He-Sun Skolemization, abstract Stackelberg structural definitions.
* `Sanctions/Postulates/` — **the primitive game environment.** The
  CORE abstract structure is `Sanctions.AbstractGame.Params`: a
  two-player dynamic game with abstract `U_T, U_S, σ` function fields,
  joint continuity, σ-feasibility, and σ-as-Sender-stage-argmax. The
  only other Postulates file is `Postulates/ShockedParams.lean` (the
  exogenous-shock extension `ShockedParams` with its atomless shock
  kernel). The historical `JointMPE.SenderResponse` interface moved to
  `Theory/Bridges/SenderResponse.lean` in the 2026-07-24 cleanup, so
  this layer now contains only live assumption surface.
  This is the *primitive game environment*, not the entire assumption
  surface of any particular theorem: the canonical paper-facing theorem
  `standardCompliance_three_goals_local` additionally consumes
  theorem-level regularity and economic sufficient conditions
  (`StandardComplianceLocalCertificate`, `ValueClass2`,
  `D.IsInvariant`, row-contraction margins, carrier-local argmax
  uniqueness, Sender high-sanction incentive, Target sanction-loss
  offset, single crossing, myopic ceiling, high-basin geometry) packaged
  in `Theory/Certificates/StandardComplianceLocal.lean`.
* `Sanctions/Theory/` — definitions and theorems derived from the
  postulates plus mathlib, organized thematically (2026-07-07
  restructure; every module imported by the `Theory.lean` aggregator):
  - `Theory/Bellman/` — value-function/operator layer (Bellman T/S,
    cone preservation, value classes and invariant carriers, C¹ track).
  - `Theory/Equilibrium/` — existence and selectors (joint MPE,
    feedback Stackelberg, corner/slaved/Perov existence, argmax
    uniqueness).
  - `Theory/Basin/` — basin geography (joint preference basin,
    tipping, stage flip and its dischargers).
  - `Theory/Certificates/` — paper-facing certificate assembly (the
    `StandardCompliance*` family, loss-offset mechanism).
  - `Theory/LockIn/` — dynamics, comparators, comparative statics.
  - `Theory/Shocked/` — the atomless-purification chain.
  - `Theory/Microfoundations/` — interest-group polities.
  - `Theory/Bridges/` — the JET bridge layer. The audit-48
    quarantine is PER-DECLARATION: the `jet_*_from_lowerSlopes`
    theorems are not citable for literal-compliance claims, while
    their `jet_*_from_lossOffset_on` replacements in the same files
    are live and consumed by `Certificates/RegularEconomy.lean`.
  (`TarskiMPE` moved to `Foundations/` in the same restructure.)

Earlier bilateral-LQ concrete instantiations (witness-specific
parameter vectors, `V_T_bilateral`/`V_S_bilateral` numerical bounds,
alt-witness same-start divergence, hysteresis shock, binary-action
benchmark, two-parameter openness) were deleted in the 2026-05-23
AbstractGame refactor. The interim non-LQ monotone-Sender witness
(`Examples/MonotoneSender.lean`) was deleted on 2026-05-24 in
preparation for a new representation layer. The package now includes a
**minimal non-vacuity witness** in `Examples/JointPositiveSanctions`:
a concrete `jointPositiveParams : AbstractGame.Params` (linear payoffs
`U_T = U_S = s`, `σ ≡ 1`, `δ = β_T = β_S = 1/2`) for which the
lower-level joint sanction-preference basin Prop
`JointPreferenceBasinTop` is provably inhabited at
`V_T = V_S = 0`, `α ≡ 0`, `xbar = sbar = 1/2`. This witness inhabits
only the lower-level basin Prop. It does **not** instantiate the
preferred core certificate `StandardComplianceLocalCoreCertificate`
(or its fixed-start extension `StandardComplianceLocalCertificate`),
and it does **not** constitute a substantive economic example of the
preferred three-goal theorem
`standardCompliance_three_goals_local_uniform_starts`. The substantive
instantiation of `StandardComplianceLocalCoreCertificate` (with the
loss-offset margin `c_T ≤ β_T · g_T · δ` and the Sender high-sanction
margin `β_S · K_S · δ < m_S` discharged from primitive payoffs) was
DISCHARGED on 2026-07-01 by `eeCertCertificate` — see the
"Non-vacuity status" section below.

## Canonical paper-facing route (audit-49 follow-up: asymmetric local certificate)

Under the **literal-compliance** reading of the Target action `a`
(`a = 1` = full compliance, `a = 0` = no compliance), the canonical
paper-facing main theorem family is:

### Preferred (audit-49 follow-up: asymmetric carrier-local route)

* **BCF route (preferred, universal-start)**:
  `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_uniform_starts`
  — from `StandardComplianceLocalCertificate` (built on the
  **asymmetric** `ValueClass2` with separate Target and Sender
  carriers and **carrier-local** stage primitives quantified over
  `∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS, …`); the path-level goals
  hold for every basin start `x₀ ∈ B` and every shock start
  `x₀shock ∈ [0, 1]`. The fixed-start form
  `standardCompliance_three_goals_local` (using `C.x₀` / `C.x₀shock`)
  is retained as a compatibility alias, and the universal-start
  pathwise dynamic-over-myopic comparison is
  `standardCompliance_three_goals_local_regime_comparison_uniform_starts`.
* **C¹ route**: `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_C1`
  — from `StandardComplianceLocalCertificateC1`.

These are the recommended targets for paper-facing citation. They use
the audit-49-follow-up asymmetric carrier-local construction, which
lets Target-side regularity restrictions (notably the loss-offset
continuation gain `LowerSlopeOnValueOn V (Icc xT 1) gT`) live on the
Target carrier alone — economically appropriate when the Sender
continuation value models national or trade welfare rather than a
Sender policymaker objective.

### Homogeneous compatibility route (audit-46/47 canonical aliases)

* BCF: `Sanctions.AbstractGame.Params.standardCompliance_three_goals`
* C¹: `Sanctions.AbstractGame.Params.standardCompliance_three_goals_C1`
* Pathwise corollary (requires `hMyo_basin`):
  `Sanctions.AbstractGame.Params.standardCompliance_three_goals_pathwise`

These are retained as **homogeneous compatibility** — the single-
carrier specialization in which `carrier_T = carrier_S` (the audit-46
`StandardComplianceCertificate` aliases for
`RegularEconomyCertificateComplianceCore`). Every existing
single-carrier `ValueClass` is realized as a `ValueClass2` via
`ValueClass.toValueClass2`, so the homogeneous route is genuinely a
specialization of the asymmetric one. Paper-facing citations may
still use this family if they only need the homogeneous case.

All five theorems live in
`Sanctions/Theory/Certificates/StandardComplianceMain.lean` as one-line
delegations to the underlying certificates. They prove persistence on
the high political basin, **statewise** dynamic-over-myopic sanction
dominance on that basin, and temporary-shock hysteresis — with
sign-correct Target preferences under literal compliance via the
loss-offset mechanism (`LowerLossSlopeOn` + `LowerSlopeOnValueOn` +
margin `cT ≤ β_T · gT · δ`, in
`Sanctions/Theory/Certificates/TargetSanctionLossOffset.lean`).

### Legacy resistance-action route (quarantined)

The older `jet_three_goals_from_valueClass_and_primitives`
(`Theory/Bridges/JETBridge.lean:648`),
`RegularEconomyCertificate.three_goals`, and the C¹ bridges
`jet_C1BellmanSystem_three_goals` and its `_compliance_on` /
`_compliance_statewise` siblings
(`Theory/Bridges/JETBridgeC1System.lean:112,241,379`)
routes remain valid **only** under the resistance / noncompliance /
sanction-triggering interpretation of `a`.

(Corrected 2026-08-11: this block previously cited the namespaces
`Theory.Abstract.JETBridge` / `Theory.Abstract.JETBridgeC1`, which do
not exist — declarations live in `Sanctions.AbstractGame.Params` — and
named `jet_C1_existence_and_three_goals`, which has **no declaration
anywhere in the tree**; it was superseded and survives only in a
past-tense docstring. A sign-convention warning that names a
nonexistent theorem cannot be acted on.) They are retained as the
`ResistanceActionCertificate` family for that interpretation.
Citing those names in a literal-compliance paper claim is a sign
error. Definition-site `⚠ LITERAL-COMPLIANCE DEPRECATION` blocks
were added on each of these in audit-48 / audit-49 so Lean developers
reading the source directly are warned of the sign convention before
citing.

## Non-vacuity status

**DISCHARGED (2026-07-01).** `Sanctions/Examples/EECertWitness.lean`
provides `eeCertCertificate` — the first **complete** instance of the
preferred core certificate `StandardComplianceLocalCoreCertificate`,
at the Eaton-Engers-form witness `eeCertParams` (rally cross-partials
`∂²U_S/∂s∂x = 1 > 0`, `∂²U_T/∂s∂x = 1/10 > 0`; compliance-placates
`∂²U_S/∂s∂a = −11/5 < 0`; strict own-concavity). Every field is
discharged unconditionally and axiom-clean: the Sender high-sanction
margin holds with `β_S·K_S·δ = 4/3 < 8/5 = m_S`, the Target
loss-offset with `c_T = 299/100 ≤ 369/110 = β_T·g_T·δ`, and the
myopic ceiling with uniform slack `1/5`
(`σ_myo(x) = clip(x − 1/5) ≤ max(x, 1/2)` on the basin `[1/10, 1]`).
The unconditional three-goals dominance corollary is
`eeCert_three_goals_dominance`; the full three goals follow from
`eeCertCertificate.three_goals_local_uniform_starts rfl`. The
dominance is substantive: the myopic realized sanction is interior
(`x − 1/5 ∈ (0, 4/5)`) on the basin interior with strict gap
`1 − (x − 1/5) ≥ 1/5` against the forward-looking corner `σ_dyn ≡ 1`.
The earlier minimal `jointPositiveParams` witness (which inhabits
only the lower-level `JointPreferenceBasinTop` Prop) is retained as
the historical minimal example. Two Rule-11 impossibility artifacts
in `Examples/SubstantiveComplianceWitness.lean`
(`substParams_DAU_counterexample`,
`substParams_certificate_senderSide_infeasible`) document why the
witness payoff must be compliance-dependent (Eaton-Engers form): any
compliance-independent `U_S` provably cannot satisfy the
certificate's Sender side.

The five layer aggregators
`Sanctions/{Domain,Foundations,Postulates,Theory,Examples}.lean` are complete:
each imports every module in its folder, and the audit gate enforces both
completeness and the `Domain → Foundations → Postulates → Theory → Examples`
dependency direction. Witnesses, counterexamples, sharpness constructions and
affine dischargers were moved out of `Foundations/` into `Examples/` on
2026-08-27 (Rule 9: a witness certifies a library, so it does not belong inside
it); each moved file declares its role in its header. In particular, `import Sanctions.Theory` pulls in
the complete parametric theory without importing any constructed economy.
-/

import Sanctions.Domain
import Sanctions.Foundations
import Sanctions.Postulates
import Sanctions.Theory
import Sanctions.Examples

-- The paper interface: statements of the main-text results, and their proofs.
import Sanctions.Paper

-- Rule-10/18 headline gate: replays `#print axioms` for every committed
-- headline row on each build (see Sanctions/Headlines.lean).
import Sanctions.Headlines
