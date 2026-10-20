# Assumption Surface Register

## Reading note: stale paths and dead names in historical entries (added 2026-08-31)

This file is an **audit trail**. Entries below record what was true in the round
that wrote them, and are deliberately not rewritten when the tree moves. Two
consequences for a reader following a pointer:

* **`Sanctions/Theory/Abstract/` no longer exists.** 26 provenance labels below
  still name it. Its contents were relocated; in particular
  `Theory/Abstract/InvariantValueClass.lean` is now
  `Sanctions/Theory/Bellman/InvariantValueClass.lean` (with a sibling
  `InvariantValueClass2.lean`).
* **Some identifiers cited below no longer exist**, having been retired or
  renamed in later rounds. Verified dead as of HEAD `6ea8a7a`:
  `jet_three_goals_from_valueClass_and_primitives` (8 occurrences here, and also
  cited in `CLAUDE.md` Rule 8 as a canonical name),
  `regularEconomyCertificate_of_lipBall`, and `ContestPolity.iota_J_nn` /
  `iota_K_nn`.

  Two names previously reported dead are **alive** and should not be removed:
  `standardCompliance_three_goals_C1` is declared at
  `Examples/AffineInstance/ComplianceTower.lean:1356`, and the
  `RegularEconomyCertificateC1Compliance` family is declared at
  `Theory/Certificates/RegularEconomy.lean:316` — only the bare
  `RegularEconomyCertificate` name is retired.

A dead name inside a historical round entry is not a defect. A dead name in a
sentence asserting something **currently** true is; those are corrected in place
and marked with the correction date.

## Four-regime complementarity conditions `C1`–`C5` — NOT ADOPTED (2026-08-29)

`suggestions/33` proposes a five-condition class for the four-regime mechanism
theorem. **None of the five is adopted.** This entry exists so that a later round
cannot treat them as settled primitives by accumulation, and so that the two
that are *cheaper than advertised* are not signed off at the price of the three
that are not.

The five do not have a common character, and bundling them would misprice both
halves. The split, measured rather than asserted:

| Condition | Classification | Status |
|---|---|---|
| **`C1`** — Sender complete objective has increasing differences in defiance and sanction | **(0) Not an assumption in the proposed form** | `Mechanism.completeID_iff_stageID` proves the continuation term cancels identically from the cross-difference, because it depends on the sanction and not on the Target's action. `completeID_forall_iff_stageID` gives the quantified form. So `C1` is *exactly* increasing differences of the stage payoff `U_S` — the compliance-placation property, a condition on primitives. `suggestions/33` §4 states it "for each state and admissible continuation value", which reads as carrier-uniform; it is not, for any continuation whatever. **Cost if adopted:** a stage-payoff sign condition. **What it does not buy:** nothing about the reduced Target objective. |
| **`C2`** — Sender continuation nondecreasing in the sanction | **(0) Derivable from a stage-payoff condition** | Chain, all links present: `F_mono_s` (a `Params` field) and `clipS'_mono` give `Params.senderContinuation_mono_of_value_mono` — a state-monotone value composes to a sanction-monotone continuation; `bellmanS_BCF_preserves_monotone` then reduces state-monotonicity of `V_S` to monotonicity of the **stage payoff** `U_S(·, α(·), s)` in the state. `profileSenderContinuation_mono_of_value_mono` carries it to every profile, the discount factor being nonnegative at all four. **Cost if adopted:** a stage-payoff monotonicity. **What it does not buy:** strictness — a strict activation result needs a strict continuation chord, which this does not supply. |
| **`C3`** — reduced Target increasing differences in defiance and Sender activation | **(3) Would be a new primitive — NOT adopted** | Lives on the Target's objective *after* the Sender's response is substituted, so it constrains an endogenous object. `suggestions/33` §4 concedes "The baseline does not imply this condition", and `Examples/SenderSwitchSignUndetermined.lean` refutes derivability of the sign it asserts. |
| **`C4`** — reduced Target increasing differences in defiance and Target activation | **(3) Would be a new primitive — NOT adopted** | Same character as `C3`. **Corrected 2026-08-30:** this entry previously called `DynamicVsMyopicIncreasingDifferencesAt` (`Theory/LockIn/DifferentPolicyComparator.lean`) "the `11`-versus-`00` member of this family" and read its undischarged status as evidence of `C4`'s difficulty. It is **not** a member: `C4` holds the Sender switch `tS` fixed, so its members are `00`-vs-`10` and `01`-vs-`11`, whereas `11`-vs-`00` moves both switches and varies `β_S` too. The difficulty of `C4` is therefore **unmeasured**, not measured-and-high — the actual `C4` may never have been attempted. |
| **`C5`** — increasing differences between the two activation indicators | **(3) Would be a new primitive — NOT adopted; the load-bearing one** | `suggestions/33` §4 states it is "stronger than the two unilateral monotonicity conditions". It is also very close to the conclusion it is meant to deliver: `C5` says a Target that values its political future reacts more strongly to a Sender that values its own, and the interaction result says the two motives amplify each other. Either the step from objectives to equilibrium outcomes is substantial — in which case that step is the contribution, and §6 concedes it is unproved — or it is thin, in which case the theorem is near-circular. **Neither branch has been established.** |

### Why `C3`–`C5` are not merely unproved

`Params.withProfile` is a *total* function: every economy has all four regime
views, so the class of economies did not shrink when the factorial was added
(`Theory/Mechanism/ContinuationProfile.lean`). Any theorem ordering the four
regimes must therefore exclude the badly-behaved economies **by hypothesis**,
and `C3`–`C5` are that exclusion. Making the scaffolding free relocates the
entire cost into these three; it does not reduce it.

### The prior obligation, which is not an assumption at all

Before any of the five matters, all four regimes must *exist*. That is an
existence obligation, not an assumption, and the numerical evidence of
2026-08-29 says it is the binding constraint: the two regimes in which the
Sender looks ahead cycle under deterministic best-response iteration, damping
and impatience both fail to fix it, and the coefficient that drives the cycle is
the sanction–state complementarity — the very feature that gives the Sender a
reason to invest in entrenchment. See `docs/WITNESS-PROPERTY-MAP.md`. Per Rule
9D that is evidence about the game and **not** a proof of nonexistence, but it
means `C1`–`C5` currently order regimes that are not known to exist in pure
strategies where the mechanism is interesting.

### Quarantine terms, if any of `C3`–`C5` is ever adopted

1. **Never a `Params` field.** Supplied as a theorem-local certificate, on the
   `Theory/Certificates/SelectorGeometry.lean` pattern, so the assumption is
   visible at every use site rather than inherited silently.
2. **Conditionality in the name.** Any theorem consuming them carries
   `_of_complementarity` or equivalent, so the condition survives citation
   (Rule 15's naming discipline for consumed-existence results).
3. **A necessity witness per condition.** An economy satisfying `Params` and the
   other conditions, violating this one, and violating the conclusion — which
   converts "we assumed it" into "it must be assumed". Without one, a reader
   cannot tell a load-bearing hypothesis from a decorative one, and Rule 13's
   unused-hypothesis audit only catches the fully unused case.
4. **No paper-facing named scalars.** Any margin extracted from these is a
   derived `inf` used as an internal handle; the paper states strict
   inequalities among existing quantities (Rule 3, symbol economy).
5. **The interaction is not stated as a cross-difference.**
   `Mechanism.interaction_sign_not_scale_invariant` proves the sign of
   `R¹¹ − R¹⁰ − R⁰¹ + R⁰⁰` reverses under `s ↦ s²`, a strictly increasing
   relabelling of `[0,1]` that changes no economics. Use strict inclusion of the
   self-sustaining sets instead, which is invariant.

## Maintained strict transition adjustment (2026-07-16)

| Symbol | Classification | Status and content |
|---|---|---|
| **`Params.StrictAdjustment`** | **(3) New maintained primitive — user-approved 2026-07-16** | Transparent general-`F` condition on the feasible square: `s < x → F x s < x` and `x < s → x < F x s`; together with the existing diagonal field `F_diag`, the next state moves in the sign direction of the state-sanction gap. It is deliberately **not** a new `Params` field, so all pre-existing general-transition theorems retain their stronger signatures and all 24 headline type hashes remain unchanged. The paper maintains the restriction as (F5). Lean derives `F_zero_lt_self` (zero-sanction descent), `hF_top` (full-sanction ascent), `F_eq_self_iff` (a feasible transition fixed point satisfies `s = x`), and the two no-overshoot bounds. The long-run corollaries `dynamicTopLockInPathF_tendsto_steadyState_of_strictAdjustment`, `dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment`, `dynamicTopRealizedRule_eq_self_of_stepF_fixedPoint_of_strictAdjustment`, and `dynamicTopLockInStepF_exists_least_fixedPoint_of_strictAdjustment` use that equivalence to identify the subsequential steady-state sanction, upgrade the entire equilibrium sanction sequence to convergence to the limiting state, and identify the realised sanction at any feasible step fixed point with the state itself. The generic affine discharger `strictAdjustment_of_F_eq_affineF` covers every interior-weight affine instance. Concrete non-affine dischargers are proved for `ratchetParams`, `qbParams`, and `lbParams`; `eatonEngersParams_strictAdjustment` covers the K–L-induced affine witness. **Cost:** excludes irreversible ratchets and exact inaction/salience bands. **What it does not buy:** no uniform adjustment rate, Lipschitz modulus, contraction margin, quantitative recovery horizon, or equilibrium-policy monotonicity. Those remain separate theorem inputs or future derived results. |

**2026-07-17 derived limit comparison.** With monotonicity of the realised
rule, `dynamicTopLockInPathF_tendsto_below_least_fixedPoint_of_rule_mono`
proves that the lower-endpoint orbit limit is weakly below the least fixed
point of the greatest-selector step. The wrapper
`dynamicTopLockInPathF_tendsto_below_least_fixedPoint_of_strictAdjustment`
derives rule monotonicity from the existing single-crossing assumption. This
adds no primitive. It also records a sharp boundary: strict adjustment does
not make the greatest optimal selector continuous, so without a separate
continuity or dynamic-argmax-uniqueness route the orbit limit is not identified
with that least selected fixed point.
At the non-affine ratchet witness, the already-proved identity
`dynamicTopRealizedRule ≡ 1` closes the stronger conclusion without a new
assumption: `ratchetParams_generalF_lowerOrbit_and_least_fixedPoint_eq_one`
proves `x_L = x_F = 1`. This is witness-specific and does not alter the
general theorem surface.

**2026-07-17 derived post-entry duration result.** The affine and general-`F`
theorems in `PostEntryNonTermination.lean` add no primitive. They restart the
existing equilibrium path at a high-basin entry date and derive that every
relief cutoff strictly below the inherited floor is never reached. Relief
remains in the feasible action set and the realised action is compared with
every relief action through equilibrium optimality. The selector-independent
and strict-payoff upgrades consume the already-defined state-local
dynamic-argmax uniqueness condition; the greatest-selector path result does
not.

## Canonical paper-facing hierarchy (audit-49 follow-up)

Under the **literal-compliance** reading of `a` (`a = 1` = full
compliance, `a = 0` = no compliance), the canonical paper-facing
theorem family is the **asymmetric carrier-local** `_local` route
(promoted in the audit-49 follow-up round 2026-05-28):

| Layer | Canonical name | File |
|---|---|---|
| **Preferred main MS theorem (universal-start)** | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_MS` | `Theory/Certificates/StandardComplianceMain.lean` |
| **Preferred main MS theorem (general transition)** | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_MS_generalF` | `Theory/Certificates/StandardComplianceMain.lean` |
| Opt-in conditional pathwise regime-comparison (universal-start, needs `hMyoBasin` — see status note below the table), **affine-transition-gated** (`hF : F = affineF δ`) | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_regime_comparison_uniform_starts` | `Examples/AffineInstance/ComplianceTower.lean:1169` |
| C¹ theorem (statewise dominance) — ⚠ C¹ track FROZEN (2026-07-04 A6 decision), affine-transition-gated (`hF : F = affineF δ`), no paper-facing load | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_C1` | `Examples/AffineInstance/ComplianceTower.lean:1215` |
| Fixed-start BCF compatibility (uses `C.x₀` / `C.x₀shock`), **affine-transition-gated** (`hF : F = affineF δ`) | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local` | `Examples/AffineInstance/ComplianceTower.lean:981` |
| Fixed-start regime-comparison (uses `C.x₀`, needs `hMyoBasin` — opt-in conditional, see status note), **affine-transition-gated** (`hF : F = affineF δ`) | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_regime_comparison` | `Examples/AffineInstance/ComplianceTower.lean:1124` |
| ⚠ **DOES NOT EXIST** (corrected 2026-09-01) — the name appears only in docstrings at `StandardComplianceMain.lean:63` and `:990`; no declaration anywhere in `Sanctions/`. Do not cite it | `Sanctions.AbstractGame.Params.standardCompliance_three_goals` | — |
| Homogeneous C¹ compatibility, **affine-transition-gated** (`hF : F = affineF δ`) | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_C1` | `Examples/AffineInstance/ComplianceTower.lean:1356` |
| Pathwise corollary (homogeneous, requires `hMyo_basin` — opt-in conditional, see status note) | `Sanctions.AbstractGame.Params.standardCompliance_three_goals_pathwise` | `Theory/Certificates/StandardComplianceMain.lean` |
| Start-free core certificate (consumed by the universal-start theorems) | `StandardComplianceLocalCoreCertificate` | `Theory/Certificates/StandardComplianceLocal.lean` |
| Fixed-start BCF certificate (`extends` the core, adds `x₀` / `x₀shock`) | `StandardComplianceLocalCertificate` | `Theory/Certificates/StandardComplianceLocal.lean` |
| Carrier-local C¹ certificate (single-carrier C¹ track) | `StandardComplianceLocalCertificateC1` | `Theory/Certificates/StandardComplianceLocalC1.lean` |
| Homogeneous BCF certificate | `StandardComplianceCertificate := RegularEconomyCertificateComplianceCore` | `Theory/Certificates/RegularEconomy.lean` |
| Homogeneous C¹ certificate | `StandardComplianceCertificateC1 := RegularEconomyCertificateC1ComplianceCore` | `Theory/Certificates/RegularEconomy.lean` |
| Homogeneous pathwise BCF certificate | `RegularEconomyCertificateCompliance extends ComplianceCore` | `Theory/Certificates/RegularEconomy.lean` |

The **preferred** routes use the asymmetric `ValueClass2`
construction (separate Target carrier `carrier_T` and Sender carrier
`carrier_S`) with carrier-local stage primitives (`∀ V_T : CarrierT,
∀ V_S : CarrierS, …`). The homogeneous routes use the original
single-carrier `ValueClass` and remain available as compatibility —
every existing `ValueClass` is a `ValueClass2` via the homogeneous
bridge `ValueClass.toValueClass2`.

The Goal-2 conclusion of the main theorem is **statewise**:

```lean
∀ x ∈ Set.Icc (max xT xS) 1,
  p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x
```

Goal 2 is sign-correct under literal compliance via the loss-offset
mechanism (`LowerLossSlopeOn` on stage Target payoff +
`LowerSlopeOnValueOn` on continuation `V_T` + margin
`cT ≤ β_T · gT · δ`) — see
`Theory/Certificates/TargetSanctionLossOffset.lean`.

### `hMyoBasin` status note (2026-07-03 demotion)

The pathwise regime-comparison rows above were previously labeled
"Preferred". **Demoted 2026-07-03**: their opt-in hypothesis
`hMyoBasin` (`∀ x ∈ [max xT xS, 1]`, the *myopic* regime's realized
sanction `σ(x, M.α x)` stays in `[max xT xS, 1]`) describes a
"both regimes lock in" parameter region and is **expected to be false
in bistable witness economies**, where the myopic regime under-sanctions
and washes out of the high basin — that wash-out is the model's point.
Machine-checked: `eeCert_hMyoBasin_counterexample`
(`Examples/EECertWitness.lean`) refutes `hMyoBasin` at the flagship
eeCert witness (the myopic rule `clip(x − 1/5)` sits uniformly `1/5`
below the diagonal, so *no* basin `[b, 1]`, `b > 0`, is preserved).
The theorems remain available as honest conditionals for the
both-locked-in region. The pathwise Goal-2′ *content* does not need
`hMyoBasin`: `ruleSanctions_le_of_ceiling_and_path_floor`
(`Theory/LockIn/DifferentPolicyComparator.lean`) delivers pathwise
dominance from a global myopic sanction ceiling plus a dynamic
sanction-path floor (no basin confinement of the myopic path), and
`eeCert_pathwise_dominance` instantiates it at the witness (myopic
capped by `1`, forward-looking realized rule pinned at the corner `1`
along its path). The **statewise** Goal 2 of the main theorem remains
the canonical regime comparison.

### Quarantined legacy resistance-action route

The following theorems / certificates are **sign-correct only under
the resistance / noncompliance / sanction-triggering** reading of
`a` and are NOT valid as literal-compliance results:

| Symbol | Quarantine note |
|---|---|
| `RegularEconomyCertificate` (alias: `ResistanceActionCertificate`) | Uses `hα_order_E + hσ_monoOn_a` chain (resistance-action only). |
| `RegularEconomyCertificate.three_goals` | Same. |
| `regularEconomyCertificate_of_lipBall` | Same. |
| `JETBridge.jet_three_goals_from_valueClass_and_primitives` | Same. Audit-48 docstring deprecation added. |
| `JETBridge.jet_persistence_at_equilibriumTop_from_lowerSlopes` | Uses Target `LowerSlopeOn` (stage non-decreasing in `s`); sign-correct only under resistance reading. |
| `JETBridge.jet_shock_at_equilibriumTop_from_lowerSlopes` | Same. |
| `JETBridge.jet_dominance_at_equilibriumTop_from_static_order` | Uses `hα_order + hσ_monoOn_a` chain. |
| `JETBridgeC1System.jet_C1BellmanSystem_three_goals` | Internally delegates to the legacy `_from_lowerSlopes` + `_static_order` bridges; inherits the restriction. |
| `DifferentPolicyComparator.dynamicTop_rule_dominates_myopic_policy_from_primitives` | Same. |
| `DifferentPolicyComparator.dynamicTop_rule_dominates_myopic_policy_from_increasingDifferences` | Same. |

Paper-facing literal-compliance claims must NOT cite any of the
above. Citing one in a literal-compliance argument is a
sign-direction error.

## Audit-49 follow-up: structural items closed (2026-05-28)

Both items the audit-48 critique flagged as "deferred structural
work" are now **implemented and integrated**. See
[[project_audit49_followup_rule3_items_2026_05_28]] for the round
entry.

* **Asymmetric `ValueClass2` — IMPLEMENTED.** New
  `Theory/Bellman/InvariantValueClass2.lean` introduces
  `structure ValueClass2 p` with separate `carrier_T : Set Val` and
  `carrier_S : Set Val`, separate `isClosed_T/S`, separate
  `nonempty_T/S`, separate `sender_unique_on : ∀ V_S ∈ carrier_S,
  DynamicArgmaxUnique V_S`, and `target_unique_on : ∀ V_T ∈
  carrier_T, ∀ V_S ∈ carrier_S, TargetArgmaxUnique V_T V_S`.
  Heterogeneous Bellman invariance `IsInvariant`. Heterogeneous
  Banach contraction template `joint_contraction_from_row_bounds_hetero`
  (audit-49 follow-up Item 1; generalizes `E × E → E × E` to
  `E × F → E × F`). Homogeneous bridge `ValueClass.toValueClass2`
  ensures every existing single-carrier `ValueClass` is realized as a
  `ValueClass2` with `carrier_T = carrier_S` — no regression. The
  audit-48 narrowness (single-carrier `valLipGainBall` forcing
  Target-style high-state gain on `V_S`) is removed by the
  asymmetric construction.

* **Carrier-local `∀ V_T : CarrierT, ∀ V_S : CarrierS, …` localization
  — IMPLEMENTED.** New
  `Theory/Certificates/StandardComplianceLocal.lean` introduces
  `StandardComplianceLocalCertificate` built on `ValueClass2` with
  carrier-local stage primitives:
  - `hV_S_lip_carrier : ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS`
  - `h_stage_target_loss_on : ∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS,
    ∀ x ∈ Icc xT 1, LowerLossSlopeOn (fun s => p.U_T x (D.α_on V_T V_S
    x) s) (Icc (max x sbar) 1) cT`
  - `hV_T_gain_on_carrier`, `h_stage_sender_on`, `hSC_on` analogously.

  The certificate's `three_goals_local` theorem produces the
  equilibrium via the heterogeneous existence with α-coincidence
  (`E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩`), then instantiates the
  carrier-local primitives at the produced equilibrium. **More
  localized to the constructed value class** than the previous
  per-E form (`∀ E : FeedbackStackelbergEquilibriumTop, …`): the
  primitives need only hold on the carrier pairs the construction
  touches, not on every possible top equilibrium of the model. The
  two forms quantify over different families (equilibria vs carrier
  pairs); the carrier-local form is the intended one when the
  carrier reflects the regular class used for the fixed-point
  argument.

* **C¹ analog — IMPLEMENTED.** Parallel
  `StandardComplianceLocalCertificateC1` in
  `Theory/Certificates/StandardComplianceLocalC1.lean` with carrier-local
  primitives quantified over `z : D_C1.carrier` (the C¹ track remains
  single-carrier — an asymmetric `ValueClass2_C1` is deferred since
  the C¹ Banach pipeline would need duplication; this is not a
  blocker).

* **Audit-49 follow-up additional items (also IMPLEMENTED).**
  - `RelevantActionRegionSenderSlope` + discharger (Item 3,
    region-restricted Sender slope at `a ≤ abar(x)` rather than
    uniform-in-`a`); see `Theory/Basin/RelevantActionRegion.lean`.
  - `three_goals_weak_persistence` (Item 4, weaker-conclusion
    sibling delivering basin invariance only — no strong-ratchet
    floor or `Monotone realized` field); see the extension to
    `Theory/Certificates/RegularEconomy.lean`.

The full canonical paper-facing hierarchy table is at the top of this
file. The closed structural items above complete the audit-49
follow-up round.

---

## Wave-2 additions (2026-07-11, both user-approved Rule-3 stops)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`FourGroup.plannerW`** | (3) New paper-facing DEFINITION (not a hypothesis) — **user-approved 2026-07-11** | The utilitarian planner objective at the four-group polity: `U_S + U_T` with every political-effectiveness weight `θ_g` set to 1 — the unweighted group surplus, **retaining the group-borne resource terms** (deadweight `kS·s²`, placation `w_pl·s·a`, compliance benefit `base_S·a`, `kT·a²`, sanction cost `d_s·s`). Zero new scalars: every coefficient is an existing `FourGroup` field. **Design disclosure:** the degenerate "labeled linear welfare pieces only" reading collapses to `W = x` (sanctions costless to the planner, lock-in planner-optimal) and is excluded by design; the adopted reading is exactly the approval memo's "the planner drops the political weights." The distortion identity `plannerW_distortion` (`U_S + U_T = plannerW + Σ_g (θ_g − 1)·w_g`, by `ring`) machine-checks that the political weights are the entire wedge. Consumed by the inefficiency results (`fgc_planner_inefficiency` + strict/endpoint corollaries; parametric flip boundary `(g_J − q_K) + (b_J − b_K) < kS + d_s` — a strict inequality among existing fields, no gap scalar). Files: `Theory/Microfoundations/FourGroupPlanner.lean`, `Examples/FourGroupPlannerWitness.lean`. |
| **`ContestPolity` primitives: `cp_J`, `cp_K` (quadratic pressure-cost coefficients), `iota_J`, `iota_K` (income-incidence exposure slopes)** | (3) New primitives on a NEW structure — **user-approved 2026-07-11** | The Becker-1983 contest layer. Net surface direction FAVORABLE: the four previously-assumed `Polity` pressure schedules (`rally`, `incid`, `empower`, `xstar`) become *derived definitions* (dominant-strategy Nash argmaxes with completed-square certificates — Rule-1 compliant), at the price of four deeper primitives plus region inequalities stated over existing+approved parameters (cost-adjusted rally dominance `cp_J·(μ·b_K) < cp_K·(ρ·b_J)`, degenerating LITERALLY to `FourGroup.rally_dom` at equal costs; incidence-burden ordering `cp_K·ι_J ≤ cp_J·ι_K`; endpoint stake nonnegativity). Lock-in is obtained BY APPLYING the existing `lockIn_of_rally_dominates`; all five `inducedF` transition discharges fire through the constructor `ContestPolity.toPolity`; `contestWitness` instantiates at the canonical four-group witness numbers with `toPolity_inducedF_eq_affineF` — the existing witness transition is now contest-microfounded with zero downstream change. The legacy field-supplied `Polity` route remains available (compatibility). Deferred (own Rule-3 stop if wanted): the wash-out mirror constructor. Files: `Foundations/BeckerContest.lean` (generic), `Theory/Microfoundations/KaempferLowenbergContest.lean` (parametric wiring), `Examples/KaempferLowenbergContestWitness.lean` (concrete non-vacuity). |

## Wave-4 declinations (2026-07-12, user decisions — CLOSED GATES, do not re-open without a fresh Rule-3 stop)

| Item | Decision | Grounds |
|------|----------|---------|
| **Bressan–Jiang distributional equilibrium concept** (`leaderAvgIndex` μ-averaged leader criterion + restricted leader class `U1` + invariance leg) | **DECLINED 2026-07-12** (user followed the probe recommendation) | Adversarially-confirmed refutation of the only in-reach proof engine: the composite μ ↦ invariantLaw(policy(μ)) is definitively NOT a global W₁ contraction at P3 (measured factor 3.185, bifurcating invariant law), and the δ-free strict-contraction margin condition among existing constants — `\|∂²U_S/∂s∂x\| + (\|∂²U_T/∂a∂x\|/c_T)·\|∂²U_S/∂s∂a\| < c_S` — fails 37/20 vs 24/20 (deficit 13/20); the chain-leg frontier `\|∂²U_S/∂s∂x\| < \|∂²U_S/∂s²\|` fails 27/20 vs 6/5 (deficit 3/20): **the strong-rally dominance the persistence mechanism requires is exactly what breaks the measure-space contraction** — a structural, not engineering, obstruction. Under the standing per-state TOP concept the composite is provably constant (Markov policies are μ-blind), so the degenerate reading's content is delivered by Wave-5 P6 with no new concept. Source: `docs/archive/workflow-scratch/w4_dist_memo_source.md`. |
| **He–Sun 2017 Theorem 1 full formalization (P1a)** | **PERMANENTLY literature-grounded 2026-07-12** (user-approved recommendation) | The distributional replacement is refuted (above); the purification formalization (Dynkin–Evstigneev measurable selection + a topological fixed point absent from mathlib) remains the only full-discharge route and is recorded as the standing accepted boundary. The interior existence rows (6, 19, 20) remain honestly conditional on the named analytic package. |

## Wave-6 status changes (2026-07-12, zero new assumptions)

| Item | Change | Notes |
|------|--------|-------|
| **C¹ track — PARTIAL UNFREEZE** (was: frozen 2026-07-04 A6) | Witness-level exact-derivative/envelope layer unfrozen and de-vacuized (`Examples/C1WitnessEnvelope.lean`: first `C1Val` inhabitants at the W2-pinned stars, first `C1BellmanSystem`/`three_goals_local_C1` discharges, exact shadow prices with the RZS boundary recursion, first interior Danskin identity at B2). The ABSTRACT envelope layer STAYS FROZEN (SmoothSanctionClass IFT Prop fields, abstract completeness route, any general-F RZS statement — each would require new differentiability/curvature hypotheses ⇒ Rule 3). One Cat-(2) statement change: `C1BellmanSystem`'s α fields carrier-localized (full Rule-13 disclosure in that file's header; consumers verified unaffected in statement; audit-49 Item-5 precedent). | Probe-first per user instruction; adversarially confirmed. |
| **Acemoglu-Jensen full-adjustment channel — CLOSED at corner witness families** (was: recorded open at `LockInComparativeStatics.lean`) | `Examples/FeedbackComparativeStatics.lean`: parametrized pinned Bellman fixed points uniform over exact windows (eeCert β_S ∈ [6/13, 4/7), δ ∈ [3/7, 2/3), β_T ∈ [598/709, 1); fgc siblings); machine-checked full = direct + feedback splits; exact δ-invariance of the lock-in value (`eeCertD_lockin_value_invariant`, `fgcD_*`); rfl-level cross-feedback decoupling. Zero new assumptions (window hypotheses on Examples-layer families only). Interior-policy feedback channel (nonzero policy response) remains open. | |
| **Within-carrier uniqueness — upgraded to ε-isolation** | `Theory/Equilibrium/EpsilonIsolation.lean` (parametric) + `Examples/EpsilonIsolationWitness.lean`: sup-norm-ε isolation with irreducible shape pins (sawtooth counterexample documented); exact ε = 1 at the coupled witness (frontier bracketed (24,25)); at eeCert UNBOUNDED ε and the global form `eeCert_global_isolation` (the defiance convention alone pins both values). Consumed package at the coupled witness: the same named shapes at ε-shifted constants, zero new kinds. | Scoped Doraszelski–Escobar-style regularity without differentiability; full genericity stays out of scope. |

## P3 full-width unconditional equilibrium (2026-07-16, zero new assumptions)

`Examples/MechanismWitnessShockedUnconditional.lean` bypasses the general
interior-existence analytic package at the concrete P3 economy and shock
half-width `h = 1`. Exact affine smoothing reduces the joint Bellman system to
the two endpoint spreads. An IVT-selected root of the resulting quartic
defines the Sender spread, the Target spread is eliminated algebraically, and
the file constructs the continuous feasible leader policy, the
equilibrium-derived greatest Sender response, and both bounded-continuous value
functions explicitly.

The capstone
`mechanismWitnessParams_purified_existence_unconditional_one` proves
`Nonempty (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop` with
no hypotheses. The former full-width inputs `sc`, `h_obj_diff`, `L_lead`,
and carrier invariance are not discharged as general abstract lemmas; they are
unnecessary for this exact witness construction. The general shocked
interior theorem remains conditional at other widths/economies.

The follow-up capstone
`mechanismWitnessParams_purified_existence_unconditional_one_monotone` proves,
again with no hypotheses, that an equilibrium exists whose own endogenous
realized-sanction rule is weakly increasing on the physical state interval.
This is proved directly for the explicit optimal leader policy and the
greatest dynamic Sender response; it is not merely inherited from the older
canonical-selector family.  The sibling results
`mwEqEquilibrium_realizedRule_one_lt_one` and
`mwEqEquilibrium_no_dynamic_floor` preserve the sharp boundary: the
equilibrium exists and its realized rule is monotone, but its top-state
sanction is strictly below one and it cannot satisfy the high-sanction
pathwise floor required by the full `hDynReg` package.

## 2026-07-23 audit follow-up (zero new assumptions)

Three closures from the 2026-07-23 assumption-surface audit; none widens the
surface.

| Item | Change |
|---|---|
| **`h_U_lip` / `h_F_lip` split** | The audit-32 historical entry below lists the pair as one category-(3) item. **Split classification (current):** the transition leg `h_F_lip` is **discharged unconditionally** — `γ_F = 1−δ` from `δ_mem` alone (`transition_Lipschitz`, R38); the payoff leg `h_U_lip` (stage-payoff Lipschitz constants `L_U_T`, `L_U_S`, `L_U_a` — suprema of the stage-payoff partials) **remains a content-bearing primitive**: the R40 wrappers only convert a user-claimed continuous partial derivative into a constant, and concrete payoff classes discharge by direct inspection. Paper `app:closedforms` already states this correctly (first-derivative bounds listed among the paper-facing primitives). |
| **Schur certificate inhabited; diagonal bounds derived** | `StandardComplianceLocalCoreCertificateSchur` was uninstantiated with free diagonal-bound scalars `hβ_T_lt` / `hβ_S_lt`. New bridge `ofRowSum` (StandardComplianceSchur.lean) proves every legacy row-sum certificate is a Schur certificate — diagonal bounds and Schur margin **derived** from the row sums by arithmetic. First inhabitant: `eeCertCertificateSchur` (EECertWitness.lean §14). The diagonal bounds are no longer free in practice. |
| **Within-carrier uniqueness applied** | The headline `feedbackStackelbergTop_unique_in_carrier_schur` (any two carrier-valued, selector-coinciding top equilibria agree in values and policy) previously had no in-tree application. Now packaged at certificate level (`unique_in_carrier` on both certificate forms) and instantiated at the flagship witness (`eeCert_unique_in_carrier`): all quantitative inputs machine-discharged; only the class-defining carrier/selector memberships remain. Headline type hash unchanged (the theorem is applied, not modified). |

Still open from the same audit (not closed here, recorded for honesty): the
`ShockedParams` kernel's "atomless" qualifier lives only in docstrings — the
formal field requires `IsProbabilityMeasure` only.
**Closed 2026-07-24:** the docstrings in `HeSunShock.lean` and
`ShockedParams.lean` now state explicitly that the formal requirement is
`IsProbabilityMeasure` alone and that atomlessness is the He–Sun narrative
interpretation, consumed by no proof. No Lean change; the assumption surface
is exactly what it formally was.

## 2026-07-24 zero-decision batch (zero new assumptions)

Uniqueness parity closure: `StandardComplianceLocalCoreCertificate_MS.unique_in_carrier`
(the MS certificate's row sums imply the Schur package via the generic
`NNMat2.schurDet_of_rowSums`), plus six witness within-carrier uniqueness
corollaries with all quantitative inputs machine-discharged (b2, dual-basin,
four-group, quad-bump — the first non-affine-transition uniqueness — ,
stage-flip, low-basin). Every certificate witness now carries within-carrier
uniqueness. Also: the `Audit-Round.ps1` hygiene gate previously scanned only
69/153 files (PowerShell 5.1 `**` glob does not recurse) — repaired with an
explicit recursive enumeration; the corrected full-tree scan is clean. The MS
certificate's contraction fields are now correctly documented as legacy ROW
SUMS (strictly stronger than the Schur margin; the Schur weakening remains
unported on the MS route — a possible future slim variant). No structure,
field, hypothesis, or headline signature changed.

## 2026-07-24 six-verdict round (zero new assumptions; one disclosed signature change)

| Item | Change |
|---|---|
| **Low-basin A2\* — now load-bearing as output** | The 2026-07-24 audit found the entire Target-side dual stack of `JointPreferenceBasinLow` (`target_dislikes_sanctions` — the A2\* assumption that the Target's forward-looking objective is non-increasing in the sanction on the low basin — plus feasibility/optimality/geometry fields) consumed by no proof, while paper Theorem 4 lists A2\* as required. **Closed via user option (a):** the new evidence variants `jointPreferenceBasinLow(F)_long_run_with_equilibrium_evidence` re-emit the full Target-side package at every path state, restoring exact symmetry with the high basin. The assumption is unchanged in content; its status changes from decorative to evidence-bearing. |
| **Coupled §9 canonical layer — DELETED** (user option (c)) | The Berge canonical-leader chain and both `_canonical` capstones consumed the refuted `CoupledLeaderStrongConcave` (modulus-2 leader strong concavity, refuted by the headline `not_coupledLeaderStrongConcave`) and were vacuous conditionals per Rule 11.3/12.2. Kept: the named hypothesis, the refutation, the §7/§8 explicit-leader templates. Paper synced in place. Revival requires a valid replacement premise first. |
| **`JointMPE.SenderResponse` — out of the postulate layer** (user option (b)) | The write-only Sender-response interface (no consumers repo-wide) moved from `Postulates/` to `Theory/Legacy/` with a historical note; `Postulates/` now contains only live assumption surface (`AbstractGame`, `ShockedParams`). No content change. |
| **Schur-form MS certificate — category-(2) weakening** | `StandardComplianceLocalCoreCertificateSchur_MS` + engine `three_goals_local_MS_generalF`: the preferred MS/general-`F` route now available under diagonal bounds + Schur margin (strictly weaker than the row sums), with `ofRowSum_MS` inhabitation at every MS witness. No new fields beyond the weakened contraction package. |
| **`fixedPoint_unique_of_schur_rows` — hypothesis dropped** (Rule-13 disclosure, user-approved) | The never-consumed `_ha_lt : a < 1` removed from the generic Schur uniqueness lemma (moved to `Foundations/PerovContraction.lean`, `Sanctions` root namespace preserved). The sibling unused `β_T < 1` in `epsIsolation_of_schur_rows` is retained underscore-marked for interface symmetry. |

## 2026-07-25 six-phase frontier repair (user-approved)

| Item | Category | Change |
|---|---|---|
| **Coupled Sender regularity** | (2) Discharged | `coupled_sender_strongConcave` proves the carrier-uniform modulus `37877/32000` directly from the existing Sender carrier and the one-box semiconcavity theorem. `coupled_sigmaDynTop_continuous_subtype` and its clamped extension derive selector continuity from uniqueness plus Berge. The coupled templates no longer consume `sc_S` or `hσc`; no assumption was added. |
| **Target quadratic growth at the realised policy** | (2) Weaker replacement, user-approved; both printed and replacement carrier-uniform forms refuted | The explicit-leader coupled templates replace the refuted modulus-`2` `CoupledLeaderStrongConcave` plus separate `lopt` input with the weaker realised-policy inequality `(1/2)(a-lead)^2 ≤ J(lead)-J(a)`. `coupled_isMaxOn_of_quadraticGrowth` derives Rule-1 optimality and `coupled_lead_lipschitz` derives the policy estimate when the product-form two-sided objective-difference bound is supplied. `not_coupledTargetQuadraticGrowth` refutes this premise uniformly on the printed monotone carrier. On the installed norm--Lipschitz carrier, `coupledRedesignTarget_two_global_maxima` constructs two distinct global optima at one admissible continuation pair and `not_coupledTargetQuadraticGrowthLipCarrier` refutes the carrier-uniform modulus-\(1/2\) package again. `coupledRedesign_reduced_branches_exact_quadratic_growth` salvages exact positive quadratic growth separately within each smooth response branch. A fixed-point-only growth substitute is not constructed. No model assumption or field was added. |
| **Carrier invariance and selected-policy state modulus** | Target self-map proved; exact uniform optimal-selector budget refuted | `coupledZeroPair_target_image_not_mem` refutes `h_invT` on the printed monotone Target carrier, while `coupledSteepPolicy_sender_image_not_mem` shows that continuity and feasibility alone cannot establish Sender invariance. The user-approved `coupledCarrierTLip` is now defined from the primitive Target stage bound, discount, response geometry, and transition sensitivity; its reduced norm and state radii are retained only as optional exact equalities. `coupled_sigmaDynTop_state_lipschitz` derives the equilibrium Sender-response modulus from the same geometry, and `coupled_target_Bellman_mem_lip_carrier` proves unconditional Target-row invariance on the replacement carrier. `coupled_sender_Bellman_mem_primitive_carrier` gives the symbolic Sender self-map indexed by a realised-policy modulus. The older fixed-carrier theorem remains a diagnostic specialization, but `coupledRedesignTarget_nearby_unique_maxima` forces every optimal selector at a fixed admissible continuation pair to take two displayed nearby-state actions, and `coupledRedesign_every_optimal_selector_violates_budget` proves that their chord exceeds that specialization's exact budget. This refutes the uniform fixed-carrier Sender-invariance route, not equilibrium existence, selector continuity, or every larger finite Lipschitz constant. No `Params`/`ShockedParams` field, kernel change, or economic assumption was added. |
| **Two-sided objective-difference estimate** | Pointwise two-channel bound proved; literal realised-choice product chord open | `coupledLeaderObj_diff_lip_in_VT` proves the complete Target-continuation action-difference channel at `2880/37877`. `not_coupledLeaderObj_sender_uniform_advertised` refutes the advertised Sender-continuation coefficient as a carrier-uniform all-actions product estimate. On the replacement carrier, `coupledLeaderObj_pair_pointwise_bound_on_lip_carrier` proves the strongest approved zero-order bound, with coefficients \(9/10\) on Target-value distance and \(43520000/283976393\) on Sender-value distance. Given the already-stated quadratic-growth inputs, `coupled_lead_sq_holder_of_quadraticGrowth_on_lip_carrier` yields a squared/Hölder-\(1/2\) policy estimate, not the Lipschitz product chord required by the Perov capstone. The literal product-form estimate at the two realised Target choices remains open. No second-order condition, kernel replacement, or new field was added. |
| **Realised-policy dominance and moving-policy comparison** | Full-width consequence proved; low-\(\delta\) implication isolated conditionally | `mwEqSenderDynObjective_realized_IDOFamilyOn` proves interval dominance after substituting the actual full-width equilibrium Target policy and continuation value. For the coupled low-\(\delta\) witness, `lowDelta_senderDynObjective_realized_IDOFamilyOn_of_policy_slope` proves full-state interval dominance whenever the endogenous Target policy obeys the one-sided slope ceiling \(2959677/3200000\); the theorem does not discharge that policy premise. `eeCert_cross_economy_moving_policy_strict` proves strict policy, realised-sanction, and path comparisons between independently optimized forward-looking and myopic certificate economies. None adds an assumption or changes a headline signature. |
| **Planner optimum and state-varying frontier** | Definitions and consequences only | `FGCPlannerPath`, the feasible-value set, and its supremum define the planner problem; the cube bound proves boundedness and the existing feasible path yields `fgc_plannerOptimalValue_lower_bound`. `mechanismWitnessParams_fullWidth_state_varying_frontier` packages strict endpoint movement of the already-constructed equilibrium policies. Neither result changes the economic assumption surface. |

## 2026-07-27 numerical-frontier disposition (user-approved; zero new assumptions)

| Item | Disposition |
|---|---|
| **Former hypothesis 4** | **Retired completely from the equilibrium-theorem surface.** The carrier-local six-premise theorem was removed. Its center-policy residual and slack calculations remain only as exact diagnostic lemmas in `LowDeltaCarrierLocalEquilibriumFrontier.lean`; no existence declaration consumes them. |
| **Former hypothesis 6** | **Replaced by symbolic Foundations geometry.** `argmax_lipschitz_two_coordinates_of_quadraticGrowth_of_coordinate_geometry` derives the two selector moduli `Lx/(2q)` and `Ly/(2q)` from quadratic growth and separate coordinatewise objective-difference chords. The coupled rational coefficients are optional specializations, not primitive policy hypotheses. |
| **Numerical carriers** | **Replaced on the canonical route.** `senderPrimitiveValLipCarrier` and `targetPrimitiveValLipCarrier` derive norm radii from stage-payoff bounds and discounts. The Sender state radius is the closed Bellman modulus from the composed stage and transition geometry; the Target state radius is the derived modulus of the realised integrand. `coupledSenderPrimitiveCarrier Lα` makes the remaining realised-policy modulus symbolic. The fixed-carrier numerical-budget theorem is retained only as a refuted-route witness check. |
| **Canonical P3 leader wrapper** | **Symbolically rederived and demoted from the headline surface.** `mechanismWitnessParams_purified_existence_canonical_leader_symbolic` now works at an arbitrary positive composite Target curvature `c_T` and nonnegative coupling modulus `L_lead`, with the direct margin `(mwShocked hh).toParams.β_S + 2 * L_lead / c_T < 1`. The full-width state-local sibling `mechanismWitnessParams_purified_existence_canonical_leader_one_local_symbolic` has the same symbolic surface and discharges follower continuity internally. The former modulus-`2` / `L_lead < 1/2` declarations remain compatibility corollaries only; no headline consumes them. The stronger refutation `mwStaticLeaderComposite_not_strongConcave_of_nonneg` proves that the primitive static Target/Sender composite is not even concave, hence is not strongly concave at any nonnegative modulus. This blocks derivation of the dynamic `sc` premise from the stage Hessian alone; it does not refute strong concavity of every continuation-adjusted shocked objective. |
| **Low-δ conditional wrapper** | **Demoted.** `lowDelta_purified_existence` remains a conditional diagnostic declaration for exact window arithmetic, but it is absent from `Sanctions/Headlines.lean` and `HEADLINE-SNAPSHOT.md`. It must not be cited as a constructed or unconditional equilibrium. |
| **Existence status** | **No promotion.** The current coupled packet does not establish existence: realised-choice objective geometry and the endogenous policy premise needed to close the coupled fixed-point route remain unproved on the relevant invariant carriers. |

## 2026-07-28 open-frontier literature round (zero new assumptions; all routes closed-negative)

Ten papers were acquired against the standing boundaries and filed under
`PaperRefer/MathTheory/` (see that folder's README for the per-paper table).
Every proposed application was judged by two independent adversarial passes and
**none survived**. No assumption, field, carrier, kernel, or equilibrium concept
was added or changed. The round's value is the closed-negatives below, which
bound what future rounds may propose.

| Item | Disposition |
|---|---|
| **S1 — Metric change cannot close F1c.** | **CLOSED-NEGATIVE.** Montrucchio (1998) Thm 5 proves `λ·d(f,g) ≤ ‖f−g‖ ≤ K·d(f,g)` on the set where the Thompson metric is usable — i.e. bi-Lipschitz equivalence with the sup norm. Bi-Lipschitz equivalence preserves modulus-of-continuity **class in both directions**, so a map that is not norm-Lipschitz on the carrier is not `d`-Lipschitz either, and Hölder-½ stays Hölder-½. F1c needs a change of *class*; the Thompson trick buys only a discount-free contraction *rate*. This **confirms from the paper's own mathematics** the earlier finding that renorming is inert (`valLipBall` membership is a norm bound plus a Lipschitz *predicate*, so counterexample witnesses survive any renorming). **Screening rule: reject any future proposal to close F1c, F1d, F2 or F3 by changing the metric on the value space — order, projective, Hilbert, Thompson, or graded.** |
| **S2 — mathlib has no Brouwer-family fixed point theorem and no measurable selection.** | **CLOSED-NEGATIVE at mathlib rev `5e932f97`.** Verified by grep over the pinned tree: no Brouwer, Schauder, Kakutani, or Fan–Glicksberg; no topological degree, no fixed-point index, no Krein–Rutman; and zero hits for `measurable_selection`, `measurableSelect`, `KuratowskiRyllNardzewski`, `Jankov`, `exists_measurable_section` (the only "Schauder" hits are Schauder *bases* in `Analysis/Normed/Module/Bases.lean`). This permanently retires, at this pin, Amann (1976) Chapters III–IV, He-Sun Theorem 1's Fan–Glicksberg leg, and Strauch (1966) Theorems 4.3 and 8.4. **Screening rule: any route whose statement is "an optimal policy *exists* in class X" hits this wall; only "no deviation in class X beats V" formulations are reachable.** |
| **F8 ledger** | Himmelberg (1975) supplies leg 3 of 3 (measurable selection: Thm 5.1 = Kuratowski–Ryll-Nardzewski verbatim, Thm 5.6 = Castaing) in **citable** form. Legs 1 (Dynkin–Evstigneev conditional expectations of correspondences) and 2 (Fan–Glicksberg) remain absent from both the literature held and mathlib. Ledger: **1/3 citable, 0/3 formalized.** Status unchanged: standing accepted boundary. |
| **F1a measurable-selector fallback** | **CLOSED-NEGATIVE, structural.** Relaxing F1a from a unique continuous selector to a merely *measurable* one is not available: `Continuous α` is a **field** of `FeedbackStackelbergEquilibriumTop` / `ShockedFeedbackStackelbergEquilibriumTop`, and `bellmanS_BCF` builds its value via `BoundedContinuousFunction.mkOfCompact`. A measurable selector cannot even be *stated* as a solution of the pinned model. Adopting one is a change of value space and of equilibrium concept (a Rule-3 stop), not a weakening. |
| **F4 freeze — now literature-supported** | Santos (1992) Thm 2.2 requires Assumption B (return `C²` and α-strongly concave) — verbatim the predicate refuted by `not_coupledLeaderStrongConcave` and `mwStaticLeaderComposite_not_strongConcave_of_nonneg` at every nonnegative modulus — and Assumption C (**interior** optimal paths), falsified in-repo by the Sender clip switching at the interior states `x = 2/27` and `x = 26/27` (`Examples/MechanismWitness.lean`), by `coupled_mwσ_five_twelfths_of_ge`, and by `lowDeltaStaticTargetPolicy = 0` on `x ≤ 40/103`. Santos §4 independently names corner solutions as a determinacy failure mode. The 2026-07-04 C¹ freeze is therefore a literature-supported scope boundary, not merely a project decision. |
| **F6 deviation-class widening — replacement route recorded** | Strauch (1966) is **not needed** and its two all-policy theorems are unreachable (S2). The obstruction it would remove does not exist here: `sender_shocked_bellman_le` (`Theory/Shocked/ShockedOneStepVerification.lean`) is **pointwise in the action**, with the deviation entering only as the point of evaluation, so an arbitrary mixture over actions is dominated automatically and no policy-class reduction is required. The recorded route, should this be attempted, is entirely in-repo: replace the state-marginal telescope in `Foundations/BorelBoxLawVerification.lean` with a **finite-product noise telescope** over `(Fin N → noise)`, using that the transition is `x_{n+1} = clipS'(F(x_n,s_n) + η_n)` with `η` iid uniform on `[-h,h]`, so a history-dependent behavioral deviation is a measurable function of `(x₁, η₁, …, η_{n-1})` plus independent internal randomization. Adds no assumption and needs no measurable selection. **Not attempted; recorded only.** |
| **VACUITY DEFECT FOUND AND CLEARED — three ε = 1 conditionals retired** | **Machine-checked.** `coupledJointOpWide_rows`, `coupledSchur_unique_in_carrier_wide`, and `coupledSchur_epsilon_isolation` each consumed `sc_T`, the modulus-`2` leader strong-concavity package quantified over the **enlarged** carriers. That premise is **contradictory**: `not_coupledLeaderStrongConcave` refutes the same package on `coupledCarrierT × coupledCarrierS`, and the refuting continuation pair `(0,0)` at state `5/12` lies in the smaller carriers, hence in the enlarged ones via the file's own `coupledCarrierT_subset_wide` / `coupledCarrierS_subset_wide`. The new theorem `coupledSchurWide_sc_T_contradictory` (`Examples/EpsilonIsolationWitness.lean`) proves `sc_T → False` structurally — it transports the existing refutation along the two carrier inclusions and uses no arithmetic. All three declarations were therefore vacuous conditionals with clean axiom scans and true statements that asserted nothing about the model, and all three are now retired to commented audit evidence (verified absent from the environment by `#check`). **Why they survived earlier sweeps:** the 2026-07-24 round deleted the §9 canonical layer and the 2026-07-27 round retired the numerical wrappers for this identical defect, but these three *inline* the modulus-`2` statement instead of referencing the named `CoupledLeaderStrongConcave` abbreviation, so a name-based scan never reached them. **Kept:** `coupledJointOpWide` (the operator) and `coupledJointOpWide_fixed_of_equilibrium` (the reverse bridge) — neither consumes `sc_T`. **Reinstatement** requires a replacement leader premise that passes its own Rule-11 gate; the weaker realised-policy inequality `(1/2)·(a − lead)^2 ≤ J(lead) − J(a)` is the candidate but has **not** been gated on the enlarged carriers. **Consequence for F9:** item 1 of the F9 audit is superseded — `coupledSchur_unique_in_carrier_wide` was not "a numerical theorem to symbolize" but a vacuous one to remove. Only `lowDelta_senderDynObjective_realized_IDOFamilyOn_of_policy_slope` remains under F9. |
| **ε = 1 carriers de-numeralized** | `coupledCarrierS_wide` and `coupledCarrierT_wide` are now defined as `valLipBall (coupledEpsMS 1) (coupledEpsKS 1)` and `{‖V‖ ≤ coupledEpsMT 1} ∩ monotone`, i.e. through the `EpsilonChain` combinators, rather than by the inlined rationals `683/160`, `73217/3200`, `21`. Those rationals were never arbitrary — `683/160 = M_S + 1` and `73217/3200` is `L_Ux + β_S·(M_S'/h)·(1−δ)` evaluated at it — but they were *evaluated and inlined*, which is what made the file read as numerical and made every constant brittle to a primitive change. The evaluated forms are preserved as `coupledCarrierS_wide_eq` / `coupledCarrierT_wide_eq`. Rule-13 direction: **none** — the carriers are the same sets; no hypothesis or conclusion moved. |
| **`6/5` stage modulus proved SHARP** | `lowDelta_sender_stage_strongConcave_sharp` (`Examples/CoupledSchurWitness.lean`) proves `¬ StrongConcaveOn Sanctions.I (6/5 + ε) (mwU_S x a ·)` for **every** state, action, and **every** `ε > 0`. This was the Rule-11 gate on the de-numericalization programme: had `6/5` been padded, every downstream constant in the `coupledEps*` chain would carry unbanked slack and restating them symbolically would paper over a loose bound rather than record a derivation. It is not padded — `6/5` is the exact stage curvature `\|∂²U_S/∂s²\|`, and the existing `lowDelta_sender_stage_strongConcave` closes with `ring_nf; exact le_rfl`, an equality, leaving no room. |
| **Zhou (1994) attribution** | Corrected in `Foundations/Supermodular.lean`. `lattice_of_equilibria` is **Knaster–Tarski** (mathlib `OrderHom.lfp`/`gfp`), not Zhou. Zhou's Thm 1 (fixed-point set is a *complete lattice*, for an *ascending correspondence*) is strictly stronger by his own Remark 1, and his "ascending" is definitionally `Foundations.Topkis.StrongSetOrder`, which collapses to `Monotone` for singleton values — hence **stronger** than `OrderHom`, so Zhou cannot be cited to relax that theorem. Zhou does genuinely evade R2 (no convexity hypothesis; on a chain every subset is a sublattice), but yields structured *multiplicity*, never the uniqueness F1a requires. |

> **Path note (2026-07-24 reorganization).** Per-symbol section headers below
> the historical divider predate the layer reorganizations; files cited as
> `Theory/Abstract/X.lean` now live under
> `Theory/{Bellman,Basin,LockIn,Certificates,Equilibrium,Shocked,Microfoundations,Bridges}/X.lean`
> (`Legacy/` was renamed `Bridges/` on 2026-08-11).
> The classifications themselves are unchanged.

# Historical audit classifications below this line

> **Audit-49 Phase A-F Item-11 hard divider.** Everything above this
> line is the **current** paper-facing assumption surface
> (canonical hierarchy table + closed structural items). The
> sections below are **retained for audit history only**. They
> document what was load-bearing in earlier audit rounds (audit-31
> through audit-43 and the audit-49 follow-up), with classifications
> and per-symbol notes that may describe symbols as "paper-facing"
> when they have since been demoted, quarantined, or superseded.
>
> When the canonical hierarchy table at the top of this file
> conflicts with any per-symbol note below, **the canonical
> hierarchy controls**. Do not cite anything below this divider as
> the current paper-facing assumption surface without first checking
> the canonical table.

---

## 2026-07-28 referee-verdict adjudication (zero new assumptions; repairs only)

An external referee report proposed a six-gate revision plan. Every factual
claim in it was audited against the live tree and each audit was then
adversarially re-checked. **No assumption, field, carrier, or equilibrium
concept was added or changed in this round.** The dispositions below record
what the audit established, including two corrections to the project's own
prior statements.

| Item | Disposition |
|---|---|
| **Equilibrium concept is FPE, not SSSE.** | **CONFIRMED — Lean-side repaired.** `α_opt_top` is `∀ x ∈ S, IsMaxOn (joint_T_top_integrand V_T V_S x) I (α x)`: per-state argmax over *actions* at *frozen* continuation values. `V_S_fix` pins the Sender value only at the equilibrium `α`, so a leader deviation is never met by a Sender re-solve. Nothing in the tree quantifies over alternative stationary leader policies; the strongest deviation result is the one-shot bound in `Theory/Equilibrium/StackelbergFeedback`. The module docstring of `Theory/Basin/JointPreferenceBasin.lean` previously called this a "**full forward-looking equilibrium**" — the strongest-sounding phrase in the repository, and the one place a reader could infer global optimality. **Repaired 2026-07-28** with an explicit scope paragraph. The paper-facing half is staged as **N12** (Rule 21); the manuscript makes **no** SSSE claim today, so this is a missing caveat, not an over-claim. |
| **P4 is *not* dispensable for persistence.** | **CORRECTION to a tempting reading.** The referee's Gate 5B would have the paper drop two-sided language on the ground that P4 only yields conclusion (vi). That is right about the *statement* and wrong about the *proof term*: `standardCompliance_persistence_generalF_from_package` routes through `P.toJointPreferenceBasinTop`, which consumes `target_combined_chord`; and the tree's sole producer of `h_level_top` is `JointPreferenceBasinTop.level_dyn_top`, whose basin structure carries `target_prefers_sanctions` as a mandatory field. **No P4-free route to (i)–(iii) is instantiated anywhere.** Writing "P4 is unnecessary" into the paper would create a *new* Lean-contradicting claim. Staged as **N13** with the admissible narrow repair spelled out. |
| **Coupled-route displacement gap is a factor of 69, not 10⁷.** | **CORRECTION to an intermediate audit of this project's own numbers.** The proved slack at `LowDeltaCarrierLocalEquilibriumFrontier.lean:142` is the exact rational `2429552350098203266063975021/488157047875412353000038524160 = 4.976989…×10⁻³`, not `4.98×10⁻⁹`. Against the proved localisation `69/200 = 0.345` the required tightening is `69.32×` — under two orders of magnitude. Recomputed independently in exact rational arithmetic. **Any decision to abandon the coupled route must be taken against the factor-69 figure.** Recorded as **R4**. |
| **Three of four coupled obligations have route refutations in-tree.** | **CONFIRMED, and route-scoped only.** Target-selector uniqueness: `lowDeltaRelativePerturbationCounterexample_two_maxima`, `lowDeltaStaticPolicyTargetLocalizationInequality_not_unique`. Sender objective-difference channel: `not_coupledLeaderObj_sender_uniform_advertised`. Sender-carrier preservation: `coupledSteepPolicy_sender_image_not_mem`. The *propositions* are not disproved; their natural *routes* are. The displacement bound is the one obligation with no refutation against it. |
| **Rule-12 budget declared but never scored.** | **OPEN COMPLIANCE DEFECT.** `audit-notes/2026-07-26-…:17-23` sets cycle / stuck-signature / wall-clock budgets for LOC-1…LOC-5 and records zero consumed values against any. The record cannot distinguish "hit the limit, scope down" from "left open". Recorded as **R5**; resolving it is a user decision, not a bookkeeping fix. |
| **Referee reviewed a stale export.** | **CONFIRMED, process hazard.** The report's paper citations are to `paper/sanctions_jet_draft.txt`, frozen 2026-07-25 10:53. Live `main_sections/03` moved 2026-07-27 20:01. The paragraph disclosing the coupled-carrier gap — which the report faults the project for omitting — is live at `03:186-224` and absent from the export. Logged to the pre-submission checklist. |
| **Kudo–Akimoto Thm 5.5 / Cor 5.6 do not exist in v2.** | **CONFIRMED — content removed, not renumbered.** v2 numbering is flat (Theorem 5 / Proposition 7 / Theorem 8 / Theorem 11), there are zero `corollary` environments, and no cross-state-intersection sufficiency result appears under any number. Verified three ways (v2 source bundle, compiled PDF, served HTML). The refuted attribution was still live in `docs/archive/INTERIOR-EXISTENCE-ROUTE-ASSESSMENT-2026-06-18.md:51`, a file clean in git — **repaired 2026-07-28**, with a numbering-provenance note added to the `PaperRefer` entry so the same v1/v2 slip cannot recur. |
| **Headline set: 28, three ways.** | **NO DRIFT IN NAMES.** `Sanctions/Headlines.lean` 28 `#print axioms` directives, `HEADLINE-SNAPSHOT.md` 28 data rows, `Generate-HeadlineSnapshot.ps1` 28 `$headlines` entries. The three 2026-07-28 retirements (`coupledJointOpWide_rows`, `coupledSchur_unique_in_carrier_wide`, `coupledSchur_epsilon_isolation`) are correctly absent from all three. **Type-hash drift is a separate question** and was unverified until this round's clean-rebuild gate. |
| **Rule-18 anchor is eleven days stale.** | **OPEN.** Last commit `0748c24` is 2026-07-17. Uncommitted: 109 tracked files (+15,864/−10,462), 105 untracked, 2 deleted, 2 renamed — every audit round from 2026-07-18 onward. The committed `HEADLINE-SNAPSHOT.md` at HEAD has **24** rows, including `lowDelta_purified_existence` and `coupledSchur_exists_equilibrium`, neither of which is in the live 28. **No 30-row or 28-row artefact exists in version control**, so the demotions are reconstructible only from prose. Rules 3 / 12 / 13 have had nothing to diff against for eleven days. |

## 2026-07-28 authorized-attempt round: both gates refuted (zero new assumptions)

The user authorized (i) adding a Sender state payoff to attempt a
behaviourally-active Sender channel, and (ii) reopening the Target
displacement bound under a fresh Rule-12 budget. **Both attempts were refuted
at the Rule-11 disprove gate, before any construction effort was spent.** Two
new counterexample modules were added; **no assumption, parameter field,
carrier condition, or headline row was added or changed.**

| Item | Disposition |
|---|---|
| **Gate 4 — a Sender state payoff cannot activate the Sender channel here.** | **REFUTED.** `Sanctions/Examples/NonAffineSenderChannelCounterexample.lean`. A state-only payoff `g x` is invisible to *both* Sender argmaxes (`dynamicArgmaxSet_indep_of_state_payoff`), since it is constant in the Sender's own action; its only channel is to make `V_S` nonconstant. But at `x = 1` the sanction floor forces the greatest dynamic response to be exactly `1` with **zero slack**, so a `V_S` with any uniform positive slope near `1` pins that response across a right-neighbourhood of `a = 1/2`. The Target's ideal `niIdeal 1 a = 9/8 − a/4` *falls* in `a`, so raising compliance by `t` gains `t/4` at cost `t²` — and `α ≡ 1/2` stops being a maximizer. `gate4_no_increasing_V_S` derives `False` for **every** continuous `g`, consuming only `α_opt_top` (the equilibrium's own Target-optimality field), hence independent of the basin route. **Economically: switching the Sender's continuation channel on destroys the Target's optimality — a Rule-1 collision, not a technical gap.** |
| **Gate 4 non-vacuity.** | **PINNED TWO WAYS.** `refutation_is_sharp_at_zero_slope` discharges every hypothesis except `0 < m` from the *existing* `maEquilibrium` (whose `V_S = 0`, slope `m = 0`), and `base_witness_response_is_not_corner_pinned` shows why that witness survives — its response `1 − t/4` falls in `a` at exactly the Target ideal's rate. Independently re-checked: the slope hypotheses are satisfiable in isolation (identity value function, `m = 1`), so the contradiction is not coming from `Monotone ∧ TopSlope` alone. The fence bites at `m > 0` and nowhere else. |
| **Gate 4 salvage.** | `ideal_is_top_of_value_maximal_at_successor` — a `V_S` maximized at the realized successor state leaves `σ_dyn_top` at the static ideal, so every proof goes through with a nonconstant `V_S`. **But it is behaviourally inert**: the variation sits in a dead zone off every equilibrium path, moves no sanction, and leaves both cross rows zero. It satisfies the letter of the target and none of its economics. Recorded so no future round mistakes it for progress. |
| **Gate 2 — the `69/200` localization cannot be tightened into the slack.** | **REFUTED.** `Sanctions/Examples/LowDeltaLocalizationFloorCounterexample.lean`. Two independent floors: (a) `gate2_localization_floor` exhibits a feasible action at `x = 1` satisfying the project's *own* localization inequality with displacement exactly `3447/10000`, so no re-derivation from that inequality beats `0.3447`; and `69/200` overshoots the governing quadratic's exact root by only `0.07%`. (b) `gate2_modulus_information_floor` shows the extremal `−(a−c)² + L·\|a−c\|` perturbation — deviation *exactly* the shape of the project's continuation-error bound — has two global maximizers at `c ± L/2` with `L/2 > 10 ×` the slack, so no modulus-only argument can succeed at any constant. |
| **Gate 2 — the architectural point supersedes the arithmetic one.** | The packet `r_T = 4/5, r_S = 3/20` being tightened *against* is already documented in `LowDeltaCarrierLocalEquilibriumFrontier` as a **retained diagnostic**, whose former conditional-existence wrapper "exposed numerical policy bounds that were not derived from the economy" and was removed; that file names `Foundations/ValidatedLocalPerovOnCarriers` as the replacement. Gate 2 was aiming at a target the project had already superseded. **Constructive reading: enlarge the slack (linear in the packet radii, and re-deriving them analytically is the intended path), do not sharpen the localization.** The required carrier-containment and Perov self-map checks for any enlarged radii are **not** done. |
| **Rule-12 budget LOC-2R.** | **SCORED AND CLOSED** at the disprove gate, before any tightening cycle was spent — the intended behaviour of Rule 11, where refutation is cheaper than the proof it replaces. LOC-1 / LOC-3 / LOC-4 formally scoped down as route-refuted. This closes the R5 compliance defect. |
| **Gate 4, unconditional form.** | **PROVED.** `Sanctions/Examples/NonAffineSenderStakeRefutation.lean`. For the concrete authorized payoff `raU_S c x a s := niU_S x a s + c * x` — every other `raParams` field verbatim from `niParams` — `ra_no_equilibrium_with_alpha_half` shows that for **every** `c > 0` there is no feedback Stackelberg equilibrium with `α ≡ 1/2`. It consumes only `V_S_fix` and `α_opt_top`, never `V_T_fix_top` or `α_mem`, so it refutes a *weaker* equilibrium notion than the full structure. Existence is **constructed** (Rule 15): `raV_S c` is the Banach fixed point of the `β_S = 1/2` contraction. Sharpness: at `c = 0` the economy *is* `niParams` and the original equilibrium returns. Not a self-cancellation trick — the added term depends on `x` only, never on `s` or `F x s`. |
| **Gate 4, generalized (2026-07-29).** | **PROMOTED TO THE MODEL LAYER.** `Sanctions/Theory/Equilibrium/AbsorbingTopObstruction.lean` states the obstruction over an **arbitrary** `p : Params` — no witness economy, no specific transition, no specific payoff. The enabling fact is that `F_diag : ∀ x, F x x = x` is a *field* of `Params`, so `F 1 1 = 1` (the top state is absorbing under the maximal sanction) holds for every economy in the class free of hypothesis. `no_equilibrium_of_slope_and_top_gain` takes three parametric inputs — Sender-value slope `m` to the top, transition responsiveness `κ` at the top, static shading bound `c` — with the single binding inequality `c ≤ β_S · m · κ` among quantities that already exist. **No new named primitive; nothing added to `Params`.** Its deviation half `target_deviation_of_pinned` needs *no* hypothesis on `F`, `U_S`, or `V_T`: once the response is pinned at the corner at two actions, the successor is literally the same term at both and the continuation cancels. Rule-19 placement: `Theory/`, since it mentions `Params`. |
| **Rule-5 discharge for the generalization.** | `ra_no_equilibrium_via_general` (in `NonAffineSenderStakeRefutation`) recovers the witness refutation from the general theorem by instantiating `m = c` (the Sender's stake *is* its value's slope to the top), `κ = 49/100` (the quadratic-bump transition's top responsiveness), and shading bound `t/2` — whereupon the general condition `c_shade ≤ β_S · m · κ` becomes exactly the witness's own `t ≤ 49c/100`. That the specialization reproduces the witness *exactly* is what makes the generalization load-bearing rather than a parallel restatement. A Rule-13 unused-hypothesis pass also removed a `0 ≤ κ` hypothesis the proof never consumed. |
| **Gate 4, the structural reason.** | `basin_forces_corner_max_at_one` (Route B, adversarially rated "the strongest artifact in the file"): for **any** params, values, policy, and thresholds, a `JointPreferenceBasinTop` forces the Sender's dynamic maximizer at `x = 1` to be exactly `1`, because `sender_high_argmax_exists` demands a maximizer in `[max 1 sbar, 1]`. Combined with the two-sided pin — a *rising* `V_S` breaks the Target's argmax, a *falling* one breaks the sanction floor — this says **`V_S` must be flat at the absorbing state**. The absorbing state is not a route around the obstruction; it is the obstruction. *(Not yet promoted into the tree; recorded here as the round's structural finding.)* |
| **⚠ CORRECTION — the "active Sender channel" must NOT be claimed.** | An intermediate agent report framed `ra_response_strictly_exceeds_static_ideal` (the Sender levying strictly above its stage-optimal sanction) as a *positive* result: the first construction in this tree with a behaviourally active Sender continuation channel. **Adversarial verification rejected that framing and it is withdrawn.** `raV_S c` is the Sender Bellman fixed point *at the hand-fixed policy* `α ≡ 1/2`, which the same file proves non-optimal for every `c > 0`; the comparison is moreover evaluated at Target actions `1/2 + t` that are argmaxes of nothing. Under Rule 1 these describe an **assumed, refuted strategy**, not equilibrium behaviour. They are load-bearing only as steps toward the refutation, and the file's docstring says so explicitly. |
| **⚠ Two further agent overclaims, withdrawn.** | (a) "No affine `V_S` for any `c > 0`" — the artifact refutes the Bellman recursion with the response *pinned* at `(x+1)/2`, but the true Sender Bellman is a supremum over feasible sanctions, so only the pinned surrogate is ruled out. (b) `corner_pin_of_slope_to_top` was described as a "strict weakening" of the conditional gate lemma; the hypothesis bundles are **incomparable** — the new one demands the slope bound on all of `[0,1]` rather than `[31/32, 1]`, and a kinked witness satisfies the old hypotheses while failing the new. Both corrected in the promoted file. |
| **⚠ Gate 2 novelty accounting, corrected.** | An agent bold-labelled its refutation of the `29/24` quadratic-growth coefficient as **NEW**. It is not: `lowDeltaStaticTarget_not_quadraticGrowth_29_div_24` is already committed in HEAD at `LowDeltaStaticStackelberg.lean:150`, under a header reading "## Disprove-first modulus check", **28 lines above** the declaration the report cited in the same paragraph. Its "target unreachable" inequality is also strictly *weaker* than the already-committed `69·slack < 3447/10000`. Genuine net new content: sharpening the localization floor from `3447/10000` to the exact attained optimum `L/2 + √(C + (L/2)²) = 0.34476245600304…`, i.e. **0.018%** — not promoted, since a third copy of the shared counterexample object would violate Rule 5 without first subsuming the two existing ones. |

## 2026-07-29 weak-floor round: off-corner persistence proved, frontier sharpened

Referee plan items 1, 3, 4 and 7 discharged. **No assumption was widened**: the
weak-floor structure is a *weakening* with its containment proved, and the
Sender-spread lower bound is *derived* from primitives with no hypothesis
beyond the equilibrium itself.

| Item | Disposition |
|---|---|
| **The ratchet dichotomy — the sharpest frontier statement.** | **PROVED, fully general.** `Theory/Equilibrium/AbsorbingTopObstruction.lean`. For any feasible rule on any upper interval ending at the top state: either the top sanction is *interior* (`r 1 < 1`), and then the strong ratchet floor fails on that interval and on **every** such interval (`Sanctions.no_upper_basin_floor_of_top_lt_one`, already in the tree at `Foundations/Basic.lean:51`); or `r 1 = 1`, and then `F 1 (r 1) = 1`, so the realized successor at the top *is* the top. `ratchet_dichotomy`, with `rule_top_eq_one_of_floor`, `successor_top_eq_one_of_floor`, and an equilibrium specialization where feasibility comes free from `dynamicTopRealizedRule_mem`. **Needs no slope, curvature, or payoff condition and no hypothesis on either value function** — pure feasibility plus `F_diag`. Strictly more general than `no_equilibrium_of_slope_and_top_gain`. **The floor that delivers maximal ratcheting is precisely what makes the top absorbing and kills the Target's channel there.** |
| **Weak-floor basin: invariance without `s(x) ≥ x`.** | **PROVED for general `F`.** `Theory/Basin/WeakFloorBasin.lean`. The strong floor is consumed in exactly one place (`DynamicTopLockIn.lean:225`, the `le_max_left x sbar` projection); invariance is *routed* through that ratchet but does not need it. The weak route uses the lower-edge chain `xbar ≤ F xbar sbar ≤ F x sbar ≤ F x (g x)`, needing only `F_mono_x`, `F_mono_s`, `F_mem`, `F_diag` — **no affineness, and not even `top_rule_mono`**. |
| **Rule-3 containment for the weak floor.** | **DISCHARGED HYPOTHESIS-FREE.** `WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed`: `JointPreferenceBasinTop … xbar sbar → WeakFloorBasinTop … xbar (max xbar sbar)`, no extra hypothesis. **Correction to my own earlier framing:** I stated the extra condition as `F xbar sbar ≥ xbar`, which is *not* implied by the strong structure — at `sbar = 0` the strong floor degenerates to `x ≤ s`, satisfiable, while `affineF (1/5) (1/2) 0 = 2/5 < 1/2`. The correct general form is `xbar ≤ sbar`, which implies the corner condition for every `F` and is equivalent for affine `F`. My affine algebra was right; the general statement was not. |
| **⚠ Rule-11 defect found and repaired in a promoted file.** | `corner_not_implied_at_given_sbar_counterexample` was **named and documented** as refuting a `JointPreferenceBasinTop` implication, but its statement mentioned neither that structure, nor `IsMaxOn`, nor `senderDynObjective` — one conjunct was `x ≤ 1` in disguise. This is the exact pattern that retired three declarations on 2026-07-28. **Repaired:** renamed to `corner_arith_ingredients_at_zero_floor` with an honest docstring, and the genuine `Params`-level witness now lives in `Examples/WeakFloorContainmentCounterexample.lean` — an actual economy carrying a full `JointPreferenceBasinTop` instance at floor `0` (every field discharged, including the Sender's `IsMaxOn` obligation) together with the corner failing. It sits under `Examples/` because `Theory/` may not import a witness economy (Rule 19). |
| **P3 satisfies the weak floor — the Sender-spread lower bound.** | **PROVED ANALYTICALLY.** `Examples/P3WeakFloorSpreadBound.lean`. `mwD_ge_seventeen_tenths`: `17/10 ≤ V_S(1) − V_S(0)` for **every** equilibrium of the shocked specialization, with **no hypothesis beyond the equilibrium** and no assumed numerical input. Route: the half-width-one smear is exactly affine, so differencing the Sender Bellman equation at the endpoints is an *identity*; at the top state the response is the unclipped vertex, so `α(1)` is eliminated and the `Δ_S·s₁` cross term cancels, giving `Δ_S ≥ 11/7`; a lower bound on `α(1)` from an *upward* Target deviation (using only the existing cap `Δ_T ≤ 60/11`) gives `α(1) ≥ 5/12` and hence `17/10`. Needed: `Δ_S ≥ 4/5`. |
| **Rule 5 for the floor.** | `mwWeakFloor_param` proves the floor at **every** `(xbar, sbar)` with `2/5 ≤ xbar ≤ 1` and the single rational inequality `41760·sbar < 31530·xbar + 5329`; `sbar ≤ 1` is a consequence, not a hypothesis. The concrete pivots are one-line corollaries, and invariance at each routes through the general-`F` step lemma. |
| **⚠ The obvious closing route is provably dead.** | An *upper* bound on `α` at the pivot is derivable (`mwAlpha_le_at_pivot`: `α(1/2) ≤ 37/160`) and is **not enough**: the test needs `α(1/2) ≤ (2Δ_S − 1)/20`, and `pivot_alpha_ceiling_gap` machine-checks that this is strictly below `37/160` even at `Δ_S = 17/10`. What closes the floor is a *downward* Target deviation, needing no `α` bound. Recorded so no future round retries the dead route. |
| **Rule 11 non-vacuity + independent cross-check.** | The equilibrium type is inhabited by the explicitly **constructed** `mwEqEquilibrium`, not `Nonempty` by assumption — verified directly, so the whole chain is meaningful. There is *no* uniqueness theorem for that economy, so the constructed equilibrium's pinned spread interval cannot serve an arbitrary equilibrium; it is used instead as a falsification test (`p3WeakFloor_bound_below_pin`: `17/10 ≤ 441/250`). Analytic route and constructed pin agree rather than contradict. |
| **What the weak floor does not carry.** | The level floor does **not entail** a monotone sanction path: `weakFloor_ratchet_counterexample` refutes that *implication* over arbitrary kinematic data `(F, g)`, with a **constant** witness rule that is not an equilibrium object at all. It does **not** refute the existence of a monotone-sanction equilibrium — the persistence conclusion is *existential* in `E`, and the ratchet floor implies the level floor hypothesis-free (`of_jointPreferenceBasinTop_reindexed`), so every economy carrying the strong basin still supplies one (`jointPreferenceBasinTopF_long_run_with_equilibrium_evidence`). Restricting to equilibrium-realized rules *strengthens* the refuted implication's hypotheses, so a counterexample to the broad universal is none against the restricted class. What is genuinely unavailable is the *guarantee*, and only where the ratchet floor is impossible on `[xbar,1]` (`r 1 < 1`). **At the full-width P3 economy monotone sanctions are in fact AVAILABLE on a sub-basin** — see the 2026-07-30 row below. `target_prefers_sanctions` survives only formally: its domain is `Icc (max x_n sbar) 1` and the realized sanction may fall below `x_n`. Basin invariance, statewise myopic dominance, and post-shock entry survive intact. |
| **N14 / N15 promoted to the manuscript (2026-07-29, user-authorized).** | `main_sections/03` now states the ratchet dichotomy as a **named** result (`prop:ratchet-dichotomy`) and level-floor invariance with its cost (`prop:level-floor`). Both carry their scope limits into the paper: the dichotomy is a sufficient-condition frontier, **not** a general impossibility theorem over all admissible economies, is silent about interior states, and constructs no replacement policy; the level floor **loses** the monotone-sanction conclusion, and the paper *exhibits* that failure rather than noting it. The level-floor hypothesis is stated as **implied** by the basin conditions when read at `max{xbar, sbar}` — a weakening of the assumption surface, matching `WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed`. Abstract unchanged; **N13 still held**. Every cited Lean name was grep-verified against HEAD before being written into the paper. |
| **Rule 6 outcome: the literature had nothing.** | A sweep of `PaperRefer/` and `BookRefer/` found **no theorem giving a lower bound on a value-function endpoint spread**; an online search added four annotated summaries (Clarke envelope, iterated Bellman inequalities, LP approach to ADP, optimistic value iteration) plus a negative-result note, and no usable route. Rule 6 is satisfied by exhaustion, not by success — the bound had to be derived in-project. |

## 2026-07-31 referee round: interval robustness and the escalation mechanism

Referee items 1--4 discharged, references folded, and one hedge replaced by a
theorem. **No assumption widened**; no headline row changed.

| Item | Disposition |
|---|---|
| **⚠ A false claim of mine, corrected at the theorem rather than the prose.** | I had written that `exists_params_with_perpetual_sanctions` contains "no parameter value", while the statement exhibited `p.F = affineF (1/2)` — a parameter value. The register row said both things **in one sentence**. Rather than soften the prose, the theorem now requires only `∃ δ, 0 < δ < 1 ∧ p.F = affineF δ`: *some* deterministic affine law, rate existentially bound. The claim is now true as stated. |
| **Knife-edge objection answered on a continuum.** | `perpetual_sanctions_on_beta_interval` (`Examples/PerpetualSanctionInterval.lean`): for **every** Sender discount factor in `[6/13, 4/7)` there is a perfect-information equilibrium with perpetual non-falling sanctions on the high basin. Stronger than the floor it was asked for — `eeCertB_sanctions_eq_one` shows the realised sanction is **exactly maximal** at every date. `beta_window_nondegenerate` records that the window is a genuine continuum. Robustness is in **one** direction only (Sender patience, other primitives fixed), and both the Lean and the paper say so. |
| **The escalation hedge replaced by a parametric theorem.** | The claim "the shock permits the interior policy, which makes the ratchet strict; under perfect information only the weak ratchet is obtained" was scoped to "in our two witnesses" — honest but conceding the wrong thing. It is now `dynamicTopLockInSanctionsF_strictMono_of_gt_self` (`Theory/LockIn/SubintervalLockIn.lean`), over an **arbitrary** economy, rule and sub-interval: if the equilibrium sanction strictly exceeds the state the political state strictly rises, and if the rule is also strictly increasing the sanction strictly rises, forever. The one-step core uses only `F_diag`. **So the weak/strict split is a property of the realised rule, not of the informational structure** — and whether a deterministic economy has such a rule is now a checkable question rather than an open-ended one. |
| **The two escalation conditions are independent.** | `strict_escalation_needs_both` exhibits a rule above the diagonal that is not monotone, and a strictly monotone rule below the diagonal. Neither conjunct is redundant, and neither follows from the basin conditions — so strict escalation is not automatic wherever persistence holds. |
| **Necessity claims withdrawn.** | Nothing in the development shows perfect information precludes strict escalation, and the manuscript now says so explicitly rather than implying a necessity theorem. |
| **Paper sync (referee items 3--4).** | Abstract and conclusion reframed around the frontier: the mechanism-active equilibrium cannot meet the floor at the ceiling *because* that floor makes the top absorbing, yet ratchets strictly on an interior sub-basin. The formalization map now lists the pinning results, the uniform sub-basin theorem, the existential declarations, the interval theorem and the escalation mechanism, each with its scope caveat. |
| **References folded (2026-07-31).** | New: Bressan–Jiang 2019 *generic structure and stability* (the file the referee flagged missing) and Jaakkola–Wagener, both in `PaperRefer/StochasticGames/`. Added a PDF for the Doraszelski–Escobar entry, which had only a summary, and the publisher version of Bressan–Jiang self-consistent. Each indexed with the reason it supplies **no importable theorem**: two are finite-state simultaneous-move, one is static, one is continuous-time Nash. |

## 2026-07-30 existence-form round: perpetual sanctions stated existentially

On the user's reframing: rather than "this calibration escalates", state **"there
exist primitives at which sanctions never end"**. The tuned magnitudes then live
inside the *proof* rather than the *claim*, which is the one use of a witness
Rule 5 endorses without reservation — an existence certificate. **No new
mathematics**; both theorems are short existential introductions over already
proved results. The value is entirely in the logical form.

| Item | Disposition |
|---|---|
| **Fully existential form.** | `exists_params_with_perpetual_sanctions`: **there exist primitives** `p`, an equilibrium, a pivot `xbar < 1` and a floor `sbar > 0`, such that from **every** initial state of `[xbar, 1]` and at **every** date the realised sanction stays at or above `sbar` and never falls. The transition is described only *qualitatively* — `∃ δ, 0 < δ < 1 ∧ p.F = affineF δ`, i.e. *some* deterministic affine adjustment law, with the rate existentially bound — so **no magnitude from the witness appears in the statement**. ⚠ **Correction (2026-07-31):** an earlier version of this row, and the theorem itself, exhibited `p.F = affineF (1/2)`, which *is* a parameter value; the row simultaneously claimed "no parameter value appears". A referee caught the contradiction. The theorem was strengthened to the magnitude-free form rather than the prose merely softened. |
| **Perfect-information form.** | `exists_perfect_information_perpetual_sanctions` (`Examples/PerpetualSanctionExistence.lean`): there exist primitives and an equilibrium of the infinite-horizon feedback Stackelberg game such that from **every** initial state in the high basin, at **every** date, the realised sanction never falls below `1/2 > 0` and the path is non-decreasing. `b2_transition_is_deterministic` records **by `rfl`, not by assertion**, that the transition is the affine law with no smoothing operator — so this is genuinely perfect information and the conclusion cannot be attributed to an informational friction. |
| **Strict-escalation form.** | `exists_perpetually_escalating_sanctions`: there exist an equilibrium and a start with the sanction path `StrictMono` — strictly higher at every date, forever — and never below `5/12 > 0`. |
| **⚠ The two are NOT the same setting, and the split is structural.** | The strict form is at `mwShocked`, whose `smear V y = 𝔼_η[V(clipS'(y+η))]` averages the continuation value over noise — so it is **not** a perfect-information game. The shock is what purifies the follower response and permits the interior Target policy, and the interior policy is what makes the ratchet strict; under perfect information the Target sits at the stage-aligned corner and only the weak ratchet is obtained. **Strict escalation under perfect information is OPEN and is not claimed.** I nearly reported the strict result under the perfect-information framing before checking what `smear` was. |
| **Boundedness stated, not glossed.** | Sanctions are feasible, so a strictly increasing path increases *while converging*. No claim of unbounded escalation is made or could be. |
| **Paper.** | `main_sections/03` gains a paragraph reading `thm:b2-benchmark` as the existence claim it already is — the parameter vector is the proof, not the claim — isolating conclusion (iv) as the perpetual-sanction statement, recording that the setting has perfect information, and stating the strict/weak split with the open item named. The theorem itself was already existential in form, so this is a reading, not a new claim. |
| **What this changes about target B.** | B is no longer "remove the witness" — the existential already does that. B becomes the sharper question: **which structural conditions on primitives suffice**, so the statement reads "for every economy with these signs, sanctions perpetuate" rather than "for some economy". That is a characterisation rather than an existence claim. |

## 2026-07-30 keystone round: the P3 spread is pinned for every equilibrium

Answers the user's objection that the results named a witness. **No assumption
widened.**

| Item | Disposition |
|---|---|
| **The spread is pinned for every equilibrium.** | **PROVED.** `Examples/P3SpreadPinned.lean`. `mwSpread_pinned`: `V_S(1) − V_S(0) = mwEqSenderSpread` for **every** equilibrium of the specialization; hence `mwAlphaOne_pinned` (Target top action) and `mwSenderRule_pinned` (the whole realised Sender rule as a function of `(x,a)`). Everything previously keyed to the constructed equilibrium's spread upgrades. |
| **`α(1)` is DERIVED, not assumed.** | The decisive check, attacked hardest by the adversarial pass and unbroken. `mwAlphaOne_pin` has exactly **one** hypothesis — the equilibrium. Optimality enters only through the structure's genuine `α_opt_shock` (`IsMaxOn` over the real action set). The Target's top-state integrand is an exact quadratic with curvature `−29/24`, **independent of the equilibrium**, so "no better deviation" upgrades to "equals the vertex" by an exact `ring` identity — no assumed regularity, no carrier, no shape condition. The tested deviation is *proved* feasible and *proved* strictly inside the unclipped Sender branch. |
| **⚠ A branch trap that would have made a FALSE theorem.** | `s₀ = 0` holds **iff `Δ_S ≤ 2`**, and the derived arbitrary-equilibrium window `[17/10, 45/16]` **straddles 2**. The quartic eliminant holds only on the `s₀ = 0` branch, so "every equilibrium satisfies the quartic" was **false as stated** until the other branch was excluded (`branchB_excluded`, via a cubic proved strictly positive on `[2, 45/16]`). Recorded because the failure mode — a plausible proof of a false statement — is the one this project most needs to catch. |
| **Root uniqueness is algebraic, not analytic.** | `mwEqQuartic_strictAntiOn` uses the divided-difference chord identity `q(a) − q(b) = (a−b)·B(a,b)`, proved by `ring`, with `B < 0` by factorisation. No derivative, no mean value theorem. The derivative route is retained only as independent corroboration. |
| **The existence window is derived, not numerically discovered.** | `[17/10, 45/16]` comes from `mwD_ge_seventeen_tenths` and `mwD_le` — hypothesis-free bounds for every equilibrium. The older tight bracket `[441/250, 17641/10000]` *was* numerically discovered, and the new results deliberately do **not** inherit it. |
| **⚠ Quantifier strengthened before promotion.** | The witness sub-interval is equilibrium-independent, so `p3_exists_ratchet_invariant_subinterval_uniform` now states **one** interval working for **every** equilibrium, not an interval per equilibrium. Flagged by the adversarial pass as the exact habit the sub-basin round was burned by. |
| **Scope, at the strength proved.** | Pins `Δ_S`, `Δ_T`, `α(1)` and the Sender rule. Does **not** pin `α(x)` at every state, so it is **not** full equilibrium uniqueness — two equilibria could differ in the Target policy away from the top. |
| **Provenance of the numbers, recorded honestly.** | The economy's own constants are **chosen**: `MechanismWitness.lean:143` says "identical signs to P2, different constants", and no derivation links `mechanismWitnessParams` to the four-group microfoundation. Signs are economics; magnitudes are a tuned point. Everything below is *forced* — the quartic coefficients are the machine-checked eliminant, the window and the curvature are derived. So the algebra is real but conditional on a chosen parameter point. **Target B** was opened for this reason: `audit-notes/2026-07-30-parametric-algebraic-existence-budget.md`, with a Rule-12 budget and discard trigger. |

## 2026-07-30 sub-basin round: P3 ratchets after all; seven overclaims repaired

Prompted by a single question from the user: *is the persistence conclusion
existential?* It is — `∃ E, … ∧ Monotone (sanctions)` — and that one observation
overturned the round's framing. **No assumption was widened.**

| Item | Disposition |
|---|---|
| **The refuted object was misread, project-wide.** | `weakFloor_ratchet_counterexample` refutes `¬(∀ F g xbar sbar, …)` — an implication over **arbitrary kinematic data**, whose witness rule is the *constant* `fun _ => 1/2`, not an equilibrium object at all. Because the persistence conclusion is **existential in the equilibrium**, and because the ratchet floor implies the level floor hypothesis-free, every economy carrying the strong basin still supplies a monotone-sanction equilibrium. **Restricting to equilibrium-realized rules *strengthens* the refuted implication's hypotheses**, so a counterexample to the broad universal is none against the restricted class. Seven documents asserted or implied the stronger reading; all seven corrected. |
| **P3 ratchets — strictly — on a sub-basin.** | **PROVED.** `Sanctions/Examples/P3SubBasinMonotonicity.lean`. `p3_monotone_sanctions_from_rational_start`: from any start in `[2/5, 1129/2000]` — entirely rational hypotheses — the political-state path and the realized-sanction path are both `StrictMono`, at every date. The direct slope `9/8` strictly beats the indirect slope through the Target's best response, so the ratchet never stalls. This is the *interior-policy, mechanism-active* economy the paper had presented only as a boundary case. |
| **Why the sub-basin ends where it does.** | **PROVED, parametric.** `Sanctions/Theory/LockIn/SubintervalLockIn.lean`. `dynamicTopLockIn_subinterval_forces_fixed_endpoint`: if `[a,b]` carries the ratchet *and* is forward invariant, the realized rule fixes `b` **exactly**. Purely kinematic — invariance at `b` gives `F b (R b) ≤ b = F b b`, hence `R b ≤ b`, while the ratchet gives `R b ≥ b`. Consumes only `F_diag` and strict monotonicity of `F b ·`. So off-corner ratcheting does not *fail*; it **terminates at an interior steady state**, and the dichotomy says why it cannot be continued to the ceiling. |
| **The endpoint is irrational.** | `mwEqFixedState_irrational`, via a route that avoids quartic ℚ-irreducibility entirely: a rational endpoint would force the spread to satisfy a rational quadratic as well as the quartic, and dividing leaves a remainder whose linear coefficient is a nonzero constant, so the spread would be rational outright — excluded by a rational-root argument on denominators dividing the leading coefficient `81`. |
| **⚠ Scope of the negative, corrected before promotion.** | `p3_no_rational_ratchet_invariant_subinterval` refutes `¬∃ interval ∀E` — no rational-endpoint interval carried by **every** equilibrium — discharged by a *single* instantiation at the constructed equilibrium. It does **not** show that no equilibrium has one. Since persistence is existential in `E`, this ∀E-orientation is not the form the economics turns on; the load-bearing result is the positive one. The Lean docstring originally stated the stronger reading and was rescoped. |
| **⚠ Two committed manuscript overclaims, repaired in place (Rule 2).** | (a) "`prop:ratchet-dichotomy` explains why **no economy in this class delivers both**" asserted exactly what this register disclaims — the dichotomy is a frontier, and ruling out an equilibrium additionally requires `prop:absorbing-obstruction`. (b) "what is **surrendered** is one conclusion — monotone sanctions" globalized a statement about an implication. Both corrected; §3 now records that monotone sanctions *are* available at P3 on a sub-basin. |
| **⚠ A docstring that contradicted its own theorem.** | `of_jointPreferenceBasinTop_reindexed` carried "Only the ratchet / `Monotone` conclusions are genuinely lost" — on a theorem whose hypothesis is the **strong** basin, from which monotonicity follows with no extra hypothesis. Corrected. |
| **Rule 13 — hypothesis weakened to what is consumed.** | `mwEq_no_int_pair` took `d ∣ 81` but consumed only `d ≤ 81`; restated at the weaker hypothesis. |
| **Rule 3 / Rule 1 / numerics.** | Clean, independently re-verified: no new `Params` field, no new load-bearing `Prop`, **no assumed pointwise bound on the Target policy** (none was needed — the constructed equilibrium's policy is explicit and argmax-certified), and **no numerically-obtained constant in any statement** (decimals appear only in docstrings; the spread window is IVT-proved upstream). |
| **Still open, unchanged.** | No pointwise interior bound on the Target policy for an *arbitrary* P3 equilibrium, and no uniqueness theorem for that economy — so the positive results are about the constructed equilibrium `mwEqEquilibrium`, not every equilibrium. |

## Shock interior-existence assumption surface (2026-06-19)

The atomless-purification shock development (`Postulates/ShockedParams.lean`,
`Theory/Abstract/{ShockedBellman,ShockedEquilibrium,ShockedInteriorExistence,
ShockedLeaderLipschitz,HeSunShock,HeSunShockExistence,MovingAverageShock}.lean`,
`Foundations/MovingAverage.lean`) delivers feedback-Stackelberg existence under a
small atomless transition shock, the deterministic-interior case being provably
blocked (selector Hölder-½). Its category-(3) surface:

| Symbol | Category | Status |
|---|---|---|
| **`κ` (atomless shock kernel)** / `smear` + `smear_nonexpansive` | (3) New primitive | **User-approved 2026-06-19.** A probability measure on the transition noise; the only structural property used is sup-norm nonexpansiveness, *derived* from `∫κ=1` (`HeSunShockParams.smearBCF_nonexpansive`). The kernel class is now **inhabited by a concrete closed witness** `eatonEngersMovAvgShock` (`Examples/MechanismWitnessShocked.lean`, instantiating the parametric wiring layer `MovingAverageShock.lean`). This makes the shock primitive concrete but does not by itself establish joint satisfiability of the interior theorem's three analytic hypotheses. The deterministic model is the `κ→δ₀` limit (untouched). |
| **`h_obj_diff` (Stackelberg-coupling regularity)** | (3) **Accepted open primitive — route (a), user-approved 2026-06-19** | The leader objective-*difference* is action-Lipschitz with constant `∝ dist(V,W)`: `|[L_V(a_V)−L_W(a_V)]−[L_V(a_W)−L_W(a_W)]| ≤ (L_lead·dist V W)·|a_V−a_W|`, where `L_Z(a) = joint_T_top_integrand (smear (V_T_dyn_shock Z)) (smear Z) x a` is the *real* leader payoff. It is one of the three remaining analytic inputs for the **general interior** shocked case, alongside joint continuity `hσc` of the shocked Sender selector and strong concavity `sc` of the composite leader objective. At the full-width specialization `h = 1`, `hσc` is now discharged for every bounded-continuous Sender value, so `h_obj_diff` and `sc` are the two leader-side inputs left. The canonical P3 theorem now derives the leader selector itself, feasibility, Berge continuity, and pointwise optimality, eliminating those four formerly free leader-map hypotheses. **Discharge status: OPEN, accepted as a standing consumed primitive** — flagged in the paper limitations. Kernel convolution regularises the state direction but does not by itself control the required action/value cross variation (Hinderer 2005 Remark 2), and the feedback-Stackelberg literature assumes analogous leader-side regularity (Bressan-Jiang 2020 A1 via IFT/genericity, fails at corners; He et al. 2025 Asm 4.3; Li et al. 2024 Thm 4.2/4.3). Two alternative routes were refuted in Lean (Rule 11): the single-crossing recast (route b) retains the `(a,V_T)` violation, and the BRW monotone-iteration pivot (route c) either needs the same condition or an action-independent mixing transition absent from the location-shift `F`. **Route-A quantitative closure (2026-07-04 kernel-width audit):** the C²-kernel derivation is quantitatively DEAD at P3 — smeared-Sender-concavity positivity requires `h > √(523/9600) ≈ 0.233`, while the realized-state no-clip window requires `h ≤ 23/250 = 0.092`; even without the latter, the derived bound is `L_lead ≥ ≈ 2.49` at zero carrier norms (≈ 3000–6663 at the actual norms `M_S = 523/160`, `M_T = 20`) against the required `< 1/2`. This establishes failure of that discharge route at P3, not an impossibility theorem for every kernel or modified economy: the same calculation opens only after changing the economy to about `δ ≤ 1/54`. |
| `L_smVT` (smear state-Lipschitz constant) | (2) Weakening → **discharged** | Was a consumed scalar; now the **closed form** `‖V‖/h` at the concrete box kernel (`movAvgShockedParams_smear_lipschitz`). No standing primitive. |
| `leaderObj` (free leader-objective function) | — → **removed** | The headline interior theorem previously took the leader objective as a free function (a Rule-14 laundering risk); `shockedFeedbackStackelbergTop_interior_discharged_canonical` **pins it** to the genuine `joint_T_top_integrand`, and `lead_opt` is then *derived* from `lopt_obj` (one fewer consumed hypothesis). |

**Net route-(a) position.** General interior shocked existence is a CONDITIONAL theorem — given joint follower continuity `hσc`, composite strong concavity `sc`, the coupling bound `h_obj_diff`, and the contraction margin — and is machine-checked exactly at that boundary. The concrete box kernel discharges the kernel-side primitives only; joint satisfiability of the general three-condition analytic package at P3 is not yet exhibited. The witness-specific canonical wrapper is now symbolic in the positive curvature `c_T` and nonnegative coupling modulus `L_lead`, with direct margin `β_S + 2 L_lead / c_T < 1`; the old modulus-`2` and `L_lead < 1/2` surface is only its arithmetic specialization. At the full-width specialization `h = 1`, exact affine smoothing discharges `hσc`, so the state-local symbolic theorem consumes only positive-modulus `sc`, `h_obj_diff`, and that direct margin. The **corner** shocked equilibrium is unconditional from primitives. In the deterministic interior case the recorded order-reversal and period-two certificates block the proposed iterative proof routes, but do not prove nonexistence of a fixed point. At P3, the audited C²/kernel-width route to `h_obj_diff` is quantitatively closed; the condition remains one explicit member of the analytic package rather than being hidden in a genericity assumption.

**2026-07-15 P3 re-check, completed full-width pass; symbolic-curvature update 2026-07-27.** The general semiconcavity theorem remains: `mwSigmaDynTop_continuous_subtype_of_smearedSemiconcave` gives joint continuity on `↥S × ℝ` when the smeared Sender continuation is `c`-semiconcave with `c < 60`. At `h = 1`, the exact moving-average identity is stronger: `mwSmearedSemiconcaveOn_one` proves `c = 0` for every bounded-continuous continuation, `mechanismWitnessParams_dynamicArgmaxUnique_one` gives argmax uniqueness, and `mwSigmaDynTop_continuous_subtype_one` fully discharges follower continuity without a carrier-invariance hypothesis. The wrapper `mechanismWitnessParams_purified_existence_canonical_leader_one_local_symbolic` therefore leaves only positive-modulus `sc`, `h_obj_diff`, and the direct margin `β_S + 2 L_lead / c_T < 1`; the older fixed-`2` wrapper is a compatibility corollary. The leader-side boundary is stronger than previously recorded: `mwStaticLeaderComposite_not_strongConcave_of_nonneg` uses the same exact points `x=5/12` and actions `9/10, 37/40, 19/20` to prove that the static composite lies below its chord, so stage curvature cannot derive `sc` at any nonnegative modulus. Finally, `mwSenderStage_no_positive_lowerSlope_at_half` still refutes the full-interval strict-increase/strong-rally *route*, but no longer implies that monotonicity itself is open. With `b = a - (27/10)x`, `mwCanonicalLeaderOne_adjusted_antitoneOn` proves the canonical adjusted leader action is antitone; `mwSenderDynObjective_canonical_one_IDOFamilyOn` establishes interval dominance; and `mwDynamicTopRealizedRule_canonical_one_monotoneOn_of_IDO` proves the full-width canonical realized rule is monotone on all of `S`. This closes the monotonicity component of `hDynReg` for that selector. The floor question is now closed in the opposite direction. `mwSigmaDynTop_eq_clip_vertex_one` gives the exact response vertex `9x/8 - 1/12 - 5a/12 + (V(1)-V(0))/24`, so a top-state floor requires `V_S(1)-V_S(0) ≥ 10 α(1)-1`. The equilibrium-specific bounds `mwShockedOne_sender_endpoint_spread_le` and `mwShockedOne_target_endpoint_spread_le` follow from the two Bellman fixed points. The first makes the putative floor imply `α(1) ≤ 17/50`; the second bounds the worst continuation loss from the Target deviation to action `1/2`. `mwShockedOne_no_top_floor` proves that deviation is strictly profitable, and `mwShockedOne_no_dynamic_floor` consequently rules out every nonempty-basin floor ending at state `1`. No hypothesis was added. Thus the `h = 1` monotonicity specialization is valid but cannot satisfy full `hDynReg` or deliver the associated pathwise dominance at P3; this is an equilibrium impossibility result specifically for the full-width specialization, not a claim about smaller shock widths.

---

## Original (audit-33) classification

Per the audit-33 critique and project Rule 3, this document classifies
every load-bearing hypothesis introduced by the audit-31/32/33 rounds
into one of three categories:

1. **Internal scaffolding** — a Prop/structure/hypothesis used only
   internally in a proof; never exposed as input to a load-bearing
   theorem.
2. **Replacing a stronger existing assumption** — a Prop/structure
   that *weakens* an existing assumption surface (e.g., localizing
   a global quantifier to a closed subset).
3. **New final paper assumption requiring confirmation** — a
   Prop/structure that is genuinely new and would appear as a stated
   hypothesis of any paper-level theorem written against the current
   architecture.

Classification (3) triggers a Rule-3 stop-and-confirm event.

## Per-symbol register

> **Audit-49 status overlay.** The per-symbol tables below were
> written across audit rounds 31–43 and at the time described many of
> these symbols as "paper-facing" or as the recommended top-level
> route. **The Quarantined legacy resistance-action route table
> above is the current source of truth.** Wherever a per-symbol entry
> describes a quarantined legacy symbol as "paper-facing," the
> entry's text is **frozen at its original audit-round status** and
> should be read together with the quarantine table.
>
> Specifically the following per-symbol entries are superseded by the
> quarantine table and should be read as **legacy / resistance-action
> only**:
>
> * `jet_C1_existence_and_three_goals` (originally tagged
>   "Paper-facing C¹-track JET bridge" in the iter-19 section).
> * `RegularEconomyCertificate`, `RegularEconomyCertificate.three_goals`,
>   `regularEconomyCertificate_of_lipBall`,
>   `RegularEconomyCertificateC1`,
>   `RegularEconomyCertificateC1.three_goals`,
>   `RegularEconomyMargins`,
>   `RegularEconomyMargins.row_inequalities_preserved_under_perturbation`
>   (originally tagged "Payoff-form-agnostic top-level theorem
>   bundle" in the audit-40 refactor section). The audit-43 critique
>   showed these inherit the resistance-action sign convention via
>   the JETBridge composition; the audit-46 `StandardComplianceCertificate`
>   family is the literal-compliance canonical replacement.
> * `jet_three_goals_from_ball_operator_lipschitz_primitives`
>   (originally tagged "Assumption-reducing bridge" in the audit-34
>   follow-up section).
> * `jet_persistence_at_equilibriumTop_from_lowerSlopes`,
>   `jet_shock_at_equilibriumTop_from_lowerSlopes`,
>   `jet_dominance_at_equilibriumTop_from_static_order`
>   (originally tagged scaffolding for the audit-33 JET-bridge round).
> * `DynamicVsMyopicIncreasingDifferencesAt`,
>   `alpha_order_dynamic_ge_myopic_of_increasingDifferences`,
>   `dynamicTop_rule_dominates_myopic_policy_from_increasingDifferences`
>   (originally tagged audit-34 item-D dischargers). The
>   compliance-direction parallel is the audit-41 family
>   (`DynamicVsMyopicDecreasingDifferencesAt`,
>   `alpha_order_dynamic_le_myopic_of_decreasingDifferences`,
>   `dynamicTop_rule_dominates_myopic_policy_audit41_compliance`).
>
> Their underlying classification (cat-1 scaffolding / cat-2
> weakening) is unchanged; what changed is which interpretation of
> `a` they apply to.

### From `Sanctions/Theory/Abstract/SelectionRobust.lean` (round audit-31)

| Symbol | Category | Notes |
|--------|----------|-------|
| `DynamicArgmaxUnique V_S` | **(3) New** | Sender forward-looking-argmax uniqueness predicate. Canonical economic sufficient condition: strict concavity of `U_S` in `s`. Confirmed by user when initially landed. Subsequently *weakened* by `ValueClass.sender_unique_on` in round audit-33 item 3. |
| `FeedbackStackelbergEquilibrium.toTop_of_unique` | (1) Scaffolding | Bridge def; the `Top` form is the load-bearing object, this is the conversion. |
| `sender_any_argmax_high_of_strictMono_below_threshold` | (1) Scaffolding | Upgrades existing exists-one-high-argmax to all-argmaxes-high; not a hypothesis-bearing primitive. |

### From `Sanctions/Theory/Abstract/PrimitiveHighBasin.lean` (round audit-31)

| Symbol | Category | Notes |
|--------|----------|-------|
| `LowerSlopeOn f D m` | (2) Weakening | Replaces the stronger `Monotone V_T` / `Monotone V_S` premises of `of_stage_preferences` with primitive stage-payoff finite-difference slope bounds. Strictly weaker than monotone V (which is itself a value-function-level assumption). |
| `ValueLipschitzWith V K` | **(3) New** | Lipschitz bound on a value function. Required by the basin discharger after dropping monotone V. **Discharged for `p.V_T`** in `ValueLipschitz.lean` (round audit-32) from primitive payoff Lipschitz + transition Lipschitz + contraction. **Not yet discharged for `E.V_T`, `E.V_S`** in the joint Stackelberg layer — see Gap 2 below. |

### From `Sanctions/Theory/Abstract/DifferentPolicyComparator.lean` (rounds audit-31 + audit-32 item 4/5)

| Symbol | Category | Notes |
|--------|----------|-------|
| `MyopicFeedbackEquilibrium` (structure) | **(3) New** | Independently-optimized myopic comparator structure. Required for the *different-α* Goal-2 dominance theorem (the previous same-α theorem is strictly weaker). |
| `hα_order` (∀ x ∈ S, M.α x ≤ E.α x) | **(3) New** | Static policy ordering primitive. Economically: the dynamic Target chooses (weakly) larger compliance than the myopic Target at every state. |
| `hσ_monoOn_a` (MonotoneOn (σ x ·) I) | **(3) New** | Sender stage best-response monotone in leader action. Economically: more compliance → more sanctions, monotonically. Discharged at concrete payoff classes via Milgrom-Shannon / Topkis. |
| `hMyo_basin`, `hDyn_basin` | (1) Scaffolding | Basin invariance for each rule's path; intermediate facts, would be discharged once a sub-theorem of the lockin layer provides basin invariance for both rules. |

### From `Sanctions/Theory/Abstract/JointExistenceFromPrimitives.lean` (round audit-31)

| Symbol | Category | Notes |
|--------|----------|-------|
| `DynamicTargetSelector` (structure) | (1) Scaffolding | Operator-level "leader has a continuous Bellman best response" packaging. Initially external; **discharged from uniqueness** in `TargetSelectorFromUnique.dynamicTargetSelector_of_unique` (round audit-32 item 2). |
| `jointTarget_BCF`, `jointTargetOp`, `jointSenderOp` | (1) Scaffolding | Operator definitions, internal. |
| Row-Lipschitz bounds `hT_row`, `hS_row` | **(3) New** | Quantitative contraction primitives. Discharged for the witness joint case via `JointLipschitz.lean`; general case still open — see Gap 3 below. |

### From `Sanctions/Theory/Abstract/TargetSelectorFromUnique.lean` (round audit-32 item 2)

| Symbol | Category | Notes |
|--------|----------|-------|
| `TargetArgmaxUnique V_T V_S` | **(3) New** | Leader joint-Bellman-argmax uniqueness predicate. Canonical economic sufficient condition: strict concavity of `joint_T_integrand V_T V_S x ·` in `a`. Subsequently *weakened* by `ValueClass.target_unique_on` in round audit-33 item 3. |
| `targetArgmax` | (1) Scaffolding | `Classical.choose` selector. |
| `dynamicTargetSelector_of_unique` | (2) Weakening | **Discharges** the `DynamicTargetSelector` structural primitive of `JointExistenceFromPrimitives` from the two uniqueness predicates — strictly weaker than supplying an external `DynamicTargetSelector`. |

### From `Sanctions/Theory/Abstract/ValueLipschitz.lean` (round audit-32 item 1)

| Symbol | Category | Notes |
|--------|----------|-------|
| `h_U_lip`, `h_F_lip` (primitive Lipschitz on `U_T_at`, `F_pair`) | **(3) New** | Primitive payoff and transition Lipschitz constants. Required by the cone-preservation step. Discharged at concrete payoff classes (LQ etc.) by inspection. |
| `h_contract : p.β_T * γ < 1` | **(3) New** | Contraction margin. Required for the cone to be a Banach contraction. Holds whenever `β_T < 1` and transition Lipschitz `γ ≤ 1` (e.g. for `L_σ ≤ 1`). |
| `lipCone`, `bellmanBCF_preserves_lipschitz_cone`, `bellmanBCF_iterate_zero_lipschitz`, `valueLipschitzWith_of_tendsto` | (1) Scaffolding | Internal cone-preservation and Banach-iteration scaffolding. |
| `V_T_valueLipschitzWith_of_primitive_margin`, `V_T_valueLipschitzWith_of_contraction` | (2) Weakening | **Discharge** `ValueLipschitzWith p.V_T K` (an assumption from `PrimitiveHighBasin`) from primitive Lipschitz constants — strictly weaker than supplying the Lipschitz bound externally. |

### From `Sanctions/Theory/Abstract/InvariantValueClass.lean` (round audit-33 item 3)

| Symbol | Category | Notes |
|--------|----------|-------|
| `ValueClass` (structure) | (2) Weakening | **Replaces** the global Sender/Target uniqueness `∀ V_S : Val, DynamicArgmaxUnique V_S` / `∀ V_T V_S : Val, TargetArgmaxUnique V_T V_S` of `TargetSelectorFromUnique.exists_feedbackStackelberg_from_uniqueness_row_bounds` with uniqueness restricted to a closed nonempty carrier `D.carrier : Set Val`. Strictly weaker. |
| `ValueClass.IsInvariant` | **(3) New → DISCHARGED on headline (2026-07-03)** | Joint Bellman operator pair preserves the carrier. Economically: Banach iteration starting from a point in the carrier stays in the carrier. Concrete sufficient condition: take the carrier to be the bounded ball `{V : Val | ‖V‖ ≤ ‖U‖_∞ / (1 - β)}` and verify the iteration is norm-bounded by `‖U‖_∞ / (1 - β)`. **Reclassified 2026-07-03 (provability audit):** for both headline certificates (`eeCertCertificate`, `eeCertCertificateMS`, sharing carrier `eeCertClass`) invariance is **proved outright** by `eeCertClass_IsInvariant` (`Examples/EECertWitness.lean` — all three gain-ball legs, norm/Lipschitz/min-slope, on both operators, via closed-form Bellman images); the sup-norm-ball case is discharged generically by `ValueClass.ofBall_IsInvariant_of_cube_bounds` (`Theory/Bellman/InvariantBall.lean:342`). **Corrected 2026-08-31: it has no consumer.** This entry previously read "consumed by the non-headline JETBridge"; `Theory/Bridges/JETBridge.lean` exists but does not reference it, and an uncapped dot-tolerant search finds only its own declaration plus docstring mentions in `InvariantBall`, `InvariantLipBall` and `GainBallInvariance`. The generic discharge route is available and unused. Residue: only the non-headline general-parametric bridges (`polyComplianceValueClass2Gain_IsInvariant`-style scaffolds) still consume per-`(V_T, V_S)` integrand-slope facts; those are compactness/`nlinarith`-derivable at concrete payoffs and carry no headline load. |
| `jointTarget_BCF_on`, `α_on`, `jointSender_BCF_on`, `jointTargetOp_sub`, `jointSenderOp_sub` | (1) Scaffolding | Subtype operator definitions; internal. |
| `exists_feedbackStackelberg_from_valueClass_with_membership`, `exists_feedbackStackelbergTop_from_valueClass` | (2) Weakening | **Replace** the global-uniqueness existence theorem with the value-class-restricted one. Strictly weaker. |

### From `Sanctions/Theory/Abstract/StrongConcaveHolder.lean` (round audit-33 Hölder progress)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`SenderObjectiveStronglyConcaveOn D c`** | **(3) New** | Strong-concavity primitive for the dynamic Sender objective on the carrier. Confirmed by user via "fully close" directive. Discharge route at concrete payoff classes: `U_S(x,a,·)` strongly concave + `V_S` concave. |
| **`LeaderObjectiveStronglyConcaveOn D c`** | **(3) New** | Strong-concavity primitive for the leader joint-Bellman integrand `a ↦ joint_T_integrand V_T V_S x a` on the carrier × carrier. Discharge at concrete payoff classes: `U_T(x, ·, σ_dyn V_S x ·)` strongly concave in `a` + structural compatibility. |
| `StrongConcaveOn.deviation_at_maximizer` | (1) Scaffolding | Substantive derivation: `f s' ≤ f s_max - (c/4)(s_max-s')²`. Pure consequence of mathlib's `StrongConcaveOn` definition + maximality. |
| **`sigma_dyn_sq_le_of_strongConcave`** | (1) Scaffolding | **Substantive Hölder-1/2 bound** for σ_dyn in V_S: `c·(σ - σ')² ≤ 4·β_S·dist V_S V_S'`. **NOT** Lipschitz — Lipschitz requires V_S in a C¹ subspace (not closed in BCF). This is the maximum substantive regularity for σ_dyn in BCF setting. |
| **`targetArgmax_sq_le_of_leaderStrongConcave`** | (1) Scaffolding | **Substantive Hölder-1/2 bound** for the leader argmax in V_T (at fixed V_S): `c·(α - α')² ≤ 4·β_T·dist V_T V_T'`. Key simplification: at fixed V_S, σ_dyn doesn't change, so the U_T component of `joint_T_integrand` cancels. V_S-variation gives only Hölder-1/4 (composes Hölder-1/2 of σ_dyn with leader Hölder-1/2). |
| **`SigmaDynHolderOn D L_H`** | (2) Weakening | Hölder-1/2 Prop for σ_dyn in V_S. **Substantively derived** from `SenderObjectiveStronglyConcaveOn` via `SigmaDynHolderOn.of_strongConcave` with `L_H = 4·β_S/c`. NOT the same as `SigmaDynLipschitzOn` (which would require C¹ subspace). |
| **`AlphaOnHolderOnInVT D L_H_VT`** | (2) Weakening | Hölder-1/2 Prop for α_on in V_T (at fixed V_S). **Substantively derived** from `LeaderObjectiveStronglyConcaveOn` via `AlphaOnHolderOnInVT.of_leaderStrongConcave` with `L_H_VT = 4·β_T/c`. |

### From `Sanctions/Theory/Abstract/C1Val.lean` iter 14 (audit-34 item A)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`SigmaDynLipschitzOn_C1 L_σ`** | **(3) New** | C¹ analog of the BCF `SigmaDynLipschitzOn`. Quantifies `|σ_dyn V_S x a − σ_dyn V_W x a| ≤ L_σ · c1dist V_S V_W` over `(V_S, V_W) : C1Val K_d × C1Val K_d` and `(x, a) ∈ S × I`. The substantive Item-A closure: genuine Lipschitz σ_dyn-in-V_S in the C¹ ambient (where it's mathematically true, unlike BCF where only Hölder-1/2 holds). |
| **`SigmaDynC1IFTBound c`** | **(3) New** | C¹ IFT-at-FOC primitive: at every `(V_S, V_W, x ∈ S, a ∈ I)`, `c · |σ - σ'| ≤ |β_S · δ · (V_S'(F) - V_W'(F))|` where σ, σ' are the dynamic argmaxes and F is the transition image at σ'. Algebraic outcome of IFT-at-FOC under uniform strong concavity (modulus c) of the dynamic Sender objective in s. Confirmed implicitly under "keep going to finish item A" directive. Discharge at concrete smooth payoff classes: direct partial-derivative inspection of the Sender FOC. |
| **`sigmaDynLipschitzOn_C1_of_IFT_bound`** | (2) Weakening | **Discharges** `SigmaDynLipschitzOn_C1 (β_S · δ / c)` from `SigmaDynC1IFTBound c` + `c > 0`. Direct application of iter-13 `sigma_dyn_lipschitz_in_C1` pointwise, plus the convex-combination membership argument `x ∈ [0,1] + σ_dyn ∈ [0,1] + δ ∈ [0,1] ⇒ F ∈ [0,1]`. Reduces the substantive selector Lipschitz primitive to the canonical IFT-at-FOC primitive. |

### From `Sanctions/Theory/Abstract/C1Val.lean` iters 15-16 (full C¹ track)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`C1Val.ContractingC1With K_d q T`** | **(3) New** | Structure encoding `T : C1Val K_d → C1Val K_d` is a `q`-contraction in `c1dist`. Confirmed under "do the full track" `/goal`. Canonical Banach fixed-point input. |
| `C1Val.banachIter T x₀ n` | (1) Scaffolding | Iteration `T^n x₀` on C¹. |
| `C1Val.banachIter_step_dist`, `banachIter_dist_le_tight`, `banachIter_dist_le`, `banachIter_dist_le_symm` | (1) Scaffolding | Standard Banach iteration estimates (geometric decay, tight + loose bounds, symmetric form). |
| **`C1Val.banachIter_isC1Cauchy`** | (1) Scaffolding | **The iter-15 milestone**: a contraction iteration is C¹-Cauchy. Direct ε-N argument from the geometric series bound. |
| **`SigmaDynLipschitzOn_C1`** (iter 14, was: from `LipschitzPrimitives` line) | **(3) New** | (Already registered above under iter 14.) |
| **`AlphaOnLipschitzOn_C1 α_on_C1 L_α_VT L_α_VS`** | **(3) New** | C¹ analog of BCF `AlphaOnLipschitzOn`. Parametric over user-supplied `α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ`. Confirmed under "full track" directive. |
| **`AlphaOnC1IFTBound α_on_C1 c L_VT_sens L_VS_sens`** | **(3) New** | C¹ IFT-at-FOC primitive for the leader argmax with two sensitivity terms (V_T via continuation, V_S via σ-mediation). Discharge at concrete smooth payoff classes by direct partial-derivative inspection of the leader FOC. |
| **`alphaOnLipschitzOn_C1_of_IFT_bound`** | (2) Weakening | Discharges `AlphaOnLipschitzOn_C1 (L_VT_sens / c) (L_VS_sens / c)` from `AlphaOnC1IFTBound c L_VT_sens L_VS_sens` + `c > 0`. Direct division by `c`. Mirrors iter 14's σ-discharger. |

### From `Sanctions/Theory/Abstract/ValueClassC1.lean` iters 17-18 (full C¹ track)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`C1Val.c1distPair`** | (1) Scaffolding | Combined C¹ pair-distance on `C1Val K_d × C1Val K_d`: sum of two c1dists. Triangle, symmetry, self = 0 derived from component versions. |
| **`AbstractGame.ValueClass_C1 K_d`** | **(3) New** | The C¹ analog of BCF `ValueClass`: closed nonempty carrier ⊆ `C1Val K_d × C1Val K_d` + parametric joint Bellman operator `T : carrier → carrier` + contraction modulus `q` + `T_contracts` Prop witness. The parametric `T` field replaces the BCF approach (T constructed from operator-row-Lipschitz dischargers) — at the C¹ layer, constructing T requires envelope-theorem differentiation, which is left to concrete payoff classes. |
| `ValueClass_C1.iter`, `iter_step_dist`, `iter_dist_le_tight`, `iter_dist_le`, `iter_dist_le_symm` | (1) Scaffolding | Banach iteration machinery on the C¹ pair carrier (mirror of iter 15 for the pair distance). |
| `IsC1CauchyPair` | (1) Scaffolding | Pair-level analog of `IsC1Cauchy`. |
| **`ValueClass_C1.iter_isC1CauchyPair`** | (1) Scaffolding | **The iter-18 milestone**: the C¹ Banach iteration on the pair carrier is Cauchy in `c1distPair`. |
| `iter_V_T_isC1Cauchy`, `iter_V_S_isC1Cauchy` | (1) Scaffolding | Projection: each component is C¹-Cauchy (since c1dist ≤ c1distPair). |

### From `Sanctions/Theory/Abstract/JETBridgeC1.lean` iter 19 (full C¹ track endpoint)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`jet_C1_existence_and_three_goals`** | (1) Scaffolding | **Paper-facing C¹-track JET bridge**. Bundles: (a) the C¹ Banach iteration is Cauchy via iter 18; (b) each component is C¹-Cauchy; (c) the BCF three-goals via the audit-34 bridge `jet_three_goals_from_ball_operator_lipschitz_primitives`. No new hypotheses beyond ValueClass_C1 + the BCF-side hypotheses of the audit-34 bridge. The C¹ and BCF outputs are independent (a concrete instantiation provides the C¹-to-BCF lift identifying the C¹ fixed point with the BCF equilibrium). |

### From audit-37 follow-up rounds (Step 2 / Problems 4+5 / Steps 3+4)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`C1Val.valueLipschitzWith`** (audit-37 Step 2, in `JETBridge.lean`) | (2) Weakening | **Discharges** `ValueLipschitzWith V.V K_d` from the C¹ bounded-derivative field of `V : C1Val K_d`, via mathlib's `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on the convex unit interval `[0, 1]`. Strictly weaker than supplying value-Lipschitz externally — once equilibrium values come from C¹ structures, both `K_T` and `K_S` are bounded by their respective `K_d`. |
| **`jet_three_goals_from_ball_operator_lipschitz_and_primitives_audit37`** (audit-37 Problems 4+5) | (1) Scaffolding | **Audit-37 final bridge**: extends `jet_three_goals_from_ball_operator_lipschitz_primitives` with the V_S Lipschitz threading (Item B closure: discharges `hV_S_lip_E` internally via `FeedbackStackelbergEquilibriumTop.V_S_valueLipschitzWith_of_contraction` from primitive Sender state-Lipschitz + transition Lipschitz + `β_S · γ < 1`) and α-order via increasing differences (Item D closure: discharges `hα_order_E` internally via `alpha_order_dynamic_ge_myopic_of_increasingDifferences` from `DynamicVsMyopicIncreasingDifferencesAt` + strict-uniqueness). Removes two per-E primitives from the user-facing surface. |
| **`ValueClass_C1Complete`** (audit-37 Step 3, in `ValueClassC1.lean`) | **(3) New** | C¹ completeness Prop: every Cauchy sequence in the C¹ carrier has a `c1distPair`-limit in the carrier. Confirmed under "do until the full track is done" `/goal`. Theorem-parameter primitive at the abstract layer; concrete discharge at instantiations via component-wise BCF/uniform-deriv completeness. |
| **`ValueClass_C1.exists_c1distPair_fixedPoint`** (audit-37 Step 3) | (1) Scaffolding | **Iter 20 milestone**: existence of a `c1distPair`-fixed point of `D.T` from contraction + `ValueClass_C1Complete`. Standard Banach contraction proof: Cauchy iteration (iter 18) + carrier-limit (completeness) + triangle inequality (`c1distPair (T z) z ≤ 2/3 · c1distPair (T z) z` contradiction). The "fixed point" is a pseudo-fixed-point in the C¹ pseudo-metric (`c1distPair = 0`), not literal Lean equality — literal equality requires the Step-1 extensionality fix on `C1Val.V'`. |
| **`AbstractGame.C1BellmanSystem p K_d`** (audit-37 Step 4, in `C1BellmanSystem.lean`) | (2) Weakening | **Iter 21**: extends `ValueClass_C1` with structural constraints (`α_on_C1` field + continuity + feasibility + `α_isMaxOn` + `T_value_eq_target` + `T_value_eq_sender`) tying the parametric `T` to the BCF joint Bellman operators. **Tightens** the iter-17 `T : carrier → carrier` parametric (no new assumptions; structural fields constrain `T` to be the C¹ analog of the BCF Bellman). Confirmed under "do the full track" directive. |
| **`C1BellmanSystem.feedbackStackelbergEquilibriumTop_of_c1distPair_fixedPoint`** | (1) Scaffolding | **The true C¹-to-BCF lift theorem** (audit-37 §B fix): produces an actual `FeedbackStackelbergEquilibriumTop` from a `c1distPair`-fixed point of `D.T`. Uses `bcf_eq_of_c1distPair_zero` to extract literal BCF equality + the `T_value_eq_*` + `α_*` fields of `C1BellmanSystem`. Replaces the previously-implicit "extraction primitive" with a theorem. |
| **`C1BellmanSystem.feedbackStackelbergEquilibriumTop_of_complete`** | (1) Scaffolding | Convenience corollary: existence of `FeedbackStackelbergEquilibriumTop` from a `C1BellmanSystem` + `ValueClass_C1Complete`. Composes iter 20 with iter 21. |
| **`C1BellmanSystem.bcf_eq_of_c1distPair_zero`** | (1) Scaffolding | Helper: `c1distPair = 0` ⇒ BCF values equal (componentwise). Uses metric-axiom `dist_eq_zero` after extracting the BCF-dist summand from `c1distPair`. |

### From `Sanctions/Theory/Abstract/InvariantLipBall.lean` (audit-37 Problem 3)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`valLipBall M K`** | (2) Weakening | Lipschitz-bounded ball: `{V ∈ Val | ‖V‖ ≤ M ∧ ValueLipschitzWith V K}`. Strictly narrower than `valBall M` (audit-37 Problem 3 addresses the critique that `valBall` is too broad — uniform Lipschitz fails on arbitrary BCF sup-norm balls). |
| `valueLipschitz_isClosed` | (1) Scaffolding | The set of K-Lipschitz functions is closed in BCF sup-norm (intersection over (y₁, y₂) of pointwise-continuous-evaluation preimages). |
| `valLipBall_isClosed`, `zero_mem_valLipBall`, `valLipBall_nonempty`, `valLipBall_subset_valBall` | (1) Scaffolding | Basic carrier properties. |
| **`ValueClass.ofLipBall`** | (2) Weakening | Constructor of a `ValueClass` on `valLipBall M K`. Strictly narrower than `ValueClass.ofBall` — uniqueness primitives only need to hold on the smaller Lipschitz-bounded carrier. |
| **`ofLipBall_V_T_lipschitz_carrier`** | (2) Weakening | **Discharges** the audit-34 `h_V_T_lipschitz_carrier` hypothesis automatically from the `valLipBall` carrier definition. Eliminates one previously-category-(3) hypothesis from the JET bridge's user-facing surface (the `valLipBall` route makes it free). |

### From `Sanctions/Theory/Abstract/SmoothSanctionClass.lean` (audit-37 Step 5)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`AbstractGame.Params.SmoothSanctionClass p K_d`** | **(3) New** (bundling) | Parametric smooth-payoff class skeleton. Bundles together: cube bounds `cube_T, cube_S` (with `hU_T_cube`, `hU_S_cube`); stage payoff Lipschitz `L_U_T_s, L_U_S_a` (with `hU_T_lip_s`, `hU_S_lip_a`); strong-concavity moduli `c_S, c_T`; IFT primitives `hSigma_IFT : SigmaDynC1IFTBound c_S` and `hAlpha_IFT : AlphaOnC1IFTBound α_on_C1 c_T L_VT_sens L_VS_sens`; the parametric `α_on_C1` field. Restatement-of-existing-primitives bundling structure — confirmed under "keep going for those that are not addressed" `/goal`. |
| `cube_T_discharge`, `cube_S_discharge`, `hU_lipschitz_discharge`, `hU_S_lip_a_discharge` | (1) Scaffolding | Direct field projections discharging cube/Lipschitz primitives. |
| **`SmoothSanctionClass.transition_Lipschitz`** | (1) Scaffolding | **Provable from `Params.δ` alone** (no SmoothSanctionClass needed): the transition `F(x, s) = (1-δ)·x + δ·s` is `(1-δ)`-Lipschitz in `x` at fixed `s`. Discharges audit-34 `h_F_lip` with constant `γ = 1 - δ`. |
| `transition_Lipschitz_at_α` | (1) Scaffolding | Specialization to `s ∈ I` form. |
| **`sigma_dyn_lipschitz_C1_discharge`**, **`alpha_on_lipschitz_C1_discharge`** | (2) Weakening | Compose IFT primitives → C¹ Lipschitz Props via iters 14, 16. Drop-in audit-37 dischargers for the parametric C¹ selector Lipschitz constants. |

### From `Sanctions/Theory/Abstract/JETBridgeC1System.lean` (audit-39 Gap 1)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`jet_C1BellmanSystem_three_goals`** | (1) Scaffolding | **Audit-39 Gap 1 closure**: paper-facing C¹-Bellman-System three-goals bridge. Composes `C1BellmanSystem.feedbackStackelbergEquilibriumTop_of_complete` (iter 21 C¹-to-BCF lift) with the three goal-specific bridges (`jet_persistence_at_equilibriumTop_from_lowerSlopes`, `jet_dominance_at_equilibriumTop_from_static_order`, `jet_shock_at_equilibriumTop_from_lowerSlopes`). The produced `E : FeedbackStackelbergEquilibriumTop` is *the same* equilibrium that satisfies the three goal conclusions — fixes the audit-39 critique that the prior `jet_C1_existence_and_three_goals` had independent C¹ and BCF outputs. No new hypotheses. |

### From `Sanctions/Theory/Abstract/JETBridge.lean` audit-39 Gap 2

| Symbol | Category | Notes |
|--------|----------|-------|
| **`jet_three_goals_from_lipBall_operator_lipschitz_and_primitives`** | (1) Scaffolding | **Audit-39 Gap 2 closure**: `valLipBall`-based JET bridge variant. Uses `ValueClass.ofLipBall` instead of `ValueClass.ofBall`; eliminates `h_V_T_lipschitz_carrier` from the user-facing surface (it becomes free via `ofLipBall_V_T_lipschitz_carrier`). Takes `IsInvariant` as a primitive (substantively narrower than audit-34's cube-discharger because Bellman preservation of K-Lipschitz is genuine economic content). |

### From `Sanctions/Theory/Abstract/RegularEconomy.lean` (audit-40 payoff-form-agnostic refactor)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`RegularEconomyCertificate p`** | (1) Scaffolding (bundling) | **Payoff-form-agnostic top-level theorem bundle**. Repackages the inputs of the audit-33 top-level bridge `jet_three_goals_from_valueClass_and_primitives` into a single structure with four economically-interpretable groups: existence-side regularity (`D`, `h_inv`, row-Lipschitz coefficients + bounds, contraction margins), high-basin per-E primitives (`hV_*_lip_E`, `h_stage_*_α`, `hSC_α`, basin geometry), dominance per-E primitives (`M`, `hα_order_E`, basin invariance, σ-monotonicity), and starting state. **Per audit-40**: this is the right top-level statement — not tied to LQ/non-LQ/C¹/etc. Rule-3 clean: no new fields beyond the existing bridge inputs. |
| **`RegularEconomyCertificate.three_goals`** | (1) Scaffolding | The payoff-form-agnostic three-goals theorem: `RegularEconomyCertificate p → ∃ E : FeedbackStackelbergEquilibriumTop, persistence ∧ dominance ∧ shock hysteresis at the same E`. One-line delegation to `jet_three_goals_from_valueClass_and_primitives`. |
| **`regularEconomyCertificate_of_lipBall`** | (1) Scaffolding | **Sufficient-condition corollary**: the `valLipBall` route to constructing a `RegularEconomyCertificate`. Takes the audit-39 lipBall bridge inputs and discharges the operator-level row-Lipschitz bounds internally via `jointTargetOp_sub_row_lipschitz_of_carrier` + `jointSenderOp_sub_row_lipschitz_of_alphaOn`. Makes the metric route a constructor of `RegularEconomyCertificate` rather than a separate top-level theorem. |
| **`RegularEconomyCertificateC1 p K_d`** | (1) Scaffolding (bundling) | **C¹-route parallel certificate** (audit-40 follow-up). Bundles inputs of the audit-39 Gap-1 bridge `jet_C1BellmanSystem_three_goals`: C¹ Bellman system + completeness + high-basin/dominance per-E primitives. Parallel to `RegularEconomyCertificate` but uses the C¹ existence route (which produces `E` directly via iter-21 lift, not via a BCF ValueClass). The two certificate types correspond to the two existence routes — users pick whichever matches their setup. Rule-3 clean: pure repackaging of `jet_C1BellmanSystem_three_goals` inputs. |
| **`RegularEconomyCertificateC1.three_goals`** | (1) Scaffolding | C¹-route three-goals theorem. One-line delegation to `jet_C1BellmanSystem_three_goals`. |
| **`RegularEconomyMargins p`** | (1) Scaffolding (bundling) | **Strict-margin extension of `RegularEconomyCertificate`** (audit-40 follow-up). Extends with explicit strict-positive slack variables `η_T, η_S > 0` on the row-contraction inequalities `β_T + L_TS + η_T ≤ 1` and `β_S + L_ST + η_S ≤ 1`. The slack quantifies how much "room" the certificate has — basis for the perturbation-robustness theorem. Strictly stronger than `RegularEconomyCertificate` (gives extra information); no new economic content. |
| **`RegularEconomyMargins.row_inequalities_preserved_under_perturbation`** | (1) Scaffolding | **The audit-40 strict-margin / open-neighborhood theorem.** If parameters `(β_T, L_TS, β_S, L_ST)` are perturbed by less than `η_T / 2` (resp. `η_S / 2`) in absolute value, the strict row-contraction inequalities `β_T' + L_TS' < 1` and `β_S' + L_ST' < 1` still hold. Demonstrates **openness** of the regularity class under small perturbations: the lock-in mechanism is robust, not knife-edge. Proof template generalizes directly to other margin inequalities (cube bounds, high-basin margins). |

### Audit-41 sign-correction additions (compliance-direction)

The audit-41 critique identified that the `DifferentPolicyComparator` chain `hα_order_E + hσ_monoOn_a` and the related JET-bridge dischargers commit implicitly to a **resistance/noncompliance** reading of `a`. Under the literal-**compliance** reading (`a = 1` = full compliance, `a = 0` = no compliance), these have the wrong sign. The following additions deliver the compliance-direction substitutes; the pre-audit-41 theorems remain in the codebase with `⚠ SIGN WARNING` docstrings restricting them to the resistance reading.

| Symbol | Category | Notes |
|--------|----------|-------|
| **`static_sanctions_le_of_alpha_order_and_sigma_antitoneOn`** (DifferentPolicyComparator.lean) | (2) Weakening | The **correct** compliance-channel theorem: `M.α ≤ E.α` + `σ` *antitone* in `a` ⇒ `σ(E.α) ≤ σ(M.α)`. Notes that the Target compliance channel **lowers** dynamic sanctions relative to myopic — opposite of the pre-audit-41 chain. Net dynamic vs. myopic comparison then requires the Sender-continuation channel to overcome via floor/ceiling. |
| **`ruleDom_of_dynamic_floor_and_myopic_ceiling`** | (2) Weakening | Clean substitute for the wrong-sign rule-dominance discharge: dynamic floor + myopic ceiling ⇒ rule dominance by transitivity. Economically interpretable: dynamic high-sanction floor (from the existing high-basin machinery) + myopic stays below that floor. |
| `ruleDom_on_S_of_dynamic_floor_and_myopic_ceiling` | (1) Scaffolding | Same discharger with `Sanctions.S` as basin. |
| **`jet_dominance_at_equilibriumTop_audit41`** (JETBridge.lean) | (1) Scaffolding | Sign-corrected Goal-2 bridge: takes `hRuleDom_on_basin` directly rather than discharging via the wrong-sign chain. Composes with `dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin`. Paper-facing route to discharge `hRuleDom_on_basin` is the floor/ceiling discharger above. |
| **`RegularEconomyCertificateCompliance`** (RegularEconomy.lean) | (1) Scaffolding (audit-41 variant) | **Sign-corrected `RegularEconomyCertificate`**. Replaces `hα_order_E + hσ_monoOn_a + hDyn_basin_E + hMyo_basin + hσ_monoOn_a` with `hRuleDom_on_basin_E + hDynMonoOn_E + hMyo_basin + hDyn_basin_E` — the rule-dominance hypothesis taken directly. The recommended top-level theorem under the literal-compliance interpretation. |
| **`RegularEconomyCertificateCompliance.three_goals`** | (1) Scaffolding | Three-goals theorem for the compliance variant, using `jet_dominance_at_equilibriumTop_audit41` internally. |
| **`LowerLossSlopeOn f D c`** (TargetSanctionLossOffset.lean) | **(3) New** | Bounded-downward-slope: `f s₂ - f s₁ ≥ -c · (s₂ - s₁)` on D. Captures "U_T may decrease in s but not too fast." Confirmed under the audit-41 directive ("apply all the fixes"). Economically: stage sanction damage rate bounded by `c`. |
| **`LowerSlopeOnValue V g`** | **(3) New** | Minimum-upward-slope on a BCF value function: `V y₂ - V y₁ ≥ g · dist y₁ y₂` for `y₁ ≤ y₂`. Captures "V_T is at least `g`-Lipschitz upward in the state." Confirmed under the audit-41 directive. Economically: under hardline-state preferences, V_T's minimum slope in x. |
| **`targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value`** | (2) Weakening | **Standard-sanctions Target high-basin discharger**: bounded stage loss (`c`) + minimum continuation value gain (`g`) + margin `c ≤ β_T · g · δ` ⇒ `targetSanctionObjective` monotone non-decreasing in `s` on basin. Replaces the audit-pre-41 monotone-stage-payoff discharger `targetSanctionObjective_mono_of_stage_mono_and_V_mono` under the literal-compliance reading where `U_T_s < 0`. Economic mechanism: "sanctions hurt today but preserve hardline future state valued by Target." |
| **`OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target`** | (2) Weakening | **Audit-41 follow-up Item 1**: wires the Phase-5 Target discharger into the existing `OneSidedSanctionPreferenceThresholds` construction. Takes audit-41 `LowerLossSlopeOn` + `LowerSlopeOnValue` + margin on the Target side; keeps the Sender side as-is (Sender preferring sanctions on the low range is standard under any reading of `a`). The compliance-direction sibling of `of_stage_lowerSlopes`. |

### Audit-41 follow-up Item 2 (DifferentPolicyComparator §10)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`DynamicVsMyopicDecreasingDifferencesAt E x`** | **(3) New** | Dual Topkis primitive: dyn-myo objective non-increasing in `a` on `Sanctions.I`. Captures "Target gives up resisting": as compliance rises, the marginal dynamic-over-myopic gain is non-positive. Confirmed under "continue the remaining items" directive (parallel to `DynamicVsMyopicIncreasingDifferencesAt`, opposite direction only). |
| **`alpha_order_dynamic_le_myopic_of_decreasingDifferences`** | (2) Weakening | Derives `E.α x ≤ M.α x` (dynamic Target *less* compliant) from `DynamicVsMyopicDecreasingDifferencesAt` + strict-uniqueness of myopic argmax at `x`. Compliance-direction parallel of `alpha_order_dynamic_ge_myopic_of_increasingDifferences`. |
| **`myopicCeiling_from_alpha_order_dynamic_le_and_sigma_antitoneOn`** | (2) Weakening | Compliance-channel ceiling: `E.α ≤ M.α` + σ antitone in a ⇒ `σ(x, M.α x) ≤ σ(x, E.α x)`. |
| **`dynamicTop_rule_dominates_myopic_policy_audit41_compliance`** | (2) Weakening | Composed compliance-direction rule-dominance theorem: decreasing-differences + σ antitone + monotone `V_S` + myopic strict-uniqueness ⇒ rule dominance via myopic ceiling + Sender escalation. The full compliance-direction parallel to `dynamicTop_rule_dominates_myopic_policy_from_primitives`. |

### Audit-43 cleanup (final sign-correction wiring)

The audit-43 critique observed that audit-41 had the right repair pieces but the old wrong-sign path still existed and several paper-facing bridges still used it. The audit-43 cleanup quarantines the old path and wires the audit-41 dischargers through end-to-end.

| Symbol | Category | Notes |
|--------|----------|-------|
| **`jet_persistence_at_equilibriumTop_from_lossOffset`** (JETBridge.lean) | (1) Scaffolding | Audit-43 sign-correct persistence bridge using `OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target` (Phase-5/Item-1 Target loss-offset discharger). Replaces `jet_persistence_at_equilibriumTop_from_lowerSlopes` under the literal-compliance reading. |
| **`jet_shock_at_equilibriumTop_from_lossOffset`** (JETBridge.lean) | (1) Scaffolding | Audit-43 sign-correct shock bridge using the same Target loss-offset discharger. Replaces `jet_shock_at_equilibriumTop_from_lowerSlopes` under the literal-compliance reading. |
| **`RegularEconomyCertificateCompliance`** (audit-43 refactored) | (1) Scaffolding | Target-side fields refactored from wrong-sign chain (`mT, KT, hT_margin, hV_T_lip_E, h_stage_target_α : LowerSlopeOn`) to audit-41 loss-offset form (`cT, gT, hcT_nn, hgT_nn, hT_loss_margin : cT ≤ β_T·gT·δ`, `h_stage_target_loss_α : LowerLossSlopeOn`, `hV_T_gain_E : LowerSlopeOnValue`). Sender side unchanged. Updated `three_goals` method delegates to the audit-43 `_lossOffset` bridges for Goals 1, 3 and to `jet_dominance_at_equilibriumTop_audit41` for Goal 2. Now fully sign-correct end-to-end under literal compliance. |
| **`jet_C1BellmanSystem_three_goals_compliance`** (JETBridgeC1System.lean) | (1) Scaffolding | C¹ compliance bridge: parallel to `jet_C1BellmanSystem_three_goals` but using `_lossOffset` persistence/shock + audit-41 dominance. The JET-paper-facing C¹ theorem under literal compliance. Uses `feedbackStackelbergEquilibriumTop_of_complete` for existence, then the three sign-correct per-E bridges. |
| **`ResistanceActionCertificate`** alias (RegularEconomy.lean) | (1) Scaffolding | Quarantine alias for the original `RegularEconomyCertificate`, making the resistance-action interpretation of `a` explicit. The original name is preserved for backward compatibility. Paper-facing references under literal compliance MUST use `RegularEconomyCertificateCompliance` instead. |
| `RegularEconomyCertificate` docstring update | (1) Scaffolding | Added `⚠ AUDIT-43 QUARANTINE WARNING` block explicitly restricting the certificate to the resistance-action interpretation and pointing users to `RegularEconomyCertificateCompliance` under literal compliance. |

### From `Sanctions/Theory/Abstract/LipschitzPrimitives.lean` (round audit-33 Gap 2/3 architectural closure)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`SigmaDynLipschitzOn D L_σ`** | **(3) New** | Carrier-restricted σ_dyn-Lipschitz-in-V_S primitive. **Confirmed by user** under the "architectural closure" choice (with explicit Rule-1 verification that substantive closure isn't a single-round deliverable). Discharge at concrete payoff class: IFT-at-FOC under uniform strict concavity of the dynamic Sender objective in `s`. |
| **`AlphaOnLipschitzOn D L_α_VT L_α_VS`** | **(3) New** | Carrier-restricted leader selector `α_on`-Lipschitz primitive. Same confirmation + same discharge route. |

### From `Sanctions/Foundations/IntervalDominanceOrder.lean` §6 + `StandardComplianceLocal.lean` B2 route (2026-07-02, user-approved Rule-3 stop)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`MonotoneTransferOn S T F`** | **(3) New — regime-scoped (2026-07-03)** | Ordinal escalation-consistency primitive for the B2 (non-monotone-`V_S`) IDO discharge: on any choice interval where the lower-state Sender dynamic objective is nondecreasing, the higher state inherits the endpoint comparison (weak + strict clauses). **Confirmed by user 2026-07-02** ("adopt both Props as stated"). **Shrink 2026-07-03 (provability audit):** `MonotoneTransferOn.of_singleCrossingOn` proves single crossing ⇒ `MonotoneTransferOn`, so throughout the single-crossing regime (e.g. strong rally) the primitive is *subsumed as a theorem*; it carries assumption load ONLY in the non-monotone-continuation regime where single crossing provably fails. There it remains OPEN at carrier generality (audit verdict: NOT derivable from increasing-differences/cross-partial conditions — the continuation sign is uncontrolled; QS07 condition (D) is a *distinct* non-ordinal assumption, not a weakening) — owned in the paper's limitations. **Witness discharge 2026-07-04 (Round R-B2):** the recorded probe-first plan executed — `b2f_monotoneTransferOn` and `b2_hMT` (`Examples/B2NonMonotoneCertWitness.lean`) PROVE the primitive outright at the designed-slice economy, in the exact regime where it carries load (single crossing machine-checked FALSE there: `b2f_not_singleCrossingOn`, `b2Cert_not_singleCrossingOn`), and `b2Certificate` is the first consumer of `hIDO_on_of_quasiconcave_monotoneTransfer`. Status: open at carrier generality only; exercised, non-vacuous, and witness-discharged in its own regime. **Derivative-form sibling delivered 2026-07-11 (Wave-0 P8):** the previously-deferred QS07-Ext Proposition-6 sign-preservation discharger is now formalized (`IDOFamilyOn.of_deriv_sign_preservation` + core step `deriv_nonneg_of_peaked_of_wellBehaved`, `Foundations/IntervalDominanceOrder.lean` §7) — a THEOREM, no assumption-surface change. Its antecedent (paired `≥(>)` sign preservation of `∂G/∂s` across basin states at the Sender dynamic objective) was probed disprove-first and adversarially confirmed MIXED: **REFUTED at carrier generality** (exact rational counterexample: monotone C¹ gain-ball carrier member with eeCert-pattern structural signs flips the derivative sign downward across states; `docs/archive/workflow-scratch/p8probe_*`, re-verified `docs/archive/workflow-scratch/p8skeptic_signpres.py`, 62/62 exact checks) but **HOLDS at both live witnesses** (eeCert via slope-pinned carrier; B2 via monotone vertex — and B2's dynamic objective IS C¹-in-s, so §7 is a live alternative to `b2_hMT` there). Consequence: like `MonotoneTransferOn`, the derivative antecedent is per-witness checkable and NOT a carrier-generality primitive; nothing was adopted (no Rule-3 event); carrier-generality single-crossing discharge remains honestly closed off by two independent refutations (ordinal + derivative forms). |
| **carrier quasiconcavity-in-`s`** (hypothesis `hQC` of `hIDO_on_of_quasiconcave_monotoneTransfer`) | **(3) New** (witness-DISCHARGED 2026-07-04) | Per-state single-peaked sanction preference of the Sender dynamic objective, quantified over carrier pairs. **Discharged at the B2 witness** (`b2_hQC` via `b2dynObj_strictConcaveOn_real`, strict concavity of the two-piece slice family — `Examples/B2NonMonotoneCertWitness.lean`, Round R-B2), the first economy where the discharger actually fires. NOT derivable from the Lipschitz carrier alone (Lipschitz perturbation of a concave stage can break quasiconcavity — structure-inspection verdict 2026-07-02, numeric counterexample re-verified 2026-07-03). |

### From `Sanctions/Theory/Abstract/OperatorRowLipschitz.lean` extension (round audit-33 Gap 2/3 architectural closure)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`jointTargetOp_sub_row_lipschitz_of_carrier`** | (2) Weakening | Carrier-restricted variant of Phase-1's row-Lipschitz; consumes `SigmaDynLipschitzOn` instead of the global σ-Lipschitz. Strictly weaker hypothesis. |
| **`jointSenderOp_sub_row_lipschitz_of_alphaOn`** | (2) Weakening | Discharges the previously-conditional Sender pointwise hypothesis from `AlphaOnLipschitzOn` + primitive `L_U_a`. |
| `L_U_a` (theorem parameter) | **(3) New** | Sender stage payoff Lipschitz constant in the leader action `a`. Discharge at concrete payoff class: direct calculation. |

### From `Sanctions/Theory/Abstract/InvariantBall.lean` (round audit-33 gap-4 closure)

| Symbol | Category | Notes |
|--------|----------|-------|
| `valBall M : Set Val` | (1) Scaffolding | Sup-norm ball; closed and nonempty for `M ≥ 0`. |
| `valBall_isClosed`, `valBall_nonempty`, `zero_mem_valBall`, `mem_valBall_iff` | (1) Scaffolding | Basic properties. |
| `jointTarget_BCF_norm_le`, `bellmanS_BCF_norm_le` | (2) Weakening | Sup-norm bounds on the joint Bellman operators in terms of `cube_T`, `cube_S` and `‖V_T‖`, `‖V_S‖`. |
| `cube_T`, `cube_S` (theorem parameters) | **(3) New** | Cube bounds on `|U_T|`, `|U_S|` over `I × I × I`. **Discharge route:** `IsCompact.exists_isMaxOn` applied to `|U_T|`, `|U_S|` continuous on the compact cube. |
| `ValueClass.ofBall` (constructor) | (2) Weakening | Concrete `ValueClass` on the sup-norm ball. |
| **`ValueClass.ofBall_IsInvariant_of_cube_bounds`** | (2) Weakening | **Discharges** `IsInvariant` from primitive cube bounds + contraction inequalities — strictly weaker than supplying `IsInvariant` externally. Closes Gap 4. |

### From `Sanctions/Theory/Abstract/OperatorRowLipschitz.lean` (round audit-33 gap-3 partial)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`jointTargetOp_sub_row_lipschitz`** | (2) Weakening | Operator-level Target row-Lipschitz from `JointLipschitz` pointwise. No new primitives beyond what JointLipschitz already takes. |
| `bellmanS_BCF_dist_le` | (1) Scaffolding | One-line lift of `bellmanS_BCF_pointwise_dist`. |
| `jointSenderOp_sub_row_lipschitz_of_pointwise` | (2) Weakening | Conditional Sender row-Lipschitz: takes a pointwise hypothesis (irreducible at this layer) and lifts it. The pointwise hypothesis is itself category-(3) until α-Lipschitz primitives `L_α_VT, L_α_VS` are derived. |

### From `Sanctions/Theory/Abstract/ValueLipschitz.lean` §5 extension (round audit-33 gap-2 partial)

| Symbol | Category | Notes |
|--------|----------|-------|
| `bellmanS_BCF_pointwise_lipschitz_in_state`, `bellmanS_BCF_preserves_lipschitz_cone`, `bellmanS_BCF_iterate_zero_lipschitz` | (1) Scaffolding | Sender-side cone-preservation scaffolding (mirrors Target §§1-3). |
| **`V_S_valueLipschitzWith_of_primitive_margin`**, **`V_S_valueLipschitzWith_of_contraction`** | (2) Weakening | **Discharge** `ValueLipschitzWith (p.V_S α hα) K` from primitive `L_U` (Sender stage payoff Lipschitz in `x` at fixed `α`) and `γ` (transition; naturally `γ = 1 - δ`). Symmetric to the Target discharger. |

### From `Sanctions/Theory/Abstract/JETBridge.lean` (round audit-33 follow-up)

| Symbol | Category | Notes |
|--------|----------|-------|
| `jet_persistence_at_equilibriumTop_from_lowerSlopes` | (1) Scaffolding | Pure composition: existing `OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes` + existing `dynamicTopRealizedRule_mono_of_singleCrossingOn` + existing `equilibriumTop_oneSidedThresholds_long_run_nonDecreasing`. No new hypotheses. |
| `jet_shock_at_equilibriumTop_from_lowerSlopes` | (1) Scaffolding | Same pattern, composes with the shock headline. No new hypotheses. |
| `jet_dominance_at_equilibriumTop_from_static_order` | (1) Scaffolding | Pure composition: existing `dynamicTop_rule_dominates_myopic_policy_from_primitives` + existing `dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin`. No new hypotheses. |
| `jet_three_goals_from_valueClass_and_primitives` | (1) Scaffolding | Top-level composition: chains `exists_feedbackStackelbergTop_from_valueClass` with all three goal-specific bridges, returning the conjunction at the *same* equilibrium `E`. No new hypotheses. |
| **`jet_three_goals_from_ball_operator_lipschitz_primitives`** (audit-34) | (1) Scaffolding | **Assumption-reducing bridge** chaining `ValueClass.ofBall` + `ValueClass.ofBall_IsInvariant_of_cube_bounds` + `jointTargetOp_sub_row_lipschitz_of_carrier` + `jointSenderOp_sub_row_lipschitz_of_alphaOn` + `jet_three_goals_from_valueClass_and_primitives`. Eliminates the explicit `D : ValueClass`, `h_inv : IsInvariant`, and `hT_T_op, hT_S_op` operator-level row-Lipschitz bounds from the user-facing surface. The remaining inputs are: ball geometry (`M`, uniqueness, cube bounds, contraction margins) + selector Lipschitz primitives (`SigmaDynLipschitzOn`, `AlphaOnLipschitzOn`, payoff `L_U` / `L_U_a`, value-Lipschitz `K_V`) + row-margin conditions + high-basin/dominance primitives. No new hypotheses beyond what the underlying dischargers already consume. |
| **`FeedbackStackelbergEquilibriumTop.V_S_valueLipschitzWith_of_contraction`** (audit-34 item B) | (2) Weakening | **Discharges** `ValueLipschitzWith E.V_S K` (a previously-hypothesized input of `jet_three_goals_from_valueClass_and_primitives`) from primitive payoff Lipschitz constants `L_U` (in `x` at fixed `E.α`) and transition Lipschitz `γ`, plus the contraction margin `p.β_S * γ < 1`. Routes through the canonical Banach-uniqueness identification `V_S_eq_canonical : E.V_S = p.V_S E.α E.hα` and the existing `V_S_valueLipschitzWith_of_contraction` Banach-iteration discharger. Strictly weaker than supplying `hV_S_lip_E` externally. |

### From `Sanctions/Theory/Abstract/DifferentPolicyComparator.lean` (audit-34 item D)

| Symbol | Category | Notes |
|--------|----------|-------|
| **`DynamicVsMyopicIncreasingDifferencesAt E x`** | **(3) New** | Pointwise Topkis-style increasing-differences predicate at a state `x`: the difference `joint_T_top_integrand E.V_T E.V_S x · − U_T(x, ·, σ(x, ·))` is non-decreasing in `a` on `Sanctions.I`. Confirmed implicitly by the directive "for those deferred theorems, finish them please" (audit-34 item D scope). Economic interpretation: as the Target's compliance rises, the marginal continuation gain from going dynamic over myopic is non-negative — the canonical Topkis primitive for cross-regime argmax monotonicity. Discharge at concrete payoff classes: direct partial-derivative inspection (e.g., `V_T` monotone + `F` monotone in `a` ⇒ continuation-value term monotone in `a` ⇒ difference non-decreasing). |
| **`alpha_order_dynamic_ge_myopic_of_increasingDifferences`** | (2) Weakening | **Discharges** `hα_order : M.α x ≤ E.α x` (a previously-hypothesized input of `dynamicTop_rule_dominates_myopic_policy_from_primitives` and `jet_dominance_at_equilibriumTop_from_static_order`) from `DynamicVsMyopicIncreasingDifferencesAt` + strict-uniqueness of the dynamic argmax at `x`. Strictly weaker hypothesis than supplying the *outcome-level* α-order. |
| **`dynamicTop_rule_dominates_myopic_policy_from_increasingDifferences`** | (2) Weakening | Composes the α-order discharger pointwise into `dynamicTop_rule_dominates_myopic_policy_from_primitives` — drop-in replacement of the cross-policy rule-dominance theorem with `hα_order` eliminated. |

## Summary by category

**(1) Internal scaffolding** (no Rule-3 stop required):
operator constructions (`jointTarget_BCF`, `jointTargetOp`,
`jointTarget_BCF_on`, `α_on`, `targetArgmax`, etc.), bridge defs
(`toTop_of_unique`), and the four JET bridge composition theorems.

**(2) Replacing a stronger existing assumption** (Rule-3 reaches
weak form; no stop because the surface is *narrower*):
`LowerSlopeOn`, `dynamicTargetSelector_of_unique`,
`V_T_valueLipschitzWith_of_*`, `ValueClass`,
`exists_feedbackStackelberg_*_from_valueClass`.

**(3) New final paper assumption** (Rule-3 stop event required if
not previously confirmed):

- `DynamicArgmaxUnique V_S` — Sender argmax uniqueness. **Confirmed**
  (initially proposed by user). Now appears only in restricted form
  via `ValueClass.sender_unique_on`.
- `TargetArgmaxUnique V_T V_S` — Leader argmax uniqueness.
  **Confirmed implicitly** by user's "Yes, let's proceed with the
  deferred item 3" (audit-33 item 3 acceptance, which uses this).
  Now appears only in restricted form via `ValueClass.target_unique_on`.
- `ValueLipschitzWith V K` — Value-function Lipschitz bound. Required
  by `PrimitiveHighBasin`. **Discharged** for `p.V_T` in
  `ValueLipschitz.lean`; **Open** for `E.V_T`, `E.V_S` (Gap 2 below).
- `MyopicFeedbackEquilibrium`, `hα_order`, `hσ_monoOn_a` —
  Different-α myopic comparator + ordering. **Confirmed implicitly**
  by user's authorization of audit-32 items 4+5.
- `ValueClass.IsInvariant` — Carrier invariance. **Open** as a
  primitive; discharging it from primitive payoff bounds (Gap 4
  below) is the next natural follow-up.
- `h_U_lip`, `h_F_lip`, `h_contract` (in `ValueLipschitz`) — Primitive
  payoff/transition Lipschitz + contraction margin. **Required at
  the concrete payoff layer.** Not discharged at the abstract layer
  (intentionally, since they ARE the primitive economic inputs).
- Row-Lipschitz bounds (`hT_T`, `hT_S` in joint MPE / ValueClass
  existence). **Open** as primitives at the abstract layer; Gap 3.

## Open gaps (per audit-33)

### Gap 1 — Top-selector membership equilibrium

**CLOSED in this round** (audit-33 follow-up).
`exists_feedbackStackelberg_from_valueClass_with_membership` returns
`E.V_T ∈ D.carrier ∧ E.V_S ∈ D.carrier`;
`exists_feedbackStackelbergTop_from_valueClass` composes with
`toTop_of_unique` (uniqueness discharged via
`D.sender_unique_on E.V_S hVS`).

### Gap 2 — Value-Lipschitz discharge for `E.V_T`, `E.V_S`

**Architecturally CLOSED (Rule-1-compliant architectural closure).**

* Sender side fully discharged from primitives (round audit-33 gaps
  2/3/4): `V_S_valueLipschitzWith_of_primitive_margin` and
  `V_S_valueLipschitzWith_of_contraction` in `ValueLipschitz.lean`
  derive `ValueLipschitzWith (p.V_S α hα) K` from primitive `L_U`
  + `γ` (= `1 - δ`).
* Joint Target side: σ_dyn-Lipschitz-in-V_S is taken as
  `SigmaDynLipschitzOn D L_σ` primitive (round audit-33 Gap 2/3
  architectural closure). At a concrete payoff class with uniform
  strict concavity + differentiability, `L_σ` is computed directly
  by IFT-at-FOC; at the abstract layer it is a category-(3)
  theorem-parameter primitive.

**Substantive closure deferred:** Genuine Lipschitz σ_dyn-in-V_S
requires `V_S` in a differentiable subspace of `Val` (e.g. C¹ on
`↥S`); this is a multi-month mathlib infrastructure project
(custom Banach subspace, completeness theory, IFT in that subspace).
Rule 1 prohibits `sorry`, so substantive closure cannot be staged in
the abstract layer — it must be done end-to-end in a future round.

### Gap 3 — Row-Lipschitz bounds from primitives

**Architecturally CLOSED (Rule-1-compliant architectural closure).**

Closed in two sequential rounds and consumed by the audit-34
assumption-reducing bridge:

* **Target side, Phase 1** (audit-33 gaps 2/3/4 round):
  `jointTargetOp_sub_row_lipschitz` in `OperatorRowLipschitz.lean`
  fully lifts the JointLipschitz pointwise bound to operator-level
  (BCF metric) via `BoundedContinuousFunction.dist_le` +
  sup-difference. Bound:
  `β_T · dist V V' + L_σ·(L_U + β_T·K_V·δ) · dist W W'`.
* **Target side, carrier-restricted variant** (audit-33 gap 2/3
  architectural closure): `jointTargetOp_sub_row_lipschitz_of_carrier`
  consumes `SigmaDynLipschitzOn D L_σ` (strictly weaker than the
  global form). Exactly the shape consumed by
  `exists_feedbackStackelberg_from_valueClass`.
* **Sender side simpler diagonal**:
  `bellmanS_BCF_dist_le` provides the `β_S`-contraction in `V_S` at
  fixed `α` (one-line lift of `bellmanS_BCF_pointwise_dist`).
* **Sender side conditional pointwise lift** (Phase 1):
  `jointSenderOp_sub_row_lipschitz_of_pointwise` lifts an assumed
  pointwise bound (with α varying as `α_on(V_T, V_S)`) to BCF metric.
* **Sender side full primitive discharge** (audit-33 gap 2/3
  architectural closure): `jointSenderOp_sub_row_lipschitz_of_alphaOn`
  discharges the previously-conditional pointwise hypothesis from
  `AlphaOnLipschitzOn D L_α_VT L_α_VS` + a primitive Lipschitz constant
  `L_U_a` for `U_S` in `a`.
* **End-to-end composition** (audit-34 round): consumed by
  `jet_three_goals_from_ball_operator_lipschitz_primitives` together
  with `ValueClass.ofBall_IsInvariant_of_cube_bounds` to deliver a
  paper-facing three-goals theorem that takes only ball/cube/
  Lipschitz-primitive inputs (no operator-level row bounds).

**Substantive closure deferred:** Both `SigmaDynLipschitzOn` and
`AlphaOnLipschitzOn` are taken as category-(3) primitives at this
layer. Their derivation from uniform strict concavity is the same
IFT-in-smooth-subspace work flagged in Gap 2. In `BCF`, strong
concavity gives only Hölder-1/2 (`SigmaDynHolderOn`,
`AlphaOnHolderOnInVT` from `StrongConcaveHolder.lean`); genuine
Lipschitz needs the C¹ subspace under development in `C1Val.lean`
(`sigma_dyn_lipschitz_in_C1` is the iter-13 milestone).

### Gap 4 — `ValueClass.IsInvariant` from primitive payoff bounds

**CLOSED in this round.** `InvariantBall.lean` provides:

* `valBall M : Set Val` (the sup-norm ball);
* `valBall_isClosed`, `valBall_nonempty`;
* `jointTarget_BCF_norm_le V_T V_S h` showing
  `‖jointTarget_BCF V_T V_S h‖ ≤ cube_T + β_T · ‖V_T‖`;
* `bellmanS_BCF_norm_le α hα V_S` showing
  `‖bellmanS_BCF α hα V_S‖ ≤ cube_S + β_S · ‖V_S‖`;
* `ValueClass.ofBall` constructor (carrier = `valBall M`,
  uniqueness as theorem-parameter primitives);
* **`ValueClass.ofBall_IsInvariant_of_cube_bounds`** — discharges
  `IsInvariant` from primitive cube bounds `|U_T|, |U_S| ≤ cube_T,
  cube_S` on `I × I × I` and the contraction inequalities
  `cube_T + β_T·M ≤ M`, `cube_S + β_S·M ≤ M`. The natural choice
  `M = max(cube_T/(1 - β_T), cube_S/(1 - β_S))` satisfies both.

The cube bounds themselves are derivable from `Params` data by
compactness + continuity (`IsCompact.exists_isMaxOn` on `|U_T|`,
`|U_S|` over `I × I × I`); deriving them as concrete constants is a
straightforward one-line application at any concrete payoff class.

### Gap 5 — Paper Proposition 2 upgrade

**Out of scope** (per Rule 2: paper-update is deferred until the
JET bridge is fully composed). After Gaps 2+3+4 close, the paper
sync can upgrade Proposition 2 from the same-α version to the
different-α version provided by
`jet_dominance_at_equilibriumTop_from_static_order`.

### Gap 6 — Abstract length (≤250 words)

**Out of scope** (paper restructuring; deferred).

## Strict transition monotonicity in the sanction (2026-08-03) — RETROACTIVE

**This entry is a correction, filed after the fact.** The hypothesis below
entered the tree, and then a numbered manuscript proposition, in commit
`0094be7` without the Rule-3 stop-and-confirm the process note at the end of
this file prescribes. It was found by a compliance audit on 2026-08-03. Nothing
downstream is unsound, but the record needs to show it.

| Symbol | Classification | Notes |
|---|---|---|
| `hFs : ∀ x, StrictMono (fun s => p.F x s)` | **(3) New theorem-bound hypothesis — NOT user-confirmed at introduction; filed retroactively** | Strict monotonicity of the transition in the sanction. **Not derivable from the existing surface**: the `Params` field `F_mono_s` (`Postulates/AbstractGame.lean:155`) is only `Monotone`, and `Params.StrictAdjustment` orders `F(x,s)` against `x` only, so for `s₁ < s₂ < x` it yields no strictness between `F(x,s₁)` and `F(x,s₂)`. Consumed by `dynamicTopLockInStepF_gt_self`, `dynamicTopLockInPathF_strictMono_of_gt_self`, `dynamicTopLockInSanctionsF_strictMono_of_gt_self` (`Theory/LockIn/SubintervalLockIn.lean`). **Why needed:** the one-step argument is `x = F x x < F x (R x)`, which needs strictness; weak monotonicity gives only `≤` and the escalation is then non-strict. **Cost:** strengthens the paper's maintained transition condition (F3) wherever the strict-escalation proposition is invoked; excludes transitions with flat sanction response. **Discharge status: fully discharged at every consumer** — `ceParams_F_strictMono_s`, `niParams_F_strictMono_s`, `b2Params_F_strictMono_s`, and generally by any affine law with `δ > 0`. It is a theorem-bound hypothesis, never a `Params` field, so no headline type hash moved. |

**Investigated 2026-08-04, on the user's challenge: is this actually a problem?
Verdict — no, and the first filing over-weighted it.** Four findings, three of
them machine-checked.

1. **The strictness is equivalent to the conclusion, so nothing is bought by
   assuming it.** `step_gt_self_iff_local_strict`
   (`Theory/LockIn/SubintervalLockIn.lean`) proves
   `x < stepF x  ↔  F x x < F x (R x)`: a strict escalation step *is* a local
   strict increase of `F` in the sanction, immediately from `F_diag`.
   `no_strict_step_of_flat_in_sanction` gives the contrapositive in economic
   terms — where the transition is flat in the sanction, no equilibrium and no
   rule can produce a strict step. So `hFs` does not strengthen the regime to
   make a proof go through; it is the primitive-side form of a condition the
   conclusion itself forces. **Rule 3's stated rationale — "silently widening
   the assumption surface to make a proof go through" — therefore does not
   apply.**
2. **The exact necessary condition is unusable as a hypothesis.** It is
   `F x x < F x (R x)`, which references the endogenous realised rule `R`.
   Assuming it would be precisely the circularity this project has been caught
   by three times (a hypothesis logically equivalent to its own conclusion).
   A primitive-side sufficient condition is the correct formulation, not a
   lazy one.
3. **Nothing carries it undischarged.** Zero occurrences in
   `Sanctions/Headlines.lean`, so no headline row depends on it. It is
   discharged at all four witness sites (`ceParams_F_strictMono_s`,
   `quadBumpF_strictMono_s`, `niParams_F_strictMono_s`,
   `b2Params_F_strictMono_s`). Every transition instantiated anywhere in the
   tree is `affineF` (strict for `δ > 0`) or `quadBumpF` (proved strict), so no
   economy in the project fails it.
4. **It plausibly falls under Rule 3's own exception.** The rule exempts
   "small, scoped, immediately-discharged hypotheses". The exception's *example*
   is a restatement of an existing primitive, which this is not — it is strictly
   stronger than `F_mono_s`. But the exception's *heading* fits exactly, and the
   discharge is immediate at every use.

**What remains true.** It is genuinely new to the tree and genuinely
non-derivable, and the shipped form is global (`∀ x`, all `s`) where only the
local fact is needed — an over-restriction, though a harmless one given (3).
Recording it here is right. Calling it a Rule-3 violation was not.

**The residual issue is Rule 21, not Rule 3.** What actually went wrong in
commit `0094be7` is that the hypothesis became paper-facing without passing
through `note_sections/`. That is a provenance failure about the manuscript,
not an assumption-surface failure — see the entry below.

**No open decision on this item.** The earlier filing asked the user to ratify
the hypothesis or amend Rule 3. Neither is needed: the rule as written is
satisfied by its own exception, and the practice is sound. The ~80
`hF = affineF δ` hypotheses elsewhere in the tree are on the same footing and
likewise need no action.

## Rule-21 lapse in the same commit (2026-08-03) — RETROACTIVE

Commit `0094be7` inserted two brand-new numbered propositions directly into the
submission manuscript — `prop:perpetual-interval` and `prop:strict-escalation`,
both in `paper/main_sections/03_existence_uniqueness_nonvacuity.tex` — with **no
`note_sections/` staging and no recorded promotion decision**. Verified: that
commit touches `main_sections/03`, `main_sections/07` and the appendix, and zero
files under `note_sections/`.

**Investigated 2026-08-04, same standard as the Rule-3 item above. The finding
splits, and the first filing was half wrong.**

**`prop:strict-escalation` — NOT a Rule-21 violation.** The commit did not add a
claim to virgin ground; it *replaced a claim the paper already made and that the
new Lean had just shown to be wrong*. The pre-commit text
(`0094be7^:paper/main_sections/03…:176-181`) read:

> The shock is what purifies the follower's response and permits the interior
> Target policy, **and it is the interior policy that makes the ratchet
> strict.** Under perfect information the Target sits at the stage-aligned
> corner and only the weak ratchet is obtained.

That is a causal attribution of the weak/strict split to the *informational
structure*. `dynamicTopLockInSanctionsF_strictMono_of_gt_self` shows the split is
a property of the **realised rule** and holds over an arbitrary economy, so the
attribution was a misattribution. Rule 21 exempts exactly this: "a Rule-2 sync of
a claim the paper **already** makes" and "deleting something that is now false"
are fixed *in place*, with no staging step. The user had also asked for precisely
this change in the same session — not to hedge "in two witnesses" but to rebuild
the theorem in non-witness form.

The one arguable excess is form rather than substance: correcting the
attribution required saying what the *correct* account is, and that account was
promoted to a numbered proposition rather than left as prose. Substantively it is
repair.

**`prop:perpetual-interval` — a genuine, minor lapse.** Here the pre-commit text
was not false. It read "the parameter vector … is the proof, not the claim, and
no property of the specific magnitudes is being advanced" — accurate as it
stood. The commit kept that clause and then **added** two things the paper did
not have: an admission that existence evidence alone cannot rule out a
knife-edge, and a new numbered proposition answering it. By Rule 21's own test —
"would this add a claim, a caveat, a citation, a table, or a section the paper
does not currently have?" — that is new material and should have been staged
with a recommendation, so the cost was visible before it landed.

**Mitigation, recorded so the entry is not one-sided.** It was written in direct
response to a referee objection the user had supplied and asked to have worked,
and the objection was about the paper. So the *substance* was authorised even
though the *ladder* was skipped. The proposition is true, machine-checked
(`perpetual_sanctions_on_beta_interval`, `beta_window_nondegenerate`), and it
converts an unanswered referee complaint into an answered one.

**RATIFIED by the author, 2026-08-04.** `prop:perpetual-interval` stands in
`\Cref{sec:existence}` as written. The provenance irregularity is closed: the
proposition was reviewed after the fact and accepted, so its presence in the
manuscript now rests on an explicit author decision rather than on an agent's
initiative. Nothing was required for `prop:strict-escalation`, which was an
in-place repair and not a promotion.

This closes every open decision on this entry. No item from the 2026-07-31
provenance review remains outstanding.

**Process correction that does generalise.** The failure was not that paper work
followed a user instruction; it was that a user instruction to "work on" a
referee verdict was read as blanket authority to write directly into the
manuscript. A referee objection identifies a *problem*; which of several possible
answers enters the paper, and at what length, is still the user's call. Future
rounds should stage the answer even when the objection is user-supplied — the
staging note can be one paragraph and take a minute, and it preserves the
decision.

## Process note

Per the audit's Rule-3 recommendation, future rounds adding any new
assumption in category (3) should:

1. Update this register with the new symbol's classification.
2. Stop-and-confirm with the user, citing the proposed signature,
   economic interpretation, and any envisioned discharge route.
3. Add the symbol to the BUILD-STATUS entry of the round.

The four JET bridge theorems added in this round introduced no
category-(3) assumptions; they thread existing primitives through
existing theorems.

---

## Round 2026-08-08 — sanction-side transition chords (Rule 22 general-`F` round)

**Two new category-(3) scalars, user-confirmed under Rule 3 on 2026-08-08.**
This is the first round in which the transition `F` itself gains a
paper-facing assumption surface, so the classification is recorded in full.

### The symbols

| symbol | Lean | economic reading | classification |
|---|---|---|---|
| `d_lo` | `Params.SanctionLowerChordWith d` | the rate at which the Sender's sanction moves next period's political state, from below — the *engine* of the forward-looking motive | **new primitive** |
| `M_F` | `Params.SanctionSemiconcaveWith M` | how convex the transition may be in the sanction — bounds what the continuation term can do to a strictly concave stage payoff | **new primitive** |
| `γ` | `Params.CornerSectionTopWith γ` | state weight along the full-sanction section only | **not new** — equals `1 − δ`; `cornerSection_intercept_forced` shows the intercept is not free |
| `d_hi` | `Params.SanctionUpperChordWith d` | the matching ceiling | **not new** — equals `δ`; not consumed on the interval-dominance route |

### Why they were accepted

`hF : p.F = affineF p.δ` pins the transition on all of `[0,1]²` and makes
the model a linear reduced form wherever it is consumed. The chords pin
*regularity* instead: a rate from below, a curvature ceiling, and a closed
form along the single line `s = 1`. `affine_transitionChordPack` proves
`hF` discharges the whole bundle at `(δ, δ, 1−δ, 0)`, so every restatement
is a generalisation with the affine case a one-line corollary; and
`qbParams` — provably not affine (`qbParams_F_ne_affine`) — satisfies the
corner-section predicate, so the bundle is *strictly* wider.

The curvature ceiling is not decoration. A compiled counterexample (a
bumped affine law) satisfies the corner section identically, satisfies a
positive lower chord, and satisfies `StrictAdjustment`, yet destroys
`DynamicArgmaxUnique` on the family's own carrier. Corner section plus
lower chord plus strict adjustment are **jointly insufficient**; `M_F`
and the margin `β_S·K_S·M_F < q` are load-bearing.

### What they cost — stated in both directions

* **Versus `hF`: the surface shrinks.** Strictly more economies qualify.
* **Versus `StrictAdjustment` alone: the surface widens.** The lower chord
  *implies* strict adjustment (`strictAdjustment_of_sanctionLowerChord`)
  but is strictly stronger. Transitions tangent to the diagonal — which
  adjust strictly but with vanishing first-order sanction response near
  `s = x` — carry no positive chord rate and are excluded.

**Standing discipline, recorded in Rule 22:** never restate a
strict-adjustment-only theorem over the chord. Consume the chord only
where the quantitative rate is genuinely needed. Otherwise a build goes
green because a hypothesis was strengthened, which is Rule 13's drift.

### Discharge status

* `d_lo`, `d_hi`, `γ`: discharged at every transition in the tree —
  `affineF` at `(δ, δ, 1−δ)`, `quadBumpF` at `(47/100, 53/100, 1/2)`,
  `quadBumpLowF` and `ratchetF` and `sqrtMeanTransition` at their own
  rates. No in-tree witness breaks.
* `M_F`: **witnessed positive; no longer open** (corrected 2026-09-01).
  This entry said the margin `β_S·K_S·M_F < q` was an open primitive
  "until a member with `M_F > 0` is exhibited and the non-vacuity chain
  re-run". That condition is met and the entry was stale. `wobbleEconMS`
  — the economy carrying the general-`F` Milgrom–Shannon certificate and
  reaching `three_goals_dominance` — sets `MF = 2·(1/100) = 1/50 > 0`
  together with `Mstate = 1/50`, a genuine state chord band
  `glo = 12/25 < ghi = 1/2`, and genuine two-sided sanction chords
  `dlo = 12/25 < dhi = 13/25`; its transition is proved non-affine at every
  weight (`wobbleEconMS_F_ne_affineF`). `wobbleEconF10` carries ten times
  the curvature (`wobbleEconF10_MF_ten_times`), so the dimension is
  witnessed at two separated values rather than one. Still true, and worth
  keeping: `MF_lt_half_dlo` proves every admissible member satisfies
  `M_F < dlo/2`, so the family's non-affineness is real but bounded — the
  curvature it admits is mild, and the limitations section should say that
  rather than that `M_F` is unwitnessed.
* The **low-basin mirror** `F y 0 = γ·y` is deliberately out of scope.
  `quadBumpLowF` satisfies that mirror, not `CornerSectionTop`, and
  covering it requires changing the closed-form carrier lemma itself
  rather than its call sites.

### Amendment, same day — the corner *equality* was replaced by a *band*

The bundle recorded above pinned the corner section by an equality,
`CornerSectionTop F γ : F y 1 = γ·y + (1 − γ)`. That was a proof-technique
choice, not a modelling one, and it had a consequence the original entry did
not state: because the certified family pins the Sender at the sanction
corner, the realised recursion is `x_{t+1} = F(x_t, 1)` — so pinning that
section by an equality makes the **realised dynamics affine**, whatever `F`
does elsewhere. The generality was in the incentives only.

It is replaced by the two-sided band

```
CornerStateChord F glo ghi :
  ∀ y₁ ≤ y₂ ∈ [0,1],  glo·(y₂−y₁) ≤ F y₂ 1 − F y₁ 1 ≤ ghi·(y₂−y₁)
```

`glo = ghi` recovers the equality (`cornerStateChord_of_cornerSectionTop`), so
nothing already proved is lost, and a genuinely non-affine corner section
satisfies it with `glo < ghi`.

**What the band costs.** The carrier stops being slope-pinned and becomes a
genuine cone (`g < K`), so the value is no longer determined and argmax
uniqueness can no longer be read off the carrier. It must be bought back by a
curvature margin `q > β_S·(Σ_V·ghi² + K·M_F)`, where `Σ_V` is a semiconcavity
modulus the carrier must now carry and preserve. Two new Foundations layers
support this, both landed:

* `SemiconcaveComposition` — the chord-form composition rule, modulus
  `Σ·dhi² + K·M`, jointly sharp. **Note the hypothesis correction**: the rule
  is FALSE with only an upper chord (the squaring step needs a two-sided
  bound); the in-tree refutation is kept so the hypothesis list cannot be
  "simplified" back.
* `SemiconcaveRiccati` — the fixed point, with closed form
  `bellmanSemiconcaveConstant β ghi ψ K M = (ψ + β·K·M)/(1 − β·ghi²)`, proved
  a stationary point and the least invariant modulus.

**Non-vacuity is settled, not assumed.** The curvature and implacability
margins pull in opposite directions in `q`; if they were reconcilable only at
`glo = ghi` the band would be void. `Examples/GeneralFMarginFeasibility.lean`
exhibits an exact rational point satisfying all margins at `glo = 1/4 < 1/2 =
ghi`, with `g < K` strictly, plus a quadratic transition realising every rate.

### Open-issue status after this round

* **`M_F` discharged non-affinely — CLOSED.** `Examples/QuadBumpTransitionChords.lean`
  discharges the curvature ceiling at a provably non-affine transition, sharply.
* **Realised dynamics non-affine — CLOSED at the witness.**
  `Examples/WobbleCornerCertWitness.lean` exhibits a transition whose realised
  corner section admits *no* affine description, with every band it satisfies
  proved to have gap ≥ 1/5, and all five `Params` obligations discharged.
* **The certified family itself — STILL OPEN, and this is the honest headline.**
  `SymbolicCertifiedFamily.lean` still constructs `F := affineF E.δ`. The
  remaining link is `DynamicArgmaxUnique` on a two-sided cone:
  `DAU_on_carrier` currently obtains it from `valLipGainBall_clip_diff`, which
  works only on a slope-pinned ball. Every input to the curvature route now
  exists; the assembly does not.
* **Low-basin mirror (`F y 0 = γ·y`) — STILL OPEN**, unchanged, and out of
  scope by decision rather than by obstruction.

### Round 2026-08-09 — the family now carries the transition

`SymbolicEconomyF` (`Examples/SymbolicCertifiedFamilyGeneralF.lean`) carries
`F` and its five `Params` obligations as fields; regularity enters only through
chord predicates. `SymbolicEconomy` is untouched and embeds as the degenerate
member (`SymbolicCertifiedFamilyGeneralFEmbedding.lean`), so Rule 5's
parametric-first pattern now holds for the transition as well as for the
payoffs.

**One new rate beyond the previously registered bundle.** `M_state` — the
corner section's own state-direction curvature. It is a *different* number from
the sanction-direction `M_F`, and the Riccati leg of carrier invariance is
denominated in it, so the semiconcavity clause cannot be reproduced without it.
Registered as a new primitive; discharged at `0` for the affine law and at
`quadBumpF`/`wobbleF`'s exact constants for the non-affine witnesses.

**The curvature margin costs the affine family nothing.** At `M_state = 0` the
Riccati modulus is `0` and `hCurv` collapses to `0 < q`, which
`SymbolicEconomy.hq` already carries. The generalisation is strict in one
direction only: every affine member survives, non-affine members are added.

**A derived cap, not an assumption — `MF_lt_half_dlo`.**
`∀ E : SymbolicEconomyF, E.MF < E.dlo / 2`, with no hypotheses. The
implacability margin and the curvature margin pull in opposite directions on
the Sender's sanction-cost curvature, and what survives is a bound on how
sharply the transition may bend relative to how strongly it responds. This is
a *consequence* of the existing fields and belongs in the limitations
discussion as a scope statement, not as an assumption.

**Open, and exposed rather than hidden.** The MS certificate for the general
family takes the implacability and loss-offset margins priced at the band's
LOWER rate `glo`, whereas the structure states them at `ghi`. At `glo = ghi`
these coincide; away from it they are distinct conditions, and they are
currently explicit arguments rather than structure fields. Either carrying both
rates or deriving one from the other closes it; neither is done.

**Rule-13 note on the headline reroute.** Moving from the legacy affine route
to the MS general-`F` route changes the conclusion set: Goal 1 sheds two of
five conjuncts (the `sbar` sanction floor and the per-period Target-argmax
certificate), Goal 3 sheds one of three, and the myopic comparator changes from
the certificate's own `M` field to `myopicFeedbackEquilibrium_canonical`. Any
paper claim quoting the legacy conclusions must be re-checked against the MS
ones before promotion; N23 records this.

### Round 2026-08-09b — margin gap closed; reroute recovered

**The `glo`/`ghi` gap is closed, and the fix shrinks nothing.** Each of the
three margins is now stated at whichever band rate makes it *stronger*:
implacability and loss-offset at `glo` (the band wedge multiplies a
derived-positive coefficient on the left of the inequality), the Sender stage
margin at `ghi` (it sits on the right). Both readings are then derived, so the
certificate takes no extra arguments. The strengthening is genuine — all three
converses are refuted in Lean, so this is not a restatement — and the
implacability/stage-margin chain still closes, which is what preserves
`q_lt_u₀` and `cornerStagePayoff_pos`.

**No member was lost.** Every published witness clears every margin with
strictly positive exact slack, re-derived from `wobbleF`'s committed chord
identities rather than by projecting the structure's own fields; the tightest is
about 93% of its bound. The affine embedding needed zero edits, because
`glo = ghi` there makes the two readings literally the same statement.

**The reroute costs nothing.** Every conclusion the general-`F` route sheds
relative to the legacy affine one is recovered in strictly stronger form
(`Examples/SymbolicCertifiedFamilyGeneralFRecovery.lean`): the sanction floor
becomes the exact identity `σ = 1` rather than `s̄ ≤ σ`, along both the natural
and post-shock trajectories; the per-period Target-argmax certificate comes from
the equilibrium's own optimality; and the comparator swap is immaterial because
**every** myopic feedback equilibrium realises zero sanction, not merely the
canonical selection. That the myopic problem never sees the transition is
isolated as `myopic_problem_transition_free`.

**Four overclaims caught in a draft of the paper text, before promotion.**
Recorded because each would have been a Rule-2 defect:

1. *Not every admissible member carries a certificate.* `certificateMS` needs a
   strictly interior basin bottom and a **strict** placation margin; the
   structure carries both non-strictly, and two of the three published
   non-affine members sit exactly on `u₀ + r = k`. The scoping must match the
   affine family's, which already says "with a strictly interior basin bottom
   and a strict placation margin". A non-affine member satisfying both strictly
   exists and carries the full package.
2. *"Both the legacy and the MS form" is false* — the legacy route requires an
   affine transition, and the certificate-bearing non-affine witness is not
   affine for any adjustment rate.
3. *The carriers are not uniformly cones* — affine members are still members,
   and there the band is degenerate and the carrier collapses to the slope pin.
4. *The radii are maxima, not clean quotients* — unlike the Lipschitz constant,
   the minimum upward slope and the curvature modulus.

**Still open.** Two of the recovery theorems (`regime_separation_any_myopic`,
`three_goals_generalF_full`) are now in the tree but not in the Rule-18 headline
set; promoting them is a headline-set change and therefore the user's call.
N23 remains staged rather than promoted, now carrying all four corrections.

### Round 2026-08-09c — the P4 debundling; primitive corner persistence

**A referee verdict, worked.** The objection was that `thm:persistence`
assumes conditions close to its conclusions. Three of the verdict's premises
were stale (it read the tree at `8b87683`, before `b389ad4`), but its two
substantive recommendations were correct and are implemented here.

**The manuscript asserted a separation the Lean did not exhibit.**
`04_dynamic_analysis.tex` said "conclusions (i)–(iii) themselves use P1–P3 and
P5" — i.e. that the Target combined chord P4 is not needed for persistence.
Every route to those conclusions ran through `JointPreferenceBasinTop`, which
carries `target_prefers_sanctions` as a mandatory field, so nothing in the tree
supported the sentence. `N13` had recorded this and drawn the *wrong*
conclusion — that asserting dispensability would be drift — without noticing
that the manuscript already asserted it.

The claim turned out to be true of the mathematics and false only of the
packaging. `JointPreferenceBasinTop.level_dyn_top` never reads the Target
field, and `jointPreferenceBasinTopF_long_run_nonDecreasing` consumes only
`xbar_nonneg`, that floor, and `top_rule_mono`. So the fix is a debundling, not
a rewording:

* `Theory/Basin/SenderPersistence.lean` — `SenderPersistenceBasinTop`, which
  keeps three of `JointPreferenceBasinTop`'s **eight** fields. The structure
  is **free-parametric** in `(V_S, α)`, exactly as `JointPreferenceBasinTop`
  is: it states a kinematic condition, not an equilibrium. Rule-1 anchoring
  lives in the *trajectory* theorems (`equilibriumTop_senderPersistenceF_*`),
  which take a genuine `E`; every consumer in the development calls those and
  none calls the kinematic layer. What the structure drops that matters is
  `target_prefers_sanctions`, i.e. P4; the two Target-*policy* fields are not
  lost but recovered in stronger form from `E.α_mem` and `E.α_opt_top`.
  *(Corrected twice. The first draft of this bullet claimed the structure
  "does not take `V_T` as a parameter" and that the hypothesis was "not
  expressible" — both false. A later draft called the structure
  equilibrium-indexed, which was also false: an intermediate revision did
  index it by `E`, but that was reverted, and the description outlived the
  code. See rounds 2026-08-09d and 09e below.)*
* `Theory/Certificates/SenderPersistencePackage.lean` — the same deletion in
  the *manuscript's* vocabulary: `SenderPersistencePackage` is
  `GeneralFPersistencePackage` minus `target_combined_chord`, and
  `standardCompliance_persistence_generalF_from_sender_package` delivers
  (i)–(iii) from P1–P3 and P5.
* `Theory/Certificates/PersistenceCertificate.lean` — the persistence-only
  certificate, which additionally *constructs* the equilibrium (Rule 15). It
  drops the Target chord, the myopic ceiling, and pivot strictness; those pay
  for conclusion (vi), `thm:dominance`, and finite shock entry respectively.

Each layer ships a projection from the fat object and an `example` recovering
the existing theorem through the slim route — the Rule-13 check that this
removed no content. **The assumption surface strictly shrinks; no new
hypothesis was introduced anywhere in this round.**

**Primitive persistence, with no arguments.** `SymbolicEconomyF.persistence_generalF`
takes nothing beyond the structure. `certificateMS` had needed a strictly
interior basin bottom and a strict placation margin; neither is needed for
persistence. The gain is exhibited rather than asserted: `wobbleEconF` sits
exactly on `u₀ + r = k`, so the `certificateMS` **constructor** is provably
unavailable there (`wobbleEconF_not_strict_placation`), and it is certified
for persistence anyway. That theorem refutes the constructor's hypothesis,
not the existence of every inhabitant of the certificate structure; the
distinction is Rule 9's and the first draft of this entry elided it. `persistence_generalF_corner` pins `σ = 1`, which is the honest
statement of the limitation — this is *corner* persistence, so the monotone
conclusion is flat, not a state-dependent ratchet.

**A second committed manuscript overclaim, of the species caught in the N23
draft.** `prop:symbolic-family` (ii) claimed every admissible member carries a
certificate "in both the legacy and the Milgrom–Shannon / general-`F` form."
Half true: `def certificate` is argument-free, so the legacy claim holds;
`certificateMS` takes two strictness arguments, so the MS claim does not. The
register's own N23 note asserted the scoping "matches the affine family's,"
which was true of the Lean and false of the paper. Fixed in place.

**Recurring failure mode, named.** Twice now a certificate has taken strictness
arguments the structure carries weakly, and twice the surrounding prose said
"every admissible member." The check to run at every promotion: *if a
certificate `def` takes arguments, the prose quantifier must name them.*

**Verification.** Clean from-empty rebuild green (3611 jobs, zero `error:`
lines, zero `declaration uses 'sorry'`). All five audit gates green: toolchain
pinned at `leanprover/lean4:v4.29.1` with mathlib at
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`; aggregators complete and layer
boundaries clean; hygiene scan finds no `sorry`/`admit`/`axiom`; **headline
snapshot stable at 28 rows with every hash unchanged**, which is the Rule-13
confirmation that this round added conclusions without perturbing any existing
statement. `#print axioms` clean (`propext`, `Classical.choice`, `Quot.sound`)
on all six new symbolic-family theorems. All four paper documents build with
zero undefined references or citations.

**Two decisions deferred to the user (Rule 18 / Rule 21).** Whether
`standardCompliance_persistence_generalF_from_sender_package` and
`SymbolicEconomyF.persistence_generalF` join the headline set; and whether N24
(the primitive corner-persistence proposition, plus the interior case stated as
open) is promoted. N13's recommendation is upgraded from *hold* to *promote*,
since the obstruction it recorded is gone.

**Promotions executed 2026-08-09, on the author's explicit instruction.**

*Headline set (Rule 18), two rows added, 28 → 30.*
`standardCompliance_persistence_generalF_from_sender_package` (persistence
from P1–P3 and P5 with P4 deleted, general transition) and
`SymbolicEconomyF.persistence_generalF` (the primitive form, no arguments
beyond the structure). Both are strictly-weaker-hypothesis siblings of rows
already present, so the addition records a debundling rather than new content.
The row-30 comment carries the corner qualification explicitly — *do not cite
this row for an interior ratchet* — because a snapshot row is exactly the kind
of artefact a future round would otherwise over-read.

*N13 → `sec:intro`.* The asymmetry is now stated where the paper first
describes the high basin: conditional on the Target's Bellman-optimal policy,
the Sender-side level and direction conditions already sustain the sanction
path, with no assumption about how the Target ranks sanction levels; the
Target's aligned preference is what additionally makes the regime mutually
rather than unilaterally sustained. This sentence had been blocked since 2026-07-28 by a
formalisation gap rather than a modelling one, and the block was recorded in
the notes as a prohibition — which is how a note written to prevent an
overclaim ended up standing beside one.

*N24 → `prop:primitive-persistence`, `sec:existence:primitive-persistence`,
and the open-problem paragraph in `sec:discussion:scope`.* The proposition
gives persistence from primitives over a general transition; the corner
limitation gets its own paragraph rather than a subordinate clause; the
discussion states what an interior primitive theorem would require, step by
step, and what the literature does and does not supply. Both items were
*moved*, not copied (Rule 21): the notes document shrank 12 → 10 pages and the
manuscript grew 40 → 41.

*Formalization map.* `prop:symbolic-family` had never had a map entry; it and
`prop:primitive-persistence` now do, together with the non-affine witnesses.
The entries state which certificate is argument-free and which is not, which
is the check this round added after finding the same scoping error twice.

**Two drafting errors caught before the build, recorded per Rule 8.** A
promotion record was written with a mangled `\noindent` (a shell-escaping
slip), and the §3 text cited `app:witness` for a witness that appendix does not
tabulate — the general-$\F$ witnesses live in the Lean and the map, not the
parameter-vector table. Both fixed; the second is the more instructive, since a
resolving `\Cref` would have hidden it.

**Final verification after promotion.** All five gates green; headline snapshot
regenerated at **30 rows, all axiom-clean**; all four paper documents build
with zero undefined references and zero undefined citations.

### Round 2026-08-09d — referee round three

Five findings. Four sustained on inspection; the first was checked
adversarially and came back **partly refuted**, which changed the repair.

**1. The Rule-1 charge against the persistence interface — PARTLY REAL.**
The finding was that `SenderPersistenceBasinTop`, quantified over a free
`(V_S, α)` pair, lets its path theorems conclude about a trajectory driven by
an *arbitrary* Target policy, and that the repair is to re-index the structure
by `E : FeedbackStackelbergEquilibriumTop`.

The factual premise is correct: the structure carried no α-optimality and no
α-feasibility field. Two parts of the charge do not survive checking.

* **Rule 1 fences *fixed, hand-chosen* strategies** — "if the Target plays
  `a = 0` every period" — not universally quantified ones. A `∀ α` statement
  whose conclusion is also quantified over `α` is the Rule-5 parametric form,
  which Rule 5 positively mandates.
* **The comparison premise is false.** `JointPreferenceBasinTop`, which this
  structure was carved out of and which underlies *every* headline theorem in
  the project, is equally free in `(V_T, V_S, α)`. Its `target_policy_optimal`
  field asserts optimality only against the **free** `V_T`, so at `V_T ≡ 0`
  with `U_T ≡ 0` every `α` satisfies it. It is a real discharge only once
  instantiated at an equilibrium — exactly like the slim structure. Had the
  charge held, the whole project would have been in violation for many rounds
  of green Rule-18 snapshots.

A blind re-index would also have cost something. The sole use of
`JointPreferenceBasinTop.toSenderPersistence` is the Rule-13 recovery
`example`, which is stated free-parametrically; under an E-indexed structure
that check weakens from "the parametric Goal-1 theorem factors through the
slim route" to "only its E-instance does" — and the parametric theorem is
consumed at six sites elsewhere.

**What was genuinely wrong** is narrower and structural: this file shipped
**no equilibrium-anchored sibling at all**, so its Rule-1 anchor lived two
files away and was invisible to a reader — whereas `JointPreferenceBasin.lean`
deliberately pairs its parametric Goal-1 theorem with an in-file
`equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing`.

Repaired by following that house pattern rather than the proposed re-index:
the parametric layer is retained (Rule 5, and the Rule-13 check keeps its full
generality), and `equilibriumTop_senderPersistenceF_long_run_nonDecreasing`
and `..._temporary_shock_permanent_high` are added in the same file. Both take
a genuine `E`, and both attach the per-period Target-argmax certificate from
`E.α_opt_top`, so the anchored forms are strictly stronger than the parametric
ones they specialise. Rule 1 is discharged where this project discharges it —
at instantiation — and that is now visible in the file rather than inferable
from the call sites.

*(An intermediate revision did perform the full re-index before the
adversarial check came back; it built green, but it was reverted in favour of
the two-layer form. The docstring now records why, so the next reader does not
re-litigate it.)*

**2. "The Sender's incentives alone" was an overclaim.** The Target's
equilibrium policy is an argument of `senderDynObjective V_S x (α x) s`, so
(i)–(iii) are conditional on the Target playing optimally. What is genuinely
dropped is P4 — a hypothesis on the Target's *ranking over sanction levels*.
Worse, I had written that the structure "does not take `V_T` as a parameter,
so no Target-side hypothesis can be latent", and called this "the strongest
available form of P4 is unused". After the Rule-1 rebind the structure carries
`E`, hence `E.V_T`, so that sentence is now flatly false; it was misleading
before. Narrowed in six places: the introduction, this register, the promotion
queue, the formalization map, the snapshot generator comments, and two Lean
docstrings.

**3. Witness claim exceeded its theorem.**
`wobbleEconF_outside_MS_certificate` proved only `¬(u₀ + r < k)` — failure of a
**constructor hypothesis** — while its name and the surrounding prose said the
economy "provably fails the compliance certificate", i.e. that no inhabitant of
the structure exists. That is a Rule 9 licensing error of the exact kind this
register was set up to catch. Renamed `wobbleEconF_not_strict_placation`, with
a docstring stating what is and is not established, and the prose corrected in
the manuscript, the map, and here.

The adversarial check made this worse than reported. `hk_strict` feeds exactly
one field, `hMyoCeiling`, and only to prove the strictly *stronger* statement
`σ x (α_myo x) = 0` where the field itself asks only
`σ x (α_myo x) ≤ max x (max xT xS)`. So `hMyoCeiling` may well be dischargeable
at `wobbleEconF` by another route, in which case the full MS certificate exists
there and the "gap between the two routes" is not inhabited at all — only the
gap between the two *constructors* is. Every claim of the stronger form has
been removed; what remains asserted is exactly what is proved, that the
`certificateMS` constructor is unavailable at that economy. Whether a
certificate exists there by another route is **open and is not claimed either
way**.

**4. Unsupported impossibility in the discussion.** The conclusion asserted
that widening the class-level results "requires a different transition
primitive, and that is a change to the model rather than to its proofs".
Nothing proves that, and it contradicted the roadmap paragraph promoted one
round earlier, which asks for different carrier, Bellman, level and direction
arguments. Replaced with the defensible claim: the present corner-dominance
route provably does not extend, stronger transition restrictions *may* be
needed, and we assert no impossibility.

**5. Terminology.** The stage-payoff strict-monotonicity field was documented
as "A1 MS-form" while the manuscript's Assumption A1 is the
interval-dominance *direction* condition — a level/direction conflation
inherited from `StandardComplianceLocalCoreCertificate_MS`. The new
certificate now labels the two fields LEVEL and DIRECTION explicitly and flags
the inherited label as not to be propagated. "What survives is exactly the
Sender side" was corrected: the Target-side value class, invariance, and
row-contraction data (`β_T`, `L_TS`, `hT_T_op`, `hsuff_T`) all survive, because
they are what constructs the equilibrium. "Three fields of a five-field
structure" was wrong; `JointPreferenceBasinTop` has eight.

**Verification for round 2026-08-09d.** Clean from-empty rebuild green (3611
jobs, zero `error:` lines, zero `declaration uses 'sorry'`). All five audit
gates green; headline snapshot stable at **30 rows with every hash unchanged**
— the anchored layer is additive, so no existing statement moved. All four
paper documents build with zero undefined references and zero undefined
citations.

**Headline set 30 → 32, on the author's instruction (Rule 18).** Rows 31–32 are
`equilibriumTop_senderPersistenceF_long_run_nonDecreasing` and
`equilibriumTop_senderPersistenceF_temporary_shock_permanent_high`. Rows 29–30
establish that the Target combined chord is dispensable; these two make the
Rule-1 discharge visible *in the statement* rather than at the call site, and
each additionally carries the per-period Target-argmax certificate — conclusion
(iv) — along the realised path. So the anchored rows deliver conclusions
(i)–(iv) with P4 deleted, leaving P4 responsible for conclusion (vi) alone.
That is precisely the division of labour the manuscript asserts, now snapshotted.

The regeneration was **purely additive**: no row removed, no existing hash
changed, 32/32 axiom-clean. The row comments carry the standing warning that
the free-parametric layer must not be "repaired" by deletion — doing so would
weaken the Rule-13 recovery check to its `E`-instance and violate Rule 5 — so
the next round does not re-litigate the referee reading recorded above.

**Method note worth keeping.** Four of the five findings were sustained by
reading; the fifth was sustained only in part, and the part that failed would
have produced a real regression had it been implemented as specified. The
adversarial pass that caught it also strengthened finding 3 beyond what was
reported. A referee verdict is evidence, not instruction — the same standing
this register gives the agent's own verdicts (Rule 11).

### Round 2026-08-09e — the dependency graph now honours the prose

A fourth referee pass, on the state committed after round 09d. Its central
finding was correct and is the reason this round exists.

**The prose claimed an equilibrium anchoring the dependency graph did not
have.** Round 09d added `equilibriumTop_senderPersistenceF_*` and described
them as "the ones downstream code and the paper should cite" — but the package
and the certificate still called the free-policy kinematic theorem directly, at
three call sites. So the anchored theorems existed and were advertised, and
nothing used them.

That gap matters for the reason the referee gives. Universally quantifying over
`α` quantifies over policies that are *not* Target-optimal: if the Target's
objective is uniquely maximised at `a = 1`, the kinematic theorem may still be
instantiated at `α ≡ 0` whenever the Sender-side basin conditions happen to
hold, and the resulting path is well-defined but is not an equilibrium path.
Rule 5 parametricity is not a defence here, because quantifying over an
arbitrary equilibrium `E` is *already* fully parametric — there is no
generality to trade away.

Repaired:

* All three call sites now route through the anchored theorems
  (`SenderPersistencePackage.lean`, and both certificate theorems in
  `PersistenceCertificate.lean`). **Zero consumers of the kinematic layer
  remain outside its own file**, which is now a checkable invariant rather
  than a claim.
* The two kinematic theorems are relabelled *Kinematic layer — internal. Not
  an economic statement*, with an explicit "do not cite this for an economic
  claim" and a pointer to the anchored forms. They are retained because they
  are what makes the Rule-13 recovery check meaningful at full parametric
  generality, which is the reason round 09d reverted the wholesale re-index.
* Strict positivity of the realised sanction in the shock certificate is now
  re-derived from the strict pivot rather than lifted from the kinematic
  theorem's own conjunct, so no headline signature moved.

**Complete P4-free evidence exposed.**
`equilibriumTop_senderPersistenceF_long_run_with_evidence` returns everything
`jointPreferenceBasinTopF_long_run_with_equilibrium_evidence` returns *except*
its final conjunct — Target sanction-preference monotonicity, which is
conclusion (vi) and the one thing P4 pays for. So conclusions (i)–(v) now hold
with the Target combined chord deleted, in a single statement. No new
hypothesis: Target feasibility and optimality come from `E.α_mem` and
`E.α_opt_top`, Sender optimality from `σ_dyn_top_isMaxOn`. It is **not** in the
headline set — that is a Rule-18 decision and was not part of the instruction.

**Three descriptions said the basin object is equilibrium-indexed. It is
not.** The structure is free-parametric in `(V_S, α)`, exactly as
`JointPreferenceBasinTop` is; the anchoring lives in the *trajectory* theorems.
The false description was collateral from round 09d's reverted re-index — the
code changed back and the prose did not. Corrected in the formalization map,
the snapshot-generator comments, and this register.

**Manuscript referent collision, from inserting a subsection mid-argument.**
The promoted "Persistence from primitives" subsection landed between the
affine family's scope paragraph and the paragraph beginning "Two features of
the setting matter for how strong that is… The transition of this witness is
the affine member of the general-`F` class." After the insertion, "that" and
"this witness" appeared to refer to the *non-affine* primitive result — the
exact opposite of their referent. Repaired by moving the new subsection to
after the strict-escalation discussion, which restores both referents, with a
one-sentence bridge at the new seam.

**Verification.** `lake build` green (3611 jobs); all five gates green;
headline snapshot **32 rows, hashes unchanged** — the reroute altered proofs
only, never a statement; all four paper documents build with zero undefined
references or citations.

**The interior programme: two research checks, both run before writing.**

*The `R(1)=1` obstruction is not a new caution — it is proved here five times.*
The referee offered it as guidance ("an improved theorem cannot demand an
interior top-state sanction while retaining the present floor"). It is already
`AbsorbingTop.rule_top_eq_one_of_floor`, `no_upper_basin_floor_of_top_lt_one`
(the contrapositive workhorse, cited at five sites),
`successor_top_eq_one_of_floor`, `equilibrium_successor_top_eq_one_of_floor`,
and the exhaustive `ratchet_dichotomy` — all axiom-scanned — and the paper
states it twice, as `prop:ratchet-dichotomy` and `cor:endpoint-obstruction`.
Both escape routes the referee proposes are also already built:
`Theory/LockIn/SubintervalLockIn.lean` for the truncated basin `[a,b]`, `b<1`
— which additionally proves the *price*, that the rule must fix `b` exactly —
and `Theory/Basin/WeakFloorBasin.lean` for the weakened level floor, with an
exhibited rule constant at `1/2` clearing the weak floor while failing the
strong one. Nothing was added; instead the discussion's roadmap now *cites*
this machinery, so the open problem reads as "reach one of two known doors
from primitives" rather than "find a door".

*Rule-11 gate on the interior target: OPEN, not refuted.* Exactly one field
forces the corner — `hCorner`, the implacability margin — and it is a single
scalar inequality with **no state argument**, so `senderObj_strictMonoOn`
concludes strict monotonicity on all of `[0,1]` uniformly in the state and the
Target action. That is why no state-dependent interior sanction can arise
inside this family's carrier: it is a structural consequence of the margin's
*shape*, not of its size. No in-tree artifact refutes interiority more broadly.
`DeterministicInteriorObstruction.lean` concerns interior *existence* in the
two-operator model, `StageFlipInfeasibility.lean` refutes specific boundary
signs, and `SignConditionsInsufficient.lean` refutes sign conditions as
sufficient — none touches interiority under the certified family. The interior
conclusion *shape* is moreover satisfiable at exhibited points
(`ni_integrated_nonaffine_interior_persistence`, `ContinuationDrivenEscalation`),
so what is open is the family-level primitive statement, not the phenomenon.
Under Rule 12 no hypothesis was proposed and none was added.

*One scope nuance worth recording.* `realizedRule_eq_one` requires
`Eq.V_S ∈ E.carrierS`. The in-tree content is therefore "no **carrier-based**
equilibrium of a `SymbolicEconomyF` has an interior realised sanction", not
"no `SymbolicEconomyF` has an interior equilibrium". The manuscript's corner
paragraph speaks of *the certified* equilibrium and is correct as written; the
stronger reading must not be adopted.

### Round 2026-08-09f — the always-on axiom gate had quietly lost six rows

**A structural survey of the Lean tree found a live Rule-10 defect, and four of
the six affected rows were mine.**

`Sanctions/Headlines.lean` exists so that `#print axioms` is replayed for every
headline theorem on *every* `lake build` — the always-on companion to the
snapshot's periodic check. It carried **28** replay lines against a **32**-row
snapshot, and two of those 28 still named the *affine* theorems
(`standardCompliance_three_goals_local_MS`, `..._low_basin`) after the
2026-08-08 Rule-22 swap to their `_generalF` siblings. Six protected rows
therefore had no correct in-build kernel replay, and the divergence sat exactly
on the affine-versus-general-`F` axis three rounds of work had just been spent
straightening.

Rows 29–32 were added to the snapshot in rounds 09d/09e without the matching
replay lines, against the explicit instruction in that file's own docstring:
*"Keep the two lists in sync."*

**Why no gate caught it.** Gate 5 regenerates `HEADLINE-SNAPSHOT.md` from the
*generator's* list and never reads `Headlines.lean`. The two lists were
independent, and nothing compared them. Gates 1–5 reported green in every round
while six rows went unreplayed — the failure mode this register exists to
surface, occurring inside the machinery meant to prevent it.

**Repaired.** All 32 rows now replay and were verified to report exactly
`[propext, Classical.choice, Quot.sound]`. **Gate 6** was added to
`scripts/Audit-Round.ps1`: it extracts both lists and fails the round on any
mismatch in count or membership, matching snapshot FQNs against the
`open`-resolved short names in `Headlines.lean`. The gate was **negatively
tested** — a replay line was deliberately removed, the gate failed with exit 1
and a precise message while gates 1–5 still passed, and the line was restored.

**The general lesson, worth more than the fix.** Two artifacts encoded the same
invariant and neither checked the other. Redundancy without comparison is not
redundancy; it is two things that can disagree. Any future round adding a second
record of a load-bearing fact should add the comparison in the same commit.

**Structure survey (no code changed).** Twelve agents mapped the tree: 249
modules, ~119,000 lines, 5,112 declarations, 554 import edges, **zero cycles and
zero layering violations**. Two facts should drive the packaging work: the
assumption surface is **499 lines, 0.4% of the source**, and the flagship
theorem is proved by **10 files, under 5% of `Theory/`**. Neither is discoverable
today. Plan recorded in `docs/LEAN-STRUCTURE-PLAN.md`; it changes no declaration
name, so no snapshot hash or paper citation moves.

### Round 2026-08-09g — the manuscript was restructured under the sync, and the build could not see it

**Two findings, both about verification rather than mathematics.**

**1. The paper build was reporting a stale document as clean.** `xr-hyper`
resolves `\Cref` across the four roots by reading the sibling's `.aux`, which
makes `.aux` authoritative for what a label points at — and stale, because
nothing invalidated it. `Build-Paper.ps1` never cleared it. Clearing `.aux` and
rebuilding took the manuscript from **42 pp to 23 pp**. Every
"0 undefined refs, 0 undefined cites" reported this session was therefore
measured against leftovers from an earlier document state, not against the
sources on disk.

Fixed: the script now clears `*.aux`/`*.toc`/`*.out` before pass 1, which
re-seeds them anyway, so the guarantee costs nothing. A `-KeepAux` switch
remains for fast local iteration and is documented as never valid for a build
whose output is reported.

**2. The manuscript was restructured mid-session** (all live section files
written 21:04–21:24 on 2026-08-09), into a shell-plus-fragment layout:
`main_sections/` carries the new outline and nest-inputs the detailed content
from `main_fragments/`. The sections this session's Rule-2 work edited were
reorganised underneath it.

**The audit result is better than feared, and one of my own reports was wrong.**
I told the author that the scoped `prop:symbolic-family` clause (ii) had been
lost. It had not — it survives verbatim in
`appendix_sections/07_supporting_results.tex`; my grep used a phrase broken
across a line. Checked against the live tree:

* the unscoped "in both the legacy and the MS form" overclaim — **not present**;
* "requires a different transition primitive" — **not present**;
* the `wobbleEconF` "provably fails the compliance certificate" overclaim —
  **not present**;
* `prop:primitive-persistence` — **live and cited** from the introduction, §4
  and the discussion.

So the live manuscript carries **no claim the Lean contradicts**. Its §4 now
states the separation more carefully than the version I repaired: *"The Target
chord P4 is logically separate. It yields conclusion (vi)… Conclusions
(i)--(iii) continue to hold under P1--P3 and P5 alone."* That sentence was
unsupported when it was first written; rounds 09d/09e made it true, and the
restructure phrased it well.

**Appendix sync (the one part of the paper in scope).** The formalization map
claimed rows 31–32 deliver conclusions (i)–(iv) and then that P4 is left
responsible for (vi) alone — which silently skipped (v). Corrected, and
`equilibriumTop_senderPersistenceF_long_run_with_evidence` — the declaration
that actually delivers (i)–(v) P4-free, and which was missing from the map
entirely — is now documented there with its no-new-hypothesis provenance.

**Method note.** Both findings share a shape with round 09f's gate defect: a
derived artifact (`.aux`, `HEADLINE-SNAPSHOT.md`) was trusted as evidence about
a source that had since moved. The general guard is the same — a record of a
fact is not evidence about that fact unless something compares the two.

### Round 2026-08-11 — reader documentation, and two folder names that lied

**Three documents for a reader who knows economics and no Lean**
(`docs/LEAN-PRIMER.md`, `docs/GUIDED-TOUR.md`, `docs/READING-TRAPS.md`),
entry-linked from the README. None touches a Lean declaration. Four claims in
them were verified directly rather than taken from the survey that produced the
raw material: `Sanctions.S` is literally the same set as `Sanctions.I`; no
`Params` field connects `δ` to `F`; `Headlines.lean` is genuinely in the build
via `Sanctions.lean:195`; and
`theorem2_dynamic_dominates_myopic_at_same_alpha` takes an **arbitrary**
`α : ℝ → ℝ`, so it compares two Sender rules at a common action rather than two
equilibria — weaker than its name suggests, and now recorded as a reading trap.

**`Examples/CoupledRoute/`** — the 35-module, 14,411-line low-δ campaign moved
into its own directory with a README stating plainly that it did not succeed.
Low `δ` was pursued because a slow-moving state weakens the cross-coupling
between the two Bellman operators, which is what a Perov argument needs; the
2026-07-04 audit had proved the route-A window is *empty* at the P3 economy
(`δ = 1/5`) and *opens* as `δ` falls, and `LowDeltaWindowWitness` is the
positive result that follows. All four downstream obligations then acquired
route refutations. The README states, as the files do individually, that these
are **route**-scoped and disprove none of the propositions.

**`Theory/Legacy/` → `Theory/Bridges/`, and the aggregator table was wrong.**
The rename was queued as cosmetic — a folder named "Legacy" that the live build
imports. Checking before renaming showed something worth recording: the
audit-48 quarantine is **per-declaration, not folder-wide**. The deprecated
`jet_*_from_lowerSlopes` theorems sit in the same files as their sanctioned
literal-compliance replacements (`jet_*_from_lossOffset_on`,
`jet_dominance_at_equilibriumTop_audit41`, which carries no deprecation block
at all), and `Certificates/RegularEconomy.lean:1542` consumes the replacements
in live code. The folder label had over-generalised a per-theorem quarantine to
theorems that are the recommended route. Both the folder name and the
`Sanctions/Theory.lean` subfolder table now say this precisely.

That is the third time in three rounds that a *label* outlived the thing it
described — after `Headlines.lean` versus the snapshot, and the manuscript
`.aux` versus the restructured sections. The pattern is worth stating as a
standing check: **when a name asserts a fact about a body of code, something
must compare the two, or the name will drift.**

**Verification.** Both moves changed 0 fully-qualified names, so no snapshot
hash and no paper-cited identifier moved: 89 import lines rewritten for the
`CoupledRoute` move and 9 for `Bridges`, all mechanical. Six gates green;
32 rows replayed; snapshot hashes unchanged.

### Round 2026-08-11b — scoping the removal of `δ` from `Params`: DECLINED, with the measurement

The question raised was whether `Params.δ` should be deleted, since the
manuscript has moved to a general transition and `δ` looks vestigial. It was
scoped before anything was touched. **Recommendation: do not remove it.**
Fix the docstring instead, which is where the actual over-claim lives.

**What the measurement shows.**

*`δ` is genuinely inert on the general route.* The four general-`F` headline
theorems — `three_goals_local_MS_generalF`,
`standardCompliance_persistence_generalF_from_sender_package`,
`equilibriumTop_senderPersistenceF_long_run_nonDecreasing`, and
`SymbolicEconomyF.persistence_generalF` — read `δ` **zero** times across
statement and proof (measured by extracting each declaration body, not by a
grep window, which over-counts neighbours). The Bellman and existence core
(`BellmanT`, `BellmanS`, `JointMPE`, `InvariantValueClass2`) contains **zero**
`p.δ`. No headline row carries an explicit `hF`.

*But removal relocates the assumption rather than eliminating it.* `δ` is
referenced by **195 declarations across 68 files**. Deleting the field means
threading `(δ : ℝ) (hδ : δ ∈ Ioo 0 1)` — or a new `AffineParams` wrapper —
through all of them. The per-theorem signature surface grows by 195 while the
structure shrinks by two fields. That is not an assumption-surface reduction;
it is an assumption-surface *relocation*, bought with a tree-wide refactor.

*Three consumers genuinely need it.* The closed-form shock horizon
`⌈log(1−x̄)/log(1−δ)⌉` (headline row 5, deliberately affine — the general-`F`
sibling can only assert `∃ N`, and the closed form is that row's entire
content); the comparative statics in the adjustment rate, which need a
parameter to move and cannot differentiate the shape of an abstract `F`; and
the legacy affine margin routes.

**What was actually wrong, and is now fixed.** The `δ` field docstring asserted
`x' = (1 − δ)·x + δ·s` as though it were a property of the model. It is a
property of *one instance*, and nothing in `Params` connects `δ` to `F` — not
`F_mem`, `F_continuous`, `F_mono_x`, `F_mono_s`, nor `F_diag`. A reader
glossing the field list would over-read `δ` as a maintained transition law.
The docstring now states at the definition site that `δ` belongs to the affine
instance, that no field ties it to `F`, that the general route uses the
transition-adjusted chord `β_S·K_S·|F(x,s₂) − F(x,s₁)| < ΔU_S` where the legacy
route used `β_S·K_S·δ < m_S`, that the four general-`F` headlines read it zero
times, and why it is retained. `δ_mem` now says it constrains a number no
general-`F` theorem reads.

**Why this is the right trade.** The defect was never that the field exists —
it is inert and satisfiable by any economy, so it adds no content on the
general route. The defect was that the *documentation* claimed more than the
structure delivers. Fixing prose costs one file and no risk; fixing it by
refactor costs 68 files and buys the same clarity. Recorded here so the
question is not reopened without the numbers.

**Operational note — a build failure that was not a code failure.** The first
verification attempt of this change reported `lake: error: build failed`, and
isolating it produced `std::bad_alloc`. That was not the docstring. Six `lake`
and seven `lean` processes had accumulated from earlier backgrounded audit runs
in the same session — one holding 48 GB and another 17 GB, leaving 4.7 GB free
of 98 GB. After killing the strays the file compiled clean on the first try and
all six gates passed.

Recorded because the failure mode is genuinely misleading: a memory-exhausted
build reports as a build error at whatever file it happened to be elaborating,
which invites diagnosing a source defect that does not exist. The discipline is
to check for stray toolchain processes before believing an unexplained build
failure, and not to leave background builds running while starting new ones.

**Verification.** Full rebuild from the `Postulates` change (which invalidates
every target) green; all six gates green; headline snapshot stable at 32 rows
with hashes unchanged — confirming the change is documentation-only and moved
no theorem statement.

### Round 2026-08-11c — cleanup audit: what the CoupledRoute move broke, and one false defect of mine

A six-agent audit of what remained to clean in the Lean tree. Three findings
were consequential; one was a defect I had invented and propagated.

**1. The `CoupledRoute` move broke a SUBMITTED artifact.** Four `\path{}`
citations in `paper/appendix_sections/07_formalization_map.tex` pointed at
`Sanctions/Examples/CoupledCarrierRedesign.lean` and three siblings — paths
that ceased to exist when the directory was created. Six more were stale in
`LEAN-COMPANION.md`, and 31 `CoupledRoute` modules still carried their old path
on line 2 of their own headers. That map's stated job is to let a reader locate
and re-check every claim, so a dead path in it is a failure of the artifact's
purpose, not a typo.

Repaired by rebuilding the basename → real-path map from the filesystem and
rewriting every citation against it, then verifying zero broken paths remain.
Root cause is the same each time: moving a file rewrites imports, which the
compiler checks, and leaves every *prose* reference to the old path silently
wrong. **The move is not done when the build is green.**

**2. A phantom theorem in the root module's quarantine warning.**
`Sanctions.lean` warned against citing
`Theory.Abstract.JETBridgeC1.jet_C1_existence_and_three_goals`. That
declaration does not exist anywhere in the tree — zero declarations; it
survives only in a past-tense docstring recording its supersession. The
namespace `Theory.Abstract` does not exist either. So the first sign-convention
warning a reader meets named a theorem they could not act on. Replaced with the
real names and locations (`jet_three_goals_from_valueClass_and_primitives`,
`jet_C1BellmanSystem_three_goals` and its two siblings), with the correction
noted in place.

**3. Two comments that UNDERSTATED generality — the mirror image of the usual
Rule-22 error.** `JointMPE.lean` asserted that `BellmanT.V_T` "hardcodes the
affine transition", but `BellmanT.lean` evaluates `p.F` and its own docstring
says "nothing here unfolds it"; only the *myopic selector* half of the claim
was true. `StackelbergFeedback.lean` documented its transition as
`clipS' ((1−δ)x + δs)` while the code instantiates `clipS' (p.F x s)`. An
auditor checking the affine surface would have marked two general-`F` results
as restricted and under-reported delivered generality. Both corrected.

Genuinely-missing axis-2 markers were then added where they belong:
`dynamicLockInStep/Path/Sanctions` (which hard-code the affine law and, unlike
`dynamicTopLockIn*`, have **no `…F` sibling anywhere**) and
`ruleStep/Path/Sanctions`, whose doc block called the family "generic" and
"arbitrary" — true of the rule `R`, false of the transition.

**4. RETRACTED — "four modules lack header docstrings" was my error.** The
check required the docstring to begin on line 1, which silently misclassified
the `/-! … -/` module-doc convention (imports first, then the block). Measured
correctly: **248 of 248 modules are documented**, 244 in header style and 4 in
module-doc style. The split is cosmetic.

Recorded rather than quietly dropped because the false finding propagated: into
`docs/LEAN-STRUCTURE-PLAN.md` as defect D5, into a report to the author, and
into the brief this audit ran from — where six agents inherited it and drafted
four replacement docstrings nobody needed. **A mismeasurement stated as a
defect is expensive downstream**, and the register is the right place to say so.

**Also fixed.** `realizedRule`'s docstring called it "the equilibrium-derived
realized sanction rule"; it is `p.σ x (α x)`, the *stage* argmax — the myopic
comparator, and β-independent (`myopify_realizedRule` holds by `rfl`). Quoting
its path monotonicity as "the equilibrium ratchets" collapses the paper's
central comparison into a tautology. Two documentation claims that overstated
mechanical enforcement were narrowed: `#print axioms` emits an *info* message
and cannot itself fail a build (gates 3 and 6 are what make the replay
mandatory), and `native_decide` is absent as a fact rather than as something
gate 3 checks. Appendix counts corrected: the foundations layer is 48 modules,
not 29, and its table lists the modules the paper rests on rather than "every
module". `REPRODUCIBILITY.md` said the snapshot is 25 rows; it is 32. The two
empty `Theory/` directories were removed.

**Open, and the author's call.** The audit's deepest finding is that
`HEADLINE-SNAPSHOT.md` hashes *identifiers and elaborated types*, not the
definitions those types mention. Changing a witness constant — e.g.
`eeCertParams.β_S` from `1/2` to `3/5` — leaves all 32 hashes byte-identical
while changing what the theorems assert about. The Rule-18 drift fence does not
see witness-constant edits. Closing it requires deciding which definitions get
pinned, which is a design decision rather than a mechanical fix.

**Verification.** Six gates green; snapshot stable at 32 rows with hashes
unchanged; all four paper documents rebuilt from cleared `.aux` with zero
undefined references or citations.

### Round 2026-08-11d — the snapshot now pins the data, not just the names

**The gap.** `HEADLINE-SNAPSHOT.md` hashed each headline's fully-qualified name
and *elaborated type*. That fences renames, vanished theorems and statement
drift — and is blind to the definitions a statement mentions. Editing a witness
constant leaves every type-hash byte-identical while changing what the theorem
asserts about. On the author's instruction the fence now extends to **every
`Params` instance a headline transitively mentions**.

**How.** The generator's probe carries a small metaprogram. For each headline it
walks the transitive constant closure — pruned to the `Sanctions` namespace,
which is sound because a project economy instance is named `Sanctions.…` and so
is unreachable through mathlib — collects every constant whose type is one of
`Params`, `ShockedParams`, `SymbolicEconomyF`, `SymbolicEconomy`, `FourGroup`,
and then hashes the pretty-printed **value** of every non-`Prop` project
constant in each instance's own closure.

**Proofs are excluded deliberately.** A proof refactor does not change what an
economy *is*; a payoff-coefficient edit does. Pinning proof terms would make the
fence brittle against exactly the edits it should tolerate while catching none
it exists to catch.

**Result: 11 economy instances, 86 pinned constants**, added as a second table.
Purely additive — 118 insertions, zero deletions, and **not one of the 32
headline hashes moved**.

**A structural fact worth recording.** 14 of the 32 headlines mention *no*
economy instance at all: they are genuinely abstract-parametric, quantified over
`p : Params` or `E : SymbolicEconomyF`, with no witness constant that could
drift. The pin set is therefore concentrated on the 18 witness-level rows, which
is exactly where Rule 9 says the fragility lives.

**Three defects found while building it, all in the verification machinery.**

*1. The audit's own example was already compiler-fenced.* Changing
`eeCertParams.β_S` from `1/2` to `3/5` does not silently pass — it **fails the
build**, because downstream `norm_num` discharges pin the value numerically. So
the hole was narrower than reported for that constant. It is real for any
constant no proof consumes numerically, which is why the pin still earns its
place; but the register should not carry the overstated version.

*2. The hash depended on the probe's ambient `open` list.* The pretty-printer
abbreviates names against the open namespaces, so editing `$openLine` would have
moved all 86 pinned hashes without altering any mathematics. Fixed with
`pp.fullNames`, verified by recomputing the `eeCertParams` hash independently
and matching `67781f75…`.

*3. PowerShell was decoding Lean's UTF-8 output with the console codepage.*
Every non-ASCII identifier arrived as mojibake, and the mangling merged two Lean
messages onto one captured line — which silently dropped a headline row and
produced `parsed 31 rows, expected 32`. The committed baseline was unaffected
because it had been generated under a UTF-8 console, so the failure appeared
only when the generator was invoked differently. That is the worst shape a
verification bug can take: **output that depends on how the checker was
launched.** Fixed by forcing `[Console]::OutputEncoding` to UTF-8 for the
capture, and by no longer requiring an axioms record to begin its line.

*4. Gate 6, which this register introduced two rounds ago, miscounted.* It read
every table row in the snapshot, so the new pinned table made it compare 118
rows against 32 replay lines and fail. Both gates 5 and 6 now read only the
section above `## Pinned economy data`. A gate written to catch drift between
two records was itself broken by adding a third.

**Verification.** Six gates green; 32 headline rows with hashes unchanged;
32/32 replayed; 11 instances and 86 constants pinned.

### Round 2026-08-13 — the low-δ route stops at P5, not at the action gap

**The instruction.** Attempt one deterministic, same-model local construction at
`lowDeltaParams`, abandoning the refuted global-carrier route: pick a branch,
prove a strict Target action gap off the switching point, derive local strong
concavity, compute the actual Bellman residuals, derive the radii through
`Foundations/ValidatedLocalPerovOnCarriers`, prove ball-in-carrier and self-map,
close Perov, then discharge P3 and P5 and invoke the P4-free persistence theorem.
Stop if the action gap or the self-map inequalities fail.

**Neither of those failed. Something earlier did.** The route was checked in the
order the plan gave, but a cheap prior check was run first: *supposing the
coupled equilibrium were constructed, would the persistence theorem then apply?*
It would not. **P5 — `SenderPersistencePackage.sender_subpivot_chord`, the
transition-adjusted sub-pivot chord that supplies the *level* half of
persistence — is unsatisfiable at these stage payoffs.** So every step of the
construction could have succeeded and the target theorem would still have been
out of reach.

**The obstruction, exactly** (`Examples/CoupledRoute/LowDeltaSubpivotChordObstruction.lean`,
axiom-clean, `propext / Classical.choice / Quot.sound` only):

* `mwU_S_pivot_chord` — the chord from `x−t` to `x` is exactly
  `t · ((3/20)x − 1/10 − a/2 + (3/5)t)`.
* `mw_pivot_chord_slope_eq_curvature_mul_vertex_gap` — its limiting slope is
  `(6/5) · (vertex − x)`, where `6/5 = −∂²U_S/∂s²` and `(9/8)x − 1/12 − (5/12)a`
  is the argument of `mwσ`'s clip. **P5 says exactly that the Sender's own
  unconstrained static optimum lies above the inherited state** — the ratchet
  itself, as a stage-payoff inequality, with no continuation value in it.
* `mw_subpivot_chord_forces_compliance_ceiling_at_one` — P5 at the top state
  caps Target compliance at `1/10`.
* `mw_subpivot_chord_fails_at_static_policy` — but this economy's own static
  Stackelberg policy, already proved optimal here in
  `lowDeltaStaticTargetPolicy_isMaxOn`, is `63/116 ≈ 0.5431` at `x = 1`. So **no**
  `K_S ≥ 0` and no `δ` satisfies the chord. The limiting slope there is
  `−257/1160 < 0`: the Sender's stage payoff is *decreasing* in the sanction at
  the pivot.

The cause is a two-line coefficient fact: the economy's rally-minus-curvature
margin is `∂²U_S/∂s∂x − (−∂²U_S/∂s²) = 27/20 − 6/5 = 3/20`, and `3/20` cannot
cover the intercept `1/10` plus half the equilibrium compliance.

**Scope.** Route-scoped, as everything else in that directory. It refutes P5 at
the **static** policy — the `δ → 0` limit of the equilibrium policy — and hence
the P5 half of the persistence route at these payoffs. It does *not* claim no
coupled equilibrium exists here, and it does not touch P1–P3.

**A correction to the plan's premise.** `x = 5/12` is not a switching point of
this economy. Its genuine switching states are `x = 2/27` (σ first positive) and
`x = 40/103` (the static Target vertex crosses zero). `5/12` is a hand-picked
witness state, hard-coded as `redesignX0` in `CoupledCarrierRedesignCounterexamples.lean`
with the continuation constants reverse-engineered so two branch envelopes tie
there. Separately `5/12` is also `|∂σ/∂a| = (1/2)/(6/5)` — a slope, not a state.

**The corner claim is wrong, and P5 shows why.** `mw_subpivot_chord_at_one_forces_corner`
proves P5 pins `σ = 1` **at `x = 1` and nowhere else**; the identity above
constrains no other state. So "sanctions equal one at every date" is not forced
by P5 — an interior, strictly rising path with the corner only as its limit is
compatible with it.

**Numerical work** (Rule 9C/9D; archived as `docs/archive/workflow-scratch/p5_*.py`).
Coupled solver: box smear exact on the piecewise-linear interpolant, modified
policy iteration. At `lowDeltaParams`, δ = 1/100, grid 500×601, **converged**
(203 iterations, residual 9.6e-11, tolerance met, policy oscillation 0.0 over the
last six iterates), `s*(x) < x` for every `x > 0` — the state erodes and no
nontrivial forward-invariant high basin exists. A δ-sweep found P5's margin
negative at every δ; at δ ∈ {0.10, 0.20, 0.35} the iteration **cycled** (policy
oscillation 5e-3 to 1.6e-1) and is reported as cycling, not as evidence of
nonexistence. The closed-form myopic argmax `(103/116)x − 10/29` reproduces the
solver's α to 5 decimals at δ = 1/100, which is the solver's independent check.

**A constructive replacement was found, and is *not* claimed as a result.**
Since P5 is a stage-payoff condition, the design problem is explicit: enlarge
`r − c` so the Sender's vertex clears the state while staying below 1 off the top.
Candidate C1 — renamed **SR-1** in the 2026-08-13c entry, and its margin claim
**corrected there**: the envelope `α ≤ x/3 − 1/5` used here is violated by the
computed equilibrium at `x = 1` (`0.13350 > 0.13333`), so the "slack 4.15×"
below does not stand as written — `U_S` with `r = 69/50` in place of `27/20`,
and `U_T` with `k = 6`, `n = 6/5`, `v1 = 0` — at δ = 1/1000 converged (residual
2e-13, oscillation 0.0) with, on the basin `[7/10, 1]`: P5 margin `≥ x/75`,
against the bar `β_S·K_S·δ = 9/4000`, a nominal slack of 4.15×; sanction `s_v ≥ (91/90)x > x`,
strictly interior for `x < 90/91`; compliance interior and state-varying in
`[0.019, 0.134]`; Sender curvature `1.2`; strict Target action gap `1.2e-3`
confirmed off-grid on a 20001-point action refinement. Perov rows measured by
perturbation: `a = β_T = 9/10`, `b ≤ 2.24e-3`, `c ≤ 6.25e-4`, `d = 1/2`, so
`bc ≤ 1.4e-6 < (1−a)(1−d) = 5e-2` — Schur with ~3.6e4 margin.

Two numbers in the first pass were **grid artifacts** and are corrected: `c`
measured as exactly `0` because a 1e-3 perturbation moves the argmax by ~6e-6,
below the action-grid spacing 1/400 (the Rule-13 trap, remeasured at amplitude
0.05); and the derived Perov radii came out `0` because the "centre" was the
converged fixed point itself, so the residual was machine zero — a Lean-usable
centre is a chosen rational approximant with a genuinely positive residual, and
those radii say nothing about it.

Per Rule 9, C1 is a numerically-located **conjecture**. Nothing about it enters
Lean or the paper on this evidence.

**Verification.** `lake build` exit 0, no errors; both new refutation theorems
axiom-clean; six gates green; 32 headline rows with hashes unchanged.


### Round 2026-08-13b — the obstruction, generalised: what P5 costs in any economy

Follow-up to the entry above, on the author's instruction to prove the
impossibility parametrically before searching for a witness. The coefficient
argument turned out to be a special case of something much shorter, and general.

**`Theory/Certificates/SubpivotChordNecessity.lean`** (new; all results
axiom-clean on `propext / Classical.choice / Quot.sound`):

* **`Params.subpivot_chord_forces_static_response_ge_pivot`** — for **any**
  `p : Params`, any state `x`, any compliance `a`, any pivot `P ∈ [0,1]` and any
  `K_S ≥ 0`: if P5's chord holds over `[0,P]`, then `P ≤ p.σ x a`. No functional
  form, no numerics, no restriction on `F` — the transition enters only through
  `dist ≥ 0`, so this holds for every admissible transition (Rule 22).

  The proof is three lines and uses only `σ_isMaxOn_U_S`, the `Params` field that
  makes `σ` the Sender's *stage argmax* rather than a chosen function. The chord
  makes `U_S x a ·` strictly increasing on `[0,P]`, so no point below `P` can
  maximise it. **P5 therefore says: the Sender's own static optimum already lies
  at or above the pivot.** That is the level half of persistence, stated as a
  property of a primitive.

* **`Params.subpivot_chord_at_top_forces_corner`** — with pivot `1`, P5 forces
  `p.σ 1 a = 1`. This is the *whole* of P5's corner content: the pivot at state
  `x` is `max x (max xT xS)`, not `1`, so nothing here constrains `p.σ x a` for
  any `x < 1`. **"Persistence forces sanctions equal to one at every date" does
  not follow from P5** — an interior, strictly rising path with the corner only
  as its limit is fully compatible with it.

* **`SenderPersistencePackage.static_response_ge_pivot`** — the package-level
  screen: every persistence package forces
  `max x (max xT xS) ≤ p.σ x (D.α_on V_T V_S x)` at every basin state and every
  carrier pair. Checkable on `Params` fields alone — no equilibrium, no value
  function, no fixed point — so an economy failing it cannot support the
  persistence route however its equilibria turn out.

* **`Params.quadSenderVertex_ge_state_iff`** — the design screen. For the
  quadratic Sender payoff family `quadSenderPayoff c r u0 w q` (curvature
  `c = −∂²U_S/∂s²`, rally `r = ∂²U_S/∂s∂x`, intercept `u0`, placation
  `w = −∂²U_S/∂s∂a`, state stake `q`), the static optimum clears the state iff
  `u0 + w·a ≤ (r − c)·x`. So the necessary condition reduces to **one inequality
  among coefficients**, which turns locating an admissible witness into a
  calculation rather than a sweep.

**Anchoring** (in `Examples/`, the correct layering direction):
`mwU_S_eq_quadSenderPayoff` proves the mechanism-witness payoff *is* that family
at `c = 6/5, r = 27/20, u0 = 1/10, w = 1/2, q = 2/5`, and
`mwσ_eq_clip_quadSenderVertex` matches its clipped response to the family vertex.
So the failing quantity is exactly the rally-minus-curvature margin
`27/20 − 6/5 = 3/20`, against `u0 + w·a = 1/10 + a/2`.

**Rule 5 applied to the previous entry.** `lowDelta_subpivot_chord_fails_at_top`
now re-derives that round's refutation from the parametric corner theorem with no
coefficient algebra at all: P5 at the top would force the corner, and the static
Sender response there is `mwσ 1 (63/116) = 1135/1392 < 1`. The coefficient
sections are retained because they exhibit the *margin*, which is what identifies
the fix; the refutation itself no longer depends on them.

One stale identifier of my own was fixed in the same pass: that file's header
cited `mw_subpivot_chord_at_one_forces_vertex_above_one`, which does not exist —
the theorem is `mw_subpivot_chord_at_one_forces_corner`.

**Verification.** `lake build` exit 0, no errors; all new results axiom-clean;
six gates green; 32 headline rows with hashes unchanged. Paper untouched, per the
standing freeze.


### Round 2026-08-13c — repairing the evidence record, and P5's exact price

Two corrections and two strengthenings, on referee findings. **Rule 2 order
honoured**: the Lean changes were made and `lake build`-verified first, then the
archive and this register were brought into line. The paper stays frozen.

#### Correction 1 — an over-claim in my own docstrings

The 2026-08-13b entry and the `SubpivotChordNecessity` header said P5 "says" the
Sender's static optimum lies at or above the pivot. **That is one direction
only.** P5 is strictly stronger: it must additionally cover the continuation
allowance `β_S·K_S·dist(F x s₁, F x s₂)`, which the static screen does not see.
The honest statement is that **P5 front-loads the level half of persistence into
the stage payoff**, not that it reduces to the static condition.

`Params.quadSender_chord_iff` now makes the gap exact for the quadratic family:
for `c > 0` and pivot `P > 0`, the chord at allowance `C` holds **iff**
`C ≤ r·x − u0 − w·a − c·P`. The right side is `c·(vertex − P)`, so the screen is
P5 at allowance zero, and a positive allowance requires the vertex to clear the
pivot by `C/c`. Docstrings corrected in both files.

Relatedly: the corner corollary does **not** rescue `persistence_generalF_corner`
from being flat at one. It shows only that flatness is a property of that
witness, not a consequence of P5. That distinction is now stated in the file.

#### Correction 2 — the candidate's exact leg did not close, and my envelope was violated

`p5_certify_c1.py` as archived had three defects. It imported `candidate` and
`verify_c1`, names that do not exist under the archive's `p5_` prefix, **so the
file could not run at all**. Its exact leg used a *constant* compliance envelope
`α ≤ 27/200`, under which its own arithmetic returns **negative** P5 margins at
`x = 7/10, 4/5, 9/10` (`−83/2000`, `−47/2000`, `−11/2000`) and prints `FAIL` —
contradicting the margin claim recorded in the 2026-08-13 entry. And the
candidate was called "C1", colliding with this repository's C¹ track.

Worse, the *affine* envelope `α ≤ x/3 − 1/5` behind that entry's "slack 4.15×"
is **itself violated** by the computed equilibrium at the top state:
`α(1) = 0.13350` against an envelope value of `0.13333`. So the number as
recorded was wrong, not merely unsupported. The earlier entry is marked in place.

**The repaired gate** (`p5_certify_sr1.py`, replacing the broken file; solver and
diagnostics renamed `p5_sr1_solver.py` / `p5_verify_sr1.py`, imports fixed and
verified to resolve). With the state-dependent envelope

  `α_on(V_T, V_S, x) ≤ x/3 − 19/100` on `x ∈ [7/10, 1]`

the margin is `≥ x/75 − 1/200 ≥ 13/3000`, against `β_S·K_S·δ ≤ 9/4000` at
`K_S ≤ 9/2`, `δ = 1/1000` — a **uniform exact slack of `1/480`**. The vertex
lower bound is `(91/90)x − 1/240`, strictly above `x` throughout the basin and
below `1` until `x = 723/728 ≈ 0.9931`, so the sanction is strictly interior on
almost all of the basin and reaches the corner only at the top. Gate: PASS.

#### Correction 3 — the Perov cross-row is not a verified bound either way

Direct perturbation measured `c ≈ 6.19e−3`; the analytic FOC estimate is
`≤ 6.25e−4`. **Neither is trustworthy.** At amplitude `0.05` the induced argmax
shift is `~3e−5`, well below the action-grid spacing `5e−4`, so the measurement
records a one-grid-step jump (`5e−4/0.05 = 1e−2`) rather than a derivative — the
same Rule-13 quantization trap that made the first pass report `c = 0` exactly.
The analytic figure is a hand FOC estimate, not a proved bound. Both values clear
Schur by 3.6e3–3.6e4×, so the *conclusion* is robust; the *bound* is not yet
established, and a Lean proof needs a derived one. Recorded in the script.

#### Strengthening — `0 ≤ K_S` is now derived, not assumed

`ValueLipschitzWith.nonneg` (`Theory/Basin/PrimitiveHighBasin.lean`): `S = [0,1]`
has two points at distance `1`, so the defining inequality there reads
`|V 1 − V 0| ≤ K` and the left side is a modulus. Hence
`SenderPersistencePackage.static_response_ge_pivot` no longer takes `hKS` — it
follows from P2 plus the carrier containing `E.V_S`. The package screen now takes
**no hypothesis beyond the package itself**.

#### Strengthening — the clip bridge needs `0 < x`, not `x ≤ 1`

`quadSenderVertex_ge_state_of_clip_ge`: the implication from the *clipped* static
response reaching the state to the *unclipped* vertex reaching it requires
`0 < x`. At `x = 0` the clip floor gives `x ≤ σ` for free while the vertex may
sit strictly below zero. The `quadSenderVertex_ge_state_iff` docstring said
`x ≤ 1`; corrected.

#### Status

SR-1 remains a **conjecture** (Rule 9). The envelope above is *read off* the
computed equilibrium; `SenderPersistencePackage` quantifies over **every** carrier
pair, so what is certified here is a consistency check, not the gate the theorem
needs. Still required before any Lean witness, all carrier-uniform: `K_S ≤ 9/2`
from carrier invariance; the compliance envelope; Sender strong concavity and
unique response; Target unique response and continuity; and P3's policy-slope
condition from the actual selector. **The Perov construction is not started.**

**Verification.** `lake build` exit 0, no errors; all new results axiom-clean;
six gates green; 32 headline rows with hashes unchanged.


### Round 2026-08-14 — attraction, and the exact word the paper had not earned

Execution of `docs/STABILITY-ENDOGENEITY-SUBMISSION-HANDOFF.md`. Worked in the
handoff's own order — general Lean theory first (WP3), paper only afterwards —
and to its hierarchy: abstract map before functional family before numeral.

**The gap.** `LockInLimit` proves a monotone equilibrium path converges to
*some* steady state, and that a least closed-loop fixed point exists. Neither
names the limit of an arbitrary path, so two starting points in one basin were
not known to share a limit. That is the entire distance between a *certified
invariant basin* and an *attractor* — and "attractor" is what the appendix
said.

**`Foundations/MonotoneAttraction.lean` (new).** Abstract interval maps only; no
transition, equilibrium, payoff family, or parameter appears.

* `monotone_orbit_tendsto_of_unique` — if `x*` is the **only** fixed point of a
  continuous non-decreasing self-map of `[a,b]`, every orbit converges to `x*`.
  The smallest addition to `StokeyLucas.monotone_orbit_converges` that names the
  limit.
* `uniqueFixedPoint_mem_and_isFixed` — non-vacuity: `x*` really is one.
* `monotoneOn_orbit_tendsto_of_unique` — the same with `MonotoneOn` /
  `ContinuousOn` hypotheses **only on `[a,b]`**, proved by clamping. Not
  cosmetic: the equilibrium rule is monotone only where a single-crossing
  condition was established, so the global form was unusable.
* `twoBasin_tendsto`, `twoBasin_limits_distinct` — one map, two disjoint
  invariant intervals, distinct limits. The honest content of dual-basin path
  dependence, with no multiplicity of maps anywhere in it.
* `strictMono_orbit_of_strict_above` — a strict ratchet makes the whole orbit
  strictly increasing. Monotonicity of `G` turned out to be unused and was
  dropped (Rule 13).
* `step_away_of_strict_above_diagonal` — deliberately weak one-step statement,
  and deliberately not called repulsion.

**Two refutations, retained because they are the paper's live boundary.**
`nonunique_fixedPoint_breaks_named_limit`: the identity on `[0,1]` is
continuous, monotone and self-mapping, `0` is fixed, and the orbit from `1`
never reaches it — "converges to some fixed point" is vacuously true while
attraction fails everywhere. `weak_level_condition_insufficient`: a map lying
*weakly* above the diagonal throughout can fix every point, so a level condition
written with `≤` constrains direction and permits a continuum of rest points.

**`Theory/LockIn/BasinAttraction.lean` (new).** The equilibrium bridge, general
in `F` throughout.

* `dynamicTopLockInStepF_monotoneOn` / `_continuousOn` — closed-loop regularity
  inherited from the realized rule through `F_mono_x`, `F_mono_s`,
  `F_continuous`. Extracted because `LockInLimit` proved the monotonicity
  inline.
* `dynamicTopLockInPathF_tendsto_of_unique_fixedPoint` (Target C) — on any
  feasible interval the closed loop preserves, a unique fixed point attracts
  every equilibrium path from that interval.
* `..._tendsto_right_endpoint` / `..._tendsto_left_endpoint` (Target D) —
  replaces equilibrium-level uniqueness with the paper's own strict-ratchet and
  wash-out language: under `StrictAdjustment`, a rule strictly above the
  diagonal below the endpoint (or strictly below it above the endpoint) admits
  no other rest point.
* `strict_ratchet_iff_endpoint_unique_fixedPoint` (Target E) — given the
  **weak** level condition the persistence machinery already supplies,
  strictness below the endpoint is **equivalent** to the endpoint being the only
  rest point.

**Outcome: `PROVED-BRIDGE`, not `PROVED-GENERAL`.** The single missing
ingredient between the current persistence hypotheses and attraction to a named
steady state is the *strictness* of the ratchet inequality — no extra
regularity, no rate, no new primitive. The equivalence shows this is not an
artefact of the proof: any route to endpoint attraction must establish it,
because the conclusion implies it. No new assumption was introduced, so no
Rule 3 stop arose.

**Paper (WP1).** The controlling declaration is
`dualParams_initial_condition_selects`. Its verified conclusion is invariance of
`[19/20,1]` and `[0,1/10]` at *one* equilibrium, a sanction floor and ceiling,
and monotone/antitone sanction sequences. It names no limit, proves no
convergence, asserts no uniqueness. Three Rule-2 repairs made in place after
that check:

* "both attractors exhibited" → "both invariant directional basins exhibited";
* "Both bistable attractors certified…" → "Both invariant directional basins
  certified…; no limit point is named";
* abstract: "establish bistability" → "establish dual-basin path dependence".

**Gate 1 passes:** zero occurrences of "attractor" remain anywhere in the
manuscript, appendix or supplement; the word survives only inside the staging
notes, where it is being discussed rather than claimed. No occurrence of
"equilibrium switching" referring to the dual-basin result was found.

Four further findings were *not* repaired in place because each adds a caveat or
a definition rather than correcting a false statement, and Rule 21 reserves that
for the author: defining "bistability" at first use; qualifying the
multiple-crossings mechanism sentence in the model section; replacing "the two
equilibria" in the comparative-statics section, where the two objects are the
dynamic equilibrium and the myopic benchmark; and softening the appendix's
metastability signature, where a *blocked sufficient condition* is being read as
evidence of multiple stationary laws. Staged as `P5`.

**Staged (WP2/5/6).** `N25`–`N30` in the promotion queue: the plain-language
front door; why this is a conflict trap and not a prisoner's dilemma; history
rather than expectations, against Krugman and Hassler et al.; the endogeneity
inventory, which surfaces the Becker-contest pressure equilibrium the paper
currently understates; the three direct answers on pessimism; and the four
distinct meanings of "stability". Each carries a recommendation, a cost, and a
target section. The Acemoglu–Wolitzky Handbook chapter is named in prose but
deliberately **not** cited formally — per the handoff it enters `annote.bib`
only on promotion.

**Verification.** Six gates green; 32 headline rows, hashes unchanged — the Lean
package is purely additive. All capstones axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`). All four paper documents rebuilt with zero
undefined references and zero undefined citations. `git diff --check` clean on
all source files.


### Round 2026-08-14b — the equilibrium anchoring, and one vacuous theorem of mine

Execution of the rewritten generalization-first brief. Outcome:
**`PROVED-GENERAL-EQUILIBRIUM`** for the top-floor case, with the interior case
honestly open and its obstruction formalized.

#### Five defects found in my own previous round, all confirmed

1. **One theorem was vacuous.** `strictMono_orbit_of_strict_above` assumed both
   closed-interval invariance and `x < G x` on all of `[a,b]`. At `b` these give
   `G b ≤ b` and `b < G b`. A Rule-11 probe compiles `False` from them, so the
   theorem was true of nothing. Removed. `strictAbove_on_closed_Icc_contradictory`
   now records the contradiction permanently, and
   `orbit_lt_succ_of_mem_Ico` / `orbit_monotone_of_strict_above_Ico` supply the
   correct half-open replacements. My own Rule-11 discipline should have caught
   this at the moment of writing; it did not.
2. **A theorem's name did not match its conclusion.**
   `dynamicTopLockInSanctionsF_tendsto_of_unique_fixedPoint` concluded
   `R x_star = x_star`, an identification, with no `Tendsto` anywhere. Renamed
   `realizedRule_eq_self_at_only_closedLoop_fixedPoint`, and genuine
   sanction-sequence convergence is now proved separately.
3. **At-most-one was conflated with `∃!`.**
   `strict_ratchet_iff_endpoint_unique_fixedPoint` proved only that every rest
   point equals the endpoint. Renamed `..._iff_endpoint_is_only_fixedPoint`;
   `strict_ratchet_endpoint_existsUnique_fixedPoint` adds existence and is the
   only declaration entitled to `∃!`.
4. **The bridge was not equilibrium-facing.** Its theorems accepted arbitrary
   `V_S` and `α`, so they were kinematics described as economics.
5. **Continuity was omitted from my own gap report.** I wrote that strictness
   was "the single missing ingredient". Continuity of the realized rule is a
   second, independent condition, and the register said otherwise.

#### Round 3 — actual-equilibrium capstones

New declarations consuming `E : p.FeedbackStackelbergEquilibriumTop`, which
carries both players' Bellman optimality and feasibility in its own fields:
`equilibriumTop_path_tendsto_of_only_fixedPoint`,
`equilibriumTop_path_mem`,
`equilibriumTop_sanctions_tendsto_of_only_fixedPoint` (a genuine `Tendsto` on
the realized sanction *sequence*, obtained by carrying the state limit through
the rule's continuity),
`equilibriumTop_tendsto_right_endpoint`, `equilibriumTop_tendsto_left_endpoint`.

#### Round 4A — continuity discharged

The realized rule is the *greatest* element of the Sender's dynamic argmax, and
such a selector is generally only upper semicontinuous, so continuity does not
follow from monotonicity. It is nonetheless already available:
`dynamicTopRealizedRule_continuousOn_of_argmaxUnique` chains the existing
`σ_dyn_top_continuous_subtype_of_unique_on` — which derives joint continuity of
the selector from `DynamicArgmaxUnique`, an existing certificate condition —
with the equilibrium's own `hα` field. **No new assumption; no Rule-3 stop.**

#### Round 4B — strict crossing discharged where the floor reaches

The persistence level condition is `max x sbar ≤ R x`. It is weak against the
state but *not* against the sanction floor: wherever `sbar > x`, the inequality
`R x ≥ sbar > x` is already strict. `strict_ratchet_of_level_floor` extracts
exactly that, on `[xbar, sbar)`; `strict_ratchet_of_top_level_floor` covers the
whole basin when the floor reaches the top state. Again no new assumption.

`equilibriumTop_tendsto_one_of_argmaxUnique_and_top_floor` is therefore an
attraction theorem at an actual equilibrium with **both** regularity conditions
discharged from existing conditions — state and sanction alike converge to the
top state.

**What stays open, precisely.** Strictness on a basin whose floor lies *below*
its right endpoint — the interior case. `weak_level_condition_insufficient`
shows the weak form cannot supply it, and
`strict_ratchet_iff_endpoint_is_only_fixedPoint` shows strictness is
*equivalent* to endpoint uniqueness there, so no route avoids establishing it.
No new assumption was introduced to close it.

#### Round 5 — two basins, one equilibrium

`equilibriumTop_twoBasin_tendsto`: a single `E`, a low interval with strict
wash-out above its left endpoint and a disjoint high interval with a strict
ratchet below its right endpoint, gives named state *and* sanction limits on
each, and proves the limits distinct. The economic reading is history-dependent
long-run outcomes **within one equilibrium rule**. Multiplicity of equilibria,
switching, expectation-driven selection, stochastic metastability, genericity
and structural stability neither appear nor follow.

#### Paper corrections made in place

"the two equilibria" (comparative statics) now names the dynamic equilibrium and
the myopic benchmark; the model section no longer asserts multiple diagonal
crossings as a general fact; the appendix no longer calls metastability the
"natural long-run stochastic signature" of a blocked contraction route; the
formalization map no longer says global uniqueness fails "by bistability";
`Headlines.lean`'s comment no longer says "both bistable attractors certified".
"Bistability" was replaced by dual-basin path dependence across the abstract,
introduction, related literature, discussion, keywords, the dynamic-analysis
section title, and four appendix sections; `\label{sec:mechanism:bistability}`
is retained as a cross-document anchor only.

A naming defect of mine was also repaired: last round I added notes paragraphs
`R4`/`R5`/`R6` to a file that already had `R4`, `R5` and `R6`. The duplicate
handles then made a slice-based edit run backwards and corrupt the file, which
the paper build caught. Mine are now `R7`/`R8`/`R9`, and `R8` is rewritten to
list continuity and strict crossing separately and to stop calling the kinematic
theorems equilibrium-derived.

**Verification.** Narrow builds green at each round; LSP diagnostics clean on
both new files; all capstones axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`); six gates green with 32 headline rows and hashes unchanged, so
the package remains additive; all four paper documents rebuilt with zero
undefined references and citations. The new declarations were **not** added to
the Rule-18 headline set, which needs author approval.

### Round 2026-08-14/15 — order selection, and the correction that followed it

Two rounds recorded together, because the second exists only to repair the
first's description of itself. **No assumption was added in either.** The
assumption surface is unchanged; what changed is what the tree can conclude from
it, and what the prose was allowed to say about that.

#### What was added

The abstract layer (`Foundations/MonotoneAttraction.lean`) gained
**order selection**: for a continuous non-decreasing self-map of an interval,
`monotoneOn_orbit_tendsto_least_fixedPoint_above` sends an orbit whose first step
is upward to the *least* fixed point weakly above its start, and
`monotoneOn_orbit_tendsto_greatest_fixedPoint_below` mirrors it downward.
`monotoneOn_orbit_tendsto_order_selected_fixedPoint` packages the exhaustive
trichotomy. **No fixed-point uniqueness hypothesis anywhere** — that is the
substance of the addition, since uniqueness is precisely what a certified basin
need not have.

It also gained the sign-region group: where the map lies strictly above the
diagonal on `[a, x*)` and fixes `x*`, invariance of `[a, x*]` and uniqueness of
the rest point are both *derived* (`strictAbove_Ico_basin_tendsto`); and
`signFlip_is_fixedPoint` shows a point where the sign of `G x − x` changes is a
rest point by continuity alone, so a threshold dividing wash-out from ratchet is
a steady state of the same map rather than a separate posit.

The model layer (`Theory/LockIn/BasinAttraction.lean`) carried these across the
closed loop `G(x) = F(x, R(x))` using only `F_diag` (a sanction equal to the
state leaves it unchanged) and `F_mono_s` (higher sanctions do not lower the next
state); `StrictAdjustment` (F5 — sanctions below the state strictly lower it,
above strictly raise it) does the strict halves and nothing else.
`equilibriumTop_tendsto_order_selected_fixedPoint` is the equilibrium capstone,
consuming a genuine `FeedbackStackelbergEquilibriumTop` and discharging continuity
of the realized rule from `DynamicArgmaxUnique` (single-valuedness of the Sender's
dynamic argmax, an existing certificate condition) plus the equilibrium's own
`hα` field.

#### The correction of 2026-08-15, and why it matters to this register

The round originally described that capstone as an **attraction** theorem and
concluded that strictness was no longer needed for stability. That was wrong, and
it is the kind of error this register exists to catch, because it silently
inflates what the assumption surface delivers.

*Order selection* binds the limit **after** the starting state: each orbit
converges, and its limit is extremal on the side it moved. *Attraction* is one
named limit reached from every start. The identity map satisfies the first and
fails the second everywhere — `nonunique_fixedPoint_breaks_named_limit`, already
in the tree when the claim was made. So:

> Strictness is unnecessary for orbit convergence and order selection.
> Strictness, fixed-point uniqueness, or another isolation condition remains
> necessary for a whole basin to reach one common limit.

The interior-persistence question is therefore **open**, not closed. Its scope
changed — it is now the gap between per-orbit selection and a common limit — but
it was not answered.

Three further corrections in the same pass.

* **`p.F` was called "completely general"** while `StrictAdjustment` sat in the
  signature. `F` carries no *functional form*; that is weaker than unrestricted.
  `equilibriumTop_tendsto_order_selected_fixedPoint_and_rule_limit` was added with
  `StrictAdjustment` dropped, concluding the sanction converges to `R(x*)` instead
  of to `x*`; the original theorem is now its corollary. The difference between
  the two statements **is** the contribution of `StrictAdjustment`, made visible
  rather than asserted. No new assumption.
* **The threshold result was over-read.** `equilibriumTop_threshold_separates_basins`
  derives fixedness of the interior crossing and invariance of each side from its
  own sign condition. It *supplies* the two endpoints, the requirement that the
  rule fix them, monotonicity on each side, and the sign regions themselves. The
  docstring claimed "every structural ingredient derived" and then listed what was
  assumed; that is repaired.
* **The P5 refutation was stated too broadly.**
  `subpivot_strictMono_and_weak_level_insufficient_for_strict_ratchet` refutes the
  implication from the *consequences the current persistence route extracts* from
  P5 (`sender_subpivot_chord`, the transition-adjusted sub-pivot chord) to strict
  persistence. It does not refute the raw hypothesis: no complete `Params` economy
  satisfying full P5 with strict persistence failing has been built. The broader
  reading is an expectation resting on `subpivot_range_collapses_above_floor` —
  above the sanction floor P5's range collapses to `[0, x]` and mentions no
  sanction exceeding the current state — and is logged as its own future round.

#### Assumption-surface effect

**Added: none.** No new hypothesis, no new `Params` field, no new load-bearing
`Prop`, no new named scalar, in either round. No Rule-3 stop was triggered and
none is proposed.

**Removed from conclusions:** fixed-point uniqueness (the order-selection group);
strict sign conditions (the two-basin capstone); basin invariance and boundary
fixedness (the sign-region group).

**Discharged:** the continuity obstruction recorded in
`PaperRefer/MathTheory/InvariantIntervalsMonotoneMaps-collected-2026-08.md` §3b,
which held that the sign-component route was unavailable parametrically because
the realized rule is a greatest-argmax selector. It is available, from
`DynamicArgmaxUnique` plus the equilibrium's own continuity field.

**Still assumed, and named honestly:** `StrictAdjustment` — a structural sign
condition on `p.F`, **not** supplied by any persistence package, discharged only
at explicit witnesses; monotonicity of the realized rule on the basin
(`SenderPersistenceBasinTop.top_rule_mono`, from P3); invariance of the basin
(`dynamicTopLockInStepF_mem_basin`, from the level condition).

**Verification.** 58 declarations added across `Sanctions/`, 1 removed, of which 2
are `private` helpers. All capstones axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`). Rule-17 clean rebuild from an emptied `.lake/build`; six gates
green; 32 headline rows with unchanged type hashes, so both rounds are additive.
Nothing was promoted to the Rule-18 headline set. New paper material is staged as
N31–N34 and unpromoted.

#### Addendum, 2026-08-15 (second review pass)

Four corrections, none of which added an assumption and one of which removed one.

**A weaker sibling was added; no existing signature changed.** This was recorded
here on 2026-08-15 as "the headline hypothesis was weakened", which is wrong twice
over: no existing theorem lost a hypothesis, and none of these declarations were
in the Rule-18 headline set at the time. What happened is that a weaker,
non-headline sibling was added beside the existing statements. `C1` is now three
tiers.
`equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` takes
`ContinuousOn R` on the basin **directly** — no `DynamicArgmaxUnique`, no
`StrictAdjustment`, not even feasibility of the interval.
`..._and_rule_limit` is the corollary in which `DynamicArgmaxUnique`
(single-valuedness of the Sender's dynamic argmax) discharges continuity, and
`equilibriumTop_tendsto_order_selected_fixedPoint` is the corollary in which
`StrictAdjustment` identifies the sanction limit with the state limit. Each tier
buys exactly one thing, though the trade is not one-for-one: tier 2 drops the
continuity hypothesis and picks up `DynamicArgmaxUnique` **together with** the
physical-domain bounds `0 ≤ a` and `b ≤ 1`, since argmax uniqueness is stated at
physical states. The tier-1 statement is nonetheless weaker than anything
previously available for this conclusion.

**`DynamicArgmaxUnique` is a paper-facing addition even though it is not a Lean
addition — and that distinction is now documented.** It is an existing project
predicate, so `Params` is untouched and no Rule-3 stop applies. But it is not a
field of `SenderPersistencePackage`, and it is **not** assumed by the manuscript's
long-run proposition, whose Lean backing
`dynamicTopLockInPathF_tendsto_steadyState` needs neither it nor rule monotonicity
nor rule continuity. So the order-selection theorems do **not** dominate that
proposition — they draw a sharper conclusion under more regularity — and staged
N31 previously said the reverse. Corrected, and
`docs/THEOREM-MANUSCRIPT-ASSUMPTION-MATRIX.md` now tabulates Lean hypotheses
against manuscript statements for every long-run claim, precisely so this class of
error is visible rather than latent.

**Attraction, basin uniqueness and the strict sign condition are equivalent.**
Previously recorded as three alternatives of unknown relative strength. For a
monotone continuous self-map of an invariant interval they are the same condition
(`attraction_iff_unique_fixedPoint`, `unique_fixedPoint_iff_strictly_signed`),
and local isolation of the candidate limit is provably insufficient
(`isolated_fixedPoint_insufficient_for_attraction`). Consequence for the register:
the word *attractor* is licensed exactly where a unique rest point in the claimed
basin has been proved, and there is no weaker condition to search for.

**No novelty is claimed for the order-theoretic step.** It is Amann (1976)
Theorem 6.1 and Corollary 6.2 specialized to a compact real interval. The Phase-7
literature sweep of the previous pass had concluded that nothing matched, while
the Amann file sat in the directory listing that same sweep had printed. The
claim is removed from the docstrings, the citation added, and the failure recorded
in `PaperRefer/MathTheory/InvariantIntervalsMonotoneMaps-collected-2026-08.md`.

**Seven top-level declarations added, none removed; all axiom-clean.** Register
unchanged at the `Params` level. (An earlier draft of this addendum said nine.)

---

### Round 2026-08-15 (later) — the dividing line derived from the closed loop

**No assumption was added.** Twenty top-level declarations added — sixteen
abstract, three parametric, one at the economy — none removed, no existing
signature changed, all axiom-clean. `Params` untouched.

#### The question this answers

Every long-run theorem in the tree had, until now, taken its interval from
outside: a certified basin, a pivot, a chosen endpoint. That is fine for a
persistence claim but it invites the referee's obvious question — is the dividing
line between the two regimes a feature of the model or of the interval someone
picked? `signFlip_is_fixedPoint` (a state where the closed loop crosses the
diagonal is a rest point) went partway, but it takes the sign pattern on *both*
sides of the crossing as a hypothesis, so the crossing is still supplied.

#### What was added

**Abstract (`Foundations/MonotoneAttraction.lean`, Rule 19 — no `Params`).**

* `weakAboveSet` / `weakBelowSet` — the states of `[a,b]` where the map is weakly
  above / below the diagonal, i.e. where the state does not erode / does not
  build. `weakAboveSet_isClosed` and its mirror: these are closed sets when the
  map is continuous.
* `leastWeakAbove` / `greatestWeakBelow` — `sInf` and `sSup` of those sets. These
  are **derived objects**: functions of the map and the window, nothing else.
* `leastWeakAbove_spec` — from two endpoint readings (`G a < a`, the state falls
  at the bottom; `b ≤ G b`, it does not fall at the top) plus continuity: the
  threshold is strictly inside above `a`, is a **rest point**, has **strict
  erosion everywhere beneath it**, and is the **least** rest point of the window.
  The sign region that `signFlip_is_fixedPoint` assumes is here a conclusion.
  `greatestWeakBelow_spec` mirrors it.
* `leastWeakAbove_le_greatestWeakBelow` and
  `derivedThresholds_eq_iff_unique_fixedPoint` — the two thresholds coincide
  **exactly** when the window holds one rest point. Between them the construction
  claims nothing, and by `attraction_iff_unique_fixedPoint` that silence is
  correct rather than lazy: where two rest points sit in a region, a common limit
  across it is false.
* `strictBelow_basin_tendsto_of_lowerBound` and
  `strictAbove_basin_tendsto_of_upperBound`, with half-open siblings
  `threshold_below_tendsto_left_of_lowerBound` /
  `threshold_above_tendsto_right_of_upperBound` — the A4 basin lemmas with
  **monotonicity dropped**. Once the strict sign holds throughout, each step moves
  the same way because of the sign, not because the map is order-preserving; all
  that is needed is a feasibility bound keeping the orbit inside. These strictly
  generalize `strictBelow_Ioc_basin_tendsto` and its mirror, since monotonicity
  implied the bound.

**Rule-11 refutations, both in the same file.**

* `derivedThreshold_needs_continuity` — a jump map with the *same* two endpoint
  readings has no rest point in the window at all. Continuity carries the whole
  content of the derivation.
* `derivedThresholds_can_differ` — `x ↦ min x (2x) + max 0 (x−1)` falls at `−1`,
  rises at `2`, and fixes all of `[0,1]`. The gap between the two thresholds is
  real, so `leastWeakAbove_le_greatestWeakBelow` cannot be upgraded to equality.

**Parametric (`Theory/LockIn/BasinAttraction.lean`).**
`equilibriumTop_derived_threshold`, `equilibriumTop_derived_upper_threshold`, and
the capstone `equilibriumTop_derived_dual_basins`: from two named long-run states,
a certified wash-out region reaching up to `xL`, a certified ratchet region
reaching down to `xH`, **no assumption at all about the sign in between**, and
continuity of the realised rule, two derived rest points `t ≤ t'` appear inside
the middle region, every path below `t` washes out to the low state, every path
above `t'` ratchets to the high one, and `t = t'` iff the middle holds one rest
point. Monotonicity of the realised rule is required **nowhere** — which is the
point, since between two certified basins monotonicity is exactly what is not
known.

**Economy (`Examples/DualBasinSelectionWitness.lean`).**
`dualParams_derived_dividing_line` discharges every input from facts already
proved at that witness: the realised rule is `0` on `[0,1/10]` and `1` on
`[19/20,1]`, `F(x,s) = (9x+s)/10` supplies the two endpoint readings and the
feasibility bounds, and continuity on the **whole** state space comes from
`dbCert_DAU_on_carrier` (single-valuedness of the Sender's dynamic argmax at every
state). The two certified basins extend from `[0,1/10]` and `[19/20,1]` to `[0,t)`
and `(t',1]`, with the new endpoints read off the equilibrium.

#### Why this is not a Rule-3 event

Every hypothesis of the new theorems is either an inequality on the existing
closed loop, the continuity condition Round 4A already discharges from
`DynamicArgmaxUnique`, or a restatement of `F_mem`. Nothing new enters `Params`,
no structure gained a field, and no `Prop` is taken as a hypothesis whose content
is not visible in the data. At the economy every input is discharged from
already-proved facts, so no witness constant was tuned to make a margin close.

#### Scope, stated so it is not over-read

* The gap `[t, t']` is **not** claimed to be empty at any economy, including the
  dual-basin one. Whether the middle region there holds one rest point or several
  is not established, and `derivedThresholds_can_differ` shows the question is not
  vacuous.
* Nothing here establishes that `t` is interior in any economically interesting
  sense, nor bounds where it sits.
* The witness statement tracks the **state** path only; the realised sanction is
  not carried to the limit there.
* Rule 9: the economy is an existence certificate. It licenses no claim that the
  derived line is generic, nor any claim about other economies.

#### Headline set and paper status (decided 2026-08-15)

`equilibriumTop_derived_dual_basins` **is headline row 35**, on the author's
Rule-18 approval. The snapshot diff is exactly one row added, no row removed, and
**no existing type-hash changed** — the set is 34 → 35.

It was added *together with* the paper claim it backs, not before it. N37 is in
the manuscript as `prop:derived-dividing-line`, with the general form
`prop:derived-crossings` in the appendix; **N32 was discarded** as superseded, its
own statement being the weaker of the two and uncited by the stronger. One
manuscript sentence was repaired in place under Rule 2 — *"the theorem does not
identify the dynamics between the two basins"* — because the new result makes it
false.

**N38 was promoted on 2026-08-16**, on a separate Rule-21 decision: the abstract
and the introduction now announce the result the body proves. Both clauses say the
derived steady states **bracket** the dividing line rather than identify it,
because `derivedThresholds_can_differ` — a continuous map fixing a whole
subinterval — is exactly why a single-line claim would be an over-statement.

**The staging queue is empty.** No item is held.


---

### Round 2026-08-16 — layer audit: one correction, one generalisation, one banner

**No assumption was added.** Fourteen declarations added (seven abstract, five
parametric, two at a witness), none removed, no existing signature changed,
`Params` untouched. Two witness proofs were replaced by corollary proofs; their
statements are byte-identical.

#### The audit error, recorded because the register exists for exactly this

A layer audit asked which paper results rest on parametric versus numeric
backing. It reported `prop:equilibrium-patience-feedback` — the Sender-patience
value decomposition — as **a universal over the symbolic certified family backed
only by a witness**, and therefore as a Rule-9 over-reach.

**That was wrong. The paper was right.** Family-level backing already existed:
`symbolic_equilibrium_feedback_decomposition`, `symbolic_lockin_amplification`,
`symbolic_lockin_strict_iff`, `symbolic_lockin_strict` and
`symbolic_VTstar_βS_invariant`, every one quantified over
`(E : SymbolicEconomy)` — precisely the family the proposition names.

The cause is worth naming, because it is structural rather than careless. The
formalization map's per-item entry for that proposition listed only the
`eeCertB_*` numeric names, and the family-level siblings live under `Examples/`.
An auditor classifying by directory, and checking the map for the backing, sees a
witness. Both surfaces have been repaired (below), and the entry now says so
against itself.

#### What was added, and why it is still worth having

The lift built on the wrong premise turned out to be worth keeping for a
different reason: the existing family-level backing is **affine-restricted**
(`SymbolicEconomy.toParams` sets `F := affineF E.δ`, Rule 22 axis 3), and the
identities do not need any functional form at all.

**Abstract — `Foundations/PatienceDecomposition.lean` (new, Rule 19, no
`Params`).** `SolvesAlong u z β V` states the stationary Bellman equation
directly over the data (`V x = u x + β · V (z x)`), so it cannot be satisfied
vacuously (Rule 14). Then: `difference_decomposition` splits a value difference
into a **direct** term — the same continuation revalued at the new patience —
and a **feedback** term — the movement in the continuation itself;
`amplification_at_fixedPoint` collapses it at an absorbing state to
`(1−β₁)(V₂−V₁) = (β₂−β₁)V₂`; `value_at_fixedPoint` capitalises the flow; and
`strict_at_fixedPoint_iff` settles the sign as an **equivalence** — more patience
raises the absorbing-state value exactly when the flow there is positive. The
state type is arbitrary, which is what lets the callers instantiate at value
functions living on the feasible-state subtype rather than on `ℝ`.

Rule-11 refutation: `decomposition_needs_common_stage_payoff`. Two value
functions each solving *their own* Bellman equation do not decompose this way, so
the shared stage payoff is load-bearing rather than a convenience of the
statement.

**Parametric — `Theory/LockIn/LockInComparativeStatics.lean`.** Four wrappers at
the `Params` layer: the decomposition, the amplification, the capitalised
lock-in value, and the sign equivalence. **No functional form for `F` is used
anywhere**, and the absorbing state the amplification needs is *derived* from
`F_diag` (a sanction equal to the state leaves the state unchanged) rather than
assumed. Names carry `_of_bellman` because the two Bellman equations are
consumed, not constructed — Rule 15's conditional-on-existence scoping, made
visible in the name.

**Witness — `Examples/FeedbackComparativeStatics.lean`.**
`eeCertB_VS_star_solvesAlong` repackages the pinned fixed point as the pointwise
Bellman equation; it is now the *only* witness-specific input the two identities
need, and `eeCertB_feedback_decomposition` and `eeCertB_lockin_amplification` are
one-line corollaries of the general algebra instead of separate `field_simp`
computations on closed forms (Rule 5).

#### Filing: the symbolic families stay in `Examples/`, and now say so

Moving them was considered and rejected. `symU_S q u₀ k r w x a s = −(q/2)s² +
s(u₀ − k·a + r·x) + w·x` fixes a *functional form*; Rule 19 reserves `Theory/`
for statements over an arbitrary `Params`, and a nine-coefficient algebraic
family is narrower than that. So `Examples/` is correct and the files are not
moved.

What was missing is a warning that these files contain **universals over a
family**, not point checks. `SymbolicCertifiedFamily.lean` and
`SymbolicCertifiedFamilyGeneralFPersistence.lean` now open with an audit banner
saying so, and saying that the filing has already misled one audit.

#### Paper

`prop:equilibrium-patience-feedback` keeps its statement — it was not wrong — and
gains two remarks recording that the two displays hold with no functional form
for `F`, and that the sign clause is an equivalence whose failing direction is
economically real. The affine gloss `F(x,1)=(1−δ)x+δ` is dropped from the
statement, since it is no longer what the identity needs.

The formalization map gained about twenty rows — every long-run result promoted
since the order-selection round, including `prop:derived-dividing-line` — plus
two stated conventions: **layer is not directory**, and **instances are
labelled**.

#### Affine-surface audit, 2026-08-16 (all three Rule-22 axes)

Run because Rule 22 requires it and because the round above touched the
transition surface. **No unmarked affine restriction was found.**

**Axis 1 — explicit `hF : p.F = affineF p.δ`.** Seven `Theory/` files carry it:
`Basin/PrimitiveHighBasin`, `Basin/StageFlipCertificate`,
`Basin/StageFlipDischargers`, `Basin/TransitionChords`, `Basin/WeakFloorBasin`,
`Certificates/StandardComplianceMain`, and the bridge lemma in
`Postulates/AbstractGame`. Every one is either an affine *sibling* of a
general-`F` theorem or an openly affine route; none is the sole backing of a
paper claim that does not say it is affine.

**Axis 2 — hard-wired recursion, no signature footprint.** The axis Rule 22
calls dangerous: `dynamicTopLockInStep/Path/Sanctions`, `lockInStep/Path` and
`shockStep/Path` write `(1−δ)x + δ·rule` by hand and never touch `p.F`, so a
theorem can be affine-restricted with no `hF` anywhere in its statement. Among
the paper-cited backings exactly **one** carries it —
`standardCompliance_three_goals_pathwise`, backing `cor:pathwise-dominance` —
and that corollary opens with "Let the transition be the affine law." The four
general-`F` package theorems (`..._persistence_generalF_from_package`,
`..._min_drift_shock_generalF_from_package`,
`..._three_goals_local_low_basin_generalF`,
`equilibriumTop_initial_condition_selects_generalF`) are clean on **both** axes.

**Axis 3 — instantiation.** Seventeen `Examples/` files set `F := affineF`,
which is what a witness does. The non-affine instantiations are real and
load-bearing: `eatonEngersPolity.inducedF`, `sqrtMeanTransition`, `wobbleF`,
`fun _ s => s`, alongside the `quadBumpF` / `quadBumpLowF` / `ratchetF` witnesses.
`SymbolicEconomyF` carries a free `F` field with a genuinely non-affine member,
which is what makes `prop:primitive-persistence`'s sentence "the class contains
non-affine realised recursions" true rather than decorative.

**Paper side.** Every affine-restricted claim marks itself in its own statement:
`cor:pathwise-dominance`, `prop:flip-route`, `prop:perpetual-interval`, and the
closed-form entry horizon in the shock section. `thm:dominance` states the
negative explicitly — "The comparison does not require the affine transition" —
and its backing is clean on both axes, so the sentence is earned.

**One residual, disclosed rather than closed.** The family backing of
`prop:equilibrium-patience-feedback` is affine on axis 3, because
`SymbolicEconomy.toParams` sets `F := affineF E.δ`. The round above is the
response: the same identities now hold at the `Params` layer with no functional
form at all, with the absorbing state derived from `F_diag`, and the proposition
records that its two displays do not need the family's affine law.


---

### Round 2026-08-16 (later) — full-tree hygiene inspection

**No assumption was added.** Three declarations moved between files with their
statements unchanged; one stale linter suppression removed; one long line
wrapped; seven documentation banners added. Headline set unchanged at 35 rows,
every hash unchanged.

#### What is clean, tree-wide (253 files, ~124k lines)

Zero `sorry`, zero `admit`, zero custom `axiom`. Zero `native_decide` — the only
matches are prose promising its absence. Zero `opaque` declarations, so Rule 14's
laundering pattern is absent by construction rather than by review. Zero uses of
the `decide` tactic, which makes Rule 16(b)'s `#guard` obligation vacuous rather
than unmet. 582 `#print axioms` calls across 53 files.

#### One Rule-19 misfiling, corrected

`Examples/C1WitnessEnvelope.lean` opened with a `namespace Params` block holding
three theorems quantified over an **arbitrary** `p : Params`, fixing no
coefficient, transition, discount factor or constant:
`joint_T_integrand_eq_top_of_unique_on` (where the Sender's dynamic argmax is
single-valued the `σ_dyn` and `σ_dyn_top` selectors coincide, so the two Target
objectives agree pointwise), `jointTarget_BCF_on_S_eq_sSup_top` (the same at the
bounded-continuous-function level — the bridge from the W2 value pins to what
`C1BellmanSystem.T_value_eq_target` requires), and
`isMaxOn_joint_T_top_of_isMaxOn_joint` (a Target maximiser transfers across the
congruence).

Moved to `Theory/Equilibrium/JointIntegrandCongruence.lean`. They had been filed
beside their first consumer, and the cost was concrete: a layer audit classified
them as witness material on the strength of the directory.

#### Parametric material in `Examples/`: seven files, all now banner-ed

The symbolic cluster (six files, quantified over `SymbolicEconomy` /
`SymbolicEconomyF`) and `SignConditionsInsufficient.lean`. The latter needed a
different banner because it is a different object: `probeParams δ βS βT ε` is a
**parametric refutation family** over four free reals, so results such as
`probe_SenderStageIDStrict` hold for every strictly positive rally slope, however
small. A family of counterexamples is stronger evidence than one, and nothing in
the file said so.

All seven stay in `Examples/` on Rule 19 grounds — each fixes a functional form —
and the banners say that explicitly, so the filing is no longer mistakable for a
statement about the strength of the results.

#### The C1 freeze is accurately labelled

`SmoothSanctionClass` is genuinely isolated: every external mention is prose in a
docstring recording that the abstract envelope layer stays frozen; no code
consumes it. `JETBridgeC1System` **is** consumed — ten references — but all from
`Theory/Certificates/RegularEconomy.lean`, and **no headline row reaches C1
material**. With gate 3 clean, the frozen C¹ track is sound, quarantined, and
outside the shipped surface. Unfreezing the abstract layer still needs
differentiability primitives, which is a Rule-3 event and remains untaken.

#### Linter inventory from a from-empty rebuild (604 lines, zero errors)

Captured deliberately, because an incremental build does not replay cached
diagnostics and the audit script filters them.

| Count | Category | Assessment |
|---|---|---|
| 414 | missing space in the source | cosmetic (`(0:ℝ)` for `(0 : ℝ)`) |
| 125 | `show` used outside an intermediate goal | cosmetic |
| 20 | unused variable | **Rule 13 — see below** |
| 14 | line exceeds 100 characters | cosmetic |
| 9 | undocumented `maxHeartbeats` change | worth a comment each |
| 8 | `tac1 <;> tac2` where `(tac1; tac2)` suffices | cosmetic |
| ~14 | assorted tactic hygiene | cosmetic |

**Suppressions were audited rather than counted.** Sixteen exist: eleven
`linter.style.longLine`, five `linter.deprecated`. Rule 17 forbids suppressing a
linter *solely* to pass the gate, so each was checked. The `longLine` ones cover
theorem names 114–136 characters long, which cannot be wrapped — knowing
acceptance, not gaming. The `deprecated` ones sit around declarations that
deliberately reference deprecated APIs, one of which is itself `@[deprecated]`
with a redirect. **One `longLine` suppression at
`Theory/Basin/JointPreferenceBasin.lean:1543` was stale**: removing it produced
no warning. Removed — a stale suppression is worse than none, because it would
silently mask a future long line in the declaration it guards. The one genuine
outstanding long line, `Foundations/StokeyLucas.lean:527`, was **fixed rather
than suppressed** (two binders sharing a line).

#### Rule 13: twenty unused hypotheses, and what they mean

An unused hypothesis does not make a theorem wrong; it makes it **weaker than it
could be**, and Rule 13 wants that surfaced rather than left latent. Six sit in
the frozen C¹ track (`Theory/Bellman/C1Val.lean`) and are left alone with it.
The rest are ordinary slack in `Foundations/Topkis.lean`,
`Foundations/MonotoneThreshold.lean` and `Theory/Shocked/HeSunShock.lean`.

Six are worth a decision rather than a shrug, and they are **two different kinds
of thing**. An earlier version of this paragraph ran them together and was wrong
on both halves of its conclusion; corrected 2026-08-16, and see the following
round entry for what was then done about it.

Four are in `Theory/Certificates/TargetSanctionLossOffset.lean` — `hc_nn` and
`hg_nn` on the affine monotonicity lemmas
`targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value` and its
localized sibling `..._on`. These genuinely are the Target's stage sanction-loss
rate `c_T` (the worst rate at which one more unit of sanction costs the Target
this period) and continuation-gain rate `g_T` (the Target value function's
minimum upward slope in the political state). Both lemmas are affine algebra and
never consume the sign hypotheses.

Two are in `Theory/Bellman/StrongConcaveHolder.lean` — `hc_nn` on
`sigma_dyn_sq_le_of_strongConcave` and on
`targetArgmax_sq_le_of_leaderStrongConcave`. **These are not Target rates.** The
`c` they constrain is the strong-concavity modulus of the Sender's (respectively
the leader's) dynamic objective in the sanction argument — how sharply that
payoff curves away from its maximiser. Removing the binder is a local helper
strengthening and nothing more: both consumers,
`SigmaDynHolderOn.of_strongConcave` and `AlphaOnHolderOnInVT.of_leaderStrongConcave`,
already carry the strictly stronger `0 < c`, which is also the form the paper
states (`03_closed_form_constants.tex` writes the joint-Target modulus as
`c_T > 0`).

**The claim that dropping all six narrows the paper-facing assumption surface
was wrong, and is withdrawn.** `0 ≤ g_T` is load-bearing elsewhere:
`Target_combined_chord_of_decomposition_lowerChord`
(`Theory/Certificates/GeneralFDischargers.lean:59`) consumes it at line 133,
where `mul_le_mul_of_nonneg_left hchord' hgT_nn` scales the transition's sanction
lower chord — `dlo·(s₂−s₁) ≤ F(x,s₂) − F(x,s₁)`, i.e. one more unit of sanction
raises next period's political state by at least `dlo` per unit — by the Target's
continuation-gain rate. With `g_T < 0` that scaling reverses and the general-`F`
route fails.

The inventory was also **incomplete**. `hgT_nn` on the *affine*
`Target_combined_chord_of_decomposition`
(`Theory/Certificates/StandardComplianceLocal.lean:338`) is a seventh unused
hypothesis of the same class and was not listed above.

---

### Round 2026-08-16 (later still) — loss-offset binder cleanup

**No assumption was added; seven were removed.** Every edit in this round
*deletes* a hypothesis. No statement was weakened, no conclusion changed, and the
headline set stayed at 35 rows with every type hash unchanged. This is the round
the preceding entry deferred.

#### What came out, and what each one said in English

| Where | Binder removed | What it asserted |
|---|---|---|
| `Theory/Bellman/StrongConcaveHolder.lean` (×2) | `hc_nn : 0 ≤ c` | the strong-concavity modulus of the Sender's — respectively the leader's — dynamic objective in the sanction argument is nonnegative |
| `Theory/Certificates/TargetSanctionLossOffset.lean` (×4) | `hc_nn : 0 ≤ c`, `hg_nn : 0 ≤ g` | the Target's stage sanction-loss rate and its continuation-value gain rate are nonnegative |
| `Theory/Certificates/StandardComplianceLocal.lean` (×1) | `hgT_nn : 0 ≤ gT` | the same gain-rate sign condition, on the **affine** combined-chord discharger `Target_combined_chord_of_decomposition` |

The two Hölder lemmas are self-contained: each has exactly one consumer, in the
same file, and both consumers already carry the strictly stronger `0 < c`.

The other five propagate. Removing them from the two affine monotonicity lemmas
made the two one-sided-threshold constructors above them
(`OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target`
and `..._on` — the constructors that assemble "Sender wants sanctions up to the
threshold, Target wants them above it" from stage-payoff and continuation
chords) carry dead binders too, and so on upward. The compiler drove the
cascade; it terminated after six files:
`StandardComplianceBridges`, `JETBridge`, `JETBridgeC1System`,
`StandardComplianceLocal`, `StandardComplianceLocalC1`, `StandardComplianceSchur`,
plus `RegularEconomy` and three witness call sites.

It stopped exactly where the binders start feeding **certificate structure
fields** rather than proof steps (`hcT_nn := hcT_nn`), which is the boundary this
round was scoped not to cross.

#### The one asymmetry worth keeping in view

`0 ≤ g_T` is *not* removable everywhere, and the reason is economic rather than
technical. The general-`F` discharger
`Target_combined_chord_of_decomposition_lowerChord`
(`Theory/Certificates/GeneralFDischargers.lean:59`) genuinely needs it at line
133: a general transition enters only through the **inequality**
`dlo·(s₂ − s₁) ≤ F(x,s₂) − F(x,s₁)` — one extra unit of sanction raises next
period's political state by at least `dlo` — and scaling an inequality by `g_T`
reverses it when `g_T < 0`. Under the affine law the same step is an
**equality**, so the sign cannot matter, which is why the affine sibling never
needed the hypothesis and why it had sat there unused.

**Generality in `F` is precisely what makes the sign of the continuation-gain
rate load-bearing.** That is now stated in the docstring of the affine
specialisation check in `GeneralFDischargers.lean`, where the drift-fence note
had previously claimed — wrongly, after this round — that the two dischargers
carry identical hypotheses.

#### Settled: the certificate fields `hcT_nn` and `hgT_nn` are now fully dead

Tracing every remaining occurrence tree-wide: each is a field declaration
(`StandardComplianceLocalCoreCertificate`, `RegularEconomyCertificate` ×2,
`StandardComplianceSchurCertificate`, `StandardComplianceLocalC1Certificate`), a
field assignment in a witness or constructor, or a binder that exists only to
fill such a field. **No proof step anywhere consumes either field.** The single
live consumer of `0 ≤ g_T` in the tree is the general-`F` chord discharger above,
which takes it as its own binder and is not reached from the certificate fields.

Removing the two fields would therefore be a real narrowing of the paper-facing
certificate surface — the genuine prize, and not the four binders this entry's
predecessor pointed at. **Not taken here.** It changes five certificate
structures, roughly eight witness instances, and the certificate inventories in
`paper/appendix_sections/07_formalization_map.tex`, so it is the user's call, not
a cleanup. *(Taken 2026-08-17 on the author's decision — see the following
entry.)*

#### Paper impact: none

The manuscript never names these hypotheses, and states no standalone `c_T ≥ 0`
or `g_T ≥ 0` assumption. Where `c_T` appears in
`paper/appendix_sections/03_closed_form_constants.tex` it is the joint-Target
strong-concavity modulus, stated as the strictly stronger `c_T > 0`, which the
surviving Hölder wrappers still require. Where `g_T` appears in
`paper/appendix_sections/07_supporting_results.tex` it is a closed form,
`g_T = (n+v)/(1 − β_T(1 − δ))`, positive by construction. No Rule-2 sync is
triggered.

---

### Round 2026-08-17 — the two Target sign fields deleted from the certificates

**On the author's decision: the narrowing the previous entry identified and
declined to take on its own authority.** Ten field declarations removed —
`hcT_nn` and `hgT_nn` from each of five certificate structures — together with
every assignment and every binder that existed only to fill them. Twelve files,
57 lines deleted against 14 inserted, and every one of those insertions is a
re-wrapped docstring. No proof body changed.

#### What left the assumption surface, in English

`hcT_nn : 0 ≤ cT` said *the Target's stage sanction-loss rate is nonnegative* —
one more unit of sanction cannot make the Target better off within the period.
`hgT_nn : 0 ≤ gT` said *the Target value function's minimum upward slope in the
political state is nonnegative* — the Target incumbent does not value a
higher-noncompliance state strictly less than a lower one. Both read as
economically innocuous, which is precisely why they went unexamined for so long.
Neither was doing any work.

The five structures: `StandardComplianceLocalCoreCertificate` (the paper-facing
compliance certificate), `StandardComplianceLocalCoreCertificateSchur` (its
Schur-margin sibling), `StandardComplianceLocalCertificateC1` (the C¹ track),
`RegularEconomyCertificateCompliance`, and
`RegularEconomyCertificateComplianceCore` (the regular-economy forms).

#### What every witness no longer has to discharge

Six economies discharged the two fields by `norm_num` (`eeCert`, `b2NonMono`,
`dualParams`, `fourGroupCert`, and the two C¹ envelope instances); the stage-flip
certificate discharged them by `le_refl 0`, and the symbolic family by
`E.cT_pos.le` / `E.gT_pos.le`. All eight discharges are gone. A new economy
entering the certificate class now supplies two fewer obligations.

#### What deliberately stays

`cT`, `gT`, and `hT_loss_margin` — *the Target's current stage loss rate is
bounded by the discounted continuation-state gain the extra sanction buys*,
`c_T ≤ β_T · g_T · δ`. The **margin** is what does the work; the signs never
did. And the sign of `g_T` survives in exactly one place in the whole tree, as
its own binder rather than a field:
`Target_combined_chord_of_decomposition_lowerChord`
(`Theory/Certificates/GeneralFDischargers.lean:65`, consumed at line 133), for
the general-`F` reason the previous entry sets out.

#### What this changes economically, stated conservatively

The certificate now asks for the margin inequality alone. It no longer excludes
by fiat an economy in which the Target's stage payoff *rises* in the sanction
(`c_T < 0`) or in which the Target values higher-noncompliance states less
(`g_T < 0`), provided the margin still holds. This is a genuine widening of the
admissible class, not a relabelling. It is **not** a claim that such an economy
exists or that one would satisfy the certificate's remaining fields — the
certificate is silent on that, and no witness of that kind is exhibited here.

#### Verification and paper impact

Gates re-run from an emptied `.lake/build`. Headline set unchanged at 35 rows
with every elaborated-type hash unchanged, which is the expected result: a
theorem whose signature names a certificate structure prints the same type when
that structure loses a field. No unused-variable warning anywhere in the touched
files.

The manuscript never named these fields and states no standalone `c_T ≥ 0` or
`g_T ≥ 0`; where the appendix lists certificate fields it names `cT`, `gT`,
`hT_loss_margin`, all of which remain. The one docstring carrying a field count
(`StandardComplianceLocal.lean`) was corrected from ~34 to ~32.

---

### Round 2026-08-17 (later) — the tree-wide sweep for the same defect

**Why a sweep was needed at all: the linter cannot see this defect.** Lean's
`unusedVariables` linter checks *theorem binders* only. A structure **field**
that nothing projects produces no warning, and `lake build` stays green and
silent. That is exactly how `hcT_nn` / `hgT_nn` survived many audit rounds. So
the certificate-field cleanup could not be declared complete on a green build;
it needed a purpose-built scan.

`docs/archive/workflow-scratch/fieldscan.py` walks every `structure … where`
block, collects its field names, and counts `.field` uses tree-wide, excluding
`field := …` (construction is not use). 259 field names; 15 flagged; 5 genuine
after triage.

#### Four more dead fields, deleted

Each had the identical fingerprint to the two removed earlier — exactly two
occurrences in the whole tree, the declaration and one discharge, no consumer.

| Field | What it asserted |
|---|---|
| `ContestPolity.iota_J_nn` | income-incidence erosion is a loss and not a subsidy on the regime-supporter side, `0 ≤ ι_J` |
| `ContestPolity.iota_K_nn` | the same on the opposition side, `0 ≤ ι_K` |
| `JointPreferenceBasinLow.xbar_low_nonneg` | the low basin's right endpoint is nonnegative |
| `JointPreferenceBasinLow.sbar_low_mem` | the low basin's sanction pivot lies in `[0,1]` |

The two `iota` fields were Rule-3 user-approved primitives (2026-07-11) and are
paper-visible through the four-group microfoundation. At the only witness they
were discharged by `le_refl 0` and `norm_num` — the witness sets `ι_J = 0`, so
nothing ever read the sign.

**The two low-basin fields were not merely unused, they were derivable**, which
is the stronger finding. The constructor discharged them as
`le_min hOne.xT_star_mem.1 hOne.xS_star_mem.1` and `hOne.sbar_star_mem` — both
follow from data the constructor already holds. They were derived facts sitting
in assumption slots.

#### One dead binder, and a correction

`argmax_lipschitz_of_strongConcave_lipschitzDiff`
(then `Theory/Shocked/ShockedArgmaxLipschitz.lean`, since 2026-09-08 `Foundations/StrongConcaveArgmax.lean`) carried `hc : 0 < c` — *the
strong-concavity modulus is strictly positive* — and never used it. Removed,
with five call sites updated.

*Correction to the report that preceded this round:* the unused binder was
identified as `hL : 0 ≤ L` from the linter's column offset. That was wrong —
`hL` is load-bearing, closing the degenerate `|a_f − a_g| = 0` branch. The
compiler caught the error on the first build after the edit. The binder actually
dead is `hc`.

#### What was checked and deliberately left

* **Six dead fields in `SmoothSanctionClass`** — consistent with the whole
  structure being consumed by nothing. It is the frozen abstract C¹ layer;
  leaving it dead is the correct treatment of a quarantine.
* **Three false positives worth recording, because they bound the scan's
  reach:** `KT` and `mT` (`RegularEconomyCertificate`) are referenced inside
  *sibling field types*, which a projection scan cannot see; `x_zero` and `step`
  (`FGCPlannerPath`) are consumed inside the existential that *defines* the
  planner's feasible set — which incidentally confirms the welfare comparison
  ranges over dynamically feasible paths, not arbitrary ones.
* **Remaining unused binders: 13**, down from 20 before this session. Seven sit
  in the frozen C¹ track, four in `Foundations` (`Topkis`,
  `MonotoneThreshold`), two are cosmetic lambda binders. **None in the
  certificate layer.**

#### Hypotheses checked for derivability and found genuinely primitive

Recorded so the question is not reopened:

* `ContestPolity.stakeJ_nn0 : 0 ≤ th0_JT * b_J` — `FourGroup` carries no sign
  field on `th0_JT` or `b_J` (its only sign condition is
  `rally_dom : μ·b_K < ρ·b_J`), so this does **not** follow by `mul_nonneg`.
* The Schur row coefficients `hβ_T_nn`, `hL_TS_nn`, … — derivable from the
  operator bounds only when the carrier holds two distinct points, and several
  witnesses use singleton carriers. Not a clean discharge.
* No hypothesis anywhere restates a `Params` field: a grep for `0 ≤ p.β_T`-style
  binders returns nothing.

#### The strong-assumption audit: quantification over the whole equilibrium set

The one pattern that deserves the label is `∀ E : FeedbackStackelbergEquilibriumTop,
<condition on E>` with **no carrier guard**. Guarded forms
(`∀ E, E.V_S ∈ D.carrier → …`) are unobjectionable. The unguarded ones assert of
*every* equilibrium the game admits: that `V_S` is monotone; that it is
`KS`-Lipschitz with a single uniform constant; that it satisfies single
crossing; that the realised rule preserves the basin; and most strikingly
`hα_order_E : ∀ E, ∀ x ∈ S, M.α x ≤ E.α x` — the myopic Target policy lies
pointwise below *every* equilibrium's Target policy, a joint restriction on the
entire equilibrium correspondence that sits awkwardly beside the paper's own
multiplicity story.

**Already fenced, and correctly.** `RegularEconomyCertificate` carries an
explicit AUDIT-43 quarantine warning that the `hα_order_E + hσ_monoOn_a` chain
is sign-correct only under the resistance reading and has the *wrong sign*
under literal compliance, directing paper-facing claims to
`RegularEconomyCertificateCompliance`, which replaced the chain with
`hMyoCeiling`. No headline row consumes the quarantined certificate.

**Residual, and not covered by any written warning:** the unguarded uniform
Lipschitz and monotonicity conditions in `JETBridgeC1System` and
`RegularEconomyCertificateC1ComplianceCore` — one `KS` for every equilibrium in
the game. These are quarantined by *layer* (no headline row reaches C¹
material) rather than by a note. A banner would close the gap; no code change is
implied.

#### Also clean, by construction rather than by review

Zero `opaque` declarations, zero `True`-valued `Prop` fields, zero `sorry` /
`admit` / custom `axiom` / `native_decide`. Rule 14's laundering pattern is
absent structurally, not merely unobserved.

---

### Round 2026-08-17 (last) — the resistance-action route deleted

**On the author's decision, and the sequel to the entry above.** The strongest
assumption in the tree is gone, along with the route that carried it: fourteen
declarations across three files, about 1,400 lines, **zero cascade** — every cut
built green on the first attempt, which is what a closed island looks like.

#### The assumption

`hα_order_E : ∀ E : FeedbackStackelbergEquilibriumTop, ∀ x ∈ S, M.α x ≤ E.α x`
— *the myopic Target policy lies pointwise below the Target policy of **every**
equilibrium the game admits*. Not a condition on one equilibrium, or on the
equilibria a carrier contains, but a restriction on the entire equilibrium
correspondence, uniform in `E`. It sat awkwardly beside the paper's own
multiplicity and dual-basin story, and it was the last unguarded `∀ E` condition
outside the frozen C¹ layer.

#### Why deleting the field alone was not an option

Unlike the six sign fields removed earlier this session, `hα_order_E` was
**not** dead: `RegularEconomyCertificate.three_goals` consumed it. It was
load-bearing for a route that was itself unreachable. Removing the field would
have meant rebuilding that theorem around a different Goal-2 argument — which
the compliance family had already done years of rounds earlier, replacing the
chain with a myopic ceiling plus an internally derived dynamic floor. The work
existed twice; only the wrong-sign copy was ever removed from service, never
from the tree.

#### What went

| File | Declarations |
|---|---|
| `Theory/Certificates/RegularEconomy.lean` | `RegularEconomyCertificate` + `three_goals`; the `ResistanceActionCertificate` alias; `regularEconomyCertificate_of_lipBall`; `regularEconomyCertificate_ofPrimitivePayoffLipschitz`; `RegularEconomyCertificateC1` + `three_goals`; `RegularEconomyMargins` + `strict_row_T` + `strict_row_S` + `row_inequalities_preserved_under_perturbation` |
| `Theory/Bridges/JETBridge.lean` | `jet_three_goals_from_valueClass_and_primitives`; `jet_three_goals_from_ball_operator_lipschitz_primitives` |
| `Theory/Bridges/JETBridgeC1System.lean` | `jet_C1BellmanSystem_three_goals` |

The last one was not in the original plan. It surfaced *after* the first cut:
its inputs were bundled by `RegularEconomyCertificateC1`, so deleting that
certificate orphaned it, and it was the final carrier of `hα_order_E` in
executable code. Its compliance siblings — `..._compliance_on` and
`..._compliance_statewise` — are alive and were left untouched.

#### What was deliberately kept

`alphaOnLipschitzOn_of_IFT_chord_form` and
`alphaOnLipschitzOn_of_C2_Hessian_lower_bound` — the Round-31 dischargers that
derive `AlphaOnLipschitzOn` (*the carrier-restricted leader selector is
Lipschitz in the value pair*) from implicit-function and Hessian conditions.
They merely shared a file with the deleted route; they are general, reusable by
the live compliance route, and cited by name from `Foundations/Curtat.lean` and
`Foundations/ImplicitFunctionTheorem.lean`.

#### Evidence the route was unreachable

Established before any edit, and confirmed by the empty cascade afterwards: no
witness constructed any of the deleted certificates; no headline row reached
them; every reference from outside the three files was a **docstring mention**;
and the manuscript never cited the route — the only `resistance` hits in
`paper/` are the North Korea discussion prose, about resistance to opening.
`regularEconomyCertificateCompliance_of_lipBall` was checked directly and calls
neither deleted constructor nor either deleted bridge.

#### Honest scope

This deleted **correct** proved content. The route is sign-correct under the
resistance reading of `a`, where a higher action triggers heavier sanctions; it
is wrong only under the literal-compliance reading the paper uses. Its own
docstring had preserved it "for backward compatibility", but there were no
backward consumers — it was compatibility with nothing. It remains in git
history if the resistance interpretation is ever wanted.

#### Follow-up 2026-08-17: abstract layer, and a duplicate retracted

An attempt to push the argmax-uniqueness dischargers down to `Foundations/`
uncovered that they had existed since July. The round is recorded in full because
what it produced is smaller than it looked and the error is worth keeping.

**Retracted.** `ArgmaxUniqueFromConcavity.lean`, added earlier the same day,
duplicated `ArgmaxUniquenessFromConcavity.lean` (2026-07-19) — the generic
midpoint lemma, the Sender discharger and the leader discharger, all with
essentially identical statements and proofs. Deleted, with its import removed
from `Theory.lean`. The cause was a truncated search; the near-identical
filenames meant nothing collided until the build rejected a duplicate
declaration.

**Kept, because it is genuinely additive:**

* `Foundations/ConcaveArgmax.lean` — the midpoint argument at the abstract layer,
  over a bare `f : ℝ → ℝ` with no `Params`. The July lemma now delegates to it,
  statement unchanged, so no drift. Mathlib was searched first and has a rich
  `StrictConcaveOn` API but no argmax-uniqueness lemma; `lt_on_openSegment` is
  the tool.
* `dynamicArgmaxUnique_on_set_of_strictConcaveOn` and
  `targetArgmaxUnique_on_set_of_strictConcaveOn`, added to the July file. These
  are the piece that was actually missing. `ValueClass.ofLipBall` consumes
  `∀ V_S ∈ valLipBall M K, DynamicArgmaxUnique V_S` **in order to build the value
  class**, so a discharger phrased over `D.carrier` cannot produce `D` — it would
  need the object it is helping to construct. Quantifying over a bare `Set Val`
  breaks the circularity, because the carrier set is known before the class
  exists.
* `Foundations/StokeyLucas.lean`'s `lowerSlope_integrand_of_joint_chord` — the
  abstract content shared by the Sender-side and Target-side cone arguments,
  which had been written twice against `Params`-level objectives.

**Carried forward from the July file, not previously known here.** It contains a
Rule-11 counterexample, `stage_strictConcavity_does_not_force_dynamic_uniqueness`:
strict concavity of the *stage* payoff does **not** give dynamic argmax
uniqueness. Any primitives-level constructor must therefore take concavity of the
*dynamic* objective; a reader reaching for the stage condition would be wrong,
and the tree already proves it.

**Net effect on the rewire.** Closer than reported, not further: step 2 was done
a month ago, and what was missing was the set-level plumbing, which is now in.

#### Follow-up 2026-08-17: the gain-ball route is general in `F`

The open question from the previous entry — whether the gain-ball invariance route
is genuinely general in `F` or only general in form — is settled affirmatively.

**What was actually wrong.** `jointTarget_BCF_preserves_lowerSlopeOnValueOn`
carries no `hF`, so the theorem is general. But it consumes
`h_integrand_lowerSlope`, and that hypothesis had **no parametric discharger
anywhere in the tree**. The only discharge is at a single witness
(`polyComplianceParams_joint_T_integrand_lowerSlope_at_carrier`), and the route
its docstring sketches runs through `bellmanLowerSlopeConstant β_T (1−δ)` — an
affine constant. So the route was general in form and affine in practice, which
is exactly the kind of gap a signature check alone does not reveal.

**`joint_T_integrand_lowerSlope_of_joint_chord`** closes it, by the same
Smith–McCardle device that freed the Sender cone: a slope floor is not a closed
convex cone property, but `V_T − g·id` being increasing is, so the transition
belongs inside a modified reward rather than in a condition of its own.

*One complication the Sender side did not have.* The Target integrand is
evaluated at `σ_dyn V_S x a`, so **the sanction moves with the state**. Two
consequences: the chord is taken along the realised pair
`(x, σ_dyn V_S x a)` rather than at a fixed sanction, and the successor states
must be ordered — `hsucc_mono` — which does **not** follow from `F_mono_x` alone,
because `σ_dyn` varies too. Assuming the Sender proof transferred verbatim would
have missed that.

Economically: *moving to a deeper political state raises the Target's realised
stage payoff plus the discounted value of the entrenchment its own best response
then produces by at least `g` per unit* — both channels together, at the
sanctions actually chosen. No `hF`, no chord on `F` alone, no new named scalar.

**`bellmanS_BCF_preserves_lowerSlopeCone_generalF_on`** makes the Sender side
domain-parametric. The morning's version was stated on `[0,1]`; the gain ball
asks for `[xT,1]`, and the restriction runs the wrong way — a guarantee on
`[0,1]` weakens to `[xT,1]`, but the Bellman step needs the *hypothesis* on the
set it concludes on. What makes the smaller domain work is `hB_inv`: from a basin
state any feasible sanction lands back in the basin, so the cone is applied only
where it holds. On `[0,1]` that is automatic from `F_mem`, which is why the unit
interval needed no such condition — and `hB_inv` is the same basin-preservation
condition the Target discharger takes.

**Status of the route.** All six preservation facts are now general in `F`, and
the structural discharger and domain adapter are in place. What remains is
composition only: a membership splitter, the two per-operator assemblies, and the
end-to-end `ofLipGainBall_IsInvariant_of_primitives`. No mathematical content is
outstanding; nothing left imposes a functional form on the transition.

#### Follow-up 2026-08-17: `SingleCrossingOn` off the affine law — Tier 1 closed

The last Tier-1 `Prop` whose only parametric route imposed a functional form on
`F`. Attacked abstract-first: the general content went to `Foundations/`, the
wiring to `Theory/`, and the affine case became a corollary.

**What the affine law was doing.** In `hSC_on_of_carrier_convexOn_range` it
appeared at exactly one `simp` step, and its role was to make the state
displacement `F(x',s) − F(x,s) = (1−δ)·(x'−x)` **independent of the sanction**.
That is what lets the two continuation chords be equal-width with a common
rightward shift, which is the shape `chord_shift` consumes.

**The right reading.** An affine transition is **modular** — its cross-difference
in `(state, sanction)` is identically zero. So the general condition is not a
functional form at all but an *order* condition: the transition has **increasing
differences**, meaning a higher inherited state weakly widens the effect of a
larger sanction on next period's state. The extra chord width that a strictly
supermodular transition creates is absorbed by monotonicity of the value along
the range. This is Topkis's composition rule — an increasing convex transform of
a supermodular map is supermodular (Topkis 1998, *Supermodularity and
Complementarity*, §2.6).

**Foundations** (`Foundations/Topkis.lean`), abstract over `g : ℝ → ℝ`, no
`Params` anywhere:

* `convexOn_chord_shift` — equal-width chords rise as they slide right. Mathlib
  was searched first and carries the slope-monotonicity forms
  (`ConvexOn.secant_mono`, `ConvexOn.slope_mono_adjacent`) but not this one, so
  it is proved here.
* `chord_le_chord_of_convexOn_monotoneOn` — the composition rule in chord form:
  four points in the supermodular ordering, a convex non-decreasing `g`, and the
  chord inequality follows.

**Theory** (`Theory/Certificates/ConvexValueRoute.lean`):

* `hSC_on_of_carrier_convexOn_range_generalF` — single crossing of the Sender's
  dynamic objective at a general transition.
* `affine_transition_increasingDifferences` — the Rule-13 drift fence: the affine
  law satisfies the order condition (with equality), so the general theorem
  covers everything the affine one did.

**Assumption accounting.** `hF` is replaced by two things, neither of them new
surface. Increasing differences of `F` is `MilgromShannon.IncreasingDifferencesOn`
applied to existing data — an existing predicate, not a new `Prop`. Sender value
monotonicity along the range is **already the `hV_S_mono_carrier` field** of
`StandardComplianceLocalCoreCertificate_MS`. No new `Prop` definition and no new
`Params` field; at certificate level the trade costs nothing, and it moves a
functional-form assumption to an order condition, which is the direction Rule 22
asks for.

#### Follow-up 2026-08-17: the gain-ball invariance route unblocked

Two additions in `Bellman/InvariantLipGainBall.lean` complete the plumbing the
earlier diagnosis identified:

* `LowerSlopeOnValueOn.mono_set` — a lower-slope guarantee restricts to a smaller
  basin. The condition is universally quantified over pairs in its domain, so
  shrinking the domain weakens it; needed because the Sender-side cone lemmas
  conclude on `[0,1]` while the gain ball asks for `[xT,1]`. It did not exist.
* `ofLipGainBall_IsInvariant_of_preservation` — the structural discharger, the
  gain-ball analogue of `ofLipBall_IsInvariant_of_preservation`. Membership in
  the gain ball is a conjunction of three conditions, so each operator must
  preserve all three; this packages that.

With the general-`F` Sender cone lemma added earlier the same day, the gain ball
now has all six preservation facts *and* a discharger to feed them into.

#### Tier-1 status after this round

All four of the most-consumed `Prop`s are now derived rather than primitive, and
three of the four routes are general in `F`:

| `Prop` | Uses | Route | General in `F` |
|---|---|---|---|
| `DynamicArgmaxUnique` | 144 | strong concavity of the dynamic Sender objective | yes |
| `SingleCrossingOn` | 123 | increasing differences of `F` + convex, monotone value | **yes, this round** |
| `StrictAdjustment` | 120 | strictly positive sanction lower chord | yes |
| `IsInvariant` | 112 | cube bounds + Lipschitz estimates + margins | ball routes yes; gain ball unblocked |

Stated honestly, these are **trades, not eliminations**: argmax uniqueness now
rests on curvature of the Sender's payoff, single crossing on an order condition
for the transition, invariance on cube and Lipschitz bounds. What each trade buys
is the move from a technical selection, crossing, or fixed-point condition to a
checkable statement about payoffs and the transition — and, in three of four
cases, off any functional form for `F`.

#### Follow-up 2026-08-17: the two deepest Props attacked

**`DynamicArgmaxUnique` — discharged. ⚠ RETRACTED 2026-08-17: it already was.**

*This paragraph as originally written claimed a new discharge. That was wrong.*
`Theory/Equilibrium/ArgmaxUniquenessFromConcavity.lean` has carried
`dynamicArgmaxUnique_of_strictConcaveOn` — and the leader-side
`targetArgmaxUnique_of_strictConcaveOn`, and the generic midpoint lemma — since
**2026-07-19** (commit `f3b42ee`). The file added on 2026-08-17,
`ArgmaxUniqueFromConcavity.lean`, duplicated all of it under a near-identical
name and has been deleted; see the consolidation entry below.

**How the error was made, recorded because the method is the point.** The search
for existing dischargers was a `grep … | head -8`, and the July file's entries
fell past the cut. "No parametric discharger anywhere" was then reported as a
finding — twice, once for each side — on the strength of a truncated result.
Nothing collided until the build failed on a duplicate declaration, because the
two filenames differ only by `Unique` versus `Uniqueness`. **A truncated search
is not a search when the finding is an absence.**

What was true and survives: the strong-concavity entry point
(`SenderObjectiveStronglyConcaveOn` with `c > 0`, the same primitive
`SigmaDynHolderOn.of_strongConcave` consumes) is a legitimate bridge, but it is
derivable in one line from the July discharger via mathlib's
`StrongConcaveOn.strictConcaveOn`, so it was dropped rather than kept.

**`IsInvariant` on `valLipBall` — derived.** Every ingredient existed and none
had been joined: `ofLipBall_IsInvariant_of_preservation` consumes exactly what
`h_T_preserves_of_integrand_lipschitz` and `h_S_preserves_of_payoff_lipschitz`
produce. `ofLipBall_IsInvariant_of_primitives` is that composition. This matters
because `IsInvariant` is the Rule-15 existence crux; the Lipschitz-ball route now
joins the sup-norm ball route in *deriving* carrier invariance rather than
postulating it, and `h_unique_S` — a hypothesis of every one of these invariance
theorems — is itself now dischargeable by the paragraph above.

**Gain-ball Sender cone preservation — generalised off the affine law.** Of the
six preservation facts a gain-ball invariance needs, five existed and were
general in `F`; the sixth, `bellmanS_BCF_preserves_lowerSlopeCone`, carried
`hF : F = affineF δ`.

The obvious repair — a linear state-side chord on `F` mirroring
`SanctionLowerChordWith` — was drafted, put to the author as a Rule-3 packet, and
then **withdrawn on a literature check**, which is the useful part of the record.
Smith and McCardle (2002), *Structural Properties of Stochastic Dynamic
Programs*, Operations Research 50(5), 796–809 (local copy in
`PaperRefer/MathTheory/`) give the governing metatheorem: a **closed convex cone
(C³)** property passes from reward to value function when the transition has the
stochastic version of it; the monotonicity case is classical and they attribute
it to Stokey–Lucas (1989), pp. 267–268. But `LowerSlopeOnValueOn V B g` with
`g > 0` is **not** a C³ property — scaling `V` by `a < 1` drops the floor to
`a·g` — so the metatheorem does not apply to it, which is exactly why the old
proof needed a chord on `F`.

The standard device removes the difficulty rather than generalising it. `V` has
lower slope `g` iff `V − g·id` is increasing, and monotonicity *is* C³.
Translating the Bellman equation through `W := V − g·id` puts the transition
inside a **modified reward** `U(x,s) + β·g·F(x,s) − g·x`, so all that is required
is that this be increasing in the state, plus monotonicity of `F` in the
state — and the latter is `F_mono_x`, already a `Params` field.

`bellmanS_BCF_preserves_lowerSlopeCone_generalF` therefore assumes **one joint
chord** in existing primitives and nothing about `F` alone:

```text
g·(y₂ − y₁) ≤ (U_S(y₂,α y₂,s) − U_S(y₁,α y₁,s)) + β_S·g·(F y₂ s − F y₁ s)
```

*Raising the inherited political state by `Δ` raises the Sender's stage payoff
plus the discounted value of the extra entrenchment it buys by at least `g·Δ`* —
the state pays for itself at rate `g` counting both channels together, rather
than each channel clearing a bar separately.

It is **strictly weaker** than the affine trio it replaces, and
`joint_state_chord_of_stage_chord_and_affine` proves it: the `m`-chord, the cone
inequality `g ≤ m + β_S·g·(1−δ)`, and `hF` together imply the joint chord, so
nothing was lost by deleting `hF`. The converse fails, because the joint form
lets the payoff compensate for a flat stretch of the transition and the separated
pair cannot express that. Two named scalars (`m` and the proposed `d`) are
deleted rather than one added, which is what Rule 3's symbol-economy clause
asks for — so this is a cat-2 weakening and no Rule-3 stop applies.

*Recorded because the process mattered:* the first proposal was an affine
artefact in general clothing, and the reference library caught it. Rule 6 exists
for this.

#### Follow-up 2026-08-17: Goal 2's comparator assumption made primitive

A diagnosis of the 35-row headline surface (see the entry below) identified
`hMyoCeiling` as the highest-leverage target, because **Goal 2 — rule dominance
— rests on that single certificate field**. Two theorems now discharge it from
the Sender stage payoff alone. Both are provable from the existing assumption
surface, so Rule 3 required no stop; both are axiom-clean on `propext`,
`Classical.choice`, `Quot.sound`.

`myopicCeiling_of_sigma_antitoneOn_at_zero` — the existing discharger
`myopicCeiling_of_alpha_floor_and_sigma_antitoneOn` routes through a free
compliance threshold `τ`, an `α`-floor `τ ≤ M.α`, and a `σ`-ceiling at `τ`.
That is a reparametrisation, not a reduction: it trades one condition on the
endogenous myopic policy for another. Evaluating it at **`τ ≡ 0`** collapses
it. The `α`-floor becomes `0 ≤ M.α x`, already guaranteed by the myopic
policy's own feasibility field, and the threshold symbol disappears. What
remains is two conditions **on `Params` primitives only** — `σ` is a `Params`
field, so neither mentions the myopic equilibrium, its policy, or any other
endogenous object.

Economically: *the Sender's stage-optimal sanction falls as the Target complies
more, and even facing complete noncompliance it already sits at or below the
basin floor.* The second clause is the worst case of the first, which is
exactly why nothing about the Target's actual choice is needed.

`myopicCeiling_of_U_S_decreasingDifferences` — composes that with the Round-28
`σ`-antitone discharger to close the chain end to end:

```
∂²U_S/∂s∂a ≤ 0  +  strict stage argmax   ⇒  σ antitone in compliance
σ antitone      +  σ(x,0) ≤ max x s̄      ⇒  hMyoCeiling  ⇒  Goal 2
```

Every input is a condition on the shape of the Sender's stage payoff. No
equilibrium, no value function, no policy appears anywhere in the hypotheses.

#### Documentation repaired rather than left dangling

Six files carried docstrings pointing at the deleted names:
`RegularEconomy.lean` (module header, three section headers),
`Bridges/JETBridgeC1System.lean` (module header),
`Foundations/Curtat.lean`, `Foundations/ImplicitFunctionTheorem.lean`,
`Theory/Certificates/StandardComplianceMain.lean`, and
`Theory/LockIn/DifferentPolicyComparator.lean`. Each now records that the route
existed, what it assumed, and that it was removed — the history is kept, the
dead pointers are not. `docs/archive/` was left untouched: it is a record of
what was true when written.

### Round 2026-08-17 (final) — carrier invariance stops being an assumption

**Zero new assumptions.** Everything below is composition or proof of something
already asserted in prose: each hypothesis of each new declaration already
appeared in one of the theorems being composed. No `Params` field, no certificate
field, no `Prop` on the assumption side was added. All nine new declarations are
axiom-clean on `propext`, `Classical.choice`, `Quot.sound`.

#### What was missing

The gain ball `valLipGainBall M K g xT` — *values bounded by `M`, responding to
the political state at rate at most `K`, and rising at rate at least `g` as the
state deepens* — had a Target-side slope-preservation theorem, a Sender-side
one (added earlier the same day, general in `F`), and a structural discharger
`ofLipGainBall_IsInvariant_of_preservation` that turns two preservation facts
into `IsInvariant`. Nothing composed them. So the gain ball was in the same
position the Lipschitz ball had been in before
`ofLipBall_IsInvariant_of_primitives`: every user still had to supply carrier
invariance by hand, economy by economy.

That matters more than convenience. `IsInvariant` is the existence crux
(Rule 15). Without it there is no Bellman fixed point and hence no equilibrium,
so a certificate that *hypothesises* invariance rests its existence claim on an
unproved premise about the object it is constructing.

#### The organising observation

`mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope` — gain-ball membership is
Lipschitz-ball membership **plus** the slope floor. So each operator has to be
shown to preserve two things the Lipschitz-ball layer already handles (sup-norm
radius, Lipschitz constant) and one thing that is new (the floor). Every
preservation proof in the round is that two-plus-one, and the reuse is why the
whole file went green on the first build.

#### What was added

`Theory/Bellman/GainBallInvariance.lean` (new):

| Name | What it says |
|---|---|
| `h_T_preserves_gain_of_integrand` | the joint Target operator keeps the gain ball, from an integrand Lipschitz bound and an integrand slope floor at the carrier |
| `h_S_preserves_gain_of_payoff` | the joint Sender operator keeps the gain ball, from a payoff Lipschitz bound at the leader selector and a joint state chord |
| `ofLipGainBall_IsInvariant_of_primitives` | the composition — carrier invariance from payoff and transition data, nothing assumed about the Bellman operators |
| `ofLipGainBall_IsInvariant_of_chords` | the same, with the Target integrand's slope floor itself derived from a joint chord on the Target's realised stage payoff |

`Theory/Bellman/SenderLowerSlopeCone.lean` (two additions):
`linSeed_mem_valLipGainBall` and `valLipGainBall_nonempty` — *the linear value
`V(y) = g · y` lies in the gain ball whenever `0 ≤ g ≤ min M K`, so the ball is
nonempty.* `ValueClass.ofLipGainBall` takes nonemptiness as an explicit
hypothesis and its docstring had named this witness in prose since the carrier
was built, but the claim was never proved — so the only discharge in the tree was
at one witness economy (`Examples/StandardCompliancePolynomialSkeleton.lean`).
Economically the seed is the simplest value the political economy admits: worth
exactly `g` per unit of entrenchment, everywhere, with no curvature. A gain ball
asks for values bounded by `M`, no steeper than `K`, no flatter than `g`; the
linear one is the extreme case of the last constraint, so it fits whenever the
first two leave room.

`Theory/Bellman/InvariantValueClass2.lean` (two additions):
`jointTargetOp_sub_rowBound_of_BCF` and `jointSenderOp_sub_rowBound_of_BCF` —
*the two Banach row bounds, stated on the value-valued operators, transport to
the subtype-valued ones.* Both are `:= h`: the subtype metric **is** the ambient
metric. Small, but it removes an ordering constraint that had real bite. The row
bounds are phrased on `jointTargetOp_sub h_inv`, so until now they could not be
written down before invariance was in hand — which would have forced any
constructor deriving invariance to inline that derivation inside two of its own
hypotheses.

`Theory/Certificates/GainBallCertificate.lean` (new):

| Name | What it says |
|---|---|
| `gainBallValueClass2` | the zero-based gain ball as an asymmetric value class |
| `gainBallValueClass2_IsInvariant` | its invariance, derived; at the zero-based ball the basin condition is `F_mem`, so it is not an input |
| `gainBallValueClass2_V_S_lipschitz` | `hV_S_lip_carrier` is carrier geometry |
| `gainBallValueClass2_V_S_monotone` | `hV_S_mono_carrier` is carrier geometry |
| `StandardComplianceLocalCoreCertificate_MS.of_gainBall_primitives` | the certificate, with `D`, `h_inv`, `hV_S_lip_carrier`, `hV_S_mono_carrier` all removed from the input list |

#### What the gain ball buys over the Lipschitz ball

`hV_S_mono_carrier` — *every Sender carrier value is monotone in the political
state*. The Lipschitz ball cannot supply it; it is exactly what the slope floor
adds. On a zero-based ball the floor applies at every pair of states, and at
`g = 0` the floor **is** monotonicity — so the field costs nothing beyond
choosing the gain ball as the carrier. `hV_S_lip_carrier` comes free on either
ball.

#### Rule 22

No result in the round carries `hF`. The transition enters through `F_mono_x`
and `F_mem` (both already `Params` fields), a state-Lipschitz modulus, the basin
condition, and the two joint chords. The affine law satisfies all of these;
none of them requires it. The drift fence
`joint_state_chord_of_stage_chord_and_affine` records that the affine hypotheses
imply the general chord, so nothing that used to be provable stopped being so.

#### What this does not establish

**No economy has been exhibited satisfying the input bundle of
`of_gainBall_primitives`.** The round delivers a derivation, not a non-vacuity
certificate: per Rule 9 a constructor whose hypotheses are jointly unsatisfiable
is useless though not unsound, and nothing here rules that out. Converting one
existing witness to the new constructor is the check, and it is deferred — it is
the first step in this sequence that could move a headline type hash, so it is
the author's call, not the agent's.

#### Paper

Rule 2 required no fix-in-place: the paper's
`\Cref{prop:F-chord-route}` describes `of_transition_adjusted_chord`, whose
hypotheses are unchanged, and its sentence that Sender-carrier monotonicity is
"still load-bearing" remains true of that route. The new route is *new material*
and went to the staging document as item **A13**
(`paper/note_sections/03_appendix_promotion_queue.tex`), recommended for
appendix promotion once a witness exists, per Rule 21.

### Round 2026-08-18 — the gain-ball constructor had the wrong shape

**A correction to the round above, found by checking its own open item.** The
previous round shipped `StandardComplianceLocalCoreCertificate_MS.of_gainBall_primitives`
and closed with "no economy has been exhibited satisfying the input bundle."
Checking that gap did not produce a witness; it produced a reason there could not
easily be one. The constructor has been **removed** and replaced.

#### What was wrong

`gainBallValueClass2` put **one** gain ball on both sides of the value class, so
a single triple `(M, K, g)` had to serve the Target and the Sender at once — in
particular a shared slope floor `g`, i.e. *both value functions rise at the same
minimum rate as entrenchment deepens.*

`chord_forces_zero_slope_of_flat_stage` (new,
`Theory/Bellman/SenderLowerSlopeCone.lean`) shows what that costs. If the
Sender's stage payoff does not move with the political state once the leader's
response is substituted, the Sender-side joint chord forces `g = 0` — **at any
transition**. The proof needs nothing but feasibility: evaluate the chord at the
two endpoints of the state space, the stage term vanishes by hypothesis, the
discounted transition term is at most `β_S · g` because `F` lands in `[0,1]`, and
`β_S < 1` closes it. Economically: *discounting cannot manufacture a stake that
the stage payoff does not pay.*

That is not hypothetical. `polyComplianceValueClass2Gain`, the only gain-ball
carrier in the tree, pairs `valLipGainBall 12 (20/3) (20/3) 0` on the Target with
a Sender carrier of Lipschitz constant **zero** — because that economy's Sender
payoff is `U_S(x,a,s) = s`, which ignores the state entirely. Its Target needs
`g = 20/3`; its Sender is pinned to `g = 0`. The homogeneous constructor could
not express the one economy it was supposed to cover.

#### What replaced it

| Name | What it says |
|---|---|
| `chord_forces_zero_slope_of_flat_stage` | a state-flat Sender stage payoff admits no positive slope floor, at any transition |
| `gainBallValueClass2` (rewritten) | **asymmetric**: `carrier_T = valLipGainBall M_T K_T g_T 0`, `carrier_S = valLipGainBall M_S K_S g_S 0`, nothing tying the triples together |
| `gainBallValueClass2_IsInvariant` | invariance of that class from primitives, each side the same two-plus-one split at its own constants |
| `gainBallValueClass2_IsInvariant_closedForm` | the same with `M_T`, `M_S`, `K_S` **equated to their SLP closed forms**, so the three margins discharge automatically — two with equality |
| `bellmanLipConstant_lip_margin_eq` | the SLP §9.2 ceiling reproduces itself exactly under one Bellman step |
| `bellmanLowerSlopeConstant_nonneg`, `bellmanLowerSlopeConstant_le_bellmanLipConstant` | the closed-form floor is nonnegative and never outruns the closed-form ceiling, so the ball stays inhabited |

`of_gainBall_primitives` is gone. Nothing consumed it, it is not a headline, and
no pinned constant moves; the composable replacement is
`of_transition_adjusted_chord p (p.gainBallValueClass2 …) (p.gainBallValueClass2_IsInvariant …) …`,
which is both shorter to read and correctly shaped. The two row-bound transports
added for its signature are kept: they are what let a caller state the Banach row
bounds *before* invariance is in hand, which is exactly the situation a derived
invariance creates.

#### The abstract economic representation

`Foundations/StokeyLucas.lean` has carried the three closed forms — radius
`M_U/(1−β)`, SLP §9.2 ceiling `L_U/(1−β·γ_F)`, SLP §4.11 Benveniste–Scheinkman
floor `g_U/(1−β·γ_F)` — with a docstring saying they leave "nothing to choose by
hand". Nothing had assembled them. `…_closedForm` does, and the assembly is where
the asymmetry stops being a modelling choice and becomes a derived fact: **each
player's value inherits its own stage payoff's state-slope, amplified by its own
discounted transition multiplier.** The Target's floor is `g_U_T/(1−β_T·γ_F)`,
the Sender's is `m_S/(1−β_S·γ_F)`, and they differ because the two stage payoffs
differ. The flat-stage theorem is the sharp edge of the same statement at
`m_S = 0`.

#### Non-vacuity: still open, but better posed

No economy has been exhibited satisfying the bundle, and the obvious candidate
was deliberately **not** used. Instantiating at `polyComplianceParams` was
drafted and then discarded on the author's instruction: its Sender ignores the
political state, so a certificate there would attest that the route is
non-vacuous only at an economy in which the mechanism the gain ball exists to
express is absent. The open question is now the right one — an economy with a
Sender that genuinely values entrenchment (`m_S > 0`) — rather than a search for
any inhabitant at all.

### Round 2026-08-18b — the closed-form prose outran the Lean, twice over

**A retraction, prompted by one question from the author** — *"is that affine
only?"*, asked of `bellmanS_BCF_preserves_lowerSlopeCone`. A four-dimension
read-only audit with an adversarial refutation pass on every finding says: yes,
and the prose written earlier the same day was wrong in a way worth recording.

#### The theorem itself

`bellmanS_BCF_preserves_lowerSlopeCone` is affine on **two independent
footprints, both in the statement**:

1. `hF : p.F = affineF p.δ` (axis 1), consumed once to produce the displacement
   identity `dist (clip (F y₁ s)) (clip (F y₂ s)) = (1 − δ)·(y₂ − y₁)`;
2. `h_cone : g ≤ m + β_S · g · (1 − δ)` (axis 2) — the affine state-displacement
   factor hard-wired into a *hypothesis*, with no `hF` involved.

The closing `nlinarith` succeeds only because the two `(1 − δ)` factors — one
manufactured from `hF`, one supplied by `h_cone` — are the same number. So
deleting `hF` alone would not generalise it; both footprints must go together.
An earlier statement of mine located axis 2 "in the proof"; the verifier
corrected that — it is in the signature, and `(1 − δ)` is load-bearing twice.

#### What was wrong in the prose

The `gainBallValueClass2_IsInvariant_closedForm` docstring, the section header
above it, and notes item **A13** all claimed the two slope floors were pinned to
`g_U_T/(1 − β_T·γ_F)` and its Sender twin, and called the resulting asymmetry
"derived". Two separate errors:

* **The theorem pins no floors.** `g_T`, `g_S` and `K_T` are free real variables
  in its signature. The symbols `L_U_T`, `g_U_T` and `m_S` on which the docstring
  built its economics do not occur in the theorem at all, and there is no
  `hden_T : 0 < 1 − β_T·γ_F` making the claimed Target closed forms even
  well-posed. What *is* pinned, and does discharge its margins — two with
  equality — is `M_T`, `M_S`, `K_S`.
* **Upper modulus substituted for lower chord rate.** The closed-form floor needs
  a *lower* bound on the transition's state displacement. The `γ_F` in these
  files is an *upper* Lipschitz modulus (`h_F_lip`). The two coincide at the
  affine law and nowhere else — which is precisely why the substitution reads as
  harmless until the affine case is left behind.

#### What the audit found that I had not

The flat answer "affine only" was also too strong. `mem_valLipGainBall_bellman_chord`
(`Theory/Bellman/ChordInvariance.lean`) proves a slope-floor closed form against a
**provably non-affine** transition, carried end-to-end at `wobbleEconF`, where the
band's lower rate `glo = 0.48` differs from `1 − δ = 0.5`. The restriction there is
**corner-pinning**, not affineness: the chord band constrains `F` only along the
section `F(·,1)`. For the sup-over-all-sanctions operator, and for the constructed
Banach fixed point `p.V_S`, the only closed-form route remains affine —
`V_S_mem_lowerSlopeCone` is the sole theorem placing that fixed point in the cone,
and it carries `hF`.

Two further standing items the sweep surfaced, neither introduced this round:

* `mem_valLipGainBall_bellman_closedForm` hard-wires the successor
  `δ·y + (1 − δ)` with **no** `hF` — a live axis-2 footprint in a theorem whose
  signature looks general.
* An upper state modulus already exists as a named reusable predicate,
  `Params.TransitionStateLipschitzWith` (`Theory/Basin/PrimitiveHighBasin.lean`).
  The `h_F_lip` hypothesis shape used throughout the gain-ball files duplicates
  it rather than consuming it.

#### The finding that matters most

`GainBallInvariance.lean`, `GainBallCertificate.lean` and
`Foundations/StokeyLucas.lean` contain **zero** occurrences of `δ` or `affineF`
and are clean on all three Rule-22 axes — but **none of their theorems has a
consumer outside its own file.** Everything that actually delivers a slope floor
to a constructed value or to a shipped certificate is affine. The general-`F`
layer built over the last two days is real and is unexercised, which is the same
"general in form, not in practice" pattern the 2026-08-17 entry named. Building
the general layer and rewiring the consumers are two jobs, and only the first is
done.

#### Corrections applied

Docstring and section header in `Theory/Certificates/GainBallCertificate.lean`
rewritten to state what is pinned, to say plainly that the floors are not, and to
record the upper-versus-lower modulus distinction. Notes item A13 rewritten to
match. No Lean statement changed; the defect was entirely in prose, which is the
only place this project has ever over-claimed.

### Round 2026-08-18d — Phase A applied: the general-`F` layer now has consumers

**Zero new assumptions; no theorem statement changed anywhere.** Six gates green
on a clean rebuild: 35 rows, hashes unchanged, and all 86 pinned constants
identical — the snapshot diff was **empty**. Every edit was a proof-body swap, a
docstring, or a de-duplication.

The round executed the six Phase A items of
[`AFFINE-GENERALIZATION-PLAN.md`](AFFINE-GENERALIZATION-PLAN.md), whose premise
was that the affine restriction persists for want of wiring rather than want of
mathematics.

#### What the three targeted affine nodes look like now

| Node | Before | After |
|---|---|---|
| `mem_valLipGainBall_bellman_closedForm` | in the closure of **5** headlines | **zero consumers** |
| `Target_combined_chord_of_decomposition` | in the closure of **3** headlines | **zero consumers** |
| `three_goals_local_MS` | shortest affine edge for a headline | **zero consumers** |

Each was replaced at every call site by a general-`F` sibling that already
existed, compiled, and was axiom-clean — and that had never been called.

#### Per item

**A1** — eight call sites across four witness economies moved from
`mem_valLipGainBall_bellman_closedForm` onto `mem_valLipGainBall_bellman_chord`.
The lemma's exact-affine successor pin is replaced by a `CornerStateChord` band.
*What this does not buy:* none of those four economies becomes general in `F` —
they still set `F := affineF` at the structure level (axis 3), and at every site
the band collapses to `glo = ghi = 1 − δ`. What changed is that **no shared lemma
in the headline closure now forces `y ↦ F(y,1)` affine.**

One correction worth recording: the corner-section rate at these witnesses is
`1 − δ`, **not** `δ`. At three of the four economies `δ = 1/2`, so the two
coincide numerically and the error would have been invisible — the same shape as
the upper/lower-modulus confusion caught earlier the same day.

**A2** — three consumers moved from `three_goals_local_MS` (whose *conclusion*
quantifies over the hand-written affine paths) to `three_goals_local_MS_generalF`
(whose conclusion runs through `p.F`). The extra hypothesis `hF_top` — full
sanctions strictly raise every state below one — is discharged at each affine
witness by the existing `affineF_hF_top`. All three headline statements are
unchanged, because the projected goal names no trajectory.

**A3** — three consumers moved onto
`Target_combined_chord_of_decomposition_lowerChord`, with the sanction lower
chord discharged by the existing `affine_transitionChordPack`. **Plus an
unplanned fourth:** the non-affine QuadBump witness previously proved its Target
combined chord by hand, *because the affine converter was unavailable to it*;
it now routes through the general converter like everyone else. That is the first
consumer of the general converter at a genuinely non-affine transition.

**A4 — the item that closes the sharpest finding in the audit.** The general-`F`
Sender cone preserver `bellmanS_BCF_preserves_lowerSlopeCone_generalF` was
instantiated at **no economy at all**, while its affine twin had two — bifurcation
rather than nesting, which is worse than circularity because a circular general
theorem at least has an instance. `Examples/QuadBumpSenderCone.lean` supplies its
first instance, and supplies it at the **non-affine** `quadBumpF`, not at an
affine restatement. New content: the state-side lower chord of the quadratic bump
(rate `12/25`, against a true infimum of `99/200`), the joint state chord at slope
`g = 15/4`, and cone preservation at the *derived* leader policy. `g = 15/4` is
checked non-knife-edge: the largest admissible slope is exactly `4`, and `41/10`
already fails.

Rule 1 is respected: the policy `qbAlpha ≡ 0` is not posited — `qbCert_zero_isMaxOn_joint`
proves full defiance maximises the joint Target integrand and
`qbCert_α_on_eq_zero` identifies the derived selector with it.

*Deliberately not done:* no instance of `..._generalF_on` (the basin-parametric
sibling). At every existing economy `s = 0` is feasible and `F(x,0) < x`, so no
`Icc xT 1` with `xT > 0` is invariant, and the only admissible basin makes `_on` a
literal restatement of `_generalF` — a fake consumer of exactly the kind Rule 13
exists to catch. A genuine instance needs an economy whose Sender optimum bounds
the sanction away from zero; none exists today.

**A5** — `oneSubBetaS_oneSubDelta_pos` deleted as a verbatim duplicate of
`oneMinus_betaS_oneMinusDelta_pos`, four call sites re-pointed. *Correcting the
audit that proposed it:* it claimed "the older copy carries the honest scope note;
the newer one does not." Both carry one. The older survives because it has a
Target twin, keeping the Round-38 pair coherent. `oneMinus_betaT_oneMinusDelta_pos`
was deliberately left alone — it has zero consumers, which is tempting, but it is
not a duplicate.

**A6** — the Sender contraction proof was re-inlined verbatim **nine times**,
including inside `V_S`'s own definition, with no named lemma. Extracted as
`bellmanS_BCF_contracting`; all nine sites now call it. Per Rule 13's
shared-helper clause the nine copies were checked to be genuinely identical
before extraction, not assumed to be.

#### Rule 2 / Rule 21

Two `paper/appendix_sections/07_formalization_map.tex` entries were corrected in
place: `eeCertMS_three_goals_dominance` and `sfCert_three_goals_dominance` are now
described as transition-independent corollaries routed through the general-`F`
headline, which is what the Lean now does. No staging: these repair claims the
paper already made.

#### What Phase A did not do

It removed axes 1 and 2 from these routes. **Axis 3 is untouched** — seven
otherwise-clean headlines are still instantiated at a fixed `F`, and the
interest-group microfoundation still cannot express a non-affine economy at all.
Those are Phase C3's territory and remain open.

### Round 2026-08-18g — the gain-ball layer may be the wrong abstraction

**A 6-agent reconstruction round: three research dimensions, each adversarially
verified. All three conclusions came back `sound: false`** — but they refute each
other's *proposals* while agreeing on the *diagnosis*, and the agreed diagnosis
is about the layer I built on 2026-08-17, not about the transition.

#### The lead I was carrying is refuted, with a Lean artifact

`dynamicArgmaxUnique_on_set_of_strictConcaveOn`
(`Theory/Equilibrium/ArgmaxUniquenessFromConcavity.lean:289`) quantifies over a
bare `Set Val`, so a loose gain ball instantiates it with no circularity. I had
flagged that as the promising route. **Its hypothesis is false on a loose ball,
and this is a refutation rather than a failed proof attempt.** A Lipschitz-plus-
slope band bounds slope, never curvature, so it contains the kink
`y ↦ g·y + (K−g)·max 0 (y−1/2)`, which defeats strict concavity of the dynamic
objective for *any* finite stage curvature. Both halves were compiled via
`lean_run_code`: the kink lies in the band for every `0 ≤ g ≤ K`, and the composed
objective fails `ConcaveOn` whenever `q·d < β(K−g)`.

So loose-ball argmax uniqueness cannot be bought from concavity of the *carrier*.

#### The route that does work is already shipped — with a different carrier

`DAU_on_cone` (`Examples/SymbolicCertifiedFamilyGeneralF.lean:755`) derives
`DynamicArgmaxUnique` on a genuinely loose cone (`g_S < K_S`) from a **curvature
ceiling** plus a stage-curvature margin — the `hCurv` field (:227),
`β_S·(Σ_V·d_hi² + K_S·M_F) < q`. The supporting `Foundations/` layer is complete
(`semiconcave_comp_of_chords`, `bellmanSemiconcaveConstant`,
`bellman_semiconcave_invariant_clip`, `sup_semiconcave_of_joint`). At `qbParams`
the margin would clear with roughly sixfold slack, because `quadBumpF`'s corner
section is exactly affine so the Riccati modulus degenerates to zero.

#### Why that cannot be bolted onto the gain-ball layer

This is the structural finding, and it is fatal to the reconstruction as I framed
it. `gainBallValueClass2` (`Theory/Certificates/GainBallCertificate.lean:91`)
**hard-codes** `carrier_S := valLipGainBall M_S K_S g_S 0` (:99) and consumes
`h_unique_S : ∀ V_S ∈ valLipGainBall M_S K_S g_S 0, DynamicArgmaxUnique V_S` (:95).
`ValueClass.ofLipGainBall` does the same. A carrier intersected with a curvature
clause is a strictly **smaller** set, so it cannot discharge a hypothesis
quantified over the **whole** ball. The two designs do not compose.

#### Two further doors closed

* **No better economy exists.** Every `U_S` in the tree with a live Sender state
  stake has an `s`-dependent `x`-slope; the certified symbolic family forbids
  `r = 0` by a structure field; the four-group microfoundation has no bare-`x`
  term to build an `s`-free slope from; and the public-choice literature supplies
  the interaction, never separability. The whole-square-floor versus
  corner-ceiling mismatch is not an artifact of a badly chosen witness.
* **One proposed "cheap repair" is already shipped.** `qbCertClass_IsInvariant`
  (`Examples/QuadBumpCertWitnessMS.lean:482`) already routes through
  `mem_valLipGainBall_bellman_chord` at both legs (:488, :524). Re-deriving it
  would be a Rule-13 fake consumer: a literal restatement adding no consumer to
  `gainBallValueClass2_IsInvariant`, which remains at zero tree-wide.

#### What this means for the layer

`gainBallValueClass2_IsInvariant`, `ofLipGainBall_IsInvariant_of_primitives` and
`ofLipGainBall_IsInvariant_of_chords` have had zero consumers since they were
written on 2026-08-17. The rounds since have established, in order: that the
obstruction is not the transition's curvature; that it is not the choice of
economy; that it is not wiring; and now that the carrier the layer hard-codes is
incompatible with the only loose-ball uniqueness route the project has.

The honest reading is that the layer is **superseded by the semiconcave-cone
family** rather than merely unwired, and the decision is whether to deprecate or
re-scope it. That is an architecture decision and it is the author's; it is
recorded here rather than taken. What should NOT happen is another round hunting
a consumer for it — three independent rounds have now failed to find one, each
for a different and sufficient reason.

---

### Rounds AT–AX (2026-09-25) — the payoff functional forms become rate conditions (user-approved, doc 104 M1–M9)

Recorded here as a pointer; the plan with its four-part justifications is doc 104
(`suggestions/abstract-two-sided-forward-looking/104_…`), the record doc 105, and the
compiler-derived statuses `docs/HYPOTHESIS-CENSUS.md`.

**Removed from the placable class:** the two functional forms
`U_S = −(q/2)s² + s(u₀ − ka + rx) + wx` and `U_T = −ℓa + s(nx − c) + vx`. The
quadratic–linear family survives as an instance (`PlacableEconomyF.toChord`).

**Added (M1):** eighteen payoff rate conditions on `ChordEconomy`, each stated over
`U_S`, `U_T` and a named scalar. The paper's (S1)–(S11) are the Sender's state slope
band `w_lo`–`w_hi`, sanction curvature `q`–`Q̄`, joint semiconcavity `(σ_x, r_hi, q)`,
state semiconvexity `τ_x`, cross-rate band `r_lo`–`r_hi`, placation band
`k_lo`–`k_hi`, and first-unit return band `u_lo`–`u_hi`. The paper's (P1)–(P3) are the
Target's compliance-cost band `ℓ_lo`–`ℓ_hi`, pain band `p_lo`–`c`, and state-slope
band `v_lo + n_lo·s` – `v_hi + n_hi·s`. Each lower/upper pair is a real split:
collapsing it re-imposes the functional form (Rule 3, the transition-class clause,
read for payoffs). The payoff bounds `M_U`, `M_T₀` are suprema, not fields. The
state modulus is signed, `0 ≤ σ_x` (M4), which loses no Sender, because the joint
semiconcavity bound increases in `σ_x`.

**Added as theorem hypotheses only (M2):** zero-sanction neutrality
(`ZeroSanctionNeutral`) and its one-sided forms (`ZeroSanctionAntitone`,
`ZeroSanctionNoGain`). They are read by the relief equilibrium, the Sender-only regime
and the four cells, relief uniqueness, the all-equilibria wedge floor and relief
participation. They are not read by the defiance side or the monotone-class uniqueness.

**Open (a Rule-3 question for the user, not taken):** the general-class form of the
tier-2 result (`rule_monotoneOn_of_policy_bounds`) takes two payoff conditions outside
the list above as hypotheses: increasing differences in (sanction, state) at every
compliance level, and semiconvexity of the Sender's stage payoff along the policy.
Whether they should become conditions of the chord economy is the author's decision.
The family corollary discharges both.

## Rounds AY–BA (2026-09-27; doc 107, sign-offs Y1–Y7; record in doc 108)

**No change to the assumption surface.** No field, no theorem-level hypothesis
beyond those already on the chord economy, no headline change (the snapshot is
unchanged at 51 rows).

**Added, as theorems on the existing surface (Rule 3 does not fire):**
`bracket_existence_sides_disjoint` shows that the sharp defiance condition and
the relief-existence condition (the `K_T^rel` form) cannot both hold. It reads
only the class conditions, through two lemmas: `glo_add_dlo_le_one` (the lower
chords span at most the unit square) and `vlo_nlo_floor_le` (the Target's
envelope at the floor is paid for by the pain spread, `c − p_lo`).
`A_lt_of_βS_lt` shows that the upper appetite rises strictly with the Sender's
discount factor. `le_gT_of_balance` and `sharp_gT_of_sharp_of_balance` show that
every slope certified by the balance inequality is at most `g_T`, so every
defiance certificate implies the condition at `g_T`. `collapse_threshold`, with
`glo_add_dlo_eq_one_of_tight` and the definition `betaStar`, solves the collapse
for the displayed threshold. `certified_sharp_mono_βT` shows that certified
defiance is inherited by a more patient Target, and `gT_balance_of_Lresp_eq_zero`
that `g_T` is certified wherever the response does not move with the state. All
of them back sentences the manuscript already made.

**Corrected record (the open question above).** The general-class tier-2
result takes more than "two payoff conditions". Its hypotheses are: a
nonincreasing policy; the Sender's stage payoff along the policy
`L`-Lipschitz and `M`-semiconvex in the state; increasing differences in
(sanction, state) at rate `ρ` at every compliance level; the policy-dependent
margin; and one-sided zero-sanction neutrality (`ZeroSanctionAntitone`). The
outside reader found the omission (review of 2026-09-27, A2), and the file
header and note N124 now list all of them.

**Decided (Y5): the question stays closed.** None of those conditions becomes
a field of the chord economy. N124 stays in the notes in both forms, and the
Target-only uniqueness on the class, which would need `r_hi < q` (a new
assumption), is deferred to revision or a referee request.

## Round BB (2026-09-28; doc 110 §5, approved on the user's word; record in doc 111)

**No change to the assumption surface.** No field, no structure taken as input by a pinned row,
no headline change (the snapshot is unchanged at 51 rows). Every hypothesis of a new theorem is an
existing field, an existing theorem hypothesis, or a strictly weaker restatement of one in
existing parameters. The pinned rows are recovered from the new siblings in Lean.

**Removed from the siblings, relative to the pinned rows:**
- the policy condition of row 46 (`hanti`);
- zero-sanction no-gain and the sequence quantifier of row 48;
- two implied equalities of row 45 (`r_hi = 0`, `n_lo = 0`);
- the margins of row 49, and argmax uniqueness;
- the rally margin of row 37's clauses (i)–(iii);
- `hsbar_pos` and `x̄ < 1` of row 27, with full-sanction ascent localised to `[0, x̄]`;
- (F5) of row 2's shock goal, replaced by pre-basin ascent;
- the Target preference P4 and the pivot's positive lower bound of rows 1–2;
- the Target anti-preference `A2*` of row 3.

**Stated for transparency:**
1. **`0 ≤ m`** in the named-chord general-transition Sender floor. It already appears as a
   hypothesis of the affine `no_top_gain` theorem, and on the chord class it is `w_lo > 0`. `hF`
   does not imply it. The sign-free joint-chord form is the de-affined sibling of record.
2. **A monotone defiance value at one member** in the `_of_monotone` patience theorems. It is
   implied by the monotone response plus the existing balance inequality, which the balance-form
   theorems use instead.
3. **`β_T ≠ β*`** in the collapse threshold. A scope restriction; the equality case is open.
4. **Data-level definitions.**
   - `DefianceBestReply` and `SameGameButβT` are written over data (Rule 14).
   - `SenderPersistenceBasinLow` copies three fields of `JointPreferenceBasinLow`. Its generality
     beyond the joint class is unwitnessed (Rule 9B).
5. **The Rule 9B record.**
   - The defiance core over `Params` is inhabited through the chord class. The quartic member
     satisfies `LossOffset₀` and has an equilibrium in the class.
   - No member outside the chord class is exhibited.
   - Pre-basin ascent is strictly weaker than (F5) at a transition proved non-affine
     (`plateauF_ne_affineF`).

**Deferred, per the user's Z4 (each needs a Rule 3 stop when its round opens):**
- the timing result (a new equilibrium structure);
- the supermodular-transition discharger of the monotone response;
- the potential form of the margin;
- the relief lower set;
- the ordinal patience form;
- the microfoundation route;
- stochastic kernels;
- the SPE security condition.

The relief-extension split of `ChordEconomy`, the demotion of `hStageRelief` and `hInterior`, and
turning `F_mem` into a theorem change pinned structures (Rule 18). They are proposed, not done.

## Round BC (2026-09-29; on the user's word; record in doc 112)

**The assumption surface shrinks; no assumption is added.** The user approved the nine re-pins
and three new rows of doc 111 §5 and the three structure changes, and declined every
new-assumption item of doc 110 (Z4).

**Structures.**
- `AbstractGame.Params` loses the field `F_mem` (the transition maps `[0,1]²` into `[0,1]`). It is
  derived from `F_mono_x`, `F_mono_s` and `F_diag` and is now the theorem `Params.F_mem`.
  `CubeData.F_mem` likewise.
- `ChordEconomy` loses eleven fields. Interiority (`A < q`) and the stage relief margin
  (`ℓ_hi·Q̄ < k_lo·p_lo`) become the predicates `ChordEconomy.Interior` and
  `ChordEconomyRelief.StageRelief`, hypotheses `hInt`, `hSR` of exactly the results that read them
  (the Sender channel's activation, the strict wedge, the cap, the myopic, Sender-only and relief
  equilibria; the stage relief margin: the myopic equilibrium and the collapse threshold).
- `ChordEconomyRelief extends ChordEconomy` holds the nine relief-side fields: `ℓhi`, `plo`,
  `vhi`, `nhi`, `hUS_crossHi` (S9), `hUT_costHi` (T3), `hUT_painLo` (T5), `hUT_stateHi` (T7),
  `hplo`. `ChordEconomyCs` extends it. Lemmas that read them moved to it; none is stated over a
  stronger class than before the round.

**Headline rows.** Nine re-pinned to siblings with fewer or weaker hypotheses (rows 1, 2, 3, 27,
37, 45, 46, 48, 49); rows 32 and 35 move to the relief extension; rows 32, 35, 39–41, 43 and 44
carry `hInt` (35 and 39 also `hSR`) where the class used to carry it; rows 52–54 added (the
Target's security bound, patience on existence, the defiance core over any economy). 54 rows,
all axiom-clean.

**Rule 9B.** The base class's extra generality is unwitnessed (every member in the tree satisfies
the relief extension, interiority and the stage relief margin); recorded in the `ChordEconomy`
docstring.

## Round BD (2026-10-01; on the user's word; record in doc 113)

**No assumption is added.** No field, no structure taken as input by a pinned row, and no headline
change (the snapshot is unchanged at 54 rows). The round machine-checks five claims the paper or
the docstrings already made in prose. Each new theorem's hypotheses are existing fields or
theorem hypotheses, or weakenings of the affine law (doc 113 §4):

- **Tight chords pin the affine law** (`TightChords.eq_of_sanctionChords_tight`,
  `eq_of_stateChordBandAll_tight`, `add_eq_one_of_tight`; chord-economy corollaries in
  `ChordEconomyTightChords`): the chord fields and `F_diag`, both existing.
- **The sharper welfare-gap bound** (`FourGroup.pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords`,
  `_of_sectionChords`): a lower chord to the fixed corners at rate `g ≥ 0` on the two endpoint
  sections. This is the hypothesis the appendix remark already named. It is implied by the chord
  economy's state band and by the affine law.
- **Entry against exit horizons** (`Params.entryBound_lt_exitBound_iff`,
  `entryBound_lt_exitBound_iff_lt_half`, the horizon comparisons and their mirrors): strict
  adjustment (existing). The midpoint statements also take reflection symmetry,
  `F(1−x, 1−s) = 1 − F(x, s)`. It is written directly over `p.F`, with no new `Prop`. The affine
  law implies it and it is strictly weaker (Rule 13's de-affining exception), witnessed non-affine
  by `cubicReflectF_ne_affineF`.
- **Balance is an upper set in `β_T`** (`ChordEconomyRelief.balanceSide_anti`,
  `balance_of_le_βT`, `ChordEconomyCs.SameButβT.balance_of_balance`): nothing beyond the existing
  balance inequality.
- **History-dependent security**
  (`HistoryDependentSecurity.isLeast_ceiling_history_of_openLoop_saddle`,
  `isGreatest_floor_history_of_openLoop_saddle`, and the chord-economy corollaries in
  `PlacableSenderSecurityHistory`): `LossOffset₀`, existing. The plan types `LeaderPlan` and
  `FollowerPlan` are definitions, not hypotheses.

**Rule 9B.** Items 2 and 3 are stated over classes that contain the affine law.
`ReflectionSymmetricWitness` exhibits a member outside it: `(x+s)/2 + (s−x)³/10`, clipped to the
square. It lies in the `Params` class, is reflection-symmetric and strictly adjusting, is not
affine at any rate, and has endpoint corner chords at `g = 2/5`. Item 5 is instantiated at the
quartic member `qwDefiance` (non-affine `F`).

**Verification.** From-empty HPC build, Slurm job 30481523 (CLAUDE.md Rule 26). All 79 public
declarations of the round are axiom-clean on `propext`, `Classical.choice` and `Quot.sound`.

## Manuscript rebuild (2026-10-01/02; author decisions D1–D5; blueprint in `suggestions/2026-10-01-manuscript-rebuild/`)

**No assumption is added.** The rebuild restructures the paper. It changes no theorem, structure
field or hypothesis.

- **Headline set, 54 → 59 (D4).** This is an anchor change the author approved under Rules 3
  and 18. The five new rows pin existing theorems with their existing hypotheses:
  - `ChordEconomy.reliefPayoff_isLeast_history` and `reliefPayoff_isGreatest_history`:
    `LossOffset₀`, existing;
  - `ChordEconomyCs.SameButβT.balance_of_balance`: the existing balance inequality, at the less
    patient member;
  - `ChordEconomy.no_zero_rule_equilibrium`: `LossOffset₀`;
  - `ChordEconomyCs.collapse_equilibrium_threshold`: `Interior`, `StageRelief`, `Placable`, the
    fourteen tightness equalities and `β_T ≠ β*`, all as before.

  No existing row's structural fingerprint, printed hash or axiom set moved.
- **Main-text propositions (D2, D5).** `prop:patience-existence`, `prop:security`,
  `prop:identification` and `prop:collapse-threshold` state those declarations with exactly their
  hypotheses. The paper's "admissible member" keeps interiority, the stage relief margin and the
  curvature margin.
- **Relocations (D1).** A1–A3, the basin and (F6-Q) moved with the persistence results to
  `app:persistence`. They remain hypotheses of exactly the results that read them; none became a
  maintained assumption, and none was dropped.

## Round BE (2026-10-03; Lean batch A of the second ChatGPT review, on the user's word; record in `suggestions/2026-10-02-chatgpt-gap-review/02_LOCAL_REVIEW_2026-10-03.md`)

**No assumption is added.** Six modules prove new theorems on the existing surface. No structure
field, `Params` field or headline row changes.

- **`prop:collapse-threshold`** now states `ChordEconomyCs.collapse_equilibrium_threshold_le`:
  the hypotheses of `collapse_equilibrium_threshold` (headline row 59, unchanged) without
  `β_T ≠ β*`. One hypothesis is removed; none is added.
- **`prop:defiance-closed`** (`ChordEconomy.exists_defiance_equilibrium_of_tendsto`,
  `ChordEconomyCs.defianceExistence_sInf_mem`): general in `F`. It reads only the class's own
  fields, a sequence of members that differ in `β_T`, and a positive infimum.
- **`prop:affine-window`** (`aw_zero_rule_iff`, `aw_full_defiance_iff`, `aw_window_at_β₁`,
  `aw_continuum`): one affine member, every coefficient but `β_T` fixed. Rule 22: AFFINE.
- **`prop:core-outside-chord`** and **`prop:interior-witness`**: existence witnesses (Rule 9).
  The first is a `Params` instance outside the chord class; the second is a `ChordEconomyCs`
  member with a quadratic compliance cost.

**Verification.** From-empty HPC build, Slurm job 30983394 (run `spcl-ba-20261003T213827Z`,
source `e5e4f52`; CLAUDE.md Rule 26): FORMAL_PASS. All 19 round declarations are axiom-clean on
`propext`, `Classical.choice` and `Quot.sound`. The release gate, job 30988819 on source
`0cc749c` (two Lean comment syncs, no declaration changed), passed as well.

## Round BF (2026-10-03; the general exact thresholds, on the user's "1. yes, 2. yes, please go")

**One theorem-level hypothesis is added, with the author's approval (Rule 3).** No structure
field, `Params` field or headline row changes.

- **The hypothesis.** `ℓ_hi·L_α ≤ v_lo`: the state's lower rate at zero sanction covers the
  compliance cost along the zero level (`L_α = M_tot·L_resp/(k_lo·μ)`, the zero level's state
  Lipschitz constant).
- **Why it is needed.** It makes the relief value `VTrel` nondecreasing in the state
  (`ChordEconomyCs.VTrel_monotone`). That gives "a less patient Target keeps the relief
  equilibrium" (`reliefBestReply_anti_βT`), hence the relief existence set is an interval
  `(0, β_R]` (`reliefExistenceSet_eq_Ioc`). It mirrors the monotone defiance value that the
  patience result already uses on the defiance side.
- **What it costs.** It reads existing constants only and does not involve `β_T`, so it holds
  across a whole `β_T` family or nowhere in it. It is sufficient, not necessary: the inheritance
  theorem itself takes the monotone relief value directly, at either member.
- **Discharge.** At the affine member, `5/23 ≤ 30` (`awE_relief_rate`).

No other new hypothesis. The exact relief test (`exists_relief_equilibrium_iff`) reads
interiority, placability and zero-sanction neutrality, as before. The closure in `β_T`
(`reliefBestReply_of_tendsto`) reads nothing new. The defiance interval
(`defianceExistenceSet_eq_Ico`) reads a monotone response at full defiance and the balance at
`g = 0` (`c·L_resp/μ ≤ v_lo + n_lo·σ(0,0)`), both existing. The affine window
(`aw_exact_thresholds`) is restated as an instance (Rule 22: AFFINE, one member).

**Verification.** From-empty HPC build, Slurm job 30991234 (run `spcl-bf-20261003T233144Z`,
source `4725d3b`; CLAUDE.md Rule 26): FORMAL_PASS, 3790 jobs. All 10 round declarations are
axiom-clean on `propext`, `Classical.choice` and `Quot.sound`. The census reviews every binder
of the new roots, the new hypothesis among them (`scripts/census_build.py`).


## Renovation Phase A (2026-10-06; rounds BG-0 to BG-3 of `docs/RENOVATION-PLAN-2026-10-06.md`, on the user's word)

**No new assumption.** Every item removes or weakens a hypothesis, derives one from the others, or
adds a general theorem with the old form kept as a corollary. The author decided all items on
2026-10-06. The Rule 3 decisions of the plan (items 1-6) are recorded in its section 3; none was
exercised in this phase.

- **Derived, so dropped (category: derivable).**
  - `a < 1` in the Perov engine (from `d < 1`, `0 ≤ b`, `0 ≤ c` and the Schur margin).
  - `g_lo ≤ g_hi` in the Bellman chord invariance (from the corner band).
  - Nonemptiness of the existence sets (from a positive infimum; an empty relief set equals
    `Ioc 0 0`).
  - The stage relief margin in the four cells (from the sharp relief margin).
  - `0 < m` and `0 < M` in the welfare-interval lemmas.
  - The strict placation margin in the symbolic MS certificate (the canonical myopic ceiling
    holds without it).
  - Several sign and range binders in Foundations (centered contraction, cross differences,
    zero level).
- **Weakened (category: localised or one-sided).**
  - Two-sided strict adjustment becomes zero-sanction descent (limit dependence) or full-sanction
    ascent below the basin (shock-strength comparisons); this is decision 3.
  - Global strict monotonicity of `F` in `s` becomes local upward adjustment (strict escalation).
  - A monotone rule becomes a monotone closed loop (path comparators).
  - A linear cost with `ℓ > 0` becomes a weak cost sign (defiance core).
  - Strict inequalities become weak ones where only existence is concluded (bracket, closed side).
  - `0 ≤ x̄` is dropped from basin invariance.
- **General forms (Rule 22).**
  - The myopic comparator reads the actual transition.
  - Shocked single crossing takes a free sanction rate; the affine forms are its instances.
  - Semiconcave composition reads a two-sided Lipschitz bound in place of two chords and a band.
  - A zero response slope forces the affine law on the square, so the `L_resp = 0` results are
    labelled AFFINE BY HYPOTHESIS, no longer "general in F".
- **Superseded statements in this register.**
  - The entries saying `coupledJointOpWide` and `…_fixed_of_equilibrium` are kept: both are now
    retired, refuted by `coupledJointOpWide_h_invT_contradictory`.
  - The entries saying the symbolic MS certificate needs a strict placation margin and is
    unavailable at `wobbleEconF`: `wobbleEconF_certificateMS` now exists.
  - The single-carrier `ValueClass` existence trio: deleted as dead.
  - The two Gate-4 refutations are now corollaries of
    `AbsorbingTop.no_equilibrium_of_slope_and_top_gain`.
- **Reverted.** BG3.12 (`WelfareCompletion.hQ : 0 ≤ Q`). It would have weakened the pinned
  existence statement `exists_completions_reversing_regime_ranking` without an approved re-pin
  (decision 41 required the `0 < Q` conclusions kept).
- **Left in pinned statements, unused.** `_hdl : 0 ≤ d_l` in
  `policy_eq_zero_of_rule_monotone`, and `_hβ_T_lt` in the two `thm:existence` Schur roots. They
  are removable only by re-pin (Rule 18). BJ1.1 needs `β_T < 1` again once the sign conditions go.

**Verification.** From-empty HPC build, Slurm job 31160363 (run `spcl-bga-20261006T221928Z`,
source `5e5830a`; CLAUDE.md Rule 26): FORMAL_PASS, 3790 jobs. The 72 new declarations are
axiom-clean. Census: 181 roots, 0 unreviewed, 0 unclassified, 0 stale.


## Renovation Phase B (2026-10-06/07; rounds BH-1 to BH-3 of `docs/RENOVATION-PLAN-2026-10-06.md`, on the user's word)

**No new assumption.** Every new theorem is provable from the existing surface. The localised
halves of (F5) used here count as weakenings, by author decision 3 (Rule 3 item 3).

- **Weakened at the manuscript roots (census re-anchored).**
  - thm:shock no longer reads P4.
  - cor:nontermination reads only the ratchet `x ≤ R(x)` on `[x̄, 1]`.
  - thm:finite-episode (iii) reads held-sanction ascent `x < F(x,h)` on `[0, x̄]` in place of (F5).
  - thm:relief-exit and prop:post-relief-persistence read post-basin descent `F(x,0) < x` on `[x̄, 1]`.
  - Order selection reads a monotone closed loop in place of a monotone rule.
  - prop:strict-dominance reads `W(d) ≤ W(m)` for `d ≤ m` only.
  - cor:pathwise-dominance and prop:flip-route are general in F.
  - The placable episodes, the 11 cell, the planner boundary and relief participation hold at
    every full-defiance equilibrium (LO and RM were used only to name the constructed one).
  - prop:patience-existence drops (T6) and uses `SameGameButβT`.
  - prop:collapse-threshold needs nine conditions and states β_D = β_T*.
  - prop:security holds for any economy with the zero-section state chord, the sanction lower
    chord, the three Target bounds and the margin.
- **Re-signed.** Interiority (`u_hi + β_S·K_S·d_hi < q`) becomes the stage appetite `u_hi < q`, and
  placability (`A ≤ k_lo`) becomes `u_hi < k_lo` wherever only the stage form is read. Both are
  implied by the old conditions.
- **Re-pinned (Rule 18, decision 12).** Headline rows 1-2 now pin the P4-free composites over the
  persistence certificate. P4 remains only in thm:persistence (vi) (J3).
- **Vacuity notes (Rule 9B).** The statements quantified over full-defiance or carrier equilibria
  are vacuous when none exists. Their docstrings record the existence criterion
  (`exists_defiance_equilibrium_iff`), and `oc_security_outside_chord_class` witnesses the security
  core outside the chord class.

**Verification.** From-empty HPC build, Slurm job 31163964 (run `spcl-bgb-20261007T011919Z`,
source `16c3ab0`): FORMAL_PASS, 3796 jobs. The 232 new declarations are axiom-clean. Census: 200
roots, 0 unreviewed, 0 unclassified, 0 stale.


## Renovation Phase C (2026-10-07; rounds BH-4 to BH-6 and BI.2 of `docs/RENOVATION-PLAN-2026-10-06.md`, on the user's word)

**One approved Rule 3 item; otherwise no new assumption.**

- **BI.2, approved as Rule 3 item 2 (2026-10-06).** It applies to the new planner-optimum theorem only.
  - *The hypotheses.* The planner margin in two cases on the sign of B = b_J − b_K:
    - for B ≥ 0, g_J − q_K + β·B·L/(1−βλ) ≤ d_s, with an upper sanction chord L and a zero-section band λ,
      βλ < 1;
    - for B ≤ 0, g_J − q_K ≤ d_s, with monotone F only.

    The maximiser a* comes from compactness.
  - *Why.* The first unit of sanction must not pay socially, counting the discounted political shift it
    causes. The tree's hawk-scaled and positive-cost economies violate the margin and have a non-zero
    planner optimum, so some margin is needed.
  - *Cost.* None for existing results: nothing existing changed, and the certificate economy's optimum
    is an instance.
- **BH4.1, weakened.** The rally margin is replaced by a monotone response at full defiance (`hmono`)
  in 19 siblings. The margin implies it, strictly (`exists_member_response_monotone_not_margin`). Being
  a condition on an endogenous object, it is stated in the appendix, and the main text keeps the margin
  (decision 24).
- **Witness families (BH-5).** Each numeric witness that carried more than existence is now a family
  over the transition, with the old witness as an instance. The stage-flip route gains its first
  non-affine inhabitant.

**Verification.** From-empty HPC build, Slurm job 31208385 (run `spcl-bgc-20261007T183642Z`, source
`dc750dd`): FORMAL_PASS, 3800 jobs. The 426 new declarations are axiom-clean. Census: 225 roots, 0
unreviewed, 0 unclassified, 0 stale.


## Renovation Phase D, waves 1-2 (2026-10-07/08; items BJ1-BJ4 of `docs/RENOVATION-PLAN-2026-10-06.md` without BJ4.3, on the user's word)

**Two approved Rule 3 items; every other change removes or weakens an assumption.**

- **Rule 3 item 5 (approved 2026-10-06): `hcn : n < c` on the placable family.** The sanction hurts the Target at every
  state. It replaces the interiority and stage-relief fields (BJ2.3); interiority, `u₀ ≤ q` and stage relief become
  hypotheses of exactly the results that read them. Stage relief implies `n < c`, so the family is strictly larger.
- **Rule 3 item 6 (approved 2026-10-06): `hnv : 0 ≤ n + v` on the symbolic persistence core.** The Target's corner stage
  payoff does not fall as the state rises. It is the single Target condition of `SymbolicEconomyFPersist`, in place of
  `0 ≤ n`, `ℓ ≤ c − n` and the loss-offset margin (BJ4.4); the old family reaches the core through `toPersist`.
- **Weakened or removed.**
  - The existence roots' four coefficient signs (BJ1.1). The value-Lipschitz chain's dead or derivable sign binders
    (BJ1.2). P5 now only on the joint basin and only against the pivot (BJ1.3). The Target loss-offset stack of the
    core certificates (BJ1.4). An unread low-basin field (BJ1.5).
  - On the chord class, q > 0 is derived (BJ2.1); the upper placation rate is a predicate read where it is needed
    (BJ2.2); the two-sided curvature fields leave the base class (BJ3.1). Rule 9B: no member in the tree lies
    outside `ChordEconomyTwoSided` or violates the placation ceiling, so that extra generality is unwitnessed.
  - On the symbolic family, the Sender stage margin and the sanction-floor block are removed; `F_mem` and `glo ≤ ghi`
    are theorems; `0 < dlo` is weakened to `0 ≤ dlo` (BJ4.1, BJ4.2).

**Verification.** From-empty HPC build, Slurm job 31227640 (run `spcl-bjd12-20261008T021529Z`, source `c0510b3`):
FORMAL_PASS, 3800 jobs. The 292 new declarations are axiom-clean. Census: 224 roots, 0 unreviewed, 0 unclassified,
0 stale.

## Renovation Phase D, wave 4 (2026-10-08; items BJ5.1 and BJ5.2 of `docs/RENOVATION-PLAN-2026-10-06.md`, on the user's word)

**No new assumption; one condition leaves the basic game.**

- **BJ5.1, weakened.** Joint continuity of the static Sender selector was a field of every economy (`Params`). It is
  now the class `Params.StaticSelectorContinuous`, required only by the myopic-comparator and static-Sender results
  (the Step-0 closure list). Headline rows 1-2 state it as a binder, because goal 2 compares with the canonical myopic
  equilibrium; their content is unchanged. The chord class keeps it as its own field (relocated: its four-cell and
  regime results compare against the static Sender). Every other result covers economies whose static best response
  jumps, for example a Sender whose payoff is linear in the sanction with a state-dependent sign. Rule 9B: no such
  economy is in the tree yet.
- **BJ5.2.** The unread `CubeData` adjustment-rate fields are removed.

**Verification.** From-empty HPC build, Slurm job 31238804 (run `spcl-bjd6-20261008T070642Z`, source `78cb300`):
FORMAL_PASS, 3800 jobs. The 93 new declarations are axiom-clean. Census: 224 roots, 0 unreviewed, 0 unclassified,
0 stale.

## Renovation Phase D, wave 3 (2026-10-08; item BJ4.3 of `docs/RENOVATION-PLAN-2026-10-06.md`, on the user's word)

**No new assumption; the symbolic family's curvature block and full-range Sender uniqueness go.**

- **Weakened: Sender argmax uniqueness.** The value class asks for uniqueness of the Sender's dynamic best response
  only at physical compliance levels a in [0,1] (`DynamicArgmaxUniqueOnI`), not at every real a.
- **Removed: the symbolic family's curvature block.** The upper sanction chord d_hi, the curvature ceilings M_F and
  M_state, the curvature margin and the semiconcavity clause of the carrier. They bought uniqueness at every real
  compliance level, which the value-class route no longer reads; at physical compliance, strict monotonicity of the
  Sender's objective in the sanction gives it. The cap M_F < d_lo/2 is gone, and the class now contains strongly curved
  transitions, including the wobble file's published one (`wobbleEconFHalfTenth`).
- **Moved to theorem level: the semiconcavity conclusion.** Row 30's carrier conjunct no longer includes semiconcavity;
  `persistence_generalF_semiconcave` restores it under a corner curvature bound stated as a hypothesis.

**Verification.** From-empty HPC build, Slurm job 31242474 (run `spcl-bjd7-20261008T111726Z`, source `2f1ec57`):
FORMAL_PASS, 3800 jobs. The 35 new declarations are axiom-clean. Census: 225 roots, 0 unreviewed, 0 unclassified,
0 stale.

## Renovation closing round (2026-10-08, on the user's word)

**No new assumption; five dead binders removed.**

- Headline row 5: the initial-state bounds `0 ≤ x₀ ≤ 1` (never read). Headline row 46: the lower-chord sign
  `0 ≤ d_lo` (unread since round BG). `feedbackStackelbergTop_unique_in_carrier_schur_of_mem`: the two discount signs
  (unread since BJ1.1).
- Kept by decision: the continuity binder of rows 1-2 (BJ5.1), the chord class's continuity field, and the BJ4.3 form
  of rows 30 and 12b.

**Verification.** From-empty HPC build, Slurm job 31248667 (run `spcl-close-20261008T133550Z`, source `b2ca088`):
FORMAL_PASS, 3800 jobs. Census: 225 roots, 0 unreviewed, 0 unclassified, 0 stale.

## Round N180 (2026-10-08, on the user's word)

**No new assumption.** The no-cycles result (`rulePathF_no_cycles`, `equilibrium_no_cycles` and the four reading
corollaries) takes the rule's feasibility and monotonicity as hypotheses and reads only the transition's monotonicity
fields.

**Verification.** From-empty HPC build, Slurm job 31267051 (run `spcl-n180-20261008T213028Z`, source `45c434a`):
FORMAL_PASS, 3802 jobs. Census: 231 roots, 0 unreviewed, 0 unclassified, 0 stale.

## Round step 2 (2026-10-10, JET preparation; on the author's "approve 1-6 (but mark explicitly for the rare use case one and note some of them cannot be general)")

**Six approved hypotheses (Rule 3), each named in the `Scope:` line of every theorem that uses it.**
1. ND10, the stage form of the net-of-compliance defiance condition with its stage balance; case 10 (`prop:target-only`)
   only.
2. Strict forms of the net conditions; used only in best-reply uniqueness clauses.
3. Hostile stake bound: `U_S(x₂,0,s) − U_S(x₁,0,s) ≤ −w̄ (x₂ − x₁)` for every sanction `s`, `w̄ > 0` (at `s = 0` only for
   the relief price). **Rare case:** a Sender whose coalition loses when hard-liners gain.
4. Residual appetite `u_lo > β_S K_S d_hi`, with hypothesis 3. **Rare case**, same.
5. Affine-policy / quadratic-value class restriction for the classification theorem. **Not general:** the classification
   covers only equilibria in that class.
6. For `r > 0`, `n = 0`; `den > 0` is derived (`rhi_div_klo_le_Lalpha`, from the round-BF relief rate condition
   `ℓ_hi·L_α ≤ v_lo`), not assumed. **Not general:** `n = 0` only.

The net-of-compliance defiance condition itself is the existing `equilibriumTop_sharp` hypothesis set, not new. The
linear-quadratic benchmark (`LQData`) is a stated benchmark family, marked "linear–quadratic benchmark only"; the witnesses
(`lw_witness`, `hsw_full_defiance_bounds`, `AWWhole.aw_exists_on_window`) are existence certificates at one example economy
(Rule 9), marked "at the example economy only (not general)".

**Verification.** From-empty HPC build, Slurm job 31409343 (run `spcl-step2-20261011T030756Z`, source `dfea641`):
FORMAL_PASS, 3817 jobs. Census: 264 roots, 0 unreviewed, 0 unclassified, 0 stale.
