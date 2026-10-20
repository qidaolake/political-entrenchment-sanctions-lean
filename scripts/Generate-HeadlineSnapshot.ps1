# Generate-HeadlineSnapshot.ps1 — Rule-18 durable ground-truth anchor.
#
# Regenerates HEADLINE-SNAPSHOT.md: one row per headline theorem with its
# fully-qualified name, a SHA256 hash of the theorem's ELABORATED type
# (pretty-printed by the compiler via `#check @name`, never source text,
# so cosmetic reformatting does not register as drift), a STRUCTURAL
# fingerprint (round O, doc 82 P5: SHA256 of a canonical de Bruijn
# serialisation of the same elaborated type -- binder names dropped, proof
# subterms elided -- so a binder rename does not register either; the
# serialiser is `#structuralRoots` in contract_probe.lean.template), its
# kernel axiom set (Rule 10 scan), and the pinned toolchain string.
#
# Regenerate-and-diff each round (Audit-Round.ps1 gate 5, keyed on the
# structural column): a removed row, a vanished theorem, or a changed
# fingerprint FAILS the round and must be surfaced to the user (Rule 3) —
# never silently overwritten; a moved printed hash with the fingerprint
# unchanged is reported as information.
#
# Usage (from repo root):
#   powershell -ExecutionPolicy Bypass -File scripts\Generate-HeadlineSnapshot.ps1
#
# Exit codes: 0 = snapshot written, all axiom sets clean;
#             1 = elaboration failure / missing theorem / disallowed axiom.

param([string]$OutFile = "HEADLINE-SNAPSHOT.md")

$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot

# ---------------------------------------------------------------------------
# LOAD-BEARING HEADLINE SET (Rule 18).
# Adding, removing, or renaming an entry is an assumption-surface change:
# it triggers a Rule-3 stop-and-confirm with the user. Do NOT edit silently.
# Names are resolved under the `open` list below; the compiler records the
# fully-qualified form in the snapshot.
# ---------------------------------------------------------------------------
$headlines = @(
    # Three-goals headlines (paper Theorems 1-3), all at a GENERAL transition.
    #
    # Rule-18 swap, user-approved 2026-08-08 (Rule 22 general-F round).
    # Rows 1 and 3 previously snapshotted the affine-trajectory forms
    # `standardCompliance_three_goals_local_MS` and
    # `standardCompliance_three_goals_local_low_basin`. Those carry no
    # `hF` hypothesis but are still affine-restricted, because their
    # conclusions are stated over `dynamicTopLockInPath` / `shockPath`,
    # which hard-code `(1-d)x + d*rule` and never route through `p.F`
    # (Rule 22, axis 2). The `_generalF` siblings below state the same
    # conclusions over `dynamicTopLockInPathF` / `shockPathF`, i.e. over
    # the actual transition field, and both already existed unused.
    #   * low basin: STRICTLY STRONGER at identical assumption cost --
    #     the dual descent F(x,s) <= F(x,x) = x needs only F_mono_s and
    #     F_diag, so no hypothesis is added.
    #   * high basin: adds only `hF_top` (x < F x 1 below the top), which
    #     the affine law satisfies automatically and which
    #     `StrictAdjustment` -- and now also a positive sanction lower
    #     chord -- supplies for free.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 1 was `standardCompliance_three_goals_local_MS_generalF`, now its sibling.
    # Re-pinned renovation round BH-1, 2026-10-06 (plan item BH1.6, author decision 12): row 1 was
    # `standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent` (MS certificate, carries P4), now the
    # P4-free composite over the persistence certificate, same conclusion.
    'StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent',
    # User-approved Rule-18 replacement 2026-07-17: this row derives
    # the explicit minimum-drift shock duration required by Theorem 3.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 2 was `standardCompliance_three_goals_local_MS_generalF_min_drift_shock`, now its sibling.
    # Re-pinned renovation round BH-1, 2026-10-06 (plan item BH1.6, author decision 12): row 2 was
    # `standardCompliance_three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent`, now its P4-free sibling.
    'StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent',
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 3 was `standardCompliance_three_goals_local_low_basin_generalF`, now its sibling.
    'standardCompliance_low_basin_generalF_of_sender_level',
    # Same-alpha dominance (paper Theorem 2 wrapper) + shock-entry closed form
    'theorem2_dynamic_dominates_myopic_at_same_alpha',
    # DELIBERATELY AFFINE (Rule 22): this row IS the closed-form shock
    # horizon N_*, and a closed form is exactly what generality costs --
    # the general-F shock entry asserts only `exists N`. Retained and
    # marked rather than generalised; the general-F counterpart is the
    # min-drift row above. Do not "fix" this to a general-F form: that
    # would delete the closed form, which is the row's whole content.
    'shockEntryHorizon_bound',
    # Shocked interior existence (conditional on the three-condition analytic package)
    # Non-vacuity witness corollaries (complete certificate instances)
    'eeCert_three_goals_dominance',
    'eeCertMS_generalF_three_goals',
    'eeCertMS_three_goals_dominance',
    # Full-width mechanism-witness existence plus realised-rule monotonicity
    # (row 10, user-approved Rule-18 addition 2026-07-16).  This theorem has
    # NO hypotheses: it packages the explicit h=1 equilibrium together with
    # monotonicity of its greatest realised sanction rule on [0,1].  It does
    # not assert the dynamic floor, which is separately refuted at this
    # equilibrium.
    # Full-width mechanism-active frontier (row 11, user-approved Rule-18
    # addition 2026-07-19): nonconstant values for both players, strict
    # dynamic-over-myopic Sender action at the top state, monotone realised
    # sanction rule, and impossibility of the high-basin dynamic floor.
    # Non-affine-transition witness corollary (row 12, user-approved
    # Rule-3 addition 2026-07-03: general-F three-goals at quadBumpF)
    'qbCertMS_generalF_three_goals',
    # Low-basin witness corollary (row 13, user-approved Rule-3
    # addition 2026-07-03: Theorem-4 mirror at quadBumpLowF)
    'lbLow_generalF_three_goals',
    # Corner-non-affine three-goals witness (user-approved Rule-18 addition
    # 2026-08-19). The strongest non-affine row: `wobbleEconMS`'s transition is
    # proved unequal to `affineF d` for EVERY adjustment weight
    # (`wobbleEconMS_F_ne_affineF`), and its CORNER SECTION -- the only slice the
    # certified recursion `x_{t+1} = F(x_t, 1)` ever executes -- is non-affine
    # too (`wobbleEconF10_corner_not_affine`). The affine route is not merely
    # unused there but false (`wobbleEconMS_legacy_route_unavailable`).
    # Contrast row 12: `quadBumpF` is non-affine on the square but its bump
    # carries a transience factor that vanishes at full sanction
    # (`quadBumpF_corner_isAffine`), so that row exercises the incentive layer
    # under a non-affine transition while its realised path stays affine. This
    # row is what makes the delivered generality reach the DYNAMICS.
    'wobbleEconMS_three_goals_full',
    # B2 non-monotone-continuation witness corollary (row 14,
    # user-approved Rule-3 addition 2026-07-04: first consumer of the
    # interval-dominance discharger; single crossing machine-checked
    # FALSE at this economy)
    'b2NonMono_three_goals_dominance',
    # Mechanism-active general-F B2 benchmark (user-approved Rule-18
    # addition 2026-07-24): the SAME positive-discount equilibrium has
    # nonconstant values for both players, an interior Sender sanction
    # at the pivot, dynamic > myopic sanctions there, high-basin
    # persistence, and finite minimum-drift shock entry from every start.
    'b2_integrated_mechanism_active_generalF_witness',
    # FourGroup microfounded witness corollary (row 16, user-approved
    # Rule-3 addition 2026-07-04: first certificate with stage payoffs
    # DERIVED from the interest-group microfoundation)
    'fourGroupCert_three_goals_dominance',
    # Krylov-Bogolyubov wash-out invariant law (row 17: exists + unique + attracting)
    'boxTransfer_existsUnique_invariant_attracting',
    # Within-carrier equilibrium uniqueness (row 18, user-approved Rule-3
    # addition 2026-07-06: under the Schur margin, any two top-selector
    # feedback Stackelberg equilibria with carrier values and selector
    # coincidence agree in both value functions and the policy — the
    # machine-checked form of the paper's within-carrier uniqueness claim)
    # Stage-flip route inhabited (row 19, user-approved Rule-3 addition
    # 2026-07-08: the three-goals conclusions at the stage-flip witness
    # economy sfParams, with the certificate produced BY the
    # of_stage_flip constructor — derived pivots, basin [1/2,1] — and the
    # trajectory evolved by the general transition law; the first
    # end-to-end discharge of the paper-canonical prop:flip-route)
    # Initial-condition selection theorem (row 20, user-approved Rule-18
    # addition 2026-07-11: both bistable attractors certified at ONE
    # economy and ONE equilibrium — dual-basin witness dualParams with the
    # loss-offset knife edge held at exact equality; every start in the
    # high basin yields the certified lock-in path, every start in the
    # low basin the certified wash-out path)
    'dualParams_initial_condition_selects',
    # Coupled Schur correction (row 21, updated 2026-07-27): the matrix arithmetic is
    # valid, but the modulus-2 leader premise is refuted on the current
    # carriers. The obstruction (historical row 22) was retired from the
    # headline set in round V (2026-09-15) and is no longer snapshotted. The
    # conditional low-delta purified wrapper is not promoted because it
    # consumes rather than constructs the decisive objective-geometry premises.
    # Equilibrium-feedback comparative statics (user-approved Rule-18
    # addition 2026-07-24): the pinned values are explicitly packaged as
    # upper-selector Stackelberg equilibria; the finite patience change
    # splits into direct + continuation feedback, lock-in value rises
    # strictly, its absorbing-state response has the resolvent identity,
    # and the Target value is invariant to Sender patience on the window.
    'eeCertB_equilibrium_feedback_decomposition',
    'eeCertB_equilibrium_lockin_strict',
    'eeCertB_lockin_amplification',
    ('eeCertB_VT_star_' + [char]0x03B2 + 'S_invariant'),
    # --- Welfare layer (rows 26-28, user-approved Rule-18 addition
    # 2026-07-13). Promoted because R-PAPER4 made the welfare verdict an
    # ABSTRACT-level claim; an abstract claim with no snapshot row is exactly
    # the drift Rule 18 exists to catch. Rows 26-27 are PARAMETRIC over every
    # FourGroup economy; row 28 is the witness-level exact margin.
    #
    # Row 26 - the political weights ARE the distortion: for every four-group
    # economy, U_S + U_T = plannerW + sum_g (theta_g - 1) * w_g. The wedge
    # between what the two governments jointly maximise and what a utilitarian
    # planner counts is the politically re-weighted group welfares, and
    # nothing else is.
    'KaempferLowenberg.FourGroup.plannerW_distortion',
    # Row 27 - the flip boundary: the sanctions lock-in corner (state maxed, full
    # defiance, sanctions maxed) is strictly planner-dominated by the zero
    # stationary point IFF (g_J - q_K) + (b_J - b_K) < kS + d_s, i.e. iff the
    # planner's per-period flow gain from holding the entrenched state falls
    # short of the per-period resource burn needed to sustain it. The welfare
    # verdict is therefore a checkable sign condition on interest-group
    # primitives, not a fixture of the calibration.
    'KaempferLowenberg.FourGroup.plannerW_lockin_dominated_iff',
    # Row 28 - the exact discounted inefficiency margin at the microfounded
    # witness, stated on the constructed top-selector equilibrium and its
    # derived Target/Sender action paths. The zero-sanction FEASIBLE path
    # raises discounted planner value by exactly
    # 23/(10(1-beta)) + 1/(1-beta/2), for every start x0 in [0,1] and every
    # beta in [0,1), with the start-state dependence cancelling.
    'fgc_planner_inefficiency_equilibrium',
    # --- P4-free persistence (rows 29-30, user-approved Rule-18 addition
    # 2026-08-09). Both rows exist because the manuscript asserts a division
    # of labour -- the Target combined chord P4 yields conclusion (vi), while
    # conclusions (i)-(iii) do not need it -- that until now had no formal
    # counterpart: every route to (i)-(iii) ran through
    # `JointPreferenceBasinTop`, which carries `target_prefers_sanctions` as a
    # mandatory field. An abstract claim with no snapshot row is exactly the
    # drift Rule 18 exists to catch.
    #
    # Row 29 - persistence from P1-P3 and P5 with P4 DELETED from the
    # hypotheses, over a general transition. `SenderPersistencePackage` is
    # `GeneralFPersistencePackage` minus `target_combined_chord` and nothing
    # else. The basin object it consumes is FREE-PARAMETRIC in (V_S, alpha),
    # exactly as `JointPreferenceBasinTop` is -- it is a kinematic condition,
    # not an equilibrium statement. The Rule-1 anchoring lives in the
    # TRAJECTORY theorem this row's proof calls,
    # `equilibriumTop_senderPersistenceF_long_run_nonDecreasing`, whose `E`
    # supplies a Bellman-optimal Target policy. What is absent is any
    # hypothesis on how the Target RANKS sanction levels. Do not read this
    # row as "the Sender alone": the Target's equilibrium policy is an
    # argument of the Sender's substituted objective. Strictly weaker
    # hypotheses than the row it sits beside -- a debundling, not a new
    # result.
    'standardCompliance_persistence_generalF_from_sender_package',
    # Row 30 - the primitive form: for every admissible member of the
    # general-F symbolic family, with NO arguments beyond the structure, an
    # equilibrium exists in the constructed carriers and every basin start
    # yields a confined path with a non-decreasing sanction sequence. The MS
    # certificate's two side conditions (strictly interior basin bottom,
    # strict placation margin) pay for shock entry and the myopic comparison
    # respectively, not for persistence. CORNER result: the realised sanction
    # is maximal at every date, so monotonicity is flat rather than a
    # state-dependent ratchet. Do not cite this row for an interior ratchet.
    'SymbolicEconomyF.persistence_generalF',
    # --- Equilibrium-anchored P4-free persistence (rows 31-32,
    # user-approved Rule-18 addition 2026-08-09). Rows 29-30 establish that
    # the Target combined chord is dispensable; these two make the Rule-1
    # discharge visible in the same statement rather than at the call site.
    # They follow the house pattern of
    # `equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing`, which
    # pairs a free-parametric basin theorem with an equilibrium-anchored
    # sibling in the same file.
    #
    # A 2026-08-09 referee round read the free-parametric layer as a Rule-1
    # defect. It is not: Rule 1 fences FIXED, hand-chosen policies, not
    # universally quantified ones, and `JointPreferenceBasinTop` -- the basis
    # of every other headline row here -- is equally free in (V_T, V_S, a).
    # What was genuinely missing was an in-file anchored form. Do not
    # "repair" the parametric layer by deleting it; that would weaken the
    # Rule-13 recovery check to its E-instance and break Rule 5.
    #
    # Row 31 - conclusions (i)-(iii) of thm:persistence along the path of an
    # ACTUAL feedback Stackelberg equilibrium, general transition, no Target
    # sanction-preference hypothesis, PLUS conclusion (iv): the per-period
    # Target-argmax certificate from `E.alpha_opt_top`. Strictly stronger
    # than the parametric theorem it specialises.
    'equilibriumTop_senderPersistenceF_long_run_nonDecreasing',
    # Row 32 - the same for the finite shock-entry leg (thm:shock's basin
    # arrival), again with the Target-argmax certificate attached along the
    # post-shock path. The exogenous shock phase is the Rule-1 transient
    # exception; the optimal dynamics resume when it ends.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 27 was `equilibriumTop_senderPersistenceF_temporary_shock_permanent_high`, now its sibling.
    'equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent',
    # --- Order-selected convergence (row 33, user-approved Rule-3/18 addition
    # 2026-08-15). The first headline row whose conclusion names WHICH rest
    # point an equilibrium path reaches, rather than only that it reaches one.
    #
    # Tier 1 of three, and deliberately the tier promoted: its only regularity
    # hypothesis is continuity of the realised rule on the basin, stated
    # directly. It does NOT assume dynamic argmax uniqueness (tier 2 derives
    # continuity from that), does not assume StrictAdjustment (tier 3 uses it to
    # identify the sanction limit with the state limit), and does not even need
    # the interval to lie in the physical state space. Promoting the weakest
    # tier keeps the mathematical requirement visible and separate from the
    # economic condition that happens to supply it.
    #
    # SCOPE, and the reason this row is not called attraction: the limit is
    # bound after the starting state and may depend on it. Two starts in one
    # basin need not share a limit. Whole-basin attraction is equivalent to the
    # basin holding a unique rest point
    # (MonotoneAttraction.attraction_iff_unique_fixedPoint) and is NOT claimed
    # here. Do not cite this row for an attractor.
    #
    # It does not dominate the baseline long-run theorem
    # `dynamicTopLockInPathF_tendsto_steadyState`, which assumes neither rule
    # monotonicity nor rule continuity and concludes less. Neither replaces the
    # other.
    'equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn',
    # --- Attraction on a derived interval (row 34, user-approved Rule-3/18
    # addition 2026-08-15). Row 33 gives ORDER SELECTION: each path converges to
    # an extremal steady state, which may differ across starting points. This row
    # gives a COMMON limit: every path from the interval reaches the SAME steady
    # state, and the realised sanction reaches it too.
    #
    # The interval is derived, not chosen: it runs from the basin pivot up to the
    # FIRST steady state of the closed loop above it. Uniqueness on that interval
    # — which `MonotoneAttraction.attraction_iff_unique_fixedPoint` shows is
    # exactly what a common limit requires — therefore holds by construction
    # rather than by assumption.
    #
    # Hypotheses are weaker than row 33's siblings carry elsewhere: an invariant
    # interval, a monotone continuous realised rule, and StrictAdjustment for the
    # sanction half only. NO level condition, NO sanction floor, NO persistence
    # package. The level-condition and argmax-uniqueness forms are corollaries.
    #
    # SCOPE. The interval may be a single point: the theorem permits x_s = xbar,
    # and ruling that out needs `G_E(xbar) != xbar`, which the persistence
    # package's own basin cannot supply (there pivot and floor coincide). Nothing
    # establishes x_s < 1 — at the one economy witnessing positive length, x_s IS
    # the corner. Do not cite this row for an interior steady state.
    'equilibriumTop_attraction_on_derived_interval_of_invariant',
    # --- The dividing line derived from the closed loop (row 35, user-approved
    # Rule-3/18 addition 2026-08-15, promoted together with the paper claim it
    # backs). Rows 33 and 34 take their interval from outside — a certified
    # basin, a pivot, a chosen endpoint. This row derives the BOUNDARY itself.
    #
    # Given two named long-run states, a certified wash-out region reaching up to
    # xL, a certified ratchet region reaching down to xH, and NOTHING AT ALL
    # about the sign of the closed-loop gap in between, two steady states t <= t'
    # are extracted from the equilibrium closed loop as
    #   t  = inf { x in [xL,xH] : x <= G_E(x) }   (erosion stops here first)
    #   t' = sup { x in [xL,xH] : G_E(x) <= x }   (building stops here last)
    # every path below t washes out to the low state, every path above t'
    # ratchets to the high one, and t = t' exactly when the middle region holds a
    # single steady state.
    #
    # Hypotheses are weaker than rows 33/34 on two axes that matter. NO
    # monotonicity of the realised rule anywhere — which is the point, since
    # between two certified basins monotonicity is exactly what is unknown. NO
    # StrictAdjustment. What remains: continuity of the realised rule (Round 4A
    # discharges it from DynamicArgmaxUnique), two endpoint inequalities on the
    # existing closed loop, and feasibility bounds restating F_mem.
    #
    # SCOPE. The gap [t, t'] is NOT claimed empty at any economy, including the
    # dual-basin one — `MonotoneAttraction.derivedThresholds_can_differ` exhibits
    # a continuous map fixing a whole subinterval, so the question is not
    # vacuous. Nothing bounds where t sits, and nothing here makes it interior.
    # The conclusion tracks the STATE path; the realised sanction is not carried
    # to the limit. Do not cite this row for a unique dividing line.
    'equilibriumTop_derived_dual_basins',
    # First NON-AFFINE inhabitant of the full compliance certificate (row 36,
    # user-approved Rule-3/18 addition 2026-08-21). Closes the Rule-9B
    # generality gap: `StandardComplianceLocalCoreCertificate` became general
    # in F on 2026-08-20b, and until now every one of its five instances
    # discharged the sanction chords by rewriting F to affineF -- so the class
    # was certified inhabited and NOT certified more general than its affine
    # predecessor. quadBumpF is refuted as affine at EVERY weight
    # (`quadBumpF_ne_affineF`), and the two chord rates separate strictly:
    # dlo = 47/100 < 53/100 = d, which a lower and upper chord at one rate
    # could not do. Full conclusion strength -- basin invariance, the free
    # sanction floor s-bar = 1/2, the pivot floor, sanction monotonicity, the
    # per-period Target-argmax certificate, statewise dominance, and finite
    # shock entry.
    #
    # SCOPE (Rule 9A). Licenses existence, and refutes "the certificate route
    # needs an affine transition". NOT evidence of genericity; 47/100 and
    # 53/100 are properties of this economy, not of the theory.
    'qbCert_three_goals_generalF',
    # Rows 38-40 (user-approved 2026-09-04, doc 49 section 2): the placable-Sender
    # class, since round AV (doc 104) the chord economy with both stage payoffs
    # abstract. Row 38 is the class statement: on every chord economy, given
    # one inequality stated as a hypothesis, both continuation channels change equilibrium behaviour at a
    # composed top-selector equilibrium with both values Banach-constructed.
    # Row 39 is the same unconditionally at quadDiagF, proved not affine at any
    # rate (Rule 9B generality, fenced). Row 40 is the general theorem behind
    # row 38: single crossing at the value plus state-local uniqueness give the
    # upper dynamic response monotone in the state, with zero model assumptions.
    # Round BC (2026-09-29): rows 32 and 35 moved to the relief extension `ChordEconomyRelief`
    # (doc 110 R5, user-approved), since they read the Target's upper rates.
    'ChordEconomyRelief.both_channels_active_of_margin_net',
    'placableQuadDiag_both_channels_active',
    ('' + [char]0x03C3 + '_dyn_top_monotoneOn_x_of_singleCrossing'),
    # Rows 41-42 (2026-09-04, doc 56, user-approved). Row 41: the re-solved
    # myopic-versus-forward-looking separation on the chord economy, general
    # in F and in the payoffs. Row 42: the affine member's closed loop is a 43/46-contraction, so
    # activation of both channels does not deliver hysteresis there.
    'ChordEconomyRelief.myopic_dynamic_equilibrium_separation_net_of_margin',
    'placableAffine_unique_attracting_state',
    # Rows 43-44 (2026-09-05, doc 62, user-approved). Row 43: the Target-only
    # reading on the chord economy, general in F and in the payoffs. Row 44: one equilibrium,
    # both regimes, both episodes, at the affine dual-basin economy.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 37 was `ChordEconomy.target_only_regime_generalF`, now its sibling.
    'ChordEconomyRelief.target_only_regime_net_core',
    'dualParams_two_sided_regimes',
    # Rows 45-46 (2026-09-05, doc 65, user-approved). Row 45: the four cells on
    # every member of the enriched subclass ChordEconomyCs, general in F --
    # the paper's Theorem 1. Row 46: the Sender-only reading behind it.
    'ChordEconomyCs.four_cell_net_generalF',
    'ChordEconomyCs.sender_only_regime_generalF',
    # Row 47 (round Q2, 2026-09-11; doc 85 S3): both channels active on the
    # enriched subclass under the rally and relief margins alone, with no stage
    # flip -- the Target channel through a small compliance at the equilibrium
    # value.
    'ChordEconomyCs.both_channels_active_of_relief_net',
    # Row 48 (round AQ, 2026-09-23; doc 102 J3): the sharp defiance side of the bracket -- at any Target value of lower slope g and any Sender carrier value, defiance is the strict unique optimum when c - l mu/k < beta_T d_lo g; general in F.
    'ChordEconomy.targetObj_strictAntiOn_of_sharp',
    # Row 49 (round AQ): the relief equilibrium under a general transition -- the forward-looking Target complies at the zero level and the realised sanction is zero at every state, under placability and the relief side.
    'ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero',
    # Row 50 (round AQ): on the relief side defiance is not a Target best reply at the defiance-profile values; general in F.
    'ChordEconomyCs.defiance_not_maxOn_of_relief_side',
    # Row 51 (round AQ): at tight chords, zero moduli and no rally the two sides of the bracket read D < beta_T delta g_T and its reverse -- the affine exact threshold as the point where the window closes.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 45 was `ChordEconomyCs.collapse_sides`, now its sibling.
    'ChordEconomyCs.collapse_sides''',
    # Row 52 (round AR): under the unrefined loss-offset margin every equilibrium with compliance nonincreasing and sanction nondecreasing in the state is the constructed defiance equilibrium; general in F.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 46 was `ChordEconomy.unique_equilibrium_of_monotone_class`, now its sibling.
    'ChordEconomy.unique_equilibrium_of_rule_monotone',
    # Row 53 (round AM; doc 100 H7): in every equilibrium whose Target policy is nonincreasing in the state the realised sanction is at least the stage optimum at defiance plus the continuation wedge; general in F and in the payoffs.
    'ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone',
    # Row 54 (round AE; doc 98 G9): no date-zero transfer makes an imposed relief spell acceptable to both governments at the constructed values under the loss-offset margin.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 48 was `ChordEconomy.no_date_zero_transfer_supports_relief`, now its sibling.
    'ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance',
    # Row 55 (round AE; doc 98 G9): branch invariance -- two members equal on the Sender's data have the same forward-looking realised sanctions at every date.
    # Re-pinned round BC, 2026-09-29 (doc 111 §5, user-approved): row 49 was `ChordEconomy.dynamicSanction_eq_of_sender_side_eq`, now its sibling.
    'defiance_branch_invariance_generalF',
    # Row 56 (round AG; doc 98 G9): no pure history-dependent Target deviation improves on the equilibrium's own play, for every top-selector equilibrium.
    'FeedbackStackelbergEquilibriumTop.leader_optimal_against_history_deviation_top',
    # Row 57 (round AG; doc 98 G9): two welfare completions preserving government payoffs and reversing the ranking of the constructed regimes at every planner discount.
    'PlacableEconomyFcs.exists_completions_reversing_regime_ranking',
    # Rows 52-54 (round BC, 2026-09-29; doc 111 §5, user-approved). Row 52: the Target's
    # security bound -- under the unrefined loss-offset margin every top-selector equilibrium
    # gives the Target at least its payoff under permanent relief, the minmax over pure
    # Sender sequences. Row 53: patience on existence -- a full-defiance equilibrium at one
    # Target discount factor implies one at every higher factor, within a family that differs
    # only in beta_T. Row 54: the defiance core over an arbitrary economy -- every equilibrium
    # with a nondecreasing realised rule has the Target defying, from chords, stage rates and
    # the unrefined margin alone.
    'ChordEconomy.reliefPayoff_le_V_T',
    ('ChordEconomyCs.exists_defiance_equilibrium_mono_' + [char]0x03B2 + 'T'),
    'FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone',
    # Rows 55-59 (manuscript rebuild, 2026-10-01; author decision D4: pin the forms the main
    # text states). 55-56: the Target's security value in pure history-dependent strategies,
    # minmax and maxmin (round BD). 57: balance inherited by a more patient Target (round BD).
    # 58: no top-selector equilibrium has a sanction rule zero at every state. 59: the exact
    # collapse threshold for existence of a full-defiance equilibrium, away from equality.
    'ChordEconomy.reliefPayoff_isLeast_history',
    'ChordEconomy.reliefPayoff_isGreatest_history',
    ('ChordEconomyCs.SameBut' + [char]0x03B2 + 'T.balance_of_balance'),
    'ChordEconomy.no_zero_rule_equilibrium',
    # Re-pinned renovation round BJ-1, 2026-10-07 (plan item BJ1.6, author decision 7): row 59 was
    # `ChordEconomyCs.collapse_equilibrium_threshold`, which carries beta_T != beta*; now the attained form,
    # which covers the threshold itself.
    'ChordEconomyCs.collapse_equilibrium_threshold_le',
    # Rows 60-63 (round W, 2026-10-15; the author: welfare in general abstract form). 60: rescaling
    # one group ranks two paths for the planner without changing the game. 61: zero sanctions are
    # planner-optimal when the first unit of sanction does not pay socially. 62: two
    # representations reverse the welfare ranking of the four constructed equilibria on the class.
    # 63: persistent play is planner-optimal for a representation whose welfare is U_S.
    'Welfare.InterestGroupRep.exists_rescaleS_ranks',
    'Welfare.zeroSanction_planner_optimal',
    'ChordEconomyCs.exists_reps_reversing_regime_ranking',
    'ChordEconomy.planner_efficient_rep_at_policy_zero',
    # Rows 64-65 (round W2, 2026-10-16; the author's layout decisions D1-D5: the main text compares
    # the myopic case 00 with the forward-looking case 11). 64: the stage-form regime separation,
    # the main theorem. 65: two representations reverse the welfare ranking of 00 and 11.
    'ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage',
    'ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking'
)
$openLine = 'open Sanctions Sanctions.Examples Sanctions.AbstractGame.Params Sanctions.AbstractGame.ShockedParams'
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')

# --- 1. Generate the elaboration probe file -------------------------------
# Keep the probe inside the project.  With newer elan/lake releases, a source
# file under the system TEMP directory can trigger project/toolchain discovery
# from that external path and an unnecessary network lookup, even though the
# pinned toolchain and built library are already available locally.
$tmp = Join-Path $root (".headline_snapshot_{0}.lean" -f $PID)
$sb = New-Object System.Text.StringBuilder
[void]$sb.AppendLine('import Sanctions')
[void]$sb.AppendLine($openLine)
# doc 70 (D3, user-approved 2026-09-08): the rendering policy is fixed here
# and in scripts/contract_probe.lean.template. Names print fully qualified, so
# no hash depends on $openLine any more; proof arguments print as `⋯`.
[void]$sb.AppendLine('set_option pp.fullNames true')
[void]$sb.AppendLine('set_option pp.deepTerms true')
[void]$sb.AppendLine('set_option pp.maxSteps 1000000')
[void]$sb.AppendLine('set_option pp.proofs false')
foreach ($h in $headlines) {
    [void]$sb.AppendLine("#check @$h")
    [void]$sb.AppendLine("#print axioms $h")
}

# --- Rule-18 extension (2026-08-11): pin the DATA the headlines denote ------
# The rows above hash each headline's fully-qualified name and elaborated
# TYPE. That fences renames, vanished theorems, and statement drift -- but it
# is blind to the definitions the statement mentions. Editing a witness
# constant (say `eeCertParams.beta_S` from 1/2 to 3/5) leaves every type-hash
# byte-identical while changing what the theorem asserts about.
#
# So we additionally pin, for every economy instance a headline transitively
# mentions, the pretty-printed VALUE of every non-Prop project constant in its
# closure. Proofs are excluded deliberately: a proof refactor does not change
# what an economy IS, and pinning proof terms would make the fence brittle
# against exactly the edits it should tolerate.
$pinProbe = @'
open Lean Elab Command Meta

partial def snapClosure (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work : List Name := [start]
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? then cs := cs ++ v.getUsedConstants
        for c in cs do
          if (`Sanctions).isPrefixOf c then work := c :: work
  return seen

def snapPinnedTypes : List Name :=
  [`Sanctions.AbstractGame.Params,
   `Sanctions.AbstractGame.ShockedParams,
   `Sanctions.Examples.SymbolicEconomyF,
   `Sanctions.Examples.SymbolicEconomy,
   `Sanctions.KaempferLowenberg.FourGroup,
   -- doc 65 (D3): the placable family and its enriched subclass. Pinning an
   -- instance hashes its data closure, which includes the structure's
   -- constructor type -- so a field added to the family (the Mcs episode of
   -- doc 63, invisible to the type-hash rows) now fails gate 5.
   `Sanctions.Examples.PlacableEconomyF,
   `Sanctions.Examples.PlacableEconomyFcs,
   -- doc 104 (round AX): the chord economy, which the placable headline rows
   -- bind over since round AV, and its enriched subclass.
   `Sanctions.Examples.ChordEconomy,
   `Sanctions.Examples.ChordEconomyCs]

def snapEconomyDeps (env : Environment) (n : Name) : Array Name := Id.run do
  let mut hits : Array Name := #[]
  for d in (snapClosure env n).toList do
    if let some ci := env.find? d then
      if let .const tn _ := ci.type.getAppFn then
        if snapPinnedTypes.contains tn then hits := hits.push d
  return hits

def snapDataClosure (env : Environment) (n : Name) : MetaM (Array Name) := do
  let mut hits : Array Name := #[]
  for d in (snapClosure env n).toList do
    if let some ci := env.find? d then
      unless (<- isProp ci.type) do hits := hits.push d
  return hits.qsort (fun a b => a.toString < b.toString)

elab "#pinSet " ids:ident+ : command => do
  let env <- getEnv
  let mut economies : NameSet := {}
  for id in ids do
    let n <- liftCoreM <| realizeGlobalConstNoOverload id
    for e in snapEconomyDeps env n do economies := economies.insert e
  let ecoList := economies.toList.toArray.qsort (fun a b => a.toString < b.toString)
  let dataArrays <- liftTermElabM do
    let mut acc : Array (Array Name) := #[]
    for e in ecoList do acc := acc.push (<- snapDataClosure env e)
    return acc
  let mut data : NameSet := {}
  for arr in dataArrays do
    for d in arr do data := data.insert d
  let dataList := data.toList.toArray.qsort (fun a b => a.toString < b.toString)
  for e in ecoList do logInfo m!"PINECON {e}"
  -- NOTE (2026-09-08, doc 70 D3): the probe file sets pp.fullNames true (and
  -- pp.deepTerms / pp.maxSteps / pp.proofs) at the top, so every hash below
  -- is independent of $openLine. Before that rebaseline the hashes depended
  -- on the `open` line (doc 68).
  liftTermElabM do
    for d in dataList do
      match env.find? d with
      | some ci =>
        let vs <- match ci.value? with
          | some v => do let f <- ppExpr v; pure f.pretty
          | none   => pure "<opaque>"
        let ts <- do let f <- ppExpr ci.type; pure f.pretty
        logInfo m!"PINVAL-BEGIN {d}
{ts}
:=
{vs}
PINVAL-END"
      | none => logInfo m!"PINVAL-BEGIN {d}
<missing>
PINVAL-END"

'@
[void]$sb.AppendLine($pinProbe)
# doc 68 L9 / doc 70 F-2: the contract-root and evidence extractors live in ONE
# file shared with scripts/Test-ContractFence.ps1, so the focused test cannot
# drift from this gate.
[void]$sb.AppendLine((Get-Content (Join-Path $PSScriptRoot 'contract_probe.lean.template') -Raw))
[void]$sb.AppendLine('#pinSet ' + ($headlines -join ' '))
# round O (doc 82 P5): the structural fingerprint of every headline.
[void]$sb.AppendLine('#structuralRoots ' + ($headlines -join ' '))
# Round AX (doc 104 §8, sign-off M7): the bodies of the definitions a headline
# names. The structural fingerprint serialises a headline's TYPE, in which a
# definition such as `LossOffset`, `KS`, `gT`, `A`, `vertex` or `Placable`
# appears only by name, so redefining its body moved no row. This probe walks,
# from the project constants in each headline's elaborated type, the closure of
# project DEFINITIONS through their values (theorems, inductives, constructors
# and axioms are not followed; proofs inside a body print as `⋯`), and
# serialises every body with the same alpha-invariant `structSer` as the
# fingerprint. The generator hashes one record per headline into the section
# "Definition bodies named by the headlines"; gate 5 treats any change there as
# drift, like every change outside the headline table.
$bodyProbe = @'
partial def bodyClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work : List Name := roots
  repeat
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      match env.find? n with
      | some (.defnInfo dv) =>
        seen := seen.insert n
        for c in dv.value.getUsedConstants do
          if (`Sanctions).isPrefixOf c then work := c :: work
      | _ => pure ()
  return seen

elab "#bodyRoots " ids:ident+ : command => do
  let env <- getEnv
  for id in ids do
    let n <- liftCoreM <| realizeGlobalConstNoOverload id
    let some ci := env.find? n | throwError "BODY-MISSING {n}"
    let roots := ci.type.getUsedConstants.toList.filter fun c => (`Sanctions).isPrefixOf c
    let defs := (bodyClosure env roots).toList.toArray.qsort (fun a b => a.toString < b.toString)
    let lines <- liftTermElabM do
      let mut acc : Array String := #[]
      for d in defs do
        match env.find? d with
        | some (.defnInfo dv) =>
          let lvls := (List.range dv.levelParams.length).map fun i =>
            Level.param (Name.mkSimple s!"u{i}")
          let v := dv.value.instantiateLevelParams dv.levelParams lvls
          let s <- structSer #[] v
          acc := acc.push s!"{d} := {s}"
        | _ => pure ()
      return acc
    logInfo m!"BODY-BEGIN {n} {defs.size}
{"\n".intercalate lines.toList}
BODY-END"
'@
[void]$sb.AppendLine($bodyProbe)
[void]$sb.AppendLine('#bodyRoots ' + ($headlines -join ' '))
# The contract roots: every economy structure, every certificate or package
# structure a headline row or a manuscript statement binds over, the
# equilibrium record, the profile, and the maintained transition predicate.
# Adding a root is a Rule-18 event (it changes the committed anchor); removing
# one is too. Names resolve under $openLine.
$contractRoots = @(
    'Sanctions.AbstractGame.Params',
    'Sanctions.AbstractGame.ShockedParams',
    'Sanctions.AbstractGame.CubeData',
    'Sanctions.AbstractGame.Params.StrictAdjustment',
    'Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop',
    'Sanctions.AbstractGame.Params.ValueClass2',
    'Sanctions.AbstractGame.Params.JointPreferenceBasinTop',
    'Sanctions.AbstractGame.Params.JointPreferenceBasinLow',
    'Sanctions.AbstractGame.Params.OneSidedSanctionPreferenceThresholds',
    'Sanctions.AbstractGame.Params.OneSidedSanctionLowBasinPreferenceThresholds',
    'Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate',
    'Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate_MS',
    'Sanctions.AbstractGame.Params.StandardComplianceLocalCertificate',
    'Sanctions.AbstractGame.Params.StandardComplianceLocalCertificateC1',
    'Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur',
    'Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur_MS',
    'Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate',
    'Sanctions.AbstractGame.Params.RegularEconomyCertificateC1ComplianceCore',
    'Sanctions.AbstractGame.Params.RegularEconomyCertificateC1Compliance',
    'Sanctions.AbstractGame.Params.SenderPersistencePackage',
    'Sanctions.AbstractGame.Params.GeneralFPersistencePackage',
    'Sanctions.Mechanism.ContinuationProfile',
    'Sanctions.Examples.SymbolicEconomy',
    'Sanctions.Examples.SymbolicEconomyF',
    # Renovation closing round (2026-10-08, author decision): the persistence core that row 30
    # is a corollary of since BJ4.4.
    'Sanctions.Examples.SymbolicEconomyFPersist',
    'Sanctions.Examples.PlacableEconomyF',
    'Sanctions.Examples.PlacableEconomyFcs',
    # doc 104 (round AX): the chord economy and its enriched subclass, which the
    # placable headline rows bind over since round AV. A field added to either
    # changes a row here.
    'Sanctions.Examples.ChordEconomy',
    'Sanctions.Examples.ChordEconomyCs',
    # Renovation closing round (2026-10-08, author decision): the two-sided class that BJ3.1 split
    # off the base (its curvature fields left the pinned ChordEconomy) and the relief class between
    # it and ChordEconomyCs, whose own fields (k_hi, the placation rate, the relief margins) were
    # not fenced.
    'Sanctions.Examples.ChordEconomyTwoSided',
    'Sanctions.Examples.ChordEconomyRelief',
    'Sanctions.KaempferLowenberg.FourGroup',
    # doc 70 (D4, user-approved 2026-09-08): predicate bodies and selector
    # definitions. A projection type that mentions `D.IsInvariant` does not
    # fingerprint the body of that predicate; a theorem type that mentions
    # `σ_dyn_top` does not fingerprint how the selector is defined. Each of
    # these is a definition hashed by its body (the `else` branch of the elab).
    'Sanctions.AbstractGame.Params.ValueClass2.IsInvariant',
    'Sanctions.AbstractGame.Params.DynamicArgmaxUnique',
    # Renovation closing round (2026-10-08, author decision): the bodies of the three conditions
    # Phase D introduced (BJ4.3, BJ2.2, BJ5.1).
    'Sanctions.AbstractGame.Params.DynamicArgmaxUniqueOnI',
    'Sanctions.Examples.ChordEconomy.PlacationCeiling',
    'Sanctions.AbstractGame.Params.StaticSelectorContinuous',
    'Sanctions.AbstractGame.Params.TargetArgmaxUnique',
    'Sanctions.AbstractGame.Params.ValueLipschitzWith',
    'Sanctions.AbstractGame.Params.SanctionLowerChordWith',
    'Sanctions.AbstractGame.Params.TargetCombinedChordOn',
    'Sanctions.AbstractGame.Params.SenderPersistenceBasinTop',
    'Sanctions.AbstractGame.Params.ContinuationChangesSenderChoiceAt',
    'Sanctions.AbstractGame.Params.ContinuationChangesTargetChoiceAt',
    'Sanctions.AbstractGame.Params.TransitionStateLipschitzWith',
    'Sanctions.AbstractGame.Params.TransitionStateLipschitzOnWith',
    'Sanctions.AbstractGame.Params.senderDynObjective',
    'Sanctions.AbstractGame.Params.dynamicArgmaxSet',
    'Sanctions.AbstractGame.Params.σ_dyn_top',
    'Sanctions.AbstractGame.Params.dynamicTopRealizedRule',
    'Sanctions.AbstractGame.Params.dynamicEquilibriumRule',
    'Sanctions.AbstractGame.Params.joint_T_top_integrand',
    'Sanctions.IntervalDominanceOrder.IDOFamilyOn',
    'Sanctions.TransitionChords.SanctionLowerChord',
    'Sanctions.TransitionChords.SanctionUpperChord',
    'Sanctions.TransitionChords.CornerStateChord',
    'Sanctions.TransitionChords.SanctionSemiconcave',
    'Sanctions.Semiconcave.StateChordBandAll',
    'Sanctions.MixedChordBound',
    'Sanctions.Semiconcave.SemiconcaveOnSet',
    'Sanctions.Semiconcave.SemiconvexOnSet',
    'Sanctions.Semiconcave.JointSemiconcaveOn',
    'Sanctions.MilgromShannon.IncreasingDifferencesOn',
    'Sanctions.MilgromShannon.SingleCrossingOn'
)
# doc 70 (C-7): the evidence declarations the hypothesis census cites, hashed
# by type so a status recorded against one becomes stale when its row moves.
$evidenceRoots = @(Get-Content (Join-Path $root 'docs/census/roots-evidence.txt') |
    ForEach-Object { ($_ -split '#')[0].Trim() } | Where-Object { $_ -ne '' })
[void]$sb.AppendLine('#contractRoots ' + ($contractRoots -join ' '))
[void]$sb.AppendLine('#evidenceRoots ' + ($evidenceRoots -join ' '))
[System.IO.File]::WriteAllText($tmp, $sb.ToString(),
    (New-Object System.Text.UTF8Encoding($false)))

# --- 2. Elaborate against the built library -------------------------------
Push-Location $root
$prevOut = [Console]::OutputEncoding
try {
    # Lean emits UTF-8. Without this, PowerShell 5.1 decodes it with the
    # console codepage, so every non-ASCII identifier arrives as mojibake and
    # the hashes below are hashes of mangled text -- deterministic, but they
    # would all move if the machine's codepage ever changed. Worse, the
    # mangling can merge two Lean messages onto one captured line, which is
    # what silently dropped a headline row on 2026-08-11.
    [Console]::OutputEncoding = New-Object System.Text.UTF8Encoding($false)
    $out = & lake env lean $tmp
    $leanExit = $LASTEXITCODE
    $leanVersion = (& lake env lean --version) -join ' '
} finally {
    [Console]::OutputEncoding = $prevOut
    Pop-Location
    Remove-Item $tmp -Force -ErrorAction SilentlyContinue
}
if ($leanExit -ne 0) {
    Write-Host "FAIL: lake env lean exited $leanExit (vanished/renamed headline?)."
    Write-Host ($out -join "`n")
    exit 1
}

# --- 3. Parse: each '#check' block is terminated by its axioms record -----
# NOTE: `#print axioms` output WRAPS long axiom lists across lines
# ("[propext,\n Classical.choice,\n Quot.sound]"), so an axioms record is
# accumulated from its "'name' depends on axioms: [" opener until the
# line containing the closing "]".
$rows = @()
$block = New-Object System.Collections.Generic.List[string]
$sha = [System.Security.Cryptography.SHA256]::Create()
$axName = $null
$axBuf = New-Object System.Text.StringBuilder
foreach ($line in @($out)) {
    if ($null -ne $axName) {
        # inside a wrapped axioms record
        [void]$axBuf.Append(' ').Append($line.Trim())
        if ($line -notmatch '\]') { continue }
        $axText = [regex]::Match($axBuf.ToString(), '\[(?<ax>[^\]]*)\]').Groups['ax'].Value
        $axioms = @($axText -split ',\s*' | ForEach-Object { $_.Trim() } | Where-Object { $_ -ne '' })
        $typeText = (($block -join ' ') -replace '\s+', ' ').Trim()
        $bytes = [System.Text.Encoding]::UTF8.GetBytes($typeText)
        $hash = ([System.BitConverter]::ToString($sha.ComputeHash($bytes)) -replace '-', '').ToLowerInvariant()
        $rows += [pscustomobject]@{ Name = $axName; TypeHash = $hash; Axioms = $axioms }
        $block.Clear(); $axName = $null; [void]$axBuf.Clear()
        continue
    }
    # NOT anchored at line start: Lean's messages can arrive merged onto one
    # captured line. Anything preceding the record belongs to the #check block.
    # Non-greedy up to the record's own closing quote: a Lean name may itself
    # end in a prime (`collapse_sides'`, row 45 since round BC), so `[^']+`
    # would drop the record.
    $m = [regex]::Match($line, "'(?<name>.+?)' depends on axioms: ")
    if ($m.Success) {
        if ($m.Index -gt 0) { [void]$block.Add($line.Substring(0, $m.Index)) }
        $axName = $m.Groups['name'].Value
        [void]$axBuf.Append($line.Substring($m.Index))
        if ($line -match '\]') {
            # single-line record: finalize immediately via the same path
            $axText = [regex]::Match($axBuf.ToString(), '\[(?<ax>[^\]]*)\]').Groups['ax'].Value
            $axioms = @($axText -split ',\s*' | ForEach-Object { $_.Trim() } | Where-Object { $_ -ne '' })
            $typeText = (($block -join ' ') -replace '\s+', ' ').Trim()
            $bytes = [System.Text.Encoding]::UTF8.GetBytes($typeText)
            $hash = ([System.BitConverter]::ToString($sha.ComputeHash($bytes)) -replace '-', '').ToLowerInvariant()
            $rows += [pscustomobject]@{ Name = $axName; TypeHash = $hash; Axioms = $axioms }
            $block.Clear(); $axName = $null; [void]$axBuf.Clear()
        }
    } else {
        [void]$block.Add($line)
    }
}
if ($rows.Count -ne $headlines.Count) {
    Write-Host ("FAIL: parsed {0} rows, expected {1}." -f $rows.Count, $headlines.Count)
    exit 1
}

# --- 3b. Parse the pinned economy data -------------------------------------
$pinEcon = @()
$pinRows = @()
$curName = $null
$curBuf = New-Object System.Collections.Generic.List[string]
foreach ($line in @($out)) {
    if ($line -match '^PINECON\s+(?<n>\S+)\s*$') { $pinEcon += $Matches['n']; continue }
    if ($line -match '^PINVAL-BEGIN\s+(?<n>\S+)\s*$') {
        $curName = $Matches['n']; $curBuf.Clear(); continue
    }
    if ($line -match '^PINVAL-END\s*$') {
        if ($curName) {
            $text = (($curBuf -join ' ') -replace '\s+', ' ').Trim()
            $b = [System.Text.Encoding]::UTF8.GetBytes($text)
            $h = ([System.BitConverter]::ToString($sha.ComputeHash($b)) -replace '-', '').ToLowerInvariant()
            $pinRows += [pscustomobject]@{ Name = $curName; ValueHash = $h }
            $curName = $null; $curBuf.Clear()
        }
        continue
    }
    if ($curName) { [void]$curBuf.Add($line) }
}
if ($pinRows.Count -eq 0) {
    Write-Host 'FAIL: the pin probe produced no PINVAL records (metaprogram broken?).'
    exit 1
}

# --- 3c. Parse the contract roots (doc 68, L9) --------------------------------
$contractRows = @()
$curName = $null
$curBuf = New-Object System.Collections.Generic.List[string]
foreach ($line in @($out)) {
    if ($line -match '^CONTRACT-BEGIN\s+(?<n>\S+)\s*$') {
        $curName = $Matches['n']; $curBuf.Clear(); continue
    }
    if ($line -match '^CONTRACT-END\s*$') {
        if ($curName) {
            $text = (($curBuf -join ' ') -replace '\s+', ' ').Trim()
            $b = [System.Text.Encoding]::UTF8.GetBytes($text)
            $h = ([System.BitConverter]::ToString($sha.ComputeHash($b)) -replace '-', '').ToLowerInvariant()
            $contractRows += [pscustomobject]@{ Name = $curName; ContractHash = $h }
            $curName = $null; $curBuf.Clear()
        }
        continue
    }
    if ($curName) { [void]$curBuf.Add($line) }
}
if ($contractRows.Count -lt $contractRoots.Count) {
    Write-Host ("FAIL: {0} contract records for {1} roots (a root vanished or the probe broke)." -f $contractRows.Count, $contractRoots.Count)
    exit 1
}
$contractRows = @($contractRows | Sort-Object Name)

# --- 3d. Parse the evidence declarations (doc 70, C-7) -------------------------
$evidenceRows = @()
$curName = $null
$curBuf = New-Object System.Collections.Generic.List[string]
foreach ($line in @($out)) {
    if ($line -match '^EVIDENCE-BEGIN\s+(?<n>\S+)\s*$') {
        $curName = $Matches['n']; $curBuf.Clear(); continue
    }
    if ($line -match '^EVIDENCE-END\s*$') {
        if ($curName) {
            $text = (($curBuf -join ' ') -replace '\s+', ' ').Trim()
            $b = [System.Text.Encoding]::UTF8.GetBytes($text)
            $h = ([System.BitConverter]::ToString($sha.ComputeHash($b)) -replace '-', '').ToLowerInvariant()
            $evidenceRows += [pscustomobject]@{ Name = $curName; TypeHash = $h }
            $curName = $null; $curBuf.Clear()
        }
        continue
    }
    if ($curName) { [void]$curBuf.Add($line) }
}
if ($evidenceRows.Count -ne $evidenceRoots.Count) {
    Write-Host ("FAIL: {0} evidence records for {1} roots (a cited declaration vanished)." -f $evidenceRows.Count, $evidenceRoots.Count)
    exit 1
}
$evidenceRows = @($evidenceRows | Sort-Object Name)
# No hashed text may be elided for depth or size (pp.deepTerms / pp.maxSteps
# guarantee it; `⋯` from pp.proofs false is a proof argument and is allowed
# only where a proof term sits inside a statement). Fail if the probe output
# carries the deep-term ellipsis marker in a headline #check block.
if (@($out | Where-Object { $_ -match 'maxSteps' }).Count -gt 0) {
    Write-Host 'FAIL: the pretty-printer hit pp.maxSteps; raise it in the probe.'
    exit 1
}

# --- 3e. Parse the structural fingerprints (round O, doc 82 P5) ---------------
# One `STRUCT-BEGIN name` / serialisation / `STRUCT-END` record per headline,
# hashed like the other records and attached to its headline row. A headline
# without a record fails closed.
$structRows = @{}
$curName = $null
$curBuf.Clear()
foreach ($line in @($out)) {
    if ($line -match '^STRUCT-BEGIN\s+(?<n>\S+)\s*$') {
        $curName = $Matches['n']; $curBuf.Clear(); continue
    }
    if ($line -match '^STRUCT-END\s*$') {
        if ($curName) {
            $text = (($curBuf -join ' ') -replace '\s+', ' ').Trim()
            $b = [System.Text.Encoding]::UTF8.GetBytes($text)
            $structRows[$curName] = ([System.BitConverter]::ToString($sha.ComputeHash($b)) -replace '-', '').ToLowerInvariant()
            $curName = $null; $curBuf.Clear()
        }
        continue
    }
    if ($curName) { [void]$curBuf.Add($line) }
}
foreach ($r in $rows) {
    if (-not $structRows.ContainsKey($r.Name)) {
        Write-Host ("FAIL: no structural fingerprint record for headline {0}." -f $r.Name)
        exit 1
    }
    $r | Add-Member -NotePropertyName StructHash -NotePropertyValue $structRows[$r.Name]
}

# --- 3f. Parse the definition bodies (round AX, doc 104 §8, sign-off M7) ------
# One `BODY-BEGIN name count` / one line per definition / `BODY-END` record per
# headline. A headline without a record fails closed.
$bodyRows = @{}
$bodyCounts = @{}
$curName = $null
$curBuf.Clear()
foreach ($line in @($out)) {
    if ($line -match '^BODY-BEGIN\s+(?<n>\S+)\s+(?<c>\d+)\s*$') {
        $curName = $Matches['n']; $bodyCounts[$curName] = [int]$Matches['c']; $curBuf.Clear(); continue
    }
    if ($line -match '^BODY-END\s*$') {
        if ($curName) {
            $text = (($curBuf -join ' ') -replace '\s+', ' ').Trim()
            $b = [System.Text.Encoding]::UTF8.GetBytes($text)
            $bodyRows[$curName] = ([System.BitConverter]::ToString($sha.ComputeHash($b)) -replace '-', '').ToLowerInvariant()
            $curName = $null; $curBuf.Clear()
        }
        continue
    }
    if ($curName) { [void]$curBuf.Add($line) }
}
foreach ($r in $rows) {
    if (-not $bodyRows.ContainsKey($r.Name)) {
        Write-Host ("FAIL: no definition-body record for headline {0}." -f $r.Name)
        exit 1
    }
    $r | Add-Member -NotePropertyName BodyHash -NotePropertyValue $bodyRows[$r.Name]
    $r | Add-Member -NotePropertyName BodyCount -NotePropertyValue $bodyCounts[$r.Name]
}

# --- 4. Rule-10 axiom gate --------------------------------------------------
$dirty = @($rows | Where-Object {
    @($_.Axioms | Where-Object { $allowedAxioms -notcontains $_ }).Count -gt 0
})
if ($dirty.Count -gt 0) {
    foreach ($d in $dirty) {
        Write-Host ("FAIL Rule-10: {0} depends on [{1}]" -f $d.Name, ($d.Axioms -join ', '))
    }
    exit 1
}

# --- 5. Write the snapshot --------------------------------------------------
$toolchain = (Get-Content (Join-Path $root 'lean-toolchain') -TotalCount 1).Trim()
$manifest = Get-Content (Join-Path $root 'lake-manifest.json') -Raw | ConvertFrom-Json
$mathlibRev = ($manifest.packages | Where-Object { $_.name -eq 'mathlib' }).rev

$md = New-Object System.Text.StringBuilder
[void]$md.AppendLine('# Headline snapshot (Rule 18)')
[void]$md.AppendLine('')
[void]$md.AppendLine('Regenerated by `scripts/Generate-HeadlineSnapshot.ps1`. One row per')
[void]$md.AppendLine('headline theorem: fully-qualified name, SHA256 of the *elaborated*')
[void]$md.AppendLine('type (compiler pretty-print, not source text), SHA256 of its structural')
[void]$md.AppendLine('fingerprint (a canonical de Bruijn serialisation of the same elaborated')
[void]$md.AppendLine('type: binder names dropped, proof subterms elided; alpha-invariant), and')
[void]$md.AppendLine('the kernel axiom set. The headline set itself is load-bearing: changing')
[void]$md.AppendLine('it triggers Rule 3. Gate 5 keys the rows on the structural column: a')
[void]$md.AppendLine('changed fingerprint, axiom set or vanished row fails the round until')
[void]$md.AppendLine('user-reviewed; a moved printed hash with the fingerprint unchanged is')
[void]$md.AppendLine('reported as information (round O, doc 82 P5, 2026-09-10).')
[void]$md.AppendLine('')
[void]$md.AppendLine("- Toolchain (``lean-toolchain``): ``$toolchain``")
[void]$md.AppendLine("- ``lake env lean --version``: ``$leanVersion``")
[void]$md.AppendLine("- mathlib (``lake-manifest.json``): ``$mathlibRev``")
[void]$md.AppendLine('- Rendering (fixed in `scripts/contract_probe.lean.template` and the probe header; doc 70 D3, rebaselined 2026-09-08): `pp.fullNames true`, `pp.deepTerms true`, `pp.maxSteps 1000000`, `pp.proofs false`')
[void]$md.AppendLine('- Structural fingerprint: `#structuralRoots` in `scripts/contract_probe.lean.template` (binder infos, constants with universe levels by position, literals and projections kept; binder names dropped; proofs elided); its invariants are checked each round by `scripts/Test-StructuralFingerprint.ps1`')
[void]$md.AppendLine('')
[void]$md.AppendLine('| Headline (fully qualified) | Elaborated-type SHA256 | Structural SHA256 | Axioms |')
[void]$md.AppendLine('|---|---|---|---|')
foreach ($r in $rows) {
    [void]$md.AppendLine(('| `{0}` | `{1}` | `{2}` | {3} |' -f $r.Name, $r.TypeHash, $r.StructHash, ($r.Axioms -join ', ')))
}
[void]$md.AppendLine('')
[void]$md.AppendLine('## Pinned economy data')
[void]$md.AppendLine('')
[void]$md.AppendLine('The rows above hash each headline''s name and elaborated *type*. That')
[void]$md.AppendLine('fences renames, vanished theorems, and statement drift -- but it cannot')
[void]$md.AppendLine('see the definitions a statement mentions. Editing a witness constant')
[void]$md.AppendLine('leaves every type-hash byte-identical while changing what the theorem')
[void]$md.AppendLine('asserts about.')
[void]$md.AppendLine('')
[void]$md.AppendLine('So the generator also walks each headline''s transitive constant closure,')
[void]$md.AppendLine('collects every economy instance it mentions, and hashes the')
[void]$md.AppendLine('pretty-printed *value* of every non-`Prop` project constant those')
[void]$md.AppendLine('instances depend on. Proofs are excluded on purpose: a proof refactor')
[void]$md.AppendLine('does not change what an economy is, and pinning proof terms would make')
[void]$md.AppendLine('this fence brittle against exactly the edits it should tolerate.')
[void]$md.AppendLine('')
[void]$md.AppendLine(('Economy instances pinned ({0}):' -f $pinEcon.Count))
[void]$md.AppendLine('')
foreach ($e in $pinEcon) { [void]$md.AppendLine(('- `{0}`' -f $e)) }
[void]$md.AppendLine('')
[void]$md.AppendLine(('| Pinned constant | Value SHA256 |' ))
[void]$md.AppendLine('|---|---|')
foreach ($r in $pinRows) {
    [void]$md.AppendLine(('| `{0}` | `{1}` |' -f $r.Name, $r.ValueHash))
}


[void]$md.AppendLine('')
[void]$md.AppendLine('## Contract roots')
[void]$md.AppendLine('')
[void]$md.AppendLine('The economy, certificate, package and equilibrium structures the headlines')
[void]$md.AppendLine('and the manuscript bind over, hashed *directly* (doc 68, L9): each root''s')
[void]$md.AppendLine('elaborated type, its constructor''s type, and every projection''s type; a')
[void]$md.AppendLine('`Prop`-valued root by its body. Unlike the pinned data above, this does not')
[void]$md.AppendLine('depend on a headline reaching an instance, so a field added to a structure')
[void]$md.AppendLine('that only generic theorems bind over changes a row here. A missing root')
[void]$md.AppendLine('fails the generator. Adding or removing a root is a Rule-18 event.')
[void]$md.AppendLine('')
[void]$md.AppendLine(('Roots ({0}), records ({1}):' -f $contractRoots.Count, $contractRows.Count))
[void]$md.AppendLine('')
[void]$md.AppendLine('| Contract declaration | SHA256 |')
[void]$md.AppendLine('|---|---|')
foreach ($r in $contractRows) { [void]$md.AppendLine(('| `{0}` | `{1}` |' -f $r.Name, $r.ContractHash)) }
[void]$md.AppendLine('')
[void]$md.AppendLine('## Evidence declarations')
[void]$md.AppendLine('')
[void]$md.AppendLine('The theorems and refutations `docs/HYPOTHESIS-CENSUS.md` cites as the')
[void]$md.AppendLine('evidence for a status (doc 70, C-7), hashed by elaborated type. The census')
[void]$md.AppendLine('records the hash it reviewed each status against in')
[void]$md.AppendLine('`docs/census/status-evidence.json`; a row here that differs from the')
[void]$md.AppendLine('recorded one marks every status citing it **stale** (gate 7).')
[void]$md.AppendLine('')
[void]$md.AppendLine('| Evidence declaration | Elaborated-type SHA256 |')
[void]$md.AppendLine('|---|---|')
foreach ($r in $evidenceRows) { [void]$md.AppendLine(('| `{0}` | `{1}` |' -f $r.Name, $r.TypeHash)) }
[void]$md.AppendLine('')
[void]$md.AppendLine('## Definition bodies named by the headlines')
[void]$md.AppendLine('')
[void]$md.AppendLine('A headline''s elaborated type holds a definition it names -- `LossOffset`,')
[void]$md.AppendLine('`KS`, `gT`, `A`, `Placable` -- by name only, so redefining the body moved')
[void]$md.AppendLine('neither hash above (doc 104 §8, the drift-fence blind spot). Each row here')
[void]$md.AppendLine('hashes, for one headline, the alpha-invariant serialisation (`structSer`,')
[void]$md.AppendLine('proofs elided) of every project definition reachable from the constants in')
[void]$md.AppendLine('its type through definition bodies (theorems, inductives, constructors and')
[void]$md.AppendLine('axioms are not followed). Any change here is drift (round AX, sign-off M7).')
[void]$md.AppendLine('')
[void]$md.AppendLine('| Headline (fully qualified) | Definitions | Body SHA256 |')
[void]$md.AppendLine('|---|---|---|')
foreach ($r in $rows) {
    [void]$md.AppendLine(('| `{0}` | {1} | `{2}` |' -f $r.Name, $r.BodyCount, $r.BodyHash))
}
[System.IO.File]::WriteAllText((Join-Path $root $OutFile), $md.ToString(),
    (New-Object System.Text.UTF8Encoding($false)))
Write-Host ("OK: {0} headlines, all axiom-clean, structural fingerprints and definition bodies attached; {1} economy instances and {2} pinned constants; {3} contract records over {4} roots; {5} evidence declarations. Snapshot written to {6}." -f $rows.Count, $pinEcon.Count, $pinRows.Count, $contractRows.Count, $contractRoots.Count, $evidenceRows.Count, $OutFile)
exit 0
