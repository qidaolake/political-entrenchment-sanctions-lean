# Primitive census of the 54 pinned headline rows

**Regenerated 2026-09-27** (round BA, doc 107), for the headline set of
`HEADLINE-SNAPSHOT.md` at the `v1.26-submission` preparation. It replaces the
census of the 46-row set of 2026-09-08, which is kept in git history (the tag
`v1.25-submission`, `cb283d8`). The row numbers below follow
`HEADLINE-SNAPSHOT.md`.

**Updated 2026-09-29** (round BC, doc 112), on the user's word: nine rows
re-pinned to their round-BB siblings (rows 1, 2, 3, 27, 37, 45, 46, 48, 49), three
rows added (52–54), and the chord class split (the relief extension
`ChordEconomyRelief`; interiority and the stage relief margin theorem hypotheses;
`Params.F_mem` a theorem). Rows 32 and 35 moved to the relief extension; rows 39–41,
43 and 44 gained the interiority hypothesis (and rows 35 and 39 the stage relief
margin), which is why their premise counts rose while the class shrank.

What changed since the previous census:

* **Six rows retired by name** in round V (2026-09-15); the theorems stay in the
  tree: `shockedFeedbackStackelbergTop_interior_discharged_canonical`,
  `mechanismWitnessParams_purified_existence_unconditional_one_monotone`,
  `mechanismWitnessParams_fullWidth_mechanism_active_frontier`,
  `feedbackStackelbergTop_unique_in_carrier_schur`, `sfCert_three_goals_generalF`
  and `not_coupledLeaderStrongConcave`.
* **Eleven rows added** since then (rows 41–51 below): the bracket, the
  monotone-class uniqueness, the wedge, relief participation, branch invariance,
  history deviations and the welfare-completion reversal.
* **The placable rows moved to the chord economy** in rounds AT–AX: rows 32, 35,
  37, 39 and 40 were stated over `PlacableEconomyF` / `PlacableEconomyFcs` and
  are now stated over `ChordEconomy` / `ChordEconomyCs`, whose stage payoffs are
  abstract functions under one-sided rate bounds.
* **A second axis, the payoffs.** The class is now general in both stage
  payoffs as well as in the transition, so the census records a payoff column
  beside the transition column.

## The two columns are read, not scripted

**Transition.** Rule 22 says deciding whether a result is general "is a
judgement about what it depends on, never the output of a search". Three
automated attempts confirmed it on 2026-09-02, each failing differently: a
substring match on `affineF` read the disequalities `quadBumpF_ne_affineF` as
equalities; following a witness economy's `F :=` field found the base economy of
a `{ … with F := … }` update, not the one the theorem is stated at; and a
word-boundary name match missed the whole `eeCertB_*` group, because `_` is a
word character. The column below was produced by opening each statement.

**Payoffs.** Same method. The question is what the statement quantifies over:
a free `Params` (payoffs constrained only by the theorem's own hypotheses), the
chord economy (payoffs constrained by the rate bounds of panel A0), a
coefficient family with fixed functional forms, or one economy.

**Premises** are the row's top-level `Prop`-typed binders, read from the
compiler-derived `docs/HYPOTHESIS-CENSUS.md` (a binder whose census status is
neither `data` nor a structure binder). Structure-typed binders — certificates,
the economy itself — count zero here and are expanded in that census. The count
is an ordering, not a measure. For the chord rows, the class fields each theorem actually reads are counted by
the compiler in `docs/census/chord-field-census.md` (round BB, 2026-09-28;
`scripts/Chord-Field-Census.ps1`): from 25 of 81 (row 47) to 77 (row 44). It replaces the syntactic counts of the previous
census, which were larger because they counted certificate fields.

## Categories

| transition | meaning |
|---|---|
| **GENERAL** | stated over an arbitrary transition constrained only by ordinal or chord conditions |
| **GENERAL-F ROUTE, AFFINE INSTANCE** | discharged through the general-`F` machinery, but instantiated at an economy whose `F` is affine |
| **NON-AFFINE (witnessed)** | stated at an economy with a proved `_ne_affineF` |
| **AFFINE** | stated at an economy with `F := affineF …`, or naming `p.δ`, or taking `δ` explicitly |
| **AFFINE BY HYPOTHESIS** | stated over the general class, with hypotheses that force the affine law (tight chords `g_lo = g_hi`, `d_lo = d_hi` with `F_diag` pin `F = affineF d_lo`) |
| **MICROFOUNDED** | the payoffs are derived from four-group public-choice primitives; the pinned member's transition is the affine law `affineF (1/2)` |
| **N/A** | no transition appears |

| payoffs | meaning |
|---|---|
| **RATE BOUNDS** | stated over `ChordEconomy` / `ChordEconomyRelief` / `ChordEconomyCs` (the relief extension since round BC): both stage payoffs abstract, under the one-sided rate bounds of panel A0 |
| **ABSTRACT** | stated over an arbitrary `Params`: payoffs free, constrained only by the theorem's hypotheses |
| **FAMILY** | stated over a coefficient family with a fixed functional form (the quadratic–linear family, or the symbolic family) |
| **WITNESS** | stated at one economy, or at a one-parameter witness family |
| **MICROFOUNDED** | four-group primitives |
| **N/A** | no stage payoff appears |

## The census

| # | row | premises | transition | payoffs |
|---|---|---|---|---|
| 1 | `standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent` | 1 | **GENERAL** — over `p`, only `hF_top_pre : ∀ x ∈ Icc 0 (max xT xS), x < F x 1` (re-pinned round BC) | ABSTRACT |
| 2 | `standardCompliance_three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent` | 1 | **GENERAL** — pre-basin ascent in place of (F5) (re-pinned round BC) | ABSTRACT |
| 3 | `standardCompliance_low_basin_generalF_of_sender_level` | 4 | **GENERAL** — the Sender's level condition only, no Target condition (re-pinned round BC; the bundle of the old row unpacked) | ABSTRACT |
| 4 | `theorem2_dynamic_dominates_myopic_at_same_alpha` | 1 | **GENERAL** | ABSTRACT |
| 5 | `shockEntryHorizon_bound` | 3 | **AFFINE** — `(1 − p.δ)^T`; deliberate, the geometric closed form is the content | ABSTRACT |
| 6 | `eeCert_three_goals_dominance` | 0 | AFFINE — `eeCertParams`, `affineF (1/2)` | WITNESS |
| 7 | `eeCertMS_generalF_three_goals` | 0 | **GENERAL-F ROUTE, AFFINE INSTANCE** | WITNESS |
| 8 | `eeCertMS_three_goals_dominance` | 0 | AFFINE | WITNESS |
| 9 | `qbCertMS_generalF_three_goals` | 0 | **NON-AFFINE** — `qbParams`, `quadBumpF_ne_affineF` | WITNESS |
| 10 | `lbLow_generalF_three_goals` | 0 | **NON-AFFINE** — `lbParams`, `quadBumpLowF_ne_affineF` | WITNESS |
| 11 | `wobbleEconMS_three_goals_full` | 0 | **NON-AFFINE** — `wobbleF`, `wobbleEconMS_F_ne_affineF` | WITNESS |
| 12 | `b2NonMono_three_goals_dominance` | 0 | AFFINE — `b2Params`, `affineF (1/2)` | WITNESS |
| 13 | `b2_integrated_mechanism_active_generalF_witness` | 0 | **GENERAL-F ROUTE, AFFINE INSTANCE** | WITNESS |
| 14 | `fourGroupCert_three_goals_dominance` | 0 | **MICROFOUNDED** | MICROFOUNDED |
| 15 | `boxTransfer_existsUnique_invariant_attracting` | 3 | AFFINE — takes `δ` explicitly; a transfer operator on measures | N/A |
| 16 | `dualParams_initial_condition_selects` | 0 | AFFINE — `affineF (1/10)` | WITNESS |
| 17 | `eeCertB_equilibrium_feedback_decomposition` | 2 | AFFINE — `eeCertParamsB β` | WITNESS (family in `β_S`) |
| 18 | `eeCertB_equilibrium_lockin_strict` | 3 | AFFINE | WITNESS (family in `β_S`) |
| 19 | `eeCertB_lockin_amplification` | 2 | AFFINE | WITNESS (family in `β_S`) |
| 20 | `eeCertB_VT_star_βS_invariant` | 2 | AFFINE | WITNESS (family in `β_S`) |
| 21 | `plannerW_distortion` | 0 | **N/A** — a stage-payoff identity | MICROFOUNDED |
| 22 | `plannerW_lockin_dominated_iff` | 0 | **N/A** — a stage-payoff inequality | MICROFOUNDED |
| 23 | `fgc_planner_inefficiency_equilibrium` | 2 | **MICROFOUNDED** | MICROFOUNDED |
| 24 | `standardCompliance_persistence_generalF_from_sender_package` | 1 | **GENERAL** | ABSTRACT |
| 25 | `SymbolicEconomyF.persistence_generalF` | 0 | **GENERAL** — `F := E.F`, a free structure field | FAMILY (symbolic) |
| 26 | `equilibriumTop_senderPersistenceF_long_run_nonDecreasing` | 1 | **GENERAL** | ABSTRACT |
| 27 | `equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent` | 2 | **GENERAL** (re-pinned round BC) | ABSTRACT |
| 28 | `equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | 5 | **GENERAL** | ABSTRACT |
| 29 | `equilibriumTop_attraction_on_derived_interval_of_invariant` | 6 | **GENERAL** | ABSTRACT |
| 30 | `equilibriumTop_derived_dual_basins` | 10 | **GENERAL** | ABSTRACT |
| 31 | `qbCert_three_goals_generalF` | 0 | **NON-AFFINE** — `qbParams`, `quadBumpF_ne_affineF` | WITNESS |
| 32 | `ChordEconomyRelief.both_channels_active_of_margin` | 6 | **GENERAL** — chords only | **RATE BOUNDS** (relief extension; interiority a hypothesis since round BC) |
| 33 | `placableQuadDiag_both_channels_active` | 1 | **NON-AFFINE** — `quadDiagF_ne_affineF` | WITNESS (a family member) |
| 34 | `σ_dyn_top_monotoneOn_x_of_singleCrossing` | 2 | **GENERAL** | ABSTRACT |
| 35 | `ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF` | 5 | **GENERAL** — chords only | **RATE BOUNDS** (relief extension; interiority and the stage relief margin hypotheses since round BC) |
| 36 | `placableAffine_unique_attracting_state` | 0 | **AFFINE** — the closed-loop constant `43/46` closes only at this member | WITNESS |
| 37 | `ChordEconomy.target_only_regime_generalF_core` | 1 | **GENERAL** — chords only (re-pinned round BC: clauses (i)–(iii), no rally margin) | **RATE BOUNDS** |
| 38 | `dualParams_two_sided_regimes` | 0 | **AFFINE** — `(9x + s)/10` | WITNESS |
| 39 | `ChordEconomyCs.four_cell_generalF` | 7 | **GENERAL** — chords only | **RATE BOUNDS**, instantiated at the quartic member |
| 40 | `ChordEconomyCs.sender_only_regime_generalF` | 4 | **GENERAL** — chords only | **RATE BOUNDS** |
| 41 | `ChordEconomyCs.both_channels_active_of_relief` | 5 | **GENERAL** — chords only | **RATE BOUNDS**, instantiated at the quartic member |
| 42 | `ChordEconomy.targetObj_strictAntiOn_of_sharp` | 5 | **GENERAL** | **RATE BOUNDS** |
| 43 | `ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero` | 5 | **GENERAL** | **RATE BOUNDS**, instantiated at the quartic member |
| 44 | `ChordEconomyCs.defiance_not_maxOn_of_relief_side` | 5 | **GENERAL** | **RATE BOUNDS** |
| 45 | `ChordEconomyCs.collapse_sides'` | 14 | **AFFINE BY HYPOTHESIS** — its tight chords pin the affine law; it is the affine collapse of the general bracket | **RATE BOUNDS** (tight) |
| 46 | `ChordEconomy.unique_equilibrium_of_rule_monotone` | 2 | **GENERAL** (re-pinned round BC: no policy condition) | **RATE BOUNDS** |
| 47 | `ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone` | 3 | **GENERAL** | **RATE BOUNDS** |
| 48 | `ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance` | 4 | **GENERAL** (re-pinned round BC: at the Target's own optimum, no zero-sanction condition) | **RATE BOUNDS** |
| 49 | `defiance_branch_invariance_generalF` | 5 | **GENERAL** (re-pinned round BC: any full-defiance equilibria of any two games) | ABSTRACT |
| 50 | `FeedbackStackelbergEquilibriumTop.leader_optimal_against_history_deviation_top` | 0 | **GENERAL** | ABSTRACT |
| 51 | `PlacableEconomyFcs.exists_completions_reversing_regime_ranking` | 4 | **GENERAL** — chords only | FAMILY (quadratic–linear; welfare kept on the family, sign-off M5 of doc 104) |
| 52 | `ChordEconomy.reliefPayoff_le_V_T` | 2 | **GENERAL** (added round BC: the Target's security bound) | **RATE BOUNDS** |
| 53 | `ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 6 | **GENERAL** (added round BC: patience on existence) | **RATE BOUNDS** |
| 54 | `FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 12 | **GENERAL** (added round BC: the defiance core over any economy) | ABSTRACT |

## What the columns say

| transition | rows | count |
|---|---|---|
| GENERAL | 1–4, 24–30, 32, 34, 35, 37, 39–44, 46–54 | **30** |
| AFFINE | 5, 6, 8, 12, 15–20, 36, 38 | **12** |
| AFFINE BY HYPOTHESIS | 45 | **1** |
| GENERAL-F ROUTE, AFFINE INSTANCE | 7, 13 | **2** |
| NON-AFFINE (witnessed) | 9, 10, 11, 31, 33 | **5** |
| MICROFOUNDED | 14, 23 | **2** |
| N/A | 21, 22 | **2** |

| payoffs | rows | count |
|---|---|---|
| RATE BOUNDS | 32, 35, 37, 39–48, 52, 53 | **15** |
| ABSTRACT | 1–5, 24, 26–30, 34, 49, 50, 54 | **15** |
| FAMILY | 25, 51 | **2** |
| WITNESS | 6–13, 16–20, 31, 33, 36, 38 | **17** |
| MICROFOUNDED | 14, 21–23 | **4** |
| N/A | 15 | **1** |

**Thirty rows are general in the transition and five are witnessed
non-affine.** The witnessed rows use four distinct transitions proved non-affine
at every weight: `quadBumpF` (rows 9, 31), `quadBumpLowF` (row 10), `wobbleF`
(row 11) and `quadDiagF` (row 33). That is the set Rule 9B's generality clause
asks for. The quartic chord member uses `quadDiagF` too, so it adds no new
transition function.

**Fifteen rows are general in both payoffs over the chord economy** (since round BC the base class, its relief extension or the enriched subclass), and rows 49 and 54 over any economy. Three of
them are instantiated in Lean at the quartic member, a member quadratic–linear
in no payoff coordinate (`qwU_S_ne_symU_S`, `qwU_T_ne_symU_T`, ten rate pairs
strictly split by `qw_pairs_split`): row 39 through `four_cell_generalF'`
(`qwDefiance_four_cells`), row 41 (`qwDefiance_both_channels`) and row 43
(`qwRelief_rule_zero`). That is the payoff-side analogue of the transition
witnesses: the rate-bound class is inhabited outside the quadratic–linear
family. It is an existence certificate and says nothing about how common such
members are (Rule 9A).

**Row 45 is general in its binders and affine in effect.** `collapse_sides`
quantifies over the whole chord economy, but its fourteen tightness equalities (sixteen before the round-BC re-pin to `collapse_sides'`; `r_hi = 0` and `n_lo = 0` follow from the rest)
include `g_lo = g_hi` and `d_lo = d_hi`, which with `F_diag` pin the affine
law. That is its content: it is the point to which the general bracket
collapses. Its docstring and the manuscript state it as a sufficient condition
for the collapse, not a characterisation (round AY).

**Two rows use the general-`F` route but land on affine economies.** Rows 7 and
13 carry `generalF` in their names, and the name refers to the machinery, not
the instance. The witness set for transition generality is rows 9–11, 31 and 33,
not rows 7 and 13.

**The affine rows are not defects.** Row 5 is deliberately affine: the geometric
closed-form horizon is the content, and a general transition has no `δ` to put
in it. The `eeCertB_*` block (rows 17–20) is the comparative-statics family,
where the affine base is what makes the closed forms computable. Rows 36 and 38
compute a constant at one member.

**Two rows have no transition at all.** Rows 21 and 22 are stage-payoff algebra
over the four-group microfoundation; row 15 has no payoff.

## The witness rows

On 2026-09-02 ten witnesses were checked for a general form (Rule 5: a witness
should be a one-line corollary of a parametric theorem). Eight are still
headline rows. Seven route to a general-`F` theorem in `Theory/`: rows 7, 8, 9 and
11 through `three_goals_local_MS_generalF` or `three_goals_generalF_full`, and
rows 6, 12 and 14 through `goal2_dominance_of_affine` → `goal2_dominance_generalF`.
Row 13, `b2_integrated_mechanism_active_generalF_witness`, is bespoke by Rule 5's
own exception: it asserts exact numeric magnitudes for both continuation
channels, and a general form would delete the content. The two
`mechanismWitnessParams` rows of that check were retired in round V.

`goal2_dominance_of_affine` (`Examples/AffineInstance/Certificates.lean`) is
literally `goal2_dominance_generalF p C`, with both affine-flavoured binders
unused (`_hF`, `_hgT_nn`). Its docstring keeps them as a drift fence; the three
witnesses on that route could call the general theorem directly.

## What is still open

**Seventeen rows have no top-level premise**: rows 6–14, 16, 21, 22, 25, 31, 36,
38 and 50. Most are witness corollaries whose real surface is the certificate's
fields, expanded in `docs/HYPOTHESIS-CENSUS.md`. Rows 21 and 22 are algebraic
identities, row 25 is a universal over the whole symbolic family, and row 50 is
a universal over every equilibrium of every `Params`. A row with no premise is
true outright; those are the rows whose statements most need a pinned hash.

**Binder review.** Every `Prop` binder and field of the 51 rows has a census
status in `docs/HYPOTHESIS-CENSUS.md` (reviewed statuses, with evidence hashes
checked by gate 7 of `Audit-Round.ps1`). That supersedes the docstring-versus-
binder spot check this document used to carry. Docstrings of non-headline
declarations are not covered by it: the v1.25 review found a file header (N124,
`PlacableSenderPolicyClass.lean`) that listed two of its theorem's six
hypotheses; it was corrected in round AY.
