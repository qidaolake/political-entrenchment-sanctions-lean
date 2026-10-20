# Unused-binder audit (Rule 13, doc 78 K12; protocol v2, doc 80 M4)

Generated 2026-10-19 by `scripts/unused_run.py` (sha `76e41bb91d702409`) from `scripts/unused_probe.lean.template` (sha `6f3077a4b05db5cd`) at commit `` under `leanprover/lean4:v4.29.1`, mathlib `5e932f97d`; run nonce `ff109e209de9479c8c7d8adda8b447ec`. Roots: 294 in `roots-headlines.txt` (sha `cb91ae6b80754a0a`), `roots-manuscript-names.txt` (sha `6becd07876395f7d`); 278 distinct declarations; 278 records, of which 0 skipped (no value). Binders inspected: 1949, of which 1470 explicit. Raw compiler output: `unused-binders.md.raw.txt`. The probe reads the built library: this report is evidence about the tree only if the build that produced the `.olean` files is the one at the commit named here.

**What a row means.** For each explicit binder of a root, the probe applies the compiled proof term to the binders of the root's own type, inlines the auxiliary lemmas the compiler split off under the root's name, and records whether the binder occurs in the proof body, in the type of another binder, or in the conclusion. A binder with all three flags false is logically removable from the statement and is listed as a **candidate**; removing one from a headline changes its elaborated type and is a Rule 3/18 decision, never an automatic edit — the decisive check is a sibling declaration without the binder that elaborates. A binder that occurs only in the proof body is used by this proof; whether another proof could avoid it is not measured, and neither is "implied by another hypothesis of the same theorem".

## Candidates: 1

| root | k | binder | type |
|---|---|---|---|
| `Sanctions.Examples.ChordEconomyTwoSided.equilibriumTop_of_margin_α_eq_zero` | 5 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |

## Explicit binders used only in the proof body: 846

These are consumed by the proof and appear neither in another binder's type nor in the conclusion. They are not candidates; they are the hypotheses whose necessity is a mathematical question, listed so a reader can pick a target for a Rule-11 refutation attempt.

| root | k | binder | type |
|---|---|---|---|
| `Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent` | 4 | `hMyoCeiling` | `∀ x ∈ Set.Icc (Max.max C.xT C.xS) 1, p.σ x (p.myopicFeedbackEquilibrium_canonical.α x) ≤ Max.max x (Max.max C.xT C.xS)` |
| `Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent` | 5 | `hF_top_pre` | `∀ x ∈ Set.Icc 0 (Max.max C.xT C.xS), x < p.F x 1` |
| `Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent` | 4 | `hMyoCeiling` | `∀ x ∈ Set.Icc (Max.max C.xT C.xS) 1, p.σ x (p.myopicFeedbackEquilibrium_canonical.α x) ≤ Max.max x (Max.max C.xT C.xS)` |
| `Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent` | 5 | `hF_top_pre` | `∀ x ∈ Set.Icc 0 (Max.max C.xT C.xS), x < p.F x 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level` | 6 | `hxbar_low_le_one` | `xbar_low ≤ 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level` | 7 | `hsbar_mem` | `sbar_low ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level` | 8 | `h_sender_low` | `∀ x ∈ Set.Icc 0 xbar_low, StrictAntiOn (fun s => p.senderDynObjective E.V_S x (E.α x) s) (Set.Icc (Min.min x sbar_low) 1)` |
| `Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level` | 9 | `hTopMono` | `MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc 0 xbar_low)` |
| `Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level` | 10 | `hx₀` | `x₀ ∈ Set.Icc 0 xbar_low` |
| `Sanctions.AbstractGame.Params.theorem2_dynamic_dominates_myopic_at_same_alpha` | 3 | `h_V_S_mono` | `Monotone ⇑V_S` |
| `Sanctions.AbstractGame.Params.shockEntryHorizon_bound` | 5 | `h_pow` | `(1 - p.δ) ^ T * (1 - x₀) ≤ 1 - xbar` |
| `Sanctions.boxTransfer_existsUnique_invariant_attracting` | 3 | `hh` | `0 < h` |
| `Sanctions.boxTransfer_existsUnique_invariant_attracting` | 4 | `hδ0` | `0 < δ` |
| `Sanctions.boxTransfer_existsUnique_invariant_attracting` | 5 | `hδ1` | `δ < 1` |
| `Sanctions.Examples.eeCertB_equilibrium_lockin_strict` | 5 | `hlt` | `β₁ < β₂` |
| `Sanctions.Examples.eeCertB_lockin_amplification` | 3 | `hβ₁` | `β₁ ∈ Set.Ico (6 / 13) (4 / 7)` |
| `Sanctions.Examples.eeCertB_lockin_amplification` | 4 | `hβ₂` | `β₂ ∈ Set.Ico (6 / 13) (4 / 7)` |
| `Sanctions.Examples.fgc_planner_inefficiency_equilibrium` | 2 | `hx0` | `x0 ∈ Set.Icc 0 1` |
| `Sanctions.Examples.fgc_planner_inefficiency_equilibrium` | 4 | `hb` | `β ∈ Set.Ico 0 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_sender_package` | 7 | `P` | `p.SenderPersistencePackage D E xT xS K_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_sender_package` | 9 | `a._@._internal._hyg.0` | `x₀ ∈ Set.Icc (Max.max xT xS) 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_long_run_nonDecreasing` | 6 | `hB` | `p.SenderPersistenceBasinTop E.V_S E.α xbar sbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_long_run_nonDecreasing` | 7 | `hx₀` | `x₀ ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent` | 6 | `hB` | `p.SenderPersistenceBasinTop E.V_S E.α xbar sbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent` | 7 | `hF_top_pre` | `∀ x ∈ Set.Icc 0 xbar, x < p.F x 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent` | 8 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | 5 | `hab` | `a ≤ b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | 6 | `hrule_mono` | `MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | 7 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | 8 | `hmaps` | `∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | 10 | `hx₀` | `x₀ ∈ Set.Icc a b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | 2 | `hAdj` | `p.StrictAdjustment` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | 5 | `hxbar0` | `0 ≤ xbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | 6 | `hxbar1` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | 7 | `hrule_mono` | `MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | 8 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | 9 | `hmaps` | `∀ x ∈ Set.Icc xbar 1, p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 7 | `hlo` | `lo < xL` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 8 | `hmid` | `xL ≤ xH` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 9 | `hhi` | `xH < hi` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 10 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc lo hi)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 11 | `hfix_lo` | `p.dynamicTopLockInStepF E.V_S E.α lo = lo` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 12 | `hfix_hi` | `p.dynamicTopLockInStepF E.V_S E.α hi = hi` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 13 | `hlow_erode` | `∀ x ∈ Set.Ioc lo xL, p.dynamicTopLockInStepF E.V_S E.α x < x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 14 | `hhigh_build` | `∀ x ∈ Set.Ico xH hi, x < p.dynamicTopLockInStepF E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 15 | `hlb` | `∀ x ∈ Set.Icc lo hi, lo ≤ p.dynamicTopLockInStepF E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | 16 | `hub` | `∀ x ∈ Set.Icc lo hi, p.dynamicTopLockInStepF E.V_S E.α x ≤ hi` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net` | 3 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net` | 4 | `hflip` | `E.ℓhi < E.sfloor * E.plo` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net` | 8 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.placableQuadDiag_both_channels_active` | 2 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.σ_dyn_top_monotoneOn_x_of_singleCrossing` | 4 | `hSC` | `Sanctions.MilgromShannon.SingleCrossingOn Sanctions.I Sanctions.S fun s x => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))` |
| `Sanctions.AbstractGame.Params.σ_dyn_top_monotoneOn_x_of_singleCrossing` | 5 | `h_unique` | `p.DynamicArgmaxUnique V_S` |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief_net` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief_net` | 4 | `hrelief` | `E.ℓhi * E.Mtot < E.klo * E.plo` |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief_net` | 7 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | 3 | `hPC` | `E.PlacationCeiling khi` |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | 5 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | 6 | `hsharp` | `E.c - E.ℓlo * E.mu / khi < E.β_T * E.dlo * g` |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | 8 | `hV_T` | `Sanctions.AbstractGame.Params.LowerSlopeOnValueOn V_T (Set.Icc 0 1) g` |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | 10 | `hV_S` | `V_S ∈ E.carrierS` |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | 12 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero` | 7 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side` | 3 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side` | 4 | `hγ` | `E.β_T * E.LloopSharp < 1` |
| `Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side` | 5 | `hrel` | `E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT)` |
| `Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side` | 7 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 2 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 3 | `hMs` | `E.Ms = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 4 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 5 | `hMcx` | `E.Mcx = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 6 | `hMcs` | `E.Mcs = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 7 | `hMmix` | `E.Mmix = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 8 | `hQ` | `E.Qbar = E.q` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 9 | `hk` | `E.klo = E.khi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 10 | `hℓ` | `E.ℓlo = E.ℓhi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 11 | `hp` | `E.plo = E.c` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 12 | `hv` | `E.vlo = E.vhi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 13 | `hnhi` | `E.nhi = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 14 | `hg` | `E.glo = E.ghi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | 15 | `hd` | `E.dlo = E.dhi` |
| `Sanctions.Examples.ChordEconomy.unique_equilibrium_of_rule_monotone` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomy.unique_equilibrium_of_rule_monotone` | 4 | `hrule` | `MonotoneOn (E.rule Eq) Sanctions.S` |
| `Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone` | 3 | `hPC` | `E.PlacationCeiling khi` |
| `Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone` | 4 | `hN` | `E.ZeroSanctionAntitone` |
| `Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone` | 6 | `hanti` | `AntitoneOn Eq.α Sanctions.S` |
| `Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone` | 8 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance` | 5 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance` | 7 | `hT` | `0 < T` |
| `Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF` | 3 | `hF` | `∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.F x s = p₂.F x s` |
| `Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF` | 4 | `hβS` | `p₁.β_S = p₂.β_S` |
| `Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF` | 5 | `hUS` | `∀ x ∈ Sanctions.I, ∀ s ∈ Sanctions.I, p₁.U_S x 0 s = p₂.U_S x 0 s` |
| `Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF` | 8 | `hα₁` | `∀ x ∈ Sanctions.I, E₁.α x = 0` |
| `Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF` | 9 | `hα₂` | `∀ x ∈ Sanctions.I, E₂.α x = 0` |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_le_V_T` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 3 | `h` | `E₁.SameButβT E₂` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 4 | `hβ` | `E₁.β_T ≤ E₂.β_T` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 5 | `hmono` | `MonotoneOn (E₁.responsePath E₁.VSstar) (Set.Icc 0 1)` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 7 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 8 | `hginv` | `g * (1 - E₁.β_T * E₁.glo) + Max.max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu) ≤ E₁.vlo + E₁.nlo * E₁.sfloor` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | 9 | `h₁` | `∃ Eq, ∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 7 | `hband` | `∀ s ∈ Set.Icc 0 1, ∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 8 | `hSlo` | `Sanctions.TransitionChords.SanctionLowerChord p.F dl` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 9 | `hDD` | `∀ x ∈ Set.Icc 0 1, Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I fun s a => p.U_S x a s` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 10 | `hcost` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, ∀ a ∈ Set.Icc 0 1, ℓ * a ≤ p.U_T x 0 s - p.U_T x a s` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 11 | `hℓ` | `0 < ℓ` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 12 | `hpain` | `∀ x ∈ Set.Icc 0 1, Sanctions.AbstractGame.Params.LowerLossSlopeOn (fun s => p.U_T x 0 s) (Set.Icc 0 1) c` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 13 | `hstate` | `∀ s ∈ Set.Icc 0 1, ∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → v * (y₂ - y₁) ≤ p.U_T y₂ 0 s - p.U_T y₁ 0 s` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 14 | `hv` | `0 ≤ v` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 15 | `hTM` | `c ≤ p.β_T * dl * p.defianceSlope gl v` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 17 | `hrule` | `MonotoneOn (p.dynamicEquilibriumRule Eq) Sanctions.S` |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | 19 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast_history` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast_history` | 4 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_isGreatest_history` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_isGreatest_history` | 4 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance` | 3 | `h` | `E₁.SameButβT E₂` |
| `Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance` | 4 | `hβ` | `E₁.β_T ≤ E₂.β_T` |
| `Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance` | 6 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance` | 7 | `hginv` | `g * (1 - E₁.β_T * E₁.glo) + Max.max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu) ≤ E₁.vlo + E₁.nlo * E₁.sfloor` |
| `Sanctions.Examples.ChordEconomy.no_zero_rule_equilibrium` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 3 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 5 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 6 | `hMs` | `E.Ms = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 7 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 8 | `hMcx` | `E.Mcx = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 9 | `hMcs` | `E.Mcs = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 10 | `hMmix` | `E.Mmix = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 11 | `hQ` | `E.Qbar = E.q` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 12 | `hk` | `E.klo = E.khi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 13 | `hℓ` | `E.ℓlo = E.ℓhi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 14 | `hp` | `E.plo = E.c` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 15 | `hv` | `E.vlo = E.vhi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 16 | `hnhi` | `E.nhi = 0` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 17 | `hg` | `E.glo = E.ghi` |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | 18 | `hd` | `E.dlo = E.dhi` |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | 9 | `hε` | `0 < ε` |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | 10 | `hWP` | `∀ (t : ℕ), |R.welfare (P t).1 (P t).2.1 (P t).2.2| ≤ M` |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | 11 | `hWQ` | `∀ (t : ℕ), |R.welfare (Q t).1 (Q t).2.1 (Q t).2.2| ≤ M` |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | 12 | `hwP` | `∀ (t : ℕ), |R.wS h (P t).1 (P t).2.1 (P t).2.2| ≤ M` |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | 13 | `hwQ` | `∀ (t : ℕ), |R.wS h (Q t).1 (Q t).2.1 (Q t).2.2| ≤ M` |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | 14 | `hsep` | `∀ (t : ℕ), R.wS h (Q t).1 (Q t).2.1 (Q t).2.2 + ε ≤ R.wS h (P t).1 (P t).2.1 (P t).2.2` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 10 | `hβ0` | `0 ≤ β` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 11 | `hβ1` | `β < 1` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 12 | `hlam0` | `0 ≤ lam` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 13 | `hβlam` | `β * lam < 1` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 14 | `hbound` | `∀ (x : ↑Sanctions.S) (a s : ↑Sanctions.I), |W x a s| ≤ M` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 15 | `hsoc` | `∀ (x : ↑Sanctions.S) (a s : ↑Sanctions.I), W x a s ≤ W x (astar x) Sanctions.Welfare.zeroI + η * ↑s` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 16 | `hchordW` | `∀ (x y : ↑Sanctions.S), ↑x ≤ ↑y → W y (astar y) Sanctions.Welfare.zeroI - W x (astar x) Sanctions.Welfare.zeroI ≤ B * (↑y - ↑x)` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 17 | `hmono0` | `∀ (x y : ↑Sanctions.S), ↑x ≤ ↑y → ↑(Fc x Sanctions.Welfare.zeroI) ≤ ↑(Fc y Sanctions.Welfare.zeroI)` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 18 | `hchord0` | `∀ (x y : ↑Sanctions.S), ↑x ≤ ↑y → ↑(Fc y Sanctions.Welfare.zeroI) - ↑(Fc x Sanctions.Welfare.zeroI) ≤ lam * (↑y - ↑x)` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 19 | `hmonoS` | `∀ (x : ↑Sanctions.S) (s : ↑Sanctions.I), ↑(Fc x Sanctions.Welfare.zeroI) ≤ ↑(Fc x s)` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 20 | `hchordS` | `∀ (x : ↑Sanctions.S) (s : ↑Sanctions.I), ↑(Fc x s) - ↑(Fc x Sanctions.Welfare.zeroI) ≤ L * ↑s` |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | 21 | `hcond` | `η + β * (Max.max B 0 / (1 - β * lam)) * L ≤ 0` |
| `Sanctions.Examples.ChordEconomy.planner_efficient_rep_at_policy_zero` | 2 | `hZ` | `E.ZeroSanctionNeutral` |
| `Sanctions.AbstractGame.Params.target_tipping_threshold` | 3 | `hID` | `p.TargetStageID` |
| `Sanctions.AbstractGame.Params.target_tipping_threshold` | 4 | `hsbar` | `sbar ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.target_tipping_threshold` | 5 | `h1` | `1 ∈ p.targetFlipSet sbar` |
| `Sanctions.AbstractGame.Params.target_tipping_threshold` | 6 | `h0` | `0 ∉ p.targetFlipSet sbar` |
| `Sanctions.AbstractGame.Params.sender_tipping_threshold` | 4 | `hID` | `p.SenderStageID` |
| `Sanctions.AbstractGame.Params.sender_tipping_threshold` | 5 | `hsbar` | `sbar ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.sender_tipping_threshold` | 6 | `h1` | `1 ∈ p.senderFloorFlipSet sbar m` |
| `Sanctions.AbstractGame.Params.sender_tipping_threshold` | 7 | `h0` | `0 ∉ p.senderFloorFlipSet sbar m` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin` | 5 | `hflip` | `E.ℓhi < E.sfloor * E.plo` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin` | 8 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.rally_softening_interval_iff` | 12 | `hβT` | `0 < βT` |
| `Sanctions.Examples.rally_softening_interval_iff` | 13 | `hdlo` | `0 < dlo` |
| `Sanctions.Examples.rally_softening_interval_iff` | 14 | `hglo` | `βT * glo < 1` |
| `Sanctions.Examples.rally_softening_interval_iff` | 15 | `hq` | `0 < q` |
| `Sanctions.Examples.rally_softening_interval_iff` | 16 | `hu₀` | `0 < u₀` |
| `Sanctions.Examples.rally_softening_interval_iff` | 17 | `hk` | `0 < k` |
| `Sanctions.Examples.lossOffset_iff_v_ge` | 9 | `hβT` | `0 < βT` |
| `Sanctions.Examples.lossOffset_iff_v_ge` | 10 | `hdlo` | `0 < dlo` |
| `Sanctions.Examples.lossOffset_iff_v_ge` | 11 | `hglo` | `βT * glo < 1` |
| `Sanctions.Examples.ChordEconomyCs.reliefSharp_uniform_iff` | 6 | `hq` | `0 < q` |
| `Sanctions.Examples.ChordEconomyCs.reliefSharp_uniform_iff` | 7 | `hk` | `0 < k` |
| `Sanctions.Examples.ChordEconomyCs.reliefSharp_uniform_iff` | 8 | `hM` | `0 < M` |
| `Sanctions.Examples.ChordEconomyCs.reliefSharp_uniform_iff` | 9 | `hC` | `0 < C` |
| `Sanctions.Examples.sigV_feasible_iff` | 10 | `hβS` | `0 < βS` |
| `Sanctions.Examples.sigV_feasible_iff` | 11 | `hdhi` | `0 < dhi` |
| `Sanctions.Examples.sigV_feasible_iff` | 12 | `hghi` | `0 ≤ ghi` |
| `Sanctions.Examples.sigV_feasible_iff` | 13 | `ha` | `βS * ghi ^ 2 < 1` |
| `Sanctions.Examples.sigV_feasible_iff` | 14 | `hKS` | `0 ≤ KS` |
| `Sanctions.Examples.sigV_feasible_iff` | 15 | `hMx` | `0 ≤ Mx` |
| `Sanctions.Examples.sigV_feasible_iff` | 16 | `hMm` | `0 ≤ Mm` |
| `Sanctions.Examples.sigV_feasible_iff` | 17 | `hr` | `0 ≤ r` |
| `Sanctions.Examples.ChordEconomyCs.four_cell_rule_chain_of_policy_zero` | 8 | `hα` | `∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.ChordEconomyCs.four_cell_rule_chain_of_policy_zero` | 10 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyTwoSided.target_only_regime_generalF` | 2 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.PlacableEconomyF.targetOnlyPath_error_le_geometric` | 5 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyF.steady10_lt_of_r_lt` | 3 | `hu` | `E₁.u₀ = E₂.u₀` |
| `Sanctions.Examples.PlacableEconomyF.steady10_lt_of_r_lt` | 4 | `hq` | `E₁.q = E₂.q` |
| `Sanctions.Examples.PlacableEconomyF.steady10_lt_of_r_lt` | 5 | `hr` | `E₁.r < E₂.r` |
| `Sanctions.Examples.PlacableEconomyF.steady10_lt_of_r_lt` | 6 | `hInt₂` | `E₂.Interior` |
| `Sanctions.Examples.PlacableEconomyF.vertex_lt_of_r_lt` | 3 | `hu` | `E₁.u₀ = E₂.u₀` |
| `Sanctions.Examples.PlacableEconomyF.vertex_lt_of_r_lt` | 4 | `hq` | `E₁.q = E₂.q` |
| `Sanctions.Examples.PlacableEconomyF.vertex_lt_of_r_lt` | 5 | `hr` | `E₁.r < E₂.r` |
| `Sanctions.Examples.PlacableEconomyF.vertex_lt_of_r_lt` | 7 | `hx` | `0 < x` |
| `Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop'` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop'` | 3 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop'` | 4 | `hrelief` | `E.ℓhi * E.Mtot < E.klo * E.plo` |
| `Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop'` | 5 | `hN` | `E.ZeroSanctionNeutral` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevel_continuousOn` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevel_continuousOn` | 3 | `hP` | `E.Placable` |
| `Sanctions.AbstractGame.Params.ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur` | 8 | `hT_T` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointTargetOp_sub h_inv (V, W)) (D.jointTargetOp_sub h_inv (V', W')) ≤ β_T * Dist.dist V V' + L_TS * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur` | 9 | `hT_S` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointSenderOp_sub h_inv (V, W)) (D.jointSenderOp_sub h_inv (V', W')) ≤ L_ST * Dist.dist V V' + β_S * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur` | 10 | `hβ_T_lt` | `β_T < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur` | 11 | `hβ_S_lt` | `β_S < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur` | 12 | `hSchur` | `L_TS * L_ST < (1 - β_T) * (1 - β_S)` |
| `Sanctions.AbstractGame.Params.ValueClass2.existsUnique_fixedPoint_in_carrier_schur` | 8 | `hT_T` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointTargetOp_sub h_inv (V, W)) (D.jointTargetOp_sub h_inv (V', W')) ≤ β_T * Dist.dist V V' + L_TS * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.existsUnique_fixedPoint_in_carrier_schur` | 9 | `hT_S` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointSenderOp_sub h_inv (V, W)) (D.jointSenderOp_sub h_inv (V', W')) ≤ L_ST * Dist.dist V V' + β_S * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.existsUnique_fixedPoint_in_carrier_schur` | 10 | `hβ_T_lt` | `β_T < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.existsUnique_fixedPoint_in_carrier_schur` | 11 | `hβ_S_lt` | `β_S < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.existsUnique_fixedPoint_in_carrier_schur` | 12 | `hSchur` | `L_TS * L_ST < (1 - β_T) * (1 - β_S)` |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_strictDecr` | 3 | `h_V_T_dyn_mono` | `Sanctions.StokeyLucas.MonotoneOnSubtype fun x => (p.V_T_dyn (p.V_S (fun x => 0) ⋯) hσc) x` |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_strictDecr` | 4 | `h_antitone` | `∀ x ∈ Sanctions.S, AntitoneOn (fun a => p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x a) Sanctions.I` |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_strictDecr` | 5 | `h_subst_stage` | `∀ x ∈ Sanctions.S, ∀ a ∈ Set.Ioc 0 1, p.U_T x a (p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x a) < p.U_T x 0 (p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x 0)` |
| `Sanctions.Examples.SymbolicEconomyF.persistence_generalF_semiconcave` | 3 | `hMstate0` | `0 ≤ Mstate` |
| `Sanctions.Examples.SymbolicEconomyF.persistence_generalF_semiconcave` | 4 | `hGsc` | `Sanctions.Semiconcave.SemiconcaveOnSet (fun y => E.F y 1) (Set.Icc 0 1) Mstate` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_package` | 7 | `P` | `p.GeneralFPersistencePackage D E xT xS K_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_package` | 9 | `a._@._internal._hyg.0` | `x₀ ∈ Set.Icc (Max.max xT xS) 1` |
| `Sanctions.AbstractGame.Params.jointPreferenceBasinTopF_sanctions_ge_entry` | 8 | `hB` | `p.JointPreferenceBasinTop V_T V_S α xbar sbar` |
| `Sanctions.AbstractGame.Params.jointPreferenceBasinTopF_sanctions_ge_entry` | 9 | `hx₀` | `x₀ ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_local_star` | 5 | `hxbar_mem` | `xbar ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_local_star` | 6 | `hlip` | `Sanctions.AbstractGame.Params.ValueLipschitzWith E.V_S K_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_local_star` | 7 | `hstar` | `∀ x ∈ Set.Icc xbar 1, ∀ s₁ ∈ Set.Ico 0 (Max.max x xbar), p.β_S * K_S * Dist.dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (Max.max x xbar))) < p.U_S x (E.α x) (Max.max x xbar) - p.U_S x (E.α x) s₁` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_local_star` | 8 | `hIDO` | `Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc xbar 1) fun s x => p.senderDynObjective E.V_S x (E.α x) s` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_local_star` | 10 | `a._@._internal._hyg.0` | `x₀ ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tailF_no_relief_of_ratchet` | 7 | `h_ratchet` | `∀ x ∈ Set.Icc xbar 1, x ≤ p.dynamicTopRealizedRule E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tailF_no_relief_of_ratchet` | 8 | `hT` | `p.dynamicTopLockInPathF E.V_S E.α x₀ T ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tailF_no_relief_of_ratchet` | 9 | `hq` | `q < Max.max (p.dynamicTopLockInPathF E.V_S E.α x₀ T) xbar` |
| `Sanctions.AbstractGame.Params.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment` | 2 | `hAdj` | `p.StrictAdjustment` |
| `Sanctions.AbstractGame.Params.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment` | 5 | `hα_cont` | `Continuous α` |
| `Sanctions.AbstractGame.Params.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment` | 8 | `hxbar0` | `0 ≤ xbar` |
| `Sanctions.AbstractGame.Params.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment` | 9 | `h_level_top` | `∀ x ∈ Set.Icc xbar 1, Max.max x sbar ≤ p.dynamicTopRealizedRule V_S α x` |
| `Sanctions.AbstractGame.Params.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment` | 11 | `hx₀` | `x₀ ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn` | 5 | `hstep_mono` | `MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc a b)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn` | 6 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn` | 7 | `hmaps` | `∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn` | 9 | `hx₀` | `x₀ ∈ Set.Icc a b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 2 | `hAdj` | `p.StrictAdjustment` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 6 | `ha0` | `0 ≤ a` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 7 | `hb1` | `b ≤ 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 8 | `hstep_mono` | `MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc a b)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 9 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 10 | `hmaps` | `∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | 12 | `hx₀` | `x₀ ∈ Set.Icc a b` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | 2 | `hAdj` | `p.StrictAdjustment` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | 5 | `hxbar0` | `0 ≤ xbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | 6 | `hxbar1` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | 7 | `hstep_mono` | `MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc xbar 1)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | 8 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | 9 | `hmaps` | `∀ x ∈ Set.Icc xbar 1, p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 7 | `hlo` | `lo < xL` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 8 | `hmid` | `xL ≤ xH` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 9 | `hhi` | `xH < hi` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 10 | `hrule_cont` | `ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc lo hi)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 11 | `hlow_erode` | `∀ x ∈ Set.Ioc lo xL, p.dynamicTopLockInStepF E.V_S E.α x < x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 12 | `hhigh_build` | `∀ x ∈ Set.Ico xH hi, x < p.dynamicTopLockInStepF E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 13 | `hlb` | `∀ x ∈ Set.Icc lo hi, lo ≤ p.dynamicTopLockInStepF E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | 14 | `hub` | `∀ x ∈ Set.Icc lo hi, p.dynamicTopLockInStepF E.V_S E.α x ≤ hi` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 7 | `hs'_mem` | `s' ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 8 | `hm_max` | `IsMaxOn (fun s => p.U_S x a s) Sanctions.I m` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 9 | `hm_greatest` | `∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ m` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 10 | `h_wedge_le` | `∀ d ∈ Sanctions.I, d ≤ m → p.senderSanctionContinuation V_S x d ≤ p.senderSanctionContinuation V_S x m` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 11 | `h_chord` | `p.U_S x a m - p.U_S x a s' < p.β_S * (p.senderSanctionContinuation V_S x s' - p.senderSanctionContinuation V_S x m)` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 13 | `a._@._internal._hyg.0` | `t ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 14 | `a._@._internal._hyg.0` | `IsMaxOn (fun s => p.U_S x a s) Sanctions.I t` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 16 | `a._@._internal._hyg.0` | `d ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | 17 | `a._@._internal._hyg.0` | `IsMaxOn (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s) Sanctions.I d` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 7 | `hm_mem` | `m ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 8 | `hs'_mem` | `s' ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 9 | `hm_max` | `IsMaxOn (fun s => p.U_S x a s) Sanctions.I m` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 10 | `hm_greatest` | `∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ m` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 11 | `h_wedge_mono` | `∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ → p.senderSanctionContinuation V_S x s₁ ≤ p.senderSanctionContinuation V_S x s₂` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 12 | `h_chord` | `p.U_S x a m - p.U_S x a s' < p.β_S * (p.senderSanctionContinuation V_S x s' - p.senderSanctionContinuation V_S x m)` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 14 | `a._@._internal._hyg.0` | `t ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 15 | `a._@._internal._hyg.0` | `IsMaxOn (fun s => p.U_S x a s) Sanctions.I t` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 17 | `a._@._internal._hyg.0` | `d ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | 18 | `a._@._internal._hyg.0` | `IsMaxOn (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s) Sanctions.I d` |
| `Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF` | 3 | `hMyoBasin` | `∀ x ∈ Set.Icc (Max.max C.xT C.xS) 1, p.myopicEquilibriumRule C.M x ∈ Set.Icc (Max.max C.xT C.xS) 1` |
| `Sanctions.Examples.ChordEconomyRelief.closedLoop_unique_attracting_of_lt_one` | 2 | `hL` | `E.Lloop < 1` |
| `Sanctions.Examples.ChordEconomyRelief.closedLoop_unique_attracting_of_sharp_lt_one` | 2 | `hL` | `E.LloopSharp < 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent` | 7 | `P` | `p.SenderPersistencePackage D E xT xS K_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent` | 8 | `hF_top_pre` | `∀ x ∈ Set.Icc 0 (Max.max xT xS), x < p.F x 1` |
| `Sanctions.AbstractGame.fullShockDrift_minima_horizon_mono_of_top_transition_le` | 4 | `hxbar_nn` | `0 ≤ xbar` |
| `Sanctions.AbstractGame.fullShockDrift_minima_horizon_mono_of_top_transition_le` | 5 | `hF₁_top_pre` | `∀ x ∈ Set.Icc 0 xbar, x < p₁.F x 1` |
| `Sanctions.AbstractGame.fullShockDrift_minima_horizon_mono_of_top_transition_le` | 6 | `hF_top_le` | `∀ x ∈ Set.Icc 0 xbar, p₁.F x 1 ≤ p₂.F x 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_nonexit_generalF` | 8 | `hCorner` | `xbar ≤ p.F xbar sbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_nonexit_generalF` | 9 | `hWeak` | `∀ x ∈ Set.Icc xbar 1, sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_nonexit_generalF` | 10 | `hT` | `p.episodePath u x₀ T ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 6 | `hxbar0` | `0 ≤ xbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 7 | `hF_held_pre` | `∀ x ∈ Set.Icc 0 xbar, x < p.F x h` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 8 | `hCorner` | `xbar ≤ p.F xbar sbar` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 9 | `hWeak` | `∀ x ∈ Set.Icc xbar 1, sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 11 | `hu_mem` | `∀ (n : ℕ), u n ∈ Set.Icc 0 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 13 | `hu` | `∀ n < T, h ≤ u n` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 14 | `hT` | `p.highEpisodeHorizon h xbar ≤ T` |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | 16 | `hx₀` | `x₀ ∈ Set.Icc 0 1` |
| `Sanctions.Examples.ChordEconomy.placable_post_episode_nonexit_of_policy_zero` | 3 | `hα` | `∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.ChordEconomy.placable_post_episode_nonexit_of_policy_zero` | 7 | `hT` | `E.episodePath u x₀ T ∈ Set.Icc E.sfloor 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_ratchet` | 8 | `h_ratchet` | `∀ x ∈ Set.Icc xbar 1, x ≤ p.dynamicTopRealizedRule E.V_S E.α x` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_ratchet` | 9 | `h_mono` | `MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1)` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_ratchet` | 10 | `hT` | `p.episodePath u x₀ T ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_ratchet` | 11 | `hq` | `q < Max.max (p.episodePath u x₀ T) xbar` |
| `Sanctions.AbstractGame.Params.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent` | 3 | `hF_bot_post` | `∀ x ∈ Set.Icc xbar 1, p.F x 0 < x` |
| `Sanctions.AbstractGame.Params.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent` | 5 | `a._@._internal._hyg.0` | `x₀ ∈ Set.Icc 0 1` |
| `Sanctions.AbstractGame.Params.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent` | 7 | `a._@._internal._hyg.0` | `n ≥ p.fullReliefExitHorizon xbar` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent` | 6 | `hxbar_le` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent` | 7 | `hF_bot_post` | `∀ x ∈ Set.Icc xbar 1, p.F x 0 < x` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent` | 8 | `h_level_low` | `∀ x ∈ Set.Icc 0 xbar, p.dynamicTopRealizedRule V_S α x ≤ Min.min x sbar_low` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent` | 10 | `hx₀` | `x₀ ∈ Set.Icc 0 1` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF_of_postBasinDescent` | 6 | `hxbar_le` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF_of_postBasinDescent` | 7 | `hF_bot_post` | `∀ x ∈ Set.Icc xbar 1, p.F x 0 < x` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF_of_postBasinDescent` | 8 | `h_level_low` | `∀ x ∈ Set.Icc 0 xbar, p.dynamicTopRealizedRule V_S α x ≤ Min.min x sbar_low` |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF_of_postBasinDescent` | 10 | `hx₀` | `x₀ ∈ Set.Icc 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.stationaryPlannerValue_lockin_dominated_iff` | 3 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief` | 5 | `hrelief` | `E.ℓhi * E.Mtot < E.klo * E.plo` |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief` | 7 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.KaempferLowenberg.FourGroup.pathValue_affineCorner_gap` | 4 | `hδ` | `δ ∈ Set.Ioo 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.pathValue_affineCorner_gap` | 5 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.affineCornerGap_pos_iff` | 4 | `hδ` | `δ ∈ Set.Ioo 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.affineCornerGap_pos_iff` | 5 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.affineCornerGap_pos_all_discounts_iff` | 3 | `hδ` | `δ ∈ Set.Ioo 0 1` |
| `Sanctions.Examples.fourGroupCertHawkScaled_gap_neg` | 3 | `hx0` | `x0 ∈ Set.Icc 0 1` |
| `Sanctions.Examples.fourGroupCertHawkScaled_gap_neg` | 4 | `hb` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.fgcPlannerOptimalValue_eq` | 3 | `hx0` | `x0 ∈ Set.Icc 0 1` |
| `Sanctions.Examples.fgcPlannerOptimalValue_eq` | 4 | `hb` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.fgc_plannerOptimalValue_gap_eq_equilibrium` | 3 | `hx0` | `x0 ∈ Set.Icc 0 1` |
| `Sanctions.Examples.fgc_plannerOptimalValue_gap_eq_equilibrium` | 4 | `hb` | `β ∈ Set.Ico 0 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 9 | `hβ_T_nn` | `0 ≤ β_T` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 10 | `hβ_S_nn` | `0 ≤ β_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 11 | `hL_TS_nn` | `0 ≤ L_TS` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 12 | `hL_ST_nn` | `0 ≤ L_ST` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 13 | `hT_T_op` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointTargetOp_sub h_inv (V, W)) (D.jointTargetOp_sub h_inv (V', W')) ≤ β_T * Dist.dist V V' + L_TS * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 14 | `hT_S_op` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointSenderOp_sub h_inv (V, W)) (D.jointSenderOp_sub h_inv (V', W')) ≤ L_ST * Dist.dist V V' + β_S * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 15 | `hsuff_T` | `β_T + L_TS < 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 16 | `hsuff_S` | `β_S + L_ST < 1` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 19 | `hmS_pos` | `0 < mS` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 20 | `hID_S` | `p.SenderStageIDOn (Set.Icc 0 sbar)` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 21 | `h1_S` | `1 ∈ p.senderFloorFlipSet sbar mS` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 22 | `h_diag_MS` | `∀ (V_T : D.CarrierT) (V_S : D.CarrierS), ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) 1, Sanctions.AbstractGame.Params.LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s) (Set.Icc sbar (Max.max x (Max.max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)))) mS` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 23 | `hV_S_mono_carrier` | `∀ V_S ∈ D.carrier_S, Monotone ⇑V_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 24 | `hIDO_on` | `∀ (V_T : D.CarrierT) (V_S : D.CarrierS), Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc (Max.max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1) fun s x => p.senderDynObjective (↑V_S) x (D.α_on V_T V_S x) s` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 25 | `hMyoCeiling` | `∀ x ∈ Set.Icc (Max.max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1, p.σ x (p.myopicFeedbackEquilibrium_canonical.α x) ≤ Max.max x (Max.max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS))` |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | 26 | `hF_top_pre` | `∀ x ∈ Set.Icc 0 (Max.max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)), x < p.F x 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 8 | `hT_T` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointTargetOp_sub h_inv (V, W)) (D.jointTargetOp_sub h_inv (V', W')) ≤ β_T * Dist.dist V V' + L_TS * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 9 | `hT_S` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointSenderOp_sub h_inv (V, W)) (D.jointSenderOp_sub h_inv (V', W')) ≤ L_ST * Dist.dist V V' + β_S * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 10 | `hβ_T_lt` | `β_T < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 11 | `hβ_S_lt` | `β_S < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 12 | `hSchur` | `L_TS * L_ST < (1 - β_T) * (1 - β_S)` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 19 | `hαE` | `E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | 20 | `hαE'` | `E'.α = D.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩` |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion` | 2 | `hr` | `E.r = 0` |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion` | 3 | `hn` | `E.n = 0` |
| `Sanctions.Examples.ChordEconomy.responsePath_ge_stage_add_wedge` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomy.responsePath_ge_stage_add_wedge` | 4 | `hV` | `V ∈ E.carrierS` |
| `Sanctions.Examples.ChordEconomy.responsePath_ge_stage_add_wedge` | 6 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyTwoSided.targetOnlySanction_add_wedge_le_dynamicSanction` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyTwoSided.targetOnlySanction_add_wedge_le_dynamicSanction` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion_of_policy_zero` | 2 | `hr` | `E.r = 0` |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion_of_policy_zero` | 3 | `hn` | `E.n = 0` |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion_of_policy_zero` | 5 | `hα` | `∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.PlacableEconomyF.exists_welfareCompletion` | 4 | `hB` | `0 < B` |
| `Sanctions.Examples.PlacableEconomyF.dynamicPath_limit_ge_steady10_add_gap` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.placableBoundary_wedge_attained` | 2 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 2 | `hZ` | `E.ZeroSanctionNoGain` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 3 | `hTM` | `E.LossOffset` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 4 | `hmono` | `MonotoneOn (E.responsePath E.VSstar) (Set.Icc 0 1)` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 6 | `hα` | `∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 8 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 10 | `ha` | `∀ (t : ℕ), a t ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | 12 | `hT` | `0 < T` |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief` | 2 | `hZ` | `E.ZeroSanctionNoGain` |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief` | 8 | `ha` | `∀ (t : ℕ), a t ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief` | 10 | `hT` | `0 < T` |
| `Sanctions.Examples.lossOffset_relief_period_benefits_target` | 2 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyRelief.VTdef_lowerSlope` | 2 | `hmono` | `MonotoneOn (E.responsePath E.VSstar) (Set.Icc 0 1)` |
| `Sanctions.Examples.ChordEconomyRelief.VTdef_lowerSlope` | 4 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomyRelief.VTdef_lowerSlope` | 5 | `hginv` | `g * (1 - E.β_T * E.glo) + Max.max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor` |
| `Sanctions.Examples.ChordEconomyRelief.equilibriumTop_sharp` | 2 | `hmono` | `MonotoneOn (E.responsePath E.VSstar) (Set.Icc 0 1)` |
| `Sanctions.Examples.ChordEconomyRelief.equilibriumTop_sharp` | 4 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomyRelief.equilibriumTop_sharp` | 5 | `hginv` | `g * (1 - E.β_T * E.glo) + Max.max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor` |
| `Sanctions.Examples.ChordEconomyRelief.equilibriumTop_sharp` | 6 | `hsharp` | `E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * g` |
| `Sanctions.Examples.ChordEconomyRelief.gSharp_balance` | 2 | `hγ` | `E.β_T * E.LloopSharp < 1` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz` | 3 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz` | 5 | `hV` | `V ∈ E.carrierS2` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz` | 8 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz` | 9 | `hx'` | `x' ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop` | 3 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop` | 4 | `hrel` | `E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel)` |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop` | 5 | `hN` | `E.ZeroSanctionNeutral` |
| `Sanctions.Examples.ChordEconomyCs.bracket_sides_disjoint` | 2 | `hγ` | `E.β_T * E.LloopSharp < 1` |
| `Sanctions.Examples.ChordEconomyCs.bracket_sides_disjoint` | 3 | `hsharp` | `E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT` |
| `Sanctions.Examples.ChordEconomyCs.bracket_sides_disjoint` | 4 | `hrel` | `E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT)` |
| `Sanctions.Examples.ChordEconomy.target_lowerSlope_of_rule_monotone` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomy.target_lowerSlope_of_rule_monotone` | 4 | `hrule` | `MonotoneOn (E.rule Eq) Sanctions.S` |
| `Sanctions.Examples.ChordEconomy.policy_eq_zero_of_rule_monotone` | 2 | `hTM` | `E.LossOffset₀` |
| `Sanctions.Examples.ChordEconomy.policy_eq_zero_of_rule_monotone` | 4 | `hrule` | `MonotoneOn (E.rule Eq) Sanctions.S` |
| `Sanctions.Examples.ChordEconomy.policy_eq_zero_of_rule_monotone` | 6 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.regimeValue11_sub_10_eq` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.regimeValue11_sub_10_eq` | 8 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyF.hawkBounded_nonempty_iff` | 5 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyF.hawkBounded_nonempty_iff` | 6 | `hm` | `0 < m` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval` | 9 | `hm` | `0 < m` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval` | 10 | `hC` | `C.HawkBounded Qbar m M` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | 16 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | 17 | `hhi` | `g ≤ Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 16 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | 17 | `hhi` | `g ≤ Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 15 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | 16 | `hhi` | `0 < Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal` | 8 | `hm1` | `m < 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal` | 9 | `hM1` | `1 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal` | 11 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal` | 13 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyF.exists_equalValuation_completion` | 2 | `hn` | `E.n = 0` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | 15 | `hne` | `Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M ≤ Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | 15 | `hne` | `Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M ≤ Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | 10 | `hm` | `0 < m` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | 11 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | 13 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | 15 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | 15 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | 16 | `hhi` | `0 < Sanctions.Examples.PlacableEconomyFcs.gapAt hTM hmargin C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal` | 8 | `hm1` | `m < 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal` | 9 | `hM1` | `1 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal` | 11 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal` | 13 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | 3 | `h` | `E₁.SameGameButβT E₂.toChordEconomy` |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | 4 | `hβ` | `E₁.β_T ≤ E₂.β_T` |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | 5 | `hmono` | `MonotoneOn (E₁.responsePath E₁.VSstar) (Set.Icc 0 1)` |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | 7 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | 8 | `hginv` | `g * (1 - E₁.β_T * E₁.glo) + Max.max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu) ≤ E₁.vlo + E₁.nlo * E₁.sfloor` |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | 9 | `h₁` | `∃ Eq, ∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.ChordEconomyRelief.balance_of_le_βT` | 3 | `hβ` | `E.β_T ≤ β'` |
| `Sanctions.Examples.ChordEconomyRelief.balance_of_le_βT` | 5 | `hg` | `0 ≤ g` |
| `Sanctions.Examples.ChordEconomyRelief.balance_of_le_βT` | 6 | `hginv` | `g * (1 - E.β_T * E.glo) + Max.max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 2 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 3 | `hMs` | `E.Ms = 0` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 4 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 5 | `hMcx` | `E.Mcx = 0` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 6 | `hMmix` | `E.Mmix = 0` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 7 | `hgd` | `1 ≤ E.glo + E.dlo` |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | 8 | `hβ` | `E.β_T = E.betaStar` |
| `Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_of_tendsto` | 3 | `hs` | `∀ (n : ℕ), E.SameGameButβT (Es n)` |
| `Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_of_tendsto` | 4 | `hlim` | `Filter.Tendsto (fun n => (Es n).β_T) Filter.atTop (nhds E.β_T)` |
| `Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_of_tendsto` | 5 | `hex` | `∀ (n : ℕ), ∃ Eq, ∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.ChordEconomy.defianceExistence_sInf_mem` | 2 | `hpos` | `0 < InfSet.sInf E.defianceExistenceSet` |
| `Sanctions.Examples.ChordEconomyCs.exists_relief_equilibrium_iff` | 4 | `hN` | `E.ZeroSanctionNeutral` |
| `Sanctions.Examples.ChordEconomyCs.VTrel_monotone` | 4 | `hvL` | `E.ℓhi * E.Lalpha ≤ E.vlo` |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_anti_βT` | 10 | `hb` | `b₁ ≤ b₂` |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_anti_βT` | 11 | `hV` | `Monotone ⇑((E.withβT b₁ h₁0 h₁1).VTrel hInt hP) ∨ Monotone ⇑((E.withβT b₂ h₂0 h₂1).VTrel hInt hP)` |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_anti_βT` | 12 | `h₂` | `(E.withβT b₂ h₂0 h₂1).ReliefBestReply hInt hP` |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_of_tendsto` | 10 | `hlim` | `Filter.Tendsto u Filter.atTop (nhds b)` |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_of_tendsto` | 11 | `hbr` | `∀ (n : ℕ), (E.withβT (u n) ⋯ ⋯).ReliefBestReply hInt hP` |
| `Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc` | 3 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc` | 4 | `hN` | `E.ZeroSanctionNeutral` |
| `Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc` | 5 | `hvL` | `E.ℓhi * E.Lalpha ≤ E.vlo` |
| `Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc` | 6 | `hlt` | `SupSet.sSup E.reliefExistenceSet < 1` |
| `Sanctions.Examples.ChordEconomyRelief.defianceExistenceSet_eq_Ico` | 2 | `hmono` | `MonotoneOn (E.responsePath E.VSstar) (Set.Icc 0 1)` |
| `Sanctions.Examples.ChordEconomyRelief.defianceExistenceSet_eq_Ico` | 3 | `hvL` | `E.c * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor` |
| `Sanctions.Examples.ChordEconomyRelief.defianceExistenceSet_eq_Ico` | 4 | `hpos` | `0 < InfSet.sInf E.defianceExistenceSet` |
| `Sanctions.Examples.ChordEconomyCs.reliefExistence_lt_margin` | 3 | `hb` | `b ∈ E.reliefExistenceSet` |
| `Sanctions.AbstractGame.Params.no_dynamic_floor_of_antitone_state_chord` | 4 | `h_U_S_anti` | `∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S, x ≤ y → p.U_S y (α y) s ≤ p.U_S x (α x) s` |
| `Sanctions.AbstractGame.Params.dynamic_stake` | 5 | `hdyn` | `p.stageTopRule α x < p.dynamicTopRealizedRule (p.V_S α hα) α x` |
| `Sanctions.AbstractGame.Params.dynamic_stake_equilibrium` | 4 | `hdyn` | `p.stageTopRule E.α x < p.dynamicTopRealizedRule E.V_S E.α x` |
| `Sanctions.AbstractGame.AbsorbingTop.ratchet_dichotomy` | 5 | `hxbar` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.AbsorbingTop.ratchet_dichotomy` | 6 | `hfeas` | `r 1 ≤ 1` |
| `Sanctions.AbstractGame.AbsorbingTop.rule_top_eq_one_of_floor` | 4 | `hxbar` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.AbsorbingTop.rule_top_eq_one_of_floor` | 5 | `hfeas` | `r 1 ≤ 1` |
| `Sanctions.AbstractGame.AbsorbingTop.rule_top_eq_one_of_floor` | 6 | `h_floor` | `∀ x ∈ Set.Icc xbar 1, Max.max x sbar ≤ r x` |
| `Sanctions.AbstractGame.AbsorbingTop.successor_top_eq_one_of_floor` | 5 | `hxbar` | `xbar ≤ 1` |
| `Sanctions.AbstractGame.AbsorbingTop.successor_top_eq_one_of_floor` | 6 | `hfeas` | `r 1 ≤ 1` |
| `Sanctions.AbstractGame.AbsorbingTop.successor_top_eq_one_of_floor` | 7 | `h_floor` | `∀ x ∈ Set.Icc xbar 1, Max.max x sbar ≤ r x` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 7 | `hm` | `0 ≤ m` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 9 | `hone` | `↑one = 1` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 10 | `hslope` | `∀ (y : ↑Sanctions.S), m * (1 - ↑y) ≤ E.V_S one - E.V_S y` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 11 | `htrans` | `∀ s ∈ Sanctions.I, κ * (1 - s) ≤ 1 - p.F 1 s` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 12 | `hshade0` | `∀ s ∈ Sanctions.I, p.U_S 1 (E.α 1) s - p.U_S 1 (E.α 1) 1 ≤ c * (1 - s)` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 13 | `hshade1` | `∀ s ∈ Sanctions.I, p.U_S 1 (E.α 1 + t) s - p.U_S 1 (E.α 1 + t) 1 ≤ c * (1 - s)` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 14 | `hc` | `c ≤ p.β_S * m * κ` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 15 | `hdev` | `E.α 1 + t ∈ Sanctions.I` |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | 16 | `hgain` | `p.U_T 1 (E.α 1) 1 < p.U_T 1 (E.α 1 + t) 1` |
| `Sanctions.AbstractGame.Params.weakFloor_dynamicTopStepF_mem_basin` | 6 | `hCorner` | `xbar ≤ p.F xbar sbar` |
| `Sanctions.AbstractGame.Params.weakFloor_dynamicTopStepF_mem_basin` | 7 | `hWeak` | `∀ x ∈ Set.Icc xbar 1, sbar ≤ p.dynamicTopRealizedRule V_S α x` |
| `Sanctions.AbstractGame.Params.weakFloor_dynamicTopStepF_mem_basin` | 9 | `hx` | `x ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed` | 7 | `hB` | `p.JointPreferenceBasinTop V_T V_S α xbar sbar` |
| `Sanctions.AbstractGame.Params.senderValue_lowerSlope_of_policy_chord` | 5 | `h_joint_state_chord` | `∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ → g * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s + p.β_S * g * (p.F y₂ s - p.F y₁ s)` |
| `Sanctions.AbstractGame.Params.senderValue_lowerSlope_of_policy_chord` | 7 | `hfix` | `p.bellmanS_BCF α hα V = V` |
| `Sanctions.Examples.ChordEconomy.V_S_lowerSlope_of_antitone` | 2 | `hN` | `E.ZeroSanctionAntitone` |
| `Sanctions.Examples.ChordEconomy.V_S_lowerSlope_of_antitone` | 4 | `hanti` | `AntitoneOn Eq.α Sanctions.S` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 8 | `hL_TS_nn` | `0 ≤ L_TS` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 9 | `hL_ST_nn` | `0 ≤ L_ST` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 10 | `hT_T` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointTargetOp_sub h_inv (V, W)) (D.jointTargetOp_sub h_inv (V', W')) ≤ β_T * Dist.dist V V' + L_TS * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 11 | `hT_S` | `∀ (V V' : D.CarrierT) (W W' : D.CarrierS), Dist.dist (D.jointSenderOp_sub h_inv (V, W)) (D.jointSenderOp_sub h_inv (V', W')) ≤ L_ST * Dist.dist V V' + β_S * Dist.dist W W'` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 12 | `hβ_S_lt` | `β_S < 1` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 13 | `hSchur` | `L_TS * L_ST < (1 - β_T) * (1 - β_S)` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 16 | `hVT` | `E.V_T ∈ D.carrier_T` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 17 | `hVS` | `E.V_S ∈ D.carrier_S` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 18 | `hVT'` | `E'.V_T ∈ D.carrier_T` |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | 19 | `hVS'` | `E'.V_S ∈ D.carrier_S` |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_le` | 3 | `h_V_T_dyn_mono` | `Sanctions.StokeyLucas.MonotoneOnSubtype fun x => (p.V_T_dyn_on (p.V_S (fun x => 0) ⋯) hσc) x` |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_le` | 4 | `h_resp_le` | `∀ x ∈ Sanctions.S, ∀ a ∈ Set.Ioc 0 1, p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x a ≤ p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x 0` |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_le` | 5 | `h_subst_stage` | `∀ x ∈ Sanctions.S, ∀ a ∈ Set.Ioc 0 1, p.U_T x a (p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x a) ≤ p.U_T x 0 (p.σ_dyn_top (p.V_S (fun x => 0) ⋯) x 0)` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_level_star` | 5 | `hxbar_mem` | `xbar ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_level_star` | 6 | `hlip` | `Sanctions.AbstractGame.Params.ValueLipschitzWith E.V_S K_S` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_level_star` | 7 | `hstar` | `∀ x ∈ Set.Icc xbar 1, ∀ s₁ ∈ Set.Ico 0 (Max.max x xbar), p.β_S * K_S * Dist.dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (Max.max x xbar))) < p.U_S x (E.α x) (Max.max x xbar) - p.U_S x (E.α x) s₁` |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_level_star` | 9 | `a._@._internal._hyg.0` | `x₀ ∈ Set.Icc xbar 1` |
| `Sanctions.AbstractGame.Params.equilibriumTop_initial_condition_selects_generalF_of_sender_basins` | 7 | `hHigh` | `p.SenderPersistenceBasinTop E.V_S E.α xbar_high sbar_high` |
| `Sanctions.AbstractGame.Params.equilibriumTop_initial_condition_selects_generalF_of_sender_basins` | 8 | `hLow` | `p.SenderPersistenceBasinLow E.V_S E.α xbar_low sbar_low` |
| `Sanctions.AbstractGame.Params.equilibriumTop_initial_condition_selects_generalF_of_sender_basins` | 9 | `hsep` | `xbar_low < xbar_high` |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | 5 | `hz` | `z ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | 6 | `hz₁₀` | `z₁₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | 7 | `hfix` | `E.responsePath E.VSstar z = z` |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | 8 | `hfix₁₀` | `E.σ z₁₀ 0 = z₁₀` |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | 9 | `hle` | `z₁₀ ≤ z` |
| `Sanctions.Examples.ChordEconomyTwoSided.dynamicPath_limit_ge_limit10_add_gap` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyTwoSided.dynamicPath_limit_ge_limit10_add_gap` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.chSigV_feasible_iff` | 11 | `hβS` | `0 < βS` |
| `Sanctions.Examples.chSigV_feasible_iff` | 12 | `hdhi` | `0 < dhi` |
| `Sanctions.Examples.chSigV_feasible_iff` | 13 | `hghi` | `0 ≤ ghi` |
| `Sanctions.Examples.chSigV_feasible_iff` | 14 | `ha` | `βS * ghi ^ 2 < 1` |
| `Sanctions.Examples.chSigV_feasible_iff` | 15 | `hKS` | `0 ≤ KS` |
| `Sanctions.Examples.chSigV_feasible_iff` | 16 | `hMx` | `0 ≤ Mx` |
| `Sanctions.Examples.chSigV_feasible_iff` | 17 | `hMm` | `0 ≤ Mm` |
| `Sanctions.Examples.chSigV_feasible_iff` | 18 | `hr` | `0 ≤ rhi` |
| `Sanctions.Examples.chSigV_feasible_iff` | 19 | `hσx` | `0 ≤ σx` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_stage` | 2 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_stage` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_stage` | 5 | `hflip` | `E.ℓhi < E.sfloor * E.plo` |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_stage` | 8 | `a._@._internal._hyg.0` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyRelief.unique_attracting_state_of_sharp_lt_one` | 2 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.ChordEconomyRelief.unique_attracting_state_of_sharp_lt_one` | 5 | `hL` | `E.LloopSharp < 1` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 6 | `hband0` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 7 | `hSlo0` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, dl * s ≤ p.F x s - p.F x 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 8 | `hpain0` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 9 | `hstate0` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 10 | `hv` | `0 ≤ v` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 11 | `hcost0` | `∀ x ∈ Set.Icc 0 1, ∀ a ∈ Set.Icc 0 1, p.U_T x a 0 ≤ p.U_T x 0 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 12 | `hTM` | `c ≤ p.β_T * dl * p.defianceSlope gl v` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | 14 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 6 | `hband0` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 7 | `hSlo0` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, dl * s ≤ p.F x s - p.F x 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 8 | `hpain0` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 9 | `hstate0` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 10 | `hv` | `0 ≤ v` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 11 | `hcost0` | `∀ x ∈ Set.Icc 0 1, ∀ a ∈ Set.Icc 0 1, p.U_T x a 0 ≤ p.U_T x 0 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 12 | `hTM` | `c ≤ p.β_T * dl * p.defianceSlope gl v` |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | 14 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | 6 | `hband0` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | 7 | `hSlo0` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, dl * s ≤ p.F x s - p.F x 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | 8 | `hpain0` | `∀ x ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s` |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | 9 | `hstate0` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0` |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | 10 | `hv` | `0 ≤ v` |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | 11 | `hTM` | `c ≤ p.β_T * dl * p.defianceSlope gl v` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 3 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 5 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 6 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 7 | `hQ` | `E.Qbar = E.q` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 8 | `hk` | `E.klo = E.khi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 9 | `hℓ` | `E.ℓlo = E.ℓhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 10 | `hp` | `E.plo = E.c` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 11 | `hv` | `E.vlo = E.vhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 12 | `hnhi` | `E.nhi = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | 13 | `hd` | `E.dlo = E.dhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 3 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 5 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 6 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 7 | `hQ` | `E.Qbar = E.q` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 8 | `hk` | `E.klo = E.khi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 9 | `hℓ` | `E.ℓlo = E.ℓhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 10 | `hp` | `E.plo = E.c` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 11 | `hv` | `E.vlo = E.vhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 12 | `hnhi` | `E.nhi = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 13 | `hd` | `E.dlo = E.dhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | 14 | `hβ1` | `E.betaStar < 1` |
| `Sanctions.Examples.ChordEconomy.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomy.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.target_only_regime_generalF_of_response_monotone` | 2 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.ChordEconomy.dynamicPath_limit_ge_limit10_add_gap_of_response_monotone` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomy.dynamicPath_limit_ge_limit10_add_gap_of_response_monotone` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyF.dynamicPath_limit_ge_steady10_add_gap_of_response_monotone` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.regimeValue11_sub_10_eq_of_response_monotone` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.regimeValue11_sub_10_eq_of_response_monotone` | 8 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval_of_response_monotone` | 9 | `hm` | `0 < m` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval_of_response_monotone` | 10 | `hC` | `C.HawkBounded Qbar m M` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | 16 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | 17 | `hhi` | `g ≤ Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 16 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g` |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | 17 | `hhi` | `g ≤ Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 15 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | 16 | `hhi` | `0 < Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone` | 8 | `hm1` | `m < 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone` | 9 | `hM1` | `1 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone` | 11 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone` | 13 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | 15 | `hne` | `Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M ≤ Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | 15 | `hne` | `Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M ≤ Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | 9 | `hQbar` | `0 < Qbar` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | 10 | `hm` | `0 < m` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | 11 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | 13 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | 15 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | 10 | `hM` | `0 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | 12 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | 14 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | 15 | `hlo` | `Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | 16 | `hhi` | `0 < Sanctions.Examples.PlacableEconomyFcs.gapAtOf hTM hmono C₀.K (Sanctions.Examples.PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone` | 2 | `hInt` | `E.toChordCs.Interior` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone` | 8 | `hm1` | `m < 1` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone` | 9 | `hM1` | `1 < M` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone` | 11 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone` | 13 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.Examples.sfFCert_three_goals_generalF` | 7 | `hcorner` | `Sanctions.TransitionChords.CornerSectionTop F (1 / 2)` |
| `Sanctions.Examples.sfFCert_three_goals_generalF` | 8 | `hlo` | `Sanctions.TransitionChords.SanctionLowerChord F d` |
| `Sanctions.Examples.sfFCert_three_goals_generalF` | 9 | `hd` | `11 / 36 ≤ d` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 5 | `hF_mem` | `∀ (x s : ℝ), x ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 → F x s ∈ Set.Icc 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 6 | `hF_mono_x` | `∀ (s : ℝ), Monotone fun x => F x s` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 7 | `hF_mono_s` | `∀ (x : ℝ), Monotone fun s => F x s` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 8 | `hL` | `Sanctions.TransitionChords.SanctionUpperChord F L` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 9 | `hband` | `∀ y₁ ∈ Set.Icc 0 1, ∀ y₂ ∈ Set.Icc 0 1, y₁ ≤ y₂ → F y₂ 0 - F y₁ 0 ≤ lam * (y₂ - y₁)` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 11 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 12 | `hβlam` | `β * lam < 1` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 13 | `hB` | `0 ≤ G.b_J - G.b_K` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 14 | `hmargin` | `G.g_J - G.q_K + β * (G.b_J - G.b_K) * L / (1 - β * lam) ≤ G.d_s` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | 16 | `hx0` | `x0 ∈ Set.Icc 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 3 | `hF_mem` | `∀ (x s : ℝ), x ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 → F x s ∈ Set.Icc 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 4 | `hF_mono_x` | `∀ (s : ℝ), Monotone fun x => F x s` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 5 | `hF_mono_s` | `∀ (x : ℝ), Monotone fun s => F x s` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 7 | `hβ` | `β ∈ Set.Ico 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 8 | `hB` | `G.b_J - G.b_K ≤ 0` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 9 | `hmargin` | `G.g_J - G.q_K ≤ G.d_s` |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | 11 | `hx0` | `x0 ∈ Set.Icc 0 1` |
| `Sanctions.KaempferLowenberg.FourGroup.exists_hawkRescale_cornerF_gap_neg` | 2 | `hg` | `0 < G.g_J` |
| `Sanctions.KaempferLowenberg.FourGroup.exists_hawkRescale_cornerF_gap_pos` | 2 | `hg` | `G.g_J < 0` |
| `Sanctions.AbstractGame.Params.rulePathF_no_cycles` | 3 | `hR_mem` | `∀ x ∈ Sanctions.I, R x ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.rulePathF_no_cycles` | 4 | `hR_mono` | `MonotoneOn R Sanctions.I` |
| `Sanctions.AbstractGame.Params.rulePathF_no_cycles` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.equilibrium_no_cycles` | 3 | `hmono` | `MonotoneOn (p.dynamicEquilibriumRule E) Sanctions.I` |
| `Sanctions.AbstractGame.Params.equilibrium_no_cycles` | 5 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyRelief.myopic_no_cycles` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyCs.senderOnly_no_cycles` | 7 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.targetOnly_no_cycles` | 4 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomyTwoSided.dynamic_no_cycles` | 5 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.Examples.LQData.characterisation` | 2 | `hInt` | `P.E.Interior` |
| `Sanctions.Examples.LQData.characterisation` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.characterisation` | 4 | `hP` | `P.E.Placable` |
| `Sanctions.Examples.LQData.relief_iff` | 2 | `hInt` | `P.E.Interior` |
| `Sanctions.Examples.LQData.relief_iff` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.relief_iff` | 4 | `hP` | `P.E.Placable` |
| `Sanctions.Examples.LQData.defiance_iff` | 2 | `hInt` | `P.E.Interior` |
| `Sanctions.Examples.LQData.defiance_iff` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.defiance_iff` | 4 | `hP` | `P.E.Placable` |
| `Sanctions.Examples.LQData.no_relief_above` | 2 | `hInt` | `P.E.Interior` |
| `Sanctions.Examples.LQData.no_relief_above` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.no_relief_above` | 4 | `hP` | `P.E.Placable` |
| `Sanctions.Examples.LQData.no_relief_above` | 5 | `hβ` | `P.E.betaStar < P.βT` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 3 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 5 | `hN` | `E.ZeroSanctionNeutral` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 6 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 7 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 8 | `hQ` | `E.Qbar = E.q` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 9 | `hk` | `E.klo = E.khi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 10 | `hℓ` | `E.ℓlo = E.ℓhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 11 | `hp` | `E.plo = E.c` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 12 | `hv` | `E.vlo = E.vhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 13 | `hnhi` | `E.nhi = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | 14 | `hd` | `E.dlo = E.dhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 2 | `hInt` | `E.Interior` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 3 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 4 | `hP` | `E.Placable` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 5 | `hN` | `E.ZeroSanctionNeutral` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 6 | `hSigV` | `E.SigV = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 7 | `hτ` | `E.τx = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 8 | `hQ` | `E.Qbar = E.q` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 9 | `hk` | `E.klo = E.khi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 10 | `hℓ` | `E.ℓlo = E.ℓhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 11 | `hp` | `E.plo = E.c` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 12 | `hv` | `E.vlo = E.vhi` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 13 | `hnhi` | `E.nhi = 0` |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | 14 | `hd` | `E.dlo = E.dhi` |
| `Sanctions.Examples.LQData.threshold_continuum` | 2 | `hInt` | `P.E.Interior` |
| `Sanctions.Examples.LQData.threshold_continuum` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.threshold_continuum` | 4 | `hP` | `P.E.Placable` |
| `Sanctions.Examples.LQData.threshold_continuum` | 5 | `hβ` | `P.βT = P.E.betaStar` |
| `Sanctions.Examples.LQData.relief_unique_carrier` | 2 | `hInt` | `P.E.Interior` |
| `Sanctions.Examples.LQData.relief_unique_carrier` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.relief_unique_carrier` | 4 | `hP` | `P.E.Placable` |
| `Sanctions.Examples.LQData.relief_unique_carrier` | 5 | `hβ` | `P.βT < P.E.betaStar` |
| `Sanctions.Examples.LQData.relief_unique_carrier` | 7 | `hVS` | `Eq.V_S ∈ P.E.carrierS2` |
| `Sanctions.Examples.LQData.entrenchment` | 3 | `hSR` | `P.E.StageRelief` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 3 | `hδ` | `P₁.δ = P₂.δ` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 4 | `hu` | `P₁.u₀ = P₂.u₀` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 5 | `hw` | `P₁.w = P₂.w` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 6 | `hk` | `P₁.k = P₂.k` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 7 | `hq` | `P₁.q = P₂.q` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 8 | `hℓ` | `P₁.ℓ = P₂.ℓ` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 9 | `hc` | `P₁.c = P₂.c` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 10 | `hv` | `P₁.v = P₂.v` |
| `Sanctions.Examples.LQData.comparative_statics_βS` | 11 | `hβ` | `P₁.βS < P₂.βS` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 3 | `hδ` | `P₁.δ = P₂.δ` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 4 | `hu` | `P₁.u₀ = P₂.u₀` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 5 | `hβS` | `P₁.βS = P₂.βS` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 6 | `hk` | `P₁.k = P₂.k` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 7 | `hq` | `P₁.q = P₂.q` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 8 | `hℓ` | `P₁.ℓ = P₂.ℓ` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 9 | `hc` | `P₁.c = P₂.c` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 10 | `hv` | `P₁.v = P₂.v` |
| `Sanctions.Examples.LQData.comparative_statics_w` | 11 | `hw` | `P₁.w < P₂.w` |
| `Sanctions.Examples.LQData.comparative_statics_δ` | 3 | `hβS` | `P₁.βS = P₂.βS` |
| `Sanctions.Examples.LQData.comparative_statics_δ` | 4 | `hu` | `P₁.u₀ = P₂.u₀` |
| `Sanctions.Examples.LQData.comparative_statics_δ` | 5 | `hw` | `P₁.w = P₂.w` |
| `Sanctions.Examples.LQData.comparative_statics_δ` | 6 | `hk` | `P₁.k = P₂.k` |
| `Sanctions.Examples.LQData.comparative_statics_δ` | 7 | `hq` | `P₁.q = P₂.q` |
| `Sanctions.Examples.LQData.comparative_statics_δ` | 8 | `hδ` | `P₁.δ < P₂.δ` |
| `Sanctions.Examples.LQData.betaStar_indep` | 3 | `hδ` | `P₁.δ = P₂.δ` |
| `Sanctions.Examples.LQData.betaStar_indep` | 4 | `hq` | `P₁.q = P₂.q` |
| `Sanctions.Examples.LQData.betaStar_indep` | 5 | `hk` | `P₁.k = P₂.k` |
| `Sanctions.Examples.LQData.betaStar_indep` | 6 | `hℓ` | `P₁.ℓ = P₂.ℓ` |
| `Sanctions.Examples.LQData.betaStar_indep` | 7 | `hc` | `P₁.c = P₂.c` |
| `Sanctions.Examples.LQData.betaStar_indep` | 8 | `hv` | `P₁.v = P₂.v` |
| `Sanctions.Examples.AQClass.lq_affineQuad_classification` | 2 | `hF` | `E.F = Sanctions.AbstractGame.affineF E.δ` |
| `Sanctions.Examples.AQClass.lq_affineQuad_classification` | 3 | `hn` | `E.n = 0` |
| `Sanctions.Examples.AQClass.lq_affineQuad_classification` | 4 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.AQClass.lq_affineQuad_classification` | 11 | `hC` | `Sanctions.Examples.AQClass.AffineQuadClass E.toChordCs.toParams Eq E.q a₀ a₁ S₂ S₁ S₀` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 2 | `hF` | `E.F = Sanctions.AbstractGame.affineF E.δ` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 3 | `hn` | `E.n = 0` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 4 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 7 | `hβ` | `E.βT < Sanctions.Examples.AQClass.betaR E.δ E.q E.k E.r E.ℓ E.c E.v` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 14 | `hpol` | `∀ x ∈ Sanctions.I, Eq.α x = a₀ + a₁ * x` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 15 | `hlt` | `∀ x ∈ Sanctions.I, Eq.α x < 1` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 16 | `hV` | `∀ (y : ↑Sanctions.S), Eq.V_S y = S₂ * ↑y ^ 2 + S₁ * ↑y + S₀` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 17 | `hQ` | `2 * E.βS * E.δ ^ 2 * S₂ < E.q` |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | 18 | `hrule` | `(∀ x ∈ Sanctions.I, E.toChordCs.dynamicEquilibriumRule Eq x ∈ Set.Ioo 0 1) ∨ ∀ x ∈ Sanctions.I, E.toChordCs.dynamicEquilibriumRule Eq x = 0` |
| `Sanctions.Examples.AQClass.lq_affineQuad_defiance` | 2 | `hF` | `E.F = Sanctions.AbstractGame.affineF E.δ` |
| `Sanctions.Examples.AQClass.lq_affineQuad_defiance` | 3 | `hn` | `E.n = 0` |
| `Sanctions.Examples.AQClass.lq_affineQuad_defiance` | 4 | `hSR` | `E.StageRelief` |
| `Sanctions.Examples.AQClass.lq_affineQuad_defiance` | 11 | `hC` | `Sanctions.Examples.AQClass.AffineQuadClass E.toChordCs.toParams Eq E.q a₀ a₁ S₂ S₁ S₀` |
| `Sanctions.Examples.AQClass.lq_affineQuad_defiance` | 12 | `hdef` | `∀ x ∈ Sanctions.I, Eq.α x = 0` |
| `Sanctions.Examples.ChordEconomyRelief.target_only_limit_lt_net` | 2 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.ChordEconomyRelief.target_only_limit_lt_net` | 6 | `hx₀` | `x₀ ∈ Sanctions.I` |
| `Sanctions.AbstractGame.Params.dynamicTopRealizedRule_eq_stageTopRule_of_stateFree` | 4 | `hflat` | `∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S, p.U_S y (α y) s = p.U_S x (α x) s` |
| `Sanctions.Examples.ChordEconomy.hostile_wedge` | 4 | `hw` | `0 < w` |
| `Sanctions.Examples.ChordEconomy.hostile_wedge` | 5 | `hH1` | `∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ → (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁))` |
| `Sanctions.Examples.ChordEconomy.hostile_wedge` | 6 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.ChordEconomy.hostile_wedge` | 8 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.hostile_relief_price` | 5 | `hw₀` | `0 < w₀` |
| `Sanctions.Examples.ChordEconomy.hostile_relief_price` | 6 | `hH1₀` | `∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ → (E.hostileParams κ).U_S x₂ 0 0 - (E.hostileParams κ).U_S x₁ 0 0 ≤ -(w₀ * (x₂ - x₁))` |
| `Sanctions.Examples.ChordEconomy.hostile_relief_price` | 7 | `hPC` | `E.PlacationCeiling khi` |
| `Sanctions.Examples.ChordEconomy.hostile_relief_price` | 8 | `hPs` | `E.uhi < E.klo` |
| `Sanctions.Examples.ChordEconomy.hostile_relief_price` | 10 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.hostile_sanction_pos` | 3 | `hH3` | `E.β_S * Sanctions.Examples.chKS E.β_S E.ghi (κ - E.wlo) * E.dhi < E.ulo` |
| `Sanctions.Examples.ChordEconomy.hostile_sanction_pos` | 5 | `hx` | `x ∈ Sanctions.I` |
| `Sanctions.Examples.ChordEconomy.hostile_full_defiance_bounds` | 4 | `hw` | `0 < w` |
| `Sanctions.Examples.ChordEconomy.hostile_full_defiance_bounds` | 5 | `hH1` | `∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ → (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁))` |
| `Sanctions.Examples.ChordEconomy.hostile_full_defiance_bounds` | 6 | `hS` | `E.uhi < E.q` |
| `Sanctions.Examples.ChordEconomy.hostile_full_defiance_bounds` | 8 | `hdef` | `∀ x ∈ Sanctions.S, EH.α x = 0` |
| `Sanctions.Examples.dbσ_eq_zero_of_le` | 3 | `hx` | `x ≤ 1 / 4` |
| `Sanctions.Examples.dbσ_eq_zero_of_le` | 4 | `ha` | `0 ≤ a` |
| `Sanctions.Examples.dualRep_rule_eq_zero` | 2 | `hx` | `x ∈ Sanctions.S` |
| `Sanctions.Examples.dualRep_rule_eq_zero_of_carrier` | 2 | `hVT` | `E.V_T ∈ Sanctions.Examples.dbCarrierT` |
| `Sanctions.Examples.dualRep_rule_eq_zero_of_carrier` | 4 | `hx` | `x ∈ Sanctions.S` |

## Per-root summary

| root | kind | telescope | binders | explicit | candidates |
|---|---|---|---|---|---|
| `Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent` | theorem | 5 | 5 | 3 | 0 |
| `Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent` | theorem | 5 | 5 | 3 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level` | theorem | 10 | 10 | 7 | 0 |
| `Sanctions.AbstractGame.Params.theorem2_dynamic_dominates_myopic_at_same_alpha` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.AbstractGame.Params.shockEntryHorizon_bound` | theorem | 5 | 5 | 3 | 0 |
| `Sanctions.Examples.eeCert_three_goals_dominance` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.eeCertMS_generalF_three_goals` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.eeCertMS_three_goals_dominance` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.qbCertMS_generalF_three_goals` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.lbLow_generalF_three_goals` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.wobbleEconMS_three_goals_full` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.b2NonMono_three_goals_dominance` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.b2_integrated_mechanism_active_generalF_witness` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.fourGroupCert_three_goals_dominance` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.boxTransfer_existsUnique_invariant_attracting` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.dualParams_initial_condition_selects` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.eeCertB_equilibrium_feedback_decomposition` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.eeCertB_equilibrium_lockin_strict` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.eeCertB_lockin_amplification` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.eeCertB_VT_star_βS_invariant` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.plannerW_distortion` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.plannerW_lockin_dominated_iff` | theorem | 1 | 1 | 1 | 0 |
| `Sanctions.Examples.fgc_planner_inefficiency_equilibrium` | theorem | 4 | 4 | 2 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_sender_package` | theorem | 9 | 9 | 4 | 0 |
| `Sanctions.Examples.SymbolicEconomyF.persistence_generalF` | theorem | 1 | 1 | 1 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_long_run_nonDecreasing` | theorem | 7 | 7 | 4 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent` | theorem | 8 | 8 | 5 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` | theorem | 10 | 10 | 7 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_invariant` | theorem | 9 | 9 | 8 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins` | theorem | 16 | 16 | 12 | 0 |
| `Sanctions.Examples.qbCert_three_goals_generalF` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_net` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.placableQuadDiag_both_channels_active` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.AbstractGame.Params.σ_dyn_top_monotoneOn_x_of_singleCrossing` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_net_of_margin` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.placableAffine_unique_attracting_state` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.target_only_regime_net_core` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.dualParams_two_sided_regimes` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.ChordEconomyCs.four_cell_net_generalF` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief_net` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.ChordEconomy.targetObj_strictAntiOn_of_sharp` | theorem | 12 | 12 | 7 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop_rule_eq_zero` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyCs.defiance_not_maxOn_of_relief_side` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyCs.collapse_sides'` | theorem | 15 | 15 | 15 | 0 |
| `Sanctions.Examples.ChordEconomy.unique_equilibrium_of_rule_monotone` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone` | theorem | 8 | 8 | 6 | 0 |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance` | theorem | 7 | 7 | 5 | 0 |
| `Sanctions.AbstractGame.Params.defiance_branch_invariance_generalF` | theorem | 9 | 9 | 7 | 0 |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.leader_optimal_against_history_deviation_top` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_completions_reversing_regime_ranking` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_le_V_T` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT` | theorem | 9 | 9 | 6 | 0 |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone` | theorem | 19 | 19 | 12 | 0 |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast_history` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.Examples.ChordEconomy.reliefPayoff_isGreatest_history` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance` | theorem | 7 | 7 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.no_zero_rule_equilibrium` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le` | theorem | 18 | 18 | 18 | 0 |
| `Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks` | theorem | 14 | 14 | 10 | 0 |
| `Sanctions.Welfare.zeroSanction_planner_optimal` | theorem | 23 | 23 | 23 | 0 |
| `Sanctions.Examples.ChordEconomyCs.exists_reps_reversing_regime_ranking` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.ChordEconomy.planner_efficient_rep_at_policy_zero` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.AbstractGame.Params.target_tipping_threshold` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.AbstractGame.Params.sender_tipping_threshold` | theorem | 7 | 7 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.ChordEconomy.VSstar_fix` | theorem | 1 | 1 | 1 | 0 |
| `Sanctions.Examples.exists_member_response_monotone_not_margin` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.rally_softening_interval_iff` | theorem | 17 | 17 | 6 | 0 |
| `Sanctions.Examples.lossOffset_iff_v_ge` | theorem | 11 | 11 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefSharp_uniform_iff` | theorem | 9 | 9 | 4 | 0 |
| `Sanctions.Examples.sigV_feasible_iff` | theorem | 17 | 17 | 8 | 0 |
| `Sanctions.Examples.PlacableEconomyF.derived_fields` | theorem | 1 | 1 | 1 | 0 |
| `Sanctions.Examples.ChordEconomyCs.four_cell_generalF'` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.ChordEconomyCs.four_cell_rule_chain_of_policy_zero` | theorem | 10 | 10 | 10 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.ChordEconomy.target_only_regime_generalF_core` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyTwoSided.target_only_regime_generalF` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.PlacableEconomyF.targetOnlyPath_error_le_geometric` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyF.steady10_lt_of_r_lt` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.PlacableEconomyF.vertex_lt_of_r_lt` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF'` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop'` | def | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyCs.zeroLevel_continuousOn` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.AbstractGame.Params.ValueClass2.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur` | theorem | 12 | 12 | 7 | 0 |
| `Sanctions.AbstractGame.Params.ValueClass2.existsUnique_fixedPoint_in_carrier_schur` | theorem | 12 | 12 | 7 | 0 |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_strictDecr` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.SymbolicEconomyF.persistence_generalF_semiconcave` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_from_package` | theorem | 9 | 9 | 4 | 0 |
| `Sanctions.AbstractGame.Params.jointPreferenceBasinTopF_sanctions_ge_entry` | theorem | 10 | 10 | 4 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_local_star` | theorem | 10 | 10 | 8 | 0 |
| `Sanctions.Examples.persistence_package_not_unique_steady_state` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_tailF_no_relief_of_ratchet` | theorem | 10 | 10 | 5 | 0 |
| `Sanctions.AbstractGame.Params.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment` | theorem | 11 | 11 | 8 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn` | theorem | 9 | 9 | 6 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn` | theorem | 12 | 12 | 9 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn` | theorem | 9 | 9 | 8 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_derived_dual_basins'` | theorem | 14 | 14 | 10 | 0 |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_of_wedge_le` | theorem | 17 | 17 | 13 | 0 |
| `Sanctions.AbstractGame.Params.all_stage_lt_dynamic_of_greatest_stage_improvement_mono` | theorem | 18 | 18 | 14 | 0 |
| `Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.closedLoop_unique_attracting_of_lt_one` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.closedLoop_unique_attracting_of_sharp_lt_one` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.placableQuadDiag_unique_attracting_state` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent` | theorem | 8 | 8 | 3 | 0 |
| `Sanctions.AbstractGame.fullShockDrift_minima_horizon_mono_of_top_transition_le` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_nonexit_generalF` | theorem | 10 | 10 | 8 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` | theorem | 16 | 16 | 10 | 0 |
| `Sanctions.Examples.ChordEconomy.placable_post_episode_nonexit_of_policy_zero` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_ratchet` | theorem | 11 | 11 | 9 | 0 |
| `Sanctions.AbstractGame.Params.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent` | theorem | 11 | 11 | 8 | 0 |
| `Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF_of_postBasinDescent` | theorem | 10 | 10 | 7 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.stationaryPlannerValue_lockin_dominated_iff` | theorem | 3 | 3 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyCs.both_channels_active_of_relief` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.placableReliefOnly_not_flip` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.pathValue_affineCorner_gap` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.affineCornerGap_pos_iff` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.affineCornerGap_pos_all_discounts_iff` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.Examples.fourGroupCertHawkScaled_gap_neg` | theorem | 4 | 4 | 2 | 0 |
| `Sanctions.Examples.fgcPlannerOptimalValue_eq` | theorem | 4 | 4 | 2 | 0 |
| `Sanctions.Examples.fgc_plannerOptimalValue_gap_eq_equilibrium` | theorem | 4 | 4 | 2 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent` | theorem | 26 | 26 | 19 | 0 |
| `Sanctions.Examples.sfCert_three_goals_generalF` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur` | theorem | 20 | 20 | 15 | 0 |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.ChordEconomy.responsePath_ge_stage_add_wedge` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyTwoSided.targetOnlySanction_add_wedge_le_dynamicSanction` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.Examples.PlacableEconomyF.exists_planner_efficient_completion_of_policy_zero` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyF.exists_welfareCompletion` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.Examples.PlacableEconomyF.dynamicPath_limit_ge_steady10_add_gap` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.placableBoundary_wedge_attained` | theorem | 2 | 2 | 1 | 0 |
| `Sanctions.Examples.ChordEconomyTwoSided.equilibriumTop_of_margin_α_eq_zero` | theorem | 5 | 5 | 5 | 1 |
| `Sanctions.Examples.ChordEconomy.relief_participation_of_policy_zero` | theorem | 12 | 12 | 9 | 0 |
| `Sanctions.Examples.ChordEconomy.no_date_zero_transfer_supports_relief` | theorem | 10 | 10 | 7 | 0 |
| `Sanctions.Examples.lossOffset_relief_period_benefits_target` | theorem | 2 | 2 | 1 | 0 |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.follower_optimal_against_history_deviation_top` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.follower_node_optimal_against_history_deviation_top` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.VTdef_lowerSlope` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.equilibriumTop_sharp` | def | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.gSharp_balance` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyCs.zeroLevelAt_lipschitz` | theorem | 9 | 9 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyCs.VTrel_lipschitz` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop` | def | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyCs.bracket_sides_disjoint` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.exists_bracket_both_sides_nonaffine` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.ChordEconomy.target_lowerSlope_of_rule_monotone` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.policy_eq_zero_of_rule_monotone` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.regimeValue11_sub_10_eq` | theorem | 8 | 8 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyF.hawkBounded_nonempty_iff` | theorem | 6 | 6 | 2 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval` | theorem | 14 | 14 | 8 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender` | theorem | 17 | 17 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained` | theorem | 17 | 17 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle` | theorem | 16 | 16 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal` | theorem | 13 | 13 | 8 | 0 |
| `Sanctions.Examples.PlacableEconomyF.exists_completion_bJ_eq_bK_iff` | theorem | 1 | 1 | 1 | 0 |
| `Sanctions.Examples.PlacableEconomyF.exists_equalValuation_completion` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff` | theorem | 15 | 15 | 9 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff` | theorem | 15 | 15 | 9 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff` | theorem | 15 | 15 | 9 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle` | theorem | 16 | 16 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal` | theorem | 13 | 13 | 8 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` | theorem | 9 | 9 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.balance_of_le_βT` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.Examples.aw_zero_rule_iff` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.aw_full_defiance_iff` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.aw_window_at_β₁` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.aw_continuum` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_of_tendsto` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.defianceExistence_sInf_mem` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.defiance_core_outside_chord_class` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.strict_interior_equilibrium_in_chord_class` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.ChordEconomyCs.exists_relief_equilibrium_iff` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyCs.VTrel_monotone` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_anti_βT` | theorem | 12 | 12 | 10 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefBestReply_of_tendsto` | theorem | 11 | 11 | 10 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.defianceExistenceSet_eq_Ico` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyCs.reliefExistence_lt_margin` | theorem | 3 | 3 | 2 | 0 |
| `Sanctions.Examples.aw_general_hypotheses` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.aw_exact_thresholds` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.AbstractGame.Params.no_dynamic_floor_of_antitone_state_chord` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.AbstractGame.Params.dynamic_stake` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.AbstractGame.Params.dynamic_stake_equilibrium` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.AbstractGame.AbsorbingTop.ratchet_dichotomy` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.AbstractGame.AbsorbingTop.rule_top_eq_one_of_floor` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.AbstractGame.AbsorbingTop.successor_top_eq_one_of_floor` | theorem | 7 | 7 | 5 | 0 |
| `Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain` | theorem | 16 | 16 | 16 | 0 |
| `Sanctions.AbstractGame.Params.weakFloor_dynamicTopStepF_mem_basin` | theorem | 9 | 9 | 6 | 0 |
| `Sanctions.AbstractGame.Params.WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed` | theorem | 7 | 7 | 2 | 0 |
| `Sanctions.AbstractGame.Params.senderValue_lowerSlope_of_policy_chord` | theorem | 7 | 7 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.V_S_lowerSlope_of_antitone` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur_of_mem` | theorem | 19 | 19 | 14 | 0 |
| `Sanctions.AbstractGame.Params.feedbackStackelbergTop_corner_of_substituted_stage_le` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.AbstractGame.Params.standardCompliance_persistence_generalF_level_star` | theorem | 9 | 9 | 7 | 0 |
| `Sanctions.AbstractGame.Params.equilibriumTop_initial_condition_selects_generalF_of_sender_basins` | theorem | 9 | 9 | 5 | 0 |
| `Sanctions.Examples.ChordEconomy.fixedPoint_ge_limit10_add_gap` | theorem | 9 | 9 | 7 | 0 |
| `Sanctions.Examples.ChordEconomyTwoSided.dynamicPath_limit_ge_limit10_add_gap` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.chSigV_feasible_iff` | theorem | 19 | 19 | 9 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.both_channels_active_of_margin_stage` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.unique_attracting_state_of_sharp_lt_one` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history` | theorem | 14 | 14 | 9 | 0 |
| `Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history` | theorem | 14 | 14 | 9 | 0 |
| `Sanctions.AbstractGame.Params.reliefPayoff_le_V_T` | theorem | 14 | 14 | 9 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet` | theorem | 13 | 13 | 12 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds` | theorem | 14 | 14 | 13 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage_of_response_monotone` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.ChordEconomy.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.Examples.ChordEconomy.target_only_regime_generalF_of_response_monotone` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyCs.four_cell_generalF'_of_response_monotone` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.ChordEconomy.dynamicPath_limit_ge_limit10_add_gap_of_response_monotone` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyF.dynamicPath_limit_ge_steady10_add_gap_of_response_monotone` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_completions_reversing_regime_ranking_of_response_monotone` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.regimeValue11_sub_10_eq_of_response_monotone` | theorem | 8 | 8 | 5 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.gap_mem_interval_of_response_monotone` | theorem | 14 | 14 | 8 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_withSender_of_response_monotone` | theorem | 17 | 17 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.gap_attained_of_response_monotone` | theorem | 17 | 17 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone` | theorem | 16 | 16 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone` | theorem | 13 | 13 | 8 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone` | theorem | 15 | 15 | 9 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone` | theorem | 15 | 15 | 9 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone` | theorem | 15 | 15 | 9 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone` | theorem | 16 | 16 | 10 | 0 |
| `Sanctions.Examples.PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone` | theorem | 13 | 13 | 8 | 0 |
| `Sanctions.Examples.persistence_package_not_unique_steady_state_generalF` | theorem | 1 | 1 | 1 | 0 |
| `Sanctions.Examples.sfFCert_three_goals_generalF` | theorem | 9 | 9 | 3 | 0 |
| `Sanctions.Examples.sfqbCert_three_goals_generalF` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords` | theorem | 16 | 16 | 11 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos` | theorem | 11 | 11 | 8 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.exists_hawkRescale_cornerF_gap_neg` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.KaempferLowenberg.FourGroup.exists_hawkRescale_cornerF_gap_pos` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.AbstractGame.Params.rulePathF_no_cycles` | theorem | 6 | 6 | 4 | 0 |
| `Sanctions.AbstractGame.Params.equilibrium_no_cycles` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_no_cycles` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyCs.senderOnly_no_cycles` | theorem | 7 | 7 | 6 | 0 |
| `Sanctions.Examples.ChordEconomy.targetOnly_no_cycles` | theorem | 4 | 4 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyTwoSided.dynamic_no_cycles` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.LQData.characterisation` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.LQData.relief_iff` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.LQData.defiance_iff` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.LQData.no_relief_above` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.collapse_regimes_tight` | theorem | 14 | 14 | 13 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.collapse_relief_iff_tight` | theorem | 14 | 14 | 13 | 0 |
| `Sanctions.Examples.LQData.threshold_continuum` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.LQData.relief_unique_carrier` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.LQData.entrenchment` | theorem | 4 | 4 | 4 | 0 |
| `Sanctions.Examples.LQData.comparative_statics_βS` | theorem | 11 | 11 | 11 | 0 |
| `Sanctions.Examples.LQData.comparative_statics_w` | theorem | 11 | 11 | 11 | 0 |
| `Sanctions.Examples.LQData.comparative_statics_δ` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.LQData.betaStar_indep` | theorem | 8 | 8 | 8 | 0 |
| `Sanctions.Examples.lw_witness` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.AQClass.lq_affineQuad_classification` | theorem | 11 | 11 | 6 | 0 |
| `Sanctions.Examples.AQClass.lq_affineQuad_relief_unique_below_betaR` | theorem | 18 | 18 | 13 | 0 |
| `Sanctions.Examples.AQClass.lq_affineQuad_defiance` | theorem | 12 | 12 | 7 | 0 |
| `Sanctions.Examples.AWWhole.aw_exists_on_window` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyCs.four_cell_net` | theorem | 7 | 7 | 7 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_net` | theorem | 6 | 6 | 6 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.target_only_regime_net` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.target_only_limit_lt_net` | theorem | 6 | 6 | 5 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.placable_family_defiance_net` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.exists_netDefiance_not_lossOffset` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.exists_netDefiance_not_lossOffset_nonaffine` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.AbstractGame.Params.dynamicTopRealizedRule_eq_stageTopRule_of_stateFree` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.hostile_wedge` | theorem | 8 | 8 | 6 | 0 |
| `Sanctions.Examples.ChordEconomy.hostile_relief_price` | theorem | 10 | 10 | 7 | 0 |
| `Sanctions.Examples.ChordEconomy.hostile_sanction_pos` | theorem | 5 | 5 | 4 | 0 |
| `Sanctions.Examples.ChordEconomy.hostile_full_defiance_bounds` | theorem | 8 | 8 | 7 | 0 |
| `Sanctions.Examples.ChordEconomy.target_only_regime_any_stake` | theorem | 3 | 3 | 3 | 0 |
| `Sanctions.Examples.ChordEconomyRelief.myopic_regime_any_stake` | theorem | 5 | 5 | 5 | 0 |
| `Sanctions.Examples.hsw_full_defiance_bounds` | theorem | 3 | 3 | 1 | 0 |
| `Sanctions.Examples.db_political_parts_zero_at_full_trade` | theorem | 2 | 2 | 2 | 0 |
| `Sanctions.Examples.dbσ_eq_zero_of_le` | theorem | 4 | 4 | 2 | 0 |
| `Sanctions.Examples.db_entrenchment_loss_after_episode` | theorem | 0 | 0 | 0 | 0 |
| `Sanctions.Examples.dualRep_rule_eq_zero` | theorem | 2 | 2 | 1 | 0 |
| `Sanctions.Examples.dualRep_rule_eq_zero_of_carrier` | theorem | 4 | 4 | 3 | 0 |

## Limits

- A value eta-reduced below its type's binder count leaves the remaining binders as arguments of a constant; the probe then counts them as used (conservative).
- Auxiliary lemmas are inlined four levels deep; a binder that disappears only deeper would be reported as used (conservative).
- Structure fields consumed through a structure-typed binder are not itemised here; the field-level audit is the census (`docs/HYPOTHESIS-CENSUS.md`) and the graph (`docs/CODEGRAPH-EVALUATION-2026-08-20.md`).
- Roots without a value are skipped, not inspected; they are listed in the per-root summary (none in this run).
