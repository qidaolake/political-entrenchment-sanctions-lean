/-
Sanctions/Examples/B2GeneralFPersistenceWitness.lean

## Integrated positive-discount, off-corner persistence witness

This module applies the explicit paper-facing general-`F` persistence
package to the B2 economy.  One constructed equilibrium simultaneously
has:

* strictly positive discount factors for both players;
* a genuinely interior forward-looking Sender sanction at `x = 1/2`;
* the complete general-`F` persistence floor; and
* the quantitative minimum-drift shock conclusion.

The concrete B2 transition is the affine partial-adjustment member of
the general `F` class.  Thus this file verifies that the transition-
general theorem and the off-corner persistence mechanism coexist in one
economy, but it does not claim a nonlinear-transition off-corner
witness or an interior Target policy.

No assumption is added: every field is discharged from
`b2Certificate`, the equilibrium construction on `b2Class`, and the
affine-to-exact-chord lemmas.
-/

import Sanctions.Examples.B2NonMonotoneCertWitness
import Sanctions.Theory.Mechanism.ContinuationStakes
import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Certificates.GeneralFDischargers
-- `affine_transitionChordPack`.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.Bridges

namespace Sanctions
namespace Examples

open Set AbstractGame Params AbstractGame.Params

noncomputable section

/-- The B2 affine transition satisfies the maintained strict-adjustment
condition F5. -/
theorem b2Params_strictAdjustment : b2Params.StrictAdjustment :=
  AbstractGame.strictAdjustment_of_F_eq_affineF
    b2Params (by constructor <;> norm_num) rfl

/-- **Integrated B2 witness for the explicit general-`F` wrappers.**

The same constructed equilibrium carries both value memberships,
has a strictly interior realized sanction at the basin pivot, satisfies
the complete persistence result for every basin start, and satisfies
the positive-minimum-drift shock result for every feasible shock start.

The theorem deliberately states the two positive discount facts and
the off-corner inequality in its conclusion so the economic features
are kernel-checked rather than left in documentation. -/
theorem b2_integrated_generalF_persistence_witness :
    ∃ E : b2Params.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ b2CarrierT
      ∧ E.V_S ∈ b2CarrierS
      ∧ E.α (1/2) = 0
      ∧ 0 < b2Params.β_T
      ∧ 0 < b2Params.β_S
      ∧ (0 < b2Params.dynamicTopRealizedRule E.V_S E.α (1/2)
          ∧ b2Params.dynamicTopRealizedRule E.V_S E.α (1/2) < 1)
      ∧ b2Params.dynamicTopRealizedRule E.V_S E.α (1/2) = 7/8
      ∧ b2Params.σ (1/2) (b2Myopic.α (1/2)) = 5/14
      ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (1/2 : ℝ) 1)
          ∧ (∀ n, (1/2 : ℝ) ≤
                    b2Params.dynamicTopLockInSanctionsF
                      E.V_S E.α x₀ n)
          ∧ Monotone
              (b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (1/2),
            η = b2Params.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (1/2),
            η ≤ b2Params.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          b2Params.shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))
              ∈ Set.Icc (1/2 : ℝ) 1
          ∧ (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α
                    (b2Params.shockPathF x₀shock
                      (Nat.ceil ((1/2 : ℝ) / η))) n
                    ∈ Set.Icc (1/2 : ℝ) 1)
          ∧ (∀ n, (1/2 : ℝ) ≤
                    b2Params.dynamicTopLockInSanctionsF E.V_S E.α
                      (b2Params.shockPathF x₀shock
                        (Nat.ceil ((1/2 : ℝ) / η))) n)
          ∧ Monotone
              (b2Params.dynamicTopLockInSanctionsF E.V_S E.α
                (b2Params.shockPathF x₀shock
                  (Nat.ceil ((1/2 : ℝ) / η)))) := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    b2Class.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      b2Certificate.h_inv
      b2Certificate.hβ_T_nn b2Certificate.hβ_S_nn
      b2Certificate.hL_TS_nn b2Certificate.hL_ST_nn
      b2Certificate.hT_T_op b2Certificate.hT_S_op
      b2Certificate.hsuff_T b2Certificate.hsuff_S
  let V_T_sub : b2Class.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : b2Class.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = b2Class.α_on V_T_sub V_S_sub at hα_eq
  have hTarget :
      b2Params.TargetCombinedChordOn
        b2Class (1/2 : ℝ) (max (1/2 : ℝ) (1/2)) := by
    rw [max_self]
    exact
      b2Params.Target_combined_chord_of_decomposition_lowerChord
        b2Certificate.hxT_mem
        (dlo := b2Params.δ)
        (b2Params.affine_transitionChordPack (δ := b2Params.δ) rfl).1
        (by norm_num)
        (by simp only [b2Params_β_T, b2Params_δ]; norm_num)
        b2_h_stage_target_loss
        b2_hV_T_gain
  have hP :
      b2Params.GeneralFPersistencePackage
        b2Class E (1/2 : ℝ) (1/2 : ℝ) 2 := by
    refine
      { xT_mem := b2Certificate.hxT_mem
        xS_mem := b2Certificate.hxS_mem
        target_value_mem := hVT
        sender_value_mem := hVS
        target_policy_eq := hα_eq
        sender_carrier_lipschitz := b2Certificate.hV_S_lip_carrier
        sender_IDO_after_target_policy := b2Certificate.hIDO_on
        sender_subpivot_chord := ?_
        target_combined_chord := hTarget }
    -- P5 in pivot-star form on the basin (round BJ1.3): the pairwise chord
    -- from the certificate, read once against the pivot.
    intro V_T V_S x hx s₁ hs₁
    simp only [max_self] at hx hs₁ ⊢
    have hstage :=
      b2Certificate.h_stage_sender_on V_T V_S x hx
    have hchord :=
      b2Params.sender_transition_adjusted_chord_of_affine_lowerSlope
        rfl b2Certificate.hKS_nonneg b2Certificate.hS_margin hstage
    exact hchord s₁ ⟨hs₁.1, hs₁.2.le⟩ (max x (1 / 2 : ℝ))
      ⟨le_trans hs₁.1 hs₁.2.le, le_rfl⟩ hs₁.2
  have hPersist :=
    b2Params.standardCompliance_persistence_generalF_from_package hP
  have hShock :=
    b2Params.standardCompliance_min_drift_shock_generalF_from_package
      hP b2Params_strictAdjustment (by norm_num)
  have hα_zero : E.α = fun _ => (0 : ℝ) := by
    calc
      E.α = b2Class.α_on V_T_sub V_S_sub := hα_eq
      _ = fun _ => (0 : ℝ) := b2_α_on_eq_zero V_T_sub V_S_sub
  have hxhalf : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by norm_num, by norm_num⟩
  have hzero : (0 : ℝ) ∈ Sanctions.I :=
    ⟨le_rfl, zero_le_one⟩
  have hUnique := b2_DAU_on_carrier hVS
  have hσ :
      b2Params.σ_dyn_top E.V_S (1/2 : ℝ) 0 =
        b2sdyn (1/2 : ℝ) 0 := by
    rw [← b2Params.σ_dyn_eq_σ_dyn_top_of_unique
      E.V_S (1/2 : ℝ) 0 (hUnique (1/2 : ℝ) hxhalf 0)]
    exact b2_σ_dyn_eq hVS hxhalf hzero
  have hInterior :
      0 < b2Params.dynamicTopRealizedRule E.V_S E.α (1/2)
        ∧ b2Params.dynamicTopRealizedRule E.V_S E.α (1/2) < 1 := by
    unfold AbstractGame.Params.dynamicTopRealizedRule
    rw [hα_zero, hσ]
    norm_num [b2sdyn, b2pt, b2clip, b2lam]
  have hAlphaPivot : E.α (1/2) = 0 := by
    rw [hα_zero]
  have hDynamicPivot :
      b2Params.dynamicTopRealizedRule E.V_S E.α (1/2) = 7/8 := by
    unfold AbstractGame.Params.dynamicTopRealizedRule
    rw [hα_zero, hσ]
    norm_num [b2sdyn, b2pt, b2clip, b2lam]
  have hMyopicPivot :
      b2Params.σ (1/2) (b2Myopic.α (1/2)) = 5/14 := by
    norm_num [b2Params, b2Myopic, b2σ, b2vertex, b2e, b2pt,
      b2clip, b2lam, b2rho]
  have hPersist' :
      ∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
        (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1)
        ∧ (∀ n, (1/2 : ℝ) ≤
                  b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
        ∧ Monotone
            (b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
    simpa only [max_self] using hPersist
  have hShock' :
      ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (1/2),
            η = b2Params.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (1/2),
            η ≤ b2Params.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          b2Params.shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))
              ∈ Set.Icc (1/2 : ℝ) 1
          ∧ (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α
                    (b2Params.shockPathF x₀shock
                      (Nat.ceil ((1/2 : ℝ) / η))) n
                    ∈ Set.Icc (1/2 : ℝ) 1)
          ∧ (∀ n, (1/2 : ℝ) ≤
                    b2Params.dynamicTopLockInSanctionsF E.V_S E.α
                      (b2Params.shockPathF x₀shock
                        (Nat.ceil ((1/2 : ℝ) / η))) n)
          ∧ Monotone
              (b2Params.dynamicTopLockInSanctionsF E.V_S E.α
                (b2Params.shockPathF x₀shock
                  (Nat.ceil ((1/2 : ℝ) / η)))) := by
    simpa only [max_self] using hShock
  exact
    ⟨E, hVT, hVS, hAlphaPivot,
      (by norm_num : 0 < b2Params.β_T),
      (by norm_num : 0 < b2Params.β_S), hInterior,
      hDynamicPivot, hMyopicPivot, hPersist', hShock'⟩

/-- The dynamic conclusions carried by the integrated B2 equilibrium.

This predicate only packages conclusions already proved by
`b2_integrated_generalF_persistence_witness`; it adds no assumption. -/
def B2IntegratedGeneralFOutcome
    (E : b2Params.FeedbackStackelbergEquilibriumTop) : Prop :=
  E.α (1/2) = 0
  ∧ 0 < b2Params.β_T
  ∧ 0 < b2Params.β_S
  ∧ (0 < b2Params.dynamicTopRealizedRule E.V_S E.α (1/2)
      ∧ b2Params.dynamicTopRealizedRule E.V_S E.α (1/2) < 1)
  ∧ b2Params.dynamicTopRealizedRule E.V_S E.α (1/2) = 7/8
  ∧ b2Params.σ (1/2) (b2Myopic.α (1/2)) = 5/14
  ∧ (∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
      (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α x₀ n
                ∈ Set.Icc (1/2 : ℝ) 1)
      ∧ (∀ n, (1/2 : ℝ) ≤
                b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
      ∧ Monotone
          (b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀))
  ∧ ∃ η : ℝ, 0 < η
    ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (1/2),
        η = b2Params.fullShockDrift xmin)
    ∧ (∀ x ∈ Set.Icc (0 : ℝ) (1/2),
        η ≤ b2Params.fullShockDrift x)
    ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
      b2Params.shockPathF x₀shock (Nat.ceil ((1/2 : ℝ) / η))
          ∈ Set.Icc (1/2 : ℝ) 1
      ∧ (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α
                (b2Params.shockPathF x₀shock
                  (Nat.ceil ((1/2 : ℝ) / η))) n
                ∈ Set.Icc (1/2 : ℝ) 1)
      ∧ (∀ n, (1/2 : ℝ) ≤
                b2Params.dynamicTopLockInSanctionsF E.V_S E.α
                  (b2Params.shockPathF x₀shock
                    (Nat.ceil ((1/2 : ℝ) / η))) n)
      ∧ Monotone
          (b2Params.dynamicTopLockInSanctionsF E.V_S E.α
            (b2Params.shockPathF x₀shock
              (Nat.ceil ((1/2 : ℝ) / η))))

/-- **Mechanism-active integrated B2 witness.**

The same equilibrium used by the general-`F` persistence and shock
application has nonconstant Target and Sender continuation values.
More strongly, their discounted changes between explicit feasible
states are exactly `9/2` and `1/4`.  Hence neither continuation channel
is silenced by a constant value function. -/
theorem b2_integrated_mechanism_active_generalF_witness :
    ∃ E : b2Params.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ b2CarrierT
      ∧ E.V_S ∈ b2CarrierS
      ∧ b2Params.β_T *
          (E.V_T (Sanctions.clipS' 1) -
            E.V_T (Sanctions.clipS' 0)) = 9/2
      ∧ b2Params.β_S *
          (E.V_S (Sanctions.clipS' (1/2)) -
            E.V_S (Sanctions.clipS' 0)) = 1/4
      ∧ B2IntegratedGeneralFOutcome E := by
  obtain
      ⟨E, hVT, hVS, hα, hβT, hβS, hInterior,
        hDynamicPivot, hMyopicPivot, hPersist, hShock⟩ :=
    b2_integrated_generalF_persistence_witness
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hhalf : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hVTzero := b2CarrierT_apply hVT hzero
  have hVTone := b2CarrierT_apply hVT hone
  have hVSzero := b2CarrierS_apply hVS hzero
  have hVShalf := b2CarrierS_apply hVS hhalf
  have hTargetWedge :
      b2Params.β_T *
          (E.V_T (Sanctions.clipS' 1) -
            E.V_T (Sanctions.clipS' 0)) = 9/2 := by
    rw [b2Params_β_T]
    norm_num at hVTzero hVTone ⊢
    linarith
  have hSenderWedge :
      b2Params.β_S *
          (E.V_S (Sanctions.clipS' (1/2)) -
            E.V_S (Sanctions.clipS' 0)) = 1/4 := by
    rw [b2Params_β_S]
    norm_num [b2base] at hVSzero hVShalf ⊢
    linarith
  exact
    ⟨E, hVT, hVS, hTargetWedge, hSenderWedge,
      hα, hβT, hβS, hInterior, hDynamicPivot, hMyopicPivot,
      hPersist, hShock⟩

end


/-- **The B2 economy has nondegenerate continuation stakes.**

`ContinuationStakesNondegenerate` (`Theory/Mechanism/ContinuationStakes.lean`) is
the named form of what `b2_integrated_mechanism_active_generalF_witness`
establishes with exact magnitudes: both discounted continuation values vary.
Only the positivity of `9/2` and `1/4` is consumed here. This is the *value*
property; the behavioural one — that the continuation changes an optimal action
— is `ContinuationChangesChoice.lean`, and B2's own name for it
(`mechanism_active`) predates and is stronger than this predicate. -/
theorem b2_continuationStakesNondegenerate :
    ∃ E : b2Params.FeedbackStackelbergEquilibriumTop,
      b2Params.ContinuationStakesNondegenerate E := by
  obtain ⟨E, _hVT, _hVS, hT, hS, _hOut⟩ :=
    b2_integrated_mechanism_active_generalF_witness
  exact ⟨E, AbstractGame.Params.continuationStakesNondegenerateOn_of_eq_pos b2Params
    (by norm_num) (by norm_num) hT hS⟩

#print axioms b2_continuationStakesNondegenerate

end Examples
end Sanctions
