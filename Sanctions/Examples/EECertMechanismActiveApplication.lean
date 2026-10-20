/-
Sanctions/Examples/EECertMechanismActiveApplication.lean

## A mechanism-active equilibrium application

The nonlinear interior witness proves that positive discounting,
interior actions, a non-affine transition, and the full persistence
conclusion are logically compatible, but its equilibrium values are
zero.  The Eaton--Engers certificate supplies the complementary
economic application:

* both equilibrium values are strictly increasing in the political
  state;
* at an explicit Sender comparison, the stage payoff prefers the lower
  sanction but the complete forward-looking objective prefers the
  higher sanction;
* at an explicit Target comparison, the stage payoff also prefers the
  lower sanction but the complete forward-looking objective prefers
  the higher sanction; and
* the same equilibrium satisfies general-transition basin invariance,
  the sanction floor, sanction monotonicity, and dominance over the
  canonical myopic regime.

Thus continuation values are behaviorally active rather than merely
nonzero.  The construction introduces no assumption and changes no
headline theorem; it only packages consequences of the existing
certificate.
-/

import Sanctions.Examples.EECertWitnessMS
import Sanctions.Theory.Mechanism.ContinuationChangesChoice

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame AbstractGame.Params

noncomputable section

/-- **Sender continuation reversal.**  At state zero and full Target
compliance, the Sender's one-period payoff strictly prefers zero
sanctions to full sanctions.  Every value in the certified Sender
carrier has slope `16/3`; with positive discounting, its continuation
gain reverses that ranking in the complete dynamic objective. -/
theorem eeCert_sender_continuation_reversal
    {V_S : Val} (hV_S : V_S ∈ eeCarrierS) :
    eeCertParams.U_S 0 1 1 < eeCertParams.U_S 0 1 0
      ∧ eeCertParams.senderDynObjective V_S 0 1 0
          < eeCertParams.senderDynObjective V_S 0 1 1 := by
  constructor
  · norm_num [eeCertParams_U_S, eecU_S]
  · have hdiff :=
      gainBall_clip_diff (c := (16 / 3 : ℝ)) (M := 12)
        (by norm_num) (mem_eeCarrierS_num hV_S)
        (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    have hF0 : eeCertParams.F 0 0 = 0 := by
      rw [eeCertParams_F]
      norm_num
    have hF1 : eeCertParams.F 0 1 = 1 / 2 := by
      rw [eeCertParams_F]
      norm_num
    apply (eeCertParams.senderDynObjective_lt_iff_continuation_gain_gt_stage_loss
      V_S 0 1 0 1).2
    rw [hF0, hF1]
    simp only [eeCertParams_U_S, eeCertParams_β_S]
    unfold eecU_S
    nlinarith [hdiff]

/-- **Target continuation reversal.**  At the basin pivot and zero
compliance, the Target's one-period payoff strictly prefers zero
sanctions to full sanctions.  Every value in the certified Target
carrier has slope `82/11`; its discounted political-state gain reverses
that ranking in the Target's complete sanction objective. -/
theorem eeCert_target_continuation_reversal
    {V_T : Val} (hV_T : V_T ∈ eeCarrierT) :
    eeCertParams.U_T (1 / 10) 0 1
        < eeCertParams.U_T (1 / 10) 0 0
      ∧ eeCertParams.targetSanctionObjective V_T (1 / 10) 0 0
          < eeCertParams.targetSanctionObjective V_T (1 / 10) 0 1 := by
  constructor
  · norm_num [eeCertParams_U_T, eecU_T]
  · have hdiff :=
      gainBall_clip_diff (c := (82 / 11 : ℝ)) (M := 80)
        (by norm_num) (mem_eeCarrierT_num hV_T)
        (show (1 / 20 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show (11 / 20 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    have hF0 : eeCertParams.F (1 / 10) 0 = 1 / 20 := by
      rw [eeCertParams_F]
      norm_num
    have hF1 : eeCertParams.F (1 / 10) 1 = 11 / 20 := by
      rw [eeCertParams_F]
      norm_num
    apply (eeCertParams.targetSanctionObjective_lt_iff_continuation_gain_gt_stage_loss
      V_T (1 / 10) 0 0 1).2
    rw [hF0, hF1]
    simp only [eeCertParams_U_T, eeCertParams_β_T]
    unfold eecU_T
    nlinarith [hdiff]

/-- **Integrated mechanism-active application.**  One
feedback-Stackelberg equilibrium of the Eaton--Engers economy has
strictly increasing Target and Sender values, exhibits both
continuation reversals above, and satisfies the complete high-basin
general-transition persistence and myopic-dominance conclusions.

Economically, the first two strict inequalities say that political
capital has positive shadow value for both players.  The two paired
reversals say more: continuation value changes the ranking of sanctions
relative to the stage game, so the dynamic mechanism is behaviorally
active. -/
theorem eeCertMS_mechanism_active_integrated_application :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT
      ∧ E.V_S ∈ eeCarrierS
      ∧ E.V_T (Sanctions.clipS' 0) < E.V_T (Sanctions.clipS' 1)
      ∧ E.V_S (Sanctions.clipS' 0) < E.V_S (Sanctions.clipS' 1)
      ∧ (eeCertParams.U_S 0 1 1 < eeCertParams.U_S 0 1 0
          ∧ eeCertParams.senderDynObjective E.V_S 0 1 0
              < eeCertParams.senderDynObjective E.V_S 0 1 1)
      ∧ (eeCertParams.U_T (1 / 10) 0 1
            < eeCertParams.U_T (1 / 10) 0 0
          ∧ eeCertParams.targetSanctionObjective E.V_T (1 / 10) 0 0
              < eeCertParams.targetSanctionObjective E.V_T (1 / 10) 0 1)
      ∧ (∀ x₀ ∈ Set.Icc (1 / 10 : ℝ) 1,
          (∀ n, eeCertParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (1 / 10 : ℝ) 1)
          ∧ (∀ n, (1 / 10 : ℝ) ≤
                    eeCertParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
          ∧ Monotone
              (eeCertParams.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (1 / 10 : ℝ) 1,
          eeCertParams.σ x
              ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
            ≤ eeCertParams.dynamicTopRealizedRule E.V_S E.α x) := by
  obtain ⟨E, hVT, hVS, hpaths, hdom, _hshock⟩ :=
    eeCertCertificateMS.three_goals_local_MS_generalF
      (p := eeCertParams)
      (AbstractGame.affineF_hF_top
        (show (1 / 2 : ℝ) ∈ Set.Ioo 0 1 by constructor <;> norm_num))
  have hVTdiff :=
    gainBall_clip_diff (c := (82 / 11 : ℝ)) (M := 80)
      (by norm_num) (mem_eeCarrierT_num hVT)
      (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
      (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hVSdiff :=
    gainBall_clip_diff (c := (16 / 3 : ℝ)) (M := 12)
      (by norm_num) (mem_eeCarrierS_num hVS)
      (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
      (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  refine ⟨E, hVT, hVS, ?_, ?_,
    eeCert_sender_continuation_reversal hVS,
    eeCert_target_continuation_reversal hVT, ?_, ?_⟩
  · nlinarith [hVTdiff]
  · nlinarith [hVSdiff]
  · change
      ∀ x₀ ∈ Set.Icc (max (1 / 10 : ℝ) (1 / 10)) 1,
        (∀ n, eeCertParams.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (max (1 / 10 : ℝ) (1 / 10)) 1)
        ∧ (∀ n, max (1 / 10 : ℝ) (1 / 10) ≤
                  eeCertParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
        ∧ Monotone
            (eeCertParams.dynamicTopLockInSanctionsF E.V_S E.α x₀)
        at hpaths
    simpa only [max_self] using hpaths
  · change
      ∀ x ∈ Set.Icc (max (1 / 10 : ℝ) (1 / 10)) 1,
        eeCertParams.σ x
            ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
          ≤ eeCertParams.dynamicTopRealizedRule E.V_S E.α x
        at hdom
    simpa only [max_self] using hdom


/-! ## The Sender reversal, in the named vocabulary (Rule 5)

`eeCert_sender_continuation_reversal` exhibits the reversal at two points:
the stage payoff prefers `s = 0` to `s = 1`, and the forward-looking objective
prefers `1` to `0`. That is the *chord* hypothesis of
`sender_dynamic_sanctions_gt_myopic_at_same_action`, not yet its conclusion.
Adding that the stage argmax at `(0, 1)` is unique (it is `0`: the stage
parabola's vertex sits at `−1/5`, below the feasible interval) and that the
continuation wedge rises (every carrier member has lower state-slope `16/3`),
the general theorem upgrades the two-point reversal to the argmax statement:
no forward-looking maximizer is stage-optimal. Parametric over the carrier, as
the reversal already was. -/

/-- **The stage argmax at `(0,1)` is unique, and it is `0`.** -/
theorem eeCert_stage_isMaxOn_eq_zero {s : ℝ} (hs : s ∈ Sanctions.I)
    (hmax : IsMaxOn (fun t => eeCertParams.U_S 0 1 t) Sanctions.I s) : s = 0 := by
  have h0 : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have h := hmax h0
  simp only [Set.mem_setOf_eq, eeCertParams_U_S, eecU_S] at h
  have hle : s ≤ 0 := by nlinarith [sq_nonneg s, hs.1]
  exact le_antisymm hle hs.1

/-- **The continuation wedge rises at `x = 0`**, for every carrier member. -/
theorem eeCert_senderSanctionContinuation_strictMono {V_S : Val} (hV_S : V_S ∈ eeCarrierS) :
    ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      eeCertParams.senderSanctionContinuation V_S 0 s₁
        < eeCertParams.senderSanctionContinuation V_S 0 s₂ :=
  eeCertParams.senderSanctionContinuation_strictMono_of_separated_primitives V_S
    ⟨le_rfl, zero_le_one⟩
    (fun s₁ _ s₂ _ h => by rw [eeCertParams_F, eeCertParams_F]; linarith)
    (fun y₁ hy₁ y₂ hy₂ h => by
      have hd := gainBall_clip_diff (c := (16 / 3 : ℝ)) (M := 12)
        (by norm_num) (mem_eeCarrierS_num hV_S) hy₁ hy₂
      linarith)

/-- **The continuation changes the Sender's optimal sanction at `(0, 1)`**, for
every carrier value function. -/
theorem eeCert_continuationChangesSenderChoice {V_S : Val} (hV_S : V_S ∈ eeCarrierS) :
    eeCertParams.ContinuationChangesSenderChoiceAt V_S 0 1 := by
  apply AbstractGame.Params.continuationChangesSenderChoiceAt_of_strict_ordering
  intro sM hsM sD hsD hstage hdyn
  rw [eeCert_stage_isMaxOn_eq_zero hsM hstage]
  have h0 : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_rfl⟩
  have hstage0 : IsMaxOn (fun t => eeCertParams.U_S 0 1 t) Sanctions.I 0 := by
    have := eecσ_isMaxOn 0 1
    have hσ : eecσ 0 1 = 0 := by unfold eecσ; norm_num
    rw [hσ] at this
    exact this
  -- the chord is the second conjunct of the reversal, rearranged
  have hchord : eeCertParams.U_S 0 1 0 - eeCertParams.U_S 0 1 1
      < eeCertParams.β_S *
          (eeCertParams.senderSanctionContinuation V_S 0 1
            - eeCertParams.senderSanctionContinuation V_S 0 0) := by
    have := (eeCert_sender_continuation_reversal hV_S).2
    simp only [AbstractGame.Params.senderDynObjective,
      AbstractGame.Params.senderSanctionContinuation] at this ⊢
    linarith
  exact eeCertParams.sender_dynamic_sanctions_gt_myopic_at_same_action V_S
    h0 hsD h1 hstage0 hdyn (by norm_num)
    (eeCert_senderSanctionContinuation_strictMono hV_S) hchord

#print axioms eeCert_continuationChangesSenderChoice

end

end Examples
end Sanctions

#print axioms Sanctions.Examples.eeCert_sender_continuation_reversal
#print axioms Sanctions.Examples.eeCert_target_continuation_reversal
#print axioms Sanctions.Examples.eeCertMS_mechanism_active_integrated_application
