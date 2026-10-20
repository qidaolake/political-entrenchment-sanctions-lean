/-
Sanctions/Examples/EECertWitnessMS.lean

**The FIRST instantiation of the MS-form certificate
`StandardComplianceLocalCoreCertificate_MS` (Step-0, affine transition;
2026-07-02).**

The MS-form certificate is the input to the general-transition headline
`standardCompliance_three_goals_local_MS_generalF`; until this file it had
ZERO instantiations, so the general-`F` route was vacuously conditional.
This file instantiates it at the certificate-complete witness economy
`eeCertParams` (affine `F`, which satisfies the general-`F` route's
strict-ascent hypothesis `hF_top` via `affineF_hF_top`), making both MS
headlines fire unconditionally.

## Field provenance (structure-inspection map, 2026-07-02)

* Verbatim reuse from `EECertWitness`: the value class `D := eeCertClass`,
  Bellman invariance `h_inv`, the decoupled Schur row block
  (`β_T = 9/10, β_S = 1/2, L_TS = L_ST = 0` — byte-identical field shapes
  between the legacy and MS structures), the basin pivots `1/10`, and the
  interval-dominance field `hIDO_on` (identical field, filled by the same
  single-crossing upcast).
* Cheap derivations: `hV_S_mono_carrier` from the gain-ball discharger
  `monotone_of_mem_valLipGainBall`; `h_stage_sender_strictMono` from the
  legacy stage lower-slope lemma restricted to the smaller MS interval;
  `h_target_combined` through the affine-free R45 converter
  `Target_combined_chord_of_decomposition_lowerChord` fed by the
  stage-loss lemma restated on the wider MS chord domain (identical
  proof body) and the carrier `V_T` gain lemma; the transition enters
  only through the sanction lower chord, discharged at this affine
  economy by `affine_transitionChordPack`.
* The ONE genuinely new proof: `hMyoCeiling`. The MS certificate pins the
  myopic comparator to `myopicFeedbackEquilibrium_canonical`, whose policy
  is `Classical.choose` of SOME stage argmax — an opaque selection. The
  discharge goes through the **myopic argmax floor**
  (`eeCert_myopic_argmax_floor`): at the witness payoffs EVERY stage
  argmax of the myopic Target objective `a ↦ U_T(x, a, σ(x, a))` lies at
  or above `min 1 ((5x+10)/11)` — proved by strict dominance across the
  three σ-clip branches (the myopic objective falls at rate 1/10 on the
  σ-saturated branch, rises at rate ≥ 6 on the placation branch, falls at
  rate 1/5 on the σ = 0 branch; the dominance gap at the floor is ≥ 0.46
  on the whole basin). Then σ-antitonicity in the compliance action gives
  `σ(x, canonical α) ≤ σ(x, floor) ≤ x`, which is the MS ceiling
  `max x (max xT xS) = x` on the basin.

Rule 3: NO new assumptions — this is an existence certificate (Rule 3's
explicit exception), and every lemma is proved from the existing surface.
Rule 5: the certificate is the allowed witness-specific existence case;
the floor lemma is witness-specific by nature (it computes the witness's
own argmax).
-/

import Sanctions.Examples.EECertWitness
import Sanctions.Theory.Basin.StageFlipCertificate
import Sanctions.Theory.Certificates.GeneralFDischargers
-- `affine_transitionChordPack`.
import Sanctions.Examples.AffineInstance.Certificates

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The myopic argmax floor

Every stage argmax of the myopic Target objective at `eeCertParams` lies
at or above the explicit floor `min 1 ((5x+10)/11)` — the argmax is in
fact unique, but the floor is all the canonical (`Classical.choose`)
comparator needs. -/

/-- **Myopic argmax floor.** Any `a ∈ [0,1]` that maximizes the myopic
Target objective `a' ↦ U_T(x, a', σ(x, a'))` on `[0,1]` satisfies
`min 1 ((5x+10)/11) ≤ a`, for every basin state `x ∈ [1/10, 1]`. -/
theorem eeCert_myopic_argmax_floor {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 10 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => eeCertParams.U_T x a' (eeCertParams.σ x a'))
      Sanctions.I a) :
    min 1 ((5 * x + 10)/11) ≤ a := by
  by_contra hcon
  rw [not_le] at hcon
  have hx0 : (1/10 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have ha0 : (0 : ℝ) ≤ a := ha.1
  have ha1 : a ≤ 1 := ha.2
  set τ : ℝ := min 1 ((5 * x + 10)/11) with hτ_def
  have hτ0 : (0 : ℝ) ≤ τ := by
    rw [hτ_def]; exact le_min (by norm_num) (by linarith)
  have hτ1 : τ ≤ 1 := by rw [hτ_def]; exact min_le_left _ _
  have hτ_hi : τ ≤ (5 * x + 10)/11 := by rw [hτ_def]; exact min_le_right _ _
  have hτ_lo : (5 * x + 5)/11 ≤ τ := by
    rw [hτ_def]; exact le_min (by linarith) (by linarith)
  have hτ_mem : τ ∈ Sanctions.I := ⟨hτ0, hτ1⟩
  have hτle : eecU_T x τ (eecσ x τ) ≤ eecU_T x a (eecσ x a) := hmax hτ_mem
  -- τ always lies in the interior-branch closure, so σ(x, τ) is affine.
  have hστ : eecσ x τ = x + 2 - 11/5 * τ := by
    unfold eecσ
    rw [min_eq_right (by linarith : x + 2 - 11/5 * τ ≤ 1),
        max_eq_right (by linarith : (0:ℝ) ≤ x + 2 - 11/5 * τ)]
  rcases le_total a ((5 * x + 5)/11) with hA | hA
  · -- σ-saturated branch at `a`: σ(x, a) = 1, so the deviation value is
    -- `41x/10 − 3 − a/10` — beaten by the floor with gap ≥ 0.46.
    have hσa : eecσ x a = 1 := by
      unfold eecσ
      rw [min_eq_left (by linarith : (1:ℝ) ≤ x + 2 - 11/5 * a),
          max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    rw [hσa, hστ] at hτle
    rcases le_total ((5 * x + 10)/11) 1 with h1 | h1
    · -- τ = (5x+10)/11 (x ≤ 1/5): the floor zeroes the sanction.
      have hτ_val : τ = (5 * x + 10)/11 := by
        rw [hτ_def]; exact min_eq_right h1
      rw [hτ_val] at hτle
      simp only [eecU_T] at hτle
      nlinarith [hτle, ha0, hx1]
    · -- τ = 1 (x ≥ 1/5): the floor buys the interior sanction x − 1/5.
      have hτ_val : τ = 1 := by rw [hτ_def]; exact min_eq_left h1
      rw [hτ_val] at hτle
      simp only [eecU_T] at hτle
      nlinarith [hτle, ha0, hx1, sq_nonneg x]
  · -- Placation branch at `a`: both `a` and `τ` carry the affine σ, and
    -- the objective chord rises at rate `(330 − 6x − 11(τ+a))/50 ≥ 6`.
    have hσa : eecσ x a = x + 2 - 11/5 * a := by
      have haτ : a < (5 * x + 10)/11 := lt_of_lt_of_le hcon hτ_hi
      unfold eecσ
      rw [min_eq_right (by linarith : x + 2 - 11/5 * a ≤ 1),
          max_eq_right (by linarith : (0:ℝ) ≤ x + 2 - 11/5 * a)]
    rw [hσa, hστ] at hτle
    simp only [eecU_T] at hτle
    have hbr : (0:ℝ) < 330 - 6 * x - 11 * (τ + a) := by linarith
    nlinarith [hτle, mul_pos (sub_pos.mpr hcon) hbr]

/-! ## 2. σ-antitonicity and the canonical-myopic ceiling -/

/-- The static Sender response is antitone in the compliance action. -/
theorem eecσ_antitone {x a₁ a₂ : ℝ} (h : a₁ ≤ a₂) :
    eecσ x a₂ ≤ eecσ x a₁ := by
  unfold eecσ
  exact max_le_max (le_refl 0) (min_le_min (le_refl 1) (by linarith))

/-- **The MS myopic ceiling at the canonical comparator.** The canonical
(`Classical.choose`) myopic policy's realized sanction stays at or below
`max x (max xT xS) = x` on the basin: the argmax floor pushes the
canonical compliance to at least `min 1 ((5x+10)/11)`, σ-antitonicity
converts the floor into a sanction ceiling, and the floor's own sanction
is `clip(x − 1/5) ≤ x`. -/
theorem eeCert_hMyoCeiling_MS :
    ∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
      eeCertParams.σ x
          ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (1/10 : ℝ) (1/10)) := by
  intro x hx
  have hx' : x ∈ Set.Icc (1/10 : ℝ) 1 := by rwa [max_self] at hx
  have hxS : x ∈ Sanctions.S := ⟨le_trans (by norm_num) hx'.1, hx'.2⟩
  have hmem :=
    (eeCertParams.myopicFeedbackEquilibrium_canonical).α_mem x hxS
  have hopt :=
    (eeCertParams.myopicFeedbackEquilibrium_canonical).α_opt x hxS
  have hfloor := eeCert_myopic_argmax_floor hx' hmem hopt
  have hanti :
      eecσ x ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
        ≤ eecσ x (min 1 ((5 * x + 10)/11)) := eecσ_antitone hfloor
  have hτx : eecσ x (min 1 ((5 * x + 10)/11)) ≤ x := by
    rcases le_total ((5 * x + 10)/11) 1 with h1 | h1
    · rw [min_eq_right h1,
        show eecσ x ((5 * x + 10)/11) = 0 from by
          unfold eecσ
          rw [show x + 2 - 11/5 * ((5 * x + 10)/11) = 0 by ring,
              min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]]
      linarith [hx'.1]
    · have hx5 : (1/5 : ℝ) ≤ x := by linarith
      rw [min_eq_left h1,
        show eecσ x 1 = x - 1/5 from by
          unfold eecσ
          rw [show x + 2 - 11/5 * 1 = x - 1/5 by ring,
              min_eq_right (by linarith [hx'.2] : x - 1/5 ≤ 1),
              max_eq_right (by linarith : (0:ℝ) ≤ x - 1/5)]]
      linarith
  calc eeCertParams.σ x
          ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
      = eecσ x ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x) :=
        rfl
    _ ≤ eecσ x (min 1 ((5 * x + 10)/11)) := hanti
    _ ≤ x := hτx
    _ ≤ max x (max (1/10 : ℝ) (1/10)) := le_max_left _ _

/-! ## 3. Stage fields on the MS domains -/

/-- Stage Target loss bound on the MS chord domain
`[max(x, 1/10), 1]` (wider than the legacy `[max(x, 1/2), 1]`; the
proof body is identical — the chord memberships are not used). -/
theorem eeCert_h_stage_target_loss_MS
    (V_T : eeCertClass.CarrierT) (V_S : eeCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerLossSlopeOn
        (fun s => eeCertParams.U_T x (eeCertClass.α_on V_T V_S x) s)
        (Set.Icc (max x (max (1/10 : ℝ) (1/10))) 1) (299/100) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [eeCert_α_on_eq_zero V_T V_S, eeCertParams_U_T, eecU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 1/10 * x - 1/100 by linarith [hx.1])]

/-- **The Target combined chord** at the witness, via the existing R45
decomposition converter: stage loss rate `299/100` is offset by the
continuation gain `β_T·g_T·δ = 369/110` along the affine transition. -/
theorem eeCert_h_target_combined :
    eeCertParams.TargetCombinedChordOn eeCertClass (1/10)
      (max (1/10 : ℝ) (1/10)) :=
  eeCertParams.Target_combined_chord_of_decomposition_lowerChord
    ⟨by norm_num, by norm_num⟩
    (dlo := eeCertParams.δ)
    (eeCertParams.affine_transitionChordPack (δ := eeCertParams.δ) rfl).1
    (by norm_num)
    (by simp only [eeCertParams_β_T, eeCertParams_δ]; norm_num)
    eeCert_h_stage_target_loss_MS eeCert_hV_T_gain

/-- **Stage Sender strict monotonicity** on the MS choice interval
`[0, max(x, 1/10)]` — a restriction of the legacy lower-slope lemma
(slope `8/5 > 0` on the larger `[0, max(x, 1/2)]`). -/
theorem eeCert_h_stage_sender_strictMono
    (V_T : eeCertClass.CarrierT) (V_S : eeCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      StrictMonoOn
        (fun s => eeCertParams.U_S x (eeCertClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (max (1/10 : ℝ) (1/10)))) := by
  intro x hx s₁ hs₁ s₂ hs₂ hlt
  have hsub : max x (max (1/10 : ℝ) (1/10)) ≤ max x (1/2 : ℝ) :=
    max_le_max le_rfl (by rw [max_self]; norm_num)
  have h := eeCert_h_stage_sender V_T V_S x hx
    s₁ ⟨hs₁.1, le_trans hs₁.2 hsub⟩
    s₂ ⟨hs₂.1, le_trans hs₂.2 hsub⟩ (le_of_lt hlt)
  have hpos : (0:ℝ) < 8/5 * (s₂ - s₁) :=
    mul_pos (by norm_num) (sub_pos.mpr hlt)
  simp only at h ⊢
  linarith

/-! ## 4. Sender-value monotonicity and same-action dominance -/

/-- **The dominance monotonicity is derived at the certificate witness.**
Membership in `eeCarrierS` (which evaluates to
`valLipGainBall 12 (16/3) (16/3) 0`) implies
that `V_S` is monotone because its minimum state slope is positive.  The
same-`α` Milgrom--Shannon theorem then yields dynamic-over-myopic sanction
dominance pointwise, with no separate monotonicity hypothesis. -/
theorem eeCert_same_alpha_dynamic_dominance_from_gain_carrier
    {V_S : Val} (hV_S : V_S ∈ eeCarrierS) (α : ℝ → ℝ) (x : ℝ) :
    eeCertParams.σ x (α x) ≤ eeCertParams.σ_dyn_top V_S x (α x) :=
  eeCertParams.theorem2_dynamic_dominates_myopic_at_same_alpha_of_mem_valLipGainBall
    (M := 12) (K := 16/3) (g := 16/3) (by norm_num)
    (mem_eeCarrierS_num hV_S) α x

/-! ## 5. THE MS-FORM CERTIFICATE -/

/-- **The first `StandardComplianceLocalCoreCertificate_MS` instance in
the development.** Same economy, carriers, Schur block, pivots, and
interval-dominance discharge as the legacy `eeCertCertificate`; the
MS-specific fields (`h_stage_sender_strictMono`, `h_target_combined`,
`hV_S_mono_carrier`, and the canonical-comparator `hMyoCeiling`) are
discharged above.

**Rule 9 scope — no longer the non-vacuity anchor.** This was for a long time
the *only* inhabitant of `StandardComplianceLocalCoreCertificate_MS` anywhere
in the development, so the two top headline rows
(`standardCompliance_three_goals_local_MS` and
`standardCompliance_three_goals_local_MS_generalF_min_drift_shock`) rested on
a single hand-chosen parameter vector for their non-emptiness. That is no
longer the case: `Sanctions.Examples.symbolic_MS_certified_family_nonvacuous`
inhabits the same bundle over the fourteen-coefficient symbolic family, naming
no point. **Cite the symbolic theorem, not this definition, when arguing that
the MS headlines are non-vacuous.** What this definition still licenses, and
all it licenses, is existence at a concrete calibration — useful as a worked
example and as a cross-check on the symbolic construction, never as evidence
about the class. -/
noncomputable def eeCertCertificateMS :
    eeCertParams.StandardComplianceLocalCoreCertificate_MS where
  D := eeCertClass
  h_inv := eeCertClass_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := eeCertClass_hT_T_op eeCertClass_IsInvariant
  hT_S_op := eeCertClass_hT_S_op eeCertClass_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 1/10
  xS := 1/10
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hpivot_mem := by rw [max_self]; exact ⟨by norm_num, by norm_num⟩
  h_stage_sender_strictMono := eeCert_h_stage_sender_strictMono
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (eeCert_hSC V_T V_S)
  h_target_combined := eeCert_h_target_combined
  hV_S_mono_carrier := fun V_S hV_S =>
    monotone_of_mem_valLipGainBall (by norm_num)
      (mem_eeCarrierS_num hV_S)
  hMyoCeiling := eeCert_hMyoCeiling_MS

/-! ## 6. The headline corollaries -/

/-- **The general-transition three-goals headline, fired at the first MS
witness** (persistence floor on the general-`F` trajectory + dominance
over the canonical myopic comparator; the strict-ascent hypothesis
`hF_top` is automatic at the affine transition). -/
theorem eeCertMS_generalF_three_goals :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT ∧ E.V_S ∈ eeCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1, ∀ n,
          max (1/10 : ℝ) (1/10)
            ≤ eeCertParams.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
          eeCertParams.σ x
              ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
            ≤ eeCertParams.dynamicTopRealizedRule E.V_S E.α x) := by
  obtain ⟨E, hVT, hVS, hG1, hG2, _hG3⟩ :=
    eeCertCertificateMS.three_goals_local_MS_generalF (p := eeCertParams)
      (AbstractGame.affineF_hF_top ⟨by norm_num, by norm_num⟩)
  exact ⟨E, hVT, hVS, fun x₀ hx₀ n => (hG1 x₀ hx₀).2.1 n, hG2⟩

/-- **The MS three-goals, dominance form.** The canonical myopic
realized sanction is dominated by the forward-looking one on the whole
basin.

Goal 2 names no trajectory, so this statement is transition-independent
and is byte-identical to the affine-routed version it replaces; only the
proof changed. It now consumes `three_goals_local_MS_generalF`, whose
Goals 1 and 3 run on `dynamicTopLockInPathF` / `shockPathF` (i.e. through
`p.F`), so nothing under this theorem touches the hard-wired affine
`dynamicTopLockInPath` / `shockPath` (Rule 22, axis 2). The extra
hypothesis `hF_top` — full sanctions strictly raise every state below
one — comes from `affineF_hF_top` at this affine witness. -/
theorem eeCertMS_three_goals_dominance :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT ∧ E.V_S ∈ eeCarrierS
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
          eeCertParams.σ x
              ((eeCertParams.myopicFeedbackEquilibrium_canonical).α x)
            ≤ eeCertParams.dynamicTopRealizedRule E.V_S E.α x) := by
  obtain ⟨E, hVT, hVS, _hG1, hG2, _hG3⟩ :=
    eeCertCertificateMS.three_goals_local_MS_generalF (p := eeCertParams)
      (AbstractGame.affineF_hF_top ⟨by norm_num, by norm_num⟩)
  exact ⟨E, hVT, hVS, hG2⟩

end -- noncomputable section

#print axioms eeCertCertificateMS
#print axioms eeCertMS_generalF_three_goals
#print axioms eeCertMS_three_goals_dominance

end Examples

end Sanctions
