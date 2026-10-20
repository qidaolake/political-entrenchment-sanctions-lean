/-
Sanctions/Examples/ComparativeStaticsWitness.lean

**Rule-16(a) directional sign witnesses for the lock-in comparative
statics (Layer 3, 2026-07-02).**

Each genuine order-form comparative static in
`Theory/LockIn/LockInComparativeStatics.lean` gets a sibling
corollary instantiated at two provably-distinct ordered endpoints, so
the economically-intended direction is exhibited on concrete data —
a flipped sign could not survive these instantiations.

Vehicle: the certificate-complete witness economy `eeCertParams`
(β_S = 1/2) against its **patient sibling** `eeCertParamsPatient`
(identical stage payoff, transition, and discounting speed; only the
Sender's patience raised to β_S = 3/5), evaluated at the canonical
carrier member `affineBCF (16/3)` and the derived-optimal defiant
policy `α ≡ 0` (the witness's Bellman argmax, `eeCert_α_on_eq_zero`).

Witnesses:

1. `eeCert_patience_response_witness` — **patience raises the greatest
   sanction response** (`σ_dyn_top_le_of_beta_le` at β_S: 1/2 < 3/5).
2. `eeCert_patience_band_witness` — **patience deepens lock-in**
   (`dynamicTopLockIn_band_le_of_beta_le` at the same endpoint pair;
   both realized rules are pinned at the corner 1 on the basin, so the
   floors and monotonicity discharge from the strict-monotonicity
   corner lemmas).
3. `eeCert_weight_band_witness` — **the positive-weight comparison is
   weak and may bind with equality** (`dynamicTopLockIn_band_mono_in_weight`
   at `w : 1/4 < 3/4`). At the corner rule used here, both positive
   weights have the same fixed point; this is a boundary check, not
   evidence that adjustment speed moves the steady state.

The transport form (`dynamicTopLockIn_least_fixedPoint_le_of_rule_le`)
is exercised through witness 2, which routes through it. Since round BH-2
(2026-10-06, BH2.4) that chain also exports leastness of both levels; witness 2
keeps its statement and projects those conjuncts away.

Rule 3: no new assumptions — pure specializations of existing
parametric theorems at concrete parameter vectors (Rule 5: the
witnesses are one application each; the only new lemmas are the
`σ_dyn_top ≡ 1` corner mirrors of the existing `eeCert_σ_dyn_eq_one`
and the patient-economy strict-monotonicity mirror).
-/

import Sanctions.Examples.EECertWitness
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.LockIn.LockInComparativeStatics
import Sanctions.Examples.AffineInstance.LockInShocked

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The patient sibling economy (β_S = 3/5) -/

/-- **The patient sibling of `eeCertParams`.** Identical in every
primitive except the Sender's discount factor, raised from `1/2` to
`3/5`. -/
def eeCertParamsPatient : AbstractGame.Params :=
  { eeCertParams with
    β_S := 3/5
    β_S_mem := ⟨by norm_num, by norm_num⟩ }

@[simp] theorem eeCertParamsPatient_U_S :
    eeCertParamsPatient.U_S = eecU_S := rfl
@[simp] theorem eeCertParamsPatient_β_S :
    eeCertParamsPatient.β_S = 3/5 := rfl
@[simp] theorem eeCertParamsPatient_δ :
    eeCertParamsPatient.δ = 1/2 := rfl

/-- Transition closed form for the patient sibling (same transition). -/
theorem eeCertParamsPatient_F (x s : ℝ) :
    eeCertParamsPatient.F x s = (x + s) / 2 :=
  eeCertParams_F x s

/-! ## 2. Corner pinning at `σ_dyn_top` (both economies)

The existing `eeCert_σ_dyn_eq_one` pins `σ_dyn`; the comparative
statics run on the greatest selection `σ_dyn_top`. Under strict
monotonicity of the objective the argmax is unique, so the greatest
selection is also pinned at the corner `1`. The base-economy pinning
`eeCert_σ_dyn_top_eq_one` lives upstream in
`Examples/EECertWitness.lean` (relocated there in the `hMyoBasin`
round, where `eeCert_pathwise_dominance` also consumes it); this file
supplies only the patient-sibling version below. -/

/-- The patient Sender's dynamic objective is also strictly increasing
in the sanction: the continuation chord coefficient rises from `4/3`
to `(3/5)·(16/3)·(1/2) = 8/5`, and the worst-case combined slope
`8/5 + 2 − 11/5 − 1 = 2/5` stays strictly positive. -/
theorem eeCertPatient_senderObj_strictMonoOn {V_S : Val}
    (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => eeCertParamsPatient.U_S x a s
        + eeCertParamsPatient.β_S
            * V_S (Sanctions.clipS' (eeCertParamsPatient.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : (x + s₁)/2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hx.1], by nlinarith [hs₁.2, hx.2]⟩
  have hmem₂ : (x + s₂)/2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hs₂.1, hx.1], by nlinarith [hs₂.2, hx.2]⟩
  have hdiff : V_S (Sanctions.clipS' ((x + s₂)/2))
      - V_S (Sanctions.clipS' ((x + s₁)/2))
      = (16/3) * ((x + s₂)/2 - (x + s₁)/2) :=
    gainBall_clip_diff (by norm_num) (mem_eeCarrierS_num hV_S) hmem₁ hmem₂
  simp only [eeCertParamsPatient_U_S, eecU_S, eeCertParamsPatient_β_S,
    eeCertParamsPatient_F]
  have hcoef : (0 : ℝ) < 8/5 + 2 - 11/5 * a + x - (s₁ + s₂)/2 := by
    nlinarith [ha.2, hx.1, hs₁.2, hs₂.2]
  have hprod := mul_pos (show (0 : ℝ) < s₂ - s₁ by linarith) hcoef
  nlinarith [hdiff, hprod]

/-- `σ_dyn_top ≡ 1` for the patient economy on the carrier. -/
theorem eeCertPatient_σ_dyn_top_eq_one {V_S : Val} (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    eeCertParamsPatient.σ_dyn_top V_S x a = 1 :=
  -- WitnessKit C5: corner pinning of the upper selector from strict
  -- monotonicity of the patient Sender's dynamic objective.
  WitnessKit.σ_dyn_top_eq_one_of_strictMonoOn
    (eeCertPatient_senderObj_strictMonoOn hV_S hx ha)

/-! ## 3. Shared witness data -/

/-- The canonical carrier member is a member of the Sender carrier. -/
theorem eeCert_affineBCF_mem : affineBCF (16/3) ∈ eeCarrierS := by
  rw [eeCarrierS_eq]
  exact affineBCF_mem_gainBall (by norm_num) (by norm_num)

/-- The carrier member satisfies the slope-zero (plain monotonicity)
value hypothesis of the patience comparative statics: its positive
gain slope `16/3` a fortiori dominates slope `0`. -/
theorem eeCert_affineBCF_lowerSlope_zero :
    AbstractGame.Params.LowerSlopeOnValueOn (affineBCF (16/3))
      (Set.Icc (0 : ℝ) 1) 0 := by
  intro y₁ y₂ h₁ h₂ hle
  have hg := (mem_eeCarrierS_num eeCert_affineBCF_mem).2.2 y₁ y₂ h₁ h₂ hle
  have hd : (0 : ℝ) ≤ dist y₁ y₂ := dist_nonneg
  nlinarith

/-- The realized rule of the base economy is pinned at the corner `1`
on the basin `[1/2, 1]` (defiant policy `α ≡ 0`). -/
theorem eeCert_rule_eq_one {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    eeCertParams.dynamicTopRealizedRule (affineBCF (16/3))
      (fun _ => 0) x = 1 :=
  eeCert_σ_dyn_top_eq_one eeCert_affineBCF_mem
    ⟨by linarith [hx.1], hx.2⟩ ⟨le_refl 0, by norm_num⟩

/-- The realized rule of the patient economy is pinned at the corner
`1` on the basin `[1/2, 1]`. -/
theorem eeCertPatient_rule_eq_one {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    eeCertParamsPatient.dynamicTopRealizedRule (affineBCF (16/3))
      (fun _ => 0) x = 1 :=
  eeCertPatient_σ_dyn_top_eq_one eeCert_affineBCF_mem
    ⟨by linarith [hx.1], hx.2⟩ ⟨le_refl 0, by norm_num⟩

/-! ## 4. The three Rule-16(a) endpoint witnesses -/

/-- **Witness 1 — patience raises the greatest sanction response.**
At two provably-distinct patience endpoints (`1/2 < 3/5`, all other
primitives equal), the more patient Sender's greatest forward-looking
sanction response at state `x = 1/2` and compliance `a = 0` is weakly
higher — the economically-intended direction of
`σ_dyn_top_le_of_beta_le`, exhibited on concrete data. -/
theorem eeCert_patience_response_witness :
    eeCertParams.β_S < eeCertParamsPatient.β_S ∧
    eeCertParams.σ_dyn_top (affineBCF (16/3)) (1/2) 0
      ≤ eeCertParamsPatient.σ_dyn_top (affineBCF (16/3)) (1/2) 0 := by
  refine ⟨by norm_num, ?_⟩
  exact σ_dyn_top_le_of_beta_le eeCertParams eeCertParamsPatient
    rfl rfl rfl rfl (by norm_num)
    (affineBCF (16/3)) eeCert_affineBCF_lowerSlope_zero
    ⟨by norm_num, by norm_num⟩ (by norm_num)

/-- **Witness 2 — patience deepens lock-in.** At the same distinct
patience endpoints, the lock-in levels on the basin `[1/2, 1]` are
ordered the intended way (`xs₁ ≤ xs₂`), each a fixed point of its
economy's step map at which the realized sanction equals the state —
the direction of `dynamicTopLockIn_band_le_of_beta_le` (and, through
it, of the transport form
`dynamicTopLockIn_least_fixedPoint_le_of_rule_le`), exhibited on
concrete data. -/
theorem eeCert_patience_band_witness :
    eeCertParams.β_S < eeCertParamsPatient.β_S ∧
    ∃ xs₁ ∈ Set.Icc (1/2 : ℝ) 1, ∃ xs₂ ∈ Set.Icc (1/2 : ℝ) 1,
      eeCertParams.dynamicTopLockInStep (affineBCF (16/3))
        (fun _ => 0) xs₁ = xs₁ ∧
      eeCertParams.dynamicTopRealizedRule (affineBCF (16/3))
        (fun _ => 0) xs₁ = xs₁ ∧
      eeCertParamsPatient.dynamicTopLockInStep (affineBCF (16/3))
        (fun _ => 0) xs₂ = xs₂ ∧
      eeCertParamsPatient.dynamicTopRealizedRule (affineBCF (16/3))
        (fun _ => 0) xs₂ = xs₂ ∧
      xs₁ ≤ xs₂ := by
  refine ⟨by norm_num, ?_⟩
  obtain ⟨xs₁, hxs₁, xs₂, hxs₂, hfix₁, hrule₁, hfix₂, hrule₂, -, -, hle⟩ :=
    dynamicTopLockIn_band_le_of_beta_le eeCertParams eeCertParamsPatient
      rfl rfl rfl rfl (by norm_num)
      (affineBCF (16/3)) (fun _ => 0)
      (xbar := 1/2) (sbar₁ := 1/2) (sbar₂ := 1/2) (lo := 0)
      ⟨by norm_num, by norm_num⟩ (by norm_num)
      eeCert_affineBCF_lowerSlope_zero
      (by
        intro x hx
        rw [eeCert_rule_eq_one hx]
        exact max_le hx.2 (by norm_num))
      (by
        intro x hx
        rw [eeCertPatient_rule_eq_one hx]
        exact max_le hx.2 (by norm_num))
      (by
        intro x hx y hy _
        rw [eeCert_rule_eq_one hx, eeCert_rule_eq_one hy])
      (by
        intro x hx y hy _
        rw [eeCertPatient_rule_eq_one hx, eeCertPatient_rule_eq_one hy])
  exact ⟨xs₁, hxs₁, xs₂, hxs₂, hfix₁, hrule₁, hfix₂, hrule₂, hle⟩

/-- **Witness 3 — the positive-weight weak comparison is non-strict.**
At two provably distinct adjustment-speed endpoints (`1/4 < 3/4`) in
the base economy, the weighted fixed points satisfy the theorem's weak
order. Because the realized rule is the corner rule `σ_real = 1`, both
positive weights select the same fixed point. The witness checks the
weak direction but does not claim that adjustment speed moves the
steady state. -/
theorem eeCert_weight_band_witness :
    (1/4 : ℝ) < 3/4 ∧
    ∃ xs₁ ∈ Set.Icc (1/2 : ℝ) 1, ∃ xs₂ ∈ Set.Icc (1/2 : ℝ) 1,
      (1 - 1/4) * xs₁ + 1/4 * eeCertParams.dynamicTopRealizedRule
        (affineBCF (16/3)) (fun _ => 0) xs₁ = xs₁ ∧
      (1 - 3/4) * xs₂ + 3/4 * eeCertParams.dynamicTopRealizedRule
        (affineBCF (16/3)) (fun _ => 0) xs₂ = xs₂ ∧
      xs₁ ≤ xs₂ := by
  refine ⟨by norm_num, ?_⟩
  apply eeCertParams.dynamicTopLockIn_band_mono_in_weight
    (affineBCF (16/3)) (fun _ => 0)
    (xbar := 1/2) (sbar := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro x hx
    rw [eeCert_rule_eq_one hx]
    exact max_le hx.2 (by norm_num)
  · intro x hx y hy _
    rw [eeCert_rule_eq_one hx, eeCert_rule_eq_one hy]

end

end Examples
end Sanctions
