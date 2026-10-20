/-
Sanctions/Theory/Shocked/ShockedInvariantLipBall.lean

Primitive self-map helpers for norm-Lipschitz value carriers under shocked
Bellman operators.

The Sender result specializes the shock to the concrete moving-average kernel,
whose norm nonexpansiveness and Lipschitz preservation are already proved.
The Target result is kernel-agnostic once a bound on the smeared continuation
and a state-Lipschitz estimate for the realized integrand are supplied.

No new field is added to `Params` or `ShockedParams`.
-/

import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Shocked.ShockedEquilibrium
import Sanctions.Theory.Shocked.ShockedValueLipschitz

namespace Sanctions
namespace AbstractGame

open Set Filter Topology BoundedContinuousFunction

noncomputable section

/-- The Sender norm--Lipschitz carrier derived from a stage-payoff bound,
a realised-policy state modulus, discounting, and transition sensitivity. -/
def senderPrimitiveValLipCarrier
    (q0 : Params) (cube_S L_U_S γ_F : ℝ) : Set SBCF :=
  Params.valLipBall
    (q0.carrierMinNormS cube_S)
    (Sanctions.StokeyLucas.bellmanLipConstant q0.β_S γ_F L_U_S)

/-- The Target norm--Lipschitz carrier derived from a stage-payoff bound,
discounting, and a state modulus for the realised Target integrand. -/
def targetPrimitiveValLipCarrier
    (q0 : Params) (cube_T K_T : ℝ) : Set SBCF :=
  Params.valLipBall (q0.carrierMinNormT cube_T) K_T

/-- **Moving-average shocked Sender `valLipBall` preservation.** The box
smear preserves both the norm radius and the value-Lipschitz modulus. Thus the
deterministic primitive preservation theorem applies to the shocked Sender
Bellman row with the same norm and state-modulus margins. -/
theorem movAvg_bellmanS_shock_mem_valLipBall
    (q0 : Params) {h : ℝ} (hh : 0 < h)
    {α : ℝ → ℝ} (hα : Continuous α)
    (α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (V : SBCF)
    {M K cube_S L_U_S γ_F : ℝ}
    (_hM_nn : 0 ≤ M) (hK_nn : 0 ≤ K)
    (_hcube_S_nn : 0 ≤ cube_S) (_hγ_F_nn : 0 ≤ γ_F)
    (_hβ_S_nn : 0 ≤ q0.β_S)
    (hV : V ∈ Params.valLipBall M K)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s ∈ Sanctions.I, |q0.U_S x a s| ≤ cube_S)
    (h_U_S_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.U_S x₂ (α x₂) s - q0.U_S x₁ (α x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.F x₂ s - q0.F x₁ s| ≤ γ_F * |x₂ - x₁|)
    (h_norm_margin : cube_S + q0.β_S * M ≤ M)
    (h_lip_margin : L_U_S + q0.β_S * K * γ_F ≤ K) :
    (movAvgShockedParams q0 hh).bellmanS_shock α hα V
      ∈ Params.valLipBall M K := by
  have hzero : Sanctions.movAvgBCF hh (0 : SBCF) = 0 := by
    ext z
    simp [Sanctions.movAvgBCF, Sanctions.movAvgReal]
  have hsm_norm : ‖Sanctions.movAvgBCF hh V‖ ≤ M := by
    have hd := Sanctions.movAvgBCF_dist_le hh V (0 : SBCF)
    rw [hzero] at hd
    simpa [dist_eq_norm] using le_trans hd hV.1
  have hsm_lip : Params.ValueLipschitzWith
      (Sanctions.movAvgBCF hh V) K :=
    movAvgShockedParams_smear_valueLipschitz q0 hh hK_nn hV.2
  have hsm_mem : Sanctions.movAvgBCF hh V
      ∈ Params.valLipBall M K :=
    ⟨hsm_norm, hsm_lip⟩
  change q0.bellmanS_BCF α hα (Sanctions.movAvgBCF hh V)
    ∈ Params.valLipBall M K
  exact q0.bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
    hα α_mem (Sanctions.movAvgBCF hh V) hK_nn hsm_mem
    hU_S_cube h_U_S_lip h_F_lip h_norm_margin h_lip_margin

/-- **Primitive-derived moving-average Sender carrier invariance.**

Unlike `movAvg_bellmanS_shock_mem_valLipBall`, this theorem does not take
freely chosen carrier radii.  It computes both radii from the payoff bound,
the realised-policy state modulus, discounting, and transition sensitivity,
and then discharges the two self-map margins by algebra. -/
theorem movAvg_bellmanS_shock_mem_senderPrimitiveValLipCarrier
    (q0 : Params) {h : ℝ} (hh : 0 < h)
    {α : ℝ → ℝ} (hα : Continuous α)
    (α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (V : SBCF) {cube_S L_U_S γ_F : ℝ}
    (hcube_S_nn : 0 ≤ cube_S) (hL_U_S_nn : 0 ≤ L_U_S)
    (hγ_F_nn : 0 ≤ γ_F) (hβ_S_nn : 0 ≤ q0.β_S)
    (hβγ_lt : q0.β_S * γ_F < 1)
    (hV : V ∈ senderPrimitiveValLipCarrier q0 cube_S L_U_S γ_F)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s ∈ Sanctions.I, |q0.U_S x a s| ≤ cube_S)
    (h_U_S_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.U_S x₂ (α x₂) s - q0.U_S x₁ (α x₁) s|
        ≤ L_U_S * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.F x₂ s - q0.F x₁ s| ≤ γ_F * |x₂ - x₁|) :
    (movAvgShockedParams q0 hh).bellmanS_shock α hα V
      ∈ senderPrimitiveValLipCarrier q0 cube_S L_U_S γ_F := by
  apply movAvg_bellmanS_shock_mem_valLipBall q0 hh hα α_mem V
  · exact q0.carrierMinNormS_nonneg hcube_S_nn
  · exact
      (Sanctions.StokeyLucas.bellman_closed_form_lipschitz_margin
        hL_U_S_nn hβ_S_nn hγ_F_nn hβγ_lt).1
  · exact hcube_S_nn
  · exact hγ_F_nn
  · exact hβ_S_nn
  · exact hV
  · exact hU_S_cube
  · exact h_U_S_lip
  · exact h_F_lip
  · exact q0.carrierMinNormS_margin cube_S
  · exact
      (Sanctions.StokeyLucas.bellman_closed_form_lipschitz_margin
        hL_U_S_nn hβ_S_nn hγ_F_nn hβγ_lt).2.le

namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Shocked Target `valLipBall` preservation from an integrand modulus.**
The Target Bellman row stays in the norm-Lipschitz carrier when the smeared
continuation respects the norm radius, the stage payoff has the stated cube
bound, and the realized Target integrand has the carrier's state modulus. -/
theorem targetDynBCF_shock_mem_valLipBall_of_integrand
    (ρ : ℝ → ℝ → ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (hρmem : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ρ x a ∈ Sanctions.I)
    (V : SBCF) {M K cube : ℝ}
    (_hM : 0 ≤ M) (_hcube : 0 ≤ cube)
    (hsmear_norm : ‖sp.smear V‖ ≤ M)
    (hU : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s ∈ Sanctions.I, |sp.toParams.U_T x a s| ≤ cube)
    (hnorm : cube + sp.toParams.β_T * M ≤ M)
    (hint : ∀ x y : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      |sp.toParams.targetDynIntegrand ρ (sp.smear V) y.val a
        - sp.toParams.targetDynIntegrand ρ (sp.smear V) x.val a|
        ≤ K * dist x y) :
    sp.targetDynBCF_shock ρ hρc V
      ∈ Params.valLipBall M K := by
  change sp.toParams.targetDynBCF ρ hρc (sp.smear V)
    ∈ Params.valLipBall M K
  refine ⟨?_, ?_⟩
  · exact (sp.toParams.targetDynBCF_norm_le_of_cube
      ρ hρc hρmem (sp.smear V) hsmear_norm hU).trans hnorm
  · exact sp.toParams.targetDynBCF_valueLipschitz_of_integrand
      ρ hρc (sp.smear V) hint

end ShockedParams

/-- **Primitive-derived moving-average Target carrier invariance.**

The norm radius is the discounted stage-payoff bound.  The second radius is
the state modulus already derived for the realised Target integrand; it is not
an independently calibrated carrier number. -/
theorem movAvg_targetDynBCF_shock_mem_targetPrimitiveValLipCarrier_of_integrand
    (q0 : Params) {h : ℝ} (hh : 0 < h)
    (ρ : ℝ → ℝ → ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (hρmem : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ρ x a ∈ Sanctions.I)
    (V : SBCF) {cube_T K_T : ℝ}
    (hcube_T_nn : 0 ≤ cube_T)
    (hV : V ∈ targetPrimitiveValLipCarrier q0 cube_T K_T)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s ∈ Sanctions.I, |q0.U_T x a s| ≤ cube_T)
    (hint : ∀ x y : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      |q0.targetDynIntegrand ρ
          ((movAvgShockedParams q0 hh).smear V) y.val a
        - q0.targetDynIntegrand ρ
          ((movAvgShockedParams q0 hh).smear V) x.val a|
        ≤ K_T * dist x y) :
    (movAvgShockedParams q0 hh).targetDynBCF_shock ρ hρc V
      ∈ targetPrimitiveValLipCarrier q0 cube_T K_T := by
  have hzero : Sanctions.movAvgBCF hh (0 : SBCF) = 0 := by
    ext z
    simp [Sanctions.movAvgBCF, Sanctions.movAvgReal]
  have hsmear_norm :
      ‖(movAvgShockedParams q0 hh).smear V‖
        ≤ q0.carrierMinNormT cube_T := by
    have hd := Sanctions.movAvgBCF_dist_le hh V (0 : SBCF)
    rw [hzero] at hd
    simpa [movAvgShockedParams_smear, dist_eq_norm] using le_trans hd hV.1
  apply
    (movAvgShockedParams q0 hh).targetDynBCF_shock_mem_valLipBall_of_integrand
      ρ hρc hρmem V
  · exact q0.carrierMinNormT_nonneg hcube_T_nn
  · exact hcube_T_nn
  · exact hsmear_norm
  · exact hU_T_cube
  · exact q0.carrierMinNormT_margin cube_T
  · exact hint

end
end AbstractGame
end Sanctions
