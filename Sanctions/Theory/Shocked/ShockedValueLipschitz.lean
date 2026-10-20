/-
Sanctions/Theory/Shocked/ShockedValueLipschitz.lean

**Step 2: the shocked Sender Bellman fixed point `V_S_shock` is itself
`K`-Lipschitz — closing the single-crossing gate AT the constructed equilibrium,
not merely for an arbitrary Lipschitz continuation.**

The shocked operator is `bellmanS_shock = bellmanS_BCF ∘ smear` (ShockedBellman.lean).
For the concrete box kernel `movAvgShockedParams q0 hh` the smear is `movAvgBCF hh`,
which **preserves** the value Lipschitz constant `K` (`movAvgShockedParams_smear_valueLipschitz`).
So the EXISTING deterministic one-step cone preservation
`bellmanS_BCF_preserves_lipschitz_cone` (ValueLipschitz.lean) applies at the smeared
continuation, and the whole iterate-closure argument that makes the deterministic
`V_S` Lipschitz (`V_S_valueLipschitzWith_of_primitive_margin`) carries over verbatim.

The Lipschitz modulus is the SAME closed form `K = L_U_S/(1 − β_S·γ_F)` as the
deterministic value, under the SAME margin `L_U + β_S·K·γ ≤ K` — the smear does not
inflate it (disprove-first probe `docs/archive/workflow-scratch/probe_open_steps.lean`: smear Lipschitz
ratio ≤ 0.98 < 1). Hence `V_S_shock ∈ valLipBall M K`, and the shocked single-crossing
gate (Step 1) holds at the actual shocked equilibrium value `V_S_shock` (Rule-15: the
fixed point is *constructed* by the Banach engine and *proved* Lipschitz, not assumed).

**Rule 3 / Rule 19.** No new field on `ShockedParams`: the cone preservation is proved
at the concrete box kernel from the Foundations smear-Lipschitz lemma, reusing the
deterministic composer. Stated at `movAvgShockedParams` to match the Steps 1/7
witness-gate form.
-/

import Sanctions.Theory.Shocked.ShockedBellman
import Sanctions.Theory.Shocked.ShockedSingleCrossing
import Sanctions.Theory.Bellman.ValueLipschitz

namespace Sanctions
namespace AbstractGame

open BoundedContinuousFunction Filter Topology

/-- **One-step shocked-Bellman Lipschitz-cone preservation.** If the continuation `V`
is `K`-Lipschitz, so is `(movAvgShockedParams q0 hh).bellmanS_shock α hα V`, under the
same primitive Sender stage/transition Lipschitz data and margin `L_U + β_S·K·γ ≤ K`
as the deterministic case. Proof: `bellmanS_shock = bellmanS_BCF (smear V)`, the smear
preserves `K`, then the deterministic `bellmanS_BCF_preserves_lipschitz_cone`. -/
theorem bellmanS_shock_preserves_lipschitz_cone
    (q0 : Params) {h : ℝ} (hh : 0 < h)
    {α : ℝ → ℝ} (hα : Continuous α) (V : SBCF)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K) (_hγ_nn : 0 ≤ γ)
    (h_V_lip : Params.ValueLipschitzWith V K)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.U_S x₂ (α x₂) s - q0.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.F x₂ s - q0.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + q0.β_S * K * γ ≤ K) :
    Params.ValueLipschitzWith ((movAvgShockedParams q0 hh).bellmanS_shock α hα V) K := by
  have h_smear_lip : Params.ValueLipschitzWith ((movAvgShockedParams q0 hh).smear V) K :=
    movAvgShockedParams_smear_valueLipschitz q0 hh hK_nn h_V_lip
  change Params.ValueLipschitzWith
      ((movAvgShockedParams q0 hh).toParams.bellmanS_BCF α hα
        ((movAvgShockedParams q0 hh).smear V)) K
  rw [movAvgShockedParams_toParams]
  exact q0.bellmanS_BCF_preserves_lipschitz_cone hα _ hK_nn h_smear_lip
    h_U_lip h_F_lip h_margin

/-- **The shocked Sender fixed point is `K`-Lipschitz.** Mirror of
`V_S_valueLipschitzWith_of_primitive_margin` for the shocked operator: every iterate
`(bellmanS_shock)^[n] 0` is `K`-Lipschitz (base + one-step preservation above), the
shocked operator is a Banach contraction, so the limit `V_S_shock` inherits the
constant. -/
theorem V_S_shock_valueLipschitzWith_of_primitive_margin
    (q0 : Params) {h : ℝ} (hh : 0 < h)
    {α : ℝ → ℝ} (hα : Continuous α)
    {K L_U γ : ℝ}
    (hK_nn : 0 ≤ K) (hγ_nn : 0 ≤ γ)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.U_S x₂ (α x₂) s - q0.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.F x₂ s - q0.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_margin : L_U + q0.β_S * K * γ ≤ K) :
    Params.ValueLipschitzWith ((movAvgShockedParams q0 hh).V_S_shock α hα) K := by
  set sp := movAvgShockedParams q0 hh with hsp
  have h_each : ∀ n, Params.ValueLipschitzWith
      ((sp.bellmanS_shock α hα)^[n] (0 : SBCF)) K := by
    intro n
    induction n with
    | zero => simpa using Params.valueLipschitzWith_zero hK_nn
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact bellmanS_shock_preserves_lipschitz_cone q0 hh hα _ hK_nn hγ_nn ih
          h_U_lip h_F_lip h_margin
  have h_contract := sp.bellmanS_shock_contracting hα
  have h_tendsto :=
    ContractingWith.tendsto_iterate_fixedPoint h_contract (0 : SBCF)
  have h_fix : Function.IsFixedPt (sp.bellmanS_shock α hα) (sp.V_S_shock α hα) :=
    sp.V_S_shock_isFixedPoint hα
  have h_unique := ContractingWith.fixedPoint_unique h_contract h_fix
  have h_tendsto' :
      Tendsto (fun n => (sp.bellmanS_shock α hα)^[n] (0 : SBCF))
        atTop (𝓝 (sp.V_S_shock α hα)) := by
    rw [h_unique]; exact h_tendsto
  exact Params.valueLipschitzWith_of_tendsto hK_nn h_each h_tendsto'

/-- **Closed-form modulus.** The shocked Sender fixed point is
`(L_U/(1 − β_S·γ))`-Lipschitz whenever `β_S·γ < 1` — the same closed form as the
deterministic `V_S`. -/
theorem V_S_shock_valueLipschitzWith_of_contraction
    (q0 : Params) {h : ℝ} (hh : 0 < h)
    {α : ℝ → ℝ} (hα : Continuous α)
    {L_U γ : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hγ_nn : 0 ≤ γ)
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.U_S x₂ (α x₂) s - q0.U_S x₁ (α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |q0.F x₂ s - q0.F x₁ s| ≤ γ * |x₂ - x₁|)
    (h_contract : q0.β_S * γ < 1) :
    Params.ValueLipschitzWith ((movAvgShockedParams q0 hh).V_S_shock α hα)
      (L_U / (1 - q0.β_S * γ)) := by
  set K : ℝ := L_U / (1 - q0.β_S * γ) with hK_def
  have h_denom_pos : 0 < 1 - q0.β_S * γ := by linarith
  have hK_nn : 0 ≤ K := by rw [hK_def]; exact div_nonneg hL_U_nn (le_of_lt h_denom_pos)
  have h_K_id : K * (1 - q0.β_S * γ) = L_U := by rw [hK_def]; field_simp
  have h_margin : L_U + q0.β_S * K * γ ≤ K := by
    have h_eq : L_U + q0.β_S * K * γ = K := by
      have h₁ : q0.β_S * K * γ = K - K * (1 - q0.β_S * γ) := by ring
      rw [h₁, h_K_id]; ring
    linarith
  exact V_S_shock_valueLipschitzWith_of_primitive_margin q0 hh hα hK_nn hγ_nn
    h_U_lip h_F_lip h_margin

end AbstractGame
end Sanctions
