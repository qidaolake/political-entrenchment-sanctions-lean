/-
Sanctions/Theory/Shocked/ShockedRowLipschitz.lean

Carrier-local quantitative row bounds for the shocked coupled operator.
The Sender selector theorem requires strong concavity only at the two
continuation values being compared.  The Target row theorem restricts payoff
regularity to the physical state-action box used by the Bellman operator.
Both results are parametric domain wiring and introduce no structure field or
economic assumption.
-/

import Sanctions.Theory.Shocked.ShockedLeaderLipschitz

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **σ-Lipschitz in `V_S`, pair form.**  Identical content and proof to
`sigma_top_lipschitz_in_V`, but consuming the smeared-objective strong
concavity only at the TWO values `V, W` actually compared (instead of at every
`V : SBCF`), so that a carrier-restricted concavity hypothesis suffices — the
all-`V` quantification of the original is not satisfiable at a fixed modulus
for arbitrarily large values, so the pair form is the honest per-witness
citable shape. -/
theorem sigma_top_lipschitz_in_V_pair
    (sm : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
    {Lκ : ℝ} (hLκ : 0 ≤ Lκ)
    (sm_sub : ∀ U W, sm (U - W) = sm U - sm W)
    (sm_lip : ∀ (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (z z' : ↥(Sanctions.S : Set ℝ)),
      |sm U z - sm U z'| ≤ Lκ * ‖U‖ * dist z z')
    {c : ℝ} (hc : 0 < c) (x a : ℝ)
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (scV : StrongConcaveOn Sanctions.I c
      (fun s => p.U_S x a s + p.β_S * (sm V) (Sanctions.clipS' (p.F x s))))
    (scW : StrongConcaveOn Sanctions.I c
      (fun s => p.U_S x a s + p.β_S * (sm W) (Sanctions.clipS' (p.F x s))))
    {LF : ℝ} (hLF : 0 ≤ LF)
    (clipF_lip : ∀ s s', |(Sanctions.clipS' (p.F x s)).val
      - (Sanctions.clipS' (p.F x s')).val| ≤ LF * |s - s'|) :
    |p.σ_dyn_top (sm V) x a - p.σ_dyn_top (sm W) x a|
      ≤ (2 * p.β_S * Lκ * LF / c) * dist V W := by
  set f : ℝ → ℝ := fun s => p.U_S x a s + p.β_S * (sm V) (Sanctions.clipS' (p.F x s)) with hf
  set g : ℝ → ℝ := fun s => p.U_S x a s + p.β_S * (sm W) (Sanctions.clipS' (p.F x s)) with hg
  set σV := p.σ_dyn_top (sm V) x a with hσV
  set σW := p.σ_dyn_top (sm W) x a with hσW
  have hσV_mem : σV ∈ Sanctions.I := p.σ_dyn_top_mem_I (sm V) x a
  have hσW_mem : σW ∈ Sanctions.I := p.σ_dyn_top_mem_I (sm W) x a
  have hfmax : ∀ y ∈ Sanctions.I, f y ≤ f σV :=
    fun y hy => p.σ_dyn_top_isMaxOn (sm V) x a hy
  have hgmax : ∀ y ∈ Sanctions.I, g y ≤ g σW :=
    fun y hy => p.σ_dyn_top_isMaxOn (sm W) x a hy
  set L : ℝ := p.β_S * Lκ * dist V W * LF with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ p.β_S := p.β_S_mem.1
    positivity
  have hdiff : |(f σV - g σV) - (f σW - g σW)| ≤ L * |σV - σW| := by
    have hpt : ∀ s, f s - g s = p.β_S * (sm (V - W)) (Sanctions.clipS' (p.F x s)) := by
      intro s
      have : sm V (Sanctions.clipS' (p.F x s)) - sm W (Sanctions.clipS' (p.F x s))
          = (sm (V - W)) (Sanctions.clipS' (p.F x s)) := by
        rw [sm_sub]; rfl
      simp only [hf, hg]; rw [← this]; ring
    rw [hpt σV, hpt σW, ← mul_sub, abs_mul, abs_of_nonneg p.β_S_mem.1]
    have hsm := sm_lip (V - W) (Sanctions.clipS' (p.F x σV)) (Sanctions.clipS' (p.F x σW))
    calc p.β_S * |sm (V - W) (Sanctions.clipS' (p.F x σV))
                  - sm (V - W) (Sanctions.clipS' (p.F x σW))|
        ≤ p.β_S * (Lκ * ‖V - W‖ * dist (Sanctions.clipS' (p.F x σV))
            (Sanctions.clipS' (p.F x σW))) :=
          mul_le_mul_of_nonneg_left hsm p.β_S_mem.1
      _ ≤ p.β_S * (Lκ * ‖V - W‖ * (LF * |σV - σW|)) := by
          apply mul_le_mul_of_nonneg_left _ p.β_S_mem.1
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Subtype.dist_eq, Real.dist_eq]; exact clipF_lip σV σW
      _ = L * |σV - σW| := by rw [hL, dist_eq_norm]; ring
  have hcore := Sanctions.argmax_lipschitz_of_strongConcave_lipschitzDiff
    hL0 (convex_Icc 0 1) scV scW hσV_mem hσW_mem hfmax hgmax hdiff
  rw [hL] at hcore
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [hcore]

end Params

namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Box-restricted shocked Target ROW inequality.**  Identical conclusion and
proof to `targetDynBCF_shock_row_lipschitz`, with the two payoff-side
hypotheses restricted to the state–action box actually used by the Bellman
operator: `hUT_lip` (stage sanction-Lipschitz of `U_T`) is required only for
`x ∈ S`, `a ∈ I`, `s, s' ∈ I` — the P3 payoff family satisfies `L_UT = 1` on
the box but NOT on all of ℝ² (its sanction slope `x + a/2 − 1/2` is unbounded
in `x`), so the box form is what a concrete economy can discharge — and
`hσ_lip` (selector Lipschitz in `V_S`) only for `x ∈ S`, `a ∈ I`.  Rule 13:
strictly weaker hypotheses, same conclusion; no assumption widening. -/
theorem targetDynBCF_shock_row_lipschitz_box
    {Lσ L_UT L_smVT LF : ℝ} (hLσ : 0 ≤ Lσ) (hL_UT : 0 ≤ L_UT)
    (hL_smVT : 0 ≤ L_smVT) (hLF : 0 ≤ LF)
    (V_T V_T' V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (ρV ρW : ℝ → ℝ → ℝ)
    (hσcV : Continuous (fun xa : ℝ × ℝ => ρV xa.1 xa.2))
    (hσcW : Continuous (fun xa : ℝ × ℝ => ρW xa.1 xa.2))
    (hρV_mem : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ρV x a ∈ Sanctions.I)
    (hρW_mem : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ρW x a ∈ Sanctions.I)
    (hσ_lip : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      |ρV x a - ρW x a| ≤ Lσ * dist V_S W_S)
    (hUT_lip : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      ∀ s' ∈ Sanctions.I,
      |sp.toParams.U_T x a s - sp.toParams.U_T x a s'| ≤ L_UT * |s - s'|)
    (hsmVT_lip : ∀ z z', |sp.smear V_T' z - sp.smear V_T' z'|
      ≤ L_smVT * dist z z')
    (hclipF_lip : ∀ x s s', |(Sanctions.clipS' (sp.toParams.F x s)).val
      - (Sanctions.clipS' (sp.toParams.F x s')).val| ≤ LF * |s - s'|) :
    dist (sp.targetDynBCF_shock ρV hσcV V_T)
      (sp.targetDynBCF_shock ρW hσcW V_T')
      ≤ sp.toParams.β_T * dist V_T V_T'
        + ((L_UT + sp.toParams.β_T * L_smVT * LF) * Lσ) * dist V_S W_S := by
  have hβT0 : (0 : ℝ) ≤ sp.toParams.β_T := sp.toParams.β_T_mem.1
  set Mc : ℝ := (L_UT + sp.toParams.β_T * L_smVT * LF) * Lσ * dist V_S W_S
    with hMc
  have hMc0 : 0 ≤ Mc := by
    have := dist_nonneg (x := V_S) (y := W_S); positivity
  -- Selector channel at the fixed own-continuation `V_T'`.
  have hsecond : dist (sp.targetDynBCF_shock ρV hσcV V_T')
      (sp.targetDynBCF_shock ρW hσcW V_T') ≤ Mc := by
    rw [BoundedContinuousFunction.dist_le hMc0]
    intro x
    refine sp.toParams.targetDynBCF_selector_pointwise_dist ρV ρW hσcV hσcW
      (sp.smear V_T') x Mc ?_
    intro a ha
    have hint : sp.toParams.targetDynIntegrand ρV (sp.smear V_T') x.val a
              - sp.toParams.targetDynIntegrand ρW (sp.smear V_T') x.val a
        = (sp.toParams.U_T x.val a (ρV x.val a)
            - sp.toParams.U_T x.val a (ρW x.val a))
          + sp.toParams.β_T
              * (sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
              - sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a)))) := by
      simp only [Sanctions.AbstractGame.Params.targetDynIntegrand]; ring
    rw [hint]
    have hd : |ρV x.val a - ρW x.val a| ≤ Lσ * dist V_S W_S :=
      hσ_lip x.val x.property a ha
    calc |(sp.toParams.U_T x.val a (ρV x.val a)
            - sp.toParams.U_T x.val a (ρW x.val a))
          + sp.toParams.β_T
              * (sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
              - sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a))))|
        ≤ |sp.toParams.U_T x.val a (ρV x.val a)
            - sp.toParams.U_T x.val a (ρW x.val a)|
          + |sp.toParams.β_T
              * (sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
              - sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a))))| := by
            simp only [← Real.norm_eq_abs]; exact norm_add_le _ _
      _ ≤ L_UT * |ρV x.val a - ρW x.val a|
          + sp.toParams.β_T * (L_smVT * (LF * |ρV x.val a - ρW x.val a|)) := by
            apply add_le_add (hUT_lip x.val x.property a ha
              (ρV x.val a) (hρV_mem x.val x.property a ha)
              (ρW x.val a) (hρW_mem x.val x.property a ha))
            rw [abs_mul, abs_of_nonneg hβT0]
            apply mul_le_mul_of_nonneg_left _ hβT0
            calc |sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
                  - sp.smear V_T' (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a)))|
                ≤ L_smVT * dist (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
                    (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a))) :=
                  hsmVT_lip _ _
              _ ≤ L_smVT * (LF * |ρV x.val a - ρW x.val a|) := by
                  apply mul_le_mul_of_nonneg_left _ hL_smVT
                  rw [Subtype.dist_eq, Real.dist_eq]; exact hclipF_lip x.val _ _
      _ = (L_UT + sp.toParams.β_T * L_smVT * LF) * |ρV x.val a - ρW x.val a| := by
            ring
      _ ≤ (L_UT + sp.toParams.β_T * L_smVT * LF) * (Lσ * dist V_S W_S) := by
            apply mul_le_mul_of_nonneg_left hd; positivity
      _ = Mc := by rw [hMc]; ring
  -- Triangle through the mixed term, own-axis contraction on the first leg.
  calc dist (sp.targetDynBCF_shock ρV hσcV V_T)
        (sp.targetDynBCF_shock ρW hσcW V_T')
      ≤ dist (sp.targetDynBCF_shock ρV hσcV V_T)
          (sp.targetDynBCF_shock ρV hσcV V_T')
        + dist (sp.targetDynBCF_shock ρV hσcV V_T')
          (sp.targetDynBCF_shock ρW hσcW V_T') := dist_triangle _ _ _
    _ ≤ sp.toParams.β_T * dist V_T V_T' + Mc :=
        add_le_add (sp.targetDynBCF_shock_dist_le ρV hσcV V_T V_T') hsecond
    _ = sp.toParams.β_T * dist V_T V_T'
        + ((L_UT + sp.toParams.β_T * L_smVT * LF) * Lσ) * dist V_S W_S := by
        rw [hMc]

end ShockedParams

end AbstractGame

end

end Sanctions
