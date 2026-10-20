/-
Sanctions/Theory/Shocked/ShockedLeaderLipschitz.lean

**The σ/α* wiring: from `smear_lipschitz` to a Lipschitz leader policy.**

This assembles the two machine-checked prerequisites — the argmax-Lipschitz core
(`argmax_lipschitz_of_strongConcave_lipschitzDiff`) and the smear regularity
(`movAvg_lipschitz`/`movAvgBCF_*`) — into the Lipschitz-in-`V_S` bounds the
interior shocked-existence theorem consumes.

First lemma here: **the shocked Sender selector `σ_dyn_top(smear V_S)` is
Lipschitz in `V_S`** (it upgrades the deterministic Hölder-½ to Lipschitz). The
argument is the argmax-core applied to the *smeared* Sender objective: its
maximiser is `σ_dyn_top(smear V_S)` (by `σ_dyn_top_isMaxOn` at the value
`smear V_S`), the objective is strongly concave in `s` (consumed, as in the
deterministic `StrongConcaveHolder`), and the objective *difference* is
action-Lipschitz with constant `∝ ‖V_S - W_S‖` because the smear is linear
(`smear_sub`) and state-Lipschitz (`smear_lip`).
-/

import Sanctions.Foundations.StrongConcaveArgmax
import Sanctions.Theory.Bellman.StrongConcaveHolder
import Sanctions.Theory.Shocked.ShockedInteriorExistence
import Sanctions.Foundations.MovingAverage

namespace Sanctions
namespace AbstractGame
namespace Params

open scoped NNReal
open BoundedContinuousFunction

variable (p : Sanctions.AbstractGame.Params)

/-- **σ-Lipschitz: the shocked Sender selector is Lipschitz in `V_S`.**

Given a smoothing operator `sm` that is linear (`sm_sub`) and state-Lipschitz
(`sm_lip`, constant `Lκ·‖·‖`), strong concavity of the smeared Sender objective
in `s` (`sc`), and an action-Lipschitz bound `clipF_lip` on `s ↦ clipS'(F x s)`,
the map `V_S ↦ σ_dyn_top(sm V_S)(x,a)` is Lipschitz with constant
`2·β_S·Lκ·LF/c`. -/
theorem sigma_top_lipschitz_in_V
    (sm : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
    {Lκ : ℝ} (hLκ : 0 ≤ Lκ)
    (sm_sub : ∀ U W, sm (U - W) = sm U - sm W)
    (sm_lip : ∀ (U : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (z z' : ↥(Sanctions.S : Set ℝ)),
      |sm U z - sm U z'| ≤ Lκ * ‖U‖ * dist z z')
    {c : ℝ} (hc : 0 < c) (x a : ℝ)
    (sc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, StrongConcaveOn Sanctions.I c
      (fun s => p.U_S x a s + p.β_S * (sm V) (Sanctions.clipS' (p.F x s))))
    {LF : ℝ} (hLF : 0 ≤ LF)
    (clipF_lip : ∀ s s', |(Sanctions.clipS' (p.F x s)).val
      - (Sanctions.clipS' (p.F x s')).val| ≤ LF * |s - s'|)
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
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
  -- objective-difference action-Lipschitz bound, with L = β_S·Lκ·‖V-W‖·LF
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
  -- argmax-core
  have hcore := Sanctions.argmax_lipschitz_of_strongConcave_lipschitzDiff
    hL0 (convex_Icc 0 1) (sc V) (sc W) hσV_mem hσW_mem hfmax hgmax hdiff
  -- c·|σV - σW| ≤ 2L = 2·β_S·Lκ·‖V-W‖·LF ⇒ divide by c
  rw [hL] at hcore
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [hcore]

/-- **Selector-channel bound for the Target Bellman operator.** If the Target
integrand difference under two selectors is uniformly bounded by `M` over the
action set, the Target Bellman values differ by at most `M`. -/
theorem targetDynBCF_selector_pointwise_dist
    (ρ ρ' : ℝ → ℝ → ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (hρ'c : Continuous (fun xa : ℝ × ℝ => ρ' xa.1 xa.2))
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) (M : ℝ)
    (hM : ∀ a ∈ Sanctions.I,
      |p.targetDynIntegrand ρ V_T x.val a - p.targetDynIntegrand ρ' V_T x.val a| ≤ M) :
    |p.targetDynBCF ρ hρc V_T x - p.targetDynBCF ρ' hρ'c V_T x| ≤ M := by
  have heq_V : p.targetDynBCF ρ hρc V_T x =
      sSup ((fun a => p.targetDynIntegrand ρ V_T x.val a) '' Sanctions.I) := rfl
  have heq_W : p.targetDynBCF ρ' hρ'c V_T x =
      sSup ((fun a => p.targetDynIntegrand ρ' V_T x.val a) '' Sanctions.I) := rfl
  rw [heq_V, heq_W]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩ (M := M)
    (Bf := sSup ((fun a => p.targetDynIntegrand ρ V_T x.val a) '' Sanctions.I))
    (Bg := sSup ((fun a => p.targetDynIntegrand ρ' V_T x.val a) '' Sanctions.I))
  · intro a ha; exact hM a ha
  · intro a ha; exact le_csSup (p.targetDynIntegrand_image_bddAbove ρ V_T hρc x.val) ⟨a, ha, rfl⟩
  · intro a ha; exact le_csSup (p.targetDynIntegrand_image_bddAbove ρ' V_T hρ'c x.val) ⟨a, ha, rfl⟩

end Params

namespace ShockedParams

open scoped NNReal
open BoundedContinuousFunction

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- The shocked Target operator is a `β_T`-contraction at the `dist` level. -/
theorem targetDynBCF_shock_dist_le
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    dist (sp.targetDynBCF_shock ρ hρc V) (sp.targetDynBCF_shock ρ hρc W)
      ≤ sp.toParams.β_T * dist V W := by
  rw [BoundedContinuousFunction.dist_le (mul_nonneg sp.toParams.β_T_mem.1 dist_nonneg)]
  intro x
  exact sp.targetDynBCF_shock_pointwise_dist ρ hρc V W x

/-- **`V_T_dyn_shock` is Lipschitz in `V_S`.** Fixed-point-Lipschitz-in-selector:
the shocked slaved Target value moves by at most `(L_UT + β_T·L_smVT·LF)·Lσ/(1−β_T)`
times `dist V_S W_S`, where `Lσ` is the σ-Lipschitz constant, `L_UT` the `U_T`
action-Lipschitz constant, `L_smVT` the (uniform) state-Lipschitz constant of the
smeared Target value, and `LF` the `clip∘F` action-Lipschitz constant. -/
theorem VTdyn_shock_lipschitz
    {Lσ L_UT L_smVT LF : ℝ} (hLσ : 0 ≤ Lσ) (hL_UT : 0 ≤ L_UT)
    (hL_smVT : 0 ≤ L_smVT) (hLF : 0 ≤ LF)
    (V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσcV : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S) xa.1 xa.2))
    (hσcW : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear W_S) xa.1 xa.2))
    (hσ_lip : ∀ x a, |sp.toParams.σ_dyn_top (sp.smear V_S) x a
      - sp.toParams.σ_dyn_top (sp.smear W_S) x a| ≤ Lσ * dist V_S W_S)
    (hUT_lip : ∀ x a s s', |sp.toParams.U_T x a s - sp.toParams.U_T x a s'|
      ≤ L_UT * |s - s'|)
    (hsmVT_lip : ∀ z z', |sp.smear (sp.V_T_dyn_shock W_S hσcW) z
      - sp.smear (sp.V_T_dyn_shock W_S hσcW) z'| ≤ L_smVT * dist z z')
    (hclipF_lip : ∀ x s s', |(Sanctions.clipS' (sp.toParams.F x s)).val
      - (Sanctions.clipS' (sp.toParams.F x s')).val| ≤ LF * |s - s'|) :
    dist (sp.V_T_dyn_shock V_S hσcV) (sp.V_T_dyn_shock W_S hσcW)
      ≤ ((L_UT + sp.toParams.β_T * L_smVT * LF) * Lσ / (1 - sp.toParams.β_T)) * dist V_S W_S := by
  set ρV := sp.toParams.σ_dyn_top (sp.smear V_S) with hρV
  set ρW := sp.toParams.σ_dyn_top (sp.smear W_S) with hρW
  set VT := sp.V_T_dyn_shock V_S hσcV with hVT
  set WT := sp.V_T_dyn_shock W_S hσcW with hWT
  have hβT1 : sp.toParams.β_T < 1 := sp.toParams.β_T_mem.2
  have hβT0 : (0 : ℝ) ≤ sp.toParams.β_T := sp.toParams.β_T_mem.1
  have hVTfix : sp.targetDynBCF_shock ρV hσcV VT = VT :=
    sp.targetDynValue_shock_isFixedPoint ρV hσcV
  have hWTfix : sp.targetDynBCF_shock ρW hσcW WT = WT :=
    sp.targetDynValue_shock_isFixedPoint ρW hσcW
  set Mc : ℝ := (L_UT + sp.toParams.β_T * L_smVT * LF) * Lσ * dist V_S W_S with hMc
  have hMc0 : 0 ≤ Mc := by have := dist_nonneg (x := V_S) (y := W_S); positivity
  -- second term: selector diff at WT, bounded by Mc
  have hsecond : dist (sp.targetDynBCF_shock ρV hσcV WT) (sp.targetDynBCF_shock ρW hσcW WT) ≤ Mc := by
    rw [BoundedContinuousFunction.dist_le hMc0]
    intro x
    refine sp.toParams.targetDynBCF_selector_pointwise_dist ρV ρW hσcV hσcW (sp.smear WT) x Mc ?_
    intro a ha
    -- integrand difference bound
    have hint : sp.toParams.targetDynIntegrand ρV (sp.smear WT) x.val a
              - sp.toParams.targetDynIntegrand ρW (sp.smear WT) x.val a
        = (sp.toParams.U_T x.val a (ρV x.val a) - sp.toParams.U_T x.val a (ρW x.val a))
          + sp.toParams.β_T * (sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
              - sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a)))) := by
      simp only [Sanctions.AbstractGame.Params.targetDynIntegrand]; ring
    rw [hint]
    have hd : |ρV x.val a - ρW x.val a| ≤ Lσ * dist V_S W_S := hσ_lip x.val a
    calc |(sp.toParams.U_T x.val a (ρV x.val a) - sp.toParams.U_T x.val a (ρW x.val a))
          + sp.toParams.β_T * (sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
              - sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a))))|
        ≤ |sp.toParams.U_T x.val a (ρV x.val a) - sp.toParams.U_T x.val a (ρW x.val a)|
          + |sp.toParams.β_T * (sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
              - sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a))))| := by
            simp only [← Real.norm_eq_abs]; exact norm_add_le _ _
      _ ≤ L_UT * |ρV x.val a - ρW x.val a|
          + sp.toParams.β_T * (L_smVT * (LF * |ρV x.val a - ρW x.val a|)) := by
            apply add_le_add (hUT_lip _ _ _ _)
            rw [abs_mul, abs_of_nonneg hβT0]
            apply mul_le_mul_of_nonneg_left _ hβT0
            calc |sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
                  - sp.smear WT (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a)))|
                ≤ L_smVT * dist (Sanctions.clipS' (sp.toParams.F x.val (ρV x.val a)))
                    (Sanctions.clipS' (sp.toParams.F x.val (ρW x.val a))) := hsmVT_lip _ _
              _ ≤ L_smVT * (LF * |ρV x.val a - ρW x.val a|) := by
                  apply mul_le_mul_of_nonneg_left _ hL_smVT
                  rw [Subtype.dist_eq, Real.dist_eq]; exact hclipF_lip x.val _ _
      _ = (L_UT + sp.toParams.β_T * L_smVT * LF) * |ρV x.val a - ρW x.val a| := by ring
      _ ≤ (L_UT + sp.toParams.β_T * L_smVT * LF) * (Lσ * dist V_S W_S) := by
            apply mul_le_mul_of_nonneg_left hd; positivity
      _ = Mc := by rw [hMc]; ring
  -- combine via the contraction + triangle
  have hkey : dist VT WT ≤ sp.toParams.β_T * dist VT WT + Mc := by
    calc dist VT WT
        = dist (sp.targetDynBCF_shock ρV hσcV VT) (sp.targetDynBCF_shock ρW hσcW WT) := by
          rw [hVTfix, hWTfix]
      _ ≤ dist (sp.targetDynBCF_shock ρV hσcV VT) (sp.targetDynBCF_shock ρV hσcV WT)
          + dist (sp.targetDynBCF_shock ρV hσcV WT) (sp.targetDynBCF_shock ρW hσcW WT) :=
          dist_triangle _ _ _
      _ ≤ sp.toParams.β_T * dist VT WT + Mc :=
          add_le_add (sp.targetDynBCF_shock_dist_le ρV hσcV VT WT) hsecond
  -- (1-β_T)·dist VT WT ≤ Mc ⇒ dist VT WT ≤ Mc/(1-β_T)
  have h1mβ : 0 < 1 - sp.toParams.β_T := by linarith
  rw [hMc] at hkey
  rw [div_mul_eq_mul_div, le_div_iff₀ h1mβ]
  nlinarith [hkey]

/-- **The shocked Target ROW inequality (two-sided-coupling checklist,
step 1).** The shocked Target Bellman operator, viewed as a function of
the pair (own continuation `V_T`; Sender continuation `V_S` entering
through the shocked greatest selector `σ_dyn_top (smear V_S)`),
satisfies the Perov/Schur-shaped row bound

  `dist (T(V_T, V_S)) (T(V_T', W_S))
     ≤ β_T · dist V_T V_T' + L_TS · dist V_S W_S`

with the closed-form cross coefficient
`L_TS = (L_UT + β_T·L_smVT·LF) · Lσ` — finite and generically nonzero
on the shocked layer, because the shocked Sender selector is genuinely
LIPSCHITZ in the value argument (`sigma_top_lipschitz_in_V`; at the box
kernel `Lσ = 2·β_S·Lκ·LF/c` with `Lκ = 1/h` kernel-derived, while the
strong-concavity constant `c` is a consumed hypothesis, not
kernel-derived). This
is the Target half of a shocked two-sided-coupled certificate: the
deterministic BCF layer provably cannot supply a finite `L_TS` off the
corner (the selector is only Hölder-½ there, `StrongConcaveHolder`),
while here it is a theorem. The Sender row remains gated on the single
named leader regularity `h_obj_diff` (see `lead_lipschitz_via_core`
below). Rule 3: consumes only the hypothesis shapes already carried by
`VTdyn_shock_lipschitz` — no new assumption surface. -/
theorem targetDynBCF_shock_row_lipschitz
    {Lσ L_UT L_smVT LF : ℝ} (hLσ : 0 ≤ Lσ) (hL_UT : 0 ≤ L_UT)
    (hL_smVT : 0 ≤ L_smVT) (hLF : 0 ≤ LF)
    (V_T V_T' V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσcV : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S) xa.1 xa.2))
    (hσcW : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear W_S) xa.1 xa.2))
    (hσ_lip : ∀ x a, |sp.toParams.σ_dyn_top (sp.smear V_S) x a
      - sp.toParams.σ_dyn_top (sp.smear W_S) x a| ≤ Lσ * dist V_S W_S)
    (hUT_lip : ∀ x a s s', |sp.toParams.U_T x a s - sp.toParams.U_T x a s'|
      ≤ L_UT * |s - s'|)
    (hsmVT_lip : ∀ z z', |sp.smear V_T' z - sp.smear V_T' z'|
      ≤ L_smVT * dist z z')
    (hclipF_lip : ∀ x s s', |(Sanctions.clipS' (sp.toParams.F x s)).val
      - (Sanctions.clipS' (sp.toParams.F x s')).val| ≤ LF * |s - s'|) :
    dist (sp.targetDynBCF_shock
        (sp.toParams.σ_dyn_top (sp.smear V_S)) hσcV V_T)
      (sp.targetDynBCF_shock
        (sp.toParams.σ_dyn_top (sp.smear W_S)) hσcW V_T')
      ≤ sp.toParams.β_T * dist V_T V_T'
        + ((L_UT + sp.toParams.β_T * L_smVT * LF) * Lσ) * dist V_S W_S := by
  set ρV := sp.toParams.σ_dyn_top (sp.smear V_S) with hρV
  set ρW := sp.toParams.σ_dyn_top (sp.smear W_S) with hρW
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
    have hd : |ρV x.val a - ρW x.val a| ≤ Lσ * dist V_S W_S := hσ_lip x.val a
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
            apply add_le_add (hUT_lip _ _ _ _)
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

open scoped BoundedContinuousFunction

/-- **Leader argmax-Lipschitz (`lead_lip`) via the argmax-core.** The leader
policy `lead V` (maximiser of the leader objective `leaderObj V x ·`) is Lipschitz
in `V` with constant `2·L_lead/c_T`, given strong concavity of the leader
objective (`sc`, consumed as in the deterministic development) and the
**leader objective-difference action-Lipschitz** estimate `h_obj_diff` with
constant `∝ dist V W`.

`h_obj_diff` is the one genuinely-irreducible new input for the Stackelberg
leader: because the Sender response `σ(x,a)` enters the leader objective and
depends on the leader's action `a`, the objective difference's variation in `a`
is *not* delivered by the shock alone (unlike the Sender side, whose objective
difference is a bare smeared-continuation term). The σ-Lipschitz and
`V_T_dyn`-Lipschitz bounds (proved above) control its *magnitude*; `h_obj_diff`
supplies the missing action-direction control. This isolates the Stackelberg
coupling as a single named regularity, exactly as `StrongConcaveHolder` isolates
strong concavity. -/
theorem lead_lipschitz_via_core
    (leaderObj : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → ℝ → ℝ → ℝ)
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → ℝ → ℝ)
    {c_T L_lead : ℝ} (hc : 0 < c_T) (hL : 0 ≤ L_lead)
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ)
    (scV : StrongConcaveOn Sanctions.I c_T (fun a => leaderObj V x a))
    (scW : StrongConcaveOn Sanctions.I c_T (fun a => leaderObj W x a))
    (hmemV : lead V x ∈ Sanctions.I) (hmemW : lead W x ∈ Sanctions.I)
    (loptV : IsMaxOn (fun a => leaderObj V x a) Sanctions.I (lead V x))
    (loptW : IsMaxOn (fun a => leaderObj W x a) Sanctions.I (lead W x))
    (h_obj_diff :
      |(leaderObj V x (lead V x) - leaderObj W x (lead V x))
        - (leaderObj V x (lead W x) - leaderObj W x (lead W x))|
        ≤ (L_lead * dist V W) * |lead V x - lead W x|) :
    |lead V x - lead W x| ≤ (2 * L_lead / c_T) * dist V W := by
  have hLd : 0 ≤ L_lead * dist V W := mul_nonneg hL dist_nonneg
  have hcore := Sanctions.argmax_lipschitz_of_strongConcave_lipschitzDiff
    hLd (convex_Icc 0 1) scV scW hmemV hmemW
    (fun y hy => loptV hy) (fun y hy => loptW hy) h_obj_diff
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [hcore]

namespace AbstractGame
namespace ShockedParams

open BoundedContinuousFunction

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Interior shocked existence with `lead_lip` discharged.** The Banach
interior existence (`shockedFeedbackStackelbergTop_interior`) but with its one
consumed input `lead_lip` *derived* from the argmax-core: it now consumes only
the leader strong concavity (`sc`), the leader top-optimality (`lopt_obj`), and
the leader objective-difference action-Lipschitz estimate (`h_obj_diff`) — the
last being the isolated Stackelberg-coupling regularity. The contraction margin
becomes `β_S + L_Ua·(2 L_lead/c_T) < 1`. CAUTION: this margin is NOT
automatically satisfiable by widening the shock — `L_lead` is a consumed
hypothesis scalar with no proven kernel-decay law (`L_lead → 0` was never
derived), and widening `h` shrinks only the σ-channel constant (`Lκ = 1/h`)
while degrading the consumed concavity constants, so the Schur and interior
margins pull against each other (confirmed quantitatively dead at the P3
witness by the 2026-07-04 kernel-width audit). The margin must be checked as
a hypothesis at each economy. Wiring: `lead_lipschitz_via_core` supplies
`lead_lip`. -/
theorem shockedFeedbackStackelbergTop_interior_discharged
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    (leaderObj : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → ℝ → ℝ → ℝ)
    {c_T L_lead L_Ua : ℝ} (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead) (hLUa : 0 ≤ L_Ua)
    (sc : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T (fun a => leaderObj V x.val a))
    (lopt_obj : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      IsMaxOn (fun a => leaderObj V x.val a) Sanctions.I (lead V x.val))
    (h_obj_diff : ∀ (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      |(leaderObj V x.val (lead V x.val) - leaderObj W x.val (lead V x.val))
        - (leaderObj V x.val (lead W x.val) - leaderObj W x.val (lead W x.val))|
        ≤ (L_lead * dist V W) * |lead V x.val - lead W x.val|)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤ L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * (2 * L_lead / c_T) < 1)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Continuous (fun xa : ℝ × ℝ => sp.toParams.σ_dyn_top (sp.smear V) xa.1 xa.2))
    (lead_opt : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      sp.bellmanS_shock (lead V) (lead_cont V) V = V →
      ∀ x ∈ Sanctions.S, IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock V (hσc V))) (sp.smear V) x a) Sanctions.I (lead V x)) :
    Nonempty sp.ShockedFeedbackStackelbergEquilibriumTop := by
  refine sp.shockedFeedbackStackelbergTop_interior lead lead_cont lead_mem
    (2 * L_lead / c_T) L_Ua (by positivity) hLUa ?_ hU_lip hmargin hσc lead_opt
  intro V W x
  exact Sanctions.lead_lipschitz_via_core leaderObj lead hcT hLlead V W x.val
    (sc V x) (sc W x) (lead_mem V x.val x.property) (lead_mem W x.val x.property)
    (lopt_obj V x) (lopt_obj W x) (h_obj_diff V W x)

/-- **State-local interior shocked existence with leader Lipschitzness derived.**
This is the physical-state-continuity version of
`shockedFeedbackStackelbergTop_interior_discharged`; the same strong-concavity
argmax estimate supplies the leader policy's value-Lipschitz bound. -/
theorem shockedFeedbackStackelbergTop_interior_discharged_local
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    (leaderObj : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → ℝ → ℝ → ℝ)
    {c_T L_lead L_Ua : ℝ} (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead)
    (hLUa : 0 ≤ L_Ua)
    (sc : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T (fun a => leaderObj V x.val a))
    (lopt_obj : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
      (x : ↥(Sanctions.S : Set ℝ)),
      IsMaxOn (fun a => leaderObj V x.val a) Sanctions.I (lead V x.val))
    (h_obj_diff : ∀ (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
      (x : ↥(Sanctions.S : Set ℝ)),
      |(leaderObj V x.val (lead V x.val) - leaderObj W x.val (lead V x.val))
        - (leaderObj V x.val (lead W x.val) - leaderObj W x.val (lead W x.val))| ≤
          (L_lead * dist V W) * |lead V x.val - lead W x.val|)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤
        L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * (2 * L_lead / c_T) < 1)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        sp.toParams.σ_dyn_top (sp.smear V) xa.1.val xa.2))
    (lead_opt : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      sp.bellmanS_shock (lead V) (lead_cont V) V = V →
      ∀ x ∈ Sanctions.S, IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock_local V (hσc V)))
        (sp.smear V) x a) Sanctions.I (lead V x)) :
    Nonempty sp.ShockedFeedbackStackelbergEquilibriumTop := by
  refine sp.shockedFeedbackStackelbergTop_interior_local lead lead_cont lead_mem
    (2 * L_lead / c_T) L_Ua (by positivity) hLUa ?_ hU_lip hmargin hσc lead_opt
  intro V W x
  exact Sanctions.lead_lipschitz_via_core leaderObj lead hcT hLlead V W x.val
    (sc V x) (sc W x) (lead_mem V x.val x.property) (lead_mem W x.val x.property)
    (lopt_obj V x) (lopt_obj W x) (h_obj_diff V W x)

/-- **Canonical interior shocked existence — `leaderObj` pinned to the real
Target payoff.** This is the headline form. Unlike
`shockedFeedbackStackelbergTop_interior_discharged` (which takes the leader
objective as a *free* function `leaderObj`, so the strong-concavity and
objective-difference hypotheses could be satisfied by a scaffold unrelated to
the economic payoff), here the leader objective **is** the genuine shocked
Target integrand

  `leaderObj V x a = joint_T_top_integrand (smear (V_T_dyn_shock V (hσc V))) (smear V) x a`,

so `sc` (strong concavity in the action) and `h_obj_diff` (objective-difference
action-Lipschitz) are assertions about the *real* leader payoff, closing the
Rule-14 free-parameter-laundering gap. Because `lopt_obj` now asserts the leader
maximises that same real integrand, the previously-separate `lead_opt`
hypothesis is **derived** from it (one fewer consumed hypothesis): the leader's
equilibrium optimality is no longer an independent assumption parallel to the
concavity surface.

Consumed (the honest remaining surface): leader continuity/feasibility, leader
strong concavity `sc` of the real integrand, `lopt_obj` (the leader is the
argmax of the real integrand — the Rule-1 best-response obligation), the
Stackelberg-coupling regularity `h_obj_diff` of the real integrand (provably not
derivable from the kernel — see the limitations discussion), `U_S` action-Lipschitz,
`σ` joint continuity `hσc`, the strict positivity `hcT : 0 < c_T` of the
strong-concavity modulus, the sign condition `hLlead : 0 ≤ L_lead`, and the
contraction margin.

**Two sign binders, and why only one of them came off.** `0 ≤ L_Ua` used to be
assumed and is now *derived* from `hU_lip` (see the proof below): its multiplier
`|a − a'|` ranges over universally quantified actions in `[0,1]`, so `a = 1`,
`a' = 0` forces it to `1` and `abs_nonneg` gives the sign. `hLlead` looks like
the same shape and is **not**: `h_obj_diff`'s multiplier is
`|lead V x − lead W x|`, and `lead` is a free function parameter constrained only
by `lead_cont` and `lead_mem` — the constant selector satisfies both and
collapses that multiplier to `0`, leaving `|…| ≤ 0`, which constrains `L_lead` in
neither direction. Dropping `hLlead` would need a nontriviality condition on
`lead`, i.e. a new hypothesis, so it stays. `hcT` is likewise irreducible and is
load-bearing rather than cosmetic: without it `sc` is vacuous and the margin
`β_S + L_Ua·(2·L_lead/c_T) < 1` divides by zero. -/
theorem shockedFeedbackStackelbergTop_interior_discharged_canonical
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    {c_T L_lead L_Ua : ℝ} (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Continuous (fun xa : ℝ × ℝ => sp.toParams.σ_dyn_top (sp.smear V) xa.1 xa.2))
    (sc : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock V (hσc V))) (sp.smear V) x.val a))
    (lopt_obj : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock V (hσc V))) (sp.smear V) x.val a)
        Sanctions.I (lead V x.val))
    (h_obj_diff : ∀ (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)),
      |(sp.toParams.joint_T_top_integrand (sp.smear (sp.V_T_dyn_shock V (hσc V)))
            (sp.smear V) x.val (lead V x.val)
          - sp.toParams.joint_T_top_integrand (sp.smear (sp.V_T_dyn_shock W (hσc W)))
            (sp.smear W) x.val (lead V x.val))
        - (sp.toParams.joint_T_top_integrand (sp.smear (sp.V_T_dyn_shock V (hσc V)))
            (sp.smear V) x.val (lead W x.val)
          - sp.toParams.joint_T_top_integrand (sp.smear (sp.V_T_dyn_shock W (hσc W)))
            (sp.smear W) x.val (lead W x.val))|
        ≤ (L_lead * dist V W) * |lead V x.val - lead W x.val|)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤ L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * (2 * L_lead / c_T) < 1) :
    Nonempty sp.ShockedFeedbackStackelbergEquilibriumTop :=
  sp.shockedFeedbackStackelbergTop_interior_discharged lead lead_cont lead_mem
    (fun V x a => sp.toParams.joint_T_top_integrand
      (sp.smear (sp.V_T_dyn_shock V (hσc V))) (sp.smear V) x a)
    hcT hLlead
    (by
      -- `0 ≤ L_Ua` is DERIVED from `hU_lip`, not assumed: instantiate the
      -- action-Lipschitz bound at the separated pair `a = 1`, `a' = 0`, where
      -- `|a - a'| = 1`, and read off the sign from `abs_nonneg`.
      have hx : (0 : ℝ) ∈ Sanctions.S := by simp [Sanctions.S]
      have h := hU_lip ⟨0, hx⟩ 1 0 (by norm_num [Sanctions.I])
        (by norm_num [Sanctions.I]) 0 (by norm_num [Sanctions.I])
      have h0 := abs_nonneg (sp.toParams.U_S (0 : ℝ) 1 0 - sp.toParams.U_S (0 : ℝ) 0 0)
      simp only [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at h
      linarith)
    sc lopt_obj h_obj_diff hU_lip hmargin hσc
    (fun V _hfix x hx => lopt_obj V ⟨x, hx⟩)

/-- **Canonical state-local interior shocked existence.**
The leader objective is the genuine shocked Target payoff built from
`V_T_dyn_shock_local`; therefore physical-state continuity of the Sender argmax
is sufficient, while leader optimality is still derived from maximization of the
same real composite objective. -/
theorem shockedFeedbackStackelbergTop_interior_discharged_canonical_local
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    {c_T L_lead L_Ua : ℝ} (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead)
    (hLUa : 0 ≤ L_Ua)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        sp.toParams.σ_dyn_top (sp.smear V) xa.1.val xa.2))
    (sc : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
      (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock_local V (hσc V))) (sp.smear V) x.val a))
    (lopt_obj : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
      (x : ↥(Sanctions.S : Set ℝ)),
      IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock_local V (hσc V))) (sp.smear V) x.val a)
        Sanctions.I (lead V x.val))
    (h_obj_diff : ∀ (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
      (x : ↥(Sanctions.S : Set ℝ)),
      |(sp.toParams.joint_T_top_integrand
            (sp.smear (sp.V_T_dyn_shock_local V (hσc V)))
            (sp.smear V) x.val (lead V x.val)
          - sp.toParams.joint_T_top_integrand
            (sp.smear (sp.V_T_dyn_shock_local W (hσc W)))
            (sp.smear W) x.val (lead V x.val))
        - (sp.toParams.joint_T_top_integrand
            (sp.smear (sp.V_T_dyn_shock_local V (hσc V)))
            (sp.smear V) x.val (lead W x.val)
          - sp.toParams.joint_T_top_integrand
            (sp.smear (sp.V_T_dyn_shock_local W (hσc W)))
            (sp.smear W) x.val (lead W x.val))| ≤
          (L_lead * dist V W) * |lead V x.val - lead W x.val|)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤
        L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * (2 * L_lead / c_T) < 1) :
    Nonempty sp.ShockedFeedbackStackelbergEquilibriumTop :=
  sp.shockedFeedbackStackelbergTop_interior_discharged_local
    lead lead_cont lead_mem
    (fun V x a => sp.toParams.joint_T_top_integrand
      (sp.smear (sp.V_T_dyn_shock_local V (hσc V))) (sp.smear V) x a)
    hcT hLlead hLUa sc lopt_obj h_obj_diff hU_lip hmargin hσc
    (fun V _hfix x hx => lopt_obj V ⟨x, hx⟩)

end ShockedParams
end AbstractGame
end Sanctions
