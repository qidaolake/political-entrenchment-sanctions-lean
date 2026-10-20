/-
Sanctions/Examples/CollapseReliefThreshold.lean

**At the collapse, relief exists exactly up to `β_T*`** (step 2, target 2c, part A, the abstract
companions Z1–Z5 of plan `STEP2_2c.md`; 2026-10-10).

`collapse_equilibrium_threshold_le_tight` (`PlacableSenderCollapseInstance.lean`) closes the
defiance side at the collapse: under the paper's nine tightness conditions a full-defiance
equilibrium exists iff `β_T* ≤ β_T`. On the relief side the class had only sufficient
conditions: existence below `β_T*` through the strict relief certificate, and non-existence
from the loss-offset patience bound `c/(d_lo v_lo + c g_lo)` up (`reliefExistence_lt_margin`),
which lies strictly above `β_T*`. This file closes the relief side.

1. **The weak relief certificate at the collapse** (`collapse_relief_side_le_iff`): under the
   fourteen tightness equalities and the stage relief margin,
   `ℓ_hi M_tot ≤ k_lo(p_lo − β_T d_hi K_T^rel)` holds iff `β_T ≤ β_T*` (the weak form of
   `collapse_threshold'`(2)).
2. **The relief value's lower slope** (`VTrel_lowerSlope_of_Lalpha_eq_zero`, general in `F`):
   when the zero level's Lipschitz constant `L_α` vanishes, the zero level is constant and the
   relief value has lower state slope `v_lo/(1 − β_T g_lo)`.
3. **No relief above `β_T*`** (`collapse_no_relief_gt`): above `β_T*` the sharp defiance side
   holds at `g_T` (`collapse_threshold'`(1)); at the collapse `L_α = 0` and `n_lo = 0`, so the
   relief value has lower slope `g_T`, and full defiance is the unique Target maximiser at the
   relief values (`targetArgmax_eq_zero_of_sharp`). But a relief equilibrium complies at the
   positive zero level. So no equilibrium has zero sanctions at every state.
4. **The exact relief threshold** (`collapse_relief_iff`, fourteen equalities;
   `ChordEconomyRelief.collapse_relief_iff_tight`, the paper's nine conditions through the
   re-certification `collapseRecert`): a top-selector equilibrium with zero sanctions at every
   state exists iff `β_T ≤ β_T*`. With the defiance side, **both regimes exist exactly at
   `β_T = β_T*`** (`ChordEconomyRelief.collapse_regimes_tight`).
5. **Relief uniqueness in the carrier class below `β_T*`** (`collapse_relief_unique_carrier`).

The linear–quadratic benchmark (`LQBenchmark.lean`) is an instance, where the same statements
are also proved from closed forms.

**Rule 22: AFFINE BY HYPOTHESIS.** `d_lo = d_hi` pins `F = affineF d_lo` on the square; each
result here that carries it is the affine collapse stated over the general class. Item 2 is
general in `F`. **Rule 3.** No new hypothesis: every hypothesis is an existing predicate
(`Interior`, `StageRelief`, `Placable`, `ZeroSanctionNeutral`) or one of the existing tightness
equalities.
-/
import Sanctions.Examples.PlacableSenderCollapseInstance

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-- **The weak relief certificate at the collapse is `β_T ≤ β_T*`.** Under the stage relief
margin and thirteen of the fourteen tightness equalities (`M_s = 0` is not read),
`ℓ_hi M_tot ≤ k_lo(p_lo − β_T d_hi K_T^rel)` holds iff `β_T ≤ β_T*`: the weak form of
`collapse_threshold'`(2), which decides the equality case.
Scope: enriched chord class under thirteen tightness equalities (affine by hypothesis). -/
theorem collapse_relief_side_le_iff (hSR : E.StageRelief) (hSigV : E.SigV = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi) :
    E.ℓhi * E.Mtot ≤ E.klo * (E.plo - E.β_T * E.dhi * E.KTrel) ↔ E.β_T ≤ E.betaStar := by
  have hr := E.rhi_eq_zero_of_SigV_eq_zero hSigV
  have hnlo := E.nlo_eq_zero_of_tight_state_rates hv hnhi
  have hM := E.collapse_Mtot hQ hτ hMcx hMcs
  have hKr := E.collapse_KTrel hr hSigV hτ hMcx hMmix hv hnlo hg
  rw [hM, hKr, hp, ← hd, hk, ← hℓ]
  set D := E.c - E.ℓlo * E.q / E.khi with hDdef
  have hkh := E.khi_pos
  have hD : 0 < D := by
    have hsr : E.StageRelief := hSR
    unfold ChordEconomyRelief.StageRelief at hsr
    rw [hQ, hk, ← hℓ, hp] at hsr
    rw [hDdef, sub_pos, div_lt_iff₀ hkh]
    linarith
  have hsum := E.glo_add_dlo_eq_one_of_tight hg hd
  have hglo : E.glo = 1 - E.dlo := by linarith
  have hβ0 := E.hβT0
  have hβ1 := E.hβT1
  have hd0 := E.hdlo0
  have hd1 : E.dlo ≤ 1 := by linarith [E.hglo0]
  have hv0 := E.hvlo
  have hden : 0 < 1 - E.β_T * (1 - E.dlo) := by nlinarith
  have hgT : E.gT = E.vlo / (1 - E.β_T * (1 - E.dlo)) := by
    unfold ChordEconomy.gT; rw [hnlo, hglo]; ring
  have hP : 0 < E.dlo * E.vlo + (1 - E.dlo) * D := by
    have := mul_pos hd0 hv0
    have := mul_nonneg (sub_nonneg.mpr hd1) hD.le
    linarith
  have step1 : E.ℓlo * E.q ≤ E.khi * (E.c - E.β_T * E.dlo * E.gT)
      ↔ E.β_T * E.dlo * E.gT ≤ D := by
    rw [hDdef]
    constructor
    · intro h
      have : E.ℓlo * E.q / E.khi ≤ E.c - E.β_T * E.dlo * E.gT := by
        rw [div_le_iff₀ hkh]; linarith
      linarith
    · intro h
      have : E.ℓlo * E.q / E.khi ≤ E.c - E.β_T * E.dlo * E.gT := by linarith
      rw [div_le_iff₀ hkh] at this
      linarith
  rw [step1]
  have hsplit : E.β_T * E.dlo * (E.vlo / (1 - E.β_T * (1 - E.dlo)))
      = E.β_T * E.dlo * E.vlo / (1 - E.β_T * (1 - E.dlo)) := by ring
  unfold ChordEconomyRelief.betaStar
  rw [← hDdef, hgT, hsplit, div_le_iff₀ hden, le_div_iff₀ hP]
  constructor <;> intro h <;> linarith

/-- **With a zero `L_α` the relief value has lower state slope `v_lo/(1 − β_T g_lo)`.** If the
zero level's Lipschitz constant vanishes, the zero level is constant; along it the stage payoff
rises at least at rate `v_lo` (T6 at zero sanction) and the zero-sanction transition at least at
rate `g_lo`, so `V_rel(y) − g y` is nondecreasing for `g = v_lo/(1 − β_T g_lo)`
(`monotone_of_eq_add_mul_comp`).
Scope: general class (enriched chord class; the hypothesis `L_α = 0` holds at the collapse). -/
theorem VTrel_lowerSlope_of_Lalpha_eq_zero (hInt : E.Interior) (hP : E.Placable)
    (hLa : E.Lalpha = 0) :
    Params.LowerSlopeOnValueOn (E.VTrel hInt hP) (Icc (0 : ℝ) 1)
      (E.vlo / (1 - E.β_T * E.glo)) := by
  set g := E.vlo / (1 - E.β_T * E.glo) with hgdef
  have hden : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have hgspec : g * (1 - E.β_T * E.glo) = E.vlo := div_mul_cancel₀ _ hden.ne'
  have hg0 : 0 ≤ g := div_nonneg E.hvlo.le hden.le
  have hzc : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), E.zeroLevel y₁.val = E.zeroLevel y₂.val := by
    intro y₁ y₂
    have h := E.zeroLevel_lipschitz hInt hP y₁.property y₂.property
    rw [hLa, zero_mul] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  have hWmono : Monotone (fun y : ↥(Sanctions.S : Set ℝ) => E.VTrel hInt hP y - g * y.val) := by
    refine Foundations.DiscountedExtremum.monotone_of_eq_add_mul_comp
      (h := fun y : ↥(Sanctions.S : Set ℝ) =>
        E.toParams.U_T y.val (E.zeroLevel y.val) 0 - g * y.val
          + E.β_T * g * E.toParams.F y.val 0)
      (z := fun y : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (E.toParams.F y.val 0))
      E.hβT0.le E.hβT1 (M := ‖E.VTrel hInt hP‖ + g) (fun y => ?_) ?_ ?_ (fun y => ?_)
    · have h1 : |E.VTrel hInt hP y| ≤ ‖E.VTrel hInt hP‖ := by
        have := BoundedContinuousFunction.norm_coe_le_norm (E.VTrel hInt hP) y
        rwa [Real.norm_eq_abs] at this
      have h2 : |g * y.val| ≤ g := by
        rw [abs_of_nonneg (mul_nonneg hg0 y.property.1)]
        nlinarith [y.property.2]
      calc |E.VTrel hInt hP y - g * y.val|
          ≤ |E.VTrel hInt hP y| + |g * y.val| := abs_sub _ _
        _ ≤ ‖E.VTrel hInt hP‖ + g := add_le_add h1 h2
    · intro y₁ y₂ hle
      have hle' : y₁.val ≤ y₂.val := hle
      have hz₁ := E.zeroLevel_mem hP y₁.property
      have hstate := E.hUT_stateLo (E.zeroLevel y₁.val) hz₁ 0 zero_mem_I y₁.val y₁.property
        y₂.val y₂.property hle'
      simp only [mul_zero, add_zero] at hstate
      have hF := (E.hbandAll 0 zero_mem_I y₁.val y₁.property y₂.val y₂.property hle').1
      have hgβ : 0 ≤ E.β_T * g := mul_nonneg E.hβT0.le hg0
      have hF' := mul_le_mul_of_nonneg_left hF hgβ
      change E.toParams.U_T y₁.val (E.zeroLevel y₁.val) 0 - g * y₁.val
          + E.β_T * g * E.toParams.F y₁.val 0
        ≤ E.toParams.U_T y₂.val (E.zeroLevel y₂.val) 0 - g * y₂.val
          + E.β_T * g * E.toParams.F y₂.val 0
      rw [← hzc y₁ y₂]
      have hkey : g * (y₂.val - y₁.val) = E.vlo * (y₂.val - y₁.val)
          + E.β_T * g * (E.glo * (y₂.val - y₁.val)) := by
        linear_combination (y₂.val - y₁.val) * hgspec
      change E.vlo * (y₂.val - y₁.val) ≤ E.U_T y₂.val (E.zeroLevel y₁.val) 0
        - E.U_T y₁.val (E.zeroLevel y₁.val) 0 at hstate
      change E.β_T * g * (E.glo * (y₂.val - y₁.val))
        ≤ E.β_T * g * (E.F y₂.val 0 - E.F y₁.val 0) at hF'
      change E.U_T y₁.val (E.zeroLevel y₁.val) 0 - g * y₁.val + E.β_T * g * E.F y₁.val 0
        ≤ E.U_T y₂.val (E.zeroLevel y₁.val) 0 - g * y₂.val + E.β_T * g * E.F y₂.val 0
      nlinarith
    · intro y₁ y₂ hle
      have hle' : y₁.val ≤ y₂.val := hle
      exact Sanctions.clipS'_mono (E.F_mono_x 0 hle')
    · have hfix := congrArg (fun V : Val => V y) (E.VTrel_fix hInt hP)
      simp only at hfix
      rw [reliefOp_apply] at hfix
      have hFm : E.toParams.F y.val 0 ∈ (Sanctions.S : Set ℝ) :=
        E.F_maps y.val y.property 0 zero_mem_I
      simp only
      rw [Sanctions.clipS'_val_eq_of_mem hFm]
      linear_combination -hfix
  intro y₁ y₂ _ _ hle
  have h := hWmono hle
  have hle' : y₁.val ≤ y₂.val := hle
  simp only at h
  have hdist : dist y₁ y₂ = y₂.val - y₁.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdist]
  linarith

/-- **No relief above `β_T*` at the collapse.** Under interiority, placability, zero-sanction
neutrality, the stage relief margin and the fourteen tightness equalities, if `β_T* < β_T` no
top-selector equilibrium has zero sanctions at every state. The sharp defiance side holds at
`g_T` (`collapse_threshold'`(1)); the relief value has lower slope `g_T`
(`VTrel_lowerSlope_of_Lalpha_eq_zero`, with `L_α = 0` and `n_lo = 0` at the collapse); so full
defiance is the only Target maximiser at the relief values (`targetArgmax_eq_zero_of_sharp`),
while a relief equilibrium complies at its zero level, which is positive.
Scope: enriched chord class under the fourteen tightness equalities (affine by hypothesis). -/
theorem collapse_no_relief_gt (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hSigV : E.SigV = 0) (hMs : E.Ms = 0) (hτ : E.τx = 0)
    (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi) (hβ : E.betaStar < E.β_T)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) :
    ¬ ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0 := by
  intro hzero
  obtain ⟨hα, hVS, hVT⟩ := E.relief_equilibrium_of_zero_rule hInt hP hN Eq hzero
  have hsharp := ((E.collapse_threshold' hSR hSigV hMs hτ hMcx hMcs hMmix hQ hk hℓ hp hv hnhi
    hg hd).1).2 hβ
  have hL := E.collapse_Lresp' hSigV hτ hMcx hMmix
  have hLa : E.Lalpha = 0 := by
    unfold ChordEconomyCs.Lalpha; rw [hL, mul_zero, zero_div]
  have hnlo := E.nlo_eq_zero_of_tight_state_rates hv hnhi
  have hgT : E.gT = E.vlo / (1 - E.β_T * E.glo) := by
    unfold ChordEconomy.gT; rw [hnlo, zero_mul, add_zero]
  have hslope : Params.LowerSlopeOnValueOn (E.VTrel hInt hP) (Icc (0 : ℝ) 1) E.gT := by
    rw [hgT]; exact E.VTrel_lowerSlope_of_Lalpha_eq_zero hInt hP hLa
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hopt := Eq.α_opt_top 0 h0I
  rw [hα 0 h0I, hVS, hVT] at hopt
  have hopt' : IsMaxOn (fun a => E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 0 a)
      Sanctions.I (E.zeroLevel 0) := by
    rw [isMaxOn_iff] at hopt ⊢
    intro a ha
    have h := hopt a ha
    rwa [E.joint_T_top_integrand_eq E.VS01_mem _ h0I,
      E.joint_T_top_integrand_eq E.VS01_mem _ h0I] at h
  have hz0 := E.toChordEconomy.targetArgmax_eq_zero_of_sharp E.placationCeiling E.gT_pos.le
    hsharp hslope E.VS01_mem h0I (E.zeroLevel_mem hP h0I) hopt'
  have hr := E.ρ01_zeroLevel hP h0I
  rw [hz0] at hr
  have hpos := E.responsePath_pos E.VS01_mem h0I
  change 0 < E.response E.VS01 0 0 at hpos
  linarith

/-- **The exact relief threshold at the collapse** (fourteen equalities). Under interiority, the
stage relief margin, placability, zero-sanction neutrality and the fourteen tightness
equalities, a top-selector equilibrium with zero sanctions at every state exists iff
`β_T ≤ β_T*`. Existence: the weak relief certificate (`collapse_relief_side_le_iff`) gives the
relief best reply (`reliefBestReply_of_relief_side_le`) and so an equilibrium
(`exists_relief_equilibrium_iff`). Non-existence above: `collapse_no_relief_gt`.
Scope: enriched chord class under the fourteen tightness equalities (affine by hypothesis). -/
theorem collapse_relief_iff (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hSigV : E.SigV = 0) (hMs : E.Ms = 0) (hτ : E.τx = 0)
    (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi) :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0) ↔ E.β_T ≤ E.betaStar := by
  constructor
  · rintro ⟨Eq, hzero⟩
    by_contra hlt
    exact E.collapse_no_relief_gt hInt hSR hP hN hSigV hMs hτ hMcx hMcs hMmix hQ hk hℓ hp hv
      hnhi hg hd (not_le.mp hlt) Eq hzero
  · intro hβ
    have hrel := (E.collapse_relief_side_le_iff hSR hSigV hτ hMcx hMcs hMmix hQ hk hℓ hp hv
      hnhi hg hd).2 hβ
    exact (E.exists_relief_equilibrium_iff hInt hP hN).2
      (E.reliefBestReply_of_relief_side_le hInt hP hrel)

/-- **Relief is unique in the carrier class below `β_T*`, at the collapse.** Under
interiority, the stage relief margin, placability, zero-sanction neutrality and the fourteen
tightness equalities, if `β_T < β_T*` every top-selector equilibrium whose Sender value is in
the two-sided carrier complies at the zero level, has the relief values and realises a zero
sanction at every state: `unique_equilibrium_of_relief_side`, with the strict relief side from
`collapse_threshold'`(3) and the loop condition from `L_resp = 0`.
Scope: enriched chord class under the fourteen tightness equalities (affine by hypothesis);
equilibria with Sender value in the carrier only (not general). -/
theorem collapse_relief_unique_carrier (hInt : E.Interior) (hSR : E.StageRelief)
    (hP : E.Placable) (hN : E.ZeroSanctionNeutral) (hSigV : E.SigV = 0) (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi)
    (hβ : E.β_T < E.betaStar) (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS2) :
    (∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevel x) ∧ Eq.V_S = E.VS01 ∧ Eq.V_T = E.VTrel hInt hP
      ∧ ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0 := by
  have hrel := ((E.collapse_threshold' hSR hSigV hMs hτ hMcx hMcs hMmix hQ hk hℓ hp hv hnhi hg
    hd).2.2).2 hβ
  have hL := E.collapse_Lresp' hSigV hτ hMcx hMmix
  have hγ : E.β_T * E.LloopSharp < 1 := by
    unfold ChordEconomyTwoSided.LloopSharp
    rw [hL, zero_div, mul_zero, add_zero]
    exact E.βT_ghi_lt_one
  exact E.unique_equilibrium_of_relief_side hInt hP hγ hrel hN Eq hVS

end ChordEconomyCs

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable {E : ChordEconomyRelief}

/-- **The exact relief threshold at the collapse, from the paper's nine conditions.** Let a
relief economy satisfy interiority, the stage relief margin, placability, zero-sanction
neutrality and the nine tightness conditions (`σ_V = τ_x = n_hi = 0`, `Q̄ = q`, `k_lo = k_hi`,
`ℓ_lo = ℓ_hi`, `p_lo = c`, `v_lo = v_hi`, `d_lo = d_hi`). Then a top-selector equilibrium with
zero sanctions at every state exists iff `β_T ≤ β_T*`. It is `collapse_relief_iff` at the
re-certified member `collapseRecert`, which has the same game and the same `β_T*`.
Scope: relief extension under the paper's nine tightness conditions (affine by hypothesis). -/
theorem collapse_relief_iff_tight (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hSigV : E.SigV = 0) (hτ : E.τx = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hd : E.dlo = E.dhi) :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0) ↔ E.β_T ≤ E.betaStar :=
  (E.collapseRecert hSigV hd).collapse_relief_iff (collapseRecert_interior hSigV hd hInt) hSR
    (collapseRecert_placable hSigV hd hP) hN rfl rfl hτ rfl rfl rfl hQ hk hℓ hp hv hnhi rfl hd

/-- **At the collapse the two regimes meet exactly at `β_T*`, from the paper's nine
conditions.** Under interiority, the stage relief margin, placability, zero-sanction neutrality
and the nine tightness conditions: an equilibrium with zero sanctions at every state exists iff
`β_T ≤ β_T*`, and one with full defiance at every state exists iff `β_T* ≤ β_T`. So below
`β_T*` only relief exists among the two, above it only full defiance, and at `β_T = β_T*` both.
Scope: relief extension under the paper's nine tightness conditions (affine by hypothesis). -/
theorem collapse_regimes_tight (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hSigV : E.SigV = 0) (hτ : E.τx = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hd : E.dlo = E.dhi) :
    ((∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0) ↔ E.β_T ≤ E.betaStar)
    ∧ ((∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
        ↔ E.betaStar ≤ E.β_T) :=
  ⟨collapse_relief_iff_tight hInt hSR hP hN hSigV hτ hQ hk hℓ hp hv hnhi hd,
    collapse_equilibrium_threshold_le_tight hInt hSR hP hSigV hτ hQ hk hℓ hp hv hnhi hd⟩

end ChordEconomyRelief

end

end Examples
end Sanctions
