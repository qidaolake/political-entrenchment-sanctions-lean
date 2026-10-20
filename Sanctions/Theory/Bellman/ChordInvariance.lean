/-
Sanctions/Theory/Bellman/ChordInvariance.lean

**Carrier invariance on a two-sided cone, under a general transition.**

`mem_valLipGainBall_bellman_closedForm` (`InvariantLipGainBall.lean`) keeps a
value inside its carrier by demanding the Bellman image have an exact closed
form, which forces the corner section `y ↦ F(y,1)` to be affine. That is the
step which made the certified family's *realised* recursion affine — not the
model, but the proof technique.

This file removes it. The transition enters only through the two-sided band
`CornerStateChord F glo ghi`, and the carrier becomes a genuine cone
(`g < K`) rather than a slope-pinned ball. Three legs, each priced by a
Stokey–Lucas closed form already in `Foundations/StokeyLucas.lean`:

* **norm** — `M ≥ bellmanNormBound β M_U`; does not mention `F` at all;
* **Lipschitz** — `K ≥ bellmanLipConstant β ghi L_U`, consuming the band's
  UPPER half;
* **lower slope** — `g ≤ g_U/(1 − β·glo)`, consuming the LOWER half.

Setting `glo = ghi` collapses the cone to the pinned ball and recovers the
closed-form route, so nothing previously proved is lost.

**One extra transition-side requirement, and it is load-bearing.** The
lower-slope leg needs the corner section to map `[0,1]` into itself. That is
*derivable* from the band together with `F 1 1 = 1` and `ghi ≤ 1`
(`cornerSection_mapsTo_of_chord`), so it costs no assumption — but it cannot
be dropped: the escape counterexample below compiles a band-satisfying
transition whose corner section leaves the interval and whose Bellman image
then leaves the carrier.

The separating witnesses live in `Examples/ChordInvarianceWitnesses.lean`
(moved there 2026-08-22, Rule 22): a genuinely non-affine corner section
admitting no `CornerSectionTop`, an instance with `g < K` strictly, and the
escape refutation showing the interval-preservation side condition above is
load-bearing. This file is general in the transition and carries no numerals.
-/

import Sanctions.Theory.Bellman.InvariantLipGainBall
import Sanctions.Foundations.TransitionChords

namespace Sanctions
namespace AbstractGame
namespace Params

open Set BoundedContinuousFunction Sanctions.TransitionChords

/-- **CORE 2: two-sided-cone carrier invariance for a general transition.**

General in `F`: the transition enters only through the corner band
`CornerStateChord F glo ghi` and the interval preservation `hF_mem` of the
corner section. If `V` is in the cone carrier (sup-norm at most `M`, Lipschitz
rate at most `K`, lower slope at least `g`) and `M`, `K`, `g` clear the three
Stokey–Lucas closed forms, then the corner-pinned Bellman image `W` of `V` is in
the same carrier.

The ordering `glo ≤ ghi` of the band's two rates is no longer a hypothesis: the
band forces it (`CornerStateChord.rates_le`; BG1.4, 2026-10-06). -/
theorem mem_valLipGainBall_bellman_chord
    {β glo ghi c₀ L_U g_U M_U M K g : ℝ}
    {stage : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hβ_nn : 0 ≤ β) (hβ_lt : β < 1)
    (hglo_nn : 0 ≤ glo) (hβghi : β * ghi < 1)
    (hL_U_nn : 0 ≤ L_U) (hg_nn : 0 ≤ g)
    (hstage_bd : ∀ y ∈ Icc (0 : ℝ) 1, |c₀ + stage y| ≤ M_U)
    (hstage_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
        |stage y₂ - stage y₁| ≤ L_U * |y₂ - y₁|)
    (hstage_slope : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
        g_U * (y₂ - y₁) ≤ stage y₂ - stage y₁)
    (hF_mem : ∀ y ∈ Icc (0 : ℝ) 1, F y 1 ∈ Icc (0 : ℝ) 1)
    (hchord : CornerStateChord F glo ghi)
    (hM : StokeyLucas.bellmanNormBound β M_U ≤ M)
    (hK : StokeyLucas.bellmanLipConstant β ghi L_U ≤ K)
    (hg : g ≤ StokeyLucas.bellmanLowerSlopeConstant β glo g_U)
    {V W : Val}
    (hV : V ∈ valLipGainBall M K g 0)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
        W y = c₀ + stage y.val + β * V (Sanctions.clipS' (F y.val 1))) :
    W ∈ valLipGainBall M K g 0 := by
  -- ## Sign bookkeeping and the three cone margins.
  have hglo_le_ghi : glo ≤ ghi := hchord.rates_le
  have hghi_nn : (0 : ℝ) ≤ ghi := le_trans hglo_nn hglo_le_ghi
  have hden_ghi : (0 : ℝ) < 1 - β * ghi := by linarith
  have hβglo : β * glo ≤ β * ghi := mul_le_mul_of_nonneg_left hglo_le_ghi hβ_nn
  have hden_glo : (0 : ℝ) < 1 - β * glo := by linarith
  have hden_β : (0 : ℝ) < 1 - β := by linarith
  have hM_U_nn : (0 : ℝ) ≤ M_U :=
    le_trans (abs_nonneg _) (hstage_bd 0 ⟨le_refl 0, zero_le_one⟩)
  have hK' : L_U / (1 - β * ghi) ≤ K := by
    simpa [StokeyLucas.bellmanLipConstant] using hK
  have hM' : M_U / (1 - β) ≤ M := by
    simpa [StokeyLucas.bellmanNormBound] using hM
  have hg' : g ≤ g_U / (1 - β * glo) := by
    simpa [StokeyLucas.bellmanLowerSlopeConstant] using hg
  have hK_nn : (0 : ℝ) ≤ K :=
    le_trans (div_nonneg hL_U_nn hden_ghi.le) hK'
  have hM_nn : (0 : ℝ) ≤ M :=
    le_trans (div_nonneg hM_U_nn hden_β.le) hM'
  have hK_marg : L_U + β * K * ghi ≤ K := by
    have h := (div_le_iff₀ hden_ghi).mp hK'
    nlinarith [h]
  have hM_marg : M_U + β * M ≤ M := by
    have h := (div_le_iff₀ hden_β).mp hM'
    nlinarith [h]
  have hg_marg : g ≤ g_U + β * g * glo := by
    have h := (le_div_iff₀ hden_glo).mp hg'
    nlinarith [h]
  -- ## The ordered-pair core: both one-sided bounds at once.
  have hpair : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), y₁.val ≤ y₂.val →
      |W y₂ - W y₁| ≤ K * (y₂.val - y₁.val) ∧
        g * (y₂.val - y₁.val) ≤ W y₂ - W y₁ := by
    intro y₁ y₂ hab
    have ha : y₁.val ∈ Icc (0 : ℝ) 1 := y₁.property
    have hb : y₂.val ∈ Icc (0 : ℝ) 1 := y₂.property
    have hd_nn : (0 : ℝ) ≤ y₂.val - y₁.val := by linarith
    obtain ⟨hlo, hhi⟩ := hchord ha hb hab
    have hFa : F y₁.val 1 ∈ Icc (0 : ℝ) 1 := hF_mem _ ha
    have hFb : F y₂.val 1 ∈ Icc (0 : ℝ) 1 := hF_mem _ hb
    have hglo_d : (0 : ℝ) ≤ glo * (y₂.val - y₁.val) := mul_nonneg hglo_nn hd_nn
    have hFord : F y₁.val 1 ≤ F y₂.val 1 := by linarith
    -- The clipped successors are the successors, and their gap is the chord gap.
    have hAval : (Sanctions.clipS' (F y₁.val 1)).val = F y₁.val 1 :=
      Sanctions.clipS'_val_eq_of_mem hFa
    have hBval : (Sanctions.clipS' (F y₂.val 1)).val = F y₂.val 1 :=
      Sanctions.clipS'_val_eq_of_mem hFb
    have hdistAB :
        dist (Sanctions.clipS' (F y₁.val 1)) (Sanctions.clipS' (F y₂.val 1))
          = F y₂.val 1 - F y₁.val 1 := by
      rw [Subtype.dist_eq, Real.dist_eq, hAval, hBval,
        abs_of_nonpos (by linarith : F y₁.val 1 - F y₂.val 1 ≤ 0)]
      ring
    have hABord :
        Sanctions.clipS' (F y₁.val 1) ≤ Sanctions.clipS' (F y₂.val 1) :=
      Sanctions.clipS'_mono hFord
    -- Carrier facts about `V`, transported to the state gap.
    have hVup :
        |V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1))|
          ≤ K * (F y₂.val 1 - F y₁.val 1) := by
      have h := hV.2.1 (Sanctions.clipS' (F y₁.val 1)) (Sanctions.clipS' (F y₂.val 1))
      rwa [hdistAB] at h
    have hVlo :
        g * (F y₂.val 1 - F y₁.val 1)
          ≤ V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1)) := by
      have h := hV.2.2 (Sanctions.clipS' (F y₁.val 1)) (Sanctions.clipS' (F y₂.val 1))
        (by rw [hAval]; exact hFa) (by rw [hBval]; exact hFb) hABord
      rwa [hdistAB] at h
    have hVabs := abs_le.mp hVup
    have hKghi : K * (F y₂.val 1 - F y₁.val 1) ≤ K * (ghi * (y₂.val - y₁.val)) :=
      mul_le_mul_of_nonneg_left hhi hK_nn
    have hgglo : g * (glo * (y₂.val - y₁.val)) ≤ g * (F y₂.val 1 - F y₁.val 1) :=
      mul_le_mul_of_nonneg_left hlo hg_nn
    -- Continuation term, both sides.
    have hDV_up :
        V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1))
          ≤ K * (ghi * (y₂.val - y₁.val)) := by linarith [hVabs.2, hKghi]
    have hDV_lo :
        -(K * (ghi * (y₂.val - y₁.val)))
          ≤ V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1)) := by
      linarith [hVabs.1, hKghi]
    have hDV_gain :
        g * (glo * (y₂.val - y₁.val))
          ≤ V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1)) := by
      linarith [hgglo, hVlo]
    have hβup :
        β * (V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1)))
          ≤ β * (K * (ghi * (y₂.val - y₁.val))) :=
      mul_le_mul_of_nonneg_left hDV_up hβ_nn
    have hβlo :
        β * (-(K * (ghi * (y₂.val - y₁.val))))
          ≤ β * (V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1))) :=
      mul_le_mul_of_nonneg_left hDV_lo hβ_nn
    have hβgain :
        β * (g * (glo * (y₂.val - y₁.val)))
          ≤ β * (V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1))) :=
      mul_le_mul_of_nonneg_left hDV_gain hβ_nn
    -- Stage term, both sides.
    have hsl := hstage_lip y₁.val ha y₂.val hb
    rw [abs_of_nonneg hd_nn] at hsl
    have hslabs := abs_le.mp hsl
    have hss := hstage_slope y₁.val ha y₂.val hb hab
    -- Scaled margins.
    have hmargK : (L_U + β * K * ghi) * (y₂.val - y₁.val) ≤ K * (y₂.val - y₁.val) :=
      mul_le_mul_of_nonneg_right hK_marg hd_nn
    have hmargg : g * (y₂.val - y₁.val) ≤ (g_U + β * g * glo) * (y₂.val - y₁.val) :=
      mul_le_mul_of_nonneg_right hg_marg hd_nn
    have hWdiff : W y₂ - W y₁
        = (stage y₂.val - stage y₁.val)
          + β * (V (Sanctions.clipS' (F y₂.val 1))
                  - V (Sanctions.clipS' (F y₁.val 1))) := by
      rw [himg y₁, himg y₂]; ring
    constructor
    · rw [hWdiff, abs_le]
      exact ⟨by linarith [hslabs.1, hβlo, hmargK], by linarith [hslabs.2, hβup, hmargK]⟩
    · rw [hWdiff]; linarith [hss, hβgain, hmargg]
  -- ## (a) norm, (b) Lipschitz, (c) lower slope.
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le hM_nn]
    intro y
    rw [himg y, Real.norm_eq_abs]
    have hVb : |V (Sanctions.clipS' (F y.val 1))| ≤ M := by
      have h1 := BoundedContinuousFunction.norm_coe_le_norm V
        (Sanctions.clipS' (F y.val 1))
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 hV.1
    have hβV : |β * V (Sanctions.clipS' (F y.val 1))| ≤ β * M := by
      rw [abs_mul, abs_of_nonneg hβ_nn]
      exact mul_le_mul_of_nonneg_left hVb hβ_nn
    have h1 := abs_le.mp (hstage_bd y.val y.property)
    have h2 := abs_le.mp hβV
    rw [abs_le]
    exact ⟨by linarith [h1.1, h2.1, hM_marg], by linarith [h1.2, h2.2, hM_marg]⟩
  · intro y₁ y₂
    rcases le_total y₁.val y₂.val with h | h
    · have hp := (hpair y₁ y₂ h).1
      rw [Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
      linarith [hp]
    · have hp := (hpair y₂ y₁ h).1
      rw [Subtype.dist_eq, Real.dist_eq,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₁.val - y₂.val), abs_sub_comm]
      linarith [hp]
  · intro y₁ y₂ _ _ hle
    have hval : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    have hp := (hpair y₁ y₂ hval).2
    rw [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    linarith [hp]

/-- **Leg (b) in isolation: the Lipschitz leg needs NO corner-section
invariance.** `hF_mem` is absent here; `clipS'` is 1-Lipschitz, so the upper
half of the band suffices even if the corner section leaves `[0,1]`.

General in `F`: a `K`-Lipschitz value has a `K`-Lipschitz corner-pinned Bellman
image whenever `K` clears the Stokey–Lucas Lipschitz closed form. As in CORE 2,
`glo ≤ ghi` is read off the band (`CornerStateChord.rates_le`; BG1.4,
2026-10-06) rather than assumed. -/
theorem valueLipschitz_bellman_chord
    {β glo ghi c₀ L_U K : ℝ}
    {stage : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hβ_nn : 0 ≤ β)
    (hglo_nn : 0 ≤ glo) (hβghi : β * ghi < 1)
    (hL_U_nn : 0 ≤ L_U)
    (hstage_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
        |stage y₂ - stage y₁| ≤ L_U * |y₂ - y₁|)
    (hchord : CornerStateChord F glo ghi)
    (hK : StokeyLucas.bellmanLipConstant β ghi L_U ≤ K)
    {V W : Val}
    (hVlip : ValueLipschitzWith V K)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
        W y = c₀ + stage y.val + β * V (Sanctions.clipS' (F y.val 1))) :
    ValueLipschitzWith W K := by
  have hglo_le_ghi : glo ≤ ghi := hchord.rates_le
  have hghi_nn : (0 : ℝ) ≤ ghi := le_trans hglo_nn hglo_le_ghi
  have hden_ghi : (0 : ℝ) < 1 - β * ghi := by linarith
  have hK' : L_U / (1 - β * ghi) ≤ K := by
    simpa [StokeyLucas.bellmanLipConstant] using hK
  have hK_nn : (0 : ℝ) ≤ K := le_trans (div_nonneg hL_U_nn hden_ghi.le) hK'
  have hK_marg : L_U + β * K * ghi ≤ K := by
    have h := (div_le_iff₀ hden_ghi).mp hK'
    nlinarith [h]
  have hpair : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), y₁.val ≤ y₂.val →
      |W y₂ - W y₁| ≤ K * (y₂.val - y₁.val) := by
    intro y₁ y₂ hab
    have ha : y₁.val ∈ Icc (0 : ℝ) 1 := y₁.property
    have hb : y₂.val ∈ Icc (0 : ℝ) 1 := y₂.property
    have hd_nn : (0 : ℝ) ≤ y₂.val - y₁.val := by linarith
    obtain ⟨hlo, hhi⟩ := hchord ha hb hab
    have hglo_d : (0 : ℝ) ≤ glo * (y₂.val - y₁.val) := mul_nonneg hglo_nn hd_nn
    have hdist :
        dist (Sanctions.clipS' (F y₁.val 1)) (Sanctions.clipS' (F y₂.val 1))
          ≤ ghi * (y₂.val - y₁.val) := by
      refine le_trans (Sanctions.clipS'_lipschitz_dist _ _) ?_
      rw [abs_of_nonpos (by linarith : F y₁.val 1 - F y₂.val 1 ≤ 0)]
      linarith
    have hV2 :
        |V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1))|
          ≤ K * (ghi * (y₂.val - y₁.val)) :=
      le_trans (hVlip (Sanctions.clipS' (F y₁.val 1)) (Sanctions.clipS' (F y₂.val 1)))
        (mul_le_mul_of_nonneg_left hdist hK_nn)
    have hVabs := abs_le.mp hV2
    have hβup :
        β * (V (Sanctions.clipS' (F y₂.val 1)) - V (Sanctions.clipS' (F y₁.val 1)))
          ≤ β * (K * (ghi * (y₂.val - y₁.val))) :=
      mul_le_mul_of_nonneg_left hVabs.2 hβ_nn
    have hβlo :
        β * (-(K * (ghi * (y₂.val - y₁.val))))
          ≤ β * (V (Sanctions.clipS' (F y₂.val 1))
                  - V (Sanctions.clipS' (F y₁.val 1))) :=
      mul_le_mul_of_nonneg_left hVabs.1 hβ_nn
    have hsl := hstage_lip y₁.val ha y₂.val hb
    rw [abs_of_nonneg hd_nn] at hsl
    have hslabs := abs_le.mp hsl
    have hmargK : (L_U + β * K * ghi) * (y₂.val - y₁.val) ≤ K * (y₂.val - y₁.val) :=
      mul_le_mul_of_nonneg_right hK_marg hd_nn
    have hWdiff : W y₂ - W y₁
        = (stage y₂.val - stage y₁.val)
          + β * (V (Sanctions.clipS' (F y₂.val 1))
                  - V (Sanctions.clipS' (F y₁.val 1))) := by
      rw [himg y₁, himg y₂]; ring
    rw [hWdiff, abs_le]
    exact ⟨by linarith [hslabs.1, hβlo, hmargK], by linarith [hslabs.2, hβup, hmargK]⟩
  intro y₁ y₂
  rcases le_total y₁.val y₂.val with h | h
  · have hp := hpair y₁ y₂ h
    rw [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    linarith [hp]
  · have hp := hpair y₂ y₁ h
    rw [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₁.val - y₂.val), abs_sub_comm]
    linarith [hp]

end Params
end AbstractGame
end Sanctions

#print axioms Sanctions.AbstractGame.Params.mem_valLipGainBall_bellman_chord
#print axioms Sanctions.AbstractGame.Params.valueLipschitz_bellman_chord
