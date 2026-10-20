/-
Sanctions/Examples/PlacableSenderBracket.lean

**The general-transition bracket in the Target's discount factor** (round AQ,
2026-09-23; doc 102 §2, on the user's word; on the abstract payoffs since round
AV, 2026-09-25, doc 104).

**The defiance side.** A chord economy certifies the forward-looking Target's
defiance by the loss-offset margin `c ≤ β_T·d_lo·g_T` (`targetArgmax_eq_zero`), a
sufficient condition. This file sharpens it. The Target's deviation from
defiance to a compliance `a` lowers the Sender's response by at most
`k_hi·a/μ`, because the Sender's dynamic objective is `μ`-strongly concave in
the sanction and a unit of compliance perturbs it with a cross rate at most
`k_hi` (S10u; `argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp`);
the pain saved is at most `c` per unit of that fall (T2), the continuation lost
at least `β_T·d_lo·g` per unit when the Target's value has lower state slope
`g`; and the compliance costs at least `ℓ_lo·a` (T4). So defiance is the strict
unique maximiser whenever

  `c − ℓ_lo·μ/k_hi < β_T·d_lo·g`      (`targetObj_strictAntiOn_of_sharp`).

Since `ℓ_lo > 0`, the weak margin `c ≤ β_T·d_lo·g_T` implies this strict
inequality at `g = g_T` (`sharp_of_lossOffset`); read at `ℓ_lo = 0` the inequality
is only a limiting mnemonic for the margin, strict where the margin is weak.

**Which slope.** The Target's value at the defiance profile lies in the
lower-slope cone with slope `g` whenever the state slope of the stage payoff,
the continuation through the lower state chord, and the pain term along a
monotone response balance:
`g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·L_resp/μ ≤ v_lo + n_lo·b`, with
`b = σ(0,0)` the sanction floor (`targetOp_mem_lowerSlopeCone`). Under the margin
the pain term vanishes and `g = g_T` works. Without it the response's state
Lipschitz rate `L_resp/μ` prices the pain term, and the effective slope
`g_eff = (v_lo + n_lo·b − c·L_resp/μ)/(1 − β_T(g_lo + d_lo·L_resp/μ))` works when
it lies below `g_T`; `gSharp = min g_T g_eff` always works (`gSharp_balance`).

**The relief side** (§5). At the Sender-only value the Target's zero level is
`L_α`-Lipschitz, `L_α = M_tot·L_resp/(k_lo·μ)`; the relief-branch Target value
along it is `K_T^rel`-Lipschitz, `K_T^rel = (v_hi + ℓ_hi·L_α)/(1 − β_T g_hi)`;
and under `ℓ_hi·M_tot < k_lo·(p_lo − β_T·d_hi·K_T^rel)` complying at the zero
level is the Target's unique optimum (`reliefEquilibriumTop`, which also reads
zero-sanction neutrality for the Sender's value). A second, different relief
inequality, with `K_T` in place of `K_T^rel` and the loop condition
`β_T·L_loop < 1`, rejects defiance at the defiance-profile values
(`defiance_not_maxOn_of_relief_side`). So the bracket has three certificates:
the sharp defiance side, relief existence (`K_T^rel`) and the rejection of
defiance (`K_T`). The sharp side is disjoint from the second relief side
(`bracket_sides_disjoint`) and from the existence side
(`bracket_existence_sides_disjoint`, in `PlacableSenderBracketSatellites.lean`);
the sharp side at `g_T` is inherited by a more patient Target, the relief side
by a less patient one, and the second relief side too under the loop condition;
and under sixteen tightness equalities (`collapse_sides`) all three read one
threshold. The collapse is a conditional equivalence, not a characterization of
when the window closes. The sharp side's properties are proved at `g_T`, which
is a certified slope under the loss-offset margin; below the margin the
certified slope is `gSharp`, and every defiance certificate implies the side at
`g_T` (`sharp_gT_of_sharp_of_balance`, in the satellites).

**Rule 3.** No field. The hypotheses `hmono` (monotone response at the
Sender's value), `hγ : β_T·L_loop < 1` and `hvL : c·L_resp/μ < v_lo + n_lo·b` are
strict inequalities among existing constants; zero-sanction neutrality is a
hypothesis of the relief equilibrium only (sign-off M2). **Rule 22.** General in
`F` through the chords and the moduli only. **Rule 9.** Witnessed in
`PlacableSenderBracketWitnesses.lean`, at the affine member and off the affine
law.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation round BG-3 (2026-10-06; items BG3.4, BG3.5). Existence needs only a weak
argmax, so the existence statements take the closed sides: the sharp side with `≤` in
`zero_isMaxOn_joint_of_sharp`, `equilibriumTop_sharp` and `equilibriumTop_gSharp`
(through `targetObj_antitoneOn_of_sharp_le`), and the relief side with `≤` in
`zeroLevel_isMaxOn_rel` (through `jointRel_le_of_lt`). The strict sides stay where
uniqueness is claimed (`targetObj_strictAntiOn_of_sharp`, `targetArgmax_eq_zero_of_sharp`,
`zeroLevel_argmax_unique_rel`, `reliefEquilibriumTop`). The `g_eff` route reads only its
own denominator, `β_T(g_lo + d_lo L_resp/μ) < 1`, in place of `β_T·L_loop^sharp < 1`
(`gSharp_balance_lo`). `collapse_Lresp` is affine by hypothesis: a zero response slope
forces the affine law (`ChordEconomyRelief.F_eq_affineF_of_Lresp_eq_zero`).

Renovation item BH3.11 (2026-10-06). `VTdef_lipschitz` is stated on the relief extension
`ChordEconomyRelief` (until then on `ChordEconomyCs`, whose sanction-section semiconvexity
it never read) and follows from `targetFix_lipschitz`. The two halves of the continuation
bracket at the defiance-profile value carry only what each reads: the upper half
`β_T·K_T·d_hi·(s₂ − s₁)` needs `β_T·γ_T < 1` alone (`VTdef_continuation_upper`), the lower
half `β_T·g·d_lo·(s₂ − s₁)` a monotone response, a slope `g ≥ 0` and the balance
(`VTdef_continuation_lower`), with corollaries at `g_T` under the margin and at `gSharp`
without it.
-/
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderTargetLipschitz
import Sanctions.Theory.Equilibrium.CertifiedEquilibria

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. Instruments at any carrier value (Rule 5 generalisations) -/


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The state-perturbation of the Sender's objective is Lipschitz in the
sanction**, with constant `L_resp·|x − y|`, at every two-sided carrier value and
every compliance in `[0,1]` (the `VSstar`, `a = 0` form is
`senderObj_state_perturbation_lipschitz`). -/
theorem senderObj_state_perturbation_lipschitz_carrier {V : Val} (hV : V ∈ E.carrierS2)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) :
    ∀ u ∈ Sanctions.I, ∀ w ∈ Sanctions.I,
      |(E.senderObj V y a u - E.senderObj V x a u)
          - (E.senderObj V y a w - E.senderObj V x a w)|
        ≤ (E.Lresp * |x - y|) * |u - w| := by
  intro u hu w hw
  have hcross := abs_crossDiff_le_of_twoSided
    (v := fun z => V (Sanctions.clipS' z)) (F := E.F)
    E.hSigV0 E.SigC_nonneg E.hglo0 E.hdlo0.le
    (E.clip_lip hV.1.1) hV.1.2 hV.2 E.F_maps
    E.hbandAll E.hSlo E.hShi E.hFmix hx hy hw hu
  simp only at hcross
  have hid : (E.senderObj V y a u - E.senderObj V x a u)
        - (E.senderObj V y a w - E.senderObj V x a w)
      = ((E.U_S y a u - E.U_S y a w) - (E.U_S x a u - E.U_S x a w))
        + E.β_S * ((V (Sanctions.clipS' (E.F y u)) - V (Sanctions.clipS' (E.F y w)))
          - (V (Sanctions.clipS' (E.F x u)) - V (Sanctions.clipS' (E.F x w)))) := by
    simp only [senderObj]; ring
  rw [hid]
  have hstage := E.hUS_crossHi a ha x hx y hy w hw u hu
  have h1 := abs_add_le ((E.U_S y a u - E.U_S y a w) - (E.U_S x a u - E.U_S x a w))
    (E.β_S * ((V (Sanctions.clipS' (E.F y u)) - V (Sanctions.clipS' (E.F y w)))
      - (V (Sanctions.clipS' (E.F x u)) - V (Sanctions.clipS' (E.F x w)))))
  have h3 := mul_le_mul_of_nonneg_left hcross E.hβS0.le
  rw [abs_mul E.β_S, abs_of_nonneg E.hβS0.le] at h1
  have h4 : (E.Lresp * |x - y|) * |u - w|
      = E.rhi * (|y - x| * |u - w|)
        + E.β_S * ((max E.SigV E.SigC * E.ghi * E.dhi + (E.KS + 2 * max E.SigV E.SigC) * E.Mmix)
          * |y - x| * |u - w|) := by
    unfold Lresp plLresp
    rw [abs_sub_comm x y]
    ring
  rw [h4]
  linarith [h1, hstage, h3]

/-- **The response is `L_resp/μ`-Lipschitz in the state at every two-sided
carrier value and every compliance in `[0,1]`** (the sharp stability lemma; the
`VSstar`, `a = 0` form is `responsePath_lipschitz_sharp`). -/
theorem response_dist_le_state {V : Val} (hV : V ∈ E.carrierS2)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) :
    |E.response V x a - E.response V y a| ≤ (E.Lresp * |x - y|) / E.mu := by
  have hf := E.senderObj_semiconcave_neg_mu hV.1 hx a
  have hpert := E.senderObj_state_perturbation_lipschitz_carrier hV hx hy ha
  exact argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp (convex_Icc 0 1) E.mu_pos
    (mul_nonneg E.Lresp_nonneg (abs_nonneg _)) hf hpert
    (E.response_mem _ _ _) (E.response_mem _ _ _)
    (E.response_isMaxOn _ _ _) (E.response_isMaxOn _ _ _)

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)


/-- **The relief rate is at most `k_hi/μ`**: between two compliance levels the
response falls by at most `k_hi·Δa/μ`, at every carrier value. A unit of
compliance perturbs a `μ`-strongly concave objective with cross rate at most
`k_hi` (S10u). General in `F`. Renovation item BJ2.2 (2026-10-07): `k_hi` is any
placation ceiling `hPC` (`PlacationCeiling`), no longer a field of the base class. -/
theorem response_sub_le_of_le {khi : ℝ} (hPC : E.PlacationCeiling khi) {V : Val}
    (hV : V ∈ E.carrierS) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {a a' : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ha' : a' ∈ Icc (0 : ℝ) 1)
    (haa' : a ≤ a') :
    E.response V x a - E.response V x a' ≤ khi * (a' - a) / E.mu := by
  have hf := E.senderObj_semiconcave_neg_mu hV hx a
  have hpert : ∀ u ∈ Sanctions.I, ∀ w ∈ Sanctions.I,
      |(E.senderObj V x a' u - E.senderObj V x a u)
        - (E.senderObj V x a' w - E.senderObj V x a w)| ≤ (khi * (a' - a)) * |u - w| := by
    intro u hu w hw
    have hid : (E.senderObj V x a' u - E.senderObj V x a u)
        - (E.senderObj V x a' w - E.senderObj V x a w)
        = (E.U_S x a' u - E.U_S x a' w) - (E.U_S x a u - E.U_S x a w) := by
      simp only [senderObj]; ring
    rw [hid]
    have h := hPC x hx a ha a' ha' w hw u hu haa'
    calc |(E.U_S x a' u - E.U_S x a' w) - (E.U_S x a u - E.U_S x a w)|
        ≤ khi * ((a' - a) * |u - w|) := h
      _ = (khi * (a' - a)) * |u - w| := by ring
  have h := argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp (convex_Icc 0 1)
    E.mu_pos (mul_nonneg (E.khi_pos hPC).le (by linarith)) hf hpert
    (E.response_mem _ _ _) (E.response_mem _ _ _)
    (E.response_isMaxOn _ _ _) (E.response_isMaxOn _ _ _)
  exact (le_abs_self _).trans h

/-- Lower slope through the clip, at any slope `g` (the carrier form is
`clipT_lowerSlope`). -/
theorem clip_lowerSlope_of (_E : ChordEconomy) {V : Val} {g : ℝ}
    (hV : Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      g * (z₂ - z₁) ≤ V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) := by
  intro z₁ hz₁ z₂ hz₂ hle
  have h := hV (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₁]; exact hz₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₂]; exact hz₂)
    (Sanctions.clipS'_mono hle)
  have hdist : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = z₂ - z₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hz₁,
      Sanctions.clipS'_val_eq_of_mem hz₂, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdist] at h
  exact h



end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- The Target's stage payoff is `ℓ_hi`-Lipschitz in compliance (T4 with its
upper partner). -/
theorem UT_compliance_lip {x a₁ a₂ s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha₁ : a₁ ∈ Icc (0 : ℝ) 1)
    (ha₂ : a₂ ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    |E.U_T x a₂ s - E.U_T x a₁ s| ≤ E.ℓhi * |a₂ - a₁| := by
  rcases le_total a₁ a₂ with h | h
  · have h1 := E.hUT_costLo x hx s hs a₁ ha₁ a₂ ha₂ h
    have h2 := E.hUT_costHi x hx s hs a₁ ha₁ a₂ ha₂ h
    have h3 := mul_nonneg E.hℓlo.le (sub_nonneg.mpr h)
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_le]
    constructor <;> linarith
  · have h1 := E.hUT_costLo x hx s hs a₂ ha₂ a₁ ha₁ h
    have h2 := E.hUT_costHi x hx s hs a₂ ha₂ a₁ ha₁ h
    have h3 := mul_nonneg E.hℓlo.le (sub_nonneg.mpr h)
    rw [abs_sub_comm a₂ a₁, abs_of_nonneg (sub_nonneg.mpr h), abs_le]
    constructor <;> linarith

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 2. The sharp defiance side -/

/-- **Defiance is the strict unique Target argmax under the sharp side**
`c − ℓ_lo·μ/k_hi < β_T·d_lo·g`, at any Target value of lower state slope `g ≥ 0`
and any Sender carrier value. The margin `c ≤ β_T d_lo g_T` implies the sharp
side at `g = g_T`, since `ℓ_lo > 0` (`sharp_of_lossOffset`; the margin route is
`targetObj_strictAntiOn`). General in `F`. A pinned headline; renovation item BJ2.2
(2026-10-07, approved re-pin): `k_hi` is any placation ceiling `hPC`
(`PlacationCeiling`), no longer a field of the base class. -/
theorem targetObj_strictAntiOn_of_sharp {khi : ℝ} (hPC : E.PlacationCeiling khi) {g : ℝ}
    (hg : 0 ≤ g)
    (hsharp : E.c - E.ℓlo * E.mu / khi < E.β_T * E.dlo * g)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    StrictAntiOn (fun a => E.toParams.joint_T_integrand V_T V_S x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hlt
  show E.toParams.joint_T_integrand V_T V_S x a₂ < E.toParams.joint_T_integrand V_T V_S x a₁
  rw [joint_T_integrand_eq, joint_T_integrand_eq]
  have hρ : E.response V_S x a₂ ≤ E.response V_S x a₁ :=
    E.response_antitoneOn_a hV_S hx ha₁ ha₂ hlt.le
  have hρ₁ := E.response_mem V_S x a₁
  have hρ₂ := E.response_mem V_S x a₂
  have hΔ : E.response V_S x a₁ - E.response V_S x a₂ ≤ khi * (a₂ - a₁) / E.mu :=
    E.response_sub_le_of_le hPC hV_S hx ha₁ ha₂ hlt.le
  have hz : E.F x (E.response V_S x a₂) ≤ E.F x (E.response V_S x a₁) := E.F_mono_s x hρ
  have hchord : E.dlo * (E.response V_S x a₁ - E.response V_S x a₂)
      ≤ E.F x (E.response V_S x a₁) - E.F x (E.response V_S x a₂) := E.hSlo hx hρ₂ hρ₁ hρ
  have hslope := E.clip_lowerSlope_of hV_T _ (E.F_mem _ _ hx hρ₂) _ (E.F_mem _ _ hx hρ₁) hz
  have hA : E.β_T * (V_T (Sanctions.clipS' (E.F x (E.response V_S x a₂)))
        - V_T (Sanctions.clipS' (E.F x (E.response V_S x a₁))))
      ≤ -(E.β_T * E.dlo * g) * (E.response V_S x a₁ - E.response V_S x a₂) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg E.hβT0.le hg)
    have h2 := mul_le_mul_of_nonneg_left hslope E.hβT0.le
    nlinarith [h1, h2]
  -- the stage: pain at most `c` per unit of sanction, cost at least `ℓ_lo` per unit
  have hU := E.UT_sub_le hx ha₁ ha₂ hρ₁ hρ₂ hlt.le hρ
  -- the pain term, priced by the relief rate
  set θ := E.c - E.β_T * E.dlo * g with hθ
  have hμ := E.mu_pos
  have hk := (E.khi_pos hPC)
  have hθk : θ * khi < E.ℓlo * E.mu := by
    have h1 : E.c - E.ℓlo * E.mu / khi < E.β_T * E.dlo * g := hsharp
    have h2 : E.ℓlo * E.mu / khi * khi = E.ℓlo * E.mu := div_mul_cancel₀ _ hk.ne'
    nlinarith [h1, h2]
  have hB : (E.response V_S x a₁ - E.response V_S x a₂) * θ < E.ℓlo * (a₂ - a₁) := by
    rcases le_or_gt θ 0 with hθ0 | hθ0
    · have : (E.response V_S x a₁ - E.response V_S x a₂) * θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) hθ0
      have : 0 < E.ℓlo * (a₂ - a₁) := mul_pos E.hℓlo (by linarith)
      linarith
    · have h1 : (E.response V_S x a₁ - E.response V_S x a₂) * θ
          ≤ khi * (a₂ - a₁) / E.mu * θ := mul_le_mul_of_nonneg_right hΔ hθ0.le
      have h2 : khi * (a₂ - a₁) / E.mu * θ < E.ℓlo * (a₂ - a₁) := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hμ]
        have := mul_lt_mul_of_pos_right hθk (show 0 < a₂ - a₁ by linarith)
        nlinarith [this]
      linarith
  change E.U_T x a₂ (E.response V_S x a₂)
      + E.β_T * V_T (Sanctions.clipS' (E.F x (E.response V_S x a₂)))
    < E.U_T x a₁ (E.response V_S x a₁)
      + E.β_T * V_T (Sanctions.clipS' (E.F x (E.response V_S x a₁)))
  nlinarith [hA, hB, hU]

/-- **Complying never pays under the weak sharp side** (renovation item BG3.5,
2026-10-06). Under `c − ℓ_lo·μ/k_hi ≤ β_T·d_lo·g`, at any Target value of lower state
slope `g ≥ 0` and any Sender carrier value, the Target's objective is nonincreasing in
compliance. In words: when the sanction pain a unit of compliance saves, net of the
continuation value the lower state costs, is at most the direct cost of that unit, the
Target gains nothing by complying. The strict form `targetObj_strictAntiOn_of_sharp`
makes defiance the unique optimum; this weak form, with the strict inequality relaxed to
`≤`, is what existence needs. General in `F`. `k_hi` is any placation ceiling `hPC`
(renovation item BJ2.2, 2026-10-07). -/
theorem targetObj_antitoneOn_of_sharp_le {khi : ℝ} (hPC : E.PlacationCeiling khi) {g : ℝ}
    (hg : 0 ≤ g)
    (hsharp : E.c - E.ℓlo * E.mu / khi ≤ E.β_T * E.dlo * g)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    AntitoneOn (fun a => E.toParams.joint_T_integrand V_T V_S x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hle
  change E.toParams.joint_T_integrand V_T V_S x a₂
    ≤ E.toParams.joint_T_integrand V_T V_S x a₁
  rw [joint_T_integrand_eq, joint_T_integrand_eq]
  have hρ : E.response V_S x a₂ ≤ E.response V_S x a₁ :=
    E.response_antitoneOn_a hV_S hx ha₁ ha₂ hle
  have hρ₁ := E.response_mem V_S x a₁
  have hρ₂ := E.response_mem V_S x a₂
  have hΔ : E.response V_S x a₁ - E.response V_S x a₂ ≤ khi * (a₂ - a₁) / E.mu :=
    E.response_sub_le_of_le hPC hV_S hx ha₁ ha₂ hle
  have hz : E.F x (E.response V_S x a₂) ≤ E.F x (E.response V_S x a₁) := E.F_mono_s x hρ
  have hchord : E.dlo * (E.response V_S x a₁ - E.response V_S x a₂)
      ≤ E.F x (E.response V_S x a₁) - E.F x (E.response V_S x a₂) := E.hSlo hx hρ₂ hρ₁ hρ
  have hslope := E.clip_lowerSlope_of hV_T _ (E.F_mem _ _ hx hρ₂) _ (E.F_mem _ _ hx hρ₁) hz
  have hA : E.β_T * (V_T (Sanctions.clipS' (E.F x (E.response V_S x a₂)))
        - V_T (Sanctions.clipS' (E.F x (E.response V_S x a₁))))
      ≤ -(E.β_T * E.dlo * g) * (E.response V_S x a₁ - E.response V_S x a₂) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg E.hβT0.le hg)
    have h2 := mul_le_mul_of_nonneg_left hslope E.hβT0.le
    nlinarith [h1, h2]
  -- the stage: pain at most `c` per unit of sanction, cost at least `ℓ_lo` per unit
  have hU := E.UT_sub_le hx ha₁ ha₂ hρ₁ hρ₂ hle hρ
  -- the pain term, priced by the relief rate
  set θ := E.c - E.β_T * E.dlo * g with hθ
  have hμ := E.mu_pos
  have hk := (E.khi_pos hPC)
  have hθk : θ * khi ≤ E.ℓlo * E.mu := by
    have h1 : E.c - E.ℓlo * E.mu / khi ≤ E.β_T * E.dlo * g := hsharp
    have h2 : E.ℓlo * E.mu / khi * khi = E.ℓlo * E.mu := div_mul_cancel₀ _ hk.ne'
    nlinarith [h1, h2]
  have hB : (E.response V_S x a₁ - E.response V_S x a₂) * θ ≤ E.ℓlo * (a₂ - a₁) := by
    rcases le_or_gt θ 0 with hθ0 | hθ0
    · have : (E.response V_S x a₁ - E.response V_S x a₂) * θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) hθ0
      have : 0 ≤ E.ℓlo * (a₂ - a₁) := mul_nonneg E.hℓlo.le (by linarith)
      linarith
    · have h1 : (E.response V_S x a₁ - E.response V_S x a₂) * θ
          ≤ khi * (a₂ - a₁) / E.mu * θ := mul_le_mul_of_nonneg_right hΔ hθ0.le
      have h2 : khi * (a₂ - a₁) / E.mu * θ ≤ E.ℓlo * (a₂ - a₁) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
        have := mul_le_mul_of_nonneg_right hθk (show 0 ≤ a₂ - a₁ by linarith)
        nlinarith [this]
      linarith
  change E.U_T x a₂ (E.response V_S x a₂)
      + E.β_T * V_T (Sanctions.clipS' (E.F x (E.response V_S x a₂)))
    ≤ E.U_T x a₁ (E.response V_S x a₁)
      + E.β_T * V_T (Sanctions.clipS' (E.F x (E.response V_S x a₁)))
  nlinarith [hA, hB, hU]

/-- **Defiance is a Target argmax under the weak sharp side**
`c − ℓ_lo·μ/k_hi ≤ β_T·d_lo·g` (renovation item BG3.5, 2026-10-06; the side was strict
until then). Existence of an optimum needs only this weak argmax; the strict side is kept
where uniqueness is claimed (`targetArgmax_eq_zero_of_sharp`). General in `F`. `k_hi` is any
placation ceiling `hPC` (renovation item BJ2.2, 2026-10-07). -/
theorem zero_isMaxOn_joint_of_sharp {khi : ℝ} (hPC : E.PlacationCeiling khi) {g : ℝ} (hg : 0 ≤ g)
    (hsharp : E.c - E.ℓlo * E.mu / khi ≤ E.β_T * E.dlo * g)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.toParams.joint_T_integrand V_T V_S x a) Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  exact E.targetObj_antitoneOn_of_sharp_le hPC hg hsharp hV_T hV_S hx
    ⟨le_refl 0, zero_le_one⟩ ha ha.1

/-- Every joint Target maximiser is full defiance, under the sharp side. General in `F`.
`k_hi` is any placation ceiling `hPC` (renovation item BJ2.2, 2026-10-07). -/
theorem targetArgmax_eq_zero_of_sharp {khi : ℝ} (hPC : E.PlacationCeiling khi) {g : ℝ} (hg : 0 ≤ g)
    (hsharp : E.c - E.ℓlo * E.mu / khi < E.β_T * E.dlo * g)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.toParams.joint_T_integrand V_T V_S x b) Sanctions.I a) :
    a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hne)
  have h1 := E.targetObj_strictAntiOn_of_sharp hPC hg hsharp hV_T hV_S hx
    ⟨le_refl 0, zero_le_one⟩ ha hpos
  have h2 := hmax (show (0:ℝ) ∈ Sanctions.I from ⟨le_refl 0, zero_le_one⟩)
  exact absurd h2 (not_le.mpr h1)

/-- The margin implies the sharp side: since `ℓ_lo > 0`, the weak margin
`c ≤ β_T d_lo g_T` gives the strict `c − ℓ_lo μ/k_hi < β_T d_lo g_T`, at any placation
ceiling `k_hi` (renovation item BJ2.2, 2026-10-07: the hypothesis `hPC`, read only for
`k_hi > 0`). General in `F`. -/
theorem sharp_of_lossOffset {khi : ℝ} (hPC : E.PlacationCeiling khi) (hTM : E.LossOffset) :
    E.c - E.ℓlo * E.mu / khi < E.β_T * E.dlo * E.gT := by
  have h : E.c ≤ E.β_T * E.dlo * E.gT := hTM
  have : 0 < E.ℓlo * E.mu / khi := div_pos (mul_pos E.hℓlo E.mu_pos) (E.khi_pos hPC)
  linarith

/-! ## 3. The Target's value at the defiance profile, at a general slope -/


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The Target operator preserves the lower-slope cone at slope `g`** at a
two-sided carrier Sender value with a monotone response, when the stage state
slope at the floor, the continuation through the lower chords and the pain term
along the response balance:
`g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·L_resp/μ ≤ v_lo + n_lo·b`. Under the
margin at `g = g_T` the pain term is absent and this is the carrier invariance
(`targetOp_mem_of_monotone`); off the margin the response's state Lipschitz
rate `L_resp/μ` prices it. -/
theorem targetOp_mem_lowerSlopeCone {V_S : Val} (hV_S : V_S ∈ E.carrierS2)
    (hmono : MonotoneOn (E.responsePath V_S) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g) :
    Params.LowerSlopeOnValueOn (E.targetOp hV_S.1 V_T) (Icc (0 : ℝ) 1) g := by
  have hβ : (0:ℝ) ≤ E.β_T := E.hβT0.le
  intro y₁ y₂ hy₁ hy₂ hle
  rw [targetOp_apply, targetOp_apply]
  have hyle : y₁.val ≤ y₂.val := hle
  have hd : dist y₁ y₂ = y₂.val - y₁.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hd]
  have hρ : E.responsePath V_S y₁.val ≤ E.responsePath V_S y₂.val := hmono hy₁ hy₂ hyle
  have hρ₁ := E.responsePath_mem V_S y₁.val
  have hρ₂ := E.responsePath_mem V_S y₂.val
  have hz₁ : E.F y₁.val (E.responsePath V_S y₁.val) ≤ E.F y₁.val (E.responsePath V_S y₂.val) :=
    E.F_mono_s _ hρ
  have hz₂ : E.F y₁.val (E.responsePath V_S y₂.val) ≤ E.F y₂.val (E.responsePath V_S y₂.val) :=
    E.F_mono_x _ hyle
  have hband := (E.hbandAll _ hρ₂) y₁.val hy₁ y₂.val hy₂ hyle
  have hchord := E.hSlo hy₁ hρ₁ hρ₂ hρ
  have hslope := E.clip_lowerSlope_of hV_T _ (E.F_mem _ _ hy₁ hρ₁) _ (E.F_mem _ _ hy₂ hρ₂)
    (hz₁.trans hz₂)
  have hsucc : E.glo * (y₂.val - y₁.val)
        + E.dlo * (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val)
      ≤ E.F y₂.val (E.responsePath V_S y₂.val) - E.F y₁.val (E.responsePath V_S y₁.val) := by
    linarith [hband.1, hchord]
  have hA : E.β_T * g * (E.glo * (y₂.val - y₁.val)
        + E.dlo * (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val))
      ≤ E.β_T * (V_T (Sanctions.clipS' (E.F y₂.val (E.responsePath V_S y₂.val)))
        - V_T (Sanctions.clipS' (E.F y₁.val (E.responsePath V_S y₁.val)))) := by
    have h1 := mul_le_mul_of_nonneg_left hsucc (mul_nonneg hβ hg)
    have h2 := mul_le_mul_of_nonneg_left hslope hβ
    nlinarith [h1, h2]
  -- the stage: the state rate `v_lo + n_lo·ρ₁` at the lower sanction, then the pain `c`
  have hUst := E.UT_state_chord_ge hy₁ hy₂ zero_mem_I hρ₁ hρ₂ hyle hρ
  have hE : E.sfloor * (E.nlo * (y₂.val - y₁.val))
      ≤ E.responsePath V_S y₁.val * (E.nlo * (y₂.val - y₁.val)) :=
    mul_le_mul_of_nonneg_right (E.responsePath_ge_sfloor hV_S.1 hy₁)
      (mul_nonneg E.hnlo (by linarith))
  -- the pain term along the response, priced by the state Lipschitz rate
  have hLip : E.responsePath V_S y₂.val - E.responsePath V_S y₁.val
      ≤ E.Lresp / E.mu * (y₂.val - y₁.val) := by
    have h := E.response_dist_le_state hV_S hy₂ hy₁ zero_mem_I
    have h' : E.responsePath V_S y₂.val - E.responsePath V_S y₁.val
        ≤ (E.Lresp * |y₂.val - y₁.val|) / E.mu := (le_abs_self _).trans h
    rw [abs_of_nonneg (by linarith)] at h'
    have : (E.Lresp * (y₂.val - y₁.val)) / E.mu = E.Lresp / E.mu * (y₂.val - y₁.val) := by ring
    linarith [h', this]
  have hC : (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val) * (E.c - E.β_T * E.dlo * g)
      ≤ max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu) * (y₂.val - y₁.val) := by
    rcases le_or_gt (E.c - E.β_T * E.dlo * g) 0 with hθ0 | hθ0
    · rw [max_eq_left hθ0]
      have : (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val)
          * (E.c - E.β_T * E.dlo * g) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) hθ0
      linarith
    · rw [max_eq_right hθ0.le]
      have := mul_le_mul_of_nonneg_right hLip hθ0.le
      linarith [this]
  have hginv' := mul_le_mul_of_nonneg_right hginv (show 0 ≤ y₂.val - y₁.val by linarith)
  change g * (y₂.val - y₁.val)
    ≤ (E.U_T y₂.val 0 (E.responsePath V_S y₂.val)
        + E.β_T * V_T (Sanctions.clipS' (E.F y₂.val (E.responsePath V_S y₂.val))))
      - (E.U_T y₁.val 0 (E.responsePath V_S y₁.val)
        + E.β_T * V_T (Sanctions.clipS' (E.F y₁.val (E.responsePath V_S y₁.val))))
  nlinarith [hA, hUst, hE, hC, hginv']

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)


/-- The cone at slope `g` is nonempty (the affine value `g·y`). -/
theorem lowerSlopeCone_nonempty (_E : ChordEconomy) (g : ℝ) :
    ({V : Val | Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g} : Set Val).Nonempty :=
  ⟨Params.slopeBCF g, Params.slopeBCF_mem_cone g⟩

/-- **The Target's value at the defiance profile**, the fixed point of the
Target operator at the Sender's constructed value on the whole value space (a
contraction, `targetOp_contracting`); equal to the carrier-constructed `VTstar`
whenever the latter exists (`VTdef_eq_VTstar`). -/
def VTdef : Val := (E.targetOp_contracting E.VSstar_mem).fixedPoint

theorem VTdef_fix : E.targetOp E.VSstar_mem E.VTdef = E.VTdef :=
  (E.targetOp_contracting E.VSstar_mem).fixedPoint_isFixedPt

theorem VTdef_eq_VTstar (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    E.VTdef = E.VTstar hTM hmono :=
  ((E.targetOp_contracting E.VSstar_mem).fixedPoint_unique (E.VTstar_fix hTM hmono)).symm


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The defiance-profile value has lower slope `g`** under the balance
inequality and a monotone response (Stokey–Lucas Corollary 1 to Theorem 3.2:
the cone is closed, nonempty and invariant). -/
theorem VTdef_lowerSlope (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor) :
    Params.LowerSlopeOnValueOn E.VTdef (Icc (0 : ℝ) 1) g := by
  have hcontr := E.targetOp_contracting E.VSstar_mem
  obtain ⟨W, hW, hWmem⟩ := StokeyLucas.fixedPoint_mem_of_mapsTo hcontr.1 _ hcontr.2
    {V : Val | Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g}
    (Params.lowerSlopeOnValueOn_isClosed _ _) (E.lowerSlopeCone_nonempty g)
    (fun V hV => E.targetOp_mem_lowerSlopeCone E.VSstar_mem2 hmono hg hginv hV)
  have h1 : W = hcontr.fixedPoint := hcontr.fixedPoint_unique hW
  show Params.LowerSlopeOnValueOn hcontr.fixedPoint (Icc (0 : ℝ) 1) g
  rw [← h1]
  exact hWmem


/-- **The composed equilibrium under the sharp defiance side**: full defiance
is a Target optimum at the values `(VTdef, VSstar)` whenever
`c − ℓ_lo μ/k_hi ≤ β_T d_lo g` for a slope `g` the defiance-profile value
carries. The margin route (`equilibriumTop`) sits at `g = g_T`, where the margin
implies the sharp side (`sharp_of_lossOffset`). Renovation item BG3.5 (2026-10-06): the
side is weak here, since existence needs only a weak argmax; under the strict side full
defiance is the Target's unique optimum (`targetArgmax_eq_zero_of_sharp`). General in
`F`. -/
def equilibriumTop_sharp (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor)
    (hsharp : E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * g) :
    E.toParams.FeedbackStackelbergEquilibriumTop where
  V_T := E.VTdef
  V_S := E.VSstar
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_refl 0, zero_le_one⟩
  V_S_fix := E.VSstar_fix.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest
        ((fun a => E.toParams.joint_T_top_integrand E.VTdef E.VSstar y.val a) '' Sanctions.I)
        (E.toParams.joint_T_top_integrand E.VTdef E.VSstar y.val 0) := by
      refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.joint_T_top_integrand_eq E.VSstar_mem _ y.property,
        E.joint_T_top_integrand_eq E.VSstar_mem _ y.property]
      exact E.zero_isMaxOn_joint_of_sharp E.placationCeiling hg hsharp
        (E.VTdef_lowerSlope hmono hg hginv) E.VSstar_mem y.property ha
    rw [hgt.csSup_eq, E.joint_T_top_integrand_eq E.VSstar_mem _ y.property,
      E.joint_T_integrand_eq]
    have h := congrArg (fun V : Val => V y) E.VTdef_fix
    simp only at h
    rw [targetOp_apply] at h
    exact h.symm
  α_opt_top := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    rw [E.joint_T_top_integrand_eq E.VSstar_mem _ hx,
      E.joint_T_top_integrand_eq E.VSstar_mem _ hx]
    exact E.zero_isMaxOn_joint_of_sharp E.placationCeiling hg hsharp
      (E.VTdef_lowerSlope hmono hg hginv) E.VSstar_mem hx ha

end ChordEconomyRelief

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-! ## 4. The slopes that satisfy the balance

The balance reads the response Lipschitz constant `L_resp`, which reads the two-sided
curvature data, so since renovation item BJ3.1 (2026-10-07) the slopes and loop rates
below are stated on `ChordEconomyTwoSided` (until then on `ChordEconomy`, otherwise
unchanged). General in `F`. -/

/-- Under the margin, `g_T` satisfies the balance (the pain term vanishes). -/
theorem gT_balance (hTM : E.LossOffset) :
    E.gT * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * E.gT) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor := by
  have h : E.c ≤ E.β_T * E.dlo * E.gT := hTM
  rw [max_eq_left (by linarith), zero_mul, add_zero, E.gT_mul]

/-- The loop rate at the lower chords, `g_lo + d_lo·L_resp/μ`; at most the
sharp loop constant `L_loop = g_hi + d_hi·L_resp/μ`. -/
def LloopLo : ℝ := E.glo + E.dlo * (E.Lresp / E.mu)


end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

theorem LloopLo_le_LloopSharp : E.LloopLo ≤ E.LloopSharp := by
  unfold LloopLo LloopSharp
  have h1 := E.hglo_ghi
  have h2 := mul_le_mul_of_nonneg_right E.hdlo_dhi
    (div_nonneg E.Lresp_nonneg E.mu_pos.le)
  linarith

theorem one_sub_βT_LloopLo_pos (hγ : E.β_T * E.LloopSharp < 1) :
    0 < 1 - E.β_T * E.LloopLo := by
  have := mul_le_mul_of_nonneg_left E.LloopLo_le_LloopSharp E.hβT0.le
  linarith

end ChordEconomyRelief

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)


/-- **The effective slope off the margin**,
`(v_lo + n_lo·b − c·L_resp/μ)/(1 − β_T(g_lo + d_lo L_resp/μ))`. On the two-sided
extension since renovation item BJ3.1 (2026-10-07). -/
def gEff : ℝ :=
  (E.vlo + E.nlo * E.sfloor - E.c * (E.Lresp / E.mu)) / (1 - E.β_T * E.LloopLo)


end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **`g_eff` is positive** under `hvL` and the lower loop condition
`β_T(g_lo + d_lo L_resp/μ) < 1`, which says exactly that its denominator is positive
(renovation item BG3.5(c), 2026-10-06; until then the stronger `β_T·L_loop^sharp < 1`,
with the upper chords). General in `F`. -/
theorem gEff_pos (hγ : E.β_T * E.LloopLo < 1)
    (hvL : E.c * (E.Lresp / E.mu) < E.vlo + E.nlo * E.sfloor) : 0 < E.gEff :=
  div_pos (by linarith) (sub_pos.mpr hγ)

/-- `g_eff` solves the balance with equality when its pain term is nonnegative. The only
condition is that its denominator `1 − β_T(g_lo + d_lo L_resp/μ)` is positive (BG3.5(c),
2026-10-06; until then the stronger `β_T·L_loop^sharp < 1`). General in `F`. -/
theorem gEff_mul (hγ : E.β_T * E.LloopLo < 1) :
    E.gEff * (1 - E.β_T * E.glo) + (E.c - E.β_T * E.dlo * E.gEff) * (E.Lresp / E.mu)
      = E.vlo + E.nlo * E.sfloor := by
  have hden := (sub_pos.mpr hγ).ne'
  have h : E.gEff * (1 - E.β_T * E.LloopLo)
      = E.vlo + E.nlo * E.sfloor - E.c * (E.Lresp / E.mu) := by
    unfold gEff; exact div_mul_cancel₀ _ hden
  unfold LloopLo at h
  linear_combination h

end ChordEconomyRelief

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)


/-- **The sharp slope** `min g_T g_eff`. On the two-sided extension since renovation item
BJ3.1 (2026-10-07). -/
def gSharp : ℝ := min E.gT E.gEff


end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- `min g_T g_eff ≥ 0` under `hvL` and the lower loop condition
`β_T(g_lo + d_lo L_resp/μ) < 1` (BG3.5(c), 2026-10-06; until then
`β_T·L_loop^sharp < 1`). General in `F`. -/
theorem gSharp_nonneg (hγ : E.β_T * E.LloopLo < 1)
    (hvL : E.c * (E.Lresp / E.mu) < E.vlo + E.nlo * E.sfloor) : 0 ≤ E.gSharp :=
  le_min E.gT_pos.le (E.gEff_pos hγ hvL).le

/-- **The sharp slope satisfies the balance**, with or without the margin, under the
lower loop condition `β_T(g_lo + d_lo L_resp/μ) < 1`, the positivity of `g_eff`'s own
denominator (renovation item BG3.5(c), 2026-10-06; it replaces `β_T·L_loop^sharp < 1`,
which reads the upper chords and is stronger, `LloopLo_le_LloopSharp`): when
`L_resp = 0` any slope at most `g_T` does; otherwise `g_T ≤ g_eff` is
equivalent to the margin at `g_T`, where `g_T` balances, and `g_eff < g_T`
makes the pain term at `g_eff` nonnegative, where `g_eff` balances with
equality. (`hvL` is not needed for the balance, only for the sign of `g_eff`.)
General in `F`. -/
theorem gSharp_balance_lo (hγ : E.β_T * E.LloopLo < 1) :
    E.gSharp * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * E.gSharp) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor := by
  set L := E.Lresp / E.mu with hLdef
  have hL : 0 ≤ L := div_nonneg E.Lresp_nonneg E.mu_pos.le
  have hβd : 0 ≤ E.β_T * E.dlo := mul_nonneg E.hβT0.le E.hdlo0.le
  have hglo1 : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have hgTm := E.gT_mul
  have hgE := E.gEff_mul hγ
  have hden : 0 < 1 - E.β_T * E.LloopLo := sub_pos.mpr hγ
  have hgEmul : E.gEff * (1 - E.β_T * E.LloopLo)
      = E.vlo + E.nlo * E.sfloor - E.c * L := by
    unfold gEff; exact div_mul_cancel₀ _ hden.ne'
  have hgTmul : E.gT * (1 - E.β_T * E.LloopLo)
      = E.vlo + E.nlo * E.sfloor - E.gT * (E.β_T * E.dlo) * L := by
    unfold LloopLo; linear_combination hgTm
  have hgS_le : E.gSharp ≤ E.gT := min_le_left _ _
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- `L = 0`: the pain term vanishes and any slope at most `g_T` balances
    rw [← hL0, mul_zero, add_zero]
    have := mul_le_mul_of_nonneg_right hgS_le hglo1.le
    linarith [hgTm]
  rcases le_or_gt E.gT E.gEff with hle | hlt
  · have hgs : E.gSharp = E.gT := min_eq_left hle
    rw [hgs]
    have h1 := mul_le_mul_of_nonneg_right hle hden.le
    rw [hgTmul, hgEmul] at h1
    -- `c·L ≤ g_T β_T d_lo L`, hence the margin at `g_T`
    have hθ : E.c - E.β_T * E.dlo * E.gT ≤ 0 := by
      have h2 : (E.c - E.β_T * E.dlo * E.gT) * L ≤ 0 := by linarith
      by_contra hcon
      have hcon' := not_le.mp hcon
      have := mul_pos hcon' hLpos
      linarith
    rw [max_eq_left hθ, zero_mul, add_zero, hgTm]
  · have hgs : E.gSharp = E.gEff := min_eq_right hlt.le
    rw [hgs]
    have h1 := mul_lt_mul_of_pos_right hlt hden
    rw [hgTmul, hgEmul] at h1
    -- `g_T β_T d_lo L < c L`, hence `β_T d_lo g_T < c` and the pain term at `g_eff` is positive
    have hθT : E.β_T * E.dlo * E.gT < E.c := by
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_right hcon' hL
      linarith
    have hθ : 0 ≤ E.c - E.β_T * E.dlo * E.gEff := by
      have := mul_le_mul_of_nonneg_left hlt.le hβd
      linarith
    rw [max_eq_right hθ]
    exact le_of_eq hgE

/-- **The sharp slope satisfies the balance** under the loop condition
`β_T·L_loop^sharp < 1`: a corollary of `gSharp_balance_lo`, since that condition implies
the lower one (`one_sub_βT_LloopLo_pos`). Kept with its statement, a pinned evidence row.
General in `F`. -/
theorem gSharp_balance (hγ : E.β_T * E.LloopSharp < 1) :
    E.gSharp * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * E.gSharp) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor :=
  E.gSharp_balance_lo (by linarith [E.one_sub_βT_LloopLo_pos hγ])

/-- **The sharp-side equilibrium at the sharp slope**: under the lower loop condition
`β_T(g_lo + d_lo L_resp/μ) < 1`, `hvL`, a monotone response and
`c − ℓ_lo μ/k_hi ≤ β_T d_lo min{g_T, g_eff}`, the composed equilibrium with full defiance
exists. Renovation item BG3.5 (2026-10-06): the loop condition was the stronger
`β_T·L_loop^sharp < 1` and the sharp side was strict; the construction reads only
`g_eff`'s own denominator and a weak argmax. General in `F`. -/
def equilibriumTop_gSharp (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hγ : E.β_T * E.LloopLo < 1)
    (hvL : E.c * (E.Lresp / E.mu) < E.vlo + E.nlo * E.sfloor)
    (hsharp : E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * E.gSharp) :
    E.toParams.FeedbackStackelbergEquilibriumTop :=
  E.equilibriumTop_sharp hmono (E.gSharp_nonneg hγ hvL) (E.gSharp_balance_lo hγ) hsharp

/-! ### The continuation bracket at the defiance-profile value, half by half -/

/-- The defiance-profile value is `K_T`-Lipschitz, with no margin (the carrier
`{V | K_T-Lipschitz}` is closed, nonempty and invariant under the Target
operator; `targetOp_lipschitz`). Renovation item BH3.11(a) (2026-10-06): stated on the
relief extension `ChordEconomyRelief`, verbatim; until then on `ChordEconomyCs`, whose
semiconvexity of `F`'s sanction section (`Mcs`, `hFcs`) it never read. `VTdef` is the
Target operator's fixed point, so this is `targetFix_lipschitz`. General in `F`. -/
theorem VTdef_lipschitz (hγ : E.β_T * E.LloopSharp < 1) :
    Params.ValueLipschitzWith E.VTdef E.KT :=
  E.targetFix_lipschitz hγ

/-- **The upper half of the continuation bracket at the defiance-profile value**: for
`s₁ ≤ s₂` in `[0,1]`, a higher sanction raises the Target's discounted continuation by at
most `β_T·K_T·d_hi·(s₂ − s₁)`. Only `β_T·γ_T < 1` is read (renovation item BH3.11(c),
2026-10-06): the equilibrium form `VTstar_continuation_bracket` also carries the
loss-offset margin and a monotone response, which only its lower half and the existence of
`VTstar` use. In words: under the loop condition a heavier sanction moves the state by at
most `d_hi` per unit, and the Target's future value rises by at most `K_T` per unit of
state. General in `F`. -/
theorem VTdef_continuation_upper (hγ : E.β_T * E.LloopSharp < 1) {y s₁ s₂ : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1)
    (hle : s₁ ≤ s₂) :
    E.β_T * (E.VTdef (Sanctions.clipS' (E.F y s₂)) - E.VTdef (Sanctions.clipS' (E.F y s₁)))
      ≤ E.β_T * E.KT * E.dhi * (s₂ - s₁) := by
  have hF₁ := E.F_mem _ _ hy hs₁
  have hF₂ := E.F_mem _ _ hy hs₂
  have hz : E.F y s₁ ≤ E.F y s₂ := E.F_mono_s _ hle
  have hβ := E.hβT0.le
  have hlip := E.VTdef_lipschitz hγ (Sanctions.clipS' (E.F y s₁)) (Sanctions.clipS' (E.F y s₂))
  have hdc : dist (Sanctions.clipS' (E.F y s₁)) (Sanctions.clipS' (E.F y s₂))
      = E.F y s₂ - E.F y s₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF₁,
        Sanctions.clipS'_val_eq_of_mem hF₂, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdc] at hlip
  have hchord := E.hShi hy hs₁ hs₂ hle
  have hKT := E.KT_nonneg hγ
  have h1 : E.KT * (E.F y s₂ - E.F y s₁) ≤ E.KT * (E.dhi * (s₂ - s₁)) :=
    mul_le_mul_of_nonneg_left hchord hKT
  have h2 := (abs_le.mp hlip).2
  have := mul_le_mul_of_nonneg_left (le_trans h2 h1) hβ
  linarith

/-- **The lower half of the continuation bracket at the defiance-profile value**: for
`s₁ ≤ s₂` in `[0,1]`, a higher sanction raises the Target's discounted continuation by at
least `β_T·g·d_lo·(s₂ − s₁)`, for any slope `g ≥ 0` that satisfies the balance under a
monotone response (`VTdef_lowerSlope`). The loop condition `β_T·γ_T < 1` and the
loss-offset margin are not read (renovation item BH3.11(c), 2026-10-06; the equilibrium
form `VTstar_continuation_bracket` carries both, at `g = g_T`). In words: a heavier
sanction moves the state up and so gives the Target a better future, at a rate of at least
`g` per unit of state. General in `F`. -/
theorem VTdef_continuation_lower (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor)
    {y s₁ s₂ : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hle : s₁ ≤ s₂) :
    E.β_T * g * E.dlo * (s₂ - s₁)
      ≤ E.β_T * (E.VTdef (Sanctions.clipS' (E.F y s₂))
          - E.VTdef (Sanctions.clipS' (E.F y s₁))) := by
  have hF₁ := E.F_mem _ _ hy hs₁
  have hF₂ := E.F_mem _ _ hy hs₂
  have hz : E.F y s₁ ≤ E.F y s₂ := E.F_mono_s _ hle
  have hβ := E.hβT0.le
  have hlo := E.VTdef_lowerSlope hmono hg hginv (Sanctions.clipS' (E.F y s₁))
    (Sanctions.clipS' (E.F y s₂))
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂)
    (Sanctions.clipS'_mono hz)
  have hdist : dist (Sanctions.clipS' (E.F y s₁)) (Sanctions.clipS' (E.F y s₂))
      = E.F y s₂ - E.F y s₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF₁,
        Sanctions.clipS'_val_eq_of_mem hF₂, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdist] at hlo
  have hchord := E.hSlo hy hs₁ hs₂ hle
  have h1 : g * (E.dlo * (s₂ - s₁)) ≤ g * (E.F y s₂ - E.F y s₁) :=
    mul_le_mul_of_nonneg_left hchord hg
  have := mul_le_mul_of_nonneg_left (le_trans h1 hlo) hβ
  linarith

/-- **The lower half at `g_T`, under the margin**: with the loss-offset margin
`c ≤ β_T·d_lo·g_T` and a monotone response, a higher sanction raises the Target's
discounted continuation at the defiance-profile value by at least
`β_T·g_T·d_lo·(s₂ − s₁)`. The margin makes `g_T` satisfy the balance (`gT_balance`). The
loop condition is not read (renovation item BH3.11(c), 2026-10-06; this is the lower half of
`VTstar_continuation_bracket` without `β_T·γ_T < 1`, since `VTdef = VTstar` there). General
in `F`. -/
theorem VTdef_continuation_lower_gT (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) {y s₁ s₂ : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1)
    (hle : s₁ ≤ s₂) :
    E.β_T * E.gT * E.dlo * (s₂ - s₁)
      ≤ E.β_T * (E.VTdef (Sanctions.clipS' (E.F y s₂))
          - E.VTdef (Sanctions.clipS' (E.F y s₁))) :=
  E.VTdef_continuation_lower hmono E.gT_pos.le (E.gT_balance hTM) hy hs₁ hs₂ hle

/-- **The lower half at the sharp slope, without the margin**: under the lower loop
condition `β_T(g_lo + d_lo L_resp/μ) < 1`, `hvL : c·L_resp/μ < v_lo + n_lo·σ(0,0)` and a
monotone response, a higher sanction raises the Target's discounted continuation at the
defiance-profile value by at least `β_T·min{g_T, g_eff}·d_lo·(s₂ − s₁)`
(`gSharp_nonneg`, `gSharp_balance_lo`). The loss-offset margin is not read (renovation item
BH3.11(c), 2026-10-06). General in `F`. -/
theorem VTdef_continuation_lower_gSharp
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hγ : E.β_T * E.LloopLo < 1)
    (hvL : E.c * (E.Lresp / E.mu) < E.vlo + E.nlo * E.sfloor) {y s₁ s₂ : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1)
    (hle : s₁ ≤ s₂) :
    E.β_T * E.gSharp * E.dlo * (s₂ - s₁)
      ≤ E.β_T * (E.VTdef (Sanctions.clipS' (E.F y s₂))
          - E.VTdef (Sanctions.clipS' (E.F y s₁))) :=
  E.VTdef_continuation_lower hmono (E.gSharp_nonneg hγ hvL) (E.gSharp_balance_lo hγ) hy hs₁
    hs₂ hle

end ChordEconomyRelief


/-! ## 5. The relief side: the zero level at any carrier value, its Lipschitz
constant, the relief-branch Target value, and the relief equilibrium -/

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-- The compliance levels at which the response to a carrier value vanishes
(the `VS01` form is `zeroSet`). -/
def zeroSetAt (V : Val) (x : ℝ) : Set ℝ :=
  Sanctions.ZeroLevel.zeroSet (fun x a => E.response V x a) x

/-- **The zero level at a carrier value**: the least compliance at which the
response vanishes (`Foundations/ZeroLevel`). -/
def zeroLevelAt (V : Val) (x : ℝ) : ℝ :=
  Sanctions.ZeroLevel.level (fun x a => E.response V x a) x

theorem zeroLevelAt_eq_sInf (V : Val) (x : ℝ) : E.zeroLevelAt V x = sInf (E.zeroSetAt V x) :=
  rfl

theorem one_mem_zeroSetAt (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : (1 : ℝ) ∈ E.zeroSetAt V x :=
  ⟨⟨zero_le_one, le_rfl⟩, E.response_at_one hP hV hx⟩

theorem zeroSetAt_bddBelow (V : Val) (x : ℝ) : BddBelow (E.zeroSetAt V x) :=
  Sanctions.ZeroLevel.zeroSet_bddBelow x

theorem response_continuous_a {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : Continuous (fun a => E.response V x a) := by
  have hc0 := E.toParams.σ_dyn_continuousOn_S_of_unique_on V
    (fun x hx a s₁ s₂ hs₁ hs₂ h₁ h₂ => E.DAU_on_carrier hV x hx a s₁ s₂ hs₁ hs₂ h₁ h₂)
  have hmap : Set.MapsTo (fun a : ℝ => ((x, a) : ℝ × ℝ)) Set.univ
      ((Sanctions.S : Set ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    fun a _ => ⟨hx, Set.mem_univ _⟩
  have hc := hc0.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hc' : ContinuousOn (fun a => E.response V x a) Set.univ :=
    hc.congr (fun a _ => rfl)
  exact continuousOn_univ.1 hc'

theorem zeroLevelAt_mem (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : E.zeroLevelAt V x ∈ Sanctions.I :=
  Sanctions.ZeroLevel.level_mem (ρ := fun x a => E.response V x a)
    (E.response_continuous_a hV hx).continuousOn (E.response_at_one hP hV hx)

theorem response_zeroLevelAt (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : E.response V x (E.zeroLevelAt V x) = 0 :=
  Sanctions.ZeroLevel.rho_level (ρ := fun x a => E.response V x a)
    (E.response_continuous_a hV hx).continuousOn (E.response_at_one hP hV hx)

theorem response_pos_of_lt_zeroLevelAt (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevelAt V x) :
    0 < E.response V x a :=
  Sanctions.ZeroLevel.rho_pos_of_lt (ρ := fun x a => E.response V x a)
    (E.response_mem V x a).1 ha0 (ha.le.trans (E.zeroLevelAt_mem hP hV hx).2) ha

theorem response_eq_zero_of_zeroLevelAt_le (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : E.zeroLevelAt V x ≤ a) (ha1 : a ≤ 1) :
    E.response V x a = 0 :=
  Sanctions.ZeroLevel.rho_eq_zero_of_ge (ρ := fun x a => E.response V x a)
    (E.response_continuous_a hV hx).continuousOn (E.response_at_one hP hV hx)
    (E.response_antitoneOn_a hV hx) ha ha1

/-- **The Sender's objective is `M_tot`-semiconvex in the sanction at every
two-sided carrier value** (the `VS01` form is `senderObj_semiconvex`). -/
theorem senderObj_semiconvex_carrier {V : Val} (hV : V ∈ E.carrierS2) {x : ℝ}
    (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    SemiconvexOnSet (fun s => E.senderObj V x a s) Sanctions.I E.Mtot := by
  have hcomp : SemiconvexOnSet (fun s => V (Sanctions.clipS' (E.F x s))) Sanctions.I
      (E.SigC * E.dhi ^ 2 + E.KS * E.Mcs) :=
    semiconvexOnSet_comp_of_stateChord
      (v := fun z => V (Sanctions.clipS' z)) (G := fun s => E.F x s)
      E.SigC_nonneg E.KS_nonneg E.hdlo0.le E.hMcs0
      (E.clip_monotoneOn hV.1.1) (E.clip_lip hV.1.1) hV.2
      (fun s hs => E.F_maps x hx s hs) (E.sanctionBand hx) (E.hFcs x hx)
  exact (E.hUS_convex x hx a ha).add (hcomp.const_mul E.hβS0.le)

/-- **Sharp relief rate at a carrier value**: between two compliance levels
strictly below the zero level, extra compliance lowers the sanction by at least
`k_lo·Δa/M_tot` (the `VS01` form is `ρ01_shift_ge_linear`). -/
theorem response_shift_ge_linear_at (hInt : E.Interior) (hP : E.Placable) {V : Val} (hV : V ∈
    E.carrierS2)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a a' : ℝ} (ha : 0 ≤ a) (haa' : a < a')
    (ha' : a' < E.zeroLevelAt V x) :
    E.klo * (a' - a) / E.Mtot ≤ E.response V x a - E.response V x a' := by
  have hz1 := (E.zeroLevelAt_mem hP hV.1 hx).2
  have haI : a ∈ Sanctions.I := ⟨ha, by linarith⟩
  have ha'I : a' ∈ Sanctions.I := ⟨by linarith, by linarith⟩
  have hint := E.response_pos_of_lt_zeroLevelAt hP hV.1 hx ha'I.1 ha'
  exact Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_tilt_of_semiconvex_interior
    E.Mtot_pos (E.senderObj_semiconvex_carrier hV hx ha'I)
    (E.senderObj_semiconvex_carrier hV hx haI) hint
    (E.response_lt_one hInt hV.1 hx ha'I) (E.response_isMaxOn _ x a')
    (mul_pos E.hklo (by linarith)) (E.response_mem _ x a)
    (E.response_lt_one hInt hV.1 hx haI) (E.response_isMaxOn _ x a)
    (fun u₁ hu₁ u₂ hu₂ hu => by
      have hdd := E.hUS_placLo x hx a haI a' ha'I u₁ hu₁ u₂ hu₂ haa'.le hu
      simp only [senderObj]
      nlinarith [hdd])

/-- **Below the zero level the response is at least `k_lo(a* − a)/M_tot`**, at
every two-sided carrier value (the `VS01` form is `ρ01_ge_of_lt_sharp`). -/
theorem response_ge_of_lt_zeroLevelAt (hInt : E.Interior) (hP : E.Placable) {V : Val} (hV : V ∈
    E.carrierS2)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevelAt V x) :
    E.klo * (E.zeroLevelAt V x - a) / E.Mtot ≤ E.response V x a := by
  have h : E.klo / E.Mtot * (E.zeroLevelAt V x - a) ≤ E.response V x a :=
    Sanctions.ZeroLevel.rho_ge_of_lt (ρ := fun x a => E.response V x a)
      (div_pos E.hklo E.Mtot_pos)
      (fun a' h1 h2 => by
        have hs := E.response_shift_ge_linear_at hInt hP hV hx ha0 h1 h2
        have heq : E.klo / E.Mtot * (a' - a) = E.klo * (a' - a) / E.Mtot := by ring
        show E.klo / E.Mtot * (a' - a) ≤ E.response V x a - E.response V x a'
        linarith)
      (fun a' _ _ => (E.response_mem V x a').1) ha
  have heq : E.klo / E.Mtot * (E.zeroLevelAt V x - a)
      = E.klo * (E.zeroLevelAt V x - a) / E.Mtot := by ring
  linarith

/-- The zero level at `VS01` is the zero level of the reading `01`. -/
theorem zeroLevelAt_VS01 (x : ℝ) : E.zeroLevelAt E.VS01 x = E.zeroLevel x := rfl

/-- **The zero level's state Lipschitz constant**, `L_α = M_tot·L_resp/(k_lo·μ)`:
across two states the response at a fixed compliance moves by at most
`L_resp·|Δx|/μ`, and below the zero level it rises at rate at least
`k_lo/M_tot`. -/
def Lalpha : ℝ := E.Mtot * E.Lresp / (E.klo * E.mu)

theorem Lalpha_nonneg : 0 ≤ E.Lalpha :=
  div_nonneg (mul_nonneg E.Mtot_pos.le E.Lresp_nonneg) (mul_nonneg E.hklo.le E.mu_pos.le)

theorem zeroLevelAt_sub_le (hInt : E.Interior) (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS2)
    {x x' : ℝ} (hx : x ∈ Sanctions.I) (hx' : x' ∈ Sanctions.I) :
    E.zeroLevelAt V x' - E.zeroLevelAt V x ≤ E.Lalpha * |x - x'| := by
  rcases le_or_gt (E.zeroLevelAt V x') (E.zeroLevelAt V x) with hle | hlt
  · have : 0 ≤ E.Lalpha * |x - x'| := mul_nonneg E.Lalpha_nonneg (abs_nonneg _)
    linarith
  · set a := E.zeroLevelAt V x with ha
    have haI : a ∈ Sanctions.I := E.zeroLevelAt_mem hP hV.1 hx
    have hzero : E.response V x a = 0 := E.response_zeroLevelAt hP hV.1 hx
    have hlow := E.response_ge_of_lt_zeroLevelAt hInt hP hV hx' haI.1 hlt
    have hdist := E.response_dist_le_state hV hx' hx haI
    rw [hzero, sub_zero] at hdist
    have h1 : E.klo * (E.zeroLevelAt V x' - a) / E.Mtot ≤ (E.Lresp * |x' - x|) / E.mu :=
      hlow.trans ((le_abs_self _).trans hdist)
    have hM := E.Mtot_pos
    have hk := E.hklo
    have hμ := E.mu_pos
    rw [abs_sub_comm x x']
    unfold Lalpha
    have h2 : E.klo * (E.zeroLevelAt V x' - a) ≤ E.Lresp * |x' - x| / E.mu * E.Mtot := by
      rwa [div_le_iff₀ hM] at h1
    have h3 : E.zeroLevelAt V x' - a ≤ E.Lresp * |x' - x| / E.mu * E.Mtot / E.klo := by
      rw [le_div_iff₀ hk]; linarith [h2]
    calc E.zeroLevelAt V x' - a ≤ E.Lresp * |x' - x| / E.mu * E.Mtot / E.klo := h3
      _ = E.Mtot * E.Lresp / (E.klo * E.mu) * |x' - x| := by field_simp

/-- **The zero level is `L_α`-Lipschitz in the state** at every two-sided
carrier value. -/
theorem zeroLevelAt_lipschitz (hInt : E.Interior) (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS2)
    {x x' : ℝ} (hx : x ∈ Sanctions.I) (hx' : x' ∈ Sanctions.I) :
    |E.zeroLevelAt V x - E.zeroLevelAt V x'| ≤ E.Lalpha * |x - x'| := by
  rw [abs_le]
  constructor
  · have := E.zeroLevelAt_sub_le hInt hP hV hx hx'
    linarith
  · have := E.zeroLevelAt_sub_le hInt hP hV hx' hx
    rw [abs_sub_comm x' x] at this
    linarith

theorem zeroLevel_lipschitz (hInt : E.Interior) (hP : E.Placable) {x x' : ℝ} (hx : x ∈ Sanctions.I)
    (hx' : x' ∈ Sanctions.I) :
    |E.zeroLevel x - E.zeroLevel x'| ≤ E.Lalpha * |x - x'| :=
  E.zeroLevelAt_lipschitz hInt hP E.VS01_mem2 hx hx'

/-! ### The relief-branch Target value -/

theorem βT_ghi_lt_one : E.β_T * E.ghi < 1 := by
  have := E.hβT1; have := E.hβT0; have := E.hghi1; have := E.ghi_nonneg
  nlinarith

theorem vhi_pos : 0 < E.vhi := by
  have h := E.vlo_le_vhi 0 zero_mem_I
  simp only [mul_zero, add_zero] at h
  linarith [E.hvlo]

/-- **The relief-branch Lipschitz constant** `K_T^rel = (v_hi + ℓ_hi L_α)/(1 − β_T g_hi)`:
the stage state rate at zero sanction (T6u) plus the compliance cost along the
zero level (T4u), compounded through the zero-sanction transition's upper state
chord. -/
def KTrel : ℝ := (E.vhi + E.ℓhi * E.Lalpha) / (1 - E.β_T * E.ghi)

theorem KTrel_nonneg : 0 ≤ E.KTrel :=
  div_nonneg (add_nonneg E.vhi_pos.le (mul_nonneg E.ℓhi_pos.le E.Lalpha_nonneg))
    (by linarith [E.βT_ghi_lt_one])

theorem KTrel_fix : E.vhi + E.ℓhi * E.Lalpha + E.β_T * E.ghi * E.KTrel = E.KTrel := by
  unfold KTrel
  have h : (1 - E.β_T * E.ghi) ≠ 0 := by linarith [E.βT_ghi_lt_one]
  field_simp
  ring

/-- The relief-branch Target operator, `V ↦ U_T(y, a*(y), 0) + β_T·V(F(y,0))`:
along the zero level the realised sanction is zero, so the state moves by
`F(·,0)`. -/
def reliefOp (hInt : E.Interior) (hP : E.Placable) (V : Val) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) =>
        E.toParams.U_T y.val (E.zeroLevel y.val) 0
          + E.toParams.β_T * V (Sanctions.clipS' (E.toParams.F y.val 0)), by
      have hz : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.zeroLevel y.val) :=
        continuousOn_iff_continuous_restrict.mp (E.zeroLevel_continuousOn hInt hP)
      have hU : Continuous (fun y : ↥(Sanctions.S : Set ℝ) =>
          E.toParams.U_T y.val (E.zeroLevel y.val) 0) :=
        E.toParams.U_T_continuous.comp
          (continuous_subtype_val.prodMk (hz.prodMk continuous_const))
      have hF : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.toParams.F y.val 0) :=
        E.toParams.F_continuous.comp (continuous_subtype_val.prodMk continuous_const)
      exact hU.add
        (continuous_const.mul (V.continuous.comp (Sanctions.clipS'_continuous.comp hF)))⟩

theorem reliefOp_apply (hInt : E.Interior) (hP : E.Placable) (V : Val) (y : ↥(Sanctions.S : Set ℝ))
    :
    E.reliefOp hInt hP V y = E.toParams.U_T y.val (E.zeroLevel y.val) 0
      + E.toParams.β_T * V (Sanctions.clipS' (E.toParams.F y.val 0)) := rfl

theorem reliefOp_contracting (hInt : E.Interior) (hP : E.Placable) :
    ContractingWith E.toParams.β_T_nnreal (E.reliefOp hInt hP) := by
  refine ⟨E.toParams.β_T_nnreal_lt_one, ?_⟩
  apply lipschitzWith_of_pointwise_dist_le
  intro V W y
  rw [reliefOp_apply, reliefOp_apply, Real.dist_eq]
  have hβ : (0:ℝ) ≤ E.toParams.β_T := E.toParams.β_T_mem.1
  have h1 : |(E.toParams.U_T y.val (E.zeroLevel y.val) 0
        + E.toParams.β_T * V (Sanctions.clipS' (E.toParams.F y.val 0)))
      - (E.toParams.U_T y.val (E.zeroLevel y.val) 0
        + E.toParams.β_T * W (Sanctions.clipS' (E.toParams.F y.val 0)))|
      = E.toParams.β_T * |V (Sanctions.clipS' (E.toParams.F y.val 0))
          - W (Sanctions.clipS' (E.toParams.F y.val 0))| := by
    rw [show ∀ a b c : ℝ, (a + E.toParams.β_T * b) - (a + E.toParams.β_T * c)
        = E.toParams.β_T * (b - c) from fun a b c => by ring, abs_mul, abs_of_nonneg hβ]
  rw [h1]
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := V) (g := W)
    (Sanctions.clipS' (E.toParams.F y.val 0))
  rw [Real.dist_eq] at h2
  have := mul_le_mul_of_nonneg_left h2 hβ
  convert this using 2

/-- **The relief operator preserves the `K_T^rel`-Lipschitz clause.** -/
theorem reliefOp_lipschitz (hInt : E.Interior) (hP : E.Placable) {V : Val}
    (hV : Params.ValueLipschitzWith V E.KTrel) :
    Params.ValueLipschitzWith (E.reliefOp hInt hP V) E.KTrel := by
  intro y₁ y₂
  rw [reliefOp_apply, reliefOp_apply]
  have hy₁ := y₁.property
  have hy₂ := y₂.property
  have hd : dist y₁ y₂ = |y₂.val - y₁.val| := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
  rw [hd]
  have hβ : (0:ℝ) ≤ E.β_T := E.hβT0.le
  have hz := E.zeroLevel_lipschitz hInt hP hy₂ hy₁
  have hz₁ := E.zeroLevel_mem hP hy₁
  have hz₂ := E.zeroLevel_mem hP hy₂
  have hF₁ : E.toParams.F y₁.val 0 ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hy₁ zero_mem_I
  have hF₂ : E.toParams.F y₂.val 0 ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hy₂ zero_mem_I
  have hsucc : |E.toParams.F y₂.val 0 - E.toParams.F y₁.val 0| ≤ E.ghi * |y₂.val - y₁.val| :=
    abs_sub_le_of_stateBand E.hglo0 (E.hbandAll 0 zero_mem_I) hy₂ hy₁
  have hV' := hV (Sanctions.clipS' (E.toParams.F y₁.val 0))
    (Sanctions.clipS' (E.toParams.F y₂.val 0))
  have hdc : dist (Sanctions.clipS' (E.toParams.F y₁.val 0))
      (Sanctions.clipS' (E.toParams.F y₂.val 0))
      = |E.toParams.F y₂.val 0 - E.toParams.F y₁.val 0| := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF₁,
      Sanctions.clipS'_val_eq_of_mem hF₂, abs_sub_comm]
  rw [hdc] at hV'
  have hK := E.KTrel_nonneg
  have hcont : |V (Sanctions.clipS' (E.toParams.F y₂.val 0))
      - V (Sanctions.clipS' (E.toParams.F y₁.val 0))|
      ≤ E.KTrel * (E.ghi * |y₂.val - y₁.val|) :=
    hV'.trans (mul_le_mul_of_nonneg_left hsucc hK)
  have hfix := E.KTrel_fix
  -- the stage along the zero level: compliance (T4u) at `y₂`, then the state (T6u) at `s = 0`
  have hstage : |E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0|
      ≤ (E.vhi + E.ℓhi * E.Lalpha) * |y₂.val - y₁.val| := by
    have h1 := E.UT_compliance_lip hy₂ hz₁ hz₂ zero_mem_I
    have h2 := E.hUT_stateHi (E.zeroLevel y₁.val) hz₁ 0 zero_mem_I y₁.val hy₁ y₂.val hy₂
    simp only [mul_zero, add_zero] at h2
    calc |E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0|
        = |(E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₂.val (E.zeroLevel y₁.val) 0)
          + (E.U_T y₂.val (E.zeroLevel y₁.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0)| := by
          ring_nf
      _ ≤ |E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₂.val (E.zeroLevel y₁.val) 0|
          + |E.U_T y₂.val (E.zeroLevel y₁.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0| :=
          abs_add_le _ _
      _ ≤ E.ℓhi * (E.Lalpha * |y₂.val - y₁.val|) + E.vhi * |y₂.val - y₁.val| :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left hz E.ℓhi_pos.le)) h2
      _ = (E.vhi + E.ℓhi * E.Lalpha) * |y₂.val - y₁.val| := by ring
  calc |(E.toParams.U_T y₂.val (E.zeroLevel y₂.val) 0
          + E.β_T * V (Sanctions.clipS' (E.toParams.F y₂.val 0)))
        - (E.toParams.U_T y₁.val (E.zeroLevel y₁.val) 0
          + E.β_T * V (Sanctions.clipS' (E.toParams.F y₁.val 0)))|
      = |(E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0)
        + E.β_T * (V (Sanctions.clipS' (E.toParams.F y₂.val 0))
          - V (Sanctions.clipS' (E.toParams.F y₁.val 0)))| := by ring_nf
    _ ≤ |E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0|
        + E.β_T * |V (Sanctions.clipS' (E.toParams.F y₂.val 0))
          - V (Sanctions.clipS' (E.toParams.F y₁.val 0))| := by
        have := abs_add_le
          (E.U_T y₂.val (E.zeroLevel y₂.val) 0 - E.U_T y₁.val (E.zeroLevel y₁.val) 0)
          (E.β_T * (V (Sanctions.clipS' (E.toParams.F y₂.val 0))
            - V (Sanctions.clipS' (E.toParams.F y₁.val 0))))
        rw [abs_mul, abs_of_nonneg hβ] at this
        exact this
    _ ≤ (E.vhi + E.ℓhi * E.Lalpha) * |y₂.val - y₁.val|
        + E.β_T * (E.KTrel * (E.ghi * |y₂.val - y₁.val|)) :=
        add_le_add hstage (mul_le_mul_of_nonneg_left hcont hβ)
    _ = E.KTrel * |y₂.val - y₁.val| := by linear_combination |y₂.val - y₁.val| * hfix

/-- **The relief-branch Target value**: the fixed point of the relief operator. -/
def VTrel (hInt : E.Interior) (hP : E.Placable) : Val := (E.reliefOp_contracting hInt hP).fixedPoint

theorem VTrel_fix (hInt : E.Interior) (hP : E.Placable) : E.reliefOp hInt hP (E.VTrel hInt hP) =
    E.VTrel hInt hP :=
  (E.reliefOp_contracting hInt hP).fixedPoint_isFixedPt

theorem VTrel_lipschitz (hInt : E.Interior) (hP : E.Placable) :
    Params.ValueLipschitzWith (E.VTrel hInt hP) E.KTrel := by
  have hcontr := E.reliefOp_contracting hInt hP
  obtain ⟨W, hW, hWmem⟩ := StokeyLucas.fixedPoint_mem_of_mapsTo hcontr.1 _ hcontr.2
    {V : Val | Params.ValueLipschitzWith V E.KTrel}
    (Params.valueLipschitz_isClosed _) ⟨0, fun y₁ y₂ => by
      simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, sub_zero, abs_zero]
      exact mul_nonneg E.KTrel_nonneg dist_nonneg⟩
    (fun V hV => E.reliefOp_lipschitz hInt hP hV)
  have h1 : W = hcontr.fixedPoint := hcontr.fixedPoint_unique hW
  show Params.ValueLipschitzWith hcontr.fixedPoint E.KTrel
  rw [← h1]
  exact hWmem

/-! ### The relief equilibrium -/

/-- Above the zero level compliance buys nothing and costs at least `ℓ_lo` per
unit, at the relief values. -/
theorem jointRel_lt_of_gt (hInt : E.Interior) (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) {a :
    ℝ}
    (ha : E.zeroLevel x < a) (ha1 : a ≤ 1) :
    E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x a
      < E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x (E.zeroLevel x) := by
  rw [joint_T_integrand_eq, joint_T_integrand_eq, E.ρ01_zeroLevel hP hx,
    E.ρ01_eq_zero_of_ge hP hx ha.le ha1]
  have hzI := E.zeroLevel_mem hP hx
  have haI : a ∈ Sanctions.I := ⟨by linarith [hzI.1], ha1⟩
  have h := E.hUT_costLo x hx 0 zero_mem_I (E.zeroLevel x) hzI a haI ha.le
  have := mul_pos E.hℓlo (by linarith : (0:ℝ) < a - E.zeroLevel x)
  change E.U_T x a 0 + E.β_T * (E.VTrel hInt hP) (Sanctions.clipS' (E.F x 0))
    < E.U_T x (E.zeroLevel x) 0 + E.β_T * (E.VTrel hInt hP) (Sanctions.clipS' (E.F x 0))
  linarith

/-- **Below the zero level, at the relief values, more compliance is worth it**
under the relief side `ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K_T^rel)`: the sanction
avoided, at least `k_lo(a* − a)/M_tot`, is worth at least `p_lo` in pain and
costs at most `β_T d_hi K_T^rel` per unit in continuation, against the
compliance cost, at most `ℓ_hi(a* − a)`. -/
theorem jointRel_lt_of_lt (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevel x) :
    E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x a
      < E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x (E.zeroLevel x) := by
  rw [joint_T_integrand_eq, joint_T_integrand_eq, E.ρ01_zeroLevel hP hx]
  set ρ := E.response E.VS01 x a with hρdef
  have hzI := E.zeroLevel_mem hP hx
  have haI : a ∈ Sanctions.I := ⟨ha0, by linarith [hzI.2]⟩
  have hρlow := E.ρ01_ge_of_lt_sharp hInt hP hx ha0 ha
  have hρmem := E.response_mem E.VS01 x a
  have hF0 : E.F x 0 ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx zero_mem_I
  have hFρ : E.F x ρ ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx hρmem
  have hchord : E.F x ρ - E.F x 0 ≤ E.dhi * (ρ - 0) :=
    E.hShi hx zero_mem_I hρmem hρmem.1
  have hFmono : E.F x 0 ≤ E.F x ρ := E.F_mono_s x hρmem.1
  have hlip := E.VTrel_lipschitz hInt hP (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
  have hdc : dist (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
      = E.F x ρ - E.F x 0 := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF0,
      Sanctions.clipS'_val_eq_of_mem hFρ, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdc] at hlip
  have hK := E.KTrel_nonneg
  have hβ := E.hβT0.le
  have hcont : E.β_T * ((E.VTrel hInt hP) (Sanctions.clipS' (E.F x ρ))
      - (E.VTrel hInt hP) (Sanctions.clipS' (E.F x 0))) ≤ E.β_T * (E.KTrel * (E.dhi * ρ)) := by
    apply mul_le_mul_of_nonneg_left _ hβ
    have h1 := (le_abs_self _).trans hlip
    have h2 : E.KTrel * (E.F x ρ - E.F x 0) ≤ E.KTrel * (E.dhi * ρ) := by
      apply mul_le_mul_of_nonneg_left _ hK; linarith [hchord]
    linarith
  -- the stage: cost at most `ℓ_hi` per unit of compliance, pain at least `p_lo` per unit
  have hstage := E.UT_sub_ge hx haI hzI hρmem zero_mem_I ha.le hρmem.1
  set Γ := E.plo - E.β_T * E.dhi * E.KTrel with hΓ
  have hM := E.Mtot_pos
  have hk := E.hklo
  have hΓpos : 0 < Γ := by
    by_contra hcon
    have : E.klo * Γ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.mp hcon)
    have : 0 < E.ℓhi * E.Mtot := mul_pos E.ℓhi_pos hM
    linarith
  have hgap : 0 < E.zeroLevel x - a := by linarith
  have h1 : E.klo * (E.zeroLevel x - a) / E.Mtot * Γ ≤ ρ * Γ :=
    mul_le_mul_of_nonneg_right hρlow hΓpos.le
  have h2 : E.ℓhi * (E.zeroLevel x - a) < E.klo * (E.zeroLevel x - a) / E.Mtot * Γ := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hM]
    have := mul_lt_mul_of_pos_right hrel hgap
    nlinarith [this]
  change E.U_T x a ρ + E.β_T * (E.VTrel hInt hP) (Sanctions.clipS' (E.F x ρ))
    < E.U_T x (E.zeroLevel x) 0 + E.β_T * (E.VTrel hInt hP) (Sanctions.clipS' (E.F x 0))
  nlinarith [h1, h2, hcont, hstage]

/-- **Below the zero level, at the relief values, more compliance is weakly worth it**
under the weak relief side `ℓ_hi·M_tot ≤ k_lo(p_lo − β_T d_hi K_T^rel)` (renovation item
BG3.5(b), 2026-10-06): the form of `jointRel_lt_of_lt` with `≤` in hypothesis and
conclusion, which is what existence reads. The side still makes
`p_lo − β_T d_hi K_T^rel` positive, because `ℓ_hi·M_tot > 0`. In words: the relief bought
by closing the gap to the zero level is worth at least its compliance cost. General in
`F`. -/
theorem jointRel_le_of_lt (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot ≤ E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevel x) :
    E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x a
      ≤ E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x (E.zeroLevel x) := by
  rw [joint_T_integrand_eq, joint_T_integrand_eq, E.ρ01_zeroLevel hP hx]
  set ρ := E.response E.VS01 x a with hρdef
  have hzI := E.zeroLevel_mem hP hx
  have haI : a ∈ Sanctions.I := ⟨ha0, by linarith [hzI.2]⟩
  have hρlow := E.ρ01_ge_of_lt_sharp hInt hP hx ha0 ha
  have hρmem := E.response_mem E.VS01 x a
  have hF0 : E.F x 0 ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx zero_mem_I
  have hFρ : E.F x ρ ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx hρmem
  have hchord : E.F x ρ - E.F x 0 ≤ E.dhi * (ρ - 0) :=
    E.hShi hx zero_mem_I hρmem hρmem.1
  have hFmono : E.F x 0 ≤ E.F x ρ := E.F_mono_s x hρmem.1
  have hlip := E.VTrel_lipschitz hInt hP (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
  have hdc : dist (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
      = E.F x ρ - E.F x 0 := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF0,
      Sanctions.clipS'_val_eq_of_mem hFρ, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdc] at hlip
  have hK := E.KTrel_nonneg
  have hβ := E.hβT0.le
  have hcont : E.β_T * ((E.VTrel hInt hP) (Sanctions.clipS' (E.F x ρ))
      - (E.VTrel hInt hP) (Sanctions.clipS' (E.F x 0))) ≤ E.β_T * (E.KTrel * (E.dhi * ρ)) := by
    apply mul_le_mul_of_nonneg_left _ hβ
    have h1 := (le_abs_self _).trans hlip
    have h2 : E.KTrel * (E.F x ρ - E.F x 0) ≤ E.KTrel * (E.dhi * ρ) := by
      apply mul_le_mul_of_nonneg_left _ hK; linarith [hchord]
    linarith
  -- the stage: cost at most `ℓ_hi` per unit of compliance, pain at least `p_lo` per unit
  have hstage := E.UT_sub_ge hx haI hzI hρmem zero_mem_I ha.le hρmem.1
  set Γ := E.plo - E.β_T * E.dhi * E.KTrel with hΓ
  have hM := E.Mtot_pos
  have hk := E.hklo
  have hΓpos : 0 < Γ := by
    by_contra hcon
    have : E.klo * Γ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.mp hcon)
    have : 0 < E.ℓhi * E.Mtot := mul_pos E.ℓhi_pos hM
    linarith
  have hgap : 0 < E.zeroLevel x - a := by linarith
  have h1 : E.klo * (E.zeroLevel x - a) / E.Mtot * Γ ≤ ρ * Γ :=
    mul_le_mul_of_nonneg_right hρlow hΓpos.le
  have h2 : E.ℓhi * (E.zeroLevel x - a) ≤ E.klo * (E.zeroLevel x - a) / E.Mtot * Γ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hM]
    have := mul_le_mul_of_nonneg_right hrel hgap.le
    nlinarith [this]
  change E.U_T x a ρ + E.β_T * (E.VTrel hInt hP) (Sanctions.clipS' (E.F x ρ))
    ≤ E.U_T x (E.zeroLevel x) 0 + E.β_T * (E.VTrel hInt hP) (Sanctions.clipS' (E.F x 0))
  nlinarith [h1, h2, hcont, hstage]

/-- **The zero level is a Target argmax at the relief values** under the weak relief side
`ℓ_hi·M_tot ≤ k_lo(p_lo − β_T d_hi K_T^rel)` (renovation item BG3.5(b), 2026-10-06; the
side was strict until then). Existence needs only this weak argmax; uniqueness keeps the
strict side (`zeroLevel_argmax_unique_rel`). General in `F`. -/
theorem zeroLevel_isMaxOn_rel (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot ≤ E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x a) Sanctions.I
      (E.zeroLevel x) := by
  rw [isMaxOn_iff]
  intro a ha
  rcases lt_trichotomy a (E.zeroLevel x) with h | h | h
  · exact E.jointRel_le_of_lt hInt hP hrel hx ha.1 h
  · rw [h]
  · exact (E.jointRel_lt_of_gt hInt hP hx h ha.2).le

theorem zeroLevel_argmax_unique_rel (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.toParams.joint_T_integrand (E.VTrel hInt hP) E.VS01 x b)
      Sanctions.I a) : a = E.zeroLevel x := by
  rcases lt_trichotomy a (E.zeroLevel x) with h | h | h
  · exfalso
    have h1 := E.jointRel_lt_of_lt hInt hP hrel hx ha.1 h
    have h2 := hmax (E.zeroLevel_mem hP hx)
    exact absurd h2 (not_le.mpr h1)
  · exact h
  · exfalso
    have h1 := E.jointRel_lt_of_gt hInt hP hx h ha.2
    have h2 := hmax (E.zeroLevel_mem hP hx)
    exact absurd h2 (not_le.mpr h1)

/-- **The relief equilibrium of a chord economy under a general transition**:
a top-selector feedback Stackelberg equilibrium in which the forward-looking
Target complies at the zero level `a*(x)` at every state, the Sender's response
is zero on the path, the Sender's value is the zero-sanction value `VS01` and
the Target's the relief-branch value `VTrel`. Exists under placability, the
relief side `ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K_T^rel)`, and zero-sanction
neutrality (which makes `VS01` the Sender's value at the zero level). Rule 1,
Rule 15: the policy is derived as the unique argmax at constructed values. -/
def reliefEquilibriumTop (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    (hN : E.ZeroSanctionNeutral) :
    E.toParams.FeedbackStackelbergEquilibriumTop where
  V_T := E.VTrel hInt hP
  V_S := E.VS01
  α := E.α01
  hα := E.α01_continuous hInt hP
  α_mem := fun x _ => E.α01_mem hP x
  V_S_fix := by
    ext y
    change E.VS01 y = sSup ((fun s => E.toParams.integrandS E.α01 (fun z => E.VS01 z)
      (y.val, s)) '' Sanctions.I)
    have hα : E.α01 y.val = E.zeroLevel y.val := E.α01_eq y.property
    have hgt : IsGreatest ((fun s => E.toParams.integrandS E.α01 (fun z => E.VS01 z)
        (y.val, s)) '' Sanctions.I)
        (E.senderObj E.VS01 y.val (E.α01 y.val) (E.response E.VS01 y.val (E.α01 y.val))) := by
      refine ⟨⟨_, E.response_mem E.VS01 y.val (E.α01 y.val), rfl⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact E.response_isMaxOn E.VS01 y.val (E.α01 y.val) hs
    rw [hgt.csSup_eq, hα, E.ρ01_zeroLevel hP y.property]
    have h := congrArg (fun V : Val => V y) E.VS01_fix
    simp only at h
    rw [relaxOp_apply] at h
    unfold senderObj
    rw [hN y.val y.property (E.zeroLevel y.val) ((E.zeroLevel_mem hP) y.property)]
    exact h.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest
        ((fun a => E.toParams.joint_T_top_integrand (E.VTrel hInt hP) E.VS01 y.val a) ''
            Sanctions.I)
        (E.toParams.joint_T_top_integrand (E.VTrel hInt hP) E.VS01 y.val (E.zeroLevel y.val)) := by
      refine ⟨⟨_, E.zeroLevel_mem hP y.property, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.joint_T_top_integrand_eq E.VS01_mem _ y.property,
        E.joint_T_top_integrand_eq E.VS01_mem _ y.property]
      exact E.zeroLevel_isMaxOn_rel hInt hP hrel.le y.property ha
    rw [hgt.csSup_eq, E.joint_T_top_integrand_eq E.VS01_mem _ y.property,
      joint_T_integrand_eq, E.ρ01_zeroLevel hP y.property]
    have h := congrArg (fun V : Val => V y) (E.VTrel_fix hInt hP)
    simp only at h
    rw [reliefOp_apply] at h
    exact h.symm
  α_opt_top := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    rw [E.joint_T_top_integrand_eq E.VS01_mem _ hx, E.joint_T_top_integrand_eq E.VS01_mem _ hx,
      E.α01_eq hx]
    exact E.zeroLevel_isMaxOn_rel hInt hP hrel.le hx ha

theorem reliefEquilibriumTop_α (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    (hN : E.ZeroSanctionNeutral) {x : ℝ} (hx : x ∈ Sanctions.I) :
    (E.reliefEquilibriumTop hInt hP hrel hN).α x = E.zeroLevel x :=
  E.α01_eq hx

/-- **The realised sanction of the relief equilibrium is zero** at every state. -/
theorem reliefEquilibriumTop_rule_eq_zero (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    (hN : E.ZeroSanctionNeutral) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.dynamicEquilibriumRule (E.reliefEquilibriumTop hInt hP hrel hN) x = 0 := by
  show E.toParams.σ_dyn_top E.VS01 x (E.α01 x) = 0
  rw [← E.response_eq_top E.VS01_mem hx, E.α01_eq hx, E.ρ01_zeroLevel hP hx]

/-! ### On the relief side, defiance is not an equilibrium

The Lipschitz bound it uses, `VTdef_lipschitz`, is stated on `ChordEconomyRelief` above
(renovation item BH3.11(a), 2026-10-06). -/

/-- **On the relief side, defiance is not a Target best reply at the
defiance-profile values**: the deviation to the zero level at `VSstar` is
strictly profitable when `ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K_T)`. -/
theorem defiance_not_maxOn_of_relief_side (hInt : E.Interior) (hP : E.Placable) (hγ : E.β_T *
    E.LloopSharp < 1)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    ¬ IsMaxOn (fun a => E.toParams.joint_T_integrand E.VTdef E.VSstar x a) Sanctions.I 0 := by
  intro hmax
  set a := E.zeroLevelAt E.VSstar x with ha
  have haI := E.zeroLevelAt_mem hP E.VSstar_mem hx
  have h := hmax haI
  simp only [Set.mem_setOf_eq] at h
  rw [joint_T_integrand_eq, joint_T_integrand_eq, E.response_zeroLevelAt hP E.VSstar_mem hx] at h
  set ρ := E.response E.VSstar x 0 with hρdef
  have hρmem := E.response_mem E.VSstar x 0
  -- the zero level is positive: the response at defiance is positive
  have hapos : 0 < a := by
    by_contra hcon
    have ha0 : a = 0 := le_antisymm (not_lt.mp hcon) haI.1
    have := E.response_zeroLevelAt hP E.VSstar_mem hx
    rw [← ha, ha0] at this
    have hpos := E.responsePath_pos E.VSstar_mem hx
    unfold responsePath at hpos
    linarith
  have hρlow := E.response_ge_of_lt_zeroLevelAt hInt hP E.VSstar_mem2 hx le_rfl hapos
  have hF0 : E.F x 0 ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx zero_mem_I
  have hFρ : E.F x ρ ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx hρmem
  have hFmono : E.F x 0 ≤ E.F x ρ := E.F_mono_s x hρmem.1
  have hchord : E.F x ρ - E.F x 0 ≤ E.dhi * (ρ - 0) :=
    E.hShi hx zero_mem_I hρmem hρmem.1
  have hlip := E.VTdef_lipschitz hγ (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
  have hdc : dist (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
      = E.F x ρ - E.F x 0 := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF0,
      Sanctions.clipS'_val_eq_of_mem hFρ, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdc] at hlip
  have hK := E.KT_nonneg hγ
  have hβ := E.hβT0.le
  have hcont : E.β_T * (E.VTdef (Sanctions.clipS' (E.F x ρ))
      - E.VTdef (Sanctions.clipS' (E.F x 0))) ≤ E.β_T * (E.KT * (E.dhi * ρ)) := by
    apply mul_le_mul_of_nonneg_left _ hβ
    have h1 := (le_abs_self _).trans hlip
    have h2 : E.KT * (E.F x ρ - E.F x 0) ≤ E.KT * (E.dhi * ρ) := by
      apply mul_le_mul_of_nonneg_left _ hK; linarith [hchord]
    linarith
  -- the stage: cost at most `ℓ_hi` per unit of compliance, pain at least `p_lo` per unit
  have hstage := E.UT_sub_ge hx zero_mem_I haI hρmem zero_mem_I haI.1 hρmem.1
  set Γ := E.plo - E.β_T * E.dhi * E.KT with hΓ
  have hM := E.Mtot_pos
  have hk := E.hklo
  have hΓpos : 0 < Γ := by
    by_contra hcon
    have : E.klo * Γ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.mp hcon)
    have : 0 < E.ℓhi * E.Mtot := mul_pos E.ℓhi_pos hM
    linarith
  have h1 : E.klo * (a - 0) / E.Mtot * Γ ≤ ρ * Γ := mul_le_mul_of_nonneg_right hρlow hΓpos.le
  have h2 : E.ℓhi * (a - 0) < E.klo * (a - 0) / E.Mtot * Γ := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hM]
    have := mul_lt_mul_of_pos_right hrel (show 0 < a - 0 by linarith)
    nlinarith [this]
  have h' : E.U_T x a 0 + E.β_T * E.VTdef (Sanctions.clipS' (E.F x 0))
      ≤ E.U_T x 0 ρ + E.β_T * E.VTdef (Sanctions.clipS' (E.F x ρ)) := h
  nlinarith [h1, h2, hcont, hstage, h']

/-- **No top-selector equilibrium with full defiance and the defiance-profile
values exists on the relief side.** -/
theorem no_defiance_equilibrium_of_relief_side (hInt : E.Interior) (hP : E.Placable)
    (hγ : E.β_T * E.LloopSharp < 1)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hVS : Eq.V_S = E.VSstar)
    (hVT : Eq.V_T = E.VTdef) : ¬ ∀ x ∈ Sanctions.I, Eq.α x = 0 := by
  intro hα
  have hx : (1/2 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hopt := Eq.α_opt_top (1/2) hx
  rw [hα _ hx, hVS, hVT] at hopt
  have hopt' : IsMaxOn (fun a => E.toParams.joint_T_integrand E.VTdef E.VSstar (1/2) a)
      Sanctions.I 0 := by
    rw [isMaxOn_iff] at hopt ⊢
    intro a ha
    have := hopt a ha
    rwa [E.joint_T_top_integrand_eq E.VSstar_mem _ hx,
      E.joint_T_top_integrand_eq E.VSstar_mem _ hx] at this
  exact E.defiance_not_maxOn_of_relief_side hInt hP hγ hrel hx hopt'

/-! ### The sharp side is disjoint from the second relief side, and the sides collapse to one threshold

(The relief-existence side's disjointness is `bracket_existence_sides_disjoint`, in the
satellites.) -/

/-- `μ ≤ M_tot`: the strong-concavity modulus is at most the curvature ceiling. -/
theorem mu_le_Mtot : E.mu ≤ E.Mtot := by
  have h1 := E.q_le_Mtot
  unfold mu plMu
  have h := mul_nonneg E.hβS0.le (add_nonneg (mul_nonneg E.hSigV0 (sq_nonneg E.dhi))
    (mul_nonneg E.KS_nonneg E.hMs0))
  linarith

/-- **The second relief side excludes the margin**: on the side against the
defiance-profile values (the `K_T` inequality, with the loop condition),
`g_T ≤ K_T`, `d_lo ≤ d_hi` and `p_lo ≤ c` put the margin's continuation above the
pain that side needs. -/
theorem relief_side_imp_not_margin (hγ : E.β_T * E.LloopSharp < 1)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT)) :
    ¬ E.LossOffset := by
  intro hTM
  have h : E.c ≤ E.β_T * E.dlo * E.gT := hTM
  have hgK := E.gT_le_KT hγ
  have hβ := E.hβT0.le
  have h1 : E.β_T * E.dlo * E.gT ≤ E.β_T * E.dhi * E.KT := by
    have := mul_le_mul E.hdlo_dhi hgK E.gT_pos.le E.dhi_nonneg
    nlinarith [this, hβ]
  have h2 : 0 < E.ℓhi * E.Mtot := mul_pos E.ℓhi_pos E.Mtot_pos
  have h3 := E.plo_le_c
  have hk := E.hklo
  have h4 : E.plo - E.β_T * E.dhi * E.KT ≤ 0 := by linarith
  have := mul_nonpos_of_nonneg_of_nonpos hk.le h4
  linarith

/-- **The sharp side and the second relief side cannot both hold**: the sharp
defiance side at `g_T` and the relief side against the defiance-profile values
(the `K_T` inequality, with the loop condition) are disjoint, because
`μ ≤ M_tot`, `ℓ_lo ≤ ℓ_hi`, `k_lo ≤ k_hi`, `p_lo ≤ c`, `d_lo ≤ d_hi` and
`g_T ≤ K_T`. The relief-existence side (the `K_T^rel` inequality) is covered by
`bracket_existence_sides_disjoint`, whose proof does not go through a comparison
of `g_T` with `K_T^rel` (none is proved). -/
theorem bracket_sides_disjoint (hγ : E.β_T * E.LloopSharp < 1)
    (hsharp : E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT)) : False := by
  have hgK := E.gT_le_KT hγ
  have hβ := E.hβT0.le
  set B := E.β_T * E.dhi * E.KT with hB
  have h1 : E.β_T * E.dlo * E.gT ≤ B := by
    have := mul_le_mul E.hdlo_dhi hgK E.gT_pos.le E.dhi_nonneg
    rw [hB]; nlinarith [this, hβ]
  have hk := E.hklo
  have hkh := E.khi_pos
  have hμ := E.mu_pos
  have hM := E.Mtot_pos
  -- the relief side: `ℓ_hi·M_tot/k_lo < p_lo − B`
  have hY : E.ℓhi * E.Mtot / E.klo < E.plo - B := by
    rw [div_lt_iff₀ hk]; linarith
  -- `ℓ_lo·μ/k_hi ≤ ℓ_hi·M_tot/k_lo`
  have hXY : E.ℓlo * E.mu / E.khi ≤ E.ℓhi * E.Mtot / E.klo := by
    rw [div_le_div_iff₀ hkh hk]
    have e1 : E.ℓlo * E.mu ≤ E.ℓhi * E.Mtot :=
      mul_le_mul E.ℓlo_le_ℓhi E.mu_le_Mtot hμ.le E.ℓhi_pos.le
    have e2 : E.klo ≤ E.khi := E.klo_le_khi
    have e3 : 0 ≤ E.ℓlo * E.mu := mul_nonneg E.hℓlo.le hμ.le
    calc E.ℓlo * E.mu * E.klo ≤ E.ℓlo * E.mu * E.khi := mul_le_mul_of_nonneg_left e2 e3
      _ ≤ E.ℓhi * E.Mtot * E.khi := mul_le_mul_of_nonneg_right e1 hkh.le
  have hpc := E.plo_le_c
  linarith

/-- At tight state and sanction curvature (`σ_V = 0`, `M_s = 0`) the
strong-concavity modulus is `q`. -/
theorem collapse_mu (hSigV : E.SigV = 0) (hMs : E.Ms = 0) : E.mu = E.q := by
  unfold mu plMu; rw [hSigV, hMs]; ring

theorem collapse_SigC (hτ : E.τx = 0) (hMcx : E.Mcx = 0) : E.SigC = 0 := by
  unfold SigC chSigC; rw [hτ, hMcx]; simp

theorem collapse_Mtot (hQ : E.Qbar = E.q) (hτ : E.τx = 0) (hMcx : E.Mcx = 0)
    (hMcs : E.Mcs = 0) : E.Mtot = E.q := by
  unfold Mtot
  rw [E.collapse_SigC hτ hMcx, hMcs, hQ]; ring

/-- **`L_resp = 0` at the collapse**: with `r_hi`, `σ_V`, `τ_x`, `M_cx` and `M_mix` zero,
every term of the response's state-Lipschitz constant vanishes. **Rule 22: AFFINE BY
HYPOTHESIS** (renovation item BG3.4, 2026-10-06; it was read as general in `F`): a zero
response slope forces the affine law `F = affineF (1 − F(1,0))` on the unit square
(`ChordEconomyRelief.F_eq_affineF_of_Lresp_eq_zero`). -/
theorem collapse_Lresp (hr : E.rhi = 0) (hSigV : E.SigV = 0) (hτ : E.τx = 0)
    (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) : E.Lresp = 0 := by
  unfold Lresp plLresp
  rw [hr, hSigV, E.collapse_SigC hτ hMcx, hMmix]; simp

theorem collapse_KTrel (hr : E.rhi = 0) (hSigV : E.SigV = 0) (hτ : E.τx = 0)
    (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) (hv : E.vlo = E.vhi) (hnlo : E.nlo = 0)
    (hg : E.glo = E.ghi) : E.KTrel = E.gT := by
  have hL := E.collapse_Lresp hr hSigV hτ hMcx hMmix
  unfold KTrel Lalpha gT
  rw [hL, hnlo, hg, hv]; ring

theorem collapse_KT (hr : E.rhi = 0) (hSigV : E.SigV = 0) (hτ : E.τx = 0)
    (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) (hv : E.vlo = E.vhi) (hnlo : E.nlo = 0)
    (hnhi : E.nhi = 0) (hg : E.glo = E.ghi) : E.KT = E.gT := by
  have hL := E.collapse_Lresp hr hSigV hτ hMcx hMmix
  unfold KT LUT LloopSharp gT
  rw [hL, hnlo, hnhi, hg, hv]
  simp only [add_zero, max_self, zero_div, mul_zero, zero_mul]

/-- **The collapse**: under sixteen tightness equalities — nine zeros (`r_hi`,
`σ_V`, `M_s`, `τ_x`, `M_cx`, `M_cs`, `M_mix`, `n_lo`, `n_hi`) and seven pair
equalities (`Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`, `v_lo = v_hi`,
`g_lo = g_hi`, `d_lo = d_hi`) — the sharp defiance side at `g_T` reads
`D < β_T δ g_T` and both relief sides read `β_T δ g_T < D`, with
`D = c − ℓ_lo q/k_hi` and `δ = d_lo`: one threshold, as the point where the
general bracket closes. The Sender's `w` and `u` pairs need not be tight. A
conditional equivalence: it does not say the equalities are necessary for the
window to close, and the strict inequalities do not decide the equality case.
**Rule 22: affine-restricted by its hypotheses.** The tight chords
`g_lo = g_hi` and `d_lo = d_hi`, with `F_diag`, pin `F = affineF d_lo` on the
square; the theorem is the affine collapse of the general bracket, stated over
the general class. -/
theorem collapse_sides (hr : E.rhi = 0) (hSigV : E.SigV = 0) (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnlo : E.nlo = 0) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi)
    (hd : E.dlo = E.dhi) :
    ((E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT)
        ↔ (E.c - E.ℓlo * E.q / E.khi < E.β_T * E.dlo * E.gT))
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
        ↔ (E.β_T * E.dlo * E.gT < E.c - E.ℓlo * E.q / E.khi))
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
        ↔ (E.β_T * E.dlo * E.gT < E.c - E.ℓlo * E.q / E.khi)) := by
  have hμ := E.collapse_mu hSigV hMs
  have hM := E.collapse_Mtot hQ hτ hMcx hMcs
  have hKr := E.collapse_KTrel hr hSigV hτ hMcx hMmix hv hnlo hg
  have hK := E.collapse_KT hr hSigV hτ hMcx hMmix hv hnlo hnhi hg
  have hkh := E.khi_pos
  refine ⟨by rw [hμ], ?_, ?_⟩
  · rw [hM, hKr, hp, ← hd, hk, ← hℓ]
    constructor
    · intro h
      have : E.ℓlo * E.q / E.khi < E.c - E.β_T * E.dlo * E.gT := by
        rw [div_lt_iff₀ hkh]; linarith
      linarith
    · intro h
      have : E.ℓlo * E.q / E.khi < E.c - E.β_T * E.dlo * E.gT := by linarith
      rw [div_lt_iff₀ hkh] at this; linarith
  · rw [hM, hK, hp, ← hd, hk, ← hℓ]
    constructor
    · intro h
      have : E.ℓlo * E.q / E.khi < E.c - E.β_T * E.dlo * E.gT := by
        rw [div_lt_iff₀ hkh]; linarith
      linarith
    · intro h
      have : E.ℓlo * E.q / E.khi < E.c - E.β_T * E.dlo * E.gT := by linarith
      rw [div_lt_iff₀ hkh] at this; linarith

/-! ### The sides are monotone in the Target's discount factor

Each side is an inequality between a constant and a quantity that rises with
`β_T` through `g_T`, `K_T^rel` or `K_T`, the other data held fixed; for `K_T` only
while the loop condition `β_T L_loop < 1` holds, which `relief_side_notdef_anti_βT`
takes at the more patient member. Stated for two economies that differ only in
`β_T`. -/

/-- Two enriched chord economies that differ only in the Target's discount
factor: the same payoffs, selector and transition, and the same rate bounds. -/
def SameButβT (E₁ E₂ : ChordEconomyCs) : Prop :=
  E₁.U_S = E₂.U_S ∧ E₁.U_T = E₂.U_T ∧ E₁.σ = E₂.σ ∧ E₁.F = E₂.F ∧
  E₁.glo = E₂.glo ∧ E₁.ghi = E₂.ghi ∧ E₁.dlo = E₂.dlo ∧ E₁.dhi = E₂.dhi ∧
  E₁.Mx = E₂.Mx ∧ E₁.Mm = E₂.Mm ∧ E₁.Ms = E₂.Ms ∧ E₁.Mcx = E₂.Mcx ∧ E₁.Mmix = E₂.Mmix ∧
  E₁.Mcs = E₂.Mcs ∧ E₁.β_S = E₂.β_S ∧ E₁.q = E₂.q ∧ E₁.Qbar = E₂.Qbar ∧ E₁.whi = E₂.whi ∧
  E₁.τx = E₂.τx ∧ E₁.rhi = E₂.rhi ∧ E₁.klo = E₂.klo ∧ E₁.ℓhi = E₂.ℓhi ∧ E₁.ℓlo = E₂.ℓlo ∧
  E₁.khi = E₂.khi ∧ E₁.c = E₂.c ∧ E₁.plo = E₂.plo ∧ E₁.vlo = E₂.vlo ∧ E₁.nlo = E₂.nlo ∧
  E₁.vhi = E₂.vhi ∧ E₁.nhi = E₂.nhi ∧ E₁.SigV = E₂.SigV

theorem SameButβT.consts {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂) :
    E₁.KS = E₂.KS ∧ E₁.mu = E₂.mu ∧ E₁.SigC = E₂.SigC ∧ E₁.Lresp = E₂.Lresp ∧
    E₁.Mtot = E₂.Mtot ∧ E₁.LloopSharp = E₂.LloopSharp ∧ E₁.LUT = E₂.LUT ∧
    E₁.Lalpha = E₂.Lalpha ∧ E₁.sfloor = E₂.sfloor := by
  obtain ⟨-, -, hσ, -, hglo, hghi, hdlo, hdhi, hMx, hMm, hMs, hMcx, hMmix, hMcs, hβS, hq, hQ,
    hwhi, hτ, hr, hk, hℓ, hℓlo, hkhi, hc, hp, hvlo, hnlo, hvhi, hnhi, hSigV⟩ := h
  have hKS : E₁.KS = E₂.KS := by unfold KS chKS; rw [hβS, hghi, hwhi]
  have hmu : E₁.mu = E₂.mu := by unfold mu plMu; rw [hβS, hq, hSigV, hdhi, hKS, hMs]
  have hSigC : E₁.SigC = E₂.SigC := by unfold SigC chSigC; rw [hβS, hτ, hKS, hMcx, hghi]
  have hL : E₁.Lresp = E₂.Lresp := by
    unfold Lresp plLresp; rw [hr, hβS, hSigV, hSigC, hghi, hdhi, hKS, hMmix]
  have hM : E₁.Mtot = E₂.Mtot := by unfold Mtot; rw [hQ, hβS, hSigC, hdhi, hKS, hMcs]
  have hLoop : E₁.LloopSharp = E₂.LloopSharp := by unfold LloopSharp; rw [hghi, hdhi, hL, hmu]
  have hLU : E₁.LUT = E₂.LUT := by unfold LUT; rw [hvhi, hnhi, hc, hL, hmu]
  have hLa : E₁.Lalpha = E₂.Lalpha := by unfold Lalpha; rw [hM, hL, hk, hmu]
  have hsf : E₁.sfloor = E₂.sfloor := by unfold sfloor; rw [hσ]
  exact ⟨hKS, hmu, hSigC, hL, hM, hLoop, hLU, hLa, hsf⟩

/-- `g_T` rises with `β_T`. -/
theorem SameButβT.gT_le {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T) : E₁.gT ≤ E₂.gT := by
  have hc := h.consts
  obtain ⟨-, -, -, -, hglo, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hvlo, hnlo, -, -, -⟩ := h
  unfold gT
  rw [hglo, hvlo, hnlo, hc.2.2.2.2.2.2.2.2]
  have h1 := E₂.βT_glo_lt_one
  have hnum : 0 ≤ E₂.vlo + E₂.nlo * E₂.sfloor :=
    add_nonneg E₂.hvlo.le (mul_nonneg E₂.hnlo E₂.sfloor_mem.1)
  have h2 : E₁.β_T * E₂.glo ≤ E₂.β_T * E₂.glo := mul_le_mul_of_nonneg_right hβ E₂.hglo0
  apply div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

/-- `K_T^rel` rises with `β_T`. -/
theorem SameButβT.KTrel_le {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T) : E₁.KTrel ≤ E₂.KTrel := by
  have hc := h.consts
  obtain ⟨-, -, -, -, -, hghi, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hℓ, -, -, -, -,
    -, -, hvhi, -, -⟩ := h
  unfold KTrel
  rw [hghi, hℓ, hvhi, hc.2.2.2.2.2.2.2.1]
  have h1 := E₂.βT_ghi_lt_one
  have hnum : 0 ≤ E₂.vhi + E₂.ℓhi * E₂.Lalpha :=
    add_nonneg E₂.vhi_pos.le (mul_nonneg E₂.ℓhi_pos.le E₂.Lalpha_nonneg)
  have h2 : E₁.β_T * E₂.ghi ≤ E₂.β_T * E₂.ghi := mul_le_mul_of_nonneg_right hβ E₂.ghi_nonneg
  apply div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

/-- `K_T` rises with `β_T` (where both are defined). -/
theorem SameButβT.KT_le {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T) (hγ₂ : E₂.β_T * E₂.LloopSharp < 1) : E₁.KT ≤ E₂.KT := by
  have hc := h.consts
  unfold KT
  rw [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]
  have hnum : 0 ≤ E₂.LUT := E₂.LUT_nonneg
  have h2 : E₁.β_T * E₂.LloopSharp ≤ E₂.β_T * E₂.LloopSharp :=
    mul_le_mul_of_nonneg_right hβ E₂.LloopSharp_nonneg
  apply div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

/-- **The sharp defiance side at `g_T` is inherited by a more patient Target.** -/
theorem sharp_side_mono_βT {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T)
    (hsharp : E₁.c - E₁.ℓlo * E₁.mu / E₁.khi < E₁.β_T * E₁.dlo * E₁.gT) :
    E₂.c - E₂.ℓlo * E₂.mu / E₂.khi < E₂.β_T * E₂.dlo * E₂.gT := by
  have hc := h.consts
  have hg := h.gT_le hβ
  obtain ⟨-, -, -, -, -, -, hdlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hℓlo, hkhi, hcc,
    -, -, -, -, -, -⟩ := h
  rw [hcc, hℓlo, hc.2.1, hkhi, hdlo] at hsharp
  have h1 : E₁.β_T * E₂.dlo * E₁.gT ≤ E₂.β_T * E₂.dlo * E₂.gT :=
    mul_le_mul (mul_le_mul_of_nonneg_right hβ E₂.hdlo0.le) hg E₁.gT_pos.le
      (mul_nonneg E₂.hβT0.le E₂.hdlo0.le)
  linarith

/-- **The relief-existence side (`K_T^rel`) is inherited by a less patient
Target.** The second relief side is `relief_side_notdef_anti_βT`, under the loop
condition. -/
theorem relief_side_anti_βT {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T)
    (hrel : E₂.ℓhi * E₂.Mtot < E₂.klo * (E₂.plo - E₂.β_T * E₂.dhi * E₂.KTrel)) :
    E₁.ℓhi * E₁.Mtot < E₁.klo * (E₁.plo - E₁.β_T * E₁.dhi * E₁.KTrel) := by
  have hc := h.consts
  have hK := h.KTrel_le hβ
  obtain ⟨-, -, -, -, -, -, -, hdhi, -, -, -, -, -, -, -, -, -, -, -, -, hk, hℓ, -, -, -, hp,
    -, -, -, -, -⟩ := h
  rw [hℓ, hc.2.2.2.2.1, hk, hp, hdhi]
  have h1 : E₁.β_T * E₂.dhi * E₁.KTrel ≤ E₂.β_T * E₂.dhi * E₂.KTrel :=
    mul_le_mul (mul_le_mul_of_nonneg_right hβ E₂.dhi_nonneg) hK E₁.KTrel_nonneg
      (mul_nonneg E₂.hβT0.le E₂.dhi_nonneg)
  have h2 := mul_le_mul_of_nonneg_left h1 E₂.hklo.le
  linarith

theorem relief_side_notdef_anti_βT {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T) (hγ₂ : E₂.β_T * E₂.LloopSharp < 1)
    (hrel : E₂.ℓhi * E₂.Mtot < E₂.klo * (E₂.plo - E₂.β_T * E₂.dhi * E₂.KT)) :
    E₁.ℓhi * E₁.Mtot < E₁.klo * (E₁.plo - E₁.β_T * E₁.dhi * E₁.KT) := by
  have hc := h.consts
  have hK := h.KT_le hβ hγ₂
  have hγ₁ : E₁.β_T * E₁.LloopSharp < 1 := by
    rw [hc.2.2.2.2.2.1]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hβ E₂.LloopSharp_nonneg) hγ₂
  obtain ⟨-, -, -, -, -, -, -, hdhi, -, -, -, -, -, -, -, -, -, -, -, -, hk, hℓ, -, -, -, hp,
    -, -, -, -, -⟩ := h
  rw [hℓ, hc.2.2.2.2.1, hk, hp, hdhi]
  have h1 : E₁.β_T * E₂.dhi * E₁.KT ≤ E₂.β_T * E₂.dhi * E₂.KT :=
    mul_le_mul (mul_le_mul_of_nonneg_right hβ E₂.dhi_nonneg) hK (E₁.KT_nonneg hγ₁)
      (mul_nonneg E₂.hβT0.le E₂.dhi_nonneg)
  have h2 := mul_le_mul_of_nonneg_left h1 E₂.hklo.le
  linarith

end ChordEconomyCs

end

end Examples
end Sanctions
