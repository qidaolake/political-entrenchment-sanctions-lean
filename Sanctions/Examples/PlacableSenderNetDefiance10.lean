/-
Sanctions/Examples/PlacableSenderNetDefiance10.lean

**The Target-only reading and the four cases under the net-of-compliance condition**
(step 2, target 2a, 2026-10-10; referee M1, fix 1).

In the Target-only reading `10` the Sender is myopic, so it answers compliance through the
stage selector `σ(x, a)`, not through the forward-looking response. The net condition of
the forward-looking reading (ND, `PlacableSenderNetDefiance.lean`) prices relief at the
dynamic curvature `μ`; the stage selector moves with the stage curvature `q`:

* **the stage relief rate**: between two compliance levels the stage sanction falls by at
  most `k_hi·Δa/q` (`stage_σ_sub_le_of_le`): the Sender's stage payoff is `q`-strongly
  concave in the sanction and a unit of compliance perturbs it with cross rate at most `k_hi`;
* **the stage state rate**: the stage sanction moves with the state at rate at most
  `r_hi/q` (`stageResp_dist_le`), from the cross-rate ceiling S9 at defiance.

**The stage net condition ND10** (`NetDefianceStageAt`; an internal helper only, since the
author withdrew approved hypothesis 1 on 2026-10-12: no paper-facing theorem takes it as a
hypothesis, every one takes ND, which implies it): a slope `g ≥ 0` with `c − ℓ_lo·q/k_hi ≤ β_T·d_lo·g` and the stage balance
`g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·r_hi/q ≤ v_lo + n_lo·b`. Against a myopic Sender a
unit of compliance removes at most `k_hi/q` units of sanction, so defiance is optimal when the
net pain is at most `ℓ_lo·q/k_hi` per unit. The curvature here must be the strong-concavity
bound `q`; the ceiling `Q̄` would overstate the cost of relief and be unsound. Under ND10 the
Target-only value `VT10def` carries the slope `g` (`VT10def_lowerSlope`), full defiance is a
best reply against the stage selector (`defianceBestReply10_of_netDefianceStage`), and the
Target-only full-defiance equilibrium exists (`targetOnlyDefianceEquilibrium`).

**ND implies ND10** (`netDefianceStageAt_of_netDefianceAt`): `μ ≤ q` (`mu_le_q`) and
`r_hi/q ≤ L_resp/μ` (`rhi_div_q_le_Lresp_div_mu`). So the four-case theorem holds under ND
alone, with no new hypothesis (`four_cell_net`).

Uniqueness of the Target's best reply uses the strict forms (approved hypothesis 2).
Nothing here says the full-defiance equilibrium is the unique equilibrium.

Rule 3: approved hypothesis 2 only (strict forms, uniqueness clauses only); the stage
condition ND10 is derived from ND and is not a hypothesis of any paper-facing theorem.
Rule 22: general in `F`. Rule 9: witnesses in `PlacableSenderNetDefianceWitnesses.lean`.
-/
import Sanctions.Examples.PlacableSenderNetDefiance

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.GeometricApproach
  Sanctions.Mechanism Sanctions.Semiconcave

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. The stage relief rate and the Target-only value at defiance -/

/-- **The stage relief rate is at most `k_hi/q`**: between two compliance levels the stage
sanction falls by at most `k_hi·Δa/q`. The stage payoff is `q`-strongly concave in the
sanction (S4) and a unit of compliance perturbs it with cross rate at most `k_hi` (the
placation ceiling `hPC`).
Scope: general class. -/
theorem stage_σ_sub_le_of_le {khi : ℝ} (hPC : E.PlacationCeiling khi) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) {a a' : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (ha' : a' ∈ Icc (0 : ℝ) 1)
    (haa' : a ≤ a') :
    E.σ x a - E.σ x a' ≤ khi * (a' - a) / E.q := by
  have hf := E.hUS_concave x hx a
  have hpert : ∀ u ∈ Sanctions.I, ∀ w ∈ Sanctions.I,
      |(E.U_S x a' u - E.U_S x a u) - (E.U_S x a' w - E.U_S x a w)|
        ≤ (khi * (a' - a)) * |u - w| := by
    intro u hu w hw
    have hid : (E.U_S x a' u - E.U_S x a u) - (E.U_S x a' w - E.U_S x a w)
        = (E.U_S x a' u - E.U_S x a' w) - (E.U_S x a u - E.U_S x a w) := by ring
    rw [hid]
    have h := hPC x hx a ha a' ha' w hw u hu haa'
    calc |(E.U_S x a' u - E.U_S x a' w) - (E.U_S x a u - E.U_S x a w)|
        ≤ khi * ((a' - a) * |u - w|) := h
      _ = (khi * (a' - a)) * |u - w| := by ring
  have h := argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp
    (f := fun s => E.U_S x a s) (g := fun s => E.U_S x a' s) (convex_Icc 0 1)
    E.hq (mul_nonneg (E.khi_pos hPC).le (by linarith)) hf hpert
    (E.σ_mem x a) (E.σ_mem x a') (E.σ_isMaxOn_U_S x a) (E.σ_isMaxOn_U_S x a')
  exact (le_abs_self _).trans h

/-- **Complying never pays against the stage selector under the stage net side**
`c − ℓ_lo·q/k_hi ≤ β_T·d_lo·g`, at any Target value of lower state slope `g ≥ 0`: the
Target-only objective is nonincreasing in compliance.
Scope: general class. -/
theorem targetObj10_antitoneOn_of_net {khi : ℝ} (hPC : E.PlacationCeiling khi) {g : ℝ}
    (hg : 0 ≤ g) (hnet : E.c - E.ℓlo * E.q / khi ≤ E.β_T * E.dlo * g)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    AntitoneOn (fun a => E.targetObj10 V_T x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hle
  change E.targetObj10 V_T x a₂ ≤ E.targetObj10 V_T x a₁
  unfold targetObj10
  have hρ : E.σ x a₂ ≤ E.σ x a₁ := E.stage_σ_antitoneOn hx ha₁ ha₂ hle
  have hρ₁ := E.σ_mem x a₁
  have hρ₂ := E.σ_mem x a₂
  have hΔ : E.σ x a₁ - E.σ x a₂ ≤ khi * (a₂ - a₁) / E.q :=
    E.stage_σ_sub_le_of_le hPC hx ha₁ ha₂ hle
  have hz : E.F x (E.σ x a₂) ≤ E.F x (E.σ x a₁) := E.F_mono_s x hρ
  have hchord : E.dlo * (E.σ x a₁ - E.σ x a₂) ≤ E.F x (E.σ x a₁) - E.F x (E.σ x a₂) :=
    E.hSlo hx hρ₂ hρ₁ hρ
  have hslope := E.clip_lowerSlope_of hV_T _ (E.F_mem _ _ hx hρ₂) _ (E.F_mem _ _ hx hρ₁) hz
  have hA : E.β_T * (V_T (Sanctions.clipS' (E.F x (E.σ x a₂)))
        - V_T (Sanctions.clipS' (E.F x (E.σ x a₁))))
      ≤ -(E.β_T * E.dlo * g) * (E.σ x a₁ - E.σ x a₂) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg E.hβT0.le hg)
    have h2 := mul_le_mul_of_nonneg_left hslope E.hβT0.le
    nlinarith [h1, h2]
  have hU := E.UT_sub_le hx ha₁ ha₂ hρ₁ hρ₂ hle hρ
  set θ := E.c - E.β_T * E.dlo * g with hθ
  have hq := E.hq
  have hk := E.khi_pos hPC
  have hθk : θ * khi ≤ E.ℓlo * E.q := by
    have h2 : E.ℓlo * E.q / khi * khi = E.ℓlo * E.q := div_mul_cancel₀ _ hk.ne'
    nlinarith [hnet, h2]
  have hB : (E.σ x a₁ - E.σ x a₂) * θ ≤ E.ℓlo * (a₂ - a₁) := by
    rcases le_or_gt θ 0 with hθ0 | hθ0
    · have : (E.σ x a₁ - E.σ x a₂) * θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) hθ0
      have : 0 ≤ E.ℓlo * (a₂ - a₁) := mul_nonneg E.hℓlo.le (by linarith)
      linarith
    · have h1 : (E.σ x a₁ - E.σ x a₂) * θ ≤ khi * (a₂ - a₁) / E.q * θ :=
        mul_le_mul_of_nonneg_right hΔ hθ0.le
      have h2 : khi * (a₂ - a₁) / E.q * θ ≤ E.ℓlo * (a₂ - a₁) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hq]
        have := mul_le_mul_of_nonneg_right hθk (show 0 ≤ a₂ - a₁ by linarith)
        nlinarith [this]
      linarith
  nlinarith [hA, hB, hU]

/-- **Defiance is the strict unique optimum against the stage selector under the strict
stage net side** `c − ℓ_lo·q/k_hi < β_T·d_lo·g`.
Scope: general class; approved hypothesis 2 (strict form, uniqueness clause only). -/
theorem targetObj10_strictAntiOn_of_net {khi : ℝ} (hPC : E.PlacationCeiling khi) {g : ℝ}
    (hg : 0 ≤ g) (hnet : E.c - E.ℓlo * E.q / khi < E.β_T * E.dlo * g)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    StrictAntiOn (fun a => E.targetObj10 V_T x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hlt
  change E.targetObj10 V_T x a₂ < E.targetObj10 V_T x a₁
  unfold targetObj10
  have hρ : E.σ x a₂ ≤ E.σ x a₁ := E.stage_σ_antitoneOn hx ha₁ ha₂ hlt.le
  have hρ₁ := E.σ_mem x a₁
  have hρ₂ := E.σ_mem x a₂
  have hΔ : E.σ x a₁ - E.σ x a₂ ≤ khi * (a₂ - a₁) / E.q :=
    E.stage_σ_sub_le_of_le hPC hx ha₁ ha₂ hlt.le
  have hz : E.F x (E.σ x a₂) ≤ E.F x (E.σ x a₁) := E.F_mono_s x hρ
  have hchord : E.dlo * (E.σ x a₁ - E.σ x a₂) ≤ E.F x (E.σ x a₁) - E.F x (E.σ x a₂) :=
    E.hSlo hx hρ₂ hρ₁ hρ
  have hslope := E.clip_lowerSlope_of hV_T _ (E.F_mem _ _ hx hρ₂) _ (E.F_mem _ _ hx hρ₁) hz
  have hA : E.β_T * (V_T (Sanctions.clipS' (E.F x (E.σ x a₂)))
        - V_T (Sanctions.clipS' (E.F x (E.σ x a₁))))
      ≤ -(E.β_T * E.dlo * g) * (E.σ x a₁ - E.σ x a₂) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg E.hβT0.le hg)
    have h2 := mul_le_mul_of_nonneg_left hslope E.hβT0.le
    nlinarith [h1, h2]
  have hU := E.UT_sub_le hx ha₁ ha₂ hρ₁ hρ₂ hlt.le hρ
  set θ := E.c - E.β_T * E.dlo * g with hθ
  have hq := E.hq
  have hk := E.khi_pos hPC
  have hθk : θ * khi < E.ℓlo * E.q := by
    have h2 : E.ℓlo * E.q / khi * khi = E.ℓlo * E.q := div_mul_cancel₀ _ hk.ne'
    nlinarith [hnet, h2]
  have hB : (E.σ x a₁ - E.σ x a₂) * θ < E.ℓlo * (a₂ - a₁) := by
    rcases le_or_gt θ 0 with hθ0 | hθ0
    · have : (E.σ x a₁ - E.σ x a₂) * θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) hθ0
      have : 0 < E.ℓlo * (a₂ - a₁) := mul_pos E.hℓlo (by linarith)
      linarith
    · have h1 : (E.σ x a₁ - E.σ x a₂) * θ ≤ khi * (a₂ - a₁) / E.q * θ :=
        mul_le_mul_of_nonneg_right hΔ hθ0.le
      have h2 : khi * (a₂ - a₁) / E.q * θ < E.ℓlo * (a₂ - a₁) := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hq]
        have := mul_lt_mul_of_pos_right hθk (show 0 < a₂ - a₁ by linarith)
        nlinarith [this]
      linarith
  nlinarith [hA, hB, hU]

/-- **The Target's value at full defiance in the Target-only reading**: the fixed point of
the Target operator against the stage selector on the whole value space (a contraction,
`targetOp10_contracting`); equal to the carrier-constructed `VT10` whenever that exists
(`VT10def_eq_VT10`).
Scope: general class. -/
def VT10def : Val := E.targetOp10_contracting.fixedPoint

/-- `VT10def` is a fixed point of the Target-only operator.
Scope: general class. -/
theorem VT10def_fix : E.targetOp10 E.VT10def = E.VT10def :=
  E.targetOp10_contracting.fixedPoint_isFixedPt

/-- `VT10def` is the loss-offset construction `VT10` whenever the latter exists.
Scope: general class. -/
theorem VT10def_eq_VT10 (hTM : E.LossOffset) : E.VT10def = E.VT10 hTM :=
  (E.targetOp10_contracting.fixedPoint_unique (E.VT10_fix hTM)).symm

/-- **Full defiance is a Target best reply in the Target-only reading**: at every feasible
state, compliance `0` maximises the Target's forward-looking objective against the stage
selector at the value `VT10def`. Written over the constructed value (Rule 14).
Scope: general class. -/
def DefianceBestReply10 : Prop :=
  ∀ x ∈ Sanctions.I, IsMaxOn (fun a => E.targetObj10 E.VT10def x a) Sanctions.I 0

/-- **The Target-only full-defiance equilibrium, built from the best-reply test**: Sender at
its stage value, Target at `VT10def`, policy full defiance. The construction of
`targetOnlyEquilibriumTop` with the best-reply property in place of the loss-offset
condition. Rule 15: constructed.
Scope: general class. -/
def targetOnlyDefianceEquilibrium (h : E.DefianceBestReply10) :
    E.toParams.RegimeEquilibrium ContinuationProfile.p10 where
  V_T := E.VT10def
  V_S := E.VS10
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_refl 0, zero_le_one⟩
  V_S_fix := by
    ext y
    change E.VS10 y = sSup ((fun s => E.pT.integrandS (fun _ => 0) (fun z => E.VS10 z)
      (y.val, s)) '' Sanctions.I)
    have hgt : IsGreatest ((fun s => E.pT.integrandS (fun _ => 0) (fun z => E.VS10 z)
        (y.val, s)) '' Sanctions.I)
        (E.toParams.U_S y.val 0 (E.toParams.σ y.val 0)) := by
      refine ⟨⟨_, E.toParams.σ_mem y.val 0, E.pT_integrandS _ _ _⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [E.pT_integrandS]
      exact E.toParams.σ_isMaxOn_U_S y.val 0 hs
    rw [hgt.csSup_eq]
    rfl
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => E.pT.joint_T_top_integrand E.VT10def E.VS10 y.val a)
        '' Sanctions.I)
        (E.pT.joint_T_top_integrand E.VT10def E.VS10 y.val 0) := by
      refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.pT_joint_T_top_integrand _ _ y.property, E.pT_joint_T_top_integrand _ _ y.property]
      exact h y.val y.property ha
    rw [hgt.csSup_eq, E.pT_joint_T_top_integrand _ _ y.property]
    have hfix := congrArg (fun V : Val => V y) E.VT10def_fix
    simp only at hfix
    rw [targetOp10_apply] at hfix
    exact hfix.symm
  α_opt_top := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    rw [E.pT_joint_T_top_integrand _ _ hx, E.pT_joint_T_top_integrand _ _ hx]
    exact h x hx ha

/-- The state path of `targetOnlyDefianceEquilibrium h`.
Scope: general class. -/
def targetOnlyDefiancePath (h : E.DefianceBestReply10) (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.rulePathF (E.pT.dynamicEquilibriumRule (E.targetOnlyDefianceEquilibrium h)) x₀ t

/-- **Every full-defiance equilibrium of the Target-only reading has the value `VT10def`
and the stage selector as its rule.** The Target's value at its own policy is the Target-only
operator applied to it (`V_T_eq_at_policy`), and that operator contracts. No defiance
condition.
Scope: general class. -/
theorem values10_eq_of_policy_zero (Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    Eq.V_T = E.VT10def ∧ ∀ x ∈ Sanctions.I, E.pT.dynamicEquilibriumRule Eq x = E.σ x 0 := by
  refine ⟨?_, fun x hx => E.pT_rule_eq_stage_of_policy_zero Eq hα hx⟩
  have hfix : E.targetOp10 Eq.V_T = Eq.V_T := by
    ext y
    have hy := Params.FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy (p := E.pT) Eq y
    rw [hα y.val y.property, E.pT_joint_T_top_integrand _ _ y.property] at hy
    rw [targetOp10_apply, hy]
    rfl
  exact E.targetOp10_contracting.fixedPoint_unique hfix

/-- **A full-defiance equilibrium of the Target-only reading exists if and only if full
defiance is a Target best reply against the stage selector at `VT10def`.** General in `F`;
no hypothesis beyond the class.
Scope: general class. -/
theorem exists_targetOnly_defiance_equilibrium_iff :
    (∃ Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ↔ E.DefianceBestReply10 := by
  constructor
  · rintro ⟨Eq, hα⟩ x hx
    have hVT := (E.values10_eq_of_policy_zero Eq hα).1
    have h := Eq.α_opt_top x hx
    rw [hα x hx, hVT] at h
    rw [isMaxOn_iff] at h ⊢
    intro a ha
    have h' := h a ha
    rwa [E.pT_joint_T_top_integrand _ _ hx, E.pT_joint_T_top_integrand _ _ hx] at h'
  · intro h
    exact ⟨E.targetOnlyDefianceEquilibrium h, fun _ _ => rfl⟩

/-- **The dynamic curvature is at most the stage curvature**, `μ ≤ q`: the continuation
only adds sanction curvature `β_S(σ_V d_hi² + K_S M_s) ≥ 0`.
Scope: general class. -/
theorem mu_le_q : E.mu ≤ E.q := by
  unfold mu plMu
  have h1 : 0 ≤ E.SigV * E.dhi ^ 2 := mul_nonneg E.hSigV0 (sq_nonneg _)
  have h2 : 0 ≤ E.KS * E.Ms := mul_nonneg E.KS_nonneg E.hMs0
  have := mul_nonneg E.hβS0.le (add_nonneg h1 h2)
  linarith

/-! ## 2. Entrenchment at every pair of full-defiance equilibria -/

/-- **The two forward-looking-Target cells at every pair of full-defiance equilibria**: from
every feasible start the Target-only path converges to a positive fixed point `z₁₀` of the
stage selector and the forward-looking path to a fixed point `z` of the response, with
`0 < z₁₀ < z`. Under the stage appetite and a nondecreasing response; no defiance condition.
Scope: general class. -/
theorem limits_of_policy_zero (hS : E.uhi < E.q)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (Eq₁₀ : E.toParams.RegimeEquilibrium ContinuationProfile.p10)
    (hα₁₀ : ∀ x ∈ Sanctions.I, Eq₁₀.α x = 0)
    (Eq₁₁ : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hα₁₁ : ∀ x ∈ Sanctions.I, Eq₁₁.α x = 0) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto (E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq₁₀) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq₁₁) x₀) atTop
        (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hlt, ht₁₀, ht⟩ :=
    E.stagePath_limit_lt_fullDefiancePath_limit hS hmono hx₀
  have hf₁₀ : E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq₁₀) x₀ = E.stagePath x₀ :=
    funext (E.pT_rulePath_eq_stagePath_of_policy_zero Eq₁₀ hα₁₀ hx₀)
  have hf₁₁ : E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq₁₁) x₀
      = E.fullDefiancePath x₀ :=
    funext (E.rulePath_eq_fullDefiancePath_of_policy_zero Eq₁₁ hα₁₁ hx₀)
  have hpos : 0 < z₁₀ := by rw [← hfix₁₀]; exact E.stage_argmax_pos hz₁₀
  rw [hf₁₀, hf₁₁]
  exact ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hpos, hlt, ht₁₀, ht⟩

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-! ## 3. The stage net condition ND10 -/

/-- **The stage state rate is at most `r_hi/q`**: the stage sanction at defiance moves with
the state at rate at most `r_hi/q`. The stage payoff is `q`-strongly concave in the sanction
and a change of state perturbs it with cross rate at most `r_hi` (S9 at `a = 0`).
Scope: general class (relief extension). -/
theorem stageResp_dist_le {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |E.stageResp x - E.stageResp y| ≤ (E.rhi * |x - y|) / E.q := by
  have hf := E.hUS_concave x hx 0
  have hpert : ∀ u ∈ Sanctions.I, ∀ w ∈ Sanctions.I,
      |(E.U_S y 0 u - E.U_S x 0 u) - (E.U_S y 0 w - E.U_S x 0 w)|
        ≤ (E.rhi * |x - y|) * |u - w| := by
    intro u hu w hw
    have hid : (E.U_S y 0 u - E.U_S x 0 u) - (E.U_S y 0 w - E.U_S x 0 w)
        = (E.U_S y 0 u - E.U_S y 0 w) - (E.U_S x 0 u - E.U_S x 0 w) := by ring
    rw [hid]
    have h := E.hUS_crossHi 0 zero_mem_I x hx y hy w hw u hu
    calc |(E.U_S y 0 u - E.U_S y 0 w) - (E.U_S x 0 u - E.U_S x 0 w)|
        ≤ E.rhi * (|y - x| * |u - w|) := h
      _ = (E.rhi * |x - y|) * |u - w| := by rw [abs_sub_comm y x]; ring
  exact argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp
    (f := fun s => E.U_S x 0 s) (g := fun s => E.U_S y 0 s) (convex_Icc 0 1)
    E.hq (mul_nonneg E.rhi_nonneg (abs_nonneg _)) hf hpert
    (E.σ_mem x 0) (E.σ_mem y 0) (E.σ_isMaxOn_U_S x 0) (E.σ_isMaxOn_U_S y 0)

/-- **The Target-only operator preserves the lower-slope cone at slope `g`** under the stage
balance `g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·r_hi/q ≤ v_lo + n_lo·b`: the stage state
rate `r_hi/q` prices the pain term along the stage selector.
Scope: general class (relief extension). -/
theorem targetOp10_mem_lowerSlopeCone {g : ℝ} (hg : 0 ≤ g)
    (hbal : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.rhi / E.q)
      ≤ E.vlo + E.nlo * E.sfloor)
    {V_T : Val} (hV_T : Params.LowerSlopeOnValueOn V_T (Icc (0 : ℝ) 1) g) :
    Params.LowerSlopeOnValueOn (E.targetOp10 V_T) (Icc (0 : ℝ) 1) g := by
  have hβ : (0:ℝ) ≤ E.β_T := E.hβT0.le
  intro y₁ y₂ hy₁ hy₂ hle
  rw [targetOp10_apply, targetOp10_apply]
  have hyle : y₁.val ≤ y₂.val := hle
  have hd : dist y₁ y₂ = y₂.val - y₁.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hd]
  have hρ : E.stageResp y₁.val ≤ E.stageResp y₂.val := E.stageResp_monotoneOn hy₁ hy₂ hyle
  have hρ₁ := E.stageResp_mem y₁.val
  have hρ₂ := E.stageResp_mem y₂.val
  have hz₁ : E.F y₁.val (E.stageResp y₁.val) ≤ E.F y₁.val (E.stageResp y₂.val) :=
    E.F_mono_s _ hρ
  have hz₂ : E.F y₁.val (E.stageResp y₂.val) ≤ E.F y₂.val (E.stageResp y₂.val) :=
    E.F_mono_x _ hyle
  have hband := (E.hbandAll _ hρ₂) y₁.val hy₁ y₂.val hy₂ hyle
  have hchord := E.hSlo hy₁ hρ₁ hρ₂ hρ
  have hslope := E.clip_lowerSlope_of hV_T _ (E.F_mem _ _ hy₁ hρ₁) _ (E.F_mem _ _ hy₂ hρ₂)
    (hz₁.trans hz₂)
  have hsucc : E.glo * (y₂.val - y₁.val)
        + E.dlo * (E.stageResp y₂.val - E.stageResp y₁.val)
      ≤ E.F y₂.val (E.stageResp y₂.val) - E.F y₁.val (E.stageResp y₁.val) := by
    linarith [hband.1, hchord]
  have hA : E.β_T * g * (E.glo * (y₂.val - y₁.val)
        + E.dlo * (E.stageResp y₂.val - E.stageResp y₁.val))
      ≤ E.β_T * (V_T (Sanctions.clipS' (E.F y₂.val (E.stageResp y₂.val)))
        - V_T (Sanctions.clipS' (E.F y₁.val (E.stageResp y₁.val)))) := by
    have h1 := mul_le_mul_of_nonneg_left hsucc (mul_nonneg hβ hg)
    have h2 := mul_le_mul_of_nonneg_left hslope hβ
    nlinarith [h1, h2]
  have hUst := E.UT_state_chord_ge hy₁ hy₂ zero_mem_I hρ₁ hρ₂ hyle hρ
  have hE : E.sfloor * (E.nlo * (y₂.val - y₁.val))
      ≤ E.stageResp y₁.val * (E.nlo * (y₂.val - y₁.val)) :=
    mul_le_mul_of_nonneg_right (E.stageResp_ge_sfloor hy₁)
      (mul_nonneg E.hnlo (by linarith))
  have hLip : E.stageResp y₂.val - E.stageResp y₁.val
      ≤ E.rhi / E.q * (y₂.val - y₁.val) := by
    have h := E.stageResp_dist_le hy₂ hy₁
    have h' : E.stageResp y₂.val - E.stageResp y₁.val
        ≤ (E.rhi * |y₂.val - y₁.val|) / E.q := (le_abs_self _).trans h
    rw [abs_of_nonneg (by linarith)] at h'
    have : (E.rhi * (y₂.val - y₁.val)) / E.q = E.rhi / E.q * (y₂.val - y₁.val) := by ring
    linarith [h', this]
  have hC : (E.stageResp y₂.val - E.stageResp y₁.val) * (E.c - E.β_T * E.dlo * g)
      ≤ max 0 (E.c - E.β_T * E.dlo * g) * (E.rhi / E.q) * (y₂.val - y₁.val) := by
    rcases le_or_gt (E.c - E.β_T * E.dlo * g) 0 with hθ0 | hθ0
    · rw [max_eq_left hθ0]
      have : (E.stageResp y₂.val - E.stageResp y₁.val)
          * (E.c - E.β_T * E.dlo * g) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) hθ0
      linarith
    · rw [max_eq_right hθ0.le]
      have := mul_le_mul_of_nonneg_right hLip hθ0.le
      linarith [this]
  have hbal' := mul_le_mul_of_nonneg_right hbal (show 0 ≤ y₂.val - y₁.val by linarith)
  change g * (y₂.val - y₁.val)
    ≤ (E.U_T y₂.val 0 (E.stageResp y₂.val)
        + E.β_T * V_T (Sanctions.clipS' (E.F y₂.val (E.stageResp y₂.val))))
      - (E.U_T y₁.val 0 (E.stageResp y₁.val)
        + E.β_T * V_T (Sanctions.clipS' (E.F y₁.val (E.stageResp y₁.val))))
  nlinarith [hA, hUst, hE, hC, hbal']

/-- **The Target-only value at full defiance has lower slope `g`** under the stage balance
(Stokey–Lucas Corollary 1 to Theorem 3.2: the cone is closed, nonempty and invariant).
Scope: general class (relief extension). -/
theorem VT10def_lowerSlope {g : ℝ} (hg : 0 ≤ g)
    (hbal : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.rhi / E.q)
      ≤ E.vlo + E.nlo * E.sfloor) :
    Params.LowerSlopeOnValueOn E.VT10def (Icc (0 : ℝ) 1) g := by
  have hcontr := E.targetOp10_contracting
  obtain ⟨W, hW, hWmem⟩ := StokeyLucas.fixedPoint_mem_of_mapsTo hcontr.1 _ hcontr.2
    {V : Val | Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g}
    (Params.lowerSlopeOnValueOn_isClosed _ _) (E.lowerSlopeCone_nonempty g)
    (fun V hV => E.targetOp10_mem_lowerSlopeCone hg hbal hV)
  have h1 : W = hcontr.fixedPoint := hcontr.fixedPoint_unique hW
  change Params.LowerSlopeOnValueOn hcontr.fixedPoint (Icc (0 : ℝ) 1) g
  rw [← h1]
  exact hWmem

/-- **The stage net defiance condition at the slope `g`** (ND10, an internal helper derived
from ND): `g ≥ 0`, `c − ℓ_lo·q/k_hi ≤ β_T·d_lo·g`, and the stage balance
`g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·r_hi/q ≤ v_lo + n_lo·b`. Written over the class's
own data (Rule 14).
Scope: general class (relief extension); internal helper (implied by ND). -/
def NetDefianceStageAt (g : ℝ) : Prop :=
  0 ≤ g ∧ E.c - E.ℓlo * E.q / E.khi ≤ E.β_T * E.dlo * g ∧
    g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.rhi / E.q)
      ≤ E.vlo + E.nlo * E.sfloor

/-- **The stage net defiance condition** (ND10): some slope satisfies `NetDefianceStageAt`.
Scope: general class (relief extension); internal helper (implied by ND). -/
def NetDefianceStage : Prop := ∃ g, E.NetDefianceStageAt g

/-- **The strict stage net defiance condition at `g`** (approved hypothesis 2: uniqueness
clauses only).
Scope: general class (relief extension); internal helper (implied by strict ND). -/
def StrictNetDefianceStageAt (g : ℝ) : Prop :=
  0 ≤ g ∧ E.c - E.ℓlo * E.q / E.khi < E.β_T * E.dlo * g ∧
    g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.rhi / E.q)
      ≤ E.vlo + E.nlo * E.sfloor

/-- **The strict stage net defiance condition.**
Scope: general class (relief extension); internal helper (implied by strict ND). -/
def StrictNetDefianceStage : Prop := ∃ g, E.StrictNetDefianceStageAt g

/-- The strict stage condition implies the weak one.
Scope: general class (relief extension); internal helper. -/
theorem StrictNetDefianceStage.toNetDefianceStage {E : ChordEconomyRelief}
    (h : E.StrictNetDefianceStage) : E.NetDefianceStage :=
  let ⟨g, hg, hside, hbal⟩ := h
  ⟨g, hg, hside.le, hbal⟩

/-- **Under ND10, full defiance is a Target best reply against the stage selector.**
Scope: general class (relief extension); internal helper (use through ND). -/
theorem defianceBestReply10_of_netDefianceStage (h : E.NetDefianceStage) :
    E.DefianceBestReply10 := by
  obtain ⟨g, hg, hnet, hbal⟩ := h
  intro x hx
  rw [isMaxOn_iff]
  intro a ha
  exact E.targetObj10_antitoneOn_of_net E.placationCeiling hg hnet (E.VT10def_lowerSlope hg hbal)
    hx ⟨le_refl 0, zero_le_one⟩ ha ha.1

/-- **At every full-defiance equilibrium of the Target-only reading, under strict ND10, full
defiance is the Target's unique optimum at every state.** A statement about the Target's best
reply, not about uniqueness of the equilibrium.
Scope: general class (relief extension); internal helper (use through strict ND; approved
hypothesis 2, uniqueness clause only). -/
theorem targetOnly_policy_zero_argmax_unique_of_strict (h : E.StrictNetDefianceStage)
    (Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.pT.joint_T_top_integrand Eq.V_T Eq.V_S x b) Sanctions.I a) :
    a = Eq.α x := by
  obtain ⟨g, hg, hnet, hbal⟩ := h
  have hVT := (E.values10_eq_of_policy_zero Eq hα).1
  rw [hα x hx]
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hne)
  have h1 := E.targetObj10_strictAntiOn_of_net E.placationCeiling hg hnet
    (E.VT10def_lowerSlope hg hbal) hx ⟨le_refl 0, zero_le_one⟩ ha hpos
  have h2 := hmax (show (0:ℝ) ∈ Sanctions.I from ⟨le_refl 0, zero_le_one⟩)
  simp only [Set.mem_setOf_eq] at h2
  rw [hVT, E.pT_joint_T_top_integrand _ _ hx, E.pT_joint_T_top_integrand _ _ hx] at h2
  exact absurd h2 (not_le.mpr h1)

/-! ## 4. ND implies ND10 -/

/-- The stage rally rate is at most the response Lipschitz constant, `r_hi ≤ L_resp`.
Scope: general class (relief extension). -/
theorem rhi_le_Lresp : E.rhi ≤ E.Lresp := by
  unfold Lresp plLresp
  have hσ : 0 ≤ max E.SigV E.SigC := le_max_of_le_left E.hSigV0
  have h : 0 ≤ E.β_S * (max E.SigV E.SigC * E.ghi * E.dhi
      + (E.KS + 2 * max E.SigV E.SigC) * E.Mmix) := by
    apply mul_nonneg E.hβS0.le
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg hσ E.ghi_nonneg) E.dhi_nonneg
    · exact mul_nonneg (by linarith [E.KS_nonneg]) E.hMmix0
  linarith

/-- **The stage state rate is at most the dynamic one**, `r_hi/q ≤ L_resp/μ`: `r_hi ≤ L_resp`
and `μ ≤ q`.
Scope: general class (relief extension). -/
theorem rhi_div_q_le_Lresp_div_mu : E.rhi / E.q ≤ E.Lresp / E.mu := by
  rw [div_le_div_iff₀ E.hq E.mu_pos]
  have h1 := mul_le_mul_of_nonneg_left E.mu_le_q E.rhi_nonneg
  have h2 := mul_le_mul_of_nonneg_right E.rhi_le_Lresp E.hq.le
  linarith

/-- **ND at `g` implies ND10 at `g`**: the stage relief rate `k_hi/q` is at most the dynamic
one `k_hi/μ` (`μ ≤ q`), so the stage net side is weaker, and the stage state rate `r_hi/q` is
at most `L_resp/μ`, so the stage balance is weaker.
Scope: general class (relief extension); internal helper (ND10 only as the conclusion). -/
theorem netDefianceStageAt_of_netDefianceAt {g : ℝ} (h : E.NetDefianceAt g) :
    E.NetDefianceStageAt g := by
  obtain ⟨hg, hside, hbal⟩ := h
  have hk := E.khi_pos
  refine ⟨hg, ?_, ?_⟩
  · have : E.ℓlo * E.mu / E.khi ≤ E.ℓlo * E.q / E.khi :=
      (div_le_div_iff_of_pos_right hk).mpr (mul_le_mul_of_nonneg_left E.mu_le_q E.hℓlo.le)
    linarith
  · have := mul_le_mul_of_nonneg_left E.rhi_div_q_le_Lresp_div_mu
      (le_max_left 0 (E.c - E.β_T * E.dlo * g))
    linarith

/-- **Strict ND at `g` implies strict ND10 at `g`.**
Scope: general class (relief extension); internal helper. -/
theorem strictNetDefianceStageAt_of_strictNetDefianceAt {g : ℝ} (h : E.StrictNetDefianceAt g) :
    E.StrictNetDefianceStageAt g := by
  obtain ⟨hg, hside, hbal⟩ := h
  obtain ⟨-, hside', hbal'⟩ := E.netDefianceStageAt_of_netDefianceAt ⟨hg, hside.le, hbal⟩
  refine ⟨hg, ?_, hbal'⟩
  have hk := E.khi_pos
  have : E.ℓlo * E.mu / E.khi ≤ E.ℓlo * E.q / E.khi :=
    (div_le_div_iff_of_pos_right hk).mpr (mul_le_mul_of_nonneg_left E.mu_le_q E.hℓlo.le)
  linarith

/-- **ND implies ND10.**
Scope: general class (relief extension). -/
theorem netDefianceStage_of_netDefiance (h : E.NetDefiance) : E.NetDefianceStage :=
  let ⟨g, hg⟩ := h
  ⟨g, E.netDefianceStageAt_of_netDefianceAt hg⟩

/-- **Strict ND implies strict ND10.**
Scope: general class (relief extension); approved hypothesis 2 (strict form). -/
theorem strictNetDefianceStage_of_strictNetDefiance (h : E.StrictNetDefiance) :
    E.StrictNetDefianceStage :=
  let ⟨g, hg⟩ := h
  ⟨g, E.strictNetDefianceStageAt_of_strictNetDefianceAt hg⟩

/-- **The loss-offset condition implies ND10.**
Scope: general class (relief extension). -/
theorem netDefianceStage_of_lossOffset (hTM : E.LossOffset) : E.NetDefianceStage :=
  E.netDefianceStage_of_netDefiance (E.netDefiance_of_lossOffset hTM)

/-! ## 5. The Target-only reading under ND -/

/-- **The Target-only reading under the net defiance condition ND, general in `F` and in the
payoffs** (net form of `target_only_regime_generalF_of_response_monotone`, clauses (i)–(iii)):
(i) the same primitives; (ii) a full-defiance equilibrium of the reading `10` exists, and at
it the realised sanction is the stage selector at defiance; (iii) the state washes in, above
the approach to the floor, and converges to a fixed point of the stage selector from every
start. Every full-defiance equilibrium of the reading has the value `VT10def` and the stage
selector as its rule. Clause (iv), the comparison with the forward-looking limit, is
`target_only_limit_lt_net`; uniqueness of the Target's best reply is
`targetOnly_policy_zero_argmax_unique_of_strict`.
Scope: general class (relief extension); net condition ND (no stage-level hypothesis). -/
theorem target_only_regime_net (hND : E.NetDefiance) :
    (E.pT.U_T = E.toParams.U_T ∧ E.pT.U_S = E.toParams.U_S ∧ E.pT.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND))).α x
        = 0 ∧
      E.pT.dynamicEquilibriumRule
        (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND))) x
          = E.σ x 0) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t
        ≤ E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND)) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND)) x₀)
          atTop (𝓝 z)) ∧
    (∀ Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10,
      (∀ x ∈ Sanctions.I, Eq.α x = 0) →
        Eq.V_T = E.VT10def ∧ ∀ x ∈ Sanctions.I, E.pT.dynamicEquilibriumRule Eq x = E.σ x 0) := by
  set h10 := E.defianceBestReply10_of_netDefianceStage (E.netDefianceStage_of_netDefiance hND)
  have hα : ∀ x ∈ Sanctions.I, (E.targetOnlyDefianceEquilibrium h10).α x = 0 := fun _ _ => rfl
  refine ⟨⟨rfl, rfl, rfl⟩, fun x hx => ⟨rfl, E.pT_rule_eq_stage_of_policy_zero _ hα hx⟩,
    fun x₀ hx₀ => ?_, fun Eq hEq => E.values10_eq_of_policy_zero Eq hEq⟩
  have hf : E.targetOnlyDefiancePath h10 x₀ = E.stagePath x₀ :=
    funext (E.pT_rulePath_eq_stagePath_of_policy_zero _ hα hx₀)
  rw [hf]
  exact ⟨E.stagePath_ge_approach hx₀, E.stagePath_tendsto hx₀⟩

/-- **The Target-only limit lies strictly below the forward-looking limit under ND**
(clause (iv) of the Target-only reading, net form), from every start, at the two constructed
full-defiance equilibria: the Target-only one exists under ND10, which ND implies. Under the
stage appetite and a nondecreasing response.
Scope: general class (relief extension). -/
theorem target_only_limit_lt_net (hS : E.uhi < E.q)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.NetDefiance)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND)) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.netDefiancePath hmono hND x₀) atTop (𝓝 z) :=
  E.limits_of_policy_zero hS hmono _ (fun _ _ => rfl) _ (fun _ _ => rfl) hx₀

/-! ## 6. The wedge, the long-run gap and resumption under ND -/

/-- **The wedge and the long-run gap under ND** (net form of the wedge path clauses and of
the long-run gap): at the two constructed full-defiance equilibria (the Target-only one
exists under ND10, which ND implies), the forward-looking rule exceeds the Target-only rule
by at least the wedge at every state; from a common start the forward-looking path dominates,
the realised sanctions differ by at least the wedge at every date, and the limits satisfy
`z ≥ z₁₀ + β_S·w_lo·d_lo/((Q̄ − r_lo)(1 − β_S·g_lo))`. Under interiority and a
nondecreasing response. The same holds at every pair of full-defiance equilibria
(`wedge_and_gap_of_policy_zero`).
Scope: general class (relief extension). -/
theorem wedge_and_gap_net (hInt : E.Interior)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.NetDefiance) :
    (∀ x ∈ Sanctions.I,
      E.pT.dynamicEquilibriumRule (E.targetOnlyDefianceEquilibrium
          (E.defianceBestReply10_of_netDefianceStage (E.netDefianceStage_of_netDefiance hND))) x
        + E.wedge ≤ E.toParams.dynamicEquilibriumRule (E.netDefianceEquilibrium hmono hND) x) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
          (E.netDefianceStage_of_netDefiance hND)) x₀ t ≤ E.netDefiancePath hmono hND x₀ t) ∧
      (∀ t, E.pT.dynamicEquilibriumRule (E.targetOnlyDefianceEquilibrium
            (E.defianceBestReply10_of_netDefianceStage (E.netDefianceStage_of_netDefiance hND)))
            (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
              (E.netDefianceStage_of_netDefiance hND)) x₀ t) + E.wedge
          ≤ E.toParams.dynamicEquilibriumRule (E.netDefianceEquilibrium hmono hND)
            (E.netDefiancePath hmono hND x₀ t)) ∧
      ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
        E.responsePath E.VSstar z = z ∧
        z₁₀ + E.β_S * E.wlo * E.dlo / ((E.Qbar - E.rlo) * (1 - E.β_S * E.glo)) ≤ z ∧
        Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
          (E.netDefianceStage_of_netDefiance hND)) x₀) atTop (𝓝 z₁₀) ∧
        Tendsto (E.netDefiancePath hmono hND x₀) atTop (𝓝 z)) :=
  E.wedge_and_gap_of_policy_zero hInt hmono _ (fun _ _ => rfl) _ (fun _ _ => rfl)

/-- **Temporary relief does not end the full-defiance equilibrium under ND** (net form of
`placable_resumption_after_episode`): after any feasible imposed schedule of any length, the
resumed equilibrium sanctions at least the stage selector plus the wedge at every later
date, and its state converges to a fixed point of the response strictly above the floor.
The same holds at every full-defiance equilibrium (`resumption_after_episode_of_policy_zero`).
Scope: general class (relief extension). -/
theorem resumption_after_episode_net (hInt : E.Interior)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.NetDefiance)
    {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, E.σ (E.toParams.splicedPath (E.netDefianceEquilibrium hmono hND).V_S
          (E.netDefianceEquilibrium hmono hND).α u T x₀ (T + n)) 0 + E.wedge
        ≤ E.toParams.splicedSanction (E.netDefianceEquilibrium hmono hND).V_S
          (E.netDefianceEquilibrium hmono hND).α u T x₀ (T + n)) ∧
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧
      Tendsto (fun n => E.toParams.splicedPath (E.netDefianceEquilibrium hmono hND).V_S
        (E.netDefianceEquilibrium hmono hND).α u T x₀ (T + n)) atTop (𝓝 z) :=
  E.resumption_after_episode_of_policy_zero hInt hmono _ (fun _ _ => rfl) hu T hx₀

/-- **Under strict ND the Target's best reply is unique in both forward-looking-Target
cells**: at every full-defiance equilibrium of the Target-only reading and of the
forward-looking reading, full defiance is the Target's unique optimum at every state. A
statement about best replies, not about uniqueness of equilibrium.
Scope: general class (relief extension); approved hypothesis 2 (strict form, uniqueness
clauses only). -/
theorem defiance_argmax_unique_both_cells_of_strict
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.StrictNetDefiance) :
    (∀ Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10,
      (∀ x ∈ Sanctions.I, Eq.α x = 0) → ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pT.joint_T_top_integrand Eq.V_T Eq.V_S x b) Sanctions.I a →
          a = Eq.α x) ∧
    (∀ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Sanctions.I, Eq.α x = 0) → ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x b) Sanctions.I a →
          a = Eq.α x) :=
  ⟨fun Eq hα _ hx _ ha hmax => E.targetOnly_policy_zero_argmax_unique_of_strict
      (E.strictNetDefianceStage_of_strictNetDefiance hND) Eq hα hx ha hmax,
   fun Eq hα _ hx _ ha hmax =>
      E.policy_zero_argmax_unique_of_strictNetDefiance hmono hND Eq hα hx ha hmax⟩

/-- **The Target-only reading under strict ND, with uniqueness of the Target's best reply**
(the net form of the pinned `target_only_regime_generalF_core`, with the loss-offset
condition replaced by strict ND, which it implies, `strictNetDefiance_of_lossOffset`):
(i) the Target-only profile has the same payoffs and transition; (ii) at every feasible
state the Target defies, every Target maximiser at the constructed full-defiance equilibrium
is defiance, and the realised sanction is the stage selector at defiance; (iii) from every
feasible start the state stays above the geometric approach to the sanction floor and
converges to a fixed point of the stage selector at or above the floor. The weak form
`target_only_regime_net` gives the same clauses without the uniqueness in (ii). The
uniqueness in (ii) is uniqueness of the Target's best reply at that equilibrium's values, not
of the equilibrium.
Scope: general class (relief extension); approved hypothesis 2 (strict form, read only
through the uniqueness of the Target's best reply). -/
theorem target_only_regime_net_core (hND : E.StrictNetDefiance) :
    (E.pT.U_T = E.toParams.U_T ∧ E.pT.U_S = E.toParams.U_S ∧ E.pT.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND.toNetDefiance))).α x = 0 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pT.joint_T_top_integrand
          (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
            (E.netDefianceStage_of_netDefiance hND.toNetDefiance))).V_T
          (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
            (E.netDefianceStage_of_netDefiance hND.toNetDefiance))).V_S x b) Sanctions.I a →
          a = 0) ∧
      E.pT.dynamicEquilibriumRule
        (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
          (E.netDefianceStage_of_netDefiance hND.toNetDefiance))) x = E.σ x 0) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t
        ≤ E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
          (E.netDefianceStage_of_netDefiance hND.toNetDefiance)) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
          (E.netDefianceStage_of_netDefiance hND.toNetDefiance)) x₀) atTop (𝓝 z)) := by
  obtain ⟨h1, h2, h3, -⟩ := E.target_only_regime_net hND.toNetDefiance
  refine ⟨h1, fun x hx => ⟨(h2 x hx).1, fun a ha hmax => ?_, (h2 x hx).2⟩, h3⟩
  have hu := E.targetOnly_policy_zero_argmax_unique_of_strict
    (E.strictNetDefianceStage_of_strictNetDefiance hND)
    (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
      (E.netDefianceStage_of_netDefiance hND.toNetDefiance))) (fun _ _ => rfl) hx ha hmax
  exact hu.trans (h2 x hx).1

/-- **Both channels active at the full-defiance equilibrium under strict ND, given the
dynamic complementarity condition** (the net form of the pinned
`both_channels_active_of_margin`, with the loss-offset condition replaced by strict ND, which
it implies): at every state of the constructed full-defiance equilibrium
`netDefianceEquilibrium`, no forward-looking Sender maximiser is a stage maximiser and no
forward-looking Target maximiser is a stage maximiser, under the stage flip
`ℓ_hi < b·p_lo`, placability and interiority. The Target side reads the uniqueness of the
Target's best reply (full defiance), which is why the strict form is used.
Scope: general class (relief extension); approved hypothesis 2 (strict form, read only
through the uniqueness of the Target's best reply). -/
theorem both_channels_active_of_margin_net (hInt : E.Interior) (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hND : E.StrictNetDefiance) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt
        (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin)
          hND.toNetDefiance).V_S x
        ((E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin)
          hND.toNetDefiance).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.netDefianceEquilibrium
            (E.responsePath_monotoneOn_of_margin hmargin) hND.toNetDefiance).V_S y b)
          (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin)
            hND.toNetDefiance).V_T x :=
  fun x hx => (E.placable_family_defiance_net_unique (E.uhi_lt_q hInt) hP hflip
    (E.responsePath_monotoneOn_of_margin hmargin) hND
    (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin) hND.toNetDefiance)
    (fun _ _ => rfl) x hx).2

end ChordEconomyRelief

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## 7. The four cases under ND -/

/-- **The four cases under the net defiance condition, general in `F` and in the payoffs**
(net form of `four_cell_generalF'_of_response_monotone`). Under the readings in which the
Target does not look ahead (`00`, `01`) the state washes out from every start. Under ND a
full-defiance equilibrium exists in each reading in which the Target looks ahead (`10`
through ND10, which ND implies; `11` directly), and from every start the state converges to
a positive limit: a fixed point `z₁₀` of the stage selector when the Sender is myopic and a
strictly higher fixed point `z` of the response when it looks ahead. The loss-offset
condition is replaced by ND, which it implies. The limits are the same at every pair of
full-defiance equilibria (`limits_of_policy_zero`); under strict ND full defiance is the
Target's unique best reply in both cells (`defiance_argmax_unique_both_cells_of_strict`).
Scope: general class (enriched subclass `ChordEconomyCs`). -/
theorem four_cell_net (hInt : E.Interior) (hP : E.Placable)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    (hND : E.NetDefiance) :
    (∀ x₀ ∈ Sanctions.I, Tendsto
      ((E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x ∈ Sanctions.I, (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
      (E.netDefianceStage_of_netDefiance hND))).α x = 0) ∧
    (∀ x ∈ Sanctions.I, (E.netDefianceEquilibrium hmono hND).α x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND)) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.netDefiancePath hmono hND x₀) atTop (𝓝 z)) :=
  ⟨fun _ hx₀ => (E.myopicPath_tendsto_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx₀,
    fun _ hx₀ => (E.senderOnlyPath_tendsto_zero' hInt hP) hrelief hN hx₀,
    fun _ _ => rfl, fun _ _ => rfl,
    fun _ hx₀ => E.target_only_limit_lt_net (E.uhi_lt_q hInt) hmono hND hx₀⟩

/-- **The four cases under ND, with the dynamic complementarity condition** in place of the
nondecreasing response (which it implies, `responsePath_monotoneOn_of_margin`).
Scope: general class (enriched subclass `ChordEconomyCs`). -/
theorem four_cell_net_of_margin (hInt : E.Interior) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    (hND : E.NetDefiance) :
    (∀ x₀ ∈ Sanctions.I, Tendsto
      ((E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x ∈ Sanctions.I, (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
      (E.netDefianceStage_of_netDefiance hND))).α x = 0) ∧
    (∀ x ∈ Sanctions.I,
      (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin) hND).α x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND)) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.netDefiancePath (E.responsePath_monotoneOn_of_margin hmargin) hND x₀) atTop
        (𝓝 z)) :=
  E.four_cell_net hInt hP (E.responsePath_monotoneOn_of_margin hmargin) hrelief hN hND

/-- **The four cells under ND, in the hypotheses of the pinned `four_cell_generalF`** (net
form of the pinned row: the loss-offset condition `hTM` is replaced by ND, which it
implies). Same hypotheses as `four_cell_generalF` otherwise (interiority, the stage relief
margin, placability, the rally margin, the two-branch relief margin, zero-sanction
neutrality). Under the readings in which the Target does not look ahead (`00`, `01`) the
state washes out from every start; under ND a full-defiance equilibrium exists in each
reading in which the Target looks ahead (`10`, `11`), and from every start the state
converges to a positive limit: a fixed point `z₁₀` of the stage selector when the Sender is
myopic and a strictly higher fixed point `z` of the response when it looks ahead. The
conclusion adds to the pinned row that both full-defiance profiles have zero policy.
Scope: general class (enriched subclass `ChordEconomyCs`). -/
theorem four_cell_net_generalF (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    (hND : E.NetDefiance) :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.myopicPath hInt hSR hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x ∈ Sanctions.I, (E.targetOnlyDefianceEquilibrium (E.defianceBestReply10_of_netDefianceStage
      (E.netDefianceStage_of_netDefiance hND))).α x = 0) ∧
    (∀ x ∈ Sanctions.I,
      (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin) hND).α x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto (E.targetOnlyDefiancePath (E.defianceBestReply10_of_netDefianceStage
        (E.netDefianceStage_of_netDefiance hND)) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.netDefiancePath (E.responsePath_monotoneOn_of_margin hmargin) hND x₀) atTop
        (𝓝 z)) := by
  obtain ⟨-, -, h3, h4, h5⟩ := E.four_cell_net_of_margin hInt hP hmargin
    (E.reliefSharp_of_relief hrelief) hN hND
  exact ⟨fun _ hx₀ => (E.myopicPath_tendsto_zero hInt hSR hP) hx₀,
    fun _ hx₀ => (E.senderOnlyPath_tendsto_zero hInt hP) hrelief hN hx₀, h3, h4, h5⟩

/-- **The Target channel is active under (RL) at every full-defiance equilibrium under strict
ND, with no stage flip** (net form of `target_channel_active_of_relief`, with the loss-offset
condition replaced by strict ND): the forward-looking optimum is full defiance, unique under
strict ND (`targetArgmax_eq_zero_of_sharp`), and a compliance
`a ≤ min(1, μρ(x,0)/(2k_hi))`, which keeps the response positive, beats it at the stage.
Scope: enriched subclass `ChordEconomyCs`; approved hypothesis 2 (strict form, read only
through the uniqueness of the Target's best reply). -/
theorem target_channel_active_of_relief_net (hInt : E.Interior)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.StrictNetDefiance)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.ContinuationChangesTargetChoiceAt (fun y b => E.response Eq.V_S y b) Eq.V_T x := by
  obtain ⟨hVS, hVT, -⟩ := E.values_eq_of_policy_zero Eq hα
  rw [hVS, hVT]
  obtain ⟨g, hg, hside, hbal⟩ := hND
  intro a ha hdyn hstage
  have hdyn' : IsMaxOn (fun b => E.toParams.joint_T_integrand E.VTdef E.VSstar x b)
      Sanctions.I a := hdyn
  have ha0 : a = 0 := E.targetArgmax_eq_zero_of_sharp E.placationCeiling hg hside
    (E.VTdef_lowerSlope hmono hg hbal) E.VSstar_mem hx ha hdyn'
  subst ha0
  have hk := E.khi_pos
  have hμ := E.mu_pos
  have hρ0 : 0 < E.response E.VSstar x 0 := E.responsePath_pos E.VSstar_mem hx
  set a₁ := min (1 : ℝ) (E.mu * E.response E.VSstar x 0 / (2 * E.khi)) with ha₁def
  have ha₁pos : 0 < a₁ := lt_min one_pos (by positivity)
  have ha₁I : a₁ ∈ Sanctions.I := ⟨ha₁pos.le, min_le_left _ _⟩
  have hsmall : E.khi * a₁ / E.mu < E.response E.VSstar x 0 := by
    have h1 : a₁ ≤ E.mu * E.response E.VSstar x 0 / (2 * E.khi) := min_le_right _ _
    have h2 : E.khi * a₁ / E.mu
        ≤ E.khi * (E.mu * E.response E.VSstar x 0 / (2 * E.khi)) / E.mu :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hk.le) hμ.le
    have h3 : E.khi * (E.mu * E.response E.VSstar x 0 / (2 * E.khi)) / E.mu
        = E.response E.VSstar x 0 / 2 := by
      have hk' : E.khi ≠ 0 := hk.ne'
      have hμ' : E.mu ≠ 0 := hμ.ne'
      field_simp
    linarith
  have hpos : 0 < E.response E.VSstar x a₁ := by
    have h := E.response_dist_le_of_compliance E.VSstar_mem hx ha₁I
    have := (abs_le.mp h).2
    linarith
  have hgain := E.targetStage_small_gain hInt hrelief hx ha₁pos ha₁I.2 hpos
  have h := hstage ha₁I
  simp only [Set.mem_setOf_eq] at h
  exact absurd h (not_le.mpr hgain)

/-- **Both channels active at the full-defiance equilibrium under (RL), strict ND and the
dynamic complementarity condition, with no stage flip** (net form of the pinned
`both_channels_active_of_relief`, with the loss-offset condition replaced by strict ND, which
it implies): at every state of the constructed full-defiance equilibrium
`netDefianceEquilibrium`, no forward-looking Sender maximiser is a stage maximiser and no
forward-looking Target maximiser is a stage maximiser. The Target side reads the uniqueness
of the Target's best reply (full defiance), which is why the strict form is used.
Scope: enriched subclass `ChordEconomyCs`; approved hypothesis 2 (strict form, read only
through the uniqueness of the Target's best reply). -/
theorem both_channels_active_of_relief_net (hInt : E.Interior)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hND : E.StrictNetDefiance) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt
        (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin)
          hND.toNetDefiance).V_S x
        ((E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin)
          hND.toNetDefiance).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.netDefianceEquilibrium
            (E.responsePath_monotoneOn_of_margin hmargin) hND.toNetDefiance).V_S y b)
          (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin)
            hND.toNetDefiance).V_T x := by
  intro x hx
  have hα : ∀ y ∈ Sanctions.I, (E.netDefianceEquilibrium
      (E.responsePath_monotoneOn_of_margin hmargin) hND.toNetDefiance).α y = 0 := fun _ _ => rfl
  refine ⟨?_, E.target_channel_active_of_relief_net hInt hrelief
    (E.responsePath_monotoneOn_of_margin hmargin) hND _ hα hx⟩
  obtain ⟨hVS, -, -⟩ := E.values_eq_of_policy_zero (E.netDefianceEquilibrium
    (E.responsePath_monotoneOn_of_margin hmargin) hND.toNetDefiance) hα
  rw [hVS, hα x hx]
  exact E.sender_channel_active (E.uhi_lt_q hInt) hx

end ChordEconomyCs

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-! ## 8. The quadratic–linear family: the closed form under ND (sign-off M6)

On the family the stage selector at defiance is the vertex `(u₀ + r·x)/q`, so the stage path
(the path of every full-defiance equilibrium of the Target-only reading) converges to the
unique steady state `u₀/(q − r)` at the geometric rate `1 − d_lo(1 − r/q)`. Exact-form
statements, on the family only. -/

/-- **Geometric convergence of the stage path on the family**: `|x_t − u₀/(q − r)| ≤
θ^t·|x₀ − u₀/(q − r)|` with `θ = 1 − d_lo(1 − r/q)`. No defiance condition.
Scope: quadratic–linear family only (not general), general in its transition `F`. -/
theorem stagePath_error_le_geometric (hInt : E.Interior) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, |E.toChord.stagePath x₀ t - E.steady10|
      ≤ (1 - E.dlo * (1 - E.r / E.q)) ^ t * |x₀ - E.steady10| := by
  intro t
  have hRz : ∀ x ∈ Sanctions.I, E.toChord.stageResp x - E.steady10
      = E.r / E.q * (x - E.steady10) := fun x hx => by
    have hv : E.toChord.stageResp x = E.vertex x := E.toChord_σ_zero hInt hx
    rw [hv]
    exact E.vertex_sub_steady10 hInt x
  have h := Sanctions.CenteredContraction.iterate_abs_le (F := E.toChord.F)
    (fun s _ => (E.toChord.F_mono_x s).monotoneOn _)
    (fun y _ => (E.toChord.F_mono_s y).monotoneOn _)
    (fun y _ => E.toChord.F_diag y)
    E.toChord.hSlo E.r_div_q_nonneg (E.r_div_q_lt_one hInt).le
    (fun x _ => E.toChord.stageResp_mem x) hRz hx₀ t
  exact h.2

/-- **The stage path converges to `u₀/(q − r)` on the family**, from every start. No
defiance condition.
Scope: quadratic–linear family only (not general), general in its transition `F`. -/
theorem stagePath_tendsto_steady10 (hInt : E.Interior) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto (E.toChord.stagePath x₀) atTop (𝓝 E.steady10) := by
  obtain ⟨z, hz, hfix, -, htend⟩ := E.toChord.stagePath_tendsto hx₀
  rw [E.toChord_σ_zero hInt hz] at hfix
  rwa [(E.vertex_eq_self_iff hInt z).1 hfix] at htend

/-- **The Target-only reading on the family under ND** (closed-form companion of
`target_only_regime_net`; net form of `target_only_regime_closedForm`): the Target defies
and the realised sanction is the vertex `(u₀ + r·x)/q`; the path washes in above the
approach to `u₀/q`, converges to the unique steady state `u₀/(q − r)` from every start, at
the geometric rate `1 − d_lo(1 − r/q)`.
Scope: quadratic–linear family only (not general), general in its transition `F`; net
condition ND (no stage-level hypothesis). -/
theorem target_only_regime_closedForm_net (hInt : E.Interior)
    (hND : E.toChord.NetDefiance) :
    (∀ x ∈ Sanctions.I,
      (E.toChord.targetOnlyDefianceEquilibrium
        (E.toChord.defianceBestReply10_of_netDefianceStage
          (E.toChord.netDefianceStage_of_netDefiance hND))).α x = 0 ∧
      E.toChord.pT.dynamicEquilibriumRule (E.toChord.targetOnlyDefianceEquilibrium
        (E.toChord.defianceBestReply10_of_netDefianceStage
          (E.toChord.netDefianceStage_of_netDefiance hND))) x = E.vertex x) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach (E.u₀ / E.q) E.dlo t ≤ E.toChord.targetOnlyDefiancePath
        (E.toChord.defianceBestReply10_of_netDefianceStage
          (E.toChord.netDefianceStage_of_netDefiance hND)) x₀ t) ∧
      (∀ t, |E.toChord.targetOnlyDefiancePath
          (E.toChord.defianceBestReply10_of_netDefianceStage
          (E.toChord.netDefianceStage_of_netDefiance hND)) x₀ t - E.steady10|
        ≤ (1 - E.dlo * (1 - E.r / E.q)) ^ t * |x₀ - E.steady10|) ∧
      Tendsto (E.toChord.targetOnlyDefiancePath
        (E.toChord.defianceBestReply10_of_netDefianceStage
          (E.toChord.netDefianceStage_of_netDefiance hND)) x₀) atTop (𝓝 E.steady10)) := by
  set h10 := E.toChord.defianceBestReply10_of_netDefianceStage
    (E.toChord.netDefianceStage_of_netDefiance hND)
  have hα : ∀ x ∈ Sanctions.I, (E.toChord.targetOnlyDefianceEquilibrium h10).α x = 0 :=
    fun _ _ => rfl
  refine ⟨fun x hx => ⟨rfl, ?_⟩, fun x₀ hx₀ => ?_⟩
  · rw [E.toChord.pT_rule_eq_stage_of_policy_zero _ hα hx]
    exact E.toChord_σ_zero hInt hx
  have hf : E.toChord.targetOnlyDefiancePath h10 x₀ = E.toChord.stagePath x₀ :=
    funext (E.toChord.pT_rulePath_eq_stagePath_of_policy_zero _ hα hx₀)
  rw [hf]
  refine ⟨?_, E.stagePath_error_le_geometric hInt hx₀, E.stagePath_tendsto_steady10 hInt hx₀⟩
  have h := E.toChord.stagePath_ge_approach hx₀
  rwa [E.toChord_sfloor (E.u₀_le_q hInt)] at h

/-- **On the family, the Target-only steady state lies strictly below the forward-looking
limit under ND**, from every start, at the constructed full-defiance equilibrium. Under a
nondecreasing response.
Scope: quadratic–linear family only (not general), general in its transition `F`. -/
theorem targetOnly_steady_lt_net_limit (hInt : E.Interior)
    (hmono : MonotoneOn (E.toChord.responsePath E.toChord.VSstar) (Icc (0 : ℝ) 1))
    (hND : E.toChord.NetDefiance) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧ E.steady10 < z ∧
      Tendsto (E.toChord.netDefiancePath hmono hND x₀) atTop (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, -, hlt, -, htend⟩ :=
    E.toChord.target_only_limit_lt_net (E.toChord.uhi_lt_q (E.toChord_interior hInt)) hmono hND
      hx₀
  rw [E.toChord_σ_zero hInt hz₁₀] at hfix₁₀
  rw [(E.vertex_eq_self_iff hInt z₁₀).1 hfix₁₀] at hlt
  exact ⟨z, hz, hfix, hlt, htend⟩

end PlacableEconomyF

end

end Examples
end Sanctions
