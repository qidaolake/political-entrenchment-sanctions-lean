/-
Sanctions/Examples/HostileSenderWitness.lean

**The hostile benchmark: two explicit equilibria, and every hostile bound attained** (step 2,
target 2b, 2026-10-10; plan W1). Rule 9: existence certificates and nothing more.

`hostileAffine b = (collapseAffine b).hostileParams 2` is the rally-free tight affine member
`collapseAffine b` (`PlacableSenderCollapseWitness.lean`) with the Sender's stake shifted by
`−2`: transition `F(x,s) = (x + s)/2`, `β_S = 1/2`, `β_T = b`; Sender payoff
`U_S(x,a,s) = −(3/2)s² + s(1 − 3a) − x` (state slope `w = 1 − 2 = −1`, rally `r = 0`); Target
payoff `U_T(x,a,s) = −a − 4s + 30x` (`n = 0`). The Sender's coalition loses one unit per unit of
hard-line entrenchment, at every sanction level.

## What is proved

* `hostileDefianceEquilibrium` (case 11, `2/11 ≤ b`): a top-selector feedback Stackelberg
  equilibrium with full defiance; Sender value `4/27 − (4/3)x`, response `max 0 (2/9 − a)`,
  realised sanction `2/9` at every state.
* `hostileReliefEquilibrium` (case 01, the profile `01`): relief at the compliance `2/9`;
  Sender value `−(4/3)x` (the relief value), realised sanction `0`.
* The hypotheses of the hostile class results hold here: the hostile stake bound at rate `1` at
  every sanction (`hsw_stake`), the residual appetite `1 > 1/3` (`hsw_residual`), the stage
  appetite, the stage placability and the placation ceiling.
* **All three mirror bounds are attained** (the mirror of `rem:wedge-sharp`):
  the reverse wedge `R = σᴹ − 1/9 = 2/9` (`hsw_wedge_attained`); the relief price
  `a* = a⁰⁰ − 1/9 = 2/9` (`hsw_relief_price_attained`); the long-run gap
  `z₁₁ = 2/9 = z₁₀ − 1/9` (`hsw_limit_attained`).
* The class results apply at the member, with the equilibrium of case 11 in hand
  (`hsw_full_defiance_bounds`), and cases 00 and 10 at the shifted economy are the original
  ones (`hsw_case10`, `hsw_case00`).

**Rule 22: AFFINE** (the member's transition is `affineF (1/2)`). **Rule 3.** No assumption is
introduced; every statement is about the member. **Scope:** at the example economy only (not
general).
-/
import Sanctions.Examples.HostileSenderClass
import Sanctions.Examples.PlacableSenderCollapseWitness
import Sanctions.Examples.ExplicitEquilibriumKit

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Mechanism

noncomputable section

/-! ## 1. The member -/

/-- **The hostile benchmark** `W1`: the tight affine member `collapseAffine b` with the Sender's
stake shifted by `−2` (state slope `−1`). -/
abbrev hostileAffine (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : Params :=
  (collapseAffine b hb0 hb1).toChordEconomy.hostileParams 2

section Member

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- The member's hostile Sender payoff `−(3/2)s² + s(1 − 3a) − x`.
Scope: at the example economy only (not general). -/
theorem hsw_U_S (x a s : ℝ) :
    (hostileAffine b hb0 hb1).U_S x a s = -(3 / 2) * s ^ 2 + s * (1 - 3 * a) - x := by
  change symU_S 3 1 3 0 1 x a s + -2 * x = _
  unfold symU_S; ring

/-- The member's Target payoff `−a − 4s + 30x`.
Scope: at the example economy only (not general). -/
theorem hsw_U_T (x a s : ℝ) : (hostileAffine b hb0 hb1).U_T x a s = -a - 4 * s + 30 * x := by
  change symU_T 1 4 0 30 x a s = _
  unfold symU_T; ring

/-- The member's transition `(x + s)/2`.
Scope: at the example economy only (not general). -/
theorem hsw_F (x s : ℝ) : (hostileAffine b hb0 hb1).F x s = (x + s) / 2 := by
  change affineF (1 / 2) x s = _
  unfold affineF; ring

/-- The member's Sender discount factor.
Scope: at the example economy only (not general). -/
theorem hsw_β_S : (hostileAffine b hb0 hb1).β_S = 1 / 2 := rfl
/-- The member's Target discount factor.
Scope: at the example economy only (not general). -/
theorem hsw_β_T : (hostileAffine b hb0 hb1).β_T = b := rfl

/-- The member's static selector `max 0 (1/3 − a)`.
Scope: at the example economy only (not general). -/
theorem hsw_σ (x : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (hostileAffine b hb0 hb1).σ x a = max 0 (1 / 3 - a) := by
  change symσ 3 1 3 0 x a = _
  unfold symσ
  rw [min_eq_right (by linarith : (1 - 3 * a + 0 * x) / 3 ≤ 1)]
  congr 1; ring

/-- The member's transition is feasible.
Scope: at the example economy only (not general). -/
theorem hsw_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [hsw_F]; constructor <;> linarith [hx.1, hx.2, hs.1, hs.2]

/-! The member's chord data (definitional). -/

/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_glo : (collapseAffine b hb0 hb1).glo = 1 / 2 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_ghi : (collapseAffine b hb0 hb1).ghi = 1 / 2 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_dlo : (collapseAffine b hb0 hb1).dlo = 1 / 2 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_dhi : (collapseAffine b hb0 hb1).dhi = 1 / 2 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_Qbar : (collapseAffine b hb0 hb1).Qbar = 3 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_q : (collapseAffine b hb0 hb1).q = 3 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_βS : (collapseAffine b hb0 hb1).β_S = 1 / 2 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_wlo : (collapseAffine b hb0 hb1).wlo = 1 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_ulo : (collapseAffine b hb0 hb1).ulo = 1 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_uhi : (collapseAffine b hb0 hb1).uhi = 1 + 0 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_klo : (collapseAffine b hb0 hb1).klo = 3 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_khi : (collapseAffine b hb0 hb1).khi = 3 := rfl
/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hsw_rlo : (collapseAffine b hb0 hb1).rlo = 0 := rfl

end Member

/-! ## 2. Case 11: the full-defiance equilibrium -/

/-- The hostile Sender's value against full defiance, `4/27 − (4/3)x`. -/
def hswVS : ChordEconomy.Val := ChordEconomy.affBCF (-4 / 3) (4 / 27)

section Defiance

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- The hostile Sender's objective at the defiance value, completed square.
Scope: at the example economy only (not general). -/
theorem hsw_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).U_S x a s
        + (hostileAffine b hb0 hb1).β_S * hswVS (Sanctions.clipS' ((hostileAffine b hb0 hb1).F x s))
      = (3 / 2 * (2 / 9 - a) ^ 2 - 4 / 3 * x + 2 / 27) - 3 / 2 * (s - (2 / 9 - a)) ^ 2 := by
  unfold hswVS
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (hsw_F_mem hx hs), hsw_U_S,
    hsw_β_S, hsw_F]
  ring

/-- **The hostile response at the defiance value**: `max 0 (2/9 − a)`.
Scope: at the example economy only (not general). -/
theorem hsw_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).σ_dyn_top hswVS x a = max 0 (2 / 9 - a) := by
  rw [σ_dyn_top_eq_clip (hostileAffine b hb0 hb1) hswVS (by norm_num : (0 : ℝ) < 3 / 2)
    (fun s hs => hsw_senderObj hx a hs)]
  rw [min_eq_right (by linarith [ha.1] : 2 / 9 - a ≤ 1)]

/-- **The defiance value is a fixed point of the hostile Sender's Bellman operator against full
defiance.**
Scope: at the example economy only (not general). -/
theorem hswVS_fix :
    (hostileAffine b hb0 hb1).bellmanS_BCF (fun _ => 0) continuous_const hswVS = hswVS := by
  ext y
  change sSup ((fun s => (hostileAffine b hb0 hb1).integrandS (fun _ => 0) (fun z => hswVS z)
    (y.val, s)) '' Sanctions.I) = hswVS y
  have hval : ∀ s ∈ Sanctions.I,
      (hostileAffine b hb0 hb1).integrandS (fun _ => 0) (fun z => hswVS z) (y.val, s)
        = (3 / 2 * (2 / 9 - 0) ^ 2 - 4 / 3 * y.val + 2 / 27) - 3 / 2 * (s - (2 / 9 - 0)) ^ 2 := by
    intro s hs
    have := hsw_senderObj (b := b) (hb0 := hb0) (hb1 := hb1) y.property 0 hs
    simp only [Params.integrandS]
    rw [this]
  have h29 : (2 / 9 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hgt : IsGreatest ((fun s => (hostileAffine b hb0 hb1).integrandS (fun _ => 0)
      (fun z => hswVS z) (y.val, s)) '' Sanctions.I) (hswVS y) := by
    refine ⟨⟨2 / 9, h29, ?_⟩, ?_⟩
    · dsimp only
      rw [hval _ h29]
      unfold hswVS; rw [ChordEconomy.affBCF_apply]; ring
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [hval s hs]
      unfold hswVS; rw [ChordEconomy.affBCF_apply]
      nlinarith [sq_nonneg (s - 2 / 9)]
  exact hgt.csSup_eq

/-- The defiance Target value's slope `60/(2 − b)`. -/
def hswmT (b : ℝ) : ℝ := 60 / (2 - b)
/-- The defiance Target value's intercept. -/
def hswcT (b : ℝ) : ℝ := (-(8 / 9) + b * hswmT b / 9) / (1 - b)
/-- The defiance Target value. -/
def hswVT (b : ℝ) : ChordEconomy.Val := ChordEconomy.affBCF (hswmT b) (hswcT b)

/-- The defiance Target slope identity.
Scope: at the example economy only (not general). -/
theorem hswmT_spec (hb1 : b < 1) : hswmT b * (1 - b / 2) = 30 := by
  have h : (2 : ℝ) - b ≠ 0 := by linarith
  unfold hswmT; field_simp; ring

/-- The defiance Target intercept identity.
Scope: at the example economy only (not general). -/
theorem hswcT_spec (hb1 : b < 1) : hswcT b * (1 - b) = -(8 / 9) + b * hswmT b / 9 := by
  have h : (1 : ℝ) - b ≠ 0 := by linarith
  unfold hswcT; field_simp

/-- **The defiance threshold**: the weight `P = 4 − b·m_T/2` of the sanction in the Target's
objective is at most `1` exactly from `b = 2/11`.
Scope: at the example economy only (not general). -/
theorem hsw_weight_le_one (hb1 : b < 1) (hb : 2 / 11 ≤ b) : 4 - b * hswmT b / 2 ≤ 1 := by
  have h2 : (0 : ℝ) < 2 - b := by linarith
  have e : b * hswmT b = 60 * b / (2 - b) := by unfold hswmT; ring
  have : 6 ≤ b * hswmT b := by rw [e, le_div_iff₀ h2]; linarith
  linarith

/-- The Target's joint objective against the defiance value.
Scope: at the example economy only (not general). -/
theorem hsw_joint {V_T : ChordEconomy.Val} {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).joint_T_top_integrand V_T hswVS x a
      = -a - 4 * max 0 (2 / 9 - a) + 30 * x
        + b * V_T (Sanctions.clipS' ((x + max 0 (2 / 9 - a)) / 2)) := by
  simp only [Params.joint_T_top_integrand]
  rw [hsw_σ_dyn_top hx ha, hsw_U_T, hsw_β_T, hsw_F]

/-- The Target's joint objective at the defiance values, in closed form.
Scope: at the example economy only (not general). -/
theorem hswT_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).joint_T_top_integrand (hswVT b) hswVS x a
      = 30 * x + b * hswmT b * x / 2 + b * hswcT b - a
        - (4 - b * hswmT b / 2) * max 0 (2 / 9 - a) := by
  rw [hsw_joint hx ha]
  have hρ : max 0 (2 / 9 - a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (by linarith [ha.1])⟩
  have hF : (x + max 0 (2 / 9 - a)) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2, hρ.1, hρ.2]
  unfold hswVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hF]
  ring

/-- The Target's gain from complying, against the hostile response, is never positive from
`b = 2/11`: full defiance is a best reply.
Scope: at the example economy only (not general). -/
theorem hsw_defiance_best {x : ℝ} (hx : x ∈ Sanctions.I) (hb1 : b < 1) (hb : 2 / 11 ≤ b)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).joint_T_top_integrand (hswVT b) hswVS x a
      ≤ (hostileAffine b hb0 hb1).joint_T_top_integrand (hswVT b) hswVS x 0 := by
  have hP := hsw_weight_le_one hb1 hb
  rw [hswT_joint hx ha, hswT_joint hx ⟨le_rfl, zero_le_one⟩]
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 2 / 9 - 0)]
  rcases le_total (2 / 9 - a) 0 with h | h
  · rw [max_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_right hP (by norm_num : (0 : ℝ) ≤ 2 / 9)]
  · rw [max_eq_right h]
    nlinarith [mul_le_mul_of_nonneg_left hP ha.1]

end Defiance

/-- **The hostile case-11 equilibrium (`2/11 ≤ b`)**, in closed form: the Target fully defies,
the Sender's value is `4/27 − (4/3)x` and the Target's is `m_T·x + c_T`. AFFINE.
Rule 15: every value is verified to be a fixed point of its Bellman equation. -/
def hostileDefianceEquilibrium (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hb : 2 / 11 ≤ b) :
    (hostileAffine b hb0 hb1).FeedbackStackelbergEquilibriumTop where
  V_T := hswVT b
  V_S := hswVS
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := hswVS_fix.symm
  V_T_fix_top := by
    intro y
    have hm := hswmT_spec hb1
    have hc := hswcT_spec hb1
    have hgt : IsGreatest ((fun a => (hostileAffine b hb0 hb1).joint_T_top_integrand (hswVT b)
        hswVS y.val a) '' Sanctions.I) (hswVT b y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hswT_joint y.property ⟨le_rfl, zero_le_one⟩,
          max_eq_right (by norm_num : (0 : ℝ) ≤ 2 / 9 - 0)]
        unfold hswVT; rw [ChordEconomy.affBCF_apply]
        linear_combination (-y.val) * hm - hc
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        have hval : (hostileAffine b hb0 hb1).joint_T_top_integrand (hswVT b) hswVS y.val 0
            = hswVT b y := by
          rw [hswT_joint y.property ⟨le_rfl, zero_le_one⟩,
            max_eq_right (by norm_num : (0 : ℝ) ≤ 2 / 9 - 0)]
          unfold hswVT; rw [ChordEconomy.affBCF_apply]
          linear_combination (-y.val) * hm - hc
        rw [← hval]
        exact hsw_defiance_best y.property hb1 hb ha
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    exact hsw_defiance_best hx hb1 hb ha

/-! ## 3. Case 01: the relief equilibrium at the profile `01` -/

/-- The relief value `−(4/3)x`. -/
def hswVSR : ChordEconomy.Val := ChordEconomy.affBCF (-4 / 3) 0

/-- The relief Target value `30x − 2/9`. -/
def hswVTR : ChordEconomy.Val := ChordEconomy.affBCF 30 (-(2 / 9))

section Relief

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- The Sender discount factor at the profile `01`.
Scope: at the example economy only (not general). -/
theorem hswR_β_S :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).β_S = 1 / 2 := rfl

/-- The Target discount factor at the profile `01`.
Scope: at the example economy only (not general). -/
theorem hswR_β_T :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).β_T = 0 := by
  simp [Params.profileβ_T, ContinuationProfile.p01]

/-- The hostile Sender's objective at the relief value, completed square.
Scope: at the example economy only (not general). -/
theorem hswR_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).U_S x a s
        + ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).β_S
          * hswVSR (Sanctions.clipS'
            (((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).F x s))
      = (3 / 2 * (2 / 9 - a) ^ 2 - 4 / 3 * x) - 3 / 2 * (s - (2 / 9 - a)) ^ 2 := by
  unfold hswVSR
  rw [hswR_β_S, Params.withProfile_U_S, Params.withProfile_F, ChordEconomy.affBCF_apply,
    Sanctions.clipS'_val_eq_of_mem (hsw_F_mem hx hs), hsw_U_S, hsw_F]
  ring

/-- The hostile response at the relief value: `max 0 (2/9 − a)`.
Scope: at the example economy only (not general). -/
theorem hswR_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).σ_dyn_top hswVSR x a
      = max 0 (2 / 9 - a) := by
  rw [σ_dyn_top_eq_clip _ hswVSR (by norm_num : (0 : ℝ) < 3 / 2)
    (fun s hs => hswR_senderObj hx a hs)]
  rw [min_eq_right (by linarith [ha.1] : 2 / 9 - a ≤ 1)]

/-- Definitional identity at the member.
Scope: at the example economy only (not general). -/
theorem hswVSR_fix :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).bellmanS_BCF
      (fun _ => 2 / 9) continuous_const hswVSR = hswVSR := by
  ext y
  change sSup ((fun s => ((hostileAffine b hb0 hb1).withProfile
    ContinuationProfile.p01).integrandS (fun _ => 2 / 9) (fun z => hswVSR z)
    (y.val, s)) '' Sanctions.I) = hswVSR y
  have hval : ∀ s ∈ Sanctions.I,
      ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).integrandS
        (fun _ => 2 / 9) (fun z => hswVSR z) (y.val, s)
        = (3 / 2 * (2 / 9 - 2 / 9) ^ 2 - 4 / 3 * y.val) - 3 / 2 * (s - (2 / 9 - 2 / 9)) ^ 2 := by
    intro s hs
    have := hswR_senderObj (b := b) (hb0 := hb0) (hb1 := hb1) y.property (2 / 9) hs
    simp only [Params.integrandS]
    rw [this]
  have hgt : IsGreatest ((fun s => ((hostileAffine b hb0 hb1).withProfile
      ContinuationProfile.p01).integrandS (fun _ => 2 / 9) (fun z => hswVSR z) (y.val, s))
      '' Sanctions.I) (hswVSR y) := by
    refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
    · dsimp only
      rw [hval 0 ⟨le_rfl, zero_le_one⟩]
      unfold hswVSR; rw [ChordEconomy.affBCF_apply]; ring
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [hval s hs]
      unfold hswVSR; rw [ChordEconomy.affBCF_apply]
      nlinarith [sq_nonneg s]
  exact hgt.csSup_eq

/-- The myopic Target's objective against the relief response.
Scope: at the example economy only (not general). -/
theorem hswR_joint {V_T : ChordEconomy.Val} {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).joint_T_top_integrand
        V_T hswVSR x a
      = -a - 4 * max 0 (2 / 9 - a) + 30 * x := by
  simp only [Params.joint_T_top_integrand]
  rw [hswR_σ_dyn_top hx ha, hswR_β_T, Params.withProfile_U_T, hsw_U_T]
  ring

/-- The myopic Target's best reply against the hostile relief response is `2/9`.
Scope: at the example economy only (not general). -/
theorem hswR_relief_best {V_T : ChordEconomy.Val} {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).joint_T_top_integrand
        V_T hswVSR x a
      ≤ ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).joint_T_top_integrand
        V_T hswVSR x (2 / 9) := by
  rw [hswR_joint hx ha, hswR_joint hx ⟨by norm_num, by norm_num⟩, sub_self, max_self]
  rcases le_total (2 / 9 - a) 0 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

end Relief

/-- **The hostile case-01 equilibrium**, in closed form: the myopic Target complies at `2/9`, the
forward-looking hostile Sender then does not sanction, its value is the relief value `−(4/3)x`,
and the Target's value is `30x − 2/9`. AFFINE. Rule 15: every value is verified to be a fixed
point of its Bellman equation. -/
def hostileReliefEquilibrium (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (hostileAffine b hb0 hb1).RegimeEquilibrium ContinuationProfile.p01 where
  V_T := hswVTR
  V_S := hswVSR
  α := fun _ => 2 / 9
  hα := continuous_const
  α_mem := fun _ _ => ⟨by norm_num, by norm_num⟩
  V_S_fix := hswVSR_fix.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => ((hostileAffine b hb0 hb1).withProfile
        ContinuationProfile.p01).joint_T_top_integrand hswVTR hswVSR y.val a) '' Sanctions.I)
        (hswVTR y) := by
      have hval : ((hostileAffine b hb0 hb1).withProfile
          ContinuationProfile.p01).joint_T_top_integrand hswVTR hswVSR y.val (2 / 9)
          = hswVTR y := by
        rw [hswR_joint y.property ⟨by norm_num, by norm_num⟩]
        unfold hswVTR; rw [ChordEconomy.affBCF_apply]
        rw [sub_self, max_self]; ring
      refine ⟨⟨2 / 9, ⟨by norm_num, by norm_num⟩, hval⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [← hval]
      exact hswR_relief_best y.property ha
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    exact hswR_relief_best hx ha

/-! ## 4. The realised objects -/

section Realised

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- **The realised hostile sanction against full defiance is `2/9`** at every feasible state.
Scope: at the example economy only (not general). -/
theorem hsw_defiance_rule (hb : 2 / 11 ≤ b) {x : ℝ} (hx : x ∈ Sanctions.I) :
    (hostileAffine b hb0 hb1).dynamicEquilibriumRule
      (hostileDefianceEquilibrium b hb0 hb1 hb) x = 2 / 9 := by
  change (hostileAffine b hb0 hb1).σ_dyn_top hswVS x 0 = 2 / 9
  rw [hsw_σ_dyn_top hx ⟨le_rfl, zero_le_one⟩]
  norm_num

/-- **The realised hostile sanction in the relief equilibrium is zero** at every feasible state.
Scope: at the example economy only (not general). -/
theorem hsw_relief_rule {x : ℝ} (hx : x ∈ Sanctions.I) :
    ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).dynamicEquilibriumRule
      (hostileReliefEquilibrium b hb0 hb1) x = 0 := by
  change ((hostileAffine b hb0 hb1).withProfile ContinuationProfile.p01).σ_dyn_top hswVSR x
    (2 / 9) = 0
  rw [hswR_σ_dyn_top hx ⟨by norm_num, by norm_num⟩]
  norm_num

/-- **The constructed hostile defiance value is `4/27 − (4/3)x`** (Banach uniqueness).
Scope: at the example economy only (not general). -/
theorem hsw_defianceValue_eq :
    (collapseAffine b hb0 hb1).toChordEconomy.hostileDefianceValue 2 = hswVS := by
  have hcontr := (hostileAffine b hb0 hb1).bellmanS_BCF_contracting
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  change (hostileAffine b hb0 hb1).V_S (fun _ => 0) continuous_const = hswVS
  unfold Params.V_S
  exact (ContractingWith.fixedPoint_unique hcontr hswVS_fix).symm

/-- **The relief value of the member is `−(4/3)x`** (Banach uniqueness of the zero-sanction
recursion).
Scope: at the example economy only (not general). -/
theorem hsw_reliefValue_eq : (hostileAffine b hb0 hb1).reliefValue = hswVSR := by
  symm
  apply (hostileAffine b hb0 hb1).eq_reliefValue_of_fix
  ext y
  have h0 : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  rw [Params.zeroSanctionOp_apply, hsw_U_S, hsw_β_S]
  unfold hswVSR
  rw [ChordEconomy.affBCF_apply, ChordEconomy.affBCF_apply,
    Sanctions.clipS'_val_eq_of_mem (hsw_F_mem y.property h0), hsw_F]
  ring

/-- **The member's myopic zero level is `1/3`** at every feasible state.
Scope: at the example economy only (not general). -/
theorem hsw_zeroLevel00 (x : ℝ) : (collapseAffine b hb0 hb1).zeroLevel00 x = 1 / 3 := by
  have hσ : ∀ a, 0 ≤ a → (collapseAffine b hb0 hb1).σ x a = max 0 (1 / 3 - a) :=
    fun a ha => hsw_σ (b := b) (hb0 := hb0) (hb1 := hb1) x ha
  have hleast : IsLeast (Sanctions.ZeroLevel.zeroSet (collapseAffine b hb0 hb1).σ x) (1 / 3) := by
    refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
    · change (collapseAffine b hb0 hb1).σ x (1 / 3) = 0
      rw [hσ _ (by norm_num)]; norm_num
    · rintro a ⟨ha, h0⟩
      have h0' : (collapseAffine b hb0 hb1).σ x a = 0 := h0
      rw [hσ a ha.1] at h0'
      by_contra hlt
      have : 0 < 1 / 3 - a := by linarith [not_le.mp hlt]
      rw [max_eq_right this.le] at h0'
      linarith
  exact hleast.csInf_eq

/-- **The hostile relief price at the member is `2/9`** at every feasible state.
Scope: at the example economy only (not general). -/
theorem hsw_hostileZeroLevel {x : ℝ} (hx : x ∈ Sanctions.I) :
    (collapseAffine b hb0 hb1).toChordEconomy.hostileZeroLevel 2 x = 2 / 9 := by
  unfold ChordEconomy.hostileZeroLevel
  change Sanctions.ZeroLevel.level
    (fun x a => (hostileAffine b hb0 hb1).σ_dyn_top (hostileAffine b hb0 hb1).reliefValue x a)
    x = 2 / 9
  rw [hsw_reliefValue_eq]
  have hR : ∀ a ∈ Sanctions.I, (hostileAffine b hb0 hb1).σ_dyn_top hswVSR x a
      = max 0 (2 / 9 - a) := by
    intro a ha
    have h := hswR_σ_dyn_top (b := b) (hb0 := hb0) (hb1 := hb1) hx ha
    exact h
  have hleast : IsLeast (Sanctions.ZeroLevel.zeroSet
      (fun x a => (hostileAffine b hb0 hb1).σ_dyn_top hswVSR x a) x) (2 / 9) := by
    refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
    · change (hostileAffine b hb0 hb1).σ_dyn_top hswVSR x (2 / 9) = 0
      rw [hR _ ⟨by norm_num, by norm_num⟩]; norm_num
    · rintro a ⟨ha, h0⟩
      have h0' : (hostileAffine b hb0 hb1).σ_dyn_top hswVSR x a = 0 := h0
      rw [hR a ha] at h0'
      by_contra hlt
      have : 0 < 2 / 9 - a := by linarith [not_le.mp hlt]
      rw [max_eq_right this.le] at h0'
      linarith
  exact hleast.csInf_eq

/-- **The hostile case-11 path converges to `2/9`**, from every feasible start:
`x_t = 2/9 + (x₀ − 2/9)/2^t`.
Scope: at the example economy only (not general). -/
theorem hsw_defiance_path_tendsto (hb : 2 / 11 ≤ b) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((hostileAffine b hb0 hb1).rulePathF ((hostileAffine b hb0 hb1).dynamicEquilibriumRule
      (hostileDefianceEquilibrium b hb0 hb1 hb)) x₀) atTop (𝓝 (2 / 9)) := by
  set R := (hostileAffine b hb0 hb1).dynamicEquilibriumRule
    (hostileDefianceEquilibrium b hb0 hb1 hb) with hR_def
  have hmem := (hostileAffine b hb0 hb1).rulePathF_mem_I
    (fun x _ => (hostileAffine b hb0 hb1).dynamicTopRealizedRule_mem _ _ x) hx₀ (R := R)
  have hform : ∀ t, (hostileAffine b hb0 hb1).rulePathF R x₀ t
      = 2 / 9 + (x₀ - 2 / 9) * (1 / 2) ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Params.rulePathF_succ]
      unfold Params.ruleStepF
      rw [hR_def, hsw_defiance_rule hb (hmem k), hsw_F, ← hR_def, ih, pow_succ]
      ring
  have hlim : Tendsto (fun t : ℕ => 2 / 9 + (x₀ - 2 / 9) * (1 / 2 : ℝ) ^ t) atTop
      (𝓝 (2 / 9 + (x₀ - 2 / 9) * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _).const_add _
  rw [mul_zero, add_zero] at hlim
  exact hlim.congr (fun t => (hform t).symm)

/-- **The stage-rule (case-10) path of the member converges to `1/3`**, from every feasible
start.
Scope: at the example economy only (not general). -/
theorem hsw_stageRulePath_tendsto {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((collapseAffine b hb0 hb1).stageRulePath x₀) atTop (𝓝 (1 / 3)) := by
  have hmem := (collapseAffine b hb0 hb1).toParams.rulePathF_mem_I
    (fun x _ => (collapseAffine b hb0 hb1).stageResp_mem x) hx₀
  have hform : ∀ t, (collapseAffine b hb0 hb1).stageRulePath x₀ t
      = 1 / 3 + (x₀ - 1 / 3) * (1 / 2) ^ t := by
    intro t
    induction t with
    | zero => simp [ChordEconomy.stageRulePath]
    | succ k ih =>
      unfold ChordEconomy.stageRulePath at ih ⊢
      rw [Params.rulePathF_succ]
      unfold Params.ruleStepF
      rw [ih]
      unfold ChordEconomy.stageResp
      have hF : ∀ x s, (collapseAffine b hb0 hb1).toParams.F x s = (x + s) / 2 :=
        fun x s => hsw_F (b := b) (hb0 := hb0) (hb1 := hb1) x s
      have hσ : ∀ x, (collapseAffine b hb0 hb1).toParams.σ x 0 = 1 / 3 := by
        intro x
        rw [show (collapseAffine b hb0 hb1).toParams.σ x 0
            = (hostileAffine b hb0 hb1).σ x 0 from rfl, hsw_σ x le_rfl]
        norm_num
      rw [hF, hσ, pow_succ]
      ring
  have hlim : Tendsto (fun t : ℕ => 1 / 3 + (x₀ - 1 / 3) * (1 / 2 : ℝ) ^ t) atTop
      (𝓝 (1 / 3 + (x₀ - 1 / 3) * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _).const_add _
  rw [mul_zero, add_zero] at hlim
  exact hlim.congr (fun t => (hform t).symm)

end Realised

/-! ## 5. The hypotheses of the hostile class results hold at the member -/

section Hypotheses

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- **The hostile stake bound at rate `1`, at every sanction level** (approved hypothesis 3,
witnessed).
Scope: at the example economy only (not general). -/
theorem hsw_stake : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
    ((collapseAffine b hb0 hb1).toChordEconomy.hostileParams 2).U_S x₂ 0 s
      - ((collapseAffine b hb0 hb1).toChordEconomy.hostileParams 2).U_S x₁ 0 s
      ≤ -(1 * (x₂ - x₁)) := by
  intro s _ x₁ _ x₂ _ _
  rw [hsw_U_S, hsw_U_S]
  linarith

/-- **The residual appetite** `u_lo = 1 > 1/3 = β_S·K_S·d_hi` (approved hypothesis 4,
witnessed).
Scope: at the example economy only (not general). -/
theorem hsw_residual :
    (collapseAffine b hb0 hb1).β_S * chKS (collapseAffine b hb0 hb1).β_S
        (collapseAffine b hb0 hb1).ghi (2 - (collapseAffine b hb0 hb1).wlo)
        * (collapseAffine b hb0 hb1).dhi < (collapseAffine b hb0 hb1).ulo := by
  rw [hsw_βS, hsw_ghi, hsw_wlo, hsw_dhi, hsw_ulo]
  unfold chKS; norm_num

/-- The stage appetite `u_hi = 1 < 3 = q`.
Scope: at the example economy only (not general). -/
theorem hsw_stageAppetite : (collapseAffine b hb0 hb1).uhi < (collapseAffine b hb0 hb1).q := by
  rw [hsw_uhi, hsw_q]; norm_num

/-- The stage placability `u_hi = 1 < 3 = k_lo`.
Scope: at the example economy only (not general). -/
theorem hsw_stagePlacable : (collapseAffine b hb0 hb1).uhi < (collapseAffine b hb0 hb1).klo := by
  rw [hsw_uhi, hsw_klo]; norm_num

/-- The loss-offset condition holds from `b = 4/17`: `4 ≤ b·(1/2)·30/(1 − b/2)`.
Scope: at the example economy only (not general). -/
theorem hsw_lossOffset (hb : 4 / 17 ≤ b) : (collapseAffine b hb0 hb1).LossOffset := by
  change (4 : ℝ) ≤ b * (1 / 2) * ((30 + 0 * (collapseAffine b hb0 hb1).sfloor) / (1 - b * (1 / 2)))
  rw [zero_mul, add_zero]
  have h : (0 : ℝ) < 1 - b * (1 / 2) := by linarith
  rw [show b * (1 / 2) * (30 / (1 - b * (1 / 2))) = 15 * b / (1 - b * (1 / 2)) by
    field_simp; ring, le_div_iff₀ h]
  linarith

end Hypotheses

/-! ## 6. The three mirror bounds are attained -/

section Attained

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- **The reverse wedge is attained** (the mirror of `rem:wedge-sharp`): at every feasible state
the hostile Sender's response to defiance at its constructed value, `2/9`, equals the class bound
`max 0 (σᴹ(x,0) − β_S·ḡ_S·d_lo/Q̄)` at the stake rate `w̄ = 1` (`ḡ_S = 4/3`, wedge `1/9`); it is
also the realised sanction of the case-11 equilibrium.
Scope: at the example economy only (not general); rare case: hostile Sender (hypotheses 3–4). -/
theorem hsw_wedge_attained {x : ℝ} (hx : x ∈ Sanctions.I) :
    ((collapseAffine b hb0 hb1).toChordEconomy.hostileParams 2).σ_dyn_top
        ((collapseAffine b hb0 hb1).toChordEconomy.hostileDefianceValue 2) x 0
      = max 0 ((collapseAffine b hb0 hb1).σ x 0
          - (collapseAffine b hb0 hb1).β_S * chGS (collapseAffine b hb0 hb1).β_S
              (collapseAffine b hb0 hb1).glo 1 * (collapseAffine b hb0 hb1).dlo
            / (collapseAffine b hb0 hb1).Qbar) := by
  rw [hsw_defianceValue_eq]
  have h := hsw_σ_dyn_top (b := b) (hb0 := hb0) (hb1 := hb1) hx ⟨le_rfl, zero_le_one⟩
  change (hostileAffine b hb0 hb1).σ_dyn_top hswVS x 0 = _
  rw [h, show (collapseAffine b hb0 hb1).σ x 0 = (hostileAffine b hb0 hb1).σ x 0 from rfl,
    hsw_σ x le_rfl, hsw_βS, hsw_glo, hsw_dlo, hsw_Qbar]
  unfold chGS; norm_num

/-- **The cheaper relief price is attained**: at every feasible state the hostile relief price
`a*(x) = 2/9` equals the class bound `max 0 (a⁰⁰(x) − β_S·ḡ⁰_S·d_lo/k_hi)` at `w̄₀ = 1`,
`k_hi = 3` (`a⁰⁰ = 1/3`, shift `1/9`), and it is the compliance of the relief equilibrium.
Scope: at the example economy only (not general); rare case: hostile Sender (hypotheses 3–4). -/
theorem hsw_relief_price_attained {x : ℝ} (hx : x ∈ Sanctions.I) :
    (collapseAffine b hb0 hb1).toChordEconomy.hostileZeroLevel 2 x
        = max 0 ((collapseAffine b hb0 hb1).zeroLevel00 x
          - (collapseAffine b hb0 hb1).β_S * chGS (collapseAffine b hb0 hb1).β_S
              (collapseAffine b hb0 hb1).glo 1 * (collapseAffine b hb0 hb1).dlo
            / (collapseAffine b hb0 hb1).khi)
      ∧ (hostileReliefEquilibrium b hb0 hb1).α x
        = (collapseAffine b hb0 hb1).toChordEconomy.hostileZeroLevel 2 x := by
  rw [hsw_hostileZeroLevel hx, hsw_zeroLevel00 x, hsw_βS, hsw_glo, hsw_dlo, hsw_khi]
  refine ⟨?_, rfl⟩
  unfold chGS; norm_num

/-- **The long-run gap is attained**: from every feasible start the case-11 path converges to
`z₁₁ = 2/9`, the case-10 path to `z₁₀ = 1/3`, and `z₁₁` equals the class bound
`max 0 (z₁₀ − β_S·ḡ_S·d_lo/(Q̄ − r_lo))` at `w̄ = 1` (gap `1/9`).
Scope: at the example economy only (not general); rare case: hostile Sender (hypotheses 3–4). -/
theorem hsw_limit_attained (hb : 2 / 11 ≤ b) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((hostileAffine b hb0 hb1).rulePathF ((hostileAffine b hb0 hb1).dynamicEquilibriumRule
      (hostileDefianceEquilibrium b hb0 hb1 hb)) x₀) atTop (𝓝 (2 / 9)) ∧
    Tendsto ((collapseAffine b hb0 hb1).stageRulePath x₀) atTop (𝓝 (1 / 3)) ∧
    (2 / 9 : ℝ) = max 0 (1 / 3 - (collapseAffine b hb0 hb1).β_S
      * chGS (collapseAffine b hb0 hb1).β_S (collapseAffine b hb0 hb1).glo 1
      * (collapseAffine b hb0 hb1).dlo
      / ((collapseAffine b hb0 hb1).Qbar - (collapseAffine b hb0 hb1).rlo)) := by
  refine ⟨hsw_defiance_path_tendsto hb hx₀, hsw_stageRulePath_tendsto hx₀, ?_⟩
  rw [hsw_βS, hsw_glo, hsw_dlo, hsw_Qbar, hsw_rlo]
  unfold chGS; norm_num

end Attained

/-! ## 7. The class results at the member -/

section ClassAtMember

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- The window binder `2/11 ≤ b` gives `0 < b`. -/
theorem hsw_hb0_of {b : ℝ} (hb : 2 / 11 ≤ b) : 0 < b := lt_of_lt_of_le (by norm_num) hb

/-- The case-11 bounds at the member, with the discount-range binder `hb0` explicit (the proof;
the public `hsw_full_defiance_bounds` derives it from `hb`). -/
theorem hsw_full_defiance_bounds_core (hb : 2 / 11 ≤ b) :
    (∀ x ∈ Sanctions.I, (hostileAffine b hb0 hb1).dynamicEquilibriumRule
        (hostileDefianceEquilibrium b hb0 hb1 hb) x
        ≤ max 0 ((collapseAffine b hb0 hb1).σ x 0 - (collapseAffine b hb0 hb1).β_S
          * chGS (collapseAffine b hb0 hb1).β_S (collapseAffine b hb0 hb1).glo 1
          * (collapseAffine b hb0 hb1).dlo / (collapseAffine b hb0 hb1).Qbar)) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t,
      (hostileAffine b hb0 hb1).rulePathF ((hostileAffine b hb0 hb1).dynamicEquilibriumRule
        (hostileDefianceEquilibrium b hb0 hb1 hb)) x₀ t
        ≤ (collapseAffine b hb0 hb1).stageRulePath x₀ t) :=
  let h := (collapseAffine b hb0 hb1).toChordEconomy.hostile_full_defiance_bounds 2 one_pos
    hsw_stake hsw_stageAppetite (hostileDefianceEquilibrium b hb0 hb1 hb) (fun _ _ => rfl)
  ⟨h.1, h.2.1⟩

/-- **The case-11 bounds of the class hold at the member's full-defiance equilibrium**
(`hostile_full_defiance_bounds` with `w̄ = 1`, `EH = hostileDefianceEquilibrium`): the hypotheses
of the class theorem are jointly satisfiable together with an equilibrium of the case.
Scope: at the example economy only (not general); rare case: hostile Sender (hypotheses 3–4). -/
theorem hsw_full_defiance_bounds (hb : 2 / 11 ≤ b) :
    (∀ x ∈ Sanctions.I, (hostileAffine b (hsw_hb0_of hb) hb1).dynamicEquilibriumRule
        (hostileDefianceEquilibrium b (hsw_hb0_of hb) hb1 hb) x
        ≤ max 0 ((collapseAffine b (hsw_hb0_of hb) hb1).σ x 0
          - (collapseAffine b (hsw_hb0_of hb) hb1).β_S
          * chGS (collapseAffine b (hsw_hb0_of hb) hb1).β_S
              (collapseAffine b (hsw_hb0_of hb) hb1).glo 1
          * (collapseAffine b (hsw_hb0_of hb) hb1).dlo
          / (collapseAffine b (hsw_hb0_of hb) hb1).Qbar)) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t,
      (hostileAffine b (hsw_hb0_of hb) hb1).rulePathF
        ((hostileAffine b (hsw_hb0_of hb) hb1).dynamicEquilibriumRule
          (hostileDefianceEquilibrium b (hsw_hb0_of hb) hb1 hb)) x₀ t
        ≤ (collapseAffine b (hsw_hb0_of hb) hb1).stageRulePath x₀ t) :=
  hsw_full_defiance_bounds_core hb

/-- **The residual floor's positivity and the cheaper relief price at the member**: the hostile
Sender sanctions a defiant Target at every state, and its relief price is strictly below the
myopic zero level (`hostile_sanction_pos`, `hostile_relief_price` at `w̄ = w̄₀ = 1`, `k_hi = 3`).
Scope: at the example economy only (not general); rare case: hostile Sender (hypotheses 3–4). -/
theorem hsw_sanction_pos_and_relief {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < ((collapseAffine b hb0 hb1).toChordEconomy.hostileParams 2).σ_dyn_top
        ((collapseAffine b hb0 hb1).toChordEconomy.hostileDefianceValue 2) x 0 ∧
    (collapseAffine b hb0 hb1).toChordEconomy.hostileZeroLevel 2 x
      < (collapseAffine b hb0 hb1).zeroLevel00 x := by
  refine ⟨(collapseAffine b hb0 hb1).toChordEconomy.hostile_sanction_pos 2
    hsw_residual hx, ?_⟩
  have h := (collapseAffine b hb0 hb1).toChordEconomy.hostile_relief_price 2 one_pos
    (fun x₁ hx₁ x₂ hx₂ hle => hsw_stake 0 ⟨le_rfl, zero_le_one⟩ x₁ hx₁ x₂ hx₂ hle)
    (collapseAffine b hb0 hb1).toChordEconomyRelief.placationCeiling hsw_stagePlacable hx
  exact h.1.trans_lt h.2

/-- **Cases 10 and 00 at the hostile member are the original ones** (`target_only_regime_any_stake`
and `myopic_regime_any_stake` at `κ = −2`): in case 10 the Target fully defies and the state
converges to a fixed point of the stage rule; in case 00 it buys relief at `a⁰⁰` and the state
converges to `0`. From `b = 4/17` the loss-offset condition holds.
Scope: at the example economy only (not general). -/
theorem hsw_case10_case00 (hb : 4 / 17 ≤ b) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    (∀ x ∈ Sanctions.I,
      ((collapseAffine b hb0 hb1).toChordEconomy.targetOnlyEquilibriumTopShift (-2)
        (hsw_lossOffset hb)).α x = 0) ∧
    (∃ z ∈ Sanctions.I, (collapseAffine b hb0 hb1).σ z 0 = z ∧
      Tendsto ((collapseAffine b hb0 hb1).targetOnlyPath (hsw_lossOffset hb) x₀) atTop (𝓝 z)) ∧
    (∀ x ∈ Sanctions.I,
      ((collapseAffine b hb0 hb1).toChordEconomyRelief.myopicEquilibriumTopShift (-2)
        hsw_stageAppetite (collapseAffine_stageRelief hb0 hb1) hsw_stagePlacable).α x
        = (collapseAffine b hb0 hb1).myopicPolicy x) ∧
    Tendsto ((collapseAffine b hb0 hb1).myopicPathS hsw_stageAppetite
      (collapseAffine_stageRelief hb0 hb1) hsw_stagePlacable x₀) atTop (𝓝 0) := by
  have h10 := (collapseAffine b hb0 hb1).toChordEconomy.target_only_regime_any_stake (-2)
    (hsw_lossOffset hb)
  have h00 := (collapseAffine b hb0 hb1).toChordEconomyRelief.myopic_regime_any_stake (-2)
    hsw_stageAppetite (collapseAffine_stageRelief hb0 hb1) hsw_stagePlacable
  obtain ⟨z, hz, hfix, -, htend⟩ := (h10.2.2 x₀ hx₀).2
  exact ⟨fun x hx => (h10.1 x hx).1, ⟨z, hz, hfix, htend⟩, fun x hx => (h00.1 x hx).1,
    (h00.2.2 x₀ hx₀).2⟩

end ClassAtMember

end

end Examples
end Sanctions
