/-
Sanctions/Examples/AffineWindowBoundaries.lean

**The exact boundaries of the two endpoint profiles at the affine member: the closed
forms** (round BE, 2026-10-03; gap G4 of `suggestions/2026-10-02-lean-gap-map/01_GAP_MAP.md`;
§§2.4–2.5 of
`suggestions/2026-10-03-books-and-mathematical-revalidation/02_MATHEMATICAL_VALIDATION.md`,
checked locally on 2026-10-03 by exact algebra and an independent numerical re-solve).

At the affine member of the quadratic–linear family with Target discount `b ∈ (0,1)`
(`awChord b`, `AffineWindowContinuum.lean`):

1. **Zero sanctions.** The zero-sanction Sender value `4x/3` (`awVS0`), the compliance
   `4/9 + x/6` that just ends the sanction (`awZ`), the relief Target value (`awVTR`), the
   joint objective against them (`awR_joint`), and the threshold algebra
   `b·m_R(b) ≤ 6 ↔ b ≤ 36/197` (`aw_mul_awmR_le_six_iff`).
2. **Full defiance.** The Sender value at defiance
   `((10 − 7√2)/2)x² + (4√2 − 4)x + 8(2 − √2)/7` (`awdVS`, a fixed point of the Sender's
   Bellman operator, `awdVS_fix`), the response `8(√2 − 1)/7 + (3 − 2√2)x`, the defiance
   Target value (`awdVT`), the joint objective against them (`awdT_joint`), and the
   threshold algebra `P(b) ≤ D/3 ↔ (82 − 7√2)/394 ≤ b` (`awdP_le_iff`).
3. **The window** (`aw_boundaries_ordered`, `awβ₁_mem_window`): `36/197 < (82 − 7√2)/394`,
   and the discount `β₁ = 25248/138097` of `AffineWindowContinuum.lean` lies strictly
   between them.

The explicit equilibria at the two endpoints (`awReliefEquilibrium` for `b ≤ 36/197`,
`awDefianceEquilibrium` for `(82 − 7√2)/394 ≤ b`) are kept as closed-form constructions.

The bracket's certificates at this member stop at about `0.180` (relief) and start at
about `0.1875` (certified defiance); the exact boundaries are `36/197 ≈ 0.18274` and
`(82 − 7√2)/394 ≈ 0.18300`.

Renovation item BH3.9 (2026-10-06). The two exact tests (`aw_zero_rule_iff`,
`aw_full_defiance_iff`), their one-way forms (`aw_zero_rule_le`, `aw_full_defiance_le`) and
`aw_window_at_β₁` moved to `AffineWindowInstance.lean`, with unchanged statements. They are
now proved by identifying the general constructed values with the closed forms above and
applying the general exact tests (`exists_relief_equilibrium_iff`,
`exists_defiance_equilibrium_iff`), so they are literally instances of those theorems; the
member-specific uniqueness arguments that proved them here are gone. The general form of
the two intervals is `PlacableSenderExactThresholds.lean`.

**Rule 9.** Statements about one member and two profiles; other policies are not
classified. **Rule 22.** AFFINE: the affine member of the family. **Rule 3.** No assumption
is introduced; the boundaries are computed from the member's own data.
-/
import Sanctions.Examples.AffineWindowContinuum

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 1. Zero sanctions: the closed forms up to `36/197` -/

/-- The compliance level at which the zero-sanction response vanishes, `4/9 + x/6`. -/
def awZ (x : ℝ) : ℝ := 4 / 9 + x / 6

/-- The Sender's value under a zero sanction at every state, `4x/3`. -/
def awVS0 : ChordEconomy.Val := ChordEconomy.affBCF (4 / 3) 0

/-- The relief Target value's slope `179/(6 − 3b)`. -/
def awmR (b : ℝ) : ℝ := 179 / (6 - 3 * b)
/-- The relief Target value's intercept `−4/(9(1 − b))`. -/
def awcR (b : ℝ) : ℝ := -(4 / (9 * (1 - b)))
/-- The relief Target value. -/
def awVTR (b : ℝ) : ChordEconomy.Val := ChordEconomy.affBCF (awmR b) (awcR b)

theorem awZ_mem {x : ℝ} (hx : x ∈ Sanctions.I) : awZ x ∈ Sanctions.I := by
  unfold awZ; constructor <;> linarith [hx.1, hx.2]

theorem half_mem {y : ℝ} (hy : y ∈ (Sanctions.S : Set ℝ)) : y / 2 ∈ (Sanctions.S : Set ℝ) :=
  ⟨by linarith [hy.1], by linarith [hy.2]⟩

section Relief

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

theorem awmR_spec (hb1 : b < 1) : awmR b * (1 - b / 2) = 179 / 6 := by
  have h : (6 : ℝ) - 3 * b ≠ 0 := by linarith
  unfold awmR; field_simp; ring

theorem awcR_spec (hb1 : b < 1) : awcR b * (1 - b) = -(4 / 9) := by
  have h : (1 : ℝ) - b ≠ 0 := by linarith
  unfold awcR; field_simp

theorem aw_mul_awmR_le_six_iff (hb0 : 0 < b) (hb1 : b < 1) :
    b * awmR b ≤ 6 ↔ b ≤ 36 / 197 := by
  have h6 : (0 : ℝ) < 6 - 3 * b := by linarith
  have e : b * awmR b = 179 * b / (6 - 3 * b) := by unfold awmR; ring
  rw [e, div_le_iff₀ h6]
  constructor <;> intro h <;> linarith

theorem aw0_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    (awParams b hb0 hb1).U_S x a s
        + (awParams b hb0 hb1).β_S * awVS0 (Sanctions.clipS' ((awParams b hb0 hb1).F x s))
      = (4 / 3 * x + 3 / 2 * (awZ x - a) ^ 2) - 3 / 2 * (s - (awZ x - a)) ^ 2 := by
  unfold awVS0
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (aw_F_mem hx hs), aw_U_S,
    aw_β_S, aw_F]
  unfold symU_S affineF awZ; ring

theorem aw0_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (awParams b hb0 hb1).σ_dyn_top awVS0 x a = max 0 (awZ x - a) := by
  rw [σ_dyn_top_eq_clip (awParams b hb0 hb1) awVS0 (by norm_num : (0 : ℝ) < 3 / 2)
    (fun s hs => aw0_senderObj hx a hs)]
  rw [min_eq_right (by unfold awZ; linarith [ha.1, hx.2] : awZ x - a ≤ 1)]

theorem aw0_joint {V_T : ChordEconomy.Val} {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    (awParams b hb0 hb1).joint_T_top_integrand V_T awVS0 x a
      = 30 * x - a - 4 * max 0 (awZ x - a)
        + b * V_T (Sanctions.clipS' ((x + max 0 (awZ x - a)) / 2)) := by
  simp only [Params.joint_T_top_integrand]
  rw [aw0_σ_dyn_top hx ha, aw_U_T, aw_β_T, aw_F]
  have harg : affineF (1 / 2) x (max 0 (awZ x - a)) = (x + max 0 (awZ x - a)) / 2 := by
    unfold affineF; ring
  rw [harg]
  unfold symU_T; ring

theorem awR_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 x a
      = 30 * x + b * awmR b * x / 2 + b * awcR b - a
        - (4 - b * awmR b / 2) * max 0 (awZ x - a) := by
  rw [aw0_joint hx ha]
  have hρ : max 0 (awZ x - a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (by unfold awZ; linarith [ha.1, hx.2])⟩
  have hF : (x + max 0 (awZ x - a)) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2, hρ.1, hρ.2]
  unfold awVTR
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hF]
  ring

/-- **The relief equilibrium for `b ≤ 36/197`**, in closed form. The exact test
`aw_zero_rule_iff` (`AffineWindowInstance.lean`) builds its equilibrium through the general
`reliefEquilibriumOfBestReply` instead. AFFINE. -/
def awReliefEquilibrium (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hb : b ≤ 36 / 197) :
    (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop where
  V_T := awVTR b
  V_S := awVS0
  α := awZ
  hα := by unfold awZ; fun_prop
  α_mem := fun _ hx => awZ_mem hx
  V_S_fix := by
    ext y
    change awVS0 y = sSup ((fun s => (awParams b hb0 hb1).integrandS awZ (fun z => awVS0 z)
      (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        (awParams b hb0 hb1).integrandS awZ (fun z => awVS0 z) (y.val, s)
          = 4 / 3 * y.val - 3 / 2 * s ^ 2 := by
      intro s hs
      have := aw0_senderObj (b := b) (hb0 := hb0) (hb1 := hb1) y.property (awZ y.val) hs
      simp only [Params.integrandS]
      rw [this]; ring
    have hgt : IsGreatest ((fun s => (awParams b hb0 hb1).integrandS awZ (fun z => awVS0 z)
        (y.val, s)) '' Sanctions.I) (awVS0 y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval 0 ⟨le_rfl, zero_le_one⟩]
        unfold awVS0; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs]
        unfold awVS0; rw [ChordEconomy.affBCF_apply]
        nlinarith [sq_nonneg s]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hm := awmR_spec hb1
    have hc := awcR_spec hb1
    have hP := (aw_mul_awmR_le_six_iff hb0 hb1).2 hb
    have hgt : IsGreatest ((fun a => (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0
        y.val a) '' Sanctions.I) (awVTR b y) := by
      have hid : awVTR b y = 30 * y.val + b * awmR b * y.val / 2 + b * awcR b - awZ y.val := by
        unfold awVTR; rw [ChordEconomy.affBCF_apply]; unfold awZ
        linear_combination y.val * hm + hc
      refine ⟨⟨awZ y.val, awZ_mem y.property, ?_⟩, ?_⟩
      · dsimp only
        rw [awR_joint y.property (awZ_mem y.property), sub_self, max_self, hid]
        ring
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [awR_joint y.property ha, hid]
        rcases le_total (awZ y.val - a) 0 with h | h
        · rw [max_eq_left h]
          linarith
        · rw [max_eq_right h]
          nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ 6 - b * awmR b)]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    change (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 x a
      ≤ (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 x (awZ x)
    have hP := (aw_mul_awmR_le_six_iff hb0 hb1).2 hb
    rw [awR_joint hx ha, awR_joint hx (awZ_mem hx), sub_self, max_self]
    rcases le_total (awZ x - a) 0 with h | h
    · rw [max_eq_left h]; unfold awZ at h ⊢; nlinarith [h]
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ 6 - b * awmR b)]

end Relief

/-! ## 2. Full defiance: the closed forms from `(82 − 7√2)/394` -/

/-- `√2`. -/
def awds : ℝ := Real.sqrt 2

theorem awds_sq : awds * awds = 2 := Real.mul_self_sqrt (by norm_num)
theorem awds_pos : 0 < awds := Real.sqrt_pos.mpr (by norm_num)
theorem awds_gt : 7 / 5 < awds := by nlinarith [awds_sq, awds_pos]
theorem awds_lt : awds < 71 / 50 := by nlinarith [awds_sq, awds_pos]

/-- The defiance response's slope `p_D = 3 − 2√2`. -/
def awdp : ℝ := 3 - 2 * awds
/-- The Sender's curvature at defiance `D = 7(2 + √2)/8`. -/
def awdD : ℝ := 7 * (2 + awds) / 8
/-- Its inverse `4(2 − √2)/7`. -/
def awdi : ℝ := 4 * (2 - awds) / 7
/-- The Sender value's quadratic coefficient `(10 − 7√2)/2`. -/
def awdη : ℝ := (10 - 7 * awds) / 2
/-- The Sender value's linear coefficient `4√2 − 4`. -/
def awdκ : ℝ := 4 * awds - 4
/-- The rally coefficient of the vertex `7(2 − √2)/8`. -/
def awdB : ℝ := 7 * (2 - awds) / 8
/-- The Sender value's intercept `8(2 − √2)/7`. -/
def awdc : ℝ := 8 * (2 - awds) / 7
/-- The defiance response's intercept `8(√2 − 1)/7`. -/
def awdr : ℝ := 8 * (awds - 1) / 7
/-- **The full-defiance boundary** `β_D = (82 − 7√2)/394`. -/
def awβD : ℝ := (82 - 7 * awds) / 394

theorem awdD_mul_awdi : awdD * awdi = 1 := by
  unfold awdD awdi; linear_combination (-1 / 2 : ℝ) * awds_sq

theorem awdi_pos : 0 < awdi := by unfold awdi; linarith [awds_lt]
theorem awdD_pos : 0 < awdD := by unfold awdD; linarith [awds_pos]
theorem awdp_pos : 0 < awdp := by unfold awdp; linarith [awds_lt]
theorem awdr_pos : 0 < awdr := by unfold awdr; linarith [awds_gt]
theorem awdr_add_awdp_lt_one : awdr + awdp < 1 := by unfold awdr awdp; linarith [awds_gt]

/-- The Sender's value at defiance. -/
def awdVS : ChordEconomy.Val := quadBCF awdη awdκ awdc
/-- The vertex of the Sender's objective against `awdVS`. -/
def awdVertex (x a : ℝ) : ℝ := (awds + awdB * x - 3 * a) * awdi

theorem awdVertex_eq (x a : ℝ) : awdVertex x a = awdr + awdp * x - 3 * a * awdi := by
  unfold awdVertex awdr awdp awdi awdB
  linear_combination ((7 * x - 8) / 14) * awds_sq

theorem awdVertex_le_one {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    awdVertex x a ≤ 1 := by
  rw [awdVertex_eq]
  nlinarith [awdr_add_awdp_lt_one, awdp_pos, awdi_pos, hx.2, ha.1,
    mul_nonneg ha.1 awdi_pos.le, mul_le_mul_of_nonneg_left hx.2 awdp_pos.le]

section Defiance

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

theorem awd_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {z : ℝ} (hz : z ∈ Sanctions.I) :
    (awParams b hb0 hb1).U_S x a z
        + (awParams b hb0 hb1).β_S * awdVS (Sanctions.clipS' ((awParams b hb0 hb1).F x z))
      = (x + awdη / 8 * x ^ 2 + awdκ / 4 * x + awdc / 2 + awdD / 2 * awdVertex x a ^ 2)
        - awdD / 2 * (z - awdVertex x a) ^ 2 := by
  unfold awdVS
  rw [quadBCF_apply, Sanctions.clipS'_val_eq_of_mem (aw_F_mem hx hz), aw_U_S, aw_β_S, aw_F]
  unfold symU_S affineF awdVertex awdη awdκ awdc awdD awdB awdi
  linear_combination (-z * (24 * a + 7 * awds * x - 8 * awds - 14 * x) / 16) * awds_sq

theorem awd_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (awParams b hb0 hb1).σ_dyn_top awdVS x a = max 0 (awdVertex x a) := by
  rw [σ_dyn_top_eq_clip (awParams b hb0 hb1) awdVS (by linarith [awdD_pos] : 0 < awdD / 2)
    (fun z hz => awd_senderObj hx a hz)]
  rw [min_eq_right (awdVertex_le_one hx ha)]

theorem awd_bellman (x : ℝ) :
    x + awdη / 8 * x ^ 2 + awdκ / 4 * x + awdc / 2 + awdD / 2 * (awdr + awdp * x) ^ 2
      = awdη * x ^ 2 + awdκ * x + awdc := by
  unfold awdη awdκ awdc awdD awdr awdp
  linear_combination ((7 * x - 4) * (7 * awds * x - 4 * awds - 7 * x) / 28) * awds_sq

theorem awdVertex_zero_mem {x : ℝ} (hx : x ∈ Sanctions.I) : awdVertex x 0 ∈ Sanctions.I := by
  rw [awdVertex_eq]
  constructor
  · nlinarith [awdr_pos, awdp_pos, hx.1]
  · nlinarith [awdr_add_awdp_lt_one, awdp_pos, hx.2, mul_le_mul_of_nonneg_left hx.2 awdp_pos.le]

/-- **The Sender's value at defiance is a fixed point of its Bellman operator against full
defiance.** -/
theorem awdVS_fix :
    (awParams b hb0 hb1).bellmanS_BCF (fun _ => 0) continuous_const awdVS = awdVS := by
  ext y
  change sSup ((fun s => (awParams b hb0 hb1).integrandS (fun _ => 0) (fun z => awdVS z)
    (y.val, s)) '' Sanctions.I) = awdVS y
  have hval : ∀ s ∈ Sanctions.I,
      (awParams b hb0 hb1).integrandS (fun _ => 0) (fun z => awdVS z) (y.val, s)
        = (y.val + awdη / 8 * y.val ^ 2 + awdκ / 4 * y.val + awdc / 2
            + awdD / 2 * awdVertex y.val 0 ^ 2) - awdD / 2 * (s - awdVertex y.val 0) ^ 2 := by
    intro s hs
    have := awd_senderObj (b := b) (hb0 := hb0) (hb1 := hb1) y.property 0 hs
    simp only [Params.integrandS]
    rw [this]
  have hv := awdVertex_zero_mem y.property
  have hgt : IsGreatest ((fun s => (awParams b hb0 hb1).integrandS (fun _ => 0)
      (fun z => awdVS z) (y.val, s)) '' Sanctions.I) (awdVS y) := by
    refine ⟨⟨awdVertex y.val 0, hv, ?_⟩, ?_⟩
    · dsimp only
      rw [hval _ hv, sub_self]
      unfold awdVS; rw [quadBCF_apply]
      have := awd_bellman y.val
      rw [awdVertex_eq] at *
      linarith
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [hval s hs]
      unfold awdVS; rw [quadBCF_apply]
      have := awd_bellman y.val
      rw [awdVertex_eq] at *
      nlinarith [mul_nonneg awdD_pos.le (sq_nonneg (s - (awdr + awdp * y.val - 3 * 0 * awdi)))]
  exact hgt.csSup_eq

/-! ### The Target side at defiance -/

/-- `Δ(b) = 1 − b(1 + p_D)/2 > 0`. -/
def awdΔ (b : ℝ) : ℝ := 1 - b * (1 + awdp) / 2
/-- The defiance Target value's slope `(30 − 4p_D)/Δ(b)`. -/
def awdm (b : ℝ) : ℝ := (30 - 4 * awdp) / awdΔ b
/-- The weight of the sanction in the Target's objective, `P(b) = 4 − b·m(b)/2`. -/
def awdP (b : ℝ) : ℝ := 4 - b * awdm b / 2
/-- The defiance Target value's intercept `−P(b)·r/(1 − b)`. -/
def awdcT (b : ℝ) : ℝ := -(awdP b * awdr / (1 - b))
/-- The defiance Target value. -/
def awdVT (b : ℝ) : ChordEconomy.Val := ChordEconomy.affBCF (awdm b) (awdcT b)

theorem awdΔ_pos (hb0 : 0 < b) (hb1 : b < 1) : 0 < awdΔ b := by
  unfold awdΔ awdp
  nlinarith [awds_gt, mul_lt_mul_of_pos_right hb1 (by linarith [awds_lt] : (0 : ℝ) < 2 - awds)]

theorem awdm_spec (hb0 : 0 < b) (hb1 : b < 1) : awdm b * awdΔ b = 30 - 4 * awdp := by
  unfold awdm; exact div_mul_cancel₀ _ (awdΔ_pos hb0 hb1).ne'

theorem awdcT_spec (hb1 : b < 1) : awdcT b * (1 - b) = -(awdP b * awdr) := by
  have h : (1 : ℝ) - b ≠ 0 := by linarith
  unfold awdcT; field_simp

/-- **The threshold identity**: `(P(b) − D/3)·Δ(b) = (197/12)(β_D − b)`. -/
theorem awd_threshold (hb0 : 0 < b) (hb1 : b < 1) :
    (awdP b - awdD / 3) * awdΔ b = 197 / 12 * (awβD - b) := by
  have hm := awdm_spec hb0 hb1
  unfold awdP awβD awdD
  unfold awdΔ at hm ⊢
  unfold awdp at hm ⊢
  linear_combination (-b / 2) * hm + (-7 * b / 24) * awds_sq

theorem awdP_le_iff (hb0 : 0 < b) (hb1 : b < 1) : awdP b ≤ awdD / 3 ↔ awβD ≤ b := by
  have h := awd_threshold hb0 hb1
  have hΔ := awdΔ_pos hb0 hb1
  constructor
  · intro hP
    by_contra hlt
    have hlt' : b < awβD := not_le.mp hlt
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : awdP b - awdD / 3 ≤ 0) hΔ.le]
  · intro hb
    by_contra hlt
    have hlt' : awdD / 3 < awdP b := not_le.mp hlt
    nlinarith [mul_pos (by linarith : 0 < awdP b - awdD / 3) hΔ]

theorem awd_joint {V_T : ChordEconomy.Val} {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    (awParams b hb0 hb1).joint_T_top_integrand V_T awdVS x a
      = 30 * x - a - 4 * max 0 (awdVertex x a)
        + b * V_T (Sanctions.clipS' ((x + max 0 (awdVertex x a)) / 2)) := by
  simp only [Params.joint_T_top_integrand]
  rw [awd_σ_dyn_top hx ha, aw_U_T, aw_β_T, aw_F]
  have harg : affineF (1 / 2) x (max 0 (awdVertex x a)) = (x + max 0 (awdVertex x a)) / 2 := by
    unfold affineF; ring
  rw [harg]
  unfold symU_T; ring

theorem awdT_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS x a
      = 30 * x + b * awdm b * x / 2 + b * awdcT b - a - awdP b * max 0 (awdVertex x a) := by
  rw [awd_joint hx ha]
  have hρ : max 0 (awdVertex x a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (awdVertex_le_one hx ha)⟩
  have hF : (x + max 0 (awdVertex x a)) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hx.1, hx.2, hρ.1, hρ.2]
  unfold awdVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hF]
  unfold awdP
  ring

/-- **The full-defiance equilibrium for `β_D ≤ b`**, in closed form. The exact test
`aw_full_defiance_iff` (`AffineWindowInstance.lean`) builds its equilibrium through the
general `defianceEquilibrium` instead. AFFINE. -/
def awDefianceEquilibrium (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hb : awβD ≤ b) :
    (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop where
  V_T := awdVT b
  V_S := awdVS
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := awdVS_fix.symm
  V_T_fix_top := by
    intro y
    have hm := awdm_spec hb0 hb1
    have hc := awdcT_spec hb1
    have hP := (awdP_le_iff hb0 hb1).2 hb
    have hDi := awdD_mul_awdi
    have hi := awdi_pos
    have hv0 := awdVertex_zero_mem y.property
    have hgt : IsGreatest ((fun a => (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS
        y.val a) '' Sanctions.I) (awdVT b y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [awdT_joint y.property ⟨le_rfl, zero_le_one⟩, max_eq_right hv0.1, awdVertex_eq]
        unfold awdVT; rw [ChordEconomy.affBCF_apply]
        unfold awdΔ at hm
        unfold awdP at hc ⊢
        linear_combination (-y.val) * hm - hc
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [awdT_joint y.property ha]
        have hfix : 30 * y.val + b * awdm b * y.val / 2 + b * awdcT b - 0
            - awdP b * max 0 (awdVertex y.val 0) = awdVT b y := by
          rw [max_eq_right hv0.1, awdVertex_eq]
          unfold awdVT; rw [ChordEconomy.affBCF_apply]
          unfold awdΔ at hm
          unfold awdP at hc ⊢
          linear_combination (-y.val) * hm - hc
        rw [← hfix, max_eq_right hv0.1]
        have hlin := awdVertex_eq y.val a
        have hlin0 := awdVertex_eq y.val 0
        rcases le_total (awdVertex y.val a) 0 with h | h
        · rw [max_eq_left h]
          -- a > (D/3)·v(y,0) ≥ P·v(y,0)
          have hv0' : awdVertex y.val 0 ≤ 3 * a * awdi := by linarith
          have h3 : awdP b * awdVertex y.val 0 ≤ awdD / 3 * awdVertex y.val 0 :=
            mul_le_mul_of_nonneg_right hP hv0.1
          have h4 : awdD / 3 * awdVertex y.val 0 ≤ awdD / 3 * (3 * a * awdi) :=
            mul_le_mul_of_nonneg_left hv0' (by linarith [awdD_pos])
          have h5 : awdD / 3 * (3 * a * awdi) = a := by
            linear_combination a * hDi
          linarith
        · rw [max_eq_right h]
          -- the gain is `a·(3P/D − 1) ≤ 0`
          have h6 : 3 * awdP b * awdi ≤ 1 := by
            have := mul_le_mul_of_nonneg_right hP hi.le
            nlinarith [hDi]
          nlinarith [mul_le_mul_of_nonneg_left h6 ha.1]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    change (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS x a
      ≤ (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS x 0
    have hP := (awdP_le_iff hb0 hb1).2 hb
    have hDi := awdD_mul_awdi
    have hi := awdi_pos
    have hv0 := awdVertex_zero_mem hx
    rw [awdT_joint hx ha, awdT_joint hx ⟨le_rfl, zero_le_one⟩, max_eq_right hv0.1]
    have hlin := awdVertex_eq x a
    have hlin0 := awdVertex_eq x 0
    rcases le_total (awdVertex x a) 0 with h | h
    · rw [max_eq_left h]
      have hv0' : awdVertex x 0 ≤ 3 * a * awdi := by linarith
      have h3 : awdP b * awdVertex x 0 ≤ awdD / 3 * awdVertex x 0 :=
        mul_le_mul_of_nonneg_right hP hv0.1
      have h4 : awdD / 3 * awdVertex x 0 ≤ awdD / 3 * (3 * a * awdi) :=
        mul_le_mul_of_nonneg_left hv0' (by linarith [awdD_pos])
      have h5 : awdD / 3 * (3 * a * awdi) = a := by linear_combination a * hDi
      linarith
    · rw [max_eq_right h]
      have h6 : 3 * awdP b * awdi ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hP hi.le
        nlinarith [hDi]
      nlinarith [mul_le_mul_of_nonneg_left h6 ha.1]

end Defiance

/-! ## 3. The window -/

/-- The two boundaries are ordered: `36/197 < (82 − 7√2)/394`. -/
theorem aw_boundaries_ordered : (36 / 197 : ℝ) < (82 - 7 * Real.sqrt 2) / 394 := by
  change (36 / 197 : ℝ) < awβD
  unfold awβD; nlinarith [awds_lt]

/-- **`β₁` lies strictly inside the window.** -/
theorem awβ₁_mem_window :
    (36 / 197 : ℝ) < awβ₁ ∧ awβ₁ < (82 - 7 * Real.sqrt 2) / 394 := by
  refine ⟨by unfold awβ₁; norm_num, ?_⟩
  change awβ₁ < awβD
  unfold awβ₁ awβD; nlinarith [awds_lt]

end

#print axioms Sanctions.Examples.aw_boundaries_ordered
#print axioms Sanctions.Examples.awβ₁_mem_window

end Examples
end Sanctions
