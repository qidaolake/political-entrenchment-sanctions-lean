/-
Sanctions/Examples/AffineWindowInstance.lean

**The exact window at the affine member is an instance of the general thresholds** (round BF,
2026-10-03).

`PlacableSenderExactThresholds.lean` proves, for every enriched chord economy and a general
transition, that across the members `E.withβT b` the discounts with a zero-rule equilibrium
form an interval `(0, β_R]` and those with a full-defiance equilibrium an interval `[β_D, 1)`:
under `ℓ_hi·L_α ≤ v_lo` on the relief side, and a monotone response with the weak balance on
the defiance side. This file applies it to the affine member.

1. The members are the affine family of `AffineWindowContinuum.lean`: `awE.withβT b` is
   `awChord b` by definition (`awE_withβT`).
2. The general hypotheses hold at the affine member (`aw_general_hypotheses`): interiority,
   placability, zero-sanction neutrality, `ℓ_hi·L_α = 5/23 ≤ 30 = v_lo`, a monotone response at
   full defiance (the rally margin, by flatness) and `c·L_resp/μ = 20/23 ≤ 30`.
3. **The exact tests at the member are instances of the general ones** (renovation item
   BH3.9, 2026-10-06). At `awE.withβT b` the constructed values that the general tests read
   are the closed forms of `AffineWindowBoundaries.lean`: the zero-sanction value `VS01` is
   `4x/3`, the zero level is `4/9 + x/6`, the relief value `VTrel` is `awVTR b`, the Sender
   value at defiance `VSstar` is `awdVS` and the defiance-profile Target value `VTdef` is
   `awdVT b` (`awE_VS01`, `awE_zeroLevel`, `awE_VTrel`, `awE_VSstar`, `awE_VTdef`; each is a
   unique fixed point). The relief best reply then holds iff `b ≤ 36/197`, and the defiance
   best reply iff `(82 − 7√2)/394 ≤ b`. So `exists_relief_equilibrium_iff` and
   `exists_defiance_equilibrium_iff` give the exact tests `aw_zero_rule_iff` and
   `aw_full_defiance_iff`, which moved here from `AffineWindowBoundaries.lean` with their
   statements unchanged, together with `aw_zero_rule_le`, `aw_full_defiance_le` and
   `aw_window_at_β₁`.
4. So the general theorems give the two intervals, and the exact tests identify their
   endpoints (`aw_exact_thresholds`): `β_R = 36/197` and `β_D = (82 − 7√2)/394`, with
   `β_R < β_D`. The margin's patience bound is `4/17` here, above `β_R`, as
   `reliefExistence_lt_margin` requires.

The continuum of equilibria at `β₁` (`aw_continuum`) is not an instance of a general theorem.
It rests on the Target's indifference among compliance levels, which needs a linear compliance
cost and the particular discount `β₁`; it stays an example.

**Rule 22.** AFFINE: one member of the family. **Rule 3.** No assumption is introduced.
-/
import Sanctions.Examples.AffineWindowBoundaries
import Sanctions.Examples.PlacableSenderExactThresholds

namespace Sanctions
namespace Examples

open Set

/-- The affine member as an enriched chord economy (its own Target discount is `1/2`). -/
noncomputable abbrev awE : ChordEconomyCs := placableAffineCs.toChordCs

/-- **The affine family is the general family**: the member at `b` is `awChord b`. -/
theorem awE_withβT (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    awE.withβT b hb0 hb1 = awChord b hb0 hb1 := rfl

/-! ## The general hypotheses at the affine member -/

theorem awE_interior : awE.Interior :=
  placableAffineCs.toChordCs_interior placableAffine_interior

theorem awE_placable : awE.Placable := by
  change placableAffineCs.toPlacableEconomyF.Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableAffineCs, placableAffine]

theorem awE_neutral : awE.ZeroSanctionNeutral :=
  placableAffineCs.toPlacableEconomyF.toChord_zeroSanctionNeutral

theorem awE_mu : awE.mu = 23 / 8 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableAffineCs, placableAffine]

theorem awE_Lresp : awE.Lresp = 5 / 8 := by
  norm_num [ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp, ChordEconomy.KS, chKS,
    ChordEconomyTwoSided.SigC, chSigC, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableAffineCs, placableAffine]

/-- The zero level's Lipschitz constant at the affine member, `L_α = 3·(5/8)/(3·(23/8)) = 5/23`. -/
theorem awE_Lalpha : awE.Lalpha = 5 / 23 := by
  unfold ChordEconomyCs.Lalpha
  rw [placableAffine_Mtot, awE_Lresp, awE_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineCs,
    placableAffine]

/-- **The relief side's rate condition**: `ℓ_hi·L_α = 5/23 ≤ 30 = v_lo`. -/
theorem awE_relief_rate : awE.ℓhi * awE.Lalpha ≤ awE.vlo := by
  rw [awE_Lalpha]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineCs,
    placableAffine]

/-- **A monotone response at full defiance**, from the rally margin, which flatness gives. -/
theorem awE_response_monotone : MonotoneOn (awE.responsePath awE.VSstar) (Icc (0 : ℝ) 1) :=
  awE.toChordEconomyTwoSided.responsePath_monotoneOn_of_margin placableAffine_rallyMargin

/-- **The defiance side's weak balance**: `c·L_resp/μ = 20/23 ≤ 30 = v_lo + n_lo·σ(0,0)`. -/
theorem awE_weak_balance : awE.c * (awE.Lresp / awE.mu) ≤ awE.vlo + awE.nlo * awE.sfloor := by
  rw [awE_Lresp, awE_mu]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineCs,
    placableAffine]

/-- **The general hypotheses hold at the affine member.** -/
theorem aw_general_hypotheses :
    awE.Interior ∧ awE.Placable ∧ awE.ZeroSanctionNeutral ∧ awE.ℓhi * awE.Lalpha ≤ awE.vlo ∧
      MonotoneOn (awE.responsePath awE.VSstar) (Icc (0 : ℝ) 1) ∧
      awE.c * (awE.Lresp / awE.mu) ≤ awE.vlo + awE.nlo * awE.sfloor :=
  ⟨awE_interior, awE_placable, awE_neutral, awE_relief_rate, awE_response_monotone,
    awE_weak_balance⟩

/-! ## The constructed values at the affine member

Renovation item BH3.9 (2026-10-06). The general exact tests read constructed values: the
zero-sanction Sender value `VS01`, the zero level, the relief value `VTrel`, the Sender value at
defiance `VSstar` and the defiance-profile Target value `VTdef`. At the member `awE.withβT b`
each is the unique fixed point of a contraction, and the closed form of
`AffineWindowBoundaries.lean` is a fixed point of the same contraction, so the two agree. -/

section Values

open AbstractGame

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

/-- **The zero-sanction Sender value at the member is `4x/3`**: `awVS0` solves the
zero-sanction operator's fixed-point equation, whose solution is unique. AFFINE. -/
theorem awE_VS01 : (awE.withβT b hb0 hb1).VS01 = awVS0 := by
  have hfix : (awE.withβT b hb0 hb1).relaxOp awVS0 = awVS0 := by
    ext y
    rw [ChordEconomyCs.relaxOp_apply]
    change (awParams b hb0 hb1).U_S y.val 0 0
        + (awParams b hb0 hb1).β_S * awVS0 (Sanctions.clipS' ((awParams b hb0 hb1).F y.val 0))
      = awVS0 y
    rw [aw0_senderObj (b := b) (hb0 := hb0) (hb1 := hb1) y.property 0
      (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)]
    unfold awVS0
    rw [ChordEconomy.affBCF_apply]
    ring
  exact (awE.withβT b hb0 hb1).relaxOp_contracting.fixedPoint_unique'
    (awE.withβT b hb0 hb1).VS01_fix hfix

/-- **The zero level at the member is `4/9 + x/6`**: against `4x/3` the Sender's response to
compliance `a` is `max 0 (4/9 + x/6 − a)`, which vanishes exactly from `4/9 + x/6` on.
AFFINE. -/
theorem awE_zeroLevel {x : ℝ} (hx : x ∈ Sanctions.I) :
    (awE.withβT b hb0 hb1).zeroLevel x = awZ x := by
  have key : ∀ a ∈ Sanctions.I,
      (awE.withβT b hb0 hb1).response (awE.withβT b hb0 hb1).VS01 x a
        = max 0 (awZ x - a) := by
    intro a ha
    rw [(awE.withβT b hb0 hb1).response_eq_top (awE.withβT b hb0 hb1).VS01_mem hx, awE_VS01]
    exact aw0_σ_dyn_top (b := b) (hb0 := hb0) (hb1 := hb1) hx ha
  have hset : (awE.withβT b hb0 hb1).zeroSet x = Icc (awZ x) 1 := by
    ext a
    constructor
    · rintro ⟨ha, hz⟩
      have hz0 : (awE.withβT b hb0 hb1).response (awE.withβT b hb0 hb1).VS01 x a = 0 := hz
      rw [key a ha] at hz0
      exact ⟨by linarith [max_eq_left_iff.mp hz0], ha.2⟩
    · rintro ⟨h1, h2⟩
      have ha : a ∈ Sanctions.I := ⟨le_trans (awZ_mem hx).1 h1, h2⟩
      refine ⟨ha, ?_⟩
      change (awE.withβT b hb0 hb1).response (awE.withβT b hb0 hb1).VS01 x a = 0
      rw [key a ha]
      exact max_eq_left (by linarith)
  rw [ChordEconomyCs.zeroLevel_eq_sInf, hset, csInf_Icc (awZ_mem hx).2]

/-- **The relief value at the member is `awVTR b`**: along the zero level `4/9 + x/6` and
the zero sanction, `awVTR b` solves the relief operator's fixed-point equation, whose
solution is unique. AFFINE. -/
theorem awE_VTrel : (awE.withβT b hb0 hb1).VTrel awE_interior awE_placable = awVTR b := by
  have hfix : (awE.withβT b hb0 hb1).reliefOp awE_interior awE_placable (awVTR b)
      = awVTR b := by
    ext y
    rw [ChordEconomyCs.reliefOp_apply, awE_zeroLevel y.property]
    change (awParams b hb0 hb1).U_T y.val (awZ y.val) 0
        + (awParams b hb0 hb1).β_T * awVTR b (Sanctions.clipS' ((awParams b hb0 hb1).F y.val 0))
      = awVTR b y
    have hF : affineF (1 / 2) y.val 0 ∈ Icc (0 : ℝ) 1 := by
      unfold affineF; constructor <;> linarith [y.property.1, y.property.2]
    have hm := awmR_spec hb1
    have hc := awcR_spec hb1
    rw [aw_U_T, aw_β_T, aw_F]
    unfold awVTR
    rw [ChordEconomy.affBCF_apply, ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hF]
    unfold symU_T affineF awZ
    linear_combination (-y.val) * hm - hc
  exact ((awE.withβT b hb0 hb1).reliefOp_contracting awE_interior awE_placable).fixedPoint_unique'
    ((awE.withβT b hb0 hb1).VTrel_fix awE_interior awE_placable) hfix

/-- **The Sender value at defiance at the member is `awdVS`**: both are fixed points of the
Sender's Bellman operator against full defiance, a contraction. AFFINE. -/
theorem awE_VSstar : (awE.withβT b hb0 hb1).VSstar = awdVS :=
  ((awParams b hb0 hb1).bellmanS_BCF_contracting (α := fun _ => 0)
    continuous_const).fixedPoint_unique' (awE.withβT b hb0 hb1).VSstar_fix awdVS_fix

/-- **The defiance-profile Target value at the member is `awdVT b`**: along full defiance and
the response to `awdVS`, `awdVT b` solves the Target operator's fixed-point equation, whose
solution is unique. AFFINE. -/
theorem awE_VTdef : (awE.withβT b hb0 hb1).VTdef = awdVT b := by
  have hfix : (awE.withβT b hb0 hb1).targetOp (awE.withβT b hb0 hb1).VSstar_mem (awdVT b)
      = awdVT b := by
    ext y
    have e : (awE.withβT b hb0 hb1).targetOp (awE.withβT b hb0 hb1).VSstar_mem (awdVT b) y
        = (awE.withβT b hb0 hb1).toParams.joint_T_top_integrand (awdVT b)
            (awE.withβT b hb0 hb1).VSstar y.val 0 := by
      rw [(awE.withβT b hb0 hb1).joint_T_top_integrand_eq (awE.withβT b hb0 hb1).VSstar_mem _
        y.property]
      rfl
    rw [e, awE_VSstar]
    change (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS y.val 0 = awdVT b y
    have hm := awdm_spec hb0 hb1
    have hc := awdcT_spec hb1
    have hv0 := awdVertex_zero_mem y.property
    rw [awdT_joint y.property ⟨le_rfl, zero_le_one⟩, max_eq_right hv0.1, awdVertex_eq]
    unfold awdVT
    rw [ChordEconomy.affBCF_apply]
    unfold awdΔ at hm
    unfold awdP at hc ⊢
    linear_combination (-y.val) * hm - hc
  exact (((awE.withβT b hb0 hb1).targetOp_contracting
    (awE.withβT b hb0 hb1).VSstar_mem).fixedPoint_unique hfix).symm

end Values

/-! ## The two exact tests at the affine member, as instances of the general ones -/

/-- **The relief best reply at the member holds exactly up to `36/197`.** At the
constructed values the zero level `4/9 + x/6` is a Target best reply at every state iff
`b ≤ 36/197`: at the zero state, defying instead of complying at `4/9` saves `4/9` in
compliance and costs `(4 − b·m_R(b)/2)·4/9` in sanction and continuation. AFFINE. -/
theorem aw_reliefBestReply_iff (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (awE.withβT b hb0 hb1).ReliefBestReply awE_interior awE_placable ↔ b ≤ 36 / 197 := by
  unfold ChordEconomyCs.ReliefBestReply
  rw [awE_VTrel, awE_VS01]
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  constructor
  · intro h
    have hopt := isMaxOn_iff.mp (h 0 h0I) 0 h0I
    rw [awE_zeroLevel h0I] at hopt
    change (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 0 0
      ≤ (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 0 (awZ 0) at hopt
    rw [awR_joint h0I h0I, awR_joint h0I (awZ_mem h0I), sub_self, max_self] at hopt
    have e1 : max 0 (awZ 0 - 0) = 4 / 9 := by unfold awZ; norm_num
    rw [e1] at hopt
    unfold awZ at hopt
    have hbm : b * awmR b ≤ 6 := by nlinarith [hopt]
    exact (aw_mul_awmR_le_six_iff hb0 hb1).1 hbm
  · intro hb x hx
    rw [awE_zeroLevel hx, isMaxOn_iff]
    intro a ha
    change (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 x a
      ≤ (awParams b hb0 hb1).joint_T_top_integrand (awVTR b) awVS0 x (awZ x)
    have hP := (aw_mul_awmR_le_six_iff hb0 hb1).2 hb
    rw [awR_joint hx ha, awR_joint hx (awZ_mem hx), sub_self, max_self]
    rcases le_total (awZ x - a) 0 with h | h
    · rw [max_eq_left h]; unfold awZ at h ⊢; nlinarith [h]
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ 6 - b * awmR b)]

/-- **Zero sanctions exist exactly up to `36/197`.** At the affine member with Target
discount `b ∈ (0,1)`, a top-selector equilibrium whose realised sanction is zero at every
state exists if and only if `b ≤ 36/197`. Renovation item BH3.9 (2026-10-06): the statement
is unchanged; it is now the general exact relief test `exists_relief_equilibrium_iff` at
`awE.withβT b` (whose game is `awParams b`), read through `aw_reliefBestReply_iff`. AFFINE. -/
theorem aw_zero_rule_iff (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (∃ Q : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, (awParams b hb0 hb1).dynamicEquilibriumRule Q x = 0)
      ↔ b ≤ 36 / 197 :=
  ((awE.withβT b hb0 hb1).exists_relief_equilibrium_iff awE_interior awE_placable
    awE_neutral).trans (aw_reliefBestReply_iff b hb0 hb1)

/-- **Every zero-sanction equilibrium has `b ≤ 36/197`**: the forward half of
`aw_zero_rule_iff` (renovation item BH3.9, 2026-10-06; statement unchanged, the
member-specific uniqueness argument replaced by the general test). AFFINE. -/
theorem aw_zero_rule_le {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}
    (Q : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop)
    (hQ : ∀ x ∈ Sanctions.I, (awParams b hb0 hb1).dynamicEquilibriumRule Q x = 0) :
    b ≤ 36 / 197 :=
  (aw_zero_rule_iff b hb0 hb1).1 ⟨Q, hQ⟩

/-- **The defiance best reply at the member holds exactly from `(82 − 7√2)/394`.** At the
constructed values full defiance is a Target best reply at every state iff `β_D ≤ b`: the
gain from complying at `a` is `a·(3P(b)/D − 1)` or less, and at the zero state complying at
`1/10` attains it. AFFINE. -/
theorem aw_defianceBestReply_iff (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (awE.withβT b hb0 hb1).DefianceBestReply ↔ awβD ≤ b := by
  unfold ChordEconomy.DefianceBestReply
  rw [awE_VTdef, awE_VSstar]
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  constructor
  · intro h
    have haI : (1 / 10 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
    have hopt := isMaxOn_iff.mp (h 0 h0I) (1 / 10) haI
    change (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS 0 (1 / 10)
      ≤ (awParams b hb0 hb1).joint_T_top_integrand (awdVT b) awdVS 0 0 at hopt
    rw [awdT_joint h0I haI, awdT_joint h0I h0I] at hopt
    have hva : 0 ≤ awdVertex 0 (1 / 10) := by
      rw [awdVertex_eq]; unfold awdr awdp awdi; nlinarith [awds_gt, awds_lt]
    have hv0 : 0 ≤ awdVertex 0 0 := (awdVertex_zero_mem h0I).1
    rw [max_eq_right hva, max_eq_right hv0, awdVertex_eq, awdVertex_eq] at hopt
    -- `hopt` reads `1/10·(3P·(1/D) − 1) ≤ 0`
    have h6 : 3 * awdP b * awdi ≤ 1 := by nlinarith [hopt]
    have hP : awdP b ≤ awdD / 3 := by
      have hDi := awdD_mul_awdi
      have hD := awdD_pos
      nlinarith [mul_le_mul_of_nonneg_left h6 hD.le]
    exact (awdP_le_iff hb0 hb1).1 hP
  · intro hb x hx
    rw [isMaxOn_iff]
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

/-- **Full defiance exists exactly from `(82 − 7√2)/394`.** At the affine member with Target
discount `b ∈ (0,1)`, a top-selector equilibrium with full defiance at every state exists
if and only if `(82 − 7√2)/394 ≤ b`. Renovation item BH3.9 (2026-10-06): the statement is
unchanged; it is now the general exact defiance test `exists_defiance_equilibrium_iff` at
`awE.withβT b`, read through `aw_defianceBestReply_iff`. AFFINE. -/
theorem aw_full_defiance_iff (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (∃ Q : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Q.α x = 0) ↔ (82 - 7 * Real.sqrt 2) / 394 ≤ b := by
  change _ ↔ awβD ≤ b
  exact (awE.withβT b hb0 hb1).exists_defiance_equilibrium_iff.trans
    (aw_defianceBestReply_iff b hb0 hb1)

/-- **Every full-defiance equilibrium has `β_D ≤ b`**: the forward half of
`aw_full_defiance_iff` (renovation item BH3.9, 2026-10-06; statement unchanged, the
member-specific uniqueness argument replaced by the general test). AFFINE. -/
theorem aw_full_defiance_le {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}
    (Q : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop)
    (hQ : ∀ x ∈ Sanctions.I, Q.α x = 0) : awβD ≤ b :=
  (aw_full_defiance_iff b hb0 hb1).1 ⟨Q, hQ⟩

/-- **At `β₁` neither endpoint profile is an equilibrium, and a continuum is.** Moved from
`AffineWindowBoundaries.lean` with the two exact tests (renovation item BH3.9, 2026-10-06);
statement unchanged. AFFINE. -/
theorem aw_window_at_β₁ :
    (¬ ∃ Q : awP₁.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, awP₁.dynamicEquilibriumRule Q x = 0) ∧
    (¬ ∃ Q : awP₁.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Q.α x = 0) ∧
    (∀ t ∈ Icc (0 : ℝ) (4 / 9), ∃ Q : awP₁.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Q.α x = t + 287 / 4206 * x) := by
  refine ⟨fun h => ?_, fun h => ?_, fun t ht => ?_⟩
  · have := (aw_zero_rule_iff awβ₁ awβ₁_pos awβ₁_lt_one).1 h
    linarith [awβ₁_mem_window.1]
  · have := (aw_full_defiance_iff awβ₁ awβ₁_pos awβ₁_lt_one).1 h
    linarith [awβ₁_mem_window.2]
  · obtain ⟨Q, hQ, -⟩ := aw_continuum.1 t ht
    exact ⟨Q, hQ⟩

/-! ## The two existence sets at the affine member -/

theorem awβD_pos : 0 < (82 - 7 * Real.sqrt 2) / 394 := by
  have h := awds_lt
  unfold awds at h
  apply div_pos _ (by norm_num)
  linarith

theorem awβD_lt_one : (82 - 7 * Real.sqrt 2) / 394 < 1 := by
  have h := awds_pos
  unfold awds at h
  rw [div_lt_one (by norm_num)]
  linarith

/-- At the affine member the discounts with a zero-rule equilibrium are exactly `(0, 36/197]`
(`aw_zero_rule_iff`). -/
theorem awE_reliefExistenceSet : awE.reliefExistenceSet = Ioc 0 (36 / 197) := by
  ext b
  constructor
  · rintro ⟨⟨h0, h1⟩, hex⟩
    exact ⟨h0, (aw_zero_rule_iff b h0 h1).1 hex⟩
  · rintro ⟨h0, hb⟩
    have h1 : b < 1 := lt_of_le_of_lt hb (by norm_num)
    exact ⟨⟨h0, h1⟩, (aw_zero_rule_iff b h0 h1).2 hb⟩

/-- At the affine member the discounts with a full-defiance equilibrium are exactly
`[(82 − 7√2)/394, 1)` (`aw_full_defiance_iff`). -/
theorem awE_defianceExistenceSet :
    awE.defianceExistenceSet = Ico ((82 - 7 * Real.sqrt 2) / 394) 1 := by
  ext b
  constructor
  · rintro ⟨⟨h0, h1⟩, hex⟩
    exact ⟨(aw_full_defiance_iff b h0 h1).1 hex, h1⟩
  · rintro ⟨hb, h1⟩
    have h0 : 0 < b := lt_of_lt_of_le awβD_pos hb
    exact ⟨⟨h0, h1⟩, (aw_full_defiance_iff b h0 h1).2 hb⟩

/-- The margin's patience bound at the affine member, `c/(d_lo·v_lo + c·g_lo) = 4/17`. -/
theorem awE_margin_bound : awE.c / (awE.dlo * awE.vlo + awE.c * awE.glo) = 4 / 17 := by
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineCs,
    placableAffine]

/-- **The affine window is an instance of the general thresholds.** At the affine member the
two existence sets are the intervals that `reliefExistenceSet_eq_Ioc` and
`defianceExistenceSet_eq_Ico` give, applied with `aw_general_hypotheses`; the member's own
computation identifies their endpoints, `β_R = 36/197` and `β_D = (82 − 7√2)/394`; the two are
ordered, `β_R < β_D`, so the window between them is non-empty; and `β_R` lies below the margin's
patience bound `4/17`. -/
theorem aw_exact_thresholds :
    awE.reliefExistenceSet = Ioc 0 (sSup awE.reliefExistenceSet) ∧
      awE.defianceExistenceSet = Ico (sInf awE.defianceExistenceSet) 1 ∧
      sSup awE.reliefExistenceSet = 36 / 197 ∧
      sInf awE.defianceExistenceSet = (82 - 7 * Real.sqrt 2) / 394 ∧
      sSup awE.reliefExistenceSet < sInf awE.defianceExistenceSet ∧
      sSup awE.reliefExistenceSet < awE.c / (awE.dlo * awE.vlo + awE.c * awE.glo) := by
  have hRsup : sSup awE.reliefExistenceSet = 36 / 197 := by
    rw [awE_reliefExistenceSet]
    exact csSup_Ioc (by norm_num)
  have hDinf : sInf awE.defianceExistenceSet = (82 - 7 * Real.sqrt 2) / 394 := by
    rw [awE_defianceExistenceSet]
    exact csInf_Ico awβD_lt_one
  refine ⟨?_, ?_, hRsup, hDinf, ?_, ?_⟩
  · refine awE.reliefExistenceSet_eq_Ioc awE_interior awE_placable awE_neutral awE_relief_rate
      ?_
    rw [hRsup]
    norm_num
  · refine awE.defianceExistenceSet_eq_Ico awE_response_monotone awE_weak_balance ?_
    rw [hDinf]
    exact awβD_pos
  · rw [hRsup, hDinf]
    exact aw_boundaries_ordered
  · rw [hRsup, awE_margin_bound]
    norm_num

#print axioms Sanctions.Examples.aw_general_hypotheses
#print axioms Sanctions.Examples.aw_zero_rule_iff
#print axioms Sanctions.Examples.aw_full_defiance_iff
#print axioms Sanctions.Examples.aw_window_at_β₁
#print axioms Sanctions.Examples.aw_exact_thresholds

end Examples
end Sanctions
