/-
Sanctions/Examples/SymbolicCertifiedFamilyGeneralFCertificate.lean

**The Milgrom–Shannon certificate for the general-transition family.**

Builds `StandardComplianceLocalCoreCertificate_MS` for `SymbolicEconomyF`,
using the lower-chord Target discharger from
`Theory/Certificates/GeneralFDischargers.lean` in place of the affine one, and
the cone carrier with its compliance-local Sender argmax uniqueness
(`DAUOnI_on_cone`: strict monotonicity in the sanction at `a ∈ [0,1]`; since plan
item BJ4.3, 2026-10-08, no curvature route).

**The glo/ghi margin gap is closed.** This certificate used to take two extra
arguments, `CornerLo` and `TMarginLo` — the implacability and loss-offset
margins priced at the band's LOWER rate `glo` — because `SymbolicEconomyF`
stated its own `hCorner` / `hTMargin` at `ghi`. The structure now states each
margin at *its own stronger rate* (`hCorner`, `hTMargin` at `glo`) and derives
the other reading, so every declaration below is hypothesis-free in the
margins. The Sender stage margin `hSMargin` and its sanction floor are gone
(plan item BJ4.1, 2026-10-07): the strict stage monotonicity they fed follows
from `u₀ > 0` and `q ≤ r` (`h_stage_sender_strictMonoOn`).

**The persistence core (plan item BJ4.4).** Everything up to W9 is proved for
`SymbolicEconomyFPersist`, the family without the Target's conditions `0 ≤ n`,
`ℓ ≤ c − n` and the loss offset (only `0 ≤ n + v` is kept), and read back for
`SymbolicEconomyF` through `toPersist`. The MS certificate (W11) still needs the
dropped conditions, through the Target combined chord and the myopic
comparator.

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**The results here are universals over a family, not witness instances.** They
are quantified over the symbolic economy variable declared below -- every
admissible member -- so they license universal statements about the family, and
Rule 9's "a witness proves only existence" restriction does **not** apply to
them.

The file sits under `Examples/` because the family fixes a *functional form* for
the stage payoffs, not because its theorems are point checks. Rule 19 keeps
`Theory/` for statements over an arbitrary `Params`; a coefficient-parameterised
algebraic family is narrower than that, so `Examples/` is the correct home and
the file is deliberately not moved.

This banner exists because the filing has already misled an audit. A 2026-08-16
review classified `prop:equilibrium-patience-feedback` as a paper universal
backed only by a witness, having found the numeric `eeCertB_*` names cited in
the formalization map and not the `symbolic_*` siblings in this cluster. The
paper was right and the audit was wrong. If you are deciding what a paper claim
rests on, grep this cluster before concluding that a family-level claim has only
witness backing.
-/

import Sanctions.Examples.SymbolicCertifiedFamilyGeneralF
import Sanctions.Theory.Certificates.GeneralFDischargers

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params Sanctions.TransitionChords Sanctions.Semiconcave

noncomputable section

namespace SymbolicEconomyF

/-! ## W1. (Retired.) The two sign-corrected margins are now structure fields

This section used to define `CornerLo` and `TMarginLo` — the implacability and
loss-offset margins restated at the band's LOWER rate `glo` — and hand them to
every downstream consequence as extra arguments, because `SymbolicEconomyF`
stated its own `hCorner` / `hTMargin` at `ghi`.

The structure now prices **each margin at its own stronger rate**: `hCorner`
and `hTMargin` at `glo`.  Both readings of each are theorems in the CORE
(`hCorner_ghi`, `hTMargin_ghi`), and the value-slope form the corner argument
spends is `SymbolicEconomyF.corner_margin_lo` — also in the CORE, and
hypothesis-free.  Nothing below takes a margin argument any more.  (A third
margin, the Sender stage margin `hSMargin`, priced at `ghi`, was deleted by plan
item BJ4.1: the stage monotonicity it fed follows from `u₀ > 0` and `q ≤ r`.) -/

/-- The semiconcavity clause through the clip is closed in BCF: it is an
intersection, over triples `(z₁, z₂, t)`, of preimages of closed half-lines
under continuous point evaluations. Economy-free. It used to cut down the
family's own carrier; since plan item BJ4.3 that carrier is the gain ball alone,
and the clause bounds the semiconcave sub-carrier of
`persistence_generalF_semiconcave` and the placable and chord families'
carriers. -/
theorem semiconcaveClause_isClosed (σ : ℝ) :
    IsClosed {V : Val |
      SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1) σ} := by
  rw [show {V : Val |
        SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1) σ}
      = ⋂ (z₁ : ℝ) (_ : z₁ ∈ Set.Icc (0 : ℝ) 1) (z₂ : ℝ)
            (_ : z₂ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1),
          {V : Val | t * V (Sanctions.clipS' z₁)
              + (1 - t) * V (Sanctions.clipS' z₂)
              - V (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))
            ≤ σ / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2)} from ?_]
  · apply isClosed_iInter; intro z₁
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro z₂
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro t
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro _
    have h₁ : Continuous (fun V : Val => V (Sanctions.clipS' z₁)) :=
      ContinuousEvalConst.continuous_eval_const _
    have h₂ : Continuous (fun V : Val => V (Sanctions.clipS' z₂)) :=
      ContinuousEvalConst.continuous_eval_const _
    have h₃ : Continuous
        (fun V : Val => V (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))) :=
      ContinuousEvalConst.continuous_eval_const _
    exact isClosed_le
      (((continuous_const.mul h₁).add (continuous_const.mul h₂)).sub h₃)
      continuous_const
  · ext V
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h z₁ hz₁ z₂ hz₂ t ht0 ht1; exact h z₁ hz₁ z₂ hz₂ t ht0 ht1
    · intro h z₁ hz₁ z₂ hz₂ t ht0 ht1; exact h z₁ hz₁ z₂ hz₂ t ht0 ht1

end SymbolicEconomyF

namespace SymbolicEconomyFPersist

variable (E : SymbolicEconomyFPersist)

/-! ## W2–W9 on the persistence core (plan item BJ4.4)

Everything the persistence certificate consumes, stated for the core
`SymbolicEconomyFPersist`: the Target carrier, the corner pin of the Sender,
the defiance corner of the Target, closedness, the value class, carrier
invariance, the decoupled Schur rows and the stage fields. The Target enters
only through `0 < ℓ` and `0 ≤ n + v`. `SymbolicEconomyF` reads each item back
through `toPersist` below. General in `F`. -/

/-! ### W2. Target-side closed forms -/

/-- Target corner stage payoff intercept, `U_T(0, ·, 1) = −c`. -/
def stageT0 : ℝ := -E.c

/-- Sup-norm of the Target's corner stage payoff on the state space. -/
def stageNormT : ℝ := max |E.stageT0| |E.stageT0 + E.stageSlopeT|

/-- Target value **lower** state-slope, `g_Tlo = (n+v)/(1 − β_T·glo)`. -/
def gTlo : ℝ := StokeyLucas.bellmanLowerSlopeConstant E.βT E.glo E.stageSlopeT

/-- Target carrier radius. -/
def MT : ℝ := max (StokeyLucas.bellmanNormBound E.βT E.stageNormT) E.gT

/-- The Target carrier's lower slope is nonnegative: the core's analogue of
`SymbolicEconomyF.gTlo_pos`, from `0 ≤ n + v` alone. -/
theorem gTlo_nn : 0 ≤ E.gTlo := by
  simp only [gTlo, StokeyLucas.bellmanLowerSlopeConstant, stageSlopeT]
  exact div_nonneg E.hnv E.ΛgloT_pos.le

theorem gTlo_le_gT : E.gTlo ≤ E.gT := by
  simp only [gTlo, gT, StokeyLucas.bellmanLowerSlopeConstant,
    StokeyLucas.bellmanLipConstant, stageSlopeT]
  rw [div_le_div_iff₀ E.ΛgloT_pos E.ΛT_pos]
  nlinarith [mul_nonneg (mul_nonneg E.hβT0 (sub_nonneg.mpr E.hglo_ghi)) E.hnv]

theorem gT_le_MT : E.gT ≤ E.MT := le_max_right _ _

theorem gTlo_le_MT : E.gTlo ≤ E.MT := le_trans E.gTlo_le_gT E.gT_le_MT

/-- **Target carrier**: the two-sided cone at the derived closed forms —
radius `M_T`, Lipschitz `K_T = g_T`, minimum upward slope `g_Tlo`. -/
def carrierT : Set Val := valLipGainBall E.MT E.gT E.gTlo 0

theorem carrierT_nonempty : E.carrierT.Nonempty :=
  ⟨affineBCF E.gTlo,
    SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gTlo_nn E.gTlo_le_gT E.gTlo_le_MT⟩

/-! ### W3. The Sender's derived response is the corner `σ_dyn ≡ 1`

The core's strict monotonicity of the Sender's dynamic objective in the
sanction, `SymbolicEconomyFPersist.senderObj_strictMonoOn`, moved to §7 of
`SymbolicCertifiedFamilyGeneralF.lean` (plan item BJ4.3, 2026-10-08) so that the
compliance-local uniqueness `DAUOnI_on_cone` can be proved there; its statement
is unchanged. -/

/-- **`σ_dyn` pinned at full sanctions** on the carrier. -/
theorem σ_dyn_eq_one {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.σ_dyn V_S x a = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn (E.senderObj_strictMonoOn hV_S hx ha)

/-- **`σ_dyn_top` pinned at full sanctions.** -/
theorem σ_dyn_top_eq_one {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.σ_dyn_top V_S x a = 1 :=
  WitnessKit.σ_dyn_top_eq_one_of_strictMonoOn
    (E.senderObj_strictMonoOn hV_S hx ha)

/-! ### W4. The Target's derived policy is the defiance corner -/

/-- **The joint Target integrand in closed form.**  With `σ_dyn ≡ 1`,
compliance only costs `ℓ` per unit and buys nothing. -/
theorem joint_T_integrand_eq (V_T : Val)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.joint_T_integrand V_T V_S x a
      = -E.ℓ * a + (E.stageT0 + E.stageSlopeT * x)
        + E.βT * V_T (Sanctions.clipS' (E.F x 1)) := by
  have hσ := E.σ_dyn_eq_one hV_S hx ha
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  simp only [toParams_U_T, symU_T, toParams_β_T, toParams_F, stageT0, stageSlopeT]
  ring

/-- **Target argmax uniqueness on the carriers.** -/
theorem TAU_on_carriers (V_T : Val)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    E.toParams.TargetArgmaxUnique V_T V_S :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn
    fun x hx a₁ ha₁ a₂ ha₂ hlt => by
      simp only [E.joint_T_integrand_eq V_T hV_S hx ha₁,
        E.joint_T_integrand_eq V_T hV_S hx ha₂]
      nlinarith [E.hℓ]

/-- **Full defiance is the Target's argmax** at every feasible state. -/
theorem zero_isMaxOn_joint (V_T : Val)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => E.toParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [E.joint_T_integrand_eq V_T hV_S hx ha,
    E.joint_T_integrand_eq V_T hV_S hx
      (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)]
  nlinarith [ha.1, E.hℓ]

/-! ### W5. Closedness of the cone carrier -/

/-- The Sender carrier is closed: it is the gain ball (since plan item BJ4.3 no
semiconcavity clause is intersected). General in `F`. -/
theorem carrierS_isClosed : IsClosed E.carrierS := valLipGainBall_isClosed _ _ _ _

/-! ### W6. The value class -/

/-- **The asymmetric value class of the persistence core.** Sender uniqueness
is the compliance-local `DAUOnI_on_cone` (plan item BJ4.3, 2026-10-08), the form
`ValueClass2.sender_unique_on` takes; it used to be the curvature-route
`DAU_on_cone`. General in `F`. -/
def valueClass : E.toParams.ValueClass2 where
  carrier_T := E.carrierT
  carrier_S := E.carrierS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := E.carrierS_isClosed
  nonempty_T := E.carrierT_nonempty
  nonempty_S := E.carrierS_nonempty
  sender_unique_on := fun _ hV_S => E.DAUOnI_on_cone hV_S
  target_unique_on := fun V_T _ _V_S hV_S => E.TAU_on_carriers V_T hV_S

/-- **The derived leader policy is the defiance corner, `α_on ≡ 0`.** -/
theorem α_on_eq_zero (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS) :
    E.valueClass.α_on V_T V_S = fun _ => (0 : ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    E.zero_isMaxOn_joint V_T.val V_S.property y.property

/-! ### W7. Bellman images and carrier invariance -/

theorem jointTarget_image (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    E.toParams.jointTarget_BCF_on_S V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) y
      = E.stageT0 + E.stageSlopeT * y.val
        + E.βT * V_T.val (Sanctions.clipS' (E.F y.val 1)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) y
        (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)
        (E.zero_isMaxOn_joint V_T.val V_S.property y.property),
      E.joint_T_integrand_eq V_T.val V_S.property y.property
        (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)]
  ring

theorem bellmanS_image {W : Val} (hW : W ∈ E.carrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * W (Sanctions.clipS' (E.F y.val 1)) := by
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  have hmono := E.senderObj_strictMonoOn hW y.property
    (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)
  have hmax : IsMaxOn
      (fun s => E.toParams.U_S y.val 0 s
        + E.toParams.β_S * W (Sanctions.clipS' (E.toParams.F y.val s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1I hlt)
  rw [WitnessKit.bellmanS_image_of_isMaxOn (p := E.toParams)
      continuous_const W y h1I hmax]
  simp only [toParams_U_S, symU_S, toParams_β_S, toParams_F, stageS0, stageSlopeS]
  ring

/-- **Heterogeneous carrier invariance under the general transition.**
Target leg by the two-sided chord invariance theorem (`F` enters only through
`CornerStateChord`), which needs only `0 ≤ n + v`; Sender leg by the core's
`carrierS_invariant` (the gain ball; no semiconcavity clause since plan item
BJ4.3). -/
theorem valueClass_IsInvariant :
    E.valueClass.IsInvariant := by
  have hβghiT : E.βT * E.ghi < 1 := by linarith [E.ΛT_pos]
  intro V_T V_S
  constructor
  · change E.toParams.jointTarget_BCF_on_S V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) ∈ E.carrierT
    refine Sanctions.AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := E.βT) (glo := E.glo) (ghi := E.ghi) (c₀ := E.stageT0)
      (L_U := E.stageSlopeT) (g_U := E.stageSlopeT) (M_U := E.stageNormT)
      (M := E.MT) (K := E.gT) (g := E.gTlo)
      (stage := fun y => E.stageSlopeT * y) (F := E.F)
      E.hβT0 E.hβT1 E.hglo0 hβghiT E.hnv
      E.gTlo_nn ?_ ?_ ?_ E.F_corner_maps E.hband
      (le_max_left _ _) (le_refl _) (le_refl _)
      V_T.property (fun y => E.jointTarget_image V_T V_S y)
    · intro y hy
      exact abs_affine_le_max_endpoints E.hnv hy
    · intro y₁ _ y₂ _
      rw [show E.stageSlopeT * y₂ - E.stageSlopeT * y₁
          = E.stageSlopeT * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ E.stageSlopeT from E.hnv)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
  · change E.toParams.bellmanS_BCF (E.valueClass.α_on V_T V_S)
        (E.valueClass.α_on_continuous V_T V_S) V_S.val ∈ E.carrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (E.α_on_eq_zero V_T V_S)
        (E.valueClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    exact E.carrierS_invariant V_S.property
      (fun y => E.bellmanS_image V_S.property y)

/-! ### W8. Decoupled Schur rows -/

theorem hT_T_op (h_inv : E.valueClass.IsInvariant)
    (V V' : E.valueClass.CarrierT) (W W' : E.valueClass.CarrierS) :
    dist (E.valueClass.jointTargetOp_sub h_inv (V, W))
          (E.valueClass.jointTargetOp_sub h_inv (V', W'))
      ≤ E.βT * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun z => E.stageT0 + E.stageSlopeT * z)
    (φ := fun z => E.F z 1)
    (fun V W y => E.jointTarget_image V W y) V V' W W'

theorem hT_S_op (h_inv : E.valueClass.IsInvariant)
    (V V' : E.valueClass.CarrierT) (W W' : E.valueClass.CarrierS) :
    dist (E.valueClass.jointSenderOp_sub h_inv (V, W))
          (E.valueClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + E.βS * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    (E.α_on_eq_zero) V V' W W'

/-! ### W9. The persistence certificate's stage fields -/

theorem q_lt_k : E.q < E.k := by linarith [E.hqr, E.hk, E.hu₀]

theorem xb_lt_one : E.xb < 1 := E.hxb1

/-- **Carrier `V_T` gain on the basin**, at the LOWER slope `g_Tlo`. -/
theorem hV_T_gain :
    ∀ V_T ∈ E.valueClass.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc E.xb 1) E.gTlo := by
  intro V_T hV_T y₁ y₂ h1 h2 hle
  exact hV_T.2.2 y₁ y₂ ⟨by linarith [h1.1, E.hxb0], h1.2⟩
    ⟨by linarith [h2.1, E.hxb0], h2.2⟩ hle

/-- **Strict stage-Sender monotonicity on the MS sanction range**, from
`u₀ > 0` and `q ≤ r` alone (plan item BJ4.1, 2026-10-07).

On the basin `x ∈ [x̄, 1]` the range is `[0, max x x̄] = [0, x]`. For
`s₁ < s₂` in it the stage chord slope at full defiance is
`u₀ + r·x − (q/2)(s₁ + s₂) ≥ u₀ + (r − q)·x ≥ u₀ > 0`, because `s₁ + s₂ ≤ 2x`.
The proof used to detour through the sanction floor `s̄` and the deleted Sender
stage margin (`m_S = u₀ + r·x̄ − q·s̄ > 0`), copying a bound that the legacy
domain `[0, max x s̄]` needs and this domain does not. General in `F`: the
statement is about the stage payoff only. -/
theorem h_stage_sender_strictMonoOn (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      StrictMonoOn
        (fun s => E.toParams.U_S x (E.valueClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (max E.xb E.xb))) := by
  intro x hx s₁ hs₁ s₂ hs₂ hlt
  have hmx : max x (max E.xb E.xb) = x := by rw [max_self]; exact max_eq_left hx.1
  have hs₁x : s₁ ≤ x := hmx ▸ hs₁.2
  have hs₂x : s₂ ≤ x := hmx ▸ hs₂.2
  have hx0 : 0 ≤ x := le_trans E.hxb0 hx.1
  have hsum : E.q / 2 * (s₁ + s₂) ≤ E.q / 2 * (x + x) :=
    mul_le_mul_of_nonneg_left (add_le_add hs₁x hs₂x) (by linarith [E.hq])
  have hbr : E.u₀ ≤ E.u₀ + E.r * x - E.q / 2 * (s₁ + s₂) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr E.hqr) hx0]
  have hpos : 0 < (s₂ - s₁) * (E.u₀ + E.r * x - E.q / 2 * (s₁ + s₂)) :=
    mul_pos (sub_pos.mpr hlt) (lt_of_lt_of_le E.hu₀ hbr)
  simp only [E.α_on_eq_zero V_T V_S, toParams_U_S, symU_S]
  nlinarith [hpos]

/-- **Single crossing on the dynamic Sender objective**, from strict
monotonicity in the sanction. -/
theorem hSC (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max E.xb E.xb) 1)
      (fun s x => E.toParams.senderDynObjective V_S.val x
        (E.valueClass.α_on V_T V_S x) s) :=
  WitnessKit.singleCrossingOn_of_strictMonoOn
    fun t ht s₁ hs₁ s₂ hs₂ hlt => by
      simp only [E.α_on_eq_zero V_T V_S,
        AbstractGame.Params.senderDynObjective]
      refine E.senderObj_strictMonoOn V_S.property ?_
        (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I) hs₁ hs₂ hlt
      rw [max_self] at ht
      exact ⟨le_trans E.hxb0 ht.1, ht.2⟩

end SymbolicEconomyFPersist

namespace SymbolicEconomyF

variable (E : SymbolicEconomyF)

/-! ## W2–W9 for the family, read through `toPersist`

Each item restates its core version for `SymbolicEconomyF` under its old name
(plan item BJ4.4); the definitions keep their own bodies. The two items the
core cannot state — `gTlo_pos` (strict) and the loss offset in value-slope form
`target_loss_margin_lo` — and the Target stage-loss field
`h_stage_target_loss_any` read `hn`, `hcn` or `hTMargin` and are proved here.
General in `F`. -/

/-! ### W2. Target-side closed forms the CORE did not need -/

/-- Target corner stage payoff intercept, `U_T(0, ·, 1) = −c`. -/
def stageT0 : ℝ := -E.c

/-- Sup-norm of the Target's corner stage payoff on the state space. -/
def stageNormT : ℝ := max |E.stageT0| |E.stageT0 + E.stageSlopeT|

/-- Target value **lower** state-slope, `g_Tlo = (n+v)/(1 − β_T·glo)`. -/
def gTlo : ℝ := StokeyLucas.bellmanLowerSlopeConstant E.βT E.glo E.stageSlopeT

/-- Target carrier radius. -/
def MT : ℝ := max (StokeyLucas.bellmanNormBound E.βT E.stageNormT) E.gT

theorem gTlo_pos : 0 < E.gTlo := by
  simp only [gTlo, StokeyLucas.bellmanLowerSlopeConstant, stageSlopeT]
  exact div_pos E.stageSlopeT_pos E.ΛgloT_pos

theorem gTlo_le_gT : E.gTlo ≤ E.gT := E.toPersist.gTlo_le_gT

theorem gT_le_MT : E.gT ≤ E.MT := le_max_right _ _

theorem gTlo_le_MT : E.gTlo ≤ E.MT := le_trans E.gTlo_le_gT E.gT_le_MT

/-- **Target loss offset in value-slope form**: `c_T ≤ β_T · g_Tlo · dlo`.

Hypothesis-free since the structure prices `hTMargin` at the band's lower rate
`glo`: that is exactly the rate at which the Target carrier's minimum upward
state slope `g_Tlo = (n+v)/(1 − β_T·glo)` is guaranteed. -/
theorem target_loss_margin_lo :
    E.c - E.n * E.xb ≤ E.βT * E.gTlo * E.dlo := by
  have hEq : E.βT * E.gTlo * E.dlo
      = E.βT * E.dlo * E.stageSlopeT / (1 - E.βT * E.glo) := by
    simp only [gTlo, StokeyLucas.bellmanLowerSlopeConstant]
    field_simp
  rw [hEq, le_div_iff₀ E.ΛgloT_pos]
  simpa only [stageSlopeT] using E.hTMargin

/-- **Target carrier**: the two-sided cone at the derived closed forms —
radius `M_T`, Lipschitz `K_T = g_T`, minimum upward slope `g_Tlo`. -/
def carrierT : Set Val := valLipGainBall E.MT E.gT E.gTlo 0

/-- **Bridge to the core**: the core's Target carrier at `E.toPersist` is `E`'s
own carrier, definitionally. -/
theorem toPersist_carrierT : E.toPersist.carrierT = E.carrierT := rfl

theorem carrierT_nonempty : E.carrierT.Nonempty := E.toPersist.carrierT_nonempty

/-! ### W3. The Sender's derived response is the corner `σ_dyn ≡ 1` -/

/-- **The Sender's dynamic objective is strictly increasing in the sanction**,
at every feasible state and compliance, for every carrier value.

This is the CORE's `corner_margin_lo` doing its work — the implacability
margin read at the carrier's guaranteed LOWER continuation slope `g_S`.  The
affine family read the continuation
gain off an EXACT affine value (`carrierS_diff`); a two-sided band has no such
value, so the gain is bounded below instead:

* the carrier's minimum upward state slope gives
  `V_S(F(x,s₂)) − V_S(F(x,s₁)) ≥ g_S · (F(x,s₂) − F(x,s₁))`;
* the **sanction lower chord** gives `F(x,s₂) − F(x,s₁) ≥ dlo·(s₂ − s₁)`;
* the worst stage disincentive is `(q + k − u₀)·(s₂ − s₁)` (compliance at
  full, state at the bottom, sanctions at the top).

`corner_margin_lo` — i.e. the structure's `hCorner`, priced at `glo` — says
the first two beat the third. -/
theorem senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => E.toParams.U_S x a s
        + E.toParams.β_S * V_S (Sanctions.clipS' (E.toParams.F x s)))
      Sanctions.I :=
  E.toPersist.senderObj_strictMonoOn hV_S hx ha

/-- **`σ_dyn` pinned at full sanctions** on the carrier. -/
theorem σ_dyn_eq_one {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.σ_dyn V_S x a = 1 :=
  E.toPersist.σ_dyn_eq_one hV_S hx ha

/-- **`σ_dyn_top` pinned at full sanctions.** -/
theorem σ_dyn_top_eq_one {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.σ_dyn_top V_S x a = 1 :=
  E.toPersist.σ_dyn_top_eq_one hV_S hx ha

/-! ### W4. The Target's derived policy is the defiance corner -/

/-- **The joint Target integrand in closed form.**  With `σ_dyn ≡ 1`,
compliance only costs `ℓ` per unit and buys nothing.  Unlike the affine
family, the continuation argument stays `F(x,1)` — it is not resolved to
`(1−δ)x + δ`. -/
theorem joint_T_integrand_eq (V_T : Val)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.joint_T_integrand V_T V_S x a
      = -E.ℓ * a + (E.stageT0 + E.stageSlopeT * x)
        + E.βT * V_T (Sanctions.clipS' (E.F x 1)) :=
  E.toPersist.joint_T_integrand_eq V_T hV_S hx ha

/-- **Target argmax uniqueness on the carriers.** -/
theorem TAU_on_carriers (V_T : Val)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    E.toParams.TargetArgmaxUnique V_T V_S :=
  E.toPersist.TAU_on_carriers V_T hV_S

/-- **Full defiance is the Target's argmax** at every feasible state. -/
theorem zero_isMaxOn_joint (V_T : Val)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => E.toParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 :=
  E.toPersist.zero_isMaxOn_joint V_T hV_S hx

/-! ### W5. Closedness of the cone carrier -/

theorem carrierS_isClosed : IsClosed E.carrierS := E.toPersist.carrierS_isClosed

/-! ### W6. The value class -/

/-- **The asymmetric value class of the general-transition family.**
Hypothesis-free: the Target's argmax uniqueness runs through `σ_dyn ≡ 1`,
which spends the implacability margin `hCorner` — now a structure field priced
at the band's lower rate `glo`, so nothing needs to be supplied here. Sender
uniqueness is the compliance-local `DAUOnI_on_cone` (plan item BJ4.3,
2026-10-08), from the same strict monotonicity; it used to be the curvature-route
`DAU_on_cone`. General in `F`. -/
def valueClass : E.toParams.ValueClass2 where
  carrier_T := E.carrierT
  carrier_S := E.carrierS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := E.carrierS_isClosed
  nonempty_T := E.carrierT_nonempty
  nonempty_S := E.carrierS_nonempty
  sender_unique_on := fun _ hV_S => E.DAUOnI_on_cone hV_S
  target_unique_on := fun V_T _ _V_S hV_S => E.TAU_on_carriers V_T hV_S

/-- **The derived leader policy is the defiance corner, `α_on ≡ 0`.** -/
theorem α_on_eq_zero (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS) :
    E.valueClass.α_on V_T V_S = fun _ => (0 : ℝ) :=
  E.toPersist.α_on_eq_zero V_T V_S

/-! ### W7. Bellman images and carrier invariance -/

theorem jointTarget_image (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    E.toParams.jointTarget_BCF_on_S V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) y
      = E.stageT0 + E.stageSlopeT * y.val
        + E.βT * V_T.val (Sanctions.clipS' (E.F y.val 1)) :=
  E.toPersist.jointTarget_image V_T V_S y

theorem bellmanS_image {W : Val} (hW : W ∈ E.carrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * W (Sanctions.clipS' (E.F y.val 1)) :=
  E.toPersist.bellmanS_image hW y

/-- **Heterogeneous carrier invariance under the general transition.**
Target leg by the two-sided chord invariance theorem (`F` enters only through
`CornerStateChord`); Sender leg by the CORE's `carrierS_invariant` (the gain
ball; no semiconcavity clause since plan item BJ4.3). -/
theorem valueClass_IsInvariant :
    E.valueClass.IsInvariant := E.toPersist.valueClass_IsInvariant

/-! ### W8. Decoupled Schur rows -/

theorem hT_T_op (h_inv : E.valueClass.IsInvariant)
    (V V' : E.valueClass.CarrierT) (W W' : E.valueClass.CarrierS) :
    dist (E.valueClass.jointTargetOp_sub h_inv (V, W))
          (E.valueClass.jointTargetOp_sub h_inv (V', W'))
      ≤ E.βT * dist V V' + 0 * dist W W' :=
  E.toPersist.hT_T_op h_inv V V' W W'

theorem hT_S_op (h_inv : E.valueClass.IsInvariant)
    (V V' : E.valueClass.CarrierT) (W W' : E.valueClass.CarrierS) :
    dist (E.valueClass.jointSenderOp_sub h_inv (V, W))
          (E.valueClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + E.βS * dist W W' :=
  E.toPersist.hT_S_op h_inv V V' W W'

/-! ## W9. The certificate's stage fields -/

theorem q_lt_k : E.q < E.k := E.toPersist.q_lt_k

theorem xb_lt_one : E.xb < 1 := E.hxb1

/-- **Stage Target loss bound on an arbitrary sanction domain.** -/
theorem h_stage_target_loss_any (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS)
    (D : Set ℝ) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      LowerLossSlopeOn
        (fun s => E.toParams.U_T x (E.valueClass.α_on V_T V_S x) s)
        D (E.c - E.n * E.xb) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [E.α_on_eq_zero V_T V_S, toParams_U_T, symU_T]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) E.hn)
    (sub_nonneg.mpr hx.1)]

/-- **Carrier `V_T` gain on the basin**, at the LOWER slope `g_Tlo`. -/
theorem hV_T_gain :
    ∀ V_T ∈ E.valueClass.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc E.xb 1) E.gTlo :=
  E.toPersist.hV_T_gain

/-- **Strict stage-Sender monotonicity on the MS sanction range**, from
`u₀ > 0` and `q ≤ r` alone (plan item BJ4.1): the core's
`SymbolicEconomyFPersist.h_stage_sender_strictMonoOn`. It no longer reads the
deleted Sender stage margin or the sanction floor. -/
theorem h_stage_sender_strictMonoOn (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      StrictMonoOn
        (fun s => E.toParams.U_S x (E.valueClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (max E.xb E.xb))) :=
  E.toPersist.h_stage_sender_strictMonoOn V_T V_S

/-- **Single crossing on the dynamic Sender objective**, from strict
monotonicity in the sanction. -/
theorem hSC (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max E.xb E.xb) 1)
      (fun s x => E.toParams.senderDynObjective V_S.val x
        (E.valueClass.α_on V_T V_S x) s) :=
  E.toPersist.hSC V_T V_S

/-! ## W10. The myopic comparator (transition-free) -/

/-- **The myopic Target's compliance**: exactly the amount that zeroes the
static Sender's sanction. -/
def myopicAlpha (x : ℝ) : ℝ := (E.u₀ + E.r * x) / E.k

theorem myopicAlpha_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    E.myopicAlpha x ∈ Set.Icc (0 : ℝ) 1 := by
  have hk := E.k_pos
  change (E.u₀ + E.r * x) / E.k ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact div_nonneg (by nlinarith [E.hu₀, E.r_pos, hx.1]) hk.le
  · rw [div_le_one hk]
    nlinarith [E.hk, E.r_pos, hx.2]

theorem myopic_sigma_eq_zero (x : ℝ) :
    E.toParams.σ x (E.myopicAlpha x) = 0 := by
  have hkne : E.k ≠ 0 := ne_of_gt E.k_pos
  have hz : E.u₀ - E.k * ((E.u₀ + E.r * x) / E.k) + E.r * x = 0 := by
    field_simp; ring
  change symσ E.q E.u₀ E.k E.r x (E.myopicAlpha x) = 0
  simp only [symσ, myopicAlpha, hz, zero_div]
  norm_num

/-- **The myopic compliance is interior below the top state, with no strict
placation margin.** Transition-free. For `x < 1`, `r > 0` gives
`u₀ + r·x < u₀ + r`, and the structure's own non-strict `hk : u₀ + r ≤ k`
finishes; the strict margin `u₀ + r < k` is not used. Verbatim the affine
family's `SymbolicEconomy.myopicAlpha_lt_one_of_lt_one`. -/
theorem myopicAlpha_lt_one_of_lt_one {x : ℝ} (hx1 : x < 1) :
    E.myopicAlpha x < 1 := by
  rw [myopicAlpha, div_lt_one E.k_pos]
  linarith [mul_lt_of_lt_one_right E.r_pos hx1, E.hk]

/-- **The myopic compliance is interior at every feasible state, under the
strict placation margin `u₀ + r < k`.** Transition-free. This is the only
place the strict margin enters the myopic argument. -/
theorem myopicAlpha_lt_one_of_strict (hk_strict : E.u₀ + E.r < E.k)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : E.myopicAlpha x < 1 := by
  rw [myopicAlpha, div_lt_one E.k_pos]
  linarith [mul_le_of_le_one_right E.r_pos.le hx.2, hk_strict]

/-- **Every myopic stage argmax zeroes the sanction, wherever the myopic
compliance `a₂ = (u₀ + r·x)/k` is interior.**  Transition-free: the myopic
problem never touches `F`, so this is verbatim the affine family's argument
(`SymbolicEconomy.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one`).

`hα1 : a₂ < 1` replaces the strict placation margin `u₀ + r < k` that
`myopic_argmax_sigma_eq_zero` takes (plan item BG3.7). It holds at every
`x < 1` with no margin (`myopicAlpha_lt_one_of_lt_one`). At the top state with
`u₀ + r = k` it fails, and so can the conclusion: if also `ℓ = c − n`, zero
compliance ties with full compliance in the Target's static objective and
draws the full sanction. -/
theorem myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hα1 : E.myopicAlpha x < 1)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => E.toParams.U_T x a' (E.toParams.σ x a'))
              Sanctions.I a) :
    E.toParams.σ x a = 0 := by
  have hk := E.k_pos
  have hq := E.hq
  have hψ : E.ℓ ≤ E.c - E.n * x := by
    nlinarith [E.hcn, mul_nonneg E.hn (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)]
  have hψ0 : (0 : ℝ) < E.c - E.n * x := lt_of_lt_of_le E.hℓ hψ
  have hka : E.k * E.myopicAlpha x = E.u₀ + E.r * x := by
    simp only [myopicAlpha]; field_simp
  rcases le_or_gt (E.u₀ - E.k * a + E.r * x) 0 with hsign | hsign
  · have ht : (E.u₀ - E.k * a + E.r * x) / E.q ≤ 0 := by
      rw [div_le_iff₀ hq]; linarith
    change symσ E.q E.u₀ E.k E.r x a = 0
    simp only [symσ, min_eq_right (le_trans ht zero_le_one), max_eq_left ht]
  · exfalso
    have ha_lt : a < E.myopicAlpha x := by
      have hmul : E.k * a < E.k * E.myopicAlpha x := by rw [hka]; linarith
      exact lt_of_mul_lt_mul_left hmul E.k_pos.le
    have hgap : (0 : ℝ) < E.myopicAlpha x - a := by linarith
    have hJ := isMaxOn_iff.mp hmax (E.myopicAlpha x) (E.myopicAlpha_mem hx)
    rw [E.myopic_sigma_eq_zero x] at hJ
    simp only [toParams_U_T, symU_T, toParams_σ] at hJ
    have hbound : symσ E.q E.u₀ E.k E.r x a * (E.c - E.n * x)
        ≤ E.ℓ * (E.myopicAlpha x - a) := by nlinarith [hJ]
    have hstrict : E.ℓ * (E.myopicAlpha x - a)
        < symσ E.q E.u₀ E.k E.r x a * (E.c - E.n * x) := by
      have hnum : E.u₀ - E.k * a + E.r * x = E.k * (E.myopicAlpha x - a) := by
        rw [mul_sub, hka]; ring
      have hpos : (0 : ℝ) < (E.u₀ - E.k * a + E.r * x) / E.q := div_pos hsign hq
      rcases le_or_gt ((E.u₀ - E.k * a + E.r * x) / E.q) 1 with ht1 | ht1
      · have hσ : symσ E.q E.u₀ E.k E.r x a
            = (E.u₀ - E.k * a + E.r * x) / E.q := by
          simp only [symσ, min_eq_right ht1, max_eq_right hpos.le]
        have hlq : E.ℓ * E.q < E.k * (E.c - E.n * x) := by
          nlinarith [E.q_lt_k, E.hℓ, hψ, hk, hq]
        rw [hσ, hnum, div_mul_eq_mul_div, lt_div_iff₀ hq]
        nlinarith [mul_lt_mul_of_pos_right hlq hgap]
      · have hσ : symσ E.q E.u₀ E.k E.r x a = 1 := by
          simp only [symσ, min_eq_left ht1.le, max_eq_right zero_le_one]
        rw [hσ, one_mul]
        nlinarith [E.hℓ, ha.1, hα1]
    linarith

/-- **Every myopic stage argmax zeroes the sanction**, at every feasible state,
under the strict placation margin `u₀ + r < k`.  Transition-free.  The
original statement, kept as a one-line corollary of
`myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one`. -/
theorem myopic_argmax_sigma_eq_zero (hk_strict : E.u₀ + E.r < E.k)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => E.toParams.U_T x a' (E.toParams.σ x a'))
              Sanctions.I a) :
    E.toParams.σ x a = 0 :=
  E.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one hx
    (E.myopicAlpha_lt_one_of_strict hk_strict hx) ha hmax

theorem canonical_myopic_sigma_eq_zero (hk_strict : E.u₀ + E.r < E.k)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x) = 0 :=
  E.myopic_argmax_sigma_eq_zero hk_strict hx
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_mem x hx)
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_opt x hx)

/-- **The canonical myopic comparator realises no sanction below the top
state, with no strict placation margin.**  Transition-free.  This is
`canonical_myopic_sigma_eq_zero` with `u₀ + r < k` dropped, at the price of
`x < 1`. -/
theorem canonical_myopic_sigma_eq_zero_of_lt_one {x : ℝ} (hx : x ∈ Sanctions.S)
    (hx1 : x < 1) :
    E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x) = 0 :=
  E.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one hx
    (E.myopicAlpha_lt_one_of_lt_one hx1)
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_mem x hx)
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_opt x hx)

/-- **The canonical myopic ceiling, with no strict placation margin.**
Transition-free.  On the basin `[x̄, 1]` the canonical myopic sanction is at
most `max x x̄`, which is the MS certificate's `hMyoCeiling` field.  Below the
top state the sanction is zero (`canonical_myopic_sigma_eq_zero_of_lt_one`);
at `x = 1` the bound is `max 1 x̄ = 1`, which every static sanction meets by
the feasibility field `σ_mem`.  So the field needs no `u₀ + r < k`. -/
theorem canonical_myopic_ceiling {x : ℝ} (hx : x ∈ Set.Icc E.xb 1) :
    E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x)
      ≤ max x E.xb := by
  rcases hx.2.lt_or_eq with hx1 | rfl
  · rw [E.canonical_myopic_sigma_eq_zero_of_lt_one ⟨le_trans E.hxb0 hx.1, hx.2⟩ hx1]
    exact le_trans E.hxb0 (le_max_right x E.xb)
  · exact le_trans (E.toParams.σ_mem 1 _).2 (le_max_left 1 E.xb)

/-! ## W11. THE GENERAL-`F` MS CERTIFICATE -/

/-- **Every admissible member of the general-transition family with a
strictly interior basin bottom carries a complete MS / general-`F`
certificate.**  General in `F`: the transition enters only through the
structure's chord fields.

The A2 field is discharged by
`Target_combined_chord_of_decomposition_lowerChord` — the affine-free
discharger — with `dlo` in place of `δ` and the Target carrier's LOWER slope
`g_Tlo` in place of `g_T`.

**Dropped hypothesis (plan item BG3.7, 2026-10-06).** The constructor used to
take the strict placation margin `hk_strict : u₀ + r < k`.  It fed only
`hMyoCeiling`, which `canonical_myopic_ceiling` now closes from the
structure's non-strict `hk` and the feasibility field `σ_mem`.  So every
member with `0 < x̄` is certified, including members on the placation
boundary `u₀ + r = k` such as `wobbleEconF`. -/
def certificateMS (hxb_pos : 0 < E.xb) :
    E.toParams.StandardComplianceLocalCoreCertificate_MS where
  D := E.valueClass
  h_inv := E.valueClass_IsInvariant
  β_T := E.βT
  β_S := E.βS
  L_TS := 0
  L_ST := 0
  hβ_T_nn := E.hβT0
  hβ_S_nn := E.hβS0
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := E.hT_T_op (E.valueClass_IsInvariant)
  hT_S_op := E.hT_S_op (E.valueClass_IsInvariant)
  hsuff_T := by simpa using E.hβT1
  hsuff_S := by simpa using E.hβS1
  xT := E.xb
  xS := E.xb
  hxT_mem := ⟨E.hxb0, E.xb_le_one⟩
  hxS_mem := ⟨E.hxb0, E.xb_le_one⟩
  hpivot_mem := by rw [max_self]; exact ⟨hxb_pos, E.xb_lt_one⟩
  h_stage_sender_strictMono := E.h_stage_sender_strictMonoOn
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (E.hSC V_T V_S)
  h_target_combined :=
    E.toParams.Target_combined_chord_of_decomposition_lowerChord
      (D := E.valueClass) ⟨E.hxb0, E.xb_le_one⟩
      (dlo := E.dlo) (cT := E.c - E.n * E.xb) (gT := E.gTlo)
      E.hSlo E.gTlo_pos.le
      (by
        have h := E.target_loss_margin_lo 
        calc E.c - E.n * E.xb ≤ E.βT * E.gTlo * E.dlo := h
          _ = E.toParams.β_T * E.gTlo * E.dlo := rfl)
      (fun V_T V_S x hx =>
        E.h_stage_target_loss_any V_T V_S
          (Set.Icc (max x (max E.xb E.xb)) 1) x hx)
      (E.hV_T_gain)
  hV_S_mono_carrier := fun _ hV_S =>
    monotone_of_mem_valLipGainBall E.gS_pos.le hV_S
  hMyoCeiling := fun x hx => by
    rw [max_self] at hx ⊢
    exact E.canonical_myopic_ceiling hx

/-! ## W12. Headline consequences on the general-`F` trajectory

`hF_top` — the strict-above-diagonal condition at full sanctions — is what the
general-`F` headline needs beyond the certificate.  It is DERIVED here from the
sanction lower chord plus `F_diag`, not assumed, so the general-`F` route costs
no extra hypothesis over the affine one. -/

/-- **Strict adjustment at the top**: `x < F(x, 1)` for every `x ∈ [0,1)`.
Instantiate the sanction lower chord at `s₁ = x`, `s₂ = 1`:
`dlo·(1 − x) ≤ F(x,1) − F(x,x) = F(x,1) − x`, and `dlo > 0` (`dlo_pos`), `x < 1`. -/
theorem hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < E.toParams.F x 1 := by
  intro x hx
  have h := E.hSlo (x := x) (s₁ := x) (s₂ := 1)
    ⟨hx.1, le_of_lt hx.2⟩ ⟨hx.1, le_of_lt hx.2⟩
    ⟨zero_le_one, le_refl 1⟩ (le_of_lt hx.2)
  have hd : 0 < E.dlo * (1 - x) := mul_pos E.dlo_pos (by linarith [hx.2])
  have hdiag : E.F x x = x := E.F_diag x
  show x < E.F x 1
  linarith [hdiag]

/-- **General-`F` three-goals dominance.**  A forward-looking feedback
Stackelberg equilibrium exists in the certified carriers, and on the whole
basin its realised sanction dominates the CANONICAL myopic regime's.  General
in `F`.  Since plan item BG3.7 it no longer takes the strict placation margin
`u₀ + r < k`: `certificateMS` does not need it. -/
theorem three_goals_dominance (hxb_pos : 0 < E.xb) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
      ∧ (∀ x ∈ Set.Icc (max E.xb E.xb) 1,
           E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x)
             ≤ E.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x) := by
  obtain ⟨Eq, hVT, hVS, _hG1, hG2, _hG3⟩ :=
    (E.certificateMS hxb_pos).three_goals_local_MS_generalF
      (p := E.toParams) E.hF_top
  exact ⟨Eq, hVT, hVS, hG2⟩

/-- **General-`F` maximal regime separation.**  There is a forward-looking
equilibrium in the carriers whose realised sanction is the top corner at every
feasible state, while the canonical myopic regime realises no sanction at
all.  This one keeps the strict placation margin `u₀ + r < k`: it asserts a
zero myopic sanction at the top state `x = 1` as well, which is exactly where
the margin is needed (`myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one`). -/
theorem regime_separation (hxb_pos : 0 < E.xb) (hk_strict : E.u₀ + E.r < E.k) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x ∈ Sanctions.S,
          E.toParams.σ x
              (E.toParams.myopicFeedbackEquilibrium_canonical.α x) = 0
          ∧ E.toParams.dynamicEquilibriumRule Eq x = 1 := by
  obtain ⟨Eq, hVT, hVS, _hG1, _hG2, _hG3⟩ :=
    (E.certificateMS hxb_pos).three_goals_local_MS_generalF
      (p := E.toParams) E.hF_top
  refine ⟨Eq, hVT, hVS, fun x hx =>
    ⟨E.canonical_myopic_sigma_eq_zero hk_strict hx, ?_⟩⟩
  exact E.σ_dyn_top_eq_one hVS hx (Eq.α_mem x hx)

/-- **Directional sign witness (Rule 16a).** -/
theorem regime_separation_strict (hxb_pos : 0 < E.xb) (hk_strict : E.u₀ + E.r < E.k) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.S,
        E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x)
          < E.toParams.dynamicEquilibriumRule Eq x := by
  obtain ⟨Eq, _hVT, _hVS, h⟩ := E.regime_separation hxb_pos hk_strict
  refine ⟨Eq, fun x hx => ?_⟩
  rw [(h x hx).1, (h x hx).2]
  exact zero_lt_one

/-! ## Within-carrier uniqueness, for the family and at general `F`

Two compositions that were available from the existing certificate and had
simply never been written down. Neither adds a hypothesis: both consume
`certificateMS` and nothing else, so they are theorems over the assumption
surface the family already carries (Rule 3 does not fire — a new theorem
provable from existing primitives is a free addition).

What makes them worth stating is *which* cell of the development they fill. The
affine sibling `SymbolicEconomy` reaches a Schur certificate and within-carrier
uniqueness; the non-affine `qbParams` reaches uniqueness at a single economy
(`qbCert_unique_in_carrier`). Neither combination is uniqueness for a
*coefficient-parametric family at a general transition*, which is what
`unique_in_carrier_family` below delivers. -/

/-- **The general-`F` family downgrades to the Schur package.**

`ofRowSum_MS` forwards the Milgrom--Shannon certificate's fields verbatim -- the
invariant carrier `h_inv`, both operator rows `hT_T_op` / `hT_S_op`, and the row
constants -- so the row-sum criterion implies the Schur determinant condition
`L_TS · L_ST < (1 − β_T)(1 − β_S)` with nothing further to supply. This is the
family-level counterpart of `qbCertCertificateSchurMS`, which inhabited the same
structure at one non-affine economy.  General in `F`; since plan item BG3.7 it
no longer takes the strict placation margin `u₀ + r < k`. -/
noncomputable def certificateSchurMS
    (hxb_pos : 0 < E.xb) :
    E.toParams.StandardComplianceLocalCoreCertificateSchur_MS :=
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS
    E.toParams (E.certificateMS hxb_pos)

/-- **Within-carrier uniqueness for the whole general-transition family.**

Any two top-selector feedback Stackelberg equilibria whose value functions lie
in the family's carriers, and whose Target policies are the carrier's own
selector `α_on` at those values, agree in *both* value functions and in the
policy. Quantified over every admissible `E : SymbolicEconomyF` -- so over every
admissible nine-coefficient payoff configuration, every discount pair, and every
transition inside the chord band, including the provably non-affine ones
(`wobbleEconMS_F_ne_affineF`).

**Scope.** This is uniqueness *within the carrier*, not among all bounded
stationary equilibria. Whether every equilibrium under these primitives must lie
in the carrier is a separate question (automatic regularity) and is not proved
anywhere in this development. Do not cite this as global uniqueness.

**Dropped hypothesis (plan item BG3.7).** The strict placation margin
`u₀ + r < k` is no longer an argument, because `certificateMS` no longer needs
it; uniqueness now covers members on the placation boundary `u₀ + r = k`. -/
theorem unique_in_carrier_family
    (hxb_pos : 0 < E.xb)
    (Eq Eq' : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVT : Eq.V_T ∈ E.carrierT) (hVS : Eq.V_S ∈ E.carrierS)
    (hVT' : Eq'.V_T ∈ E.carrierT) (hVS' : Eq'.V_S ∈ E.carrierS)
    (hαE : Eq.α = E.valueClass.α_on ⟨Eq.V_T, hVT⟩ ⟨Eq.V_S, hVS⟩)
    (hαE' : Eq'.α = E.valueClass.α_on ⟨Eq'.V_T, hVT'⟩ ⟨Eq'.V_S, hVS'⟩) :
    Eq.V_T = Eq'.V_T ∧ Eq.V_S = Eq'.V_S ∧ Eq.α = Eq'.α :=
  (E.certificateMS hxb_pos).unique_in_carrier (p := E.toParams)
    Eq Eq' hVT hVS hVT' hVS' hαE hαE'

/-- **Within-carrier uniqueness for the whole general-transition family, with no
selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`unique_in_carrier_family` without `hαE`, `hαE'`: any two top-selector feedback
Stackelberg equilibria whose value functions lie in the family's carriers share
both value functions, and their Target policies agree at every feasible state.
The selector coincidence is not assumed, because every equilibrium with carrier
values already plays the carrier selector on the state set. Quantified over
every admissible `E : SymbolicEconomyF`, so general in `F` within the family's
chord band, the provably non-affine members included. Uniqueness within the
carrier only, not among all bounded stationary equilibria. -/
theorem unique_in_carrier_family_of_mem
    (hxb_pos : 0 < E.xb)
    (Eq Eq' : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVT : Eq.V_T ∈ E.carrierT) (hVS : Eq.V_S ∈ E.carrierS)
    (hVT' : Eq'.V_T ∈ E.carrierT) (hVS' : Eq'.V_S ∈ E.carrierS) :
    Eq.V_T = Eq'.V_T ∧ Eq.V_S = Eq'.V_S ∧ Set.EqOn Eq.α Eq'.α Sanctions.S :=
  (E.certificateMS hxb_pos).unique_in_carrier_of_mem (p := E.toParams)
    Eq Eq' hVT hVS hVT' hVS'

end SymbolicEconomyF

/-! ## W13. Rule-9 non-vacuity: the general-`F` certificate is inhabited

`wobbleEconF` (CORE §9) **fails** the strict placation margin
`u₀ + r < k` — it sits exactly on `u₀ + r = k = 3`.  When this witness was
built, `certificateMS` required that margin, so the certificate needed its own
witness.  Since plan item BG3.7 (2026-10-06) the constructor takes only
`0 < x̄`, and `wobbleEconF` (with `x̄ = 1/2`) is certified as well
(`wobbleEconF_certificateMS`, in the persistence file).  `wobbleEconMS` is
kept: it is a pinned instance, and the margin still feeds the regime-separation
theorems, which assert a zero myopic sanction at the top state.

Same transition as `wobbleEconF` — `wobbleF (1/2) (1/100)`, realised recursion
`x' = x/2 + 1/2 + (1−x)²/100`, a genuine parabola — same chord data
(`glo = 12/25 < 1/2 = ghi`, `dlo = 12/25`), and a repriced payoff point located
by exact-rational arithmetic before any Lean was written (Rule 9C):

    β_S = β_T = 1/2,  q = 1/2,  u₀ = 7,  k = 9,  r = 1,  w = 20,
    ℓ = 1,  c = 1,  n = 0,  v = 4,  x̄ = 1/2,  δ = 1/2.

Every margin clears with slack, so this is not a knife-edge:

| margin | value | bound |
|---|---|---|
| `hCorner` (field, at `glo`) | `19/10 = 1.9` | `< 126/25 = 5.04` |
| `hCorner_ghi` (derived) | `15/8 = 1.875` | `< 126/25 = 5.04` |
| `hTMargin` (field, at `glo`) | `19/25 = 0.76` | `≤ 24/25 = 0.96` |
| `hTMargin_ghi` (derived) | `3/4 = 0.75` | `≤ 24/25 = 0.96` |
| `hk_strict` | `u₀ + r = 8` | `< k = 9` |

(The `hk_strict` row is consumed only by the regime-separation corollaries
below; `certificateMS` no longer reads it. Until plan item BJ4.1 the point also
fixed a sanction floor `s̄ = 1/2` for the deleted Sender stage margin, which
cleared as `126/25 < 87/16`, and until plan item BJ4.3 the upper sanction chord
`dhi = 13/25`, the curvature ceilings `M_F = M_state = 1/50` and the deleted
curvature margin, which cleared as `5051/15625 < 1/2`.)
-/

/-- **The non-affine witness economy for the general-`F` certificate.** Its
fields `dhi`, `MF`, `Mstate`, `hShi`, `hFsc`, `hGsc`, `hMF0`, `hMstate0` and
`hCurv` were dropped with the structure's curvature block (plan item BJ4.3,
2026-10-08); every other field is unchanged. -/
def wobbleEconMS : SymbolicEconomyF where
  F := wobbleF (1 / 2) (1 / 100)
  F_continuous := wobbleF_continuous _ _
  F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
  F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
  F_diag := wobbleF_diag _ _
  glo := 1 - 1 / 2 - 2 * (1 / 100)
  ghi := 1 - 1 / 2
  dlo := 1 / 2 - 2 * (1 / 100)
  hband := wobbleF_cornerStateChord (by norm_num)
  hSlo := wobbleF_sanctionLowerChord (by norm_num)
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  δ := 1 / 2
  βS := 1 / 2
  βT := 1 / 2
  q := 1 / 2
  u₀ := 7
  k := 9
  r := 1
  w := 20
  ℓ := 1
  c := 1
  n := 0
  v := 4
  xb := 1 / 2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  hq := by norm_num
  hqr := by norm_num
  hu₀ := by norm_num
  hk := by norm_num
  hn := by norm_num
  hℓ := by norm_num
  hcn := by norm_num
  hxb0 := by norm_num
  hxb1 := by norm_num
  hCorner := by norm_num
  hTMargin := by norm_num

/-- The realised recursion is a parabola, not an affine map. -/
theorem wobbleEconMS_not_cornerSectionTop :
    ¬ ∃ γ : ℝ, CornerSectionTop wobbleEconMS.F γ :=
  wobbleF_not_cornerSectionTop (by norm_num)

theorem wobbleEconMS_F_ne_affineF (d : ℝ) :
    wobbleEconMS.F ≠ AbstractGame.affineF d :=
  wobbleF_ne_affineF (by norm_num) d

/-- The band is strictly two-sided, so the carrier is a genuine cone. -/
theorem wobbleEconMS_band_strict : wobbleEconMS.glo < wobbleEconMS.ghi := by
  show (1 : ℝ) - 1 / 2 - 2 * (1 / 100) < 1 - 1 / 2
  norm_num

theorem wobbleEconMS_gS_lt_KS : wobbleEconMS.gS < wobbleEconMS.KS := by
  show symGS (1 / 2) (1 - 1 / 2 - 2 * (1 / 100)) 1 20
      < symKS (1 / 2) (1 - 1 / 2) 1 20
  simp only [symGS, symKS, StokeyLucas.bellmanLowerSlopeConstant,
    StokeyLucas.bellmanLipConstant]
  norm_num

/-- **Both readings of implacability hold at the witness** — the `glo` one is
now the structure field `hCorner`, the `ghi` one its CORE consequence. -/
theorem wobbleEconMS_corner_both :
    (wobbleEconMS.q + wobbleEconMS.k - wobbleEconMS.u₀)
        * (1 - wobbleEconMS.βS * wobbleEconMS.glo)
      < wobbleEconMS.βS * wobbleEconMS.dlo * (wobbleEconMS.r + wobbleEconMS.w)
    ∧ (wobbleEconMS.q + wobbleEconMS.k - wobbleEconMS.u₀)
        * (1 - wobbleEconMS.βS * wobbleEconMS.ghi)
      < wobbleEconMS.βS * wobbleEconMS.dlo * (wobbleEconMS.r + wobbleEconMS.w) :=
  ⟨wobbleEconMS.hCorner, wobbleEconMS.hCorner_ghi⟩

/-- **Both readings of the Target loss offset hold at the witness.** -/
theorem wobbleEconMS_tmargin_both :
    (wobbleEconMS.c - wobbleEconMS.n * wobbleEconMS.xb)
        * (1 - wobbleEconMS.βT * wobbleEconMS.glo)
      ≤ wobbleEconMS.βT * wobbleEconMS.dlo * (wobbleEconMS.n + wobbleEconMS.v)
    ∧ (wobbleEconMS.c - wobbleEconMS.n * wobbleEconMS.xb)
        * (1 - wobbleEconMS.βT * wobbleEconMS.ghi)
      ≤ wobbleEconMS.βT * wobbleEconMS.dlo * (wobbleEconMS.n + wobbleEconMS.v) :=
  ⟨wobbleEconMS.hTMargin, wobbleEconMS.hTMargin_ghi⟩

theorem wobbleEconMS_xb_pos : (0 : ℝ) < wobbleEconMS.xb := by
  show (0 : ℝ) < 1 / 2
  norm_num

theorem wobbleEconMS_k_strict :
    wobbleEconMS.u₀ + wobbleEconMS.r < wobbleEconMS.k := by
  show (7 : ℝ) + 1 < 9
  norm_num

/-- **The general-`F` MS certificate is inhabited.** -/
def wobbleEconMS_certificate :
    wobbleEconMS.toParams.StandardComplianceLocalCoreCertificate_MS :=
  wobbleEconMS.certificateMS wobbleEconMS_xb_pos

/-- **End-to-end at a genuinely non-affine realised recursion**: the
forward-looking regime's realised sanction dominates the canonical myopic
regime's on the whole basin. -/
theorem wobbleEconMS_three_goals_dominance :
    ∃ Eq : wobbleEconMS.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconMS.carrierT ∧ Eq.V_S ∈ wobbleEconMS.carrierS
      ∧ (∀ x ∈ Set.Icc (max wobbleEconMS.xb wobbleEconMS.xb) 1,
           wobbleEconMS.toParams.σ x
               (wobbleEconMS.toParams.myopicFeedbackEquilibrium_canonical.α x)
             ≤ wobbleEconMS.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x) :=
  wobbleEconMS.three_goals_dominance wobbleEconMS_xb_pos

/-- **End-to-end maximal regime separation** at the same non-affine witness. -/
theorem wobbleEconMS_regime_separation_strict :
    ∃ Eq : wobbleEconMS.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.S,
        wobbleEconMS.toParams.σ x
            (wobbleEconMS.toParams.myopicFeedbackEquilibrium_canonical.α x)
          < wobbleEconMS.toParams.dynamicEquilibriumRule Eq x :=
  wobbleEconMS.regime_separation_strict wobbleEconMS_xb_pos wobbleEconMS_k_strict

/-! ## W14. An INTERIOR member — a candidate robustness centre

`wobbleEconMS` certifies, but it is not a point one can perturb freely: it sits
on **two** constraint boundaries at once — `n = 0` and `ℓ = c - n`, each holding
with equality. A robustness theorem needs a centre strictly inside the
admissible set, and `wobbleEconMS` is a corner of it. (Until plan item BJ4.1
there was a third, `xb = sbar`; the sanction floor `sbar` and the constraint
`xb ≤ sbar` were deleted with the Sender stage margin, and `wobbleEconInterior`
had set `sbar = 11/20`.)

`wobbleEconInterior` moves exactly those coordinates off their boundaries
(`n = 1/100`, `c = 11/10`) and lowers the Sender's discount factor to
`βS = 1/4`, chosen to keep the corner margin and the curvature margin (deleted
by plan item BJ4.3) clear. The transition side is untouched, so it is the same
non-affine `wobbleF` law.

**What this licenses, and what it does not (Rule 9A).** Exactly one sentence:
*the admissible set of `SymbolicEconomyF` has a member at which the
constraints `wobbleEconMS` meets with equality hold strictly.* It is a
**candidate centre**, not a robustness result — no open neighbourhood is
constructed, and constructing one needs continuity of every admissibility
constraint in the coefficients, which is proved nowhere in this development. Do
not cite this as robustness, and do not cite it as a strengthening of
`wobbleEconMS`, which it is not: it is a different point of the same family.

Found by exact-rational sweep (Rule 9C) —
`docs/archive/workflow-scratch/four-decisions-interior-member-2026-09-01.py` —
then discharged here. -/

/-- **An interior member of the general-`F` family.** Same `wobbleF` transition
as `wobbleEconMS`; the boundary coordinates moved strictly inside. The
curvature-block fields were dropped with the structure's (plan item BJ4.3). -/
def wobbleEconInterior : SymbolicEconomyF where
  F := wobbleF (1 / 2) (1 / 100)
  F_continuous := wobbleF_continuous _ _
  F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
  F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
  F_diag := wobbleF_diag _ _
  glo := 1 - 1 / 2 - 2 * (1 / 100)
  ghi := 1 - 1 / 2
  dlo := 1 / 2 - 2 * (1 / 100)
  hband := wobbleF_cornerStateChord (by norm_num)
  hSlo := wobbleF_sanctionLowerChord (by norm_num)
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  δ := 1 / 2
  βS := 1 / 4
  βT := 1 / 2
  q := 1 / 2
  u₀ := 7
  k := 9
  r := 1
  w := 20
  ℓ := 1
  c := 11 / 10
  n := 1 / 100
  v := 4
  xb := 1 / 2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  hq := by norm_num
  hqr := by norm_num
  hu₀ := by norm_num
  hk := by norm_num
  hn := by norm_num
  hℓ := by norm_num
  hcn := by norm_num
  hxb0 := by norm_num
  hxb1 := by norm_num
  hCorner := by norm_num
  hTMargin := by norm_num

/-- **The constraints `wobbleEconMS` meets with equality hold strictly
here.** `0 < n` — the Target's state-loss coefficient is live rather than
absent; `ℓ < c - n` — the compliance cost sits strictly below the net stage
constant. These two are the whole content of the witness.

**Edited in place (plan item BJ4.1, 2026-10-07).** The statement had a third
conjunct, `xb < sbar` (the basin threshold strictly below the sanction floor).
The floor `sbar` is no longer a field of `SymbolicEconomyF`, so that conjunct
has nothing to refer to; the name is kept. -/
theorem wobbleEconInterior_strict_at_the_three_boundaries :
    0 < wobbleEconInterior.n
    ∧ wobbleEconInterior.ℓ < wobbleEconInterior.c - wobbleEconInterior.n := by
  refine ⟨?_, ?_⟩
  · show (0 : ℝ) < 1 / 100
    norm_num
  · show (1 : ℝ) < 11 / 10 - 1 / 100
    norm_num

/-- For contrast: `wobbleEconMS` meets both with equality, which is exactly
why it cannot serve as a robustness centre. Edited in place like its sibling
(plan item BJ4.1): the third conjunct `xb = sbar` referred to the deleted
sanction floor; the name is kept. -/
theorem wobbleEconMS_on_the_three_boundaries :
    wobbleEconMS.n = 0
    ∧ wobbleEconMS.ℓ = wobbleEconMS.c - wobbleEconMS.n := by
  refine ⟨rfl, ?_⟩
  show (1 : ℝ) = 1 - 0
  norm_num

/-- The interior member carries the same non-affine transition, so moving off
the boundaries costs none of the generality. -/
theorem wobbleEconInterior_F_ne_affineF (d : ℝ) :
    wobbleEconInterior.F ≠ AbstractGame.affineF d :=
  wobbleF_ne_affineF (by norm_num) d

end -- noncomputable section

end Examples

end Sanctions

#print axioms Sanctions.Examples.SymbolicEconomyF.target_loss_margin_lo
#print axioms Sanctions.Examples.wobbleEconMS_corner_both
#print axioms Sanctions.Examples.wobbleEconMS_tmargin_both
#print axioms Sanctions.Examples.SymbolicEconomyF.certificateMS
#print axioms Sanctions.Examples.SymbolicEconomyF.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one
#print axioms Sanctions.Examples.SymbolicEconomyF.canonical_myopic_ceiling
#print axioms Sanctions.Examples.SymbolicEconomyF.certificateSchurMS
#print axioms Sanctions.Examples.wobbleEconInterior_strict_at_the_three_boundaries
#print axioms Sanctions.Examples.wobbleEconMS_on_the_three_boundaries
#print axioms Sanctions.Examples.wobbleEconInterior_F_ne_affineF
#print axioms Sanctions.Examples.SymbolicEconomyF.unique_in_carrier_family
#print axioms Sanctions.Examples.SymbolicEconomyF.unique_in_carrier_family_of_mem
#print axioms Sanctions.Examples.SymbolicEconomyF.three_goals_dominance
#print axioms Sanctions.Examples.SymbolicEconomyF.regime_separation
#print axioms Sanctions.Examples.SymbolicEconomyF.regime_separation_strict
#print axioms Sanctions.Examples.wobbleEconMS_certificate
#print axioms Sanctions.Examples.wobbleEconMS_three_goals_dominance
#print axioms Sanctions.Examples.wobbleEconMS_regime_separation_strict
#print axioms Sanctions.Examples.wobbleEconMS_not_cornerSectionTop
#print axioms Sanctions.Examples.wobbleEconMS_gS_lt_KS
