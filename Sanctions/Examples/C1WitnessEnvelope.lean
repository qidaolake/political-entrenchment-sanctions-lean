/-
Sanctions/Examples/C1WitnessEnvelope.lean

**P9 partial unfreeze (Wave 6, 2026-07-12): the witness-level C¹
exact-derivative / envelope layer.**

The C¹ track (`DerivativeOnS` / `C1Val` / `ValueClass_C1` /
`C1BellmanSystem` / `StandardComplianceLocalCertificateC1`) was frozen
2026-07-04 (A6) as vacuous — no witness instantiated it. This file
de-vacuizes it at the witness level, with **zero new hypotheses**:
every declaration is proved from the existing assumption surface.

Contents:

1. **Selector-coincidence congruence** (parametric): under per-state
   Sender-argmax uniqueness, the `σ_dyn`-based Target integrand
   `joint_T_integrand` coincides with the `σ_dyn_top`-based
   `joint_T_top_integrand` at physical states, hence
   `jointTarget_BCF_on_S` equals the sSup of the top integrand.
   (Natural home: `Theory/Equilibrium`; colocated here because this
   round's only permitted existing-file edit was the
   `C1BellmanSystem` α-localization.)
2. **First inhabitants of the C¹ carrier**: `C1Val` packages at the
   four W2-pinned exact Bellman fixed values (eeCert
   `V_S* = (16x+17)/3`, `V_T* = (82x+39)/11` with `K_d = 82/11`;
   fourGroup `V_S* = 11/3 + (4/3)x`, `V_T* = 52/11 + (80/11)x` with
   `K_d = 80/11`), each with a constant exact derivative witness.
3. **Singleton-carrier discharges**: `ValueClass_C1`,
   `ValueClass_C1Complete`, and `C1BellmanSystem` at both witnesses
   (`T = id` on the singleton `{(V_T*, V_S*)}`; the Bellman
   constraints ARE the W2 pins modulo the congruence of item 1), and
   the `three_goals_local_C1` endpoint instantiated at both.
4. **Exact equilibrium shadow prices** (the paper-facing payoff):
   `dV_T*/dx = 82/11`, `dV_S*/dx = 16/3` at eeCert; `80/11`, `4/3` at
   fourGroup — as within-`S` derivatives of the equilibrium values,
   each with the machine-checked envelope recursion
   `slope = U_x + β(1−δ)·slope`. This is the
   Rincón-Zapatero–Santos (2009, *Econometrica* 77(1), Theorem 3.1)
   boundary-solution formula for the corner solution `(s,a) = (1,0)`:
   reduced-form binding constraint `g(x,y) = F(x,1) − y` with
   `D₁g = 1−δ`, `D₂g = −1`, scalar constraint matrix `G = 1−δ`;
   `βG < 1` (checked) gives the D4 transversality condition, so the
   bubble term vanishes (`B₀ = 0`) and
   `D₁v = Σ_t β^t G^t U_x = U_x/(1−βG)`. Rule-16 sign corollaries:
   `dV_T/dx > 0` with exact magnitude — the Target incumbent strictly
   gains from hardline consolidation.
5. **The B2 interior Danskin identity** — the first machine-checked
   interior envelope identity in the tree: at the B2 witness
   (shape-pinned carriers, state-varying interior `σ_dyn`), on the
   smooth window `x₀ ∈ (0, 1/2)` (away from the coefficient kinks at
   `x ∈ {1/2, 5/8, 23/32}`), the Sender Bellman image has exact state
   derivative `−4(x₀ − 1/2)`, and the partial-`x` of the Sender
   objective at the *frozen interior argmax* `σ_dyn(x₀,0) = 7/8`
   has the same derivative. Exact carrier derivatives
   `dV_S/dx = −4(x − 1/2)` and `dV_T/dx = 5` on all of `S`.

**STAYS FROZEN** (per the adversarially-confirmed P9 probe): the
abstract envelope layer — `SmoothSanctionClass` IFT Prop fields, the
abstract `ValueClass_C1Complete` derivation, any general-`F` RZS-style
statement. Every abstract form needs new differentiability /
concavity hypotheses (Rule 3), so it is not touched here.

**Rule-18 note**: none of these theorems enters the headline set;
they ship as non-headline witness-layer results.

## Rule compliance

**Rule 1.** Every strategic object is equilibrium-derived: the leader
policy is the derived defiance argmax `α ≡ 0` (pinned by
`eeCert_zero_isMaxOn_joint` / `fgc_zero_isMaxOn_joint` /
`b2_α_on_eq_zero`), the Sender response is `σ_dyn` (Bellman argmax),
and the value functions are the exact Bellman fixed points (W2 pins)
or certificate-produced equilibrium values.

**Rule 3.** Zero new hypotheses: every statement is proved from the
existing witness lemmas and parametric machinery.

**Rule 5.** The congruence lemmas and the gain-ball derivative lemma
are parametric; witness statements are corollaries.
-/

import Sanctions.Examples.FourGroupPlannerWitness
import Sanctions.Examples.B2NonMonotoneCertWitness
import Sanctions.Theory.Certificates.StandardComplianceLocalC1
import Sanctions.Theory.Equilibrium.JointIntegrandCongruence
import Sanctions.Examples.AffineInstance.ComplianceTower

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

/-! ## 1. Selector-coincidence congruence (moved 2026-08-16)

The three parametric congruence lemmas that used to open this file --
`joint_T_integrand_eq_top_of_unique_on`, `jointTarget_BCF_on_S_eq_sSup_top`
and `isMaxOn_joint_T_top_of_isMaxOn_joint` -- now live in
`Theory/Equilibrium/JointIntegrandCongruence.lean`.

They quantify over an arbitrary `p : Params` and fix no coefficient,
transition, discount factor or constant, so under Rule 19 they are Theory
content that happened to be filed beside its first consumer. A 2026-08-16
layer audit classified them as witness material on the strength of the
directory, which is the cost the misfiling was carrying. -/

namespace Examples

open AbstractGame Sanctions.AbstractGame.Params

/-! ## 2. Exact derivatives on slope-pinned gain balls

Every member of a slope-`c` gain ball is affine with slope exactly `c`
on the state space (`gainBall_clip_diff`), so its `bcfExtendToR`
extension has exact within-`S` derivative `c` at every state. -/

/-- **Exact derivative on the slope-pinned gain ball.** Every member of
`valLipGainBall M c c 0` (Lipschitz `c` ∧ min-slope `c`, i.e. affine
slope exactly `c` on `S`) has within-`S` derivative `c` at every
physical state. -/
theorem gainBall_hasDerivWithinAt {M c : ℝ} (hc : 0 ≤ c) {V : Val}
    (hV : V ∈ valLipGainBall M c c 0) :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR V) c Sanctions.S x := by
  intro x hx
  have hpoly : HasDerivWithinAt
      (fun y : ℝ => V (Sanctions.clipS' 0) + c * y) c Sanctions.S x := by
    simpa using
      (((hasDerivAt_id x).const_mul c).const_add
        (V (Sanctions.clipS' 0))).hasDerivWithinAt
        (s := Sanctions.S)
  have hval : ∀ y ∈ Sanctions.S,
      bcfExtendToR V y = V (Sanctions.clipS' 0) + c * y := by
    intro y hy
    have hd := gainBall_clip_diff hc hV
      (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) hy
    have hd' : c * (y - 0) = c * y := by ring
    change V (Sanctions.clipS' y) = V (Sanctions.clipS' 0) + c * y
    linarith [hd, hd']
  exact hpoly.congr hval (hval x hx)

/-! ## 3. The first inhabitants of the C¹ carrier

`C1Val` packages at the four W2-pinned exact Bellman fixed values,
with constant exact-derivative witnesses. `K_d` is the max of the two
component slopes: `82/11` (eeCert), `80/11` (fourGroup). -/

/-- eeCert Target star as a C¹ value: `V_T* = (82x+39)/11`,
`dV_T*/dx ≡ 82/11`, bound `K_d = 82/11`. -/
noncomputable def eeVTstarC1 : C1Val (82/11 : ℝ) where
  V := eeVTstar
  V' := fun _ => 82/11
  hasDeriv :=
    ⟨gainBall_hasDerivWithinAt (by norm_num) (mem_eeCarrierT_num eeVTstar_mem),
     fun _ _ => le_of_eq (abs_of_nonneg (by norm_num))⟩

/-- eeCert Sender star as a C¹ value: `V_S* = (16x+17)/3`,
`dV_S*/dx ≡ 16/3 ≤ 82/11 = K_d`. -/
noncomputable def eeVSstarC1 : C1Val (82/11 : ℝ) where
  V := eeVSstar
  V' := fun _ => 16/3
  hasDeriv :=
    ⟨gainBall_hasDerivWithinAt (by norm_num) (mem_eeCarrierS_num eeVSstar_mem),
     fun _ _ => by
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16/3)]; norm_num⟩

/-- fourGroup Target star as a C¹ value: `V_T* = 52/11 + (80/11)x`,
`dV_T*/dx ≡ 80/11`, bound `K_d = 80/11`. -/
noncomputable def fgcVTstarC1 : C1Val (80/11 : ℝ) where
  V := fgcVTstar
  V' := fun _ => 80/11
  hasDeriv :=
    ⟨gainBall_hasDerivWithinAt (by norm_num) (mem_fgcCarrierT_num fgcVTstar_mem),
     fun _ _ => le_of_eq (abs_of_nonneg (by norm_num))⟩

/-- fourGroup Sender star as a C¹ value: `V_S* = 11/3 + (4/3)x`,
`dV_S*/dx ≡ 4/3 ≤ 80/11 = K_d`. -/
noncomputable def fgcVSstarC1 : C1Val (80/11 : ℝ) where
  V := fgcVSstar
  V' := fun _ => 4/3
  hasDeriv :=
    ⟨gainBall_hasDerivWithinAt (by norm_num) (mem_fgcCarrierS_num fgcVSstar_mem),
     fun _ _ => by
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4/3)]; norm_num⟩

/-! ## 4. Singleton-carrier `ValueClass_C1` + completeness (eeCert) -/

/-- The eeCert C¹ fixed pair `(V_T*, V_S*)`. -/
noncomputable def eeC1Pair : C1Val (82/11 : ℝ) × C1Val (82/11 : ℝ) :=
  (eeVTstarC1, eeVSstarC1)

/-- **Singleton-carrier C¹ value class at eeCert**: carrier
`{(V_T*, V_S*)}`, joint Bellman operator `T = id` (legitimate because
the pair IS the exact joint Bellman fixed point — see
`eeC1System`), contraction modulus `q = 0` (all carrier distances
vanish). The first inhabited `ValueClass_C1`. -/
noncomputable def eeC1Class : AbstractGame.ValueClass_C1 (82/11 : ℝ) where
  carrier := {eeC1Pair}
  isNonempty := ⟨eeC1Pair, rfl⟩
  T := id
  q := 0
  q_nn := le_refl 0
  q_lt_one := zero_lt_one
  T_contracts := fun a b => by
    have ha : a.val = eeC1Pair := a.property
    have hb : b.val = eeC1Pair := b.property
    simp [id_eq, ha, hb, C1Val.c1distPair_self]

/-- **Completeness of the singleton eeCert C¹ carrier**: constant
Cauchy sequences converge to the singleton element (the frozen
completeness deficiency is vacuous for singleton carriers). -/
theorem eeC1Class_complete :
    AbstractGame.ValueClass_C1Complete eeC1Class := by
  intro s _hs
  refine ⟨⟨eeC1Pair, rfl⟩, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  have hn : (s n).val = eeC1Pair := (s n).property
  simpa [hn, C1Val.c1distPair_self] using hε

/-! ## 5. Singleton-carrier `ValueClass_C1` + completeness (fourGroup) -/

/-- The fourGroup C¹ fixed pair `(V_T*, V_S*)`. -/
noncomputable def fgcC1Pair : C1Val (80/11 : ℝ) × C1Val (80/11 : ℝ) :=
  (fgcVTstarC1, fgcVSstarC1)

/-- Singleton-carrier C¹ value class at the microfounded fourGroup
witness (mirror of `eeC1Class`). -/
noncomputable def fgcC1Class : AbstractGame.ValueClass_C1 (80/11 : ℝ) where
  carrier := {fgcC1Pair}
  isNonempty := ⟨fgcC1Pair, rfl⟩
  T := id
  q := 0
  q_nn := le_refl 0
  q_lt_one := zero_lt_one
  T_contracts := fun a b => by
    have ha : a.val = fgcC1Pair := a.property
    have hb : b.val = fgcC1Pair := b.property
    simp [id_eq, ha, hb, C1Val.c1distPair_self]

/-- Completeness of the singleton fourGroup C¹ carrier. -/
theorem fgcC1Class_complete :
    AbstractGame.ValueClass_C1Complete fgcC1Class := by
  intro s _hs
  refine ⟨⟨fgcC1Pair, rfl⟩, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  have hn : (s n).val = fgcC1Pair := (s n).property
  simpa [hn, C1Val.c1distPair_self] using hε

/-! ## 6. The C¹ Bellman systems at the two witnesses

`T = id` is a *legitimate* joint Bellman operator on the singleton
carrier because the pair is the exact joint Bellman fixed point:
`T_value_eq_sender` IS the W2 pin `*_VS_star_fixed`, and
`T_value_eq_target` IS the pin `*_VT_star_fixed` transported along the
selector-coincidence congruence of §1. The leader policy `α_on_C1 ≡ 0`
is the *derived* defiance argmax (`*_zero_isMaxOn_joint`), Rule 1. -/

/-- **The first `C1BellmanSystem` instance** (eeCert witness). -/
noncomputable def eeC1System :
    AbstractGame.C1BellmanSystem eeCertParams (82/11 : ℝ) where
  toValueClass_C1 := eeC1Class
  α_on_C1 := fun _ _ _ => 0
  α_cont := fun _ => continuous_const
  α_mem := fun _ _x _hx => ⟨le_refl 0, zero_le_one⟩
  α_isMaxOn := by
    intro z x hx
    have hz : z.val = eeC1Pair := z.property
    have hz1 : z.val.1.V = eeVTstar := by rw [hz]; rfl
    have hz2 : z.val.2.V = eeVSstar := by rw [hz]; rfl
    change IsMaxOn
      (fun a => eeCertParams.joint_T_top_integrand z.val.1.V z.val.2.V x a)
      Sanctions.I 0
    rw [hz1, hz2]
    exact eeCertParams.isMaxOn_joint_T_top_of_isMaxOn_joint eeVTstar eeVSstar
      (eeCert_DAU_on_carrier eeVSstar_mem) hx
      (eeCert_zero_isMaxOn_joint eeVTstar eeVSstar_mem hx)
  T_value_eq_target := by
    intro z x
    have hz : z.val = eeC1Pair := z.property
    have hz1 : z.val.1.V = eeVTstar := by rw [hz]; rfl
    have hz2 : z.val.2.V = eeVSstar := by rw [hz]; rfl
    change z.val.1.V x
      = sSup ((fun a =>
          eeCertParams.joint_T_top_integrand z.val.1.V z.val.2.V x.val a)
            '' Sanctions.I)
    rw [hz1, hz2,
        ← eeCertParams.jointTarget_BCF_on_S_eq_sSup_top eeVTstar eeVSstar
            (eeCert_DAU_on_carrier eeVSstar_mem) x]
    exact (eeCert_VT_star_fixed x).symm
  T_value_eq_sender := by
    intro z
    have hz : z.val = eeC1Pair := z.property
    have hz2 : z.val.2.V = eeVSstar := by rw [hz]; rfl
    change z.val.2.V
      = eeCertParams.bellmanS_BCF (fun _ => 0) continuous_const z.val.2.V
    rw [hz2]
    exact eeCert_VS_star_fixed.symm

/-- The `C1BellmanSystem` instance at the microfounded fourGroup
witness (mirror of `eeC1System`). -/
noncomputable def fgcC1System :
    AbstractGame.C1BellmanSystem fgcParams (80/11 : ℝ) where
  toValueClass_C1 := fgcC1Class
  α_on_C1 := fun _ _ _ => 0
  α_cont := fun _ => continuous_const
  α_mem := fun _ _x _hx => ⟨le_refl 0, zero_le_one⟩
  α_isMaxOn := by
    intro z x hx
    have hz : z.val = fgcC1Pair := z.property
    have hz1 : z.val.1.V = fgcVTstar := by rw [hz]; rfl
    have hz2 : z.val.2.V = fgcVSstar := by rw [hz]; rfl
    change IsMaxOn
      (fun a => fgcParams.joint_T_top_integrand z.val.1.V z.val.2.V x a)
      Sanctions.I 0
    rw [hz1, hz2]
    exact fgcParams.isMaxOn_joint_T_top_of_isMaxOn_joint fgcVTstar fgcVSstar
      (fgc_DAU_on_carrier fgcVSstar_mem) hx
      (fgc_zero_isMaxOn_joint fgcVTstar_mem fgcVSstar_mem hx)
  T_value_eq_target := by
    intro z x
    have hz : z.val = fgcC1Pair := z.property
    have hz1 : z.val.1.V = fgcVTstar := by rw [hz]; rfl
    have hz2 : z.val.2.V = fgcVSstar := by rw [hz]; rfl
    change z.val.1.V x
      = sSup ((fun a =>
          fgcParams.joint_T_top_integrand z.val.1.V z.val.2.V x.val a)
            '' Sanctions.I)
    rw [hz1, hz2,
        ← fgcParams.jointTarget_BCF_on_S_eq_sSup_top fgcVTstar fgcVSstar
            (fgc_DAU_on_carrier fgcVSstar_mem) x]
    exact (fgc_VT_star_fixed x).symm
  T_value_eq_sender := by
    intro z
    have hz : z.val = fgcC1Pair := z.property
    have hz2 : z.val.2.V = fgcVSstar := by rw [hz]; rfl
    change z.val.2.V
      = fgcParams.bellmanS_BCF (fun _ => 0) continuous_const z.val.2.V
    rw [hz2]
    exact fgc_VS_star_fixed.symm

/-- Equilibrium existence at eeCert through the C¹ route (the iter-21
lift, first time consumed by a witness). -/
theorem eeCert_equilibriumTop_via_C1 :
    Nonempty eeCertParams.FeedbackStackelbergEquilibriumTop :=
  eeC1System.feedbackStackelbergEquilibriumTop_of_complete
    (by norm_num) eeC1Class_complete

/-- Equilibrium existence at fourGroup through the C¹ route. -/
theorem fgc_equilibriumTop_via_C1 :
    Nonempty fgcParams.FeedbackStackelbergEquilibriumTop :=
  fgcC1System.feedbackStackelbergEquilibriumTop_of_complete
    (by norm_num) fgcC1Class_complete

/-! ## 7. `StandardComplianceLocalCertificateC1` at the two witnesses

The carrier-local fields quantify over the SINGLETON C¹ carrier, so
each reduces to the already-proved witness fact at `(V_T*, V_S*)`
with the derived leader policy `α ≡ 0`. Constants are those of the
shipped BCF certificates (`eeCertCertificate` /
`fourGroupCertCertificate`). -/

/-- **The first `StandardComplianceLocalCertificateC1` instance**
(eeCert witness; basin `[1/10, 1]`, floor `s̄ = 1/2`, margins as in
`eeCertCertificate`). -/
noncomputable def eeC1Certificate :
    eeCertParams.StandardComplianceLocalCertificateC1 (82/11 : ℝ) where
  hK_d_nn := by norm_num
  D_C1 := eeC1System
  hComplete := eeC1Class_complete
  xT := 1/10
  xS := 1/10
  sbar := 1/2
  mS := 8/5
  KS := 16/3
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  hKS_nonneg := by norm_num
  hS_margin := by
    simp only [eeCertParams_β_S, eeCertParams_δ]
    norm_num
  hsbar_pos := by norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := by
    intro z
    have hz2 : z.val.2.V = eeVSstar := by
      rw [(z.property : z.val = eeC1Pair)]; rfl
    rw [hz2]
    exact (mem_eeCarrierS_num eeVSstar_mem).2.1
  cT := 299/100
  gT := 82/11
  hT_loss_margin := by
    simp only [eeCertParams_β_T, eeCertParams_δ]
    norm_num
  h_stage_target_loss_carrier := by
    intro z x hx
    have h := eeCert_h_stage_target_loss ⟨eeVTstar, eeVTstar_mem⟩
      ⟨eeVSstar, eeVSstar_mem⟩ x hx
    rw [eeCert_α_on_eq_zero] at h
    exact h
  hV_T_gain_on_carrier := by
    intro z
    have hz1 : z.val.1.V = eeVTstar := by
      rw [(z.property : z.val = eeC1Pair)]; rfl
    rw [hz1]
    exact eeCert_hV_T_gain eeVTstar eeVTstar_mem
  h_stage_sender_carrier := by
    intro z x hx
    have h := eeCert_h_stage_sender ⟨eeVTstar, eeVTstar_mem⟩
      ⟨eeVSstar, eeVSstar_mem⟩ x hx
    rw [eeCert_α_on_eq_zero] at h
    exact h
  hSC_carrier := by
    intro z
    have hz2 : z.val.2.V = eeVSstar := by
      rw [(z.property : z.val = eeC1Pair)]; rfl
    rw [hz2]
    have h := eeCert_hSC ⟨eeVTstar, eeVTstar_mem⟩ ⟨eeVSstar, eeVSstar_mem⟩
    rw [eeCert_α_on_eq_zero] at h
    exact h
  M := eeCertMyopic
  hMyoCeiling := eeCert_hMyoCeiling
  x₀ := 1/10
  hx₀ := ⟨(max_self (1/10 : ℝ)).le, by norm_num⟩
  x₀shock := 0
  hx₀shock_nn := le_refl 0
  hx₀shock_le := zero_le_one

/-- The `StandardComplianceLocalCertificateC1` instance at the
microfounded fourGroup witness (mirror of `eeC1Certificate`, constants
as in `fourGroupCertCertificate`). -/
noncomputable def fgcC1Certificate :
    fgcParams.StandardComplianceLocalCertificateC1 (80/11 : ℝ) where
  hK_d_nn := by norm_num
  D_C1 := fgcC1System
  hComplete := fgcC1Class_complete
  xT := 1/10
  xS := 1/10
  sbar := 1/2
  mS := 3/2
  KS := 4/3
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  hKS_nonneg := by norm_num
  hS_margin := by
    simp only [fgcParams_β_S, fgcParams_δ]
    norm_num
  hsbar_pos := by norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := by
    intro z
    have hz2 : z.val.2.V = fgcVSstar := by
      rw [(z.property : z.val = fgcC1Pair)]; rfl
    rw [hz2]
    exact (mem_fgcCarrierS_num fgcVSstar_mem).2.1
  cT := 14/5
  gT := 80/11
  hT_loss_margin := by
    simp only [fgcParams_β_T, fgcParams_δ]
    norm_num
  h_stage_target_loss_carrier := by
    intro z x hx
    have h := fgc_h_stage_target_loss ⟨fgcVTstar, fgcVTstar_mem⟩
      ⟨fgcVSstar, fgcVSstar_mem⟩ x hx
    rw [fgc_α_on_eq_zero] at h
    exact h
  hV_T_gain_on_carrier := by
    intro z
    have hz1 : z.val.1.V = fgcVTstar := by
      rw [(z.property : z.val = fgcC1Pair)]; rfl
    rw [hz1]
    exact fgc_hV_T_gain fgcVTstar fgcVTstar_mem
  h_stage_sender_carrier := by
    intro z x hx
    have h := fgc_h_stage_sender ⟨fgcVTstar, fgcVTstar_mem⟩
      ⟨fgcVSstar, fgcVSstar_mem⟩ x hx
    rw [fgc_α_on_eq_zero] at h
    exact h
  hSC_carrier := by
    intro z
    have hz2 : z.val.2.V = fgcVSstar := by
      rw [(z.property : z.val = fgcC1Pair)]; rfl
    rw [hz2]
    have h := fgc_hSC ⟨fgcVTstar, fgcVTstar_mem⟩ ⟨fgcVSstar, fgcVSstar_mem⟩
    rw [fgc_α_on_eq_zero] at h
    exact h
  M := fgcMyopic
  hMyoCeiling := fgc_hMyoCeiling
  x₀ := 1/10
  hx₀ := ⟨(max_self (1/10 : ℝ)).le, by norm_num⟩
  x₀shock := 0
  hx₀shock_nn := le_refl 0
  hx₀shock_le := zero_le_one

/-- **`three_goals_local_C1` instantiated at eeCert** — the audit-49
Item-5 C¹ endpoint discharged by a witness for the first time. The
conclusion duplicates the shipped BCF three-goals content; the value
of this theorem is the de-vacuization of the C¹ certificate route
(`hF` holds since `eeCertParams.F = affineF (1/2)` definitionally). -/
theorem eeCert_three_goals_local_C1 :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      ((∀ n, eeCertParams.dynamicTopLockInPath E.V_S E.α (1/10) n
                ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) ∧
       (∀ n, (1/2 : ℝ)
          ≤ eeCertParams.dynamicTopLockInSanctions E.V_S E.α (1/10) n) ∧
       (∀ n, max (1/10 : ℝ) (1/10)
          ≤ eeCertParams.dynamicTopLockInSanctions E.V_S E.α (1/10) n) ∧
       Monotone (eeCertParams.dynamicTopLockInSanctions E.V_S E.α (1/10)) ∧
       (∀ n, IsMaxOn
         (fun a => eeCertParams.joint_T_top_integrand E.V_T E.V_S
                     (eeCertParams.dynamicTopLockInPath E.V_S E.α (1/10) n) a)
         Sanctions.I
         (E.α (eeCertParams.dynamicTopLockInPath E.V_S E.α (1/10) n))))
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
           eeCertParams.σ x (eeCertMyopic.α x)
             ≤ eeCertParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, eeCertParams.dynamicTopLockInPath E.V_S E.α
                  (eeCertParams.shockPath 0 N) n
                  ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) ∧
          (∀ n, (1/2 : ℝ) ≤ eeCertParams.dynamicTopLockInSanctions E.V_S E.α
                          (eeCertParams.shockPath 0 N) n) ∧
          (∀ n, max (1/10 : ℝ) (1/10)
              ≤ eeCertParams.dynamicTopLockInSanctions E.V_S E.α
                  (eeCertParams.shockPath 0 N) n) :=
  eeC1Certificate.three_goals_local_C1 (p := eeCertParams) rfl

/-- **`three_goals_local_C1` instantiated at the microfounded
fourGroup witness** (mirror of `eeCert_three_goals_local_C1`). -/
theorem fgc_three_goals_local_C1 :
    ∃ E : fgcParams.FeedbackStackelbergEquilibriumTop,
      ((∀ n, fgcParams.dynamicTopLockInPath E.V_S E.α (1/10) n
                ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) ∧
       (∀ n, (1/2 : ℝ)
          ≤ fgcParams.dynamicTopLockInSanctions E.V_S E.α (1/10) n) ∧
       (∀ n, max (1/10 : ℝ) (1/10)
          ≤ fgcParams.dynamicTopLockInSanctions E.V_S E.α (1/10) n) ∧
       Monotone (fgcParams.dynamicTopLockInSanctions E.V_S E.α (1/10)) ∧
       (∀ n, IsMaxOn
         (fun a => fgcParams.joint_T_top_integrand E.V_T E.V_S
                     (fgcParams.dynamicTopLockInPath E.V_S E.α (1/10) n) a)
         Sanctions.I
         (E.α (fgcParams.dynamicTopLockInPath E.V_S E.α (1/10) n))))
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
           fgcParams.σ x (fgcMyopic.α x)
             ≤ fgcParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, fgcParams.dynamicTopLockInPath E.V_S E.α
                  (fgcParams.shockPath 0 N) n
                  ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) ∧
          (∀ n, (1/2 : ℝ) ≤ fgcParams.dynamicTopLockInSanctions E.V_S E.α
                          (fgcParams.shockPath 0 N) n) ∧
          (∀ n, max (1/10 : ℝ) (1/10)
              ≤ fgcParams.dynamicTopLockInSanctions E.V_S E.α
                  (fgcParams.shockPath 0 N) n) :=
  fgcC1Certificate.three_goals_local_C1 (p := fgcParams) rfl

/-! ## 8. Exact equilibrium shadow prices (RZS boundary envelope)

The paper-facing payoff: the exact marginal value of the political
state at the shipped equilibria, with the machine-checked envelope
recursion `slope = U_x + β(1−δ)·slope` — the
**Rincón-Zapatero–Santos (2009, Thm 3.1)** boundary-solution formula
at the corner `(s,a) = (1,0)`: binding reduced-form constraint
`g(x,y) = F(x,1) − y`, `G = −D₁g/D₂g = 1−δ`, `βG < 1` (D4) so the
bubble term is `B₀ = 0` and `D₁v = U_x/(1−βG)`. -/

/-- **Exact eeCert Target shadow price**: `dV_T*/dx = 82/11` at every
state (within-`S` derivative of the equilibrium Target value). -/
theorem eeCert_shadow_price_target :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR eeVTstar) (82/11) Sanctions.S x :=
  gainBall_hasDerivWithinAt (by norm_num) (mem_eeCarrierT_num eeVTstar_mem)

/-- **Exact eeCert Sender shadow price**: `dV_S*/dx = 16/3`. -/
theorem eeCert_shadow_price_sender :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR eeVSstar) (16/3) Sanctions.S x :=
  gainBall_hasDerivWithinAt (by norm_num) (mem_eeCarrierS_num eeVSstar_mem)

/-- **Exact fourGroup Target shadow price**: `dV_T*/dx = 80/11`. -/
theorem fgc_shadow_price_target :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR fgcVTstar) (80/11) Sanctions.S x :=
  gainBall_hasDerivWithinAt (by norm_num) (mem_fgcCarrierT_num fgcVTstar_mem)

/-- **Exact fourGroup Sender shadow price**: `dV_S*/dx = 4/3`. -/
theorem fgc_shadow_price_sender :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR fgcVSstar) (4/3) Sanctions.S x :=
  gainBall_hasDerivWithinAt (by norm_num) (mem_fgcCarrierS_num fgcVSstar_mem)

/-- **Shadow prices at the certificate-produced equilibrium** (eeCert):
the equilibrium values produced by `eeCert_three_goals_dominance` live
in the slope-pinned carriers, so they carry the SAME exact
derivatives — the shadow prices are properties of the equilibrium,
not of a hand-picked candidate (Rule 1). -/
theorem eeCert_equilibrium_shadow_prices :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Sanctions.S,
        HasDerivWithinAt (bcfExtendToR E.V_T) (82/11) Sanctions.S x)
      ∧ (∀ x ∈ Sanctions.S,
          HasDerivWithinAt (bcfExtendToR E.V_S) (16/3) Sanctions.S x) := by
  obtain ⟨E, hVT, hVS, _⟩ := eeCert_three_goals_dominance
  exact ⟨E, gainBall_hasDerivWithinAt (by norm_num) (mem_eeCarrierT_num hVT),
    gainBall_hasDerivWithinAt (by norm_num) (mem_eeCarrierS_num hVS)⟩

/-- Shadow prices at the certificate-produced equilibrium (fourGroup). -/
theorem fgc_equilibrium_shadow_prices :
    ∃ E : fgcParams.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Sanctions.S,
        HasDerivWithinAt (bcfExtendToR E.V_T) (80/11) Sanctions.S x)
      ∧ (∀ x ∈ Sanctions.S,
          HasDerivWithinAt (bcfExtendToR E.V_S) (4/3) Sanctions.S x) := by
  obtain ⟨E, hVT, hVS, _⟩ := fourGroupCert_three_goals_dominance
  exact ⟨E, gainBall_hasDerivWithinAt (by norm_num) (mem_fgcCarrierT_num hVT),
    gainBall_hasDerivWithinAt (by norm_num) (mem_fgcCarrierS_num hVS)⟩

/-! ### Envelope recursion identities (scalar form)

`slope = U_x + β·(1−δ)·slope` with the model's own `β`, `δ`, and the
kernel-checked corner stage slope `U_x`. -/

/-- eeCert Target corner stage `x`-slope: `U_T(·, 0, 1)` is affine in
`x` with slope exactly `41/10`. -/
theorem eeCert_stage_slope_target (x y : ℝ) :
    eeCertParams.U_T y 0 1 - eeCertParams.U_T x 0 1 = 41/10 * (y - x) := by
  simp only [eeCertParams_U_T, eecU_T]; ring

/-- eeCert Sender corner stage `x`-slope: `U_S(·, 0, 1)` has slope
exactly `4`. -/
theorem eeCert_stage_slope_sender (x y : ℝ) :
    eeCertParams.U_S y 0 1 - eeCertParams.U_S x 0 1 = 4 * (y - x) := by
  simp only [eeCertParams_U_S, eecU_S]; ring

/-- fourGroup Target corner stage `x`-slope: exactly `4`. -/
theorem fgc_stage_slope_target (x y : ℝ) :
    fgcParams.U_T y 0 1 - fgcParams.U_T x 0 1 = 4 * (y - x) := by
  simp only [fgcParams_U_T]; ring

/-- fourGroup Sender corner stage `x`-slope: exactly `1`. -/
theorem fgc_stage_slope_sender (x y : ℝ) :
    fgcParams.U_S y 0 1 - fgcParams.U_S x 0 1 = 1 * (y - x) := by
  simp only [fgcParams_U_S]; ring

/-- **eeCert Target envelope recursion**:
`82/11 = 41/10 + β_T·(1−δ)·(82/11)` (RZS boundary form, `G = 1−δ`). -/
theorem eeCert_envelope_recursion_target :
    (82/11 : ℝ)
      = 41/10 + eeCertParams.β_T * (1 - eeCertParams.δ) * (82/11) := by
  rw [eeCertParams_β_T, eeCertParams_δ]; norm_num

/-- **eeCert Sender envelope recursion**:
`16/3 = 4 + β_S·(1−δ)·(16/3)`. -/
theorem eeCert_envelope_recursion_sender :
    (16/3 : ℝ)
      = 4 + eeCertParams.β_S * (1 - eeCertParams.δ) * (16/3) := by
  rw [eeCertParams_β_S, eeCertParams_δ]; norm_num

/-- **fourGroup Target envelope recursion**:
`80/11 = 4 + β_T·(1−δ)·(80/11)`. -/
theorem fgc_envelope_recursion_target :
    (80/11 : ℝ)
      = 4 + fgcParams.β_T * (1 - fgcParams.δ) * (80/11) := by
  rw [fgcParams_β_T, fgcParams_δ]; norm_num

/-- **fourGroup Sender envelope recursion**:
`4/3 = 1 + β_S·(1−δ)·(4/3)`. -/
theorem fgc_envelope_recursion_sender :
    (4/3 : ℝ)
      = 1 + fgcParams.β_S * (1 - fgcParams.δ) * (4/3) := by
  rw [fgcParams_β_S, fgcParams_δ]; norm_num

/-- RZS D4 transversality at eeCert: `β_T·G = β_T·(1−δ) = 9/20 < 1`
and `β_S·G = 1/4 < 1`, so the bubble term vanishes (`B₀ = 0`). -/
theorem eeCert_RZS_D4 :
    eeCertParams.β_T * (1 - eeCertParams.δ) < 1
      ∧ eeCertParams.β_S * (1 - eeCertParams.δ) < 1 := by
  rw [eeCertParams_β_T, eeCertParams_β_S, eeCertParams_δ]
  constructor <;> norm_num

/-- RZS D4 transversality at fourGroup (`9/20 < 1`, `1/4 < 1`). -/
theorem fgc_RZS_D4 :
    fgcParams.β_T * (1 - fgcParams.δ) < 1
      ∧ fgcParams.β_S * (1 - fgcParams.δ) < 1 := by
  rw [fgcParams_β_T, fgcParams_β_S, fgcParams_δ]
  constructor <;> norm_num

/-! ### Envelope recursion identities (value-level form)

The recursion checked ON the model objects: the equilibrium-value
increment decomposes exactly into the stage increment plus the
discounted continuation increment along the corner transition
`x' = (x+1)/2`. -/

/-- **eeCert Target value-level envelope recursion**:
`V_T*(y₂) − V_T*(y₁) = (U_T(y₂,0,1) − U_T(y₁,0,1))
  + β_T·(V_T*((y₂+1)/2) − V_T*((y₁+1)/2))`. -/
theorem eeCert_value_envelope_recursion_target {y₁ y₂ : ℝ}
    (h₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (h₂ : y₂ ∈ Set.Icc (0 : ℝ) 1) :
    eeVTstar (Sanctions.clipS' y₂) - eeVTstar (Sanctions.clipS' y₁)
      = (eeCertParams.U_T y₂ 0 1 - eeCertParams.U_T y₁ 0 1)
        + eeCertParams.β_T
          * (eeVTstar (Sanctions.clipS' ((y₂ + 1)/2))
              - eeVTstar (Sanctions.clipS' ((y₁ + 1)/2))) := by
  have hm₁ : (y₁ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
  have hm₂ : (y₂ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
  have hval := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 82/11)
    (mem_eeCarrierT_num eeVTstar_mem) h₁ h₂
  have hcont := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 82/11)
    (mem_eeCarrierT_num eeVTstar_mem) hm₁ hm₂
  have hstage : eeCertParams.U_T y₂ 0 1 - eeCertParams.U_T y₁ 0 1
      = 41/10 * (y₂ - y₁) := eeCert_stage_slope_target y₁ y₂
  rw [hval, hstage, eeCertParams_β_T, hcont]
  ring

/-- **eeCert Sender value-level envelope recursion** (mirror, with
`β_S` and stage slope `4`). -/
theorem eeCert_value_envelope_recursion_sender {y₁ y₂ : ℝ}
    (h₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (h₂ : y₂ ∈ Set.Icc (0 : ℝ) 1) :
    eeVSstar (Sanctions.clipS' y₂) - eeVSstar (Sanctions.clipS' y₁)
      = (eeCertParams.U_S y₂ 0 1 - eeCertParams.U_S y₁ 0 1)
        + eeCertParams.β_S
          * (eeVSstar (Sanctions.clipS' ((y₂ + 1)/2))
              - eeVSstar (Sanctions.clipS' ((y₁ + 1)/2))) := by
  have hm₁ : (y₁ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
  have hm₂ : (y₂ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
  have hval := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 16/3)
    (mem_eeCarrierS_num eeVSstar_mem) h₁ h₂
  have hcont := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 16/3)
    (mem_eeCarrierS_num eeVSstar_mem) hm₁ hm₂
  have hstage : eeCertParams.U_S y₂ 0 1 - eeCertParams.U_S y₁ 0 1
      = 4 * (y₂ - y₁) := eeCert_stage_slope_sender y₁ y₂
  rw [hval, hstage, eeCertParams_β_S, hcont]
  ring

/-- **fourGroup Target value-level envelope recursion**. -/
theorem fgc_value_envelope_recursion_target {y₁ y₂ : ℝ}
    (h₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (h₂ : y₂ ∈ Set.Icc (0 : ℝ) 1) :
    fgcVTstar (Sanctions.clipS' y₂) - fgcVTstar (Sanctions.clipS' y₁)
      = (fgcParams.U_T y₂ 0 1 - fgcParams.U_T y₁ 0 1)
        + fgcParams.β_T
          * (fgcVTstar (Sanctions.clipS' ((y₂ + 1)/2))
              - fgcVTstar (Sanctions.clipS' ((y₁ + 1)/2))) := by
  have hm₁ : (y₁ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
  have hm₂ : (y₂ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
  have hval := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 80/11)
    (mem_fgcCarrierT_num fgcVTstar_mem) h₁ h₂
  have hcont := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 80/11)
    (mem_fgcCarrierT_num fgcVTstar_mem) hm₁ hm₂
  have hstage : fgcParams.U_T y₂ 0 1 - fgcParams.U_T y₁ 0 1
      = 4 * (y₂ - y₁) := fgc_stage_slope_target y₁ y₂
  rw [hval, hstage, fgcParams_β_T, hcont]
  ring

/-- **fourGroup Sender value-level envelope recursion**. -/
theorem fgc_value_envelope_recursion_sender {y₁ y₂ : ℝ}
    (h₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (h₂ : y₂ ∈ Set.Icc (0 : ℝ) 1) :
    fgcVSstar (Sanctions.clipS' y₂) - fgcVSstar (Sanctions.clipS' y₁)
      = (fgcParams.U_S y₂ 0 1 - fgcParams.U_S y₁ 0 1)
        + fgcParams.β_S
          * (fgcVSstar (Sanctions.clipS' ((y₂ + 1)/2))
              - fgcVSstar (Sanctions.clipS' ((y₁ + 1)/2))) := by
  have hm₁ : (y₁ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
  have hm₂ : (y₂ + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
  have hval := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 4/3)
    (mem_fgcCarrierS_num fgcVSstar_mem) h₁ h₂
  have hcont := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 4/3)
    (mem_fgcCarrierS_num fgcVSstar_mem) hm₁ hm₂
  have hstage : fgcParams.U_S y₂ 0 1 - fgcParams.U_S y₁ 0 1
      = 1 * (y₂ - y₁) := fgc_stage_slope_sender y₁ y₂
  rw [hval, hstage, fgcParams_β_S, hcont]
  ring

/-! ### Rule-16(a) sign corollaries

The Target incumbent strictly gains from hardline consolidation,
exhibited at the provably-distinct ordered endpoints `0 < 1` with the
exact magnitude. -/

/-- **eeCert: hardline consolidation strictly benefits the Target
incumbent** — exact gain `82/11` over the full state range, and strict
order at the endpoints. -/
theorem eeCert_target_hardline_gain :
    eeVTstar (Sanctions.clipS' 1) - eeVTstar (Sanctions.clipS' 0) = 82/11
      ∧ eeVTstar (Sanctions.clipS' 0) < eeVTstar (Sanctions.clipS' 1) := by
  have h := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 82/11)
    (mem_eeCarrierT_num eeVTstar_mem)
    (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (⟨zero_le_one, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
  constructor
  · rw [h]; norm_num
  · nlinarith [h]

/-- **fourGroup: hardline consolidation strictly benefits the Target
incumbent** — exact gain `80/11`, strict order at the endpoints. -/
theorem fgc_target_hardline_gain :
    fgcVTstar (Sanctions.clipS' 1) - fgcVTstar (Sanctions.clipS' 0) = 80/11
      ∧ fgcVTstar (Sanctions.clipS' 0) < fgcVTstar (Sanctions.clipS' 1) := by
  have h := gainBall_clip_diff (by norm_num : (0:ℝ) ≤ 80/11)
    (mem_fgcCarrierT_num fgcVTstar_mem)
    (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (⟨zero_le_one, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
  constructor
  · rw [h]; norm_num
  · nlinarith [h]

/-! ## 9. The B2 interior layer: exact derivatives and the first
machine-checked interior envelope (Danskin) identity

At the B2 witness the carriers are shape-pinned: Sender members are
vertical shifts of `base(y) = 8 − 2(y − 1/2)²`, Target members are
`5y + t`. So the equilibrium values have exact closed-form derivatives
`dV_S/dx = −4(x − 1/2)` and `dV_T/dx = 5` on ALL of `S` — no envelope
theorem needed. On the smooth window `x₀ ∈ (0, 1/2)` (away from the
coefficient kinks at `x ∈ {1/2, 5/8, 23/32}`) the interior Danskin
identity holds by direct algebra: the Bellman image's state
derivative equals the partial-`x` of the objective at the frozen
interior argmax `σ_dyn(x₀, 0) = 7/8 ∈ (0,1)`. -/

/-- Helper: the B2 slice vertex is pinned flat, `p̃(y) = 7/8`, on
`[0, 5/8]`. -/
theorem b2pt_eq_of_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 5 / 8) :
    b2pt y = 7/8 := by
  unfold b2pt
  rw [b2clip_of_mem ⟨hy0, by linarith⟩,
      max_eq_right (by linarith : y - 5/8 ≤ 0)]
  ring

/-- **The B2 forward-looking Sender response is pinned interior at
`7/8`** on the flat window `[0, 5/8]` (at the derived defiance action
`a = 0`). -/
theorem b2_σ_dyn_zero_eq_of_le {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 5 / 8) :
    b2Params.σ_dyn W x 0 = 7/8 := by
  have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0, by linarith⟩
  rw [b2_σ_dyn_eq hW hxI (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Sanctions.I),
      b2sdyn_zero]
  unfold b2p
  rw [b2pt_eq_of_le hx0 hx, min_eq_right (by norm_num : (7:ℝ)/8 ≤ 1)]

/-- Helper: exact derivative of the B2 carrier shape
`y ↦ 8 − 2(y − 1/2)² + t`. -/
theorem hasDerivAt_b2shape (t x : ℝ) :
    HasDerivAt (fun y : ℝ => 8 - 2*(y - 1/2)^2 + t) (-4 * (x - 1/2)) x := by
  have hlin : HasDerivAt (fun y : ℝ => y - 1/2) 1 x :=
    (hasDerivAt_id x).sub_const _
  have hsq : HasDerivAt (fun y : ℝ => (y - 1/2) * (y - 1/2))
      (1 * (x - 1/2) + (x - 1/2) * 1) x := hlin.mul hlin
  have h := ((hsq.const_mul (2 : ℝ)).const_sub 8).add_const t
  have hfun : (fun y : ℝ => 8 - 2*(y - 1/2)^2 + t)
      = (fun y : ℝ => 8 - 2 * ((y - 1/2) * (y - 1/2)) + t) := by
    funext y; ring
  rw [hfun, show -4 * (x - 1/2)
      = -(2 * (1 * (x - 1/2) + (x - 1/2) * 1)) by ring]
  exact h

/-- **Exact B2 Sender shadow price**: every Sender-carrier member —
in particular the equilibrium Sender value — has within-`S` derivative
exactly `−4(x − 1/2)` (positive below `1/2`, negative above: the
non-monotone interior-peaked shape). -/
theorem b2CarrierS_shadow_price {W : Val} (hW : W ∈ b2CarrierS) :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR W) (-4 * (x - 1/2)) Sanctions.S x := by
  intro x hx
  have hval : ∀ y ∈ Sanctions.S,
      bcfExtendToR W y
        = 8 - 2*(y - 1/2)^2 + (W (Sanctions.clipS' 0) - b2base 0) := by
    intro y hy
    change W (Sanctions.clipS' y) = _
    rw [b2CarrierS_apply hW hy]
    unfold b2base; ring
  exact (hasDerivAt_b2shape (W (Sanctions.clipS' 0) - b2base 0)
    x).hasDerivWithinAt.congr hval (hval x hx)

/-- **Exact B2 Target shadow price**: every Target-carrier member —
in particular the equilibrium Target value — has within-`S` derivative
exactly `5`. -/
theorem b2CarrierT_shadow_price {V : Val} (hV : V ∈ b2CarrierT) :
    ∀ x ∈ Sanctions.S,
      HasDerivWithinAt (bcfExtendToR V) 5 Sanctions.S x := by
  intro x hx
  have hpoly : HasDerivAt
      (fun y : ℝ => 5*y + V (Sanctions.clipS' 0)) 5 x := by
    simpa using ((hasDerivAt_id x).const_mul (5:ℝ)).add_const
      (V (Sanctions.clipS' 0))
  have hval : ∀ y ∈ Sanctions.S,
      bcfExtendToR V y = 5*y + V (Sanctions.clipS' 0) := by
    intro y hy
    change V (Sanctions.clipS' y) = _
    exact b2CarrierT_apply hV hy
  exact hpoly.hasDerivWithinAt.congr hval (hval x hx)

/-- Helper: at the frozen peak `s = 7/8` on the flat window, the pure
dynamic objective collapses to the carrier shape:
`dg(y, 0, 7/8) = base(y)`. -/
theorem b2dg_frozen_peak {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 5 / 8) :
    b2dg y 0 (7/8) = b2base y := by
  have hpt := b2pt_eq_of_le hy0 hy
  unfold b2dg b2f b2hump b2comp
  rw [hpt,
      show max ((7:ℝ)/8 - 7/8) 0 = 0 from max_eq_right (by norm_num),
      show max ((7:ℝ)/8 - 1) 0 = 0 from max_eq_right (by norm_num)]
  ring

/-- **Exact state derivative of the B2 Sender Bellman image**: on the
interior of `S`, the value update `x ↦ (T_S W)(x)` (at the derived
defiance policy) has derivative `−4(x₀ − 1/2)` — the Bellman sup is
attained at the state-varying interior peak, yet its exact derivative
is computable. -/
theorem b2_bellman_image_hasDerivAt {W : Val} (hW : W ∈ b2CarrierS)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (bcfExtendToR (b2Params.bellmanS_BCF (fun _ => 0) continuous_const W))
      (-4 * (x₀ - 1/2)) x₀ := by
  have hEq : bcfExtendToR (b2Params.bellmanS_BCF (fun _ => 0)
        continuous_const W)
      =ᶠ[nhds x₀]
      (fun y => 8 - 2*(y - 1/2)^2
        + (W (Sanctions.clipS' 0) - b2base 0)/2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀] with y hy
    have hyI : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    change b2Params.bellmanS_BCF (fun _ => 0) continuous_const W
      (Sanctions.clipS' y) = _
    rw [b2_bellmanS_image hW (Sanctions.clipS' y), clipS'_val_of_mem hyI]
    unfold b2base; ring
  exact hEq.hasDerivAt_iff.mpr
    (hasDerivAt_b2shape ((W (Sanctions.clipS' 0) - b2base 0)/2) x₀)

/-- **Partial-`x` of the B2 Sender objective at the FROZEN interior
argmax**: on the smooth window `x₀ ∈ (0, 1/2)`, the map
`x ↦ U_S(x, 0, s*) + β_S·W(F(x, s*))` with `s* = σ_dyn(x₀, 0)` frozen
has derivative `−4(x₀ − 1/2)` at `x₀`. -/
theorem b2_frozen_objective_hasDerivAt {W : Val} (hW : W ∈ b2CarrierS)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt
      (fun x => b2Params.U_S x 0 (b2Params.σ_dyn W x₀ 0)
        + b2Params.β_S
          * W (Sanctions.clipS' (b2Params.F x (b2Params.σ_dyn W x₀ 0))))
      (-4 * (x₀ - 1/2)) x₀ := by
  have hσ : b2Params.σ_dyn W x₀ 0 = 7/8 :=
    b2_σ_dyn_zero_eq_of_le hW hx₀.1.le (by linarith [hx₀.2])
  have hEq : (fun x => b2Params.U_S x 0 (b2Params.σ_dyn W x₀ 0)
        + b2Params.β_S
          * W (Sanctions.clipS' (b2Params.F x (b2Params.σ_dyn W x₀ 0))))
      =ᶠ[nhds x₀]
      (fun y => 8 - 2*(y - 1/2)^2
        + (W (Sanctions.clipS' 0) - b2base 0)/2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx₀] with y hy
    have hyI : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1.le, by linarith [hy.2]⟩
    rw [hσ,
        b2dynObj_eq hW hyI 0
          (⟨by norm_num, by norm_num⟩ : (7/8:ℝ) ∈ Set.Icc (0:ℝ) 1),
        b2dg_frozen_peak hy.1.le (by linarith [hy.2])]
    unfold b2base; ring
  exact hEq.hasDerivAt_iff.mpr
    (hasDerivAt_b2shape ((W (Sanctions.clipS' 0) - b2base 0)/2) x₀)

/-- **The first machine-checked INTERIOR envelope (Danskin) identity
in the tree.** At the B2 witness, on the smooth window
`x₀ ∈ (0, 1/2)`: (i) the equilibrium Sender response at the derived
defiance action is strictly interior (`σ_dyn(x₀,0) = 7/8 ∈ (0,1)`);
(ii) the Sender Bellman image has exact state derivative
`−4(x₀ − 1/2)`; (iii) the partial-`x` of the Sender objective at the
frozen interior argmax has the SAME derivative — i.e.
`d/dx [max_s obj(x,s)] = ∂_x obj(x, s*)|_{s* interior}`, the Danskin /
envelope identity, by direct algebra with zero new hypotheses. -/
theorem b2_interior_envelope_identity {W : Val} (hW : W ∈ b2CarrierS)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    b2Params.σ_dyn W x₀ 0 ∈ Set.Ioo (0:ℝ) 1
    ∧ HasDerivAt
        (bcfExtendToR (b2Params.bellmanS_BCF (fun _ => 0)
          continuous_const W))
        (-4 * (x₀ - 1/2)) x₀
    ∧ HasDerivAt
        (fun x => b2Params.U_S x 0 (b2Params.σ_dyn W x₀ 0)
          + b2Params.β_S
            * W (Sanctions.clipS' (b2Params.F x (b2Params.σ_dyn W x₀ 0))))
        (-4 * (x₀ - 1/2)) x₀ := by
  refine ⟨?_, b2_bellman_image_hasDerivAt hW
      ⟨hx₀.1, by linarith [hx₀.2]⟩,
    b2_frozen_objective_hasDerivAt hW hx₀⟩
  rw [b2_σ_dyn_zero_eq_of_le hW hx₀.1.le (by linarith [hx₀.2])]
  exact ⟨by norm_num, by norm_num⟩

/-- **Exact shadow prices at the B2 certificate-produced equilibrium**:
`dV_T/dx = 5` and `dV_S/dx = −4(x − 1/2)` at the equilibrium produced
by `b2NonMono_three_goals_dominance` (Rule 1: the values are the
certificate-route equilibrium values, which live in the shape-pinned
carriers). -/
theorem b2_equilibrium_shadow_prices :
    ∃ E : b2Params.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Sanctions.S,
        HasDerivWithinAt (bcfExtendToR E.V_T) 5 Sanctions.S x)
      ∧ (∀ x ∈ Sanctions.S,
          HasDerivWithinAt (bcfExtendToR E.V_S) (-4 * (x - 1/2))
            Sanctions.S x) := by
  obtain ⟨E, hVT, hVS, _⟩ := b2NonMono_three_goals_dominance
  exact ⟨E, b2CarrierT_shadow_price hVT, b2CarrierS_shadow_price hVS⟩

/-! ## Axiom hygiene (Rule 10) -/

#print axioms eeCert_shadow_price_target
#print axioms eeCert_shadow_price_sender
#print axioms fgc_shadow_price_target
#print axioms fgc_shadow_price_sender
#print axioms eeCert_equilibrium_shadow_prices
#print axioms fgc_equilibrium_shadow_prices
#print axioms eeCert_envelope_recursion_target
#print axioms eeCert_envelope_recursion_sender
#print axioms fgc_envelope_recursion_target
#print axioms fgc_envelope_recursion_sender
#print axioms eeCert_value_envelope_recursion_target
#print axioms eeCert_value_envelope_recursion_sender
#print axioms fgc_value_envelope_recursion_target
#print axioms fgc_value_envelope_recursion_sender
#print axioms eeCert_target_hardline_gain
#print axioms fgc_target_hardline_gain
#print axioms eeCert_three_goals_local_C1
#print axioms fgc_three_goals_local_C1
#print axioms eeCert_equilibriumTop_via_C1
#print axioms fgc_equilibriumTop_via_C1
#print axioms b2_interior_envelope_identity
#print axioms b2_bellman_image_hasDerivAt
#print axioms b2_frozen_objective_hasDerivAt
#print axioms b2_equilibrium_shadow_prices

end Examples

end -- noncomputable section

end Sanctions
