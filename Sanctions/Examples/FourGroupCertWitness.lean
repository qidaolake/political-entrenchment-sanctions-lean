/-
Sanctions/Examples/FourGroupCertWitness.lean

**The first certificate-complete witness with MICROFOUNDED stage payoffs.**

Unlike every previous complete certificate witness (`EECertWitness`,
`QuadBumpCertWitnessMS`, `LowBasinCertWitness`, `B2NonMonotoneCertWitness`),
whose stage payoffs were hand-asserted polynomial forms, this witness derives
`U_S` and `U_T` from a Kaempfer-Lowenberg **four-group interest-group polity**
(Grossman-Helpman weighted-sum aggregation, `Theory/Microfoundations/FourGroupPolity`)
over the strict rally-dominant region (R). The tuned group primitives
(probe-validated, exact rationals):

  Sender groups:  θ_{J_S}(x) = 3 + x  (hawks, benefit g_J·s = s),
                  θ_{K_S} = 1 with q_K = 1 (trade-dependent anti-sanction),
                  deadweight kS·s² = s²/2, placation w_pl·s·a = (11/5)·s·a.
  Target groups:  θ_{J_T}(s) = 7/4 + s (regime, welfare 2x − (4/25)a),
                  θ_{K_T}(s) = 1/2 + s (opposition, welfare −x + (4/25)a),
                  sanction cost d_s·s = (14/5)·s, kT = 0.

Induced stage payoffs (derived, then simp-normalized):

  U_S(x,a,s) = (2 + x)·s − ½s² − (11/5)·s·a
  U_T(x,a,s) = 3x − (1/5)a + s·(x − 14/5)     (the (4/25)·a·s terms cancel)
  σ(x,a)     = clip(2 + x − (11/5)a)           (clipped vertex, derived argmax)
  F(x,s)     = (x+s)/2  (affineF, δ = 1/2),  β_S = 1/2,  β_T = 9/10.

Certificate geometry: basin `xT = xS = 1/10`, floor `s̄ = 1/2`; carriers are
slope-pinned affine gain balls of slope `4/3` (Sender, radius `5 = (5/2)/(1 − 1/2)`)
and `80/11` (Target, radius `28 = (14/5)/(1 − 9/10)`; `fgcCarrierS_eq`,
`fgcCarrierT_eq` below are authoritative); Schur rows `β_T = 9/10, β_S = 1/2, L_TS = L_ST = 0`;
`KS = 4/3, mS = 3/2, gT = 80/11, cT = 14/5`. Exact affine fixed points (for
orientation only): `V_S* = 11/3 + (4/3)x`, `V_T* = 52/11 + (80/11)x`.

Structural deviation from the eeCert route: `U_S` has no direct-`x` term, so
`σ_dyn ≡ 1` CANNOT be pinned at all compliance levels (that would force
`β_S > 1`). Instead the corner pin `σ_dyn = 1` is proved **only at `a = 0`**,
and the leader side is discharged by the **chord decomposition** of the joint
integrand: for `σ_a := σ_dyn(V_S) x a ∈ [0,1]`,

  J(x,a) − J(x,0) = −(1/5)·a + (σ_a − 1)·(x − 14/5 + 36/11)
                  = −(1/5)·a − (1 − σ_a)·(x + 26/55) ≤ −(1/5)·a,

using only `σ_dyn` membership and the carrier slope `80/11` — so full
defiance `α_on ≡ 0` is the strict, unique leader argmax at every state.

Economics: the forward-looking Sender is implacable at the defiance corner
(sanctions maxed at `a = 0` because the political-state continuation
dominates), so the forward-looking hardline Target defies. The *myopic*
Sender is placable through the derived placation channel `−(11/5)·a·s`, so
the myopic Target complies at the derived threshold
`M.α(x) = min(1, (5x+10)/11)` — fully for `x ≥ 1/5`, `21/22` at the basin pivot
`x = 1/10` — and buys sanctions down to `σ_myo(x) = clip(x − 1/5)`, zero at and
below `x = 1/5` and interior above it (wording corrected 2026-09-15, the
reader's Q2-5). The dominance gap `σ_dyn − σ_myo ≥ 1/5` is strict on the whole
basin — now with
every coefficient of both stage payoffs *derived* from the four-group
polity's effectiveness weights rather than hand-chosen.
-/

import Sanctions.Examples.EECertWitness
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Microfoundations.FourGroupPolity
import Sanctions.Theory.Bellman.ChordInvariance
-- `affine_sender_chord_on`, which discharges this economy's `hF_chord` field.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.Microfoundations
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params
open KaempferLowenberg

noncomputable section

/-! ## 1. The four-group polity and the induced `Params` -/

/-- **The tuned four-group polity** (strict rally-dominant region (R)):
`ν·g_J = 1 > 0` (sender rally), `w_pl = 11/5 ≥ 0` (placation),
`μ·b_K = 1 < 2 = ρ·b_J` (target rally dominance), `kS = 1/2 > 0`. -/
def fourGroupCert : FourGroup where
  th0_JS := 3
  nu := 1
  g_J := 1
  th0_KS := 1
  q_K := 1
  kS := 1/2
  w_pl := 11/5
  base_S := 0
  th0_JT := 7/4
  rho := 1
  b_J := 2
  c_J := 4/25
  th0_KT := 1/2
  mu := 1
  b_K := 1
  c_K := 4/25
  kT := 0
  d_s := 14/5
  w_pl_nn := by norm_num
  kS_pos := by norm_num
  senderRally_pos := by norm_num
  rally_dom := by norm_num

/-- **The microfounded certificate `Params`** (δ = 1/2, β_T = 9/10,
β_S = 1/2): stage payoffs and static Sender selector all *derived* from
`fourGroupCert` via the Grossman-Helpman aggregation `FourGroup.toParams`. -/
def fgcParams : Sanctions.AbstractGame.Params :=
  fourGroupCert.toParams (1/2) (9/10) (1/2)
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (by constructor <;> norm_num)

@[simp] theorem fgcParams_δ : fgcParams.δ = 1/2 := rfl
@[simp] theorem fgcParams_β_S : fgcParams.β_S = 1/2 := rfl
@[simp] theorem fgcParams_β_T : fgcParams.β_T = 9/10 := rfl

/-- Induced Sender stage payoff in closed form:
`U_S(x,a,s) = (2+x)·s − ½s² − (11/5)·s·a` (derived, not asserted). -/
@[simp] theorem fgcParams_U_S (x a s : ℝ) :
    fgcParams.U_S x a s = (2 + x) * s - 1/2 * s ^ 2 - 11/5 * s * a := by
  show fourGroupCert.U_S x a s = _
  simp only [FourGroup.U_S, fourGroupCert]
  ring

/-- Induced Target stage payoff in closed form:
`U_T(x,a,s) = 3x − (1/5)a + s·(x − 14/5)` — the `(4/25)·a·s` cross terms of
the two target groups cancel exactly at the tuned weights. -/
@[simp] theorem fgcParams_U_T (x a s : ℝ) :
    fgcParams.U_T x a s = 3 * x - 1/5 * a + s * (x - 14/5) := by
  show fourGroupCert.U_T x a s = _
  simp only [FourGroup.U_T, fourGroupCert]
  ring

/-- Induced static Sender response: the clipped vertex
`σ(x,a) = clip(2 + x − (11/5)a)` (identical closed form to the eeCert
witness — but here derived from the group primitives). -/
theorem fgcParams_σ (x a : ℝ) :
    fgcParams.σ x a = max 0 (min 1 (2 + x - 11/5 * a)) := by
  show fourGroupCert.sigmaSel x a = _
  simp only [FourGroup.sigmaSel, fourGroupCert]
  norm_num
  congr 2
  ring

/-- Transition closed form: `F(x,s) = (x+s)/2`. -/
theorem fgcParams_F (x s : ℝ) : fgcParams.F x s = (x + s) / 2 := by
  show AbstractGame.affineF (1/2) x s = (x + s) / 2
  unfold AbstractGame.affineF
  ring

/-! ## 2. Carriers: slope-pinned affine gain balls at the SLP closed forms

As at the `eeCert` witness, neither carrier magnitude is chosen: the
slope is `bellmanLipConstant β δ g_U = g_U/(1 − β·δ)` (Hinderer 4.2(c))
and the radius is `bellmanNormBound β M_U = M_U/(1 − β)`, both evaluated
at the stage payoff the player collects along the **derived** corner path
(`σ_dyn(·,0) ≡ 1` full sanctions against `α_on ≡ 0` full defiance). Here
the stage payoffs are themselves microfounded — aggregated from
`fourGroupCert` by `FourGroup.toParams` — so the carrier magnitudes trace
all the way back to the four groups' primitives. -/

/-- Sender stage payoff along the certified corner path,
`x ↦ U_S(x, 0, 1)`. -/
def fgcStageS (x : ℝ) : ℝ := fgcParams.U_S x 0 1

/-- Target stage payoff along the certified corner path,
`x ↦ U_T(x, 0, 1)`. -/
def fgcStageT (x : ℝ) : ℝ := fgcParams.U_T x 0 1

@[simp] theorem fgcStageS_eq (x : ℝ) : fgcStageS x = 3/2 + x := by
  simp only [fgcStageS, fgcParams_U_S]; ring

@[simp] theorem fgcStageT_eq (x : ℝ) : fgcStageT x = 4 * x - 14/5 := by
  simp only [fgcStageT, fgcParams_U_T]; ring

/-- State-slope of the Sender's corner stage payoff (the `g_U` of the
closed forms). -/
def fgcStageSlopeS : ℝ := fgcStageS 1 - fgcStageS 0

/-- State-slope of the Target's corner stage payoff. -/
def fgcStageSlopeT : ℝ := fgcStageT 1 - fgcStageT 0

/-- Sup-norm of the Sender's corner stage payoff on the state space (the
`M_U` of the radius closed form); affine, so attained at an endpoint. -/
def fgcStageNormS : ℝ := max |fgcStageS 0| |fgcStageS 1|

/-- Sup-norm of the Target's corner stage payoff on the state space. -/
def fgcStageNormT : ℝ := max |fgcStageT 0| |fgcStageT 1|

@[simp] theorem fgcStageSlopeS_eq : fgcStageSlopeS = 1 := by
  simp only [fgcStageSlopeS, fgcStageS_eq]; norm_num

@[simp] theorem fgcStageSlopeT_eq : fgcStageSlopeT = 4 := by
  simp only [fgcStageSlopeT, fgcStageT_eq]; norm_num

@[simp] theorem fgcStageNormS_eq : fgcStageNormS = 5/2 := by
  simp only [fgcStageNormS, fgcStageS_eq]
  rw [show |(3:ℝ)/2 + 0| = 3/2 by rw [abs_of_nonneg] <;> norm_num,
    show |(3:ℝ)/2 + 1| = 5/2 by rw [abs_of_nonneg] <;> norm_num]
  norm_num

@[simp] theorem fgcStageNormT_eq : fgcStageNormT = 14/5 := by
  simp only [fgcStageNormT, fgcStageT_eq]
  rw [show |(4:ℝ) * 0 - 14/5| = 14/5 by rw [abs_of_nonpos] <;> norm_num,
    show |(4:ℝ) * 1 - 14/5| = 6/5 by rw [abs_of_nonneg] <;> norm_num]
  norm_num

/-- Sender carrier: the slope-pinned gain ball at the SLP closed forms.
Evaluates to `valLipGainBall 5 (4/3) (4/3) 0` (`fgcCarrierS_eq`). -/
def fgcCarrierS : Set Val :=
  valLipGainBall
    (StokeyLucas.bellmanNormBound fgcParams.β_S fgcStageNormS)
    (StokeyLucas.bellmanLipConstant fgcParams.β_S (1 - fgcParams.δ) fgcStageSlopeS)
    (StokeyLucas.bellmanLipConstant fgcParams.β_S (1 - fgcParams.δ) fgcStageSlopeS)
    0

/-- Target carrier: the same construction on the Target side. Evaluates
to `valLipGainBall 28 (80/11) (80/11) 0` (`fgcCarrierT_eq`). -/
def fgcCarrierT : Set Val :=
  valLipGainBall
    (StokeyLucas.bellmanNormBound fgcParams.β_T fgcStageNormT)
    (StokeyLucas.bellmanLipConstant fgcParams.β_T (1 - fgcParams.δ) fgcStageSlopeT)
    (StokeyLucas.bellmanLipConstant fgcParams.β_T (1 - fgcParams.δ) fgcStageSlopeT)
    0

/-- Numeric evaluation of the Sender carrier: slope `1/(1 − 1/4) = 4/3`,
radius `(5/2)/(1 − 1/2) = 5`. -/
theorem fgcCarrierS_eq : fgcCarrierS = valLipGainBall 5 (4/3) (4/3) 0 := by
  simp only [fgcCarrierS, StokeyLucas.bellmanNormBound_def,
    StokeyLucas.bellmanLipConstant_def, fgcParams_β_S, fgcParams_δ,
    fgcStageNormS_eq, fgcStageSlopeS_eq]
  norm_num

/-- Numeric evaluation of the Target carrier: slope `4/(1 − 9/20) = 80/11`,
radius `(14/5)/(1 − 9/10) = 28`. -/
theorem fgcCarrierT_eq : fgcCarrierT = valLipGainBall 28 (80/11) (80/11) 0 := by
  simp only [fgcCarrierT, StokeyLucas.bellmanNormBound_def,
    StokeyLucas.bellmanLipConstant_def, fgcParams_β_T, fgcParams_δ,
    fgcStageNormT_eq, fgcStageSlopeT_eq]
  norm_num

/-- Carrier membership in numeric form (Sender side). -/
theorem mem_fgcCarrierS_num {V : Val} (h : V ∈ fgcCarrierS) :
    V ∈ valLipGainBall 5 (4/3) (4/3) 0 := fgcCarrierS_eq ▸ h

/-- Carrier membership in numeric form (Target side). -/
theorem mem_fgcCarrierT_num {V : Val} (h : V ∈ fgcCarrierT) :
    V ∈ valLipGainBall 28 (80/11) (80/11) 0 := fgcCarrierT_eq ▸ h

theorem fgcCarrierS_nonempty : fgcCarrierS.Nonempty := by
  rw [fgcCarrierS_eq]
  exact ⟨affineBCF (4/3), affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

theorem fgcCarrierT_nonempty : fgcCarrierT.Nonempty := by
  rw [fgcCarrierT_eq]
  exact ⟨affineBCF (80/11), affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

/-! ## 3. The corner pin at the defiance policy: `σ_dyn(·, 0) ≡ 1`

On the slope-`4/3` Sender carrier the Sender dynamic objective at `a = 0`
has `s`-chord slope `≥ 4/3 > 0` at every physical state
(`2 + x − (s₁+s₂)/2 + 1/3 ≥ 4/3`): the forward-looking Sender is implacable
against a defiant Target. (Unlike eeCert, the pin does NOT hold at all
compliance levels — the microfounded `U_S` has no direct-`x` term — and the
leader side is instead discharged by the chord decomposition of §5.) -/

/-- The Sender dynamic objective at the defiance policy `a = 0` is strictly
increasing in the sanction on `[0,1]`, at every physical state. -/
theorem fgc_senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ fgcCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    StrictMonoOn
      (fun s => fgcParams.U_S x 0 s
        + fgcParams.β_S * V_S (Sanctions.clipS' (fgcParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : (x + s₁)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hx.1], by nlinarith [hs₁.2, hx.2]⟩
  have hmem₂ : (x + s₂)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hs₂.1, hx.1], by nlinarith [hs₂.2, hx.2]⟩
  have hdiff : V_S (Sanctions.clipS' ((x + s₂)/2))
      - V_S (Sanctions.clipS' ((x + s₁)/2))
      = (4/3) * ((x + s₂)/2 - (x + s₁)/2) :=
    gainBall_clip_diff (by norm_num) (mem_fgcCarrierS_num hV_S) hmem₁ hmem₂
  simp only [fgcParams_U_S, fgcParams_β_S, fgcParams_F]
  have hcoef : (0:ℝ) < 1/3 + 2 + x - (s₁ + s₂)/2 := by
    nlinarith [hx.1, hs₁.2, hs₂.2]
  have hprod := mul_pos (show (0:ℝ) < s₂ - s₁ by linarith) hcoef
  nlinarith [hdiff, hprod]

/-- **`σ_dyn` pinned at the corner `1` at the defiance policy `a = 0`**,
for every carrier `V_S` and every physical state. -/
theorem fgc_σ_dyn_zero_eq_one {V_S : Val} (hV_S : V_S ∈ fgcCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    fgcParams.σ_dyn V_S x 0 = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn (fgc_senderObj_strictMonoOn hV_S hx)

/-! ## 4. State-local Sender argmax uniqueness (DAU) -/

/-- **State-local `DynamicArgmaxUnique` on the Sender carrier.** On the
physical state space the Sender objective is a strictly concave parabola
(the clip is inactive, the carrier `V_S` is affine of slope `4/3`). -/
theorem fgc_DAU_on_carrier {V_S : Val} (hV_S : V_S ∈ fgcCarrierS) :
    fgcParams.DynamicArgmaxUnique V_S := by
  apply fgcParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have hQ : ∀ s ∈ Sanctions.I,
      fgcParams.U_S x a s
          + fgcParams.β_S * V_S (Sanctions.clipS' (fgcParams.F x s))
        = -(1/2) * s ^ 2 + (2 + x - 11/5 * a + 1/3) * s
          + (1/3 * x + 1/2 * c₀) := by
    intro s hs
    have hmem : (x + s)/2 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by nlinarith [hs.1, hx.1], by nlinarith [hs.2, hx.2]⟩
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hdiff := gainBall_clip_diff (show (0:ℝ) ≤ 4/3 by norm_num)
      (mem_fgcCarrierS_num hV_S) h0 hmem
    simp only [fgcParams_U_S, fgcParams_β_S, fgcParams_F]
    rw [hc₀]
    linear_combination (1/2) * hdiff
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p q hp hq hpq
  have hq_eq : q = 1 - p := by linarith
  subst hq_eq
  have hmid : p * s₁ + (1 - p) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  simp only [smul_eq_mul, hQ s₁ hs₁, hQ s₂ hs₂, hQ _ hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [mul_pos (mul_pos hp hq) hsq]

/-! ## 5. The leader side: chord decomposition of the joint integrand

`J(x,a) − J(x,0) = −(1/5)a + (σ_a − 1)·(x − 14/5 + 36/11)` where
`σ_a := σ_dyn(V_S) x a ∈ [0,1]` (only membership needed), the direct
compliance slope of the derived `U_T` is `−1/5`, and the bracket
`x + 26/55 > 0` multiplies `(σ_a − 1) ≤ 0` — so
`J(x,a) ≤ J(x,0) − (1/5)a`: full defiance is the strict leader argmax. -/

/-- Joint Target integrand evaluated through the closed forms (generic
compliance; the dynamic Sender response is kept symbolic). -/
theorem fgc_joint_T_integrand_eval (V_T V_S : Val) (x a : ℝ) :
    fgcParams.joint_T_integrand V_T V_S x a
      = 3 * x - 1/5 * a + fgcParams.σ_dyn V_S x a * (x - 14/5)
        + 9/10 * V_T (Sanctions.clipS'
            ((x + fgcParams.σ_dyn V_S x a)/2)) := by
  simp only [AbstractGame.Params.joint_T_integrand]
  rw [show fgcParams.F x (fgcParams.σ_dyn V_S x a)
      = (x + fgcParams.σ_dyn V_S x a)/2 from fgcParams_F x _]
  simp only [fgcParams_U_T, fgcParams_β_T]

/-- **The chord bound**: raising compliance from `0` to `a` lowers the
joint integrand by at least `(1/5)·a` — compliance costs `1/5` per unit
directly, and any sanction relief `(1 − σ_a)` it might buy is *worth
negative* to the Target on the carrier (bracket `x + 26/55 > 0`). -/
theorem fgc_joint_T_chord {V_T : Val} (hV_T : V_T ∈ fgcCarrierT)
    {V_S : Val} (hV_S : V_S ∈ fgcCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (_ha : a ∈ Sanctions.I) :
    fgcParams.joint_T_integrand V_T V_S x a
      ≤ fgcParams.joint_T_integrand V_T V_S x 0 - 1/5 * a := by
  have hσm := fgcParams.σ_dyn_mem V_S x a
  have hσ0 := fgc_σ_dyn_zero_eq_one hV_S hx
  have hmem₁ : (x + fgcParams.σ_dyn V_S x a)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hσm.1, hx.1], by nlinarith [hσm.2, hx.2]⟩
  have hmem₂ : (x + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have hdiff := gainBall_clip_diff (show (0:ℝ) ≤ 80/11 by norm_num)
    (mem_fgcCarrierT_num hV_T) hmem₂ hmem₁
  rw [fgc_joint_T_integrand_eval V_T V_S x a,
      fgc_joint_T_integrand_eval V_T V_S x 0, hσ0]
  nlinarith [hdiff,
    mul_nonneg (show (0:ℝ) ≤ 1 - fgcParams.σ_dyn V_S x a by linarith [hσm.2])
      (show (0:ℝ) ≤ x + 26/55 by linarith [hx.1])]

/-- **Zero (full defiance) is the Target argmax** at every physical state. -/
theorem fgc_zero_isMaxOn_joint {V_T : Val} (hV_T : V_T ∈ fgcCarrierT)
    {V_S : Val} (hV_S : V_S ∈ fgcCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn (fun a => fgcParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  have h := fgc_joint_T_chord hV_T hV_S hx ha
  have ha0 := ha.1
  show fgcParams.joint_T_integrand V_T V_S x a
      ≤ fgcParams.joint_T_integrand V_T V_S x 0
  linarith

/-- **State-local `TargetArgmaxUnique` on the carriers**: the chord bound
makes `0` the strictly unique maximizer, so any two maximizers coincide. -/
theorem fgc_TAU_on_carriers {V_T V_S : Val}
    (hV_T : V_T ∈ fgcCarrierT) (hV_S : V_S ∈ fgcCarrierS) :
    fgcParams.TargetArgmaxUnique V_T V_S := by
  intro x hx a₁ a₂ ha₁ ha₂ h₁ h₂
  have h0 : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩
  have hz₁ : a₁ = 0 := by
    have hle : fgcParams.joint_T_integrand V_T V_S x 0
        ≤ fgcParams.joint_T_integrand V_T V_S x a₁ := h₁ h0
    have hc := fgc_joint_T_chord hV_T hV_S hx ha₁
    have := ha₁.1
    linarith
  have hz₂ : a₂ = 0 := by
    have hle : fgcParams.joint_T_integrand V_T V_S x 0
        ≤ fgcParams.joint_T_integrand V_T V_S x a₂ := h₂ h0
    have hc := fgc_joint_T_chord hV_T hV_S hx ha₂
    have := ha₂.1
    linarith
  rw [hz₁, hz₂]

/-! ## 6. The asymmetric value class and the derived leader policy -/

/-- **The `ValueClass2` at the microfounded witness**: slope-pinned affine
gain-ball carriers with state-local Sender/Target argmax uniqueness. -/
def fgcClass : fgcParams.ValueClass2 where
  carrier_T := fgcCarrierT
  carrier_S := fgcCarrierS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := valLipGainBall_isClosed _ _ _ _
  nonempty_T := fgcCarrierT_nonempty
  nonempty_S := fgcCarrierS_nonempty
  sender_unique_on := fun _ hV_S => (fgc_DAU_on_carrier hV_S).toOnI
  target_unique_on := fun _ hV_T _ hV_S => fgc_TAU_on_carriers hV_T hV_S

/-- **The derived leader policy is the defiance corner: `α_on ≡ 0`.**
Rule 1: this is the *derived* argmax of the joint dynamic objective,
pinned by the chord decomposition and state-local uniqueness. -/
theorem fgc_α_on_eq_zero (V_T : fgcClass.CarrierT)
    (V_S : fgcClass.CarrierS) :
    fgcClass.α_on V_T V_S = fun _ => (0:ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    fgc_zero_isMaxOn_joint V_T.property V_S.property y.property

/-! ## 7. Bellman images in closed form -/

/-- **Target Bellman image in closed form**: the sSup over compliance
collapses at the defiance corner `a = 0` (where `σ_dyn = 1`). -/
theorem fgc_jointTarget_image (V_T : fgcClass.CarrierT)
    (V_S : fgcClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    fgcParams.jointTarget_BCF_on_S V_T.val V_S.val
      (fgcClass.sender_unique_on V_S.val V_S.property) y
      = 4 * y.val - 14/5
        + 9/10 * V_T.val (Sanctions.clipS' ((y.val + 1)/2)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (fgcClass.sender_unique_on V_S.val V_S.property) y
        ⟨le_refl 0, by norm_num⟩
        (fgc_zero_isMaxOn_joint V_T.property V_S.property y.property),
      fgc_joint_T_integrand_eval V_T.val V_S.val y.val 0,
      fgc_σ_dyn_zero_eq_one V_S.property y.property]
  ring

/-- **Sender Bellman image in closed form** at the defiance policy
`α ≡ 0`: the sSup over sanctions collapses at the corner `s = 1`. -/
theorem fgc_bellmanS_image {W : Val} (hW : W ∈ fgcCarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    fgcParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3/2 + y.val
        + 1/2 * W (Sanctions.clipS' ((y.val + 1)/2)) := by
  have h1I : (1:ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmono := fgc_senderObj_strictMonoOn hW y.property
  rw [WitnessKit.bellmanS_image_of_isMaxOn (α := fun _ => (0:ℝ))
        continuous_const W y h1I
        (isMaxOn_iff.mpr fun s hs => hmono.monotoneOn hs h1I hs.2)]
  rw [show fgcParams.F y.val 1 = (y.val + 1)/2 from fgcParams_F _ _]
  simp only [fgcParams_U_S, fgcParams_β_S]
  ring

/-! ## 8. Carrier invariance -/

/-- **Heterogeneous carrier invariance**, discharged by the general
two-sided-band lemma `mem_valLipGainBall_bellman_chord`, at the
degenerate band `glo = ghi = 1 − δ = 1/2`. Both Bellman
images are corner-pinned affine, so each re-enters *the same* ball: the
image slope `g_U + β·K·δ` is `K` exactly because `K` is the SLP closed
form, and the image sup-norm bound `M_U + β·M` is `M` exactly because
`M` is the radius closed form. No magnitude here is chosen. -/
theorem fgcClass_IsInvariant : fgcClass.IsInvariant := by
  intro V_T V_S
  constructor
  · -- Target image ∈ fgcCarrierT.
    show fgcParams.jointTarget_BCF_on_S V_T.val V_S.val
        (fgcClass.sender_unique_on V_S.val V_S.property) ∈ fgcCarrierT
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := fgcParams.β_T)
      (glo := 1 - fgcParams.δ) (ghi := 1 - fgcParams.δ)
      (c₀ := fgcStageT 0) (L_U := fgcStageSlopeT) (g_U := fgcStageSlopeT)
      (M_U := fgcStageNormT) (stage := fun y => fgcStageSlopeT * y)
      (F := fgcParams.F)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      ?_ ?_ ?_
      (fun y hy => fgcParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩) ?_
      le_rfl le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_T.property ?_
    · intro z hz
      simp only [fgcStageT_eq, fgcStageSlopeT_eq, fgcStageNormT_eq]
      rw [abs_le]
      constructor <;> nlinarith [hz.1, hz.2]
    · intro y₁ _ y₂ _
      rw [show fgcStageSlopeT * y₂ - fgcStageSlopeT * y₁
          = fgcStageSlopeT * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ fgcStageSlopeT)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y₁ y₂ _ _ hle
      simp only [fgcParams_F, fgcParams_δ]
      constructor <;> linarith
    · intro y
      rw [fgc_jointTarget_image V_T V_S y,
        show fgcParams.F y.val 1 = (y.val + 1)/2 from fgcParams_F _ _]
      simp only [fgcStageT_eq, fgcStageSlopeT_eq, fgcParams_β_T]
      ring
  · -- Sender image ∈ fgcCarrierS.
    show fgcParams.bellmanS_BCF (fgcClass.α_on V_T V_S)
        (fgcClass.α_on_continuous V_T V_S) V_S.val ∈ fgcCarrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (fgc_α_on_eq_zero V_T V_S)
        (fgcClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := fgcParams.β_S)
      (glo := 1 - fgcParams.δ) (ghi := 1 - fgcParams.δ)
      (c₀ := fgcStageS 0) (L_U := fgcStageSlopeS) (g_U := fgcStageSlopeS)
      (M_U := fgcStageNormS) (stage := fun y => fgcStageSlopeS * y)
      (F := fgcParams.F)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      ?_ ?_ ?_
      (fun y hy => fgcParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩) ?_
      le_rfl le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_S.property ?_
    · intro z hz
      simp only [fgcStageS_eq, fgcStageSlopeS_eq, fgcStageNormS_eq]
      rw [abs_le]
      constructor <;> nlinarith [hz.1, hz.2]
    · intro y₁ _ y₂ _
      rw [show fgcStageSlopeS * y₂ - fgcStageSlopeS * y₁
          = fgcStageSlopeS * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ fgcStageSlopeS)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y₁ y₂ _ _ hle
      simp only [fgcParams_F, fgcParams_δ]
      constructor <;> linarith
    · intro y
      rw [fgc_bellmanS_image V_S.property y,
        show fgcParams.F y.val 1 = (y.val + 1)/2 from fgcParams_F _ _]
      simp only [fgcStageS_eq, fgcStageSlopeS_eq, fgcParams_β_S]
      ring

/-! ## 9. Schur row bounds (`L_TS = L_ST = 0`, decoupled) -/

/-- **Target-row bound**: `β_T = 9/10`, cross coefficient `L_TS = 0` (the
Target image is `V_S`-independent, since `σ_dyn(·,0) ≡ 1` on the carrier). -/
theorem fgcClass_hT_T_op
    (h_inv : fgcClass.IsInvariant)
    (V V' : fgcClass.CarrierT) (W W' : fgcClass.CarrierS) :
    dist (fgcClass.jointTargetOp_sub h_inv (V, W))
          (fgcClass.jointTargetOp_sub h_inv (V', W'))
      ≤ (9/10 : ℝ) * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun y => 4 * y - 14/5) (φ := fun y => (y + 1)/2)
    fgc_jointTarget_image V V' W W'

/-- **Sender-row bound**: `β_S = 1/2`, cross coefficient `L_ST = 0` (the
Sender operator is `V_T`-independent because the derived leader policy is
the constant `α_on ≡ 0` for every carrier pair). -/
theorem fgcClass_hT_S_op
    (h_inv : fgcClass.IsInvariant)
    (V V' : fgcClass.CarrierT) (W W' : fgcClass.CarrierS) :
    dist (fgcClass.jointSenderOp_sub h_inv (V, W))
          (fgcClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    fgc_α_on_eq_zero V V' W W'

/-! ## 10. The myopic comparator

The myopic (β = 0) Target best-responds to the *static* placable Sender:
`M.α(x) = min(1, (5x+10)/11)`. At pre-basin states it complies exactly
enough to zero out sanctions (`σ = 0`); on `x ≥ 1/5` it corners at full
compliance and buys sanctions down to the interior `σ_myo(x) = x − 1/5`.
The myopic objective `G(a) = 3x − a/5 + σ(x,a)·(x − 14/5)` is piecewise:
decreasing while the Sender is clipped at `σ = 1` (slope `−1/5`), steeply
increasing on the placation region (slope `149/25 − (11/5)x ≥ 94/25`),
decreasing again once `σ = 0`. Corner gain `G(M.α) − G(0) ≥ 4/25` at the
worst basin state `x = 1`; pre-basin gain `≥ 12/5`. -/

/-- **The myopic feedback equilibrium at the microfounded witness.** -/
def fgcMyopic : fgcParams.MyopicFeedbackEquilibrium where
  α := fun x => min 1 ((5 * x + 10)/11)
  α_mem := fun x hx =>
    ⟨le_min (by norm_num) (by linarith [hx.1]), min_le_left _ _⟩
  α_opt := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [isMaxOn_iff]
    intro a ha
    obtain ⟨ha0, ha1⟩ := ha
    show fgcParams.U_T x a (fgcParams.σ x a)
        ≤ fgcParams.U_T x (min 1 ((5 * x + 10)/11))
            (fgcParams.σ x (min 1 ((5 * x + 10)/11)))
    simp only [fgcParams_U_T, fgcParams_σ]
    rcases le_total (1/5 : ℝ) x with hx5 | hx5
    · -- `x ≥ 1/5`: myopic corner `a = 1`, interior sanction `x − 1/5`.
      have hα : min 1 ((5 * x + 10)/11) = 1 :=
        min_eq_left (by linarith : (1:ℝ) ≤ (5 * x + 10)/11)
      rw [hα]
      have hσ1 : max 0 (min 1 (2 + x - 11/5 * 1)) = x - 1/5 := by
        rw [show 2 + x - 11/5 * (1:ℝ) = x - 1/5 by ring,
            min_eq_right (by linarith : x - 1/5 ≤ 1),
            max_eq_right (by linarith : (0:ℝ) ≤ x - 1/5)]
      rw [hσ1]
      rcases le_total 1 (2 + x - 11/5 * a) with ht1 | ht1
      · -- Sender clipped at `σ = 1`.
        have hσa : max 0 (min 1 (2 + x - 11/5 * a)) = 1 := by
          rw [min_eq_left ht1, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        rw [hσa]
        nlinarith [sq_nonneg (1 - x), ha0, hx1]
      · rcases le_total 0 (2 + x - 11/5 * a) with ht0 | ht0
        · -- interior Sender response.
          have hσa : max 0 (min 1 (2 + x - 11/5 * a)) = 2 + x - 11/5 * a := by
            rw [min_eq_right ht1, max_eq_right ht0]
          rw [hσa]
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a)
            (by linarith : (0:ℝ) ≤ 149/25 - 11/5 * x)]
        · -- `σ = 0` (degenerate: forces `x = 1/5`, `a = 1`).
          have hσa : max 0 (min 1 (2 + x - 11/5 * a)) = 0 := by
            rw [min_eq_right (le_trans ht0 (by norm_num : (0:ℝ) ≤ 1)),
                max_eq_left ht0]
          rw [hσa]
          have hx15 : x = 1/5 := le_antisymm (by linarith) hx5
          rw [hx15] at ht0 ⊢
          nlinarith [ht0]
    · -- `x < 1/5`: interior myopic compliance zeroes the sanction.
      have hα : min 1 ((5 * x + 10)/11) = (5 * x + 10)/11 :=
        min_eq_right (by linarith : (5 * x + 10)/11 ≤ 1)
      rw [hα]
      have hσm : max 0 (min 1 (2 + x - 11/5 * ((5 * x + 10)/11))) = 0 := by
        rw [show 2 + x - 11/5 * ((5 * x + 10)/11) = 0 by ring,
            min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]
      rw [hσm]
      rcases le_total 1 (2 + x - 11/5 * a) with ht1 | ht1
      · have hσa : max 0 (min 1 (2 + x - 11/5 * a)) = 1 := by
          rw [min_eq_left ht1, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        rw [hσa]
        nlinarith [ha0, hx5]
      · rcases le_total 0 (2 + x - 11/5 * a) with ht0 | ht0
        · have hσa : max 0 (min 1 (2 + x - 11/5 * a)) = 2 + x - 11/5 * a := by
            rw [min_eq_right ht1, max_eq_right ht0]
          rw [hσa]
          have h_gap : (0:ℝ) ≤ (5 * x + 10)/11 - a := by linarith
          have h_pos : (0:ℝ) ≤ 149/25 - 11/5 * x := by linarith
          nlinarith [mul_nonneg h_gap h_pos]
        · have hσa : max 0 (min 1 (2 + x - 11/5 * a)) = 0 := by
            rw [min_eq_right (le_trans ht0 (by norm_num : (0:ℝ) ≤ 1)),
                max_eq_left ht0]
          rw [hσa]
          nlinarith [ht0]

/-- **Myopic ceiling on the basin**: the myopic realized sanction stays
below `max(x, s̄)` — with slack `1/5` on `x ≥ 1/5` (`σ_myo = x − 1/5`)
and trivially at pre-basin states (`σ_myo = 0`). -/
theorem fgc_hMyoCeiling :
    ∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
      fgcParams.σ x (fgcMyopic.α x) ≤ max x (1/2 : ℝ) := by
  intro x hx
  have hx1 : x ≤ 1 := hx.2
  show fgcParams.σ x (min 1 ((5 * x + 10)/11)) ≤ max x (1/2 : ℝ)
  rw [fgcParams_σ]
  rcases le_total (1/5 : ℝ) x with hx5 | hx5
  · have hα : min 1 ((5 * x + 10)/11) = 1 :=
      min_eq_left (by linarith : (1:ℝ) ≤ (5 * x + 10)/11)
    rw [hα, show 2 + x - 11/5 * (1:ℝ) = x - 1/5 by ring,
        min_eq_right (by linarith : x - 1/5 ≤ 1),
        max_eq_right (by linarith : (0:ℝ) ≤ x - 1/5)]
    exact le_trans (by linarith) (le_max_left x (1/2 : ℝ))
  · have hα : min 1 ((5 * x + 10)/11) = (5 * x + 10)/11 :=
      min_eq_right (by linarith : (5 * x + 10)/11 ≤ 1)
    rw [hα, show 2 + x - 11/5 * ((5 * x + 10)/11) = 0 by ring,
        min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]
    exact le_trans (by norm_num) (le_max_right x (1/2 : ℝ))

/-! ## 11. Stage fields -/

/-- **Stage Target loss bound** at the derived (defiant) leader policy:
the loss rate `14/5 − x ≤ 27/10` on the basin is at most `cT = 14/5`
(slack `x ≥ 1/10`). -/
theorem fgc_h_stage_target_loss
    (V_T : fgcClass.CarrierT) (V_S : fgcClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerLossSlopeOn
        (fun s => fgcParams.U_T x (fgcClass.α_on V_T V_S x) s)
        (Set.Icc (max x (1/2 : ℝ)) 1) (14/5) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [fgc_α_on_eq_zero V_T V_S, fgcParams_U_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ x by linarith [hx.1])]

/-- **Stage Sender slope** at the derived leader policy: chord slope
`2 + x − (s₁+s₂)/2 ≥ 8/5 > 3/2 = mS` on `[0, max(x, s̄)]` for basin `x`
(the key inequality: `max(x, 1/2) ≤ x + 2/5` at the basin bottom). -/
theorem fgc_h_stage_sender
    (V_T : fgcClass.CarrierT) (V_S : fgcClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerSlopeOn
        (fun s => fgcParams.U_S x (fgcClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (1/2 : ℝ))) (3/2) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hmax : max x (1/2 : ℝ) ≤ x + 2/5 := by
    rcases max_cases x (1/2 : ℝ) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;>
      linarith [hx.1]
  simp only [fgc_α_on_eq_zero V_T V_S, fgcParams_U_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 2 + x - (s₁ + s₂)/2 - 3/2 by
      linarith [hs₁.2, hs₂.2, hmax])]

/-- **Carrier `V_T` gain on the basin**: restriction of the gain-ball
minimum slope from `[0,1]` to `[1/10, 1]`. -/
theorem fgc_hV_T_gain :
    ∀ V_T ∈ fgcClass.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc (1/10 : ℝ) 1) (80/11) := by
  intro V_T hV_T y₁ y₂ h1 h2 hle
  exact (mem_fgcCarrierT_num hV_T).2.2 y₁ y₂
    ⟨by linarith [h1.1], h1.2⟩ ⟨by linarith [h2.1], h2.2⟩ hle

/-- **Single crossing (trivial form)**: the Sender dynamic objective at
the derived defiance policy is strictly increasing in the sanction at
every basin state, so both single-crossing consequents hold. -/
theorem fgc_hSC (V_T : fgcClass.CarrierT) (V_S : fgcClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max (1/10 : ℝ) (1/10)) 1)
      (fun s x => fgcParams.senderDynObjective V_S.val x
        (fgcClass.α_on V_T V_S x) s) := by
  apply WitnessKit.singleCrossingOn_of_strictMonoOn
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans (by norm_num) (le_trans (le_max_left _ _) ht.1), ht.2⟩
  simp only [fgc_α_on_eq_zero V_T V_S,
    AbstractGame.Params.senderDynObjective]
  exact fgc_senderObj_strictMonoOn V_S.property ht'

/-! ## 12. THE CERTIFICATE -/

/-- **The first certificate-complete witness with microfounded stage
payoffs.** Every field discharged unconditionally at `fgcParams` — whose
`U_S`, `U_T`, `σ` are *derived* from the four-group polity `fourGroupCert`:
the slope-pinned gain-ball value class with state-local argmax uniqueness
(`D`), Bellman invariance (`h_inv`), decoupled Schur rows
(`β_T = 9/10, β_S = 1/2, L_TS = L_ST = 0`), the high basin `[1/10, 1]`
with sanction floor `s̄ = 1/2`, the Sender stage margin
(`mS = 3/2 > 1/3 = β_S·KS·δ`), carrier-local stage slopes, interval
dominance (via single crossing), and the myopic comparator with its
ceiling (`σ_myo(x) = clip(x − 1/5) ≤ max(x, 1/2)`, slack `1/5`). The Target
loss-offset (`cT = 14/5 ≤ 36/11 = β_T·gT·δ`) was a field until round BJ1.4
(2026-10-07); its halves remain proved here (`fgc_h_stage_target_loss`,
`fgc_hV_T_gain`). -/
noncomputable def fourGroupCertCertificate :
    fgcParams.StandardComplianceLocalCoreCertificate where
  D := fgcClass
  h_inv := fgcClass_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := fgcClass_hT_T_op fgcClass_IsInvariant
  hT_S_op := fgcClass_hT_S_op fgcClass_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 1/10
  xS := 1/10
  sbar := 1/2
  mS := 3/2
  KS := 4/3
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  d := fgcParams.δ
  hF_chord := fgcParams.affine_sender_chord_on rfl _ _
  hS_margin := by
    simp only [fgcParams_β_S, fgcParams_δ]
    norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := fun _ hV_S => (mem_fgcCarrierS_num hV_S).2.1
  h_stage_sender_on := fgc_h_stage_sender
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (fgc_hSC V_T V_S)
  M := fgcMyopic
  hMyoCeiling := fgc_hMyoCeiling

/-! ## 13. The unconditional three-goals corollary -/

/-- **Unconditional three-goals dominance at the microfounded witness**
(Goal 2 exposed; Goals 1 and 3 are delivered by the same certificate via
`three_goals_local_uniform_starts`). The forward-looking equilibrium
exists on the carriers, and on the whole basin the myopic realized
sanction is dominated by the forward-looking realized sanction — with
both stage payoffs derived from the four-group interest-group polity
rather than hand-asserted. Upgrades the Rule-15 honest-conditional
`fourGroupWitnessParams_three_goals_conditional`: the certificate is
fully constructed above, so nothing is left conditional. -/
theorem fourGroupCert_three_goals_dominance :
    ∃ E : fgcParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ fgcCarrierT ∧ E.V_S ∈ fgcCarrierS
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
           fgcParams.σ x (fgcMyopic.α x)
             ≤ fgcParams.dynamicTopRealizedRule E.V_S E.α x) := by
  -- G3 re-route (2026-08-19): Goal 2 mentions no transition, so it is
  -- taken through the general-`F` chord route rather than the affine
  -- `three_goals_local_uniform_starts`. The statement is unchanged. Round
  -- BG (2026-10-06): the call goes to `goal2_dominance_generalF` itself;
  -- the affine wrapper it used to pass through read neither its `hF` nor
  -- its `0 ≤ g_T` binder and was deleted. The affine law enters only as the
  -- `d = δ` instance of the certificate's Sender chord field (its Target lower
  -- chord at `dlo` was deleted in round BJ1.4).
  obtain ⟨E, hVT, hVS, hG2⟩ :=
    fourGroupCertCertificate.goal2_dominance_generalF (p := fgcParams)
  exact ⟨E, hVT, hVS, hG2⟩

/-! ## Within-carrier uniqueness (Schur route, 2026-07-24) -/

/-- Schur-certificate inhabitant at the microfounded four-group witness,
via the row-sum ⇒ Schur bridge (decoupled rows:
`L_TS·L_ST = 0 < (1/10)·(1/2)`). -/
noncomputable def fourGroupCertCertificateSchur :
    fgcParams.StandardComplianceLocalCoreCertificateSchur :=
  AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur.ofRowSum
    fgcParams fourGroupCertCertificate

/-- **Witness within-carrier uniqueness at the microfounded four-group
economy.** Any two top-selector feedback Stackelberg equilibria with
carrier values and selector-coinciding policies agree in both value
functions and the policy; every quantitative input is machine-discharged
by `fourGroupCertCertificate` — the uniqueness result at the only
witness whose payoffs are derived from the Kaempfer–Lowenberg
group-politics microfoundation. -/
theorem fourGroupCert_unique_in_carrier
    (E E' : fgcParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ fgcCarrierT) (hVS : E.V_S ∈ fgcCarrierS)
    (hVT' : E'.V_T ∈ fgcCarrierT) (hVS' : E'.V_S ∈ fgcCarrierS)
    (hαE : E.α = fgcClass.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = fgcClass.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  fourGroupCertCertificate.unique_in_carrier (p := fgcParams)
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Witness within-carrier uniqueness at the microfounded four-group economy,
with no selector hypothesis (round BH1.1, 2026-10-06).** Sibling of
`fourGroupCert_unique_in_carrier` without `hαE`, `hαE'`: any two top-selector
feedback Stackelberg equilibria whose values lie in the carriers share both value
functions, and their policies agree at every feasible state. Every quantitative
input is discharged by `fourGroupCertCertificate`, through the certificate-level
`unique_in_carrier_of_mem`. The economy runs the affine law (`δ = 1/2`); the
theorem it instantiates is general in `F`. -/
theorem fourGroupCert_unique_in_carrier_of_mem
    (E E' : fgcParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ fgcCarrierT) (hVS : E.V_S ∈ fgcCarrierS)
    (hVT' : E'.V_T ∈ fgcCarrierT) (hVS' : E'.V_S ∈ fgcCarrierS) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  fourGroupCertCertificate.unique_in_carrier_of_mem (p := fgcParams)
    E E' hVT hVS hVT' hVS'

end -- noncomputable section

#print axioms fourGroupCertCertificate
#print axioms fourGroupCert_three_goals_dominance
#print axioms fourGroupCertCertificateSchur
#print axioms fourGroupCert_unique_in_carrier
#print axioms fourGroupCert_unique_in_carrier_of_mem
#print axioms fgc_joint_T_chord
#print axioms fgc_α_on_eq_zero
#print axioms fgcClass_IsInvariant

end Examples

end Sanctions
