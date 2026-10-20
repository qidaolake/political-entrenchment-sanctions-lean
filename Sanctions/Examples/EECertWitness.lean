/-
Sanctions/Examples/EECertWitness.lean

**The first complete `StandardComplianceLocalCoreCertificate` witness.**

An Eaton-Engers-form economy with certificate-tuned constants (probe-validated
2026-07-01, `docs/archive/workflow-scratch/ee_cert_probe.py`, all inequalities pass):

  U_S(x,a,s) = a − ½s² + s·(2 − (11/5)a + x) + 3x
  U_T(x,a,s) = −(1/5)a + s·((1/10)a + (1/10)x − 3) + 4x
  F(x,s)     = (x+s)/2            (affineF, δ = 1/2)
  β_S = 1/2,  β_T = 9/10
  σ(x,a)     = clip(x + 2 − (11/5)a)   (static stage vertex)
  basin: xT = xS = 1/10, s̄ = 1/2

All four literature sign conditions of the P2 witness (`EatonEngersWitness`)
hold: ∂²U_S/∂s∂x = 1 > 0 and ∂²U_T/∂s∂x = 1/10 > 0 (Kaempfer-Lowenberg
rally), ∂²U_S/∂s∂a = −11/5 < 0 (Eaton-Engers "compliance placates"),
∂²U_S/∂s² = −1 < 0 (strict concavity). The constants differ from P2 so
that the **equilibrium is globally affine** (no non-smooth flip): on the
slope-pinned gain-ball carriers the dynamic Sender response is the corner
`σ_dyn ≡ 1` at every physical state and the dynamic Target response is the
corner `α_dyn ≡ 0`, giving exact affine Bellman images
(`V_S* = (16x+17)/3`, `V_T* = (82x+39)/11`).

The economics: the forward-looking Sender is **implacable** (sanctions
maxed regardless of compliance, because the continuation value of the
political state dominates), so the forward-looking hardline Target
**defies** (`α_dyn = 0`). The *myopic* Sender is placable (`σ` responds to
compliance through the `−(11/5)·a·s` placation term), so the myopic Target
**complies** (`M.α(x) = min(1, (5x+10)/11)`), buying its sanctions down to
`σ_myo(x) = clip(x − 1/5) < 1`. The dominance gap
`σ_dyn − σ_myo ≥ 1/5` is strict on the whole basin and the myopic realized
sanction is interior on `(1/5, 1)` — the substantive (non-degenerate)
content the polynomial floor witness lacked.

Design law (why the placation term is necessary): the certificate's
`h_stage_sender_on` + `hS_margin` + `hMyoCeiling` are jointly UNSATISFIABLE
for any compliance-independent `U_S` (machine-checked at the previous
candidate: `substParams_certificate_senderSide_infeasible`). The escape is
`k·a_myo > β_S·K_S·δ`: the placation shift at the myopic action must
exceed the discounted continuation Lipschitz bound.
-/

import Sanctions.Examples.SubstantiveComplianceWitness
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Certificates.StandardComplianceSchur
import Sanctions.Theory.Certificates.GeneralFDischargers
import Sanctions.Theory.Bellman.ChordInvariance
-- `affine_sender_chord_on`, which discharges this economy's `hF_chord` field.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The parameters -/

/-- Sender stage payoff. `∂²U_S/∂s∂x = 1 > 0` (rally),
`∂²U_S/∂s∂a = −11/5 < 0` (compliance placates), `∂²U_S/∂s² = −1 < 0`. -/
def eecU_S (x a s : ℝ) : ℝ := a - 1/2 * s ^ 2 + s * (2 - 11/5 * a + x) + 3 * x

/-- Target stage payoff. `∂²U_T/∂s∂x = 1/10 > 0` (rally),
`∂U_T/∂a` at `s = 1` is `−1/10 < 0` (defiance under maxed sanctions). -/
def eecU_T (x a s : ℝ) : ℝ := -(1/5) * a + s * (1/10 * a + 1/10 * x - 3) + 4 * x

/-- Static Sender response: the clipped vertex of the concave parabola
`U_S(x,a,·)`, `σ(x,a) = clip(x + 2 − (11/5)a)`. -/
def eecσ (x a : ℝ) : ℝ := max 0 (min 1 (x + 2 - 11/5 * a))

theorem eecσ_mem (x a : ℝ) : eecσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem eecσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => eecσ xa.1 xa.2) := by
  unfold eecσ
  fun_prop

/-- **Rule-1 coupling.** The clipped vertex maximizes `U_S(x,a,·)` on
`[0,1]`: `U_S(x,a,s) = C(x,a) − ½(s − t)²` with `t = x + 2 − (11/5)a`. -/
theorem eecσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => eecU_S x a s) (Set.Icc (0 : ℝ) 1) (eecσ x a) :=
  WitnessKit.clipVertex_isMaxOn (by norm_num : (0:ℝ) < 1/2)
    (C := a + 3 * x + 1/2 * (x + 2 - 11/5 * a) ^ 2)
    (fun s => by simp only [eecU_S]; ring)

/-- **The certificate witness `Params` (Eaton-Engers form, tuned constants).** -/
def eeCertParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 9/10
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := eecU_T
  U_S := eecU_S
  σ := eecσ
  σ_mem := eecσ_mem
  σ_isMaxOn_U_S := eecσ_isMaxOn
  U_T_continuous := by unfold eecU_T; fun_prop
  U_S_continuous := by unfold eecU_S; fun_prop
  F := AbstractGame.affineF (1/2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`eeCertParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance eeCertParams_staticSelectorContinuous :
    eeCertParams.StaticSelectorContinuous where
  σ_continuous := eecσ_continuous

@[simp] theorem eeCertParams_U_S : eeCertParams.U_S = eecU_S := rfl
@[simp] theorem eeCertParams_U_T : eeCertParams.U_T = eecU_T := rfl
@[simp] theorem eeCertParams_δ : eeCertParams.δ = 1/2 := rfl
@[simp] theorem eeCertParams_β_S : eeCertParams.β_S = 1/2 := rfl
@[simp] theorem eeCertParams_β_T : eeCertParams.β_T = 9/10 := rfl

/-- Transition closed form: `F(x,s) = (x+s)/2`. -/
theorem eeCertParams_F (x s : ℝ) : eeCertParams.F x s = (x + s) / 2 := by
  show AbstractGame.affineF (1/2) x s = (x + s) / 2
  unfold AbstractGame.affineF
  ring

/-! ## 2. Carriers: slope-pinned affine gain balls at the SLP closed forms

A slope-pinned gain ball has exactly two magnitudes, its slope and its
radius, and both are governed by the Stokey-Lucas closed forms evaluated
at this economy's own primitives — applied to the stage payoff each
player collects along the **derived** corner path (full sanctions
`σ_dyn ≡ 1`, §4, against full defiance `α_on ≡ 0`, §6):

* slope  `= bellmanLipConstant β δ g_U = g_U / (1 − β·δ)`  (Hinderer 4.2(c) /
  Hinderer 4.2(c): the discounted geometric sum of the stage state-slope amplified
  through the transition). This one is **forced**: no other slope makes
  the ball Bellman-invariant, and the carriers below are now *defined*
  by the closed form, with `16/3` and `82/11` surviving only as proved
  evaluations of it.
* radius `≥ bellmanNormBound β M_U = M_U / (1 − β)`  (the discounted
  geometric sum of the largest stage payoff attainable). Here the closed
  form is a **minimum**, not an identity: every larger radius is
  invariant too. At this witness the radius keeps deliberate slack above
  that minimum (`12 > 11` Sender, `80 > 30` Target) because
  `eeCert_epsilon_isolation` spends exactly that slack as its isolation
  radius `(ε_T, ε_S) = (69, 1)`. The slack is therefore exhibited —
  `eeCarrierS_closedForm_radius` / `eeCarrierT_closedForm_radius` prove
  what the minimum is and that the shipped radius dominates it — rather
  than removed. See the `fgc` witness for the no-slack case, where the
  radius *is* the closed form. -/

/-- Sender stage payoff along the certified corner path,
`x ↦ U_S(x, 0, 1)`. -/
def eeStageS (x : ℝ) : ℝ := eecU_S x 0 1

/-- Target stage payoff along the certified corner path,
`x ↦ U_T(x, 0, 1)`. -/
def eeStageT (x : ℝ) : ℝ := eecU_T x 0 1

@[simp] theorem eeStageS_eq (x : ℝ) : eeStageS x = 3/2 + 4 * x := by
  simp only [eeStageS, eecU_S]; ring

@[simp] theorem eeStageT_eq (x : ℝ) : eeStageT x = 41/10 * x - 3 := by
  simp only [eeStageT, eecU_T]; ring

/-- State-slope of the Sender's corner stage payoff (the `g_U` of SLP
Hinderer 4.2(c)). -/
def eeStageSlopeS : ℝ := eeStageS 1 - eeStageS 0

/-- State-slope of the Target's corner stage payoff. -/
def eeStageSlopeT : ℝ := eeStageT 1 - eeStageT 0

/-- Sup-norm of the Sender's corner stage payoff on the state space (the
`M_U` of the radius closed form). The stage payoff is affine in the
state, so its sup-norm on `[0,1]` is attained at an endpoint. -/
def eeStageNormS : ℝ := max |eeStageS 0| |eeStageS 1|

/-- Sup-norm of the Target's corner stage payoff on the state space. -/
def eeStageNormT : ℝ := max |eeStageT 0| |eeStageT 1|

@[simp] theorem eeStageSlopeS_eq : eeStageSlopeS = 4 := by
  simp only [eeStageSlopeS, eeStageS_eq]; norm_num

@[simp] theorem eeStageSlopeT_eq : eeStageSlopeT = 41/10 := by
  simp only [eeStageSlopeT, eeStageT_eq]; norm_num

@[simp] theorem eeStageNormS_eq : eeStageNormS = 11/2 := by
  simp only [eeStageNormS, eeStageS_eq]
  rw [show |(3:ℝ)/2 + 4 * 0| = 3/2 by rw [abs_of_nonneg] <;> norm_num,
    show |(3:ℝ)/2 + 4 * 1| = 11/2 by rw [abs_of_nonneg] <;> norm_num]
  norm_num

@[simp] theorem eeStageNormT_eq : eeStageNormT = 3 := by
  simp only [eeStageNormT, eeStageT_eq]
  rw [show |(41:ℝ)/10 * 0 - 3| = 3 by rw [abs_of_nonpos] <;> norm_num,
    show |(41:ℝ)/10 * 1 - 3| = 11/10 by rw [abs_of_nonneg] <;> norm_num]
  norm_num

/-- Sender carrier: the slope-pinned gain ball whose **slope is the SLP
closed form** `bellmanLipConstant β_S δ g_U` (Lipschitz constant and
minimum slope alike, so its members are exactly affine with that slope),
read off `U_S` along the certified corner.

The radius is the one magnitude here that is *not* forced. The smallest
invariant radius is the closed form
`bellmanNormBound β_S (sup-norm of the corner stage payoff) = 11`
(`eeCarrierS_closedForm_radius`); the carrier deliberately carries the
larger `12`, and that slack of `1` is exactly the `ε_S = 1` of
`eeCert_epsilon_isolation` (any equilibrium within sup-norm distance `1`
of the certified Sender value, with the slope pins, *is* it). Shrinking
the radius to the closed-form minimum would shrink that ε, so the slack
is load-bearing and is kept explicit rather than removed. -/
def eeCarrierS : Set Val :=
  valLipGainBall 12
    (StokeyLucas.bellmanLipConstant eeCertParams.β_S (1 - eeCertParams.δ) eeStageSlopeS)
    (StokeyLucas.bellmanLipConstant eeCertParams.β_S (1 - eeCertParams.δ) eeStageSlopeS)
    0

/-- Target carrier: the same construction on the Target side. Closed-form
slope; smallest invariant radius `3/(1 − 9/10) = 30`
(`eeCarrierT_closedForm_radius`), with the carrier carrying `80` so that
`eeCert_epsilon_isolation` can state its `ε_T = 69`. -/
def eeCarrierT : Set Val :=
  valLipGainBall 80
    (StokeyLucas.bellmanLipConstant eeCertParams.β_T (1 - eeCertParams.δ) eeStageSlopeT)
    (StokeyLucas.bellmanLipConstant eeCertParams.β_T (1 - eeCertParams.δ) eeStageSlopeT)
    0

/-- The Sender carrier's slope is forced: `4/(1 − 1/4) = 16/3`. -/
theorem eeCarrierS_eq : eeCarrierS = valLipGainBall 12 (16/3) (16/3) 0 := by
  simp only [eeCarrierS, StokeyLucas.bellmanLipConstant_def,
    eeCertParams_β_S, eeCertParams_δ, eeStageSlopeS_eq]
  norm_num

/-- The Target carrier's slope is forced: `(41/10)/(1 − 9/20) = 82/11`. -/
theorem eeCarrierT_eq : eeCarrierT = valLipGainBall 80 (82/11) (82/11) 0 := by
  simp only [eeCarrierT, StokeyLucas.bellmanLipConstant_def,
    eeCertParams_β_T, eeCertParams_δ, eeStageSlopeT_eq]
  norm_num

/-- **The smallest invariant Sender radius is `11`, and the carrier's
`12` dominates it.** The residual slack, exhibited rather than hidden:
`bellmanNormBound β_S M_U = (11/2)/(1 − 1/2) = 11 ≤ 12`. -/
theorem eeCarrierS_closedForm_radius :
    StokeyLucas.bellmanNormBound eeCertParams.β_S eeStageNormS = 11
      ∧ StokeyLucas.bellmanNormBound eeCertParams.β_S eeStageNormS ≤ 12 := by
  constructor <;>
    simp only [StokeyLucas.bellmanNormBound_def, eeCertParams_β_S,
      eeStageNormS_eq] <;> norm_num

/-- **The smallest invariant Target radius is `30`, and the carrier's
`80` dominates it**: `bellmanNormBound β_T M_U = 3/(1 − 9/10) = 30 ≤ 80`. -/
theorem eeCarrierT_closedForm_radius :
    StokeyLucas.bellmanNormBound eeCertParams.β_T eeStageNormT = 30
      ∧ StokeyLucas.bellmanNormBound eeCertParams.β_T eeStageNormT ≤ 80 := by
  constructor <;>
    simp only [StokeyLucas.bellmanNormBound_def, eeCertParams_β_T,
      eeStageNormT_eq] <;> norm_num

/-- Carrier membership in numeric form, for downstream consumers that
need the evaluated slope. -/
theorem mem_eeCarrierS_num {V : Val} (h : V ∈ eeCarrierS) :
    V ∈ valLipGainBall 12 (16/3) (16/3) 0 := eeCarrierS_eq ▸ h

/-- Carrier membership in numeric form (Target side). -/
theorem mem_eeCarrierT_num {V : Val} (h : V ∈ eeCarrierT) :
    V ∈ valLipGainBall 80 (82/11) (82/11) 0 := eeCarrierT_eq ▸ h

theorem eeCarrierS_nonempty : eeCarrierS.Nonempty := by
  rw [eeCarrierS_eq]
  exact ⟨affineBCF (16/3), affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

theorem eeCarrierT_nonempty : eeCarrierT.Nonempty := by
  rw [eeCarrierT_eq]
  exact ⟨affineBCF (82/11), affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

/-! ## 3. Affine extraction at general slope -/

/-- **Affine extraction (general slope).** Every member of the slope-`c`
gain ball (`Lipschitz c ∧ min-slope c`) satisfies
`V(clip z₂) − V(clip z₁) = c·(z₂ − z₁)` for `z₁, z₂ ∈ [0,1]` — i.e. it is
affine with slope exactly `c` on the state space. Generalizes
`substV_S_clip_diff` (the slope-1 case). -/
theorem gainBall_clip_diff {c M : ℝ} (hc : 0 ≤ c) {V : Val}
    (hV : V ∈ valLipGainBall M c c 0)
    {z₁ z₂ : ℝ} (h1 : z₁ ∈ Set.Icc (0:ℝ) 1) (h2 : z₂ ∈ Set.Icc (0:ℝ) 1) :
    V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) = c * (z₂ - z₁) :=
  AbstractGame.Params.valLipGainBall_clip_diff hc hV h1 h2

/-! ## 4. The dynamic Sender response is pinned at the corner `σ_dyn ≡ 1`

On the slope-`16/3` carrier the Sender dynamic objective has `s`-chord
slope `≥ 2/15 > 0` at every physical state (`−(s₁+s₂)/2 + 2 − (11/5)a + x
+ 4/3 ≥ 2/15`): the forward-looking Sender is implacable. -/

/-- The Sender dynamic objective is strictly increasing in the sanction on
`[0,1]`, at every physical state and feasible compliance. -/
theorem eeCert_senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => eeCertParams.U_S x a s
        + eeCertParams.β_S * V_S (Sanctions.clipS' (eeCertParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : (x + s₁)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hx.1], by nlinarith [hs₁.2, hx.2]⟩
  have hmem₂ : (x + s₂)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hs₂.1, hx.1], by nlinarith [hs₂.2, hx.2]⟩
  have hdiff : V_S (Sanctions.clipS' ((x + s₂)/2))
      - V_S (Sanctions.clipS' ((x + s₁)/2))
      = (16/3) * ((x + s₂)/2 - (x + s₁)/2) :=
    gainBall_clip_diff (by norm_num) (mem_eeCarrierS_num hV_S) hmem₁ hmem₂
  simp only [eeCertParams_U_S, eecU_S, eeCertParams_β_S, eeCertParams_F]
  have hcoef : (0:ℝ) < 4/3 + 2 - 11/5 * a + x - (s₁ + s₂)/2 := by
    nlinarith [ha.2, hx.1, hs₁.2, hs₂.2]
  have hprod := mul_pos (show (0:ℝ) < s₂ - s₁ by linarith) hcoef
  nlinarith [hdiff, hprod]

/-- **`σ_dyn` pinned at the corner `1`** for every carrier `V_S`, at every
physical state `x ∈ [0,1]` and feasible compliance `a ∈ [0,1]`. -/
theorem eeCert_σ_dyn_eq_one {V_S : Val} (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    eeCertParams.σ_dyn V_S x a = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn
    (eeCert_senderObj_strictMonoOn hV_S hx ha)

/-- **`σ_dyn_top` pinned at the corner `1`** for every carrier `V_S`:
the *upper-selector* Sender response (sup of the dynamic argmax set,
the selector the top equilibrium's realized rule uses) coincides with
the unique argmax `1`. Same strict-monotonicity route as
`eeCert_σ_dyn_eq_one`, entered through
`σ_dyn_top_mem_dynamicArgmaxSet`. -/
theorem eeCert_σ_dyn_top_eq_one {V_S : Val} (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    eeCertParams.σ_dyn_top V_S x a = 1 :=
  WitnessKit.σ_dyn_top_eq_one_of_strictMonoOn
    (eeCert_senderObj_strictMonoOn hV_S hx ha)

/-! ## 5. State-local uniqueness (Sender + Target) -/

/-- **State-local `DynamicArgmaxUnique` on the Sender carrier.** On the
physical state space the Sender objective is a strictly concave parabola
(the clip is inactive, the carrier `V_S` is affine). -/
theorem eeCert_DAU_on_carrier {V_S : Val} (hV_S : V_S ∈ eeCarrierS) :
    eeCertParams.DynamicArgmaxUnique V_S := by
  apply eeCertParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have hQ : ∀ s ∈ Sanctions.I,
      eeCertParams.U_S x a s
          + eeCertParams.β_S * V_S (Sanctions.clipS' (eeCertParams.F x s))
        = -(1/2) * s ^ 2 + (2 - 11/5 * a + x + 4/3) * s
          + (a + 3 * x + 4/3 * x + 1/2 * c₀) := by
    intro s hs
    have hmem : (x + s)/2 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by nlinarith [hs.1, hx.1], by nlinarith [hs.2, hx.2]⟩
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hdiff := gainBall_clip_diff (show (0:ℝ) ≤ 16/3 by norm_num)
      (mem_eeCarrierS_num hV_S) h0 hmem
    simp only [eeCertParams_U_S, eecU_S, eeCertParams_β_S, eeCertParams_F]
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

/-- **Joint Target integrand in closed form at physical states.** With
`σ_dyn ≡ 1`: `−(1/10)a + (41/10)x − 3 + (9/10)·V_T(clip((x+1)/2))` —
strictly decreasing in compliance `a` (the defiance corner). -/
theorem eeCert_joint_T_integrand_eq (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    eeCertParams.joint_T_integrand V_T V_S x a
      = -(1/10) * a + 41/10 * x - 3
        + 9/10 * V_T (Sanctions.clipS' ((x + 1)/2)) := by
  have hσ := eeCert_σ_dyn_eq_one hV_S hx ha
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [show eeCertParams.F x 1 = (x + 1)/2 from eeCertParams_F x 1]
  simp only [eeCertParams_U_T, eecU_T, eeCertParams_β_T]
  ring

/-- **State-local `TargetArgmaxUnique` on the carriers**: the joint
integrand is strictly decreasing in `a`, so two maximizers that dominate
each other must coincide. -/
theorem eeCert_TAU_on_carriers (V_T V_S : Val) (hV_S : V_S ∈ eeCarrierS) :
    eeCertParams.TargetArgmaxUnique V_T V_S :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn fun x hx a₁ ha₁ a₂ ha₂ hlt => by
    simp only [eeCert_joint_T_integrand_eq V_T hV_S hx ha₁,
      eeCert_joint_T_integrand_eq V_T hV_S hx ha₂]
    linarith

/-- **Zero (full defiance) is the Target argmax** at every physical state. -/
theorem eeCert_zero_isMaxOn_joint (V_T : Val) {V_S : Val}
    (hV_S : V_S ∈ eeCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn (fun a => eeCertParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [eeCert_joint_T_integrand_eq V_T hV_S hx ha,
      eeCert_joint_T_integrand_eq V_T hV_S hx
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  linarith [ha.1]

/-! ## 6. The asymmetric value class -/

/-- **The `ValueClass2` at the witness**: slope-pinned affine gain-ball
carriers with state-local Sender/Target argmax uniqueness. -/
def eeCertClass : eeCertParams.ValueClass2 where
  carrier_T := eeCarrierT
  carrier_S := eeCarrierS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := valLipGainBall_isClosed _ _ _ _
  nonempty_T := eeCarrierT_nonempty
  nonempty_S := eeCarrierS_nonempty
  sender_unique_on := fun _ hV_S => (eeCert_DAU_on_carrier hV_S).toOnI
  target_unique_on := fun V_T _ V_S hV_S => eeCert_TAU_on_carriers V_T V_S hV_S

/-- **The derived leader policy is the defiance corner: `α_on ≡ 0`.**
The forward-looking Target's Bellman argmax is `0` at every state (the
implacable Sender's sanctions are maxed regardless, so compliance buys
nothing and costs `1/10` per unit). Rule 1: this is the *derived* argmax
of the joint dynamic objective, pinned by state-local uniqueness. -/
theorem eeCert_α_on_eq_zero (V_T : eeCertClass.CarrierT)
    (V_S : eeCertClass.CarrierS) :
    eeCertClass.α_on V_T V_S = fun _ => (0:ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    eeCert_zero_isMaxOn_joint V_T.val V_S.property y.property

/-! ## 7. Bellman images in closed form

With `σ_dyn ≡ 1` and `α_on ≡ 0`, both joint Bellman operators evaluate in
closed form — the sSup collapses at the respective corner. All invariance
and row-contraction facts follow by affine arithmetic. -/

/-- **Target Bellman image in closed form**: the sSup over compliance
collapses at the defiance corner `a = 0`. -/
theorem eeCert_jointTarget_image (V_T : eeCertClass.CarrierT)
    (V_S : eeCertClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    eeCertParams.jointTarget_BCF_on_S V_T.val V_S.val
      (eeCertClass.sender_unique_on V_S.val V_S.property) y
      = 41/10 * y.val - 3
        + 9/10 * V_T.val (Sanctions.clipS' ((y.val + 1)/2)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (eeCertClass.sender_unique_on V_S.val V_S.property) y
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)
        (eeCert_zero_isMaxOn_joint V_T.val V_S.property y.property),
      eeCert_joint_T_integrand_eq V_T.val V_S.property y.property
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  ring

/-- **Sender Bellman image in closed form** at the defiance policy
`α ≡ 0`: the sSup over sanctions collapses at the corner `s = 1`. -/
theorem eeCert_bellmanS_image {W : Val} (hW : W ∈ eeCarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    eeCertParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3/2 + 4 * y.val
        + 1/2 * W (Sanctions.clipS' ((y.val + 1)/2)) := by
  have h1I : (1:ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmono := eeCert_senderObj_strictMonoOn hW y.property
    (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)
  have hmax : IsMaxOn
      (fun s => eeCertParams.U_S y.val 0 s
        + eeCertParams.β_S * W (Sanctions.clipS' (eeCertParams.F y.val s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1I hlt)
  rw [WitnessKit.bellmanS_image_of_isMaxOn (p := eeCertParams)
      continuous_const W y h1I hmax]
  rw [show eeCertParams.F y.val 1 = (y.val + 1)/2 from eeCertParams_F _ _]
  simp only [eeCertParams_U_S, eecU_S, eeCertParams_β_S]
  ring

/-! ## 8. Carrier invariance -/

/-- **Heterogeneous carrier invariance**, now discharged by the general
two-sided-band lemma `mem_valLipGainBall_bellman_chord` rather than by
hand-checked numerals. The transition enters only through
`CornerStateChord F glo ghi`, here at the degenerate band
`glo = ghi = 1 − δ = 1/2`; nothing pins the Bellman image to an exact
affine successor. Both Bellman images are corner-pinned affine, so
each re-enters *the same* ball: the image slope is `g_U + β·K·δ`, which
is `K` exactly because `K` is the SLP closed form, and the image sup-norm
is at most `M_U + β·M`, which is `M` exactly because `M` is the radius
closed form. Nothing here is a chosen magnitude — the carrier is the
unique ball the operator preserves. -/
theorem eeCertClass_IsInvariant : eeCertClass.IsInvariant := by
  intro V_T V_S
  constructor
  · -- Target image ∈ eeCarrierT.
    show eeCertParams.jointTarget_BCF_on_S V_T.val V_S.val
        (eeCertClass.sender_unique_on V_S.val V_S.property) ∈ eeCarrierT
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := eeCertParams.β_T)
      (glo := 1 - eeCertParams.δ) (ghi := 1 - eeCertParams.δ)
      (c₀ := eeStageT 0) (L_U := eeStageSlopeT) (g_U := eeStageSlopeT)
      (M_U := eeStageNormT) (stage := fun y => eeStageSlopeT * y)
      (F := eeCertParams.F)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      ?_ ?_ ?_
      (fun y hy => eeCertParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩) ?_
      eeCarrierT_closedForm_radius.2 le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_T.property ?_
    · intro z hz
      simp only [eeStageT_eq, eeStageSlopeT_eq, eeStageNormT_eq]
      rw [abs_le]
      constructor <;> nlinarith [hz.1, hz.2]
    · intro y₁ _ y₂ _
      rw [show eeStageSlopeT * y₂ - eeStageSlopeT * y₁
          = eeStageSlopeT * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ eeStageSlopeT)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y₁ y₂ _ _ hle
      simp only [eeCertParams_F, eeCertParams_δ]
      constructor <;> linarith
    · intro y
      rw [eeCert_jointTarget_image V_T V_S y,
        show eeCertParams.F y.val 1 = (y.val + 1)/2 from eeCertParams_F _ _]
      simp only [eeStageT_eq, eeStageSlopeT_eq, eeCertParams_β_T]
      ring
  · -- Sender image ∈ eeCarrierS.
    show eeCertParams.bellmanS_BCF (eeCertClass.α_on V_T V_S)
        (eeCertClass.α_on_continuous V_T V_S) V_S.val ∈ eeCarrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (eeCert_α_on_eq_zero V_T V_S)
        (eeCertClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := eeCertParams.β_S)
      (glo := 1 - eeCertParams.δ) (ghi := 1 - eeCertParams.δ)
      (c₀ := eeStageS 0) (L_U := eeStageSlopeS) (g_U := eeStageSlopeS)
      (M_U := eeStageNormS) (stage := fun y => eeStageSlopeS * y)
      (F := eeCertParams.F)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      ?_ ?_ ?_
      (fun y hy => eeCertParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩) ?_
      eeCarrierS_closedForm_radius.2 le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_S.property ?_
    · intro z hz
      simp only [eeStageS_eq, eeStageSlopeS_eq, eeStageNormS_eq]
      rw [abs_le]
      constructor <;> nlinarith [hz.1, hz.2]
    · intro y₁ _ y₂ _
      rw [show eeStageSlopeS * y₂ - eeStageSlopeS * y₁
          = eeStageSlopeS * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ eeStageSlopeS)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y₁ y₂ _ _ hle
      simp only [eeCertParams_F, eeCertParams_δ]
      constructor <;> linarith
    · intro y
      rw [eeCert_bellmanS_image V_S.property y,
        show eeCertParams.F y.val 1 = (y.val + 1)/2 from eeCertParams_F _ _]
      simp only [eeStageS_eq, eeStageSlopeS_eq, eeCertParams_β_S]
      ring

/-! ## 9. Schur row bounds (`L_TS = L_ST = 0`, decoupled) -/

/-- **Target-row bound**: `β_T = 9/10`, cross coefficient `L_TS = 0` (the
Target image is `V_S`-independent, since `σ_dyn ≡ 1` on the carrier). -/
theorem eeCertClass_hT_T_op
    (h_inv : eeCertClass.IsInvariant)
    (V V' : eeCertClass.CarrierT) (W W' : eeCertClass.CarrierS) :
    dist (eeCertClass.jointTargetOp_sub h_inv (V, W))
          (eeCertClass.jointTargetOp_sub h_inv (V', W'))
      ≤ (9/10 : ℝ) * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun z => 41/10 * z - 3) (φ := fun z => (z + 1)/2)
    (fun V W y => eeCert_jointTarget_image V W y) V V' W W'

/-- **Sender-row bound**: `β_S = 1/2`, cross coefficient `L_ST = 0` (the
Sender operator is `V_T`-independent because the derived leader policy is
the constant `α_on ≡ 0` for every carrier pair). -/
theorem eeCertClass_hT_S_op
    (h_inv : eeCertClass.IsInvariant)
    (V V' : eeCertClass.CarrierT) (W W' : eeCertClass.CarrierS) :
    dist (eeCertClass.jointSenderOp_sub h_inv (V, W))
          (eeCertClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    eeCert_α_on_eq_zero V V' W W'

/-! ## 10. The myopic comparator

The myopic (β = 0) Target best-responds to the *static* placable Sender:
`M.α(x) = min(1, (5x+10)/11)`. At pre-basin states it complies exactly
enough to zero out sanctions (`σ = 0`); on `x ≥ 1/5` it corners at full
compliance and buys sanctions down to the interior `σ_myo(x) = x − 1/5`.
The myopic Target objective in `a` is piecewise: decreasing while the
Sender is clipped at `σ = 1`, steeply increasing on the placation region
(slope `≈ +6` from the `−(11/5)·a·s` term against the sanction pain
`ℓ = 3`), decreasing again once `σ = 0`. -/

/-- **The myopic feedback equilibrium at the witness.** -/
def eeCertMyopic : eeCertParams.MyopicFeedbackEquilibrium where
  α := fun x => min 1 ((5 * x + 10)/11)
  α_mem := fun x hx =>
    ⟨le_min (by norm_num) (by linarith [hx.1]), min_le_left _ _⟩
  α_opt := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [isMaxOn_iff]
    intro a ha
    obtain ⟨ha0, ha1⟩ := ha
    show eecU_T x a (eecσ x a)
        ≤ eecU_T x (min 1 ((5 * x + 10)/11))
            (eecσ x (min 1 ((5 * x + 10)/11)))
    rcases le_total (1/5 : ℝ) x with hx5 | hx5
    · -- `x ≥ 1/5`: myopic corner `a = 1`, interior sanction `x − 1/5`.
      have hα : min 1 ((5 * x + 10)/11) = 1 := min_eq_left (by linarith)
      have hσ1 : eecσ x 1 = x - 1/5 := by
        unfold eecσ
        rw [show x + 2 - 11/5 * 1 = x - 1/5 by ring,
            min_eq_right (by linarith : x - 1/5 ≤ 1),
            max_eq_right (by linarith : (0:ℝ) ≤ x - 1/5)]
      rw [hα, hσ1]
      rcases le_total 1 (x + 2 - 11/5 * a) with ht1 | ht1
      · -- Sender clipped at `σ = 1`.
        have hσa : eecσ x a = 1 := by
          unfold eecσ
          rw [min_eq_left ht1, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        rw [hσa]
        simp only [eecU_T]
        nlinarith [ha0, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x)
          (by linarith : (0:ℝ) ≤ 146/5 - x)]
      · -- interior Sender response (`t ≥ 0` since `x ≥ 1/5`, `a ≤ 1`).
        have ht0 : (0:ℝ) ≤ x + 2 - 11/5 * a := by linarith
        have hσa : eecσ x a = x + 2 - 11/5 * a := by
          unfold eecσ
          rw [min_eq_right (by linarith : x + 2 - 11/5 * a ≤ 1),
              max_eq_right ht0]
        rw [hσa]
        simp only [eecU_T]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a)
          (by linarith : (0:ℝ) ≤ 319/5 - 11/5 * a - 6/5 * x)]
    · -- `x < 1/5`: interior myopic compliance zeroes the sanction.
      have hα : min 1 ((5 * x + 10)/11) = (5 * x + 10)/11 :=
        min_eq_right (by linarith)
      have hσm : eecσ x ((5 * x + 10)/11) = 0 := by
        unfold eecσ
        rw [show x + 2 - 11/5 * ((5 * x + 10)/11) = 0 by ring,
            min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]
      rw [hα, hσm]
      rcases le_total 1 (x + 2 - 11/5 * a) with ht1 | ht1
      · have hσa : eecσ x a = 1 := by
          unfold eecσ
          rw [min_eq_left ht1, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        rw [hσa]
        simp only [eecU_T]
        nlinarith [ha0, hx1]
      · rcases le_total 0 (x + 2 - 11/5 * a) with ht0 | ht0
        · have hσa : eecσ x a = x + 2 - 11/5 * a := by
            unfold eecσ
            rw [min_eq_right (by linarith : x + 2 - 11/5 * a ≤ 1),
                max_eq_right ht0]
          rw [hσa]
          simp only [eecU_T]
          have h_gap : (0:ℝ) ≤ (5 * x + 10)/11 - a := by linarith
          have h_pos : (0:ℝ) ≤ 64 - 11/5 * x - 11/5 * a := by linarith
          nlinarith [mul_nonneg h_gap h_pos]
        · have hσa : eecσ x a = 0 := by
            unfold eecσ
            rw [min_eq_right (by linarith : x + 2 - 11/5 * a ≤ 1),
                max_eq_left ht0]
          rw [hσa]
          simp only [eecU_T]
          nlinarith [ht0]

/-- The myopic Target's optimal compliance is strictly positive at every
physical state. -/
theorem eeCert_myopic_policy_pos {x : ℝ} (hx : x ∈ Sanctions.S) :
    0 < eeCertMyopic.α x := by
  change 0 < min 1 ((5 * x + 10) / 11)
  rw [lt_min_iff]
  constructor <;> nlinarith [hx.1]

/-- The sanction induced by the myopic equilibrium is strictly below the
full-sanction corner at every physical state. -/
theorem eeCert_myopic_rule_lt_one {x : ℝ} (hx : x ∈ Sanctions.S) :
    eeCertParams.myopicEquilibriumRule eeCertMyopic x < 1 := by
  change eecσ x (min 1 ((5 * x + 10) / 11)) < 1
  rcases le_total (1 / 5 : ℝ) x with hx5 | hx5
  · have ha : min 1 ((5 * x + 10) / 11) = 1 :=
      min_eq_left (by linarith)
    rw [ha]
    unfold eecσ
    rw [show x + 2 - 11 / 5 * 1 = x - 1 / 5 by ring,
      min_eq_right (by linarith [hx.2] : x - 1 / 5 ≤ 1),
      max_eq_right (by linarith : (0 : ℝ) ≤ x - 1 / 5)]
    linarith [hx.2]
  · have ha : min 1 ((5 * x + 10) / 11) = (5 * x + 10) / 11 :=
      min_eq_right (by linarith)
    rw [ha]
    unfold eecσ
    rw [show x + 2 - 11 / 5 * ((5 * x + 10) / 11) = 0 by ring]
    norm_num

/-- **Myopic ceiling on the basin**: the myopic realized sanction stays
below `max(x, s̄)` — with slack `1/5` on `x ≥ 1/5` (`σ_myo = x − 1/5`)
and trivially at pre-basin states (`σ_myo = 0`). -/
theorem eeCert_hMyoCeiling :
    ∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
      eeCertParams.σ x (eeCertMyopic.α x) ≤ max x (1/2 : ℝ) := by
  intro x hx
  show eecσ x (min 1 ((5 * x + 10)/11)) ≤ max x (1/2 : ℝ)
  have hx1 : x ≤ 1 := hx.2
  rcases le_total (1/5 : ℝ) x with hx5 | hx5
  · have hα : min 1 ((5 * x + 10)/11) = 1 := min_eq_left (by linarith)
    rw [hα]
    have hσ1 : eecσ x 1 = x - 1/5 := by
      unfold eecσ
      rw [show x + 2 - 11/5 * 1 = x - 1/5 by ring,
          min_eq_right (by linarith : x - 1/5 ≤ 1),
          max_eq_right (by linarith : (0:ℝ) ≤ x - 1/5)]
    rw [hσ1]
    exact le_trans (by linarith) (le_max_left x (1/2 : ℝ))
  · have hα : min 1 ((5 * x + 10)/11) = (5 * x + 10)/11 :=
      min_eq_right (by linarith)
    rw [hα]
    have hσm : eecσ x ((5 * x + 10)/11) = 0 := by
      unfold eecσ
      rw [show x + 2 - 11/5 * ((5 * x + 10)/11) = 0 by ring,
          min_eq_right (by norm_num : (0:ℝ) ≤ 1), max_self]
    rw [hσm]
    exact le_trans (by norm_num) (le_max_right x (1/2 : ℝ))

/-- **Rule-11 counterexample: myopic basin preservation (`hMyoBasin`)
FAILS at the witness.** The opt-in hypothesis of the pathwise
regime-comparison theorems
(`three_goals_local_regime_comparison(_uniform_starts)`) —
`∀ x ∈ [max xT xS, 1], σ(x, M.α x) ∈ [max xT xS, 1]` — is refuted at
the eeCert basin `xT = xS = 1/10`: at the basin edge `x = 1/10 < 1/5`
the myopic Target complies exactly enough to zero out sanctions
(`σ_myo = 0 ∉ [1/10, 1]`). Indeed `σ_myo(x) = clip(x − 1/5)` sits
uniformly `1/5` below the diagonal, so NO basin `[b, 1]` with `b > 0`
is preserved: the myopic regime *washes out* — the bistable economics
the witness exists to exhibit, not a defect. The pathwise dominance
content is salvaged without `hMyoBasin` by `eeCert_pathwise_dominance`
below, via the ceiling/floor route
`ruleSanctions_le_of_ceiling_and_path_floor`. -/
theorem eeCert_hMyoBasin_counterexample :
    ¬ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
        eeCertParams.myopicEquilibriumRule eeCertMyopic x
          ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1) := by
  simp only [max_self]
  intro h
  have h0 : eeCertParams.myopicEquilibriumRule eeCertMyopic (1/10) = 0 := by
    show eecσ (1/10) (min 1 ((5 * (1/10 : ℝ) + 10) / 11)) = 0
    unfold eecσ
    norm_num [min_def, max_def]
  have hc := (h (1/10) ⟨le_refl _, by norm_num⟩).1
  rw [h0] at hc
  norm_num at hc

/-- **Salvaged pathwise dominance at the witness (Goal 2′, no
`hMyoBasin`).** From every feasible start, the sanction sequence
realized by the fully myopic regime is pointwise dominated by the
sequence realized by the forward-looking top equilibrium — even though
the myopic path exits the basin (`eeCert_hMyoBasin_counterexample`).
Route: every myopic sanction is capped by `1` (stage feasibility),
while the forward-looking realized rule is pinned at the corner `1`
along its own path (`eeCert_σ_dyn_top_eq_one`); one transitivity step
through `ruleSanctions_le_of_ceiling_and_path_floor`. Shows the
pathwise comparison never depended on the myopic regime staying in the
basin — the ceiling/floor separation IS the bistability mechanism. -/
theorem eeCert_pathwise_dominance
    (E : eeCertParams.FeedbackStackelbergEquilibriumTop)
    (hV_S : E.V_S ∈ eeCarrierS)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n,
      eeCertParams.ruleSanctions
          (eeCertParams.myopicEquilibriumRule eeCertMyopic) x₀ n
        ≤ eeCertParams.ruleSanctions
            (eeCertParams.dynamicEquilibriumRule E) x₀ n := by
  refine eeCertParams.ruleSanctions_le_of_ceiling_and_path_floor
      (c := 1) ?_ ?_ hx₀ ?_
  · intro x _hx
    exact eecσ_mem x (eeCertMyopic.α x)
  · intro x _hx
    exact (eecσ_mem x (eeCertMyopic.α x)).2
  · intro n
    have hy_mem : eeCertParams.rulePath
        (eeCertParams.dynamicEquilibriumRule E) x₀ n ∈ Sanctions.I :=
      eeCertParams.rulePath_mem_I
        (fun x _hx => eeCertParams.dynamicTopRealizedRule_mem E.V_S E.α x)
        hx₀ n
    have hα_mem : E.α (eeCertParams.rulePath
        (eeCertParams.dynamicEquilibriumRule E) x₀ n) ∈ Sanctions.I :=
      E.α_mem _ hy_mem
    have h1 := eeCert_σ_dyn_top_eq_one hV_S hy_mem hα_mem
    exact h1.ge

/-! ## 11. Stage fields -/

/-- **Stage Target loss bound** at the derived (defiant) leader policy:
the loss rate `3 − x/10` is at most `cT = 299/100` on the basin. -/
theorem eeCert_h_stage_target_loss
    (V_T : eeCertClass.CarrierT) (V_S : eeCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerLossSlopeOn
        (fun s => eeCertParams.U_T x (eeCertClass.α_on V_T V_S x) s)
        (Set.Icc (max x (1/2 : ℝ)) 1) (299/100) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [eeCert_α_on_eq_zero V_T V_S, eeCertParams_U_T, eecU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 1/10 * x - 1/100 by linarith [hx.1])]

/-- **Stage Sender slope** at the derived leader policy: chord slope
`2 + x − (s₁+s₂)/2 ≥ 8/5` on `[0, max(x, s̄)]` for basin `x` (the key
inequality: `max(x, 1/2) ≤ x + 2/5` exactly at the basin bottom). -/
theorem eeCert_h_stage_sender
    (V_T : eeCertClass.CarrierT) (V_S : eeCertClass.CarrierS) :
    ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
      LowerSlopeOn
        (fun s => eeCertParams.U_S x (eeCertClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (1/2 : ℝ))) (8/5) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hmax : max x (1/2 : ℝ) ≤ x + 2/5 := by
    rcases max_cases x (1/2 : ℝ) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;>
      linarith [hx.1]
  simp only [eeCert_α_on_eq_zero V_T V_S, eeCertParams_U_S, eecU_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ 2 + x - (s₁ + s₂)/2 - 8/5 by
      linarith [hs₁.2, hs₂.2, hmax])]

/-- **Carrier `V_T` gain on the basin**: restriction of the gain-ball
minimum slope from `[0,1]` to `[1/10, 1]`. -/
theorem eeCert_hV_T_gain :
    ∀ V_T ∈ eeCertClass.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc (1/10 : ℝ) 1) (82/11) := by
  intro V_T hV_T y₁ y₂ h1 h2 hle
  exact (mem_eeCarrierT_num hV_T).2.2 y₁ y₂
    ⟨by linarith [h1.1], h1.2⟩ ⟨by linarith [h2.1], h2.2⟩ hle

/-- **Single crossing (trivial form)**: the Sender dynamic objective is
strictly increasing in the sanction at every basin state, so both
single-crossing consequents hold unconditionally. -/
theorem eeCert_hSC (V_T : eeCertClass.CarrierT) (V_S : eeCertClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max (1/10 : ℝ) (1/10)) 1)
      (fun s x => eeCertParams.senderDynObjective V_S.val x
        (eeCertClass.α_on V_T V_S x) s) :=
  WitnessKit.singleCrossingOn_of_strictMonoOn fun t ht s₁ hs₁ s₂ hs₂ hlt => by
    simp only [eeCert_α_on_eq_zero V_T V_S,
      AbstractGame.Params.senderDynObjective]
    exact eeCert_senderObj_strictMonoOn V_S.property
      ⟨le_trans (by norm_num) (le_trans (le_max_left _ _) ht.1), ht.2⟩
      (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I) hs₁ hs₂ hlt

/-! ## 12. THE CERTIFICATE -/

/-- **The first complete `StandardComplianceLocalCoreCertificate`
instance in the development.** Every field discharged unconditionally at
`eeCertParams`: the slope-pinned gain-ball value class with state-local
argmax uniqueness (`D`), Bellman invariance (`h_inv`), decoupled Schur
rows (`β_T = 9/10, β_S = 1/2, L_TS = L_ST = 0`), the high basin
`[1/10, 1]` with sanction floor `s̄ = 1/2`, the Sender stage margin
(`mS = 8/5 > 4/3 = β_S·K_S·δ`), carrier-local stage slopes,
single crossing, and the myopic comparator with its ceiling
(`σ_myo(x) = clip(x − 1/5) ≤ max(x, 1/2)`, slack `1/5`). The Target
loss-offset (`cT = 299/100 ≤ 369/110 = β_T·g_T·δ`) was a field until round
BJ1.4 (2026-10-07) deleted the Target stack from the certificate; its two
halves remain proved here (`eeCert_h_stage_target_loss`, `eeCert_hV_T_gain`). -/
noncomputable def eeCertCertificate :
    eeCertParams.StandardComplianceLocalCoreCertificate where
  D := eeCertClass
  h_inv := eeCertClass_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := eeCertClass_hT_T_op eeCertClass_IsInvariant
  hT_S_op := eeCertClass_hT_S_op eeCertClass_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 1/10
  xS := 1/10
  sbar := 1/2
  mS := 8/5
  KS := 16/3
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  d := eeCertParams.δ
  hF_chord := eeCertParams.affine_sender_chord_on rfl _ _
  hS_margin := by
    simp only [eeCertParams_β_S, eeCertParams_δ]
    norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := fun _ hV_S => (mem_eeCarrierS_num hV_S).2.1
  h_stage_sender_on := eeCert_h_stage_sender
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (eeCert_hSC V_T V_S)
  M := eeCertMyopic
  hMyoCeiling := eeCert_hMyoCeiling

/-- **Strict moving-policy equilibrium comparison.** There exists a
forward-looking feedback Stackelberg equilibrium in the certified carriers
whose optimal Target policy is strictly below the independently optimal
myopic policy at every state, whose realized sanction is strictly above the
myopic sanction at every state, and whose sanction path remains strictly
above the myopic path from every feasible common start. -/
theorem eeCert_cross_economy_moving_policy_strict :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT ∧ E.V_S ∈ eeCarrierS ∧
      (∀ x ∈ Sanctions.S,
        E.α x < eeCertMyopic.α x ∧
        eeCertParams.myopicEquilibriumRule eeCertMyopic x <
          eeCertParams.dynamicEquilibriumRule E x) ∧
      ∀ x₀ ∈ Sanctions.I, ∀ n,
        eeCertParams.ruleSanctions
            (eeCertParams.myopicEquilibriumRule eeCertMyopic) x₀ n <
          eeCertParams.ruleSanctions
            (eeCertParams.dynamicEquilibriumRule E) x₀ n := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    eeCertCertificate.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      eeCertCertificate.h_inv eeCertCertificate.hβ_T_nn
      eeCertCertificate.hβ_S_nn eeCertCertificate.hL_TS_nn
      eeCertCertificate.hL_ST_nn eeCertCertificate.hT_T_op
      eeCertCertificate.hT_S_op eeCertCertificate.hsuff_T
      eeCertCertificate.hsuff_S
  let V_T_sub : eeCertCertificate.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : eeCertCertificate.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = eeCertCertificate.D.α_on V_T_sub V_S_sub at hα_eq
  have hαzero : E.α = fun _ => (0 : ℝ) := by
    rw [hα_eq]
    exact eeCert_α_on_eq_zero V_T_sub V_S_sub
  refine ⟨E, hVT, hVS, ?_, ?_⟩
  · intro x hx
    constructor
    · rw [hαzero]
      exact eeCert_myopic_policy_pos hx
    · have hDyn : eeCertParams.dynamicEquilibriumRule E x = 1 :=
        eeCert_σ_dyn_top_eq_one hVS hx (E.α_mem x hx)
      rw [hDyn]
      exact eeCert_myopic_rule_lt_one hx
  · intro x₀ hx₀ n
    have hMmem : ∀ x ∈ Sanctions.I,
        eeCertParams.myopicEquilibriumRule eeCertMyopic x ∈ Sanctions.I :=
      fun x _ => eeCertParams.σ_mem x (eeCertMyopic.α x)
    have hDmem : ∀ x ∈ Sanctions.I,
        eeCertParams.dynamicEquilibriumRule E x ∈ Sanctions.I :=
      fun x _ => eeCertParams.dynamicTopRealizedRule_mem E.V_S E.α x
    have hxM := eeCertParams.rulePath_mem_I hMmem hx₀ n
    have hxD := eeCertParams.rulePath_mem_I hDmem hx₀ n
    change eeCertParams.myopicEquilibriumRule eeCertMyopic
        (eeCertParams.rulePath
          (eeCertParams.myopicEquilibriumRule eeCertMyopic) x₀ n) <
      eeCertParams.dynamicEquilibriumRule E
        (eeCertParams.rulePath
          (eeCertParams.dynamicEquilibriumRule E) x₀ n)
    have hM := eeCert_myopic_rule_lt_one hxM
    have hD :
        eeCertParams.dynamicEquilibriumRule E
          (eeCertParams.rulePath
            (eeCertParams.dynamicEquilibriumRule E) x₀ n) = 1 :=
      eeCert_σ_dyn_top_eq_one hVS hxD (E.α_mem _ hxD)
    rw [hD]
    exact hM

/-! ## 13. The unconditional three-goals corollary -/

/-- **Unconditional three-goals dominance at the witness** (Goal 2 of the
JET paper, exposed; Goals 1 and 3 are delivered by the same certificate
via `three_goals_local_uniform_starts`). The forward-looking equilibrium
exists on the carriers, and on the whole basin the myopic realized
sanction is dominated by the forward-looking realized sanction. Unlike
`eatonEngersParams_three_goals_conditional` (Rule-15 honest-conditional),
this is UNCONDITIONAL: the certificate is fully constructed above. -/
theorem eeCert_three_goals_dominance :
    ∃ E : eeCertParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ eeCarrierT ∧ E.V_S ∈ eeCarrierS
      ∧ (∀ x ∈ Set.Icc (max (1/10 : ℝ) (1/10)) 1,
           eeCertParams.σ x (eeCertMyopic.α x)
             ≤ eeCertParams.dynamicTopRealizedRule E.V_S E.α x) := by
  -- G3 re-route (2026-08-19): Goal 2 mentions no transition, so it is
  -- taken through the general-`F` chord route rather than the affine
  -- `three_goals_local_uniform_starts`. The statement is unchanged. Round
  -- BG (2026-10-06): the call goes to `goal2_dominance_generalF` itself;
  -- the affine wrapper it used to pass through read neither its `hF` nor
  -- its `0 ≤ g_T` binder and was deleted. The affine law enters only as the
  -- `d = δ` instance of the certificate's Sender chord field (its Target lower
  -- chord at `dlo` was deleted in round BJ1.4).
  obtain ⟨E, hVT, hVS, hG2⟩ :=
    eeCertCertificate.goal2_dominance_generalF (p := eeCertParams)
  exact ⟨E, hVT, hVS, hG2⟩

/-! ## 14. Within-carrier uniqueness (Schur route, 2026-07-23) -/

/-- **First Schur-certificate inhabitant.** The row-sum certificate
downgrades to the Schur form via `ofRowSum` (decoupled rows give
`L_TS·L_ST = 0 < (1/10)·(1/2)`), closing the previously-uninstantiated
`StandardComplianceLocalCoreCertificateSchur`. -/
def eeCertCertificateSchur :
    eeCertParams.StandardComplianceLocalCoreCertificateSchur :=
  StandardComplianceLocalCoreCertificateSchur.ofRowSum
    eeCertParams eeCertCertificate

/-- **Witness within-carrier uniqueness.** Any two top-selector feedback
Stackelberg equilibria of the eeCert economy whose value pairs lie in
the gain-ball carriers and whose policies coincide with the carrier
selector agree in both value functions and in the policy. Every
quantitative input of the headline uniqueness theorem
(`feedbackStackelbergTop_unique_in_carrier_schur`) — carrier invariance,
the decoupled row bounds `L_TS = L_ST = 0` with diagonals `9/10`, `1/2`,
and the Schur margin — is machine-discharged by `eeCertCertificate`;
only the carrier/selector memberships remain, and they define the
uniqueness class itself. This theorem makes no global
equilibrium-uniqueness claim; the economy's bistability concerns
state-path selection under a single equilibrium. -/
theorem eeCert_unique_in_carrier
    (E E' : eeCertParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ eeCarrierT) (hVS : E.V_S ∈ eeCarrierS)
    (hVT' : E'.V_T ∈ eeCarrierT) (hVS' : E'.V_S ∈ eeCarrierS)
    (hαE : E.α = eeCertClass.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = eeCertClass.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  eeCertCertificateSchur.unique_in_carrier (p := eeCertParams)
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Witness within-carrier uniqueness at eeCert, with no selector hypothesis
(round BH1.1, 2026-10-06).** Sibling of `eeCert_unique_in_carrier` without
`hαE`, `hαE'`: any two top-selector feedback Stackelberg equilibria of the
eeCert economy whose values lie in the gain-ball carriers share both value
functions, and their policies agree at every feasible state. Carrier membership
alone defines the uniqueness class; every quantitative input is discharged by
`eeCertCertificateSchur`. The economy runs the affine law (`δ = 1/2`); the
theorem it instantiates is general in `F`. No global uniqueness claim. -/
theorem eeCert_unique_in_carrier_of_mem
    (E E' : eeCertParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ eeCarrierT) (hVS : E.V_S ∈ eeCarrierS)
    (hVT' : E'.V_T ∈ eeCarrierT) (hVS' : E'.V_S ∈ eeCarrierS) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  eeCertCertificateSchur.unique_in_carrier_of_mem (p := eeCertParams)
    E E' hVT hVS hVT' hVS'

end -- noncomputable section

#print axioms eeCertCertificate
#print axioms eeCertCertificateSchur
#print axioms eeCert_unique_in_carrier
#print axioms eeCert_unique_in_carrier_of_mem
#print axioms eeCert_three_goals_dominance
#print axioms eeCert_hMyoBasin_counterexample
#print axioms eeCert_pathwise_dominance

end Examples

end Sanctions
