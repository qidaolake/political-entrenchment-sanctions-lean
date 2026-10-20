/-
Sanctions/Examples/DualBasinSelectionWitness.lean

**P5: the dual-basin selection witness — the FIRST single
economy carrying BOTH a certified high-basin lock-in AND a certified
low-basin wash-out at the SAME equilibrium (2026-07-11).**

Until this file, the high-basin persistence certificate
(`StandardComplianceLocalCoreCertificate`, Theorem 1) and the low-basin
wash-out headline (`standardCompliance_three_goals_local_low_basin`,
Theorem 4) had only been instantiated at *different* economies
(`eeCertParams` hardline vs `lbParams` dovish). Here ONE rational
parameter vector carries both: **initial-condition selection between
the two invariant directional basins is now a machine-checked theorem at a
single `Params`, not a narrative** (`dualParams_initial_condition_selects`).

## The economy (all exact rationals; verified spec `docs/archive/workflow-scratch/w1b_p5_spec.md`,
25/25 design + 53/53 adversarial exact-rational checks)

* `δ = 1/10`, `β_S = 1/2`, `β_T = 9/10`, affine transition
  `F(x,s) = (9x + s)/10`.
* `U_S(x,a,s) = a − s²/2 + s·(2x − 1/2 − 2a)` — rally cross-partial
  `∂²U_S/∂s∂x = +2`, placation `∂²U_S/∂s∂a = −2`, strict concavity
  `∂²U_S/∂s² = −1`.
* `U_T(x,a,s) = (19/10)x − (1/5)a − (9/10)s` — compliance costly,
  sanctions hurt at rate `9/10`, incumbent values hardline states.
* Static Sender selector `σ(x,a) = clip(2x − 1/2 − 2a)` (derived
  vertex argmax of the concave stage parabola — Rule 1).

## The two load-bearing exact identities

(i) `g_T = (19/10)/(1 − (9/10)(9/10)) = 10`: the Target Bellman image
of a slope-10 affine `V_T` is again exactly slope-10 affine (pinned
band `b ∈ [−19, 9]` invariant, `b ↦ (9/10)b`).

(ii) **The knife edge** `c_T = 9/10 = β_T·δ·g_T` EXACTLY: with `V_T`
slope-pinned at 10, the Target's joint dynamic objective is exactly
FLAT in the sanction — the leader integrand
`J(x,a) = 10x − (1/5)a + (9/10)·V_T(0-point)` is INDEPENDENT of the
Sender response, so `α ≡ 0` is the strict unique leader argmax at every
state for every carrier pair, the Target operator ignores `V_S`
(`L_TS = 0` exactly), and the `σ_dyn` 0→1 transition sweep between the
basins never contaminates the Target side. The high-basin loss-offset
margin (`c_T ≤ β_T·g_T·δ`, WEAK; a certificate field until round BJ1.4)
holds at equality; the
low-basin field `target_dislikes_high_sanctions` (`AntitoneOn`, WEAK)
holds with the identically-zero chord. Both weak field shapes admit the
knife edge — this is what makes a single dual-basin economy possible.

## Carriers (asymmetric `ValueClass2`)

* `dbCarrierT = valLipGainBall 19 10 10 0` — slope-pinned
  `{V = 10x + b : b ∈ [−19, 9]}`.
* `dbCarrierS = {‖V‖ ≤ 5/2, 4-Lipschitz, 40-semiconcave}` — the
  **semiconcavity clause** (`SemiconcaveOn V 40`: chord defect at most
  `20·t(1−t)·Δy²`, i.e. `V(u) − 20u²` concave) is the witness-level
  device that discharges state-local Sender argmax uniqueness for ALL
  real compliance tilts `a`: the Sender dynamic objective's
  `s`-curvature is `≤ −1 + (1/2)(1/10)²·40 = −4/5 < 0`. The Sender
  Bellman operator maps this ball into itself with margin: image
  Lipschitz `19/5 ≤ 4`, norm `9/4 ≤ 5/2`, semiconcavity `137/4 ≤ 40`
  (the interior-regime formula, obtained here by a convex-combination
  candidate argument plus one quadratic completion — no regime split).

## The two basins, both certified at the same equilibrium `E`

* HIGH `[19/20, 1]`, sanction floor `s̄ = 1/2`: full
  `StandardComplianceLocalCoreCertificate` (dominance gap over the
  myopic comparator `M.α = clip(x − 1/4)`, whose realized sanction is
  identically 0, is the full `1`).
* LOW `[0, 1/10]`, sanction ceiling `s̄* = 1/10`: dual one-sided
  thresholds `OneSidedSanctionLowBasinPreferenceThresholds` + top-rule
  monotonicity, discharged at the SAME `E` produced by the high
  certificate's Banach fixed point (only carrier membership of
  `(E.V_T, E.V_S)` and feasibility of `E.α` are used).

Basins disjoint (`1/10 < 19/20`, `dbBasins_disjoint`). Rule 3: NO new
assumptions — the semiconcave carrier is a definition (a witness-level
carrier SET like `valLipGainBall`), not a hypothesis. Rule 5: existence
certificate; the general machinery is consumed, not duplicated.
-/

import Sanctions.Examples.EECertWitness
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Certificates.StandardComplianceLowBasin
import Sanctions.Theory.LockIn.BasinAttraction
-- `affine_sender_chord_on`, which discharges this economy's `hF_chord` field.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.ComplianceTower
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The stage economy -/

/-- Sender stage payoff. `∂²U_S/∂s∂x = 2 > 0` (rally),
`∂²U_S/∂s∂a = −2 < 0` (compliance placates), `∂²U_S/∂s² = −1 < 0`. -/
def dbU_S (x a s : ℝ) : ℝ := a - 1/2 * s ^ 2 + s * (2 * x - 1/2 - 2 * a)

/-- Target stage payoff: compliance costly (`−a/5`), sanctions hurt at
the exact knife-edge rate `9/10`, incumbent values hardline states
(`(19/10)x`). -/
def dbU_T (x a s : ℝ) : ℝ := 19/10 * x - 1/5 * a - 9/10 * s

/-- Static Sender response: the clipped vertex of the concave parabola
`U_S(x,a,·)`, `σ(x,a) = clip(2x − 1/2 − 2a)`. -/
def dbσ (x a : ℝ) : ℝ := max 0 (min 1 (2 * x - 1/2 - 2 * a))

theorem dbσ_mem (x a : ℝ) : dbσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem dbσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => dbσ xa.1 xa.2) := by
  unfold dbσ
  fun_prop

/-- **Rule-1 coupling.** The clipped vertex maximizes `U_S(x,a,·)` on
`[0,1]`: `U_S(x,a,s) = C(x,a) − ½(s − t)²` with `t = 2x − 1/2 − 2a`. -/
theorem dbσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => dbU_S x a s) (Set.Icc (0 : ℝ) 1) (dbσ x a) :=
  WitnessKit.clipVertex_isMaxOn (by norm_num : (0 : ℝ) < 1/2)
    (C := a + 1/2 * (2 * x - 1/2 - 2 * a) ^ 2)
    (fun s => by simp only [dbU_S]; ring)

/-- **The dual-basin witness `Params`.** -/
def dualParams : AbstractGame.Params where
  δ := 1/10
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 9/10
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := dbU_T
  U_S := dbU_S
  σ := dbσ
  σ_mem := dbσ_mem
  σ_isMaxOn_U_S := dbσ_isMaxOn
  U_T_continuous := by unfold dbU_T; fun_prop
  U_S_continuous := by unfold dbU_S; fun_prop
  F := AbstractGame.affineF (1/10)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`dualParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/10)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance dualParams_staticSelectorContinuous :
    dualParams.StaticSelectorContinuous where
  σ_continuous := dbσ_continuous

@[simp] theorem dualParams_U_S : dualParams.U_S = dbU_S := rfl
@[simp] theorem dualParams_U_T : dualParams.U_T = dbU_T := rfl
@[simp] theorem dualParams_δ : dualParams.δ = 1/10 := rfl
@[simp] theorem dualParams_β_S : dualParams.β_S = 1/2 := rfl
@[simp] theorem dualParams_β_T : dualParams.β_T = 9/10 := rfl

/-- Transition closed form: `F(x,s) = (9x + s)/10`. -/
theorem dualParams_F (x s : ℝ) : dualParams.F x s = (9 * x + s) / 10 := by
  change AbstractGame.affineF (1/10) x s = (9 * x + s) / 10
  unfold AbstractGame.affineF
  ring

/-! ## 2. The semiconcave Sender carrier

The genuinely new carrier device of this witness. Chord-form
`c`-semiconcavity (`V(u) − (c/2)u²` concave): the chord defect of `V`
at any convex combination of states is bounded by
`(c/2)·t(1−t)·(y₁ − y₂)²`. Concave kinks are allowed; only *upward*
curvature is capped. This is a witness-level carrier SET definition
(like `valLipGainBall`), not an assumption. -/

/-- **Chord-form `c`-semiconcavity on the state space.** Equivalent to
"`V(u) − (c/2)·u²` is concave on `[0,1]`": for every pair of states and
every convex weight, the chord defect is at most
`(c/2)·t·(1−t)·(y₁−y₂)²`. -/
def SemiconcaveOn (V : Val) (c : ℝ) : Prop :=
  ∀ (y₁ y₂ m : ↥(Sanctions.S : Set ℝ)) (t : ℝ), 0 ≤ t → t ≤ 1 →
    m.val = t * y₁.val + (1 - t) * y₂.val →
    t * V y₁ + (1 - t) * V y₂ - V m
      ≤ c / 2 * (t * (1 - t) * (y₁.val - y₂.val) ^ 2)

/-- The `SemiconcaveOn · c` set is closed in BCF (intersection of
pointwise-closed evaluation half-spaces). -/
theorem semiconcaveOn_isClosed (c : ℝ) :
    IsClosed {V : Val | SemiconcaveOn V c} := by
  rw [show {V : Val | SemiconcaveOn V c}
        = ⋂ (y₁ : ↥(Sanctions.S : Set ℝ)) (y₂ : ↥(Sanctions.S : Set ℝ))
              (m : ↥(Sanctions.S : Set ℝ)) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
              (_ : m.val = t * y₁.val + (1 - t) * y₂.val),
            {V : Val | t * V y₁ + (1 - t) * V y₂ - V m
              ≤ c / 2 * (t * (1 - t) * (y₁.val - y₂.val) ^ 2)} from ?_]
  · apply isClosed_iInter; intro y₁
    apply isClosed_iInter; intro y₂
    apply isClosed_iInter; intro m
    apply isClosed_iInter; intro t
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro _
    have h₁ : Continuous (fun V : Val => V y₁) :=
      ContinuousEvalConst.continuous_eval_const y₁
    have h₂ : Continuous (fun V : Val => V y₂) :=
      ContinuousEvalConst.continuous_eval_const y₂
    have hm : Continuous (fun V : Val => V m) :=
      ContinuousEvalConst.continuous_eval_const m
    exact isClosed_le
      (((continuous_const.mul h₁).add (continuous_const.mul h₂)).sub hm)
      continuous_const
  · ext V
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h y₁ y₂ m t ht0 ht1 hm; exact h y₁ y₂ m t ht0 ht1 hm
    · intro h y₁ y₂ m t ht0 ht1 hm; exact h y₁ y₂ m t ht0 ht1 hm

/-- **The semiconcave Sender carrier**: norm ≤ 5/2, 4-Lipschitz,
40-semiconcave. -/
def dbCarrierS : Set Val :=
  {V : Val | ‖V‖ ≤ 5/2 ∧ ValueLipschitzWith V 4 ∧ SemiconcaveOn V 40}

/-- **The slope-pinned Target carrier**: `{V = 10x + b : b ∈ [−19, 9]}`
as the gain ball `valLipGainBall 19 10 10 0` (norm radius 19 encodes
the band: `|b| ≤ 19 ∧ |b + 10| ≤ 19 ⟺ b ∈ [−19, 9]`). -/
def dbCarrierT : Set Val := valLipGainBall 19 10 10 0

theorem dbCarrierS_isClosed : IsClosed dbCarrierS := by
  unfold dbCarrierS
  rw [show {V : Val | ‖V‖ ≤ 5/2 ∧ ValueLipschitzWith V 4 ∧ SemiconcaveOn V 40}
        = ({V : Val | ‖V‖ ≤ 5/2} ∩ {V : Val | ValueLipschitzWith V 4}) ∩
            {V : Val | SemiconcaveOn V 40} from ?_]
  · exact ((isClosed_le continuous_norm continuous_const).inter
            (valueLipschitz_isClosed 4)).inter (semiconcaveOn_isClosed 40)
  · ext V; simp [Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]

theorem dbCarrierT_isClosed : IsClosed dbCarrierT :=
  valLipGainBall_isClosed _ _ _ _

/-- The zero value function is in the semiconcave Sender carrier. -/
theorem dbCarrierS_nonempty : dbCarrierS.Nonempty := by
  refine ⟨0, ?_, ?_, ?_⟩
  · rw [norm_zero]; norm_num
  · intro y₁ y₂
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, sub_zero,
      abs_zero]
    exact mul_nonneg (by norm_num) dist_nonneg
  · intro y₁ y₂ m t ht0 ht1 _
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero,
      add_zero, sub_zero]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _))

theorem dbCarrierT_nonempty : dbCarrierT.Nonempty :=
  ⟨affineBCF 10, affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

/-- **Lipschitz chord through the clip**: every Sender-carrier member
moves at most `4·|z₂ − z₁|` between clipped states. -/
theorem dbS_clip_chord {W : Val} (hW : W ∈ dbCarrierS) (z₁ z₂ : ℝ) :
    |W (Sanctions.clipS' z₂) - W (Sanctions.clipS' z₁)| ≤ 4 * |z₂ - z₁| := by
  have h := hW.2.1 (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
  have hd : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) ≤ |z₁ - z₂| :=
    Sanctions.clipS'_lipschitz_dist z₁ z₂
  calc |W (Sanctions.clipS' z₂) - W (Sanctions.clipS' z₁)|
      ≤ 4 * dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) := h
    _ ≤ 4 * |z₁ - z₂| := by linarith
    _ = 4 * |z₂ - z₁| := by rw [abs_sub_comm]

/-! ## 3. The Sender dynamic objective on the two basins

On the high basin `[19/20, 1]` (at the derived leader policy `a = 0`)
the objective is strictly increasing in `s` on all of `[0,1]` — worst
chord slope `2x − 3/2 − 1/5 ≥ 1/5 > 0` under maximal carrier drag. On
the low basin `[0, 1/10]` it is strictly decreasing for EVERY
feasible compliance `a ≥ 0` — worst chord slope `2x − 3/10 ≤ −1/10 < 0`.
The 4-Lipschitz carrier bound caps the continuation drag at `±1/5`. -/

/-- **High-basin strict increase** of the Sender dynamic objective in
the sanction, at the defiance policy `a = 0`, for every carrier member. -/
theorem dbCert_senderObj_strictMonoOn_high {W : Val} (hW : W ∈ dbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (19 / 20 : ℝ) 1) :
    StrictMonoOn
      (fun s => dualParams.U_S x 0 s
        + dualParams.β_S * W (Sanctions.clipS' (dualParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hWd := dbS_clip_chord hW (dualParams.F x s₁) (dualParams.F x s₂)
  have hF : dualParams.F x s₂ - dualParams.F x s₁ = (s₂ - s₁) / 10 := by
    rw [dualParams_F, dualParams_F]; ring
  have habs : |W (Sanctions.clipS' (dualParams.F x s₂))
      - W (Sanctions.clipS' (dualParams.F x s₁))| ≤ 4 * ((s₂ - s₁) / 10) := by
    calc |W (Sanctions.clipS' (dualParams.F x s₂))
        - W (Sanctions.clipS' (dualParams.F x s₁))|
        ≤ 4 * |dualParams.F x s₂ - dualParams.F x s₁| := hWd
      _ = 4 * ((s₂ - s₁) / 10) := by
          rw [hF, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s₂ - s₁) / 10)]
  have hlow := (abs_le.mp habs).1
  have hcoef : (0 : ℝ) < 2 * x - 1/2 - (s₁ + s₂) / 2 - 1/5 := by
    nlinarith [hx.1, hs₁.2, hs₂.2]
  have hprod := mul_pos (sub_pos.mpr hlt) hcoef
  simp only [dualParams_U_S, dbU_S, dualParams_β_S]
  nlinarith [hlow, hprod]

/-- **Low-basin strict decrease** of the Sender dynamic objective in
the sanction, for EVERY feasible compliance level `a ≥ 0` and every
carrier member — this pins the wash-out corner `σ_dyn_top ≡ 0` at the
same equilibrium the high certificate produces. -/
theorem dbCert_senderObj_strictAntiOn_low {W : Val} (hW : W ∈ dbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 10)) {a : ℝ} (ha : 0 ≤ a) :
    StrictAntiOn
      (fun s => dualParams.U_S x a s
        + dualParams.β_S * W (Sanctions.clipS' (dualParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hWd := dbS_clip_chord hW (dualParams.F x s₁) (dualParams.F x s₂)
  have hF : dualParams.F x s₂ - dualParams.F x s₁ = (s₂ - s₁) / 10 := by
    rw [dualParams_F, dualParams_F]; ring
  have habs : |W (Sanctions.clipS' (dualParams.F x s₂))
      - W (Sanctions.clipS' (dualParams.F x s₁))| ≤ 4 * ((s₂ - s₁) / 10) := by
    calc |W (Sanctions.clipS' (dualParams.F x s₂))
        - W (Sanctions.clipS' (dualParams.F x s₁))|
        ≤ 4 * |dualParams.F x s₂ - dualParams.F x s₁| := hWd
      _ = 4 * ((s₂ - s₁) / 10) := by
          rw [hF, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s₂ - s₁) / 10)]
  have hup := (abs_le.mp habs).2
  have hcoef : (0 : ℝ) < (s₁ + s₂) / 2 + 1/2 + 2 * a - 2 * x - 1/5 := by
    nlinarith [hx.2, hs₁.1, hs₂.1]
  have hprod := mul_pos (sub_pos.mpr hlt) hcoef
  simp only [dualParams_U_S, dbU_S, dualParams_β_S]
  nlinarith [hup, hprod]

/-! ## 4. State-local argmax uniqueness (Sender + Target)

Sender: the 40-semiconcavity of the carrier caps the continuation's
upward `s`-curvature at `40·(1/10)² = 2/5`, so the objective inherits
strict concavity `−1 + (1/2)·(2/5)·... = −4/5 < 0` from the stage
payoff — **uniformly in the (unrestricted real) compliance tilt `a`**,
which is exactly what `DynamicArgmaxUnique` quantifies. -/

/-- **State-local `DynamicArgmaxUnique` on the semiconcave carrier.**
The Sender dynamic objective is strictly concave in `s` for every
physical state and every real compliance level. -/
theorem dbCert_DAU_on_carrier {W : Val} (hW : W ∈ dbCarrierS) :
    dualParams.DynamicArgmaxUnique W := by
  apply dualParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p q hp hq hpq
  have hq_eq : q = 1 - p := by linarith
  subst hq_eq
  -- Transition points and their clip identities.
  have hz₁ : dualParams.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := dualParams.F_mem x s₁ hx hs₁
  have hz₂ : dualParams.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := dualParams.F_mem x s₂ hx hs₂
  have hsm : p * s₁ + (1 - p) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  have hzm : dualParams.F x (p * s₁ + (1 - p) * s₂) ∈ Set.Icc (0 : ℝ) 1 :=
    dualParams.F_mem x _ hx hsm
  -- The carrier semiconcavity chord at the three transition points.
  have hcombo : (Sanctions.clipS' (dualParams.F x (p * s₁ + (1 - p) * s₂))).val
      = p * (Sanctions.clipS' (dualParams.F x s₁)).val
        + (1 - p) * (Sanctions.clipS' (dualParams.F x s₂)).val := by
    rw [clipS'_val_of_mem hzm, clipS'_val_of_mem hz₁, clipS'_val_of_mem hz₂,
        dualParams_F, dualParams_F, dualParams_F]
    ring
  have hW_sc := hW.2.2 (Sanctions.clipS' (dualParams.F x s₁))
    (Sanctions.clipS' (dualParams.F x s₂))
    (Sanctions.clipS' (dualParams.F x (p * s₁ + (1 - p) * s₂)))
    p hp.le (by linarith) hcombo
  rw [clipS'_val_of_mem hz₁, clipS'_val_of_mem hz₂] at hW_sc
  -- hW_sc : p·W(z₁) + (1−p)·W(z₂) − W(zm) ≤ 20·p(1−p)·(F(x,s₁) − F(x,s₂))².
  have hFdiff : dualParams.F x s₁ - dualParams.F x s₂ = (s₁ - s₂) / 10 := by
    rw [dualParams_F, dualParams_F]; ring
  rw [hFdiff] at hW_sc
  simp only [smul_eq_mul, dualParams_U_S, dbU_S, dualParams_β_S]
  have hsq : (0 : ℝ) < (s₁ - s₂) ^ 2 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [hW_sc, mul_pos (mul_pos hp hq) hsq]

/-! ## 5. The knife-edge Target cancellation

With `V_T` slope-pinned at 10, the per-unit-sanction coefficient of the
Target's joint dynamic payoff is `−9/10 + (9/10)·10·(1/10) = 0` — the
sanction drops out EXACTLY. The joint Target integrand is
`10x − (1/5)a + (9/10)·V_T(0-point)` for every `V_S`, every real `a`,
and every value the Sender response takes. -/

/-- **Knife-edge closed form of the Target sanction objective**: at any
slope-pinned carrier member the sanction cancels exactly. -/
theorem dbCert_targetObj_const {V_T : Val} (hV_T : V_T ∈ dbCarrierT)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (a : ℝ) :
    dualParams.U_T x a s + dualParams.β_T * V_T (Sanctions.clipS' (dualParams.F x s))
      = 10 * x - 1/5 * a + 9/10 * V_T (Sanctions.clipS' 0) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have hz : dualParams.F x s ∈ Set.Icc (0 : ℝ) 1 := dualParams.F_mem x s hx hs
  have hdiff := gainBall_clip_diff (show (0 : ℝ) ≤ 10 by norm_num) hV_T h0 hz
  rw [dualParams_F] at hdiff
  simp only [dualParams_U_T, dbU_T, dualParams_β_T]
  rw [dualParams_F]
  linear_combination (9/10 : ℝ) * hdiff

/-- **Joint Target integrand in closed form** — σ-independent by the
knife edge: `10x − (1/5)a + (9/10)·V_T(0-point)`, strictly decreasing
in compliance. Needs only that the Sender response is feasible. -/
theorem dbCert_joint_T_integrand_eq {V_T : Val} (hV_T : V_T ∈ dbCarrierT)
    (V_S : Val) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    dualParams.joint_T_integrand V_T V_S x a
      = 10 * x - 1/5 * a + 9/10 * V_T (Sanctions.clipS' 0) := by
  simp only [AbstractGame.Params.joint_T_integrand]
  exact dbCert_targetObj_const hV_T hx (dualParams.σ_dyn_mem V_S x a) a

/-- **State-local `TargetArgmaxUnique` on the carriers**: the joint
integrand has exact compliance slope `−1/5`, so maximizers coincide. -/
theorem dbCert_TAU_on_carriers {V_T : Val} (hV_T : V_T ∈ dbCarrierT)
    (V_S : Val) :
    dualParams.TargetArgmaxUnique V_T V_S :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn fun x hx a₁ _ a₂ _ hlt => by
    simp only [dbCert_joint_T_integrand_eq hV_T V_S hx a₁,
      dbCert_joint_T_integrand_eq hV_T V_S hx a₂]
    linarith

/-- **Zero (full defiance) is the Target argmax** at every physical
state — the strict unique leader argmax the knife edge delivers. -/
theorem dbCert_zero_isMaxOn_joint {V_T : Val} (hV_T : V_T ∈ dbCarrierT)
    (V_S : Val) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => dualParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [dbCert_joint_T_integrand_eq hV_T V_S hx a,
      dbCert_joint_T_integrand_eq hV_T V_S hx 0]
  linarith [ha.1]

/-! ## 6. The Sender Bellman image lives in the semiconcave carrier

The one genuinely new invariance lemma of this witness. The image is
evaluated at an *attained* argmax (compactness + continuity — no corner
pinning is available here, because the argmax sweeps the interior
between the basins), and each carrier leg is proved by comparing
argmax-evaluated images against feasible candidates. -/

/-- Argmax attainment for the Sender dynamic objective at the defiance
policy: continuity on the compact sanction interval. -/
theorem dbCert_exists_argmax (W : Val) (y : ↥(Sanctions.S : Set ℝ)) :
    ∃ sStar ∈ Sanctions.I,
      IsMaxOn (fun s => dualParams.U_S y.val 0 s
        + dualParams.β_S * W (Sanctions.clipS' (dualParams.F y.val s)))
        Sanctions.I sStar := by
  have hcont : Continuous (fun s : ℝ => dualParams.U_S y.val 0 s
      + dualParams.β_S * W (Sanctions.clipS' (dualParams.F y.val s))) := by
    apply Continuous.add
    · simp only [dualParams_U_S]
      unfold dbU_S
      fun_prop
    · apply continuous_const.mul
      apply W.continuous.comp
      apply Sanctions.clipS'_continuous.comp
      exact dualParams.F_continuous.comp
        (Continuous.prodMk continuous_const continuous_id)
  obtain ⟨sStar, hsI, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hcont.continuousOn
  exact ⟨sStar, hsI, hmax⟩

/-- **Sender Bellman image evaluated at an attained argmax**, together
with the sup-domination of every feasible sanction. -/
theorem dbCert_bellmanS_spec (W : Val) (y : ↥(Sanctions.S : Set ℝ)) :
    ∃ sStar ∈ Sanctions.I,
      dualParams.bellmanS_BCF (fun _ => 0) continuous_const W y
        = dualParams.U_S y.val 0 sStar
          + dualParams.β_S * W (Sanctions.clipS' (dualParams.F y.val sStar))
      ∧ ∀ s ∈ Sanctions.I,
          dualParams.U_S y.val 0 s
            + dualParams.β_S * W (Sanctions.clipS' (dualParams.F y.val s))
          ≤ dualParams.bellmanS_BCF (fun _ => 0) continuous_const W y := by
  obtain ⟨sStar, hsI, hmax⟩ := dbCert_exists_argmax W y
  have heq := WitnessKit.bellmanS_image_of_isMaxOn (p := dualParams)
    (α := fun _ => 0) continuous_const W y hsI hmax
  refine ⟨sStar, hsI, heq, ?_⟩
  intro s hs
  rw [heq]
  exact hmax hs

/-- **The semiconcave-carrier invariance lemma** (the substantive new
piece): the Sender Bellman operator at the derived defiance policy maps
`dbCarrierS` into itself.

* norm: `|image| ≤ 1 + (1/2)(5/2) = 9/4 ≤ 5/2`;
* Lipschitz: `2 + (1/2)·4·(9/10) = 19/5 ≤ 4` (sup-difference bound);
* semiconcavity: evaluating the two outer images at their attained
  argmaxes `s₁✦, s₂✦` and feeding the middle image the convex candidate
  `t·s₁✦ + (1−t)·s₂✦` turns the chord defect into
  `t(1−t)·[−(1/2)Δs² + 2·Δs·Δy + (1/10)(9Δy + Δs)²]`; one quadratic
  completion bounds the bracket by `(137/8)·Δy²` for ALL `Δs`
  (`20·Δy² − bracket = (1/40)(4Δs − 19Δy)² + (115/40)Δy² ≥ 0`) — the
  interior-regime constant `Φ(40) = 137/4 ≤ 40`, with no regime split
  and no argmax-location information. -/
theorem dbCert_bellmanS_mem {W : Val} (hW : W ∈ dbCarrierS) :
    dualParams.bellmanS_BCF (fun _ => 0) continuous_const W ∈ dbCarrierS := by
  have hWn : ∀ z : ℝ, |W (Sanctions.clipS' z)| ≤ 5/2 := by
    intro z
    have h := BoundedContinuousFunction.norm_coe_le_norm W (Sanctions.clipS' z)
    rw [Real.norm_eq_abs] at h
    exact le_trans h hW.1
  refine ⟨?_, ?_, ?_⟩
  · -- Leg 1: norm ≤ 5/2 (with margin: |image| ≤ 9/4).
    rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 5/2)]
    intro y
    obtain ⟨s₀, hs₀I, heq, hdom⟩ := dbCert_bellmanS_spec W y
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · -- lower: image ≥ obj(0) = (1/2)·W(clip(F(y,0))) ≥ −5/4.
      have h0 := hdom 0 ⟨le_refl 0, by norm_num⟩
      have hb := (abs_le.mp (hWn (dualParams.F y.val 0))).1
      simp only [dualParams_U_S, dbU_S, dualParams_β_S] at h0
      nlinarith [h0, hb]
    · -- upper: image = obj(s₀) ≤ 1 + 5/4 = 9/4.
      have hb := (abs_le.mp (hWn (dualParams.F y.val s₀))).2
      rw [heq]
      simp only [dualParams_U_S, dbU_S, dualParams_β_S]
      nlinarith [hb, hs₀I.1, hs₀I.2, y.property.1, y.property.2,
        mul_nonneg hs₀I.1 (sub_nonneg.mpr y.property.2),
        mul_nonneg (by linarith [hs₀I.2] : (0 : ℝ) ≤ 1 - s₀)
          (by linarith [hs₀I.2] : (0 : ℝ) ≤ 2 - s₀)]
  · -- Leg 2: 4-Lipschitz (with margin: the true constant is 19/5).
    have key : ∀ u v : ↥(Sanctions.S : Set ℝ),
        dualParams.bellmanS_BCF (fun _ => 0) continuous_const W v
          - dualParams.bellmanS_BCF (fun _ => 0) continuous_const W u
        ≤ 4 * dist u v := by
      intro u v
      obtain ⟨sv, hsvI, heqv, _⟩ := dbCert_bellmanS_spec W v
      obtain ⟨su, hsuI, hequ, hdomu⟩ := dbCert_bellmanS_spec W u
      have hle := hdomu sv hsvI
      have hWd := dbS_clip_chord hW (dualParams.F u.val sv) (dualParams.F v.val sv)
      have hF : dualParams.F v.val sv - dualParams.F u.val sv
          = 9/10 * (v.val - u.val) := by
        rw [dualParams_F, dualParams_F]; ring
      have habs : |W (Sanctions.clipS' (dualParams.F v.val sv))
          - W (Sanctions.clipS' (dualParams.F u.val sv))|
          ≤ 4 * (9/10 * |v.val - u.val|) := by
        calc |W (Sanctions.clipS' (dualParams.F v.val sv))
            - W (Sanctions.clipS' (dualParams.F u.val sv))|
            ≤ 4 * |dualParams.F v.val sv - dualParams.F u.val sv| := hWd
          _ = 4 * (9/10 * |v.val - u.val|) := by
              rw [hF, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9/10)]
      have hdist : dist u v = |v.val - u.val| := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      rw [heqv, hdist]
      have hup := (abs_le.mp habs).2
      simp only [dualParams_U_S, dbU_S, dualParams_β_S] at hle ⊢
      nlinarith [hup, hle, abs_nonneg (v.val - u.val),
        le_abs_self (v.val - u.val), hsvI.1, hsvI.2,
        mul_le_mul_of_nonneg_left (le_abs_self (v.val - u.val))
          (by linarith [hsvI.1] : (0 : ℝ) ≤ 2 * sv),
        mul_le_mul_of_nonneg_right hsvI.2 (abs_nonneg (v.val - u.val))]
    intro y₁ y₂
    rw [abs_sub_le_iff]
    constructor
    · exact key y₁ y₂
    · have h := key y₂ y₁
      rwa [dist_comm] at h
  · -- Leg 3: 40-semiconcavity (with margin: the image is 137/4-semiconcave).
    intro y₁ y₂ m t ht0 ht1 hm
    obtain ⟨s₁, hs₁I, heq₁, _⟩ := dbCert_bellmanS_spec W y₁
    obtain ⟨s₂, hs₂I, heq₂, _⟩ := dbCert_bellmanS_spec W y₂
    have hcand : t * s₁ + (1 - t) * s₂ ∈ Sanctions.I :=
      ⟨by nlinarith [hs₁I.1, hs₂I.1], by nlinarith [hs₁I.2, hs₂I.2]⟩
    obtain ⟨_, _, _, hdomm⟩ := dbCert_bellmanS_spec W m
    have hge := hdomm (t * s₁ + (1 - t) * s₂) hcand
    have hz₁ : dualParams.F y₁.val s₁ ∈ Set.Icc (0 : ℝ) 1 :=
      dualParams.F_mem _ _ y₁.property hs₁I
    have hz₂ : dualParams.F y₂.val s₂ ∈ Set.Icc (0 : ℝ) 1 :=
      dualParams.F_mem _ _ y₂.property hs₂I
    have hzm : dualParams.F m.val (t * s₁ + (1 - t) * s₂) ∈ Set.Icc (0 : ℝ) 1 :=
      dualParams.F_mem _ _ m.property hcand
    have hcombo : (Sanctions.clipS'
          (dualParams.F m.val (t * s₁ + (1 - t) * s₂))).val
        = t * (Sanctions.clipS' (dualParams.F y₁.val s₁)).val
          + (1 - t) * (Sanctions.clipS' (dualParams.F y₂.val s₂)).val := by
      rw [clipS'_val_of_mem hzm, clipS'_val_of_mem hz₁, clipS'_val_of_mem hz₂,
          dualParams_F, dualParams_F, dualParams_F, hm]
      ring
    have hW_sc := hW.2.2 (Sanctions.clipS' (dualParams.F y₁.val s₁))
      (Sanctions.clipS' (dualParams.F y₂.val s₂))
      (Sanctions.clipS' (dualParams.F m.val (t * s₁ + (1 - t) * s₂)))
      t ht0 ht1 hcombo
    rw [clipS'_val_of_mem hz₁, clipS'_val_of_mem hz₂] at hW_sc
    have hFdiff : dualParams.F y₁.val s₁ - dualParams.F y₂.val s₂
        = (9 * (y₁.val - y₂.val) + (s₁ - s₂)) / 10 := by
      rw [dualParams_F, dualParams_F]; ring
    rw [hFdiff] at hW_sc
    rw [heq₁, heq₂]
    simp only [dualParams_U_S, dbU_S, dualParams_β_S] at hge hW_sc ⊢
    rw [hm] at hge hW_sc
    have hP : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
    have h1 : (0 : ℝ) ≤ t * (1 - t)
        * (4 * (s₁ - s₂) - 19 * (y₁.val - y₂.val)) ^ 2 :=
      mul_nonneg hP (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ t * (1 - t) * (y₁.val - y₂.val) ^ 2 :=
      mul_nonneg hP (sq_nonneg _)
    nlinarith [hge, hW_sc, h1, h2]

/-! ## 7. The asymmetric value class, the derived leader policy, and
Bellman invariance -/

/-- **The `ValueClass2` at the dual-basin witness**: slope-pinned
Target gain ball × semiconcave Sender ball, with state-local
Sender/Target argmax uniqueness. -/
def dbClass : dualParams.ValueClass2 where
  carrier_T := dbCarrierT
  carrier_S := dbCarrierS
  isClosed_T := dbCarrierT_isClosed
  isClosed_S := dbCarrierS_isClosed
  nonempty_T := dbCarrierT_nonempty
  nonempty_S := dbCarrierS_nonempty
  sender_unique_on := fun _ hV_S => (dbCert_DAU_on_carrier hV_S).toOnI
  target_unique_on := fun _ hV_T V_S _ => dbCert_TAU_on_carriers hV_T V_S

/-- **The derived leader policy is the defiance corner `α_on ≡ 0`.**
By the knife-edge cancellation the joint integrand is σ-independent
with exact compliance slope `−1/5`, so full defiance is the strict
unique leader argmax at every state, for every carrier pair (Rule 1:
derived, not assumed). -/
theorem dbCert_α_on_eq_zero (V_T : dbClass.CarrierT)
    (V_S : dbClass.CarrierS) :
    dbClass.α_on V_T V_S = fun _ => (0 : ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    dbCert_zero_isMaxOn_joint V_T.property V_S.val y.property

/-- **Target Bellman image in closed form**: the sSup over compliance
collapses at the defiance corner, and the knife edge leaves the exact
slope-10 affine `10·y + (9/10)·V_T(0-point)` — the `g_T = 10` pin. -/
theorem dbCert_jointTarget_image (V_T : dbClass.CarrierT)
    (V_S : dbClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    dualParams.jointTarget_BCF_on_S V_T.val V_S.val
      (dbClass.sender_unique_on V_S.val V_S.property) y
      = 10 * y.val + 9/10 * V_T.val (Sanctions.clipS' 0) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (dbClass.sender_unique_on V_S.val V_S.property) y
        (⟨le_refl 0, by norm_num⟩ : (0 : ℝ) ∈ Sanctions.I)
        (dbCert_zero_isMaxOn_joint V_T.property V_S.val y.property),
      dbCert_joint_T_integrand_eq V_T.property V_S.val y.property 0]
  ring

/-- **Heterogeneous carrier invariance**: the Target image is exactly
slope-10 affine with band contraction `b ↦ (9/10)b` (staying inside
`[−19, 9]`), and the Sender image stays in the semiconcave ball by the
new invariance lemma. -/
theorem dbClass_IsInvariant : dbClass.IsInvariant := by
  intro V_T V_S
  constructor
  · -- Target image ∈ dbCarrierT.
    change dualParams.jointTarget_BCF_on_S V_T.val V_S.val
        (dbClass.sender_unique_on V_S.val V_S.property) ∈ dbCarrierT
    -- The band bound: b = V_T(0-point) ∈ [−19, 9] from the two-point
    -- norm bound plus the slope-10 pin.
    have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
    have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl 1⟩
    have hpin := gainBall_clip_diff (show (0 : ℝ) ≤ 10 by norm_num)
      V_T.property h0I h1I
    have hVn : ‖V_T.val‖ ≤ 19 := V_T.property.1
    have hb0 : |V_T.val (Sanctions.clipS' 0)| ≤ 19 := by
      have h := BoundedContinuousFunction.norm_coe_le_norm V_T.val
        (Sanctions.clipS' 0)
      rw [Real.norm_eq_abs] at h
      exact le_trans h hVn
    have hb1 : |V_T.val (Sanctions.clipS' 1)| ≤ 19 := by
      have h := BoundedContinuousFunction.norm_coe_le_norm V_T.val
        (Sanctions.clipS' 1)
      rw [Real.norm_eq_abs] at h
      exact le_trans h hVn
    have hband_lo : -19 ≤ V_T.val (Sanctions.clipS' 0) := (abs_le.mp hb0).1
    have hband_hi : V_T.val (Sanctions.clipS' 0) ≤ 9 := by
      have h1 := (abs_le.mp hb1).2
      linarith [hpin]
    refine ⟨?_, ?_, ?_⟩
    · -- norm ≤ 19 (image range [−17.1, 18.1]).
      rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 19)]
      intro y
      rw [dbCert_jointTarget_image V_T V_S y, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [y.property.1, y.property.2, hband_lo, hband_hi]
    · -- Lipschitz 10 (exact affine slope; the V_T-term is constant).
      intro y₁ y₂
      rw [dbCert_jointTarget_image V_T V_S y₁,
          dbCert_jointTarget_image V_T V_S y₂,
          Subtype.dist_eq, Real.dist_eq]
      have hkey : 10 * y₂.val + 9/10 * V_T.val (Sanctions.clipS' 0)
          - (10 * y₁.val + 9/10 * V_T.val (Sanctions.clipS' 0))
          = 10 * (y₂.val - y₁.val) := by ring
      rw [hkey, abs_mul, show |(10 : ℝ)| = 10 by norm_num,
          abs_sub_comm y₁.val y₂.val]
    · -- min-slope 10 (exact affine slope).
      intro y₁ y₂ _ _ hle
      have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
      rw [dbCert_jointTarget_image V_T V_S y₁,
          dbCert_jointTarget_image V_T V_S y₂,
          Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
      linarith
  · -- Sender image ∈ dbCarrierS (the new semiconcave invariance lemma).
    change dualParams.bellmanS_BCF (dbClass.α_on V_T V_S)
        (dbClass.α_on_continuous V_T V_S) V_S.val ∈ dbCarrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (dbCert_α_on_eq_zero V_T V_S)
        (dbClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    exact dbCert_bellmanS_mem V_S.property

/-! ## 8. Decoupled Schur row bounds

The knife edge decouples BOTH rows exactly: the Target image is
`V_S`-independent (`L_TS = 0`) and the Sender operator is
`V_T`-independent because the derived leader policy is the constant
defiance corner for every carrier pair (`L_ST = 0`). -/

/-- **Target-row bound**: `β_T = 9/10`, cross coefficient `L_TS = 0`. -/
theorem dbClass_hT_T_op
    (h_inv : dbClass.IsInvariant)
    (V V' : dbClass.CarrierT) (W W' : dbClass.CarrierS) :
    dist (dbClass.jointTargetOp_sub h_inv (V, W))
          (dbClass.jointTargetOp_sub h_inv (V', W'))
      ≤ (9/10 : ℝ) * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun z => 10 * z) (φ := fun _ => 0)
    (fun V W y => dbCert_jointTarget_image V W y) V V' W W'

/-- **Sender-row bound**: `β_S = 1/2`, cross coefficient `L_ST = 0`. -/
theorem dbClass_hT_S_op
    (h_inv : dbClass.IsInvariant)
    (V V' : dbClass.CarrierT) (W W' : dbClass.CarrierS) :
    dist (dbClass.jointSenderOp_sub h_inv (V, W))
          (dbClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    dbCert_α_on_eq_zero V V' W W'

/-! ## 9. The myopic comparator

The myopic (β = 0) Target best-responds to the static placable Sender:
`M.α(x) = clip(x − 1/4)`. It complies exactly enough to zero out the
static sanction (`σ_myo ≡ 0` identically), so the dynamic-over-myopic
dominance gap on the high basin is the full `1 − 0 = 1`. -/

/-- **The myopic realized sanction is identically zero**:
`σ(x, clip(x − 1/4)) = clip(2x − 1/2 − 2·clip(x − 1/4)) = 0`. -/
theorem dbσ_myopic_eq_zero (x : ℝ) : dbσ x (max 0 (x - 1/4)) = 0 := by
  unfold dbσ
  rcases le_total x (1/4 : ℝ) with h4 | h4
  · rw [max_eq_left (by linarith : x - 1/4 ≤ 0)]
    rw [min_eq_right (by linarith : 2 * x - 1/2 - 2 * 0 ≤ 1),
        max_eq_left (by linarith : 2 * x - 1/2 - 2 * 0 ≤ 0)]
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ x - 1/4),
        show 2 * x - 1/2 - 2 * (x - 1/4) = 0 by ring,
        min_eq_right (by norm_num : (0 : ℝ) ≤ 1), max_self]

/-- **The myopic feedback equilibrium at the witness.** The myopic
stage objective `h(a) = U_T(x, a, σ(x,a))` is piecewise linear with
slopes `−1/5 / +8/5 / −1/5` (breakpoints `x − 3/4 < x − 1/4`); its
argmax is the placation kink `clip(x − 1/4)` (Rule 1: derived as the
stage argmax, not assumed). -/
def dbMyopic : dualParams.MyopicFeedbackEquilibrium where
  α := fun x => max 0 (x - 1/4)
  α_mem := fun x hx =>
    ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hx.2])⟩
  α_opt := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    change dbU_T x a (dbσ x a)
        ≤ dbU_T x (max 0 (x - 1/4)) (dbσ x (max 0 (x - 1/4)))
    rw [dbσ_myopic_eq_zero x]
    have hσ_nn : 0 ≤ dbσ x a := (dbσ_mem x a).1
    simp only [dbU_T]
    rcases le_total x (1/4 : ℝ) with h4 | h4
    · -- pre-placation region: the myopic argmax is full defiance.
      rw [max_eq_left (by linarith : x - 1/4 ≤ 0)]
      linarith [ha.1, hσ_nn]
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ x - 1/4)]
      rcases le_total (x - 1/4) a with hcase | hcase
      · -- over-compliance: paying more than the placation kink loses.
        linarith [hσ_nn]
      · -- under-compliance: the sanction bites at rate 9/10 > 1/5·(1/2).
        have hσ_eq : dbσ x a = min 1 (2 * x - 1/2 - 2 * a) := by
          unfold dbσ
          exact max_eq_right (le_min (by norm_num) (by linarith))
        rcases le_total (2 * x - 1/2 - 2 * a) 1 with h1 | h1
        · rw [hσ_eq, min_eq_right h1]
          linarith
        · rw [hσ_eq, min_eq_left h1]
          linarith [ha.1, hx.2]

/-- **Myopic ceiling on the basin**: the myopic realized sanction is
identically `0 ≤ max(x, 1/2)`. -/
theorem dbCert_hMyoCeiling :
    ∀ x ∈ Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1,
      dualParams.σ x (dbMyopic.α x) ≤ max x (1/2 : ℝ) := by
  intro x _
  change dbσ x (max 0 (x - 1/4)) ≤ max x (1/2 : ℝ)
  rw [dbσ_myopic_eq_zero x]
  exact le_trans (by norm_num) (le_max_right x (1/2 : ℝ))

/-! ## 10. High-basin stage fields -/

/-- **Stage Target loss bound**: the Target stage payoff has EXACT
sanction chord slope `−9/10 = −c_T` (uniform in the compliance level,
so no leader-policy rewrite is needed). -/
theorem dbCert_h_stage_target_loss (V_T : dbClass.CarrierT)
    (V_S : dbClass.CarrierS) :
    ∀ x ∈ Set.Icc (19 / 20 : ℝ) 1,
      LowerLossSlopeOn
        (fun s => dualParams.U_T x (dbClass.α_on V_T V_S x) s)
        (Set.Icc (max x (1/2 : ℝ)) 1) (9/10) := by
  intro x _ s₁ _ s₂ _ _
  simp only [dualParams_U_T, dbU_T]
  linarith

/-- **Stage Sender slope** at the derived defiance policy: chord slope
`2x − 1/2 − (s₁+s₂)/2 ≥ x − 1/2 ≥ 9/20` on `[0, max(x, 1/2)] = [0, x]`
for basin `x ≥ 19/20`. -/
theorem dbCert_h_stage_sender (V_T : dbClass.CarrierT)
    (V_S : dbClass.CarrierS) :
    ∀ x ∈ Set.Icc (19 / 20 : ℝ) 1,
      LowerSlopeOn
        (fun s => dualParams.U_S x (dbClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (1/2 : ℝ))) (9/20) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hmax : max x (1/2 : ℝ) = x :=
    max_eq_left (le_trans (by norm_num) hx.1)
  rw [hmax] at hs₁ hs₂
  simp only [dbCert_α_on_eq_zero V_T V_S, dualParams_U_S, dbU_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0 : ℝ) ≤ 2 * x - 1/2 - (s₁ + s₂) / 2 - 9/20 by
      linarith [hs₁.2, hs₂.2, hx.1])]

/-- **Carrier `V_T` gain on the basin**: restriction of the slope-10
pin from `[0,1]` to `[19/20, 1]`. -/
theorem dbCert_hV_T_gain :
    ∀ V_T ∈ dbClass.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc (19 / 20 : ℝ) 1) 10 := by
  intro V_T hV_T y₁ y₂ h1 h2 hle
  exact hV_T.2.2 y₁ y₂ ⟨by linarith [h1.1], h1.2⟩
    ⟨by linarith [h2.1], h2.2⟩ hle

/-- **Single crossing (trivial form)**: the Sender dynamic objective is
strictly increasing in the sanction at every basin state (min chord
slope `1/5 > 0` under maximal carrier drag), so both single-crossing
consequents hold unconditionally. -/
theorem dbCert_hSC (V_T : dbClass.CarrierT) (V_S : dbClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1)
      (fun s x => dualParams.senderDynObjective V_S.val x
        (dbClass.α_on V_T V_S x) s) :=
  WitnessKit.singleCrossingOn_of_strictMonoOn fun t ht s₁ hs₁ s₂ hs₂ hlt => by
    simp only [dbCert_α_on_eq_zero V_T V_S,
      AbstractGame.Params.senderDynObjective]
    exact dbCert_senderObj_strictMonoOn_high V_S.property
      ⟨le_trans (le_max_left _ _) ht.1, ht.2⟩ hs₁ hs₂ hlt

/-! ## 11. THE HIGH-BASIN CERTIFICATE -/

/-- **The dual-basin witness's `StandardComplianceLocalCoreCertificate`**
on the high basin `[19/20, 1]` with sanction floor `s̄ = 1/2`. Every
field discharged unconditionally: the asymmetric slope-pinned/semiconcave
value class with state-local argmax uniqueness (`D`), heterogeneous
Bellman invariance (`h_inv`, via the new semiconcave-carrier lemma),
exactly decoupled Schur rows (`β_T = 9/10, β_S = 1/2, L_TS = L_ST = 0`),
the Sender stage margin (`m_S = 9/20 > 1/5 = β_S·K_S·δ`), carrier-local
stage slopes, interval dominance from strict monotonicity, and the myopic
comparator `clip(x − 1/4)` with its trivial ceiling (`σ_myo ≡ 0`). The
Target loss-offset at the knife edge (`c_T = 9/10 ≤ 9/10 = β_T·g_T·δ`) was a
field until round BJ1.4 (2026-10-07); its halves remain proved here
(`dbCert_h_stage_target_loss`, `dbCert_hV_T_gain`). -/
noncomputable def dbCertCertificate :
    dualParams.StandardComplianceLocalCoreCertificate where
  D := dbClass
  h_inv := dbClass_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := dbClass_hT_T_op dbClass_IsInvariant
  hT_S_op := dbClass_hT_S_op dbClass_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 19/20
  xS := 19/20
  sbar := 1/2
  mS := 9/20
  KS := 4
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  d := dualParams.δ
  hF_chord := dualParams.affine_sender_chord_on rfl _ _
  hS_margin := by
    simp only [dualParams_β_S, dualParams_δ]
    norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := fun _ hV_S => hV_S.2.1
  h_stage_sender_on := dbCert_h_stage_sender
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (dbCert_hSC V_T V_S)
  M := dbMyopic
  hMyoCeiling := dbCert_hMyoCeiling

/-! ## 12. The high-basin three-goals corollary (one line, Rule 5) -/

/-- **Theorem 1 + Goals 2/3 fired at the dual-basin witness** (high
basin `[19/20, 1]`): the forward-looking equilibrium exists on the
carriers; from every basin start the state path stays in the basin,
realized sanctions are ≥ 1/2 and ≥ 19/20 and non-decreasing, and the
Target policy is Bellman-optimal along the path; the myopic realized
rule is dominated statewise; every shock start eventually re-enters
the basin regime. One-line specialization of
`three_goals_local_uniform_starts`. -/
theorem dbCert_three_goals_high :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ dbCarrierT
      ∧ E.V_S ∈ dbCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1,
          (∀ n, dualParams.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1) ∧
          (∀ n, (1/2 : ℝ)
                  ≤ dualParams.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max (19 / 20 : ℝ) (19 / 20)
                  ≤ dualParams.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (dualParams.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => dualParams.joint_T_top_integrand E.V_T E.V_S
                        (dualParams.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I
            (E.α (dualParams.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1,
           dualParams.σ x (dbMyopic.α x)
             ≤ dualParams.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, dualParams.dynamicTopLockInPath E.V_S E.α
                    (dualParams.shockPath x₀shock N) n
                    ∈ Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1) ∧
            (∀ n, (1/2 : ℝ)
                    ≤ dualParams.dynamicTopLockInSanctions E.V_S E.α
                        (dualParams.shockPath x₀shock N) n) ∧
            (∀ n, max (19 / 20 : ℝ) (19 / 20)
                    ≤ dualParams.dynamicTopLockInSanctions E.V_S E.α
                        (dualParams.shockPath x₀shock N) n)) :=
  dbCertCertificate.three_goals_local_uniform_starts (p := dualParams) rfl

/-! ## 13. The low-basin thresholds AT THE SAME EQUILIBRIUM

Both low-basin inputs are discharged from carrier membership of the
equilibrium value pair alone — no α-coincidence and no re-solving. The
Sender side uses only `E.α x ≥ 0` (feasibility); the Target side is the
knife-edge indifference, exact for every compliance level. -/

/-- **Dual one-sided thresholds at any carrier equilibrium**: on the
low basin `[0, 1/10]` the Sender's forward-looking objective strictly
decreases in the sanction (margin `1/10`), and the Target's is exactly
flat (weakly antitone — the knife edge). -/
theorem dbCert_lowBasin_thresholds
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) (hVS : E.V_S ∈ dbCarrierS) :
    dualParams.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
      (1 / 10) (1 / 10) (1 / 10) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · -- Sender strictly dislikes sanctions on the low basin.
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2 (by norm_num)⟩
    have haI : E.α x ∈ Sanctions.I := E.α_mem x hxI
    have hanti := dbCert_senderObj_strictAntiOn_low hVS hx haI.1
    have hsub : Set.Icc (min x (1 / 10 : ℝ)) 1 ⊆ Sanctions.I :=
      Set.Icc_subset_Icc (le_min hx.1 (by norm_num)) (le_refl 1)
    intro s₁ hs₁ s₂ hs₂ hlt
    exact hanti (hsub hs₁) (hsub hs₂) hlt
  · -- Target knife-edge indifference: the chord is identically zero.
    intro x hx s₁ hs₁ s₂ hs₂ _
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2 (by norm_num)⟩
    have hmin_nn : (0 : ℝ) ≤ min x (1 / 10) := le_min hx.1 (by norm_num)
    have hs₁I : s₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hmin_nn hs₁.1, hs₁.2⟩
    have hs₂I : s₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hmin_nn hs₂.1, hs₂.2⟩
    simp only [AbstractGame.Params.targetSanctionObjective]
    rw [dbCert_targetObj_const hVT hxI hs₂I, dbCert_targetObj_const hVT hxI hs₁I]

/-- **Top-rule monotonicity on the low basin**: the strict decrease of
the Sender dynamic objective pins the upper-selector realized rule at
the constant `0`, which is trivially monotone. -/
theorem dbCert_lowBasin_topMono
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ dbCarrierS) :
    MonotoneOn (dualParams.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc (0 : ℝ) (min (1 / 10 : ℝ) (1 / 10))) := by
  have hrule : ∀ x ∈ Set.Icc (0 : ℝ) (min (1 / 10 : ℝ) (1 / 10)),
      dualParams.dynamicTopRealizedRule E.V_S E.α x = 0 := by
    intro x hx
    rw [min_self] at hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2 (by norm_num)⟩
    have haI : E.α x ∈ Sanctions.I := E.α_mem x hxI
    exact WitnessKit.σ_dyn_top_eq_zero_of_strictAntiOn
      (dbCert_senderObj_strictAntiOn_low hVS hx haI.1)
  intro y hy z hz _
  rw [hrule y hy, hrule z hz]

/-! ## 14. The low-basin three-goals corollary (one line, Rule 5) -/

/-- **Theorem 4 fired at the dual-basin witness** (low basin
`[0, 1/10]`), at an equilibrium living on the SAME carriers: from every
low start the state path stays in the low basin, realized sanctions are
bounded by `1/10`, and the sanction sequence is non-increasing — the
wash-out mirror. One-line specialization of
`standardCompliance_three_goals_local_low_basin` at the equilibrium
produced by the high-basin certificate. -/
theorem dbCert_three_goals_low :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ dbCarrierT ∧ E.V_S ∈ dbCarrierS
      ∧ ∀ x₀ ∈ Set.Icc (0 : ℝ) (min (1 / 10 : ℝ) (1 / 10)),
          (∀ n, dualParams.dynamicTopLockInPath E.V_S E.α x₀ n
                  ∈ Set.Icc (0 : ℝ) (min (1 / 10 : ℝ) (1 / 10))) ∧
          (∀ n, dualParams.dynamicTopLockInSanctions E.V_S E.α x₀ n
                  ≤ 1 / 10) ∧
          (∀ n, dualParams.dynamicTopLockInSanctions E.V_S E.α x₀ n
                  ≤ min (1 / 10 : ℝ) (1 / 10)) ∧
          Antitone (dualParams.dynamicTopLockInSanctions E.V_S E.α x₀) := by
  obtain ⟨E, hVT, hVS, _, _, _⟩ := dbCert_three_goals_high
  exact ⟨E, hVT, hVS, fun x₀ hx₀ =>
    dualParams.standardCompliance_three_goals_local_low_basin E
      (dbCert_lowBasin_thresholds E hVT hVS)
      (dbCert_lowBasin_topMono E hVS) hx₀⟩

/-! ## 15. THE SELECTION THEOREM -/

/-- The two certified basins are disjoint: `[19/20, 1] ∩ [0, 1/10] = ∅`. -/
theorem dbBasins_disjoint :
    Disjoint (Set.Icc (19 / 20 : ℝ) 1) (Set.Icc (0 : ℝ) (1 / 10)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := hx.1
  have h2 := hx'.2
  linarith

/-- **Initial-condition selection at a single economy — the dual-basin
headline.** At `dualParams` there is ONE forward-looking feedback
Stackelberg equilibrium `E` (produced by the Banach fixed point on the
slope-pinned/semiconcave carrier pair) such that, simultaneously:

* **(lock-in)** from every start in the high basin `[19/20, 1]`, the
  equilibrium state path stays in the high basin forever, realized
  sanctions are bounded below by `19/20` and non-decreasing;
* **(wash-out)** from every start in the (disjoint,
  `dbBasins_disjoint`) low basin `[0, 1/10]`, the equilibrium state
  path stays in the low basin forever, realized sanctions are bounded
  above by `1/10` and non-increasing.

Which long-run regime obtains is decided by the initial political
state alone — the same players, the same payoffs, the same equilibrium
strategies. Both bundles are the existing headline conclusions
(Theorem 1's persistence goal and Theorem 4's wash-out mirror)
packaged at one `Params`; no new dynamics are introduced. -/
theorem dualParams_initial_condition_selects :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ dbCarrierT ∧ E.V_S ∈ dbCarrierS
      ∧ (∀ x₀ ∈ Set.Icc (19 / 20 : ℝ) 1,
          (∀ n, dualParams.dynamicTopLockInPath E.V_S E.α x₀ n
                  ∈ Set.Icc (19 / 20 : ℝ) 1) ∧
          (∀ n, (19 / 20 : ℝ)
                  ≤ dualParams.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (dualParams.dynamicTopLockInSanctions E.V_S E.α x₀))
      ∧ (∀ x₀ ∈ Set.Icc (0 : ℝ) (1 / 10),
          (∀ n, dualParams.dynamicTopLockInPath E.V_S E.α x₀ n
                  ∈ Set.Icc (0 : ℝ) (1 / 10)) ∧
          (∀ n, dualParams.dynamicTopLockInSanctions E.V_S E.α x₀ n
                  ≤ 1 / 10) ∧
          Antitone (dualParams.dynamicTopLockInSanctions E.V_S E.α x₀)) := by
  obtain ⟨E, hVT, hVS, hG1, _, _⟩ := dbCert_three_goals_high
  refine ⟨E, hVT, hVS, ?_, ?_⟩
  · -- HIGH BASIN: project the certified lock-in bundle.
    intro x₀ hx₀
    have hx₀' : x₀ ∈ Set.Icc (max (19 / 20 : ℝ) (19 / 20)) 1 := by
      rwa [max_self]
    obtain ⟨hpath, _, hfloor, hmono, _⟩ := hG1 x₀ hx₀'
    refine ⟨fun n => ?_, fun n => ?_, hmono⟩
    · have h := hpath n
      rwa [max_self] at h
    · have h := hfloor n
      rwa [max_self] at h
  · -- LOW BASIN: the certified wash-out bundle at the SAME `E`.
    intro x₀ hx₀
    have hx₀' : x₀ ∈ Set.Icc (0 : ℝ) (min (1 / 10 : ℝ) (1 / 10)) := by
      rwa [min_self]
    obtain ⟨hpath, hceil, _, hanti⟩ :=
      dualParams.standardCompliance_three_goals_local_low_basin E
        (dbCert_lowBasin_thresholds E hVT hVS)
        (dbCert_lowBasin_topMono E hVS) hx₀'
    refine ⟨fun n => ?_, hceil, hanti⟩
    have h := hpath n
    rwa [min_self] at h

/-! ## 16. Named limits, from the general theory (2026-08-14)

`dualParams_initial_condition_selects` above reports *persistence*: the state
stays in its basin and the sanction sequence is monotone with a floor or a
ceiling. It does not say where either sequence ends up.

This section closes that, and does so by **applying** the general attraction
theory rather than re-deriving it. Everything dynamic comes from
`equilibriumTop_twoBasin_order_selected` in `Theory/LockIn/BasinAttraction.lean`,
which is general in `p.F`, assumes no uniqueness of the rest point, and imposes
no strict sign condition. What this witness contributes is only the four inputs
that theorem needs at one economy — the realized rule on each basin, and the
resulting monotonicity and invariance — plus the arithmetic identifying the two
selected rest points as `0` and `1`.

Rule 9: this is an **existence certificate**. It shows the general theory is
non-vacuous and that its hypotheses are jointly satisfiable at a constructed
equilibrium. It licenses no claim that the mechanism is generic, that the limits
are `0` and `1` in other economies, or that the two basins are the only ones.

Note what the equilibrium does here, since it bears on the paper's reading: the
Target defects fully (`E.α ≡ 0`) at **every** state, and the Sender's realized
rule is pinned at the corner `1` on the high basin and at `0` on the low one. So
at this economy both long-run outcomes are corners. That is a property of this
witness, not of the theory: the general theorem reaches whatever rest point the
economy's own rule generates, at a corner or away from one. -/

/-- **Strict directional adjustment at the dual-basin witness.**

`F(x,s) = (9x + s)/10`, so a sanction below the state strictly lowers it and one
above strictly raises it. Direct from the closed form. -/
theorem dbParams_strictAdjustment : dualParams.StrictAdjustment := by
  constructor
  · intro x s _ _ hsx; rw [dualParams_F]; linarith
  · intro x s _ _ hxs; rw [dualParams_F]; linarith

/-- **Joint Target top-integrand in closed form.** The companion to
`dbCert_joint_T_integrand_eq` for the *upper-selector* integrand the equilibrium
object actually optimizes. Same closed form, because the knife edge cancels the
sanction whatever the selector returns. -/
theorem dbCert_joint_T_top_integrand_eq
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (hV_T : V_T ∈ dbCarrierT)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (a : ℝ) :
    dualParams.joint_T_top_integrand V_T V_S x a
      = 10 * x - 1 / 5 * a + 9 / 10 * V_T (Sanctions.clipS' 0) := by
  simp only [AbstractGame.Params.joint_T_top_integrand]
  exact dbCert_targetObj_const hV_T hx (dualParams.σ_dyn_top_mem_I V_S x a) a

/-- **The equilibrium Target policy is full defiance, at every feasible state.**

Derived from the equilibrium's own Bellman-optimality field `α_opt_top`, not
assumed and not read off a carrier selector: the joint top integrand has exact
compliance slope `−1/5`, so `0` weakly beats `E.α x`, and feasibility gives the
reverse inequality. Rule 1 is satisfied because the policy is an optimization
result of `E` itself. -/
theorem dbCert_E_alpha_eq_zero
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) {x : ℝ} (hx : x ∈ Sanctions.S) : E.α x = 0 := by
  have hxI : x ∈ Set.Icc (0 : ℝ) 1 := hx
  have h : dualParams.joint_T_top_integrand E.V_T E.V_S x 0
      ≤ dualParams.joint_T_top_integrand E.V_T E.V_S x (E.α x) :=
    E.α_opt_top x hx (show (0 : ℝ) ∈ Sanctions.I from ⟨le_rfl, by norm_num⟩)
  rw [dbCert_joint_T_top_integrand_eq hVT E.V_S hxI 0,
    dbCert_joint_T_top_integrand_eq hVT E.V_S hxI (E.α x)] at h
  linarith [(E.α_mem x hx).1]

/-- **On the high basin the equilibrium realized rule sits at the corner.**
The Sender's dynamic objective strictly increases in the sanction there
(`dbCert_senderObj_strictMonoOn_high`) once the Target policy is pinned at full
defiance, so the greatest maximizer is `1`. -/
theorem dbCert_highBasin_rule_eq_one
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) (hVS : E.V_S ∈ dbCarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (19 / 20 : ℝ) 1) :
    dualParams.dynamicTopRealizedRule E.V_S E.α x = 1 := by
  have hxS : x ∈ Sanctions.S := ⟨by linarith [hx.1], hx.2⟩
  change dualParams.σ_dyn_top E.V_S x (E.α x) = 1
  rw [dbCert_E_alpha_eq_zero E hVT hxS]
  exact WitnessKit.σ_dyn_top_eq_one_of_strictMonoOn
    (dbCert_senderObj_strictMonoOn_high hVS hx)

/-- **On the low basin the equilibrium realized rule sits at zero.** The mirror:
the objective strictly decreases in the sanction for every feasible compliance
level, so the greatest maximizer is `0`. -/
theorem dbCert_lowBasin_rule_eq_zero
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ dbCarrierS) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 10)) :
    dualParams.dynamicTopRealizedRule E.V_S E.α x = 0 := by
  have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2 (by norm_num)⟩
  exact WitnessKit.σ_dyn_top_eq_zero_of_strictAntiOn
    (dbCert_senderObj_strictAntiOn_low hVS hx (E.α_mem x hxI).1)

/-- Rule monotonicity on the high basin: constant, hence monotone. -/
theorem dbCert_highBasin_topMono
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) (hVS : E.V_S ∈ dbCarrierS) :
    MonotoneOn (dualParams.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc (19 / 20 : ℝ) 1) := by
  intro y hy z hz _
  rw [dbCert_highBasin_rule_eq_one E hVT hVS hy,
    dbCert_highBasin_rule_eq_one E hVT hVS hz]

/-- Rule monotonicity on the low basin, on the un-clipped interval. -/
theorem dbCert_lowBasin_topMono'
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ dbCarrierS) :
    MonotoneOn (dualParams.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc (0 : ℝ) (1 / 10)) := by
  intro y hy z hz _
  rw [dbCert_lowBasin_rule_eq_zero E hVS hy, dbCert_lowBasin_rule_eq_zero E hVS hz]

/-- High-basin invariance: with the rule at `1`, `G(x) = (9x + 1)/10`, which maps
`[19/20, 1]` into itself. -/
theorem dbCert_highBasin_stepF_mem
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) (hVS : E.V_S ∈ dbCarrierS) :
    ∀ x ∈ Set.Icc (19 / 20 : ℝ) 1,
      dualParams.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc (19 / 20 : ℝ) 1 := by
  intro x hx
  change dualParams.F x (dualParams.dynamicTopRealizedRule E.V_S E.α x) ∈ _
  rw [dbCert_highBasin_rule_eq_one E hVT hVS hx, dualParams_F]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Low-basin invariance: with the rule at `0`, `G(x) = 9x/10`, which maps
`[0, 1/10]` into itself. -/
theorem dbCert_lowBasin_stepF_mem
    (E : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ dbCarrierS) :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / 10),
      dualParams.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc (0 : ℝ) (1 / 10) := by
  intro x hx
  change dualParams.F x (dualParams.dynamicTopRealizedRule E.V_S E.α x) ∈ _
  rw [dbCert_lowBasin_rule_eq_zero E hVS hx, dualParams_F]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **The general attraction theory, applied at one economy.**

At `dualParams` there is a single forward-looking feedback Stackelberg
equilibrium `E` such that every state path started in the low basin `[0, 1/10]`
converges to `0` — state and realized sanction alike — and every state path
started in the high basin `[19/20, 1]` converges to `1`. The initial political
state alone decides which, within one equilibrium rule.

This strengthens `dualParams_initial_condition_selects` from monotone bounded
sequences to **named limits**, and it is short because it does no dynamics: the
convergence is `equilibriumTop_twoBasin_order_selected`, and all this adds is the
rule's value on each basin and the arithmetic pinning the two rest points.

Deleting this economy would remove no general theorem. Rule 9: existence and
non-vacuity only. -/
theorem dualParams_initial_condition_selects_named_limits :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ dbCarrierT ∧ E.V_S ∈ dbCarrierS ∧
      (∀ x₀ ∈ Set.Icc (0 : ℝ) (1 / 10),
        Filter.Tendsto (dualParams.dynamicTopLockInPathF E.V_S E.α x₀)
            Filter.atTop (𝓝 0) ∧
        Filter.Tendsto (dualParams.dynamicTopLockInSanctionsF E.V_S E.α x₀)
            Filter.atTop (𝓝 0)) ∧
      (∀ x₀ ∈ Set.Icc (19 / 20 : ℝ) 1,
        Filter.Tendsto (dualParams.dynamicTopLockInPathF E.V_S E.α x₀)
            Filter.atTop (𝓝 1) ∧
        Filter.Tendsto (dualParams.dynamicTopLockInSanctionsF E.V_S E.α x₀)
            Filter.atTop (𝓝 1)) := by
  obtain ⟨E, hVT, hVS, -, -, -⟩ := dbCert_three_goals_high
  have hbasins : ∀ xL₀ ∈ Set.Icc (0 : ℝ) (1 / 10),
      ∀ xH₀ ∈ Set.Icc (19 / 20 : ℝ) 1, _ :=
    fun xL₀ hxL₀ xH₀ hxH₀ =>
      dualParams.equilibriumTop_twoBasin_order_selected (aL := 0) (bL := 1 / 10)
        (aH := 19 / 20) (bH := 1) dbParams_strictAdjustment E
        (dbCert_DAU_on_carrier hVS) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
        (dbCert_lowBasin_topMono' E hVS) (dbCert_lowBasin_stepF_mem E hVS)
        (dbCert_highBasin_topMono E hVT hVS)
        (dbCert_highBasin_stepF_mem E hVT hVS) hxL₀ hxH₀
  refine ⟨E, hVT, hVS, ?_, ?_⟩
  · intro x₀ hx₀
    obtain ⟨zL, hzLm, zH, -, hzLf, -, hzLp, hzLs, -, -, -⟩ :=
      hbasins x₀ hx₀ 1 ⟨by norm_num, le_rfl⟩
    have hz : zL = 0 := by
      have hfix : dualParams.F zL
          (dualParams.dynamicTopRealizedRule E.V_S E.α zL) = zL := hzLf
      rw [dbCert_lowBasin_rule_eq_zero E hVS hzLm, dualParams_F] at hfix
      linarith
    exact ⟨hz ▸ hzLp, hz ▸ hzLs⟩
  · intro x₀ hx₀
    obtain ⟨zL, -, zH, hzHm, -, hzHf, -, -, hzHp, hzHs, -⟩ :=
      hbasins 0 ⟨le_rfl, by norm_num⟩ x₀ hx₀
    have hz : zH = 1 := by
      have hfix : dualParams.F zH
          (dualParams.dynamicTopRealizedRule E.V_S E.α zH) = zH := hzHf
      rw [dbCert_highBasin_rule_eq_one E hVT hVS hzHm, dualParams_F] at hfix
      linarith
    exact ⟨hz ▸ hzHp, hz ▸ hzHs⟩

/-- **The derived interval is not empty here.**

`equilibriumTop_attraction_up_to_least_steadyState` permits `x_s = x̄`, in which
case the interval it names is a single point and the theorem, while true, says
nothing. This economy shows that case is not the only one: at `dualParams` the
high-basin floor sits strictly above the pivot, so the least steady state above
`19/20` is strictly above it and the derived interval has positive length.

Rule 9: existence only. Note in particular what this does **not** show. The least
steady state here is the corner `1` — the realised rule is pinned there — so this
witnesses positive length, not interiority, and nothing in the development proves
`x_s < 1` at any economy.

Note also why the floor-gap route is available here at all. It is *not* available
on the persistence package's own basin, where
`SenderPersistencePackage.toSenderPersistenceBasinTop` sets pivot and floor both
to `max xT xS`, making the gap hypothesis false. It is available here because the
corner-pinned rule supplies a floor of `1` against a pivot of `19/20`. -/
theorem dualParams_derived_interval_nonEmpty :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ dbCarrierT ∧ E.V_S ∈ dbCarrierS ∧
      ∃ xs ∈ Set.Icc (19 / 20 : ℝ) 1, (19 / 20 : ℝ) < xs ∧
        dualParams.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
        ∀ x₀ ∈ Set.Icc (19 / 20 : ℝ) xs,
          Filter.Tendsto (dualParams.dynamicTopLockInPathF E.V_S E.α x₀)
            Filter.atTop (𝓝 xs) := by
  obtain ⟨E, hVT, hVS, -, -, -⟩ := dbCert_three_goals_high
  refine ⟨E, hVT, hVS, ?_⟩
  have hlevel : ∀ x ∈ Set.Icc (19 / 20 : ℝ) 1,
      max x (1 : ℝ) ≤ dualParams.dynamicTopRealizedRule E.V_S E.α x := by
    intro x hx
    rw [dbCert_highBasin_rule_eq_one E hVT hVS hx, max_eq_right hx.2]
  exact dualParams.equilibriumTop_least_steadyState_gt_pivot_of_floor
    dbParams_strictAdjustment E (dbCert_DAU_on_carrier hVS) (by norm_num)
    (by norm_num) (dbCert_highBasin_topMono E hVT hVS) hlevel (by norm_num)

/-- **The dividing line between the two basins, derived at this economy.**

`dualParams_initial_condition_selects_named_limits` certifies two basins that
were *chosen*: `[0, 1/10]` and `[19/20, 1]`. Between them the development said
nothing — the realised rule is pinned only on the two certified intervals, and
across the middle neither its sign nor its monotonicity is known.

This closes most of that middle, and closes it without learning anything new
about the rule there. The only facts used are the two already proved at the ends
(the rule is `0` on the low basin and `1` on the high one) and continuity of the
realised rule on the whole state space, which `dbCert_DAU_on_carrier` — single-
valuedness of the Sender's dynamic argmax at every state — already supplies.
`equilibriumTop_derived_dual_basins` then extracts two steady states `t ≤ t'`
from the equilibrium closed loop itself (since round BH-2, 2026-10-06, through
its unit-interval corollary `equilibriumTop_derived_dual_basins_unit`, so the
endpoint fixations `G(0) = 0`, `G(1) = 1` and the "closed loop maps `[0, 1]` into
itself" bounds are no longer supplied here: they follow from continuity, the
strict drifts and feasibility), and:

* every equilibrium state path started **anywhere below `t`** washes out to `0`;
* every equilibrium state path started **anywhere above `t'`** ratchets to `1`;
* `t = t'` exactly when the middle region holds a single steady state, in which
  case one derived line divides the whole unit interval.

So the two basins are no longer `[0, 1/10]` and `[19/20, 1]` but `[0, t)` and
`(t', 1]`, with the new endpoints read off the equilibrium instead of assumed.

Rule 9: existence only. This exhibits one economy at which the derivation is
non-vacuous. It says nothing about where `t` sits at other economies, nor that
`t = t'` here — the theorem reports the gap rather than closing it, because
closing it needs a uniqueness fact about the middle region that this economy has
not been shown to have. The claim is about the **state** path; the realised
sanction is not tracked. -/
theorem dualParams_derived_dividing_line :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ dbCarrierT ∧ E.V_S ∈ dbCarrierS ∧
      ∃ t ∈ Set.Ioc (1 / 10 : ℝ) (19 / 20), ∃ t' ∈ Set.Ico (1 / 10 : ℝ) (19 / 20),
        t ≤ t' ∧
        dualParams.dynamicTopLockInStepF E.V_S E.α t = t ∧
        dualParams.dynamicTopLockInStepF E.V_S E.α t' = t' ∧
        (∀ x₀ ∈ Set.Ico (0 : ℝ) t,
          Filter.Tendsto (dualParams.dynamicTopLockInPathF E.V_S E.α x₀)
            Filter.atTop (𝓝 0)) ∧
        (∀ x₀ ∈ Set.Ioc t' (1 : ℝ),
          Filter.Tendsto (dualParams.dynamicTopLockInPathF E.V_S E.α x₀)
            Filter.atTop (𝓝 1)) ∧
        (t = t' ↔ ∀ y ∈ Set.Icc (1 / 10 : ℝ) (19 / 20),
          ∀ z ∈ Set.Icc (1 / 10 : ℝ) (19 / 20),
          dualParams.dynamicTopLockInStepF E.V_S E.α y = y →
          dualParams.dynamicTopLockInStepF E.V_S E.α z = z → y = z) := by
  obtain ⟨E, hVT, hVS, -, -, -⟩ := dbCert_three_goals_high
  refine ⟨E, hVT, hVS, ?_⟩
  -- the realised rule is continuous on the whole state space (argmax uniqueness)
  have hcont : ContinuousOn (dualParams.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc (0 : ℝ) 1) :=
    dualParams.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E
      (dbCert_DAU_on_carrier hVS) (fun y hy => hy)
  -- strict erosion on the certified low basin, strict building on the high one
  have hlow : ∀ x ∈ Set.Ioc (0 : ℝ) (1 / 10),
      dualParams.dynamicTopLockInStepF E.V_S E.α x < x := by
    intro x hx
    change dualParams.F x (dualParams.dynamicTopRealizedRule E.V_S E.α x) < x
    rw [dbCert_lowBasin_rule_eq_zero E hVS ⟨le_of_lt hx.1, hx.2⟩, dualParams_F]
    linarith [hx.1]
  have hhigh : ∀ x ∈ Set.Ico (19 / 20 : ℝ) 1,
      x < dualParams.dynamicTopLockInStepF E.V_S E.α x := by
    intro x hx
    change x < dualParams.F x (dualParams.dynamicTopRealizedRule E.V_S E.α x)
    rw [dbCert_highBasin_rule_eq_one E hVT hVS ⟨hx.1, le_of_lt hx.2⟩, dualParams_F]
    linarith [hx.2]
  exact dualParams.equilibriumTop_derived_dual_basins_unit E (by norm_num) (by norm_num)
    (by norm_num) hcont hlow hhigh

/-! ## Within-carrier uniqueness (Schur route, 2026-07-24) -/

/-- Schur-certificate inhabitant at the dual-basin witness, via the
row-sum ⇒ Schur bridge (decoupled rows: `L_TS·L_ST = 0 < (1/10)·(1/2)`). -/
noncomputable def dbCertCertificateSchur :
    dualParams.StandardComplianceLocalCoreCertificateSchur :=
  AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur.ofRowSum
    dualParams dbCertCertificate

/-- **Witness within-carrier uniqueness at the dual-basin economy.**
Any two top-selector feedback Stackelberg equilibria with carrier values
and selector-coinciding policies agree in both value functions and the
policy; every quantitative input is machine-discharged by
`dbCertCertificate`. Note this is uniqueness within the HIGH-side
carrier class — the economy's dual-basin path dependence
(initial-condition selection between basins) is across classes, not
within one. -/
theorem dbCert_unique_in_carrier
    (E E' : dualParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) (hVS : E.V_S ∈ dbCarrierS)
    (hVT' : E'.V_T ∈ dbCarrierT) (hVS' : E'.V_S ∈ dbCarrierS)
    (hαE : E.α = dbClass.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = dbClass.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  dbCertCertificate.unique_in_carrier (p := dualParams)
    E E' hVT hVS hVT' hVS' hαE hαE'

end -- noncomputable section

#print axioms dbCertCertificate
#print axioms dbCertCertificateSchur
#print axioms dbCert_unique_in_carrier
#print axioms dbCert_three_goals_high
#print axioms dbCert_three_goals_low
#print axioms dualParams_initial_condition_selects
#print axioms dualParams_initial_condition_selects_named_limits
#print axioms dualParams_derived_interval_nonEmpty
#print axioms dualParams_derived_dividing_line

end Examples

end Sanctions
