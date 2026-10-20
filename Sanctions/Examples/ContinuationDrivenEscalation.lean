/-
Sanctions/Examples/ContinuationDrivenEscalation.lean

**A deterministic economy whose continuation channel is load-bearing for strict
escalation — and whose Target likes being sanctioned.**

Both halves of that sentence are stated as theorems below.  This file settles
one thing and deliberately fails to settle another; read the two together.

## WHAT IS SETTLED

`Examples/DeterministicStrictEscalation.lean` exhibits a deterministic economy
with strictly escalating equilibrium sanctions, but `ni_continuation_channel_inactive`
there proves both equilibrium value functions are identically `0` at that
witness: every `β · V(…)` term vanishes, so the escalation there is *transition
geometry*, not a *continuation motive*.

Here the continuation channel is active and load-bearing.  The economy
`ceParams` is deterministic (`F x s = (x + s)/2`, no kernel, no shock phase);
the stationary equilibrium `ceEquilibrium` is **constructed**, not consumed, and
both of its value functions are the identity on `[0,1]` — bounded, continuous,
and *strictly increasing* (`ce_V_S_strictMono`, `ce_V_T_strictMono`), hence not
zero (`ceVid_ne_zero`).  At every feasible state the equilibrium sanction
exceeds the Sender's stage argmax by exactly `1/8` (`ce_wedge`).  Deleting the
Sender's continuation term from its argmax — a *partial counterfactual*, see
the scope limits below — returns exactly the stage argmax
(`ce_zero_rule_eq_stage`); on `(1/2, 3/4)` that stage rule lies strictly below
the diagonal, so the state strictly **decays** (`ce_zero_path_strictAnti`) on
the very interval where the equilibrium path strictly **escalates**
(`ce_strict_escalation`).

One implication is worth recording as refuted, with its cheapness stated.
`Theory/LockIn/EscalationGap.exists_small_drift_of_invariant` forces the
closed-loop drift to come arbitrarily close to zero somewhere on any
forward-invariant half-open interval.  One might guess that this forces the
Sender's continuation value to be *flat* there — that a shrinking gap and a
non-constant `V_S` are incompatible.  They are not: `ce_V_S_strictMono` and
`ce_V_S_not_constant_on_invariant_interval` exhibit a strictly increasing `V_S`
on an invariant interval whose *escalation* gap `(3/4 − x)/2` (`ce_gap_eq`) does
shrink to zero at the top.  The gap is a property of the closed loop's *slope*;
the value is a property of its *level*.

Two honest qualifications.  First, this economy's `V_S` is the identity by
construction, so the refutation costs nothing here — it disproves an
implication, which needs only one instance, but it should not be read as a
hard-won result.  Second, the guess being refuted is stated here for the first
time; no part of this project ever asserted it.  Nothing above is a correction
of a prior project claim.

(Note the distinction the earlier draft of this header blurred: `(3/4 − x)/2` is
the **escalation** gap `R x − x`.  The **drift** `stepF x − x` is
`(3/4 − x)/4`, half of it, since `δ = 1/2`.  Both shrink to zero at the top, so
the qualitative point is unaffected, but the two are not the same quantity.)

## WHAT IS NOT SETTLED

**This witness is a common-interest game, and that is a deeper limitation than
the Target's sanction preference alone.**  Three separate facts, each a theorem
(`ce_common_interest`, `ce_target_prefers_sanctions`):

* `∂U_T/∂s = +1` identically — the Target is made strictly better off by a
  heavier sanction at every state and compliance level, with **no stage loss to
  offset** the continuation gain.
* `∂U_S/∂x = +5/8 > 0` — the Sender is made better off by a *more defiant*
  Target.  This is the `ceG` term, and it is not incidental: it is the sole
  reason `V_S` is strictly increasing and therefore the sole source of the
  `+1/8` continuation wedge that this entire file exists to exhibit.
* `ceEquilibrium.V_S = ceEquilibrium.V_T` (by `rfl`), and both players' realised
  stage payoffs are the *same real number* at every date along the equilibrium
  path.

So the players' interests are aligned, not opposed.  Both realised stage-payoff
sequences rise along the escalating path — note that this follows from the two
gradient facts *jointly*, not from `∂U_T/∂s = +1` alone: the Sender's rise comes
entirely from `ceG`.  What is exhibited is **mutually agreeable escalation, not
a sanctions conflict**.

A precision about "Pareto-improving": what is proved is time-monotonicity of
each player's realised stage payoff along one path, not a Pareto ranking of
escalation against an alternative.  Read cross-sectionally the Sender is
strictly *worse* off in stage terms at the equilibrium sanction than at its own
stage argmax — by exactly `1/64` at every feasible state, which is precisely the
price it pays for the wedge.

Contrast the project's conflict witnesses, where the sanction genuinely hurts
the Target:

* `Examples/EatonEngersWitness.eeU_T` and `Examples/MechanismWitness.mwU_T` have
  `∂U_T/∂s = −(1/2 − a/2 − x)`, which is *negative* at low states and turns
  positive only once the target is entrenched — that sign flip **is** the rally
  mechanism those files model;
* `Examples/B2NonMonotoneCertWitness.b2U_T` has `∂U_T/∂s = −7/4 < 0` throughout.

So this file does **not** exhibit continuation-driven escalation in a genuine
sanctions conflict.  Whether such a witness exists under determinism is **open**;
nothing here settles it, and no claim in this file should be read as doing so.

**Update (round BB, 2026-09-28).** Another file settles the wedge form of it.
The chord class (`ChordEconomy`, deterministic, general in `F`) has a genuine
conflict in the sense above: a sanction hurts the Target at the stage by at
least `p_lo > 0` per unit (field T5). There, `both_channels_active_of_margin`
(headline row 32, `Examples/PlacableSenderEquilibrium.lean`) shows, under its
margins, that at every state of the constructed equilibrium the continuation
changes both players' choices. The Sender's forward-looking sanction is never
a stage optimum, and it is at least the stage one (`response_ge_stage`), so it
lies strictly above it.
A non-affine member has it (`placableQuadDiag_both_channels_active`, row 33).
Row 32 does not state this file's other fact, a strictly escalating equilibrium
path set against a decaying channel-off path.

## TWO FURTHER SCOPE LIMITS

**The "channel off" comparison is a partial Sender-side counterfactual, not an
equilibrium of a different game.**  Every statement about
`dynamicTopRealizedRule 0 E.α` — `ce_zero_rule_eq`, `ce_zero_rule_eq_stage`,
`ce_zero_rule_lt_self`, `ce_zero_stepF_eq`, `ce_zero_path_mem`,
`ce_zero_path_strictAnti`, and the last three conjuncts of the headline —
substitutes `V_S := 0` inside the Sender's argmax while holding the economy, the
Target's policy `ceAlpha`, and `V_T` fixed.  No myopic game is solved and
`ceAlpha` is not re-optimised against the myopic rule.  It isolates the Sender's
continuation term; it does not describe another economy's equilibrium.

**Escalation is bounded.**  The closed loop has fixed point `3/4`
(`ce_top_fixed`) and escalation gap `(3/4 − x)/2` (`ce_gap_eq`), which tends to
`0`.  The state and the sanction rise strictly at every date and converge; the
sanction never reaches the feasibility ceiling (`ce_sanction_lt_one`).  No
unbounded-escalation reading is licensed.

## RULE COMPLIANCE

Rule 1: `ceAlpha` is the unique argmax of the joint top integrand, which is
strictly concave in `a` (`ce_joint_eq`, `ce_target_policy_optimal`); the
realised rule is the Sender's greatest forward-looking maximiser; `ceSigma` is
coupled to `U_S` as the stage argmax.  No assumed constant strategy anywhere.
Rule 15: `ceEquilibrium` is a `def` whose every field is discharged by a proved
equation; no fixed point is consumed as a hypothesis.
Rule 3: no new `Params` field, no new hypothesis on any existing theorem, no
load-bearing `Prop` taken as hypothesis.
Exact rationals throughout; no `decide`, no `native_decide`, no decimal literal.
-/

import Sanctions.Theory.LockIn.EscalationGap
import Sanctions.Theory.LockIn.DynamicStake
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Mechanism.ContinuationChangesChoice

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame AbstractGame.Params

noncomputable section

/-! ## Primitives -/

/-- Sender's *stage* ideal sanction (vertex of the stage payoff). -/
def ceIdeal (x a : ℝ) : ℝ := x / 2 + 3 / 8 - a / 4

/-- The forward-looking (equilibrium) sanction: the stage ideal shifted up
by the continuation wedge `1/8`. -/
def ceR (x a : ℝ) : ℝ := x / 2 + 1 / 2 - a / 4

/-- State-dependent level of the Sender stage payoff, with slope `+5/8`.

**This is the witness's load-bearing defect, not a feature** — see
`ce_common_interest`.  It makes the Sender's stage payoff, and hence its
continuation value, *rise* with the Target's hardline state: the Sender is
better off facing a more defiant Target.  That is the sole reason `V_S` is
strictly increasing, and therefore the sole source of the `+1/8` continuation
wedge this file exists to exhibit.  Remove it and the wedge vanishes.

No citation is offered for it.  An earlier draft justified the sign by a
Kaempfer–Lowenberg public-choice reading; the project's own summary of that
paper (`PaperRefer/Sanctions/TheoryOfInternationalEconomicSanctions-KaempferLowenberg-1988.md`)
supports only the weaker claim that sanctions are adopted for the sender's
domestic distributional reasons regardless of effectiveness, and treats target
rally-round-the-flag as an *obstacle* to the sender rather than a gain.  The
sign here is a modelling choice made to obtain the wedge, and it should be read
as such. -/
def ceG (x : ℝ) : ℝ := 5 / 8 * x - 5 / 64

def ceU_S (x a s : ℝ) : ℝ := -(s - ceIdeal x a) ^ 2 + ceG x

/-- Target stage payoff.  `∂U_T/∂a = −2(a − 1/2) + 5/16` (strictly concave in
compliance, vertex `21/32`) and `∂U_T/∂s = +1` — **positive**, so this Target is
made better off by a heavier sanction.  That is a defect of the witness, not a
feature; it is recorded as a theorem in `ce_target_prefers_sanctions`. -/
def ceU_T (x a s : ℝ) : ℝ :=
  -(a - 1 / 2) ^ 2 + 5 / 16 * (a - 1 / 2) + s + x / 8 - 15 / 32

def ceSigma (x a : ℝ) : ℝ := Sanctions.clipS (ceIdeal x a)

theorem ceSigma_mem (x a : ℝ) : ceSigma x a ∈ Set.Icc (0 : ℝ) 1 :=
  Sanctions.clipS_mem _

theorem ceSigma_continuous :
    Continuous (fun xa : ℝ × ℝ => ceSigma xa.1 xa.2) := by
  unfold ceSigma
  apply Sanctions.clipS_continuous.comp
  unfold ceIdeal
  fun_prop

theorem ceU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => ceU_S xas.1 xas.2.1 xas.2.2) := by
  unfold ceU_S ceIdeal ceG; fun_prop

theorem ceU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => ceU_T xas.1 xas.2.1 xas.2.2) := by
  unfold ceU_T; fun_prop

theorem ceSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => ceU_S x a s) Sanctions.I (ceSigma x a) := by
  refine WitnessKit.clipVertex_isMaxOn (k := (1 : ℝ)) (C := ceG x)
    (t := ceIdeal x a) (U := fun s => ceU_S x a s) (by norm_num) ?_
  intro s
  simp [ceU_S]
  ring

/-- The economy.  Deterministic: `F` is the ordinary function
`F x s = (x + s)/2`, no kernel and no exogenous segment anywhere. -/
def ceParams : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 1 / 2
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := ceU_T
  U_S := ceU_S
  σ := ceSigma
  σ_mem := ceSigma_mem
  σ_isMaxOn_U_S := ceSigma_isMaxOn
  U_T_continuous := ceU_T_continuous
  U_S_continuous := ceU_S_continuous
  F := AbstractGame.affineF (1 / 2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x (by constructor <;> norm_num)
  F_mono_s := AbstractGame.affineF_mono_s (by constructor <;> norm_num)
  F_diag := AbstractGame.affineF_diag _

/-- **`ceParams` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance ceParams_staticSelectorContinuous :
    ceParams.StaticSelectorContinuous where
  σ_continuous := ceSigma_continuous

@[simp] theorem ceParams_U_S : ceParams.U_S = ceU_S := rfl
@[simp] theorem ceParams_U_T : ceParams.U_T = ceU_T := rfl
@[simp] theorem ceParams_σ : ceParams.σ = ceSigma := rfl
@[simp] theorem ceParams_β_S : ceParams.β_S = 1 / 2 := rfl
@[simp] theorem ceParams_β_T : ceParams.β_T = 1 / 2 := rfl
@[simp] theorem ceParams_δ : ceParams.δ = 1 / 2 := rfl

theorem ceF_eq (x s : ℝ) : ceParams.F x s = (x + s) / 2 := by
  change AbstractGame.affineF (1 / 2) x s = _
  unfold AbstractGame.affineF
  ring

theorem ceParams_F_strictMono_s (x : ℝ) : StrictMono (fun s => ceParams.F x s) := by
  intro s₁ s₂ h
  change ceParams.F x s₁ < ceParams.F x s₂
  rw [ceF_eq, ceF_eq]
  linarith

/-! ## The continuation values -/

/-- The identity value function on `[0,1]`.  Serves as **both** equilibrium
value functions: bounded, continuous, and strictly increasing. -/
def ceVid : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun z : ↥(Sanctions.S : Set ℝ) => (z.val : ℝ)) (by fun_prop))

theorem ceVid_apply (z : ↥(Sanctions.S : Set ℝ)) : ceVid z = z.val := rfl

theorem ceVid_clip {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ceVid (Sanctions.clipS' y) = y :=
  Sanctions.clipS'_val_eq_of_mem hy

def ceAlpha (_x : ℝ) : ℝ := 1 / 2

theorem ceAlpha_continuous : Continuous ceAlpha := continuous_const

theorem ceAlpha_mem (x : ℝ) : ceAlpha x ∈ Sanctions.I := by
  constructor <;> norm_num [ceAlpha]

theorem ce_half_mem : (1 / 2 : ℝ) ∈ Sanctions.I := by constructor <;> norm_num

/-! ## The Sender's forward-looking argmax -/

theorem ceR_mem {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    ceR x a ∈ Sanctions.I := by
  constructor <;> · unfold ceR; linarith [hx.1, hx.2, ha.1, ha.2]

theorem ceIdeal_mem {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    ceIdeal x a ∈ Sanctions.I := by
  constructor <;> · unfold ceIdeal; linarith [hx.1, hx.2, ha.1, ha.2]

/-- On the feasible rectangle the Sender's stage selector is unclipped: it
equals the raw vertex `ceIdeal`. -/
theorem ceSigma_eq_ideal {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    ceParams.σ x a = ceIdeal x a :=
  Sanctions.clipS'_val_eq_of_mem (ceIdeal_mem hx ha)

/-- The Sender's *forward-looking* objective is maximised on `[0,1]` at
`ceR x a` — the stage ideal plus the continuation wedge `1/8`. -/
theorem ce_dyn_isMaxOn {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    IsMaxOn (fun s => ceParams.U_S x a s
        + ceParams.β_S * ceVid (Sanctions.clipS' (ceParams.F x s)))
      Sanctions.I (ceR x a) := by
  rw [isMaxOn_iff]
  intro s hs
  have hRmem : ceR x a ∈ Sanctions.I := ceR_mem hx ha
  have hm1 : (x + s) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩
  have hm2 : (x + ceR x a) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, hRmem.1], by linarith [hx.2, hRmem.2]⟩
  change ceParams.U_S x a s + ceParams.β_S * ceVid (Sanctions.clipS' (ceParams.F x s))
      ≤ ceParams.U_S x a (ceR x a)
        + ceParams.β_S * ceVid (Sanctions.clipS' (ceParams.F x (ceR x a)))
  rw [ceF_eq, ceF_eq, ceVid_clip hm1, ceVid_clip hm2, ceParams_U_S, ceParams_β_S]
  unfold ceU_S ceIdeal ceG ceR
  nlinarith [sq_nonneg (s - (x / 2 + 1 / 2 - a / 4))]

/-- The upper dynamic argmax is exactly `ceR x a`.  The forward-looking
objective is strictly concave in `s`, so its argmax is a singleton at every
state and the greatest selector `σ_dyn_top` coincides with it. -/
theorem ce_top_eq {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    ceParams.σ_dyn_top ceVid x a = ceR x a := by
  have hRmem : ceR x a ∈ Sanctions.I := ceR_mem hx ha
  have htop_mem := ceParams.σ_dyn_top_mem_I ceVid x a
  have hmax := ceParams.σ_dyn_top_isMaxOn ceVid x a
  rw [isMaxOn_iff] at hmax
  have hcomp := hmax (ceR x a) hRmem
  set T := ceParams.σ_dyn_top ceVid x a with hT
  have hm1 : (x + T) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, htop_mem.1], by linarith [hx.2, htop_mem.2]⟩
  have hm2 : (x + ceR x a) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, hRmem.1], by linarith [hx.2, hRmem.2]⟩
  have hcomp' : ceU_S x a (ceR x a) + (1 / 2 : ℝ) * ((x + ceR x a) / 2)
      ≤ ceU_S x a T + (1 / 2 : ℝ) * ((x + T) / 2) := by
    have := hcomp
    rw [ceF_eq, ceF_eq, ceVid_clip hm1, ceVid_clip hm2, ceParams_U_S,
      ceParams_β_S] at this
    exact this
  unfold ceU_S ceIdeal ceG ceR at hcomp'
  unfold ceR
  nlinarith [sq_nonneg (T - (x / 2 + 1 / 2 - a / 4))]

/-! ## The Sender Bellman fixed point (Rule 15: constructed, not consumed) -/

theorem ce_sender_value_fix :
    ceVid = ceParams.bellmanS_BCF ceAlpha ceAlpha_continuous ceVid := by
  ext y
  have hy : y.val ∈ Sanctions.S := y.property
  have hhalf : (1 / 2 : ℝ) ∈ Sanctions.I := ceAlpha_mem 0
  have hRmem : ceR y.val (1 / 2) ∈ Sanctions.I := ceR_mem hy hhalf
  have hmax : IsMaxOn
      (fun s => ceParams.U_S y.val (ceAlpha y.val) s
        + ceParams.β_S * ceVid (Sanctions.clipS' (ceParams.F y.val s)))
      Sanctions.I (ceR y.val (1 / 2)) := ce_dyn_isMaxOn hy hhalf
  have himage := WitnessKit.bellmanS_image_of_isMaxOn
    (p := ceParams) ceAlpha_continuous ceVid y hRmem hmax
  change (y.val : ℝ) = ceParams.bellmanS_BCF ceAlpha ceAlpha_continuous ceVid y
  rw [himage]
  have hm2 : (y.val + ceR y.val (1 / 2)) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hy.1, hRmem.1], by linarith [hy.2, hRmem.2]⟩
  rw [ceF_eq, ceVid_clip hm2, ceParams_U_S, ceParams_β_S]
  unfold ceU_S ceIdeal ceG ceR ceAlpha
  ring

/-! ## The Target side -/

theorem ce_joint_eq {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    ceParams.joint_T_top_integrand ceVid ceVid x a = -(a - 1 / 2) ^ 2 + x := by
  have hRmem : ceR x a ∈ Sanctions.I := ceR_mem hx ha
  have hm2 : (x + ceR x a) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, hRmem.1], by linarith [hx.2, hRmem.2]⟩
  change ceParams.U_T x a (ceParams.σ_dyn_top ceVid x a)
      + ceParams.β_T * ceVid (Sanctions.clipS'
          (ceParams.F x (ceParams.σ_dyn_top ceVid x a))) = _
  rw [ce_top_eq hx ha, ceF_eq, ceVid_clip hm2, ceParams_U_T, ceParams_β_T]
  unfold ceU_T ceR
  ring

theorem ce_target_policy_optimal {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn (fun a => ceParams.joint_T_top_integrand ceVid ceVid x a)
      Sanctions.I (ceAlpha x) := by
  rw [isMaxOn_iff]
  intro a ha
  rw [ce_joint_eq hx ha]
  change _ ≤ ceParams.joint_T_top_integrand ceVid ceVid x (1 / 2)
  rw [ce_joint_eq hx ce_half_mem]
  nlinarith [sq_nonneg (a - 1 / 2)]

theorem ce_target_value_fix_top (x : ↥(Sanctions.S : Set ℝ)) :
    ceVid x = sSup ((fun a => ceParams.joint_T_top_integrand ceVid ceVid x.val a)
      '' Sanctions.I) := by
  have hx : x.val ∈ Sanctions.S := x.property
  have hgreatest : IsGreatest
      ((fun a => ceParams.joint_T_top_integrand ceVid ceVid x.val a) '' Sanctions.I)
      (ceParams.joint_T_top_integrand ceVid ceVid x.val (1 / 2)) := by
    constructor
    · exact ⟨1 / 2, ceAlpha_mem 0, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ce_target_policy_optimal hx ha
  rw [hgreatest.csSup_eq, ce_joint_eq hx ce_half_mem]
  change (x.val : ℝ) = _
  ring

/-- **The constructed stationary equilibrium.**  Every field is discharged by
a proved equation: no fixed point is hypothesised (Rule 15). -/
def ceEquilibrium : ceParams.FeedbackStackelbergEquilibriumTop where
  V_T := ceVid
  V_S := ceVid
  α := ceAlpha
  hα := ceAlpha_continuous
  α_mem := fun x _ => ceAlpha_mem x
  V_S_fix := ce_sender_value_fix
  V_T_fix_top := ce_target_value_fix_top
  α_opt_top := fun _ hx => ce_target_policy_optimal hx

/-! ## The three escalation conditions -/

theorem ce_realized_rule_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x
      = x / 2 + 3 / 8 := by
  change ceParams.σ_dyn_top ceVid x (ceAlpha x) = _
  rw [ceAlpha, ce_top_eq hx ce_half_mem]
  unfold ceR
  ring

theorem ce_stepF_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopLockInStepF ceEquilibrium.V_S ceEquilibrium.α x
      = 3 * x / 4 + 3 / 16 := by
  unfold AbstractGame.Params.dynamicTopLockInStepF
  rw [ce_realized_rule_eq hx, ceF_eq]
  ring

/-- **(i)** the rule lies strictly above the diagonal on `[a, 3/4)`. -/
theorem ce_rule_gt_self {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Set.Ico a (3 / 4)) :
    x < ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x := by
  rw [ce_realized_rule_eq ⟨le_trans ha hx.1, by linarith [hx.2]⟩]
  linarith [hx.2]

/-- **(ii)** the rule is strictly increasing on `[a, 3/4)`. -/
theorem ce_rule_strictMonoOn {a : ℝ} (ha : 0 ≤ a) :
    StrictMonoOn
      (ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α)
      (Set.Ico a (3 / 4)) := by
  intro u hu v hv huv
  rw [ce_realized_rule_eq ⟨le_trans ha hu.1, by linarith [hu.2]⟩,
      ce_realized_rule_eq ⟨le_trans ha hv.1, by linarith [hv.2]⟩]
  linarith

/-- **(iii)** `[a, 3/4)` is forward invariant under the equilibrium closed loop. -/
theorem ce_stepF_mem {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Set.Ico a (3 / 4)) :
    ceParams.dynamicTopLockInStepF ceEquilibrium.V_S ceEquilibrium.α x
      ∈ Set.Ico a (3 / 4) := by
  rw [ce_stepF_eq ⟨le_trans ha hx.1, by linarith [hx.2]⟩]
  exact ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩

/-- The whole equilibrium closed-loop path from a state of `[a, 3/4)` stays in
`[a, 3/4)`, by iterating the forward-invariance step `ce_stepF_mem`. -/
theorem ce_path_mem {a x₀ : ℝ} (ha : 0 ≤ a) (hx₀ : x₀ ∈ Set.Ico a (3 / 4)) (n : ℕ) :
    ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n
      ∈ Set.Ico a (3 / 4) := by
  induction n with
  | zero => simpa using hx₀
  | succ k ih => rw [dynamicTopLockInPathF_succ]; exact ce_stepF_mem ha ih

/-- **Strict escalation** — one-line application of the parametric
`dynamicTopLockInPathF_strictMono_of_gt_self` /
`dynamicTopLockInSanctionsF_strictMono_of_gt_self`, through their
`_of_strictMono_s` forms: `ceParams`' transition is strictly increasing in the
sanction at every state, which gives the local upward adjustment those
theorems ask for since BG2.3. -/
theorem ce_strict_escalation {a x₀ : ℝ} (ha : 0 ≤ a) (hx₀ : x₀ ∈ Set.Ico a (3 / 4)) :
    StrictMono
        (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀)
    ∧ StrictMono
        (ceParams.dynamicTopLockInSanctionsF ceEquilibrium.V_S ceEquilibrium.α x₀) :=
  ⟨ceParams.dynamicTopLockInPathF_strictMono_of_gt_self_of_strictMono_s
      ceEquilibrium.V_S ceEquilibrium.α ceParams_F_strictMono_s
      (fun _ hx => ce_rule_gt_self ha hx) (fun _ hx => ce_stepF_mem ha hx) hx₀,
   ceParams.dynamicTopLockInSanctionsF_strictMono_of_gt_self_of_strictMono_s
      ceEquilibrium.V_S ceEquilibrium.α ceParams_F_strictMono_s
      (fun _ hx => ce_rule_gt_self ha hx) (fun _ hx => ce_stepF_mem ha hx)
      (ce_rule_strictMonoOn ha) hx₀⟩

/-- The escalation is not confined to the contrast window: it holds from *every*
starting state strictly below the fixed point `3/4`. -/
theorem ce_strict_escalation_full_basin {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) (3 / 4)) :
    StrictMono
        (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀)
    ∧ StrictMono
        (ceParams.dynamicTopLockInSanctionsF ceEquilibrium.V_S ceEquilibrium.α x₀) :=
  ce_strict_escalation (a := 0) le_rfl hx₀

/-! ## The continuation channel is active

The comparisons in this section are **partial Sender-side counterfactuals**:
they replace `V_S` by `0` inside the Sender's forward-looking argmax while
holding the economy `ceParams`, the Target's policy `ceEquilibrium.α`, and `V_T`
fixed.  They do not re-solve the game and are not the equilibrium of a myopic
economy. -/

theorem ceVid_ne_zero : ceVid ≠ 0 := by
  intro h
  have h1 : ceVid ⟨1, by constructor <;> norm_num⟩ = (0 : ℝ) := by rw [h]; rfl
  rw [ceVid_apply] at h1
  norm_num at h1

/-- **The stage (myopic) sanction.** -/
theorem ce_stage_rule_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.σ x (ceEquilibrium.α x) = x / 2 + 1 / 4 := by
  change ceSigma x (ceAlpha x) = _
  unfold ceSigma ceAlpha
  rw [show Sanctions.clipS (ceIdeal x (1/2)) = ceIdeal x (1/2) from
    Sanctions.clipS'_val_eq_of_mem (ceIdeal_mem hx ce_half_mem)]
  unfold ceIdeal
  ring

/-- **The continuation wedge.**  The equilibrium (forward-looking) sanction
exceeds the Sender's stage argmax by exactly `1/8` at every feasible state. -/
theorem ce_wedge {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x
      = ceParams.σ x (ceEquilibrium.α x) + 1 / 8 := by
  rw [ce_realized_rule_eq hx, ce_stage_rule_eq hx]
  ring

/-- **Partial Sender-side counterfactual.**  Setting `V_S := 0` inside the
Sender's forward-looking argmax — everything else, including `ceEquilibrium.α`
and `V_T`, held fixed — returns exactly the stage argmax `x/2 + 1/4`.  This is
not the equilibrium of a myopic game. -/
theorem ce_zero_rule_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopRealizedRule 0 ceEquilibrium.α x = x / 2 + 1 / 4 := by
  have hhalf : (1 / 2 : ℝ) ∈ Sanctions.I := ceAlpha_mem 0
  have hImem : ceIdeal x (1 / 2) ∈ Sanctions.I := ceIdeal_mem hx hhalf
  have htop_mem := ceParams.σ_dyn_top_mem_I
    (0 : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) x (ceAlpha x)
  have hmax := ceParams.σ_dyn_top_isMaxOn
    (0 : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) x (ceAlpha x)
  rw [isMaxOn_iff] at hmax
  have hcomp := hmax (ceIdeal x (1 / 2)) hImem
  change ceParams.σ_dyn_top 0 x (ceAlpha x) = _
  set T := ceParams.σ_dyn_top
    (0 : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) x (ceAlpha x) with hT
  have hcomp' : ceU_S x (1 / 2) (ceIdeal x (1 / 2)) ≤ ceU_S x (1 / 2) T := by
    have := hcomp
    simp only [ceAlpha, ceParams_U_S, ceParams_β_S,
      BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero] at this
    exact this
  unfold ceU_S ceIdeal at hcomp'
  nlinarith [sq_nonneg (T - (x / 2 + 3 / 8 - 1 / 8))]

/-- **Partial Sender-side counterfactual.**  With `V_S := 0` in the Sender's
argmax the realised rule is exactly the Sender's *stage* argmax `p.σ`.  Again:
`ceEquilibrium.α` is held fixed and is *not* re-optimised against this rule, so
this is not an equilibrium of a myopic economy. -/
theorem ce_zero_rule_eq_stage {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopRealizedRule 0 ceEquilibrium.α x
      = ceParams.σ x (ceEquilibrium.α x) := by
  rw [ce_zero_rule_eq hx, ce_stage_rule_eq hx]

/-- **Partial Sender-side counterfactual.**  With `V_S := 0` the rule lies
strictly **below** the diagonal on `(1/2, 3/4)`: the state would strictly decay
if the Sender's continuation term were deleted and nothing else changed. -/
theorem ce_zero_rule_lt_self {x : ℝ} (hx : x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4)) :
    ceParams.dynamicTopRealizedRule 0 ceEquilibrium.α x < x := by
  rw [ce_zero_rule_eq ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  linarith [hx.1]

theorem ce_zero_stepF_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopLockInStepF 0 ceEquilibrium.α x = 3 * x / 4 + 1 / 8 := by
  unfold AbstractGame.Params.dynamicTopLockInStepF
  rw [ce_zero_rule_eq hx, ceF_eq]
  ring

theorem ce_zero_path_mem {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4)) (n : ℕ) :
    ceParams.dynamicTopLockInPathF 0 ceEquilibrium.α x₀ n
      ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4) := by
  induction n with
  | zero => simpa using hx₀
  | succ k ih =>
    rw [dynamicTopLockInPathF_succ,
      ce_zero_stepF_eq ⟨by linarith [ih.1], by linarith [ih.2]⟩]
    exact ⟨by linarith [ih.1], by linarith [ih.2]⟩

/-- **The partial Sender-side counterfactual strictly decays** on the very
interval where the equilibrium path strictly escalates.  The counterfactual
loop deletes `V_S` from the Sender's argmax and holds everything else — the
economy, `ceEquilibrium.α`, `V_T` — fixed; it does not re-solve the game. -/
theorem ce_zero_path_strictAnti {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4)) :
    StrictAnti (ceParams.dynamicTopLockInPathF 0 ceEquilibrium.α x₀) := by
  refine strictAnti_nat_of_succ_lt (fun n => ?_)
  have hm := ce_zero_path_mem hx₀ n
  rw [dynamicTopLockInPathF_succ,
    ce_zero_stepF_eq ⟨by linarith [hm.1], by linarith [hm.2]⟩]
  linarith [hm.1]

/-! ## Rule-11 artifacts against the three candidate obstructions -/

/-- The economy is in the project's maintained strict-adjustment regime. -/
theorem ceParams_strictAdjustment : ceParams.StrictAdjustment :=
  AbstractGame.strictAdjustment_of_F_eq_affineF ceParams
    (by constructor <;> norm_num) rfl

/-- **The escalation gap.**  `R x − x = (3/4 − x)/2`: strictly positive below
`3/4` and vanishing at `3/4`, exactly the shape `exists_small_drift_of_invariant`
forces on an invariant interval.  In particular the escalation is **bounded**:
the gap tends to `0` as the state approaches the fixed point `3/4`. -/
theorem ce_gap_eq {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x - x
      = (3 / 4 - x) / 2 := by
  rw [ce_realized_rule_eq hx]; ring

/-- **OBSTRUCTION 1 REFUTED.**  The equilibrium Sender continuation value is
*strictly increasing* on the whole state space, even though the escalation gap
must shrink to `0` at the top of the invariant interval.  The gap is a property
of the *slope* of the closed loop; the value is a property of its *level*. -/
theorem ce_V_S_strictMono (y z : ↥(Sanctions.S : Set ℝ)) (h : y.val < z.val) :
    ceEquilibrium.V_S y < ceEquilibrium.V_S z := by
  change (y.val : ℝ) < z.val
  exact h

/-- **The continuation value is non-constant at two exhibited points that both
lie inside the invariant escalation interval `[5/8, 3/4)`.** -/
theorem ce_V_S_not_constant_on_invariant_interval :
    (5 / 8 : ℝ) ∈ Set.Ico (5 / 8 : ℝ) (3 / 4)
    ∧ (11 / 16 : ℝ) ∈ Set.Ico (5 / 8 : ℝ) (3 / 4)
    ∧ ceEquilibrium.V_S ⟨5 / 8, by constructor <;> norm_num⟩
        ≠ ceEquilibrium.V_S ⟨11 / 16, by constructor <;> norm_num⟩ := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  change (5 / 8 : ℝ) ≠ 11 / 16
  norm_num

theorem ce_V_S_not_constant_on_invariant_closure :
    ceEquilibrium.V_S ⟨5 / 8, by constructor <;> norm_num⟩
      ≠ ceEquilibrium.V_S ⟨3 / 4, by constructor <;> norm_num⟩ := by
  change (5 / 8 : ℝ) ≠ 3 / 4
  norm_num

theorem ce_V_T_strictMono (y z : ↥(Sanctions.S : Set ℝ)) (h : y.val < z.val) :
    ceEquilibrium.V_T y < ceEquilibrium.V_T z := by
  change (y.val : ℝ) < z.val
  exact h

/-- **OBSTRUCTION 2 REFUTED.**  The top of the invariant interval *is* a fixed
point of the rule and of the closed loop — and that is consistent with strict
escalation on the half-open interval below it, not contradictory to it.  It is
also the reason the escalation is bounded: the path converges to `3/4`. -/
theorem ce_top_fixed :
    ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α (3 / 4)
        = 3 / 4
    ∧ ceParams.dynamicTopLockInStepF ceEquilibrium.V_S ceEquilibrium.α (3 / 4)
        = 3 / 4 := by
  constructor
  · rw [ce_realized_rule_eq ⟨by norm_num, by norm_num⟩]; norm_num
  · rw [ce_stepF_eq ⟨by norm_num, by norm_num⟩]; norm_num

/-- **OBSTRUCTION 3 REFUTED.**  The realised rule is affine on the state space,
hence continuous — no jump of the greatest-argmax selector, because the Sender's
forward-looking objective is strictly concave and its argmax is a singleton at
every state.  No smoothing device (atomless shock) is used anywhere. -/
theorem ce_rule_continuousOn :
    ∀ x ∈ Sanctions.S,
      ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x
        = x / 2 + 3 / 8 :=
  fun _ hx => ce_realized_rule_eq hx

/-- The escalating sanction never reaches the ceiling. -/
theorem ce_sanction_lt_one {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) (3 / 4)) :
    ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x < 1 := by
  rw [ce_realized_rule_eq ⟨hx.1, by linarith [hx.2]⟩]
  linarith [hx.2]

/-! ## The Target's compliance choice, decomposed

The Target's equilibrium compliance `1/2 = 16/32` is strictly below its pure
stage argmax `21/32`.  The deviation is `5/32`, and it is **mostly not** a
continuation effect.  Three argmaxes, all proved below:

* `21/32` — the Target's argmax of `a ↦ U_T x a s` at a **fixed** sanction
  (`ce_target_stage_argmax`): `∂U_T/∂a = −2(a − 1/2) + 5/16`.
* `17/32` — the Target's argmax once the Sender's **stage** response
  `σ x a = x/2 + 3/8 − a/4` is substituted, with no continuation term anywhere
  (`ce_target_stage_composite_argmax`): `∂σ/∂a = −1/4` and `∂U_T/∂s = +1`, so
  the composite derivative is `−2(a − 1/2) + 5/16 − 1/4`, zero at `17/32`.
* `16/32` — the equilibrium compliance (`ce_target_policy_optimal`), which adds
  the Target's own continuation term `β_T · V_T(F(x, R(x,a)))` and the Sender's
  `1/8` wedge.

So `4/32` of the `5/32` deviation is a **pure stage effect** — it survives with
the continuation channel entirely absent — and only `1/32`, exactly **one
fifth**, is attributable to the continuation motive
(`ce_under_compliance_decomposition`).  Four fifths is stage arithmetic.  Any
reading of this file that attributes the Target's under-compliance *to* its
forward-looking motive is wrong. -/

/-- **The Target's pure stage argmax is `21/32`.**  Holding the sanction fixed
at any `s`, `a ↦ U_T x a s` is a strictly concave parabola with vertex `21/32`,
interior to `[0,1]`, so `21/32` maximises it on `[0,1]`. -/
theorem ce_target_stage_argmax (x s : ℝ) :
    IsMaxOn (fun a => ceParams.U_T x a s) Sanctions.I (21 / 32) := by
  have h : max (0 : ℝ) (min 1 (21 / 32)) = 21 / 32 := by norm_num
  rw [← h]
  refine WitnessKit.clipVertex_isMaxOn (k := (1 : ℝ))
    (C := s + x / 8 - 15 / 32 + 25 / 1024) (t := 21 / 32)
    (U := fun a => ceParams.U_T x a s) (by norm_num) ?_
  intro a
  change ceU_T x a s = _
  unfold ceU_T
  ring

/-- **The Target's argmax against the Sender's *stage* response is `17/32`.**
Substituting the Sender's stage selector `σ x a` (unclipped on the feasible
rectangle, `ceSigma_eq_ideal`) gives
`U_T x a (σ x a) = −(a − 17/32)² + (5x/8 − 223/1024)`, a strictly concave
parabola with interior vertex `17/32`.  **No continuation term appears
anywhere in this statement**: it is the Target's optimum in a world with the
continuation channel switched off on both sides. -/
theorem ce_target_stage_composite_argmax {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn (fun a => ceParams.U_T x a (ceParams.σ x a)) Sanctions.I (17 / 32) := by
  have key : ∀ a ∈ Sanctions.I, ceParams.U_T x a (ceParams.σ x a)
      = -(a - 17 / 32) ^ 2 + (5 * x / 8 - 223 / 1024) := by
    intro a ha
    rw [ceSigma_eq_ideal hx ha]
    change ceU_T x a (ceIdeal x a) = _
    unfold ceU_T ceIdeal
    ring
  have h17 : (17 / 32 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  rw [isMaxOn_iff]
  intro a ha
  change ceParams.U_T x a (ceParams.σ x a)
      ≤ ceParams.U_T x (17 / 32) (ceParams.σ x (17 / 32))
  rw [key a ha, key _ h17]
  nlinarith [sq_nonneg (a - 17 / 32)]

/-- **The equilibrium Target under-complies relative to its pure stage argmax**:
`1/2 = 16/32 < 21/32`.  See `ce_under_compliance_decomposition` for the split:
four fifths of the `5/32` gap is a stage effect operating through the Sender's
response, only one fifth is the continuation motive. -/
theorem ce_target_under_complies (x : ℝ) :
    ceEquilibrium.α x < 21 / 32 := by
  change (1 : ℝ) / 2 < 21 / 32
  norm_num

/-- **The under-compliance decomposition, as a theorem.**  Four numbers, three
of them argmaxes:

* pure stage argmax `21/32` (sanction held fixed);
* stage argmax against the Sender's stage response `17/32` (no continuation
  anywhere);
* equilibrium compliance `16/32`;

so of the total deviation `21/32 − 16/32 = 5/32`, the part `21/32 − 17/32 =
4/32` is pure stage arithmetic and only `17/32 − 16/32 = 1/32` is the
continuation motive — one fifth of the total, as the final conjunct
`5 · (17/32 − 16/32) = 21/32 − 16/32` records. -/
theorem ce_under_compliance_decomposition {x : ℝ} (hx : x ∈ Sanctions.S) (s : ℝ) :
    IsMaxOn (fun a => ceParams.U_T x a s) Sanctions.I (21 / 32)
    ∧ IsMaxOn (fun a => ceParams.U_T x a (ceParams.σ x a)) Sanctions.I (17 / 32)
    ∧ ceEquilibrium.α x = 16 / 32
    ∧ (21 : ℝ) / 32 - 16 / 32 = 5 / 32
    ∧ (21 : ℝ) / 32 - 17 / 32 = 4 / 32
    ∧ (17 : ℝ) / 32 - 16 / 32 = 1 / 32
    ∧ 5 * ((17 : ℝ) / 32 - 16 / 32) = (21 : ℝ) / 32 - 16 / 32 := by
  refine ⟨ce_target_stage_argmax x s, ce_target_stage_composite_argmax hx, ?_,
    by norm_num, by norm_num, by norm_num, by norm_num⟩
  change (1 : ℝ) / 2 = 16 / 32
  norm_num

/-! ## The economic limitation of this witness, as a theorem

`Examples/DeterministicStrictEscalation.ni_continuation_channel_inactive` is the
model followed here: a limitation of a witness stated as a theorem, so it cannot
be dropped from a docstring on the way into a paper. -/

/-- The realised stage payoff of the **Sender** at date `n` along the
equilibrium closed loop started at `x₀`: current state, equilibrium compliance
at that state, realised equilibrium sanction at that state. -/
def ceStagePayoffS (x₀ : ℝ) (n : ℕ) : ℝ :=
  ceParams.U_S
    (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n)
    (ceEquilibrium.α
      (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n))
    (ceParams.dynamicTopLockInSanctionsF ceEquilibrium.V_S ceEquilibrium.α x₀ n)

/-- The realised stage payoff of the **Target** at date `n` along the same
equilibrium closed loop. -/
def ceStagePayoffT (x₀ : ℝ) (n : ℕ) : ℝ :=
  ceParams.U_T
    (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n)
    (ceEquilibrium.α
      (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n))
    (ceParams.dynamicTopLockInSanctionsF ceEquilibrium.V_S ceEquilibrium.α x₀ n)

/-- Both players' realised stage payoffs on the equilibrium path coincide and
equal `5x/8 − 3/32` at state `x`.  The Sender is `1/8` off its stage vertex
(costing `1/64`) but collects the state level `ceG x = 5x/8 − 5/64`; the Target
is at its joint-integrand vertex and collects `s + x/8 − 15/32`. -/
theorem ce_stage_payoff_closed_form {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.U_S x (ceEquilibrium.α x)
        (ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x)
      = 5 * x / 8 - 3 / 32
    ∧ ceParams.U_T x (ceEquilibrium.α x)
        (ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x)
      = 5 * x / 8 - 3 / 32 := by
  rw [ce_realized_rule_eq hx]
  constructor
  · change ceU_S x (1 / 2 : ℝ) (x / 2 + 3 / 8) = _
    unfold ceU_S ceIdeal ceG; ring
  · change ceU_T x (1 / 2 : ℝ) (x / 2 + 3 / 8) = _
    unfold ceU_T; ring

theorem ceStagePayoffS_eq {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) (3 / 4)) (n : ℕ) :
    ceStagePayoffS x₀ n
      = 5 * ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n / 8
        - 3 / 32 := by
  have hm := ce_path_mem (a := 0) le_rfl hx₀ n
  exact (ce_stage_payoff_closed_form ⟨hm.1, by linarith [hm.2]⟩).1

theorem ceStagePayoffT_eq {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) (3 / 4)) (n : ℕ) :
    ceStagePayoffT x₀ n
      = 5 * ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀ n / 8
        - 3 / 32 := by
  have hm := ce_path_mem (a := 0) le_rfl hx₀ n
  exact (ce_stage_payoff_closed_form ⟨hm.1, by linarith [hm.2]⟩).2

/-- **Escalation here is Pareto-improving in stage payoffs.**  Along the
strictly escalating equilibrium path from any `x₀ ∈ [0, 3/4)`, *both* players'
realised stage payoffs strictly increase at every date. -/
theorem ce_escalation_pareto_improving_in_stage_payoffs
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (0 : ℝ) (3 / 4)) :
    StrictMono (ceStagePayoffS x₀) ∧ StrictMono (ceStagePayoffT x₀) := by
  have hpath : StrictMono
      (ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α x₀) :=
    (ce_strict_escalation_full_basin hx₀).1
  constructor
  · intro m n hmn
    rw [ceStagePayoffS_eq hx₀ m, ceStagePayoffS_eq hx₀ n]
    linarith [hpath hmn]
  · intro m n hmn
    rw [ceStagePayoffT_eq hx₀ m, ceStagePayoffT_eq hx₀ n]
    linarith [hpath hmn]

/-- **THIS WITNESS IS A COMMON-INTEREST GAME.**  The deepest limitation of the
construction, stated as a theorem so it cannot be lost from a docstring — the
same discipline `ni_continuation_channel_inactive`
(`Examples/DeterministicStrictEscalation.lean`) applies to the other
deterministic witness.

Three facts:

1. The two equilibrium value functions are *the same function* — both fields of
   `ceEquilibrium` are `ceVid`, so equality holds by `rfl`.  The players do not
   merely agree about escalation; they have identical continuation valuations.
2. The Sender's best attainable stage payoff at a state is exactly `ceG x`,
   which is strictly increasing: **the Sender is better off facing a more
   defiant Target.**  This is the sign that generates everything else here —
   it is why `V_S` rises, hence why the `+1/8` wedge exists, hence why the
   escalation is continuation-driven at all.
3. Along the equilibrium path both players' realised stage payoffs are the same
   real number at every date.

Consequence for how the file may be read.  The escalation exhibited here is not
coercive: it is jointly preferred by two players whose interests are aligned by
construction.  It settles that a deterministic economy *can* have a load-bearing
continuation channel, and it settles nothing about sanctions as a conflict.
Together with `ce_target_prefers_sanctions` this is the full statement of what
is wrong with the witness economically; the mathematics above is unaffected. -/
theorem ce_common_interest :
    ceEquilibrium.V_S = ceEquilibrium.V_T
    ∧ (∀ x a : ℝ, ceParams.U_S x a (ceIdeal x a) = ceG x)
    ∧ StrictMono ceG
    ∧ (∀ x₀ ∈ Set.Ico (0 : ℝ) (3 / 4), ∀ n : ℕ,
        ceStagePayoffS x₀ n = ceStagePayoffT x₀ n) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x a
    show -(ceIdeal x a - ceIdeal x a) ^ 2 + ceG x = ceG x
    ring
  · intro x₁ x₂ h
    show 5 / 8 * x₁ - 5 / 64 < 5 / 8 * x₂ - 5 / 64
    linarith
  · intro x₀ hx₀ n
    rw [ceStagePayoffS_eq hx₀ n, ceStagePayoffT_eq hx₀ n]

/-- **THE ECONOMIC LIMITATION OF THIS WITNESS, STATED AS A THEOREM.**

This Target *prefers* being sanctioned.  Three claims, all proved here:

1. **Exact unit gain.** `U_T x a s₂ − U_T x a s₁ = s₂ − s₁` for all states,
   compliance levels and sanction pairs — i.e. `∂U_T/∂s = +1` identically,
   globally, with no state or action at which it is anything else.
2. **Strict monotonicity.** Hence `s ↦ U_T x a s` is strictly increasing at
   every `(x, a)`: a heavier sanction makes this Target strictly better off.
3. **Both realised stage payoffs rise along the path**, at every date, from
   every `x₀ ∈ [0, 3/4)`.  Note this does *not* follow from `∂U_T/∂s = +1`
   alone: the Sender's half comes entirely from `ceG` (see
   `ce_common_interest`), and the two gradient facts are needed jointly.  Note
   also that this is time-monotonicity along one path, not a Pareto ranking of
   escalation against an alternative — cross-sectionally the Sender is strictly
   worse off in stage terms at the equilibrium sanction than at its own stage
   argmax, by `1/64` at every feasible state.

What this costs the file.  The project's conflict witnesses have a *negative*
sanction gradient somewhere: `eeU_T` and `mwU_T` have
`∂U_T/∂s = −(1/2 − a/2 − x)`, negative at low states and turning positive only
once the target is entrenched — that sign flip is the rally mechanism; `b2U_T`
has `∂U_T/∂s = −7/4 < 0` throughout.  Here there is a continuation gain from a
harsher sanction with **no stage loss to offset it**, so what the file exhibits
is *mutually agreeable escalation*, not a sanctions conflict.

Nothing above is weakened by this: `exists_continuation_driven_strict_escalation`
and the `V_S`-non-flatness refutation stand exactly as stated.  What this fixes
is how they may be read.  They show that a deterministic economy can have an
active, load-bearing continuation channel with a strictly increasing `V_S` on an
invariant interval whose drift gap shrinks to zero.  They do **not** show
continuation-driven escalation in a genuine sanctions conflict; whether that
exists under determinism remains **open**. -/
theorem ce_target_prefers_sanctions :
    (∀ x a s₁ s₂ : ℝ, ceParams.U_T x a s₂ - ceParams.U_T x a s₁ = s₂ - s₁)
    ∧ (∀ x a : ℝ, StrictMono fun s => ceParams.U_T x a s)
    ∧ (∀ x₀ ∈ Set.Ico (0 : ℝ) (3 / 4),
        StrictMono (ceStagePayoffS x₀) ∧ StrictMono (ceStagePayoffT x₀)) := by
  refine ⟨fun x a s₁ s₂ => ?_, fun x a s₁ s₂ h => ?_,
    fun _ hx₀ => ce_escalation_pareto_improving_in_stage_payoffs hx₀⟩
  · change ceU_T x a s₂ - ceU_T x a s₁ = _
    unfold ceU_T; ring
  · change ceU_T x a s₁ < ceU_T x a s₂
    unfold ceU_T; linarith

/-! ## Non-vacuity and concrete direction (Rules 11, 16(a)) -/

/-- The escalation window is non-empty, so the `∀ x₀ ∈ Ico (5/8) (3/4)` clauses
of the headline are not vacuously true. -/
theorem ce_window_nonempty : (Set.Ico (5 / 8 : ℝ) (3 / 4)).Nonempty :=
  ⟨5 / 8, by constructor <;> norm_num⟩

/-- Concrete directional check at `x = 5/8`: the forward-looking sanction
`11/16` is strictly above the state, the partial-counterfactual stage sanction
`9/16` strictly below it. -/
theorem ce_at_five_eighths :
    ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α (5 / 8)
        = 11 / 16
    ∧ ceParams.dynamicTopRealizedRule 0 ceEquilibrium.α (5 / 8) = 9 / 16
    ∧ (9 : ℝ) / 16 < 5 / 8 ∧ (5 : ℝ) / 8 < 11 / 16 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [ce_realized_rule_eq ⟨by norm_num, by norm_num⟩]; norm_num
  · rw [ce_zero_rule_eq ⟨by norm_num, by norm_num⟩]; norm_num

/-- The first two steps of both closed loops from `x₀ = 5/8`, in exact
rationals.  Equilibrium: `5/8 → 21/32 → 87/128`, strictly up.  Partial
Sender-side counterfactual (`V_S := 0` in the Sender's argmax only):
`5/8 → 19/32 → 73/128`, strictly down. -/
theorem ce_first_steps :
    ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α (5 / 8) 1
        = 21 / 32
    ∧ ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α (5 / 8) 2
        = 87 / 128
    ∧ ceParams.dynamicTopLockInPathF 0 ceEquilibrium.α (5 / 8) 1 = 19 / 32
    ∧ ceParams.dynamicTopLockInPathF 0 ceEquilibrium.α (5 / 8) 2 = 73 / 128
    ∧ (5 : ℝ) / 8 < 21 / 32 ∧ (21 : ℝ) / 32 < 87 / 128
    ∧ (73 : ℝ) / 128 < 19 / 32 ∧ (19 : ℝ) / 32 < 5 / 8 := by
  have e0 : ceParams.dynamicTopLockInPathF ceEquilibrium.V_S ceEquilibrium.α
      (5 / 8) 1 = 21 / 32 := by
    rw [dynamicTopLockInPathF_succ, dynamicTopLockInPathF_zero,
      ce_stepF_eq ⟨by norm_num, by norm_num⟩]
    norm_num
  have z0 : ceParams.dynamicTopLockInPathF 0 ceEquilibrium.α (5 / 8) 1
      = 19 / 32 := by
    rw [dynamicTopLockInPathF_succ, dynamicTopLockInPathF_zero,
      ce_zero_stepF_eq ⟨by norm_num, by norm_num⟩]
    norm_num
  refine ⟨e0, ?_, z0, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [dynamicTopLockInPathF_succ, e0, ce_stepF_eq ⟨by norm_num, by norm_num⟩]
    norm_num
  · rw [dynamicTopLockInPathF_succ, z0, ce_zero_stepF_eq ⟨by norm_num, by norm_num⟩]
    norm_num

/-! ## Headline -/

/-- **CONTINUATION-DRIVEN STRICT ESCALATION AT A DETERMINISTIC ECONOMY.**

There is a deterministic economy `p` and a stationary feedback-Stackelberg
equilibrium `E` of it such that:

* both discount factors are strictly positive and `p` satisfies the project's
  strict-adjustment regime;
* both equilibrium value functions are non-zero, and the Sender's is *strictly
  increasing* — in particular non-constant at two exhibited points inside the
  escalation window;
* the Target's equilibrium compliance is interior at every state;
* with the Sender's continuation value switched off, the Sender's greatest
  forward-looking maximiser is *exactly* its stage argmax `p.σ`, and with it
  switched on the equilibrium sanction exceeds `p.σ` by exactly `1/8` at every
  feasible state;
* on `[5/8, 3/4)` the equilibrium state path and sanction sequence are strictly
  increasing forever, while on the *same* interval the zero-`V_S` rule lies
  strictly below the diagonal and its path is strictly decreasing forever.

**Quantifier order.**  This is `∃ economy, ∀ start`.  It does **not** claim that
a continuation motive is *necessary* for deterministic escalation —
`exists_deterministic_strict_escalation` already refutes that.

**The last three conjuncts are a partial Sender-side counterfactual.**
`p.dynamicTopRealizedRule 0 E.α` substitutes `V_S := 0` inside the Sender's
forward-looking argmax while holding the economy, `E.α`, and `V_T` fixed.  It is
not the equilibrium of a myopic game: no myopic game is solved and `E.α` is not
re-optimised against the myopic rule.

**Escalation is bounded.**  The closed loop's fixed point is `3/4`
(`ce_top_fixed`) and its escalation gap is `(3/4 − x)/2` (`ce_gap_eq`), which
tends to `0`.  Strict escalation forever is *not* unbounded escalation; the
sanction stays strictly below the ceiling (`ce_sanction_lt_one`).

**What this witness does *not* show** (see `ce_target_prefers_sanctions`).  This
Target's stage payoff has `∂U_T/∂s = +1` identically: it is strictly better off
under a heavier sanction at every state and compliance level.  Both players'
realised stage payoffs therefore *rise* along the escalating path.  What is
exhibited is mutually agreeable escalation, not a sanctions conflict — so this
does not settle whether continuation-driven escalation arises in a genuine
sanctions conflict under determinism, which remains open. -/
theorem exists_continuation_driven_strict_escalation :
    ∃ (p : AbstractGame.Params) (E : p.FeedbackStackelbergEquilibriumTop),
      0 < p.β_S ∧ 0 < p.β_T
      ∧ p.StrictAdjustment
      ∧ E.V_S ≠ 0 ∧ E.V_T ≠ 0
      ∧ (∀ y z : ↥(Sanctions.S : Set ℝ), y.val < z.val → E.V_S y < E.V_S z)
      ∧ (∃ y z : ↥(Sanctions.S : Set ℝ),
            y.val ∈ Set.Ico (5 / 8 : ℝ) (3 / 4)
            ∧ z.val ∈ Set.Ico (5 / 8 : ℝ) (3 / 4)
            ∧ E.V_S y ≠ E.V_S z)
      ∧ (∀ x, 0 < E.α x ∧ E.α x < 1)
      ∧ (∀ x ∈ Sanctions.S,
            p.dynamicTopRealizedRule 0 E.α x = p.σ x (E.α x))
      ∧ (∀ x ∈ Sanctions.S,
            p.dynamicTopRealizedRule E.V_S E.α x = p.σ x (E.α x) + 1 / 8)
      ∧ (∀ x₀ ∈ Set.Ico (5 / 8 : ℝ) (3 / 4),
            StrictMono (p.dynamicTopLockInPathF E.V_S E.α x₀)
            ∧ StrictMono (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Ico (5 / 8 : ℝ) (3 / 4),
            p.dynamicTopRealizedRule 0 E.α x < x)
      ∧ (∀ x₀ ∈ Set.Ico (5 / 8 : ℝ) (3 / 4),
            StrictAnti (p.dynamicTopLockInPathF 0 E.α x₀)) := by
  refine ⟨ceParams, ceEquilibrium, by norm_num, by norm_num,
    ceParams_strictAdjustment, ceVid_ne_zero, ceVid_ne_zero,
    ce_V_S_strictMono, ?_, fun x => by norm_num [ceEquilibrium, ceAlpha],
    fun x hx => ce_zero_rule_eq_stage hx, fun x hx => ce_wedge hx, ?_, ?_, ?_⟩
  · exact ⟨⟨5 / 8, by constructor <;> norm_num⟩, ⟨11 / 16, by constructor <;> norm_num⟩,
      ce_V_S_not_constant_on_invariant_interval.1,
      ce_V_S_not_constant_on_invariant_interval.2.1,
      ce_V_S_not_constant_on_invariant_interval.2.2⟩
  · intro x₀ hx₀
    exact ce_strict_escalation (a := 5 / 8) (by norm_num) hx₀
  · intro x hx
    exact ce_zero_rule_lt_self ⟨by linarith [hx.1], hx.2⟩
  · intro x₀ hx₀
    exact ce_zero_path_strictAnti ⟨by linarith [hx₀.1], hx₀.2⟩

/-! ## DYNAMIC-STAKE at `ceParams`

This economy supplies the two rows DYNAMIC-STAKE needs from a *real* game with a
*constructed* equilibrium: the hypothesis is met, and the upper-chord form is
non-vacuous. It also supplies the counter-row that pins the result's scope: the
existential rise it delivers is genuinely existential, and is **not** located at
the state carrying the floor. -/

/-- **The hypothesis `stageTopRule < realised rule` is realised in this tree.**
`ceParams`' constructed equilibrium sanctions strictly above the greatest stage
maximiser — by exactly `1/8`, from `ce_wedge` against `ce_zero_rule_eq_stage`.
So "the floor strictly exceeds the stage argmax" is a real restriction, met at a
*constructed feedback Stackelberg equilibrium* and not merely at a
value-function computation. -/
theorem ce_is_a_genuine_dynamic_floor {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.stageTopRule ceEquilibrium.α x
      < ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α x := by
  rw [ceParams.stageTopRule_eq_zeroValue_rule, ce_zero_rule_eq_stage hx, ce_wedge hx]
  linarith

/-- DYNAMIC-STAKE applied at `ceParams`' constructed equilibrium: there exist
feasible states `y₁ ≤ y₂` and a feasible sanction `s` at which the Sender's
composed stage payoff strictly rises.

**What this does NOT recover.** It does *not* re-derive `ce_common_interest`.
That theorem is a four-fold conjunction — `V_S = V_T`, the envelope closed form
`U_S x a (ceIdeal x a) = ceG x`, `StrictMono ceG`, and equality of the two
players' realised stage-payoff paths. What DYNAMIC-STAKE delivers here is one
existential strict inequality at one fixed sanction. In particular it does not
deliver `StrictMono ceG`: that conjunct is about the *envelope* at the ideal
sanction, a different function from `y ↦ U_S(y, α y, s)` at fixed `s`, and the
composed map is not even monotone here (`ce_composed_not_monotone`). -/
theorem ce_dynamic_stake_conclusion {x : ℝ} (hx : x ∈ Sanctions.S) :
    ∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
      y₁ ≤ y₂ ∧ ceParams.U_S y₁ (ceEquilibrium.α y₁) s
        < ceParams.U_S y₂ (ceEquilibrium.α y₂) s :=
  ceParams.dynamic_stake_equilibrium ceEquilibrium x (ce_is_a_genuine_dynamic_floor hx)

/-- An admissible **upper** chord constant for `ceParams` at its equilibrium
policy `ceAlpha ≡ 1/2`: the composed state chord is `s + 3/8 − (y₁+y₂)/4`, which
is at most `11/8` on the feasible box. -/
theorem ce_upper_chord :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      ceParams.U_S y₂ (ceEquilibrium.α y₂) s - ceParams.U_S y₁ (ceEquilibrium.α y₁) s
        ≤ (11/8 : ℝ) * (y₂ - y₁) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  show ceU_S y₂ (ceAlpha y₂) s - ceU_S y₁ (ceAlpha y₁) s ≤ (11/8 : ℝ) * (y₂ - y₁)
  unfold ceU_S ceIdeal ceG ceAlpha
  nlinarith [hs.2, hy₁.1, hy₂.1, sub_nonneg.mpr hle]

/-- **`chord_pos_of_equilibrium_dynamic_floor` is non-vacuous.** `ceParams` at
its constructed equilibrium satisfies **both** of that theorem's hypotheses
simultaneously — an admissible upper chord constant (`11/8`) and a dynamic floor
(here at the state `0`) — and the theorem then returns strict positivity of the
constant.

This closes the gap the two neighbouring witnesses leave open: `lbParams` has a
(non-positive) chord and provably no floor, `ceParams` had the floor with no
exhibited chord. The conjunction is what makes the `c_S > 0` form a statement
about a realisable configuration rather than an empty implication. -/
theorem ce_chord_pos :
    (∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        ceParams.U_S y₂ (ceEquilibrium.α y₂) s - ceParams.U_S y₁ (ceEquilibrium.α y₁) s
          ≤ (11/8 : ℝ) * (y₂ - y₁))
    ∧ (ceParams.stageTopRule ceEquilibrium.α 0
        < ceParams.dynamicTopRealizedRule ceEquilibrium.V_S ceEquilibrium.α 0)
    ∧ (0 : ℝ) < 11/8 :=
  ⟨ce_upper_chord,
   ce_is_a_genuine_dynamic_floor (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.S),
   ceParams.chord_pos_of_equilibrium_dynamic_floor ceEquilibrium ce_upper_chord
     (ce_is_a_genuine_dynamic_floor (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.S))⟩

/-- **SCOPE — the rise DYNAMIC-STAKE delivers is not located at the floor
state.** At `ceParams` a dynamic floor holds at *every* feasible state
(`ce_is_a_genuine_dynamic_floor`), yet the Sender's composed stage payoff at the
equilibrium policy strictly **falls** from `y = 3/4` to `y = 1` at the zero
sanction.

So a floor at `x = 1` licenses only "the composed payoff rises somewhere in
`[0,1]`" while the payoff is locally falling at `1` itself. This is the in-tree
instance of the `x`-free scope limit recorded abstractly by
`Sanctions.AbstractGame.Params.dynamic_stake_conclusion_is_x_free`. -/
theorem ce_composed_chord_negative_somewhere :
    ceParams.U_S 1 (ceEquilibrium.α 1) 0
      < ceParams.U_S (3/4) (ceEquilibrium.α (3/4)) 0 := by
  show ceU_S 1 (ceAlpha 1) 0 < ceU_S (3/4) (ceAlpha (3/4)) 0
  unfold ceU_S ceIdeal ceG ceAlpha
  norm_num

/-- Consequently the composed `ceParams` state payoff is **not** monotone in the
Target's political state, even though the envelope `ceG` (the stage payoff at the
Target-ideal sanction) is strictly increasing. The two are different functions,
and DYNAMIC-STAKE's existential rise cannot be upgraded to the strict
monotonicity that `ce_common_interest` asserts for `ceG`. -/
theorem ce_composed_not_monotone :
    ¬ (∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, ∀ s ∈ Sanctions.I, y₁ ≤ y₂ →
        ceParams.U_S y₁ (ceEquilibrium.α y₁) s
          ≤ ceParams.U_S y₂ (ceEquilibrium.α y₂) s) := by
  intro h
  have := h (3/4) ⟨by norm_num, by norm_num⟩ 1 ⟨by norm_num, by norm_num⟩
    0 ⟨le_refl 0, by norm_num⟩ (by norm_num)
  exact absurd this (not_le.mpr ce_composed_chord_negative_somewhere)

#print axioms ceParams
#print axioms ceEquilibrium
#print axioms ce_strict_escalation
#print axioms ce_strict_escalation_full_basin
#print axioms ce_path_mem
#print axioms ce_wedge
#print axioms ce_zero_rule_eq_stage
#print axioms ce_zero_path_strictAnti
#print axioms ce_V_S_strictMono
#print axioms ce_V_S_not_constant_on_invariant_interval
#print axioms ce_top_fixed
#print axioms ce_first_steps
#print axioms ce_target_stage_argmax
#print axioms ce_target_stage_composite_argmax
#print axioms ce_under_compliance_decomposition
#print axioms ce_stage_payoff_closed_form
#print axioms ce_escalation_pareto_improving_in_stage_payoffs
#print axioms ce_common_interest
#print axioms ce_target_prefers_sanctions
#print axioms exists_continuation_driven_strict_escalation
#print axioms ce_is_a_genuine_dynamic_floor
#print axioms ce_dynamic_stake_conclusion
#print axioms ce_upper_chord
#print axioms ce_chord_pos
#print axioms ce_composed_chord_negative_somewhere
#print axioms ce_composed_not_monotone


/-! ## The Sender-investment channel, in the named vocabulary (Rule 5)

`ce_wedge` gives the exact `1/8`. The general theorem
`sender_dynamic_sanctions_gt_myopic_at_same_action` needs three things at this
economy, each already essentially present: the stage argmax is unique (the
stage payoff is a clipped parabola, `ceSigma_isMaxOn`), the continuation wedge
rises (`V_S` is the identity and `F` is strictly increasing in the sanction), and
one chord — the forward-looking objective at the stage argmax is beaten by the
forward-looking objective one-eighth higher. With those, *every* forward-looking
maximizer sits strictly above *every* stage maximizer, and no forward-looking
maximizer is stage-optimal. That is what "the continuation changes the Sender's
optimal action" means, and this file was the first economy where it was proved
— by hand. It is now a corollary. -/

/-- **The stage argmax is unique.** Any stage maximizer is the vertex. -/
theorem ce_stage_isMaxOn_eq {x a s : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun t => ceParams.U_S x a t) Sanctions.I s) :
    s = ceIdeal x a := by
  have h := hmax (ceIdeal_mem hx ha)
  simp only [Set.mem_setOf_eq, ceParams_U_S, ceU_S] at h
  have hsq : (s - ceIdeal x a) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)

/-- **The continuation wedge rises**, from the two primitives. -/
theorem ce_senderSanctionContinuation_strictMono {x : ℝ} (hx : x ∈ Sanctions.S) :
    ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      ceParams.senderSanctionContinuation ceVid x s₁
        < ceParams.senderSanctionContinuation ceVid x s₂ :=
  ceParams.senderSanctionContinuation_strictMono_of_separated_primitives ceVid hx
    (fun s₁ _ s₂ _ h => ceParams_F_strictMono_s x h)
    (fun y₁ hy₁ y₂ hy₂ h => by rw [ceVid_clip hy₁, ceVid_clip hy₂]; exact h)

/-- **The chord at the stage argmax.** One-eighth higher beats it. -/
theorem ce_sender_chord {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.U_S x (ceAlpha x) (ceIdeal x (ceAlpha x))
        - ceParams.U_S x (ceAlpha x) (ceR x (ceAlpha x))
      < ceParams.β_S *
          (ceParams.senderSanctionContinuation ceVid x (ceR x (ceAlpha x))
            - ceParams.senderSanctionContinuation ceVid x (ceIdeal x (ceAlpha x))) := by
  have ha : ceAlpha x ∈ Sanctions.I := ceAlpha_mem x
  have hI := ceIdeal_mem hx ha
  have hR := ceR_mem hx ha
  have hm1 : (x + ceIdeal x (ceAlpha x)) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, hI.1], by linarith [hx.2, hI.2]⟩
  have hm2 : (x + ceR x (ceAlpha x)) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, hR.1], by linarith [hx.2, hR.2]⟩
  simp only [AbstractGame.Params.senderSanctionContinuation, ceF_eq,
    ceVid_clip hm1, ceVid_clip hm2, ceParams_U_S, ceParams_β_S]
  unfold ceU_S ceR ceIdeal ceG ceAlpha
  linarith

/-- **The continuation changes the Sender's optimal sanction, at every feasible
state** — the named form, as a corollary of the general strict theorem. -/
theorem ce_continuationChangesSenderChoice {x : ℝ} (hx : x ∈ Sanctions.S) :
    ceParams.ContinuationChangesSenderChoiceAt ceVid x (ceAlpha x) := by
  apply AbstractGame.Params.continuationChangesSenderChoiceAt_of_strict_ordering
  intro sM _hsM sD hsD hstage hdyn
  rw [ce_stage_isMaxOn_eq hx (ceAlpha_mem x) hstage]
  have hstage' : IsMaxOn (fun t => ceParams.U_S x (ceAlpha x) t) Sanctions.I
      (ceIdeal x (ceAlpha x)) := by
    have := ceSigma_isMaxOn x (ceAlpha x)
    change IsMaxOn (fun s => ceU_S x (ceAlpha x) s) Sanctions.I
      (ceParams.σ x (ceAlpha x)) at this
    rw [ceSigma_eq_ideal hx (ceAlpha_mem x)] at this
    exact this
  exact ceParams.sender_dynamic_sanctions_gt_myopic_at_same_action ceVid
    (ceIdeal_mem hx (ceAlpha_mem x)) hsD (ceR_mem hx (ceAlpha_mem x))
    hstage' hdyn (by norm_num)
    (ce_senderSanctionContinuation_strictMono hx) (ce_sender_chord hx)

#print axioms ce_continuationChangesSenderChoice

end

end Examples
end Sanctions
