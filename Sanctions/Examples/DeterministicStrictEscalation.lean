/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.NonAffineInteriorWitness
import Sanctions.Examples.B2GeneralFPersistenceWitness
import Sanctions.Examples.FeedbackComparativeStatics
import Sanctions.Theory.LockIn.EscalationGap
-- `dynamicTopLockInPathF_escape_of_uniform_gap_affine`.
import Sanctions.Examples.AffineInstance.Kinematics

/-!
# Strict escalation at a deterministic economy: SETTLED, affirmatively

`Theory/LockIn/SubintervalLockIn.lean` reduced strict escalation to three
conditions on the equilibrium-realised sanction rule
`R = dynamicTopRealizedRule V_S α` and an interval `[a,b)`:

  (i)   `x < R x` on `[a,b)`               — the rule lies above the diagonal;
  (ii)  `StrictMonoOn R [a,b)`             — the rule strictly increases;
  (iii) `[a,b)` forward invariant under `x ↦ F x (R x)`.

The project had strict escalation only through the exogenous shock phase, and
had explicitly declined to claim that the shock is *necessary*.  This file
settles the question: it is not.  A **perfect-information (deterministic-
transition) economy with a fully constructed stationary equilibrium** satisfies
all three, so its equilibrium sanction path strictly rises at every date,
forever, with no exogenous phase anywhere.

## The witness

`niParams` / `niEquilibrium` (`Examples/NonAffineInteriorWitness.lean`) —
transition `quadBumpF` (a deterministic function of `(x,s)`, no shock, no
kernel), interior Target policy `α ≡ 1/2` derived as the Target argmax, Sender
rule the forward-looking upper argmax `σ_dyn_top`, both continuation values
verified Bellman fixed points.  Its realised rule is exactly

  `R x = (x + 1)/2`   (`ni_realized_rule_eq`),

which meets the diagonal only at the top state.  The three conditions become
`ni_rule_gt_self`, `ni_rule_strictMonoOn`, `ni_stepF_mem_Ico`, and the headline
is `ni_strict_escalation`.

## Why the two economies one would have guessed do not work

* **eeCert family** — `R ≡ 1` (`eeCertB_σ_dyn_top_eq_one`).  (i) holds and (iii)
  holds, so the *state* strictly escalates, but (ii) fails: the sanction is
  already maximal and therefore constant.  Maximal, but weak.
  (`eeCertB_rule_not_strictMonoOn`.)
* **B2 economy** — `R = b2p`, flat at `7/8` on `[0,5/8]`, rising with slope
  `4/3` on `[5/8,23/32]`, pinned at `1` above.  So (ii) fails on the flat
  stretch (`b2_rule_not_strictMonoOn`), and on the stretch where (ii) *does*
  hold the slope `4/3 > 1` overshoots so badly that the rule clears the
  diagonal by at least `1/4`; by the escalation-gap theorem no sub-interval of
  it can be invariant (`b2_steep_window_no_invariant_subinterval`).  What
  survives at B2 is the *state* path: it is genuinely `StrictMono`
  (`b2_state_path_strictMono`).

Both failures are instances of the same shape condition: by
`exists_small_drift_of_invariant` the escalation gap must shrink to zero at the
top of the invariant interval.  `eeCert` fails it from below (zero slope, gap
pinned by the ceiling), B2 fails it from above (slope `> 1`, gap bounded away
from zero).  The witness rule `(x+1)/2` has slope `1/2 ∈ (0,1)` and gap
`(1−x)/2 → 0`: it threads exactly between them.

## Rule compliance

**Rule 1.** Every strategic object is an optimisation result.  `α = niAlpha` is
the Target argmax (`ni_target_policy_optimal`), `R` is the Sender's
forward-looking upper argmax `σ_dyn_top`, and both values are Bellman fixed
points (`ni_sender_value_fix`, `ni_target_value_fix_top`) — the equilibrium
`niEquilibrium` is *constructed*, not hypothesised.  No exogenous phase is used
anywhere in this file.

Rule 1 is satisfied, but one qualification belongs here rather than in a
footnote.  At this witness both equilibrium values are identically zero
(`ni_continuation_channel_inactive`), so `σ_dyn_top` — the *forward-looking*
upper argmax by definition — coincides with the myopic stage argmax in value.
The optimality is genuine; the continuation channel is inert.  Nothing in this
file should be read as showing that forward-looking behaviour *produces* the
escalation here.

**Rule 3.** No new assumption: only existing `Params` fields, the existing
constructed equilibrium, and the parametric theorems of
`Theory/LockIn/{SubintervalLockIn,EscalationGap}.lean`.

**Rule 5.** All the mathematics is in the parametric theorems; the content here
is a witness discharge of their hypotheses, which is exactly the admissible
witness-specific case (an existence certificate).

**Rule 11.** The two negative results are exhibited as Lean refutations of
condition (ii) / (iii) at the economies where they fail, not asserted in prose.
-/

namespace Sanctions
namespace Examples

open Set AbstractGame AbstractGame.Params

noncomputable section

/-! ## Part 0 — strictness of the quadratic-bump transition in the sanction

The `Params` field `F_mono_s` is only `Monotone`; the strict-escalation
theorems need `StrictMono`.  The bump's sanction-chord is bounded by `3/100`
against the affine term's `1/2`, so the transition gains at least `47/100` per
unit of sanction. -/

/-- **Strict** monotonicity of the quadratic-bump transition in the sanction
(the shipped `quadBumpF_mono_s` is only weak). -/
theorem quadBumpF_strictMono_s (x : ℝ) : StrictMono (fun s => quadBumpF x s) := by
  intro s₁ s₂ hlt
  unfold quadBumpF
  set c₁ := Sanctions.clipS s₁ with hc₁
  set c₂ := Sanctions.clipS s₂ with hc₂
  set cx := Sanctions.clipS x with hcx
  have hc₁m : c₁ ∈ Set.Icc (0 : ℝ) 1 := Sanctions.clipS_mem s₁
  have hc₂m : c₂ ∈ Set.Icc (0 : ℝ) 1 := Sanctions.clipS_mem s₂
  have hcxm : cx ∈ Set.Icc (0 : ℝ) 1 := Sanctions.clipS_mem x
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hlt.le
  have hclip : c₂ - c₁ ≤ s₂ - s₁ := by
    have := Sanctions.clipS_lipschitz_abs s₂ s₁
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₂ - s₁)] at this
    linarith
  simp only
  have hkey : (c₂ - cx)^2 * (1 - c₂) - (c₁ - cx)^2 * (1 - c₁)
      = (c₂ - c₁) * ((1 - c₂) * (c₂ + c₁ - 2*cx) - (c₁ - cx)^2) := by ring
  have h1 : (0 : ℝ) ≤ (1 - c₂) * (c₂ + c₁ - 2*cx + 2) :=
    mul_nonneg (by linarith [hc₂m.2]) (by linarith [hc₁m.1, hc₂m.1, hcxm.2])
  have h2 : (c₁ - cx)^2 ≤ 1 := by
    nlinarith [hc₁m.1, hc₁m.2, hcxm.1, hcxm.2]
  have hbr : (-3 : ℝ) ≤ (1 - c₂) * (c₂ + c₁ - 2*cx) - (c₁ - cx)^2 := by
    nlinarith [h1, h2, hc₂m.1, hc₂m.2]
  have hprod : (c₂ - c₁) * (-3 : ℝ)
      ≤ (c₂ - c₁) * ((1 - c₂) * (c₂ + c₁ - 2*cx) - (c₁ - cx)^2) :=
    mul_le_mul_of_nonneg_left hbr (by linarith)
  linarith [hkey, hprod, hclip]

theorem niParams_F_strictMono_s (x : ℝ) :
    StrictMono (fun s => niParams.F x s) := by
  rw [niParams_F]; exact quadBumpF_strictMono_s x

/-! ## Part 1 — the three conditions at the constructed equilibrium -/

/-- Closed form of the equilibrium closed loop on the state space:
`F(x, (x+1)/2) = (3x+1)/4 + (1−x)³/800`. -/
theorem ni_stepF_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    niParams.dynamicTopLockInStepF niEquilibrium.V_S niEquilibrium.α x
      = (3*x+1)/4 + (1-x)^3 / 800 := by
  unfold AbstractGame.Params.dynamicTopLockInStepF
  rw [ni_realized_rule_eq hx]
  change quadBumpF x ((x+1)/2) = _
  rw [quadBumpF_sq hx ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  ring

/-- **(i)** The equilibrium rule lies strictly above the diagonal on `[a,1)`:
the Sender more than replaces the inherited level of entrenchment. -/
theorem ni_rule_gt_self {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Set.Ico a 1) :
    x < niParams.dynamicTopRealizedRule niEquilibrium.V_S niEquilibrium.α x := by
  rw [ni_realized_rule_eq ⟨le_trans ha hx.1, hx.2.le⟩]
  linarith [hx.2]

/-- **(ii)** The equilibrium rule is strictly increasing on `[a,1)`: a more
entrenched state draws a strictly heavier sanction. -/
theorem ni_rule_strictMonoOn {a : ℝ} (ha : 0 ≤ a) :
    StrictMonoOn
      (niParams.dynamicTopRealizedRule niEquilibrium.V_S niEquilibrium.α)
      (Set.Ico a 1) := by
  intro u hu v hv huv
  rw [ni_realized_rule_eq ⟨le_trans ha hu.1, hu.2.le⟩,
      ni_realized_rule_eq ⟨le_trans ha hv.1, hv.2.le⟩]
  linarith

/-- **(iii)** `[a,1)` is forward invariant under the equilibrium closed loop. -/
theorem ni_stepF_mem_Ico {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Set.Ico a 1) :
    niParams.dynamicTopLockInStepF niEquilibrium.V_S niEquilibrium.α x
      ∈ Set.Ico a 1 := by
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ha hx.1, hx.2.le⟩
  rw [ni_stepF_eq hx01]
  have hu : 0 < 1 - x := by linarith [hx.2]
  have hu1 : 1 - x ≤ 1 := by linarith [hx01.1]
  exact ⟨by nlinarith [hx.1, pow_pos hu 3],
         by nlinarith [pow_pos hu 3, sq_nonneg (1-x)]⟩

/-- The escalation gap `R x − x = (1−x)/2` shrinks to zero at the top state —
the shape condition that `exists_small_drift_of_invariant` shows is forced. -/
theorem ni_gap_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    niParams.dynamicTopRealizedRule niEquilibrium.V_S niEquilibrium.α x - x
      = (1 - x)/2 := by
  rw [ni_realized_rule_eq hx]; ring

/-! ## Part 2 — the headline -/

/-- **STRICT ESCALATION AT A DETERMINISTIC ECONOMY.**  At the constructed
stationary equilibrium `niEquilibrium` of the deterministic economy `niParams`,
from every start in `[a,1)` the political state **and** the equilibrium sanction
are strictly increasing sequences — at every date, forever, with no exogenous
shock phase. -/
theorem ni_strict_escalation {a x₀ : ℝ} (ha : 0 ≤ a) (hx₀ : x₀ ∈ Set.Ico a 1) :
    StrictMono
        (niParams.dynamicTopLockInPathF niEquilibrium.V_S niEquilibrium.α x₀)
    ∧ StrictMono
        (niParams.dynamicTopLockInSanctionsF
          niEquilibrium.V_S niEquilibrium.α x₀) :=
  ⟨niParams.dynamicTopLockInPathF_strictMono_of_gt_self_of_strictMono_s
      niEquilibrium.V_S niEquilibrium.α niParams_F_strictMono_s
      (fun _ hx => ni_rule_gt_self ha hx)
      (fun _ hx => ni_stepF_mem_Ico ha hx) hx₀,
   niParams.dynamicTopLockInSanctionsF_strictMono_of_gt_self_of_strictMono_s
      niEquilibrium.V_S niEquilibrium.α niParams_F_strictMono_s
      (fun _ hx => ni_rule_gt_self ha hx)
      (fun _ hx => ni_stepF_mem_Ico ha hx)
      (ni_rule_strictMonoOn ha) hx₀⟩

/-- **The integrated statement.**  One deterministic economy, one constructed
equilibrium: the transition is a deterministic function (not a kernel) and is
genuinely non-affine, both discount factors are strictly positive, the Target
policy is interior, the realised sanction is interior at the basin pivot, and
from every basin start both the state path and the sanction path are strictly
increasing forever. -/
theorem ni_deterministic_strict_escalation_integrated :
    0 < niParams.β_T
    ∧ 0 < niParams.β_S
    ∧ niParams.F ≠ AbstractGame.affineF (1 / 2)
    ∧ (0 < niEquilibrium.α (1 / 2) ∧ niEquilibrium.α (1 / 2) < 1)
    ∧ niParams.dynamicTopRealizedRule niEquilibrium.V_S
        niEquilibrium.α (1 / 2) = 3 / 4
    ∧ ∀ x₀ ∈ Set.Ico (1 / 2 : ℝ) 1,
        StrictMono
          (niParams.dynamicTopLockInPathF
            niEquilibrium.V_S niEquilibrium.α x₀)
        ∧ StrictMono
          (niParams.dynamicTopLockInSanctionsF
            niEquilibrium.V_S niEquilibrium.α x₀) := by
  refine ⟨by norm_num [niParams], by norm_num [niParams],
    niParams_F_ne_affine, by norm_num [niEquilibrium, niAlpha], ?_, ?_⟩
  · rw [ni_realized_rule_eq ⟨by norm_num, by norm_num⟩]; norm_num
  · intro x₀ hx₀
    exact ni_strict_escalation (by norm_num) hx₀

/-! ## Part 2b — the existential form

The theorems above are stated *at* `niParams`.  The existential form — **some**
deterministic economy escalates strictly — is the one the paper may cite,
because it carries **no witness magnitude**: the non-affinity of the transition
is quantified over every rate, the discount factors appear only through their
sign, and the Target policy appears only through its interiority.

**It is not stronger than the named form.**  It is obtained from the named
theorems by `∃`-introduction, so it is weaker-or-equal: the named statement
implies it and not conversely.  Its value is that a reader need not inspect the
witness to read the claim, not that it says more.  (An earlier draft of this
comment asserted the opposite, which is backwards.) -/

/-- The witness transition is not affine **at any rate** — so the strict
escalation is not an artefact of linearity.  (The shipped
`niParams_F_ne_affine` fixes the rate at `1/2`; this quantifies it away, which
is what lets the existential below carry no witness magnitude.) -/
theorem niParams_F_ne_affine_all (d : ℝ) : niParams.F ≠ AbstractGame.affineF d := by
  intro h
  have h1 : niParams.F 0 1 = AbstractGame.affineF d 0 1 := by rw [h]
  have h2 : niParams.F 0 (1 / 2) = AbstractGame.affineF d 0 (1 / 2) := by rw [h]
  rw [niParams_F] at h1 h2
  unfold quadBumpF AbstractGame.affineF at h1 h2
  rw [clipS_of_mem (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1),
      clipS_of_mem (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)] at h1
  rw [clipS_of_mem (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1),
      clipS_of_mem (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)] at h2
  norm_num at h1 h2
  rw [← h1] at h2
  norm_num at h2

/-- The equilibrium state path stays inside `[a,1)` at every date. -/
theorem ni_path_mem_Ico {a x₀ : ℝ} (ha : 0 ≤ a) (hx₀ : x₀ ∈ Set.Ico a 1) (n : ℕ) :
    niParams.dynamicTopLockInPathF niEquilibrium.V_S niEquilibrium.α x₀ n
      ∈ Set.Ico a 1 := by
  induction n with
  | zero => simpa using hx₀
  | succ k ih => rw [dynamicTopLockInPathF_succ]; exact ni_stepF_mem_Ico ha ih

/-- The escalating sanction is **strictly interior at every date**: it rises
forever without ever reaching the feasibility ceiling `1`.  This is the sharp
contrast with the eeCert family, whose sanction is maximal (`R ≡ 1`) and
therefore constant. -/
theorem ni_sanction_lt_one {a x₀ : ℝ} (ha : 0 ≤ a) (hx₀ : x₀ ∈ Set.Ico a 1) (n : ℕ) :
    niParams.dynamicTopLockInSanctionsF niEquilibrium.V_S niEquilibrium.α x₀ n < 1 := by
  have hm := ni_path_mem_Ico ha hx₀ n
  unfold AbstractGame.Params.dynamicTopLockInSanctionsF
  rw [ni_realized_rule_eq ⟨le_trans ha hm.1, hm.2.le⟩]
  linarith [hm.2]

/-- **The continuation channel at this witness is inert.**  Both equilibrium
value functions are identically zero, so the Sender's forward-looking objective
coincides pointwise with its stage payoff and every `β · V(…)` term vanishes.

This is a limitation of the witness, stated as a theorem so that it cannot be
lost from a docstring.  It does not weaken `exists_deterministic_strict_escalation`
— that theorem's hypotheses and conclusion are unaffected — but it fixes what the
result may be read as showing: determinism does not *preclude* strict escalation.
It is not evidence that a continuation motive *sustains* escalation under
determinism, which remains open. -/
theorem ni_continuation_channel_inactive :
    niEquilibrium.V_S = 0 ∧ niEquilibrium.V_T = 0
    ∧ ∀ x a s : ℝ,
        niParams.U_S x a s
          + niParams.β_S * niEquilibrium.V_S (Sanctions.clipS' (niParams.F x s))
        = niParams.U_S x a s := by
  refine ⟨rfl, rfl, fun x a s => ?_⟩
  show _ + niParams.β_S * (0 : ℝ) = _
  ring

/-- **THERE EXIST DETERMINISTIC PRIMITIVES AND AN EQUILIBRIUM WITH STRICTLY
ESCALATING SANCTIONS.**

The existential form of the settlement.  There is an economy `p` — a plain
`AbstractGame.Params`, whose transition `p.F : ℝ → ℝ → ℝ` is a *deterministic
function* of the current state and sanction, with no kernel, no shock and no
smoothing anywhere — and a **constructed** stationary equilibrium `E` of the
resulting infinite-horizon feedback Stackelberg game, such that:

* both discount factors are strictly positive;
* the transition is non-affine at every rate;
* the Target's equilibrium policy is interior at every state (escalation is not
  a corner artefact);
* and from **every** non-maximal initial state, both the political state path
  and the realised sanction path are strictly increasing at every date, forever,
  while the sanction remains strictly below the feasibility ceiling throughout.

Rule 1: `E.α` carries the equilibrium's Bellman-optimality field and the
realised sanction is the Sender's greatest maximiser of its forward-looking
objective; nothing is imposed on either player.

**Quantifier order.**  This is the existential *generalisation* of the named
results above, obtained from them by `⟨niParams, niEquilibrium, …⟩`.  It is
therefore weaker than — not stronger than — the named statements: an economy
that satisfies the named conjunction satisfies this, and the converse direction
is not available.  Its value is that the reader need not inspect the witness to
read the claim, not that it says more.

**What this witness does *not* show** (see `ni_continuation_channel_inactive`).
Both equilibrium value functions are identically zero here, so every
continuation term `β · V(…)` vanishes and the Sender's forward-looking objective
coincides pointwise with its stage payoff.  The discount factors are positive
but multiply nothing.  The escalation is therefore driven by the geometry of the
transition and the shape of the realised rule, *not* by forward-looking
incentives: this settles that determinism does not preclude strict escalation,
and does not exhibit strict escalation sustained by a continuation motive. -/
theorem exists_deterministic_strict_escalation :
    ∃ (p : AbstractGame.Params) (E : p.FeedbackStackelbergEquilibriumTop),
      0 < p.β_S ∧ 0 < p.β_T
      ∧ (∀ d : ℝ, p.F ≠ AbstractGame.affineF d)
      ∧ (∀ x, 0 < E.α x ∧ E.α x < 1)
      ∧ ∀ x₀ ∈ Set.Ico (0 : ℝ) 1,
          StrictMono (p.dynamicTopLockInPathF E.V_S E.α x₀)
          ∧ StrictMono (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)
          ∧ ∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n < 1 := by
  refine ⟨niParams, niEquilibrium, by norm_num [niParams], by norm_num [niParams],
    niParams_F_ne_affine_all, fun x => by norm_num [niEquilibrium, niAlpha], ?_⟩
  intro x₀ hx₀
  exact ⟨(ni_strict_escalation le_rfl hx₀).1, (ni_strict_escalation le_rfl hx₀).2,
    fun n => ni_sanction_lt_one le_rfl hx₀ n⟩

/-! ## Part 3 — Rule-11 refutations at the two economies that fail

### 3a. The eeCert family: `R ≡ 1`, so (ii) fails. -/

/-- At the eeCert `β`-family the realised rule is the constant `1`, hence not
strictly increasing: the escalation there is maximal but only **weak**. -/
theorem eeCertB_rule_not_strictMonoOn (β : ℝ) (hβ : β ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    {V_S : Val} (hV_S : V_S ∈ eeCarrierSB β) {α : ℝ → ℝ}
    (hα : ∀ x ∈ Set.Icc (0 : ℝ) 1, α x ∈ Sanctions.I) :
    ¬ StrictMonoOn ((eeCertParamsB β hβ).dynamicTopRealizedRule V_S α)
        (Set.Ico (0 : ℝ) 1) := by
  intro hmono
  have h0 : (eeCertParamsB β hβ).dynamicTopRealizedRule V_S α 0 = 1 := by
    change (eeCertParamsB β hβ).σ_dyn_top V_S 0 (α 0) = 1
    exact eeCertB_σ_dyn_top_eq_one β hβ hV_S ⟨le_rfl, by norm_num⟩
      (hα 0 ⟨le_rfl, by norm_num⟩)
  have h1 : (eeCertParamsB β hβ).dynamicTopRealizedRule V_S α (1 / 2) = 1 := by
    change (eeCertParamsB β hβ).σ_dyn_top V_S (1 / 2) (α (1 / 2)) = 1
    exact eeCertB_σ_dyn_top_eq_one β hβ hV_S ⟨by norm_num, by norm_num⟩
      (hα (1 / 2) ⟨by norm_num, by norm_num⟩)
  have hcon := hmono (a := 0) ⟨le_rfl, by norm_num⟩ (b := 1 / 2)
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  rw [h0, h1] at hcon
  exact absurd hcon (lt_irrefl 1)

/-! ### 3b. The B2 economy: flat, then too steep. -/

theorem b2clip_id {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : b2clip x = x := by
  unfold b2clip
  rw [max_eq_left hx.1, min_eq_left hx.2]

/-- **The B2 equilibrium realised rule in closed form.**  At the all-defiance
equilibrium policy `α ≡ 0` and any Sender-carrier continuation value, the
forward-looking upper argmax is exactly the clipped slice peak
`b2p x = min 1 (7/8 + (4/3)(x − 5/8)⁺)`. -/
theorem b2_rule_eq {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    b2Params.dynamicTopRealizedRule W (fun _ => (0 : ℝ)) x = b2p x := by
  change b2Params.σ_dyn_top W x 0 = b2p x
  rw [← b2Params.σ_dyn_eq_σ_dyn_top_of_unique W x 0
        ((b2_DAU_on_carrier hW) x hx 0),
      b2_σ_dyn_eq hW hx ⟨le_rfl, zero_le_one⟩]
  unfold b2sdyn b2p
  norm_num

/-- **Flat stretch.**  On `[0, 5/8]` the B2 rule is the constant `7/8`. -/
theorem b2p_flat {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (5 / 8)) : b2p x = 7 / 8 := by
  have h1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  unfold b2p b2pt
  rw [b2clip_id h1, max_eq_right (by linarith [hx.2] : x - 5 / 8 ≤ 0)]
  norm_num

/-- **Steep stretch.**  On `[5/8, 23/32]` the rule rises with slope `4/3`. -/
theorem b2p_mid {x : ℝ} (hx : x ∈ Set.Icc (5 / 8 : ℝ) (23 / 32)) :
    b2p x = 7 / 8 + (4 / 3) * (x - 5 / 8) := by
  have h1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  unfold b2p b2pt
  rw [b2clip_id h1, max_eq_left (by linarith [hx.1] : (0 : ℝ) ≤ x - 5 / 8),
      min_eq_right (by linarith [hx.2] : 7 / 8 + (4 / 3)*(x - 5 / 8) ≤ 1)]

/-- **The escalation gap on the steep stretch is at least `1/4`** — uniformly
bounded away from zero, which is precisely what
`dynamicTopLockInPathF_escape_of_uniform_gap_affine` forbids on an invariant
interval. -/
theorem b2_gap_ge_quarter {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (5 / 8 : ℝ) (23 / 32)) :
    x + 1 / 4 ≤ b2Params.dynamicTopRealizedRule W (fun _ => (0 : ℝ)) x := by
  have h1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [b2_rule_eq hW h1, b2p_mid hx]
  linarith [hx.1]

/-- **No sub-interval of B2's strictly-increasing stretch is forward
invariant**, so the strict-escalation theorem has nowhere to be applied at B2.
Derived from the parametric escalation-gap theorem. -/
theorem b2_steep_window_no_invariant_subinterval {W : Val} (hW : W ∈ b2CarrierS)
    {a b : ℝ} (ha : 5 / 8 ≤ a) (hab : a < b) (hb : b ≤ 23 / 32) :
    ¬ (∀ x ∈ Set.Ico a b,
        b2Params.dynamicTopLockInStepF W (fun _ => (0 : ℝ)) x ∈ Set.Ico a b) := by
  intro hinv
  exact b2Params.dynamicTopLockInPathF_escape_of_uniform_gap_affine
    W (fun _ => (0 : ℝ)) (b := b) (x₀ := a) rfl (by norm_num)
    (fun x hx => b2_gap_ge_quarter hW ⟨le_trans ha hx.1, by linarith [hx.2]⟩)
    hinv ⟨le_rfl, hab⟩

/-- **The B2 rule is not strictly increasing on the basin `[1/2,1)`**: it is
flat at `7/8` across `[1/2, 5/8]`. -/
theorem b2_rule_not_strictMonoOn {W : Val} (hW : W ∈ b2CarrierS) :
    ¬ StrictMonoOn (b2Params.dynamicTopRealizedRule W (fun _ => (0 : ℝ)))
        (Set.Ico (1 / 2 : ℝ) 1) := by
  intro hmono
  have h1 : b2Params.dynamicTopRealizedRule W (fun _ => (0 : ℝ)) (1 / 2) = 7 / 8 := by
    rw [b2_rule_eq hW ⟨by norm_num, by norm_num⟩]
    exact b2p_flat ⟨by norm_num, by norm_num⟩
  have h2 : b2Params.dynamicTopRealizedRule W (fun _ => (0 : ℝ)) (9 / 16) = 7 / 8 := by
    rw [b2_rule_eq hW ⟨by norm_num, by norm_num⟩]
    exact b2p_flat ⟨by norm_num, by norm_num⟩
  have hcon := hmono (a := 1 / 2) ⟨le_rfl, by norm_num⟩ (b := 9 / 16)
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  rw [h1, h2] at hcon
  exact absurd hcon (lt_irrefl _)

/-- What *does* survive at B2: the rule clears the diagonal everywhere below
the top state. -/
theorem b2p_gt_self {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) : x < b2p x := by
  rcases lt_or_ge x (7 / 8) with h | h
  · have hge : (7 : ℝ)/8 ≤ b2p x := le_min (by norm_num) (b2pt_lb x)
    linarith
  · have hclip : b2clip x = x := b2clip_id ⟨hx.1, hx.2.le⟩
    have hpt : (1 : ℝ) ≤ b2pt x := by
      unfold b2pt
      rw [hclip, max_eq_left (by linarith : (0 : ℝ) ≤ x - 5 / 8)]
      linarith
    have hone : b2p x = 1 := min_eq_left hpt
    rw [hone]; exact hx.2

theorem b2Params_F_strictMono_s (x : ℝ) :
    StrictMono (fun s => b2Params.F x s) := by
  intro s₁ s₂ h
  change b2Params.F x s₁ < b2Params.F x s₂
  rw [b2Params_F, b2Params_F]
  linarith

theorem b2_stepF_mem_Ico {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Ico (1 / 2 : ℝ) 1) :
    b2Params.dynamicTopLockInStepF W (fun _ => (0 : ℝ)) x ∈ Set.Ico (1 / 2 : ℝ) 1 := by
  have h01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2.le⟩
  change b2Params.F x (b2Params.dynamicTopRealizedRule W (fun _ => (0 : ℝ)) x)
      ∈ Set.Ico (1 / 2 : ℝ) 1
  rw [b2_rule_eq hW h01, b2Params_F]
  have hgt := b2p_gt_self ⟨by linarith [hx.1], hx.2⟩
  have hle : b2p x ≤ 1 := min_le_left _ _
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **B2's state path is genuinely strictly increasing** on the basin: the
failure at B2 is located exactly in condition (ii) (strict monotonicity of the
rule), not in (i) or (iii). Applied through the `_of_strictMono_s` form, since
`b2Params`' transition is strictly increasing in the sanction (BG2.3). -/
theorem b2_state_path_strictMono {W : Val} (hW : W ∈ b2CarrierS)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    StrictMono (b2Params.dynamicTopLockInPathF W (fun _ => (0 : ℝ)) x₀) :=
  b2Params.dynamicTopLockInPathF_strictMono_of_gt_self_of_strictMono_s W
    (fun _ => (0 : ℝ))
    b2Params_F_strictMono_s
    (fun x hx => by
      rw [b2_rule_eq hW ⟨by linarith [hx.1], hx.2.le⟩]
      exact b2p_gt_self ⟨by linarith [hx.1], hx.2⟩)
    (fun x hx => b2_stepF_mem_Ico hW hx) hx₀

/-! ## Axiom hygiene (Rule 10) -/

#print axioms ni_strict_escalation
#print axioms ni_deterministic_strict_escalation_integrated
#print axioms exists_deterministic_strict_escalation
#print axioms ni_continuation_channel_inactive
#print axioms niParams_F_ne_affine_all
#print axioms ni_sanction_lt_one
#print axioms eeCertB_rule_not_strictMonoOn
#print axioms b2_steep_window_no_invariant_subinterval
#print axioms b2_rule_not_strictMonoOn
#print axioms b2_state_path_strictMono

end

end Examples
end Sanctions
