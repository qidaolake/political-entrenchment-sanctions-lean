/-
Sanctions/Examples/PlacableSenderNetDefiance.lean

**The forward-looking defiance results under the net-of-compliance condition** (step 2,
target 2a, 2026-10-10; referee M1, fix 1).

The forward-looking headlines of the class (cell `11` of the four cases, part (ii) of the
regime separation, the defiance clause of the class under placability, the Sender wedge,
the long-run gap and resumption after an imposed episode) were stated under the loss-offset
condition `c ≤ β_T·d_lo·g_T`. Their proofs read that condition only to name the constructed
full-defiance equilibrium (`equilibriumTop hTM hmono`). This file restates them in two
steps.

* **At every full-defiance equilibrium, with no defiance condition.** Every top-selector
  equilibrium in which the Target defies at every state has the constructed values and the
  response `responsePath VSstar` as its rule (`values_eq_of_policy_zero`), so its state path
  is the one path `fullDefiancePath` (`rulePath_eq_fullDefiancePath_of_policy_zero`). The same
  holds for the Target-only reading `10`, whose rule is the stage selector `σ(x,0)` whatever the
  values (`pT_rulePath_eq_stagePath_of_policy_zero`), with path `stagePath`. The path
  results (wash-in, domination of the myopic path, convergence, the wedge, the long-run gap,
  resumption, a unique attracting state) are proved for these two paths, hence at every
  full-defiance equilibrium of either reading.
* **Existence under the net condition ND.** A slope `g ≥ 0` with
  (ND-a) `c − ℓ_lo·μ/k_hi ≤ β_T·d_lo·g` and
  (ND-b) `g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·L_resp/μ ≤ v_lo + n_lo·b`
  (`NetDefianceAt`). These are exactly the hypotheses of the existing `equilibriumTop_sharp`
  (`prop:bracket`(i)); no new hypothesis. (ND-a) says the net pain of a unit of sanction is at
  most the least cost of avoiding it by compliance: a unit of compliance costs at least `ℓ_lo`
  and removes at most `k_hi/μ` units of sanction. (ND-b) certifies that the Target's value
  rises at rate at least `g`. Under ND and a nondecreasing response, full defiance is a
  Target best reply at the defiance-profile values (`defianceBestReply_of_netDefiance`), so
  a full-defiance equilibrium exists (`netDefianceEquilibrium`). The loss-offset condition
  implies ND at `g_T` (`netDefianceAt_gT_of_lossOffset`); the converse fails (witnesses in
  `PlacableSenderNetDefianceWitnesses.lean`).

**Uniqueness.** Full defiance is the Target's *unique* best reply at every full-defiance
equilibrium under the strict form of (ND-a) (`StrictNetDefiance`; approved hypothesis 2 of
the step-2 sign-off, used only for best-reply uniqueness clauses). Nothing here says that
the full-defiance equilibrium is the unique equilibrium: just above the existence threshold
a non-defiance equilibrium can coexist with it.

**What stays under the loss-offset condition.** The minmax (`prop:security`), the
identification and monotone-uniqueness results and the Target half of relief participation
are not restated: outside the loss-offset region they are false or unproved. That region is
the one in which sanctions are a political good for the Target.

Rule 3: no new hypothesis beyond approved hypothesis 2 (the strict form, uniqueness clauses
only). Rule 22: general in `F` (chord conditions only). Rule 9: witnesses in
`PlacableSenderNetDefianceWitnesses.lean`.
-/
import Sanctions.Examples.PlacableSenderWedge
import Sanctions.Examples.PlacableSenderPatienceExistence
import Sanctions.Examples.PlacableSenderBracketSatellites

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.GeometricApproach
  Sanctions.Mechanism

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. The two full-defiance paths, with no defiance condition -/

/-- **The full-defiance path of the forward-looking reading**: the state path under the
response `responsePath VSstar`. Every full-defiance equilibrium of the forward-looking
reading has this path (`rulePath_eq_fullDefiancePath_of_policy_zero`).
Scope: general class. -/
def fullDefiancePath (x₀ : ℝ) (t : ℕ) : ℝ := E.toParams.rulePathF (E.responsePath E.VSstar) x₀ t

/-- **The full-defiance path of the Target-only reading**: the state path under the stage
selector `σ(x, 0)`. Every full-defiance equilibrium of the reading `10` has this path
(`pT_rulePath_eq_stagePath_of_policy_zero`).
Scope: general class. -/
def stagePath (x₀ : ℝ) (t : ℕ) : ℝ := E.toParams.rulePathF E.stageResp x₀ t

/-- The full-defiance path stays in `[0, 1]`.
Scope: general class. -/
theorem fullDefiancePath_mem {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.fullDefiancePath x₀ t ∈ Sanctions.I :=
  E.toParams.rulePathF_mem_I (fun x _ => E.responsePath_mem E.VSstar x) hx₀ t

/-- The stage path stays in `[0, 1]`.
Scope: general class. -/
theorem stagePath_mem {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.stagePath x₀ t ∈ Sanctions.I :=
  E.toParams.rulePathF_mem_I (fun x _ => E.stageResp_mem x) hx₀ t

/-- **Every full-defiance equilibrium follows the full-defiance path.** If the Target
defies at every feasible state, the realised rule is the response `responsePath VSstar`
(`values_eq_of_policy_zero`), so from every feasible start the equilibrium's state path is
`fullDefiancePath`. No defiance condition and no monotonicity are read.
Scope: general class. -/
theorem rulePath_eq_fullDefiancePath_of_policy_zero
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀ t
      = E.fullDefiancePath x₀ t :=
  E.toParams.rulePathF_congr_on (fun _ _ => E.toParams.σ_dyn_top_mem_I _ _ _)
    (E.values_eq_of_policy_zero Eq hα).2.2 hx₀

/-- **The rule of every full-defiance equilibrium of the Target-only reading is the stage
selector.** At `β_S = 0` the Sender's top selector is the stage argmax at every value
(`pT_σ_dyn_top`), so full defiance gives the sanction `σ(x, 0)`. No defiance condition is
read.
Scope: general class. -/
theorem pT_rule_eq_stage_of_policy_zero
    (Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pT.dynamicEquilibriumRule Eq x = E.σ x 0 := by
  change E.pT.σ_dyn_top Eq.V_S x (Eq.α x) = E.toParams.σ x 0
  rw [hα x hx]
  exact E.pT_σ_dyn_top _ hx 0

/-- **Every full-defiance equilibrium of the Target-only reading follows the stage path.**
Scope: general class. -/
theorem pT_rulePath_eq_stagePath_of_policy_zero
    (Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq) x₀ t = E.stagePath x₀ t :=
  E.toParams.rulePathF_congr_on (fun _ _ => E.pT.σ_dyn_top_mem_I _ _ _)
    (fun _ hx => E.pT_rule_eq_stage_of_policy_zero Eq hα hx) hx₀

/-- **Wash-in along the full-defiance path**: the state dominates the approach to the floor
`b = σ(0, 0)` at rate `d_lo`. No defiance condition.
Scope: general class. -/
theorem fullDefiancePath_ge_approach {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, approach E.sfloor E.dlo t ≤ E.fullDefiancePath x₀ t :=
  E.toParams.rulePathF_ge_approach_of_rule_ge E.hdlo0.le E.hSlo E.sfloor_mem
    (fun x _ => E.responsePath_mem E.VSstar x)
    (fun _ hx => E.responsePath_ge_sfloor E.VSstar_mem hx) hx₀

/-- **Wash-in along the stage path.** No defiance condition.
Scope: general class. -/
theorem stagePath_ge_approach {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, approach E.sfloor E.dlo t ≤ E.stagePath x₀ t :=
  E.toParams.rulePathF_ge_approach_of_rule_ge E.hdlo0.le E.hSlo E.sfloor_mem
    (fun x _ => E.stageResp_mem x) (fun _ hx => E.stageResp_ge_sfloor hx) hx₀

/-- **The full-defiance path converges to an interior steady state**, given a nondecreasing
response: `ρ(z) = z ∈ (b, A/q]`. Under the stage appetite `u_hi < q`. No defiance
condition: the response is nondecreasing and continuous, so the path is monotone and
converges.
Scope: general class. -/
theorem fullDefiancePath_tendsto (hS : E.uhi < E.q)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
      Tendsto (E.fullDefiancePath x₀) atTop (𝓝 z) := by
  obtain ⟨z, hz, hfix, htend⟩ := E.toParams.rulePathF_tendsto_fixedPoint_of_monotoneOn
    (fun x _ => E.responsePath_mem E.VSstar x) hmono (E.responsePath_continuousOn E.VSstar_mem)
    hx₀
  have hrz := E.toParams.rule_eq_self_of_closedLoop_fixed E.hdlo0 E.hSlo hz
    (E.responsePath_mem E.VSstar z) hfix
  refine ⟨z, hz, hrz, ?_, ?_, htend⟩
  · rw [← hrz]; exact E.responsePath_gt_sfloor hS E.VSstar_mem hz
  · rw [← hrz]; exact E.responsePath_le_cap E.VSstar_mem hz

/-- **The stage path converges to a fixed point of the stage selector**, `σ(z, 0) = z ≥ b`,
from every start. No defiance condition.
Scope: general class. -/
theorem stagePath_tendsto {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧ Tendsto (E.stagePath x₀) atTop (𝓝 z) := by
  obtain ⟨z, hz, hfix, htend⟩ := E.toParams.rulePathF_tendsto_fixedPoint_of_monotoneOn
    (fun x _ => E.stageResp_mem x) E.stageResp_monotoneOn E.stageResp_continuous.continuousOn hx₀
  have hRz := E.toParams.rule_eq_self_of_closedLoop_fixed E.hdlo0 E.hSlo hz (E.stageResp_mem z) hfix
  refine ⟨z, hz, hRz, ?_, htend⟩
  rw [← hRz]
  exact E.stageResp_ge_sfloor hz

/-- **The full-defiance path dominates the stage path**, given a nondecreasing response:
the response lies above the stage selector at every state (`response_ge_stage`) and is
nondecreasing, so the comparison carries along the paths. No defiance condition.
Scope: general class. -/
theorem stagePath_le_fullDefiancePath (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, E.stagePath x₀ t ≤ E.fullDefiancePath x₀ t :=
  E.toParams.rulePathF_le_of_rule_le_and_upper_mono (fun x _ => E.stageResp_mem x)
    (fun x _ => E.responsePath_mem E.VSstar x) hmono
    (fun _ hx => E.response_ge_stage E.VSstar_mem hx 0) hx₀

/-- **The stage limit lies strictly below the full-defiance limit**, from every start, given
a nondecreasing response and the stage appetite `u_hi < q`. The strict order comes from the
strict wedge `σ(x,0) < ρ(x)` (`responsePath_gt_stage`). No defiance condition.
Scope: general class. -/
theorem stagePath_limit_lt_fullDefiancePath_limit (hS : E.uhi < E.q)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ z₁₀ < z ∧
      Tendsto (E.stagePath x₀) atTop (𝓝 z₁₀) ∧ Tendsto (E.fullDefiancePath x₀) atTop (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, hfix₁₀, -, ht₁₀⟩ := E.stagePath_tendsto hx₀
  obtain ⟨z, hz, hfix, -, -, ht⟩ := E.fullDefiancePath_tendsto hS hmono hx₀
  have hle : z₁₀ ≤ z :=
    le_of_tendsto_of_tendsto' ht₁₀ ht (E.stagePath_le_fullDefiancePath hmono hx₀)
  refine ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, ?_, ht₁₀, ht⟩
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    have hgt := E.responsePath_gt_stage hS E.VSstar_mem hz
    rw [hfix] at hgt
    linarith [hfix₁₀]

/-! ## 2. The wedge, the long-run gap and resumption, at every full-defiance equilibrium -/

/-- **The wedge along the full-defiance paths**: from a common start, at every date, the
forward-looking sanction exceeds the stage sanction by at least the wedge
`β_S·g_S·d_lo/Q̄`. Under interiority (the cap `A/q < 1`) and a nondecreasing response. No
defiance condition.
Scope: general class. -/
theorem stageSanction_add_wedge_le_defianceSanction (hInt : E.Interior)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.σ (E.stagePath x₀ t) 0 + E.wedge ≤ E.responsePath E.VSstar (E.fullDefiancePath x₀ t) := by
  have h10 := E.stagePath_mem hx₀ t
  have h11 := E.fullDefiancePath_mem hx₀ t
  have hv : E.σ (E.stagePath x₀ t) 0 ≤ E.σ (E.fullDefiancePath x₀ t) 0 :=
    E.stage_argmax_mono h10 h11 (E.stagePath_le_fullDefiancePath hmono hx₀ t)
  have := E.responsePath_ge_stage_add_wedge hInt E.VSstar_mem h11
  linarith

/-- **The long-run gap along the full-defiance paths**: from every start the stage path
converges to a fixed point `z₁₀` of the stage selector, the full-defiance path to a fixed
point `z` of the response, and `z ≥ z₁₀ + β_S·w_lo·d_lo/((Q̄ − r_lo)(1 − β_S·g_lo))`. Under
interiority and a nondecreasing response. No defiance condition.
Scope: general class. -/
theorem fullDefiancePath_limit_ge_stagePath_limit_add_gap (hInt : E.Interior)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧
      z₁₀ + E.β_S * E.wlo * E.dlo / ((E.Qbar - E.rlo) * (1 - E.β_S * E.glo)) ≤ z ∧
      Tendsto (E.stagePath x₀) atTop (𝓝 z₁₀) ∧ Tendsto (E.fullDefiancePath x₀) atTop (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hlt, ht₁₀, ht⟩ :=
    E.stagePath_limit_lt_fullDefiancePath_limit (E.uhi_lt_q hInt) hmono hx₀
  refine ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, ?_, ht₁₀, ht⟩
  rw [← E.steadyGap_eq (E.uhi_lt_q hInt)]
  exact E.fixedPoint_ge_limit10_add_gap hInt hz hz₁₀ hfix hfix₁₀ hlt.le

/-- **The wedge and the long-run gap at every pair of full-defiance equilibria** (the
Target-only reading `10` and the forward-looking reading `11`). At every state the `11` rule
exceeds the `10` rule by at least the wedge; from a common start the `11` path dominates the
`10` path, the realised sanctions differ by at least the wedge at every date, and the limits
satisfy `z ≥ z₁₀ + β_S·w_lo·d_lo/((Q̄ − r_lo)(1 − β_S·g_lo))`. Under interiority and a
nondecreasing response; no defiance condition (existence is separate: ND for `11` and for
`10`, through ND10).
Scope: general class. -/
theorem wedge_and_gap_of_policy_zero (hInt : E.Interior)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (Eq₁₀ : E.toParams.RegimeEquilibrium ContinuationProfile.p10)
    (hα₁₀ : ∀ x ∈ Sanctions.I, Eq₁₀.α x = 0)
    (Eq₁₁ : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hα₁₁ : ∀ x ∈ Sanctions.I, Eq₁₁.α x = 0) :
    (∀ x ∈ Sanctions.I, E.pT.dynamicEquilibriumRule Eq₁₀ x + E.wedge
        ≤ E.toParams.dynamicEquilibriumRule Eq₁₁ x) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq₁₀) x₀ t
        ≤ E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq₁₁) x₀ t) ∧
      (∀ t, E.pT.dynamicEquilibriumRule Eq₁₀
            (E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq₁₀) x₀ t) + E.wedge
          ≤ E.toParams.dynamicEquilibriumRule Eq₁₁
            (E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq₁₁) x₀ t)) ∧
      ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
        E.responsePath E.VSstar z = z ∧
        z₁₀ + E.β_S * E.wlo * E.dlo / ((E.Qbar - E.rlo) * (1 - E.β_S * E.glo)) ≤ z ∧
        Tendsto (E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq₁₀) x₀) atTop (𝓝 z₁₀) ∧
        Tendsto (E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq₁₁) x₀) atTop
          (𝓝 z)) := by
  have hR₁₁ := (E.values_eq_of_policy_zero Eq₁₁ hα₁₁).2.2
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_⟩
  · rw [E.pT_rule_eq_stage_of_policy_zero Eq₁₀ hα₁₀ hx, hR₁₁ x hx]
    exact E.responsePath_ge_stage_add_wedge hInt E.VSstar_mem hx
  have hp₁₀ := E.pT_rulePath_eq_stagePath_of_policy_zero Eq₁₀ hα₁₀ hx₀
  have hp₁₁ := E.rulePath_eq_fullDefiancePath_of_policy_zero Eq₁₁ hα₁₁ hx₀
  have hf₁₀ : E.toParams.rulePathF (E.pT.dynamicEquilibriumRule Eq₁₀) x₀ = E.stagePath x₀ :=
    funext hp₁₀
  have hf₁₁ : E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq₁₁) x₀
      = E.fullDefiancePath x₀ := funext hp₁₁
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · rw [hp₁₀ t, hp₁₁ t]; exact E.stagePath_le_fullDefiancePath hmono hx₀ t
  · rw [hp₁₀ t, hp₁₁ t, E.pT_rule_eq_stage_of_policy_zero Eq₁₀ hα₁₀ (E.stagePath_mem hx₀ t),
      hR₁₁ _ (E.fullDefiancePath_mem hx₀ t)]
    exact E.stageSanction_add_wedge_le_defianceSanction hInt hmono hx₀ t
  · rw [hf₁₀, hf₁₁]
    exact E.fullDefiancePath_limit_ge_stagePath_limit_add_gap hInt hmono hx₀

/-- **Temporary relief does not end any full-defiance equilibrium.** After any feasible
imposed sanction schedule `u` of any length `T` (zero sanctions included), every
full-defiance equilibrium, restarted at the episode-end state, sanctions at least the stage
selector plus the wedge at every later date, and its state converges to a fixed point of
the response strictly above the floor `b = σ(0,0)`. Under interiority and a nondecreasing
response; no defiance condition.
Scope: general class. -/
theorem resumption_after_episode_of_policy_zero (hInt : E.Interior)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, E.σ (E.toParams.splicedPath Eq.V_S Eq.α u T x₀ (T + n)) 0 + E.wedge
        ≤ E.toParams.splicedSanction Eq.V_S Eq.α u T x₀ (T + n)) ∧
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧
      Tendsto (fun n => E.toParams.splicedPath Eq.V_S Eq.α u T x₀ (T + n)) atTop (𝓝 z) := by
  have hend : E.toParams.episodePath u x₀ T ∈ Sanctions.I := E.toParams.episodePath_mem hu hx₀ T
  have hpath : ∀ n, E.toParams.splicedPath Eq.V_S Eq.α u T x₀ (T + n)
      = E.fullDefiancePath (E.toParams.episodePath u x₀ T) n := fun n => by
    rw [E.toParams.splicedPath_add]
    exact E.rulePath_eq_fullDefiancePath_of_policy_zero Eq hα hend n
  have hR := (E.values_eq_of_policy_zero Eq hα).2.2
  refine ⟨fun n => ?_, ?_⟩
  · have hmemn := E.fullDefiancePath_mem hend n
    rw [E.toParams.splicedSanction_of_not_lt Eq.V_S Eq.α x₀ (Nat.not_lt.2 (Nat.le_add_right T n)),
      hpath n]
    exact (E.responsePath_ge_stage_add_wedge hInt E.VSstar_mem hmemn).trans_eq (hR _ hmemn).symm
  · obtain ⟨z, hz, hfix, hgt, -, htend⟩ := E.fullDefiancePath_tendsto (E.uhi_lt_q hInt) hmono hend
    have hf : (fun n => E.toParams.splicedPath Eq.V_S Eq.α u T x₀ (T + n))
        = E.fullDefiancePath (E.toParams.episodePath u x₀ T) := funext hpath
    exact ⟨z, hz, hfix, hgt, by rw [hf]; exact htend⟩

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-! ## 3. The net-of-compliance defiance condition -/

/-- **The net defiance condition at the slope `g`** (ND): `g ≥ 0`,
(ND-a) `c − ℓ_lo·μ/k_hi ≤ β_T·d_lo·g`, and
(ND-b) `g(1 − β_T g_lo) + max{0, c − β_T d_lo g}·L_resp/μ ≤ v_lo + n_lo·b`.
The three inequalities are the hypotheses of `equilibriumTop_sharp` (`prop:bracket`(i));
written over the class's own data (Rule 14).
Scope: general class (relief extension). -/
def NetDefianceAt (g : ℝ) : Prop :=
  0 ≤ g ∧ E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * g ∧
    g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor

/-- **The net defiance condition** (ND): some slope satisfies `NetDefianceAt`.
Scope: general class (relief extension). -/
def NetDefiance : Prop := ∃ g, E.NetDefianceAt g

/-- **The strict net defiance condition at `g`**: (ND-a) strict. Approved hypothesis 2 of
the step-2 sign-off: read only by best-reply uniqueness clauses.
Scope: general class (relief extension); approved hypothesis 2 (strict form). -/
def StrictNetDefianceAt (g : ℝ) : Prop :=
  0 ≤ g ∧ E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * g ∧
    g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor

/-- **The strict net defiance condition**: some slope satisfies `StrictNetDefianceAt`.
Scope: general class (relief extension); approved hypothesis 2 (strict form). -/
def StrictNetDefiance : Prop := ∃ g, E.StrictNetDefianceAt g

/-- The strict condition implies the weak one at the same slope.
Scope: general class (relief extension); approved hypothesis 2 (strict form). -/
theorem StrictNetDefianceAt.toNetDefianceAt {E : ChordEconomyRelief} {g : ℝ}
    (h : E.StrictNetDefianceAt g) : E.NetDefianceAt g :=
  ⟨h.1, h.2.1.le, h.2.2⟩

/-- The strict condition implies the weak one.
Scope: general class (relief extension); approved hypothesis 2 (strict form). -/
theorem StrictNetDefiance.toNetDefiance {E : ChordEconomyRelief} (h : E.StrictNetDefiance) :
    E.NetDefiance :=
  let ⟨g, hg⟩ := h
  ⟨g, hg.toNetDefianceAt⟩

/-- **The loss-offset condition implies the strict net condition at `g_T`**: since
`ℓ_lo > 0` the margin `c ≤ β_T d_lo g_T` gives the strict (ND-a), and under the margin the
pain term of (ND-b) vanishes, where `g_T` balances (`gT_balance`).
Scope: general class (relief extension). -/
theorem strictNetDefianceAt_gT_of_lossOffset (hTM : E.LossOffset) :
    E.StrictNetDefianceAt E.gT :=
  ⟨E.gT_pos.le, E.sharp_of_lossOffset E.placationCeiling hTM, E.gT_balance hTM⟩

/-- **The loss-offset condition implies ND at `g_T`.**
Scope: general class (relief extension). -/
theorem netDefianceAt_gT_of_lossOffset (hTM : E.LossOffset) : E.NetDefianceAt E.gT :=
  (E.strictNetDefianceAt_gT_of_lossOffset hTM).toNetDefianceAt

/-- **The loss-offset condition implies the strict net condition.**
Scope: general class (relief extension). -/
theorem strictNetDefiance_of_lossOffset (hTM : E.LossOffset) : E.StrictNetDefiance :=
  ⟨E.gT, E.strictNetDefianceAt_gT_of_lossOffset hTM⟩

/-- **The loss-offset condition implies ND.**
Scope: general class (relief extension). -/
theorem netDefiance_of_lossOffset (hTM : E.LossOffset) : E.NetDefiance :=
  (E.strictNetDefiance_of_lossOffset hTM).toNetDefiance

/-- **ND at `g_T` when the response does not move with the state** (`L_resp = 0`): then
(ND-b) holds at `g_T` and ND reads `c − ℓ_lo μ/k_hi ≤ β_T d_lo g_T`.
Scope: general class (relief extension). -/
theorem netDefianceAt_gT_of_Lresp_eq_zero (hL : E.Lresp = 0)
    (hside : E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * E.gT) : E.NetDefianceAt E.gT :=
  ⟨E.gT_pos.le, hside, E.gT_balance_of_Lresp_eq_zero hL⟩

/-- **ND at the sharp slope `min{g_T, g_eff}`**, under the lower loop condition
`β_T(g_lo + d_lo L_resp/μ) < 1` and `c·L_resp/μ < v_lo + n_lo·b`, whenever
`c − ℓ_lo μ/k_hi ≤ β_T d_lo min{g_T, g_eff}` (the closed form of `prop:bracket`(i)).
Scope: general class (relief extension). -/
theorem netDefianceAt_gSharp (hγ : E.β_T * E.LloopLo < 1)
    (hvL : E.c * (E.Lresp / E.mu) < E.vlo + E.nlo * E.sfloor)
    (hside : E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * E.gSharp) :
    E.NetDefianceAt E.gSharp :=
  ⟨E.gSharp_nonneg hγ hvL, hside, E.gSharp_balance_lo hγ⟩

/-! ## 4. Full defiance is a best reply under ND; the equilibrium -/

/-- **Under ND and a nondecreasing response, full defiance is a Target best reply at the
defiance-profile values** (`VTdef`, `VSstar`): the defiance-profile value carries the slope
`g` (ND-b, `VTdef_lowerSlope`), and against the response a unit of compliance saves at most
`c` per unit of sanction while removing at most `k_hi/μ` units of it, costs at least
`ℓ_lo` and loses at least `β_T·d_lo·g` of continuation per unit of sanction (ND-a).
Scope: general class (relief extension). -/
theorem defianceBestReply_of_netDefiance
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.NetDefiance) :
    E.DefianceBestReply := by
  obtain ⟨g, hg, hside, hbal⟩ := hND
  intro x hx
  rw [isMaxOn_iff]
  intro a ha
  rw [E.joint_T_top_integrand_eq E.VSstar_mem _ hx, E.joint_T_top_integrand_eq E.VSstar_mem _ hx]
  exact E.zero_isMaxOn_joint_of_sharp E.placationCeiling hg hside
    (E.VTdef_lowerSlope hmono hg hbal) E.VSstar_mem hx ha

/-- **Under strict ND, full defiance is the Target's unique best reply at the
defiance-profile values.**
Scope: general class (relief extension); approved hypothesis 2 (strict form, uniqueness
clause only). -/
theorem defiance_argmax_unique_of_strictNetDefiance
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.StrictNetDefiance)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.toParams.joint_T_top_integrand E.VTdef E.VSstar x b)
      Sanctions.I a) :
    a = 0 := by
  obtain ⟨g, hg, hside, hbal⟩ := hND
  apply E.targetArgmax_eq_zero_of_sharp E.placationCeiling hg hside
    (E.VTdef_lowerSlope hmono hg hbal) E.VSstar_mem hx ha
  intro b hb
  have := hmax hb
  simp only [Set.mem_setOf_eq] at this ⊢
  rwa [E.joint_T_top_integrand_eq E.VSstar_mem _ hx,
    E.joint_T_top_integrand_eq E.VSstar_mem _ hx] at this

/-- **At every full-defiance equilibrium, under strict ND, full defiance is the Target's
unique optimum at every state.** Every such equilibrium has the defiance-profile values
(`values_eq_of_policy_zero`). This is a statement about the Target's best reply, not about
uniqueness of the equilibrium.
Scope: general class (relief extension); approved hypothesis 2 (strict form, uniqueness
clause only). -/
theorem policy_zero_argmax_unique_of_strictNetDefiance
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.StrictNetDefiance)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x b)
      Sanctions.I a) :
    a = Eq.α x := by
  obtain ⟨hVS, hVT, -⟩ := E.values_eq_of_policy_zero Eq hα
  rw [hα x hx]
  rw [hVS, hVT] at hmax
  exact E.defiance_argmax_unique_of_strictNetDefiance hmono hND hx ha hmax

/-- **The full-defiance equilibrium under ND**: the construction `defianceEquilibrium` at
the best-reply property that ND gives. Values `VTdef`, `VSstar`, policy full defiance.
Scope: general class (relief extension). -/
def netDefianceEquilibrium (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hND : E.NetDefiance) : E.toParams.FeedbackStackelbergEquilibriumTop :=
  E.defianceEquilibrium (E.defianceBestReply_of_netDefiance hmono hND)

/-- The state path of `netDefianceEquilibrium`.
Scope: general class (relief extension). -/
def netDefiancePath (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hND : E.NetDefiance) (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule (E.netDefianceEquilibrium hmono hND))
    x₀ t

/-- **A full-defiance equilibrium exists under ND and a nondecreasing response.**
Scope: general class (relief extension). -/
theorem exists_defiance_equilibrium_of_netDefiance
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.NetDefiance) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  ⟨E.netDefianceEquilibrium hmono hND, fun _ _ => rfl⟩

/-! ## 5. Regime separation (ii) and the class under placability, net form -/

/-- **The forward-looking path strictly dominates the stage-form myopic path**, from a
common feasible start, at every positive date. Under the stage appetite, the stage relief
margin and the stage placability (which define the myopic equilibrium); no defiance
condition.
Scope: general class (relief extension). -/
theorem myopicPathS_lt_fullDefiancePath (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hPs : E.uhi < E.klo) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ E.fullDefiancePath x₀ t
      ∧ (1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < E.fullDefiancePath x₀ t) := by
  have hzero : ∀ t, (E.myopicPathS hS hSR hPs) x₀ t
      = E.toParams.rulePathF (fun _ => 0) x₀ t :=
    E.toParams.rulePathF_congr_on
      (fun x hx => by rw [(E.myopicRuleS_eq_zero hS hSR hPs) hx]; exact ⟨le_rfl, zero_le_one⟩)
      (fun x hx => (E.myopicRuleS_eq_zero hS hSR hPs) hx) hx₀
  have h := E.toParams.rulePathF_gt_zero_rule_of_pos E.hdlo0 E.hSlo
    (fun x _ => E.responsePath_mem E.VSstar x)
    (fun _ hx => E.responsePath_pos E.VSstar_mem hx) hx₀
  intro t
  rw [hzero t]
  exact h t

/-- **The forward-looking side of the regime separation at every full-defiance
equilibrium.** At every state the sanction lies in `(σ(x,0), A/q]`; from every start the
state dominates the approach `b(1 − (1 − d_lo)^t)`, strictly dominates the myopic state at
every positive date, and converges to a steady state with sanction equal to state in
`(b, A/q]`. Under the stage appetite, the stage relief margin, the stage placability and a
nondecreasing response; no defiance condition (existence is
`exists_defiance_equilibrium_of_netDefiance`).
Scope: general class (relief extension). -/
theorem defiance_side_of_policy_zero (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hPs : E.uhi < E.klo) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    (∀ x ∈ Sanctions.I,
      E.toParams.σ x 0 < E.toParams.dynamicEquilibriumRule Eq x ∧
      E.toParams.dynamicEquilibriumRule Eq x ≤ E.cap) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t
        ≤ E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t
        < E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto (E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀) atTop
          (𝓝 z)) := by
  have hR := (E.values_eq_of_policy_zero Eq hα).2.2
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_⟩
  · rw [hR x hx]
    exact ⟨E.responsePath_gt_stage hS E.VSstar_mem hx, E.responsePath_le_cap E.VSstar_mem hx⟩
  have hp := E.rulePath_eq_fullDefiancePath_of_policy_zero Eq hα hx₀
  have hf : E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀
      = E.fullDefiancePath x₀ := funext hp
  refine ⟨fun t => ?_, fun t ht => ?_, ?_⟩
  · rw [hp t]; exact E.fullDefiancePath_ge_approach hx₀ t
  · rw [hp t]; exact (E.myopicPathS_lt_fullDefiancePath hS hSR hPs hx₀ t).2 ht
  · rw [hf]; exact E.fullDefiancePath_tendsto hS hmono hx₀

/-- **Regime separation under the net defiance condition, general in `F`** (net form of
`myopic_dynamic_equilibrium_separation_generalF_stage_of_response_monotone`). The myopic
Target complies partially and uniquely, buys a zero sanction, and the state washes out. Under
ND a full-defiance equilibrium of the forward-looking reading exists; at it the sanction is
strictly above the stage selector and at most `A/q`, the state dominates the myopic state at
every positive date from any common start, and it converges to a steady state with sanction
equal to state in `(b, A/q]`. The loss-offset condition is replaced by ND, which it implies
(`netDefiance_of_lossOffset`). Clauses (3)–(4) hold at every full-defiance equilibrium
(`defiance_side_of_policy_zero`).
Scope: general class (relief extension). -/
theorem myopic_dynamic_equilibrium_separation_net (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hPs : E.uhi < E.klo) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hND : E.NetDefiance) :
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTopS hS hSR hPs).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTopS hS hSR hPs).V_T
          (E.myopicEquilibriumTopS hS hSR hPs).V_S x b) Sanctions.I a →
            a = (E.myopicEquilibriumTopS hS hSR hPs).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPathS hS hSR hPs) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: defiance, strict wedge, the cap
    (∀ x ∈ Sanctions.I,
      (E.netDefianceEquilibrium hmono hND).α x = 0 ∧
      E.toParams.σ x 0 < E.toParams.dynamicEquilibriumRule (E.netDefianceEquilibrium hmono hND) x ∧
      E.toParams.dynamicEquilibriumRule (E.netDefianceEquilibrium hmono hND) x ≤ E.cap) ∧
    -- (4) paths: wash-in, strict dominance, the limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t ≤ E.netDefiancePath hmono hND x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < E.netDefiancePath hmono hND x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto (E.netDefiancePath hmono hND x₀) atTop (𝓝 z)) := by
  obtain ⟨h3, h4⟩ := E.defiance_side_of_policy_zero hS hSR hPs hmono
    (E.netDefianceEquilibrium hmono hND) (fun _ _ => rfl)
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ?_, fun x hx => ⟨rfl, h3 x hx⟩, h4⟩
  · intro x hx
    exact ⟨(E.myopicPolicy_mem_Ioo hPs) hx,
      fun a ha hmax => (E.myopicEquilibriumTopS_argmax_unique hS hSR hPs) hx ha hmax,
      (E.myopicRuleS_eq_zero hS hSR hPs) hx⟩
  · intro x₀ hx₀
    exact ⟨(E.myopicPathS_le_geom hS hSR hPs) hx₀, (E.myopicPathS_tendsto_zero hS hSR hPs) hx₀⟩

/-- **Regime separation under the net defiance condition, at interiority, placability and
the dynamic complementarity condition** (the net form of the pinned
`myopic_dynamic_equilibrium_separation_generalF`, with the loss-offset condition replaced by
ND). The dynamic complementarity condition is read only to make the response
nondecreasing; interiority adds the clause `A/q < 1`.
Scope: general class (relief extension). -/
theorem myopic_dynamic_equilibrium_separation_net_of_margin (hInt : E.Interior)
    (hSR : E.StageRelief) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hND : E.NetDefiance) :
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTop hInt hSR hP).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTop hInt hSR hP).V_T
          (E.myopicEquilibriumTop hInt hSR hP).V_S x b) Sanctions.I a →
            a = (E.myopicEquilibriumTop hInt hSR hP).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPath hInt hSR hP) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPath hInt hSR hP) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: defiance, strict wedge, interior cap
    (∀ x ∈ Sanctions.I,
      (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin) hND).α x = 0 ∧
      E.toParams.σ x 0 < E.toParams.dynamicEquilibriumRule
        (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin) hND) x ∧
      E.toParams.dynamicEquilibriumRule
        (E.netDefianceEquilibrium (E.responsePath_monotoneOn_of_margin hmargin) hND) x ≤ E.cap ∧
      E.cap < 1) ∧
    -- (4) paths: wash-in, strict dominance, interior limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t
        ≤ E.netDefiancePath (E.responsePath_monotoneOn_of_margin hmargin) hND x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPath hInt hSR hP) x₀ t
        < E.netDefiancePath (E.responsePath_monotoneOn_of_margin hmargin) hND x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto (E.netDefiancePath (E.responsePath_monotoneOn_of_margin hmargin) hND x₀) atTop
          (𝓝 z)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := E.myopic_dynamic_equilibrium_separation_net
    (E.uhi_lt_q hInt) hSR (E.uhi_lt_k hP) (E.responsePath_monotoneOn_of_margin hmargin) hND
  rw [E.myopicEquilibriumTop_eq_S, E.myopicPath_eq_S]
  exact ⟨h1, h2, h3,
    fun x hx => ⟨(h4 x hx).1, (h4 x hx).2.1, (h4 x hx).2.2, E.cap_lt_one hInt⟩, h5⟩

/-- **The defiance clause of the class under placability, net form.** Under ND and a
nondecreasing response, the defiance-profile value `VTdef` is the Banach fixed point of the
Target's Bellman operator against the response, and `(VTdef, VSstar, α ≡ 0)` is a
top-selector equilibrium (`netDefianceEquilibrium`). Every full-defiance equilibrium has
these values and the response as its rule.
Scope: general class (relief extension). -/
theorem placable_family_defiance_net
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.NetDefiance) :
    E.targetOp E.VSstar_mem E.VTdef = E.VTdef ∧
    (E.netDefianceEquilibrium hmono hND).V_T = E.VTdef ∧
    (E.netDefianceEquilibrium hmono hND).V_S = E.VSstar ∧
    (∀ x ∈ Sanctions.I, (E.netDefianceEquilibrium hmono hND).α x = 0) ∧
    ∀ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, (∀ x ∈ Sanctions.I, Eq.α x = 0) →
      Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
      ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x :=
  ⟨E.VTdef_fix, rfl, rfl, fun _ _ => rfl, fun Eq hα => E.values_eq_of_policy_zero Eq hα⟩

/-- **The Target channel is active at every full-defiance equilibrium under strict ND**,
when full compliance beats full defiance in the one-period problem (`ℓ_hi < b·p_lo`) and
placability holds: no forward-looking Target maximiser is a stage maximiser. The
forward-looking maximiser is full defiance (unique under strict ND); at the stage, full
compliance beats it.
Scope: general class (relief extension); approved hypothesis 2 (strict form, read only
through the uniqueness of the Target's best reply). -/
theorem target_channel_active_of_strictNetDefiance (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.StrictNetDefiance)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.ContinuationChangesTargetChoiceAt (fun y b => E.response Eq.V_S y b) Eq.V_T x := by
  obtain ⟨hVS, hVT, -⟩ := E.values_eq_of_policy_zero Eq hα
  rw [hVS, hVT]
  obtain ⟨g, hg, hside, hbal⟩ := hND
  intro a ha hdyn hstage
  have hdyn' : IsMaxOn (fun b => E.toParams.joint_T_integrand E.VTdef E.VSstar x b)
      Sanctions.I a := hdyn
  have ha0 : a = 0 := E.targetArgmax_eq_zero_of_sharp E.placationCeiling hg hside
    (E.VTdef_lowerSlope hmono hg hbal) E.VSstar_mem hx ha hdyn'
  subst ha0
  have h := hstage (show (1:ℝ) ∈ Sanctions.I from ⟨zero_le_one, le_refl 1⟩)
  exact absurd h (not_le.mpr (E.targetStage_one_gt_zero hP hflip E.VSstar_mem hx))

/-- **The defiance clause of the class under placability, uniqueness part, net form.**
Under strict ND and a nondecreasing response: at every full-defiance equilibrium full
defiance is the Target's unique optimum at every state; under the stage appetite no
maximiser of the Sender's dynamic objective is a stage maximiser; and when in addition
`ℓ_hi < b·p_lo` and placability hold, no forward-looking Target maximiser is a stage
maximiser either. Uniqueness here is of the Target's best reply, not of the equilibrium.
Scope: general class (relief extension); approved hypothesis 2 (strict form, uniqueness
clauses only). -/
theorem placable_family_defiance_net_unique (hS : E.uhi < E.q) (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (hND : E.StrictNetDefiance)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∀ x ∈ Sanctions.I,
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x b) Sanctions.I a →
          a = Eq.α x) ∧
      E.toParams.ContinuationChangesSenderChoiceAt Eq.V_S x (Eq.α x) ∧
      E.toParams.ContinuationChangesTargetChoiceAt (fun y b => E.response Eq.V_S y b) Eq.V_T x := by
  intro x hx
  refine ⟨fun a ha hmax => E.policy_zero_argmax_unique_of_strictNetDefiance hmono hND Eq hα hx ha
      hmax, ?_, E.target_channel_active_of_strictNetDefiance hP hflip hmono hND Eq hα hx⟩
  obtain ⟨hVS, -, -⟩ := E.values_eq_of_policy_zero Eq hα
  rw [hVS, hα x hx]
  exact E.sender_channel_active hS hx

/-! ## 6. Activation without hysteresis at every full-defiance equilibrium -/

/-- **One globally attracting steady state at every full-defiance equilibrium**, when the
closed loop contracts at the sharp constant `L_loop^sharp = g_hi + d_hi·L_resp/μ < 1`: the
steady state is unique in `[0, 1]`, sanction equals state there, it lies in `(b, A/q]`, and
the state path of every full-defiance equilibrium converges to it from every feasible start.
Under the stage appetite `u_hi < q`; neither a defiance condition nor a monotone response is
read.
Scope: general class (relief extension). -/
theorem unique_attracting_state_of_policy_zero (hS : E.uhi < E.q) (hL : E.LloopSharp < 1) :
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
      (∀ y ∈ Sanctions.I, E.closedLoop y = y → y = z) ∧
      ∀ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, (∀ x ∈ Sanctions.I, Eq.α x = 0) →
        ∀ x₀ ∈ Sanctions.I,
          Tendsto (E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀) atTop
            (𝓝 z) := by
  obtain ⟨z, hz, hcl, huniq, hall⟩ := E.closedLoop_unique_attracting_of_sharp_lt_one hL
  have hrz : E.responsePath E.VSstar z = z :=
    E.toParams.rule_eq_self_of_closedLoop_fixed E.hdlo0 E.hSlo hz (E.responsePath_mem E.VSstar z)
      hcl
  refine ⟨z, hz, hrz, ?_, ?_, huniq, ?_⟩
  · rw [← hrz]; exact E.responsePath_gt_sfloor hS E.VSstar_mem hz
  · rw [← hrz]; exact E.responsePath_le_cap E.VSstar_mem hz
  · intro Eq hα x₀ hx₀
    have heq : E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule Eq) x₀
        = fun n => E.closedLoop^[n] x₀ :=
      funext (fun n => (E.rulePath_eq_fullDefiancePath_of_policy_zero Eq hα hx₀ n).trans rfl)
    rw [heq]
    exact hall x₀ hx₀

end ChordEconomyRelief

end

end Examples
end Sanctions
