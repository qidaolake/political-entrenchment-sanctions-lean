/-
Sanctions/Examples/LQAboveThresholdWitness.lean

**Above the threshold, a non-defiance equilibrium with a rising sanction rule coexists with full
defiance** (step 2, target 2c, part D; 2026-10-10; plan `STEP2_2c.md`, Proposition LQ-4 and
finding 3; data from `scratchpad/step2c/exact_witness.py`, re-verified symbolically).

The economy is the paper's collapse member `collapseAffine b` (`PlacableSenderCollapseWitness.lean`:
`q = 3`, `u₀ = 1`, `k = 3`, `r = 0`, `w = 1`, `ℓ = 1`, `c = 4`, `n = 0`, `v = 30`,
`δ = β_S = 1/2`, threshold `β_T* = 2/11`) at the Target discount

    b = 4208/23133 ≈ 0.18190,   2/11 < b < 4/17.

At `b` the profile

    α(x) = 1/5 − 69x/701,
    s(x) = 7711/30450 + x/10,
    V_S(x) = (12/701)x² + (208/145)x + 84821/441525,
    V_T(x) = 33x − 1519067/2744125,

is a top-selector equilibrium (`lwEquilibrium`). Its sanction is positive and rises with the
state, its policy falls with the state, and it is not full defiance (`lw_rule`, `lw_witness`). At
the same `b > 2/11` a full-defiance equilibrium exists (`collapseAffine_threshold`). The Target
is indifferent along its compliance plateau: against these values the sanction enters its
objective with weight `700/701`, while a unit of compliance lowers the Sender's response by
`701/700`, so the plateau slope is exactly zero (`lw_joint`, `lw_joint_le`).

**What it shows** (`lw_limit_of_rule_monotone_uniqueness`). `unique_equilibrium_of_rule_monotone`
(`prop:monotone-uniqueness`) says that under the unrefined loss-offset margin `LossOffset₀`
(here `β_T ≥ 4/17`) every equilibrium with a non-decreasing sanction rule is full defiance. At
`b` the margin fails and the conclusion fails too: the equilibrium above has a non-decreasing
rule and is not full defiance. So the margin cannot be weakened to `β_T > β_T*` (the
net-of-compliance region): this marks the limit of the uniqueness result.

**Scope.** At the example economy only (not general): one member, one discount. It is an
existence certificate (Rule 9); it does not classify the equilibria at `b` or say how large the
band of such discounts is. **Rule 3.** No assumption is introduced. **Rule 1.** The response is
the unique Sender maximiser at every compliance level (a strictly concave parabola), and the
policy a Target maximiser at every state. **Rule 22.** AFFINE: the member's transition is
`affineF (1/2)`.
-/
import Sanctions.Examples.ExplicitEquilibriumKit
import Sanctions.Examples.PlacableSenderCollapseWitness
import Sanctions.Examples.PlacableSenderExactThresholds

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 1. The member and its game -/

/-- The witness discount `b = 4208/23133`. -/
def lwβ : ℝ := 4208 / 23133

/-- `0 < b`.
Scope: at the example economy only (not general). -/
theorem lwβ_pos : 0 < lwβ := by unfold lwβ; norm_num
/-- `b < 1`.
Scope: at the example economy only (not general). -/
theorem lwβ_lt_one : lwβ < 1 := by unfold lwβ; norm_num

/-- The collapse member at the witness discount. -/
abbrev lwE : ChordEconomyCs := collapseAffine lwβ lwβ_pos lwβ_lt_one

/-- Its game. -/
abbrev lwP : Params := lwE.toParams

/-- The member's Sender payoff, `symU_S 3 1 3 0 1`.
Scope: at the example economy only (not general). -/
theorem lw_U_S : lwP.U_S = symU_S 3 1 3 0 1 := rfl
/-- The member's Target payoff, `symU_T 1 4 0 30`.
Scope: at the example economy only (not general). -/
theorem lw_U_T : lwP.U_T = symU_T 1 4 0 30 := rfl
/-- The member's transition, `affineF (1/2)`.
Scope: at the example economy only (not general). -/
theorem lw_F : lwP.F = affineF (1 / 2) := rfl
/-- The member's Sender discount, `1/2`.
Scope: at the example economy only (not general). -/
theorem lw_β_S : lwP.β_S = 1 / 2 := rfl
/-- The member's Target discount, `b`.
Scope: at the example economy only (not general). -/
theorem lw_β_T : lwP.β_T = lwβ := rfl

/-- The transition keeps the state feasible.
Scope: at the example economy only (not general). -/
theorem lw_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    lwP.F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [lw_F]; unfold affineF; constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

/-! ## 2. The equilibrium -/

/-- The Sender's value `(12/701)x² + (208/145)x + 84821/441525`. -/
def lwVS : ChordEconomy.Val := quadBCF (12 / 701) (208 / 145) (84821 / 441525)
/-- The Target's value `33x − 1519067/2744125`. -/
def lwVT : ChordEconomy.Val := ChordEconomy.affBCF 33 (-(1519067 / 2744125))
/-- The Target's policy `1/5 − 69x/701`. -/
def lwα (x : ℝ) : ℝ := 1 / 5 - 69 / 701 * x

/-- The vertex of the Sender's objective, `(197/145 + 3x/701 − 3a)(701/2100)`. -/
def lwVertex (x a : ℝ) : ℝ := (197 / 145 + 3 / 701 * x - 3 * a) * (701 / 2100)

/-- **The Sender's objective is a concave parabola** with curvature `1050/701`.
Scope: at the example economy only (not general). -/
theorem lw_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    lwP.U_S x a s + lwP.β_S * lwVS (Sanctions.clipS' (lwP.F x s))
      = (x + 3 / 1402 * x ^ 2 + 52 / 145 * x + 84821 / 883050
          + 1050 / 701 * lwVertex x a ^ 2) - 1050 / 701 * (s - lwVertex x a) ^ 2 := by
  unfold lwVS
  rw [quadBCF_apply, Sanctions.clipS'_val_eq_of_mem (lw_F_mem hx hs), lw_U_S, lw_β_S, lw_F]
  unfold symU_S affineF lwVertex
  ring

/-- The vertex is below full sanction at every feasible state and compliance.
Scope: at the example economy only (not general). -/
theorem lwVertex_le_one {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lwVertex x a ≤ 1 := by
  unfold lwVertex
  nlinarith [hx.2, ha.1]

/-- **The top response is the positive part of the vertex.**
Scope: at the example economy only (not general). -/
theorem lw_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lwP.σ_dyn_top lwVS x a = max 0 (lwVertex x a) := by
  rw [σ_dyn_top_eq_clip lwP lwVS (by norm_num : (0 : ℝ) < 1050 / 701)
    (fun s hs => lw_senderObj hx a hs)]
  rw [min_eq_right (lwVertex_le_one hx ha)]

/-- The policy is feasible at every feasible state.
Scope: at the example economy only (not general). -/
theorem lwα_mem {x : ℝ} (hx : x ∈ Sanctions.I) : lwα x ∈ Sanctions.I := by
  unfold lwα; constructor <;> nlinarith [hx.1, hx.2]

/-- At the policy the vertex is `7711/30450 + x/10`.
Scope: at the example economy only (not general). -/
theorem lwVertex_at_policy (x : ℝ) : lwVertex x (lwα x) = 7711 / 30450 + x / 10 := by
  unfold lwVertex lwα; ring

/-- At the policy the vertex is positive.
Scope: at the example economy only (not general). -/
theorem lwVertex_at_policy_pos {x : ℝ} (hx : x ∈ Sanctions.I) : 0 < lwVertex x (lwα x) := by
  rw [lwVertex_at_policy]; nlinarith [hx.1]

/-- The Target's objective at the constructed values: the sanction enters with weight
`700/701`.
Scope: at the example economy only (not general). -/
theorem lw_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lwP.joint_T_top_integrand lwVT lwVS x a
      = 30 * x + 2104 / 701 * x - 828976 / 8232375 - a
        - 700 / 701 * max 0 (lwVertex x a) := by
  simp only [Params.joint_T_top_integrand]
  rw [lw_σ_dyn_top hx ha]
  have hρ : max 0 (lwVertex x a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (lwVertex_le_one hx ha)⟩
  unfold lwVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (lw_F_mem hx hρ), lw_U_T,
    lw_β_T, lw_F]
  unfold symU_T affineF lwβ
  ring

/-- **The Target is indifferent up to the zero-sanction level and loses beyond it.**
Scope: at the example economy only (not general). -/
theorem lw_joint_le {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lwP.joint_T_top_integrand lwVT lwVS x a
      ≤ 30 * x + 2104 / 701 * x - 828976 / 8232375 - (197 / 145 + 3 / 701 * x) / 3 := by
  rw [lw_joint hx ha]
  rcases le_total (lwVertex x a) 0 with h | h
  · rw [max_eq_left h]
    unfold lwVertex at h
    nlinarith [h]
  · rw [max_eq_right h]
    unfold lwVertex
    nlinarith [h]

/-- At the policy the Target's objective attains its plateau value.
Scope: at the example economy only (not general). -/
theorem lw_joint_at_policy {x : ℝ} (hx : x ∈ Sanctions.I) :
    lwP.joint_T_top_integrand lwVT lwVS x (lwα x)
      = 30 * x + 2104 / 701 * x - 828976 / 8232375 - (197 / 145 + 3 / 701 * x) / 3 := by
  rw [lw_joint hx (lwα_mem hx), max_eq_right (lwVertex_at_policy_pos hx).le]
  unfold lwVertex lwα
  ring

/-- **The witness equilibrium** at `b = 4208/23133`: policy `1/5 − 69x/701`, Sender value
`(12/701)x² + (208/145)x + 84821/441525`, Target value `33x − 1519067/2744125`.
Scope: at the example economy only (not general). -/
def lwEquilibrium : lwP.FeedbackStackelbergEquilibriumTop where
  V_T := lwVT
  V_S := lwVS
  α := lwα
  hα := by unfold lwα; fun_prop
  α_mem := fun _ hx => lwα_mem hx
  V_S_fix := by
    ext y
    change lwVS y = sSup ((fun s => lwP.integrandS lwα (fun z => lwVS z) (y.val, s))
      '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        lwP.integrandS lwα (fun z => lwVS z) (y.val, s)
          = (y.val + 3 / 1402 * y.val ^ 2 + 52 / 145 * y.val + 84821 / 883050
              + 1050 / 701 * lwVertex y.val (lwα y.val) ^ 2)
            - 1050 / 701 * (s - lwVertex y.val (lwα y.val)) ^ 2 := by
      intro s hs
      have := lw_senderObj y.property (lwα y.val) hs
      simp only [Params.integrandS]
      rw [this]
    have hv0 := (lwVertex_at_policy_pos y.property).le
    have hv1 := lwVertex_le_one y.property (lwα_mem y.property)
    have hgt : IsGreatest ((fun s => lwP.integrandS lwα (fun z => lwVS z) (y.val, s))
        '' Sanctions.I) (lwVS y) := by
      refine ⟨⟨lwVertex y.val (lwα y.val), ⟨hv0, hv1⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval _ ⟨hv0, hv1⟩, lwVertex_at_policy]
        unfold lwVS; rw [quadBCF_apply]
        ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs, lwVertex_at_policy]
        unfold lwVS; rw [quadBCF_apply]
        nlinarith [sq_nonneg (s - (7711 / 30450 + y.val / 10))]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hv : lwVT y = 30 * y.val + 2104 / 701 * y.val - 828976 / 8232375
        - (197 / 145 + 3 / 701 * y.val) / 3 := by
      unfold lwVT; rw [ChordEconomy.affBCF_apply]; ring
    have hgt : IsGreatest ((fun a => lwP.joint_T_top_integrand lwVT lwVS y.val a)
        '' Sanctions.I) (lwVT y) := by
      refine ⟨⟨lwα y.val, lwα_mem y.property, ?_⟩, ?_⟩
      · dsimp only
        rw [lw_joint_at_policy y.property, hv]
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [hv]
        exact lw_joint_le y.property ha
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    change lwP.joint_T_top_integrand lwVT lwVS x a
      ≤ lwP.joint_T_top_integrand lwVT lwVS x (lwα x)
    rw [lw_joint_at_policy hx]
    exact lw_joint_le hx ha

/-- **The witness's realised sanction is `7711/30450 + x/10`** at every state.
Scope: at the example economy only (not general). -/
theorem lw_rule {x : ℝ} (hx : x ∈ Sanctions.I) :
    lwP.dynamicEquilibriumRule lwEquilibrium x = 7711 / 30450 + x / 10 := by
  change lwP.σ_dyn_top lwVS x (lwα x) = _
  rw [lw_σ_dyn_top hx (lwα_mem hx), max_eq_right (lwVertex_at_policy_pos hx).le,
    lwVertex_at_policy]

/-! ## 3. The witness statements -/

/-- **Above `β_T*`, a non-defiance equilibrium with a rising sanction rule coexists with full
defiance** (plan LQ-4). At the collapse member with Target discount `b = 4208/23133`, which lies
strictly between the threshold `β_T* = 2/11` and the unrefined loss-offset bound `4/17`:
(i) a full-defiance top-selector equilibrium exists;
(ii) a top-selector equilibrium exists whose policy is `1/5 − 69x/701` (antitone on the state set,
`1/5` at the zero state, so not full defiance) and whose realised sanction is
`7711/30450 + x/10` (positive and monotone on the state set).
Scope: at the example economy only (not general). -/
theorem lw_witness :
    2 / 11 < lwβ ∧ lwβ < 4 / 17 ∧ lwE.betaStar = 2 / 11
    ∧ (∃ Eq : lwP.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
    ∧ ∃ Eq : lwP.FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Eq.α x = 1 / 5 - 69 / 701 * x)
        ∧ AntitoneOn Eq.α Sanctions.S ∧ Eq.α 0 = 1 / 5
        ∧ (∀ x ∈ Sanctions.I, lwP.dynamicEquilibriumRule Eq x = 7711 / 30450 + x / 10)
        ∧ (∀ x ∈ Sanctions.I, 0 < lwP.dynamicEquilibriumRule Eq x)
        ∧ MonotoneOn (lwP.dynamicEquilibriumRule Eq) Sanctions.S := by
  have hb1 : 2 / 11 < lwβ := by unfold lwβ; norm_num
  refine ⟨hb1, by unfold lwβ; norm_num, collapseAffine_betaStar lwβ_pos lwβ_lt_one,
    (collapseAffine_threshold lwβ_pos lwβ_lt_one (ne_of_gt hb1)).2 hb1,
    lwEquilibrium, fun _ _ => rfl, ?_, by change lwα 0 = 1 / 5; unfold lwα; ring,
    fun _ hx => lw_rule hx, fun x hx => ?_, ?_⟩
  · intro x _ y _ hxy
    change lwα y ≤ lwα x
    unfold lwα
    linarith
  · rw [lw_rule hx]; nlinarith [hx.1]
  · intro x hx y hy hxy
    rw [lw_rule hx, lw_rule hy]
    linarith

/-- **The limit of monotone-rule uniqueness** (plan finding 3, side consequence for M1).
`ChordEconomy.unique_equilibrium_of_rule_monotone` (`prop:monotone-uniqueness`) concludes, under
the unrefined loss-offset margin `LossOffset₀`, that every top-selector equilibrium with a
non-decreasing sanction rule is full defiance. At the collapse member with `b = 4208/23133`,
above the threshold `β_T* = 2/11`, the margin fails and so does the conclusion: there is a
top-selector equilibrium whose sanction rule is non-decreasing on the state set and in which the
Target does not defy at every state, and a full-defiance equilibrium coexists with it. So the
margin cannot be weakened to `β_T > β_T*`.
Scope: at the example economy only (not general). -/
theorem lw_limit_of_rule_monotone_uniqueness :
    lwE.betaStar < lwE.β_T ∧ ¬ lwE.LossOffset₀
    ∧ (∃ Eq : lwP.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
    ∧ ∃ Eq : lwP.FeedbackStackelbergEquilibriumTop,
        MonotoneOn (lwE.rule Eq) Sanctions.S ∧ ¬ ∀ x ∈ Sanctions.I, Eq.α x = 0 := by
  obtain ⟨hb1, hb2, hstar, hdef, Eq, -, -, h0, -, -, hmono⟩ := lw_witness
  refine ⟨?_, ?_, hdef, Eq, hmono, fun h => ?_⟩
  · rw [hstar]; exact hb1
  · intro hTM
    have h := (lwE.toChordEconomyRelief.lossOffset₀_iff_βT_ge).1 hTM
    have e : lwE.c / (lwE.dlo * lwE.vlo + lwE.c * lwE.glo) = 4 / 17 := by
      change (4 : ℝ) / (1 / 2 * 30 + 4 * (1 / 2)) = 4 / 17
      norm_num
    rw [e] at h
    change 4 / 17 ≤ lwβ at h
    linarith
  · have := h 0 ⟨le_rfl, zero_le_one⟩
    rw [h0] at this
    norm_num at this

end

end Examples
end Sanctions
