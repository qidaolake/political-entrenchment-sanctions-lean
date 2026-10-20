/-
Sanctions/Examples/FourGroupWelfareSign.lean

**Rally dominance does not determine the sign of the welfare gap: two region-(R)
polities with a negative or discount-dependent gap** (round S, 2026-09-15; doc
87 W3; the reader's packages of 2026-09-11, 09-12 and 09-15 answering doc 86).

`FourGroup.affineCornerGap_pos_all_discounts_iff` says exactly when the
zero-sanction path beats the persistent corner path for every planner
discount: `C > 0` and `H ≥ 0` in the coefficients. Neither inequality is a
region-(R) condition (the four region fields constrain cross-partials and
curvature, not the resource burn against the groups' benefits), and this file
exhibits the failure at the smallest possible distance from the constructed
economy:

* `fourGroupCertHawkScaled` changes three Sender fields of `fourGroupCert`
  (`g_J := 5`, `θ⁰_{J_S} := 3/5`, `ν := 1/5`) so that the hawk coalition's
  political weight times its per-unit benefit, `(3/5 + x/5)·5 = 3 + x`, is
  exactly what it was. Both government payoffs are unchanged
  (`fourGroupCertHawkScaled_U_S`, `_U_T`), the induced game is `fgcParams`
  itself (`fourGroupCertHawkScaled_toParams`), so the exact equilibrium
  `fgcExactEquilibriumTop` is an equilibrium of this polity verbatim
  (`fourGroupCertHawkScaledEquilibriumTop`). The planner flow, which counts
  the hawks' benefit at unit weight, rises by `4s`: `C = −7/10`, `H = −17/10`,
  and the gap is `−(14 + 3β)/(20(1−β)(1−β/2)) < 0` at every discount
  (`fourGroupCertHawkScaled_gap_neg`, stated on the equilibrium-derived
  paths). Same government game, same equilibrium, opposite welfare ranking.
* `fourGroupCertPositiveCost` changes only the direct sanction cost, `d_s :=
  1/10` (positive, so no degeneracy objection): `C = 3/5`, `H = −2/5`, and the
  gap is `3/5` at `β = 0`, zero at `β = 3/4`, `−24/11` at `β = 9/10` — the sign
  depends on the planner's patience. Accounting only: `U_T` changes, so no
  equilibrium transfers.

Since 2026-10-07 (BH6.1) the first polity is the member `k = 5` of the Theory
family `FourGroup.hawkRescale` (`fourGroupCertHawkScaled_eq_hawkRescale`): its
payoff, selector and planner-flow identities are instances of the family's, and
its gap is the certificate gap shifted by `−(k − 1)·g_J/(1 − β) = −4/(1 − β)`
(`fourGroupCertHawkScaled_gap_shift`). The family theorem
`FourGroup.exists_hawkRescale_cornerF_gap_neg` states the refutation at every
polity with `g_J > 0`, every planner discount, every start and every
cube-preserving transition monotone in both arguments (one-directional: it makes
the gap negative, not positive).

Rule 9: both are existence certificates — refutations of the universal
"region (R) implies a positive gap" — and license nothing about magnitudes.
Rule 11: they were built and checked in exact arithmetic
(`docs/archive/workflow-scratch/fourgroup_welfare_sign.py`) before the
characterization they refute was proved. Rule 22: affine (`δ = 1/2`), said so.
-/
import Sanctions.Examples.FourGroupPlannerWitness

namespace Sanctions
namespace Examples

open KaempferLowenberg

noncomputable section

/-! ## 1. The payoff-preserving polity -/

/-- **The hawk-scaled polity**: `fourGroupCert` with the pro-sanction
coalition's per-unit benefit raised from `1` to `5` and its weight schedule
scaled down by the same factor, `θ⁰_{J_S} = 3/5`, `ν = 1/5`. Region (R) holds
(`ν·g_J = 1 > 0`, the rest unchanged). -/
def fourGroupCertHawkScaled : FourGroup where
  th0_JS := 3/5
  nu := 1/5
  g_J := 5
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

/-- **The hawk-scaled polity is the `k = 5` member of the hawk-rescaling family**
(BH6.1, 2026-10-07): `fourGroupCert.hawkRescale 5` has `g_J = 5·1`,
`θ⁰_{J_S} = 3/5`, `ν = 1/5` and every other field of `fourGroupCert`. Affine only
through the witness transition used below; the identity itself has no
transition. -/
theorem fourGroupCertHawkScaled_eq_hawkRescale :
    fourGroupCertHawkScaled = fourGroupCert.hawkRescale 5 (by norm_num) := by
  simp only [fourGroupCertHawkScaled, FourGroup.hawkRescale, fourGroupCert, FourGroup.mk.injEq]
  norm_num

/-- The Sender's stage payoff is unchanged: `(3/5 + x/5)·5·s = (3 + x)·s`. The
`k = 5` instance of `FourGroup.hawkRescale_U_S`. -/
theorem fourGroupCertHawkScaled_U_S : fourGroupCertHawkScaled.U_S = fourGroupCert.U_S := by
  rw [fourGroupCertHawkScaled_eq_hawkRescale]
  exact fourGroupCert.hawkRescale_U_S 5 _

/-- The Target's stage payoff is unchanged (no Target field moved). The `k = 5`
instance of `FourGroup.hawkRescale_U_T`. -/
theorem fourGroupCertHawkScaled_U_T : fourGroupCertHawkScaled.U_T = fourGroupCert.U_T := by
  rw [fourGroupCertHawkScaled_eq_hawkRescale]
  exact fourGroupCert.hawkRescale_U_T 5 _

/-- The derived static Sender selector is unchanged. The `k = 5` instance of
`FourGroup.hawkRescale_sigmaSel`. -/
theorem fourGroupCertHawkScaled_sigmaSel :
    fourGroupCertHawkScaled.sigmaSel = fourGroupCert.sigmaSel := by
  rw [fourGroupCertHawkScaled_eq_hawkRescale]
  exact fourGroupCert.hawkRescale_sigmaSel 5 _

/-- **The induced game is `fgcParams` itself**: the two polities differ only in
how the planner counts the hawks' benefit, not in either government's
objective, selector or transition. -/
theorem fourGroupCertHawkScaled_toParams :
    fourGroupCertHawkScaled.toParams (1/2) (9/10) (1/2)
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)
      = fgcParams := by
  unfold fgcParams FourGroup.toParams FourGroup.toParamsF
  congr 1
  · exact fourGroupCertHawkScaled_U_S
  · exact fourGroupCertHawkScaled_sigmaSel

/-- **The certificate economy's exact equilibrium is an equilibrium of the
hawk-scaled polity's game** (Rule 1: the same optimising play, transported
along the equality of the games). -/
def fourGroupCertHawkScaledEquilibriumTop :
    (fourGroupCertHawkScaled.toParams (1/2) (9/10) (1/2)
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).FeedbackStackelbergEquilibriumTop := by
  rw [fourGroupCertHawkScaled_toParams]
  exact fgcExactEquilibriumTop

/-- The planner flow rises by the hawks' extra unit-weight benefit, `4s`. The
`k = 5` instance of `FourGroup.hawkRescale_plannerW` (`(k − 1)·g_J = 4`). -/
theorem fourGroupCertHawkScaled_plannerW (x a s : ℝ) :
    fourGroupCertHawkScaled.plannerW x a s = fourGroupCert.plannerW x a s + 4 * s := by
  rw [fourGroupCertHawkScaled_eq_hawkRescale, FourGroup.hawkRescale_plannerW]
  have hg : fourGroupCert.g_J = 1 := rfl
  rw [hg]
  ring

/-- **The certificate gap shifted by the family formula** (BH6.1; affine-restricted
through the witness paths, `δ = 1/2`): on the affine comparison paths the
hawk-scaled polity's gap is the certificate polity's gap minus
`(5 − 1)·g_J/(1 − β) = 4/(1 − β)`, the `k = 5` instance of
`FourGroup.hawkRescale_cornerF_gap`. -/
theorem fourGroupCertHawkScaled_gap_shift {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    fourGroupCertHawkScaled.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
        - fourGroupCertHawkScaled.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1)
      = (fourGroupCert.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
          - fourGroupCert.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1))
        - 4 / (1 - β) := by
  rw [← affineZeroPath_half, ← affineCornerPath_half, ← zeroPathF_affineF,
    ← cornerPathF_affineF, fourGroupCertHawkScaled_eq_hawkRescale,
    fourGroupCert.hawkRescale_cornerF_gap 5 _
      (AbstractGame.affineF_mem (by constructor <;> norm_num)) hb hx0]
  have hg : fourGroupCert.g_J = 1 := rfl
  rw [hg]
  ring

/-- **The gap is negative at every planner discount**, on the affine comparison
paths: `−17/(10(1−β)) + 1/(1−β/2) = −(14 + 3β)/(20(1−β)(1−β/2)) < 0`. -/
theorem fourGroupCertHawkScaled_gap_neg_paths {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1)
    (x0 : ℝ) :
    fourGroupCertHawkScaled.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
      - fourGroupCertHawkScaled.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1) < 0 := by
  rw [← affineZeroPath_half, ← affineCornerPath_half,
    fourGroupCertHawkScaled.pathValue_affineCorner_gap (by constructor <;> norm_num) hb x0]
  simp only [fourGroupCertHawkScaled]
  have h1 : (0 : ℝ) < 1 - β := by linarith [hb.2]
  have h2 : (0 : ℝ) < 1 - β * (1 - 1/2) := by linarith [hb.2]
  rw [div_add_div _ _ h1.ne' h2.ne']
  apply div_neg_of_neg_of_pos
  · nlinarith [hb.1]
  · exact mul_pos h1 h2

/-- **Same government game, same equilibrium, opposite welfare ranking**: along
the equilibrium-derived paths of `fgcExactEquilibriumTop` (full defiance,
maximal sanctions; an equilibrium of this polity's game by
`fourGroupCertHawkScaled_toParams`), the hawk-scaled polity's planner value of
the persistent equilibrium path strictly exceeds that of the feasible
zero-sanction path from the same start, for every start and every planner
discount. Region (R) holds; the sign of the gap is reversed. -/
theorem fourGroupCertHawkScaled_gap_neg {x0 β : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCertHawkScaled β (altPath x0) (fun _ => 0) (fun _ => 0)
      - plannerValue fourGroupCertHawkScaled β (eqPath x0)
          (fgcEquilibriumTargetPath x0) (fgcEquilibriumSenderPath x0) < 0 := by
  have hα : fgcEquilibriumTargetPath x0 = fun _ => (0 : ℝ) := by
    funext t; exact fgcEquilibriumTargetPath_eq_zero x0 t
  have hσ : fgcEquilibriumSenderPath x0 = fun _ => (1 : ℝ) := by
    funext t; exact fgcEquilibriumSenderPath_eq_one hx0 t
  rw [hα, hσ, plannerValue_eq_pathValue, plannerValue_eq_pathValue]
  exact fourGroupCertHawkScaled_gap_neg_paths hb x0

/-! ## 2. The positive-cost polity: the sign depends on the planner's patience -/

/-- **The positive-cost polity**: `fourGroupCert` with the direct sanction cost
`d_s = 1/10` instead of `14/5`. Region (R) holds (no region field reads `d_s`).
`C = 3/5`, `H = −2/5`. -/
def fourGroupCertPositiveCost : FourGroup where
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
  d_s := 1/10
  w_pl_nn := by norm_num
  kS_pos := by norm_num
  senderRally_pos := by norm_num
  rally_dom := by norm_num

/-- The gap on the affine comparison paths, in closed form:
`(−2/5)/(1−β) + 1/(1−β/2)`. -/
theorem fourGroupCertPositiveCost_gap_eq {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    fourGroupCertPositiveCost.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
      - fourGroupCertPositiveCost.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1)
      = (-2/5) / (1 - β) + 1 / (1 - β / 2) := by
  rw [← affineZeroPath_half, ← affineCornerPath_half,
    fourGroupCertPositiveCost.pathValue_affineCorner_gap (by constructor <;> norm_num) hb x0]
  simp only [fourGroupCertPositiveCost]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith [hb.2]
  have h2 : (1 : ℝ) - β / 2 ≠ 0 := by linarith [hb.2]
  field_simp
  ring

/-- At `β = 0` the gap is `3/5 > 0`: the myopic planner prefers the zero path. -/
theorem fourGroupCertPositiveCost_gap_at_zero (x0 : ℝ) :
    fourGroupCertPositiveCost.pathValue 0 (altPath x0) (fun _ => 0) (fun _ => 0)
      - fourGroupCertPositiveCost.pathValue 0 (eqPath x0) (fun _ => 0) (fun _ => 1) = 3/5 := by
  rw [fourGroupCertPositiveCost_gap_eq ⟨le_rfl, by norm_num⟩ x0]
  norm_num

/-- At `β = 9/10` the gap is `−24/11 < 0`: the patient planner prefers the
persistent corner path. The sign turns at `β = 3/4`. -/
theorem fourGroupCertPositiveCost_gap_at_nine_tenths (x0 : ℝ) :
    fourGroupCertPositiveCost.pathValue (9/10) (altPath x0) (fun _ => 0) (fun _ => 0)
      - fourGroupCertPositiveCost.pathValue (9/10) (eqPath x0) (fun _ => 0) (fun _ => 1)
      = -24/11 := by
  rw [fourGroupCertPositiveCost_gap_eq (by constructor <;> norm_num) x0]
  norm_num

/-- **The sign turns exactly at `β = 3/4`** (round X, 2026-09-17; the reader's
P2 of 2026-09-16): on the affine comparison paths the gap is positive iff
`β < 3/4`, zero iff `β = 3/4`, negative iff `β > 3/4`, since it equals
`(3 − 4β)/(5(1−β)(1−β/2))`. The paths are feasible planner paths, not a
transported equilibrium (the Target payoff changed with `d_s`). -/
theorem fourGroupCertPositiveCost_gap_sign_iff {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    (0 < fourGroupCertPositiveCost.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
          - fourGroupCertPositiveCost.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1)
        ↔ β < 3/4)
    ∧ (fourGroupCertPositiveCost.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
          - fourGroupCertPositiveCost.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1) = 0
        ↔ β = 3/4)
    ∧ (fourGroupCertPositiveCost.pathValue β (altPath x0) (fun _ => 0) (fun _ => 0)
          - fourGroupCertPositiveCost.pathValue β (eqPath x0) (fun _ => 0) (fun _ => 1) < 0
        ↔ 3/4 < β) := by
  rw [fourGroupCertPositiveCost_gap_eq hb x0]
  have h1 : (0 : ℝ) < 1 - β := by linarith [hb.2]
  have h2 : (0 : ℝ) < 1 - β / 2 := by linarith [hb.2]
  have key : (-2/5 : ℝ) / (1 - β) + 1 / (1 - β / 2)
      = (3 - 4 * β) / (5 * ((1 - β) * (1 - β / 2))) := by
    rw [div_add_div _ _ h1.ne' h2.ne', div_eq_div_iff (mul_ne_zero h1.ne' h2.ne') (by positivity)]
    ring
  have hD : (0 : ℝ) < 5 * ((1 - β) * (1 - β / 2)) := by positivity
  rw [key]
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hD, zero_mul]
    constructor <;> intro h <;> linarith
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hD.ne'
    · intro h
      left
      linarith
  · rw [div_lt_iff₀ hD, zero_mul]
    constructor <;> intro h <;> linarith

/-- **Neither polity satisfies the all-discount condition** — the Rule 11
reading of `affineCornerGap_pos_all_discounts_iff` at the two witnesses: for the
hawk-scaled polity `C = −7/10 < 0`, for the positive-cost polity `H = −2/5 < 0`. -/
theorem fourGroupCert_variants_fail_all_discounts :
    ¬ (0 < (fourGroupCertHawkScaled.kS + fourGroupCertHawkScaled.d_s)
          - (fourGroupCertHawkScaled.g_J - fourGroupCertHawkScaled.q_K))
    ∧ ¬ (0 ≤ (fourGroupCertPositiveCost.kS + fourGroupCertPositiveCost.d_s)
          - (fourGroupCertPositiveCost.g_J - fourGroupCertPositiveCost.q_K)
          - (fourGroupCertPositiveCost.b_J - fourGroupCertPositiveCost.b_K)) := by
  simp only [fourGroupCertHawkScaled, fourGroupCertPositiveCost]
  norm_num

end

/-! ## 3. The government game does not identify the welfare ranking (round X,
2026-09-17; the reader's P1 of 2026-09-16) -/

/-- **Same game, same equilibrium, opposite welfare rankings, at every planner
discount and every physical start.** `fourGroupCert` and `fourGroupCertHawkScaled`
induce the same `Params`, namely `fgcParams` (the first by definition, the
second by `fourGroupCertHawkScaled_toParams`), so the exact equilibrium
`fgcExactEquilibriumTop` is an equilibrium of both games and its derived paths
are the same paths. Along those paths the unit-weight planner of the first
polity strictly prefers the feasible zero-sanction alternative
(`fgc_planner_inefficiency_equilibrium`) and the planner of the second strictly
prefers the equilibrium path (`fourGroupCertHawkScaled_gap_neg`). Government
payoff functions and equilibrium behaviour therefore do not determine the
welfare ranking of these two paths; what does is the group-level decomposition
the planner aggregates at unit weight. Rule 9: an existence statement about two
polities; it licenses nothing about magnitudes and nothing about the
hawk-scaled planner's own optimum. -/
theorem fourGroupCert_welfare_not_identified_by_game :
    fourGroupCert.toParams (1/2) (9/10) (1/2)
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num) = fgcParams
    ∧ fourGroupCertHawkScaled.toParams (1/2) (9/10) (1/2)
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num) = fgcParams
    ∧ ∀ x0 ∈ Set.Icc (0 : ℝ) 1, ∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0)
              - plannerValue fourGroupCert β (eqPath x0)
                  (fgcEquilibriumTargetPath x0) (fgcEquilibriumSenderPath x0)
        ∧ plannerValue fourGroupCertHawkScaled β (altPath x0) (fun _ => 0) (fun _ => 0)
              - plannerValue fourGroupCertHawkScaled β (eqPath x0)
                  (fgcEquilibriumTargetPath x0) (fgcEquilibriumSenderPath x0) < 0 := by
  refine ⟨rfl, fourGroupCertHawkScaled_toParams, fun x0 hx0 β hb => ⟨?_, ?_⟩⟩
  · have h := fgc_planner_inefficiency_equilibrium hx0 hb
    have hm1 : (0 : ℝ) < 23 / (10 * (1 - β)) :=
      div_pos (by norm_num) (by nlinarith [hb.2])
    have hm2 : (0 : ℝ) < 1 / (1 - β / 2) := div_pos (by norm_num) (by linarith [hb.2])
    linarith
  · exact fourGroupCertHawkScaled_gap_neg hx0 hb

#print axioms fourGroupCertHawkScaled_toParams
#print axioms fourGroupCertHawkScaled_eq_hawkRescale
#print axioms fourGroupCertHawkScaled_gap_shift
#print axioms fourGroupCertPositiveCost_gap_sign_iff
#print axioms fourGroupCert_welfare_not_identified_by_game
#print axioms fourGroupCertHawkScaled_gap_neg
#print axioms fourGroupCertPositiveCost_gap_at_nine_tenths
#print axioms fourGroupCert_variants_fail_all_discounts

end Examples
end Sanctions
