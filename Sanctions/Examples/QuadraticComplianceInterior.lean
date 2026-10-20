/-
Sanctions/Examples/QuadraticComplianceInterior.lean

**A strict optimum with interior compliance at a positive sanction, inside the chord
class** (round BE, 2026-10-03; gap G9 of `suggestions/2026-10-02-lean-gap-map/01_GAP_MAP.md`,
construction C2 of the first ChatGPT gap review, checked locally on 2026-10-03).

Until this file the discussion recorded, as open on a primitive family, a strict optimum
with interior compliance at a positive sanction: the constructed families have
compliance at a corner, or interior compliance only through indifference. Here the
Target's compliance cost is quadratic, `ℓ·a + h·a²/2` with `ℓ = h = 1`, inside the
abstract chord class (compliance costs between `ℓ_lo = 1` and `ℓ_hi = 2` per unit) but
outside the leading quadratic–linear family, whose cost is linear.

The economy (`qcChord`): the affine transition `F(x,s) = (x+s)/2`, `β_S = 1/2`,
`β_T = 1/4`, the quadratic–linear Sender `U_S = x − (3/2)s² + (1 − 3a)s` (no rally), and
the Target payoff `U_T = 10x − (5/2)s − a − a²/2`. It is the family's affine member with
`r = 0`, `c = 5/2`, `v = 10`, `β_T = 1/4`, with the Target's payoff replaced and only the
six Target rate fields re-proved.

1. `qcEquilibrium`: a top-selector equilibrium with `α ≡ 1/14`, realised sanction
   `47/126 > 0`, `V_S = 4x/3 + 2209/5292`, `V_T = 80x/7 − 557/882`.
2. `qc_growth`: the Target's objective at any compliance `a` is below its value at
   `1/14` by at least `(a − 1/14)²/2`, uniformly in the state. So `1/14` is the strict and
   unique optimum (`qc_argmax_unique`); no first-order condition or grid is used.
3. The member lies in the chord class with interiority, the stage relief margin,
   placability and zero-sanction neutrality (`qc_interior`, `qc_stageRelief`,
   `qc_placable`, `qc_neutral`).

**Rule 9.** An existence certificate for the class: it is not a claim about how common
such members are. **Rule 22.** AFFINE TRANSITION in this witness. **Rule 1.** The
response is the unique Sender maximiser at every compliance level and `1/14` the unique
Target maximiser at every state. **Rule 3.** No assumption is introduced.
-/
import Sanctions.Examples.ExplicitEquilibriumKit
import Sanctions.Examples.PlacableSenderWitnesses

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-- The quadratic–linear base: the affine member without a rally (`r = 0`), Target pain
`c = 5/2`, state value `v = 10`, and `β_T = 1/4`. -/
def qcBase : PlacableEconomyF :=
  { placableAffine with
    βT := 1 / 4, hβT0 := by norm_num, hβT1 := by norm_num,
    r := 0, hr := le_refl 0,
    c := 5 / 2, v := 10, hv := by norm_num,
    hCurv := by norm_num [plKS, placableAffine],
    hSigV := by norm_num [plSigImg, plSig, plRho, plMu, plKS, placableAffine],
    hcn := by norm_num [placableAffine] }

/-- The base with its sanction-section modulus. -/
def qcBaseCs : PlacableEconomyFcs := { placableAffineCs with toPlacableEconomyF := qcBase }

/-- The Target's stage payoff with a quadratic compliance cost:
`10x − (5/2)s − a − a²/2`. -/
def qcU_T (x a s : ℝ) : ℝ := 10 * x - 5 / 2 * s - a - a ^ 2 / 2

/-- **The economy**, a member of the chord class: the base with the Target's payoff
replaced. Compliance costs between `1` and `2` per unit on `[0,1]`. -/
def qcChord : ChordEconomyCs :=
  { qcBaseCs.toChordCs with
    U_T := qcU_T
    U_T_continuous := by unfold qcU_T; fun_prop
    ℓlo := 1
    c := 5 / 2
    vlo := 10
    nlo := 0
    ℓhi := 2
    plo := 5 / 2
    vhi := 10
    nhi := 0
    hℓlo := by norm_num
    hvlo := by norm_num
    hnlo := le_refl 0
    hplo := by norm_num
    hUT_costLo := by
      intro x _ s _ a₁ ha₁ a₂ ha₂ hle
      show qcU_T x a₂ s - qcU_T x a₁ s ≤ -(1 * (a₂ - a₁))
      unfold qcU_T
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg ha₂.1 ha₁.1)]
    hUT_costHi := by
      intro x _ s _ a₁ ha₁ a₂ ha₂ hle
      show -(2 * (a₂ - a₁)) ≤ qcU_T x a₂ s - qcU_T x a₁ s
      unfold qcU_T
      have h2 : (0 : ℝ) ≤ 2 - a₁ - a₂ := by linarith [ha₁.2, ha₂.2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) h2]
    hUT_painHi := by
      intro x _ a _ s₁ _ s₂ _ _
      show qcU_T x a s₁ - qcU_T x a s₂ ≤ 5 / 2 * (s₂ - s₁)
      exact le_of_eq (by unfold qcU_T; ring)
    hUT_painLo := by
      intro x _ a _ s₁ _ s₂ _ _
      show 5 / 2 * (s₂ - s₁) ≤ qcU_T x a s₁ - qcU_T x a s₂
      exact le_of_eq (by unfold qcU_T; ring)
    hUT_stateLo := by
      intro a _ s _ x₁ _ x₂ _ _
      show (10 + 0 * s) * (x₂ - x₁) ≤ qcU_T x₂ a s - qcU_T x₁ a s
      exact le_of_eq (by unfold qcU_T; ring)
    hUT_stateHi := by
      intro a _ s _ x₁ _ x₂ _
      show |qcU_T x₂ a s - qcU_T x₁ a s| ≤ (10 + 0 * s) * |x₂ - x₁|
      have h : qcU_T x₂ a s - qcU_T x₁ a s = 10 * (x₂ - x₁) := by unfold qcU_T; ring
      rw [h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
      simp }

/-! ## 1. The member's class predicates -/

/-- **Interiority**, from the base (a Sender-side condition, unchanged). -/
theorem qc_interior : qcChord.Interior :=
  qcBaseCs.toChordCs_interior (by
    unfold PlacableEconomyF.Interior plAppetite plKS
    norm_num [qcBaseCs, qcBase, placableAffineCs, placableAffine])

/-- **The stage relief margin**: `ℓ_hi·Q̄ = 6 < 15/2 = k_lo·p_lo`. -/
theorem qc_stageRelief : qcChord.StageRelief := by
  change (2 : ℝ) * 3 < 3 * (5 / 2)
  norm_num

/-- **Placability**: the appetite `4/3` is at most the placation rate `3`. -/
theorem qc_placable : qcChord.Placable := by
  change qcBase.Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [qcBase, placableAffine]

/-- **Zero-sanction neutrality**: at a zero sanction the Sender's payoff does not depend
on compliance. -/
theorem qc_neutral : qcChord.ZeroSanctionNeutral := by
  intro x _ a _
  change symU_S 3 1 3 0 1 x a 0 = symU_S 3 1 3 0 1 x 0 0
  unfold symU_S; ring

/-! ## 2. The equilibrium -/

/-- The economy's game. -/
abbrev qcParams : Params := qcChord.toParams

theorem qc_U_S : qcParams.U_S = symU_S 3 1 3 0 1 := rfl
theorem qc_U_T : qcParams.U_T = qcU_T := rfl
theorem qc_F : qcParams.F = affineF (1 / 2) := rfl
theorem qc_β_S : qcParams.β_S = 1 / 2 := rfl
theorem qc_β_T : qcParams.β_T = 1 / 4 := rfl

/-- The Sender's value `4x/3 + 2209/5292`. -/
def qcVS : ChordEconomy.Val := ChordEconomy.affBCF (4 / 3) (2209 / 5292)
/-- The Target's value `80x/7 − 557/882`. -/
def qcVT : ChordEconomy.Val := ChordEconomy.affBCF (80 / 7) (-(557 / 882))

theorem qc_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    qcParams.F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [qc_F]; unfold affineF; constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

/-- The Sender's objective: a concave parabola with vertex `4/9 − a`. -/
theorem qc_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    qcParams.U_S x a s + qcParams.β_S * qcVS (Sanctions.clipS' (qcParams.F x s))
      = (4 / 3 * x + 2209 / 10584 + 3 / 2 * (4 / 9 - a) ^ 2)
          - 3 / 2 * (s - (4 / 9 - a)) ^ 2 := by
  unfold qcVS
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (qc_F_mem hx hs), qc_U_S,
    qc_β_S, qc_F]
  unfold symU_S affineF; ring

/-- **The top response is `max 0 (4/9 − a)`.** -/
theorem qc_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    qcParams.σ_dyn_top qcVS x a = max 0 (4 / 9 - a) := by
  rw [σ_dyn_top_eq_clip qcParams qcVS (by norm_num : (0 : ℝ) < 3 / 2)
    (fun s hs => qc_senderObj hx a hs)]
  rw [min_eq_right (by linarith [ha.1] : 4 / 9 - a ≤ 1)]

/-- The Target's objective at the constructed values. -/
theorem qc_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    qcParams.joint_T_top_integrand qcVT qcVS x a
      = 80 / 7 * x - 557 / 3528 - a - a ^ 2 / 2 - 15 / 14 * max 0 (4 / 9 - a) := by
  simp only [Params.joint_T_top_integrand]
  rw [qc_σ_dyn_top hx ha]
  have hρ : max 0 (4 / 9 - a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (by linarith [ha.1])⟩
  unfold qcVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (qc_F_mem hx hρ), qc_U_T,
    qc_β_T, qc_F]
  unfold qcU_T affineF; ring

theorem qc_mem_c : (1 / 14 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩

/-- **Quadratic growth**: the Target's objective at any compliance level is below its
value at `1/14` by at least `(a − 1/14)²/2`, at every state. -/
theorem qc_growth {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    qcParams.joint_T_top_integrand qcVT qcVS x a + (a - 1 / 14) ^ 2 / 2
      ≤ qcParams.joint_T_top_integrand qcVT qcVS x (1 / 14) := by
  rw [qc_joint hx ha, qc_joint hx qc_mem_c,
    max_eq_right (by norm_num : (0 : ℝ) ≤ 4 / 9 - 1 / 14)]
  rcases le_total (4 / 9 - a) 0 with h | h
  · rw [max_eq_left h]; nlinarith [h]
  · rw [max_eq_right h]; nlinarith [h]

/-- **`1/14` is the Target's unique optimum** at every feasible state. -/
theorem qc_argmax_unique' {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => qcParams.joint_T_top_integrand qcVT qcVS x b) Sanctions.I a) :
    a = 1 / 14 := by
  have h1 := hmax qc_mem_c
  simp only [Set.mem_setOf_eq] at h1
  have h2 := qc_growth hx ha
  have h3 : (a - 1 / 14) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  linarith

/-- **The equilibrium.** Rule 15: constructed; Rule 1: `1/14` is the unique argmax. -/
def qcEquilibrium : qcParams.FeedbackStackelbergEquilibriumTop where
  V_T := qcVT
  V_S := qcVS
  α := fun _ => 1 / 14
  hα := continuous_const
  α_mem := fun _ _ => qc_mem_c
  V_S_fix := by
    ext y
    change qcVS y = sSup ((fun s => qcParams.integrandS (fun _ => 1 / 14) (fun z => qcVS z)
      (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        qcParams.integrandS (fun _ => 1 / 14) (fun z => qcVS z) (y.val, s)
          = (4 / 3 * y.val + 2209 / 10584 + 3 / 2 * (47 / 126) ^ 2)
              - 3 / 2 * (s - 47 / 126) ^ 2 := by
      intro s hs
      have := qc_senderObj y.property (1 / 14) hs
      simp only [Params.integrandS]
      rw [this]; ring
    have hgt : IsGreatest ((fun s => qcParams.integrandS (fun _ => 1 / 14) (fun z => qcVS z)
        (y.val, s)) '' Sanctions.I) (qcVS y) := by
      refine ⟨⟨47 / 126, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval (47 / 126) ⟨by norm_num, by norm_num⟩]
        unfold qcVS; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs]
        unfold qcVS; rw [ChordEconomy.affBCF_apply]
        nlinarith [sq_nonneg (s - 47 / 126)]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => qcParams.joint_T_top_integrand qcVT qcVS y.val a)
        '' Sanctions.I) (qcVT y) := by
      refine ⟨⟨1 / 14, qc_mem_c, ?_⟩, ?_⟩
      · dsimp only
        rw [qc_joint y.property qc_mem_c,
          max_eq_right (by norm_num : (0 : ℝ) ≤ 4 / 9 - 1 / 14)]
        unfold qcVT; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        have h := qc_growth y.property ha
        rw [qc_joint y.property qc_mem_c,
          max_eq_right (by norm_num : (0 : ℝ) ≤ 4 / 9 - 1 / 14)] at h
        have hv : qcVT y = 80 / 7 * y.val - 557 / 882 := by
          unfold qcVT; rw [ChordEconomy.affBCF_apply]; ring
        rw [hv]
        nlinarith [sq_nonneg (a - 1 / 14)]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    change qcParams.joint_T_top_integrand qcVT qcVS x a
      ≤ qcParams.joint_T_top_integrand qcVT qcVS x (1 / 14)
    nlinarith [qc_growth hx ha, sq_nonneg (a - 1 / 14)]

/-- **Compliance `1/14` is the unique optimum** of the equilibrium's Target problem. -/
theorem qc_argmax_unique {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => qcParams.joint_T_top_integrand
      qcEquilibrium.V_T qcEquilibrium.V_S x b) Sanctions.I a) :
    a = 1 / 14 :=
  qc_argmax_unique' hx ha hmax

/-- **The realised sanction is `47/126 > 0`** at every feasible state. -/
theorem qc_rule {x : ℝ} (hx : x ∈ Sanctions.I) :
    qcParams.dynamicEquilibriumRule qcEquilibrium x = 47 / 126 := by
  change qcParams.σ_dyn_top qcVS x (1 / 14) = 47 / 126
  rw [qc_σ_dyn_top hx qc_mem_c]
  norm_num

/-- **Rule 9 form.** A member of the chord class with interiority, the stage relief margin,
placability and zero-sanction neutrality, and a top-selector equilibrium of it in which
the Target's compliance `1/14` is strictly interior and its unique optimum at every state,
with uniform quadratic growth, while the realised sanction is `47/126 > 0`. -/
theorem strict_interior_equilibrium_in_chord_class :
    ∃ (E : ChordEconomyCs) (Q : E.toParams.FeedbackStackelbergEquilibriumTop),
      E.Interior ∧ E.StageRelief ∧ E.Placable ∧ E.ZeroSanctionNeutral ∧
      (∀ x ∈ Sanctions.I, Q.α x = 1 / 14) ∧
      (∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Q x = 47 / 126) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        E.toParams.joint_T_top_integrand Q.V_T Q.V_S x a + (a - 1 / 14) ^ 2 / 2
          ≤ E.toParams.joint_T_top_integrand Q.V_T Q.V_S x (1 / 14)) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.toParams.joint_T_top_integrand Q.V_T Q.V_S x b) Sanctions.I a →
          a = 1 / 14) :=
  ⟨qcChord, qcEquilibrium, qc_interior, qc_stageRelief, qc_placable, qc_neutral,
    fun _ _ => rfl, fun _ hx => qc_rule hx, fun _ hx _ ha => qc_growth hx ha,
    fun _ hx _ ha hmax => qc_argmax_unique hx ha hmax⟩

end

#print axioms Sanctions.Examples.qcChord
#print axioms Sanctions.Examples.qcEquilibrium
#print axioms Sanctions.Examples.qc_growth
#print axioms Sanctions.Examples.qc_argmax_unique
#print axioms Sanctions.Examples.strict_interior_equilibrium_in_chord_class

end Examples
end Sanctions
