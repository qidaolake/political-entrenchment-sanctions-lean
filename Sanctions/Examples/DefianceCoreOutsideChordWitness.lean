/-
Sanctions/Examples/DefianceCoreOutsideChordWitness.lean

**The defiance core reaches outside the chord class** (round BE, 2026-10-03; gap G6 of
`suggestions/2026-10-02-lean-gap-map/01_GAP_MAP.md`, construction C1 of the first
ChatGPT gap review, checked locally on 2026-10-03).

`Theory/Equilibrium/DefianceCore.lean` proves the defiance core over an arbitrary
economy: two transition chords, decreasing differences of the Sender's payoff in
(sanction; compliance), four Target rates read only at full defiance or relative to
zero compliance, and the unrefined margin. Its extra generality over the chord class
was unwitnessed, and the appendix said so. This file supplies the witness.

The economy: the affine transition `F(x,s) = (x+s)/2`, both discounts `1/2`, the
quadratic–linear Sender `U_S = x − (3/2)s² + (1 − 3a)s` (no rally), and a Target whose
compliance cost `C(a) = a + 10·a·(1 − a)` is at least `a` but not monotone:
`C(3/4) = 21/8 > C(1) = 1`.

1. `ocEquilibrium`: a top-selector equilibrium with `V_S = 4x/3 + 16/27`, `V_T = 4x`,
   full defiance, and response `max 0 (4/9 − a)`. The Target's objective is exactly
   `4x − C(a)` whatever the sanction, so full defiance is its unique optimum
   (`oc_argmax_unique`).
2. The core's hypotheses hold with `g_lo = d_lo = 1/2`, `v = 3`, `c = ℓ = 1`, and the
   margin binds (`β_T·d_lo·v/(1 − β_T·g_lo) = 1 = c`). Hence every top-selector
   equilibrium of this economy whose realised rule is nondecreasing defies at every
   state (`oc_core_policy_zero`), and the class is non-empty (`oc_rule_monotone`).
3. No chord economy has this Target payoff (`oc_not_chord`): the chord class's T2 field
   `hUT_costLo` asks every compliance increment to cost at least `ℓ_lo > 0`, and raising
   compliance from `3/4` to `1` raises the Target's stage payoff by `13/8`.

**Rule 9.** An existence certificate: the core's hypotheses are satisfiable outside the
chord class at an optimising equilibrium. It is not evidence that such economies are
typical. **Rule 22.** AFFINE TRANSITION in this witness; the theorem it instantiates is
general in `F`, and the generality witnessed is in the Target's payoff. **Rule 1.**
Every strategy is proved optimal: the response is the unique Sender maximiser at every
compliance level and full defiance the unique Target maximiser. **Rule 3.** No
assumption is introduced.
-/
import Sanctions.Examples.ExplicitEquilibriumKit
import Sanctions.Theory.Equilibrium.DefianceCore

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-- The Target's compliance cost `C(a) = a + 10·a·(1 − a)`. -/
def ocCost (a : ℝ) : ℝ := a + 10 * a * (1 - a)

/-- The Target's stage payoff `3x − s − C(a)`. -/
def ocU_T (x a s : ℝ) : ℝ := 3 * x - s - ocCost a

/-- **The economy.** The quadratic–linear Sender of the family without a rally, the
affine transition at rate `1/2`, both discounts `1/2`, and the Target payoff `ocU_T`. -/
def ocParams : Params where
  δ := 1 / 2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1 / 2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1 / 2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := ocU_T
  U_S := symU_S 3 1 3 0 1
  σ := symσ 3 1 3 0
  σ_mem := symσ_mem 3 1 3 0
  σ_isMaxOn_U_S := symσ_isMaxOn (by norm_num) 1 3 0 1
  U_T_continuous := by unfold ocU_T ocCost; fun_prop
  U_S_continuous := symU_S_continuous 3 1 3 0 1
  F := affineF (1 / 2)
  F_continuous := affineF_continuous _
  F_mono_x := affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := affineF_diag _

/-- **`ocParams` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance ocParams_staticSelectorContinuous :
    ocParams.StaticSelectorContinuous where
  σ_continuous := symσ_continuous 3 1 3 0

/-- The Sender's value `4x/3 + 16/27`. -/
def ocVS : ChordEconomy.Val := ChordEconomy.affBCF (4 / 3) (16 / 27)
/-- The Target's value `4x`. -/
def ocVT : ChordEconomy.Val := ChordEconomy.affBCF 4 0

theorem oc_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    ocParams.F x s ∈ (Sanctions.S : Set ℝ) := by
  change affineF (1 / 2) x s ∈ (Sanctions.S : Set ℝ)
  unfold affineF; constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

/-- The Sender's objective on the square: a concave parabola with vertex `4/9 − a`. -/
theorem oc_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    ocParams.U_S x a s + ocParams.β_S * ocVS (Sanctions.clipS' (ocParams.F x s))
      = (4 / 3 * x + 8 / 27 + 3 / 2 * (4 / 9 - a) ^ 2) - 3 / 2 * (s - (4 / 9 - a)) ^ 2 := by
  unfold ocVS
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (oc_F_mem hx hs)]
  change symU_S 3 1 3 0 1 x a s + 1 / 2 * (4 / 3 * affineF (1 / 2) x s + 16 / 27) = _
  unfold symU_S affineF; ring

/-- **The top response is `max 0 (4/9 − a)`**, the clipped vertex. -/
theorem oc_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    ocParams.σ_dyn_top ocVS x a = max 0 (4 / 9 - a) := by
  rw [σ_dyn_top_eq_clip ocParams ocVS (by norm_num : (0 : ℝ) < 3 / 2)
    (fun s hs => oc_senderObj hx a hs)]
  rw [min_eq_right (by linarith [ha.1] : 4 / 9 - a ≤ 1)]

/-- **The Target's objective is `4x − C(a)` at every compliance level**: the sanction's
pain is exactly offset by the value of the state it builds. -/
theorem oc_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    ocParams.joint_T_top_integrand ocVT ocVS x a = 4 * x - ocCost a := by
  simp only [Params.joint_T_top_integrand]
  rw [oc_σ_dyn_top hx ha]
  have hρ : max 0 (4 / 9 - a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (by linarith [ha.1])⟩
  unfold ocVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (oc_F_mem hx hρ)]
  change ocU_T x a (max 0 (4 / 9 - a)) + 1 / 2 * (4 * affineF (1 / 2) x (max 0 (4 / 9 - a)) + 0)
    = _
  unfold ocU_T affineF; ring

theorem oc_zero_isMaxOn {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => ocParams.joint_T_top_integrand ocVT ocVS x a) Sanctions.I 0 := by
  intro a ha
  change ocParams.joint_T_top_integrand ocVT ocVS x a
    ≤ ocParams.joint_T_top_integrand ocVT ocVS x 0
  rw [oc_joint hx ha, oc_joint hx ⟨le_rfl, zero_le_one⟩]
  unfold ocCost
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]

/-- **The equilibrium.** Rule 15: constructed; Rule 1: full defiance is proved to be the
unique argmax (`oc_argmax_unique`), and the response the unique Sender maximiser. -/
def ocEquilibrium : ocParams.FeedbackStackelbergEquilibriumTop where
  V_T := ocVT
  V_S := ocVS
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := by
    ext y
    change ocVS y = sSup ((fun s => ocParams.integrandS (fun _ => 0) (fun z => ocVS z)
      (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        ocParams.integrandS (fun _ => 0) (fun z => ocVS z) (y.val, s)
          = -(3 / 2) * s ^ 2 + 4 / 3 * s + 4 / 3 * y.val + 8 / 27 := by
      intro s hs
      have := oc_senderObj y.property 0 hs
      simp only [Params.integrandS]
      rw [this]; ring
    have hgt : IsGreatest ((fun s => ocParams.integrandS (fun _ => 0) (fun z => ocVS z)
        (y.val, s)) '' Sanctions.I) (ocVS y) := by
      refine ⟨⟨4 / 9, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval (4 / 9) ⟨by norm_num, by norm_num⟩]
        unfold ocVS; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs]
        unfold ocVS; rw [ChordEconomy.affBCF_apply]
        nlinarith [sq_nonneg (s - 4 / 9)]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => ocParams.joint_T_top_integrand ocVT ocVS y.val a)
        '' Sanctions.I) (ocVT y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [oc_joint y.property ⟨le_rfl, zero_le_one⟩]
        unfold ocVT ocCost; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [oc_joint y.property ha]
        unfold ocVT ocCost; rw [ChordEconomy.affBCF_apply]
        nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => oc_zero_isMaxOn hx

/-- **Full defiance is the Target's unique optimum** at every feasible state. -/
theorem oc_argmax_unique {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => ocParams.joint_T_top_integrand
      ocEquilibrium.V_T ocEquilibrium.V_S x b) Sanctions.I a) :
    a = 0 := by
  have h := hmax ⟨le_rfl, zero_le_one⟩
  simp only [Set.mem_setOf_eq] at h
  change ocParams.joint_T_top_integrand ocVT ocVS x 0
    ≤ ocParams.joint_T_top_integrand ocVT ocVS x a at h
  rw [oc_joint hx ha, oc_joint hx ⟨le_rfl, zero_le_one⟩] at h
  unfold ocCost at h
  have : a ≤ 0 := by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
  linarith [ha.1]

/-! ## The defiance core's hypotheses -/

theorem oc_band : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    1 / 2 * (y₂ - y₁) ≤ ocParams.F y₂ s - ocParams.F y₁ s := by
  intro s _ y₁ _ y₂ _ _
  change 1 / 2 * (y₂ - y₁) ≤ affineF (1 / 2) y₂ s - affineF (1 / 2) y₁ s
  unfold affineF; linarith

theorem oc_Slo : Sanctions.TransitionChords.SanctionLowerChord ocParams.F (1 / 2) := by
  intro x s₁ s₂ _ _ _ _
  change 1 / 2 * (s₂ - s₁) ≤ affineF (1 / 2) x s₂ - affineF (1 / 2) x s₁
  unfold affineF; linarith

theorem oc_DD : ∀ x ∈ Icc (0 : ℝ) 1, Sanctions.MilgromShannon.DecreasingDifferencesOn
    Sanctions.I Sanctions.I (fun s a => ocParams.U_S x a s) := by
  intro x _ s₁ s₂ t t' _ _ hs _ _ ht
  change symU_S 3 1 3 0 1 x t' s₂ - symU_S 3 1 3 0 1 x t' s₁
    ≤ symU_S 3 1 3 0 1 x t s₂ - symU_S 3 1 3 0 1 x t s₁
  unfold symU_S
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)]

theorem oc_cost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    1 * a ≤ ocParams.U_T x 0 s - ocParams.U_T x a s := by
  intro x _ s _ a ha
  change 1 * a ≤ ocU_T x 0 s - ocU_T x a s
  unfold ocU_T ocCost
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]

theorem oc_pain : ∀ x ∈ Icc (0 : ℝ) 1,
    Params.LowerLossSlopeOn (fun s => ocParams.U_T x 0 s) (Icc (0 : ℝ) 1) 1 := by
  intro x _ s₁ _ s₂ _ _
  change ocU_T x 0 s₂ - ocU_T x 0 s₁ ≥ -1 * (s₂ - s₁)
  unfold ocU_T ocCost; linarith

theorem oc_state : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    3 * (y₂ - y₁) ≤ ocParams.U_T y₂ 0 s - ocParams.U_T y₁ 0 s := by
  intro s _ y₁ _ y₂ _ _
  change 3 * (y₂ - y₁) ≤ ocU_T y₂ 0 s - ocU_T y₁ 0 s
  unfold ocU_T ocCost; linarith

/-- **The unrefined margin binds**: `β_T·d_lo·v/(1 − β_T·g_lo) = 1 = c`. -/
theorem oc_margin : (1 : ℝ) ≤ ocParams.β_T * (1 / 2) * ocParams.defianceSlope (1 / 2) 3 := by
  change (1 : ℝ) ≤ 1 / 2 * (1 / 2) * (3 / (1 - 1 / 2 * (1 / 2)))
  norm_num

/-- **The defiance core applies**: every top-selector equilibrium of this economy whose
realised rule is nondecreasing defies at every feasible state. -/
theorem oc_core_policy_zero (Q : ocParams.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (ocParams.dynamicEquilibriumRule Q) Sanctions.S)
    {x : ℝ} (hx : x ∈ Sanctions.I) : Q.α x = 0 :=
  Q.policy_eq_zero_of_rule_monotone oc_band oc_Slo oc_DD oc_cost one_pos
    oc_pain oc_state (by norm_num) oc_margin hrule hx

/-- **The class is inhabited**: the constructed equilibrium's realised rule is the
constant `4/9`. -/
theorem oc_rule_monotone : MonotoneOn (ocParams.dynamicEquilibriumRule ocEquilibrium)
    Sanctions.S := by
  intro x hx y hy _
  have hx' : x ∈ Sanctions.I := hx
  have hy' : y ∈ Sanctions.I := hy
  change ocParams.σ_dyn_top ocVS x 0 ≤ ocParams.σ_dyn_top ocVS y 0
  rw [oc_σ_dyn_top hx' ⟨le_rfl, zero_le_one⟩, oc_σ_dyn_top hy' ⟨le_rfl, zero_le_one⟩]

/-- **No chord economy has this Target payoff.** The chord class's field `hUT_costLo`
(T2: every compliance increment costs at least `ℓ_lo > 0`) fails between `3/4` and `1`. -/
theorem oc_not_chord : ¬ ∃ E : ChordEconomy, E.U_T = ocParams.U_T := by
  rintro ⟨E, hE⟩
  have h := E.hUT_costLo 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ (3 / 4)
    ⟨by norm_num, by norm_num⟩ 1 ⟨zero_le_one, le_rfl⟩ (by norm_num)
  have hl := E.hℓlo
  rw [hE] at h
  change ocU_T 0 1 0 - ocU_T 0 (3 / 4) 0 ≤ -(E.ℓlo * (1 - 3 / 4)) at h
  unfold ocU_T ocCost at h
  linarith

/-- **Rule 9 form.** There is an economy, outside the chord class, with an optimising
top-selector equilibrium whose realised rule is nondecreasing, at which the defiance core
applies: every equilibrium with a nondecreasing realised rule defies at every state. -/
theorem defiance_core_outside_chord_class :
    ∃ (p : Params) (Q : p.FeedbackStackelbergEquilibriumTop),
      (¬ ∃ E : ChordEconomy, E.U_T = p.U_T) ∧
      MonotoneOn (p.dynamicEquilibriumRule Q) Sanctions.S ∧
      (∀ x ∈ Sanctions.I, Q.α x = 0) ∧
      (∀ Q' : p.FeedbackStackelbergEquilibriumTop,
        MonotoneOn (p.dynamicEquilibriumRule Q') Sanctions.S →
          ∀ x ∈ Sanctions.I, Q'.α x = 0) :=
  ⟨ocParams, ocEquilibrium, oc_not_chord, oc_rule_monotone, fun _ _ => rfl,
    fun Q' h _ hx => oc_core_policy_zero Q' h hx⟩

end

#print axioms Sanctions.Examples.ocEquilibrium
#print axioms Sanctions.Examples.oc_argmax_unique
#print axioms Sanctions.Examples.oc_core_policy_zero
#print axioms Sanctions.Examples.oc_not_chord
#print axioms Sanctions.Examples.defiance_core_outside_chord_class

end Examples
end Sanctions
