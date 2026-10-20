/-
Sanctions/Examples/StageSignsNotIDOCounterexample.lean

**Stage complementarity does not imply interval dominance of the substituted
Sender objective: an optimising counterexample** (round K, doc 78 L1 / doc 77
K8; the reader's package `suggestions/2026-09-09-round-I-validation/`, doc 01
§5).

The persistence certificate's condition P3 (`ass:sender`,
`SenderPersistencePackage.sender_IDO_after_target_policy`) asks that the
Sender's dynamic objective, with the Target's equilibrium policy substituted,
satisfy interval dominance in (sanction; state). Census row 3 records that P3
is "not automatic from stage complementarity": the stage signs the model
maintains — a positive cross difference of `U_S` in `(s, x)`, a negative one
in `(s, a)` (placation), strong concavity in `s`, a positive cross difference
of `U_T` in `(s, x)` — do not by themselves deliver it, so that A1 is a genuine
assumption. This file is the Lean object behind that verdict (Rule 11).

The economy: with `τ(x, a) = 1/2 + x/10 − a/5`,

    U_S(x, a, s) = −(s − τ(x, a))²,
    U_T(x, a, s) = −(a − x)² + (x/10)·(s − τ(x, a)),

the affine transition at rate `1/2`, both discounts `1/2`. Every stage sign
holds as an exact identity of cross differences (section 1). Both values are
identically zero, the Sender's unique dynamic response is `τ` (strictly
interior: `τ ∈ [3/10, 3/5]` on the square), the Target's unique optimum is
`a = x`, and both Bellman identities hold, so `(0, 0, id)` is a top-selector
feedback Stackelberg equilibrium (section 2; Rule 15: constructed; Rule 1:
both policies are proved unique optima, not assumed). At that equilibrium the
substituted Sender objective is `−(s − (1/2 − x/10))²`: at `x = 0` the
sanction `1/2` beats `2/5` and dominates the interval between them, at
`x = 1` it is strictly worse — the reversal that interval dominance in
(sanction; state) forbids (section 3).

Rule 9: an existence certificate refuting one implication. It says nothing
about the placable family, whose A1 is discharged from its own chord
conditions (`IDOFamilyOn.of_singleCrossingOn` at the witnesses), and nothing
about any class on which P3 does hold; the open question in census row 3 — a
primitive class implying P3 for every carrier pair — stays open, now with the
information that such a class must add more than the stage signs. Rule 9C:
every quantity is rational and was checked in exact arithmetic first
(`docs/archive/workflow-scratch/round_K_stage0_check.py`).

**Any transition (renovation item BH5.3, 2026-10-07).** Both values are zero,
so neither the transition nor the discounts enter any Bellman identity, argmax
or the refuted property. `ssOver p₀` installs the stage payoffs above on an
arbitrary economy `p₀`, keeping its transition and discounts, and every result
of sections 2 and 3 is proved there; `stage_signs_not_IDO_generalF` refutes the
implication for every transition and every pair of discounts, with no
hypothesis, and exposes `p.F = p₀.F`, `p.β_S = p₀.β_S`, `p.β_T = p₀.β_T`. The
open question in census row 3 narrows accordingly: a class implying P3 must add
more than the stage signs, and no condition on the transition or the discounts
can supply the difference. Rule 22: the
family is general in `F`; the named economy `ssParams` and the original
statement `stage_signs_not_IDO_counterexample` are its affine instance (rate
`1/2`), kept under their names.
-/
import Sanctions.Examples.WitnessKit
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Foundations.IntervalDominanceOrder
import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.IntervalDominanceOrder

noncomputable section

/-! ## 0. The economy -/

/-- The stage vertex `τ(x, a) = 1/2 + x/10 − a/5`. -/
def ssTau (x a : ℝ) : ℝ := 1 / 2 + x / 10 - a / 5

/-- Sender stage payoff `−(s − τ)²`. -/
def ssU_S (x a s : ℝ) : ℝ := -(s - ssTau x a) ^ 2

/-- Target stage payoff `−(a − x)² + (x/10)·(s − τ)`. -/
def ssU_T (x a s : ℝ) : ℝ := -(a - x) ^ 2 + x / 10 * (s - ssTau x a)

/-- The stage selector: the clipped vertex. -/
def ssSigma (x a : ℝ) : ℝ := Sanctions.clipS (ssTau x a)

theorem ssSigma_mem (x a : ℝ) : ssSigma x a ∈ Set.Icc (0 : ℝ) 1 := Sanctions.clipS_mem _

theorem ssSigma_continuous : Continuous (fun xa : ℝ × ℝ => ssSigma xa.1 xa.2) := by
  unfold ssSigma
  apply Sanctions.clipS_continuous.comp
  unfold ssTau
  fun_prop

theorem ssU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => ssU_S xas.1 xas.2.1 xas.2.2) := by
  unfold ssU_S ssTau; fun_prop

theorem ssU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => ssU_T xas.1 xas.2.1 xas.2.2) := by
  unfold ssU_T ssTau; fun_prop

/-- Rule-1 coupling of the stage selector: the clipped vertex maximises the
concave parabola `−(s − τ)²` on `[0,1]`. -/
theorem ssSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => ssU_S x a s) Sanctions.I (ssSigma x a) := by
  refine WitnessKit.clipVertex_isMaxOn (k := (1 : ℝ)) (C := 0) (t := ssTau x a)
    (U := fun s => ssU_S x a s) (by norm_num) ?_
  intro s
  unfold ssU_S; ring

/-- The economy. Rule 22: affine-restricted (`affineF (1/2)`), and marked so. The
same stage payoffs over any transition are `ssOver` below; `ssParams` is
`ssOver ssParams` field for field. -/
def ssParams : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 1 / 2
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := ssU_T
  U_S := ssU_S
  σ := ssSigma
  σ_mem := ssSigma_mem
  σ_isMaxOn_U_S := ssSigma_isMaxOn
  U_T_continuous := ssU_T_continuous
  U_S_continuous := ssU_S_continuous
  F := AbstractGame.affineF (1 / 2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x (by constructor <;> norm_num)
  F_mono_s := AbstractGame.affineF_mono_s (by constructor <;> norm_num)
  F_diag := AbstractGame.affineF_diag _

/-- **`ssParams` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance ssParams_staticSelectorContinuous :
    ssParams.StaticSelectorContinuous where
  σ_continuous := ssSigma_continuous

@[simp] theorem ssParams_U_S : ssParams.U_S = ssU_S := rfl
@[simp] theorem ssParams_U_T : ssParams.U_T = ssU_T := rfl
@[simp] theorem ssParams_β_S : ssParams.β_S = 1 / 2 := rfl
@[simp] theorem ssParams_β_T : ssParams.β_T = 1 / 2 := rfl
@[simp] theorem ssParams_F : ssParams.F = AbstractGame.affineF (1 / 2) := rfl

/-- **The stage payoffs over an arbitrary economy** (renovation item BH5.3,
2026-10-07). Keeps the transition `F`, both discount factors and the adjustment
rate of `p₀`, and installs the stage payoffs `ssU_S`, `ssU_T` and the stage
selector `ssSigma`. General in `F`: the transition is whatever `p₀` carries. -/
def ssOver (p₀ : Params) : Params :=
  { p₀ with
    U_T := ssU_T
    U_S := ssU_S
    σ := ssSigma
    σ_mem := ssSigma_mem
    σ_isMaxOn_U_S := ssSigma_isMaxOn
    U_T_continuous := ssU_T_continuous
    U_S_continuous := ssU_S_continuous }

/-- **`ssOver` has a continuous static Sender selector.** General in `F`: the transition
is `p₀`'s, and the selector does not read it. The proof is the one that was the economy's
`σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left `Params` for
the class `Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender
results can use it at this economy. -/
instance ssOver_staticSelectorContinuous (p₀ : Params) :
    (ssOver p₀).StaticSelectorContinuous where
  σ_continuous := ssSigma_continuous

@[simp] theorem ssOver_U_S (p₀ : Params) : (ssOver p₀).U_S = ssU_S := rfl
@[simp] theorem ssOver_U_T (p₀ : Params) : (ssOver p₀).U_T = ssU_T := rfl
@[simp] theorem ssOver_F (p₀ : Params) : (ssOver p₀).F = p₀.F := rfl
@[simp] theorem ssOver_β_S (p₀ : Params) : (ssOver p₀).β_S = p₀.β_S := rfl
@[simp] theorem ssOver_β_T (p₀ : Params) : (ssOver p₀).β_T = p₀.β_T := rfl

/-! ## 1. The stage signs, as exact cross differences -/

/-- Stage complementarity of the Sender payoff in (sanction; state): the cross
difference is `(1/5)·Δx·Δs`. -/
theorem ss_senderCross_state (x₁ x₂ a s₁ s₂ : ℝ) :
    (ssU_S x₂ a s₂ - ssU_S x₂ a s₁) - (ssU_S x₁ a s₂ - ssU_S x₁ a s₁)
      = 1 / 5 * (x₂ - x₁) * (s₂ - s₁) := by
  unfold ssU_S ssTau; ring

/-- Placation: the cross difference of the Sender payoff in (sanction;
compliance) is `−(2/5)·Δa·Δs`. -/
theorem ss_senderCross_action (x a₁ a₂ s₁ s₂ : ℝ) :
    (ssU_S x a₂ s₂ - ssU_S x a₂ s₁) - (ssU_S x a₁ s₂ - ssU_S x a₁ s₁)
      = -(2 / 5) * (a₂ - a₁) * (s₂ - s₁) := by
  unfold ssU_S ssTau; ring

/-- Strong concavity of the Sender payoff in the sanction: the midpoint gain is
exactly `(1/4)·Δs²`. -/
theorem ss_sender_midpoint (x a s₁ s₂ : ℝ) :
    ssU_S x a ((s₁ + s₂) / 2) - (ssU_S x a s₁ + ssU_S x a s₂) / 2
      = 1 / 4 * (s₂ - s₁) ^ 2 := by
  unfold ssU_S ssTau; ring

/-- Stage complementarity of the Target payoff in (sanction; state):
`(1/10)·Δx·Δs`. -/
theorem ss_targetCross_state (x₁ x₂ a s₁ s₂ : ℝ) :
    (ssU_T x₂ a s₂ - ssU_T x₂ a s₁) - (ssU_T x₁ a s₂ - ssU_T x₁ a s₁)
      = 1 / 10 * (x₂ - x₁) * (s₂ - s₁) := by
  unfold ssU_T ssTau; ring

/-! ## 2. The equilibrium: values zero, response `τ`, policy `a = x`

Every result in sections 2 and 3 is stated over `ssOver p₀` for an arbitrary
economy `p₀` (renovation item BH5.3, 2026-10-07). Both values are zero, so the
transition and the discounts never enter; general in `F`. The `ssParams` forms,
under their original names, are the instances at `p₀ = ssParams` (section 4). -/

/-- The zero value. -/
def ssZero : ChordEconomy.Val := ChordEconomy.affBCF 0 0

theorem ssZero_apply (y : ↥(Sanctions.S : Set ℝ)) : ssZero y = 0 := by
  unfold ssZero; rw [ChordEconomy.affBCF_apply]; ring

theorem ssTau_mem {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    ssTau x a ∈ Sanctions.I := by
  unfold ssTau; constructor <;> nlinarith [hx.1, hx.2, ha.1, ha.2]

theorem ssTau_interior {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    ssTau x a ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold ssTau; constructor <;> nlinarith [hx.1, hx.2, ha.1, ha.2]

section OverAnyTransition

variable (p₀ : Params)

/-- The Sender's dynamic objective at the zero value is the stage payoff, over any
transition and any Sender discount. General in `F`. -/
theorem ssOver_senderObj (x a s : ℝ) :
    (ssOver p₀).U_S x a s + (ssOver p₀).β_S * ssZero (Sanctions.clipS' ((ssOver p₀).F x s))
      = -(s - ssTau x a) ^ 2 := by
  rw [ssZero_apply, ssOver_U_S]; unfold ssU_S; ring

/-- **The top response is `τ`**, over any transition: the objective is a concave
parabola with that vertex, interior, so its unique maximiser on `[0,1]` is the
vertex. General in `F`. -/
theorem ssOver_σ_dyn_top {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    (ssOver p₀).σ_dyn_top ssZero x a = ssTau x a := by
  set t := (ssOver p₀).σ_dyn_top ssZero x a with ht
  have hmax := (ssOver p₀).σ_dyn_top_isMaxOn ssZero x a (ssTau_mem hx ha)
  simp only [Set.mem_setOf_eq] at hmax
  rw [← ht, ssOver_senderObj, ssOver_senderObj] at hmax
  have h0 : t - ssTau x a = 0 := by nlinarith [sq_nonneg (t - ssTau x a)]
  linarith

/-- The Target's joint objective at the zero values is `−(a − x)²`, over any
transition and any Target discount. General in `F`. -/
theorem ssOver_joint {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    (ssOver p₀).joint_T_top_integrand ssZero ssZero x a = -(a - x) ^ 2 := by
  simp only [Params.joint_T_top_integrand]
  rw [ssOver_σ_dyn_top p₀ hx ha, ssZero_apply, ssOver_U_T]
  unfold ssU_T; ring

theorem ssOver_x_isMaxOn {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => (ssOver p₀).joint_T_top_integrand ssZero ssZero x a) Sanctions.I x := by
  intro a ha
  change (ssOver p₀).joint_T_top_integrand ssZero ssZero x a
    ≤ (ssOver p₀).joint_T_top_integrand ssZero ssZero x x
  rw [ssOver_joint p₀ hx ha, ssOver_joint p₀ hx hx]
  nlinarith [sq_nonneg (a - x)]

/-- **The equilibrium, over any transition.** Rule 15: constructed; Rule 1: both
policies are proved unique optima (`ssOver_σ_dyn_top`,
`ssOver_target_argmax_unique`), not assumed. General in `F`. -/
def ssOverEquilibrium : (ssOver p₀).FeedbackStackelbergEquilibriumTop where
  V_T := ssZero
  V_S := ssZero
  α := fun x => x
  hα := continuous_id
  α_mem := fun _ hx => hx
  V_S_fix := by
    ext y
    change ssZero y = sSup ((fun s => (ssOver p₀).integrandS (fun x => x) (fun z => ssZero z)
      (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        (ssOver p₀).integrandS (fun x => x) (fun z => ssZero z) (y.val, s)
          = -(s - ssTau y.val y.val) ^ 2 := by
      intro s _
      simp only [Params.integrandS]
      exact ssOver_senderObj p₀ y.val y.val s
    have hgt : IsGreatest ((fun s => (ssOver p₀).integrandS (fun x => x) (fun z => ssZero z)
        (y.val, s)) '' Sanctions.I) (ssZero y) := by
      refine ⟨⟨ssTau y.val y.val, ssTau_mem y.property y.property, ?_⟩, ?_⟩
      · dsimp only
        rw [hval _ (ssTau_mem y.property y.property), ssZero_apply]; ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs, ssZero_apply]
        nlinarith [sq_nonneg (s - ssTau y.val y.val)]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => (ssOver p₀).joint_T_top_integrand ssZero ssZero y.val a)
        '' Sanctions.I) (ssZero y) := by
      refine ⟨⟨y.val, y.property, ?_⟩, ?_⟩
      · dsimp only
        rw [ssOver_joint p₀ y.property y.property, ssZero_apply]; ring
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [ssOver_joint p₀ y.property ha, ssZero_apply]
        nlinarith [sq_nonneg (a - y.val)]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => ssOver_x_isMaxOn p₀ hx

/-- **`a = x` is the unique Target optimum** at every feasible state, over any
transition. General in `F`. -/
theorem ssOver_target_argmax_unique {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => (ssOver p₀).joint_T_top_integrand
      (ssOverEquilibrium p₀).V_T (ssOverEquilibrium p₀).V_S x b) Sanctions.I a) :
    a = x := by
  have h := hmax hx
  simp only [Set.mem_setOf_eq] at h
  change (ssOver p₀).joint_T_top_integrand ssZero ssZero x x
    ≤ (ssOver p₀).joint_T_top_integrand ssZero ssZero x a at h
  rw [ssOver_joint p₀ hx ha, ssOver_joint p₀ hx hx] at h
  have h0 : a - x = 0 := by nlinarith [sq_nonneg (a - x)]
  linarith

/-! ## 3. Interval dominance fails at the equilibrium -/

/-- The substituted Sender objective at the equilibrium, over any transition:
`−(s − (1/2 − x/10))²`. General in `F`. -/
theorem ssOver_substituted (x s : ℝ) :
    (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S x ((ssOverEquilibrium p₀).α x) s
      = -(s - (1 / 2 - x / 10)) ^ 2 := by
  change (ssOver p₀).senderDynObjective ssZero x x s = _
  unfold Params.senderDynObjective
  rw [ssOver_senderObj]
  unfold ssTau; ring

/-- **Interval dominance in (sanction; state) fails at the equilibrium, over any
transition.** At `x = 0` the sanction `1/2` beats `2/5` and dominates the
interval between them; at `x = 1` it is strictly worse. General in `F`. -/
theorem ssOver_not_IDO :
    ¬ IDOFamilyOn Sanctions.I (Set.Icc (0 : ℝ) 1)
        (fun s x => (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S x
          ((ssOverEquilibrium p₀).α x) s) := by
  intro h
  have h01 := @h 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have hint : ∀ u ∈ Set.Icc (2 / 5 : ℝ) (1 / 2),
      (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S 0 ((ssOverEquilibrium p₀).α 0) u
        ≤ (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S 0
            ((ssOverEquilibrium p₀).α 0) (1 / 2) := by
    intro u _
    rw [ssOver_substituted, ssOver_substituted]
    nlinarith [sq_nonneg (u - (1 / 2 - 0 / 10))]
  have hkey := (@h01 (2 / 5) (1 / 2) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num) hint).1
  have hlow : (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S 0
        ((ssOverEquilibrium p₀).α 0) (2 / 5)
      ≤ (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S 0
        ((ssOverEquilibrium p₀).α 0) (1 / 2) := by
    rw [ssOver_substituted, ssOver_substituted]; norm_num
  have hfalse : (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S 1
        ((ssOverEquilibrium p₀).α 1) (2 / 5)
      ≤ (ssOver p₀).senderDynObjective (ssOverEquilibrium p₀).V_S 1
        ((ssOverEquilibrium p₀).α 1) (1 / 2) := hkey hlow
  rw [ssOver_substituted, ssOver_substituted] at hfalse
  norm_num at hfalse

/-- **Rule 9 form, over any transition and any discounts** (renovation item BH5.3,
2026-10-07). For every economy `p₀` there is an economy with the same transition
and the same two discount factors, the maintained stage signs — a positive cross
difference of `U_S` in (sanction; state), a negative one in (sanction;
compliance), strong concavity in the sanction, a positive cross difference of
`U_T` in (sanction; state) — and a constructed top-selector feedback Stackelberg
equilibrium at which the Target's policy is the identity, both policies are
unique optima, the Sender's response is strictly interior, and the substituted
Sender objective is **not** interval-dominant in (sanction; state) on `[0,1]`.

So P3 (A1) does not follow from the stage signs together with any condition on
the transition or the discounts. General in `F`, with no hypothesis on `p₀`: what
`stage_signs_not_IDO_counterexample` fixed (the affine transition at rate `1/2`,
both discounts `1/2`) is dropped and replaced by `p.F = p₀.F`, `p.β_S = p₀.β_S`,
`p.β_T = p₀.β_T`. -/
theorem stage_signs_not_IDO_generalF :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop),
      p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T ∧
      (∀ x₁ x₂ a s₁ s₂ : ℝ, (p.U_S x₂ a s₂ - p.U_S x₂ a s₁) - (p.U_S x₁ a s₂ - p.U_S x₁ a s₁)
        = 1 / 5 * (x₂ - x₁) * (s₂ - s₁)) ∧
      (∀ x a₁ a₂ s₁ s₂ : ℝ, (p.U_S x a₂ s₂ - p.U_S x a₂ s₁) - (p.U_S x a₁ s₂ - p.U_S x a₁ s₁)
        = -(2 / 5) * (a₂ - a₁) * (s₂ - s₁)) ∧
      (∀ x a s₁ s₂ : ℝ, p.U_S x a ((s₁ + s₂) / 2) - (p.U_S x a s₁ + p.U_S x a s₂) / 2
        = 1 / 4 * (s₂ - s₁) ^ 2) ∧
      (∀ x₁ x₂ a s₁ s₂ : ℝ, (p.U_T x₂ a s₂ - p.U_T x₂ a s₁) - (p.U_T x₁ a s₂ - p.U_T x₁ a s₁)
        = 1 / 10 * (x₂ - x₁) * (s₂ - s₁)) ∧
      (∀ x, E.α x = x) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => p.joint_T_top_integrand E.V_T E.V_S x b) Sanctions.I a → a = x) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, p.σ_dyn_top E.V_S x a ∈ Set.Ioo (0 : ℝ) 1) ∧
      ¬ IDOFamilyOn Sanctions.I (Set.Icc (0 : ℝ) 1)
          (fun s x => p.senderDynObjective E.V_S x (E.α x) s) :=
  ⟨ssOver p₀, ssOverEquilibrium p₀, rfl, rfl, rfl,
    ss_senderCross_state, ss_senderCross_action, ss_sender_midpoint, ss_targetCross_state,
    fun _ => rfl,
    fun _ hx _ ha hmax => ssOver_target_argmax_unique p₀ hx ha hmax,
    fun _ hx _ ha => by
      change (ssOver p₀).σ_dyn_top ssZero _ _ ∈ Set.Ioo (0 : ℝ) 1
      rw [ssOver_σ_dyn_top p₀ hx ha]; exact ssTau_interior hx ha,
    ssOver_not_IDO p₀⟩

end OverAnyTransition

/-! ## 4. The affine instance `ssParams`

The original statements, under their original names, as instances of the
general family at `p₀ = ssParams` (renovation item BH5.3, 2026-10-07):
`ssOver ssParams` is `ssParams` field for field, so each is a one-line
corollary. Statements unchanged. Rule 22: affine-restricted (`affineF (1/2)`). -/

/-- The Sender's dynamic objective at the zero value is the stage payoff. -/
theorem ss_senderObj (x a s : ℝ) :
    ssParams.U_S x a s + ssParams.β_S * ssZero (Sanctions.clipS' (ssParams.F x s))
      = -(s - ssTau x a) ^ 2 :=
  ssOver_senderObj ssParams x a s

/-- **The top response is `τ`**: the objective is a concave parabola with that
vertex, interior, so its unique maximiser on `[0,1]` is the vertex. -/
theorem ss_σ_dyn_top {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    ssParams.σ_dyn_top ssZero x a = ssTau x a :=
  ssOver_σ_dyn_top ssParams hx ha

/-- The Target's joint objective at the zero values is `−(a − x)²`. -/
theorem ss_joint {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I) :
    ssParams.joint_T_top_integrand ssZero ssZero x a = -(a - x) ^ 2 :=
  ssOver_joint ssParams hx ha

theorem ss_x_isMaxOn {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => ssParams.joint_T_top_integrand ssZero ssZero x a) Sanctions.I x :=
  ssOver_x_isMaxOn ssParams hx

/-- **The equilibrium.** Rule 15: constructed; Rule 1: both policies are proved
unique optima (`ss_σ_dyn_top`, `ss_target_argmax_unique`), not assumed. The
instance of `ssOverEquilibrium` at `p₀ = ssParams`. -/
def ssEquilibrium : ssParams.FeedbackStackelbergEquilibriumTop :=
  ssOverEquilibrium ssParams

/-- **`a = x` is the unique Target optimum** at every feasible state. -/
theorem ss_target_argmax_unique {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => ssParams.joint_T_top_integrand
      ssEquilibrium.V_T ssEquilibrium.V_S x b) Sanctions.I a) :
    a = x :=
  ssOver_target_argmax_unique ssParams hx ha hmax

/-- The substituted Sender objective at the equilibrium: `−(s − (1/2 − x/10))²`. -/
theorem ss_substituted (x s : ℝ) :
    ssParams.senderDynObjective ssEquilibrium.V_S x (ssEquilibrium.α x) s
      = -(s - (1 / 2 - x / 10)) ^ 2 :=
  ssOver_substituted ssParams x s

/-- **Interval dominance in (sanction; state) fails at the equilibrium.** At
`x = 0` the sanction `1/2` beats `2/5` and dominates the interval between them;
at `x = 1` it is strictly worse. -/
theorem ss_not_IDO :
    ¬ IDOFamilyOn Sanctions.I (Set.Icc (0 : ℝ) 1)
        (fun s x => ssParams.senderDynObjective ssEquilibrium.V_S x (ssEquilibrium.α x) s) :=
  ssOver_not_IDO ssParams

/-- **Rule 9 form.** There is an economy with the maintained stage signs — a
positive cross difference of `U_S` in (sanction; state), a negative one in
(sanction; compliance), strong concavity in the sanction, a positive cross
difference of `U_T` in (sanction; state) — the affine transition and interior
discounts, and a constructed top-selector feedback Stackelberg equilibrium at
which the Target's policy is the identity, both policies are unique optima,
the Sender's response is strictly interior, and the substituted Sender
objective is **not** interval-dominant in (sanction; state) on `[0,1]`. So P3
(A1) does not follow from the stage signs and the transition conditions.

Since round BH-5 (renovation item BH5.3, 2026-10-07) the instance of
`stage_signs_not_IDO_generalF` at `p₀ = ssParams`, which drops the affine
transition and the discount values; statement unchanged (pinned). -/
theorem stage_signs_not_IDO_counterexample :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop),
      p.F = affineF (1 / 2) ∧ p.β_S = 1 / 2 ∧ p.β_T = 1 / 2 ∧
      (∀ x₁ x₂ a s₁ s₂ : ℝ, (p.U_S x₂ a s₂ - p.U_S x₂ a s₁) - (p.U_S x₁ a s₂ - p.U_S x₁ a s₁)
        = 1 / 5 * (x₂ - x₁) * (s₂ - s₁)) ∧
      (∀ x a₁ a₂ s₁ s₂ : ℝ, (p.U_S x a₂ s₂ - p.U_S x a₂ s₁) - (p.U_S x a₁ s₂ - p.U_S x a₁ s₁)
        = -(2 / 5) * (a₂ - a₁) * (s₂ - s₁)) ∧
      (∀ x a s₁ s₂ : ℝ, p.U_S x a ((s₁ + s₂) / 2) - (p.U_S x a s₁ + p.U_S x a s₂) / 2
        = 1 / 4 * (s₂ - s₁) ^ 2) ∧
      (∀ x₁ x₂ a s₁ s₂ : ℝ, (p.U_T x₂ a s₂ - p.U_T x₂ a s₁) - (p.U_T x₁ a s₂ - p.U_T x₁ a s₁)
        = 1 / 10 * (x₂ - x₁) * (s₂ - s₁)) ∧
      (∀ x, E.α x = x) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => p.joint_T_top_integrand E.V_T E.V_S x b) Sanctions.I a → a = x) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, p.σ_dyn_top E.V_S x a ∈ Set.Ioo (0 : ℝ) 1) ∧
      ¬ IDOFamilyOn Sanctions.I (Set.Icc (0 : ℝ) 1)
          (fun s x => p.senderDynObjective E.V_S x (E.α x) s) :=
  stage_signs_not_IDO_generalF ssParams

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ssEquilibrium
#print axioms Sanctions.Examples.stage_signs_not_IDO_counterexample
#print axioms Sanctions.Examples.ssOverEquilibrium
#print axioms Sanctions.Examples.stage_signs_not_IDO_generalF

end Examples
end Sanctions
