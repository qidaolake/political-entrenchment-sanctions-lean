/-
Sanctions/Examples/Counterexamples/EndpointFloorRule.lean

**An endpoint floor is not a whole-basin corner** (doc 70, L4; the scope
example of `app:scope-notes`, previously marked "not formalised").

A realised rule with `R(x) ≥ x` on the basin and a floor reaching the top state
forces `R(1) = 1` and nothing more. The economy below realises the rule
`R(x) = (x + 1)/2`: Sender stage payoff `−(s − (x+1)/2)²` (with the target
clipped to the state set so the stage selector is total), Target stage payoff
`−a²`, both values zero, `α ≡ 0`, the affine transition at rate `1/2` and both
discounts `1/2` from the affine member. The rule satisfies `R(x) ≥ x`, `R(1) = 1`
and `R(x) < 1` for every `x < 1`.

Nothing is posited: both Bellman equations are verified (each objective is a
negative square, maximised at zero), the Target's `α ≡ 0` is proved optimal,
and the realised rule is identified from the Sender's top selector as the
unique maximiser of the quadratic objective. Rule 9: an existence
certificate delimiting one reading of "floor".

**Any transition (renovation item BH5.3, 2026-10-07).** Both values are zero,
so the transition and the discounts never enter the Bellman equations, the
Target's optimum or the realised rule. `floorOver p₀` installs the two stage
payoffs and the stage selector on an arbitrary economy `p₀`, keeping its
transition and discounts; the equilibrium and the rule are built there, and
`endpoint_floor_not_whole_basin_corner_generalF` gives the separation for every
transition and every pair of discounts, with no hypothesis, exposing
`p.F = p₀.F`, `p.β_S = p₀.β_S`, `p.β_T = p₀.β_T`. Rule 22: the family is general
in `F`; the named economy `floorParams` is its instance at the affine member,
and `endpoint_floor_not_whole_basin_corner` keeps its statement.
-/
import Sanctions.Examples.PlacableSenderWitnesses
import Sanctions.Examples.PlacableSenderRegimes

namespace Sanctions
namespace Examples

open Set AbstractGame BoundedContinuousFunction

noncomputable section

/-- The rule `(x + 1)/2`, clipped to the state set so it is total on `ℝ`. -/
def floorRule (x : ℝ) : ℝ := Sanctions.clipS ((x + 1) / 2)

theorem floorRule_continuous : Continuous floorRule :=
  Sanctions.clipS_continuous.comp (by fun_prop)

theorem floorRule_mem (x : ℝ) : floorRule x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem floorRule_of_mem {x : ℝ} (hx : x ∈ Sanctions.I) : floorRule x = (x + 1) / 2 := by
  unfold floorRule
  exact clipS_of_mem' ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Sender stage payoff `−(s − R(x))²`. -/
def floorU_S (x _a s : ℝ) : ℝ := -(s - floorRule x) ^ 2
/-- Target stage payoff `−a²`. -/
def floorU_T (_x a _s : ℝ) : ℝ := -(a ^ 2)

theorem floorU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => floorU_S xas.1 xas.2.1 xas.2.2) := by
  unfold floorU_S
  exact ((continuous_snd.snd.sub (floorRule_continuous.comp continuous_fst)).pow 2).neg

theorem floorU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => floorU_T xas.1 xas.2.1 xas.2.2) := by
  unfold floorU_T; fun_prop

/-- **The economy over an arbitrary base** (renovation item BH5.3, 2026-10-07):
the transition, discounts and adjustment rate of `p₀`, the two negative-square
stage payoffs, and the stage selector `R` (a stage argmax). General in `F`: the
transition is whatever `p₀` carries. -/
def floorOver (p₀ : Params) : Params :=
  { p₀ with
    U_S := floorU_S
    U_S_continuous := floorU_S_continuous
    U_T := floorU_T
    U_T_continuous := floorU_T_continuous
    σ := fun x _ => floorRule x
    σ_mem := fun x _ => floorRule_mem x
    σ_isMaxOn_U_S := fun x a s _ => by
      change -(s - floorRule x) ^ 2 ≤ -(floorRule x - floorRule x) ^ 2
      rw [sub_self, zero_pow two_ne_zero, neg_zero]
      exact neg_nonpos.mpr (sq_nonneg _) }

/-- **`floorOver` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance floorOver_staticSelectorContinuous (p₀ : Params) :
    (floorOver p₀).StaticSelectorContinuous where
  σ_continuous := floorRule_continuous.comp continuous_fst

theorem floorOver_U_S (p₀ : Params) : (floorOver p₀).U_S = floorU_S := rfl
theorem floorOver_U_T (p₀ : Params) : (floorOver p₀).U_T = floorU_T := rfl
theorem floorOver_F (p₀ : Params) : (floorOver p₀).F = p₀.F := rfl
theorem floorOver_β_S (p₀ : Params) : (floorOver p₀).β_S = p₀.β_S := rfl
theorem floorOver_β_T (p₀ : Params) : (floorOver p₀).β_T = p₀.β_T := rfl

/-- The economy: the affine member's transition and discounts, the two
negative-square stage payoffs, and the stage selector `R` (a stage argmax). Since
round BH-5 (renovation item BH5.3, 2026-10-07) written as `floorOver` at the
affine member; the same economy as before. -/
def floorParams : Params := floorOver placableAffine.toParams

theorem floorParams_U_S : floorParams.U_S = floorU_S := rfl
theorem floorParams_U_T : floorParams.U_T = floorU_T := rfl
theorem floorParams_F : floorParams.F = affineF (1 / 2) := rfl

/-- The common value `0`. -/
def floorV : ChordEconomy.Val := ChordEconomy.affBCF 0 0

theorem floorV_apply (y : ↥(Sanctions.S : Set ℝ)) : floorV y = 0 := by
  unfold floorV; rw [ChordEconomy.affBCF_apply]; ring

section OverAnyTransition

variable (p₀ : Params)

/-- The Sender's objective at the zero value is the negative square, over any
transition and any Sender discount. General in `F`. -/
theorem floorOver_senderObj (x a s : ℝ) :
    (floorOver p₀).U_S x a s
        + (floorOver p₀).β_S * floorV (Sanctions.clipS' ((floorOver p₀).F x s))
      = -(s - floorRule x) ^ 2 := by
  rw [floorV_apply, floorOver_U_S]; unfold floorU_S; ring

/-- The Target's joint objective at the zero values is `−a²`, over any transition
and any Target discount. General in `F`. -/
theorem floorOver_joint (x a : ℝ) :
    (floorOver p₀).joint_T_top_integrand floorV floorV x a = -(a ^ 2) := by
  simp only [Params.joint_T_top_integrand]
  rw [floorV_apply, floorOver_U_T]; unfold floorU_T; ring

/-- **The equilibrium, over any transition.** Rule 15: constructed; Rule 1: `α ≡ 0`
is proved optimal, and the realised rule is identified below, not assumed.
General in `F`. -/
def floorOverEquilibrium : (floorOver p₀).FeedbackStackelbergEquilibriumTop where
  V_T := floorV
  V_S := floorV
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := by
    ext y
    change floorV y = sSup ((fun s => (floorOver p₀).integrandS (fun _ => 0)
      (fun z => floorV z) (y.val, s)) '' Sanctions.I)
    have hval : ∀ s, (floorOver p₀).integrandS (fun _ => 0) (fun z => floorV z) (y.val, s)
        = -(s - floorRule y.val) ^ 2 := by
      intro s
      have := floorOver_senderObj p₀ y.val 0 s
      simp only [Params.integrandS]
      exact this
    have hgt : IsGreatest ((fun s => (floorOver p₀).integrandS (fun _ => 0)
        (fun z => floorV z) (y.val, s)) '' Sanctions.I) (floorV y) := by
      refine ⟨⟨floorRule y.val, floorRule_mem _, ?_⟩, ?_⟩
      · dsimp only
        rw [hval, floorV_apply, sub_self, zero_pow two_ne_zero, neg_zero]
      · rintro _ ⟨s, _, rfl⟩
        dsimp only
        rw [hval, floorV_apply]
        exact neg_nonpos.mpr (sq_nonneg _)
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => (floorOver p₀).joint_T_top_integrand floorV floorV
        y.val a) '' Sanctions.I) (floorV y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [floorOver_joint, floorV_apply]; ring
      · rintro _ ⟨a, _, rfl⟩
        dsimp only
        rw [floorOver_joint, floorV_apply]
        exact neg_nonpos.mpr (sq_nonneg _)
    exact hgt.csSup_eq.symm
  α_opt_top := fun x _ => by
    intro a _
    change (floorOver p₀).joint_T_top_integrand floorV floorV x a
      ≤ (floorOver p₀).joint_T_top_integrand floorV floorV x 0
    rw [floorOver_joint, floorOver_joint]
    nlinarith [sq_nonneg a]

/-- **The realised rule is `(x + 1)/2`** on the state set, over any transition:
the top selector is a maximiser of `−(s − R(x))²`, whose unique maximiser is
`R(x)`. General in `F`. -/
theorem floorOver_rule_eq {x : ℝ} (hx : x ∈ Sanctions.I) :
    (floorOver p₀).dynamicEquilibriumRule (floorOverEquilibrium p₀) x = (x + 1) / 2 := by
  change (floorOver p₀).σ_dyn_top floorV x 0 = (x + 1) / 2
  set t := (floorOver p₀).σ_dyn_top floorV x 0 with ht
  have hmax := (floorOver p₀).σ_dyn_top_isMaxOn floorV x 0 (floorRule_mem x)
  simp only [Set.mem_setOf_eq] at hmax
  rw [← ht, floorOver_senderObj, floorOver_senderObj, floorRule_of_mem hx] at hmax
  have hsq : (t - (x + 1) / 2) ^ 2 ≤ 0 := by nlinarith
  have : t - (x + 1) / 2 = 0 := by nlinarith [sq_nonneg (t - (x + 1) / 2)]
  linarith

theorem floorOver_rule_ge {x : ℝ} (hx : x ∈ Sanctions.I) :
    x ≤ (floorOver p₀).dynamicEquilibriumRule (floorOverEquilibrium p₀) x := by
  rw [floorOver_rule_eq p₀ hx]; linarith [hx.2]

theorem floorOver_rule_top :
    (floorOver p₀).dynamicEquilibriumRule (floorOverEquilibrium p₀) 1 = 1 := by
  rw [floorOver_rule_eq p₀ ⟨zero_le_one, le_rfl⟩]; norm_num

theorem floorOver_rule_lt_one {x : ℝ} (hx : x ∈ Sanctions.I) (h1 : x < 1) :
    (floorOver p₀).dynamicEquilibriumRule (floorOverEquilibrium p₀) x < 1 := by
  rw [floorOver_rule_eq p₀ hx]; linarith

/-- **Rule 9 form, over any transition and any discounts** (renovation item BH5.3,
2026-10-07). For every economy `p₀` there is an economy with the same transition
and the same two discount factors, with a constructed top-selector equilibrium
whose realised rule lies at or above the state everywhere, equals `1` at the top
state, and lies strictly below `1` at every other state: a floor reaching the top
forces `R(1) = 1` and nothing more, whatever the transition.

General in `F`, with no hypothesis on `p₀`: the affine member's transition and
discounts, fixed in `endpoint_floor_not_whole_basin_corner`, are dropped and
replaced by `p.F = p₀.F`, `p.β_S = p₀.β_S`, `p.β_T = p₀.β_T`. -/
theorem endpoint_floor_not_whole_basin_corner_generalF :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop),
      p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T ∧
      (∀ x ∈ Sanctions.I, x ≤ p.dynamicEquilibriumRule E x) ∧
      p.dynamicEquilibriumRule E 1 = 1 ∧
      ∀ x ∈ Sanctions.I, x < 1 → p.dynamicEquilibriumRule E x < 1 :=
  ⟨floorOver p₀, floorOverEquilibrium p₀, rfl, rfl, rfl,
    fun _ hx => floorOver_rule_ge p₀ hx, floorOver_rule_top p₀,
    fun _ hx h1 => floorOver_rule_lt_one p₀ hx h1⟩

end OverAnyTransition

/-! ### The affine instance `floorParams`

The original statements, under their original names, as instances at
`p₀ = placableAffine.toParams` (renovation item BH5.3, 2026-10-07). Statements
unchanged. Rule 22: affine-restricted (the affine member's `affineF (1/2)`). -/

/-- The Sender's objective at the zero value is the negative square. -/
theorem floor_senderObj (x a s : ℝ) :
    floorParams.U_S x a s + floorParams.β_S * floorV (Sanctions.clipS' (floorParams.F x s))
      = -(s - floorRule x) ^ 2 :=
  floorOver_senderObj placableAffine.toParams x a s

/-- The Target's joint objective at the zero values is `−a²`. -/
theorem floor_joint (x a : ℝ) :
    floorParams.joint_T_top_integrand floorV floorV x a = -(a ^ 2) :=
  floorOver_joint placableAffine.toParams x a

/-- **The equilibrium.** Rule 15: constructed; Rule 1: `α ≡ 0` is proved
optimal, and the realised rule is identified below, not assumed. The instance of
`floorOverEquilibrium` at the affine member. -/
def floorEquilibrium : floorParams.FeedbackStackelbergEquilibriumTop :=
  floorOverEquilibrium placableAffine.toParams

/-- **The realised rule is `(x + 1)/2`** on the state set: the top selector is
a maximiser of `−(s − R(x))²`, whose unique maximiser is `R(x)`. -/
theorem floor_rule_eq {x : ℝ} (hx : x ∈ Sanctions.I) :
    floorParams.dynamicEquilibriumRule floorEquilibrium x = (x + 1) / 2 :=
  floorOver_rule_eq placableAffine.toParams hx

theorem floor_rule_ge {x : ℝ} (hx : x ∈ Sanctions.I) :
    x ≤ floorParams.dynamicEquilibriumRule floorEquilibrium x :=
  floorOver_rule_ge placableAffine.toParams hx

theorem floor_rule_top : floorParams.dynamicEquilibriumRule floorEquilibrium 1 = 1 :=
  floorOver_rule_top placableAffine.toParams

theorem floor_rule_lt_one {x : ℝ} (hx : x ∈ Sanctions.I) (h1 : x < 1) :
    floorParams.dynamicEquilibriumRule floorEquilibrium x < 1 :=
  floorOver_rule_lt_one placableAffine.toParams hx h1

/-- **Rule 9 form.** There is an economy with a constructed top-selector
equilibrium whose realised rule lies at or above the state everywhere, equals
`1` at the top state, and lies strictly below `1` at every other state: a
floor reaching the top forces `R(1) = 1` and nothing more.

Since round BH-5 (renovation item BH5.3, 2026-10-07) the instance of
`endpoint_floor_not_whole_basin_corner_generalF` at the affine member, with the
transition and discount conjuncts forgotten; statement unchanged (pinned). -/
theorem endpoint_floor_not_whole_basin_corner :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop),
      (∀ x ∈ Sanctions.I, x ≤ p.dynamicEquilibriumRule E x) ∧
      p.dynamicEquilibriumRule E 1 = 1 ∧
      ∀ x ∈ Sanctions.I, x < 1 → p.dynamicEquilibriumRule E x < 1 := by
  obtain ⟨p, E, -, -, -, h⟩ :=
    endpoint_floor_not_whole_basin_corner_generalF placableAffine.toParams
  exact ⟨p, E, h⟩

end

#print axioms Sanctions.Examples.floorEquilibrium
#print axioms Sanctions.Examples.endpoint_floor_not_whole_basin_corner
#print axioms Sanctions.Examples.floorOverEquilibrium
#print axioms Sanctions.Examples.endpoint_floor_not_whole_basin_corner_generalF

end Examples
end Sanctions
