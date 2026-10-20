/-
Sanctions/Examples/LowBasinSeparationWitness.lean

**The Sender-only low basin is strictly weaker than the joint low basin** (renovation item
BH5.6(a), 2026-10-07; audit item H-7; Rule 9B generality witness).

`Theory/Basin/SenderPersistenceLow.lean` drops the Target's sanction preference from the low
basin. `SenderPersistenceBasinLow` keeps three of the six fields of `JointPreferenceBasinLow`
(the ceiling `x̄ ≤ 1`, the Sender's level condition and monotonicity of the realised rule), and
the row-3 sibling `standardCompliance_low_basin_generalF_of_sender_level` asks for no Target
condition at all. Until now no economy was exhibited in which the Target condition fails while
the Sender conditions hold, so that file recorded the extra generality as unwitnessed. This file
supplies the witness, over any transition.

The economy over a base economy `p₀` (its transition, discounts and adjustment rate are kept):

* Sender stage payoff `U_S(x, a, s) = −s`: every unit of sanction costs the Sender one unit;
* Target stage payoff `U_T(x, a, s) = s − a`: the Target gains from sanctions (a rally) and pays
  for compliance.

1. `lowSepEquilibrium p₀`: both values are zero, the Target defies (`α ≡ 0`) and the Sender
   never sanctions. Both Bellman equations hold, the zero sanction is the Sender's unique
   maximiser and full defiance the Target's unique maximiser, whatever the transition.
2. At every basin `[0, x̄]` with `x̄ ≤ 1` and every ceiling `s̄ ∈ [0, 1]`, the hypotheses of the
   row-3 sibling hold: the Sender's forward-looking objective `−s` is strictly decreasing, and
   the realised rule (identically `0`) is monotone. Hence `SenderPersistenceBasinLow` holds
   (`lowSep_senderBasin`).
3. The Target's forward-looking sanction objective is `s − a`, strictly increasing in the
   sanction, so the Target field fails at the state `0` of every basin: no
   `JointPreferenceBasinLow` (`lowSep_not_jointLowBasin`) and no
   `OneSidedSanctionLowBasinPreferenceThresholds` (`lowSep_not_oneSidedLow`) holds at this
   equilibrium.

`lowBasin_senderOnly_strictly_weaker_generalF` packages the three facts for every base economy;
`senderLowBasin_strictly_weaker` is the closed existential at the affine member `lowSepParams`.

**Rule 9 (9A).** An existence certificate for the separation of the two classes, and nothing
more. The equilibrium never sanctions, so the four persistence conclusions of the row-3 sibling
are trivially true here (the conjunct `∀ x, rule x = 0` says so in the statement): the witness
says nothing about persistence while sanctions are active, and nothing about how common such
economies are. **Rule 9B.** No opaque `Prop` field is supplied: every field of
`SenderPersistenceBasinLow` is a relation over the data `(V_S, α, x̄, s̄)`, and joint
satisfiability is what the constructed equilibrium is. **Rule 22.** General in `F`: the family
`lowSepOver p₀` keeps any transition; the closed instance `lowSepParams` uses the affine law at
rate `1/2` and is marked so. **Rule 1.** Both strategies are proved optimal. **Rule 3.** No
assumption is introduced. **Rule 9C.** The arithmetic (the objectives `−s` and `s − a`, the
zero fixed points, and the gap `1` between the Target's objective at `s = 1` and at `s = 0`) was
checked in exact arithmetic before the Lean was written.
-/
import Sanctions.Theory.Basin.SenderPersistenceLow

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## The economy over an arbitrary base -/

/-- The Sender's stage payoff `−s`: every unit of sanction costs one unit. -/
def lowSepU_S (_x _a s : ℝ) : ℝ := -s

/-- The Target's stage payoff `s − a`: sanctions rally the Target, compliance costs it. -/
def lowSepU_T (_x a s : ℝ) : ℝ := s - a

theorem lowSepU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => lowSepU_S xas.1 xas.2.1 xas.2.2) := by
  unfold lowSepU_S; fun_prop

theorem lowSepU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => lowSepU_T xas.1 xas.2.1 xas.2.2) := by
  unfold lowSepU_T; fun_prop

/-- Rule-1 coupling of the stage selector: the zero sanction maximises `−s` on `[0, 1]`. -/
theorem lowSep_zero_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => lowSepU_S x a s) (Set.Icc (0 : ℝ) 1) 0 := by
  intro s hs
  change -s ≤ -0
  linarith [hs.1]

/-- **The economy over an arbitrary base economy.** Keeps the transition `F`, both discount
factors and the adjustment rate of `p₀`, and installs the stage payoffs `−s` (Sender) and
`s − a` (Target) with the stage selector `0`. General in `F`: the transition is whatever `p₀`
carries. -/
def lowSepOver (p₀ : Params) : Params :=
  { p₀ with
    U_T := lowSepU_T
    U_S := lowSepU_S
    σ := fun _ _ => 0
    σ_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
    σ_isMaxOn_U_S := lowSep_zero_isMaxOn
    U_T_continuous := lowSepU_T_continuous
    U_S_continuous := lowSepU_S_continuous }

/-- **`lowSepOver` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance lowSepOver_staticSelectorContinuous (p₀ : Params) :
    (lowSepOver p₀).StaticSelectorContinuous where
  σ_continuous := continuous_const

theorem lowSepOver_U_S (p₀ : Params) (x a s : ℝ) : (lowSepOver p₀).U_S x a s = -s := rfl
theorem lowSepOver_U_T (p₀ : Params) (x a s : ℝ) : (lowSepOver p₀).U_T x a s = s - a := rfl
theorem lowSepOver_F (p₀ : Params) : (lowSepOver p₀).F = p₀.F := rfl
theorem lowSepOver_β_S (p₀ : Params) : (lowSepOver p₀).β_S = p₀.β_S := rfl
theorem lowSepOver_β_T (p₀ : Params) : (lowSepOver p₀).β_T = p₀.β_T := rfl

/-- The zero value. -/
def lowSepZero : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := 0

theorem lowSepZero_apply (y : ↥(Sanctions.S : Set ℝ)) : lowSepZero y = 0 := by
  change (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) y = 0
  rw [BoundedContinuousFunction.coe_zero]; rfl

section OverAnyTransition

variable (p₀ : Params)

/-- The Sender's forward-looking objective at the zero value is `−s`, over any transition and
any Sender discount. General in `F`. -/
theorem lowSep_senderObj (x a s : ℝ) :
    (lowSepOver p₀).U_S x a s
        + (lowSepOver p₀).β_S * lowSepZero (Sanctions.clipS' ((lowSepOver p₀).F x s))
      = -s := by
  rw [lowSepZero_apply, mul_zero, add_zero, lowSepOver_U_S]

/-- **The Sender never sanctions**: at the zero value its greatest forward-looking best response
is `0` at every state and every Target action, over any transition. General in `F`. -/
theorem lowSep_σ_dyn_top (x a : ℝ) : (lowSepOver p₀).σ_dyn_top lowSepZero x a = 0 := by
  have hmem := (lowSepOver p₀).σ_dyn_top_mem_I lowSepZero x a
  have hmax := (lowSepOver p₀).σ_dyn_top_isMaxOn lowSepZero x a
    (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)
  simp only [Set.mem_setOf_eq] at hmax
  rw [lowSep_senderObj, lowSep_senderObj] at hmax
  linarith [hmem.1]

/-- The Target's joint objective at the zero values is `−a`, over any transition and any
Target discount: the sanction it faces is `0` whatever it does. General in `F`. -/
theorem lowSep_joint (x a : ℝ) :
    (lowSepOver p₀).joint_T_top_integrand lowSepZero lowSepZero x a = -a := by
  simp only [Params.joint_T_top_integrand]
  rw [lowSep_σ_dyn_top, lowSepZero_apply, mul_zero, add_zero, lowSepOver_U_T, zero_sub]

/-- The Target's forward-looking sanction objective at the zero value is `s − a`: it rises with
the sanction. General in `F`. -/
theorem lowSep_targetObj (x a s : ℝ) :
    (lowSepOver p₀).targetSanctionObjective lowSepZero x a s = s - a := by
  unfold Params.targetSanctionObjective
  rw [lowSepZero_apply, mul_zero, add_zero, lowSepOver_U_T]

/-- **The equilibrium, over any transition.** Rule 15: constructed. Rule 1: the zero sanction
is the Sender's unique maximiser (`lowSep_σ_dyn_top`) and full defiance the Target's unique
maximiser (its objective is `−a`). Both values are the zero function. General in `F`. -/
def lowSepEquilibrium : (lowSepOver p₀).FeedbackStackelbergEquilibriumTop where
  V_T := lowSepZero
  V_S := lowSepZero
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := by
    ext y
    change lowSepZero y = sSup ((fun s => (lowSepOver p₀).integrandS (fun _ => 0)
      (fun z => lowSepZero z) (y.val, s)) '' Sanctions.I)
    have hval : ∀ s, (lowSepOver p₀).integrandS (fun _ => 0) (fun z => lowSepZero z)
        (y.val, s) = -s := by
      intro s
      simp only [Params.integrandS]
      exact lowSep_senderObj p₀ y.val 0 s
    have hgt : IsGreatest ((fun s => (lowSepOver p₀).integrandS (fun _ => 0)
        (fun z => lowSepZero z) (y.val, s)) '' Sanctions.I) (lowSepZero y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval, lowSepZero_apply, neg_zero]
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval, lowSepZero_apply]
        linarith [hs.1]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => (lowSepOver p₀).joint_T_top_integrand lowSepZero
        lowSepZero y.val a) '' Sanctions.I) (lowSepZero y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [lowSep_joint, lowSepZero_apply, neg_zero]
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [lowSep_joint, lowSepZero_apply]
        linarith [ha.1]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x _ => by
    intro a ha
    change (lowSepOver p₀).joint_T_top_integrand lowSepZero lowSepZero x a
      ≤ (lowSepOver p₀).joint_T_top_integrand lowSepZero lowSepZero x 0
    rw [lowSep_joint, lowSep_joint, neg_zero]
    linarith [ha.1]

/-- The realised sanction is `0` at every state. General in `F`. -/
theorem lowSep_rule_eq_zero (x : ℝ) :
    (lowSepOver p₀).dynamicTopRealizedRule (lowSepEquilibrium p₀).V_S
      (lowSepEquilibrium p₀).α x = 0 :=
  lowSep_σ_dyn_top p₀ x 0

/-- The Sender's forward-looking objective along the equilibrium is `−s`. General in `F`. -/
theorem lowSep_senderDynObjective (x s : ℝ) :
    (lowSepOver p₀).senderDynObjective (lowSepEquilibrium p₀).V_S x
      ((lowSepEquilibrium p₀).α x) s = -s :=
  lowSep_senderObj p₀ x 0 s

/-- The Target's forward-looking sanction objective along the equilibrium is `s`. General in
`F`. -/
theorem lowSep_targetSanctionObjective (x s : ℝ) :
    (lowSepOver p₀).targetSanctionObjective (lowSepEquilibrium p₀).V_T x
      ((lowSepEquilibrium p₀).α x) s = s := by
  have h := lowSep_targetObj p₀ x 0 s
  rw [sub_zero] at h
  exact h

/-! ## The Sender-only low basin holds -/

/-- **The row-3 sibling's Sender input holds**: the Sender's forward-looking objective, at the
Target's equilibrium action, is strictly decreasing in the sanction on every interval. General
in `F`. -/
theorem lowSep_sender_strictAnti (x sbar : ℝ) :
    StrictAntiOn (fun s => (lowSepOver p₀).senderDynObjective (lowSepEquilibrium p₀).V_S x
      ((lowSepEquilibrium p₀).α x) s) (Set.Icc (min x sbar) (1 : ℝ)) := by
  intro s₁ _ s₂ _ h
  simp only [lowSep_senderDynObjective]
  linarith

/-- **The realised rule is monotone** on every set (it is identically `0`). General in `F`. -/
theorem lowSep_rule_monotone (T : Set ℝ) :
    MonotoneOn ((lowSepOver p₀).dynamicTopRealizedRule (lowSepEquilibrium p₀).V_S
      (lowSepEquilibrium p₀).α) T := by
  intro x _ y _ _
  rw [lowSep_rule_eq_zero, lowSep_rule_eq_zero]

/-- **The Sender-only low basin holds at every basin `[0, x̄]` with `x̄ ≤ 1` and every ceiling
`s̄ ≥ 0`.** The realised sanction `0` is below `min(x, s̄)` on the basin, and the rule is
monotone. General in `F`. -/
theorem lowSep_senderBasin {xbar sbar : ℝ} (hxbar : xbar ≤ 1) (hsbar : 0 ≤ sbar) :
    (lowSepOver p₀).SenderPersistenceBasinLow (lowSepEquilibrium p₀).V_S
      (lowSepEquilibrium p₀).α xbar sbar where
  xbar_low_le_one := hxbar
  sender_low_argmax_le_threshold := fun x hx => by
    rw [lowSep_rule_eq_zero]
    exact le_min hx.1 hsbar
  top_rule_mono := lowSep_rule_monotone p₀ _

/-! ## The Target condition fails -/

/-- **The Target likes sanctions at the state `0`**: its forward-looking sanction objective is
not non-increasing on `[min(0, s̄), 1]`, whatever `s̄` is, since it equals `s`. General in
`F`. -/
theorem lowSep_target_not_antitone (sbar : ℝ) :
    ¬ AntitoneOn (fun s => (lowSepOver p₀).targetSanctionObjective (lowSepEquilibrium p₀).V_T 0
      ((lowSepEquilibrium p₀).α 0) s) (Set.Icc (min 0 sbar) (1 : ℝ)) := by
  intro h
  have h01 := h ⟨min_le_left 0 sbar, zero_le_one⟩
    ⟨(min_le_left 0 sbar).trans zero_le_one, le_rfl⟩ zero_le_one
  dsimp only at h01
  rw [lowSep_targetSanctionObjective, lowSep_targetSanctionObjective] at h01
  linarith

/-- **No joint low basin holds at this equilibrium**, at any basin containing the state `0`:
its Target field `target_dislikes_sanctions` fails at `0`. General in `F`. -/
theorem lowSep_not_jointLowBasin {xbar sbar : ℝ} (hxbar : 0 ≤ xbar) :
    ¬ (lowSepOver p₀).JointPreferenceBasinLow (lowSepEquilibrium p₀).V_T
      (lowSepEquilibrium p₀).V_S (lowSepEquilibrium p₀).α xbar sbar :=
  fun hB => lowSep_target_not_antitone p₀ sbar (hB.target_dislikes_sanctions 0 ⟨le_rfl, hxbar⟩)

/-- **Row 3's hypothesis bundle fails at this equilibrium**, for every pair of pivots and every
ceiling: its Target field `target_dislikes_high_sanctions` fails at the state `0` (the pivot
`xT⋆` is feasible, so `0` lies in its basin). General in `F`. -/
theorem lowSep_not_oneSidedLow {xT xS sbar : ℝ} :
    ¬ (lowSepOver p₀).OneSidedSanctionLowBasinPreferenceThresholds (lowSepEquilibrium p₀).V_T
      (lowSepEquilibrium p₀).V_S (lowSepEquilibrium p₀).α xT xS sbar :=
  fun hOne => lowSep_target_not_antitone p₀ sbar
    (hOne.target_dislikes_high_sanctions 0 ⟨le_rfl, hOne.xT_star_mem.1⟩)

end OverAnyTransition

/-! ## The separation -/

/-- **The Sender-only low basin is strictly weaker than the joint one, over any transition**
(renovation item BH5.6(a), 2026-10-07).

For every economy `p₀` there is an economy with the same transition and the same two discount
factors, and a constructed top-selector equilibrium of it, such that

* the realised sanction is `0` at every state (Rule 9A: the persistence conclusions are trivial
  here, and the witness separates classes only);
* at every basin `[0, x̄]` with `x̄ ≤ 1` and every ceiling `s̄ ∈ [0, 1]`, the hypotheses of the
  row-3 sibling `standardCompliance_low_basin_generalF_of_sender_level` hold — the Sender's
  forward-looking objective is strictly decreasing in the sanction above `min(x, s̄)`, and the
  realised rule is monotone — and so does `SenderPersistenceBasinLow`;
* at every basin containing the state `0`, the joint low basin `JointPreferenceBasinLow` fails;
* row 3's hypothesis bundle `OneSidedSanctionLowBasinPreferenceThresholds` fails for every pair
  of pivots and every ceiling.

So dropping the Target's sanction preference from the low basin enlarges the class. General in
`F`, with no hypothesis on `p₀`. -/
theorem lowBasin_senderOnly_strictly_weaker_generalF (p₀ : Params) :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop),
      p.F = p₀.F ∧ p.β_S = p₀.β_S ∧ p.β_T = p₀.β_T ∧
      (∀ x, p.dynamicTopRealizedRule E.V_S E.α x = 0) ∧
      (∀ xbar sbar : ℝ, xbar ≤ 1 → sbar ∈ Sanctions.I →
        (∀ x ∈ Set.Icc (0 : ℝ) xbar,
          StrictAntiOn (fun s => p.senderDynObjective E.V_S x (E.α x) s)
            (Set.Icc (min x sbar) (1 : ℝ))) ∧
        MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc (0 : ℝ) xbar) ∧
        p.SenderPersistenceBasinLow E.V_S E.α xbar sbar) ∧
      (∀ xbar sbar : ℝ, 0 ≤ xbar → ¬ p.JointPreferenceBasinLow E.V_T E.V_S E.α xbar sbar) ∧
      (∀ xT xS sbar : ℝ,
        ¬ p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α xT xS sbar) :=
  ⟨lowSepOver p₀, lowSepEquilibrium p₀, rfl, rfl, rfl, lowSep_rule_eq_zero p₀,
    fun _ _ hx hs => ⟨fun x _ => lowSep_sender_strictAnti p₀ x _, lowSep_rule_monotone p₀ _,
      lowSep_senderBasin p₀ hx hs.1⟩,
    fun _ _ hx => lowSep_not_jointLowBasin p₀ hx,
    fun _ _ _ => lowSep_not_oneSidedLow p₀⟩

/-- **A closed member**: the affine transition at rate `1/2` and both discounts `1/2`, with the
stage payoffs above. Rule 22: affine-restricted, and marked so; `lowSepOver` is the family over
any transition, and `lowSepOver lowSepParams` is this economy field for field. -/
def lowSepParams : Params where
  δ := 1 / 2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1 / 2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1 / 2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := lowSepU_T
  U_S := lowSepU_S
  σ := fun _ _ => 0
  σ_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  σ_isMaxOn_U_S := lowSep_zero_isMaxOn
  U_T_continuous := lowSepU_T_continuous
  U_S_continuous := lowSepU_S_continuous
  F := affineF (1 / 2)
  F_continuous := affineF_continuous _
  F_mono_x := affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := affineF_diag _

/-- **`lowSepParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance lowSepParams_staticSelectorContinuous :
    lowSepParams.StaticSelectorContinuous where
  σ_continuous := continuous_const

/-- **Rule 9 form.** There is an economy, an optimising top-selector equilibrium of it and a
basin `[0, x̄]` with ceiling `s̄` at which the Sender-only low basin holds and the joint low basin
fails (here `x̄ = s̄ = 1`, at `lowSepParams`). An existence certificate separating the two
classes; the equilibrium never sanctions. -/
theorem senderLowBasin_strictly_weaker :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop) (xbar sbar : ℝ),
      p.SenderPersistenceBasinLow E.V_S E.α xbar sbar ∧
      ¬ p.JointPreferenceBasinLow E.V_T E.V_S E.α xbar sbar :=
  ⟨lowSepOver lowSepParams, lowSepEquilibrium lowSepParams, 1, 1,
    lowSep_senderBasin lowSepParams le_rfl zero_le_one,
    lowSep_not_jointLowBasin lowSepParams zero_le_one⟩

/-- **Rule 11 form.** The Sender-only low basin does not imply the joint low basin: the
universal implication fails. -/
theorem senderLowBasin_not_implies_joint :
    ¬ ∀ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop) (xbar sbar : ℝ),
      p.SenderPersistenceBasinLow E.V_S E.α xbar sbar →
        p.JointPreferenceBasinLow E.V_T E.V_S E.α xbar sbar := by
  intro h
  obtain ⟨p, E, xbar, sbar, hS, hJ⟩ := senderLowBasin_strictly_weaker
  exact hJ (h p E xbar sbar hS)

end

#print axioms Sanctions.Examples.lowSepEquilibrium
#print axioms Sanctions.Examples.lowBasin_senderOnly_strictly_weaker_generalF
#print axioms Sanctions.Examples.senderLowBasin_strictly_weaker
#print axioms Sanctions.Examples.senderLowBasin_not_implies_joint

end Examples
end Sanctions
