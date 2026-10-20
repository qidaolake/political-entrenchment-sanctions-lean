/-
Sanctions/Examples/PersistencePackageNonuniqueWitness.lean

**The persistence package does not select one common steady state for the
basin: every field filled at an economy whose equilibrium closed loop is the
identity, so every path converges — to its own starting state** (round M, doc
82 P4; title sharpened 2026-09-11, the reader's C07;
the reader's mathematical-validation package of 2026-09-06, documents 01 §7 and
02 §8; doc 71 T6).

`thm:persistence` (`standardCompliance_persistence_generalF_from_sender_package`)
concludes, from the Sender persistence package (P1, P2, P3, P5) at an
equilibrium, that every path started in the basin stays there with sanctions at
or above the pivot and nondecreasing. It does not conclude that the paths share
a limit; the manuscript says so in words and
`MonotoneAttraction.attraction_iff_unique_fixedPoint` says why in the abstract.
This file is the package-level Rule-11 object: an economy, a `ValueClass2` with
singleton carriers, a constructed top-selector equilibrium and every field of
`SenderPersistencePackage` discharged, at which the equilibrium closed loop
fixes every state of the basin — persistence holds, and no state is a common
limit of the basin's paths.

The economy: `U_S(x, a, s) = −(s − x)²`, `U_T(x, a, s) = xs − a²`, any
transition `F` (the literal member `tsParams` uses the affine law at rate
`1/2`), both discounts `1/2`. The values `V_S ≡ 0` and
`V_T(y) = 2y²`, the policy `α ≡ 0`, the response `R(x) = x`. Both Bellman
identities hold (the Sender's objective at the zero value is `−(s − x)²`,
maximal at `s = x` with value `0`; the Target's joint objective is `2x² − a²`,
maximal at `a = 0` with value `2x²`), both optima are unique, so `(V_T, V_S, 0)`
is a top-selector feedback Stackelberg equilibrium (Rule 15: constructed;
Rule 1: both policies derived). Carriers `{V_T}` and `{V_S}`, `K_S = 0`, pivots
`x_T = x_S = 1/2`: P2 is trivial, P3 follows from increasing differences of
`−(s − x)²` in `(s, x)` through the single-crossing bridge, P5's chord is
`(s₂ − s₁)(2x − s₁ − s₂) > 0` for `0 ≤ s₁ < s₂ ≤ x` (the pivot is `x` on
`[1/2, 1]`), and the carrier selector equals `α` everywhere because the Target
optimum is unique at every physical state. The closed loop is `F(x, R(x)) = x`.

Rule 9: an existence certificate refuting one implication ("the package selects
a limit"); it says nothing about the placable family, whose non-affine member
contracts (`placableQuadDiag_unique_attracting_state`). Rule 22: general in `F`
(round BH-5, item BH5.1, 2026-10-07). The construction is `tsParamsOf p₀`, which
takes the transition and its four structural fields from any economy `p₀`. The
witness reads the transition only through `F_diag`, at three places (the two
Target objectives and the closed loop): the Sender's optimum is the state
itself, so the successor is `F(x, x) = x` whatever the law does off the
diagonal. `persistence_package_not_unique_steady_state_generalF` states the
refutation at every transition; the literal `tsParams` (affine, `affineF (1/2)`)
is the member at its own transition (`tsParamsOf_self`), and every literal name
is kept as a one-line instance. Rule 9C: every quantity is rational and was
checked in exact arithmetic first
(`docs/archive/workflow-scratch/round_M_stage0_check.py`).
-/
import Sanctions.Examples.WitnessKit
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Foundations.IntervalDominanceOrder
import Sanctions.Foundations.MilgromShannon
import Sanctions.Theory.Certificates.SenderPersistencePackage

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame Sanctions.IntervalDominanceOrder Sanctions.MilgromShannon

noncomputable section

/-! ## 0. The economy -/

/-- Sender stage payoff `−(s − x)²`: the Sender wants the sanction at the state. -/
def tsU_S (x a s : ℝ) : ℝ := -(s - x) ^ 2

/-- Target stage payoff `xs − a²`. -/
def tsU_T (x a s : ℝ) : ℝ := x * s - a ^ 2

/-- The stage selector: the clipped vertex `x`. -/
def tsSigma (x a : ℝ) : ℝ := Sanctions.clipS x

theorem tsSigma_mem (x a : ℝ) : tsSigma x a ∈ Set.Icc (0 : ℝ) 1 := Sanctions.clipS_mem _

theorem tsSigma_continuous : Continuous (fun xa : ℝ × ℝ => tsSigma xa.1 xa.2) := by
  unfold tsSigma
  exact Sanctions.clipS_continuous.comp continuous_fst

theorem tsU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => tsU_S xas.1 xas.2.1 xas.2.2) := by
  unfold tsU_S; fun_prop

theorem tsU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => tsU_T xas.1 xas.2.1 xas.2.2) := by
  unfold tsU_T; fun_prop

/-- Rule-1 coupling of the stage selector: the clipped vertex maximises the
concave parabola `−(s − x)²` on `[0,1]`. -/
theorem tsSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => tsU_S x a s) Sanctions.I (tsSigma x a) := by
  refine WitnessKit.clipVertex_isMaxOn (k := (1 : ℝ)) (C := 0) (t := x)
    (U := fun s => tsU_S x a s) (by norm_num) ?_
  intro s
  unfold tsU_S; ring

/-- The economy. Rule 22: affine-restricted (`affineF (1/2)`), and marked so. It is
the member of the general-`F` family `tsParamsOf` at its own transition
(`tsParamsOf_self`); every result below is proved for the family. -/
def tsParams : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 1 / 2
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := tsU_T
  U_S := tsU_S
  σ := tsSigma
  σ_mem := tsSigma_mem
  σ_isMaxOn_U_S := tsSigma_isMaxOn
  U_T_continuous := tsU_T_continuous
  U_S_continuous := tsU_S_continuous
  F := AbstractGame.affineF (1 / 2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x (by constructor <;> norm_num)
  F_mono_s := AbstractGame.affineF_mono_s (by constructor <;> norm_num)
  F_diag := AbstractGame.affineF_diag _

/-- **`tsParams` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance tsParams_staticSelectorContinuous :
    tsParams.StaticSelectorContinuous where
  σ_continuous := tsSigma_continuous

@[simp] theorem tsParams_U_S : tsParams.U_S = tsU_S := rfl
@[simp] theorem tsParams_U_T : tsParams.U_T = tsU_T := rfl
@[simp] theorem tsParams_β_S : tsParams.β_S = 1 / 2 := rfl
@[simp] theorem tsParams_β_T : tsParams.β_T = 1 / 2 := rfl
@[simp] theorem tsParams_F : tsParams.F = AbstractGame.affineF (1 / 2) := rfl

/-- **The economy over any transition** (round BH-5, item BH5.1, 2026-10-07). The
stage payoffs, the stage selector, the discounts and the inert rate `δ` of
`tsParams`, with the transition `F` and its four structural fields (continuity,
the two monotonicities, the diagonal) taken from an arbitrary economy `p₀`.
Rule 22: general in `F`. Nothing is assumed about `p₀.F` beyond the `Params`
fields it already carries, and the witness reads it only through `F_diag`. -/
def tsParamsOf (p₀ : AbstractGame.Params) : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 1 / 2
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := tsU_T
  U_S := tsU_S
  σ := tsSigma
  σ_mem := tsSigma_mem
  σ_isMaxOn_U_S := tsSigma_isMaxOn
  U_T_continuous := tsU_T_continuous
  U_S_continuous := tsU_S_continuous
  F := p₀.F
  F_continuous := p₀.F_continuous
  F_mono_x := p₀.F_mono_x
  F_mono_s := p₀.F_mono_s
  F_diag := p₀.F_diag

/-- **`tsParamsOf` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance tsParamsOf_staticSelectorContinuous (p₀ : AbstractGame.Params) :
    (tsParamsOf p₀).StaticSelectorContinuous where
  σ_continuous := tsSigma_continuous

@[simp] theorem tsParamsOf_U_S (p₀ : AbstractGame.Params) : (tsParamsOf p₀).U_S = tsU_S := rfl
@[simp] theorem tsParamsOf_U_T (p₀ : AbstractGame.Params) : (tsParamsOf p₀).U_T = tsU_T := rfl
@[simp] theorem tsParamsOf_β_S (p₀ : AbstractGame.Params) : (tsParamsOf p₀).β_S = 1 / 2 := rfl
@[simp] theorem tsParamsOf_β_T (p₀ : AbstractGame.Params) : (tsParamsOf p₀).β_T = 1 / 2 := rfl
@[simp] theorem tsParamsOf_F (p₀ : AbstractGame.Params) : (tsParamsOf p₀).F = p₀.F := rfl

/-- The literal economy is the family member at its own (affine) transition, by
definition. -/
theorem tsParamsOf_self : tsParamsOf tsParams = tsParams := rfl

/-! ## 1. The values, the selectors, the two uniqueness facts -/

/-- The zero Sender value. -/
def tsZero : ChordEconomy.Val := ChordEconomy.affBCF 0 0

theorem tsZero_apply (y : ↥(Sanctions.S : Set ℝ)) : tsZero y = 0 := by
  unfold tsZero; rw [ChordEconomy.affBCF_apply]; ring

/-- The Target value `2y²`. -/
def tsVT : ChordEconomy.Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => 2 * y.val ^ 2, by fun_prop⟩

theorem tsVT_apply (y : ↥(Sanctions.S : Set ℝ)) : tsVT y = 2 * y.val ^ 2 := rfl

/-- The Sender's dynamic objective at the zero value is the stage payoff, over any
transition: the continuation is identically zero, so the successor state never
enters. General in `F`. -/
theorem tsOf_senderObj (p₀ : AbstractGame.Params) (x a s : ℝ) :
    (tsParamsOf p₀).U_S x a s
        + (tsParamsOf p₀).β_S * tsZero (Sanctions.clipS' ((tsParamsOf p₀).F x s))
      = -(s - x) ^ 2 := by
  rw [tsZero_apply, tsParamsOf_U_S, tsParamsOf_β_S]; unfold tsU_S; ring

/-- The Sender's dynamic objective at the zero value is the stage payoff. -/
theorem ts_senderObj (x a s : ℝ) :
    tsParams.U_S x a s + tsParams.β_S * tsZero (Sanctions.clipS' (tsParams.F x s))
      = -(s - x) ^ 2 :=
  tsOf_senderObj tsParams x a s

/-- `tsOf_senderObj` in the `senderDynObjective` vocabulary. General in `F`. -/
theorem tsOf_dynObj (p₀ : AbstractGame.Params) (x a s : ℝ) :
    (tsParamsOf p₀).senderDynObjective tsZero x a s = -(s - x) ^ 2 := by
  unfold Params.senderDynObjective; exact tsOf_senderObj p₀ x a s

theorem ts_dynObj (x a s : ℝ) :
    tsParams.senderDynObjective tsZero x a s = -(s - x) ^ 2 :=
  tsOf_dynObj tsParams x a s

/-- Every maximiser of the Sender's objective at a feasible state is the state,
over any transition. General in `F`. -/
theorem tsOf_sender_argmax_eq (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a s : ℝ}
    (hmax : IsMaxOn (fun s' => (tsParamsOf p₀).U_S x a s'
      + (tsParamsOf p₀).β_S * tsZero (Sanctions.clipS' ((tsParamsOf p₀).F x s')))
        Sanctions.I s) :
    s = x := by
  have h := hmax hx
  simp only [Set.mem_setOf_eq] at h
  rw [tsOf_senderObj, tsOf_senderObj] at h
  have h0 : s - x = 0 := by nlinarith [sq_nonneg (s - x)]
  linarith

/-- Every maximiser of the Sender's objective at a feasible state is the state. -/
theorem ts_sender_argmax_eq {x : ℝ} (hx : x ∈ Sanctions.I) {a s : ℝ}
    (hmax : IsMaxOn (fun s' => tsParams.U_S x a s'
      + tsParams.β_S * tsZero (Sanctions.clipS' (tsParams.F x s'))) Sanctions.I s) :
    s = x :=
  tsOf_sender_argmax_eq tsParams hx hmax

/-- The greatest Sender response at the zero value is the state. General in `F`. -/
theorem tsOf_σ_dyn_top (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    (tsParamsOf p₀).σ_dyn_top tsZero x a = x :=
  tsOf_sender_argmax_eq p₀ hx ((tsParamsOf p₀).σ_dyn_top_isMaxOn tsZero x a)

theorem ts_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    tsParams.σ_dyn_top tsZero x a = x :=
  tsOf_σ_dyn_top tsParams hx a

/-- The ordinary Sender response at the zero value is the state. General in `F`. -/
theorem tsOf_σ_dyn (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    (tsParamsOf p₀).σ_dyn tsZero x a = x :=
  tsOf_sender_argmax_eq p₀ hx ((tsParamsOf p₀).σ_dyn_isMaxOn tsZero x a)

theorem ts_σ_dyn {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    tsParams.σ_dyn tsZero x a = x :=
  tsOf_σ_dyn tsParams hx a

/-- **Sender argmax uniqueness at the zero value** (`DynamicArgmaxUnique`), over
any transition. General in `F`. -/
theorem tsOf_DAU (p₀ : AbstractGame.Params) : (tsParamsOf p₀).DynamicArgmaxUnique tsZero := by
  intro x hx a s₁ s₂ _ _ h₁ h₂
  rw [tsOf_sender_argmax_eq p₀ hx h₁, tsOf_sender_argmax_eq p₀ hx h₂]

/-- **Sender argmax uniqueness at the zero value** (`DynamicArgmaxUnique`). -/
theorem ts_DAU : tsParams.DynamicArgmaxUnique tsZero :=
  tsOf_DAU tsParams

/-- The Target's joint objective (ordinary selector) is `2x² − a²`, over any
transition: the realised successor is `F(x, x) = x` (first of the three `F_diag`
reads). General in `F`. -/
theorem tsOf_joint (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    (tsParamsOf p₀).joint_T_integrand tsVT tsZero x a = 2 * x ^ 2 - a ^ 2 := by
  simp only [Params.joint_T_integrand]
  rw [tsOf_σ_dyn p₀ hx a, tsParamsOf_U_T, tsParamsOf_β_T, tsParamsOf_F, p₀.F_diag,
    tsVT_apply, Sanctions.clipS'_val_eq_of_mem hx]
  unfold tsU_T; ring

/-- The Target's joint objective (ordinary selector) is `2x² − a²`. -/
theorem ts_joint {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    tsParams.joint_T_integrand tsVT tsZero x a = 2 * x ^ 2 - a ^ 2 :=
  tsOf_joint tsParams hx a

/-- The Target's joint objective (top selector) is `2x² − a²`, over any transition
(second `F_diag` read). General in `F`. -/
theorem tsOf_joint_top (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    (tsParamsOf p₀).joint_T_top_integrand tsVT tsZero x a = 2 * x ^ 2 - a ^ 2 := by
  simp only [Params.joint_T_top_integrand]
  rw [tsOf_σ_dyn_top p₀ hx a, tsParamsOf_U_T, tsParamsOf_β_T, tsParamsOf_F, p₀.F_diag,
    tsVT_apply, Sanctions.clipS'_val_eq_of_mem hx]
  unfold tsU_T; ring

/-- The Target's joint objective (top selector) is `2x² − a²`. -/
theorem ts_joint_top {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    tsParams.joint_T_top_integrand tsVT tsZero x a = 2 * x ^ 2 - a ^ 2 :=
  tsOf_joint_top tsParams hx a

/-- Every Target maximiser at a feasible state is full defiance, over any
transition. General in `F`. -/
theorem tsOf_target_argmax_eq (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (_ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => (tsParamsOf p₀).joint_T_integrand tsVT tsZero x b)
      Sanctions.I a) :
    a = 0 := by
  have h := hmax (show (0 : ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
  simp only [Set.mem_setOf_eq] at h
  rw [tsOf_joint p₀ hx, tsOf_joint p₀ hx] at h
  have h2 : a ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg a)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2

/-- Every Target maximiser at a feasible state is full defiance. -/
theorem ts_target_argmax_eq {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => tsParams.joint_T_integrand tsVT tsZero x b) Sanctions.I a) :
    a = 0 :=
  tsOf_target_argmax_eq tsParams hx ha hmax

/-- **Target argmax uniqueness at the pair** (`TargetArgmaxUnique`), over any
transition. General in `F`. -/
theorem tsOf_TAU (p₀ : AbstractGame.Params) : (tsParamsOf p₀).TargetArgmaxUnique tsVT tsZero := by
  intro x hx a₁ a₂ h₁ h₂ hm₁ hm₂
  rw [tsOf_target_argmax_eq p₀ hx h₁ hm₁, tsOf_target_argmax_eq p₀ hx h₂ hm₂]

/-- **Target argmax uniqueness at the pair** (`TargetArgmaxUnique`). -/
theorem ts_TAU : tsParams.TargetArgmaxUnique tsVT tsZero :=
  tsOf_TAU tsParams

/-! ## 2. The carrier class (singleton carriers) and the equilibrium -/

/-- Singleton carriers `{V_T}` and `{V_S}`, over any transition. General in `F`. -/
def tsClassOf (p₀ : AbstractGame.Params) : (tsParamsOf p₀).ValueClass2 where
  carrier_T := {tsVT}
  carrier_S := {tsZero}
  isClosed_T := isClosed_singleton
  isClosed_S := isClosed_singleton
  nonempty_T := Set.singleton_nonempty _
  nonempty_S := Set.singleton_nonempty _
  sender_unique_on := by
    intro V hV
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact (tsOf_DAU p₀).toOnI
  target_unique_on := by
    intro V_T hVT V_S hVS
    rw [Set.mem_singleton_iff] at hVT hVS
    subst hVT
    subst hVS
    exact tsOf_TAU p₀

/-- Singleton carriers: `{V_T}` and `{V_S}`. -/
def tsClass : tsParams.ValueClass2 := tsClassOf tsParams

/-- Full defiance maximises the Target's top-selector objective, over any
transition. General in `F`. -/
theorem tsOf_zero_isMaxOn_top (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => (tsParamsOf p₀).joint_T_top_integrand tsVT tsZero x a) Sanctions.I 0 := by
  intro a _
  change (tsParamsOf p₀).joint_T_top_integrand tsVT tsZero x a
    ≤ (tsParamsOf p₀).joint_T_top_integrand tsVT tsZero x 0
  rw [tsOf_joint_top p₀ hx, tsOf_joint_top p₀ hx]
  nlinarith [sq_nonneg a]

theorem ts_zero_isMaxOn_top {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => tsParams.joint_T_top_integrand tsVT tsZero x a) Sanctions.I 0 :=
  tsOf_zero_isMaxOn_top tsParams hx

/-- **The equilibrium, over any transition.** Rule 15: constructed; Rule 1: both
policies are unique optima (`tsOf_σ_dyn_top`, `tsOf_target_argmax_eq`), not
assumed. General in `F`: the transition enters only through `F_diag`. -/
def tsEquilibriumOf (p₀ : AbstractGame.Params) :
    (tsParamsOf p₀).FeedbackStackelbergEquilibriumTop where
  V_T := tsVT
  V_S := tsZero
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := by
    ext y
    change tsZero y = sSup ((fun s => (tsParamsOf p₀).integrandS (fun _ => 0)
      (fun z => tsZero z) (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        (tsParamsOf p₀).integrandS (fun _ => 0) (fun z => tsZero z) (y.val, s)
          = -(s - y.val) ^ 2 := by
      intro s _
      simp only [Params.integrandS]
      exact tsOf_senderObj p₀ y.val 0 s
    have hgt : IsGreatest ((fun s => (tsParamsOf p₀).integrandS (fun _ => 0)
        (fun z => tsZero z) (y.val, s)) '' Sanctions.I) (tsZero y) := by
      refine ⟨⟨y.val, y.property, ?_⟩, ?_⟩
      · dsimp only
        rw [hval _ y.property, tsZero_apply]; ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs, tsZero_apply]
        nlinarith [sq_nonneg (s - y.val)]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => (tsParamsOf p₀).joint_T_top_integrand tsVT tsZero y.val a)
        '' Sanctions.I) (tsVT y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [tsOf_joint_top p₀ y.property, tsVT_apply]; ring
      · rintro _ ⟨a, _, rfl⟩
        dsimp only
        rw [tsOf_joint_top p₀ y.property, tsVT_apply]
        nlinarith [sq_nonneg a]
    exact hgt.csSup_eq.symm
  α_opt_top := fun _ hx => tsOf_zero_isMaxOn_top p₀ hx

/-- **The equilibrium.** Rule 15: constructed; Rule 1: both policies are unique
optima (`ts_σ_dyn_top`, `ts_target_argmax_eq`), not assumed. -/
def tsEquilibrium : tsParams.FeedbackStackelbergEquilibriumTop := tsEquilibriumOf tsParams

/-! ## 3. The package -/

/-- The carrier selector is full defiance everywhere, over any transition: at a
physical state it is a Target maximiser, which is unique; off the physical
states it is the selector at the clamped state, hence the same. General in
`F`. -/
theorem tsOf_α_on_eq (p₀ : AbstractGame.Params) (hVT : tsVT ∈ (tsClassOf p₀).carrier_T)
    (hVS : tsZero ∈ (tsClassOf p₀).carrier_S) :
    (tsClassOf p₀).α_on ⟨tsVT, hVT⟩ ⟨tsZero, hVS⟩ = fun _ => 0 := by
  funext x
  change (tsParamsOf p₀).α_on_ext tsVT tsZero ((tsClassOf p₀).sender_unique_on tsZero hVS) x = 0
  set h := (tsClassOf p₀).sender_unique_on tsZero hVS
  set y := (Sanctions.clipS' x).val with hy
  have hyS : y ∈ Sanctions.S := (Sanctions.clipS' x).property
  have hclip : Sanctions.clipS' y = Sanctions.clipS' x :=
    Subtype.ext (Sanctions.clipS'_val_eq_of_mem hyS)
  have hxy : (tsParamsOf p₀).α_on_ext tsVT tsZero h x
      = (tsParamsOf p₀).α_on_ext tsVT tsZero h y := by
    unfold Params.α_on_ext; rw [hclip]
  rw [hxy]
  exact tsOf_target_argmax_eq p₀ hyS ((tsParamsOf p₀).α_on_ext_mem tsVT tsZero h y)
    ((tsParamsOf p₀).α_on_ext_isMaxOn_of_mem tsVT tsZero h hyS)

/-- The carrier selector is full defiance everywhere: at a physical state it is
a Target maximiser, which is unique; off the physical states it is the selector
at the clamped state, hence the same. -/
theorem ts_α_on_eq (hVT : tsVT ∈ tsClass.carrier_T) (hVS : tsZero ∈ tsClass.carrier_S) :
    tsClass.α_on ⟨tsVT, hVT⟩ ⟨tsZero, hVS⟩ = fun _ => 0 :=
  tsOf_α_on_eq tsParams hVT hVS

/-- Increasing differences of `−(s − x)²` in `(s, x)`: the cross difference is
`2·Δs·Δx`. -/
theorem ts_increasingDifferences :
    IncreasingDifferencesOn Sanctions.I (Set.Icc (max (1 / 2 : ℝ) (1 / 2)) 1)
      (fun s x => -(s - x) ^ 2) := by
  intro s s' x x' _ _ hss' _ _ hxx'
  nlinarith [mul_nonneg (sub_nonneg.2 hss') (sub_nonneg.2 hxx')]

/-- **Every field of the Sender persistence package, over any transition**, at
the singleton carriers, `K_S = 0`, pivots `1/2` (the fields are listed at
`tsPackage`). General in `F`: no field reads the transition. -/
theorem tsPackageOf (p₀ : AbstractGame.Params) :
    (tsParamsOf p₀).SenderPersistencePackage (tsClassOf p₀) (tsEquilibriumOf p₀)
      (1 / 2) (1 / 2) 0 :=
  { xT_mem := by constructor <;> norm_num
    xS_mem := by constructor <;> norm_num
    target_value_mem := Set.mem_singleton _
    sender_value_mem := Set.mem_singleton _
    target_policy_eq := (tsOf_α_on_eq p₀ (Set.mem_singleton _) (Set.mem_singleton _)).symm
    sender_carrier_lipschitz := by
      intro V hV
      have hV' : V = tsZero := by simpa [tsClassOf] using hV
      subst hV'
      intro y₁ y₂
      rw [tsZero_apply, tsZero_apply]
      simp
    sender_IDO_after_target_policy := by
      intro V_T V_S
      have hVS : V_S.val = tsZero := by
        have h : V_S.val ∈ ({tsZero} : Set ChordEconomy.Val) := V_S.property
        exact Set.mem_singleton_iff.mp h
      have hfun : (fun s x => (tsParamsOf p₀).senderDynObjective V_S.val x
            ((tsClassOf p₀).α_on V_T V_S x) s)
          = fun s x => -(s - x) ^ 2 := by
        funext s x
        rw [hVS]
        exact tsOf_dynObj p₀ x _ s
      rw [hfun]
      exact IDOFamilyOn.of_singleCrossingOn ts_increasingDifferences.toSingleCrossingOn
    sender_subpivot_chord := by
      -- P5 in pivot-star form on the basin (round BJ1.3): on the basin the
      -- pivot is the state itself.
      intro V_T V_S x hx s₁ hs₁
      have hpiv : max x (max (1 / 2 : ℝ) (1 / 2)) = x := max_eq_left hx.1
      rw [hpiv] at hs₁ ⊢
      rw [tsParamsOf_U_S]
      unfold tsU_S
      have h1 : 0 < x - s₁ := sub_pos.2 hs₁.2
      have h3 : 0 < (x - s₁) * (x - s₁) := mul_pos h1 h1
      simp only [mul_zero, zero_mul]
      nlinarith [h3] }

/-- **Every field of the Sender persistence package** at the singleton carriers,
`K_S = 0`, pivots `1/2`: P1 (the values in the carriers and the carrier selector
equal to the policy), P2 (Lipschitz with modulus `0`), P3 (interval dominance
from increasing differences), P5 (the sub-pivot chord, strict even with a zero
continuation allowance). -/
theorem tsPackage : tsParams.SenderPersistencePackage tsClass tsEquilibrium (1 / 2) (1 / 2) 0 :=
  tsPackageOf tsParams

/-! ## 4. Persistence holds, every basin state is steady, no common limit -/

/-- The equilibrium closed loop fixes every feasible state, over any transition
(third `F_diag` read: the realised sanction is the state). General in `F`. -/
theorem tsOf_step_eq (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) :
    (tsParamsOf p₀).dynamicTopLockInStepF (tsEquilibriumOf p₀).V_S (tsEquilibriumOf p₀).α x
      = x := by
  unfold Params.dynamicTopLockInStepF Params.dynamicTopRealizedRule
  change (tsParamsOf p₀).F x ((tsParamsOf p₀).σ_dyn_top tsZero x 0) = x
  rw [tsOf_σ_dyn_top p₀ hx 0, tsParamsOf_F, p₀.F_diag]

theorem ts_step_eq {x : ℝ} (hx : x ∈ Sanctions.I) :
    tsParams.dynamicTopLockInStepF tsEquilibrium.V_S tsEquilibrium.α x = x :=
  tsOf_step_eq tsParams hx

/-- Every equilibrium path from a feasible state is constant, over any
transition. General in `F`. -/
theorem tsOf_path_eq (p₀ : AbstractGame.Params) {x : ℝ} (hx : x ∈ Sanctions.I) (n : ℕ) :
    (tsParamsOf p₀).dynamicTopLockInPathF (tsEquilibriumOf p₀).V_S (tsEquilibriumOf p₀).α x n
      = x := by
  unfold Params.dynamicTopLockInPathF
  exact Function.iterate_fixed (tsOf_step_eq p₀ hx) n

theorem ts_path_eq {x : ℝ} (hx : x ∈ Sanctions.I) (n : ℕ) :
    tsParams.dynamicTopLockInPathF tsEquilibrium.V_S tsEquilibrium.α x n = x :=
  tsOf_path_eq tsParams hx n

/-- **Rule 9 form, at every transition** (round BH-5, item BH5.1). For any
economy `p₀` there is an economy with the same transition (`p.F = p₀.F`), a
carrier class, a constructed top-selector equilibrium and pivots at which every
field of the Sender persistence package holds — so `thm:persistence` applies —
while the equilibrium closed loop fixes every state of the basin, so different
starts have different limits and no state is a common limit of the basin's
paths. Rule 22: general in `F`; no transition is excluded, the affine law
included. The failure of a common limit is therefore not an artefact of a
particular law of motion: the package never pins the transition's behaviour off
the diagonal, and the witness never uses it. -/
theorem persistence_package_not_unique_steady_state_generalF (p₀ : AbstractGame.Params) :
    ∃ (p : Params) (D : p.ValueClass2) (E : p.FeedbackStackelbergEquilibriumTop)
      (xT xS K_S : ℝ),
      p.F = p₀.F ∧
      p.SenderPersistencePackage D E xT xS K_S ∧
      (∀ x₀ ∈ Set.Icc (max xT xS) 1,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
        (∀ n, max xT xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) ∧
      (∀ x ∈ Set.Icc (max xT xS) 1, p.dynamicTopLockInStepF E.V_S E.α x = x) ∧
      ¬ ∃ z : ℝ, ∀ x₀ ∈ Set.Icc (max xT xS) 1,
          Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) atTop (𝓝 z) := by
  refine ⟨tsParamsOf p₀, tsClassOf p₀, tsEquilibriumOf p₀, 1 / 2, 1 / 2, 0, rfl, tsPackageOf p₀,
    (tsParamsOf p₀).standardCompliance_persistence_generalF_from_sender_package (tsPackageOf p₀),
    ?_, ?_⟩
  · intro x hx
    have h0 : (0 : ℝ) ≤ max (1 / 2 : ℝ) (1 / 2) := by rw [max_self]; norm_num
    exact tsOf_step_eq p₀ ⟨le_trans h0 hx.1, hx.2⟩
  · rintro ⟨z, hz⟩
    have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (max (1 / 2 : ℝ) (1 / 2)) 1 := by
      rw [max_self]; constructor <;> norm_num
    have hone : (1 : ℝ) ∈ Set.Icc (max (1 / 2 : ℝ) (1 / 2)) 1 := by
      rw [max_self]; constructor <;> norm_num
    have h1 := hz _ hhalf
    have h2 := hz _ hone
    have e1 : (tsParamsOf p₀).dynamicTopLockInPathF (tsEquilibriumOf p₀).V_S
        (tsEquilibriumOf p₀).α (1 / 2) = fun _ => (1 / 2 : ℝ) :=
      funext (tsOf_path_eq p₀ (by constructor <;> norm_num))
    have e2 : (tsParamsOf p₀).dynamicTopLockInPathF (tsEquilibriumOf p₀).V_S
        (tsEquilibriumOf p₀).α 1 = fun _ => (1 : ℝ) :=
      funext (tsOf_path_eq p₀ (by constructor <;> norm_num))
    rw [e1] at h1
    rw [e2] at h2
    have hz1 : z = 1 / 2 := tendsto_nhds_unique h1 tendsto_const_nhds
    have hz2 : z = 1 := tendsto_nhds_unique h2 tendsto_const_nhds
    linarith

/-- **Rule 9 form.** There is an economy, a carrier class, a constructed
top-selector equilibrium and pivots at which every field of the Sender
persistence package holds — so `thm:persistence` applies: every basin path stays
in the basin with sanctions at or above the pivot and nondecreasing — while the
equilibrium closed loop fixes every state of the basin, so every path converges
(it is constant) and different starts have different limits: no state is a
common limit of the basin's paths. Persistence does not imply attraction to one
steady state; it does not even exclude convergence of every path. The member of
`persistence_package_not_unique_steady_state_generalF` at `p₀ := tsParams`; that
sibling holds at every transition. -/
theorem persistence_package_not_unique_steady_state :
    ∃ (p : Params) (D : p.ValueClass2) (E : p.FeedbackStackelbergEquilibriumTop)
      (xT xS K_S : ℝ),
      p.SenderPersistencePackage D E xT xS K_S ∧
      (∀ x₀ ∈ Set.Icc (max xT xS) 1,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
        (∀ n, max xT xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) ∧
      (∀ x ∈ Set.Icc (max xT xS) 1, p.dynamicTopLockInStepF E.V_S E.α x = x) ∧
      ¬ ∃ z : ℝ, ∀ x₀ ∈ Set.Icc (max xT xS) 1,
          Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) atTop (𝓝 z) := by
  obtain ⟨p, D, E, xT, xS, K_S, -, h⟩ :=
    persistence_package_not_unique_steady_state_generalF tsParams
  exact ⟨p, D, E, xT, xS, K_S, h⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.tsEquilibrium
#print axioms Sanctions.Examples.tsPackage
#print axioms Sanctions.Examples.persistence_package_not_unique_steady_state
#print axioms Sanctions.Examples.tsPackageOf
#print axioms Sanctions.Examples.persistence_package_not_unique_steady_state_generalF

end Examples
end Sanctions
