/-
Sanctions/Examples/SenderStakeShift.lean

**Cases 00 and 10 do not read the Sender's stake** (step 2, target 2b, 2026-10-10; referee
M2(a)): the stake-shift transfer.

The *stake shift* `p.senderStateShift κ` adds `κ·x` to the Sender's stage payoff and changes
nothing else: not the static selector `σ`, not the transition `F`, not the Target's payoff, not
the discount factors. For every real `κ` — of either sign — it moves the Sender's stake in the
political state by `κ` per unit: a negative `κ` large enough turns a Sender that values the
adversary's entrenchment into one that wants it weakened.

## What is proved

* `Params.senderStateShift` (S1) and its projections; the static-selector continuity instance
  transfers.
* `senderStateShift_stageArgmaxSet`, `senderStateShift_σ_dyn_top_of_βS_zero` (S2): the stage
  argmax set is unchanged, and at `β_S = 0` so is the greatest forward-looking sanction, against
  any continuation values.
* `FeedbackStackelbergEquilibriumTop.senderStateShift` (S3): at `β_S = 0`, every top-selector
  equilibrium of `p` is an equilibrium of the shifted economy with the same Target policy, the
  same Target value, the same realised sanction rule and the same state path; the Sender's value
  is shifted by `κ·x`.
* `target_only_regime_any_stake`, `myopic_regime_any_stake` (S4): for every chord economy and
  every `κ ∈ ℝ`, the economy with Sender payoff `U_S + κ·x` has the same case-10 equilibrium (full
  defiance, the stage sanction rule `σ(x,0)`, convergence to a fixed point `z₁₀` of the stage
  rule) and the same case-00 equilibrium (relief at the myopic zero level `a⁰⁰`, zero sanctions,
  convergence to `0`). This is the Lean content of "cases 00 and 10 do not read the Sender's
  stake".

**Representability caveat.** A hostile economy `p₀` is covered when `p₀ + κ·x` is a chord
economy for some `κ`. The shifted economy is in general not itself a chord economy (its field
`hwlo : 0 < w_lo` fails for `κ` negative enough), and that is the point: the results below are
about it, not about a member of the class.

Rule 1: every policy is the original equilibrium's derived policy. Rule 3: no assumption is
introduced; `κ` is any real number. Rule 15: every equilibrium is the constructed one,
transported. Rule 22: general in `F`.
-/
import Sanctions.Examples.PlacableSenderRegime10
import Sanctions.Theory.LockIn.RegimePathBounds

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

/-! ## S1. The stake shift -/

/-- **The stake shift** (S1): the economy whose Sender stage payoff is `U_S(x,a,s) + κ·x`, with
every other primitive — the static selector `σ`, the transition `F`, the Target's payoff and
both discount factors — unchanged. Adding a function of the state alone leaves the stage
argmax in the sanction, hence `σ_isMaxOn_U_S`, intact. -/
def senderStateShift (p : Params) (κ : ℝ) : Params :=
  { p with
    U_S := fun x a s => p.U_S x a s + κ * x
    σ_isMaxOn_U_S := fun x a => by
      intro s hs
      have h := p.σ_isMaxOn_U_S x a hs
      simp only [Set.mem_setOf_eq] at h ⊢
      linarith
    U_S_continuous := p.U_S_continuous.add (continuous_const.mul continuous_fst) }

variable (p : Params) (κ : ℝ)

/-- The shifted Sender payoff.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_U_S (x a s : ℝ) :
    (p.senderStateShift κ).U_S x a s = p.U_S x a s + κ * x := rfl
/-- The Target payoff is unchanged by the stake shift.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_U_T : (p.senderStateShift κ).U_T = p.U_T := rfl
/-- The static selector is unchanged by the stake shift.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_σ : (p.senderStateShift κ).σ = p.σ := rfl
/-- The transition is unchanged by the stake shift.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_F : (p.senderStateShift κ).F = p.F := rfl
/-- The Sender's discount factor is unchanged by the stake shift.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_β_S : (p.senderStateShift κ).β_S = p.β_S := rfl
/-- The Target's discount factor is unchanged by the stake shift.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_β_T : (p.senderStateShift κ).β_T = p.β_T := rfl

/-- **The shifted economy keeps a continuous static selector**: `σ` is unchanged. -/
instance senderStateShift_staticSelectorContinuous [p.StaticSelectorContinuous] :
    (p.senderStateShift κ).StaticSelectorContinuous :=
  ⟨p.σ_continuous⟩

/-- **The shift commutes with the profile view**: reading the shifted economy at a
continuation profile is shifting the economy read at that profile. Definitional.
Scope: general class (any `Params`, any `κ`, any profile). -/
theorem withProfile_senderStateShift (c : Mechanism.ContinuationProfile) :
    (p.senderStateShift κ).withProfile c = (p.withProfile c).senderStateShift κ := rfl

/-- **The shift leaves every state path unchanged**: paths read only the transition.
Scope: general class (any `Params`, any `κ`, any rule). -/
theorem senderStateShift_rulePathF (R : ℝ → ℝ) (x₀ : ℝ) (t : ℕ) :
    (p.senderStateShift κ).rulePathF R x₀ t = p.rulePathF R x₀ t := rfl

/-! ## S2. The stage argmax, and the myopic Sender's response, are unchanged -/

/-- Adding a constant does not move a maximiser.
Scope: general class (any `Params`, any `κ`). -/
theorem isMaxOn_add_const_iff {f : ℝ → ℝ} {c s : ℝ} {K : Set ℝ} :
    IsMaxOn (fun t => f t + c) K s ↔ IsMaxOn f K s := by
  simp only [isMaxOn_iff, add_le_add_iff_right]

/-- **The stage argmax set is unchanged by the stake shift** (S2).
Scope: general class (any `Params`, any `κ`). -/
theorem senderStateShift_stageArgmaxSet (α : ℝ → ℝ) (x : ℝ) :
    (p.senderStateShift κ).stageArgmaxSet α x = p.stageArgmaxSet α x := by
  ext s
  simp only [stageArgmaxSet, Set.mem_setOf_eq, senderStateShift_U_S]
  exact and_congr_right fun _ => isMaxOn_add_const_iff

/-- **A myopic Sender's response is unchanged by the stake shift** (S2): at `β_S = 0` the
greatest forward-looking sanction of the shifted economy against any continuation value equals
that of the original economy against any other.
Scope: general class (any `Params` with `β_S = 0`, any `κ`). -/
theorem senderStateShift_σ_dyn_top_of_βS_zero (hβ : p.β_S = 0)
    (V V' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    (p.senderStateShift κ).σ_dyn_top V' x a = p.σ_dyn_top V x a := by
  rw [(p.senderStateShift κ).σ_dyn_top_eq_sSup_stageArgmax_of_βS_zero hβ,
    p.σ_dyn_top_eq_sSup_stageArgmax_of_βS_zero hβ]
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, senderStateShift_U_S]
  exact and_congr_right fun _ => isMaxOn_add_const_iff

/-- **The Target's joint objective is unchanged by the stake shift at `β_S = 0`**: the
Sender's response does not move, and the Target's payoff, discount and transition are the
originals.
Scope: general class (any `Params` with `β_S = 0`, any `κ`). -/
theorem senderStateShift_joint_T_top_integrand (hβ : p.β_S = 0)
    (V_T V V' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    (p.senderStateShift κ).joint_T_top_integrand V_T V' x a
      = p.joint_T_top_integrand V_T V x a := by
  simp only [joint_T_top_integrand, p.senderStateShift_σ_dyn_top_of_βS_zero κ hβ V V' x a]
  rfl

end Params

/-! ## S3. The equilibrium transfer at `β_S = 0` -/

namespace Params.FeedbackStackelbergEquilibriumTop

/-- **The stake-shifted equilibrium** (S3). At `β_S = 0`, a top-selector feedback Stackelberg
equilibrium `E` of `p` gives one of `p.senderStateShift κ` with the same Target policy and Target
value; the Sender's value is `E.V_S + κ·x`, the fixed point of the shifted stage problem (the
supremum of `f + κ·x` is the supremum of `f` plus `κ·x`, attained at the same sanction).
Rule 15: transported, not assumed. -/
def senderStateShift {p : Params} (hβ : p.β_S = 0) (κ : ℝ)
    (E : p.FeedbackStackelbergEquilibriumTop) :
    (p.senderStateShift κ).FeedbackStackelbergEquilibriumTop where
  V_T := E.V_T
  V_S := E.V_S + Params.linSeed κ
  α := E.α
  hα := E.hα
  α_mem := E.α_mem
  V_S_fix := by
    ext y
    have hs₀ : p.σ_dyn_top E.V_S y.val (E.α y.val) ∈ Sanctions.I :=
      p.σ_dyn_top_mem_I E.V_S y.val (E.α y.val)
    have hmax := p.σ_dyn_top_isMaxOn E.V_S y.val (E.α y.val)
    set s₀ := p.σ_dyn_top E.V_S y.val (E.α y.val) with hs₀_def
    have hgt : IsGreatest ((fun s => p.integrandS E.α (fun z => E.V_S z) (y.val, s))
        '' Sanctions.I) (p.integrandS E.α (fun z => E.V_S z) (y.val, s₀)) := by
      refine ⟨⟨s₀, hs₀, rfl⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact hmax hs
    have hV : E.V_S y = p.integrandS E.α (fun z => E.V_S z) (y.val, s₀) :=
      (congrArg (fun V => V y) E.V_S_fix).trans hgt.csSup_eq
    have hgt' : IsGreatest ((fun s => (p.senderStateShift κ).integrandS E.α
        (fun z => (E.V_S + Params.linSeed κ) z) (y.val, s)) '' Sanctions.I)
        (p.integrandS E.α (fun z => E.V_S z) (y.val, s₀) + κ * y.val) := by
      refine ⟨⟨s₀, hs₀, ?_⟩, ?_⟩
      · simp only [Params.integrandS, Params.senderStateShift_U_S,
          Params.senderStateShift_β_S, Params.senderStateShift_F, hβ, zero_mul, add_zero]
      · rintro _ ⟨s, hs, rfl⟩
        have h := hmax hs
        simp only [Set.mem_setOf_eq, hβ, zero_mul, add_zero] at h
        simp only [Params.integrandS, Params.senderStateShift_U_S,
          Params.senderStateShift_β_S, Params.senderStateShift_F, hβ, zero_mul, add_zero]
        linarith
    change (E.V_S + Params.linSeed κ) y
      = sSup ((fun s => (p.senderStateShift κ).integrandS E.α
          (fun z => (E.V_S + Params.linSeed κ) z) (y.val, s)) '' Sanctions.I)
    rw [hgt'.csSup_eq, BoundedContinuousFunction.add_apply, Params.linSeed_apply, hV]
  V_T_fix_top := by
    intro y
    have hfun : (fun a => (p.senderStateShift κ).joint_T_top_integrand E.V_T
        (E.V_S + Params.linSeed κ) y.val a)
        = fun a => p.joint_T_top_integrand E.V_T E.V_S y.val a :=
      funext fun a => p.senderStateShift_joint_T_top_integrand κ hβ _ _ _ _ _
    rw [hfun]
    exact E.V_T_fix_top y
  α_opt_top := by
    intro x hx
    have hfun : (fun a => (p.senderStateShift κ).joint_T_top_integrand E.V_T
        (E.V_S + Params.linSeed κ) x a)
        = fun a => p.joint_T_top_integrand E.V_T E.V_S x a :=
      funext fun a => p.senderStateShift_joint_T_top_integrand κ hβ _ _ _ _ _
    rw [hfun]
    exact E.α_opt_top x hx

variable {p : Params} (hβ : p.β_S = 0) (κ : ℝ) (E : p.FeedbackStackelbergEquilibriumTop)

/-- The shifted equilibrium keeps the Target policy.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_α : (E.senderStateShift hβ κ).α = E.α := rfl
/-- The shifted equilibrium keeps the Target value.
Scope: general class (any `Params`, any `κ`). -/
@[simp] theorem senderStateShift_V_T : (E.senderStateShift hβ κ).V_T = E.V_T := rfl

/-- **The shifted equilibrium realises the same sanction rule** (S3): at every state, the
myopic Sender's sanction under the shifted payoff is the original one.
Scope: general class (any `Params` with `β_S = 0`, any `κ`). -/
theorem senderStateShift_dynamicEquilibriumRule (x : ℝ) :
    (p.senderStateShift κ).dynamicEquilibriumRule (E.senderStateShift hβ κ) x
      = p.dynamicEquilibriumRule E x :=
  p.senderStateShift_σ_dyn_top_of_βS_zero κ hβ _ _ x (E.α x)

/-- **The shifted equilibrium follows the same state path** (S3), from every start.
Scope: general class (any `Params` with `β_S = 0`, any `κ`). -/
theorem senderStateShift_path (x₀ : ℝ) (t : ℕ) :
    (p.senderStateShift κ).rulePathF
        ((p.senderStateShift κ).dynamicEquilibriumRule (E.senderStateShift hβ κ)) x₀ t
      = p.rulePathF (p.dynamicEquilibriumRule E) x₀ t := by
  have h : (p.senderStateShift κ).dynamicEquilibriumRule (E.senderStateShift hβ κ)
      = p.dynamicEquilibriumRule E :=
    funext fun x => E.senderStateShift_dynamicEquilibriumRule hβ κ x
  rw [h]
  rfl

/-- **The Target's joint objective at the shifted equilibrium is the original one** (S3), so
every best-reply statement transfers.
Scope: general class (any `Params` with `β_S = 0`, any `κ`). -/
theorem senderStateShift_joint (x a : ℝ) :
    (p.senderStateShift κ).joint_T_top_integrand (E.senderStateShift hβ κ).V_T
        (E.senderStateShift hβ κ).V_S x a
      = p.joint_T_top_integrand E.V_T E.V_S x a :=
  p.senderStateShift_joint_T_top_integrand κ hβ _ _ _ x a

end Params.FeedbackStackelbergEquilibriumTop

end AbstractGame

/-! ## S4. Cases 10 and 00 at every stake -/

namespace Examples

open AbstractGame Mechanism

namespace ChordEconomy

variable (E : ChordEconomy) (κ : ℝ)

/-- **The Target-only equilibrium of the stake-shifted economy**: the case-10 equilibrium of the
chord economy `E`, transported to the economy with Sender payoff `U_S + κ·x` at the profile
`10` (S3; the profile view commutes with the shift). Rule 15: constructed. -/
def targetOnlyEquilibriumTopShift (hTM : E.LossOffset) :
    (E.toParams.senderStateShift κ).RegimeEquilibrium ContinuationProfile.p10 :=
  (E.targetOnlyEquilibriumTop hTM).senderStateShift (p := E.pT) rfl κ

/-- **Case 10 does not read the Sender's stake** (S4). For every chord economy `E`, every real
`κ` (of either sign) and the loss-offset condition, the economy with Sender payoff `U_S + κ·x`
has a Target-only equilibrium in which: (i) at every state the Target fully defies, every
maximiser of its joint objective is full defiance, and the realised sanction is the stage
selector `σ(x, 0)`; (ii) the Target's value is that of `E`'s case-10 equilibrium; (iii) from
every start the state path is `E`'s Target-only path, approaches the sanction floor from below,
and converges to a fixed point `z₁₀ = σ(z₁₀, 0)` of the stage rule.
The shifted economy need not be in the class. General in `F`.
Scope: class under any Sender stake, both signs; no approved hypothesis 1–6 is used. -/
theorem target_only_regime_any_stake (hTM : E.LossOffset) :
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyEquilibriumTopShift κ hTM).α x = 0 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => ((E.toParams.senderStateShift κ).withProfile
            ContinuationProfile.p10).joint_T_top_integrand
          (E.targetOnlyEquilibriumTopShift κ hTM).V_T
          (E.targetOnlyEquilibriumTopShift κ hTM).V_S x b) Sanctions.I a → a = 0) ∧
      ((E.toParams.senderStateShift κ).withProfile ContinuationProfile.p10).dynamicEquilibriumRule
          (E.targetOnlyEquilibriumTopShift κ hTM) x = E.σ x 0) ∧
    (E.targetOnlyEquilibriumTopShift κ hTM).V_T = (E.targetOnlyEquilibriumTop hTM).V_T ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, (E.toParams.senderStateShift κ).rulePathF
          (((E.toParams.senderStateShift κ).withProfile
            ContinuationProfile.p10).dynamicEquilibriumRule
            (E.targetOnlyEquilibriumTopShift κ hTM)) x₀ t = E.targetOnlyPath hTM x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto (E.targetOnlyPath hTM x₀) atTop (𝓝 z)) := by
  refine ⟨fun x hx => ⟨rfl, fun a ha hmax => ?_, ?_⟩, rfl, fun x₀ hx₀ => ⟨fun t => ?_,
    E.targetOnlyPath_tendsto hTM hx₀⟩⟩
  · apply E.targetOnlyEquilibriumTop_argmax_unique hTM hx ha
    intro b hb
    have h := hmax hb
    simp only [Set.mem_setOf_eq] at h ⊢
    have e1 := Params.FeedbackStackelbergEquilibriumTop.senderStateShift_joint (p := E.pT) rfl κ
      (E.targetOnlyEquilibriumTop hTM) x b
    have e2 := Params.FeedbackStackelbergEquilibriumTop.senderStateShift_joint (p := E.pT) rfl κ
      (E.targetOnlyEquilibriumTop hTM) x a
    exact e1.symm.le.trans (h.trans e2.le)
  · exact ((E.targetOnlyEquilibriumTop hTM).senderStateShift_dynamicEquilibriumRule
      (p := E.pT) rfl κ x).trans (E.targetOnlyRule_eq_stage hTM hx)
  · exact (E.targetOnlyEquilibriumTop hTM).senderStateShift_path (p := E.pT) rfl κ x₀ t

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy

variable (E : ChordEconomyRelief) (κ : ℝ)

/-- **The fully myopic equilibrium of the stake-shifted economy**: the case-00 equilibrium of the
chord economy `E` (stage-form binders), transported to the economy with Sender payoff
`U_S + κ·x` at the profile `00`. Rule 15: constructed. -/
def myopicEquilibriumTopShift (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo) :
    (E.toParams.senderStateShift κ).RegimeEquilibrium ContinuationProfile.p00 :=
  (E.myopicEquilibriumTopS hS hSR hPs).senderStateShift (p := E.pM) rfl κ

/-- **Case 00 does not read the Sender's stake** (S4). For every relief chord economy `E`, every
real `κ` (of either sign), under the stage appetite `u_hi < q`, the stage relief margin and the
stage placability `u_hi < k_lo`, the economy with Sender payoff `U_S + κ·x` has a fully myopic
equilibrium in which: (i) at every state the Target buys relief at the myopic zero level
`a⁰⁰(x)` (the myopic policy), every maximiser of its objective is that level, and the realised
sanction is zero; (ii) the Target's value is that of `E`'s case-00 equilibrium; (iii) from every
start the state path is `E`'s myopic path and converges to `0`.
The shifted economy need not be in the class. General in `F`.
Scope: class under any Sender stake, both signs; no approved hypothesis 1–6 is used. -/
theorem myopic_regime_any_stake (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hPs : E.uhi < E.klo) :
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTopShift κ hS hSR hPs).α x = E.myopicPolicy x ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => ((E.toParams.senderStateShift κ).withProfile
            ContinuationProfile.p00).joint_T_top_integrand
          (E.myopicEquilibriumTopShift κ hS hSR hPs).V_T
          (E.myopicEquilibriumTopShift κ hS hSR hPs).V_S x b) Sanctions.I a →
          a = E.myopicPolicy x) ∧
      ((E.toParams.senderStateShift κ).withProfile ContinuationProfile.p00).dynamicEquilibriumRule
          (E.myopicEquilibriumTopShift κ hS hSR hPs) x = 0) ∧
    (E.myopicEquilibriumTopShift κ hS hSR hPs).V_T = (E.myopicEquilibriumTopS hS hSR hPs).V_T ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, (E.toParams.senderStateShift κ).rulePathF
          (((E.toParams.senderStateShift κ).withProfile
            ContinuationProfile.p00).dynamicEquilibriumRule
            (E.myopicEquilibriumTopShift κ hS hSR hPs)) x₀ t = E.myopicPathS hS hSR hPs x₀ t) ∧
      Tendsto (E.myopicPathS hS hSR hPs x₀) atTop (𝓝 0)) := by
  refine ⟨fun x hx => ⟨rfl, fun a ha hmax => ?_, ?_⟩, rfl, fun x₀ hx₀ => ⟨fun t => ?_,
    E.myopicPathS_tendsto_zero hS hSR hPs hx₀⟩⟩
  · apply E.myopicEquilibriumTopS_argmax_unique hS hSR hPs hx ha
    intro b hb
    have h := hmax hb
    simp only [Set.mem_setOf_eq] at h ⊢
    have e1 := Params.FeedbackStackelbergEquilibriumTop.senderStateShift_joint (p := E.pM) rfl κ
      (E.myopicEquilibriumTopS hS hSR hPs) x b
    have e2 := Params.FeedbackStackelbergEquilibriumTop.senderStateShift_joint (p := E.pM) rfl κ
      (E.myopicEquilibriumTopS hS hSR hPs) x a
    exact e1.symm.le.trans (h.trans e2.le)
  · exact ((E.myopicEquilibriumTopS hS hSR hPs).senderStateShift_dynamicEquilibriumRule
      (p := E.pM) rfl κ x).trans (E.myopicRuleS_eq_zero hS hSR hPs hx)
  · exact (E.myopicEquilibriumTopS hS hSR hPs).senderStateShift_path (p := E.pM) rfl κ x₀ t

end ChordEconomyRelief

end Examples

end -- noncomputable section

end Sanctions
