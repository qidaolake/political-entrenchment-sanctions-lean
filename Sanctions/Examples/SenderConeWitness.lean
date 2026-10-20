/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.LockIn.PersistenceMargin
import Sanctions.Theory.LockIn.DynamicStake
-- `joint_state_chord_of_stage_chord_and_affine`.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.LockInShocked
-- The general-`F` floor and cone lemmas, and the quadratic-bump member (round BH-5).
import Sanctions.Theory.LockIn.SenderSanctionFloorGeneralF
import Sanctions.Examples.QuadBumpSenderCone

/-!
# Witnesses for the `V_S`-free sanction floor

Two concrete economies, both with exact rational data, that bracket
`AbstractGame.Params.V_S_free_sanction_floor`
(`Theory/LockIn/PersistenceMargin.lean`):

* **`wParams` — non-vacuity.**  The `V_S`-free condition fires, certifying the
  sanction floor `1` at every feasible state against the *constructed* Sender
  Bellman fixed point, while the myopic (stage) floor at the same economy is
  `0`.  So the certified floor is not a repackaged stage argmax, and the
  barrier `uniform_floor_iff_stage_floor` is defeated quantitatively
  (`w_barrier_defeated`).
* **`qParams` — separation.**  The floor `1 ≤ R 1` holds at the top state, yet
  **no** admissible pair `(m, cS)` satisfies the condition's margin
  (`q_condition_fails`), and the quantification is not vacuous because an
  admissible pair exists (`q_state_slope_witness`, `q_sanction_loss_witness`).
  So the `V_S`-free condition is *strictly stronger* than the floor it
  certifies — it is informative, not a restatement of the conclusion.
* **`wParamsOf p₀` — the non-vacuity witness over any transition** (round
  BH-5, item BH5.5, 2026-10-07).  The stage data of `wParams` over the
  transition of an arbitrary economy `p₀`.  The constructed Sender value is
  nonzero at every transition (`wOf_V_S_ne_zero`), and the floor `1`, the
  realised rule `1` and perpetual sanctions hold whenever the transition has a
  lower state chord `g_lo` and a lower sanction chord `d_lo` with
  `(1/4)(1 − g_lo/2) ≤ d_lo/2` (`wOf_floor`, `wOf_rule_eq_one`,
  `wOf_perpetual`), through the general-`F` floor
  `V_S_free_sanction_floor_generalF`.  `wParams` is the affine member
  (`g_lo = d_lo = 1/2`), and `wqbParams` is the quadratic-bump member
  (`g_lo = 12/25`, `d_lo = 47/100`): the first non-affine member at which the
  Sender's continuation channel is active, lifting the sanction from the stage
  optimum `0` to `1` (`wqb_nonaffine_continuation_active`).

## THE WITNESSES ARE NOT GAMES — read this before citing them

At **both** economies the Sender's stage payoff is independent of the Target's
action: `wU_S x a s = x − s/4` and `qU_S x a s = −(s − qIdeal x)²` do not
mention `a`, and the transition `F(x,s) = (1−δ)x + δs` never did.  Therefore
the Target's action moves **no** Sender payoff, **no** Sender best response and
**no** transition; it enters only the Target's own stage payoff.

`w_not_a_game` and `q_not_a_game` prove exactly this, by `rfl`: the Sender's
dynamic argmax set, its greatest selector `σ_dyn_top`, and the realised rule
`dynamicTopRealizedRule` are literally the same objects at every Target action
and at every Target policy.  The same holds at every member of `wParamsOf p₀`,
whatever its transition (`wOf_not_a_game`): no transition depends on the
Target's action.

Rule 1 is technically satisfied — the Target policy `α ≡ 0` is derived as the
unique argmax of `U_T x a s = −a²` against every continuation value
(`wAlpha_isMaxOn`, `wAlpha_unique`, `qAlpha_isMaxOn`) — but the object being
certified is a **single-agent dynamic program**, not a game.  The honest
statement of what these witnesses establish is:

> the `V_S`-free floor condition is satisfiable, and **no non-degenerate
> economy satisfying it has been exhibited.**

**Whether that degeneracy is forced is open, and an earlier draft of this
docstring wrongly said it was settled.**  The claim was that
`no_top_gain_equilibrium_of_V_S_free_floor_condition`
(`Theory/LockIn/PersistenceMargin.lean`) explains it.  It does not, for two
reasons: that theorem needs an off-policy sanction-loss bound the floor condition
does not supply, and its top-gain hypothesis is *unsatisfiable at both economies
below*, so it is vacuous exactly where it was being invoked as an explanation.

The honest position: these two economies have a payoff-irrelevant Target because
that is how they were built, and nothing here shows a non-degenerate one is
impossible.  Finding one, or proving none exists, is the open question.

## Rule compliance

* **Rule 1** — the Target policy is an argmax, and the certified sanction is
  `dynamicTopRealizedRule`, the greatest maximiser of the Sender's
  forward-looking objective.  Both are optimisation outputs; neither is
  posited.  See the caveat above for why that is not sufficient to call these
  witnesses games.
* **Rule 5** — all content is a specialisation of the parametric theorems in
  `Theory/LockIn/PersistenceMargin.lean` and
  `Theory/Bellman/SenderLowerSlopeCone.lean`; nothing is re-proved by hand.
* **Rule 19** — witness economies, hence `Examples/`.
* Exact rationals throughout; no `native_decide`.
-/

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace Examples

/-! # PART A — witness economy: the condition holds and the myopic floor is `0` -/

namespace ConeWitness

open Sanctions.AbstractGame Sanctions.AbstractGame.Params

/-- Sender stage payoff: a unit political-state stake and a quarter-rate own
sanction cost.  `U_S(x,a,s) = x − s/4` — the Sender strictly *dislikes*
sanctioning, period by period, and its payoff does not mention the Target's
action `a`. -/
def wU_S (x _a s : ℝ) : ℝ := x - s / 4

/-- Target stage payoff `U_T(x,a,s) = −a²`: full defiance `a = 0` is the unique
Target optimum, at every state, against every continuation value. -/
def wU_T (_x a _s : ℝ) : ℝ := -(a ^ 2)

/-- Static Sender stage argmax: with `U_S` strictly decreasing in `s`, it is `0`. -/
def wSigma (_x _a : ℝ) : ℝ := 0

theorem wSigma_mem (x a : ℝ) : wSigma x a ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_refl 0, zero_le_one⟩

theorem wSigma_continuous :
    Continuous (fun xa : ℝ × ℝ => wSigma xa.1 xa.2) := continuous_const

theorem wSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => wU_S x a s) (Set.Icc (0:ℝ) 1) (wSigma x a) := by
  intro s hs
  simp only [Set.mem_setOf_eq, wU_S, wSigma]
  linarith [hs.1]

theorem wU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => wU_S xas.1 xas.2.1 xas.2.2) := by
  unfold wU_S; fun_prop

theorem wU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => wU_T xas.1 xas.2.1 xas.2.2) := by
  unfold wU_T; fun_prop

/-- The witness economy: `δ = β_T = β_S = 1/2`, affine transition. -/
def wParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := by constructor <;> norm_num
  β_T := 1/2
  β_T_mem := by constructor <;> norm_num
  β_S := 1/2
  β_S_mem := by constructor <;> norm_num
  U_T := wU_T
  U_S := wU_S
  σ := wSigma
  σ_mem := wSigma_mem
  σ_isMaxOn_U_S := wSigma_isMaxOn
  U_T_continuous := wU_T_continuous
  U_S_continuous := wU_S_continuous
  F := AbstractGame.affineF (1/2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`wParams` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance wParams_staticSelectorContinuous :
    wParams.StaticSelectorContinuous where
  σ_continuous := wSigma_continuous

@[simp] theorem wParams_U_S : wParams.U_S = wU_S := rfl
@[simp] theorem wParams_U_T : wParams.U_T = wU_T := rfl
@[simp] theorem wParams_β_S : wParams.β_S = 1/2 := rfl
@[simp] theorem wParams_β_T : wParams.β_T = 1/2 := rfl
@[simp] theorem wParams_δ : wParams.δ = 1/2 := rfl

theorem wParams_F_affine : wParams.F = AbstractGame.affineF wParams.δ := rfl

/-- The Target policy: full defiance. -/
def wAlpha : ℝ → ℝ := fun _ => 0

theorem wAlpha_continuous : Continuous wAlpha := continuous_const

/-! ## The degeneracy, stated as a theorem -/

/-- **THIS WITNESS IS NOT A GAME.**  Four claims, all by `rfl`:

1. the Sender's stage payoff is the same real number at every Target action;
2. hence the Sender's dynamic argmax set at a state is the same *set* at every
   Target action, against every continuation value;
3. hence its greatest selector `σ_dyn_top` is the same real number; and
4. hence the realised rule `dynamicTopRealizedRule` is the same function at
   every Target *policy*.

Since the transition `F(x,s)` depends only on the state and the sanction, the
Target's action therefore moves no Sender payoff, no Sender best response and
no transition — it enters only `U_T`.  The certified object is a single-agent
dynamic program plus a decoupled static Target choice.

This is the witness's economic limitation, recorded as a theorem so that it
cannot be lost from a docstring — the discipline of
`Examples/DeterministicStrictEscalation.ni_continuation_channel_inactive`.  It
does not weaken `w_floor` or `w_barrier_defeated`, whose statements and proofs
are unaffected; it fixes what they may be read as showing.  The condition is
**satisfiable**; no *non-degenerate* economy satisfying it has been exhibited,
and by `no_top_gain_equilibrium_of_V_S_free_floor_condition` no economy with a
top-state-gaining Target ever will be. -/
theorem w_not_a_game :
    (∀ x a a' s : ℝ, wParams.U_S x a s = wParams.U_S x a' s)
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ),
        wParams.dynamicArgmaxSet V x a = wParams.dynamicArgmaxSet V x a')
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ),
        wParams.σ_dyn_top V x a = wParams.σ_dyn_top V x a')
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α α' : ℝ → ℝ) (x : ℝ),
        wParams.dynamicTopRealizedRule V α x
          = wParams.dynamicTopRealizedRule V α' x) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

/-- The second conjunct of `w_not_a_game`, isolated for use as a rewrite. -/
theorem w_argmax_indep (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ) :
    wParams.dynamicArgmaxSet V x a = wParams.dynamicArgmaxSet V x a' := rfl

/-! ## Rule 1 — the Target policy is an argmax, not a posit -/

/-- **Rule 1: full defiance is the Target's optimum** — at every state, against
every continuation value and every realised sanction. -/
theorem wAlpha_isMaxOn (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x s : ℝ) :
    IsMaxOn (fun a => wParams.U_T x a s
        + wParams.β_T * V_T (Sanctions.clipS' (wParams.F x s)))
      Sanctions.I (wAlpha x) := by
  intro a _
  simp only [Set.mem_setOf_eq, wParams_U_T, wU_T, wAlpha]
  nlinarith [sq_nonneg a]

/-- and it is the **unique** optimum. -/
theorem wAlpha_unique (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x s a : ℝ)
    (hne : a ≠ 0) :
    wParams.U_T x a s + wParams.β_T * V_T (Sanctions.clipS' (wParams.F x s))
      < wParams.U_T x (wAlpha x) s
        + wParams.β_T * V_T (Sanctions.clipS' (wParams.F x s)) := by
  simp only [wParams_U_T, wU_T, wAlpha]
  have : 0 < a ^ 2 := by positivity
  linarith

/-! ## The `V_S`-free hypotheses, discharged with exact rationals -/

/-- The Sender's stage payoff has state chord exactly `1`: the coalition's
political stake in the Target's entrenchment. -/
theorem w_state_slope :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (1:ℝ) * (y₂ - y₁)
        ≤ wParams.U_S y₂ (wAlpha y₂) s - wParams.U_S y₁ (wAlpha y₁) s := by
  intro s _ y₁ _ y₂ _ _
  simp only [wParams_U_S, wU_S]
  linarith

/-- The Sender's stage payoff falls in its own sanction at rate exactly `1/4`. -/
theorem w_sanction_loss (x : ℝ) :
    LowerLossSlopeOn (fun s => wParams.U_S x (wAlpha x) s)
      (Set.Icc (0:ℝ) 1) (1/4) := by
  intro s₁ _ s₂ _ _
  simp only [wParams_U_S, wU_S]
  linarith

/-- The margin: `cS·(1 − β_S(1−δ)) = 3/16 ≤ 1/4 = β_S·m·δ`. -/
theorem w_margin :
    (1/4 : ℝ) * (1 - wParams.β_S * (1 - wParams.δ))
      ≤ wParams.β_S * 1 * wParams.δ := by
  simp only [wParams_β_S, wParams_δ]
  norm_num

/-! ## The general-`F` cone preserver, discharged here through the drift fence -/

/-- **The joint state chord at `wParams`, at the Benveniste–Scheinkman constant
`g = 4/3`.**  Not proved by hand: it is the output of the Rule-13 drift fence
`joint_state_chord_of_stage_chord_and_affine`, which converts the affine trio --
the affine law, the stage state chord `m = 1` (`w_state_slope`: the coalition's
unit political stake in the Target's entrenchment), and the sub-solution
inequality `g ≤ m + β_S·g·(1−δ)` -- into the single joint chord the general-`F`
theorem consumes.

`4/3 = 1/(1 − β_S(1−δ))` at `β_S = δ = 1/2` is exactly
`bellmanLowerSlopeConstant β_S (1−δ) 1`, so the sub-solution inequality holds with
equality here; that is the closed form doing its job, not a numerical accident. -/
theorem w_joint_state_chord :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (4/3 : ℝ) * (y₂ - y₁)
        ≤ (wParams.U_S y₂ (wAlpha y₂) s - wParams.U_S y₁ (wAlpha y₁) s)
          + wParams.β_S * (4/3) * (wParams.F y₂ s - wParams.F y₁ s) :=
  wParams.joint_state_chord_of_stage_chord_and_affine wParams_F_affine
    w_state_slope (by norm_num [wParams_β_S, wParams_δ])

/-- **The general-`F` Sender cone preserver, instantiated at `wParams`.**  The
affine economy satisfies the general hypothesis, so the general theorem covers the
ground the affine twin covered -- the converse direction of the drift fence,
exhibited rather than asserted.

Read against `w_not_a_game`: this economy's Sender payoff ignores the Target's
action, so the instance is at a single-agent dynamic program.  The non-degenerate,
non-affine instance is `qbParams_bellmanS_preserves_cone`
(`Examples/QuadBumpSenderCone.lean`). -/
theorem w_bellmanS_preserves_cone
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) (4/3)) :
    LowerSlopeOnValueOn (wParams.bellmanS_BCF wAlpha wAlpha_continuous V)
      (Set.Icc (0:ℝ) 1) (4/3) :=
  wParams.bellmanS_BCF_preserves_lowerSlopeCone_generalF wAlpha_continuous
    w_joint_state_chord hV

/-! ## Non-vacuity: the `V_S`-free condition certifies the ceiling -/

/-- **NON-VACUITY.**  The `V_S`-free sufficient condition fires at `wParams`,
certifying the sanction floor `1` at every state, against the *constructed*
Sender Bellman fixed point.

Read together with `w_not_a_game`: satisfiability is established, at a
degenerate (single-agent) economy. -/
theorem w_floor (x : ℝ) (hx : x ∈ Sanctions.I) :
    (1:ℝ) ≤ wParams.dynamicTopRealizedRule
      (wParams.V_S wAlpha wAlpha_continuous) wAlpha x :=
  wParams.V_S_free_sanction_floor wAlpha_continuous wParams_F_affine
    hx ⟨zero_le_one, le_refl 1⟩ w_state_slope (w_sanction_loss x) w_margin

/-- and so the realised equilibrium sanction is exactly `1` at every state. -/
theorem w_rule_eq_one (x : ℝ) (hx : x ∈ Sanctions.I) :
    wParams.dynamicTopRealizedRule
      (wParams.V_S wAlpha wAlpha_continuous) wAlpha x = 1 :=
  le_antisymm (wParams.dynamicTopRealizedRule_mem _ _ x).2 (w_floor x hx)

/-! ## The barrier is defeated, quantitatively -/

/-- At `wParams` the **stage** argmax set is `{0}`: the myopic Sender never
sanctions. -/
theorem w_stage_argmax_set (x a : ℝ) :
    {s | s ∈ Sanctions.I ∧
      IsMaxOn (fun s' => wParams.U_S x a s') Sanctions.I s} = {0} := by
  ext s
  constructor
  · rintro ⟨hsI, hmax⟩
    have h := hmax (show (0:ℝ) ∈ Sanctions.I from ⟨le_refl 0, zero_le_one⟩)
    simp only [Set.mem_setOf_eq, wParams_U_S, wU_S] at h
    have hs0 : s ≤ 0 := by linarith
    simp only [Set.mem_singleton_iff]
    linarith [hsI.1]
  · rintro rfl
    refine ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩
    intro s' hs'
    simp only [Set.mem_setOf_eq, wParams_U_S, wU_S]
    linarith [hs'.1]

/-- so the myopic (monotone-carrier-uniform) floor at `wParams` is `0`. -/
theorem w_stage_floor_zero (x a : ℝ) :
    sSup {s | s ∈ Sanctions.I ∧
      IsMaxOn (fun s' => wParams.U_S x a s') Sanctions.I s} = 0 := by
  rw [w_stage_argmax_set]
  exact csSup_singleton 0

/-- **THE BARRIER IS DEFEATED.**  `uniform_floor_iff_stage_floor` says a floor
demanded uniformly over the *monotone* continuation carrier is exactly a floor
on the greatest *stage* maximiser, which at `wParams` is `0`.  The `V_S`-free
route never quantifies over that carrier: it pins the one continuation value
the economy actually has — the constructed Banach fixed point — and certifies
the floor `1` against it.  The gap between the two floors is the whole
interval. -/
theorem w_barrier_defeated (x : ℝ) (hx : x ∈ Sanctions.I) :
    (1:ℝ) ≤ wParams.dynamicTopRealizedRule
        (wParams.V_S wAlpha wAlpha_continuous) wAlpha x
    ∧ ¬ (∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, Monotone V →
          (1:ℝ) ≤ wParams.dynamicTopRealizedRule V wAlpha x) := by
  refine ⟨w_floor x hx, ?_⟩
  intro h
  have hstage := (wParams.uniform_floor_iff_stage_floor wAlpha x 1).mp h
  rw [w_stage_floor_zero x (wAlpha x)] at hstage
  linarith

/-- The constructed equilibrium value is **not** the zero function: the
lower-slope cone restriction has real content, and the zero-continuation
witness that drives the barrier is unavailable here. -/
theorem w_V_S_ne_zero : wParams.V_S wAlpha wAlpha_continuous ≠ 0 :=
  wParams.V_S_ne_zero_of_pos_state_slope wAlpha_continuous wParams_F_affine
    one_pos w_state_slope

/-- **Perpetual sanctions from the `V_S`-free condition.**  Along the realised
equilibrium path from any feasible start, the state stays feasible, the
sanction is at least `1` at every date, and is therefore strictly positive
forever — even though the Sender's stage payoff strictly falls in the sanction
every period. -/
theorem w_perpetual {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) :
    (∀ n, wParams.dynamicTopLockInPathF
        (wParams.V_S wAlpha wAlpha_continuous) wAlpha x₀ n ∈ Set.Icc (0:ℝ) 1)
    ∧ (∀ n, (1:ℝ) ≤ wParams.dynamicTopLockInSanctionsF
        (wParams.V_S wAlpha wAlpha_continuous) wAlpha x₀ n)
    ∧ (∀ n, 0 < wParams.dynamicTopLockInSanctionsF
        (wParams.V_S wAlpha wAlpha_continuous) wAlpha x₀ n) := by
  refine wParams.perpetual_sanctions_of_margin
    (wParams.V_S wAlpha wAlpha_continuous) wAlpha one_pos ?_ ?_ hx₀
  · show (0:ℝ) ≤ AbstractGame.affineF (1/2) 0 1
    unfold AbstractGame.affineF
    norm_num
  · intro x hx
    exact wParams.margin_of_realizedRule_ge (wParams.V_S wAlpha wAlpha_continuous)
      wAlpha (w_floor x ⟨hx.1, hx.2⟩)

/-! ## DYNAMIC-STAKE at `wParams` — hypothesis satisfiable, at a DEGENERATE economy

⚠ **Read every row below against `w_not_a_game`.** `wParams` is proved in this
file to be a degenerate, effectively single-agent economy: its Sender stage
payoff `wU_S x a s = x − s/4` does **not** depend on the Target's action `a` at
all, so the Sender's dynamic argmax set, its greatest selector, and its realised
rule are all literally independent of the Target policy. Nothing here is
evidence that DYNAMIC-STAKE's hypothesis is satisfiable in a genuine two-player
economy. For the hypothesis at a *constructed equilibrium of a real game*, see
`Examples.ce_is_a_genuine_dynamic_floor` at `ceParams`.

Also note that at `wParams` the composed chord and the raw partial `∂U_S/∂x`
coincide (again because `U_S` ignores `a`), so this witness does **not** exercise
the composed-versus-raw distinction that `Sanctions.raw_chord_ne_composed_chord`
fences. -/

/-- The general `stageTopRule` agrees, **by application and not by eye**, with
this file's own stage floor computation `w_stage_floor_zero`: the greatest stage
maximiser at `wParams` is `0`, at every state. -/
theorem w_stageTopRule_zero (x : ℝ) :
    wParams.stageTopRule wAlpha x = 0 :=
  w_stage_floor_zero x (wAlpha x)

/-- **DYNAMIC-STAKE's hypothesis is satisfiable — at a degenerate economy.** At
`wParams` the greatest stage maximiser is `0` (`w_stageTopRule_zero`) while the
greatest forward-looking maximiser against the *constructed* Sender value is `1`
(`w_rule_eq_one`). So the hypothesis is not vacuous.

Degeneracy caveat: by `w_not_a_game` this economy is not a game — the Sender's
payoff ignores the Target's action — so satisfiability is established here only
in that degenerate class. -/
theorem w_dynamic_stake_hypothesis (x : ℝ) (hx : x ∈ Sanctions.I) :
    wParams.stageTopRule wAlpha x
      < wParams.dynamicTopRealizedRule
          (wParams.V_S wAlpha wAlpha_continuous) wAlpha x := by
  rw [w_stageTopRule_zero, w_rule_eq_one x hx]
  norm_num

/-- and DYNAMIC-STAKE then delivers its existential conclusion at `wParams`: the
Sender's composed stage payoff rises strictly somewhere in the state space.

`w_barrier_defeated` should not be described as a DYNAMIC-STAKE instance: it
concludes a sanction floor together with the failure of the uniform monotone-carrier
floor, which is an instance of DYNAMIC-STAKE's *hypothesis* (stage ceiling `0`
strictly below the realised rule `1`), not of its conclusion.  It says nothing
about the composed state payoff rising.

Note also the caveat of `w_not_a_game`: at this economy `U_S` ignores the
Target's action, so the composed chord and the raw partial coincide and this
instance does not exercise the composed-versus-raw distinction at all. -/
theorem w_dynamic_stake_conclusion (x : ℝ) (hx : x ∈ Sanctions.I) :
    ∃ s ∈ Sanctions.I, ∃ y₁ ∈ Sanctions.S, ∃ y₂ ∈ Sanctions.S,
      y₁ ≤ y₂ ∧ wParams.U_S y₁ (wAlpha y₁) s < wParams.U_S y₂ (wAlpha y₂) s :=
  wParams.dynamic_stake wAlpha_continuous x (w_dynamic_stake_hypothesis x hx)

/-! ## The witness over any transition (round BH-5, item BH5.5, 2026-10-07)

`wParams` fixes the affine law at rate `1/2`, but nothing in the witness needs
it.  `wParamsOf p₀` keeps the stage data and takes the transition and its four
structural fields from an arbitrary economy `p₀`.  The general-`F` floor
`V_S_free_sanction_floor_generalF` (`Theory/LockIn/SenderSanctionFloorGeneralF.lean`)
then certifies the floor `1` from two chord rates of that transition, a lower
state chord `g_lo` and a lower sanction chord `d_lo`, under the margin
`(1/4)(1 − g_lo/2) ≤ d_lo/2`, which is the affine margin `w_margin` with
`1 − δ` and `δ` replaced by the two rates.  The constructed Sender value is
nonzero at every transition, with no chord at all: monotonicity of `F` in the
state gives the lower state chord `0`, and the unit stage stake alone keeps the
value out of the zero function.

Read every row against `wOf_not_a_game`: the Sender payoff ignores the Target's
action at every member, so each member is a single-agent dynamic program in
the sense of `w_not_a_game`, whatever the transition. -/

/-- **The witness economy over any transition.**  The stage payoffs, the stage
selector, the discounts and the inert rate `δ` of `wParams`, with the transition
`F` and its four structural fields taken from an arbitrary economy `p₀`.
Rule 22: general in `F`; nothing is assumed about `p₀.F` beyond the `Params`
fields it already carries. -/
def wParamsOf (p₀ : AbstractGame.Params) : AbstractGame.Params where
  δ := 1/2
  δ_mem := by constructor <;> norm_num
  β_T := 1/2
  β_T_mem := by constructor <;> norm_num
  β_S := 1/2
  β_S_mem := by constructor <;> norm_num
  U_T := wU_T
  U_S := wU_S
  σ := wSigma
  σ_mem := wSigma_mem
  σ_isMaxOn_U_S := wSigma_isMaxOn
  U_T_continuous := wU_T_continuous
  U_S_continuous := wU_S_continuous
  F := p₀.F
  F_continuous := p₀.F_continuous
  F_mono_x := p₀.F_mono_x
  F_mono_s := p₀.F_mono_s
  F_diag := p₀.F_diag

/-- **`wParamsOf` has a continuous static Sender selector.** General in `F`: the
transition is `p₀`'s, and the selector does not read it. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance wParamsOf_staticSelectorContinuous (p₀ : AbstractGame.Params) :
    (wParamsOf p₀).StaticSelectorContinuous where
  σ_continuous := wSigma_continuous

@[simp] theorem wParamsOf_U_S (p₀ : AbstractGame.Params) : (wParamsOf p₀).U_S = wU_S := rfl
@[simp] theorem wParamsOf_β_S (p₀ : AbstractGame.Params) : (wParamsOf p₀).β_S = 1/2 := rfl
@[simp] theorem wParamsOf_F (p₀ : AbstractGame.Params) : (wParamsOf p₀).F = p₀.F := rfl

/-- The affine witness is the family member at its own transition, by
definition. -/
theorem wParamsOf_self : wParamsOf wParams = wParams := rfl

/-- **Every member is a single-agent program** (the four `rfl` claims of
`w_not_a_game`, at every transition).  General in `F`. -/
theorem wOf_not_a_game (p₀ : AbstractGame.Params) :
    (∀ x a a' s : ℝ, (wParamsOf p₀).U_S x a s = (wParamsOf p₀).U_S x a' s)
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ),
        (wParamsOf p₀).dynamicArgmaxSet V x a = (wParamsOf p₀).dynamicArgmaxSet V x a')
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ),
        (wParamsOf p₀).σ_dyn_top V x a = (wParamsOf p₀).σ_dyn_top V x a')
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α α' : ℝ → ℝ) (x : ℝ),
        (wParamsOf p₀).dynamicTopRealizedRule V α x
          = (wParamsOf p₀).dynamicTopRealizedRule V α' x) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

/-- The Sender's stage payoff has state chord exactly `1` at every member.
General in `F` (the stage payoff does not read the transition). -/
theorem wOf_state_slope (p₀ : AbstractGame.Params) :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (1 : ℝ) * (y₂ - y₁)
        ≤ (wParamsOf p₀).U_S y₂ (wAlpha y₂) s - (wParamsOf p₀).U_S y₁ (wAlpha y₁) s := by
  intro s _ y₁ _ y₂ _ _
  simp only [wParamsOf_U_S, wU_S]
  linarith

/-- The Sender's stage payoff falls in its own sanction at rate exactly `1/4` at
every member.  General in `F`. -/
theorem wOf_sanction_loss (p₀ : AbstractGame.Params) (x : ℝ) :
    LowerLossSlopeOn (fun s => (wParamsOf p₀).U_S x (wAlpha x) s)
      (Set.Icc (0 : ℝ) 1) (1 / 4) := by
  intro s₁ _ s₂ _ _
  simp only [wParamsOf_U_S, wU_S]
  linarith

/-- **The constructed Sender value is nonzero at every transition.**  The unit
stage stake (`wOf_state_slope`) and the lower state chord `0`, which monotonicity
of `F` in the state supplies at every member, place the value in the cone of
slope `1/(1 − β_S·0) = 1`, which excludes the zero function
(`V_S_mem_lowerSlopeCone_of_lower_state_chord`, `zero_not_mem_lowerSlopeCone`).
General in `F`: no chord hypothesis; the affine-only `V_S_ne_zero_of_pos_state_slope`
behind `w_V_S_ne_zero` needed `F = affineF δ`. -/
theorem wOf_V_S_ne_zero (p₀ : AbstractGame.Params) :
    (wParamsOf p₀).V_S wAlpha wAlpha_continuous ≠ 0 := by
  intro hzero
  have hchord0 : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (0 : ℝ) * (y₂ - y₁) ≤ (wParamsOf p₀).F y₂ s - (wParamsOf p₀).F y₁ s := by
    intro s _ y₁ _ y₂ _ hle
    have h : p₀.F y₁ s ≤ p₀.F y₂ s := p₀.F_mono_x s hle
    rw [zero_mul]
    exact sub_nonneg.mpr h
  have hcone := (wParamsOf p₀).V_S_mem_lowerSlopeCone_of_lower_state_chord
    wAlpha_continuous zero_le_one (wOf_state_slope p₀) hchord0
  rw [hzero] at hcone
  refine zero_not_mem_lowerSlopeCone ?_ hcone
  rw [Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
  norm_num

/-- **The floor `1` at every member with a margin-clearing pair of chords.**  If
the transition of `p₀` has a lower state chord `g_lo` (raising the inherited
state by `Δ` raises next period's state by at least `g_lo·Δ`, at every
sanction), a lower sanction chord `d_lo`, and `(1/4)(1 − g_lo/2) ≤ d_lo/2`,
then the greatest forward-looking Sender response against the constructed
Sender value is `≥ 1` at every feasible state.  The general-`F` floor
`V_S_free_sanction_floor_generalF` at `m = 1`, `cS = 1/4`, `β_S = 1/2`, `c = 1`.
Rule 22: general in `F`; the affine law (`w_floor`) is the member
`g_lo = d_lo = 1/2`. -/
theorem wOf_floor (p₀ : AbstractGame.Params) {g_lo d_lo : ℝ}
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p₀.F y₂ s - p₀.F y₁ s)
    (h_sanction_chord : Sanctions.TransitionChords.SanctionLowerChord p₀.F d_lo)
    (h_margin : 1 / 4 * (1 - g_lo / 2) ≤ d_lo / 2)
    (x : ℝ) (hx : x ∈ Sanctions.I) :
    (1 : ℝ) ≤ (wParamsOf p₀).dynamicTopRealizedRule
      ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha x :=
  (wParamsOf p₀).V_S_free_sanction_floor_generalF wAlpha_continuous hx
    ⟨zero_le_one, le_refl 1⟩ zero_le_one (wOf_state_slope p₀) h_state_chord
    h_sanction_chord (wOf_sanction_loss p₀ x)
    (by simp only [wParamsOf_β_S]; linarith)

/-- and so the realised equilibrium sanction is exactly `1` at every feasible
state.  General in `F`, under the hypotheses of `wOf_floor`. -/
theorem wOf_rule_eq_one (p₀ : AbstractGame.Params) {g_lo d_lo : ℝ}
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p₀.F y₂ s - p₀.F y₁ s)
    (h_sanction_chord : Sanctions.TransitionChords.SanctionLowerChord p₀.F d_lo)
    (h_margin : 1 / 4 * (1 - g_lo / 2) ≤ d_lo / 2)
    (x : ℝ) (hx : x ∈ Sanctions.I) :
    (wParamsOf p₀).dynamicTopRealizedRule
      ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha x = 1 :=
  le_antisymm ((wParamsOf p₀).dynamicTopRealizedRule_mem _ _ x).2
    (wOf_floor p₀ h_state_chord h_sanction_chord h_margin x hx)

/-- **Perpetual sanctions at every member with a margin-clearing pair of
chords.**  Along the realised equilibrium path from any feasible start, the
state stays feasible and the sanction is at least `1`, hence strictly positive,
at every date, although the Sender's stage payoff falls in the sanction every
period.  General in `F`, under the hypotheses of `wOf_floor`; the corner input
`0 ≤ F(0, 1)` is feasibility of the transition (`F_mem`). -/
theorem wOf_perpetual (p₀ : AbstractGame.Params) {g_lo d_lo : ℝ}
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p₀.F y₂ s - p₀.F y₁ s)
    (h_sanction_chord : Sanctions.TransitionChords.SanctionLowerChord p₀.F d_lo)
    (h_margin : 1 / 4 * (1 - g_lo / 2) ≤ d_lo / 2)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, (wParamsOf p₀).dynamicTopLockInPathF
        ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha x₀ n ∈ Set.Icc (0 : ℝ) 1)
    ∧ (∀ n, (1 : ℝ) ≤ (wParamsOf p₀).dynamicTopLockInSanctionsF
        ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha x₀ n)
    ∧ (∀ n, 0 < (wParamsOf p₀).dynamicTopLockInSanctionsF
        ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha x₀ n) := by
  refine (wParamsOf p₀).perpetual_sanctions_of_margin
    ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha one_pos ?_ ?_ hx₀
  · exact ((wParamsOf p₀).F_mem 0 1 ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩).1
  · intro x hx
    exact (wParamsOf p₀).margin_of_realizedRule_ge
      ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha
      (wOf_floor p₀ h_state_chord h_sanction_chord h_margin x ⟨hx.1, hx.2⟩)

/-- The greatest stage maximiser is `0` at every member: the stage payoff, and
hence the stage argmax set `{0}`, does not read the transition.  General in
`F`. -/
theorem wOf_stageTopRule_zero (p₀ : AbstractGame.Params) (x : ℝ) :
    (wParamsOf p₀).stageTopRule wAlpha x = 0 :=
  w_stage_floor_zero x (wAlpha x)

/-- **The continuation channel is active at every member with a
margin-clearing pair of chords**: the greatest stage maximiser is `0`, the
realised forward-looking sanction is `1`.  The whole gap is the Sender's
continuation value of moving next period's state.  General in `F`, under the
hypotheses of `wOf_floor`. -/
theorem wOf_continuation_active (p₀ : AbstractGame.Params) {g_lo d_lo : ℝ}
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p₀.F y₂ s - p₀.F y₁ s)
    (h_sanction_chord : Sanctions.TransitionChords.SanctionLowerChord p₀.F d_lo)
    (h_margin : 1 / 4 * (1 - g_lo / 2) ≤ d_lo / 2)
    (x : ℝ) (hx : x ∈ Sanctions.I) :
    (wParamsOf p₀).stageTopRule wAlpha x
      < (wParamsOf p₀).dynamicTopRealizedRule
          ((wParamsOf p₀).V_S wAlpha wAlpha_continuous) wAlpha x := by
  rw [wOf_stageTopRule_zero, wOf_rule_eq_one p₀ h_state_chord h_sanction_chord h_margin x hx]
  norm_num

/-! ### The quadratic-bump member -/

/-- **The witness economy over the quadratic-bump transition**
`F(x,s) = x/2 + s/2 + (1/100)(s − x)²(1 − s)` (`quadBumpF`), the member
`p₀ := qbParams` of `wParamsOf`. -/
def wqbParams : AbstractGame.Params := wParamsOf qbParams

/-- The member's transition is `quadBumpF`. -/
theorem wqbParams_F : wqbParams.F = quadBumpF := rfl

/-- The member's transition is the affine law at no rate
(`quadBumpF_ne_affineF`). -/
theorem wqbParams_F_ne_affineF (δ : ℝ) : wqbParams.F ≠ AbstractGame.affineF δ :=
  quadBumpF_ne_affineF δ

/-- Lower state chord `12/25` of the quadratic-bump transition
(`quadBumpF_state_lowerChord`), in the form `wOf_floor` reads. -/
theorem wqb_state_chord :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      12 / 25 * (y₂ - y₁) ≤ qbParams.F y₂ s - qbParams.F y₁ s :=
  fun _ hs _ hy₁ _ hy₂ hle => quadBumpF_state_lowerChord hy₁ hy₂ hs hle

/-- The margin at the quadratic-bump rates: `(1/4)(1 − (12/25)/2) = 19/100 ≤
47/200 = (47/100)/2`. -/
theorem wqb_margin : 1 / 4 * (1 - (12 / 25 : ℝ) / 2) ≤ (47 / 100 : ℝ) / 2 := by
  norm_num

/-- **The first non-affine member with an active continuation channel.**  At
`wqbParams`, whose transition is the affine law at no rate: the constructed
Sender value is nonzero; at every feasible state the greatest stage maximiser
is `0` while the realised forward-looking sanction is `1`, so the continuation
value is what moves the Sender to full sanction; and from every feasible start
the sanction stays at `1 > 0` forever.  The chord rates are `g_lo = 12/25`
(`wqb_state_chord`) and `d_lo = 47/100` (`qbCert_hchord_lo`).

The non-affine instance of the named-chord floor at `qbParams`
(`Examples/QuadBumpSenderFloor.lean`) has the continuation channel inactive;
here it is active.  Degeneracy caveat (`wOf_not_a_game`): the Sender payoff
ignores the Target's action at this member too, so the active channel is the
Sender's own dynamic program, not a strategic interaction. -/
theorem wqb_nonaffine_continuation_active :
    (∀ δ : ℝ, wqbParams.F ≠ AbstractGame.affineF δ)
    ∧ wqbParams.V_S wAlpha wAlpha_continuous ≠ 0
    ∧ (∀ x ∈ Sanctions.I,
        wqbParams.stageTopRule wAlpha x = 0
        ∧ wqbParams.dynamicTopRealizedRule
            (wqbParams.V_S wAlpha wAlpha_continuous) wAlpha x = 1)
    ∧ (∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
        (∀ n, wqbParams.dynamicTopLockInPathF
            (wqbParams.V_S wAlpha wAlpha_continuous) wAlpha x₀ n ∈ Set.Icc (0 : ℝ) 1)
        ∧ (∀ n, (1 : ℝ) ≤ wqbParams.dynamicTopLockInSanctionsF
            (wqbParams.V_S wAlpha wAlpha_continuous) wAlpha x₀ n)
        ∧ (∀ n, 0 < wqbParams.dynamicTopLockInSanctionsF
            (wqbParams.V_S wAlpha wAlpha_continuous) wAlpha x₀ n)) :=
  ⟨wqbParams_F_ne_affineF, wOf_V_S_ne_zero qbParams,
    fun x hx => ⟨wOf_stageTopRule_zero qbParams x,
      wOf_rule_eq_one qbParams wqb_state_chord qbCert_hchord_lo wqb_margin x hx⟩,
    fun _ hx₀ => wOf_perpetual qbParams wqb_state_chord qbCert_hchord_lo wqb_margin hx₀⟩

end ConeWitness

/-! # PART B — separation economy: the floor holds, the condition fails -/

namespace ConeSeparation

open Sanctions.AbstractGame Sanctions.AbstractGame.Params

/-- The Sender's ideal sanction, clipped to be feasible: `(x+1)/2` on `[0,1]`. -/
def qIdeal (x : ℝ) : ℝ := Sanctions.clipS ((x + 1) / 2)

/-- Sender stage payoff: a strictly concave tracking loss around `qIdeal`.
Like `wU_S`, it does not mention the Target's action. -/
def qU_S (x _a s : ℝ) : ℝ := -(s - qIdeal x) ^ 2

/-- Target stage payoff `−a²`. -/
def qU_T (_x a _s : ℝ) : ℝ := -(a ^ 2)

def qSigma (x _a : ℝ) : ℝ := qIdeal x

theorem qIdeal_mem (x : ℝ) : qIdeal x ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem _

theorem qIdeal_one : qIdeal 1 = 1 := by
  unfold qIdeal Sanctions.clipS
  norm_num

theorem qIdeal_half : qIdeal (1/2) = 3/4 := by
  unfold qIdeal Sanctions.clipS
  norm_num

theorem qIdeal_of_mem {x : ℝ} (hx : x ∈ Sanctions.S) : qIdeal x = (x + 1) / 2 := by
  unfold qIdeal Sanctions.clipS
  rw [min_eq_right (by linarith [hx.1, hx.2]), max_eq_right (by linarith [hx.1, hx.2])]

theorem qSigma_mem (x a : ℝ) : qSigma x a ∈ Set.Icc (0:ℝ) 1 := qIdeal_mem x

theorem qSigma_continuous :
    Continuous (fun xa : ℝ × ℝ => qSigma xa.1 xa.2) := by
  unfold qSigma qIdeal Sanctions.clipS
  fun_prop

theorem qSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => qU_S x a s) (Set.Icc (0:ℝ) 1) (qSigma x a) := by
  intro s _
  simp only [Set.mem_setOf_eq, qU_S, qSigma]
  nlinarith [sq_nonneg (s - qIdeal x)]

theorem qU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => qU_S xas.1 xas.2.1 xas.2.2) := by
  unfold qU_S qIdeal Sanctions.clipS
  fun_prop

theorem qU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => qU_T xas.1 xas.2.1 xas.2.2) := by
  unfold qU_T; fun_prop

/-- The separation economy: same discount factors and the same affine
transition as the witness, but the Sender's payoff is a tracking loss whose
*ideal rises with the state*, so the equilibrium sanction is positive while the
uniform state chord is negative. -/
def qParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := by constructor <;> norm_num
  β_T := 1/2
  β_T_mem := by constructor <;> norm_num
  β_S := 1/2
  β_S_mem := by constructor <;> norm_num
  U_T := qU_T
  U_S := qU_S
  σ := qSigma
  σ_mem := qSigma_mem
  σ_isMaxOn_U_S := qSigma_isMaxOn
  U_T_continuous := qU_T_continuous
  U_S_continuous := qU_S_continuous
  F := AbstractGame.affineF (1/2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`qParams` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance qParams_staticSelectorContinuous :
    qParams.StaticSelectorContinuous where
  σ_continuous := qSigma_continuous

@[simp] theorem qParams_U_S : qParams.U_S = qU_S := rfl
@[simp] theorem qParams_U_T : qParams.U_T = qU_T := rfl
@[simp] theorem qParams_β_S : qParams.β_S = 1/2 := rfl
@[simp] theorem qParams_δ : qParams.δ = 1/2 := rfl

theorem qParams_F_affine : qParams.F = AbstractGame.affineF qParams.δ := rfl

def qAlpha : ℝ → ℝ := fun _ => 0

theorem qAlpha_continuous : Continuous qAlpha := continuous_const

/-- **THE SEPARATION ECONOMY IS NOT A GAME EITHER.**  Same four `rfl` claims as
`w_not_a_game`: `qU_S` does not mention the Target's action, so the Sender's
dynamic argmax set, its greatest selector and the realised rule are literally
action-independent, and the transition never depended on the action.  The
separation below is therefore a statement about a single-agent dynamic program
too. -/
theorem q_not_a_game :
    (∀ x a a' s : ℝ, qParams.U_S x a s = qParams.U_S x a' s)
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ),
        qParams.dynamicArgmaxSet V x a = qParams.dynamicArgmaxSet V x a')
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a a' : ℝ),
        qParams.σ_dyn_top V x a = qParams.σ_dyn_top V x a')
    ∧ (∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α α' : ℝ → ℝ) (x : ℝ),
        qParams.dynamicTopRealizedRule V α x
          = qParams.dynamicTopRealizedRule V α' x) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

/-- **Rule 1: full defiance is the Target's optimum** at `qParams` too. -/
theorem qAlpha_isMaxOn (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x s : ℝ) :
    IsMaxOn (fun a => qParams.U_T x a s
        + qParams.β_T * V_T (Sanctions.clipS' (qParams.F x s)))
      Sanctions.I (qAlpha x) := by
  intro a _
  simp only [Set.mem_setOf_eq, qParams_U_T, qU_T, qAlpha]
  nlinarith [sq_nonneg a]

/-! ## The constructed Sender value here is the zero function -/

/-- Rule 5: one-line specialization of the parametric
`AbstractGame.Params.bellmanS_BCF_contracting`. -/
theorem q_contracting :
    ContractingWith qParams.β_S_nnreal
      (qParams.bellmanS_BCF qAlpha qAlpha_continuous) :=
  qParams.bellmanS_BCF_contracting qAlpha_continuous

theorem q_bellmanS_zero :
    qParams.bellmanS_BCF qAlpha qAlpha_continuous 0 = 0 := by
  ext y
  have hidealI : qIdeal y.val ∈ Sanctions.I := qIdeal_mem y.val
  have hgreat : IsGreatest
      ((fun s => qParams.integrandS qAlpha
        (fun z => (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) z) (y.val, s)) '' Sanctions.I)
      0 := by
    constructor
    · refine ⟨qIdeal y.val, hidealI, ?_⟩
      simp [AbstractGame.Params.integrandS, qParams_U_S, qU_S]
    · rintro _ ⟨s, _, rfl⟩
      simp only [AbstractGame.Params.integrandS, qParams_U_S, qU_S,
        BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero]
      nlinarith [sq_nonneg (s - qIdeal y.val)]
  have hval : qParams.bellmanS_BCF qAlpha qAlpha_continuous 0 y
      = sSup ((fun s => qParams.integrandS qAlpha
          (fun z => (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) z) (y.val, s)) ''
            Sanctions.I) := rfl
  rw [hval, hgreat.csSup_eq]
  simp

/-- **The constructed Sender Bellman fixed point at `qParams` is `0`.**  The
Sender can always hit its ideal sanction exactly, so the Bellman operator fixes
the zero function and Banach uniqueness does the rest. -/
theorem q_V_S_eq_zero : qParams.V_S qAlpha qAlpha_continuous = 0 := by
  have h_eq : qParams.V_S qAlpha qAlpha_continuous = q_contracting.fixedPoint := by
    unfold AbstractGame.Params.V_S; congr
  have h0 : (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) = q_contracting.fixedPoint :=
    ContractingWith.fixedPoint_unique q_contracting q_bellmanS_zero
  rw [h_eq, ← h0]

/-! ## The floor holds at the ceiling state -/

/-- **The floor holds**: at `x = 1` the realised equilibrium sanction is `1`. -/
theorem q_floor_at_one :
    (1:ℝ) ≤ qParams.dynamicTopRealizedRule
      (qParams.V_S qAlpha qAlpha_continuous) qAlpha 1 := by
  rw [q_V_S_eq_zero]
  have hmem : (1:ℝ) ∈ qParams.dynamicArgmaxSet 0 1 (qAlpha 1) := by
    refine ⟨⟨zero_le_one, le_refl 1⟩, ?_⟩
    intro s' _
    simp only [Set.mem_setOf_eq, qParams_U_S, qU_S, qIdeal_one,
      BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero, add_zero]
    nlinarith [sq_nonneg (s' - 1)]
  exact le_csSup (qParams.dynamicArgmaxSet_bddAbove 0 1 (qAlpha 1)) hmem

/-! ## but the `V_S`-free condition fails, for every admissible pair -/

/-- **THE SEPARATION.**  At `qParams`, state `x = 1`, level `c = 1`: the floor
`1 ≤ R 1` holds (`q_floor_at_one`), but **no** pair `(m, cS)` satisfying the
two `V_S`-free chord hypotheses satisfies the margin.  Hence the `V_S`-free
condition is strictly stronger than the floor — it is informative, not a
restatement of its own conclusion.

The quantification is universal over `(m, cS)`, and it is not vacuous:
`q_state_slope_witness` and `q_sanction_loss_witness` exhibit an admissible
pair `(−1, 0)`.

Numerically, the state chord between `y₁ = 1/2` and `y₂ = 1` at `s = 0` forces
`m ≤ −7/8`, while the sanction chord on `[99/100, 1]` forces `cS ≥ −1/100`; the
margin `cS·(1 − β_S(1−δ)) ≤ β_S·m·δ` then reads `−3/400 ≤ −7/32`, which is
false. -/
theorem q_condition_fails (m cS : ℝ)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ qParams.U_S y₂ (qAlpha y₂) s - qParams.U_S y₁ (qAlpha y₁) s)
    (h_sanction_loss :
      LowerLossSlopeOn (fun s => qParams.U_S 1 (qAlpha 1) s) (Set.Icc (0:ℝ) 1) cS) :
    ¬ (cS * (1 - qParams.β_S * (1 - qParams.δ)) ≤ qParams.β_S * m * qParams.δ) := by
  intro hmargin
  -- The state chord at `s = 0` between `y₁ = 1/2` and `y₂ = 1` forces `m ≤ −7/8`.
  have h1 := h_state_slope 0 ⟨le_refl 0, zero_le_one⟩
    (1/2) ⟨by norm_num, by norm_num⟩ 1 ⟨by norm_num, by norm_num⟩ (by norm_num)
  simp only [qParams_U_S, qU_S, qIdeal_one, qIdeal_half] at h1
  -- The sanction chord on `[99/100, 1]` forces `cS ≥ −1/100`.
  have h2 := h_sanction_loss (99/100) ⟨by norm_num, by norm_num⟩ 1
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  simp only [qParams_U_S, qU_S, qIdeal_one] at h2
  simp only [qParams_β_S, qParams_δ] at hmargin
  norm_num at h1 h2 hmargin
  linarith

/-! ## The separation is not vacuous: an admissible pair exists -/

/-- The state chord at `qParams` is bounded below by `−1` — an *admissible*
`m`, so the universal quantifier in `q_condition_fails` ranges over a nonempty
set. -/
theorem q_state_slope_witness :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (-1 : ℝ) * (y₂ - y₁)
        ≤ qParams.U_S y₂ (qAlpha y₂) s - qParams.U_S y₁ (qAlpha y₁) s := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  simp only [qParams_U_S, qU_S, qIdeal_of_mem hy₁, qIdeal_of_mem hy₂]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (show (0:ℝ) ≤ s - (y₁ + y₂) / 4 + 1/2 by linarith [hs.1, hy₁.2, hy₂.2])]

/-- The Sender's stage payoff at `x = 1` is non-decreasing in the sanction on
`[0,1]` — an *admissible* `cS = 0`. -/
theorem q_sanction_loss_witness :
    LowerLossSlopeOn (fun s => qParams.U_S 1 (qAlpha 1) s) (Set.Icc (0:ℝ) 1) 0 := by
  intro s₁ hs₁ s₂ hs₂ hle
  simp only [qParams_U_S, qU_S, qIdeal_one]
  nlinarith [hs₁.1, hs₂.2, hle]

/-- The two halves of the separation, packaged: the floor holds at the top
state, and the `V_S`-free condition fails there for **every** admissible
`(m, cS)`. -/
theorem q_floor_holds_condition_fails :
    ((1:ℝ) ≤ qParams.dynamicTopRealizedRule
        (qParams.V_S qAlpha qAlpha_continuous) qAlpha 1)
    ∧ (∀ m cS : ℝ,
        (∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
          m * (y₂ - y₁)
            ≤ qParams.U_S y₂ (qAlpha y₂) s - qParams.U_S y₁ (qAlpha y₁) s) →
        LowerLossSlopeOn (fun s => qParams.U_S 1 (qAlpha 1) s)
          (Set.Icc (0:ℝ) 1) cS →
        ¬ (cS * (1 - qParams.β_S * (1 - qParams.δ))
            ≤ qParams.β_S * m * qParams.δ)) :=
  ⟨q_floor_at_one, fun m cS h1 h2 => q_condition_fails m cS h1 h2⟩

end ConeSeparation

end Examples

end -- noncomputable section

end Sanctions

/-! ## Axiom hygiene (Rule 10) -/

#print axioms Sanctions.Examples.ConeWitness.w_not_a_game
#print axioms Sanctions.Examples.ConeWitness.wAlpha_isMaxOn
#print axioms Sanctions.Examples.ConeWitness.wAlpha_unique
#print axioms Sanctions.Examples.ConeWitness.w_floor
#print axioms Sanctions.Examples.ConeWitness.w_rule_eq_one
#print axioms Sanctions.Examples.ConeWitness.w_stage_floor_zero
#print axioms Sanctions.Examples.ConeWitness.w_barrier_defeated
#print axioms Sanctions.Examples.ConeWitness.w_V_S_ne_zero
#print axioms Sanctions.Examples.ConeWitness.w_joint_state_chord
#print axioms Sanctions.Examples.ConeWitness.w_bellmanS_preserves_cone
#print axioms Sanctions.Examples.ConeWitness.w_perpetual
#print axioms Sanctions.Examples.ConeWitness.w_stageTopRule_zero
#print axioms Sanctions.Examples.ConeWitness.w_dynamic_stake_hypothesis
#print axioms Sanctions.Examples.ConeWitness.w_dynamic_stake_conclusion
#print axioms Sanctions.Examples.ConeWitness.wOf_V_S_ne_zero
#print axioms Sanctions.Examples.ConeWitness.wOf_floor
#print axioms Sanctions.Examples.ConeWitness.wOf_perpetual
#print axioms Sanctions.Examples.ConeWitness.wOf_continuation_active
#print axioms Sanctions.Examples.ConeWitness.wqb_nonaffine_continuation_active
#print axioms Sanctions.Examples.ConeSeparation.q_not_a_game
#print axioms Sanctions.Examples.ConeSeparation.qAlpha_isMaxOn
#print axioms Sanctions.Examples.ConeSeparation.q_V_S_eq_zero
#print axioms Sanctions.Examples.ConeSeparation.q_floor_at_one
#print axioms Sanctions.Examples.ConeSeparation.q_condition_fails
#print axioms Sanctions.Examples.ConeSeparation.q_state_slope_witness
#print axioms Sanctions.Examples.ConeSeparation.q_sanction_loss_witness
#print axioms Sanctions.Examples.ConeSeparation.q_floor_holds_condition_fails
