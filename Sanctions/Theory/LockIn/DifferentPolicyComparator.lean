/-
Sanctions/Theory/LockIn/DifferentPolicyComparator.lean

**Equilibrium-vs-equilibrium dynamic-myopic comparator.**

The existing `dynamicTopSanctions_ge_myopify_same_alpha`
(`JointPreferenceBasin`) compares the upper-dynamic sanction sequence
to the `myopify`-comparator sanction sequence at the **same** Target
policy `α`. That is technically a comparison between the dynamic
equilibrium and a *re-run* of the dynamic equilibrium with discount
factors zeroed — not against a genuinely independently-optimized
myopic equilibrium with its own Target policy `α_myo`.

This file closes that gap. The construction has two layers:

1. **Generic order-theoretic comparator.** For *any* two realized
   sanction rules `R₁, R₂ : ℝ → ℝ`, if the upper rule `R₂` is monotone
   on `I` and pointwise dominates `R₁` on `I`, then the two natural
   paths agree on `I`-feasibility and the upper rule's path and
   sanction sequence pointwise dominate the lower rule's.

2. **Myopic feedback equilibrium.** A `MyopicFeedbackEquilibrium`
   packages an independently-optimized myopic Target policy
   `α_myo : ℝ → ℝ` together with `α_myo(x)` being the stage argmax of
   `U_T(x, ·, σ(x, ·))`. The dynamic-vs-myopic dominance theorem then
   compares two genuinely distinct equilibria.

The primitive route discharger
`dynamicTop_rule_dominates_myopic_policy_of_static_order` reduces the
key cross-policy rule-dominance hypothesis to a primitive
*static* policy ordering `σ(x, α_myo x) ≤ σ(x, α_dyn x)` plus monotone
`V_S` — the right form for an economically interpretable assumption.

No new fields added to `AbstractGame.Params`; all hypotheses are
theorem-parameter primitives or recovered from existing structure.
-/

import Sanctions.Foundations.CrossOrderComparison
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.RulePathF
import Sanctions.Theory.Equilibrium.SelectionRobust

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Generic rule path and sanction sequence

Parametric over an arbitrary realized sanction rule `R : ℝ → ℝ`.
The step `(1 - δ) x + δ R x` is the same convex combination used by
`dynamicTopLockInStep` and `lockInStep`, so the generic comparator
specializes directly to existing concrete paths.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** "Generic" and "arbitrary"
here describe the RULE `R`, not the TRANSITION. `ruleStep` / `rulePath` /
`ruleSanctions` hard-code `(1 − δ)·x + δ·R x` and never touch `p.F`, so
theorems over them are affine-restricted with no signature footprint.
The general-`F` siblings are `ruleStepF` / `rulePathF` / `ruleSanctionsF`
(`Theory/LockIn/RulePathF.lean`; moved there from §11 below in BH6.9).
Since BH6.9 (2026-10-07) `rulePath` is, by `rfl`, the general rule path of
the affine copy `p.affineCopy` (`rulePath_eq_affineCopy`), and the path
lemmas of §2, §3 and §7 are one-line instances of their general-`F`
siblings. No statement changed and no `hF` was added. -/

/-- One natural-dynamics step under an arbitrary realized rule `R`. -/
def ruleStep (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - p.δ) * x + p.δ * R x

/-- Natural state path under a realized rule `R`, from `x₀`. -/
def rulePath (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.ruleStep R x)^[n] x₀

/-- Sanction sequence along the natural path under rule `R`. -/
def ruleSanctions (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  R (p.rulePath R x₀ n)

@[simp] theorem rulePath_zero (R : ℝ → ℝ) (x₀ : ℝ) :
    p.rulePath R x₀ 0 = x₀ := rfl

@[simp] theorem rulePath_succ (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.rulePath R x₀ (n + 1) = p.ruleStep R (p.rulePath R x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- **The affine rule path is the general-`F` rule path of the affine copy**
(BH6.9, 2026-10-07): `p.rulePath R = p.affineCopy.rulePathF R`, by `rfl`. The
step `(1 − δ)·x + δ·R x` of `ruleStep` is literally the copy's transition
`affineF p.δ` at the rule's sanction.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22), by construction.** Both sides are
the affine law at rate `p.δ`; neither assumes `p.F = affineF p.δ`. The bridge
is what makes the hF-free lemmas below instances of the general-`F` lemmas of
`RulePathF.lean`. -/
theorem rulePath_eq_affineCopy (R : ℝ → ℝ) :
    p.rulePath R = p.affineCopy.rulePathF R := rfl

/-! ## 2. Feasibility under arbitrary rule -/

/-- If a rule preserves feasibility on `I`, so does its natural path.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** `rulePath` hard-codes the affine
law. Since BH6.9 (2026-10-07) a one-line instance of the general-`F`
`rulePathF_mem_I` (`RulePathF.lean`) at the affine copy `p.affineCopy`
(`rulePath_eq_affineCopy`); statement unchanged, no `hF` added. -/
theorem rulePath_mem_I
    {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePath R x₀ n ∈ Sanctions.I :=
  p.affineCopy.rulePathF_mem_I hR_mem hx₀

/-! ## 3. Generic comparison: lower rule path ≤ upper rule path -/

/-- **Generic path comparison.** If `R₂` is monotone on `I`, pointwise
dominates `R₁` on `I`, and both preserve feasibility, then the natural
state path under `R₁` is dominated by the natural state path under
`R₂` from any feasible start. This is purely order-theoretic; no
reference to discount factors or equilibrium concepts.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** `rulePath` hard-codes the affine
law. Since BH6.9 (2026-10-07) a one-line instance of the general-`F`
`rulePathF_le_of_rule_le_and_upper_mono` (`RulePathF.lean`), which has exactly
these hypotheses, at the affine copy `p.affineCopy`
(`rulePath_eq_affineCopy`); statement unchanged, no `hF` added. -/
theorem rulePath_le_of_rule_le_and_upper_mono
    {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ Sanctions.I, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePath R₁ x₀ n ≤ p.rulePath R₂ x₀ n :=
  p.affineCopy.rulePathF_le_of_rule_le_and_upper_mono hR₁_mem hR₂_mem hR₂_mono
    hR₁_le_R₂ hx₀

/-- Direct sanction-sequence comparison: under the same hypotheses,
`R₁`'s sanctions at every step are dominated by `R₂`'s sanctions. -/
theorem ruleSanctions_le_of_rule_le_and_upper_mono
    {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ Sanctions.I, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctions R₁ x₀ n ≤ p.ruleSanctions R₂ x₀ n := by
  intro n
  unfold ruleSanctions
  have h_paths := p.rulePath_le_of_rule_le_and_upper_mono
    hR₁_mem hR₂_mem hR₂_mono hR₁_le_R₂ hx₀ n
  have h_y₁_mem : p.rulePath R₁ x₀ n ∈ Sanctions.I :=
    p.rulePath_mem_I hR₁_mem hx₀ n
  have h_y₂_mem : p.rulePath R₂ x₀ n ∈ Sanctions.I :=
    p.rulePath_mem_I hR₂_mem hx₀ n
  -- R₁ (y₁) ≤ R₂ (y₁) ≤ R₂ (y₂)
  have h_step1 : R₁ (p.rulePath R₁ x₀ n) ≤ R₂ (p.rulePath R₁ x₀ n) :=
    hR₁_le_R₂ _ h_y₁_mem
  have h_step2 : R₂ (p.rulePath R₁ x₀ n) ≤ R₂ (p.rulePath R₂ x₀ n) :=
    hR₂_mono h_y₁_mem h_y₂_mem h_paths
  exact le_trans h_step1 h_step2

end Params
end AbstractGame

/-! ## 4. Myopic feedback equilibrium (β = 0 comparator)

A *myopic* feedback equilibrium has its own independently-optimized
Target policy `α_myo`. With both discount factors zero, the leader's
"continuation value" is identically the stage payoff, and the leader's
Bellman optimality reduces to stage-by-stage best response against
`σ(x, ·)`. No value-function fields are needed. -/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Myopic feedback equilibrium.** A Target policy `α_myo` that is
the *stage* argmax of `U_T(x, ·, σ(x, ·))` on `Sanctions.I`, with the
audit-28-compatible quantifier restriction to `Sanctions.S`. This is
the right object for an "independently-optimized myopic comparator."
The realized sanction at state `x` under this equilibrium is the
stage-Sender response `σ(x, α_myo x)`, by Rule-1 (Sender plays its
stage argmax). -/
structure MyopicFeedbackEquilibrium where
  /-- Myopic Target policy. -/
  α : ℝ → ℝ
  /-- α is feasible at every feasible state. -/
  α_mem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I
  /-- α is the stage-Bellman argmax of `U_T(x, ·, σ(x, ·))`. -/
  α_opt : ∀ x ∈ Sanctions.S,
    IsMaxOn
      (fun a => p.U_T x a (p.σ x a))
      Sanctions.I
      (α x)

/-! ### Round-11 Priority 2: existence from Berge's Maximum Theorem

The certificate field `M : MyopicFeedbackEquilibrium` packages the
fully myopic (β = 0) Target stage-best-response policy. Until now this
existed as a primitive obligation on the certificate, requiring the
user to construct `α` by hand. The existence is in fact a one-shot
consequence of continuity: `U_T_continuous` (a `Params` field, jointly
continuous in `(x, a, s)`) and the joint continuity of the static selector
`σ` in `(x, a)`, which since round BJ5.1 (2026-10-07) is the instance
`[p.StaticSelectorContinuous]` rather than a `Params` field:

> For each state `x`, the stage Target objective `a ↦ U_T(x, a, σ(x, a))`
> is continuous on the compact action set `[0, 1]`, hence attains a
> maximum (Berge / Maximum Theorem specialization to the constant
> correspondence `(x) ↦ [0, 1]`).

Wrapping `Classical.choose` over the per-state argmax produces a
canonical `MyopicFeedbackEquilibrium`, eliminating the certificate's
`M` field as a primitive obligation. Pure Rule-3 no-new-assumption
discharger.

## Rule compliance
* Rule 1: `α x` is, by `Classical.choose_spec`, an `IsMaxOn`-witness
  of the Target's β = 0 stage objective `U_T(x, ·, σ(x, ·))` — the
  optimal myopic Target reaction. The Sender's `σ` is the existing
  primitive β = 0 Sender selector. Both players play stage argmaxes
  ⇒ a genuine β = 0 / static-stage equilibrium.
* Rule 3: pure discharger, no new fields, no new hypotheses. Since round
  BJ5.1 the lemmas below, the canonical equilibrium and the greatest myopic
  equilibrium take `[p.StaticSelectorContinuous]` (formerly the `Params` field
  `σ_continuous`): the condition moved from every economy to these binders.
  General in `F`: nothing here mentions the transition.
* Rule 5: fully parametric over `Params`.
* Rule 8: paraphrase above.
* Rule 9: non-vacuity witness in
  `Sanctions/Examples/JointPositiveSanctions.lean` — instantiates at
  `jointPositiveParams` and confirms the produced `M.α x` is in `[0, 1]`. -/

/-- **Round-11 Priority 2 lemma.** For each state `x`, the Target's
β = 0 stage objective `a ↦ U_T(x, a, σ(x, a))` is continuous in `a`.
Pure composition of `U_T_continuous` with the static-selector continuity
instance (round BJ5.1: formerly the `Params` field `σ_continuous`). General
in `F`. -/
theorem myopic_stage_objective_continuous_in_a [p.StaticSelectorContinuous] (x : ℝ) :
    Continuous (fun a : ℝ => p.U_T x a (p.σ x a)) := by
  -- Continuity of (x, a) ↦ σ x a restricted to fixed x:
  have hσ_slice : Continuous (fun a : ℝ => p.σ x a) :=
    p.σ_continuous.comp (Continuous.prodMk continuous_const continuous_id)
  -- Continuity of (x, a, s) ↦ U_T x a s restricted to fixed x and s := σ x a:
  have hUT_slice : Continuous (fun a : ℝ => p.U_T x a (p.σ x a)) := by
    have h_triple : Continuous (fun a : ℝ => (x, a, p.σ x a)) := by
      refine Continuous.prodMk continuous_const ?_
      exact Continuous.prodMk continuous_id hσ_slice
    exact p.U_T_continuous.comp h_triple
  exact hUT_slice

/-- **Round-11 Priority 2 lemma.** For each state `x`, the Target's
β = 0 stage objective `a ↦ U_T(x, a, σ(x, a))` attains a maximum on
`[0, 1]` (= `Sanctions.I`). One-line consequence of compactness
(`isCompact_Icc`), nonemptiness (`0 ∈ [0, 1]`), and continuity
(`myopic_stage_objective_continuous_in_a`). -/
theorem myopic_stage_argmax_exists [p.StaticSelectorContinuous] (x : ℝ) :
    ∃ a ∈ Sanctions.I,
      IsMaxOn (fun a' => p.U_T x a' (p.σ x a')) Sanctions.I a := by
  apply IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by simp⟩
  exact (p.myopic_stage_objective_continuous_in_a x).continuousOn

/-- **Round-11 Priority 2 canonical construction.** A canonical
`MyopicFeedbackEquilibrium` built from the per-state stage-argmax
existence, via `Classical.choose`. The certificate's `M` field can
now be supplied as `p.myopicFeedbackEquilibrium_canonical` rather
than being a separate primitive obligation. General in `F`. Takes
`[p.StaticSelectorContinuous]` (round BJ5.1): the per-state argmax exists by
Weierstrass because the stage objective is continuous in `a`, which needs the
static selector continuous; at an economy carrying the instance (every
economy did, when it was a field) the construction is the same as before. -/
noncomputable def myopicFeedbackEquilibrium_canonical [p.StaticSelectorContinuous] :
    p.MyopicFeedbackEquilibrium where
  α x := Classical.choose (p.myopic_stage_argmax_exists x)
  α_mem x _ := (Classical.choose_spec (p.myopic_stage_argmax_exists x)).1
  α_opt x _ := (Classical.choose_spec (p.myopic_stage_argmax_exists x)).2

/-- **Round-11 Priority 2 existence theorem.** The
`MyopicFeedbackEquilibrium` carrier is inhabited at any `Params` whose
static selector is continuous (`[p.StaticSelectorContinuous]`, a `Params` field
until round BJ5.1), via the canonical construction. Eliminates the
certificate's `M : MyopicFeedbackEquilibrium` field as a primitive obligation.
General in `F`. -/
theorem myopicFeedbackEquilibrium_exists_of_continuity [p.StaticSelectorContinuous] :
    Nonempty p.MyopicFeedbackEquilibrium :=
  ⟨p.myopicFeedbackEquilibrium_canonical⟩

/-! ### The greatest myopic policy

`myopicFeedbackEquilibrium_canonical` chooses *a* stage maximizer at each state
and says nothing about which. That is enough wherever the conclusion holds for
every selection, which is most of this development. It is not enough for the
weak comparison: when both channels are only weakly signed, the honest
conclusion orders the two argmax *correspondences*, and turning that into a
statement about policies needs a named extremal selection to compare against.

The Sender side already has one — `σ_dyn_top`, the supremum of the dynamic
argmax set, shown to be a member of it via `IsClosed.csSup_mem`. This is the
Target-side mirror, and the argument is the same three facts: the stage argmax
set is non-empty (Berge, from continuity on a compact action set), bounded above
(it sits in `[0,1]`), and closed (it is the interval met with the preimage of a
point under a continuous objective). A non-empty closed bounded set of reals
contains its supremum.

Topkis (1998, *Optimal Decision Models*) states exactly this standing condition:
each argmax set has a greatest element when the feasible set is non-empty and
compact and the objective is upper semicontinuous in the decision variable.
Milgrom and Roberts (1994) is the reason to want one — their comparisons are
formulated at the highest and lowest equilibria precisely because those are what
survive multiplicity.

**Scope, stated once and meant** (Rule 9A). What follows compares against *the
greatest* myopic equilibrium, not against every myopic selection. The
pointwise-greatest selection need not be continuous in the state, and no claim is
made that it is: `MyopicFeedbackEquilibrium` asks for feasibility and stage
optimality and nothing else, which is why the construction needs no continuity
proof — and equally why the result must not be fed into a forward-looking Bellman
construction without a separate continuity or uniqueness argument.

Rule 1: every object here is an argmax of the Target's own stage payoff. Rule 3:
no new assumption — continuity of the stage objective is
`myopic_stage_objective_continuous_in_a`, derived from `U_T_continuous` and the
static-selector instance `[p.StaticSelectorContinuous]` (a `Params` field until
round BJ5.1, 2026-10-07), which the non-emptiness and closedness lemmas and the
greatest equilibrium therefore take as a binder. The definitions
`myopicTargetArgmaxSet` and `greatestMyopicAlpha`, the bound
`myopicTargetArgmaxSet_bddAbove` and the order fact `le_greatestMyopicAlpha` do
not need it. General in `F`. -/

/-- The Target's **stage** argmax set at `x`: the maximizers of `U_T(x, ·, σ(x, ·))`
over the feasible compliance interval. -/
def myopicTargetArgmaxSet (x : ℝ) : Set ℝ :=
  {a | a ∈ Sanctions.I ∧ IsMaxOn (fun a' => p.U_T x a' (p.σ x a')) Sanctions.I a}

theorem myopicTargetArgmaxSet_nonempty [p.StaticSelectorContinuous] (x : ℝ) :
    (p.myopicTargetArgmaxSet x).Nonempty := by
  obtain ⟨a, ha_mem, ha_opt⟩ := p.myopic_stage_argmax_exists x
  exact ⟨a, ha_mem, ha_opt⟩

theorem myopicTargetArgmaxSet_bddAbove (x : ℝ) :
    BddAbove (p.myopicTargetArgmaxSet x) := ⟨1, fun _ ha => ha.1.2⟩

/-- The stage argmax set is closed: it is `[0,1]` intersected with the preimage
of a single value under the continuous stage objective. -/
theorem myopicTargetArgmaxSet_isClosed [p.StaticSelectorContinuous] (x : ℝ) :
    IsClosed (p.myopicTargetArgmaxSet x) := by
  have hcont := p.myopic_stage_objective_continuous_in_a x
  set M : ℝ := sSup ((fun a' => p.U_T x a' (p.σ x a')) '' Sanctions.I) with hM
  have hset : p.myopicTargetArgmaxSet x
      = Sanctions.I ∩ (fun a' => p.U_T x a' (p.σ x a'))⁻¹' {M} := by
    ext a
    constructor
    · rintro ⟨ha_mem, ha_opt⟩
      refine ⟨ha_mem, ?_⟩
      have hub : ∀ z ∈ (fun a' => p.U_T x a' (p.σ x a')) '' Sanctions.I,
          z ≤ p.U_T x a (p.σ x a) := by
        rintro _ ⟨b, hb, rfl⟩; exact ha_opt hb
      have hne : ((fun a' => p.U_T x a' (p.σ x a')) '' Sanctions.I).Nonempty :=
        ⟨_, ⟨a, ha_mem, rfl⟩⟩
      exact le_antisymm (le_csSup ⟨_, hub⟩ ⟨a, ha_mem, rfl⟩)
        (csSup_le hne hub)
    · rintro ⟨ha_mem, ha_val⟩
      refine ⟨ha_mem, ?_⟩
      intro b hb
      have : p.U_T x b (p.σ x b) ≤ M := by
        refine le_csSup ?_ ⟨b, hb, rfl⟩
        obtain ⟨c, hc_mem, hc_opt⟩ := p.myopic_stage_argmax_exists x
        exact ⟨p.U_T x c (p.σ x c), by rintro _ ⟨d, hd, rfl⟩; exact hc_opt hd⟩
      have hval : p.U_T x a (p.σ x a) = M := ha_val
      show p.U_T x b (p.σ x b) ≤ p.U_T x a (p.σ x a)
      rw [hval]; exact this
  rw [hset]
  exact isClosed_Icc.inter (isClosed_singleton.preimage hcont)

/-- **The greatest myopic compliance level at each state.** -/
noncomputable def greatestMyopicAlpha (x : ℝ) : ℝ :=
  sSup (p.myopicTargetArgmaxSet x)

/-- It is itself a stage maximizer: a non-empty closed bounded set of reals
contains its supremum. -/
theorem greatestMyopicAlpha_mem_argmaxSet [p.StaticSelectorContinuous] (x : ℝ) :
    p.greatestMyopicAlpha x ∈ p.myopicTargetArgmaxSet x :=
  (p.myopicTargetArgmaxSet_isClosed x).csSup_mem
    (p.myopicTargetArgmaxSet_nonempty x) (p.myopicTargetArgmaxSet_bddAbove x)

theorem greatestMyopicAlpha_mem [p.StaticSelectorContinuous] (x : ℝ) :
    p.greatestMyopicAlpha x ∈ Sanctions.I :=
  (p.greatestMyopicAlpha_mem_argmaxSet x).1

theorem greatestMyopicAlpha_isMaxOn [p.StaticSelectorContinuous] (x : ℝ) :
    IsMaxOn (fun a' => p.U_T x a' (p.σ x a')) Sanctions.I
      (p.greatestMyopicAlpha x) :=
  (p.greatestMyopicAlpha_mem_argmaxSet x).2

/-- **And it is the greatest one**: every myopic stage maximizer at `x` lies weakly
below it. This is the property the weak comparison consumes. -/
theorem le_greatestMyopicAlpha {x a : ℝ} (ha_mem : a ∈ Sanctions.I)
    (ha_opt : IsMaxOn (fun a' => p.U_T x a' (p.σ x a')) Sanctions.I a) :
    a ≤ p.greatestMyopicAlpha x :=
  le_csSup (p.myopicTargetArgmaxSet_bddAbove x) ⟨ha_mem, ha_opt⟩

/-- **The greatest myopic feedback equilibrium.**

A genuine `MyopicFeedbackEquilibrium` whose policy is, at every state, the
largest stage-optimal compliance level. No continuity of the policy is claimed,
and the structure does not ask for any. The static-selector instance
`[p.StaticSelectorContinuous]` (round BJ5.1) is what makes each stage argmax set
non-empty and closed, so that its supremum is a stage maximizer. General in
`F`. -/
noncomputable def myopicFeedbackEquilibrium_greatest [p.StaticSelectorContinuous] :
    p.MyopicFeedbackEquilibrium where
  α := p.greatestMyopicAlpha
  α_mem x _ := p.greatestMyopicAlpha_mem x
  α_opt x _ := p.greatestMyopicAlpha_isMaxOn x

@[simp] theorem myopicFeedbackEquilibrium_greatest_alpha [p.StaticSelectorContinuous] (x : ℝ) :
    p.myopicFeedbackEquilibrium_greatest.α x = p.greatestMyopicAlpha x := rfl

/-- **Every myopic equilibrium's policy lies weakly below the greatest one.**

So the greatest myopic equilibrium is an upper envelope of the whole myopic
class, state by state — which is what makes it the right comparator for a weak
ordering result. -/
theorem myopic_alpha_le_greatest [p.StaticSelectorContinuous]
    (M : p.MyopicFeedbackEquilibrium) {x : ℝ} (hx : x ∈ Sanctions.S) :
    M.α x ≤ p.myopicFeedbackEquilibrium_greatest.α x :=
  p.le_greatestMyopicAlpha (M.α_mem x hx) (M.α_opt x hx)

/-- **Paper-facing alias for the myopic regime's realized sanction rule.**
At every state `x`, the fully myopic feedback regime realizes the
sanction `p.σ x (M.α x)`: the Target plays its β = 0 best response
`M.α x` (the Bellman argmax of the stage payoff
`U_T(x, ·, σ(x, ·))`), and the Sender plays its β = 0 stage best
response `σ(x, M.α x)` (a stage argmax of `U_S(x, M.α x, ·)`). This
is exposed under a paper-facing name so the regime-comparison theorem
reads `myopicEquilibriumRule M x ≤ dynamicEquilibriumRule E x`
instead of the lower-level `σ`/`σ_dyn_top` syntax. -/
def myopicEquilibriumRule (M : p.MyopicFeedbackEquilibrium) : ℝ → ℝ :=
  fun x => p.σ x (M.α x)

/-! ## 5. Different-policy dynamic-myopic dominance -/

/-- **Different-α dynamic ≥ myopic equilibrium dominance.**

The upper-dynamic equilibrium sanction sequence pointwise dominates the
independently-optimized myopic-equilibrium sanction sequence at every
step. Unlike `dynamicTopSanctions_ge_myopify_same_alpha`, the dynamic
and myopic equilibria use **different** Target policies `E.α` and
`M.α`, so this is a genuine equilibrium-vs-equilibrium comparison.

The cross-policy rule-dominance hypothesis `hRuleDom` can be discharged
via `dynamicTop_rule_dominates_myopic_policy_of_static_order` from a
primitive static policy ordering + monotone `V_S`. -/
theorem dynamicTopSanctions_ge_myopicEquilibrium_different_alpha
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hDynMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (hRuleDom : ∀ x ∈ Sanctions.I,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n,
      p.ruleSanctions (fun x => p.σ x (M.α x)) x₀ n
        ≤
      p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  -- Feasibilities are automatic from σ_mem and dynamicTopRealizedRule_mem.
  have hMyo_mem : ∀ x ∈ Sanctions.I, p.σ x (M.α x) ∈ Sanctions.I :=
    fun x _hx => p.σ_mem x (M.α x)
  have hDyn_mem : ∀ x ∈ Sanctions.I,
      p.dynamicTopRealizedRule E.V_S E.α x ∈ Sanctions.I :=
    fun x _hx => p.dynamicTopRealizedRule_mem E.V_S E.α x
  exact p.ruleSanctions_le_of_rule_le_and_upper_mono
    hMyo_mem hDyn_mem hDynMono hRuleDom hx₀

/-! ## 6. Primitive discharger for the cross-policy rule-dominance hypothesis

The cross-policy hypothesis `hRuleDom` decomposes as

```
σ(x, M.α x) ≤ σ(x, E.α x) ≤ σ_dyn_top V_S x (E.α x).
```

The right inequality is the established `σ_dyn_top_ge_sigma` under
monotone `V_S`; the left is the *static* policy ordering — a clean
primitive economic hypothesis. -/

/-- **Primitive route for the cross-policy rule dominance.**

If the Sender's stage best response under the myopic Target policy is
pointwise dominated by its stage best response under the dynamic
Target policy (a *static* policy ordering on the Target side), and the
Sender's value function is monotone, then the myopic realized rule is
pointwise dominated by the upper-dynamic realized rule. -/
theorem dynamicTop_rule_dominates_myopic_policy_of_static_order
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (h_static_order : ∀ x ∈ Sanctions.I, p.σ x (M.α x) ≤ p.σ x (E.α x)) :
    ∀ x ∈ Sanctions.I,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  intro x hx
  have h_step1 : p.σ x (M.α x) ≤ p.σ x (E.α x) := h_static_order x hx
  have h_step2 : p.σ x (E.α x) ≤ p.σ_dyn_top E.V_S x (E.α x) :=
    p.σ_dyn_top_ge_sigma E.V_S hV_S_mono x (E.α x)
  exact le_trans h_step1 h_step2

/-! ## 7. Localized basin comparator (audit-32 follow-up)

The §3–§5 comparators above quantify hypotheses over all of
`Sanctions.I`. In practice the project's lock-in API only needs
monotonicity and rule dominance on the high basin
`B := Set.Icc xbar 1`, paralleling `dynamicTopRealizedRule_mono_of_singleCrossingOn`
which also localizes single-crossing to the basin. The theorems below
restrict every hypothesis (monotonicity, rule dominance, feasibility-
preservation) to `B`, on the additional hypothesis that both rules
preserve the basin (i.e. their natural paths from a basin start stay
in the basin). -/

/-- **Localized path comparison on a basin `Set.Icc xbar 1`.**
Same content as `rulePath_le_of_rule_le_and_upper_mono`, but every
hypothesis is restricted to the basin `[xbar, 1]`. Both rules must
preserve the basin (`hR₁_basin`, `hR₂_basin`); the conclusion is the
same pointwise path comparison plus basin-membership of both paths.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** `rulePath` hard-codes the affine
law. Since BH6.9 (2026-10-07) a one-line instance of the general-`F`
`rulePathF_le_of_rule_le_and_upper_monoOn_basin` (`RulePathF.lean`), which
has exactly these hypotheses since BG2.1 dropped its `0 ≤ xbar`, at the
affine copy `p.affineCopy` (`rulePath_eq_affineCopy`); statement unchanged,
no `hF` added. -/
theorem rulePath_le_of_rule_le_and_upper_monoOn_basin
    {R₁ R₂ : ℝ → ℝ} {xbar : ℝ}
    (hR₁_basin : ∀ x ∈ Set.Icc xbar 1, R₁ x ∈ Set.Icc xbar 1)
    (hR₂_basin : ∀ x ∈ Set.Icc xbar 1, R₂ x ∈ Set.Icc xbar 1)
    (hR₂_monoOn : MonotoneOn R₂ (Set.Icc xbar 1))
    (hR₁_le_R₂ : ∀ x ∈ Set.Icc xbar 1, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      p.rulePath R₁ x₀ n ∈ Set.Icc xbar 1
      ∧ p.rulePath R₂ x₀ n ∈ Set.Icc xbar 1
      ∧ p.rulePath R₁ x₀ n ≤ p.rulePath R₂ x₀ n :=
  p.affineCopy.rulePathF_le_of_rule_le_and_upper_monoOn_basin hR₁_basin hR₂_basin
    hR₂_monoOn hR₁_le_R₂ hx₀

/-- **Localized sanction-sequence comparison on a basin.**
Corollary of `rulePath_le_of_rule_le_and_upper_monoOn_basin`. -/
theorem ruleSanctions_le_of_rule_le_and_upper_monoOn_basin
    {R₁ R₂ : ℝ → ℝ} {xbar : ℝ}
    (hR₁_basin : ∀ x ∈ Set.Icc xbar 1, R₁ x ∈ Set.Icc xbar 1)
    (hR₂_basin : ∀ x ∈ Set.Icc xbar 1, R₂ x ∈ Set.Icc xbar 1)
    (hR₂_monoOn : MonotoneOn R₂ (Set.Icc xbar 1))
    (hR₁_le_R₂ : ∀ x ∈ Set.Icc xbar 1, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.ruleSanctions R₁ x₀ n ≤ p.ruleSanctions R₂ x₀ n := by
  intro n
  unfold ruleSanctions
  obtain ⟨h_y1_mem, h_y2_mem, h_paths⟩ :=
    p.rulePath_le_of_rule_le_and_upper_monoOn_basin
      hR₁_basin hR₂_basin hR₂_monoOn hR₁_le_R₂ hx₀ n
  have h_step1 : R₁ (p.rulePath R₁ x₀ n) ≤ R₂ (p.rulePath R₁ x₀ n) :=
    hR₁_le_R₂ _ h_y1_mem
  have h_step2 : R₂ (p.rulePath R₁ x₀ n) ≤ R₂ (p.rulePath R₂ x₀ n) :=
    hR₂_monoOn h_y1_mem h_y2_mem h_paths
  exact le_trans h_step1 h_step2

/-- **Different-α dynamic ≥ myopic dominance on a basin.**

Localized analog of `dynamicTopSanctions_ge_myopicEquilibrium_different_alpha`:
all hypotheses (rule dominance, dynamic-side monotonicity, basin
invariance of both rules) live on `Set.Icc xbar 1` rather than on all
of `Sanctions.I`. This is the form that composes with the existing
`JointPreferenceBasinTop` discharges, where the dynamic-side basin
invariance and the on-basin monotonicity already drop out of
`dynamicTopRealizedRule_mono_of_singleCrossingOn` and the lock-in
floor. -/
theorem dynamicTopSanctions_ge_myopicEquilibrium_different_alpha_on_basin
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {xbar : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1, p.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hDyn_basin : ∀ x ∈ Set.Icc xbar 1,
      p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc xbar 1)
    (hDynMonoOn : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hRuleDom_on_basin : ∀ x ∈ Set.Icc xbar 1,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      p.ruleSanctions (fun x => p.σ x (M.α x)) x₀ n
        ≤
      p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) x₀ n :=
  p.ruleSanctions_le_of_rule_le_and_upper_monoOn_basin
    hMyo_basin hDyn_basin hDynMonoOn hRuleDom_on_basin hx₀

/-- **Pathwise sanction dominance from a global rule ceiling and a
sanction-path floor (no basin confinement of the dominated rule).**

Ceiling/floor alternative to
`ruleSanctions_le_of_rule_le_and_upper_monoOn_basin`: instead of
requiring the dominated rule `R_lo` to keep its own path inside the
basin (the `hMyoBasin`-style hypothesis, which fails in bistable
economies where the myopic regime washes out — see
`eeCert_hMyoBasin_counterexample` in `Examples/EECertWitness.lean`),
it requires only

* stage feasibility of `R_lo` on `[0,1]` (automatic for any realized
  sanction rule, from `σ_mem`);
* a level `c` capping `R_lo` on all of `[0,1]`; and
* the dominating sanction sequence staying at or above `c` forever.

The dominated path may drift anywhere in `[0,1]` — in particular it
may exit every high basin, which is exactly the myopic wash-out the
bistable witnesses exhibit. Pure transitivity through `c`. -/
theorem ruleSanctions_le_of_ceiling_and_path_floor
    {R_lo R_hi : ℝ → ℝ} {c : ℝ}
    (hlo_mem : ∀ x ∈ Sanctions.I, R_lo x ∈ Sanctions.I)
    (hceil : ∀ x ∈ Sanctions.I, R_lo x ≤ c)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (hfloor : ∀ n, c ≤ p.ruleSanctions R_hi x₀ n) :
    ∀ n, p.ruleSanctions R_lo x₀ n ≤ p.ruleSanctions R_hi x₀ n := by
  intro n
  have hceil_n : p.ruleSanctions R_lo x₀ n ≤ c :=
    hceil _ (p.rulePath_mem_I hlo_mem hx₀ n)
  exact le_trans hceil_n (hfloor n)

/-! ## 8. Static-order discharger from primitive (α-order + σ-monotone)

The cross-policy hypothesis `h_static_order` in
`dynamicTop_rule_dominates_myopic_policy_of_static_order` requires
`p.σ x (M.α x) ≤ p.σ x (E.α x)`. The theorem below derives this from
two cleaner primitives: pointwise policy ordering `M.α x ≤ E.α x` and
stage-Sender monotonicity in the leader action `MonotoneOn (σ x ·) I`.
This is the right form for a Milgrom-Shannon / Topkis-discharged
static comparator. -/

/-- **Static-order discharger from policy ordering and σ monotonicity.**
If the myopic leader policy is pointwise below the dynamic leader
policy and the Sender's stage best response is monotone in the leader
action at every state, then the Sender response under the myopic
policy is pointwise below the Sender response under the dynamic
policy — discharging the `h_static_order` hypothesis of
`dynamicTop_rule_dominates_myopic_policy_of_static_order`. The
domain `B ⊆ I` can be either the whole interval (use `B := Sanctions.I`)
or the basin `Set.Icc xbar 1` for the localized chain.

**⚠ SIGN WARNING (audit-41).** This theorem requires `σ` *monotone
non-decreasing* in `a`. In a literal-**compliance** interpretation
(`a = 1` is full compliance, `a = 0` is no compliance) the natural
sign is `σ` *non-increasing* in `a` (more compliance → fewer
sanctions). Under that compliance reading this theorem is vacuous /
backwards: use the audit-41 dual `static_sanctions_le_of_alpha_order_and_sigma_antitoneOn`
below instead. The monotone version is only safe when `a` is
re-interpreted as the Target's *resistance / noncompliance / stance*
(higher `a` = more sanction-triggering). -/
theorem static_order_of_alpha_order_and_sigma_monoOn
    {E_α M_α : ℝ → ℝ}
    (hE_mem : ∀ x ∈ Sanctions.S, E_α x ∈ Sanctions.I)
    (hM_mem : ∀ x ∈ Sanctions.S, M_α x ∈ Sanctions.I)
    {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hα_order : ∀ x ∈ B, M_α x ≤ E_α x)
    (hσ_monoOn_a : ∀ x ∈ B, MonotoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ B, p.σ x (M_α x) ≤ p.σ x (E_α x) := by
  intro x hx
  have hxS : x ∈ Sanctions.S := hB_subS hx
  have hMx : M_α x ∈ Sanctions.I := hM_mem x hxS
  have hEx : E_α x ∈ Sanctions.I := hE_mem x hxS
  exact hσ_monoOn_a x hx hMx hEx (hα_order x hx)

/-- **Composed discharger: cross-policy rule dominance from primitive
α-ordering + σ-monotonicity + monotone V_S.** Plugs
`static_order_of_alpha_order_and_sigma_monoOn` into
`dynamicTop_rule_dominates_myopic_policy_of_static_order` to give the
full chain from the four primitive economic inputs (α-ordering,
σ-monotonicity in a, monotone V_S, basin/I feasibility) to the
`hRuleDom` hypothesis consumed by
`dynamicTopSanctions_ge_myopicEquilibrium_different_alpha`.

**⚠ SIGN WARNING (audit-41).** Inherits the sign warning from
`static_order_of_alpha_order_and_sigma_monoOn`: requires `σ` monotone
non-decreasing in `a`, which is *backwards* under a literal-compliance
interpretation of `a`. Safe paper-facing dischargers should instead
use the audit-41 floor/ceiling discharger
`ruleDom_of_dynamic_floor_and_myopic_ceiling`. -/
@[deprecated "wrong sign under literal compliance (audit-41): requires σ monotone in a, backwards under compliance; use ruleDom_of_dynamic_floor_and_myopic_ceiling and the carrier-local StandardComplianceLocalCoreCertificate route" (since := "2026-06-23")]
theorem dynamicTop_rule_dominates_myopic_policy_from_primitives
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (hα_order : ∀ x ∈ Sanctions.S, M.α x ≤ E.α x)
    (hσ_monoOn_a : ∀ x ∈ Sanctions.S,
      MonotoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ Sanctions.S,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  have h_static :
      ∀ x ∈ Sanctions.S, p.σ x (M.α x) ≤ p.σ x (E.α x) :=
    p.static_order_of_alpha_order_and_sigma_monoOn
      (E_α := E.α) (M_α := M.α)
      (fun x hx => E.α_mem x hx) (fun x hx => M.α_mem x hx)
      (B := Sanctions.S) (fun _ hx => hx) hα_order hσ_monoOn_a
  intro x hx
  have h_step1 : p.σ x (M.α x) ≤ p.σ x (E.α x) := h_static x hx
  have h_step2 : p.σ x (E.α x) ≤ p.σ_dyn_top E.V_S x (E.α x) :=
    p.σ_dyn_top_ge_sigma E.V_S hV_S_mono x (E.α x)
  exact le_trans h_step1 h_step2

/-! ## 6. α-order from Topkis increasing differences

The cross-policy dominance discharger above takes `hα_order` as a
hypothesis. The audit-34 critique recommends deriving `hα_order` from
a primitive economic condition — specifically, **increasing differences
of the dynamic objective relative to the myopic objective**: as the
Target's compliance action `a` rises, the marginal continuation gain
from going dynamic (vs. myopic) is non-negative.

This is the canonical Topkis-style sufficient condition for argmax
monotonicity (Topkis 1978; Milgrom-Shannon 1994 Thm 4): if
`(a, regime) ↦ objective(a, regime)` has increasing differences in
the regime parameter (myopic = 0, dynamic = 1), then
`argmax_a objective(a, dynamic) ≥ argmax_a objective(a, myopic)` in
the strong set order.

The economic rationale: the dynamic objective adds the continuation
term `β_T · V_T(F(x, σ_dyn_top E.V_S x a))` over the myopic stage
payoff `U_T(x, a, σ(x, a))`. If higher compliance `a` raises the
continuation term faster than (or at least as fast as) it changes
the σ-mediated stage component, then the dynamic regime favors
higher `a` than the myopic regime — exactly `M.α ≤ E.α`.

The hypothesis is taken as a theorem-parameter primitive (no new
`Params` field). It is a category-(2) weakening of `hα_order`: it
replaces an *outcome* statement (one specific inequality between
two argmaxes) with a *structural* condition (increasing differences
across the regime parameter) that has a clean economic
interpretation and admits direct discharge at concrete payoff
classes via partial-derivative inspection. -/

/-- **Pointwise increasing differences of the dynamic-vs-myopic
objective family at a state `x`.** Captures the Topkis-style
sufficient condition for the argmax monotonicity that yields
`M.α x ≤ E.α x` (see `alpha_order_dynamic_ge_myopic_of_increasingDifferences`).

Concretely: for every pair of actions `a₁ ≤ a₂` in `Sanctions.I`,
moving from `a₁` to `a₂` is *at least as profitable* under the
dynamic regime (joint top integrand) as under the myopic regime
(stage payoff at `σ`). Equivalently, the *difference*
`dynamic_obj - myopic_obj` is non-decreasing in `a` on `Sanctions.I`. -/
def DynamicVsMyopicIncreasingDifferencesAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ ≤ a₂ →
    (p.joint_T_top_integrand E.V_T E.V_S x a₁ - p.U_T x a₁ (p.σ x a₁))
      ≤ (p.joint_T_top_integrand E.V_T E.V_S x a₂ - p.U_T x a₂ (p.σ x a₂))

/-- **α-order from Topkis increasing differences.** Derives the
`M.α x ≤ E.α x` ordering used by
`dynamicTop_rule_dominates_myopic_policy_from_primitives` from:

1. **Topkis increasing differences** at `x` between the dynamic top
   integrand `joint_T_top_integrand E.V_T E.V_S x ·` and the myopic
   stage integrand `U_T(x, ·, σ(x, ·))`.
2. **Uniqueness of the dynamic argmax at `x`** — strict argmax
   property: every `a ∈ I` other than `E.α x` is strictly worse than
   `E.α x` under the dynamic integrand.

Proof by contradiction: if `E.α x < M.α x`, apply increasing
differences to the pair `(E.α x, M.α x)` and combine with `M.α x`
being the myopic argmax (so the myopic-side jump is ≥ 0) to get
that `M.α x` is at least as good as `E.α x` under the dynamic
integrand. Then `E.α x` is the dynamic argmax, so they're equal in
dynamic value; strict-uniqueness then forces `M.α x = E.α x`,
contradicting `E.α x < M.α x`. -/
theorem alpha_order_dynamic_ge_myopic_of_increasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (h_incr_diff : p.DynamicVsMyopicIncreasingDifferencesAt E x)
    (h_dyn_unique : ∀ a ∈ Sanctions.I, a ≠ E.α x →
      p.joint_T_top_integrand E.V_T E.V_S x a
        < p.joint_T_top_integrand E.V_T E.V_S x (E.α x)) :
    M.α x ≤ E.α x := by
  by_contra h_not_le
  -- `h_not_le : ¬ (M.α x ≤ E.α x)` ⇒ `E.α x < M.α x`.
  have h_not_le : E.α x < M.α x := not_le.mp h_not_le
  -- Memberships in I:
  have hE_mem : E.α x ∈ Sanctions.I := E.α_mem x hx
  have hM_mem : M.α x ∈ Sanctions.I := M.α_mem x hx
  -- Increasing differences at (E.α x, M.α x):
  have h_incr :
      (p.joint_T_top_integrand E.V_T E.V_S x (E.α x)
        - p.U_T x (E.α x) (p.σ x (E.α x)))
        ≤ (p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
            - p.U_T x (M.α x) (p.σ x (M.α x))) :=
    h_incr_diff (E.α x) hE_mem (M.α x) hM_mem (le_of_lt h_not_le)
  -- M.α x is myopic argmax, so the myopic-side gain is non-negative:
  have h_myo_max :
      p.U_T x (E.α x) (p.σ x (E.α x)) ≤ p.U_T x (M.α x) (p.σ x (M.α x)) :=
    M.α_opt x hx hE_mem
  -- Rearrange h_incr: dyn(M.α x) ≥ dyn(E.α x) + [myo(M.α x) - myo(E.α x)]:
  have h_dyn_M_ge_E :
      p.joint_T_top_integrand E.V_T E.V_S x (E.α x)
        ≤ p.joint_T_top_integrand E.V_T E.V_S x (M.α x) := by
    linarith
  -- E.α x is dynamic argmax (at this x ∈ Sanctions.S):
  have h_dyn_max :
      p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
        ≤ p.joint_T_top_integrand E.V_T E.V_S x (E.α x) :=
    E.α_opt_top x hx hM_mem
  -- Equality of dynamic values at M.α x and E.α x:
  have h_dyn_eq :
      p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
        = p.joint_T_top_integrand E.V_T E.V_S x (E.α x) :=
    le_antisymm h_dyn_max h_dyn_M_ge_E
  -- M.α x ≠ E.α x (since E.α x < M.α x):
  have h_M_ne_E : M.α x ≠ E.α x := ne_of_gt h_not_le
  -- Strict uniqueness at the dynamic argmax: contradiction.
  have h_strict :
      p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
        < p.joint_T_top_integrand E.V_T E.V_S x (E.α x) :=
    h_dyn_unique (M.α x) hM_mem h_M_ne_E
  exact (lt_irrefl _) (h_strict.trans_le (le_of_eq h_dyn_eq.symm))

set_option linter.deprecated false in
/-- **Drop-in: full cross-policy dominance with `hα_order` discharged
from increasing differences.** Composes
`alpha_order_dynamic_ge_myopic_of_increasingDifferences` (per `x ∈ S`)
into the existing
`dynamicTop_rule_dominates_myopic_policy_from_primitives`, eliminating
`hα_order` from the user-facing surface.

Replaces it with the per-`x` increasing-differences primitive +
strict-uniqueness of dynamic argmax — both natural Topkis-style
economic conditions that admit direct discharge at concrete payoff
classes via partial-derivative inspection.

**⚠ SIGN WARNING (audit-41).** Inherits the wrong-sign issue: the
underlying `hσ_monoOn_a` is `σ` non-decreasing in `a`, which is
backwards under literal compliance. Safe paper-facing route: use the
audit-41 floor/ceiling discharger `ruleDom_of_dynamic_floor_and_myopic_ceiling`. -/
@[deprecated "wrong sign under literal compliance (audit-41): underlying hσ_monoOn_a is backwards under compliance; use ruleDom_of_dynamic_floor_and_myopic_ceiling and the carrier-local StandardComplianceLocalCoreCertificate route" (since := "2026-06-23")]
theorem dynamicTop_rule_dominates_myopic_policy_from_increasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (h_incr_diff : ∀ x ∈ Sanctions.S, p.DynamicVsMyopicIncreasingDifferencesAt E x)
    (h_dyn_unique : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, a ≠ E.α x →
        p.joint_T_top_integrand E.V_T E.V_S x a
          < p.joint_T_top_integrand E.V_T E.V_S x (E.α x))
    (hσ_monoOn_a : ∀ x ∈ Sanctions.S,
      MonotoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ Sanctions.S,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  -- Discharge hα_order pointwise via the increasing-differences theorem.
  have hα_order : ∀ x ∈ Sanctions.S, M.α x ≤ E.α x := fun x hx =>
    p.alpha_order_dynamic_ge_myopic_of_increasingDifferences E M hx
      (h_incr_diff x hx) (h_dyn_unique x hx)
  exact p.dynamicTop_rule_dominates_myopic_policy_from_primitives
    E M hV_S_mono hα_order hσ_monoOn_a

/-! ## 9. Audit-41 corrections: compliance-direction dischargers

The audit-41 critique observed that under the literal-compliance
interpretation of `a` (`a = 1` is full compliance, `a = 0` no
compliance), the canonical economic sign is `σ` **non-increasing** in
`a` (more compliance → fewer sanctions). The §8 chain — `hσ_monoOn_a`
together with the ordering of the myopic policy below every
equilibrium's policy — is sign-correct only under the *resistance /
noncompliance* reading of `a`, and the certificate family that carried
that ordering hypothesis was deleted on 2026-08-17. For the literal-
compliance reading, this section adds:

1. **`static_sanctions_le_of_alpha_order_and_sigma_antitoneOn`** — the
   correct compliance-channel theorem: `dynamic compliance ≥ myopic
   compliance` + `σ antitone in a` ⇒ `dynamic static sanctions ≤
   myopic static sanctions`. The two effects in the dynamic
   comparison **point in opposite directions** under literal
   compliance.

2. **`ruleDom_of_dynamic_floor_and_myopic_ceiling`** — the clean
   floor/ceiling discharger replacing the wrong-sign rule-dominance
   chain. Says: if the dynamic top-selector rule has a high floor on
   the basin AND the myopic stage-σ rule stays below that floor on
   the basin, THEN dynamic rule dominates myopic pointwise.

3. The compliance-direction analog of
   `DynamicVsMyopicIncreasingDifferencesAt`, capturing the "Target gives
   up resisting" mechanism where the dynamic Target chooses *less*
   compliance.

   **Naming note.** This item is announced here as
   `DynamicVsMyopicAlphaOrderDown`, and no declaration of that name
   exists. It was delivered in §10 below under
   `DynamicVsMyopicDecreasingDifferencesAt`,
   `alpha_order_dynamic_le_myopic_of_decreasingDifferences`, and
   `dynamicTop_rule_dominates_myopic_policy_audit41_compliance`. The
   announced name is a stale label, not a missing theorem; search for the
   §10 names instead.

   A **uniqueness-free** strengthening of that route — same α-ordering
   from a *strictly* decreasing wedge, valid for every selection from
   either argmax correspondence — is in
   `Theory/LockIn/TwoSidedForwardLooking.lean`.

These additions DO NOT replace the §8 theorems (which remain valid
under the resistance reading). They give the paper-facing user a
choice depending on which economic interpretation the model commits
to. -/

/-- **Static-sanctions discharger from policy ordering and σ
**antitone**.** The correct compliance-channel theorem: if the
dynamic Target chooses pointwise *more* compliance than the myopic
Target, AND the Sender's stage response is non-increasing in the
Target's compliance action, then the Sender response under the
*dynamic* policy is pointwise *below* the Sender response under the
*myopic* policy.

This is the literal-compliance dual of
`static_order_of_alpha_order_and_sigma_monoOn`. Under literal
compliance: `E.α x ≥ M.α x` + `σ x ↘ in a` ⇒ `σ(x, E.α x) ≤ σ(x, M.α x)`.

**Important**: the conclusion goes the *opposite* direction from the
§8 chain. It says the Target-compliance channel *lowers* dynamic
sanctions relative to myopic. The net dynamic-vs-myopic sanction
comparison then requires the Sender-continuation channel (σ_dyn ≥ σ
at the same `a`) to *overcome* this compliance relief — see the
floor/ceiling discharger below. -/
theorem static_sanctions_le_of_alpha_order_and_sigma_antitoneOn
    {E_α M_α : ℝ → ℝ}
    (hE_mem : ∀ x ∈ Sanctions.S, E_α x ∈ Sanctions.I)
    (hM_mem : ∀ x ∈ Sanctions.S, M_α x ∈ Sanctions.I)
    {B : Set ℝ}
    (hB_subS : B ⊆ Sanctions.S)
    (hα_order : ∀ x ∈ B, M_α x ≤ E_α x)
    (hσ_antiOn_a :
      ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ B, p.σ x (E_α x) ≤ p.σ x (M_α x) := by
  intro x hx
  have hxS : x ∈ Sanctions.S := hB_subS hx
  have hMx : M_α x ∈ Sanctions.I := hM_mem x hxS
  have hEx : E_α x ∈ Sanctions.I := hE_mem x hxS
  exact hσ_antiOn_a x hx hMx hEx (hα_order x hx)

/-! ### Audit-41 floor/ceiling discharger for rule dominance

The clean substitute for the wrong-sign chain
`hα_order + hσ_monoOn_a ⇒ rule dominance`. Under literal compliance,
the rule-dominance hypothesis is decomposed as: "dynamic has a high
sanction floor on the basin; myopic stays below that floor on the
basin." Both pieces are economically interpretable and naturally
arise from the existing high-basin machinery (the dynamic floor is
already given by `JointPreferenceBasinTop.level_dyn_top` or its
equilibrium wrappers; the myopic ceiling is the new piece, expressing
that the myopic stage equilibrium has *lower* sanctions than the
dynamic basin floor — usually because myopic Target complies more
than is needed to keep sanctions below the floor). -/

/-- **Audit-41 floor/ceiling discharger: rule dominance from a
dynamic floor and a myopic ceiling.** Composes a *dynamic floor*
(the dynamic top-selector rule produces sanctions at least
`max x sbar` on the basin) with a *myopic ceiling* (the myopic stage
σ-rule stays at or below `max x sbar` on the basin) to give pointwise
rule dominance. The composition is a one-line transitivity. -/
theorem ruleDom_of_dynamic_floor_and_myopic_ceiling
    {E : p.FeedbackStackelbergEquilibriumTop}
    {M : p.MyopicFeedbackEquilibrium}
    {xbar sbar : ℝ}
    (hDynFloor :
      ∀ x ∈ Set.Icc xbar 1,
        max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc xbar 1,
        p.σ x (M.α x) ≤ max x sbar) :
    ∀ x ∈ Set.Icc xbar 1,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  intro x hx
  exact le_trans (hMyoCeiling x hx) (hDynFloor x hx)

/-- **Convenience corollary**: the same discharger using
`Sanctions.S = [0, 1]` as the basin (when no proper basin endpoint
applies). -/
theorem ruleDom_on_S_of_dynamic_floor_and_myopic_ceiling
    {E : p.FeedbackStackelbergEquilibriumTop}
    {M : p.MyopicFeedbackEquilibrium}
    {sbar : ℝ}
    (hDynFloor :
      ∀ x ∈ Sanctions.S, max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hMyoCeiling :
      ∀ x ∈ Sanctions.S, p.σ x (M.α x) ≤ max x sbar) :
    ∀ x ∈ Sanctions.S, p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  intro x hx
  exact le_trans (hMyoCeiling x hx) (hDynFloor x hx)

/-! ### Audit-45 Step 3: optional `hMyoCeiling` discharger from
compliance-threshold primitives

The audit-45 critique noted that `hMyoCeiling` is "the main
remaining comparator assumption" and recommended an *optional*
decomposition into more interpretable primitives:

```text
τ(x) is enough compliance to keep sanctions below the floor.
myopic compliance M.α(x) is at least τ(x).
σ is antitone in compliance.
⇒ myopic sanctions are below the floor.
```

This is an *optional* discharger; it is not load-bearing on the
main compliance certificate (which keeps `hMyoCeiling` as a
primitive per Rule 3). -/

/-- **Audit-45 Step 3 optional `hMyoCeiling` discharger.** From a
compliance threshold `τ` such that `σ(x, τ(x)) ≤ max x sbar` on `B`,
together with `M.α ≥ τ` and `σ` antitone in compliance on `B`,
derive the myopic-ceiling property `σ(x, M.α x) ≤ max x sbar` on `B`. -/
theorem myopicCeiling_of_alpha_floor_and_sigma_antitoneOn
    {M : p.MyopicFeedbackEquilibrium}
    {B : Set ℝ}
    {τ : ℝ → ℝ}
    {sbar : ℝ}
    (hτ_mem : ∀ x ∈ B, τ x ∈ Sanctions.I)
    (hM_mem : ∀ x ∈ B, M.α x ∈ Sanctions.I)
    (hα_floor : ∀ x ∈ B, τ x ≤ M.α x)
    (hσ_antitone :
      ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hσ_ceiling_at_τ :
      ∀ x ∈ B, p.σ x (τ x) ≤ max x sbar) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ max x sbar := by
  intro x hx
  have hτ := hτ_mem x hx
  have hM := hM_mem x hx
  -- σ antitone in a: τ x ≤ M.α x ⇒ σ(x, M.α x) ≤ σ(x, τ x).
  have hσ_le : p.σ x (M.α x) ≤ p.σ x (τ x) :=
    hσ_antitone x hx hτ hM (hα_floor x hx)
  exact le_trans hσ_le (hσ_ceiling_at_τ x hx)

/-! ### Round-28: paper-facing σ-antitone discharger from `U_S` decreasing differences

The four-primitive `myopicCeiling_of_alpha_floor_and_sigma_antitoneOn`
decomposition above takes the `hσ_antitone` field
`∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I` as a primitive
sub-assumption. Round 28 reduces it further to a payoff-level
**decreasing-differences-in-`(s, a)`** primitive on `U_S` via the
Milgrom-Shannon Theorem 4' (Monotone Selection) dual antitone-argmax
result from `Foundations/MilgromShannon.lean` §6.

Paper reading (C² witnesses): `∂²U_S/∂s∂a ≤ 0` — the Sender's marginal
gain from *more* sanctions falls as the Target *complies more*. This is
the natural cross-partial assumption for the literal-compliance reading
of `a`. Combined with `σ_isMaxOn_U_S` (`σ(x, a)` is the Sender's stage
argmax on `[0, 1]`, Rule-1 coupling) and a strict-uniqueness assumption
on that argmax, the dual MS Theorem 4' delivers the cross-policy
antitone property directly.

Caveat (Round-28 polynomial witness): with
`polyComplianceParams.U_S = s` (linear, independent of `a`), the cross
difference `U_S(x, a', s') - U_S(x, a, s')` vanishes identically, so DD
holds *weakly with equality* and the strict-uniqueness hypothesis cannot
fire. In that degenerate case `σ ≡ 1` is constant in `a` and trivially
antitone — the Round-28 discharger is for *richer* payoffs where the
cross-partial bites. -/

/-- **Round-28 paper-facing σ-antitone discharger.** For a fixed state
`x` (typically in a basin `B`), suppose:

* `U_S(x, ·, ·)` has *decreasing differences* in `(s, a)` on
  `Sanctions.I × Sanctions.I` (the marginal Sender gain from more
  sanctions falls as the Target complies more — paper: `∂²U_S/∂s∂a ≤
  0`);
* at every parameter `a ∈ Sanctions.I` the Sender stage argmax
  `σ(x, a)` is *strictly* unique on `[0, 1]` (no tie with any other
  feasible sanction).

Then `σ(x, ·)` is `AntitoneOn` on `Sanctions.I`: raising the Target's
compliance lowers the Sender's stage selector.

The proof composes the Rule-1 coupling `σ_isMaxOn_U_S` with the
Foundations lemma `argmax_antitone_of_decreasingDifferencesOn_strict`. -/
theorem sigma_antitoneOn_a_of_U_S_decreasing_differences
    (x : ℝ)
    (hDD :
      Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
        (fun s a => p.U_S x a s))
    (h_unique :
      ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I, s ≠ p.σ x a →
        p.U_S x a s < p.U_S x a (p.σ x a)) :
    AntitoneOn (fun a => p.σ x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ ha_le
  -- Recover the maximizer facts from `σ_isMaxOn_U_S` (Rule-1 coupling).
  have hσ_max_a₁ : ∀ s ∈ Sanctions.I, p.U_S x a₁ s ≤ p.U_S x a₁ (p.σ x a₁) :=
    fun s hs => p.σ_isMaxOn_U_S x a₁ hs
  have hσ_max_a₂ : ∀ s ∈ Sanctions.I, p.U_S x a₂ s ≤ p.U_S x a₂ (p.σ x a₂) :=
    fun s hs => p.σ_isMaxOn_U_S x a₂ hs
  -- σ-membership in I.
  have hσ_in_a₁ : p.σ x a₁ ∈ Sanctions.I := p.σ_mem x a₁
  have hσ_in_a₂ : p.σ x a₂ ∈ Sanctions.I := p.σ_mem x a₂
  -- Strict-uniqueness conversion: at parameter a, every s ≠ σ(x, a) is
  -- strictly worse.
  have hs_strict_a₁ :
      ∀ y ∈ Sanctions.I, y ≠ p.σ x a₁ → p.U_S x a₁ y < p.U_S x a₁ (p.σ x a₁) :=
    h_unique a₁ ha₁
  have hs_strict_a₂ :
      ∀ y ∈ Sanctions.I, y ≠ p.σ x a₂ → p.U_S x a₂ y < p.U_S x a₂ (p.σ x a₂) :=
    h_unique a₂ ha₂
  -- Apply the Foundations dual MS Theorem 4' to f(s, a) := U_S(x, a, s).
  exact Sanctions.MilgromShannon.argmax_antitone_of_decreasingDifferencesOn_strict
    hDD ha_le ha₁ ha₂ hσ_in_a₁ hσ_in_a₂ hs_strict_a₁ hs_strict_a₂

/-! ### Zero-compliance collapse of the myopic ceiling

`myopicCeiling_of_alpha_floor_and_sigma_antitoneOn` above decomposes the
ceiling through a free compliance threshold `τ`, an `α`-floor `τ ≤ M.α`, and
a `σ`-ceiling at `τ`.  Evaluating that decomposition at `τ ≡ 0` collapses it:
the `α`-floor becomes `0 ≤ M.α x`, which is already guaranteed by the myopic
policy's own feasibility field, and the threshold symbol disappears.

What is left is a condition on **primitives only**.  `σ` is a `Params` field,
so neither hypothesis below mentions the myopic equilibrium, its policy, or
any other endogenous object — where the original spoke about what the myopic
Target *does*, this speaks only about the shape of the Sender's stage payoff.

Economically: the Sender's stage-optimal sanction falls as the Target complies
more, and *even facing complete noncompliance* it stays at or below the basin
floor.  The second clause is the worst case of the first, which is why nothing
about the Target's actual choice is needed. -/

/-- **Myopic ceiling from the zero-compliance stage sanction.**  If the
Sender's stage selector is antitone in the Target's compliance on the basin,
and its value against *zero* compliance already sits at or below the floor
`max x s̄`, then the myopic equilibrium's realised sanction does too.

Strictly weaker in stated content than
`myopicCeiling_of_alpha_floor_and_sigma_antitoneOn`: the threshold function
and the `α`-floor hypothesis are both eliminated, and what remains refers to
no endogenous object. -/
theorem myopicCeiling_of_sigma_antitoneOn_at_zero
    {M : p.MyopicFeedbackEquilibrium}
    {B : Set ℝ} {sbar : ℝ}
    (hB : B ⊆ Sanctions.S)
    (hσ_antitone :
      ∀ x ∈ B, AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hσ_zero : ∀ x ∈ B, p.σ x 0 ≤ max x sbar) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ max x sbar :=
  p.myopicCeiling_of_alpha_floor_and_sigma_antitoneOn
    (τ := fun _ => 0)
    (fun _ _ => ⟨le_refl 0, zero_le_one⟩)
    (fun x hx => M.α_mem x (hB hx))
    (fun x hx => (M.α_mem x (hB hx)).1)
    hσ_antitone
    hσ_zero

/-- **Myopic ceiling from payoff primitives alone.**  Composes the
zero-compliance collapse with the Round-28 `σ`-antitone discharger, so the
whole of the Goal-2 comparator assumption is discharged from the Sender stage
payoff:

* `hDD` — `U_S(x, ·, ·)` has decreasing differences in `(s, a)`; in C² form
  `∂²U_S/∂s∂a ≤ 0`, the Sender's marginal gain from more sanctions falls as
  the Target complies more;
* `h_unique` — the Sender's stage argmax is strict at every compliance level;
* `hσ_zero` — against zero compliance the stage-optimal sanction is already at
  or below the basin floor.

None of the three mentions an equilibrium, a value function, or a policy. -/
theorem myopicCeiling_of_U_S_decreasingDifferences
    {M : p.MyopicFeedbackEquilibrium}
    {B : Set ℝ} {sbar : ℝ}
    (hB : B ⊆ Sanctions.S)
    (hDD :
      ∀ x ∈ B,
        Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
          (fun s a => p.U_S x a s))
    (h_unique :
      ∀ x ∈ B, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I, s ≠ p.σ x a →
        p.U_S x a s < p.U_S x a (p.σ x a))
    (hσ_zero : ∀ x ∈ B, p.σ x 0 ≤ max x sbar) :
    ∀ x ∈ B, p.σ x (M.α x) ≤ max x sbar :=
  p.myopicCeiling_of_sigma_antitoneOn_at_zero (M := M) hB
    (fun x hx =>
      p.sigma_antitoneOn_a_of_U_S_decreasing_differences x (hDD x hx) (h_unique x hx))
    hσ_zero

/-! ### Audit-45 Step 4: uniform-in-action stage-bound dischargers

The compliance certificate's stage-bound fields
(`h_stage_target_loss_α`, `h_stage_sender_α`) quantify over every
top equilibrium `E` — paper-facing awkward. The dischargers below
reduce these `∀ E` fields to **uniform-in-action** versions
(stage bound holds for *every* feasible `a ∈ Sanctions.I`, not just
for the specific `E.α x`). The uniform-in-action form is strictly
stronger but much cleaner to state in the paper, and is the natural
discharge from a concrete payoff family. -/

/- **Audit-45 Step 4 uniform-in-action stage-bound dischargers**
have been moved to `Sanctions.Theory.Certificates.TargetSanctionLossOffset`
so that they live next to the `LowerLossSlopeOn` / `LowerSlopeOn`
predicates they consume. See:

* `stage_target_loss_at_equilibrium_of_uniform_action_loss`
* `stage_sender_slope_at_equilibrium_of_uniform_action_slope`
-/

/-! ## 10. Audit-41 compliance-direction α-order: "Target gives up resisting"

Parallel to `alpha_order_dynamic_ge_myopic_of_increasingDifferences`
but for the compliance reading of `a`. Under literal compliance, the
forward-looking Target may rationally CHOOSE LESS compliance (E.α ≤
M.α) when sanctions persist regardless — the "Target gives up
resisting" mechanism.

Captured by the dual Topkis condition: **myopic-minus-dynamic
objective has increasing differences** in `a` (equivalently,
dynamic-minus-myopic has *decreasing* differences). -/

/-- **Decreasing-differences-style Topkis primitive at a state `x`.**
For every `a₁ ≤ a₂ ∈ Sanctions.I`, the dynamic-minus-myopic objective
is *non-increasing* in `a` on `Sanctions.I`. Equivalently, the
myopic-minus-dynamic objective has increasing differences in `a`.

Economic interpretation under literal compliance: as compliance `a`
rises, the marginal continuation gain from going dynamic over myopic
is *non-positive*. The dynamic Target gets less marginal value from
extra compliance than the myopic Target does — consistent with the
"Target gives up resisting" / "compliance is futile under persistent
sanctions" story. -/
def DynamicVsMyopicDecreasingDifferencesAt
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) : Prop :=
  ∀ a₁ ∈ Sanctions.I, ∀ a₂ ∈ Sanctions.I, a₁ ≤ a₂ →
    (p.joint_T_top_integrand E.V_T E.V_S x a₂ - p.U_T x a₂ (p.σ x a₂))
      ≤ (p.joint_T_top_integrand E.V_T E.V_S x a₁ - p.U_T x a₁ (p.σ x a₁))

/-- **Audit-41 compliance-direction α-order from decreasing
differences.** Parallel to
`alpha_order_dynamic_ge_myopic_of_increasingDifferences`, but proves
the OPPOSITE direction `E.α x ≤ M.α x` (dynamic Target less
compliant) from the dual Topkis primitive
`DynamicVsMyopicDecreasingDifferencesAt`.

Proof by contradiction: if `E.α x > M.α x`, apply decreasing
differences to the pair `(M.α x, E.α x)` and combine with `E.α x`
being the dynamic argmax (so the dynamic-side jump is ≥ 0) to get
that `M.α x` is at least as good as `E.α x` under the *myopic*
integrand. By strict-uniqueness of the myopic argmax at `x`, this
forces `M.α x = E.α x`, contradicting `M.α x < E.α x`. -/
theorem alpha_order_dynamic_le_myopic_of_decreasingDifferences
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    {x : ℝ} (hx : x ∈ Sanctions.S)
    (h_decr_diff : p.DynamicVsMyopicDecreasingDifferencesAt E x)
    (h_myo_unique : ∀ a ∈ Sanctions.I, a ≠ M.α x →
      p.U_T x a (p.σ x a)
        < p.U_T x (M.α x) (p.σ x (M.α x))) :
    E.α x ≤ M.α x := by
  by_contra h_not_le
  -- h_not_le : ¬ (E.α x ≤ M.α x) ⇒ M.α x < E.α x.
  have h_not_le : M.α x < E.α x := not_le.mp h_not_le
  have hE_mem : E.α x ∈ Sanctions.I := E.α_mem x hx
  have hM_mem : M.α x ∈ Sanctions.I := M.α_mem x hx
  -- Decreasing differences at (M.α x, E.α x):
  --   dyn(E.α x) - myo(E.α x) ≤ dyn(M.α x) - myo(M.α x)
  have h_decr :
      (p.joint_T_top_integrand E.V_T E.V_S x (E.α x)
        - p.U_T x (E.α x) (p.σ x (E.α x)))
        ≤ (p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
            - p.U_T x (M.α x) (p.σ x (M.α x))) :=
    h_decr_diff (M.α x) hM_mem (E.α x) hE_mem (le_of_lt h_not_le)
  -- E.α x is dynamic argmax at x:
  have h_dyn_max :
      p.joint_T_top_integrand E.V_T E.V_S x (M.α x)
        ≤ p.joint_T_top_integrand E.V_T E.V_S x (E.α x) :=
    E.α_opt_top x hx hM_mem
  -- Rearrange: myo(E.α x) ≥ myo(M.α x) + [dyn(E.α x) - dyn(M.α x)] ≥ myo(M.α x).
  -- I.e., U_T(x, E.α x, σ(x, E.α x)) ≥ U_T(x, M.α x, σ(x, M.α x)).
  have h_myo_E_ge_M :
      p.U_T x (M.α x) (p.σ x (M.α x))
        ≤ p.U_T x (E.α x) (p.σ x (E.α x)) := by
    linarith
  -- M.α x is myopic argmax, so myo(E.α x) ≤ myo(M.α x):
  have h_myo_max_M :
      p.U_T x (E.α x) (p.σ x (E.α x)) ≤ p.U_T x (M.α x) (p.σ x (M.α x)) :=
    M.α_opt x hx hE_mem
  -- Equality at the two argmaxes:
  have h_myo_eq :
      p.U_T x (E.α x) (p.σ x (E.α x)) = p.U_T x (M.α x) (p.σ x (M.α x)) :=
    le_antisymm h_myo_max_M h_myo_E_ge_M
  -- E.α x ≠ M.α x (since M.α x < E.α x):
  have h_E_ne_M : E.α x ≠ M.α x := ne_of_gt h_not_le
  -- Strict uniqueness at the myopic argmax: contradiction.
  have h_strict :
      p.U_T x (E.α x) (p.σ x (E.α x))
        < p.U_T x (M.α x) (p.σ x (M.α x)) :=
    h_myo_unique (E.α x) hE_mem h_E_ne_M
  exact lt_irrefl _ (h_strict.trans_le (le_of_eq h_myo_eq.symm))

/-- **Audit-41 compliance-direction myopic ceiling discharger.**
Under literal compliance, with the dynamic Target choosing
*less* compliance (`E.α ≤ M.α` from decreasing differences) and σ
*antitone* in `a` (more compliance ⇒ fewer sanctions), we have the
myopic ceiling `σ(x, M.α x) ≤ σ(x, E.α x)`.

Combined with a *floor* from the dynamic-Sender escalation
(`σ(x, E.α x) ≤ σ_dyn_top E.V_S x (E.α x)`, under monotone V_S), this
gives the rule-dominance hypothesis `σ(x, M.α x) ≤
dynamicTopRealizedRule E.V_S E.α x` directly — the audit-41
compliance-direction route. -/
theorem myopicCeiling_from_alpha_order_dynamic_le_and_sigma_antitoneOn
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hα_order : ∀ x ∈ Sanctions.S, E.α x ≤ M.α x)
    (hσ_antiOn_a : ∀ x ∈ Sanctions.S,
      AntitoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ Sanctions.S, p.σ x (M.α x) ≤ p.σ x (E.α x) := by
  intro x hx
  have hMx : M.α x ∈ Sanctions.I := M.α_mem x hx
  have hEx : E.α x ∈ Sanctions.I := E.α_mem x hx
  exact hσ_antiOn_a x hx hEx hMx (hα_order x hx)

/-- **Audit-41 compliance-direction rule-dominance from primitives.**
Direct composition: decreasing differences + σ antitone + monotone V_S
+ myopic strict-uniqueness ⇒ rule dominance. -/
theorem dynamicTop_rule_dominates_myopic_policy_audit41_compliance
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hV_S_mono : Monotone E.V_S)
    (h_decr_diff : ∀ x ∈ Sanctions.S, p.DynamicVsMyopicDecreasingDifferencesAt E x)
    (h_myo_unique : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, a ≠ M.α x →
        p.U_T x a (p.σ x a) < p.U_T x (M.α x) (p.σ x (M.α x)))
    (hσ_antiOn_a : ∀ x ∈ Sanctions.S,
      AntitoneOn (fun a => p.σ x a) Sanctions.I) :
    ∀ x ∈ Sanctions.S,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
  -- Derive E.α ≤ M.α pointwise.
  have hα_order_down : ∀ x ∈ Sanctions.S, E.α x ≤ M.α x := fun x hx =>
    p.alpha_order_dynamic_le_myopic_of_decreasingDifferences E M hx
      (h_decr_diff x hx) (h_myo_unique x hx)
  -- Myopic ceiling: σ(M.α x) ≤ σ(E.α x).
  have hMyoCeiling : ∀ x ∈ Sanctions.S, p.σ x (M.α x) ≤ p.σ x (E.α x) :=
    p.myopicCeiling_from_alpha_order_dynamic_le_and_sigma_antitoneOn
      E M hα_order_down hσ_antiOn_a
  -- Dynamic escalation: σ(E.α x) ≤ σ_dyn_top E.V_S x (E.α x).
  intro x hx
  have h_ceil : p.σ x (M.α x) ≤ p.σ x (E.α x) := hMyoCeiling x hx
  have h_esc : p.σ x (E.α x) ≤ p.σ_dyn_top E.V_S x (E.α x) :=
    p.σ_dyn_top_ge_sigma E.V_S hV_S_mono x (E.α x)
  exact le_trans h_ceil h_esc

/-! ## 11. General-`F` cross-policy comparator (Option B, R-2026-07-08)

The §1–§7 comparator machinery evolves both regimes' natural paths by
the affine law `(1 − δ)·x + δ·R x` (`ruleStep`). The siblings below
evolve them by the **abstract transition** `p.F x (R x)`, so the
cross-policy pathwise-dominance conclusions hold for any transition
satisfying the structural `Params` fields — `F_mem` (feasibility),
`F_mono_x` (power persists), `F_mono_s` (sanctions entrench the
state), and `F_diag` (diagonal steady state) — not only the affine
instance; the affine objects are the `F := affineF δ` specialisation.
**No new assumption**: every lemma consumes only existing `Params`
fields, and where the affine proofs use the ring identity
`xbar = (1 − δ)·xbar + δ·xbar` the general proofs use the diagonal
anchor `F xbar xbar = xbar` plus monotonicity in both arguments. The
basin-localized forms used to carry an extra `0 ≤ xbar`, read only to
get the upper basin edge from `F_mem`. Since BG2.1 (2026-10-06) that edge
comes from `F_le_one_of_le` (via `F_mem_uIcc`, on all of `ℝ`), so they
hold for any `xbar`, as in the general-`F` lock-in machinery
(`dynamicTopLockInStepF_mem_basin`).

**Moved core (BH6.9, 2026-10-07).** The definitions `ruleStepF` / `rulePathF`
/ `ruleSanctionsF`, their `_zero`/`_succ` simp lemmas, the feasibility lemmas
`rulePathF_mem_I` and `rulePathF_mem_I_of_rule_mem`, and the path comparisons
`rulePathF_le_of_rule_le_and_closedLoop_mono`,
`rulePathF_le_of_rule_le_and_upper_mono` and
`rulePathF_le_of_rule_le_and_upper_monoOn_basin` now live in
`Theory/LockIn/RulePathF.lean`, with the same names and statements, so that
the affine path lemmas of §1–§7 and of `JointPreferenceBasin.lean` can be
proved as instances of them. The sanction-sequence corollaries and the
stopped-induction surface stay here. -/

/-- General-`F` sanction-sequence comparison on `I`: under the same
hypotheses, `R₁`'s sanctions along the general-`F` path are dominated
by `R₂`'s at every step. General-`F` sibling of
`ruleSanctions_le_of_rule_le_and_upper_mono`. -/
theorem ruleSanctionsF_le_of_rule_le_and_upper_mono
    {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ Sanctions.I, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF R₁ x₀ n ≤ p.ruleSanctionsF R₂ x₀ n := by
  intro n
  unfold ruleSanctionsF
  have h_paths := p.rulePathF_le_of_rule_le_and_upper_mono
    hR₁_mem hR₂_mem hR₂_mono hR₁_le_R₂ hx₀ n
  have h_y₁_mem : p.rulePathF R₁ x₀ n ∈ Sanctions.I :=
    p.rulePathF_mem_I hR₁_mem hx₀ n
  have h_y₂_mem : p.rulePathF R₂ x₀ n ∈ Sanctions.I :=
    p.rulePathF_mem_I hR₂_mem hx₀ n
  -- R₁ (y₁) ≤ R₂ (y₁) ≤ R₂ (y₂)
  exact le_trans (hR₁_le_R₂ _ h_y₁_mem)
    (hR₂_mono h_y₁_mem h_y₂_mem h_paths)

/-- **Strict general-`F` sanction-sequence comparison on `I`.**
If the lower rule is pointwise strictly below the monotone upper rule,
then its realized sanctions are strictly lower in every period.  The
state paths themselves need only be weakly ordered. -/
theorem ruleSanctionsF_lt_of_rule_lt_and_upper_mono
    {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_lt_R₂ : ∀ x ∈ Sanctions.I, R₁ x < R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF R₁ x₀ n < p.ruleSanctionsF R₂ x₀ n := by
  intro n
  unfold ruleSanctionsF
  have h_paths := p.rulePathF_le_of_rule_le_and_upper_mono
    hR₁_mem hR₂_mem hR₂_mono
    (fun x hx => (hR₁_lt_R₂ x hx).le) hx₀ n
  have h_y₁_mem : p.rulePathF R₁ x₀ n ∈ Sanctions.I :=
    p.rulePathF_mem_I hR₁_mem hx₀ n
  have h_y₂_mem : p.rulePathF R₂ x₀ n ∈ Sanctions.I :=
    p.rulePathF_mem_I hR₂_mem hx₀ n
  exact lt_of_lt_of_le (hR₁_lt_R₂ _ h_y₁_mem)
    (hR₂_mono h_y₁_mem h_y₂_mem h_paths)

/-- **General-`F` dynamic-versus-myopic equilibrium comparison.**
The forward-looking and myopic regimes use their independently optimal
Target policies.  If the dynamic realized rule is monotone and dominates
the myopic realized rule, its sanctions are weakly higher in every period
under the maintained transition `F`. -/
theorem dynamicTopSanctionsF_ge_myopicEquilibrium_different_alpha
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hDynMono : MonotoneOn
      (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (hRuleDom : ∀ x ∈ Sanctions.I,
      p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n,
      p.ruleSanctionsF (p.myopicEquilibriumRule M) x₀ n
        ≤ p.ruleSanctionsF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  have hMyo_mem : ∀ x ∈ Sanctions.I,
      p.myopicEquilibriumRule M x ∈ Sanctions.I :=
    fun x _ => p.σ_mem x (M.α x)
  have hDyn_mem : ∀ x ∈ Sanctions.I,
      p.dynamicTopRealizedRule E.V_S E.α x ∈ Sanctions.I :=
    fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x
  exact p.ruleSanctionsF_le_of_rule_le_and_upper_mono
    hMyo_mem hDyn_mem hDynMono hRuleDom hx₀

/-- Strict sibling of
`dynamicTopSanctionsF_ge_myopicEquilibrium_different_alpha`.  A strict
pointwise ordering of the two equilibrium rules yields strict sanctions in
every period, although their endogenous state paths need only be weakly
ordered. -/
theorem dynamicTopSanctionsF_gt_myopicEquilibrium_different_alpha
    (E : p.FeedbackStackelbergEquilibriumTop)
    (M : p.MyopicFeedbackEquilibrium)
    (hDynMono : MonotoneOn
      (p.dynamicTopRealizedRule E.V_S E.α) Sanctions.I)
    (hRuleDom : ∀ x ∈ Sanctions.I,
      p.σ x (M.α x) < p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n,
      p.ruleSanctionsF (p.myopicEquilibriumRule M) x₀ n
        < p.ruleSanctionsF (p.dynamicTopRealizedRule E.V_S E.α) x₀ n := by
  have hMyo_mem : ∀ x ∈ Sanctions.I,
      p.myopicEquilibriumRule M x ∈ Sanctions.I :=
    fun x _ => p.σ_mem x (M.α x)
  have hDyn_mem : ∀ x ∈ Sanctions.I,
      p.dynamicTopRealizedRule E.V_S E.α x ∈ Sanctions.I :=
    fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x
  exact p.ruleSanctionsF_lt_of_rule_lt_and_upper_mono
    hMyo_mem hDyn_mem hDynMono hRuleDom hx₀

/-- **Same-α pathwise Goal 2, general in `F`** (BH2.9, 2026-10-06). Under a
monotone Sender value and a forward-looking realised rule that is monotone on
`[0, 1]`, the forward-looking sanction sequence weakly dominates, in every
period, the sequence the *static* Sender rule `x ↦ σ(x, α x)` produces against
the same Target policy `α`, both evolved by the maintained transition `p.F`
from a common feasible start.

General-`F` sibling of the affine-restricted
`dynamicTopSanctions_ge_myopify_same_alpha` (`JointPreferenceBasin.lean`), with
the same three hypotheses: only the affine law `(1 − δ)·x + δ·rule` is replaced
by `p.F`, and nothing is added. The proof feeds the pointwise bound
`σ ≤ σ_dyn_top` (`σ_dyn_top_ge_sigma`) to the general-`F` comparator
`ruleSanctionsF_le_of_rule_le_and_upper_mono`. The right-hand side is
definitionally `dynamicTopLockInSanctionsF V_S α x₀ n`.

**Scope.** Same α on both sides: this compares the Sender's forward-looking and
static responses to one Target policy, not two independently optimised
equilibria (for that, `dynamicTopSanctionsF_ge_myopicEquilibrium_different_alpha`
above). A sharper form with `Monotone V_S` weakened to the response-pair
condition is `dynamicTopSanctionsF_ge_realizedRule_same_alpha_of_responsePair`
(`TwoSidedForwardLooking.lean` §10). -/
theorem dynamicTopSanctionsF_ge_realizedRule_same_alpha
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {x₀ : ℝ}
    (hV : Monotone V_S)
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule V_S α) Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.ruleSanctionsF (p.realizedRule α) x₀ n
        ≤ p.ruleSanctionsF (p.dynamicTopRealizedRule V_S α) x₀ n :=
  p.ruleSanctionsF_le_of_rule_le_and_upper_mono
    (fun x _ => p.realizedRule_mem α x) (fun x _ => p.dynamicTopRealizedRule_mem V_S α x)
    hTopMonoI (fun x _ => p.σ_dyn_top_ge_sigma V_S hV x (α x)) hx₀

/-! ### The exact surface the stopped induction consumes

`rulePathF_le_of_rule_le_on_stopped` below asks two things of the rules: the
lower one is dominated by the upper one on the region, and the upper one is
monotone on `[0,1]`. Reading its induction, neither is what the argument uses.
At each step it holds `x = path₁ k` in the region, `y = path₂ k` feasible, and
`x ≤ y`, and it needs exactly

    F(x, R₁ x) ≤ F(y, R₂ y),

which is `CrossOrderOn` (`Foundations/CrossOrderComparison.lean`) applied to the
two closed-loop state maps. That predicate is what this section names, and the
old hypothesis pair becomes one discharger of it among others.

The weakening is real rather than cosmetic. `crossOrderOn_iff_le_monotoneFloorOn`
identifies the exact condition as domination by the *greatest monotone minorant*
of the upper closed loop, which coincides with the upper closed loop precisely
when that loop is already monotone;
`Sanctions/Examples/CrossStepWithoutMonotoneRule.lean` exhibits an economy where
it does not (Rule 9B). Economically: rule monotonicity is irrelevant wherever the
transition is insensitive to the rule, and the old hypothesis was paying for
regularity the dynamics never used.

Rule 3: this narrows the assumption surface. Every hypothesis removed is
recovered by a discharger proved below, and the existing theorem is re-proved
through the general one with its statement unchanged, so the drift fence
(Rule 13) can check the direction rather than count symbols. -/

/-- **The cross-order condition on the two closed-loop state maps.**

The lower path is known to sit in `B`; the upper one is known only to be
feasible. `B` need not be invariant, closed, an interval, or a subset of
anything. -/
def CrossClosedLoopStepOrderOn (R₁ R₂ : ℝ → ℝ) (B : Set ℝ) : Prop :=
  Sanctions.CrossOrder.CrossOrderOn (p.ruleStepF R₁) (p.ruleStepF R₂)
    B Sanctions.I

/-! The matching condition on the two *sanction rules* needs no name here, and
the reason is worth recording: it is `CrossOrder.CrossOrderOn R₁ R₂ B Sanctions.I`
verbatim, with no mention of `p` at all. The state condition above has to route
through `p.F`, so it is genuinely about this game; the sanction condition is pure
order theory about two functions on `[0,1]` and belongs to the `Foundations`
vocabulary (Rule 19). It is spelled out at its use sites below rather than
wrapped, so nothing suggests the two conditions live at the same layer.

They are kept apart for a second reason. Ordering the *states* along the two
paths says nothing on its own about ordering the *sanctions* levied along them,
because the two rules are evaluated at different states. Deriving one from the
other silently is exactly the confusion this split prevents. -/

/-- **A monotone rule gives a monotone closed loop.** Both transition
monotonicities are used: in the state directly, and in the sanction through the
rule. -/
theorem ruleStepF_monotoneOn_of_rule_monotoneOn
    {R : ℝ → ℝ} (hR_mono : MonotoneOn R Sanctions.I) :
    MonotoneOn (p.ruleStepF R) Sanctions.I := by
  intro x hx y hy hxy
  exact le_trans (p.F_mono_s x (hR_mono hx hy hxy)) (p.F_mono_x (R y) hxy)

/-- **Closed-loop monotonicity plus rule domination discharge the condition.**

Sibling of `crossClosedLoopStepOrderOn_of_rule_le_and_upper_mono` below: the
upper rule need not be monotone, only the upper closed loop `x ↦ F(x, R₂ x)` on
`[0,1]`, which is all the argument reads from it. In plain terms: if at each
state of `B` the lower rule sanctions no more than the upper one, and the upper
policy's state-to-next-state map preserves order, then the lower closed loop
from a state of `B` never lands above the upper closed loop from a higher
feasible state. Dropped: `MonotoneOn R₂ I`. The old hypothesis implies the new
one (`ruleStepF_monotoneOn_of_rule_monotoneOn`) and the converse fails
(`exists_closedLoopMono_without_monotone_rule`). General in `F` (BG1.8). -/
theorem crossClosedLoopStepOrderOn_of_rule_le_and_closedLoop_mono
    {R₁ R₂ : ℝ → ℝ} {B : Set ℝ}
    (hB_sub : B ⊆ Sanctions.I)
    (hstep₂_mono : MonotoneOn (p.ruleStepF R₂) Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ B, R₁ x ≤ R₂ x) :
    p.CrossClosedLoopStepOrderOn R₁ R₂ B := by
  refine Sanctions.CrossOrder.crossOrderOn_of_le_of_monotoneOn hB_sub ?_
    hstep₂_mono
  intro x hx
  exact p.F_mono_s x (hR₁_le_R₂ x hx)

/-- **The old hypothesis pair discharges the new condition.**

Pointwise domination of the rules on `B` plus monotonicity of the upper rule on
`[0,1]` gives cross-order of the closed loops. `B ⊆ Sanctions.I` is needed and is
not in the roadmap sketch: without it the monotone upper rule cannot be applied
at a point of `B`. -/
theorem crossClosedLoopStepOrderOn_of_rule_le_and_upper_mono
    {R₁ R₂ : ℝ → ℝ} {B : Set ℝ}
    (hB_sub : B ⊆ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ B, R₁ x ≤ R₂ x) :
    p.CrossClosedLoopStepOrderOn R₁ R₂ B := by
  -- Statement unchanged; routed through the closed-loop discharger above
  -- (BG1.8): the monotone rule is used only to make the closed loop monotone.
  exact p.crossClosedLoopStepOrderOn_of_rule_le_and_closedLoop_mono hB_sub
    (p.ruleStepF_monotoneOn_of_rule_monotoneOn hR₂_mono) hR₁_le_R₂

/-- **Stopped path order from the cross-step condition alone.**

The general form: no monotonicity of either rule appears, and no invariance is
asserted. The two feasibility hypotheses remain, but they are bookkeeping for
`F_mem` — they say the rules produce feasible sanctions, not anything about how
the two rules compare.

`hstay` is a statement about the trajectory that was actually run, at the
horizon in question. It is not a claim that the path must stay in `B`, and it is
discharged by inspection wherever it is used. -/
theorem rulePathF_le_on_stopped_of_crossStepOrder
    {R₁ R₂ : ℝ → ℝ} {B : Set ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hcross : p.CrossClosedLoopStepOrderOn R₁ R₂ B)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {n : ℕ}
    (hstay : ∀ k, k ≤ n → p.rulePathF R₁ x₀ k ∈ B) :
    p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
  have key : ∀ k, k ≤ n →
      p.rulePathF R₁ x₀ k ∈ Sanctions.I
      ∧ p.rulePathF R₂ x₀ k ∈ Sanctions.I
      ∧ p.rulePathF R₁ x₀ k ≤ p.rulePathF R₂ x₀ k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨by simpa using hx₀, by simpa using hx₀, le_rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, hle⟩ := ih (Nat.le_of_succ_le hj)
      refine ⟨?_, ?_, ?_⟩
      · rw [rulePathF_succ]; exact p.F_mem _ _ h1 (hR₁_mem _ h1)
      · rw [rulePathF_succ]; exact p.F_mem _ _ h2 (hR₂_mem _ h2)
      · rw [rulePathF_succ, rulePathF_succ]
        exact hcross _ (hstay j (Nat.le_of_succ_le hj)) _ h2 hle
  exact (key n le_rfl).2.2

/-- **Stopped sanction order, stated in its own right.**

The sanctions levied along the two paths are ordered at horizon `n` once the
states are — but only through a condition on the rules evaluated at *different*
states, which is what `CrossRuleOrderOn` supplies and what state order alone
does not. Both cross-conditions are consumed, and the caller gets state order
and sanction order from one call. -/
theorem ruleSanctionsF_le_on_stopped_of_crossOrders
    {R₁ R₂ : ℝ → ℝ} {B : Set ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hcross : p.CrossClosedLoopStepOrderOn R₁ R₂ B)
    (hcrossRule : Sanctions.CrossOrder.CrossOrderOn R₁ R₂ B Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {n : ℕ}
    (hstay : ∀ k, k ≤ n → p.rulePathF R₁ x₀ k ∈ B) :
    p.ruleSanctionsF R₁ x₀ n ≤ p.ruleSanctionsF R₂ x₀ n :=
  hcrossRule _ (hstay n le_rfl) _
    (p.rulePathF_mem_I_of_rule_mem hR₂_mem hx₀ n)
    (p.rulePathF_le_on_stopped_of_crossStepOrder hR₁_mem hR₂_mem hcross hx₀ hstay)


/-- **Stopped path order from closed-loop monotonicity.**

Sibling of `rulePathF_le_of_rule_le_on_stopped` with the upper rule's
monotonicity on `[0,1]` replaced by monotonicity of the upper closed loop
`x ↦ F(x, R₂ x)` there. In plain terms: for as long as the lower path has in
fact stayed in the region `B` where the lower rule sanctions no more than the
upper one, the lower state stays weakly below the upper state, provided the
upper policy's state-to-next-state map preserves order. Dropped:
`MonotoneOn R₂ I`, which the induction never reads except to make the closed
loop monotone. General in `F` (BG1.8, 2026-10-06). -/
theorem rulePathF_le_of_rule_le_on_stopped_closedLoopMono
    {R₁ R₂ : ℝ → ℝ} {B : Set ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hstep₂_mono : MonotoneOn (p.ruleStepF R₂) Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ B, R₁ x ≤ R₂ x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {n : ℕ}
    (hstay : ∀ k, k ≤ n → p.rulePathF R₁ x₀ k ∈ B) :
    p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
  -- Instantiated at `B ∩ Sanctions.I` rather than `B`. The discharger needs
  -- the region inside `[0,1]` to apply the monotone upper closed loop there,
  -- while this theorem never assumes `B ⊆ Sanctions.I` — it gets feasibility
  -- of the path points from the induction instead. Intersecting recovers
  -- exactly that: `hstay` still supplies membership in `B`, and
  -- `rulePathF_mem_I_of_rule_mem` supplies membership in `[0,1]`.
  refine p.rulePathF_le_on_stopped_of_crossStepOrder hR₁_mem hR₂_mem
    (p.crossClosedLoopStepOrderOn_of_rule_le_and_closedLoop_mono
      (B := B ∩ Sanctions.I) Set.inter_subset_right hstep₂_mono
      (fun x hx => hR₁_le_R₂ x hx.1))
    hx₀ (fun k hk => ⟨hstay k hk, ?_⟩)
  exact p.rulePathF_mem_I_of_rule_mem hR₁_mem hx₀ k

/-- **Paths are ordered as far as the lower path stays in the region — no
invariance required.**

`rulePathF_le_of_rule_le_and_upper_monoOn_basin` needs the region to be
*invariant* under both rules, which is a permanent commitment about where the
dynamics can go. Often the rule comparison is only known on a region the
trajectory may eventually leave, and then invariance is not available and should
not be assumed.

This is the stopped form. The rule comparison is needed only on `B`, and the
conclusion holds at every horizon through which the *lower* path has in fact
stayed in `B` — a hypothesis about the trajectory that was run, not a claim that
it must stay. Nothing is asked of the upper path beyond feasibility, and `B` need
not be invariant, closed, or an interval.

The asymmetry is deliberate and is what makes the hypothesis cheap: monotonicity
of the upper rule is asked on all of `[0,1]`, because that is typically a global
regularity property, while the rule *comparison* is the region-local one, because
that is what a region-local argument delivers.

Rule 3: no new assumption surface. `hstay` is a statement about a particular
trajectory at a particular horizon, discharged by inspection wherever it is
used. -/
theorem rulePathF_le_of_rule_le_on_stopped
    {R₁ R₂ : ℝ → ℝ} {B : Set ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ B, R₁ x ≤ R₂ x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {n : ℕ}
    (hstay : ∀ k, k ≤ n → p.rulePathF R₁ x₀ k ∈ B) :
    p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
  -- Re-proved through `rulePathF_le_on_stopped_closedLoopMono`, and from
  -- there through `rulePathF_le_on_stopped_of_crossStepOrder`. The statement
  -- is unchanged (Rule 13 drift fence); only the route moved, so that the
  -- monotone upper rule is visibly one *discharger* of closed-loop
  -- monotonicity (`ruleStepF_monotoneOn_of_rule_monotoneOn`), which is in turn
  -- one discharger of the exact cross-order condition.
  exact p.rulePathF_le_of_rule_le_on_stopped_closedLoopMono hR₁_mem hR₂_mem
    (p.ruleStepF_monotoneOn_of_rule_monotoneOn hR₂_mono) hR₁_le_R₂ hx₀ hstay

/-- **Localized general-`F` sanction-sequence comparison on a basin.**
Corollary of `rulePathF_le_of_rule_le_and_upper_monoOn_basin`.
General-`F` sibling of
`ruleSanctions_le_of_rule_le_and_upper_monoOn_basin` — the exact
statement shape consumed by the general-`F` regime-comparison
engine. General in `F`; no `0 ≤ xbar` (dropped in BG2.1). -/
theorem ruleSanctionsF_le_of_rule_le_and_upper_monoOn_basin
    {R₁ R₂ : ℝ → ℝ} {xbar : ℝ}
    (hR₁_basin : ∀ x ∈ Set.Icc xbar 1, R₁ x ∈ Set.Icc xbar 1)
    (hR₂_basin : ∀ x ∈ Set.Icc xbar 1, R₂ x ∈ Set.Icc xbar 1)
    (hR₂_monoOn : MonotoneOn R₂ (Set.Icc xbar 1))
    (hR₁_le_R₂ : ∀ x ∈ Set.Icc xbar 1, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.ruleSanctionsF R₁ x₀ n ≤ p.ruleSanctionsF R₂ x₀ n := by
  intro n
  unfold ruleSanctionsF
  obtain ⟨h_y1_mem, h_y2_mem, h_paths⟩ :=
    p.rulePathF_le_of_rule_le_and_upper_monoOn_basin
      hR₁_basin hR₂_basin hR₂_monoOn hR₁_le_R₂ hx₀ n
  exact le_trans (hR₁_le_R₂ _ h_y1_mem)
    (hR₂_monoOn h_y1_mem h_y2_mem h_paths)

/-- **Strict localized general-`F` sanction comparison.**
On an invariant basin, a pointwise strict rule ordering and monotonicity
of the upper rule imply a strict sanction ordering in every period.
General in `F`; no `0 ≤ xbar` (dropped in BG2.1). -/
theorem ruleSanctionsF_lt_of_rule_lt_and_upper_monoOn_basin
    {R₁ R₂ : ℝ → ℝ} {xbar : ℝ}
    (hR₁_basin : ∀ x ∈ Set.Icc xbar 1, R₁ x ∈ Set.Icc xbar 1)
    (hR₂_basin : ∀ x ∈ Set.Icc xbar 1, R₂ x ∈ Set.Icc xbar 1)
    (hR₂_monoOn : MonotoneOn R₂ (Set.Icc xbar 1))
    (hR₁_lt_R₂ : ∀ x ∈ Set.Icc xbar 1, R₁ x < R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.ruleSanctionsF R₁ x₀ n < p.ruleSanctionsF R₂ x₀ n := by
  intro n
  unfold ruleSanctionsF
  obtain ⟨h_y1_mem, h_y2_mem, h_paths⟩ :=
    p.rulePathF_le_of_rule_le_and_upper_monoOn_basin
      hR₁_basin hR₂_basin hR₂_monoOn
      (fun x hx => (hR₁_lt_R₂ x hx).le) hx₀ n
  exact lt_of_lt_of_le (hR₁_lt_R₂ _ h_y1_mem)
    (hR₂_monoOn h_y1_mem h_y2_mem h_paths)

end Params
end AbstractGame

end

end Sanctions
