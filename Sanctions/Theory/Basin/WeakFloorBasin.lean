/-
Sanctions/Theory/Basin/WeakFloorBasin.lean

**Weak-floor joint preference basin (upper selector).**

`Theory/Basin/JointPreferenceBasin.lean` bundles the high basin's
structural hypotheses in `JointPreferenceBasinTop`, whose Sender field
demands a *ratchet* floor

    max x sbar ≤ s   for every basin state `x ∈ [xbar, 1]`,

which at the corner `x = 1` forces `s = 1`. That corner demand is exactly
what `Theory/Equilibrium/AbsorbingTopObstruction.lean` shows is
unattainable for any equilibrium whose top rule satisfies `rule 1 < 1`
(the general obstruction lemma is
`Sanctions.no_upper_basin_floor_of_top_lt_one`,
`Foundations/Basic.lean:51`), and the shocked mechanism witness P3 is
proved to be such an economy
(`mwShockedOne_no_top_floor`,
`Examples/MechanismWitnessShockedDominance.lean:495`).

This file introduces the **weak-floor** basin structure
`WeakFloorBasinTop`, identical to `JointPreferenceBasinTop` except that
the Sender field demands only the *level* floor `sbar ≤ s` (no `x ≤ s`),
compensated by one transition-level corner condition
`xbar ≤ F xbar sbar`. It then proves that forward invariance of
`[xbar, 1]` under the realized closed-loop map survives the weakening,
and records — with Lean counterexamples — exactly which downstream
conclusions do **not**.

## Rule compliance

**Rule 1.** The realized sanction along every path is
`p.dynamicTopRealizedRule V_S α x = p.σ_dyn_top V_S x (α x)`, the upper
selector of the Sender's *forward-looking argmax set*; the Target policy
`α` carries `target_policy_optimal` (Bellman-optimal against that
selector). No fixed or hand-chosen action is used. The exogenous shock
phase (`shockPathF`, `s ≡ 1`) is the project's sole Rule-1 exception and
is unchanged from `LockIn.lean`.

**Rule 3 (the load-bearing obligation).** `WeakFloorBasinTop` is a
*weakening*, not a new assumption axis. Two containment theorems
discharge this:

* `WeakFloorBasinTop.of_jointPreferenceBasinTop` — the strong basin plus
  the corner condition gives the weak basin at the *same* `sbar`.
* `WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed` — the strong
  basin gives the weak basin at the reindexed floor `max xbar sbar`
  **with no extra hypothesis at all** (the corner condition is then free
  from `F_diag` + `F_mono_s`).

The corner condition is *not* implied at an arbitrary `sbar`
(see `corner_arith_ingredients_at_zero_floor` and the genuine
`Params`-level witness in `Examples/WeakFloorContainmentCounterexample`), which is why the
reindexed form is the canonical containment.

**Rule 5.** The invariance core is stated for an arbitrary feasible rule
`g` and an arbitrary transition `p.F` (`weakFloor_stepF_mem_basin`); the
structure-level and affine-level statements are corollaries.

**Rule 11.** Everything the weakening loses is exhibited as a Lean
counterexample (`*_counterexample`), not asserted in prose.

**Rule 19.** All content here mentions `AbstractGame.Params` /
`dynamicTopRealizedRule`, i.e. it is Sender-Target model wiring, so it
belongs in `Theory/`, not `Foundations/`.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.PostEntryNonTermination

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Part 0 — the transition-level corner condition -/

/-- **The corner condition is free once the floor clears the pivot.**
`xbar ≤ sbar` implies `xbar ≤ F xbar sbar` for *every* transition
satisfying `F_diag` (`F x x = x`) and `F_mono_s` (`F` non-decreasing in
the sanction). -/
theorem corner_of_pivot_le_floor {xbar sbar : ℝ} (h : xbar ≤ sbar) :
    xbar ≤ p.F xbar sbar := by
  have hmono : p.F xbar xbar ≤ p.F xbar sbar := p.F_mono_s xbar h
  rwa [p.F_diag xbar] at hmono

/-- The corner condition at the *reindexed* floor `max xbar sbar` is free
for every transition — no hypothesis at all. -/
theorem corner_at_reindexed_floor (xbar sbar : ℝ) :
    xbar ≤ p.F xbar (max xbar sbar) :=
  p.corner_of_pivot_le_floor (le_max_left xbar sbar)

/-! ## Part 1 — the weak-floor basin structure -/

/-- **Weak-floor joint sanction-preference basin under the upper dynamic
selector.**

Identical to `JointPreferenceBasinTop` (`Theory/Basin/JointPreferenceBasin.lean:212`)
except:

* `sender_high_argmax_exists` demands only the **level floor**
  `sbar ≤ s` at every basin state, instead of the ratchet floor
  `max x sbar ≤ s`; and
* one new field `corner_holds : xbar ≤ p.F xbar sbar` supplies the single
  transition-level inequality that the dropped `x ≤ s` part was
  implicitly providing at the basin's lower edge.

`target_prefers_sanctions` keeps the *same* range `[max x sbar, 1]` as
the strong structure. Widening it to `[sbar, 1]` would be a
*strengthening* (a larger set to be monotone on) and would break the
Rule-3 containment, so it is deliberately not done. See the semantic
caveat in `Part 5` below: under the weak floor the realized sanction can
fall below `x`, so this field no longer necessarily covers the realized
point.

**Rule-13 note on unused fields --- read before pruning this structure.**
Several fields below (`top_rule_mono`, `target_prefers_sanctions`,
`target_policy_optimal`) are *not consumed* by the weak-floor invariance
results in this file.  That is deliberate and must not be "cleaned up".

The structure is field-for-field the strong `JointPreferenceBasinTop` with the
floor weakened and one corner condition added, for two reasons.  First, it is
then a **drop-in replacement**: a theorem written against the strong structure
can be re-derived against this one without re-plumbing its other hypotheses.
Second, the hypothesis-free containment
`of_jointPreferenceBasinTop_reindexed` maps *every* field across; dropping a
field here would make that containment state something weaker than "the strong
basin is a weak basin", which is exactly the property that keeps this a
weakening rather than a new assumption axis (Rule 3).

So an unused-hypothesis audit should record these as *carried for containment
and reuse*, not as decorative assumptions.  They are consumed by the downstream
conclusions the strong structure supports --- the Goal-2 dominance and
shock-entry results --- not by invariance, which is precisely the point:
invariance never needed the ratchet. -/
structure WeakFloorBasinTop
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xbar sbar : ℝ) : Prop where
  xbar_nonneg : 0 ≤ xbar
  xbar_le_one : xbar ≤ 1
  sbar_mem : sbar ∈ Sanctions.I

  /-- **The one new field.** At the basin's lower edge the floor sanction
  is enough to keep the state from falling out: `xbar ≤ F xbar sbar`.
  Free from `F_diag` whenever `xbar ≤ sbar` (`corner_of_pivot_le_floor`);
  for the affine transition it is *equivalent* to `xbar ≤ sbar`
  (`affine_corner_iff`). -/
  corner_holds : xbar ≤ p.F xbar sbar

  /-- Target policy is feasible on the basin (unchanged). -/
  target_policy_feasible :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), α x ∈ Sanctions.I

  /-- **Weakened Sender field.** At every basin state some forward-looking
  Sender maximizer is at least the *floor* `sbar`. The strong structure
  demanded `max x sbar ≤ s`. -/
  sender_high_argmax_exists :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s ∧
        sbar ≤ s

  /-- Topkis / monotone-comparative-statics property (unchanged). -/
  top_rule_mono :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1)

  /-- Target's forward-looking sanction preference on the high range
  (unchanged range `[max x sbar, 1]`). -/
  target_prefers_sanctions :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
        (Set.Icc (max x sbar) 1)

  /-- Target policy is Bellman-optimal against the upper dynamic Sender
  selector (unchanged; the Rule-1 discharge on the Target side). -/
  target_policy_optimal :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a) Sanctions.I (α x)

/-! ## Part 2 — bridge to the kinematic level condition -/

/-- **Weak basin ⇒ weak level condition.** The upper dynamic selector
inherits `sbar ≤ σ_dyn_top V_S x (α x)` on the basin. Weak-floor analogue
of `JointPreferenceBasinTop.level_dyn_top`
(`JointPreferenceBasin.lean:266`). -/
theorem WeakFloorBasinTop.level_dyn_top_weak
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  obtain ⟨s, hsI, hsMax, hsHigh⟩ := hB.sender_high_argmax_exists x hx
  have hsSet : s ∈ p.dynamicArgmaxSet V_S x (α x) := by
    refine ⟨hsI, ?_⟩
    intro s' hs'
    exact hsMax hs'
  unfold dynamicTopRealizedRule σ_dyn_top
  exact le_trans hsHigh (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x (α x)) hsSet)

/-- **Single-point reduction of the weak floor.** Because
`top_rule_mono` makes the realized top rule non-decreasing on the basin,
the basin-wide level floor `sbar ≤ rule x` follows from the **one**
inequality at the basin's lower edge, `sbar ≤ rule xbar`. This is the
practical entry point for checking a concrete economy against
`WeakFloorBasinTop`: one pivot bound instead of a family of bounds.
Contrast the strong ratchet floor, which cannot be reduced this way — it
must be verified at the corner `x = 1`, where it forces `rule 1 = 1`. -/
theorem weakFloor_of_pivot_bound_and_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_le : xbar ≤ 1)
    (hMono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1))
    (hPivotBound : sbar ≤ p.dynamicTopRealizedRule V_S α xbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  exact le_trans hPivotBound (hMono ⟨le_rfl, hxbar_le⟩ hx hx.1)

/-! ## Part 3 — Rule-3 containment: the weak structure is a weakening

Two theorems. The first is the containment the referee plan asked for
(same `sbar`, corner condition supplied). The second is stronger and is
the canonical one: after reindexing the floor to `max xbar sbar` the
strong structure implies the weak structure with **no extra hypothesis**,
so `WeakFloorBasinTop` is provably not a new independent assumption
axis. -/

/-- **Containment (as asked): `JointPreferenceBasinTop` + corner condition
⇒ `WeakFloorBasinTop`**, at the same floor `sbar`. -/
theorem WeakFloorBasinTop.of_jointPreferenceBasinTop
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hCorner : xbar ≤ p.F xbar sbar) :
    p.WeakFloorBasinTop V_T V_S α xbar sbar where
  xbar_nonneg := hB.xbar_nonneg
  xbar_le_one := hB.xbar_le_one
  sbar_mem := hB.sbar_mem
  corner_holds := hCorner
  target_policy_feasible := hB.target_policy_feasible
  sender_high_argmax_exists := by
    intro x hx
    obtain ⟨s, hsI, hsMax, hsHigh⟩ := hB.sender_high_argmax_exists x hx
    exact ⟨s, hsI, hsMax, le_trans (le_max_right x sbar) hsHigh⟩
  top_rule_mono := hB.top_rule_mono
  target_prefers_sanctions := hB.target_prefers_sanctions
  target_policy_optimal := hB.target_policy_optimal

/-- **Containment, hypothesis-free (canonical form).**
`JointPreferenceBasinTop … xbar sbar` implies
`WeakFloorBasinTop … xbar (max xbar sbar)` with no extra hypothesis: the
reindexed floor makes the corner condition free (`F_diag` + `F_mono_s`),
and `x ≥ xbar` upgrades the strong ratchet floor `max x sbar ≤ s` to the
reindexed level floor `max xbar sbar ≤ s`.

Note the reindexed floor automatically satisfies `xbar ≤ max xbar sbar`,
so the `xbar ≤ s_n` sanction floor is *also* recovered on this route
(`WeakFloorBasinTop.sanctionsF_ge_xbar`).

Nothing is lost *on this route*. The hypothesis is the strong basin, which
still delivers the ratchet, hence `Monotone (dynamicTopLockInSanctionsF ...)`
via `jointPreferenceBasinTopF_long_run_with_equilibrium_evidence`. What the
weak-floor structure fails to entail *by itself* is the ratchet and the
`Monotone` conclusions --- see Part 6. -/
theorem WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar) :
    p.WeakFloorBasinTop V_T V_S α xbar (max xbar sbar) where
  xbar_nonneg := hB.xbar_nonneg
  xbar_le_one := hB.xbar_le_one
  sbar_mem :=
    ⟨le_trans hB.xbar_nonneg (le_max_left _ _),
     max_le hB.xbar_le_one hB.sbar_mem.2⟩
  corner_holds := p.corner_at_reindexed_floor xbar sbar
  target_policy_feasible := hB.target_policy_feasible
  sender_high_argmax_exists := by
    intro x hx
    obtain ⟨s, hsI, hsMax, hsHigh⟩ := hB.sender_high_argmax_exists x hx
    exact ⟨s, hsI, hsMax, le_trans (max_le_max hx.1 le_rfl) hsHigh⟩
  top_rule_mono := hB.top_rule_mono
  target_prefers_sanctions := by
    intro x hx
    have hEq : max x (max xbar sbar) = max x sbar := by
      rw [← max_assoc, max_eq_left hx.1]
    rw [hEq]
    exact hB.target_prefers_sanctions x hx
  target_policy_optimal := hB.target_policy_optimal

/-! ## Part 4 — basin invariance under the weak floor (general `F`)

The strong structure proves invariance *through* the ratchet
`x ≤ F x (rule x)` (`dynamicTopLockInStepF_ge_self`,
`DynamicTopLockIn.lean:218`, whose only use of the strong floor is the
projection `le_max_left x sbar`), then chains `xbar ≤ x ≤ step`. That
routing is why the strong floor *looks* load-bearing for invariance. It
is not: the lower-edge chain

    xbar ≤ F xbar sbar ≤ F x sbar ≤ F x (rule x)

bypasses the ratchet entirely, using `F_mono_x` for the middle step and
`F_mono_s` for the last. Both are **global** `Monotone` fields on ℝ
(`Postulates/AbstractGame.lean:151,155`), so no domain side-condition is
needed.

The upper edge is domain-free too: `F x (g x) ≤ 1` follows from `x ≤ 1`
and `g x ≤ 1` alone (`F_le_one_of_le`, from `F_mem_uIcc`, which holds on
all of ℝ). So no lemma in this Part assumes `0 ≤ xbar`. They used to,
only to route the upper edge through `F_mem`; that hypothesis was dropped
on 2026-10-06 (BG2.1). -/

/-- **Weak-floor one-step invariance, arbitrary transition, arbitrary
feasible rule.** General in `F`. The Rule-5 parametric core: only
`sbar ≤ g x` on the basin is assumed (no `x ≤ g x`), plus the corner
condition. It holds for every `xbar`, negative ones included: the
hypothesis `0 ≤ xbar` was dropped on 2026-10-06 (BG2.1), because the upper
edge now comes from `F_le_one_of_le` rather than from `F_mem`. -/
theorem weakFloor_stepF_mem_basin
    (g : ℝ → ℝ) (hg_mem : ∀ x, g x ∈ Sanctions.I)
    {xbar sbar : ℝ}
    (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ g x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.F x (g x) ∈ Set.Icc xbar 1 := by
  refine ⟨?_, p.F_le_one_of_le hx.2 (hg_mem x).2⟩
  calc xbar ≤ p.F xbar sbar := hCorner
    _ ≤ p.F x sbar := p.F_mono_x sbar hx.1
    _ ≤ p.F x (g x) := p.F_mono_s x (hWeak x hx)

/-- Weak-floor one-step invariance at the **equilibrium** top rule
(general in `F`; no `0 ≤ xbar`, dropped in BG2.1). -/
theorem weakFloor_dynamicTopStepF_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicTopLockInStepF V_S α x ∈ Set.Icc xbar 1 :=
  p.weakFloor_stepF_mem_basin (p.dynamicTopRealizedRule V_S α)
    (fun y => p.dynamicTopRealizedRule_mem V_S α y) hCorner hWeak hx

/-- **Weak-floor full-path invariance** (level-condition form; general in
`F`). Direct replacement for `dynamicTopLockInPathF_mem_basin`
(`DynamicTopLockIn.lean`). No `0 ≤ xbar` (dropped in BG2.1). -/
theorem weakFloor_dynamicTopPathF_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPathF_succ]
    exact p.weakFloor_dynamicTopStepF_mem_basin V_S α hCorner hWeak ih

/-- **Structure-level invariance.** `WeakFloorBasinTop` keeps `[xbar, 1]`
forward invariant under the realized closed-loop map
`x ↦ F x (σ_dyn_top V_S x (α x))`. -/
theorem WeakFloorBasinTop.pathF_mem_basin
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1 :=
  p.weakFloor_dynamicTopPathF_mem_basin V_S α hB.corner_holds
    (WeakFloorBasinTop.level_dyn_top_weak p hB) hx₀

/-- One-step form of the structure-level invariance. -/
theorem WeakFloorBasinTop.stepF_mem_basin
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicTopLockInStepF V_S α x ∈ Set.Icc xbar 1 :=
  p.weakFloor_dynamicTopStepF_mem_basin V_S α hB.corner_holds
    (WeakFloorBasinTop.level_dyn_top_weak p hB) hx

/-- The `sbar`-floor on realized sanctions survives: it *is* the weak
floor. Replacement for `dynamicTopLockInSanctionsF_floor`
(`DynamicTopLockIn.lean:274`). -/
theorem WeakFloorBasinTop.sanctionsF_floor
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n := fun n =>
  WeakFloorBasinTop.level_dyn_top_weak p hB _
    (WeakFloorBasinTop.pathF_mem_basin p hB hx₀ n)

/-- The `xbar`-floor on realized sanctions survives **when the floor
clears the pivot** (`xbar ≤ sbar`) — in particular on the reindexed
containment route of
`WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed`, and for every
affine transition (where `corner_holds` is *equivalent* to `xbar ≤ sbar`
by `affine_corner_iff`). It does **not** survive from `corner_holds`
alone for a general `F`: see
`weakFloor_sanctions_ge_xbar_counterexample`. -/
theorem WeakFloorBasinTop.sanctionsF_ge_xbar
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hPivot : xbar ≤ sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n := fun n =>
  le_trans hPivot (WeakFloorBasinTop.sanctionsF_floor p hB hx₀ n)

/-- **Sharp weak-floor basin.** When the floor clears the pivot, the
*tighter* set `[sbar, 1]` is itself forward invariant — the weak floor's
natural basin is `[sbar, 1]`, and `corner_holds` is precisely what
extends invariance down to `[xbar, 1]`. -/
theorem WeakFloorBasinTop.pathF_mem_sharp_basin
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hPivot : xbar ≤ sbar)
    (hx₀ : x₀ ∈ Set.Icc sbar 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc sbar 1 := by
  have hWeak : ∀ x ∈ Set.Icc sbar (1 : ℝ),
      sbar ≤ p.dynamicTopRealizedRule V_S α x := by
    intro x hx
    exact WeakFloorBasinTop.level_dyn_top_weak p hB x
      ⟨le_trans hPivot hx.1, hx.2⟩
  exact p.weakFloor_dynamicTopPathF_mem_basin V_S α
    (p.corner_of_pivot_le_floor (le_refl sbar)) hWeak hx₀

/-! ## Part 5 — the weak-floor Goal-1 package (general `F`)

Everything `jointPreferenceBasinTopF_long_run_with_equilibrium_evidence`
(`JointPreferenceBasin.lean:765`) concludes, **minus** the two conjuncts
that provably die (Part 6): the `Monotone` sanction ratchet, and (for a
general `F` without `xbar ≤ sbar`) the `xbar ≤ s_n` floor. -/

/-- **Weak-floor Goal 1 with equilibrium evidence, general transition.**

Conclusions, in order:
1. the realized state path stays in the basin `[xbar, 1]`;
2. realized sanctions never fall below the floor `sbar`;
3. the Target policy is feasible at every path state;
4. the Target policy is Bellman-optimal (joint top integrand) at every
   path state — the Rule-1 Target discharge along the path;
5. the realized sanction is a forward-looking Sender maximizer at every
   path state — the Rule-1 Sender discharge along the path;
6. the Target weakly prefers more sanctions on `[max x_n, sbar), 1]`.

**Semantic caveat on (6).** Under the weak floor the realized sanction
may lie *below* `x_n`, so the range `[max x_n sbar, 1]` need not contain
the realized point. Conjunct (6) is literally the same statement as in
the strong package but no longer reads "the Target likes sanctions at the
realized point". This is a paper-facing meaning loss, not a Lean gap. -/
theorem weakFloorBasinTopF_long_run_with_equilibrium_evidence
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    (∀ n, α (p.dynamicTopLockInPathF V_S α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S
                              (p.dynamicTopLockInPathF V_S α x₀ n) a)
              Sanctions.I (α (p.dynamicTopLockInPathF V_S α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective V_S
                              (p.dynamicTopLockInPathF V_S α x₀ n)
                              (α (p.dynamicTopLockInPathF V_S α x₀ n)) s')
              Sanctions.I (p.dynamicTopLockInSanctionsF V_S α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective V_T
        (p.dynamicTopLockInPathF V_S α x₀ n)
        (α (p.dynamicTopLockInPathF V_S α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPathF V_S α x₀ n) sbar) 1)) := by
  have h_path := WeakFloorBasinTop.pathF_mem_basin p hB hx₀
  refine ⟨h_path, WeakFloorBasinTop.sanctionsF_floor p hB hx₀, ?_, ?_, ?_, ?_⟩
  · intro n; exact hB.target_policy_feasible _ (h_path n)
  · intro n; exact hB.target_policy_optimal _ (h_path n)
  · intro n s' hs'
    exact p.σ_dyn_top_isMaxOn V_S
      (p.dynamicTopLockInPathF V_S α x₀ n)
      (α (p.dynamicTopLockInPathF V_S α x₀ n)) hs'
  · intro n; exact hB.target_prefers_sanctions _ (h_path n)

/-- **Weak-floor Goal 3 (temporary shock ⇒ permanent floor), general
transition.** The shock phase is exogenous (`s ≡ 1`, the sole Rule-1
exception) and hence floor-independent, so the shock-entry step
`shockPathF_eventually_in_basin` is inherited verbatim; the post-shock
tail is then the weak-floor invariance of Part 4. The `Monotone`
conjunct of `jointPreferenceBasinTopF_temporary_shock_permanent_high`
(`JointPreferenceBasin.lean:966`) is dropped — it provably fails
(Part 6). -/
theorem weakFloorBasinTopF_temporary_shock_permanent_floor
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hxbar_lt_one : xbar < 1)
    (hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective V_T
          (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n)
          (α (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n)) s)
        (Set.Icc
          (max (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n) sbar)
          1)) := by
  obtain ⟨N, hN⟩ :=
    p.shockPathF_eventually_in_basin hF_top hx₀_nn hx₀_le hxbar_lt_one
  have h_N_in : p.shockPathF x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  have h_path := WeakFloorBasinTop.pathF_mem_basin p hB h_N_in
  have h_floor := WeakFloorBasinTop.sanctionsF_floor p hB h_N_in
  refine ⟨N, h_path, h_floor, ?_, ?_⟩
  · intro n; exact lt_of_lt_of_le hsbar_pos (h_floor n)
  · intro n; exact hB.target_prefers_sanctions _ (h_path n)

/-- **Weak-floor post-entry non-termination.** After basin entry at date
`T`, no relief cutoff strictly below the floor `sbar` is ever reached.
Weakened form of `jointPreferenceBasinTopF_tail_no_relief`
(`PostEntryNonTermination.lean:215`), whose cutoff is the *entry state*
`max x_T xbar`: that stronger cutoff routes through path monotonicity
(the ratchet) and does not survive the weakening. -/
theorem weakFloorBasinTopF_tail_no_relief
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ q : ℝ} {T : ℕ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < sbar) :
    ∀ n, ¬ p.dynamicTopLockInSanctionsF V_S α x₀ (T + n) ≤ q := by
  intro n hrelief
  have hfloor := WeakFloorBasinTop.sanctionsF_floor p hB hT n
  rw [p.dynamicTopLockInSanctionsF_add V_S α x₀ T n] at hrelief
  exact (not_le_of_gt hq) (le_trans hfloor hrelief)

/-! ## Part 6 — what the weakening loses (Rule-11 counterexamples)

Each statement below is a *refutation* of the corresponding strong-basin
conclusion under weak-floor hypotheses, exhibited in Lean rather than
asserted. The witnesses are ordinary real functions, not `Params`
instances, so what is refuted is the *implication*, at its weakest
hypothesis set: the level floor does not entail these conjuncts for
arbitrary kinematic data `(F, g)`.

Read that scope carefully. The witness rule below is a *constant*, which is
not an equilibrium object at all, so the refutation says nothing about the
sub-class of equilibrium-realized rules --- restricting to that class
*strengthens* the refuted implication's hypotheses, and a counterexample to a
broad universal is no counterexample to a restricted one. In particular the
ratchet floor does rescue every conjunct below
(`of_jointPreferenceBasinTop_reindexed`). What is refuted is that the *level*
floor suffices. -/

/-- Counterexample witness: the **flat** transition `F x s = x`. It
satisfies every structural `F` field of `Params`, and makes the corner
condition `xbar ≤ F xbar sbar` hold vacuously for *every* `sbar`. -/
def flatTransition : ℝ → ℝ → ℝ := fun x _ => x

theorem flatTransition_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 →
    s ∈ Set.Icc (0 : ℝ) 1 → flatTransition x s ∈ Set.Icc (0 : ℝ) 1 :=
  fun _ _ hx _ => hx

theorem flatTransition_continuous :
    Continuous (fun (xs : ℝ × ℝ) => flatTransition xs.1 xs.2) := continuous_fst

theorem flatTransition_mono_x : ∀ s, Monotone (fun x => flatTransition x s) :=
  fun _ _ _ h => h

theorem flatTransition_mono_s : ∀ x, Monotone (fun s => flatTransition x s) :=
  fun _ _ _ _ => le_rfl

theorem flatTransition_diag : ∀ x, flatTransition x x = x := fun _ => rfl

/-- **COUNTEREXAMPLE 1 — the `xbar ≤ s_n` sanction floor dies** under the
corner condition alone (general `F`). The flat transition satisfies every
`F` field and makes the corner condition hold at `sbar = 0 < xbar = 1/2`,
so a rule sitting at `0` clears the weak floor without clearing `xbar`.
Refutes the weak-floor analogue of
`dynamicTopLockInSanctionsF_ge_xbar` (`DynamicTopLockIn.lean:288`).

This is exactly why `WeakFloorBasinTop.sanctionsF_ge_xbar` takes the
extra `xbar ≤ sbar` — which is automatic on the reindexed containment
route and equivalent to `corner_holds` for affine `F`. -/
theorem weakFloor_sanctions_ge_xbar_counterexample :
    ¬ (∀ (F : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (xbar sbar : ℝ),
        (∀ x s, x ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
          F x s ∈ Set.Icc (0:ℝ) 1) →
        (∀ s, Monotone (fun x => F x s)) →
        (∀ x, Monotone (fun s => F x s)) →
        (∀ x, F x x = x) →
        (∀ x, g x ∈ Set.Icc (0:ℝ) 1) →
        xbar ≤ F xbar sbar →
        (∀ x ∈ Set.Icc xbar (1:ℝ), sbar ≤ g x) →
        ∀ x ∈ Set.Icc xbar (1:ℝ), xbar ≤ g x) := by
  intro h
  have hc : (1:ℝ)/2 ≤ flatTransition (1/2) 0 := le_rfl
  have := h flatTransition (fun _ => 0) (1/2) 0
    flatTransition_mem flatTransition_mono_x flatTransition_mono_s
    flatTransition_diag (fun _ => ⟨le_rfl, zero_le_one⟩) hc
    (fun _ _ => le_rfl) (1/2) ⟨le_rfl, by norm_num⟩
  norm_num at this


/-- **The weak floor evades the absorbing-boundary obstruction.**
`Sanctions.no_upper_basin_floor_of_top_lt_one` (`Foundations/Basic.lean:51`)
kills the *strong* ratchet floor on every basin as soon as `rule 1 < 1`.
The weak floor is not obstructed: a rule strictly below one at the top
can still clear a level floor `sbar` with `xbar ≤ sbar`. Witness:
`r ≡ 1/2`, `xbar = sbar = 1/2`, so `r 1 = 1/2 < 1`.

This is the structural reason the weak basin is the right home for the
shocked mechanism witness P3, for which `mwShockedOne_no_top_floor`
(`Examples/MechanismWitnessShockedDominance.lean:495`) proves
`¬ (1 ≤ rule 1)` at *every* equilibrium. -/
theorem weak_floor_alive_when_top_lt_one :
    ((fun _ : ℝ => (1:ℝ)/2) 1 < 1)
    ∧ ((1:ℝ)/2 ≤ (1:ℝ)/2)
    ∧ (∀ x ∈ Set.Icc ((1:ℝ)/2) 1, (1:ℝ)/2 ≤ (fun _ : ℝ => (1:ℝ)/2) x)
    ∧ ¬ (∀ x ∈ Set.Icc ((1:ℝ)/2) 1,
          max x ((1:ℝ)/2) ≤ (fun _ : ℝ => (1:ℝ)/2) x) :=
  ⟨by norm_num, le_rfl, fun _ _ => le_rfl,
   Sanctions.no_upper_basin_floor_of_top_lt_one (fun _ => (1:ℝ)/2)
     (by norm_num) (by norm_num)⟩

/-! ## Part 8 — Goal 2 (myopic dominance) is floor-free

`dynamicTopSanctions_ge_myopify_same_alpha`
(`JointPreferenceBasin.lean:844`) takes only `Monotone V_S`, a monotone
top rule **on all of `[0,1]`**, and a feasible start. It mentions no
basin and no floor, so it is untouched by the weakening. The wrapper
below records that fact; note that its `hTopMonoI` hypothesis is *not*
supplied by either basin structure, whose `top_rule_mono` field is only
`MonotoneOn … (Icc xbar 1)`. -/

/-- Goal 2 under the weak-floor basin: verbatim
`dynamicTopSanctions_ge_myopify_same_alpha`, showing the weak basin data
is not consumed.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** Stated over the affine paths of
`dynamicTopSanctions_ge_myopify_same_alpha` (`lockInPath`,
`dynamicTopLockInPath`), with no `hF` in the signature. General-`F` siblings,
which take no basin data at all: `dynamicTopSanctionsF_ge_realizedRule_same_alpha`
(`DifferentPolicyComparator.lean` §11) and its response-pair form in
`TwoSidedForwardLooking.lean` §10 (BH2.9, 2026-10-06). No weak-floor general-`F`
wrapper is added: it would only restate that sibling with an unused basin. -/
theorem weakFloorBasinTop_goal2_dominance
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (_hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hV : Monotone V_S)
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule V_S α) Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.myopify.lockInSanctions α x₀ n
            ≤ p.dynamicTopLockInSanctions V_S α x₀ n :=
  p.dynamicTopSanctions_ge_myopify_same_alpha hV hTopMonoI hx₀

/-! ## Part 9 — equilibrium-level headline (Rule-1 form)

Weak-floor counterpart of
`equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing`
(`JointPreferenceBasin.lean:1267`): the persistence conclusions hold along
the realized path of a *feedback Stackelberg equilibrium with the upper
dynamic selector*, so every strategic object is equilibrium-derived. The
`Monotone` conjunct of the strong headline is dropped (Part 6). -/

/-- **Weak-floor headline.** Along the realized general-`F` path of a
feedback Stackelberg equilibrium `E` started anywhere in the basin: the
state never leaves `[xbar, 1]`, the realized sanction never falls below
the floor `sbar`, and the leader's action is the argmax of the joint top
integrand at every path state. -/
theorem equilibriumTop_weakFloorBasinTopF_long_run
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop E.V_T E.V_S E.α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))) := by
  have h_path := WeakFloorBasinTop.pathF_mem_basin p hB hx₀
  refine ⟨h_path, WeakFloorBasinTop.sanctionsF_floor p hB hx₀, ?_⟩
  intro n
  exact E.α_opt_top _
    ⟨le_trans hB.xbar_nonneg (h_path n).1, (h_path n).2⟩


/-- **Returned to `Theory/` on 2026-08-22.** This statement is general: it
quantifies over *every* transition `F` that is monotone in each argument and
fixes the diagonal, and denies that a level floor forces a monotone sanction
path for all of them. The affine law appears only inside the proof, as the
witness that does the refuting (Rule 9C: the witness is how a negative claim is
discharged, not what the claim is about). Under Rule 22 it is therefore a
general-`F` result and belongs with the general theory, not with the affine
instance. -/
theorem weakFloor_ratchet_counterexample :
    ¬ (∀ (F : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (xbar sbar : ℝ),
        (∀ s, Monotone (fun x => F x s)) →
        (∀ x, Monotone (fun s => F x s)) →
        (∀ x, F x x = x) →
        xbar ≤ sbar →
        (∀ x ∈ Set.Icc xbar (1:ℝ), sbar ≤ g x) →
        ∀ x ∈ Set.Icc xbar (1:ℝ), x ≤ F x (g x)) := by
  intro h
  have hmx : ∀ s : ℝ, Monotone (fun x => AbstractGame.affineF (1/5) x s) := by
    intro s a b hab
    simp only [AbstractGame.affineF]
    nlinarith
  have hms : ∀ x : ℝ, Monotone (fun s => AbstractGame.affineF (1/5) x s) := by
    intro x a b hab
    simp only [AbstractGame.affineF]
    nlinarith
  have hdiag : ∀ x : ℝ, AbstractGame.affineF (1/5) x x = x := by
    intro x; simp only [AbstractGame.affineF]; ring
  have := h (AbstractGame.affineF (1/5)) (fun _ => 1/2) (1/2) (1/2)
    hmx hms hdiag le_rfl (fun _ _ => le_rfl) 1 ⟨by norm_num, le_rfl⟩
  norm_num [AbstractGame.affineF] at this

end Params
end AbstractGame

end

end Sanctions
