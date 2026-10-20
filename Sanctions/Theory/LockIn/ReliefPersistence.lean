/-
Sanctions/Theory/LockIn/ReliefPersistence.lean

**Relief exit composed with low-basin persistence — the full mirror of
shock-entry hysteresis.**

## What this closes

`ReliefExit.lean` proves an exogenously imposed zero-sanction phase of
`fullReliefExitHorizon x̄` periods drives every feasible state to at or below
`x̄`. Its header is explicit that it stops there: it says nothing about whether
the state *stays* below `x̄` once the episode ends, and warns that claiming
otherwise would reproduce the entry theorem's over-claim in mirror image.

That caveat is now discharged, and by machinery that was already in the tree.
`Theory/Certificates/StandardComplianceLowBasin.lean` — the Hassler-bistability
mirror — proves that once the state is inside the low basin the *equilibrium*
closed loop keeps it there (`dynamicTopLockInPath_mem_low_basin`), that the path
is non-increasing (`dynamicTopLockInPath_anti_low`), and that the sanction
sequence is bounded above (`dynamicTopLockInSanctions_ceiling_low`). Those need
a starting state in `[0, x̄]`, which is exactly what the relief horizon supplies.

The composition is the exit-side counterpart of
`temporary_shock_post_shock_persistence`. Read together the two say that the
threshold can be crossed in either direction by an imposed episode of
sufficient length, and that on each side a level condition makes the resumed
closed loop stay there:

* **entry** — a finite maximum-sanction episode moves the state into the high
  basin, after which a rule at or above `max x s̄_hi` there keeps it there;
* **exit** — a finite zero-sanction episode moves it back into the low basin,
  after which a rule at or below `min x s̄_low` there keeps it there.

That is two opposite-direction threshold crossings with conditional
persistence on each side. It is **not** a same-equilibrium hysteresis
theorem: the two level conditions are separate inputs, and nothing here shows
that one equilibrium rule satisfies both (docs 58/60, 2026-09-05).

## Why no new assumption (Rule 3)

Both inputs are existing results and both of their hypotheses are theorem
parameters, not `Params` fields:

* `hAdj : p.StrictAdjustment` — the paper's ordinal transition condition (F5),
  that sanctions below the inherited state strictly erode entrenchment and
  sanctions above it strictly build it. Already a `Params`-level predicate used
  throughout, and the relief side spends only its below-diagonal half.
* `h_level_low` — that on `[0, x̄]` the equilibrium's realized sanction rule
  sits at or below `min x s̄_low`, i.e. the equilibrium neither raises the
  sanction above the current state nor above the low ceiling. This is
  assumption **A2\*** of the low-basin module, a theorem-parameter input
  confirmed with the user in the Round-47 request, and the exact dual of the
  high-basin level condition `max x s̄ ≤ realizedRule α x` that
  `temporary_shock_post_shock_persistence` consumes.

Nothing here adds a field, a `Prop`, or a hypothesis of its own.

## Scope (Rule 9A)

What is proved: *conditional* on the low-basin level condition holding for the
equilibrium in question, a long enough imposed relief episode is followed by
permanent residence in `[0, x̄]`.

What is **not** proved, and must not be inferred:

* **that the level condition holds at any particular economy.** It is an input.
  The low-basin module supplies dischargers for it
  (`OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low`), but
  discharging it at a witness is separate work and is not done here.
* **that relief is optimal, or that anyone would choose it.** The episode is
  exogenous — Rule 1's transient-shock exception — and
  `PostEntryNonTermination.lean` proves the equilibrium would *not* choose it
  from inside the high basin.
* **that entry and exit are symmetric.** The two horizons come from different
  sections of the transition and are not claimed equal.

## Rule 22 — corrected 2026-09-05 (doc 58 §4)

**The three original theorems are affine on their post-episode leg.** The
relief *horizon* is general: `reliefPathF` iterates `p.F x 0`. But the
post-relief path `dynamicTopLockInPath` iterates
`dynamicTopLockInStep = (1 − δ)·x + δ·rule`, the affine law with the inert
`p.δ`, and the high leg of `two_sided_hysteresis` iterates `lockInPath`, which
is the affine law under the **stage** selector `realizedRule = σ`, not the
dynamic equilibrium rule. The header above previously said the low-basin
results "route through `p.F`"; they do not. That claim was wrong and is
withdrawn.

**The `_generalF` siblings below are general in `F`** on both legs: they
iterate `dynamicTopLockInPathF`, whose step is `p.F x (rule x)`, and take
one dynamic rule `dynamicTopRealizedRule V_S α` on both sides. The original
three are kept unchanged as the affine specialisation; `two_sided_hysteresis`
is a legacy mixed-definition template and must not be cited as a
general-transition or same-equilibrium result.
-/

import Sanctions.Theory.LockIn.ReliefExit
import Sanctions.Theory.Certificates.StandardComplianceLowBasin

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Temporary relief causes permanent low sanctions** (affine post-relief
leg).

The exit-side mirror of `temporary_shock_post_shock_persistence`. From *any*
feasible initial state, after `fullReliefExitHorizon x̄` periods of imposed zero
sanction, the closed loop stays in the low basin `[0, x̄]` at every subsequent
date.

**Rule 22.** The relief episode is general in `F`; the post-relief path
`dynamicTopLockInPath` is the affine law `(1 − δ)x + δ·rule`. The general-`F`
form is `temporary_relief_post_relief_low_persistence_generalF` below.

`h_level_low` is the low-basin level condition: on `[0, x̄]` the equilibrium's
realized sanction rule lies at or below `min x s̄_low`. -/
theorem temporary_relief_post_relief_low_persistence
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, p.dynamicTopLockInPath V_S α
          (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar)) n
        ∈ Set.Icc (0 : ℝ) xbar :=
  p.dynamicTopLockInPath_mem_low_basin V_S α h_level_low
    (p.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj hxbar
      x₀ hx₀ _ (le_refl _))

/-- **Temporary relief causes a permanently non-increasing state path**
(affine post-relief leg; general-`F` form `..._anti_generalF` below).

Strengthens the previous theorem with the low-basin anti-monotonicity: after the
relief episode the political state never rises again. -/
theorem temporary_relief_post_relief_anti
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (p.dynamicTopLockInPath V_S α
      (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar))) :=
  p.dynamicTopLockInPath_anti_low V_S α h_level_low
    (p.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj hxbar
      x₀ hx₀ _ (le_refl _))

/-- **Legacy mixed-definition template: two imposed episodes, two affine
post-episode regimes under two different rules.** Kept for its literal
content; not a general-transition theorem and not a same-equilibrium one.

At an interior threshold, under strict adjustment:

* a finite maximum-sanction episode (general `F`) puts the state in `[x̄, 1]`,
  after which the **affine, stage-selector** path `lockInPath α_hi` — the law
  `(1 − δ)x + δ·σ(x, α_hi x)` — keeps it there, given the level condition on
  the stage rule;
* a finite zero-sanction episode (general `F`) puts it in `[0, x̄]`, after
  which the **affine** dynamic path `dynamicTopLockInPath V_S α_lo` keeps it
  there, given the low level condition on the dynamic rule.

The high leg and the low leg use different rules, and neither leg uses `p.F`
after the episode. The corrected composition — one dynamic rule, `p.F` on
both legs — is `two_sided_regimes_generalF` below (doc 58 §4, doc 60 §6). -/
theorem two_sided_hysteresis
    (hAdj : p.StrictAdjustment)
    (α_hi : ℝ → ℝ) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α_lo : ℝ → ℝ)
    {xbar sbar_hi sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioo (0 : ℝ) 1)
    (h_level_hi : ∀ x ∈ Set.Icc xbar (1 : ℝ), max x sbar_hi ≤ p.realizedRule α_hi x)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α_lo x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, p.lockInPath α_hi
        (p.shockPathF x₀ (p.fullShockEntryHorizon xbar)) n ∈ Set.Icc xbar 1)
    ∧ (∀ n, p.dynamicTopLockInPath V_S α_lo
        (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar)) n
          ∈ Set.Icc (0 : ℝ) xbar) := by
  refine ⟨?_, p.temporary_relief_post_relief_low_persistence hAdj V_S α_lo
    ⟨hxbar.1, le_of_lt hxbar.2⟩ h_level_low hx₀⟩
  exact p.lockInPath_mem_basin α_hi h_level_hi
    (p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment hAdj
      ⟨le_of_lt hxbar.1, hxbar.2⟩ x₀ hx₀ _ (le_refl _))

/-! ## General-`F` siblings (2026-09-05, doc 58 §4)

Same episodes, but the post-episode path is `dynamicTopLockInPathF`, whose
step is `p.F x (rule x)`. The proofs consume the general-`F` low-basin lemmas
of `StandardComplianceLowBasin.lean` (`dynamicTopLockInPathF_mem_low_basin`,
`_anti_low`) and the general-`F` high-basin lemma of `DynamicTopLockIn.lean`
(`dynamicTopLockInPathF_mem_basin`), all of which already existed. No new
hypothesis: the level conditions are the same theorem parameters as before,
now imposed on one dynamic rule. -/

/-- **Temporary relief, then permanent residence in the low basin, general in
`F`.** Conditional on the low-basin level condition for the dynamic rule.
Localised sibling (BH2.2, 2026-10-06):
`temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent`
(`LocalisedReliefExit.lean`), with strict adjustment and `0 < x̄` replaced by
zero-sanction descent on `[x̄, 1]`. -/
theorem temporary_relief_post_relief_low_persistence_generalF
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α
          (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar)) n
        ∈ Set.Icc (0 : ℝ) xbar :=
  p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar.2 h_level_low
    (p.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj hxbar
      x₀ hx₀ _ (le_refl _))

/-- **Temporary relief, then a permanently non-increasing state, general in
`F`.** Localised sibling (BH2.2):
`temporary_relief_post_relief_anti_generalF_of_postBasinDescent`
(`LocalisedReliefExit.lean`). -/
theorem temporary_relief_post_relief_anti_generalF
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (p.dynamicTopLockInPathF V_S α
      (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar))) :=
  p.dynamicTopLockInPathF_anti_low V_S α hxbar.2 h_level_low
    (p.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj hxbar
      x₀ hx₀ _ (le_refl _))

/-- **Two opposite-direction crossings with conditional persistence, one
dynamic rule, general in `F`.**

At an interior threshold, under strict adjustment, for one dynamic rule
`dynamicTopRealizedRule V_S α` satisfying the high level condition on
`[x̄, 1]` and the low level condition on `[0, x̄]`:

* a finite maximum-sanction episode puts the state in `[x̄, 1]` and the
  general-`F` closed loop keeps it there;
* a finite zero-sanction episode puts it in `[0, x̄]` and the same closed loop
  keeps it there.

**Scope.** The two level conditions together force `rule x̄ = x̄` and
`s̄_hi ≤ x̄ ≤ s̄_low`; they are jointly satisfiable (the identity rule) but are
discharged at no equilibrium in this development. On the placable-Sender
family they cannot hold, since the high condition needs `rule 1 ≥ 1` and that
family's response is interior. This is a conditional statement about which
regions a rule preserves, not a theorem that the model exhibits two-sided
hysteresis. -/
theorem two_sided_regimes_generalF
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_hi sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioo (0 : ℝ) 1)
    (h_level_hi : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar_hi ≤ p.dynamicTopRealizedRule V_S α x)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α
        (p.shockPathF x₀ (p.fullShockEntryHorizon xbar)) n ∈ Set.Icc xbar 1)
    ∧ (∀ n, p.dynamicTopLockInPathF V_S α
        (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar)) n
          ∈ Set.Icc (0 : ℝ) xbar) := by
  refine ⟨?_, p.temporary_relief_post_relief_low_persistence_generalF hAdj V_S α
    ⟨hxbar.1, le_of_lt hxbar.2⟩ h_level_low hx₀⟩
  exact p.dynamicTopLockInPathF_mem_basin V_S α h_level_hi
    (p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment hAdj
      ⟨le_of_lt hxbar.1, hxbar.2⟩ x₀ hx₀ _ (le_refl _))

/-- **Two thresholds.** The same two crossings with a low region `[0, x̄_L]`
and a high region `[x̄_H, 1]` that may differ, so the two level conditions no
longer meet at a point. This is the form discharged at the dual-basin economy
(`Examples/DualBasinTwoSidedRegimes.lean`): one equilibrium whose rule is at
the top on `[19/20, 1]` and at zero on `[0, 1/10]`. Localised sibling (BH2.2,
2026-10-06): `two_sided_regimes_generalF_of_thresholds_of_localTransition`
(`LocalisedReliefExit.lean`), with strict adjustment replaced by full-sanction
ascent on `[0, x̄_H]` and zero-sanction descent on `[x̄_L, 1]`. -/
theorem two_sided_regimes_generalF_of_thresholds
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xL xH sbar_hi sbar_low : ℝ} (hxL : xL ∈ Set.Ioc (0 : ℝ) 1) (hxH : xH ∈ Set.Ico (0 : ℝ) 1)
    (h_level_hi : ∀ x ∈ Set.Icc xH (1 : ℝ),
        max x sbar_hi ≤ p.dynamicTopRealizedRule V_S α x)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xL,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α
        (p.shockPathF x₀ (p.fullShockEntryHorizon xH)) n ∈ Set.Icc xH 1)
    ∧ (∀ n, p.dynamicTopLockInPathF V_S α
        (p.reliefPathF x₀ (p.fullReliefExitHorizon xL)) n
          ∈ Set.Icc (0 : ℝ) xL) := by
  refine ⟨?_, p.temporary_relief_post_relief_low_persistence_generalF hAdj V_S α
    hxL h_level_low hx₀⟩
  exact p.dynamicTopLockInPathF_mem_basin V_S α h_level_hi
    (p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment hAdj hxH x₀ hx₀ _ (le_refl _))

/-! ## Rule 10 — axiom inventory -/

#print axioms Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence
#print axioms Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti
#print axioms Sanctions.AbstractGame.Params.two_sided_hysteresis
#print axioms Sanctions.AbstractGame.Params.temporary_relief_post_relief_low_persistence_generalF
#print axioms Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF
#print axioms Sanctions.AbstractGame.Params.two_sided_regimes_generalF
#print axioms Sanctions.AbstractGame.Params.two_sided_regimes_generalF_of_thresholds

end Params
end AbstractGame
end Sanctions
