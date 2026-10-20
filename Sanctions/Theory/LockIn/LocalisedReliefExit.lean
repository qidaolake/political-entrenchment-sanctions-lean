/-
Sanctions/Theory/LockIn/LocalisedReliefExit.lean

**Relief exit needs zero sanctions to erode the state only above the basin**
(BH2.2, 2026-10-06; the relief mirror of round BB's `LocalisedShockEntry.lean`).

The relief-exit and post-relief-persistence theorems of `ReliefExit.lean` and
`ReliefPersistence.lean` take strict adjustment (F5) — two-sided, on the whole
feasible square — together with `0 < x̄` (and `x̄ ≤ 1`). Their proofs read F5
once, at the minimiser of the relief drift `x − F(x, 0)` on the compact basin
`[x̄, 1]`, and only its descent half at zero sanction. This file restates them
with the single hypothesis

  `hF_bot_post : ∀ x ∈ [x̄, 1], F(x, 0) < x`

("post-basin descent": a zero sanction strictly erodes every state at or above
the threshold) and nothing else about `F` beyond the `Params` fields. This is
the binder spelling already used by the exit-horizon comparison
`fullReliefExitHorizon_antitone_of_bottom_transition_le` (BG2.4).

What is proved:

* `pos_of_F_zero_lt_self`, `pos_of_postBasinDescent` — a threshold that zero
  sanction still erodes is strictly positive. So the side condition `0 < x̄`
  carried by the old lemmas is *derivable* and is not carried. The proof uses
  only `F_mem_uIcc` (monotonicity plus the diagonal).
* `postBasinDescent_of_strictAdjustment` — the direction of the weakening: F5
  with `0 < x̄` implies post-basin descent.
* the minimum-drift lemmas, the uniform exit horizon, strict exit one period
  later, the two post-relief persistence theorems, and the two-threshold
  regimes theorem, localised (the last also on the shock side, through
  `LocalisedShockEntry.lean`).

**The interval is closed**, as on the entry side: a continuous positive drift
on the compact `[x̄, 1]` has a positive minimum, whereas on `(x̄, 1]` the
infimum may be zero (a fixed point of `F(·, 0)` at `x̄`).

**`x̄ ≤ 1`.** The drift lemmas keep it: their conclusion names a minimiser in
`[x̄, 1]`, which is empty otherwise. The horizon and strict-exit theorems drop
it: for `x̄ > 1` every feasible relief path already lies below `x̄`. The
post-relief theorems keep it, because the low-basin invariance lemmas they
compose with take it.

Scope (Rule 9): universal statements over every `Params` and every threshold;
no witness is involved. The relief phase is exogenous, the project's Rule-1
transient-phase exception; nothing here says relief is chosen or optimal.

Rule 22: general in `F`. No affine law is used anywhere; `δ` is not read.

Rule 3: no new assumption. `hF_bot_post` is the descent half of F5, read on
`[x̄, 1]` only; F5 with `0 < x̄` implies it
(`postBasinDescent_of_strictAdjustment`), and every theorem below is a
weakening in hypotheses of the theorem it sits beside, as the `example`s at the
end re-derive. The same status as round BB's pre-basin ascent.
-/

import Sanctions.Theory.LockIn.ReliefPersistence
import Sanctions.Theory.LockIn.LocalisedShockEntry

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The threshold is positive -/

/-- **A state that zero sanction still erodes is strictly positive.** If
`F(x, 0) < x`, then `0 < x`. Otherwise `x ≤ 0`, and the successor `F(x, 0)` lies
between the current state `x` and the sanction `0` (`F_mem_uIcc`, from
monotonicity and the diagonal alone), so `x ≤ F(x, 0)` — a contradiction.
Mirror of `lt_one_of_lt_F_one`. General in `F`. -/
theorem pos_of_F_zero_lt_self {x : ℝ} (h : p.F x 0 < x) : 0 < x := by
  by_contra hle
  have hx0 : x ≤ 0 := not_lt.mp hle
  have hmem := p.F_mem_uIcc x 0
  rw [Set.uIcc_of_le hx0] at hmem
  linarith [hmem.1]

/-- **Post-basin descent puts the threshold above zero.** If `x̄ ≤ 1` and a zero
sanction strictly erodes every state of `[x̄, 1]`, then `0 < x̄`: apply
`pos_of_F_zero_lt_self` at `x̄` itself, which the closed interval contains.
This is why the localised theorems below carry no separate `0 < x̄`. General
in `F`. -/
theorem pos_of_postBasinDescent {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x) : 0 < xbar :=
  p.pos_of_F_zero_lt_self (hF_bot_post xbar ⟨le_rfl, hxbar_le⟩)

/-! ## Direction of the weakening -/

/-- **Strict adjustment (F5) implies post-basin descent** above any positive
threshold. F5 is two-sided and holds on the whole feasible square; post-basin
descent is its zero-sanction descent half (`StrictAdjustment.F_zero_lt_self`),
on `[x̄, 1]` only. General in `F`. -/
theorem postBasinDescent_of_strictAdjustment (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar_pos : 0 < xbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x :=
  fun _ hx => hAdj.F_zero_lt_self ⟨hxbar_pos.le.trans hx.1, hx.2⟩ (hxbar_pos.trans_le hx.1)

/-! ## Minimum relief drift, localised -/

/-- **The canonical minimum relief drift `η_R(x̄)` is positive and attained
under post-basin descent.** Localised sibling of
`fullReliefMinDrift_pos_attains_isMinOn`: continuity attains the minimum of
`x − F(x, 0)` on `[x̄, 1]` (`fullReliefMinDrift_attains_isMinOn`), and descent
at the minimiser makes it positive. Strict adjustment and `0 < x̄` are replaced
by descent on `[x̄, 1]`; `x̄ ≤ 1` stays, so that the interval is non-empty.
General in `F`. -/
theorem fullReliefMinDrift_pos_attains_isMinOn_of_postBasinDescent
    {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x) :
    0 < p.fullReliefMinDrift xbar ∧
      (∃ xmin ∈ Set.Icc xbar (1 : ℝ),
        p.fullReliefMinDrift xbar = p.fullReliefDrift xmin) ∧
      ∀ x ∈ Set.Icc xbar (1 : ℝ),
        p.fullReliefMinDrift xbar ≤ p.fullReliefDrift x := by
  obtain ⟨⟨xmin, hxmin, heq⟩, hmin⟩ := p.fullReliefMinDrift_attains_isMinOn hxbar_le
  refine ⟨?_, ⟨xmin, hxmin, heq⟩, hmin⟩
  rw [heq]
  have hlt := hF_bot_post xmin hxmin
  unfold fullReliefDrift
  linarith

/-- **Positive attained minimum relief drift from post-basin descent.**
Localised sibling of `fullReliefDrift_exists_pos_isMinOn`: there is an attained
minimum `η > 0` of the relief drift on `[x̄, 1]`. Strict adjustment and `0 < x̄`
are replaced by descent on `[x̄, 1]` (`0 < x̄` is derived,
`pos_of_postBasinDescent`). General in `F`. -/
theorem fullReliefDrift_exists_pos_isMinOn_of_postBasinDescent
    {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc xbar (1 : ℝ), η = p.fullReliefDrift xmin) ∧
      ∀ x ∈ Set.Icc xbar (1 : ℝ), η ≤ p.fullReliefDrift x := by
  obtain ⟨hpos, hattain, hmin⟩ :=
    p.fullReliefMinDrift_pos_attains_isMinOn_of_postBasinDescent hxbar_le hF_bot_post
  exact ⟨p.fullReliefMinDrift xbar, hpos, hattain, hmin⟩

/-! ## The exit horizon, localised -/

/-- **The canonical relief horizon guarantees exit under post-basin descent**
(thm:relief-exit, localised). Every feasible initial state is at or below `x̄`
after `fullReliefExitHorizon x̄ = ⌈(1 − x̄) / η_R(x̄)⌉` periods of imposed zero
sanction, and at every later relief date.

Localised sibling of
`reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment`: strict
adjustment (F5) and `x̄ ∈ (0, 1]` are replaced by descent at zero sanction on
`[x̄, 1]` alone. `0 < x̄` is derived; `x̄ ≤ 1` is not needed, since for `x̄ > 1`
every relief path from a feasible start already stays in `[0, 1] ⊆ [0, x̄]`.
The relief phase is exogenous (Rule 1's transient-phase exception). General
in `F`. -/
theorem reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent
    {xbar : ℝ} (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
      ∀ n ≥ p.fullReliefExitHorizon xbar,
        p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) xbar := by
  rcases le_or_gt xbar 1 with hxbar_le | hxbar_gt
  · obtain ⟨hη_pos, _, hη_min⟩ :=
      p.fullReliefMinDrift_pos_attains_isMinOn_of_postBasinDescent hxbar_le hF_bot_post
    exact p.reliefPathF_uniform_natCeil_exit_of_drift hη_pos hη_min
  · intro x₀ hx₀ n _
    have h := p.reliefPathF_mem_Icc hx₀.1 hx₀.2 n
    exact ⟨h.1, h.2.trans (hx₀.2.trans hxbar_gt.le)⟩

/-- **Strict relief exit under post-basin descent.** After
`fullReliefExitHorizon x̄ + 1` periods of imposed zero sanction every feasible
start is strictly below `x̄`, and stays strictly below at every later relief
date. Localised sibling of `reliefPathF_lt_of_fullReliefExitHorizon_succ`:
strict adjustment and `x̄ ∈ (0, 1]` are replaced by descent on `[x̄, 1]`. At the
threshold itself descent lowers the state; below it the relief step cannot
rise; for `x̄ > 1` the claim is immediate. General in `F`. -/
theorem reliefPathF_lt_of_fullReliefExitHorizon_succ_of_postBasinDescent
    {xbar : ℝ} (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
      ∀ n ≥ p.fullReliefExitHorizon xbar + 1, p.reliefPathF x₀ n < xbar := by
  intro x₀ hx₀ n hn
  rcases le_or_gt xbar 1 with hxbar_le | hxbar_gt
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m ≥ p.fullReliefExitHorizon xbar := by omega
    have hmem := p.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent hF_bot_post
      x₀ hx₀ m hm
    rw [reliefPathF_succ]
    rcases hmem.2.lt_or_eq with hlt | heq
    · exact lt_of_le_of_lt (p.reliefStepF_le_self hmem.1) hlt
    · have h := hF_bot_post (p.reliefPathF x₀ m) ⟨heq.ge, heq.le.trans hxbar_le⟩
      calc p.reliefStepF (p.reliefPathF x₀ m) = p.F (p.reliefPathF x₀ m) 0 := rfl
        _ < p.reliefPathF x₀ m := h
        _ = xbar := heq
  · have h := p.reliefPathF_mem_Icc hx₀.1 hx₀.2 n
    exact lt_of_le_of_lt (h.2.trans hx₀.2) hxbar_gt

/-! ## Post-relief persistence, localised (prop:post-relief-persistence) -/

/-- **Temporary relief, then permanent residence in the low basin, under
post-basin descent** (general in `F`). Conditional on the low-basin level
condition for the dynamic rule, from every feasible start the general-`F`
closed loop resumed after `fullReliefExitHorizon x̄` periods of imposed zero
sanction stays in `[0, x̄]` at every later date.

Localised sibling of `temporary_relief_post_relief_low_persistence_generalF`:
strict adjustment and `0 < x̄` are replaced by descent on `[x̄, 1]`; `x̄ ≤ 1`
stays (the low-basin invariance lemma takes it). -/
theorem temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α
          (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar)) n
        ∈ Set.Icc (0 : ℝ) xbar :=
  p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar_le h_level_low
    (p.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent hF_bot_post
      x₀ hx₀ _ (le_refl _))

/-- **Temporary relief, then a permanently non-increasing state, under
post-basin descent** (general in `F`). Localised sibling of
`temporary_relief_post_relief_anti_generalF`: strict adjustment and `0 < x̄`
are replaced by descent on `[x̄, 1]`; `x̄ ≤ 1` stays. -/
theorem temporary_relief_post_relief_anti_generalF_of_postBasinDescent
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p.F x 0 < x)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (p.dynamicTopLockInPathF V_S α
      (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar))) :=
  p.dynamicTopLockInPathF_anti_low V_S α hxbar_le h_level_low
    (p.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent hF_bot_post
      x₀ hx₀ _ (le_refl _))

/-! ## Two thresholds, both transitions localised -/

/-- **Two opposite-direction crossings with conditional persistence, one
dynamic rule, two thresholds, local transition conditions** (general in `F`).

For one dynamic rule satisfying the high level condition on `[x̄_H, 1]` and the
low level condition on `[0, x̄_L]`: a finite maximum-sanction episode puts the
state in `[x̄_H, 1]` and the general-`F` closed loop keeps it there; a finite
zero-sanction episode puts it in `[0, x̄_L]` and the same closed loop keeps it
there.

Localised sibling of `two_sided_regimes_generalF_of_thresholds`: strict
adjustment (F5), `x̄_L ∈ (0, 1]` and `x̄_H ∈ [0, 1)` are replaced by full-sanction
ascent on `[0, x̄_H]` with `0 ≤ x̄_H` (round BB's pre-basin ascent) and
zero-sanction descent on `[x̄_L, 1]` with `x̄_L ≤ 1`. The derived range bounds
`x̄_H < 1` and `0 < x̄_L` are not carried. The same scope caveats apply as for
the sibling: a conditional statement about which regions one rule preserves. -/
theorem two_sided_regimes_generalF_of_thresholds_of_localTransition
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xL xH sbar_hi sbar_low : ℝ}
    (hxL_le : xL ≤ 1) (hF_bot_post : ∀ x ∈ Set.Icc xL (1 : ℝ), p.F x 0 < x)
    (hxH_nn : 0 ≤ xH) (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xH, x < p.F x 1)
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
  refine ⟨?_, p.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent
    V_S α hxL_le hF_bot_post h_level_low hx₀⟩
  exact p.dynamicTopLockInPathF_mem_basin V_S α h_level_hi
    (p.shockPathF_uniform_fullShockEntryHorizon_of_preBasinAscent hxH_nn hF_top_pre
      x₀ hx₀ _ (le_refl _))

/-! ## Rule 13 — the old theorems are recovered

Each `example` re-derives a strict-adjustment theorem from its localised
sibling through `postBasinDescent_of_strictAdjustment` (and, on the shock side,
`preBasinAscent_of_strictAdjustment`), so the localisation removed no content. -/

example (hAdj : p.StrictAdjustment) {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ p.fullReliefExitHorizon xbar,
      p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) xbar :=
  p.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent
    (p.postBasinDescent_of_strictAdjustment hAdj hxbar.1)

example (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar_low : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1)
    (h_level_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α
          (p.reliefPathF x₀ (p.fullReliefExitHorizon xbar)) n
        ∈ Set.Icc (0 : ℝ) xbar :=
  p.temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent V_S α hxbar.2
    (p.postBasinDescent_of_strictAdjustment hAdj hxbar.1) h_level_low hx₀

example (hAdj : p.StrictAdjustment)
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
          ∈ Set.Icc (0 : ℝ) xL) :=
  p.two_sided_regimes_generalF_of_thresholds_of_localTransition V_S α hxL.2
    (p.postBasinDescent_of_strictAdjustment hAdj hxL.1) hxH.1
    (p.preBasinAscent_of_strictAdjustment hAdj hxH.2) h_level_hi h_level_low hx₀

/-! ## Rule 10 — axiom inventory -/

#print axioms Sanctions.AbstractGame.Params.fullReliefDrift_exists_pos_isMinOn_of_postBasinDescent
#print axioms
  Sanctions.AbstractGame.Params.reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent
#print axioms
  Sanctions.AbstractGame.Params.reliefPathF_lt_of_fullReliefExitHorizon_succ_of_postBasinDescent
#print axioms
  temporary_relief_post_relief_low_persistence_generalF_of_postBasinDescent
#print axioms
  Sanctions.AbstractGame.Params.temporary_relief_post_relief_anti_generalF_of_postBasinDescent
#print axioms
  Sanctions.AbstractGame.Params.two_sided_regimes_generalF_of_thresholds_of_localTransition

end Params
end AbstractGame
end Sanctions
