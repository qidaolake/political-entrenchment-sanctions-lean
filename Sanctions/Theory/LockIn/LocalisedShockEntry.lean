/-
Sanctions/Theory/LockIn/LocalisedShockEntry.lean

**Shock entry needs full sanction to lift the state only below the basin**
(round BB, 2026-09-28; doc 110 item R7, the localisation of `hF_top`).

The general-`F` shock-entry lemmas in `LockIn.lean` take either the global
full-sanction ascent condition

  `hF_top : ∀ x ∈ [0, 1), x < F(x, 1)`

or the whole two-sided strict-adjustment condition F5
(`StrictAdjustment`), and in addition a threshold `x̄ < 1`. The minimum-drift
lemmas read the condition only on the compact pre-basin interval `[0, x̄]`:
the minimum full-sanction drift `F(x, 1) − x` is taken over that interval, and
once the drift floor is known, entry is pure kinematics
(`shockPathF_uniform_natCeil_entry_of_drift`, which has no transition
hypothesis at all). The convergence-based entry lemmas
(`shockPathF_eventually_in_basin`, `shockPathF_uniform_eventually_in_basin`)
read `hF_top` at the limit of the shock path, which can lie anywhere in
`[x₀, 1)`; their siblings here are re-proved through the minimum-drift bound
instead. This file restates those lemmas with the single
hypothesis

  `hF_top_pre : ∀ x ∈ [0, x̄], x < F(x, 1)`

("pre-basin ascent": a full sanction strictly raises every state at or
below the threshold) and nothing else about `F` beyond the `Params` fields.

What is proved:

* `lt_one_of_lt_F_one`, `lt_one_of_preBasinAscent` — a threshold that full
  sanction still lifts lies strictly below one. So the side condition
  `x̄ < 1` carried by the old lemmas is *derivable* from the new hypothesis
  (together with `0 ≤ x̄`) and is not carried. The proof uses only
  `F_mem_uIcc` (monotonicity plus the diagonal).
* `preBasinAscent_of_hF_top`, `preBasinAscent_of_strictAdjustment` — the
  direction of the weakening: each old hypothesis set implies the new one.
* the minimum-drift lemmas and the uniform entry lemmas, localised.

**The interval is closed.** The proof needs ascent at `x̄` itself: a
continuous positive function on the compact `[0, x̄]` has a positive minimum,
whereas on the half-open `[0, x̄)` the infimum of the drift may be zero (a
fixed point of `F(·, 1)` at `x̄`), and the minimum-drift argument then gives
nothing.

**What is not localised.** `shockPathF_tendsto_one` (convergence of the shock
path to `1`) is left with the global `hF_top`. Its proof excludes every
interior fixed point of `F(·, 1)` on `[x₀, 1)`, and pre-basin ascent says
nothing about fixed points above `x̄`. Its conclusion is in fact false under
pre-basin ascent alone: `Examples/PreBasinAscentStrictness.lean`
(`plateauParams_shockPathF_not_tendsto_one`) exhibits a transition with
pre-basin ascent below `1/2` whose full-sanction path from `0` never exceeds
`3/4`. Only finite entry into `[x̄, 1]` is localised, and that is what every
persistence consumer uses; the same file shows finite entry at that economy
through the localised lemma (`plateauParams_uniform_entry`).

Scope (Rule 9): these are universal statements over every `Params` and
every threshold; no witness is involved. The shock phase is the project's
sole Rule-1 exception (an exogenously imposed full-sanction episode).

Rule 22: general in `F`. No affine law is used anywhere; `δ` is not read.

Rule 3: no new assumption. `hF_top_pre` is implied by `hF_top` together with
`x̄ < 1` (and hence by `StrictAdjustment` with `x̄ < 1`), as the two
`preBasinAscent_of_*` theorems below record; every new lemma is a weakening in
hypotheses of the lemma it sits beside. The weakening is proper:
`Examples/PreBasinAscentStrictness.lean`
(`exists_preBasinAscent_not_strictAdjustment`) exhibits an economy with
pre-basin ascent below `1/2` that fails both `hF_top` and F5.
-/

import Sanctions.Theory.LockIn.LockIn

namespace Sanctions

open Set Filter Topology

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The threshold lies below one -/

/-- **A state that full sanction still lifts lies strictly below one.**
If `x̄ < F(x̄, 1)`, then `x̄ < 1`. Otherwise `1 ≤ x̄`, and the successor
`F(x̄, 1)` lies between the current state `x̄` and the sanction `1`
(`F_mem_uIcc`, from monotonicity and the diagonal alone), so
`F(x̄, 1) ≤ x̄` — a contradiction. General in `F`. -/
theorem lt_one_of_lt_F_one {xbar : ℝ} (h : xbar < p.F xbar 1) : xbar < 1 := by
  by_contra hlt
  have hge : 1 ≤ xbar := not_lt.mp hlt
  have hmem := p.F_mem_uIcc xbar 1
  rw [Set.uIcc_of_ge hge] at hmem
  linarith [hmem.2]

/-- **Pre-basin ascent puts the threshold below one.** If `0 ≤ x̄` and a
full sanction strictly raises every state in `[0, x̄]`, then `x̄ < 1`: apply
`lt_one_of_lt_F_one` at `x̄` itself, which the closed interval contains.
This is why the localised theorems in this file and its consumers carry no
separate `x̄ < 1` hypothesis. General in `F`. -/
theorem lt_one_of_preBasinAscent {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) : xbar < 1 :=
  p.lt_one_of_lt_F_one (hF_top_pre xbar ⟨hxbar_nn, le_rfl⟩)

/-! ## Direction of the weakening -/

/-- **Global full-sanction ascent implies pre-basin ascent** below any
threshold `x̄ < 1`. This is the implication that makes every localised
theorem here a weakening of its `hF_top` sibling. General in `F`. -/
theorem preBasinAscent_of_hF_top
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1 :=
  fun x hx => hF_top x ⟨hx.1, lt_of_le_of_lt hx.2 hxbar_lt⟩

/-- **Strict adjustment (F5) implies pre-basin ascent** below any threshold
`x̄ < 1`. F5 is two-sided and holds on the whole feasible square; pre-basin
ascent is its full-sanction ascent half, on `[0, x̄]` only. General in `F`. -/
theorem preBasinAscent_of_strictAdjustment
    (hAdj : p.StrictAdjustment) {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1 :=
  p.preBasinAscent_of_hF_top hAdj.hF_top hxbar_lt

/-! ## Minimum drift, localised -/

/-- **Positive attained minimum drift from pre-basin ascent.** Localised
sibling of `fullShockDrift_exists_pos_isMinOn`: the drift `F(x, 1) − x` is
continuous, so it attains its minimum on the compact interval `[0, x̄]`, and
pre-basin ascent makes that minimum strictly positive.

Hypotheses, against the sibling: `StrictAdjustment` (two-sided, whole
square) and `x̄ ∈ [0, 1)` are replaced by `0 ≤ x̄` and ascent at full
sanction on `[0, x̄]` only — strictly weaker by
`preBasinAscent_of_strictAdjustment`. General in `F`. -/
theorem fullShockDrift_exists_pos_isMinOn_of_preBasinAscent
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar, η = p.fullShockDrift xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x := by
  have hcont : Continuous (p.fullShockDrift) := by
    have hpair : Continuous (fun x : ℝ => (x, (1 : ℝ))) := by fun_prop
    exact (p.F_continuous.comp hpair).sub continuous_id
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hxbar_nn) hcont.continuousOn
  refine ⟨p.fullShockDrift xmin, ?_, ⟨xmin, hxmin, rfl⟩, fun x hx => hmin hx⟩
  have hlt := hF_top_pre xmin hxmin
  unfold fullShockDrift
  linarith

/-- **The canonical minimum drift `η_F(x̄)` is positive and attained under
pre-basin ascent.** Localised sibling of `fullShockMinDrift_pos_attains_isMinOn`
(which takes `StrictAdjustment` and `x̄ ∈ [0, 1)`): the named infimum
`fullShockMinDrift x̄` equals the attained minimum. General in `F`. -/
theorem fullShockMinDrift_pos_attains_isMinOn_of_preBasinAscent
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) :
    0 < p.fullShockMinDrift xbar ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar,
        p.fullShockMinDrift xbar = p.fullShockDrift xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.fullShockMinDrift xbar ≤ p.fullShockDrift x := by
  obtain ⟨η, hη_pos, ⟨xmin, hxmin, hη_eq⟩, hη_min⟩ :=
    p.fullShockDrift_exists_pos_isMinOn_of_preBasinAscent hxbar_nn hF_top_pre
  have hRange_nonempty :
      (p.fullShockDrift '' Set.Icc (0 : ℝ) xbar).Nonempty :=
    ⟨p.fullShockDrift xmin, ⟨xmin, hxmin, rfl⟩⟩
  have hRange_bdd : BddBelow (p.fullShockDrift '' Set.Icc (0 : ℝ) xbar) := by
    refine ⟨η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hMin_le : p.fullShockMinDrift xbar ≤ η :=
    csInf_le hRange_bdd ⟨xmin, hxmin, hη_eq.symm⟩
  have hMin_ge : η ≤ p.fullShockMinDrift xbar := by
    apply le_csInf hRange_nonempty
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hMin_eq : p.fullShockMinDrift xbar = η := le_antisymm hMin_le hMin_ge
  refine ⟨hMin_eq ▸ hη_pos, ⟨xmin, hxmin, hMin_eq.trans hη_eq⟩, ?_⟩
  intro x hx
  rw [hMin_eq]
  exact hη_min x hx

/-! ## Uniform entry, localised -/

/-- **Quantitative uniform shock entry from pre-basin ascent (doc 110 R7(i)).**
Localised sibling of
`shockPathF_exists_min_drift_uniform_natCeil_bound_of_strictAdjustment`. There
is an attained minimum drift `η > 0` on `[0, x̄]`, and the duration
`⌈x̄ / η⌉₊` of imposed full sanction moves every feasible initial state into
the basin `[x̄, 1]`, where it stays at every later shock date.

Hypotheses, against the sibling: `StrictAdjustment` and `x̄ ∈ [0, 1)` become
`0 ≤ x̄` and ascent at full sanction on the closed pre-basin interval
`[0, x̄]` — strictly weaker (`preBasinAscent_of_strictAdjustment`); `x̄ < 1`
is recovered by `lt_one_of_preBasinAscent`. The shock is the Rule-1
exogenous-phase exception. General in `F`. -/
theorem shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar, η = p.fullShockDrift xmin) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x) ∧
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ Nat.ceil (xbar / η),
        p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  obtain ⟨η, hη_pos, hη_attains, hη⟩ :=
    p.fullShockDrift_exists_pos_isMinOn_of_preBasinAscent hxbar_nn hF_top_pre
  exact ⟨η, hη_pos, hη_attains, hη,
    p.shockPathF_uniform_natCeil_entry_of_drift hη_pos hη⟩

/-- **The canonical horizon `⌈x̄ / η_F(x̄)⌉` guarantees entry under pre-basin
ascent.** Localised sibling of
`shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment`: at the named
horizon `fullShockEntryHorizon x̄`, and at every later shock date, every
feasible initial state is in `[x̄, 1]`. Hypotheses `0 ≤ x̄` and pre-basin
ascent replace `StrictAdjustment` and `x̄ ∈ [0, 1)` (strictly weaker).
General in `F`. -/
theorem shockPathF_uniform_fullShockEntryHorizon_of_preBasinAscent
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
      ∀ n ≥ p.fullShockEntryHorizon xbar,
        p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  obtain ⟨hη_pos, _, hη_min⟩ :=
    p.fullShockMinDrift_pos_attains_isMinOn_of_preBasinAscent hxbar_nn hF_top_pre
  exact p.shockPathF_uniform_natCeil_entry_of_drift hη_pos hη_min

/-- **One finite shock duration enters the basin from every feasible start,
under pre-basin ascent alone.** Localised sibling of
`shockPathF_uniform_eventually_in_basin`, which takes the global `hF_top` and
`x̄ < 1`. Here the only transition hypothesis is ascent at full sanction on
`[0, x̄]`, and no sign or size condition on `x̄` is carried: for `x̄ < 0` the
claim is immediate (every path stays in `[x₀, 1] ⊆ [x̄, 1]`), and for
`0 ≤ x̄` it is the minimum-drift bound. So this is a weakening of the sibling
in every case (`preBasinAscent_of_hF_top`). General in `F`. -/
theorem shockPathF_uniform_eventually_in_basin_of_preBasinAscent
    {xbar : ℝ} (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) :
    ∃ N : ℕ, ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ N,
      p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  rcases lt_or_ge xbar 0 with hneg | hxbar_nn
  · refine ⟨0, fun x₀ hx₀ n _ => ?_⟩
    have h := p.shockPathF_mem_Icc hx₀.1 hx₀.2 n
    exact ⟨le_trans (le_of_lt hneg) (le_trans hx₀.1 h.1), h.2⟩
  · obtain ⟨η, -, -, -, hentry⟩ :=
      p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
        hxbar_nn hF_top_pre
    exact ⟨Nat.ceil (xbar / η), hentry⟩

/-- **Finite shock entry from one feasible start, under pre-basin ascent.**
Localised sibling of `shockPathF_eventually_in_basin` (global `hF_top` and
`x̄ < 1`). The sibling goes through convergence of the shock path to `1`
(`shockPathF_tendsto_one`), which uses the global `hF_top`; this proof goes
through the minimum-drift bound instead and never asks where the path
converges. General in `F`. -/
theorem shockPathF_eventually_in_basin_of_preBasinAscent
    {xbar : ℝ} (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1)
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ, ∀ n ≥ N, p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  obtain ⟨N, hN⟩ := p.shockPathF_uniform_eventually_in_basin_of_preBasinAscent hF_top_pre
  exact ⟨N, fun n hn => hN x₀ ⟨hx₀_nn, hx₀_le⟩ n hn⟩

/-! ## Rule-13 recovery checks

Each old lemma's statement follows from its localised sibling through the
implications above, so nothing is lost by citing the localised form. -/

example (hAdj : p.StrictAdjustment) {xbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar, η = p.fullShockDrift xmin) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x) ∧
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ Nat.ceil (xbar / η),
        p.shockPathF x₀ n ∈ Set.Icc xbar 1 :=
  p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent hxbar.1
    (p.preBasinAscent_of_strictAdjustment hAdj hxbar.2)

example (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∃ N : ℕ, ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ N,
      p.shockPathF x₀ n ∈ Set.Icc xbar 1 :=
  p.shockPathF_uniform_eventually_in_basin_of_preBasinAscent
    (p.preBasinAscent_of_hF_top hF_top hxbar_lt)

end Params
end AbstractGame

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.lt_one_of_lt_F_one
#print axioms Sanctions.AbstractGame.Params.lt_one_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.preBasinAscent_of_hF_top
#print axioms Sanctions.AbstractGame.Params.preBasinAscent_of_strictAdjustment
#print axioms Sanctions.AbstractGame.Params.fullShockDrift_exists_pos_isMinOn_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.fullShockMinDrift_pos_attains_isMinOn_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.shockPathF_uniform_fullShockEntryHorizon_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.shockPathF_uniform_eventually_in_basin_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.shockPathF_eventually_in_basin_of_preBasinAscent

end Sanctions
