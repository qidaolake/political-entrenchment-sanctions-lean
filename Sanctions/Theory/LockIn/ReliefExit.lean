/-
Sanctions/Theory/LockIn/ReliefExit.lean

**Exit from lock-in: the relief mirror of the shock-entry horizon.**

## The gap this closes

`LockIn.lean` builds the *entry* half of hysteresis: an exogenously imposed
maximum-sanction phase drives every feasible state into the high basin within
`fullShockEntryHorizon xbar = ⌈x̄ / η_F(x̄)⌉` periods, where `η_F(x̄)` is the
minimum drift `F(x,1) − x` below the threshold.

The *exit* half was missing, and its absence was asymmetric in an
uncomfortable way. What the tree already had on the exit side was an
**impossibility**: `Theory/LockIn/PostEntryNonTermination.lean` shows that
inside the basin the equilibrium never grants relief — the realized sanction
stays above the state that was inherited at entry, and the set of relief dates
is empty. So the model said sanctions cannot end *endogenously* and said
nothing at all about whether they can be ended *at all*.

This file supplies the missing possibility half, and the two together say
something sharper than either alone:

> The equilibrium never ends sanctions on its own. An outside institution can,
> and `fullReliefExitHorizon` is a duration of imposed relief that suffices —
> a ceiling, not a minimum: every longer phase also crosses, and nothing here
> says a shorter one cannot.

## Why no new assumption is needed (Rule 3)

`StrictAdjustment` is already two-sided:

    (∀ x s, s < x → F x s < x)   ∧   (∀ x s, x < s → x < F x s)

The entry theorem spends only the **second** conjunct (`self_lt_F_one`). The
first conjunct — sanctions strictly below the inherited state erode
entrenchment, `F_zero_lt_self`, the "zero-sanction descent (D0)" already named
in `Postulates/AbstractGame.lean` — has been sitting in the primitive surface
unspent since it was written. Everything below is that conjunct, plus the same
compactness argument the entry side already uses. No `Params` field, no new
hypothesis, no new `Prop`.

## Rule 1 — why an exogenous relief path is admissible

The relief phase is *not* chosen by either player: it is imposed from outside,
exactly as the sanction shock is. That is Rule 1's **sole exception** — a fixed
action path is admissible for a transient, externally-imposed phase, because
the utility-maximization criterion does not apply to periods in which neither
player is choosing. `reliefStepF x = F x 0` is such a phase and is labelled as
one.

## Scope — what this proves and what it does not (Rule 9A)

Proved: under strict adjustment, with `0 < x̄ < 1`, a sustained exogenous
full-relief phase of `⌈(1 − x̄) / η_R(x̄)⌉` periods drives **every** feasible
starting state to at or below `x̄`, and every longer phase does too.

**Not** proved, and no reader may infer:

* **that the state stays low after relief ends.** This file stops at the
  crossing. Post-relief behaviour is governed by the equilibrium closed loop and
  needs a low-basin absorption theorem, which is a separate result. Stating a
  finite exit and then implying permanence would be exactly the entry theorem's
  mirror-image over-claim.
* **that relief is optimal, or that any player would choose it.** It is
  exogenous by construction, and `PostEntryNonTermination.lean` proves the
  equilibrium would *not* choose it inside the basin.
* **that the entry and exit horizons are equal.** They are computed from
  different minima on different intervals (`η_F` on `[0, x̄]` from the top
  section `F(·,1)`; `η_R` on `[x̄, 1]` from the bottom section `F(·,0)`) and
  there is no reason for them to coincide. Their difference is an asymmetry
  between two *sufficient* duration certificates computed from different
  transition sections — not a measured width of anything, since neither
  horizon is a minimum — and asserting symmetry would need a theorem nobody
  has (wording corrected 2026-09-11, the reader's C05–C06).

## Rule 22

General in `F` throughout. Nothing below mentions `p.δ`, `affineF`, or any
functional form; the drift is read off `p.F` directly and the only structural
inputs are `F_mono_s`, `F_diag`, `F_mem`, `F_continuous`, and
`StrictAdjustment`. The affine instance is a specialization, not the statement.
-/

import Sanctions.Theory.LockIn.LockIn

namespace Sanctions

open Set Filter Topology

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The exogenous relief phase

The mirror of `shockStepF` / `shockPathF`: the sanction is held at its **floor**
rather than its ceiling, for an externally imposed number of periods. -/

/-- **One period of exogenously imposed full relief.** The sanction is forced to
zero, so next period's state is `F(x, 0)`. Exogenous, hence admissible under
Rule 1's transient-shock exception. -/
def reliefStepF (x : ℝ) : ℝ := p.F x 0

/-- **The one-period state loss under a forced zero sanction.** Positive
whenever the state is positive, by strict adjustment's below-diagonal
conjunct. This is the exit-side counterpart of `fullShockDrift`. -/
def fullReliefDrift (x : ℝ) : ℝ := x - p.F x 0

/-- **The relief path**: iterate the forced-zero-sanction step. -/
def reliefPathF (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.reliefStepF x)^[n] x₀

@[simp] theorem reliefPathF_zero (x₀ : ℝ) : p.reliefPathF x₀ 0 = x₀ := rfl

@[simp] theorem reliefPathF_succ (x₀ : ℝ) (n : ℕ) :
    p.reliefPathF x₀ (n + 1) = p.reliefStepF (p.reliefPathF x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- One relief step is weakly **below** the current state
(`F x 0 ≤ F x x = x`, since `0 ≤ x` and `F_mono_s` + `F_diag`). The exact
mirror of `shockStepF_ge_self`. -/
theorem reliefStepF_le_self {x : ℝ} (hx0 : 0 ≤ x) : p.reliefStepF x ≤ x := by
  have hmono : p.F x 0 ≤ p.F x x := p.F_mono_s x hx0
  rwa [p.F_diag x] at hmono

/-- One relief step from a feasible state stays feasible. -/
theorem reliefStepF_mem_Icc01 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    p.reliefStepF x ∈ Set.Icc (0 : ℝ) 1 :=
  p.F_mem x 0 hx ⟨le_refl _, zero_le_one⟩

/-- The relief path stays in `[0, x₀]` from any `x₀ ∈ [0, 1]` — it never rises
above where it started and never leaves the feasible interval. -/
theorem reliefPathF_mem_Icc {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∀ n, p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) x₀ := by
  intro n
  induction n with
  | zero => exact ⟨hx₀_nn, le_refl _⟩
  | succ n ih =>
    obtain ⟨ih_nn, ih_le⟩ := ih
    have hxn_mem : p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨ih_nn, le_trans ih_le hx₀_le⟩
    rw [reliefPathF_succ]
    exact ⟨(p.reliefStepF_mem_Icc01 hxn_mem).1,
           le_trans (p.reliefStepF_le_self ih_nn) ih_le⟩

/-- The relief path is feasible at every date. -/
theorem reliefPathF_mem_Icc01 {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∀ n, p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) 1 := by
  intro n
  obtain ⟨h1, h2⟩ := p.reliefPathF_mem_Icc hx₀_nn hx₀_le n
  exact ⟨h1, le_trans h2 hx₀_le⟩

/-- The relief path is non-increasing from `x₀ ∈ [0, 1]`. -/
theorem reliefPathF_antitone {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    Antitone (p.reliefPathF x₀) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [reliefPathF_succ]
  exact p.reliefStepF_le_self (p.reliefPathF_mem_Icc hx₀_nn hx₀_le n).1

/-- Relief paths preserve the order of their initial states. -/
theorem reliefPathF_mono_start {x₀ y₀ : ℝ} (hxy : x₀ ≤ y₀) :
    ∀ n, p.reliefPathF x₀ n ≤ p.reliefPathF y₀ n := by
  intro n
  induction n with
  | zero => exact hxy
  | succ n ih =>
    rw [reliefPathF_succ, reliefPathF_succ]
    exact p.F_mono_x 0 ih

/-! ## 2. The minimum relief drift above the threshold

Compactness plus strict adjustment, mirroring
`fullShockDrift_exists_pos_isMinOn`. Where the entry side needs `x̄ < 1` (so
that the top section can still move the state up), the exit side needs
`0 < x̄` (so that the bottom section can still move it down). -/

/-- **Canonical minimum full-relief drift above a basin threshold.** The
infimum of `x − F(x, 0)` over the compact basin `[x̄, 1]`. This is the exit-side
`η_R(x̄)`, the mirror of `fullShockMinDrift`. -/
noncomputable def fullReliefMinDrift (xbar : ℝ) : ℝ :=
  sInf (p.fullReliefDrift '' Set.Icc xbar (1 : ℝ))

/-- **Canonical conservative full-relief exit horizon**, `⌈(1 − x̄) / η_R(x̄)⌉`.
The worst case starts at full entrenchment `x = 1` and must fall the whole
distance to `x̄`. -/
noncomputable def fullReliefExitHorizon (xbar : ℝ) : ℕ :=
  Nat.ceil ((1 - xbar) / p.fullReliefMinDrift xbar)

/-- **Positive minimum relief drift above a basin threshold.** Under strict
adjustment, continuity makes `fullReliefDrift` attain its minimum on `[x̄, 1]`,
and the below-diagonal conjunct makes that minimum strictly positive when
`0 < x̄`. The witness `xmin` records that `η` is the actual minimum, not merely
an arbitrary positive lower bound. -/
theorem fullReliefDrift_exists_pos_isMinOn
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc xbar (1 : ℝ), η = p.fullReliefDrift xmin) ∧
      ∀ x ∈ Set.Icc xbar (1 : ℝ), η ≤ p.fullReliefDrift x := by
  have hcont : Continuous (p.fullReliefDrift) := by
    have hpair : Continuous (fun x : ℝ => (x, (0 : ℝ))) := by fun_prop
    exact continuous_id.sub (p.F_continuous.comp hpair)
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hxbar.2) hcont.continuousOn
  refine ⟨p.fullReliefDrift xmin, ?_, ⟨xmin, hxmin, rfl⟩, fun x hx => hmin hx⟩
  have hxmin_mem : xmin ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans (le_of_lt hxbar.1) hxmin.1, hxmin.2⟩
  have hxmin_pos : 0 < xmin := lt_of_lt_of_le hxbar.1 hxmin.1
  have hlt := hAdj.F_zero_lt_self hxmin_mem hxmin_pos
  dsimp [fullReliefDrift]
  linarith

/-- **The canonical minimum relief drift is positive and attained.** -/
theorem fullReliefMinDrift_pos_attains_isMinOn
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1) :
    0 < p.fullReliefMinDrift xbar ∧
      (∃ xmin ∈ Set.Icc xbar (1 : ℝ),
        p.fullReliefMinDrift xbar = p.fullReliefDrift xmin) ∧
      ∀ x ∈ Set.Icc xbar (1 : ℝ),
        p.fullReliefMinDrift xbar ≤ p.fullReliefDrift x := by
  obtain ⟨η, hη_pos, ⟨xmin, hxmin, hη_eq⟩, hη_min⟩ :=
    p.fullReliefDrift_exists_pos_isMinOn hAdj hxbar
  have hRange_nonempty : (p.fullReliefDrift '' Set.Icc xbar (1 : ℝ)).Nonempty :=
    ⟨p.fullReliefDrift xmin, ⟨xmin, hxmin, rfl⟩⟩
  have hRange_bdd : BddBelow (p.fullReliefDrift '' Set.Icc xbar (1 : ℝ)) := by
    refine ⟨η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hMin_le : p.fullReliefMinDrift xbar ≤ η :=
    csInf_le hRange_bdd ⟨xmin, hxmin, hη_eq.symm⟩
  have hMin_ge : η ≤ p.fullReliefMinDrift xbar := by
    apply le_csInf hRange_nonempty
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hMin_eq : p.fullReliefMinDrift xbar = η := le_antisymm hMin_le hMin_ge
  refine ⟨hMin_eq ▸ hη_pos, ⟨xmin, hxmin, hMin_eq.trans hη_eq⟩, ?_⟩
  intro x hx
  rw [hMin_eq]
  exact hη_min x hx

/-! ## 3. The finite exit horizon -/

/-- **Linear decay while the worst-case relief path remains above the
threshold.** If every state in the basin loses at least `η` under full relief,
then the relief path from full entrenchment has lost at least `n · η` after `n`
periods, provided its earlier iterates remain at or above `x̄`. Mirror of
`shockPathF_linear_lower_bound_before_basin`. -/
theorem reliefPathF_linear_upper_bound_before_exit
    {xbar η : ℝ}
    (hη : ∀ x ∈ Set.Icc xbar (1 : ℝ), η ≤ p.fullReliefDrift x) :
    ∀ n : ℕ, (∀ k < n, xbar ≤ p.reliefPathF 1 k) →
      p.reliefPathF 1 n ≤ 1 - (n : ℝ) * η := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hstay
    have hprev_mem : p.reliefPathF 1 n ∈ Set.Icc xbar (1 : ℝ) :=
      ⟨hstay n (Nat.lt_succ_self n),
        (p.reliefPathF_mem_Icc zero_le_one (le_refl 1) n).2⟩
    have hdrift := hη _ hprev_mem
    have hih : p.reliefPathF 1 n ≤ 1 - (n : ℝ) * η :=
      ih (fun k hk => hstay k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    rw [reliefPathF_succ]
    simp only [reliefStepF, Nat.cast_add, Nat.cast_one]
    unfold fullReliefDrift at hdrift
    linarith

/-- **Explicit general-`F` exit horizon from a drift floor.** If `η > 0` is a
lower bound for the full-relief drift on `[x̄, 1]`, then `⌈(1 − x̄) / η⌉₊` relief
periods bring every feasible initial state to at or below `x̄`. Every longer
imposed episode also works.

This is the exact mirror of `shockPathF_uniform_natCeil_entry_of_drift`. -/
theorem reliefPathF_uniform_natCeil_exit_of_drift
    {xbar η : ℝ} (hη_pos : 0 < η)
    (hη : ∀ x ∈ Set.Icc xbar (1 : ℝ), η ≤ p.fullReliefDrift x) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ Nat.ceil ((1 - xbar) / η),
      p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) xbar := by
  -- the worst case starts at full entrenchment
  have hone :
      p.reliefPathF 1 (Nat.ceil ((1 - xbar) / η)) ∈ Set.Icc (0 : ℝ) xbar := by
    set N := Nat.ceil ((1 - xbar) / η) with hN
    refine ⟨(p.reliefPathF_mem_Icc zero_le_one (le_refl 1) N).1, ?_⟩
    by_contra hnot
    have hlt : xbar < p.reliefPathF 1 N := lt_of_not_ge hnot
    have hanti := p.reliefPathF_antitone (zero_le_one) (le_refl (1 : ℝ))
    have hstay : ∀ k < N, xbar ≤ p.reliefPathF 1 k := by
      intro k hk
      exact le_trans (le_of_lt hlt) (hanti (Nat.le_of_lt hk))
    have hupper : p.reliefPathF 1 N ≤ 1 - (N : ℝ) * η :=
      p.reliefPathF_linear_upper_bound_before_exit hη N hstay
    have hceil : (1 : ℝ) - xbar ≤ (N : ℝ) * η := by
      have hratio : (1 - xbar) / η ≤ (N : ℝ) := by
        simpa [hN] using (Nat.le_ceil ((1 - xbar) / η))
      calc
        (1 : ℝ) - xbar = ((1 - xbar) / η) * η := by field_simp
        _ ≤ (N : ℝ) * η := mul_le_mul_of_nonneg_right hratio hη_pos.le
    linarith
  intro x₀ hx₀ n hn
  refine ⟨(p.reliefPathF_mem_Icc hx₀.1 hx₀.2 n).1, ?_⟩
  -- start no higher than 1, then run no shorter than the horizon
  exact le_trans
    (le_trans (p.reliefPathF_antitone hx₀.1 hx₀.2 hn)
      (p.reliefPathF_mono_start hx₀.2 (Nat.ceil ((1 - xbar) / η))))
    hone.2

/-- **The canonical general-`F` relief horizon uniformly guarantees exit.**
Under strict adjustment, every feasible initial state is at or below `x̄` after
`fullReliefExitHorizon p x̄ = ⌈(1 − x̄) / η_R(x̄)⌉` periods of imposed full
relief, and remains there at every later relief date.

Mirror of `shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment`.
Localised sibling (BH2.2, 2026-10-06):
`reliefPathF_uniform_fullReliefExitHorizon_of_postBasinDescent`
(`LocalisedReliefExit.lean`), which replaces strict adjustment and
`x̄ ∈ (0, 1]` by zero-sanction descent on `[x̄, 1]` alone. -/
theorem reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
      ∀ n ≥ p.fullReliefExitHorizon xbar,
        p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) xbar := by
  obtain ⟨hη_pos, _, hη_min⟩ :=
    p.fullReliefMinDrift_pos_attains_isMinOn hAdj hxbar
  exact p.reliefPathF_uniform_natCeil_exit_of_drift hη_pos hη_min

/-! ## 4. Two-sided hysteresis

Both horizons in one statement. This is the object doc 41 §9.3 called the
hysteresis width; read it as two sufficient duration certificates: the model
has an explicit finite ceiling on the cost of pushing the state *into* lock-in
and an explicit finite ceiling on the cost of pushing it back *out*, computed
from different sections of the same transition — `F(·,1)` below the
threshold, `F(·,0)` above it — so they do not generally coincide, and neither
is a minimum. -/

/-- **Two-sided hysteresis: explicit entry and exit horizons.**

Under strict adjustment, at any interior threshold `x̄`:

* `fullShockEntryHorizon x̄` periods of imposed **maximum** sanction move every
  feasible state into `[x̄, 1]`;
* `fullReliefExitHorizon x̄` periods of imposed **zero** sanction move every
  feasible state into `[0, x̄]`.

Both are explicit ceilings of a distance over an attained minimum drift. The
theorem asserts their existence and their form; it asserts **nothing** about
their relative size, which depends on the two sections of `F` and is the
model's hysteresis asymmetry. -/
theorem entry_and_exit_horizons_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ p.fullShockEntryHorizon xbar,
        p.shockPathF x₀ n ∈ Set.Icc xbar 1)
    ∧ (∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ p.fullReliefExitHorizon xbar,
        p.reliefPathF x₀ n ∈ Set.Icc (0 : ℝ) xbar) :=
  ⟨p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment hAdj
      ⟨le_of_lt hxbar.1, hxbar.2⟩,
   p.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj
      ⟨hxbar.1, le_of_lt hxbar.2⟩⟩

/-! ## 5. Rule 10 — axiom inventory -/

#print axioms Sanctions.AbstractGame.Params.fullReliefDrift_exists_pos_isMinOn
#print axioms Sanctions.AbstractGame.Params.reliefPathF_uniform_natCeil_exit_of_drift
#print axioms
  Sanctions.AbstractGame.Params.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment
/-! ## The exit-side comparative-statics instrument (Rule 16a)

The entry side compares two economies' *top* transitions
(`fullShockDrift_minima_horizon_strict_of_top_transition_lt`). The exit side
compares their *bottom* transitions: an economy whose zero-sanction transition
erodes entrenchment faster on `[x̄, 1]` has a strictly larger minimum relief
drift, and hence a weakly shorter conservative exit horizon — weakly, because
the ceiling is locally constant. Same hypotheses in kind as the entry side.
Since BG2.4 (2026-10-06) that means: continuity alone for attainment
(`fullReliefMinDrift_attains_isMinOn`, needing only `x̄ ≤ 1`), so the
named-minimum comparisons carry no adjustment hypothesis at all; and, only
where a positive drift is needed (the horizon), zero-sanction descent of the
*first* economy on `[x̄, 1]`, `F₁(x,0) < x`. Strict adjustment (F5) of both
economies and `0 < x̄` were dropped; F5 with `0 < x̄` implies the new
hypotheses (`StrictAdjustment.F_zero_lt_self`). General in `F`. -/

/-- **The canonical minimum relief drift is attained, with no adjustment
hypothesis.** Attainment helper for the comparisons below: the relief drift
`x − F(x,0)` is continuous, so on the compact non-empty interval `[x̄, 1]` it
attains its minimum, and the named infimum `fullReliefMinDrift x̄` equals that
minimum. Nothing about the sign of the drift is assumed. General in `F`
(BG2.4). -/
theorem fullReliefMinDrift_attains_isMinOn {xbar : ℝ} (hxbar_le : xbar ≤ 1) :
    (∃ xmin ∈ Set.Icc xbar (1 : ℝ),
        p.fullReliefMinDrift xbar = p.fullReliefDrift xmin) ∧
      ∀ x ∈ Set.Icc xbar (1 : ℝ), p.fullReliefMinDrift xbar ≤ p.fullReliefDrift x := by
  have hcont : Continuous (p.fullReliefDrift) := by
    have hpair : Continuous (fun x : ℝ => (x, (0 : ℝ))) := by fun_prop
    exact continuous_id.sub (p.F_continuous.comp hpair)
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hxbar_le) hcont.continuousOn
  have hleast : IsLeast (p.fullReliefDrift '' Set.Icc xbar (1 : ℝ))
      (p.fullReliefDrift xmin) :=
    ⟨⟨xmin, hxmin, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmin hx⟩
  have heq : p.fullReliefMinDrift xbar = p.fullReliefDrift xmin := hleast.csInf_eq
  refine ⟨⟨xmin, hxmin, heq⟩, fun x hx => ?_⟩
  rw [heq]
  exact hmin hx

/-- **Canonical minimum relief drift is monotone under bottom-transition
dominance.** If the second economy's zero-sanction transition is pointwise
lower on `[x̄, 1]`, its minimum relief drift is weakly larger.

General in `F`. Since BG2.4 (2026-10-06) no adjustment hypothesis at all: only
`x̄ ≤ 1`, so that both minima are attained; they need not be positive for the
comparison. Strict adjustment of both economies and `0 < x̄` were dropped. -/
theorem fullReliefMinDrift_mono_of_bottom_transition_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_le : ∀ x ∈ Set.Icc xbar (1 : ℝ), p₂.F x 0 ≤ p₁.F x 0) :
    p₁.fullReliefMinDrift xbar ≤ p₂.fullReliefMinDrift xbar := by
  obtain ⟨-, hmin₁⟩ := p₁.fullReliefMinDrift_attains_isMinOn hxbar_le
  obtain ⟨⟨xmin₂, hxmin₂, hmin₂_eq⟩, -⟩ := p₂.fullReliefMinDrift_attains_isMinOn hxbar_le
  calc
    p₁.fullReliefMinDrift xbar ≤ p₁.fullReliefDrift xmin₂ := hmin₁ xmin₂ hxmin₂
    _ ≤ p₂.fullReliefDrift xmin₂ := by
      unfold Params.fullReliefDrift
      linarith [hF_bot_le xmin₂ hxmin₂]
    _ = p₂.fullReliefMinDrift xbar := hmin₂_eq.symm

/-- **Strict bottom-transition dominance strictly raises the canonical minimum
relief drift.** The minimum for the faster-eroding transition is attained;
evaluating the slower one at that same minimiser gives the strict comparison.

General in `F`. Since BG2.4 (2026-10-06) no adjustment hypothesis at all: only
`x̄ ≤ 1`, for attainment. Strict adjustment of both economies and `0 < x̄`
were dropped. -/
theorem fullReliefMinDrift_strictMono_of_bottom_transition_lt
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hF_bot_lt : ∀ x ∈ Set.Icc xbar (1 : ℝ), p₂.F x 0 < p₁.F x 0) :
    p₁.fullReliefMinDrift xbar < p₂.fullReliefMinDrift xbar := by
  obtain ⟨-, hmin₁⟩ := p₁.fullReliefMinDrift_attains_isMinOn hxbar_le
  obtain ⟨⟨xmin₂, hxmin₂, hmin₂_eq⟩, -⟩ := p₂.fullReliefMinDrift_attains_isMinOn hxbar_le
  calc
    p₁.fullReliefMinDrift xbar ≤ p₁.fullReliefDrift xmin₂ := hmin₁ xmin₂ hxmin₂
    _ < p₂.fullReliefDrift xmin₂ := by
      unfold Params.fullReliefDrift
      linarith [hF_bot_lt xmin₂ hxmin₂]
    _ = p₂.fullReliefMinDrift xbar := hmin₂_eq.symm

/-- **A faster-eroding zero-sanction transition exits no later.** The
conservative full-relief exit horizon is antitone under bottom-transition
dominance: weakly, because the ceiling is locally constant. This is the
exit-side comparison instrument of Rule 16(a).

General in `F`. Since BG2.4 (2026-10-06): `x̄ ≤ 1` and zero-sanction descent
of the first economy on `[x̄, 1]` (`hF₁_bot_post`, which makes its minimum
relief drift positive so the ratio is meaningful) replace strict adjustment of
both economies and `x̄ ∈ (0,1]`. Descent forces `0 < x̄` by itself, since
`F(0,0) = 0`. -/
theorem fullReliefExitHorizon_antitone_of_bottom_transition_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hF₁_bot_post : ∀ x ∈ Set.Icc xbar (1 : ℝ), p₁.F x 0 < x)
    (hF_bot_le : ∀ x ∈ Set.Icc xbar (1 : ℝ), p₂.F x 0 ≤ p₁.F x 0) :
    p₂.fullReliefExitHorizon xbar ≤ p₁.fullReliefExitHorizon xbar := by
  obtain ⟨⟨xmin₁, hxmin₁, hmin₁_eq⟩, -⟩ := p₁.fullReliefMinDrift_attains_isMinOn hxbar_le
  have hη₁_pos : 0 < p₁.fullReliefMinDrift xbar := by
    rw [hmin₁_eq]
    unfold Params.fullReliefDrift
    linarith [hF₁_bot_post xmin₁ hxmin₁]
  have hη_le := fullReliefMinDrift_mono_of_bottom_transition_le p₁ p₂ hxbar_le hF_bot_le
  unfold Params.fullReliefExitHorizon
  exact Nat.ceil_mono (div_le_div_of_nonneg_left (by linarith) hη₁_pos hη_le)

/-! ## 6. Strict exit after one more period (round AB, 2026-09-19)

`reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment` delivers the
*weak* crossing `x_n ≤ x̄`. One more zero-sanction period makes it strict: below
`x̄` the relief step cannot rise, and at `x̄ > 0` strict adjustment lowers the
state. No new hypothesis; the episode is exogenous (Rule 1's transient
exception). What this does **not** buy: a low invariant basin, an optimal or
minimal duration, or any willingness of the equilibrium to grant relief. -/

/-- **Strict relief exit.** Under strict adjustment, after
`fullReliefExitHorizon x̄ + 1` periods of imposed zero sanctions every feasible
start is strictly below `x̄`, and stays strictly below at every later relief
date. Localised sibling (BH2.2):
`reliefPathF_lt_of_fullReliefExitHorizon_succ_of_postBasinDescent`
(`LocalisedReliefExit.lean`), zero-sanction descent on `[x̄, 1]` only. -/
theorem reliefPathF_lt_of_fullReliefExitHorizon_succ
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
      ∀ n ≥ p.fullReliefExitHorizon xbar + 1, p.reliefPathF x₀ n < xbar := by
  intro x₀ hx₀ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≥ p.fullReliefExitHorizon xbar := by omega
  have hmem := p.reliefPathF_uniform_fullReliefExitHorizon_of_strictAdjustment hAdj hxbar
    x₀ hx₀ m hm
  have hfeas : p.reliefPathF x₀ m ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hmem.1, le_trans hmem.2 hxbar.2⟩
  rw [reliefPathF_succ]
  rcases hmem.2.lt_or_eq with hlt | heq
  · exact lt_of_le_of_lt (p.reliefStepF_le_self hmem.1) hlt
  · have hpos : 0 < p.reliefPathF x₀ m := heq ▸ hxbar.1
    have h := hAdj.F_zero_lt_self hfeas hpos
    calc p.reliefStepF (p.reliefPathF x₀ m) = p.F (p.reliefPathF x₀ m) 0 := rfl
      _ < p.reliefPathF x₀ m := h
      _ = xbar := heq

#print axioms Sanctions.AbstractGame.Params.fullReliefExitHorizon_antitone_of_bottom_transition_le
#print axioms Sanctions.AbstractGame.Params.reliefPathF_lt_of_fullReliefExitHorizon_succ
#print axioms Sanctions.AbstractGame.Params.entry_and_exit_horizons_of_strictAdjustment

end Params
end AbstractGame
end Sanctions
