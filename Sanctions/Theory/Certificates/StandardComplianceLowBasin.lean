/-
Sanctions/Theory/Certificates/StandardComplianceLowBasin.lean

**Hassler-bistability mirror: dual structural infrastructure for the
low-political absorbing basin.**

This module supplies the dual structural predicates and single-crossing
lemmas for the proposed `Theorem 4 (Low political absorbing basin)`,
the sanctions analogue of the absorbing equilibrium in
\citet{HasslerEtAl2003}. The headline theorem
`standardCompliance_three_goals_local_low_basin` consumes this module's
`OneSidedSanctionLowBasinPreferenceThresholds` Prop and is delivered
in a follow-up round.

## Economic content (plain English)

From any starting state `x_0` in a low political basin `B* = [0, x̄*]`,
the upper-dynamic feedback Stackelberg equilibrium produces:

1. **State invariance.** `x^E_t ∈ B*` for every `t ≥ 0`.
2. **Sanction ceiling.** `s^E_t ≤ min(x_0, x̄*)` for every `t ≥ 0`.
3. **Sanction monotonicity.** `s^E_{t+1} ≤ s^E_t` (non-increasing).
4. **Bellman optimality.** `α` is Bellman-optimal on the path.

This is the **mirror image** of `Theorem 1 (persistence)` for the
high political basin. The model is bistable: from low political starts
the system locks into permanent low sanctions; from high political
starts the system locks into permanent high sanctions.

Round BB (2026-09-28): row 3's four conclusions (state invariance, the
two sanction ceilings, monotonicity) do not use the Target's side
(`target_dislikes_high_sanctions`). The Sender-only sibling
`standardCompliance_low_basin_generalF_of_sender_level`
(`Basin/SenderPersistenceLow.lean`) drops it; see the Target-side note below.

## Dual structural assumptions

The joint route to the mirror theorem reads the dual one-sided thresholds
`OneSidedSanctionLowBasinPreferenceThresholds` (§3). They bundle two
sign-reversed analogues of `Assumption 1` and `Assumption 2` on the high
basin:

* **Sender side (`sender_dislikes_above_threshold`).** At every state
  `x ∈ [0, x̄*]`, the Sender's forward-looking objective is strictly
  decreasing in `s` on the upper-sanction range `[min(x, x̄*), 1]`.
  In plain English: at low hardliner influence there is no domestic
  political constituency demanding harshness, so the Sender gains by
  lifting sanctions, not imposing them. The shipped discharge is
  `of_stage_preferences_low` (§3) and its `sbar_star`-default form (§3a).
  The paper states this condition as A1_ε at the low orientation
  `ε = −1` (`thm:lowbasin`).

* **Target side (`target_dislikes_high_sanctions`).** At every state
  `x ∈ [0, x̄*]`, the Target's forward-looking sanction payoff is
  non-increasing in `s` on the same range. In plain English: lower
  sanctions today raise both the Target's stage payoff and its
  discounted continuation value (the Target incumbent in the low-basin
  equilibrium values low-hardliner continuation states).
  Round BB (2026-09-28): row 3's conclusions do not read it. On the joint
  route it only fills the Target field of `JointPreferenceBasinLow`, and
  the path lemmas never read that field. The Sender-only sibling
  `standardCompliance_low_basin_generalF_of_sender_level`
  (`Basin/SenderPersistenceLow.lean`) drops it, and the paper's
  `thm:lowbasin` reads no Target condition at `ε = −1` (its A2_{+1} is
  the high orientation's Target condition only).

* **A3 — strict concavity of `U_S` in `s`.** Not a hypothesis of the
  low-basin theorems in this file: neither the bundle nor any theorem
  here reads it. Earlier drafts listed it as shared with `Theorem 1`'s
  assumption surface (a sign-symmetric regularity condition giving Sender
  stage argmax uniqueness); the top selector `σ_dyn_top` picks the
  greatest maximiser, so uniqueness is not needed here.

Round BG (2026-10-06): the two chord-form anchors that carried the
paper's former A1*/A2* names, `SenderLowBasinStrictSlopeWedge` and
`TargetLowBasinCombinedChordOn`, had no consumers and were deleted (§2).

The dual `V_T, V_S` are anti-monotone (decreasing in `x`) in the
low-basin equilibrium, mirroring the monotone-increasing `V_T, V_S`
of the high-basin equilibrium. The dual single-crossing lemmas below
deliver dynamic-objective anti-monotonicity from these dual
primitives.

## Rule compliance

**Rule 1 (optimal strategies).** All dual objects are equilibrium-
derived. `σ_dyn_top` is the equilibrium Sender response (same selector
convention as the high-basin theorem); the dual hypotheses pin down
its location on the low basin.

**Rule 3 (assumption surface).** The dual hypotheses (the two
preference fields of `OneSidedSanctionLowBasinPreferenceThresholds`) are
theorem-parameter inputs (not new `Params` fields). User-confirmed in
the Round 47 confirmation request. Same epistemic shape as `Theorem 1`'s
hypotheses A1, A2.

**Rule 5 (parametric form).** All declarations parametric over
abstract `(V_T, V_S, α, xT_star, xS_star, sbar_star)`; no witness-
specific specialisation.

**Rule 8 (English paraphrases).** Module header + per-section
descriptions explain every introduced object in plain English.

**Rule 10 (axiom hygiene).** All declarations in this module are
expected to be axiom-clean (`propext, Classical.choice, Quot.sound`),
verified post-build.

**Rule 11 (no verdict without artifact).** The Round-47 delivery of
this module was structural prerequisites only; the headline theorem
has since SHIPPED. `standardCompliance_three_goals_local_low_basin`
(below, ~line 830) is now a compiled, axiom-clean, drift-fenced
headline-snapshot row, and its non-vacuity is discharged by the green
witness `lbLow_generalF_three_goals`
(`Sanctions/Examples/LowBasinCertWitness.lean`, 2026-07-03): a dovish
economy with a non-affine transition inhabiting the low-basin mirror
certificate. The paper §4 Theorem 4 is therefore fully machine-checked,
not "in progress".
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions

open BoundedContinuousFunction

namespace AbstractGame
namespace Params

variable (p : Params)

/-! ## §1 Dual single-crossing lemmas

Mirror of `senderDynObjective_strictMono_of_stage_strictMono_and_V_mono`
and `targetSanctionObjective_mono_of_stage_mono_and_V_mono` from
`JointPreferenceBasin.lean`. Stage-level strict-anti / monotone-anti +
anti-monotone continuation values implies dynamic-objective
strict-anti / monotone-anti. The transition `F(x, ·)` is monotone in
`s` (since `δ > 0`); composing with an anti-monotone `V_S` gives an
anti-monotone continuation; adding to the strict-anti stage payoff
preserves strict-anti. -/

/-- **Bridge (Sender, low-basin dual).** Sign-mirror of
`senderDynObjective_strictMono_of_stage_strictMono_and_V_mono`. If the
stage Sender payoff `U_S(x, α(x), ·)` is strict-anti (strictly
*decreasing*) in `s` on `[min(x, sbar_star), 1]` and the Sender
continuation value `V_S` is anti-monotone (decreasing on `↥S`), then
the forward-looking Sender dynamic objective is strict-anti in `s` on
the same interval.

Plain English: on the low political basin, raising the sanction
strictly worsens the Sender (stage hurt + lower continuation value),
so the Sender's forward-looking objective is strict-anti. -/
theorem senderDynObjective_strictAntiOn_of_stage_strictAntiOn_and_V_antiMono
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_S_anti : Antitone V_S)
    {α : ℝ → ℝ} {x sbar_star : ℝ}
    (h_stage_anti :
      StrictAntiOn (fun s => p.U_S x (α x) s)
        (Set.Icc (min x sbar_star) (1 : ℝ))) :
    StrictAntiOn (fun s => p.senderDynObjective V_S x (α x) s)
                 (Set.Icc (min x sbar_star) (1 : ℝ)) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  change p.U_S x (α x) s₂ + p.β_S * V_S
          (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (α x) s₁ + p.β_S * V_S
          (Sanctions.clipS' (p.F x s₁))
  have h_stage_gt : p.U_S x (α x) s₂ < p.U_S x (α x) s₁ :=
    h_stage_anti hs₁ hs₂ hlt
  have h_F_le : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hlt.le
  have h_clip_le : Sanctions.clipS' (p.F x s₁)
                    ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono h_F_le
  -- V_S anti: V_S(clip s₂) ≤ V_S(clip s₁)
  have h_V_le := h_V_S_anti h_clip_le
  have hβ_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have h_βV_le := mul_le_mul_of_nonneg_left h_V_le hβ_nn
  linarith

/-- **Bridge (Target, low-basin dual).** Sign-mirror of
`targetSanctionObjective_mono_of_stage_mono_and_V_mono`. If the stage
Target payoff `U_T(x, α(x), ·)` is monotone non-increasing in `s` on
`[min(x, sbar_star), 1]` and the Target continuation value `V_T` is
anti-monotone, then the forward-looking Target sanction payoff is
monotone non-increasing in `s` on the same interval.

Plain English: on the low political basin, raising the sanction
weakly worsens the Target (stage harm or zero + lower continuation
value), so the Target's forward-looking objective is anti-monotone. -/
theorem targetSanctionObjective_antiOn_of_stage_anti_and_V_T_antiMono
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_T_anti : Antitone V_T)
    {α : ℝ → ℝ} {x sbar_star : ℝ}
    (h_stage_anti :
      AntitoneOn (fun s => p.U_T x (α x) s)
        (Set.Icc (min x sbar_star) (1 : ℝ))) :
    AntitoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
               (Set.Icc (min x sbar_star) (1 : ℝ)) := by
  intro s₁ hs₁ s₂ hs₂ hle
  change p.U_T x (α x) s₂ + p.β_T * V_T
          (Sanctions.clipS' (p.F x s₂))
          ≤ p.U_T x (α x) s₁ + p.β_T * V_T
          (Sanctions.clipS' (p.F x s₁))
  have h_stage_ge := h_stage_anti hs₁ hs₂ hle
  have h_F_le : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hle
  have h_clip_le := Sanctions.clipS'_mono h_F_le
  have h_V_le := h_V_T_anti h_clip_le
  have hβ_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_βV_le := mul_le_mul_of_nonneg_left h_V_le hβ_nn
  linarith

/-! ## §2 Dual structural predicates (retired)

Round BG (2026-10-06): this section held two chord-form statement
anchors for the paper's former A1*/A2* names, the Sender low-basin
strict-slope wedge `SenderLowBasinStrictSlopeWedge` and the Target
low-basin combined chord `TargetLowBasinCombinedChordOn`. Both had zero
consumers: the shipped low-basin route goes through
`of_stage_preferences_low` (§3), and the paper now states the low basin
as `thm:lowbasin` with A1_ε at `ε = −1` and no Target condition (A2_{+1}
belongs to the high orientation). Both were deleted. The wedge also read
the inert slot `p.δ` as a contraction rate, which has no meaning for a
general transition; it is not restated with a chord rate. The section
number is kept so that the §3–§13 references stay valid. -/

/-! ## §3 Dual `OneSidedSanctionLowBasinPreferenceThresholds`

Sign-mirror of `OneSidedSanctionPreferenceThresholds` from
`JointPreferenceBasin.lean`. The Sender prefers LOW sanctions
on the low basin's upper-sanction range; the Target prefers LOW
sanctions on the low basin's upper-sanction range. -/

/-- **Dual one-sided thresholds (low basin).** Sign-mirror of
`OneSidedSanctionPreferenceThresholds`. Bundles:

* `xT_star_mem, sbar_star_mem` — basin geometry. (Round BJ1.5, 2026-10-07,
  author-approved re-pin of the two contract rows: the field
  `xS_star_mem : xS_star ∈ I` is deleted. No theorem read it: the low basin is
  `[0, min xT_star xS_star]`, whose ceiling is feasible by `xT_star_mem` alone,
  and the Sender field below only quantifies over `[0, xS_star]`.)
* `sender_dislikes_above_threshold` — the Sender's forward-looking
  objective is strict-anti (strictly decreasing) in `s` on the
  upper-sanction range `[min(x, sbar_star), 1]`, for every basin
  state `x ∈ [0, xS_star]`.
* `target_dislikes_high_sanctions` — the Target's forward-looking
  sanction payoff is monotone anti (non-increasing) in `s` on
  `[min(x, sbar_star), 1]`, at every basin state `x ∈ [0, xT_star]`.

Plain English: at every low-basin state, both players' dynamic
objectives are dominated by *lower* sanctions on the relevant
upper-sanction range. The dynamic equilibrium then places
`σ_dyn_top` in `[0, min(x, sbar_star)]`, the low-sanction range. -/
structure OneSidedSanctionLowBasinPreferenceThresholds
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xT_star xS_star sbar_star : ℝ) : Prop where
  xT_star_mem : xT_star ∈ Sanctions.I
  sbar_star_mem : sbar_star ∈ Sanctions.I

  /-- Sender's forward-looking objective is strict-anti (strictly
  decreasing) in `s` on the upper-sanction range, at every Sender
  low-basin state. -/
  sender_dislikes_above_threshold :
    ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
      StrictAntiOn (fun s => p.senderDynObjective V_S x (α x) s)
        (Set.Icc (min x sbar_star) (1 : ℝ))

  /-- Target's forward-looking sanction payoff is monotone anti
  (non-increasing) in `s` on the upper-sanction range, at every
  Target low-basin state. -/
  target_dislikes_high_sanctions :
    ∀ x ∈ Set.Icc (0 : ℝ) xT_star,
      AntitoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
        (Set.Icc (min x sbar_star) (1 : ℝ))

/-- **Bridge constructor: dual one-sided thresholds from stage
preferences.** Sign-mirror of
`OneSidedSanctionPreferenceThresholds.of_stage_preferences`. Builds
`OneSidedSanctionLowBasinPreferenceThresholds` from stage-level
anti-monotone preferences plus anti-monotone continuation values,
using the dual single-crossing lemmas from §1.

Round BJ1.5 (2026-10-07): the binder `xS_star ∈ I` is dropped together with
the structure field it filled, which nothing read. General in `F`: the
transition enters only through the continuation values. -/
theorem OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_T_anti : Antitone V_T) (h_V_S_anti : Antitone V_S)
    {α : ℝ → ℝ} {xT_star xS_star sbar_star : ℝ}
    (hxT_star_mem : xT_star ∈ Sanctions.I)
    (hsbar_star_mem : sbar_star ∈ Sanctions.I)
    (h_stage_sender_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
        StrictAntiOn (fun s => p.U_S x (α x) s)
          (Set.Icc (min x sbar_star) (1 : ℝ)))
    (h_stage_target_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xT_star,
        AntitoneOn (fun s => p.U_T x (α x) s)
          (Set.Icc (min x sbar_star) (1 : ℝ))) :
    p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α xT_star
        xS_star sbar_star where
  xT_star_mem := hxT_star_mem
  sbar_star_mem := hsbar_star_mem
  sender_dislikes_above_threshold := fun x hx =>
    p.senderDynObjective_strictAntiOn_of_stage_strictAntiOn_and_V_antiMono
      h_V_S_anti (h_stage_sender_low x hx)
  target_dislikes_high_sanctions := fun x hx =>
    p.targetSanctionObjective_antiOn_of_stage_anti_and_V_T_antiMono
      h_V_T_anti (h_stage_target_low x hx)

/-! ## §3a Round 1.8 — canonical `sbar_star`-default low-basin constructor

Sign-mirror of the high-basin R43 `s̄`-default constructor
`StandardComplianceLocalCoreCertificate.with_strict_slope_wedge_canonical_sbar_default`.
On the low basin, the natural pivot for the sanction-range pivot
`sbar_star` is the joint low pivot `min(xT_star, xS_star)` (the
right-endpoint of the low basin). Under this default the upper-
sanction range `[min(x, sbar_star), 1]` simplifies to
`[x, 1]` for every basin state `x ∈ [0, min(xT_star, xS_star)]`,
mirroring the high-basin simplification `[max(x, sbar), 1] = [x, 1]`.

Plain English: the canonical low-basin sanction-range pivot is the
basin ceiling itself. Naming `s̄_*` separately from `x̄_* :=
min(xT_star, xS_star)` adds a redundant scalar to the paper-facing
surface; defaulting `sbar_star := min(xT_star, xS_star)` removes
it. This is the symmetric counterpart of R43 Phase A on the high
basin.

## Rule compliance
* Rule 3 symbol-economy: `sbar_star` is identified with the existing
  primitive `min(xT_star, xS_star)` at the canonical default; no new
  modeling content. Mirrors R43.
* Rule 5: parametric.
* Rule 8: human-language paraphrase here. -/

/-- **Round 1.8 (low basin) — `sbar_star`-default smart constructor.**

    Builds `OneSidedSanctionLowBasinPreferenceThresholds` defaulting
    `sbar_star := min(xT_star, xS_star)`. The user no longer supplies
    a separate `sbar_star`; the upper-sanction range becomes
    `[x, 1]` for every basin state `x ∈ [0, min(xT_star, xS_star)]`
    (the basin ceiling itself), mirroring the high-basin canonical
    range `[x, 1]` on `x ∈ [max(xT, xS), 1]`.

    Composes with the existing
    `of_stage_preferences_low` constructor by defaulting the third
    sanction-pivot argument; the strict-anti and antitone hypotheses
    are then supplied on `[x, 1]` directly.

    Round BJ1.5 (2026-10-07): the second pivot now needs only
    `0 ≤ xS_star` (weakened from `xS_star ∈ I`). That is all the default
    pivot `min xT_star xS_star` needs to be feasible, since its upper bound
    comes from `xT_star ≤ 1`. General in `F`. -/
theorem
    OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low_canonical_default
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_T_anti : Antitone V_T) (h_V_S_anti : Antitone V_S)
    {α : ℝ → ℝ} {xT_star xS_star : ℝ}
    (hxT_star_mem : xT_star ∈ Sanctions.I)
    (hxS_star_nn : 0 ≤ xS_star)
    (h_stage_sender_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
        StrictAntiOn (fun s => p.U_S x (α x) s)
          (Set.Icc (min x (min xT_star xS_star)) (1 : ℝ)))
    (h_stage_target_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xT_star,
        AntitoneOn (fun s => p.U_T x (α x) s)
          (Set.Icc (min x (min xT_star xS_star)) (1 : ℝ))) :
    p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α xT_star
        xS_star (min xT_star xS_star) :=
  have hsbar_star_mem : (min xT_star xS_star) ∈ Sanctions.I :=
    ⟨le_min hxT_star_mem.1 hxS_star_nn,
     le_trans (min_le_left _ _) hxT_star_mem.2⟩
  OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low
    p h_V_T_anti h_V_S_anti
    hxT_star_mem hsbar_star_mem
    h_stage_sender_low h_stage_target_low

/-! ## §4 Dual top-selector level condition

The high-basin chain uses
`max x sbar ≤ σ_dyn_top V_S x (α x)`
as its load-bearing "level condition" (every dynamic Sender maximiser
on the high basin sits at least at the threshold `max x sbar`). The
dual condition for the low basin is the sign-mirror

  `σ_dyn_top V_S x (α x) ≤ min x sbar_star`

— every dynamic Sender maximiser on the low basin sits at most at the
threshold `min x sbar_star`. Discharger below: strict-anti dynamic
objective on `[min x sbar_star, 1]` ⇒ no maximiser lies above
`min x sbar_star` ⇒ the supremum of the argmax set is at most
`min x sbar_star`.

Since round BH-2 (2026-10-06, BH2.6) the discharger is stated first in its
pivot-star form: the objective at the pivot `min x sbar_star` strictly beats
its value at every higher feasible sanction. The strict-anti form is a
corollary. -/

/-- **Dual level discharger from the pivot beating every super-pivot
sanction (round BH-2, 2026-10-06, BH2.6).** If, at every low-basin state
`x ∈ [0, xS_star]`, the Sender's forward-looking objective at the pivot
`t = min x sbar_star` is strictly higher than at every sanction in `(t, 1]`,
then the upper selector satisfies `σ_dyn_top V_S x (α x) ≤ t`.

In plain terms: on the low basin the Sender strictly prefers the ceiling
sanction to anything heavier, so its greatest best response never exceeds the
ceiling. Only one comparison per heavier sanction is read, always against the
pivot; two heavier sanctions are never compared with each other.

Dropped relative to `sender_low_argmax_le_threshold_of_strictAntiOn`: strict
monotonicity of the objective on the whole interval `[t, 1]` (only comparisons
with the pivot are used), and the upper bound `sbar_star ≤ 1` (the pivot is at
most `1` as soon as some feasible maximiser lies above it). The lower bound
`0 ≤ sbar_star` stays: it makes the pivot a feasible sanction, and without it
the conclusion "realised sanctions at most `sbar_star`" could contradict
feasibility. General in `F`: the transition enters only through the objective. -/
theorem sender_low_argmax_le_threshold_of_pivot_beats_superpivot
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xS_star sbar_star : ℝ}
    (hsbar_nn : 0 ≤ sbar_star)
    (h_star : ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
      ∀ s ∈ Set.Ioc (min x sbar_star) (1 : ℝ),
        p.senderDynObjective V_S x (α x) s
          < p.senderDynObjective V_S x (α x) (min x sbar_star)) :
    ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
      p.dynamicTopRealizedRule V_S α x ≤ min x sbar_star := by
  intro x hx
  -- the realised sanction is itself a maximiser (`σ_dyn_top_isMaxOn`)
  have hs_mem : p.dynamicTopRealizedRule V_S α x ∈ Sanctions.I :=
    p.σ_dyn_top_mem_I V_S x (α x)
  by_contra h_not_le
  have h_lt : min x sbar_star < p.dynamicTopRealizedRule V_S α x :=
    lt_of_not_ge h_not_le
  -- the pivot is feasible: `0 ≤ t` from `0 ≤ x` and `0 ≤ s̄`, `t ≤ 1` from `t < σ ≤ 1`
  have ht_mem : min x sbar_star ∈ Sanctions.I :=
    ⟨le_min hx.1 hsbar_nn, h_lt.le.trans hs_mem.2⟩
  have h_obj_lt :=
    h_star x hx (p.dynamicTopRealizedRule V_S α x) ⟨h_lt, hs_mem.2⟩
  have h_max_ge :
      p.senderDynObjective V_S x (α x) (min x sbar_star)
        ≤ p.senderDynObjective V_S x (α x) (p.dynamicTopRealizedRule V_S α x) :=
    p.σ_dyn_top_isMaxOn V_S x (α x) ht_mem
  linarith

/-- **Dual level discharger: top-selector ≤ threshold from
strict-anti-on.** If the Sender's dynamic objective is strictly
decreasing in `s` on `[min x sbar_star, 1]` for every low-basin state
`x ∈ [0, xS_star]`, then the upper selector satisfies
`σ_dyn_top V_S x (α x) ≤ min x sbar_star`. The proof: any maximiser
`s` with `s > min x sbar_star` is dominated by `s' = min x sbar_star`
on the strict-anti interval, contradicting maximality. Hence the
argmax set is contained in `[0, min x sbar_star]` and its supremum is
at most `min x sbar_star`.

Since round BH-2 (2026-10-06, BH2.6) a corollary of
`sender_low_argmax_le_threshold_of_pivot_beats_superpivot`: strict decrease on
`[min x sbar_star, 1]` gives the pivot-star comparison at every higher
sanction. Statement unchanged. General in `F`. -/
theorem sender_low_argmax_le_threshold_of_strictAntiOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xS_star sbar_star : ℝ}
    (hsbar_star_mem : sbar_star ∈ Sanctions.I)
    (h_strict_anti : ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
        StrictAntiOn (fun s => p.senderDynObjective V_S x (α x) s)
          (Set.Icc (min x sbar_star) (1 : ℝ))) :
    ∀ x ∈ Set.Icc (0 : ℝ) xS_star,
      p.dynamicTopRealizedRule V_S α x ≤ min x sbar_star :=
  p.sender_low_argmax_le_threshold_of_pivot_beats_superpivot V_S α hsbar_star_mem.1
    (fun x hx _ hs =>
      h_strict_anti x hx ⟨le_rfl, hs.1.le.trans hs.2⟩ ⟨hs.1.le, hs.2⟩ hs.1)

/-! ## §5 Dual `DynamicTopLockIn` lemmas

Sign-mirrors of the lemmas in `Theory/LockIn/DynamicTopLockIn.lean`.
Each takes the dual level condition `σ_dyn_top ≤ min x sbar_star` on
the low basin and proves the dual conclusion: step decreases, state
path stays in `[0, xbar_low]`, sanctions are bounded above, etc. -/

/-- **Dual step ≤ self.** From the dual level condition, one
top-dynamic step is weakly below the current state. -/
theorem dynamicTopLockInStep_le_self_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xbar_low) :
    p.dynamicTopLockInStep V_S α x ≤ x := by
  have h_σ_le : p.dynamicTopRealizedRule V_S α x ≤ x :=
    le_trans (h_level_top_low x hx) (min_le_left x sbar_low)
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  unfold dynamicTopLockInStep
  nlinarith [mul_nonneg hδ_nonneg (sub_nonneg.mpr h_σ_le)]

/-- **Dual step ≥ 0.** One top-dynamic step from `[0, xbar_low]` stays ≥ 0. -/
theorem dynamicTopLockInStep_nn_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low : ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xbar_low) :
    0 ≤ p.dynamicTopLockInStep V_S α x := by
  have hg := p.dynamicTopRealizedRule_mem V_S α x
  have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have h1δ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  unfold dynamicTopLockInStep
  have h1 : 0 ≤ (1 - p.δ) * x := mul_nonneg h1δ_nn hx.1
  have h2 : 0 ≤ p.δ * p.dynamicTopRealizedRule V_S α x :=
    mul_nonneg hδ_nn hg.1
  linarith

/-- **Dual forward invariance.** Step stays in `[0, xbar_low]`. -/
theorem dynamicTopLockInStep_mem_low_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xbar_low) :
    p.dynamicTopLockInStep V_S α x ∈ Set.Icc (0 : ℝ) xbar_low := by
  refine ⟨p.dynamicTopLockInStep_nn_low V_S α hx, ?_⟩
  exact le_trans (p.dynamicTopLockInStep_le_self_low V_S α h_level_top_low hx) hx.2

/-- **Dual state path invariance.** Every state stays in `[0, xbar_low]`. -/
theorem dynamicTopLockInPath_mem_low_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    ∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPath_succ]
    exact p.dynamicTopLockInStep_mem_low_basin V_S α h_level_top_low ih

/-- **Dual state-path anti-monotonicity.** Non-increasing path. -/
theorem dynamicTopLockInPath_anti_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    Antitone (p.dynamicTopLockInPath V_S α x₀) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [dynamicTopLockInPath_succ]
  exact p.dynamicTopLockInStep_le_self_low V_S α h_level_top_low
    (p.dynamicTopLockInPath_mem_low_basin V_S α h_level_top_low hx₀ n)

/-- **Dual sanction ceiling.** Sanctions are bounded above by `sbar_low`. -/
theorem dynamicTopLockInSanctions_ceiling_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    ∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ sbar_low := by
  intro n
  unfold dynamicTopLockInSanctions
  exact le_trans (h_level_top_low (p.dynamicTopLockInPath V_S α x₀ n)
    (p.dynamicTopLockInPath_mem_low_basin V_S α h_level_top_low hx₀ n))
    (min_le_right _ _)

/-- **Dual sanction ≤ basin ceiling.** Sanctions are bounded above by `xbar_low`. -/
theorem dynamicTopLockInSanctions_le_xbar_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    ∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ xbar_low := by
  intro n
  unfold dynamicTopLockInSanctions
  have h_mem : p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low :=
    p.dynamicTopLockInPath_mem_low_basin V_S α h_level_top_low hx₀ n
  exact le_trans (h_level_top_low _ h_mem)
    (le_trans (min_le_left _ _) h_mem.2)

/-- **Dual sanction anti-monotonicity.** If the top rule is monotone on the
low basin (same monotonicity as the high basin — the rule is monotone
in `x` everywhere by Milgrom-Shannon single-crossing), the sanction
sequence is non-increasing. -/
theorem dynamicTopLockInSanctions_anti_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    (h_top_rule_mono :
        MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    Antitone (p.dynamicTopLockInSanctions V_S α x₀) := by
  intro m n hmn
  unfold dynamicTopLockInSanctions
  -- Path is anti-monotone, rule is monotone in x ⇒ sanctions are anti-monotone.
  exact h_top_rule_mono
    (p.dynamicTopLockInPath_mem_low_basin V_S α h_level_top_low hx₀ n)
    (p.dynamicTopLockInPath_mem_low_basin V_S α h_level_top_low hx₀ m)
    (p.dynamicTopLockInPath_anti_low V_S α h_level_top_low hx₀ hmn)

/-! ## §6 `JointPreferenceBasinLow` Prop structure

Sign-mirror of `JointPreferenceBasinTop` (in `JointPreferenceBasin.lean`).
Bundles low-basin geometry + the four structural fields needed for the
dual workhorse persistence theorem. -/

/-- **Dual joint sanction-preference basin (low political basin).**
Predicate on `(V_T, V_S, α, xbar_low, sbar_low)` capturing:

1. **Basin geometry.** `0 ≤ xbar_low ≤ 1`, `sbar_low ∈ [0, 1]`.
2. **Target policy feasibility.** `α x ∈ [0, 1]` for every low-basin state.
3. **Dual Sender level condition** (`sender_low_argmax_le_threshold`):
   `σ_dyn_top V_S x (α x) ≤ min x sbar_low` at every low-basin state.
4. **Top-rule monotonicity in `x`** (same as high-basin: monotone, from
   Milgrom-Shannon single-crossing).
5. **Dual Target preference** (`target_dislikes_sanctions_on_low`): the
   Target's forward-looking objective is monotone non-increasing in `s`
   on `[min(x, sbar_low), 1]`.
6. **Target policy optimality.** `α` is Bellman-optimal against the
   upper dynamic Sender response. -/
structure JointPreferenceBasinLow
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xbar_low sbar_low : ℝ) : Prop where
  xbar_low_le_one : xbar_low ≤ 1

  target_policy_feasible :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar_low, α x ∈ Sanctions.I

  /-- Dual top-selector level condition. -/
  sender_low_argmax_le_threshold :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
      p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low

  /-- Topkis / monotone comparative statics (same as in `JointPreferenceBasinTop` —
  monotone-in-`x` rule from Milgrom-Shannon single-crossing). -/
  top_rule_mono :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low)

  /-- Target prefers low sanctions on the low basin. -/
  target_dislikes_sanctions :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
      AntitoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
        (Set.Icc (min x sbar_low) 1)

  target_policy_optimal :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
      IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a) Sanctions.I (α x)

/-! ## §7 Bridge: `OneSidedSanctionLowBasinPreferenceThresholds` ⇒ `JointPreferenceBasinLow` -/

/-- **Bridge constructor.** Sign-mirror of
`JointPreferenceBasinTop.of_oneSidedThresholds`. Builds
`JointPreferenceBasinLow` at `xbar_low := min(xT_star, xS_star)` from
the dual one-sided-thresholds Prop plus top-rule monotonicity and
Target-policy optimality. -/
theorem JointPreferenceBasinLow.of_oneSidedLowBasinThresholds
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT_star xS_star sbar_star : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α
              xT_star xS_star sbar_star)
    (hα_feas : ∀ x ∈ Set.Icc (0 : ℝ) (min xT_star xS_star), α x ∈ Sanctions.I)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hα_opt :
      ∀ x ∈ Set.Icc (0 : ℝ) (min xT_star xS_star),
        IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                Sanctions.I (α x)) :
    p.JointPreferenceBasinLow V_T V_S α (min xT_star xS_star) sbar_star where
  xbar_low_le_one := le_trans (min_le_left _ _) hOne.xT_star_mem.2
  target_policy_feasible := hα_feas
  sender_low_argmax_le_threshold := by
    -- Apply the level discharger with xS := xS_star, restricted to the joint min.
    intro x hx
    -- `[0, min xT_star xS_star] ⊆ [0, xS_star]`, so the strict-anti hypothesis applies.
    have hxS : x ∈ Set.Icc (0 : ℝ) xS_star :=
      ⟨hx.1, le_trans hx.2 (min_le_right _ _)⟩
    exact p.sender_low_argmax_le_threshold_of_strictAntiOn V_S α
      hOne.sbar_star_mem
      (fun y hy => hOne.sender_dislikes_above_threshold y hy) x hxS
  top_rule_mono := hTopMono
  target_dislikes_sanctions := by
    intro x hx
    -- `[0, min xT_star xS_star] ⊆ [0, xT_star]`, so the Target hypothesis applies.
    exact hOne.target_dislikes_high_sanctions x
      ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
  target_policy_optimal := hα_opt

/-! ## §8 Workhorse: `jointPreferenceBasinLow_long_run_nonIncreasing` -/

/-- **Workhorse (dual of `jointPreferenceBasinTop_long_run_nonDecreasing`).**
From any starting state in the low political basin
`[0, xbar_low]`, the upper-dynamic state path stays in the basin,
sanctions are bounded above by `sbar_low`, bounded above by the basin
ceiling `xbar_low`, and **non-increasing**. -/
theorem jointPreferenceBasinLow_long_run_nonIncreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low x₀ : ℝ}
    (hB : p.JointPreferenceBasinLow V_T V_S α xbar_low sbar_low)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctions V_S α x₀) :=
  ⟨p.dynamicTopLockInPath_mem_low_basin V_S α hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctions_ceiling_low V_S α hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctions_le_xbar_low V_S α hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctions_anti_low V_S α hB.sender_low_argmax_le_threshold
     hB.top_rule_mono hx₀⟩

/-- **Low-basin workhorse with equilibrium evidence along the path
(2026-07-24, user-approved audit item 1(a)).** Sign-mirror of
`jointPreferenceBasinTop_long_run_with_equilibrium_evidence`: keeps the
four §8 conclusions and re-emits, at every path state, the Target-side
dual package — policy feasibility, Target Bellman optimality, Sender
dynamic optimality of the realised sanction, and the **A2\* dual
preference** (the Target's forward-looking sanction objective is
non-increasing in the sanction on the low-sanction interval). This
makes the Target-side fields of `JointPreferenceBasinLow`
(`target_dislikes_sanctions`, `target_policy_feasible`,
`target_policy_optimal`) load-bearing as output conjuncts, restoring
exact symmetry with the high basin — closing the 2026-07-24 audit
finding that the A2\* stack was decorative. -/
theorem jointPreferenceBasinLow_long_run_with_equilibrium_evidence
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low x₀ : ℝ}
    (hB : p.JointPreferenceBasinLow V_T V_S α xbar_low sbar_low)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctions V_S α x₀) ∧
    (∀ n, α (p.dynamicTopLockInPath V_S α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S
                              (p.dynamicTopLockInPath V_S α x₀ n) a)
              Sanctions.I (α (p.dynamicTopLockInPath V_S α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective V_S
                              (p.dynamicTopLockInPath V_S α x₀ n)
                              (α (p.dynamicTopLockInPath V_S α x₀ n)) s')
              Sanctions.I (p.dynamicTopLockInSanctions V_S α x₀ n)) ∧
    (∀ n, AntitoneOn
      (fun s => p.targetSanctionObjective V_T
        (p.dynamicTopLockInPath V_S α x₀ n)
        (α (p.dynamicTopLockInPath V_S α x₀ n)) s)
      (Set.Icc (min (p.dynamicTopLockInPath V_S α x₀ n) sbar_low) 1)) := by
  have h_path := p.dynamicTopLockInPath_mem_low_basin V_S α
    hB.sender_low_argmax_le_threshold hx₀
  refine ⟨h_path,
          p.dynamicTopLockInSanctions_ceiling_low V_S α
            hB.sender_low_argmax_le_threshold hx₀,
          p.dynamicTopLockInSanctions_le_xbar_low V_S α
            hB.sender_low_argmax_le_threshold hx₀,
          p.dynamicTopLockInSanctions_anti_low V_S α
            hB.sender_low_argmax_le_threshold hB.top_rule_mono hx₀,
          ?_, ?_, ?_, ?_⟩
  · intro n; exact hB.target_policy_feasible _ (h_path n)
  · intro n; exact hB.target_policy_optimal _ (h_path n)
  · intro n s' hs'
    exact p.σ_dyn_top_isMaxOn V_S
      (p.dynamicTopLockInPath V_S α x₀ n)
      (α (p.dynamicTopLockInPath V_S α x₀ n)) hs'
  · intro n; exact hB.target_dislikes_sanctions _ (h_path n)

/-! ## §9 Headline wrapper: `oneSidedLowBasinThresholds_long_run_nonIncreasing` -/

/-- **Headline (dual one-sided thresholds ⇒ long-run non-increasing
low sanctions).** Composes
`JointPreferenceBasinLow.of_oneSidedLowBasinThresholds` with
`jointPreferenceBasinLow_long_run_nonIncreasing`. -/
theorem oneSidedLowBasinThresholds_long_run_nonIncreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α
              xT_star xS_star sbar_star)
    (hα_feas : ∀ x ∈ Set.Icc (0 : ℝ) (min xT_star xS_star), α x ∈ Sanctions.I)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hα_opt :
      ∀ x ∈ Set.Icc (0 : ℝ) (min xT_star xS_star),
        IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                Sanctions.I (α x))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctions V_S α x₀ n ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctions V_S α x₀) :=
  p.jointPreferenceBasinLow_long_run_nonIncreasing
    (JointPreferenceBasinLow.of_oneSidedLowBasinThresholds p hOne hα_feas
      hTopMono hα_opt) hx₀

end Params
end AbstractGame

/-! ## §10 Helper: low-basin ⊆ feasible state space `Sanctions.S`

Symmetric to the high-basin `icc_max_subset_S` helper. Used to convert
membership in the low-basin closed interval `[0, min xT_star xS_star]`
into membership in the feasible state space `Sanctions.S = [0, 1]`. -/

/-- Low basin `[0, min xT_star xS_star]` lies inside the feasible state
space `Sanctions.S = [0, 1]` whenever `xT_star ∈ Sanctions.I`. -/
private theorem icc_min_subset_S_low {xT_star xS_star : ℝ}
    (hxT_star_mem : xT_star ∈ Sanctions.I) :
    Set.Icc (0 : ℝ) (min xT_star xS_star) ⊆ Sanctions.S := fun _ hx =>
  ⟨hx.1, le_trans (le_trans hx.2 (min_le_left _ _)) hxT_star_mem.2⟩

namespace AbstractGame
namespace Params

/-! ## §11 Strongest headline (full equilibrium + dual one-sided thresholds ⇒
low-basin persistence)

Sign-mirror of `equilibriumTop_oneSidedThresholds_long_run_nonDecreasing`.
No witness needed; auxiliary `hα_feas` and `hα_opt` are discharged from
`E.α_mem` and `E.α_opt_top` automatically. -/

/-- **Strongest dual headline.** Given a forward-looking Stackelberg
equilibrium `E` plus the dual one-sided thresholds, every starting
state in the low basin `[0, min(xT_star, xS_star)]` yields:
- state path stays in the low basin,
- sanctions bounded above by `sbar_star`,
- sanctions bounded above by the low-basin pivot `min(xT_star, xS_star)`,
- sanction sequence non-increasing (`Antitone`),
- α is Bellman-optimal at every path state (Rule-1 conclusion). -/
theorem equilibriumTop_oneSidedLowBasinThresholds_long_run_nonIncreasing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n
            ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  -- Reuse the four-conjunct dual wrapper for (i)-(iv).
  obtain ⟨h_path, h_ceil, h_xbar, h_anti⟩ :=
    p.oneSidedLowBasinThresholds_long_run_nonIncreasing hOne
      (fun x hx => E.α_mem x (icc_min_subset_S_low hOne.xT_star_mem hx))
      hTopMono
      (fun x hx => E.α_opt_top x (icc_min_subset_S_low hOne.xT_star_mem hx))
      hx₀
  refine ⟨h_path, h_ceil, h_xbar, h_anti, ?_⟩
  -- (v) Bellman optimality at every path state: each path n ∈ low basin
  -- ⊆ Sanctions.S, so E.α_opt_top applies.
  intro n
  exact E.α_opt_top _ (icc_min_subset_S_low hOne.xT_star_mem (h_path n))

/-! ## §12 Paper-facing headline alias

The final theorem in this module — the paper-facing **Theorem 4
(Low political absorbing basin)**. Renames the §11 equilibrium-level
wrapper to the public-facing `standardCompliance_three_goals_local_low_basin`
identifier, matching the project's headline-naming convention and
mirroring `standardCompliance_three_goals_local` (the high-basin
headline). -/

/-- **Theorem 4 (Low political absorbing basin) — paper-facing headline.**

Plain English: under the dual structural assumptions (the Sender's
forward-looking objective falls in the sanction above the low pivot,
the paper's A1_ε at `ε = −1`; the Target's forward-looking sanction
payoff is non-increasing there; both packaged, with the three basin
memberships, into the `OneSidedSanctionLowBasinPreferenceThresholds`
Prop bundle; no concavity of `U_S` in `s` (A3) is read), plus
top-rule monotonicity (discharged from R28/R30 Milgrom-Shannon
single-crossing on the dual single-crossing), from every starting
state `x_0` in the low political basin `[0, min(xT_star, xS_star)]`,
a forward-looking feedback Stackelberg equilibrium `E` exhibits:

(i)   the state path stays in the low political basin forever;
(ii)  the realised-sanction sequence is bounded above by `sbar_star`;
(iii) the realised-sanction sequence is bounded above by the low-basin
      pivot `min(xT_star, xS_star)`;
(iv)  the realised-sanction sequence is non-increasing (`Antitone`);
(v)   the Target policy `α` is Bellman-optimal at every path state.

This is the **mirror of Theorem 1** (`standardCompliance_three_goals_local`):
the persistence theorem on the high political basin is non-decreasing
and bounded below; the low-basin theorem is non-increasing and bounded
above. Together they form the bistable picture: which basin the
system locks into is determined by initial conditions.

The proof chain anchors at the dual single-crossing lemmas in §1, the
dual one-sided-thresholds
characterisation in §3, the level-discharger in §4, the dual
`dynamicTopLockIn` lemmas in §5, the dual basin Prop in §6, the
bridge constructor in §7, the workhorse theorem in §8, the wrapper
in §9, and the equilibrium-level wrapper in §11. -/
theorem standardCompliance_three_goals_local_low_basin
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n
            ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctions E.V_S E.α x₀) := by
  -- Project the per-path Bellman-optimality conjunct out of the
  -- 5-conjunct workhorse output. Issue 9 of the 2026-06-07 JET
  -- referee response: clause (iv) is a definitional consequence of
  -- (E3) (the feedback Stackelberg equilibrium concept), not a
  -- substantive theorem conclusion. The fat 5-conjunct form remains
  -- available as `standardCompliance_three_goals_local_low_basin_with_path_optimality`.
  obtain ⟨hInv, hSbarCeiling, hxBarCeiling, hAnti, _hIsMax⟩ :=
    p.equilibriumTop_oneSidedLowBasinThresholds_long_run_nonIncreasing E
      hOne hTopMono hx₀
  exact ⟨hInv, hSbarCeiling, hxBarCeiling, hAnti⟩

/-- **Low-basin backward-compatibility alias retaining clause (iv).**
Reverts to the 5-conjunct persistence form (i.e.\ the pre-Round-1
shape), with the per-path `IsMaxOn` Bellman-optimality conjunct
restored. The restored conjunct is *not* a substantive theorem
conclusion --- it is a definitional consequence of the Stackelberg-
feedback equilibrium concept (E3) --- but the alias is provided for
backward-compatibility with code written against the pre-Round-1
paper draft. -/
theorem standardCompliance_three_goals_local_low_basin_with_path_optimality
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n
            ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) :=
  p.equilibriumTop_oneSidedLowBasinThresholds_long_run_nonIncreasing E
    hOne hTopMono hx₀

/-! ## §13 General-`F` low-basin trajectory (Option B, R-2026-06-23)

The §5–§12 low-basin chain above runs the realised political-state
**trajectory** on the affine law `dynamicTopLockInStep = (1−δ)x + δ·σ`.
This section ports it to an arbitrary monotone transition `F`, mirroring
the **high**-basin general-`F` family in
`Theory/LockIn/DynamicTopLockIn.lean` (§ "One-step top-dynamic natural
dynamics", `dynamicTopLockInStepF` etc.). The realised state now evolves
by the opaque `p.F` (`dynamicTopLockInStepF V_S α x = p.F x (σ)`), closing
the affine-vs-general-`F` asymmetry between the two basins (the high basin
already had `dynamicTopLockInStepF`/`PathF`; the low basin did not).

**No new assumption.** Unlike the high-basin general-`F` *shock* goal
(which needs `hF_top : x < F x 1`), the low-basin result is
persistence-only, so the dual step `F(x, σ) ≤ F(x, x) = x` (since
`σ ≤ x` on the low basin) follows from `F_mono_s` + `F_diag` alone, and
feasibility from `F_mem`. The only side condition, `xbar_low ≤ 1`, is
already a field of `JointPreferenceBasinLow` (`xbar_low_le_one`) and is
discharged at the equilibrium headline from the threshold membership
`hOne.xT_star_mem.2`. Hence every theorem below is provable from the
existing assumption surface (Rule 3: a new theorem, not a new
assumption). The affine §5–§12 chain is recovered as the
`F := affineF δ` specialisation (`affineF` satisfies `F_mono_s`,
`F_diag`, `F_mem`). -/

variable (p : Params)

/-- **Dual general-`F` step ≤ self.** One general-`F` top-dynamic step is
weakly below the current state: `F(x, σ) ≤ F(x, x) = x` because the dual
level condition gives `σ ≤ x` on the low basin (`F_mono_s` + `F_diag`).
Sign-mirror of `dynamicTopLockInStepF_ge_self`. -/
theorem dynamicTopLockInStepF_le_self_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xbar_low) :
    p.dynamicTopLockInStepF V_S α x ≤ x := by
  have h_σ_le : p.dynamicTopRealizedRule V_S α x ≤ x :=
    le_trans (h_level_top_low x hx) (min_le_left x sbar_low)
  have hmono : p.F x (p.dynamicTopRealizedRule V_S α x) ≤ p.F x x :=
    p.F_mono_s x h_σ_le
  rwa [p.F_diag x] at hmono

/-- **Dual general-`F` forward invariance.** One general-`F` step from
`[0, xbar_low]` stays in `[0, xbar_low]` (`F_mem` for `≥ 0`, dual
step ≤ self for `≤ xbar_low`; `xbar_low ≤ 1` makes the state feasible
for `F_mem`). -/
theorem dynamicTopLockInStepF_mem_low_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xbar_low) :
    p.dynamicTopLockInStepF V_S α x ∈ Set.Icc (0 : ℝ) xbar_low := by
  have hxI : x ∈ Sanctions.I := ⟨hx.1, le_trans hx.2 hxbar_low_le_one⟩
  refine ⟨(p.dynamicTopLockInStepF_mem_I_of_mem_I V_S α hxI).1, ?_⟩
  exact le_trans (p.dynamicTopLockInStepF_le_self_low V_S α h_level_top_low hx) hx.2

/-- **Dual general-`F` state-path invariance.** Every general-`F` state
stays in `[0, xbar_low]`. -/
theorem dynamicTopLockInPathF_mem_low_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPathF_succ]
    exact p.dynamicTopLockInStepF_mem_low_basin V_S α hxbar_low_le_one
      h_level_top_low ih

/-- **Dual general-`F` state-path anti-monotonicity.** The general-`F`
state path is non-increasing. -/
theorem dynamicTopLockInPathF_anti_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    Antitone (p.dynamicTopLockInPathF V_S α x₀) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [dynamicTopLockInPathF_succ]
  exact p.dynamicTopLockInStepF_le_self_low V_S α h_level_top_low
    (p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar_low_le_one
      h_level_top_low hx₀ n)

/-- **Dual general-`F` sanction ceiling.** General-`F` sanctions are
bounded above by `sbar_low`. -/
theorem dynamicTopLockInSanctionsF_ceiling_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    ∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ sbar_low := by
  intro n
  unfold dynamicTopLockInSanctionsF
  have h_mem : p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low :=
    p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar_low_le_one
      h_level_top_low hx₀ n
  exact le_trans (h_level_top_low _ h_mem) (min_le_right _ _)

/-- **Dual general-`F` sanction ≤ basin ceiling.** General-`F` sanctions
are bounded above by `xbar_low`. -/
theorem dynamicTopLockInSanctionsF_le_xbar_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    ∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ xbar_low := by
  intro n
  unfold dynamicTopLockInSanctionsF
  have h_mem : p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low :=
    p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar_low_le_one
      h_level_top_low hx₀ n
  exact le_trans (h_level_top_low _ h_mem)
    (le_trans (min_le_left _ _) h_mem.2)

/-- **Dual general-`F` sanction anti-monotonicity.** With the top rule
monotone on the low basin, the general-`F` sanction sequence is
non-increasing (monotone rule ∘ non-increasing path). -/
theorem dynamicTopLockInSanctionsF_anti_low
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_level_top_low : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
                          p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low)
    (h_top_rule_mono :
        MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    Antitone (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  intro m n hmn
  unfold dynamicTopLockInSanctionsF
  exact h_top_rule_mono
    (p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar_low_le_one
      h_level_top_low hx₀ n)
    (p.dynamicTopLockInPathF_mem_low_basin V_S α hxbar_low_le_one
      h_level_top_low hx₀ m)
    (p.dynamicTopLockInPathF_anti_low V_S α hxbar_low_le_one
      h_level_top_low hx₀ hmn)

/-- **General-`F` low-basin workhorse.** Dual of
`jointPreferenceBasinLow_long_run_nonIncreasing` with the realised state
**trajectory** evolved by the opaque `p.F` rather than the affine law.
From any starting state in the low basin, the general-`F` state path
stays in `[0, xbar_low]`, sanctions are bounded above by `sbar_low` and
by `xbar_low`, and the sanction sequence is non-increasing. -/
theorem jointPreferenceBasinLowF_long_run_nonIncreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low x₀ : ℝ}
    (hB : p.JointPreferenceBasinLow V_T V_S α xbar_low sbar_low)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctionsF V_S α x₀) :=
  ⟨p.dynamicTopLockInPathF_mem_low_basin V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctionsF_ceiling_low V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctionsF_le_xbar_low V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctionsF_anti_low V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hB.top_rule_mono hx₀⟩

/-- **General-`F` low-basin workhorse with equilibrium evidence
(2026-07-24, user-approved audit item 1(a)).** General-transition
sibling of `jointPreferenceBasinLow_long_run_with_equilibrium_evidence`,
evolving the state with `p.F`; same four evidence conjuncts (Target
feasibility, Target Bellman optimality, Sender dynamic optimality,
A2\* dual preference) at every path state. -/
theorem jointPreferenceBasinLowF_long_run_with_equilibrium_evidence
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low x₀ : ℝ}
    (hB : p.JointPreferenceBasinLow V_T V_S α xbar_low sbar_low)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctionsF V_S α x₀) ∧
    (∀ n, α (p.dynamicTopLockInPathF V_S α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S
                              (p.dynamicTopLockInPathF V_S α x₀ n) a)
              Sanctions.I (α (p.dynamicTopLockInPathF V_S α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective V_S
                              (p.dynamicTopLockInPathF V_S α x₀ n)
                              (α (p.dynamicTopLockInPathF V_S α x₀ n)) s')
              Sanctions.I (p.dynamicTopLockInSanctionsF V_S α x₀ n)) ∧
    (∀ n, AntitoneOn
      (fun s => p.targetSanctionObjective V_T
        (p.dynamicTopLockInPathF V_S α x₀ n)
        (α (p.dynamicTopLockInPathF V_S α x₀ n)) s)
      (Set.Icc (min (p.dynamicTopLockInPathF V_S α x₀ n) sbar_low) 1)) := by
  have h_path := p.dynamicTopLockInPathF_mem_low_basin V_S α
    hB.xbar_low_le_one hB.sender_low_argmax_le_threshold hx₀
  refine ⟨h_path,
          p.dynamicTopLockInSanctionsF_ceiling_low V_S α
            hB.xbar_low_le_one hB.sender_low_argmax_le_threshold hx₀,
          p.dynamicTopLockInSanctionsF_le_xbar_low V_S α
            hB.xbar_low_le_one hB.sender_low_argmax_le_threshold hx₀,
          p.dynamicTopLockInSanctionsF_anti_low V_S α
            hB.xbar_low_le_one hB.sender_low_argmax_le_threshold
            hB.top_rule_mono hx₀,
          ?_, ?_, ?_, ?_⟩
  · intro n; exact hB.target_policy_feasible _ (h_path n)
  · intro n; exact hB.target_policy_optimal _ (h_path n)
  · intro n s' hs'
    exact p.σ_dyn_top_isMaxOn V_S
      (p.dynamicTopLockInPathF V_S α x₀ n)
      (α (p.dynamicTopLockInPathF V_S α x₀ n)) hs'
  · intro n; exact hB.target_dislikes_sanctions _ (h_path n)

/-- **General-`F` low-basin headline wrapper.** Dual of
`oneSidedLowBasinThresholds_long_run_nonIncreasing` over the general-`F`
trajectory. Composes the §7 bridge with the general-`F` workhorse. -/
theorem oneSidedLowBasinThresholdsF_long_run_nonIncreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α
              xT_star xS_star sbar_star)
    (hα_feas : ∀ x ∈ Set.Icc (0 : ℝ) (min xT_star xS_star), α x ∈ Sanctions.I)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hα_opt :
      ∀ x ∈ Set.Icc (0 : ℝ) (min xT_star xS_star),
        IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                Sanctions.I (α x))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctionsF V_S α x₀) :=
  p.jointPreferenceBasinLowF_long_run_nonIncreasing
    (JointPreferenceBasinLow.of_oneSidedLowBasinThresholds p hOne hα_feas
      hTopMono hα_opt) hx₀

/-- **Theorem 4 (Low political absorbing basin), general-`F` trajectory —
paper-facing headline.**

Sign-mirror of the high-basin
`standardCompliance_three_goals_local_MS_generalF` for the low basin:
identical conclusion to `standardCompliance_three_goals_local_low_basin`
(§12), but with the realised political-state **trajectory** itself
evolved by the abstract monotone transition `p.F`
(`dynamicTopLockInPathF` / `dynamicTopLockInSanctionsF`), not only the
affine law `(1−δ)x + δσ`. Given a forward-looking feedback Stackelberg
equilibrium `E` plus the dual one-sided thresholds, from every starting
state in the low basin `[0, min(xT_star, xS_star)]`:

(i)   the general-`F` state path stays in the low political basin forever;
(ii)  the realised-sanction sequence is bounded above by `sbar_star`;
(iii) the realised-sanction sequence is bounded above by the low-basin
      pivot `min(xT_star, xS_star)`;
(iv)  the realised-sanction sequence is non-increasing (`Antitone`).

No extra hypothesis beyond the affine §12 headline: the dual descent
`F(x, σ) ≤ F(x, x) = x` uses only `F_mono_s` + `F_diag`, feasibility uses
`F_mem`, and `min(xT_star, xS_star) ≤ 1` is discharged from
`hOne.xT_star_mem.2`. The affine headline is the `F := affineF δ`
specialisation. This substantiates §4's "(F2)–(F4), never the affine
form" claim at the state-evolution level for the **low** basin,
restoring symmetry with the high basin.

Round BB (2026-09-28): none of (i)–(iv) uses the Target condition, the
Target field `target_dislikes_high_sanctions` of `hOne`. The joint route fills the
Target field of `JointPreferenceBasinLow` from it, and the path lemmas
never read that field. The Sender-only sibling
`standardCompliance_low_basin_generalF_of_sender_level`
(`Basin/SenderPersistenceLow.lean`) drops it, and a Rule-13 `example` there
recovers this statement. This theorem stays as it is because it is a pinned
headline row. -/
theorem standardCompliance_three_goals_local_low_basin_generalF
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n
            ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  p.oneSidedLowBasinThresholdsF_long_run_nonIncreasing hOne
    (fun x hx => E.α_mem x (icc_min_subset_S_low hOne.xT_star_mem hx))
    hTopMono
    (fun x hx => E.α_opt_top x (icc_min_subset_S_low hOne.xT_star_mem hx))
    hx₀

/-- **Low-basin general-`F` backward-compatibility twin retaining
clause (v) (R-2026-07-08).** General-`F` sibling of
`standardCompliance_three_goals_local_low_basin_with_path_optimality`:
identical to `standardCompliance_three_goals_local_low_basin_generalF`
with the per-path `IsMaxOn` Bellman-optimality conjunct restored,
stated **along the general-`F` realized path**
`dynamicTopLockInPathF`. The restored conjunct is *not* a substantive
theorem conclusion — it is a definitional consequence of the feedback
Stackelberg equilibrium concept (E3), hence transition-agnostic: every
general-`F` path state stays in the low basin `⊆ Sanctions.S`, where
`E.α_opt_top` applies verbatim. No hypothesis beyond the general-`F`
base headline. -/
theorem standardCompliance_three_goals_local_low_basin_with_path_optimality_generalF
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n
            ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))) := by
  obtain ⟨h_path, h_ceil, h_xbar, h_anti⟩ :=
    p.standardCompliance_three_goals_local_low_basin_generalF E hOne
      hTopMono hx₀
  refine ⟨h_path, h_ceil, h_xbar, h_anti, ?_⟩
  -- Clause (v): every general-`F` path state lies in the low basin
  -- ⊆ Sanctions.S, so the equilibrium Bellman optimality applies.
  intro n
  exact E.α_opt_top _ (icc_min_subset_S_low hOne.xT_star_mem (h_path n))

/-- **Initial conditions select between two disjoint equilibrium basins.**
Suppose one feedback Stackelberg equilibrium satisfies both a high-basin
preference package on `[xbar_high, 1]` and a low-basin preference package on
`[0, xbar_low]`, with `xbar_low < xbar_high`. Then the basins are disjoint;
every high start generates an invariant high path with a sanction floor and a
non-decreasing sanction sequence; every low start generates an invariant low
path with a sanction ceiling and a non-increasing sanction sequence. The
players, primitives, values, and equilibrium policies are identical across
the two conclusions: only the initial political state differs. -/
theorem equilibriumTop_initial_condition_selects
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar_high sbar_high xbar_low sbar_low : ℝ}
    (hHigh : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar_high sbar_high)
    (hLow : p.JointPreferenceBasinLow E.V_T E.V_S E.α xbar_low sbar_low)
    (hsep : xbar_low < xbar_high) :
    Disjoint (Set.Icc xbar_high 1) (Set.Icc 0 xbar_low) ∧
      (∀ x₀ ∈ Set.Icc xbar_high 1,
        (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc xbar_high 1) ∧
        (∀ n, sbar_high ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
        (∀ n, xbar_high ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
        Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀)) ∧
      (∀ x₀ ∈ Set.Icc 0 xbar_low,
        (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc 0 xbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n ≤ sbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctions E.V_S E.α x₀ n ≤ xbar_low) ∧
        Antitone (p.dynamicTopLockInSanctions E.V_S E.α x₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hxHigh hxLow
    linarith [hxHigh.1, hxLow.2]
  · intro x₀ hx₀
    exact p.jointPreferenceBasinTop_long_run_nonDecreasing hHigh hx₀
  · intro x₀ hx₀
    exact p.jointPreferenceBasinLow_long_run_nonIncreasing hLow hx₀

/-- **General-`F` initial-condition selection.** General-transition sibling
of `equilibriumTop_initial_condition_selects`: both equilibrium state paths
are evolved by the maintained transition `F`. Under the same equilibrium and
the same two disjoint basin packages, high starts lock in with non-decreasing
sanctions and low starts wash out with non-increasing sanctions. -/
theorem equilibriumTop_initial_condition_selects_generalF
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar_high sbar_high xbar_low sbar_low : ℝ}
    (hHigh : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar_high sbar_high)
    (hLow : p.JointPreferenceBasinLow E.V_T E.V_S E.α xbar_low sbar_low)
    (hsep : xbar_low < xbar_high) :
    Disjoint (Set.Icc xbar_high 1) (Set.Icc 0 xbar_low) ∧
      (∀ x₀ ∈ Set.Icc xbar_high 1,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar_high 1) ∧
        (∀ n, sbar_high ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        (∀ n, xbar_high ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) ∧
      (∀ x₀ ∈ Set.Icc 0 xbar_low,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc 0 xbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ xbar_low) ∧
        Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hxHigh hxLow
    linarith [hxHigh.1, hxLow.2]
  · intro x₀ hx₀
    exact p.jointPreferenceBasinTopF_long_run_nonDecreasing hHigh hx₀
  · intro x₀ hx₀
    exact p.jointPreferenceBasinLowF_long_run_nonIncreasing hLow hx₀

end Params
end AbstractGame
end Sanctions
