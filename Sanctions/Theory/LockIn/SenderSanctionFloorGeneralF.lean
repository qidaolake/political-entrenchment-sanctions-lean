/-
Sanctions/Theory/LockIn/SenderSanctionFloorGeneralF.lean

**The Sender half of the defiance mechanism, general in the transition.**

Round BB, 2026-09-28; doc 110 item M1.

## What this file proves, in English

`Examples/AffineInstance/LockInShocked.lean` carries two theorems about the
Sender that say nothing about any continuation value on their hypothesis side:

* `V_S_free_sanction_floor` — if the Sender's stage payoff rises with the
  Target's political entrenchment at rate at least `m`, falls in its own
  sanction at rate at most `cS`, and the discounted continuation gain covers
  the stage loss, then the Sender's greatest forward-looking best response
  against its **constructed** equilibrium value is at least `c`;
* `no_top_gain_equilibrium_of_V_S_free_floor_condition` — the same condition,
  with one off-policy loss bound, rules out any feedback Stackelberg
  equilibrium in which the Target strictly gains from deviating at the top
  state.

Both assume the affine transition `F(x,s) = (1−δ)x + δs` on the whole square.
This file proves both without it.  The affine law is replaced by two chord
rates of the actual transition `p.F`:

* a **lower state chord** `g_lo` — raising the inherited state by `Δ` raises
  next period's state by at least `g_lo·Δ`, at every feasible sanction;
* a **lower sanction chord** `d_lo` — raising the sanction by `Δ` raises next
  period's state by at least `d_lo·Δ` (`SanctionLowerChordWith`, the existing
  predicate in `Theory/Basin/TransitionChords.lean`).

The margin becomes `cS·(1 − β_S·g_lo) ≤ β_S·m·d_lo`, which is literally the
affine margin `cS·(1 − β_S·(1−δ)) ≤ β_S·m·δ` at `g_lo = 1 − δ`, `d_lo = δ`.

### The declarations

* `lower_state_chord_rate_le_one` — the lower state chord rate is at most `1`
  (the transition maps the square into itself), so `1 − β_S·g_lo > 0` is
  derived, never assumed.
* `V_S_mem_lowerSlopeCone_of_lower_state_chord` — the constructed Sender value
  rises in the state at rate at least `m / (1 − β_S·g_lo)`, the general-`F`
  Benveniste–Scheinkman lower bound.  Needs `0 ≤ m` (see Rule 3 below).
* `senderDynObjective_monotoneOn_of_joint_sanction_chord` — the general-`F`
  mirror of `senderDynObjective_monotoneOn_of_sanction_loss_offset`: the
  Sender's forward-looking objective is non-decreasing on `[0,c]` when the
  stage loss is covered by the discounted value gain along the transition's
  actual sanction increment.
* `V_S_free_sanction_floor_of_joint_chords` — the floor in **joint-chord**
  form, sign-free: one joint chord in the state (stage plus discounted
  transition, as `V_S_mem_lowerSlopeCone_generalF` already takes) and one joint
  chord in the sanction.  This is the weakest form, and the one through which
  the affine original is recovered at every sign of `m`.
* `V_S_free_sanction_floor_generalF` — the floor in **named-chord** form, over
  `g_lo`, `d_lo` and the margin above.
* `no_top_gain_equilibrium_of_V_S_free_floor_condition_generalF` — the
  structural price, general in `F`.
* `lower_state_chord_of_stateChordBandAll` — adapter: the lower half of the
  existing band predicate `StateChordBandAll` (a `ChordEconomy` field) is the
  lower state chord used here.

## Scope (Rule 9)

These are universal statements over every `Params`.  Four of them are also
universal over the Target policy: the cone lemma
`V_S_mem_lowerSlopeCone_of_lower_state_chord`, the objective-monotonicity lemma
`senderDynObjective_monotoneOn_of_joint_sanction_chord` (any policy and any
value), and the two floor theorems `V_S_free_sanction_floor_of_joint_chords`
and `V_S_free_sanction_floor_generalF` (every continuous policy).  The price is
universal over every feedback Stackelberg equilibrium.  The two chord-rate
lemmas and the band adapter mention no policy.
The floor is about the **constructed** Sender value `p.V_S α hα` (Rule 15: a
Banach fixed point, never hypothesised); at an equilibrium it is the
equilibrium value by `equilibrium_V_S_eq_constructed`.  No witness is exhibited
here: the affine recovery is in
`Examples/AffineInstance/LockInShockedGeneralFBridge.lean`, and a non-affine
instance of the named-chord floor (at `qbParams`, transition `quadBumpF`; an
existence certificate in which the continuation channel is inactive) is in
`Examples/QuadBumpSenderFloor.lean`.  The three open
points recorded in `Theory/LockIn/PersistenceMargin.lean` for the affine
original (no interior tight floor; no non-degenerate witness; `V_S`-free is
not `α`-free) carry over unchanged.

## Rule 22

General in `F`.  No hypothesis mentions `p.δ`, `affineF`, or a functional form;
the transition enters only through `F_mem`, `F_mono_x`, `F_mono_s`, `F_diag`
(fields of `Params`) and the two chord rates.

## Rule 3 / Rule 13

No `Params` field, structure or `Prop` definition is added.  Relative to the
affine originals, `hF : p.F = affineF p.δ` is deleted and replaced by the two
lower chords, which `hF` implies at `(1 − δ, δ)` and which admit non-affine
laws (the de-affining exception of Rule 13).  One sign hypothesis appears in
the named-chord floor: `0 ≤ m`, the Sender's stage state chord is nonnegative.
It is needed because under a general transition the continuation enters as an
inequality (`F y₂ s − F y₁ s ≥ g_lo·(y₂ − y₁)`), which can be multiplied by the
value slope only when that slope is nonnegative; the affine law made it an
equality.  It is already a hypothesis of the affine
`no_top_gain_equilibrium_of_V_S_free_floor_condition`, and the affine floor at
`m < 0` is still recovered, from the sign-free joint-chord form.

So the de-affining exception does not cover the whole file.  The named-chord
floor `V_S_free_sanction_floor_generalF` carries the sign `0 ≤ m` (the
Sender's stage payoff rises weakly with the state).  The affine original
`V_S_free_sanction_floor` does not carry it, and `hF` does not imply it, so on
the affine instance the named-chord form loses the case `m < 0`.  Only the
joint-chord form `V_S_free_sanction_floor_of_joint_chords` is a net weakening
of `hF`; it is the de-affined sibling of record.  The general-`F` price also
carries `0 ≤ m`, but so does its affine original, so it loses nothing.
-/

import Sanctions.Theory.LockIn.PersistenceMargin
import Sanctions.Theory.Basin.TransitionChords
import Sanctions.Foundations.SemiconcaveJointComposition

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The lower state chord and the Sender value's slope -/

/-- **The lower state chord rate is at most one.**  Read the chord at the two
endpoints of the state space at sanction `0`: the successor state rises by at
least `g_lo`, but both successors lie in `[0,1]`, so the rise is at most `1`.

This is what makes `1 − β_S·g_lo` strictly positive without a hypothesis.
General in `F`: only `F_mem` is used. -/
theorem lower_state_chord_rate_le_one {g_lo : ℝ}
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s) :
    g_lo ≤ 1 := by
  have h0 : (0 : ℝ) ∈ Sanctions.S := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Sanctions.S := ⟨zero_le_one, le_refl 1⟩
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_refl 0, zero_le_one⟩
  have hc := h_state_chord 0 h0I 0 h0 1 h1 zero_le_one
  have hF0 := p.F_mem 0 0 h0 h0I
  have hF1 := p.F_mem 1 0 h1 h0I
  simp only [sub_zero, mul_one] at hc
  linarith [hF0.1, hF1.2]

/-- **`1 − β_S·g_lo` is strictly positive** for any lower state chord rate:
`g_lo ≤ 1` and `0 ≤ β_S < 1` give `β_S·g_lo ≤ β_S < 1`.  General in `F`. -/
theorem oneMinus_betaS_lowerStateChord_pos {g_lo : ℝ}
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s) :
    0 < 1 - p.β_S * g_lo := by
  have hle := p.lower_state_chord_rate_le_one h_state_chord
  have hβ0 : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hβ1 : p.β_S < 1 := p.β_S_mem.2
  nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr hle)]

/-- **The constructed Sender value rises in the state at rate at least
`m / (1 − β_S·g_lo)`, under any transition with lower state chord `g_lo`.**

The general-`F` sibling of `V_S_mem_lowerSlopeCone`
(`Examples/AffineInstance/ComplianceTower.lean`), which takes the affine law and
gets the Benveniste–Scheinkman constant `m / (1 − β_S·(1−δ))`.  Here the
transition's state response is only bounded *below*, by `g_lo`, and the same
closed form with `g_lo` in place of `1 − δ` is a lower bound on the value's
slope.

Inputs: the Sender's stage payoff along the policy `α` rises in the state at
rate at least `m ≥ 0` at every sanction (`h_state_slope`, the same hypothesis
as the affine original), and the transition's lower state chord is `g_lo`
(`h_state_chord`).  The argument feeds the joint chord of
`V_S_mem_lowerSlopeCone_generalF`: at `g = m / (1 − β_S·g_lo)` the identity
`g = m + β_S·g·g_lo` holds, and `g ≥ 0` lets the lower chord of `F` be
multiplied through.

Rule 15: `p.V_S α hα` is the Banach fixed point of `bellmanS_BCF`; its cone
membership is derived.  Rule 22: general in `F`. -/
theorem V_S_mem_lowerSlopeCone_of_lower_state_chord
    {α : ℝ → ℝ} (hα : Continuous α)
    {m g_lo : ℝ} (hm : 0 ≤ m)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s) :
    LowerSlopeOnValueOn (p.V_S α hα) (Set.Icc (0 : ℝ) 1)
      (Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S g_lo m) := by
  have hpos := p.oneMinus_betaS_lowerStateChord_pos h_state_chord
  have hβ0 : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  set g : ℝ := Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S g_lo m
    with hgdef
  have hg_nn : 0 ≤ g := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
    exact div_nonneg hm hpos.le
  have hid : m + p.β_S * g * g_lo = g := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
    field_simp
    ring
  refine p.V_S_mem_lowerSlopeCone_generalF hα ?_
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have hU := h_state_slope s hs y₁ hy₁ y₂ hy₂ hle
  have hFc := h_state_chord s hs y₁ hy₁ y₂ hy₂ hle
  have hFscaled : p.β_S * g * (g_lo * (y₂ - y₁))
      ≤ p.β_S * g * (p.F y₂ s - p.F y₁ s) :=
    mul_le_mul_of_nonneg_left hFc (mul_nonneg hβ0 hg_nn)
  have hid' : g * (y₂ - y₁) = m * (y₂ - y₁) + p.β_S * g * (g_lo * (y₂ - y₁)) := by
    linear_combination (-(y₂ - y₁)) * hid
  linarith

/-! ## 2. The Sender's objective in the sanction -/

/-- **The Sender's forward-looking objective is non-decreasing up to `c`,
under any transition.**

The general-`F` mirror of
`senderDynObjective_monotoneOn_of_sanction_loss_offset`
(`Examples/AffineInstance/LockInShocked.lean`).  The Sender's stage payoff may
fall in the sanction at rate at most `cS` on `[0,c]` (`h_stage_loss`); the
continuation value `V` rises in the state at rate at least `g`
(`hV_gain`); and on `[0,c]` the stage loss is covered by the discounted value
gain along the transition's *actual* sanction increment:
`cS·(s₂ − s₁) ≤ β_S·g·(F(x,s₂) − F(x,s₁))` (`h_joint_sanction_chord`).  Then
`s ↦ U_S(x, α x, s) + β_S·V(F(x,s))` is monotone on `[0,c]`.

No sign is needed on `g`: the value's slope floor is applied to the ordered
pair `F(x,s₁) ≤ F(x,s₂)` (`F_mono_s`), and the joint chord is stated against
the actual increment, so nothing is multiplied through an inequality.
General in `F` (Rule 22). -/
theorem senderDynObjective_monotoneOn_of_joint_sanction_chord
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {x c cS g : ℝ}
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (h_stage_loss : LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0 : ℝ) c) cS)
    (hV_gain : LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) g)
    (h_joint_sanction_chord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) c, ∀ s₂ ∈ Set.Icc (0 : ℝ) c, s₁ ≤ s₂ →
        cS * (s₂ - s₁) ≤ p.β_S * g * (p.F x s₂ - p.F x s₁)) :
    MonotoneOn (fun s => p.senderDynObjective V x (α x) s) (Set.Icc (0 : ℝ) c) := by
  intro s₁ hs₁ s₂ hs₂ hle
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hs₁I : s₁ ∈ Sanctions.I := ⟨hs₁.1, le_trans hs₁.2 hc.2⟩
  have hs₂I : s₂ ∈ Sanctions.I := ⟨hs₂.1, le_trans hs₂.2 hc.2⟩
  have hstage := h_stage_loss s₁ hs₁ s₂ hs₂ hle
  have hjoint := h_joint_sanction_chord s₁ hs₁ s₂ hs₂ hle
  have hF₁ : p.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hx hs₁I
  have hF₂ : p.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hx hs₂I
  have hFle : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hle
  have hord : Sanctions.clipS' (p.F x s₁) ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono hFle
  have hVslope := hV_gain (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) hord
  have hdF : dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
      = p.F x s₂ - p.F x s₁ := by
    rw [clipS'_dist_eq_of_mem hF₁ hF₂, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [hdF] at hVslope
  have hVscaled : p.β_S * (g * (p.F x s₂ - p.F x s₁))
      ≤ p.β_S * (V (Sanctions.clipS' (p.F x s₂)) - V (Sanctions.clipS' (p.F x s₁))) :=
    mul_le_mul_of_nonneg_left hVslope hβ
  change p.U_S x (α x) s₁ + p.β_S * V (Sanctions.clipS' (p.F x s₁))
    ≤ p.U_S x (α x) s₂ + p.β_S * V (Sanctions.clipS' (p.F x s₂))
  nlinarith [hstage, hVscaled, hjoint]

/-! ## 3. The `V_S`-free sanction floor, general in `F` -/

/-- **`V_S`-free equilibrium sanction floor, joint-chord form (general `F`,
sign-free).**

No hypothesis mentions a continuation value.  Two joint chords at one slope `g`
carry everything:

* `h_joint_state_chord` — raising the inherited state by `Δ` raises the
  Sender's stage payoff plus the discounted value of the induced rise in next
  period's state by at least `g·Δ`, at every sanction.  This is exactly the
  hypothesis of `V_S_mem_lowerSlopeCone_generalF`
  (`Theory/Bellman/SenderLowerSlopeCone.lean`), which places the constructed
  Sender value in the cone of slope `g`;
* `h_sanction_loss` — the Sender's stage payoff at `x` falls in its own
  sanction at rate at most `cS` on `[0,c]` (as in the affine original);
* `h_joint_sanction_chord` — on `[0,c]` that stage loss is covered by
  `β_S·g` times the transition's actual sanction increment at `x`.

Conclusion: the greatest forward-looking Sender best response against the
**constructed** Sender value `p.V_S α hα` is at least `c`.

This is the weakest form in the file and carries no sign condition on `g` or
on the stage chord, so the affine original `V_S_free_sanction_floor` follows
from it at every sign of `m`
(`Examples/AffineInstance/LockInShockedGeneralFBridge.lean`).

Rule 1: `dynamicTopRealizedRule` is the greatest element of the Sender's
dynamic argmax set.  Rule 15: `p.V_S α hα` is constructed.  Rule 22: general
in `F`. -/
theorem V_S_free_sanction_floor_of_joint_chords
    {α : ℝ → ℝ} (hα : Continuous α)
    {g cS x c : ℝ}
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (h_joint_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g * (y₂ - y₁)
          ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
            + p.β_S * g * (p.F y₂ s - p.F y₁ s))
    (h_sanction_loss :
      LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0 : ℝ) c) cS)
    (h_joint_sanction_chord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) c, ∀ s₂ ∈ Set.Icc (0 : ℝ) c, s₁ ≤ s₂ →
        cS * (s₂ - s₁) ≤ p.β_S * g * (p.F x s₂ - p.F x s₁)) :
    c ≤ p.dynamicTopRealizedRule (p.V_S α hα) α x :=
  p.realizedRule_ge_of_monotoneOn (p.V_S α hα) α hc
    (p.senderDynObjective_monotoneOn_of_joint_sanction_chord hx hc h_sanction_loss
      (p.V_S_mem_lowerSlopeCone_generalF hα h_joint_state_chord)
      h_joint_sanction_chord)

/-- **`V_S`-free equilibrium sanction floor, general in `F` (named-chord
form).**

The general-transition sibling of `V_S_free_sanction_floor`
(`Examples/AffineInstance/LockInShocked.lean:397`).  The affine law and its
rate `δ` are replaced by two chord rates of the actual transition:

* `h_state_chord` — lower state chord `g_lo`: raising the inherited state by
  `Δ` raises next period's state by at least `g_lo·Δ`, at every sanction;
* `h_sanction_chord` — lower sanction chord `d_lo`
  (`SanctionLowerChordWith`): raising the sanction by `Δ` raises next period's
  state by at least `d_lo·Δ`.

The remaining inputs are those of the affine original:

* `hm`, `h_state_slope` — the Sender's stage payoff along the policy `α` rises
  in the political state at rate at least `m ≥ 0`, at every sanction (the
  sanctioning coalition's political stake in the Target's entrenchment);
* `h_sanction_loss` — the Sender's stage payoff at `x` falls in its own
  sanction at rate at most `cS` on `[0,c]`;
* `h_margin` — `cS·(1 − β_S·g_lo) ≤ β_S·m·d_lo`: the stage loss rate is covered
  by the discounted continuation gain rate `β_S·(m/(1 − β_S·g_lo))·d_lo`, where
  `m/(1 − β_S·g_lo)` is the derived lower bound on the value's state slope
  (`V_S_mem_lowerSlopeCone_of_lower_state_chord`).  At `g_lo = 1 − δ`,
  `d_lo = δ` this is the affine margin verbatim.

Conclusion: the greatest forward-looking Sender best response against the
constructed Sender value is at least `c`.

`hm : 0 ≤ m` is the one hypothesis the affine original does not carry; see the
file header (Rule 3 / 13) for why the general transition needs it and how the
affine floor at `m < 0` is still recovered.  Rule 22: general in `F`. -/
theorem V_S_free_sanction_floor_generalF
    {α : ℝ → ℝ} (hα : Continuous α)
    {m cS g_lo d_lo x c : ℝ}
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (hm : 0 ≤ m)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (h_sanction_chord : p.SanctionLowerChordWith d_lo)
    (h_sanction_loss :
      LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0 : ℝ) c) cS)
    (h_margin : cS * (1 - p.β_S * g_lo) ≤ p.β_S * m * d_lo) :
    c ≤ p.dynamicTopRealizedRule (p.V_S α hα) α x := by
  have hpos := p.oneMinus_betaS_lowerStateChord_pos h_state_chord
  have hβ0 : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  set g : ℝ := Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S g_lo m
    with hgdef
  have hg_nn : 0 ≤ g := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
    exact div_nonneg hm hpos.le
  have hcS : cS ≤ p.β_S * g * d_lo := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def,
      show p.β_S * (m / (1 - p.β_S * g_lo)) * d_lo
          = (p.β_S * m * d_lo) / (1 - p.β_S * g_lo) from by ring,
      le_div_iff₀ hpos]
    exact h_margin
  have hcone := p.V_S_mem_lowerSlopeCone_of_lower_state_chord hα hm h_state_slope
    h_state_chord
  refine p.realizedRule_ge_of_monotoneOn (p.V_S α hα) α hc ?_
  refine p.senderDynObjective_monotoneOn_of_joint_sanction_chord hx hc
    h_sanction_loss hcone ?_
  intro s₁ hs₁ s₂ hs₂ hle
  have hs₁I : s₁ ∈ Sanctions.I := ⟨hs₁.1, le_trans hs₁.2 hc.2⟩
  have hs₂I : s₂ ∈ Sanctions.I := ⟨hs₂.1, le_trans hs₂.2 hc.2⟩
  have hch : Sanctions.TransitionChords.SanctionLowerChord p.F d_lo := h_sanction_chord
  have hd := hch hx hs₁I hs₂I hle
  have hsdiff : (0 : ℝ) ≤ s₂ - s₁ := by linarith
  have h1 : cS * (s₂ - s₁) ≤ p.β_S * g * d_lo * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right hcS hsdiff
  have h2 : p.β_S * g * (d_lo * (s₂ - s₁)) ≤ p.β_S * g * (p.F x s₂ - p.F x s₁) :=
    mul_le_mul_of_nonneg_left hd (mul_nonneg hβ0 hg_nn)
  linarith

/-! ## 4. The structural price, general in `F` -/

/-- **The structural price of the `V_S`-free floor condition, general in `F`.**

The general-transition sibling of
`no_top_gain_equilibrium_of_V_S_free_floor_condition`
(`Examples/AffineInstance/LockInShocked.lean:465`), with the affine law and `δ`
replaced by the lower state chord `g_lo` and the lower sanction chord `d_lo`
of the actual transition.

At a nonnegative stage state chord `m ≥ 0`, the floor condition's hypotheses —
the stage state chord `m` along the equilibrium policy, the transition's two
lower chords, the stage sanction-loss rate `cS` at the top state for the
equilibrium action (`h_loss0`) **and** for one deviation action `E.α 1 + t`
(`h_loss1`, an off-policy input the floor condition does not itself supply),
and the margin `cS·(1 − β_S·g_lo) ≤ β_S·m·d_lo` — discharge every hypothesis
of `AbsorbingTop.no_equilibrium_of_slope_and_top_gain`
(`Theory/Equilibrium/AbsorbingTopObstruction.lean`) at
`(m := m/(1 − β_S·g_lo), κ := d_lo, c := cS)`.  Hence no feedback Stackelberg
equilibrium in which the Target strictly gains at the top state
(`hgain`: `U_T(1, α 1, 1) < U_T(1, α 1 + t, 1)`) satisfies the condition.

Where the transition enters: the affine law's "the successor falls from the top
at rate `δ`" becomes the lower sanction chord read between `s` and `1` at the
top state, together with `F_diag` (`F(1,1) = 1`, a `Params` field).

The two scope limits of the affine original stand unchanged: `h_loss1` is
off-policy, and the theorem is vacuous at both witness economies of
`Examples/SenderConeWitness.lean`.  Rule 22: general in `F`. -/
theorem no_top_gain_equilibrium_of_V_S_free_floor_condition_generalF
    (E : p.FeedbackStackelbergEquilibriumTop)
    {m cS g_lo d_lo t : ℝ} (hm : 0 ≤ m)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (E.α y₂) s - p.U_S y₁ (E.α y₁) s)
    (h_state_chord :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        g_lo * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (h_sanction_chord : p.SanctionLowerChordWith d_lo)
    (h_loss0 : LowerLossSlopeOn (fun s => p.U_S 1 (E.α 1) s) (Set.Icc (0 : ℝ) 1) cS)
    (h_loss1 : LowerLossSlopeOn (fun s => p.U_S 1 (E.α 1 + t) s) (Set.Icc (0 : ℝ) 1) cS)
    (h_margin : cS * (1 - p.β_S * g_lo) ≤ p.β_S * m * d_lo)
    (hdev : E.α 1 + t ∈ Sanctions.I)
    (hgain : p.U_T 1 (E.α 1) 1 < p.U_T 1 (E.α 1 + t) 1) : False := by
  have hpos := p.oneMinus_betaS_lowerStateChord_pos h_state_chord
  set g : ℝ := Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S g_lo m
    with hgdef
  have hg_nn : 0 ≤ g := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
    exact div_nonneg hm hpos.le
  have hcone0 := p.V_S_mem_lowerSlopeCone_of_lower_state_chord E.hα hm
    h_state_slope h_state_chord
  have hcone : LowerSlopeOnValueOn E.V_S (Set.Icc (0 : ℝ) 1) g := by
    rw [p.equilibrium_V_S_eq_constructed E]; exact hcone0
  have h1S : (1 : ℝ) ∈ (Sanctions.S : Set ℝ) := ⟨zero_le_one, le_refl 1⟩
  have hch : Sanctions.TransitionChords.SanctionLowerChord p.F d_lo := h_sanction_chord
  refine Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain
    p E g d_lo cS t hg_nn ⟨1, h1S⟩ rfl ?_ ?_ ?_ ?_ ?_ hdev hgain
  · -- `hslope`: the equilibrium Sender value rises to the top at rate ≥ g.
    intro y
    have hyle : y ≤ (⟨1, h1S⟩ : ↥(Sanctions.S : Set ℝ)) := y.property.2
    have h := hcone y ⟨1, h1S⟩ y.property h1S hyle
    rwa [dist_eq_sub_of_le hyle] at h
  · -- `htrans`: the lower sanction chord at the top state, with `F(1,1) = 1`.
    intro s hs
    have hd := hch (x := 1) (s₁ := s) (s₂ := 1) h1S hs h1S hs.2
    rw [p.F_diag 1] at hd
    exact hd
  · -- `hshade0`: the equilibrium action's static shading gain is ≤ cS·(1−s).
    intro s hs
    have h := h_loss0 s ⟨hs.1, hs.2⟩ 1 ⟨zero_le_one, le_refl 1⟩ hs.2
    simp only at h
    linarith
  · -- `hshade1`: same bound at the deviation action `E.α 1 + t`.
    intro s hs
    have h := h_loss1 s ⟨hs.1, hs.2⟩ 1 ⟨zero_le_one, le_refl 1⟩ hs.2
    simp only at h
    linarith
  · -- `hc`: cS ≤ β_S · g · d_lo, i.e. exactly the general-`F` margin.
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def,
      show p.β_S * (m / (1 - p.β_S * g_lo)) * d_lo
          = (p.β_S * m * d_lo) / (1 - p.β_S * g_lo) from by ring,
      le_div_iff₀ hpos]
    exact h_margin

/-! ## 5. Adapter from the existing band predicate -/

/-- **The lower half of the state chord band is the lower state chord.**
`StateChordBandAll F glo ghi` (`Foundations/SemiconcaveJointComposition.lean`;
a field of `ChordEconomy`) bounds the transition's state response from both
sides at every sanction; the theorems above consume only the lower side.  This
adapter supplies `h_state_chord` from it.  General in `F`. -/
theorem lower_state_chord_of_stateChordBandAll {glo ghi : ℝ}
    (hband : Sanctions.Semiconcave.StateChordBandAll p.F glo ghi) :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      glo * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s :=
  fun s hs y₁ hy₁ y₂ hy₂ hle => (hband s hs y₁ hy₁ y₂ hy₂ hle).1

end Params
end AbstractGame

end -- noncomputable section

end Sanctions

/-! ## Axiom hygiene (Rule 10) -/

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.lower_state_chord_rate_le_one
#print axioms Sanctions.AbstractGame.Params.oneMinus_betaS_lowerStateChord_pos
#print axioms Sanctions.AbstractGame.Params.V_S_mem_lowerSlopeCone_of_lower_state_chord
#print axioms Sanctions.AbstractGame.Params.senderDynObjective_monotoneOn_of_joint_sanction_chord
#print axioms Sanctions.AbstractGame.Params.V_S_free_sanction_floor_of_joint_chords
#print axioms Sanctions.AbstractGame.Params.V_S_free_sanction_floor_generalF
#print axioms Sanctions.AbstractGame.Params.no_top_gain_equilibrium_of_V_S_free_floor_condition_generalF
#print axioms Sanctions.AbstractGame.Params.lower_state_chord_of_stateChordBandAll
