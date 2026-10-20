/-
Sanctions/Theory/Basin/StageFlip.lean

**Stage-payoff flip structure: derived tipping thresholds from
stage supermodularity in (sanction, state).**

Round A of the stage-flip upgrade (user-approved 2026-06-10). The two
new paper-facing primitives are *stage complementarity* conditions in
chord (increasing-differences) form:

* `SenderStageID` — for every fixed Target action `a`, the Sender
  stage payoff `U_S(x, a, s)` has increasing differences in `(s, x)`:
  raising the hardline political state `x` weakly raises the Sender's
  chord payoff from any sanction increase `s₁ → s₂`. Order form of
  `∂²U_S/∂s∂x ≥ 0` (the strict C² form `> 0` of the paper assumption
  implies this; strict refinements land in a later round).
* `TargetStageID` — same for the Target stage payoff `U_T`: rally
  around the flag — a harder state weakly raises the Target
  incumbent's chord payoff from being sanctioned more.

From these (plus boundary sign conditions at the *single* states
`x = 0, 1`), the basin geography is **derived** rather than assumed:

* `targetFlipSet sbar` — states at which every sanction chord in the
  fixed high range `[s̄, 1]` weakly raises the Target stage payoff,
  uniformly over feasible actions. Upward closed (`TargetStageID`),
  closed (continuity), hence exactly an upper interval
  `[targetFlipPivot, 1]`.
* `senderFloorFlipSet sbar m` — states at which every sanction chord
  in the fixed floor range `[0, s̄]` has slope at least `m`, uniformly
  over feasible actions. Same structure. At wedge level
  `m = m_S > β_S·K_S·δ` its pivot is the *dynamic* Sender threshold;
  at `m = 0` the *static* flip. `senderFlipPivot_le_of_level_le` is
  the two-threshold comparison (static flip ≤ dynamic pivot).
* `senderFlipFrontier sbar m a` — the per-action threshold. Under the
  R28 action-complementarity sign (`SenderActionDD`,
  `∂²U_S/∂s∂a ≤ 0` in chord form — an existing project condition, not
  new surface), the frontier is monotone non-decreasing in the action
  (`senderFlipFrontier_mono`: *compliance placates*) and the uniform
  flip set collapses to the full-compliance slice
  (`senderFloorFlipSet_eq_at_one`): the certified basin opens where
  sanctioning clears the wedge even against a fully compliant Target.

Range conventions (deliberate, Rule-11-safe conservatism): the flip
sets use *fixed* chord ranges — `[s̄, 1]` (Target) and `[0, s̄]`
(Sender floor) — rather than the per-state ranges `[max(x,s̄), 1]` /
`[0, max(x,s̄)]` consumed downstream. Fixed ranges make the sets
closed and upward closed by `StageID` alone; the per-state Target
range is recovered by restriction
(`targetFlipSet.monotoneOn_high_range` — the per-state range is a
subset of the fixed range), so the derived pivot is a conservative
(weakly higher) certified threshold. The Sender's *above-floor*
chords (`s ∈ (s̄, max(x,s̄)]`, nonvacuous only at basin states above
the sanction floor) are NOT derivable from the floor flip set — they
remain an equilibrium-action condition supplied at the certificate
layer (Round B), exactly as analyzed in the design discussion.

## Rule compliance

**Rule 3.** `SenderStageID` / `TargetStageID` are the two
user-approved new primitives (stop-and-confirm completed 2026-06-10);
the boundary sign conditions enter as theorem hypotheses of the form
`1 ∈ flipSet` / `0 ∉ flipSet`. `SenderActionDD` restates the existing
R28 cross-partial sign in chord form — not a new primitive; theorems
take it as an explicit hypothesis exactly as R28 consumers do.

**Round BH-1 (item BH1.8, 2026-10-06): local stage complementarity.**
`TargetStageIDOn R` and `SenderStageIDOn R` restrict the two primitives
to a sanction range `R`. Each flip set reads its chords only on its own
fixed range — `[s̄, 1]` for the Target, `[0, s̄]` for the Sender floor —
so upward closure, the interval characterisation, interiority and the
bundled tipping thresholds need stage complementarity only on that range
(the `_of_stageIDOn` siblings). They also drop `s̄ ∈ [0, 1]`, which the
global forms used only to place the chord range inside `[0, 1]` before
applying the global primitive. These are not new primitives: the global
primitives imply them (`targetStageIDOn_of_targetStageID`,
`senderStageIDOn_of_senderStageID`, through
`IncreasingDifferencesOn.mono`), and `example`s recover the global
tipping thresholds. `targetFlipPivot_feasible` and
`senderFlipPivot_feasible` record that each derived pivot lies in
`[0, 1]` with no hypothesis at all.

**Rule 5.** Fully parametric over `(p, sbar, m, a)` — no witness
content.

**Rule 19.** The generic threshold machinery (upward-closed sets,
pivot membership, pivot comparison) lives in
`Foundations/MonotoneThreshold.lean`; this file is the wiring to the
sanction game's stage payoffs.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Foundations.MilgromShannon
import Sanctions.Foundations.MonotoneThreshold

namespace Sanctions

open Set

noncomputable section

/-! ## Restricting increasing differences to a sub-rectangle -/

namespace MilgromShannon

/-- **Increasing differences restrict to sub-rectangles** (round BH-1, item
BH1.8). If `f` has increasing differences on `S × T`, it has them on every
`S' × T'` with `S' ⊆ S` and `T' ⊆ T`: each chord comparison on the smaller
rectangle is one of the comparisons on the larger. Pure order fact, no
economics; no transition enters, so the general-`F` / affine distinction
does not arise. -/
theorem IncreasingDifferencesOn.mono {S T S' T' : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : IncreasingDifferencesOn S T f) (hS : S' ⊆ S) (hT : T' ⊆ T) :
    IncreasingDifferencesOn S' T' f := by
  intro s s' x x' hs hs' hss hx hx' hxx
  exact h (hS hs) (hS hs') hss (hT hx) (hT hx') hxx

end MilgromShannon

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The two stage-complementarity primitives (chord form) -/

/-- **Sender stage complementarity (new primitive, Round A).** For
every fixed feasible action `a`, the Sender stage payoff, read as a
function of the sanction (choice) and the state (parameter), has
increasing differences on `[0,1] × [0,1]`: for `s₁ ≤ s₂` and
`x₁ ≤ x₂`,

  `U_S(x₁, a, s₂) − U_S(x₁, a, s₁) ≤ U_S(x₂, a, s₂) − U_S(x₂, a, s₁)`.

Order-language form of `∂²U_S/∂s∂x ≥ 0` — a harder political state
raises the Sender's marginal value of sanctioning (the public-choice
channel: sanction-benefiting interests strengthen under
confrontation). -/
def SenderStageID : Prop :=
  ∀ a ∈ Sanctions.I,
    Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s x => p.U_S x a s)

/-- **Target stage complementarity (new primitive, Round A).** Same
chord condition for the Target stage payoff `U_T`: a harder political
state raises the Target incumbent's marginal payoff from being
sanctioned (rally around the flag / habituation). Order form of
`∂²U_T/∂s∂x ≥ 0`. -/
def TargetStageID : Prop :=
  ∀ a ∈ Sanctions.I,
    Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s x => p.U_T x a s)

/-- **R28 action-complementarity sign, chord form (NOT new
surface).** For every fixed state `x`, the Sender's sanction chord is
non-increasing in the Target action: `∂²U_S/∂s∂a ≤ 0` — the Sender's
marginal value of sanctioning falls as the Target complies more. This
restates the existing R28 cross-partial condition as a named
predicate; theorems consume it as an explicit hypothesis exactly as
the R28 σ-antitone machinery does. -/
def SenderActionDD : Prop :=
  ∀ x ∈ Sanctions.I,
    Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => p.U_S x a s)

/-! ## Local stage complementarity (round BH-1, item BH1.8) -/

/-- **Sender stage complementarity on a sanction range `R`.** The chord
condition of `SenderStageID`, required only for sanctions in `R` (states and
actions still range over `[0, 1]`): a harder political state weakly raises the
Sender's gain from any sanction increase within `R`. The Sender floor flip set
at floor `s̄` reads chords only on `R = [0, s̄]`, so that is the only range its
consumers need. A weakening of the Round-A primitive, not a new one
(`senderStageIDOn_of_senderStageID`). A stage-payoff condition: no
transition enters. -/
def SenderStageIDOn (R : Set ℝ) : Prop :=
  ∀ a ∈ Sanctions.I,
    Sanctions.MilgromShannon.IncreasingDifferencesOn R Sanctions.I
      (fun s x => p.U_S x a s)

/-- **Target stage complementarity on a sanction range `R`.** The chord
condition of `TargetStageID`, required only for sanctions in `R`: a harder
political state weakly raises the Target incumbent's gain from being
sanctioned more within `R` (rally around the flag on that range). The Target
flip set at floor `s̄` reads chords only on `R = [s̄, 1]`. A weakening of the
Round-A primitive, not a new one (`targetStageIDOn_of_targetStageID`). A
stage-payoff condition: no transition enters. -/
def TargetStageIDOn (R : Set ℝ) : Prop :=
  ∀ a ∈ Sanctions.I,
    Sanctions.MilgromShannon.IncreasingDifferencesOn R Sanctions.I
      (fun s x => p.U_T x a s)

/-- The global Sender primitive gives the local one on every feasible
sanction range (restriction of the chord condition; no transition enters). -/
theorem senderStageIDOn_of_senderStageID (hID : p.SenderStageID)
    {R : Set ℝ} (hR : R ⊆ Sanctions.I) : p.SenderStageIDOn R :=
  fun a ha => (hID a ha).mono hR subset_rfl

/-- The global Target primitive gives the local one on every feasible
sanction range (restriction of the chord condition; no transition enters). -/
theorem targetStageIDOn_of_targetStageID (hID : p.TargetStageID)
    {R : Set ℝ} (hR : R ⊆ Sanctions.I) : p.TargetStageIDOn R :=
  fun a ha => (hID a ha).mono hR subset_rfl

/-! ## Flip sets

Fixed-range chord conditions, uniform over feasible actions. The
membership Prop is stated with explicit binders (not `Set.sep`) so
that downstream consumers can `rintro`/apply it directly. -/

/-- **Per-action Target flip set.** States `x ∈ [0,1]` at which every
sanction chord `s₁ ≤ s₂` in the fixed high range `[s̄, 1]` weakly
raises the Target stage payoff at action `a`:
`U_T(x, a, s₁) ≤ U_T(x, a, s₂)`. -/
def targetFlipSetAt (sbar a : ℝ) : Set ℝ :=
  Sanctions.I ∩ {x | ∀ s₁ ∈ Set.Icc sbar 1, ∀ s₂ ∈ Set.Icc sbar 1,
    s₁ ≤ s₂ → p.U_T x a s₁ ≤ p.U_T x a s₂}

/-- **Uniform Target flip set.** States at which the per-action chord
condition holds for *every* feasible action — the action-free
sufficient statistic that cuts the endogeneity of the equilibrium
action `α(x)` (which always lies in `[0,1]`). -/
def targetFlipSet (sbar : ℝ) : Set ℝ :=
  Sanctions.I ∩ {x | ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Set.Icc sbar 1,
    ∀ s₂ ∈ Set.Icc sbar 1, s₁ ≤ s₂ → p.U_T x a s₁ ≤ p.U_T x a s₂}

/-- **Per-action Sender floor flip set at slope level `m`.** States
`x ∈ [0,1]` at which every sanction chord `s₁ ≤ s₂` in the fixed
floor range `[0, s̄]` has chord slope at least `m`:
`m·(s₂ − s₁) ≤ U_S(x, a, s₂) − U_S(x, a, s₁)`. At `m = 0` this is the
static flip ("sanctioning stops being a stage loss"); at the wedge
level `m = m_S > β_S·K_S·δ` it is the dynamic-certifiable flip (the
stage slope beats the worst-case continuation drag). -/
def senderFloorFlipSetAt (sbar m a : ℝ) : Set ℝ :=
  Sanctions.I ∩ {x | ∀ s₁ ∈ Set.Icc (0 : ℝ) sbar, ∀ s₂ ∈ Set.Icc (0 : ℝ) sbar,
    s₁ ≤ s₂ → m * (s₂ - s₁) ≤ p.U_S x a s₂ - p.U_S x a s₁}

/-- **Uniform Sender floor flip set at slope level `m`.** The
per-action condition holding for every feasible action. -/
def senderFloorFlipSet (sbar m : ℝ) : Set ℝ :=
  Sanctions.I ∩ {x | ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Set.Icc (0 : ℝ) sbar,
    ∀ s₂ ∈ Set.Icc (0 : ℝ) sbar,
    s₁ ≤ s₂ → m * (s₂ - s₁) ≤ p.U_S x a s₂ - p.U_S x a s₁}

/-! ## Derived pivots -/

/-- **Derived Target tipping threshold** — the infimum of the uniform
Target flip set. Previously a free certificate location (`xT`); now a
defined object. -/
def targetFlipPivot (sbar : ℝ) : ℝ := sInf (p.targetFlipSet sbar)

/-- **Derived Sender tipping threshold at slope level `m`** — the
infimum of the uniform Sender floor flip set. At the wedge level this
is the dynamic pivot `xhat_S`; at `m = 0` the static flip `x_S`. -/
def senderFlipPivot (sbar m : ℝ) : ℝ := sInf (p.senderFloorFlipSet sbar m)

/-- **Per-action Sender flip frontier** `a ↦ x_S(a)` — the per-action
threshold whose monotonicity in `a` ("compliance placates") is
`senderFlipFrontier_mono`. -/
def senderFlipFrontier (sbar m a : ℝ) : ℝ :=
  sInf (p.senderFloorFlipSetAt sbar m a)

/-! ## Upward closure (from the stage-complementarity primitives) -/

/-- **Target flip set is upward closed in `[0, 1]`.** Membership
propagates to higher states: each chord is weakly larger at a higher
state (`TargetStageID`), and the chord range is fixed. -/
theorem targetFlipSet_upwardClosedIn {sbar : ℝ}
    (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I) :
    Sanctions.MonotoneThreshold.UpwardClosedIn (p.targetFlipSet sbar) 0 1 := by
  constructor
  · exact Set.inter_subset_left
  · rintro x ⟨hxI, hx⟩ y hyI hxy
    refine ⟨hyI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hs₁I : s₁ ∈ Sanctions.I := ⟨le_trans hsbar.1 hs₁.1, hs₁.2⟩
    have hs₂I : s₂ ∈ Sanctions.I := ⟨le_trans hsbar.1 hs₂.1, hs₂.2⟩
    have hchord := hID a ha hs₁I hs₂I hs hxI hyI hxy
    have h0 := hx a ha s₁ hs₁ s₂ hs₂ hs
    linarith

/-- **Sender floor flip set is upward closed in `[0, 1]`.** Same
propagation via `SenderStageID` on the fixed floor range. -/
theorem senderFloorFlipSet_upwardClosedIn {sbar m : ℝ}
    (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I) :
    Sanctions.MonotoneThreshold.UpwardClosedIn
      (p.senderFloorFlipSet sbar m) 0 1 := by
  constructor
  · exact Set.inter_subset_left
  · rintro x ⟨hxI, hx⟩ y hyI hxy
    refine ⟨hyI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hs₁I : s₁ ∈ Sanctions.I := ⟨hs₁.1, le_trans hs₁.2 hsbar.2⟩
    have hs₂I : s₂ ∈ Sanctions.I := ⟨hs₂.1, le_trans hs₂.2 hsbar.2⟩
    have hchord := hID a ha hs₁I hs₂I hs hxI hyI hxy
    have h0 := hx a ha s₁ hs₁ s₂ hs₂ hs
    linarith

/-! ## Closedness (from joint continuity of the stage payoffs) -/

/-- Continuity of a single-state slice of a jointly continuous
ternary payoff: `x ↦ U(x, a, s)`. -/
private theorem continuous_slice
    {U : ℝ → ℝ → ℝ → ℝ}
    (hU : Continuous (fun (xas : ℝ × ℝ × ℝ) => U xas.1 xas.2.1 xas.2.2))
    (a s : ℝ) : Continuous (fun x : ℝ => U x a s) := by
  have h : Continuous (fun x : ℝ => ((x, a, s) : ℝ × ℝ × ℝ)) :=
    continuous_id.prodMk continuous_const
  exact hU.comp h

/-- **The Target flip set is closed.** Intersection of the closed
ambient interval with closed chord conditions (continuity of `U_T`
in the state). -/
theorem isClosed_targetFlipSet (sbar : ℝ) :
    IsClosed (p.targetFlipSet sbar) := by
  apply IsClosed.inter isClosed_Icc
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro a _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₁ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₂ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_imp
  exact isClosed_le (continuous_slice p.U_T_continuous a s₁)
    (continuous_slice p.U_T_continuous a s₂)

/-- **The Sender floor flip set is closed.** -/
theorem isClosed_senderFloorFlipSet (sbar m : ℝ) :
    IsClosed (p.senderFloorFlipSet sbar m) := by
  apply IsClosed.inter isClosed_Icc
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro a _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₁ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₂ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_imp
  exact isClosed_le continuous_const
    (((continuous_slice p.U_S_continuous a s₂).sub
      (continuous_slice p.U_S_continuous a s₁)))

/-! ## Tipping thresholds: membership, characterization, interiority

The boundary sign conditions enter as the two single-state
hypotheses: `1 ∈ flipSet` (the flip has happened at the top state —
nonemptiness) and `0 ∉ flipSet` (it has not happened at the bottom
state — interiority). -/

/-- **The Target flip set is exactly `[targetFlipPivot, 1]`.** The
basin geography on the Target side is a derived object: the chord
condition holds at a state iff the state is at or above the pivot. -/
theorem targetFlipSet_eq_Icc {sbar : ℝ}
    (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar) :
    p.targetFlipSet sbar = Set.Icc (p.targetFlipPivot sbar) 1 :=
  (p.targetFlipSet_upwardClosedIn hID hsbar).eq_Icc_pivot
    (p.isClosed_targetFlipSet sbar) ⟨1, h1⟩

/-- **The Target pivot satisfies its own flip condition** (the
crossing is attained). -/
theorem targetFlipPivot_mem {sbar : ℝ}
    (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar) :
    p.targetFlipPivot sbar ∈ p.targetFlipSet sbar :=
  (p.targetFlipSet_upwardClosedIn hID hsbar).pivot_mem
    (p.isClosed_targetFlipSet sbar) ⟨1, h1⟩

/-- **Target pivot interiority.** If the flip has not happened at
`x = 0` (boundary sign), the derived threshold is strictly
positive. -/
theorem targetFlipPivot_pos {sbar : ℝ}
    (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h0 : (0 : ℝ) ∉ p.targetFlipSet sbar) :
    0 < p.targetFlipPivot sbar :=
  (p.targetFlipSet_upwardClosedIn hID hsbar).lo_lt_pivot
    (p.isClosed_targetFlipSet sbar) ⟨1, h1⟩ h0

/-- **Target pivot is feasible**: `targetFlipPivot ∈ [0, 1]`. -/
theorem targetFlipPivot_mem_I {sbar : ℝ}
    (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar) :
    p.targetFlipPivot sbar ∈ Sanctions.I :=
  (p.targetFlipPivot_mem hID hsbar h1).1

/-- **The Sender floor flip set is exactly `[senderFlipPivot, 1]`.** -/
theorem senderFloorFlipSet_eq_Icc {sbar m : ℝ}
    (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m) :
    p.senderFloorFlipSet sbar m = Set.Icc (p.senderFlipPivot sbar m) 1 :=
  (p.senderFloorFlipSet_upwardClosedIn hID hsbar).eq_Icc_pivot
    (p.isClosed_senderFloorFlipSet sbar m) ⟨1, h1⟩

/-- **The Sender pivot satisfies its own flip condition.** -/
theorem senderFlipPivot_mem {sbar m : ℝ}
    (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m) :
    p.senderFlipPivot sbar m ∈ p.senderFloorFlipSet sbar m :=
  (p.senderFloorFlipSet_upwardClosedIn hID hsbar).pivot_mem
    (p.isClosed_senderFloorFlipSet sbar m) ⟨1, h1⟩

/-- **Sender pivot interiority.** -/
theorem senderFlipPivot_pos {sbar m : ℝ}
    (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m)
    (h0 : (0 : ℝ) ∉ p.senderFloorFlipSet sbar m) :
    0 < p.senderFlipPivot sbar m :=
  (p.senderFloorFlipSet_upwardClosedIn hID hsbar).lo_lt_pivot
    (p.isClosed_senderFloorFlipSet sbar m) ⟨1, h1⟩ h0

/-- **Sender pivot is feasible.** -/
theorem senderFlipPivot_mem_I {sbar m : ℝ}
    (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m) :
    p.senderFlipPivot sbar m ∈ Sanctions.I :=
  (p.senderFlipPivot_mem hID hsbar h1).1

/-! ## Two-threshold structure: static flip ≤ dynamic pivot -/

/-- **Level monotonicity of the Sender flip set**: a higher slope
level is a more demanding condition. -/
theorem senderFloorFlipSet_anti_level {sbar m m' : ℝ}
    (hmm' : m ≤ m') :
    p.senderFloorFlipSet sbar m' ⊆ p.senderFloorFlipSet sbar m := by
  rintro x ⟨hxI, hx⟩
  refine ⟨hxI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
  have h' := hx a ha s₁ hs₁ s₂ hs₂ hs
  have : m * (s₂ - s₁) ≤ m' * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right hmm' (by linarith)
  linarith

/-- **Two-threshold comparison (static flip ≤ dynamic pivot).** The
zero-level (static) flip point is weakly below the wedge-level
(dynamic) pivot: between them lies the *contested band*, where the
Sender's stage incentive has flipped but the worst-case
forward-looking drag is not yet dominated. -/
theorem senderFlipPivot_le_of_level_le {sbar m m' : ℝ}
    (hmm' : m ≤ m')
    (hne' : (p.senderFloorFlipSet sbar m').Nonempty) :
    p.senderFlipPivot sbar m ≤ p.senderFlipPivot sbar m' :=
  Sanctions.MonotoneThreshold.pivot_le_pivot_of_subset
    (p.senderFloorFlipSet_anti_level hmm')
    ⟨0, fun _ hx => hx.1.1⟩ hne'

/-! ## Action frontier: monotonicity and the full-compliance collapse -/

/-- **Uniform set ⊆ per-action set** (specialization to any feasible
action). -/
theorem senderFloorFlipSet_subset_at {sbar m a : ℝ}
    (ha : a ∈ Sanctions.I) :
    p.senderFloorFlipSet sbar m ⊆ p.senderFloorFlipSetAt sbar m a := by
  rintro x ⟨hxI, hx⟩
  exact ⟨hxI, fun s₁ hs₁ s₂ hs₂ hs => hx a ha s₁ hs₁ s₂ hs₂ hs⟩

/-- **Action monotonicity of the per-action flip sets** (from the R28
action-complementarity sign): at a *more compliant* action the chord
condition is more demanding, so the flip set is smaller. -/
theorem senderFloorFlipSetAt_anti_action {sbar m : ℝ}
    (hDD : p.SenderActionDD) (hsbar : sbar ∈ Sanctions.I)
    {a a' : ℝ} (ha : a ∈ Sanctions.I) (ha' : a' ∈ Sanctions.I)
    (haa : a ≤ a') :
    p.senderFloorFlipSetAt sbar m a' ⊆ p.senderFloorFlipSetAt sbar m a := by
  rintro x ⟨hxI, hx⟩
  refine ⟨hxI, fun s₁ hs₁ s₂ hs₂ hs => ?_⟩
  have hs₁I : s₁ ∈ Sanctions.I := ⟨hs₁.1, le_trans hs₁.2 hsbar.2⟩
  have hs₂I : s₂ ∈ Sanctions.I := ⟨hs₂.1, le_trans hs₂.2 hsbar.2⟩
  have hchord := hDD x hxI hs₁I hs₂I hs ha ha' haa
  have h' := hx s₁ hs₁ s₂ hs₂ hs
  linarith

/-- **Frontier monotonicity: compliance placates.** Under the R28
sign, the per-action Sender threshold `x_S(a)` is non-decreasing in
the action: against a more compliant Target, a harder state is needed
before sanctioning clears the slope level. Derived, not assumed. -/
theorem senderFlipFrontier_mono {sbar m : ℝ}
    (hDD : p.SenderActionDD) (hsbar : sbar ∈ Sanctions.I)
    {a a' : ℝ} (ha : a ∈ Sanctions.I) (ha' : a' ∈ Sanctions.I)
    (haa : a ≤ a')
    (hne' : (p.senderFloorFlipSetAt sbar m a').Nonempty) :
    p.senderFlipFrontier sbar m a ≤ p.senderFlipFrontier sbar m a' :=
  Sanctions.MonotoneThreshold.pivot_le_pivot_of_subset
    (p.senderFloorFlipSetAt_anti_action hDD hsbar ha ha' haa)
    ⟨0, fun _ hx => hx.1.1⟩ hne'

/-- **Full-compliance collapse of the uniform flip set.** Under the
R28 sign, the uniform-in-action flip set *equals* its slice at the
maximal action `a = 1`: the binding action for the Sender's flip is
full compliance, so the conservative uniform pivot has the closed
form `x_S(1)`. ("The certified basin opens where sanctioning clears
the wedge even against a fully compliant Target.") -/
theorem senderFloorFlipSet_eq_at_one {sbar m : ℝ}
    (hDD : p.SenderActionDD) (hsbar : sbar ∈ Sanctions.I) :
    p.senderFloorFlipSet sbar m = p.senderFloorFlipSetAt sbar m 1 := by
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  apply Set.Subset.antisymm
  · exact p.senderFloorFlipSet_subset_at h1I
  · rintro x ⟨hxI, hx⟩
    refine ⟨hxI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hs₁I : s₁ ∈ Sanctions.I := ⟨hs₁.1, le_trans hs₁.2 hsbar.2⟩
    have hs₂I : s₂ ∈ Sanctions.I := ⟨hs₂.1, le_trans hs₂.2 hsbar.2⟩
    have hchord := hDD x hxI hs₁I hs₂I hs ha h1I ha.2
    have h' := hx s₁ hs₁ s₂ hs₂ hs
    linarith

/-- **Closed form for the uniform Sender pivot**: it equals the
full-compliance frontier value `x_S(1)`. -/
theorem senderFlipPivot_eq_frontier_one {sbar m : ℝ}
    (hDD : p.SenderActionDD) (hsbar : sbar ∈ Sanctions.I) :
    p.senderFlipPivot sbar m = p.senderFlipFrontier sbar m 1 := by
  unfold senderFlipPivot senderFlipFrontier
  rw [p.senderFloorFlipSet_eq_at_one hDD hsbar]

/-! ## Bundled tipping-threshold propositions (headline shape) -/

/-- **Tipping threshold, Target side (bundled).** Under Target stage
complementarity and the two boundary signs, the derived pivot is
interior (`0 < x̄_T ≤ 1`) and the flip region is exactly the upper
interval `[x̄_T, 1]`. -/
theorem target_tipping_threshold {sbar : ℝ}
    (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h0 : (0 : ℝ) ∉ p.targetFlipSet sbar) :
    0 < p.targetFlipPivot sbar ∧ p.targetFlipPivot sbar ≤ 1 ∧
      p.targetFlipSet sbar = Set.Icc (p.targetFlipPivot sbar) 1 :=
  ⟨p.targetFlipPivot_pos hID hsbar h1 h0,
   (p.targetFlipPivot_mem_I hID hsbar h1).2,
   p.targetFlipSet_eq_Icc hID hsbar h1⟩

/-- **Tipping threshold, Sender side (bundled).** Same package for
the Sender floor flip set at slope level `m`. -/
theorem sender_tipping_threshold {sbar m : ℝ}
    (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m)
    (h0 : (0 : ℝ) ∉ p.senderFloorFlipSet sbar m) :
    0 < p.senderFlipPivot sbar m ∧ p.senderFlipPivot sbar m ≤ 1 ∧
      p.senderFloorFlipSet sbar m = Set.Icc (p.senderFlipPivot sbar m) 1 :=
  ⟨p.senderFlipPivot_pos hID hsbar h1 h0,
   (p.senderFlipPivot_mem_I hID hsbar h1).2,
   p.senderFloorFlipSet_eq_Icc hID hsbar h1⟩

/-! ## Tipping thresholds under local stage complementarity (round BH-1)

Item BH1.8. Each flip set reads its chords on one fixed sanction range:
`[s̄, 1]` for the Target, `[0, s̄]` for the Sender floor. The siblings below
take stage complementarity on that range only, through `TargetStageIDOn` and
`SenderStageIDOn`, and they drop `s̄ ∈ [0, 1]`. The conclusions are verbatim
those of the global forms above, and the `example`s at the end of the section
recover the global bundled thresholds. General in `F` (no transition enters):
these are statements about the stage payoffs only. -/

/-- **The derived Target pivot is always a feasible state**, with no
hypothesis. The Target flip set lies in `[0, 1]`, so its infimum is in
`[0, 1]` when the set is nonempty, and equals `0` (the convention
`sInf ∅ = 0` on `ℝ`) when it is empty. Compared with `targetFlipPivot_mem_I`,
stage complementarity, `s̄ ∈ [0, 1]` and the boundary sign `1 ∈ targetFlipSet s̄`
are all dropped: feasibility of the pivot says nothing about where, or whether,
the Target's stage payoff flips. -/
theorem targetFlipPivot_feasible (sbar : ℝ) :
    p.targetFlipPivot sbar ∈ Sanctions.I := by
  refine ⟨Real.sInf_nonneg (fun _ hz => hz.1.1), ?_⟩
  rcases (p.targetFlipSet sbar).eq_empty_or_nonempty with hempty | ⟨y, hy⟩
  · unfold targetFlipPivot
    rw [hempty, Real.sInf_empty]
    exact zero_le_one
  · exact le_trans (csInf_le ⟨0, fun _ hz => hz.1.1⟩ hy) hy.1.2

/-- **The derived Sender pivot is always a feasible state**, with no
hypothesis (same argument as `targetFlipPivot_feasible`). Compared with
`senderFlipPivot_mem_I`, stage complementarity, `s̄ ∈ [0, 1]` and the boundary
sign `1 ∈ senderFloorFlipSet s̄ m` are dropped. -/
theorem senderFlipPivot_feasible (sbar m : ℝ) :
    p.senderFlipPivot sbar m ∈ Sanctions.I := by
  refine ⟨Real.sInf_nonneg (fun _ hz => hz.1.1), ?_⟩
  rcases (p.senderFloorFlipSet sbar m).eq_empty_or_nonempty with hempty | ⟨y, hy⟩
  · unfold senderFlipPivot
    rw [hempty, Real.sInf_empty]
    exact zero_le_one
  · exact le_trans (csInf_le ⟨0, fun _ hz => hz.1.1⟩ hy) hy.1.2

/-- **The Target flip set is upward closed under local stage
complementarity.** Sibling of `targetFlipSet_upwardClosedIn`: `TargetStageID`
(all sanctions in `[0, 1]`) is replaced by `TargetStageIDOn (Icc s̄ 1)` (the
flip set's own chord range), and `s̄ ∈ [0, 1]` is dropped. A state that has
flipped stays flipped at every harder state, because rally around the flag
raises each chord the flip set reads. -/
theorem targetFlipSet_upwardClosedIn_of_stageIDOn {sbar : ℝ}
    (hID : p.TargetStageIDOn (Set.Icc sbar 1)) :
    Sanctions.MonotoneThreshold.UpwardClosedIn (p.targetFlipSet sbar) 0 1 := by
  constructor
  · exact Set.inter_subset_left
  · rintro x ⟨hxI, hx⟩ y hyI hxy
    refine ⟨hyI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hchord := hID a ha hs₁ hs₂ hs hxI hyI hxy
    have h0 := hx a ha s₁ hs₁ s₂ hs₂ hs
    linarith

/-- **The Sender floor flip set is upward closed under local stage
complementarity.** Sibling of `senderFloorFlipSet_upwardClosedIn`:
`SenderStageID` is replaced by `SenderStageIDOn (Icc 0 s̄)` (the floor range),
and `s̄ ∈ [0, 1]` is dropped. -/
theorem senderFloorFlipSet_upwardClosedIn_of_stageIDOn {sbar m : ℝ}
    (hID : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar)) :
    Sanctions.MonotoneThreshold.UpwardClosedIn
      (p.senderFloorFlipSet sbar m) 0 1 := by
  constructor
  · exact Set.inter_subset_left
  · rintro x ⟨hxI, hx⟩ y hyI hxy
    refine ⟨hyI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hchord := hID a ha hs₁ hs₂ hs hxI hyI hxy
    have h0 := hx a ha s₁ hs₁ s₂ hs₂ hs
    linarith

/-- **The Target flip set is exactly `[targetFlipPivot, 1]`, local form.**
Sibling of `targetFlipSet_eq_Icc` with Target stage complementarity needed only
on `[s̄, 1]` and no hypothesis `s̄ ∈ [0, 1]`. -/
theorem targetFlipSet_eq_Icc_of_stageIDOn {sbar : ℝ}
    (hID : p.TargetStageIDOn (Set.Icc sbar 1))
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar) :
    p.targetFlipSet sbar = Set.Icc (p.targetFlipPivot sbar) 1 :=
  (p.targetFlipSet_upwardClosedIn_of_stageIDOn hID).eq_Icc_pivot
    (p.isClosed_targetFlipSet sbar) ⟨1, h1⟩

/-- **The Sender floor flip set is exactly `[senderFlipPivot, 1]`, local
form.** Sibling of `senderFloorFlipSet_eq_Icc` with Sender stage
complementarity needed only on `[0, s̄]` and no hypothesis `s̄ ∈ [0, 1]`. -/
theorem senderFloorFlipSet_eq_Icc_of_stageIDOn {sbar m : ℝ}
    (hID : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar))
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m) :
    p.senderFloorFlipSet sbar m = Set.Icc (p.senderFlipPivot sbar m) 1 :=
  (p.senderFloorFlipSet_upwardClosedIn_of_stageIDOn hID).eq_Icc_pivot
    (p.isClosed_senderFloorFlipSet sbar m) ⟨1, h1⟩

/-- **Target pivot interiority, local form.** Sibling of
`targetFlipPivot_pos`: if the flip has not happened at `x = 0`, the derived
threshold is strictly positive, with stage complementarity only on `[s̄, 1]`
and no hypothesis `s̄ ∈ [0, 1]`. -/
theorem targetFlipPivot_pos_of_stageIDOn {sbar : ℝ}
    (hID : p.TargetStageIDOn (Set.Icc sbar 1))
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h0 : (0 : ℝ) ∉ p.targetFlipSet sbar) :
    0 < p.targetFlipPivot sbar :=
  (p.targetFlipSet_upwardClosedIn_of_stageIDOn hID).lo_lt_pivot
    (p.isClosed_targetFlipSet sbar) ⟨1, h1⟩ h0

/-- **Sender pivot interiority, local form.** Sibling of
`senderFlipPivot_pos`, with stage complementarity only on `[0, s̄]` and no
hypothesis `s̄ ∈ [0, 1]`. -/
theorem senderFlipPivot_pos_of_stageIDOn {sbar m : ℝ}
    (hID : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar))
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m)
    (h0 : (0 : ℝ) ∉ p.senderFloorFlipSet sbar m) :
    0 < p.senderFlipPivot sbar m :=
  (p.senderFloorFlipSet_upwardClosedIn_of_stageIDOn hID).lo_lt_pivot
    (p.isClosed_senderFloorFlipSet sbar m) ⟨1, h1⟩ h0

/-- **Tipping threshold, Target side, local form (bundled).** Sibling of
`target_tipping_threshold`. Under Target stage complementarity on the high
sanction range `[s̄, 1]` alone, and the two boundary signs, the derived pivot
is interior (`0 < x̄_T ≤ 1`) and the flip region is exactly `[x̄_T, 1]`. The
dropped hypotheses are complementarity at sanctions below `s̄` and
`s̄ ∈ [0, 1]`. In economic terms: the rally-around-the-flag comparison is
needed only for the sanction levels at which the Target's flip is judged. -/
theorem target_tipping_threshold_of_stageIDOn {sbar : ℝ}
    (hID : p.TargetStageIDOn (Set.Icc sbar 1))
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h0 : (0 : ℝ) ∉ p.targetFlipSet sbar) :
    0 < p.targetFlipPivot sbar ∧ p.targetFlipPivot sbar ≤ 1 ∧
      p.targetFlipSet sbar = Set.Icc (p.targetFlipPivot sbar) 1 :=
  ⟨p.targetFlipPivot_pos_of_stageIDOn hID h1 h0,
   (p.targetFlipPivot_feasible sbar).2,
   p.targetFlipSet_eq_Icc_of_stageIDOn hID h1⟩

/-- **Tipping threshold, Sender side, local form (bundled).** Sibling of
`sender_tipping_threshold`, with Sender stage complementarity on the floor
range `[0, s̄]` alone and no hypothesis `s̄ ∈ [0, 1]`. In economic terms: the
public-choice complementarity is needed only for the sub-floor sanction levels
whose slope defines the Sender's flip. -/
theorem sender_tipping_threshold_of_stageIDOn {sbar m : ℝ}
    (hID : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar))
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m)
    (h0 : (0 : ℝ) ∉ p.senderFloorFlipSet sbar m) :
    0 < p.senderFlipPivot sbar m ∧ p.senderFlipPivot sbar m ≤ 1 ∧
      p.senderFloorFlipSet sbar m = Set.Icc (p.senderFlipPivot sbar m) 1 :=
  ⟨p.senderFlipPivot_pos_of_stageIDOn hID h1 h0,
   (p.senderFlipPivot_feasible sbar m).2,
   p.senderFloorFlipSet_eq_Icc_of_stageIDOn hID h1⟩

/-- Rule-13 check: the global Target tipping threshold is the local sibling at
the restricted primitive (`s̄ ∈ [0, 1]` puts `[s̄, 1]` inside `[0, 1]`). -/
example {sbar : ℝ} (hID : p.TargetStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h0 : (0 : ℝ) ∉ p.targetFlipSet sbar) :
    0 < p.targetFlipPivot sbar ∧ p.targetFlipPivot sbar ≤ 1 ∧
      p.targetFlipSet sbar = Set.Icc (p.targetFlipPivot sbar) 1 :=
  p.target_tipping_threshold_of_stageIDOn
    (p.targetStageIDOn_of_targetStageID hID
      (fun _ hs => ⟨le_trans hsbar.1 hs.1, hs.2⟩)) h1 h0

/-- Rule-13 check: the global Sender tipping threshold is the local sibling at
the restricted primitive (`s̄ ≤ 1` puts `[0, s̄]` inside `[0, 1]`). -/
example {sbar m : ℝ} (hID : p.SenderStageID) (hsbar : sbar ∈ Sanctions.I)
    (h1 : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m)
    (h0 : (0 : ℝ) ∉ p.senderFloorFlipSet sbar m) :
    0 < p.senderFlipPivot sbar m ∧ p.senderFlipPivot sbar m ≤ 1 ∧
      p.senderFloorFlipSet sbar m = Set.Icc (p.senderFlipPivot sbar m) 1 :=
  p.sender_tipping_threshold_of_stageIDOn
    (p.senderStageIDOn_of_senderStageID hID
      (fun _ hs => ⟨hs.1, le_trans hs.2 hsbar.2⟩)) h1 h0

/-! ## Downstream-facing restriction bridge (Round B consumer) -/

/-- **Per-state high-range monotonicity from flip-set membership.**
At any state in the Target flip set, the Target stage payoff is
monotone non-decreasing in the sanction on the *per-state* high range
`[max(x, s̄), 1]` (a subset of the fixed range `[s̄, 1]`), at every
feasible action — exactly the stage-level shape consumed by the
one-sided-thresholds layer (`h_stage_target` in
`OneSidedSanctionPreferenceThresholds.of_stage_preferences`). -/
theorem monotoneOn_high_range_of_mem_targetFlipSet {sbar : ℝ}
    {x : ℝ} (hx : x ∈ p.targetFlipSet sbar)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    MonotoneOn (fun s => p.U_T x a s) (Set.Icc (max x sbar) 1) := by
  rintro s₁ hs₁ s₂ hs₂ hs
  exact hx.2 a ha s₁ ⟨le_trans (le_max_right x sbar) hs₁.1, hs₁.2⟩
    s₂ ⟨le_trans (le_max_right x sbar) hs₂.1, hs₂.2⟩ hs

/-! ## Low-basin duals (Round B)

Below the flips the same two ID primitives force the marginals
*negative*: the dual flip sets collect the states at which every
sanction chord on the **full feasible range** `[0, 1]` weakly
*lowers* the payoff (Target) / has slope at most `−m` (Sender). By
the ID primitives these sets are *downward* closed, so each is
exactly a lower interval `[0, x*]` with derived pivot `x* = sSup` —
the low basin of the R47/R48 bistability chain, now derived from the
same primitives as the high basin ("one assumption, two basins").

Full-range chords are the dual of the high side's fixed-range
conservatism: the per-state R47 ranges `[min(x, s̄*), 1]` are subsets
of `[0, 1]`, so dual flip-set membership *restricts* to every
per-state condition (`antitoneOn_of_mem_targetLowFlipSet`,
`strictAntiOn_of_mem_senderLowFlipSet`) — at the cost of a weakly
*lower* (conservative) derived pivot. No myopic-ceiling conflict
arises on the low side (the high-basin ceiling field only quantifies
over the high basin). -/

/-- **Target low flip set.** States at which every sanction chord on
`[0, 1]` weakly lowers the Target stage payoff, uniformly in the
action: below the rally threshold, sanctions hurt the incumbent at
every level. -/
def targetLowFlipSet : Set ℝ :=
  Sanctions.I ∩ {x | ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I,
    ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ → p.U_T x a s₂ ≤ p.U_T x a s₁}

/-- **Sender low flip set at slope level `m`.** States at which every
sanction chord on `[0, 1]` has slope at most `−m`, uniformly in the
action: at dovish states, marginal sanctions are a strict stage loss
to the Sender everywhere. -/
def senderLowFlipSet (m : ℝ) : Set ℝ :=
  Sanctions.I ∩ {x | ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I,
    ∀ s₂ ∈ Sanctions.I,
    s₁ ≤ s₂ → p.U_S x a s₂ - p.U_S x a s₁ ≤ -m * (s₂ - s₁)}

/-- **Derived low-basin Target ceiling** — the supremum of the Target
low flip set: the right endpoint of the derived low basin. -/
def targetLowFlipPivot : ℝ := sSup p.targetLowFlipSet

/-- **Derived low-basin Sender ceiling at slope level `m`.** -/
def senderLowFlipPivot (m : ℝ) : ℝ := sSup (p.senderLowFlipSet m)

/-- **Target low flip set is downward closed in `[0, 1]`.** Chords
grow with the state (`TargetStageID`), so "all chords ≤ 0"
propagates downward. -/
theorem targetLowFlipSet_downwardClosedIn (hID : p.TargetStageID) :
    Sanctions.MonotoneThreshold.DownwardClosedIn p.targetLowFlipSet 0 1 := by
  constructor
  · exact Set.inter_subset_left
  · rintro x ⟨hxI, hx⟩ y hyI hyx
    refine ⟨hyI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hchord := hID a ha hs₁ hs₂ hs hyI hxI hyx
    have h0 := hx a ha s₁ hs₁ s₂ hs₂ hs
    linarith

/-- **Sender low flip set is downward closed in `[0, 1]`.** -/
theorem senderLowFlipSet_downwardClosedIn {m : ℝ}
    (hID : p.SenderStageID) :
    Sanctions.MonotoneThreshold.DownwardClosedIn (p.senderLowFlipSet m) 0 1 := by
  constructor
  · exact Set.inter_subset_left
  · rintro x ⟨hxI, hx⟩ y hyI hyx
    refine ⟨hyI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
    have hchord := hID a ha hs₁ hs₂ hs hyI hxI hyx
    have h0 := hx a ha s₁ hs₁ s₂ hs₂ hs
    linarith

/-- **The Target low flip set is closed.** -/
theorem isClosed_targetLowFlipSet : IsClosed p.targetLowFlipSet := by
  apply IsClosed.inter isClosed_Icc
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro a _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₁ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₂ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_imp
  exact isClosed_le (continuous_slice p.U_T_continuous a s₂)
    (continuous_slice p.U_T_continuous a s₁)

/-- **The Sender low flip set is closed.** -/
theorem isClosed_senderLowFlipSet (m : ℝ) :
    IsClosed (p.senderLowFlipSet m) := by
  apply IsClosed.inter isClosed_Icc
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro a _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₁ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_forall_mem
  intro s₂ _
  apply Sanctions.MonotoneThreshold.isClosed_setOf_imp
  exact isClosed_le
    ((continuous_slice p.U_S_continuous a s₂).sub
      (continuous_slice p.U_S_continuous a s₁))
    continuous_const

/-- **The Target low flip set is exactly `[0, targetLowFlipPivot]`.** -/
theorem targetLowFlipSet_eq_Icc (hID : p.TargetStageID)
    (h0 : (0 : ℝ) ∈ p.targetLowFlipSet) :
    p.targetLowFlipSet = Set.Icc 0 p.targetLowFlipPivot :=
  (p.targetLowFlipSet_downwardClosedIn hID).eq_Icc_pivot
    p.isClosed_targetLowFlipSet ⟨0, h0⟩

/-- **The Target low pivot satisfies its own condition.** -/
theorem targetLowFlipPivot_mem (hID : p.TargetStageID)
    (h0 : (0 : ℝ) ∈ p.targetLowFlipSet) :
    p.targetLowFlipPivot ∈ p.targetLowFlipSet :=
  (p.targetLowFlipSet_downwardClosedIn hID).pivot_mem
    p.isClosed_targetLowFlipSet ⟨0, h0⟩

/-- **Target low pivot interiority**: strictly below 1 when the top
state is flipped. -/
theorem targetLowFlipPivot_lt_one (hID : p.TargetStageID)
    (h0 : (0 : ℝ) ∈ p.targetLowFlipSet)
    (h1 : (1 : ℝ) ∉ p.targetLowFlipSet) :
    p.targetLowFlipPivot < 1 :=
  (p.targetLowFlipSet_downwardClosedIn hID).pivot_lt_hi
    p.isClosed_targetLowFlipSet ⟨0, h0⟩ h1

/-- **Target low pivot is feasible.** -/
theorem targetLowFlipPivot_mem_I (hID : p.TargetStageID)
    (h0 : (0 : ℝ) ∈ p.targetLowFlipSet) :
    p.targetLowFlipPivot ∈ Sanctions.I :=
  (p.targetLowFlipPivot_mem hID h0).1

/-- **The Sender low flip set is exactly `[0, senderLowFlipPivot]`.** -/
theorem senderLowFlipSet_eq_Icc {m : ℝ} (hID : p.SenderStageID)
    (h0 : (0 : ℝ) ∈ p.senderLowFlipSet m) :
    p.senderLowFlipSet m = Set.Icc 0 (p.senderLowFlipPivot m) :=
  (p.senderLowFlipSet_downwardClosedIn hID).eq_Icc_pivot
    (p.isClosed_senderLowFlipSet m) ⟨0, h0⟩

/-- **The Sender low pivot satisfies its own condition.** -/
theorem senderLowFlipPivot_mem {m : ℝ} (hID : p.SenderStageID)
    (h0 : (0 : ℝ) ∈ p.senderLowFlipSet m) :
    p.senderLowFlipPivot m ∈ p.senderLowFlipSet m :=
  (p.senderLowFlipSet_downwardClosedIn hID).pivot_mem
    (p.isClosed_senderLowFlipSet m) ⟨0, h0⟩

/-- **Sender low pivot interiority.** -/
theorem senderLowFlipPivot_lt_one {m : ℝ} (hID : p.SenderStageID)
    (h0 : (0 : ℝ) ∈ p.senderLowFlipSet m)
    (h1 : (1 : ℝ) ∉ p.senderLowFlipSet m) :
    p.senderLowFlipPivot m < 1 :=
  (p.senderLowFlipSet_downwardClosedIn hID).pivot_lt_hi
    (p.isClosed_senderLowFlipSet m) ⟨0, h0⟩ h1

/-- **Sender low pivot is feasible.** -/
theorem senderLowFlipPivot_mem_I {m : ℝ} (hID : p.SenderStageID)
    (h0 : (0 : ℝ) ∈ p.senderLowFlipSet m) :
    p.senderLowFlipPivot m ∈ Sanctions.I :=
  (p.senderLowFlipPivot_mem hID h0).1

/-! ## Low-side restriction bridges (R47 per-state ranges) -/

/-- **Per-state antitonicity from low-flip-set membership.** At any
state in the Target low flip set, the Target stage payoff is
antitone in the sanction on the R47 per-state range
`[min(x, s̄*), 1] ⊆ [0, 1]`, at every feasible action — the stage
shape consumed by
`OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low`. -/
theorem antitoneOn_of_mem_targetLowFlipSet
    {x : ℝ} (hx : x ∈ p.targetLowFlipSet)
    {a : ℝ} (ha : a ∈ Sanctions.I) {sbar_star : ℝ}
    (hsbar : sbar_star ∈ Sanctions.I) :
    AntitoneOn (fun s => p.U_T x a s)
      (Set.Icc (min x sbar_star) 1) := by
  rintro s₁ hs₁ s₂ hs₂ hs
  have hlo : (0 : ℝ) ≤ min x sbar_star := le_min hx.1.1 hsbar.1
  exact hx.2 a ha s₁ ⟨le_trans hlo hs₁.1, hs₁.2⟩
    s₂ ⟨le_trans hlo hs₂.1, hs₂.2⟩ hs

/-- **Per-state strict antitonicity from low-flip-set membership
(Sender, slope level `m > 0`).** -/
theorem strictAntiOn_of_mem_senderLowFlipSet
    {m : ℝ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ p.senderLowFlipSet m)
    {a : ℝ} (ha : a ∈ Sanctions.I) {sbar_star : ℝ}
    (hsbar : sbar_star ∈ Sanctions.I) :
    StrictAntiOn (fun s => p.U_S x a s)
      (Set.Icc (min x sbar_star) 1) := by
  rintro s₁ hs₁ s₂ hs₂ hlt
  have hlo : (0 : ℝ) ≤ min x sbar_star := le_min hx.1.1 hsbar.1
  have h := hx.2 a ha s₁ ⟨le_trans hlo hs₁.1, hs₁.2⟩
    s₂ ⟨le_trans hlo hs₂.1, hs₂.2⟩ (le_of_lt hlt)
  have hpos : 0 < m * (s₂ - s₁) := mul_pos hm (sub_pos.mpr hlt)
  linarith

/-! ## Joint-pivot convenience (certificate inputs) -/

/-- **Joint high pivots below 1 from a common sub-1 member.** If some
state `xhat < 1` lies in both high flip sets, both derived pivots are
`≤ xhat`, so their max is `< 1` — the certificate's nondegeneracy input
`hjoint_lt` in checkable form. -/
theorem flipPivots_lt_one_of_mem_lt {sbar m xhat : ℝ}
    (hxhatT : xhat ∈ p.targetFlipSet sbar)
    (hxhatS : xhat ∈ p.senderFloorFlipSet sbar m)
    (hlt : xhat < 1) :
    max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar m) < 1 := by
  have hT : p.targetFlipPivot sbar ≤ xhat :=
    csInf_le ⟨0, fun _ hy => hy.1.1⟩ hxhatT
  have hS : p.senderFlipPivot sbar m ≤ xhat :=
    csInf_le ⟨0, fun _ hy => hy.1.1⟩ hxhatS
  exact max_lt (lt_of_le_of_lt hT hlt) (lt_of_le_of_lt hS hlt)

/-! ## Round E3 — pivot comparative statics in payoff shifts

Monotone comparative statics of the derived tipping thresholds via
flip-set inclusion: any payoff change that raises all relevant chords
weakly *lowers* the corresponding pivot (deeper lock-in; Arthur 1989
"lock-in depth" framing, Krugman 1991 overlap as the band template).
All proofs are set-inclusion transports through
`MonotoneThreshold.pivot_le_pivot_of_subset` — zero new
assumptions. -/

/-- **Chord dominance (Target) ⇒ flip-set inclusion.** If the
alternative economy `p'` has weakly larger Target high-range chords
than `p` everywhere, every state flipped for `p` is flipped for
`p'`. -/
theorem targetFlipSet_subset_of_chord_dominance
    (p' : Sanctions.AbstractGame.Params) {sbar : ℝ}
    (hdom : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s₁ ∈ Set.Icc sbar 1, ∀ s₂ ∈ Set.Icc sbar 1, s₁ ≤ s₂ →
        p.U_T x a s₂ - p.U_T x a s₁ ≤ p'.U_T x a s₂ - p'.U_T x a s₁) :
    p.targetFlipSet sbar ⊆ p'.targetFlipSet sbar := by
  rintro x ⟨hxI, hx⟩
  refine ⟨hxI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
  have h := hx a ha s₁ hs₁ s₂ hs₂ hs
  have hd := hdom x hxI a ha s₁ hs₁ s₂ hs₂ hs
  linarith

/-- **Chord dominance (Target) ⇒ pivot comparison: lock-in depth.**
Raising all Target high-range chords weakly lowers the derived Target
tipping threshold — the basin opens earlier. -/
theorem targetFlipPivot_le_of_chord_dominance
    (p' : Sanctions.AbstractGame.Params) {sbar : ℝ}
    (hdom : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s₁ ∈ Set.Icc sbar 1, ∀ s₂ ∈ Set.Icc sbar 1, s₁ ≤ s₂ →
        p.U_T x a s₂ - p.U_T x a s₁ ≤ p'.U_T x a s₂ - p'.U_T x a s₁)
    (hne : (p.targetFlipSet sbar).Nonempty) :
    p'.targetFlipPivot sbar ≤ p.targetFlipPivot sbar :=
  Sanctions.MonotoneThreshold.pivot_le_pivot_of_subset
    (p.targetFlipSet_subset_of_chord_dominance p' hdom)
    ⟨0, fun _ hy => hy.1.1⟩ hne

/-- **Chord dominance (Sender floor, fixed slope level) ⇒ flip-set
inclusion.** -/
theorem senderFloorFlipSet_subset_of_chord_dominance
    (p' : Sanctions.AbstractGame.Params) {sbar m : ℝ}
    (hdom : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s₁ ∈ Set.Icc (0 : ℝ) sbar, ∀ s₂ ∈ Set.Icc (0 : ℝ) sbar, s₁ ≤ s₂ →
        p.U_S x a s₂ - p.U_S x a s₁ ≤ p'.U_S x a s₂ - p'.U_S x a s₁) :
    p.senderFloorFlipSet sbar m ⊆ p'.senderFloorFlipSet sbar m := by
  rintro x ⟨hxI, hx⟩
  refine ⟨hxI, fun a ha s₁ hs₁ s₂ hs₂ hs => ?_⟩
  have h := hx a ha s₁ hs₁ s₂ hs₂ hs
  have hd := hdom x hxI a ha s₁ hs₁ s₂ hs₂ hs
  linarith

/-- **Chord dominance (Sender) ⇒ pivot comparison.** Raising all
Sender floor chords weakly lowers the derived dynamic pivot — the
contested band's upper edge moves down. -/
theorem senderFlipPivot_le_of_chord_dominance
    (p' : Sanctions.AbstractGame.Params) {sbar m : ℝ}
    (hdom : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
      ∀ s₁ ∈ Set.Icc (0 : ℝ) sbar, ∀ s₂ ∈ Set.Icc (0 : ℝ) sbar, s₁ ≤ s₂ →
        p.U_S x a s₂ - p.U_S x a s₁ ≤ p'.U_S x a s₂ - p'.U_S x a s₁)
    (hne : (p.senderFloorFlipSet sbar m).Nonempty) :
    p'.senderFlipPivot sbar m ≤ p.senderFlipPivot sbar m :=
  Sanctions.MonotoneThreshold.pivot_le_pivot_of_subset
    (p.senderFloorFlipSet_subset_of_chord_dominance p' hdom)
    ⟨0, fun _ hy => hy.1.1⟩ hne

/-- **Pivot monotonicity in the sanction floor (Target).** A higher
floor narrows the Target's required chord range, so the flip set
grows and the pivot weakly falls. -/
theorem targetFlipPivot_anti_in_sbar {sbar sbar' : ℝ}
    (hss : sbar ≤ sbar')
    (hne : (p.targetFlipSet sbar).Nonempty) :
    p.targetFlipPivot sbar' ≤ p.targetFlipPivot sbar := by
  apply Sanctions.MonotoneThreshold.pivot_le_pivot_of_subset _
    ⟨0, fun _ hy => hy.1.1⟩ hne
  rintro x ⟨hxI, hx⟩
  exact ⟨hxI, fun a ha s₁ hs₁ s₂ hs₂ hs =>
    hx a ha s₁ ⟨le_trans hss hs₁.1, hs₁.2⟩
      s₂ ⟨le_trans hss hs₂.1, hs₂.2⟩ hs⟩

/-- **Pivot monotonicity in the sanction floor (Sender).** A higher
floor widens the Sender's required chord range, so the flip set
shrinks and the dynamic pivot weakly rises. -/
theorem senderFlipPivot_mono_in_sbar {sbar sbar' m : ℝ}
    (hss : sbar ≤ sbar')
    (hne : (p.senderFloorFlipSet sbar' m).Nonempty) :
    p.senderFlipPivot sbar m ≤ p.senderFlipPivot sbar' m := by
  apply Sanctions.MonotoneThreshold.pivot_le_pivot_of_subset _
    ⟨0, fun _ hy => hy.1.1⟩ hne
  rintro x ⟨hxI, hx⟩
  exact ⟨hxI, fun a ha s₁ hs₁ s₂ hs₂ hs =>
    hx a ha s₁ ⟨hs₁.1, le_trans hs₁.2 hss⟩
      s₂ ⟨hs₂.1, le_trans hs₂.2 hss⟩ hs⟩

/-- **Sharpness via contraposition.** If every Target high-range
chord at a state `x ∈ [0,1]` is non-negative, the derived pivot is at
or below `x`. Contrapositively: strictly below the pivot, at least
one chord is strictly negative — the flip boundary is sharp without
any strictness assumption (real-valued chords fail strictly when
they fail). -/
theorem targetFlipPivot_le_of_forall_chords {sbar x : ℝ}
    (hxI : x ∈ Sanctions.I)
    (hall : ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Set.Icc sbar 1,
      ∀ s₂ ∈ Set.Icc sbar 1, s₁ ≤ s₂ → p.U_T x a s₁ ≤ p.U_T x a s₂) :
    p.targetFlipPivot sbar ≤ x :=
  csInf_le ⟨0, fun _ hy => hy.1.1⟩ ⟨hxI, hall⟩

/-! ## Round E3 — strict stage complementarity (flagged strengthening)

Strict chord variants of the two Round-A primitives. A strengthening
of an existing primitive (recorded per Rule 3 under the standing
enrichment authorization of 2026-06-11), with no new objects and no
named scalars: a strict inequality among existing payoffs. Buys
sharp crossings: each fixed chord's flip state is unique. -/

/-- **Strict Sender stage complementarity.** Proper chords of `U_S`
in the sanction are *strictly* increasing in the state. -/
def SenderStageIDStrict : Prop :=
  ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
    StrictMonoOn (fun x => p.U_S x a s₂ - p.U_S x a s₁) Sanctions.I

/-- **Strict Target stage complementarity.** -/
def TargetStageIDStrict : Prop :=
  ∀ a ∈ Sanctions.I, ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
    StrictMonoOn (fun x => p.U_T x a s₂ - p.U_T x a s₁) Sanctions.I

/-- **Sharp crossing (Target).** Under strict complementarity, each
proper chord's flip state — a state at which the chord vanishes — is
unique. -/
theorem targetChord_zero_unique_of_strictID
    (hID : p.TargetStageIDStrict)
    {a s₁ s₂ : ℝ} (ha : a ∈ Sanctions.I)
    (hs₁ : s₁ ∈ Sanctions.I) (hs₂ : s₂ ∈ Sanctions.I) (hs : s₁ < s₂)
    {x y : ℝ} (hx : x ∈ Sanctions.I) (hy : y ∈ Sanctions.I)
    (hgx : p.U_T x a s₂ - p.U_T x a s₁ = 0)
    (hgy : p.U_T y a s₂ - p.U_T y a s₁ = 0) : x = y :=
  Sanctions.MonotoneThreshold.zero_unique_of_strictMonoOn
    (hID a ha s₁ hs₁ s₂ hs₂ hs) hx hy hgx hgy

/-- **Sharp crossing (Sender).** -/
theorem senderChord_zero_unique_of_strictID
    (hID : p.SenderStageIDStrict)
    {a s₁ s₂ : ℝ} (ha : a ∈ Sanctions.I)
    (hs₁ : s₁ ∈ Sanctions.I) (hs₂ : s₂ ∈ Sanctions.I) (hs : s₁ < s₂)
    {x y : ℝ} (hx : x ∈ Sanctions.I) (hy : y ∈ Sanctions.I)
    (hgx : p.U_S x a s₂ - p.U_S x a s₁ = 0)
    (hgy : p.U_S y a s₂ - p.U_S y a s₁ = 0) : x = y :=
  Sanctions.MonotoneThreshold.zero_unique_of_strictMonoOn
    (hID a ha s₁ hs₁ s₂ hs₂ hs) hx hy hgx hgy

/-- Strict complementarity implies the chord (weak) form. -/
theorem TargetStageIDStrict.toTargetStageID
    (hID : p.TargetStageIDStrict) : p.TargetStageID := by
  intro a ha s₁ s₂ x x' hs₁ hs₂ hss hx hx' hxx'
  rcases eq_or_lt_of_le hss with rfl | hlt
  · simp
  rcases eq_or_lt_of_le hxx' with rfl | hxlt
  · exact le_refl _
  · have := hID a ha s₁ hs₁ s₂ hs₂ hlt hx hx' hxlt
    linarith

/-- Strict complementarity implies the chord (weak) form (Sender). -/
theorem SenderStageIDStrict.toSenderStageID
    (hID : p.SenderStageIDStrict) : p.SenderStageID := by
  intro a ha s₁ s₂ x x' hs₁ hs₂ hss hx hx' hxx'
  rcases eq_or_lt_of_le hss with rfl | hlt
  · simp
  rcases eq_or_lt_of_le hxx' with rfl | hxlt
  · exact le_refl _
  · have := hID a ha s₁ hs₁ s₂ hs₂ hlt hx hx' hxlt
    linarith

end Params
end AbstractGame

end

end Sanctions
