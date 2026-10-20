/-
Sanctions/Foundations/SemiconcaveRiccati.lean

**Bellman invariance of a semiconcavity clause under a NON-AFFINE state
transition — the Riccati step.**

The slope-pinned route pins the corner section of the transition by an
*equality* (`F y 1 = γ·y + (1 − γ)`).  That equality is what makes the
successor state an exactly affine function of the current state, hence the
carrier exactly affine, hence every curvature bookkeeping trivial.  This
file removes it.

What replaces it is a **two-sided state band** on the corner section
together with a **curvature ceiling** on it.  Under those, a carrier that
demands

  * sup-norm radius `M`,
  * Lipschitz constant `K`,
  * lower state-slope `g` (hence monotonicity), and
  * semiconcavity modulus `Sg`

is still mapped into itself by the Bellman operator, provided `Sg` clears a
**Riccati threshold**.  The threshold is the third member of the project's
closed-form family, alongside `StokeyLucas.bellmanLipConstant`
(`L_U/(1 − β·γ)`), `StokeyLucas.bellmanLowerSlopeConstant`
(`g_U/(1 − β·γ_F)`) and `StokeyLucas.bellmanNormBound` (`M_U/(1 − β)`):

    bellmanSemiconcaveConstant β ghi ψ K M_state
      = (ψ + β·K·M_state) / (1 − β·ghi²)

Read economically: the image's upward curvature is fed by three sources —
the stage payoff's own curvature `ψ`; the continuation's curvature `Sg`
seen through the successor map, which contracts the *state gap* by at most
`ghi` and therefore the *squared* gap by at most `ghi²`; and the successor
map's own curvature `M_state`, which the continuation charges at its
Lipschitz rate `K` because a curved successor map moves the realized next
state off the chord.  The last term is exactly what the affine route got
for free (`M_state = 0`).

## Why monotonicity of the continuation is load-bearing

The curvature ceiling on the successor map is one-sided: `M_state`-
semiconcavity says the successor at the midpoint is *not much below* the
chord, and says nothing about how far above it may be.  A Lipschitz bound
on `V` alone therefore cannot price the off-chord displacement.  What
prices it is that `V` is **nondecreasing**: when the realized successor sits
*above* the chord the continuation can only have gained, so the chord defect
is not charged at all; when it sits *below*, the displacement is bounded by
`M_state` and the Lipschitz constant does the rest.  Both branches live in
`SemiconcaveComposition.semiconcave_comp_of_chords`, which this file reuses
along the state coordinate rather than reproving; that the hypothesis cannot
simply be dropped is recorded here as a refutation,
`bellman_semiconcave_step_needs_monotone`.

## What this file adds on top of the composition rule

`Foundations/SemiconcaveComposition.lean` already prices *one* composition,
`s ↦ v (F x s)`, at modulus `Σ·dhi² + K·M`.  Read along the state coordinate
it prices `y ↦ V (G y)` at `Sg·ghi² + K·M_state`
(`semiconcave_comp_state_of_band`).  What is new here is the **fixed-point**
layer: adding the stage payoff, closing the recursion
`Sg ↦ ψ + β·(Sg·ghi² + K·M_state)`, and exhibiting the closed form at which
that recursion is stationary.

## Scope, stated honestly

* No differentiability, no interiority, no functional form: every hypothesis
  is a chord inequality.  The affine corner section is the special case
  `glo = ghi = γ`, `M_state = 0`, at which the threshold collapses to
  `ψ/(1 − β·γ²)`.
* The band forms require `0 ≤ glo`, which is what turns the two-sided band
  into the absolute bound `|G y₁ − G y₂| ≤ ghi·|y₁ − y₂|`.  That absolute
  bound is all the proofs read, and `glo` never reaches a conclusion, so
  every band form now has an `_of_lipschitz` sibling that assumes the
  absolute bound directly and needs neither `glo` nor `0 ≤ K` (round BG-1,
  2026-10-06, item BG1.3).  The band forms are wrappers of those siblings,
  with unchanged statements.
* `0 ≤ M_state` is required.  A strictly concave successor map
  (`M_state < 0`) would make the off-chord budget negative, and the
  monotone branch could not absorb it.
* The threshold is **attained, not merely sufficient**: see
  `bellman_closed_form_semiconcave_margin` (equality at the constant) and
  `semiconcave_image_modulus_le_iff` (no smaller modulus is invariant).

Rule 19: nothing here mentions `Params` or the sanctions game.  The
`clipS'`-composed restatement at the end is a definitional instantiation,
not new content, and is provided only so the carrier-level consumer does
not have to perform the beta-reduction by hand.

## Where the evidence lives

The affine section is the `glo = ghi` degeneracy of the band, and the Riccati
constant collapses at zero transition curvature: both are in
`Examples/AffineInstance/SemiconcaveRiccati.lean`. That the continuation's
monotonicity cannot be dropped is refuted by construction in
`Examples/Counterexamples/SemiconcaveRiccatiMonotone.lean`. Moved there
2026-08-27, so this file carries the recursion and nothing that certifies it.
-/

import Sanctions.Foundations.SemiconcaveComposition
import Sanctions.Domain.UnitIntervalProjection

noncomputable section
open Set

namespace Sanctions.Semiconcave

/-! ## 1. Monotonicity of the modulus

A semiconcavity bound weakens upward: a `c`-semiconcave function is
`c'`-semiconcave for every `c' ≥ c`.  This is what turns the exact image
modulus computed below into membership of a carrier whose modulus clears
the threshold. -/

/-- Semiconcavity only sees the function on the (convex) set, so a
pointwise-on-`X` equality transports it.  This is what lets a consumer
supply the Bellman image via a *composition rule* — an equation valid on
`[0,1]` — rather than as a literal lambda. -/
theorem SemiconcaveOnSet.congr_on {v w : ℝ → ℝ} {X : Set ℝ} {c : ℝ}
    (hX : Convex ℝ X) (h : ∀ x ∈ X, v x = w x)
    (hv : SemiconcaveOnSet v X c) : SemiconcaveOnSet w X c := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  have hm : t * x₁ + (1 - t) * x₂ ∈ X :=
    hX hx₁ hx₂ ht0 (by linarith) (by ring)
  rw [← h x₁ hx₁, ← h x₂ hx₂, ← h _ hm]
  exact hv x₁ hx₁ x₂ hx₂ t ht0 ht1

/-- Raising the modulus preserves semiconcavity. -/
theorem SemiconcaveOnSet.mono_modulus {v : ℝ → ℝ} {X : Set ℝ} {c c' : ℝ}
    (h : SemiconcaveOnSet v X c) (hcc : c ≤ c') :
    SemiconcaveOnSet v X c' := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  refine le_trans (h x₁ hx₁ x₂ hx₂ t ht0 ht1) ?_
  have hP : (0 : ℝ) ≤ t * (1 - t) * (x₁ - x₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right (by linarith) hP

/-- **Semiconcavity is additive, with nonnegative discounting.** A sum
`v + β·w` of a `c₁`-semiconcave and a `c₂`-semiconcave function is
`(c₁ + β·c₂)`-semiconcave whenever `β ≥ 0`.  This is the *only* thing the
stage payoff contributes to the Riccati step; all the geometry is in the
composition rule. -/
theorem SemiconcaveOnSet.add_smul {v w : ℝ → ℝ} {X : Set ℝ} {c₁ c₂ β : ℝ}
    (hv : SemiconcaveOnSet v X c₁) (hw : SemiconcaveOnSet w X c₂)
    (hβ : 0 ≤ β) :
    SemiconcaveOnSet (fun x => v x + β * w x) X (c₁ + β * c₂) := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  have h1 := hv x₁ hx₁ x₂ hx₂ t ht0 ht1
  have h2 := mul_le_mul_of_nonneg_left (hw x₁ hx₁ x₂ hx₂ t ht0 ht1) hβ
  simp only
  nlinarith [h1, h2]

/-! ## 2. The two-sided state band on a one-variable section

`StateChordBand G glo ghi` is the corner-section band written over the
one-variable section `G = fun y => F y 1`.

The design's two-variable predicate `CornerStateChord F glo ghi` has **not**
landed in the tree as of this file's writing, so no defeq to it is claimed
or checked here.  When it does land, spelled as

    ∀ y₁ ∈ Icc 0 1, ∀ y₂ ∈ Icc 0 1, y₁ ≤ y₂ →
      glo*(y₂-y₁) ≤ F y₂ 1 - F y₁ 1 ∧ F y₂ 1 - F y₁ 1 ≤ ghi*(y₂-y₁)

it is definitionally `StateChordBand (fun y => F y 1) glo ghi` and may be
passed directly; if it is spelled differently, a one-line adapter is needed
and this comment should be corrected rather than trusted. -/

/-- **Two-sided chord band.** On `[0,1]`, moving the argument up by `Δ`
moves the value up by at least `glo·Δ` and at most `ghi·Δ`.  With
`glo = ghi` this pins `G` to an affine map; with `glo < ghi` genuinely
non-affine sections qualify. -/
def StateChordBand (G : ℝ → ℝ) (glo ghi : ℝ) : Prop :=
  ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    glo * (y₂ - y₁) ≤ G y₂ - G y₁ ∧ G y₂ - G y₁ ≤ ghi * (y₂ - y₁)

/-- **The band's rates are ordered.** Between `0` and `1` the band reads
`glo ≤ G 1 − G 0 ≤ ghi`, so `glo ≤ ghi` is a consequence of the band and never a
separate condition (round P, 2026-09-11; the reader's R2). -/
theorem StateChordBand.rates_le {G : ℝ → ℝ} {glo ghi : ℝ}
    (h : StateChordBand G glo ghi) : glo ≤ ghi := by
  have h01 := h 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [sub_zero, mul_one] at h01
  linarith [h01.1, h01.2]

/-- **The band is an absolute Lipschitz bound.** A nonnegative lower rate
turns the two-sided band into `|G y₁ − G y₂| ≤ ghi·|y₁ − y₂|`. -/
theorem abs_sub_le_of_stateChordBand {G : ℝ → ℝ} {glo ghi : ℝ}
    (hglo : 0 ≤ glo) (h : StateChordBand G glo ghi)
    {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
    |G y₁ - G y₂| ≤ ghi * |y₁ - y₂| := by
  rcases le_total y₁ y₂ with hle | hle
  · obtain ⟨hlo, hhi⟩ := h y₁ hy₁ y₂ hy₂ hle
    have h1 : 0 ≤ G y₂ - G y₁ :=
      le_trans (mul_nonneg hglo (by linarith)) hlo
    rw [abs_of_nonpos (by linarith : G y₁ - G y₂ ≤ 0),
      abs_of_nonpos (by linarith : y₁ - y₂ ≤ 0)]
    linarith
  · obtain ⟨hlo, hhi⟩ := h y₂ hy₂ y₁ hy₁ hle
    have h1 : 0 ≤ G y₁ - G y₂ :=
      le_trans (mul_nonneg hglo (by linarith)) hlo
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₁ - y₂)]
    linarith

/-- The squared form of the band bound: the successor **squared** gap
contracts by `ghi²`.  This is the factor that appears on the continuation's
curvature term, and it is why the Riccati denominator is `1 − β·ghi²`
rather than `1 − β·ghi`. -/
theorem sq_sub_le_of_stateChordBand {G : ℝ → ℝ} {glo ghi : ℝ}
    (hglo : 0 ≤ glo) (h : StateChordBand G glo ghi)
    {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
    (G y₁ - G y₂) ^ 2 ≤ ghi ^ 2 * (y₁ - y₂) ^ 2 := by
  have habs := abs_sub_le_of_stateChordBand hglo h hy₁ hy₂
  have h1 : (0 : ℝ) ≤ |G y₁ - G y₂| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ |y₁ - y₂| := abs_nonneg _
  have h3 : (G y₁ - G y₂) ^ 2 = |G y₁ - G y₂| ^ 2 := (sq_abs _).symm
  have h4 : (y₁ - y₂) ^ 2 = |y₁ - y₂| ^ 2 := (sq_abs _).symm
  rw [h3, h4]
  nlinarith [habs, h1, h2]

/-! ## 3. The Riccati closed form -/

/-- **Closed-form invariant semiconcavity modulus (named).**

`Sg* := (ψ + β·K·M_state) / (1 − β·ghi²)`, from a stage-payoff curvature
ceiling `ψ`, the carrier's Lipschitz constant `K`, the successor map's
curvature ceiling `M_state`, the discount factor `β` and the successor
map's upper chord rate `ghi`.

Mirrors `StokeyLucas.bellmanLipConstant` (`L_U/(1 − β·γ)`),
`StokeyLucas.bellmanLowerSlopeConstant` (`g_U/(1 − β·γ_F)`) and
`StokeyLucas.bellmanNormBound` (`M_U/(1 − β)`).  Unlike those three, the
geometric series here is damped by the *square* of the transition rate,
because curvature is a second-order quantity, and it carries an extra
numerator term `β·K·M_state` that is absent exactly when the successor map
is affine. -/
def bellmanSemiconcaveConstant (β ghi ψ K M_state : ℝ) : ℝ :=
  (ψ + β * K * M_state) / (1 - β * ghi ^ 2)

/-- Unfold lemma for `bellmanSemiconcaveConstant`. -/
@[simp] theorem bellmanSemiconcaveConstant_def (β ghi ψ K M_state : ℝ) :
    bellmanSemiconcaveConstant β ghi ψ K M_state
      = (ψ + β * K * M_state) / (1 - β * ghi ^ 2) := rfl

/-- **The contraction margin is automatic.** With `β < 1` and an upper
chord rate at most one — which holds for every transition mapping `[0,1]`
into itself — the Riccati denominator is positive. -/
theorem semiconcave_contract_of_le_one {β ghi : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hghi0 : 0 ≤ ghi) (hghi1 : ghi ≤ 1) :
    β * ghi ^ 2 < 1 := by
  have h : ghi ^ 2 ≤ 1 := by nlinarith
  calc β * ghi ^ 2 ≤ β * 1 := mul_le_mul_of_nonneg_left h hβ0
    _ = β := mul_one β
    _ < 1 := hβ1

/-- **The Riccati fixed point is attained, with equality.**

At `Sg = Sg*` the image modulus `ψ + β·(Sg·ghi² + K·M_state)` equals `Sg`
exactly — the semiconcavity clause is reproduced, not merely dominated.
This is the exact analogue of `bellman_closed_form_lipschitz_margin`
(`L_U + β·K·γ = K`) and `bellman_closed_form_lowerSlope_margin`
(`g_U + β·g·γ_F = g`). -/
theorem bellman_closed_form_semiconcave_margin {β ghi ψ K M_state : ℝ}
    (h_nn : 0 ≤ ψ + β * K * M_state) (h_contract : β * ghi ^ 2 < 1) :
    0 ≤ bellmanSemiconcaveConstant β ghi ψ K M_state ∧
      ψ + β * (bellmanSemiconcaveConstant β ghi ψ K M_state * ghi ^ 2
          + K * M_state)
        = bellmanSemiconcaveConstant β ghi ψ K M_state := by
  have hd : 0 < 1 - β * ghi ^ 2 := by linarith
  refine ⟨div_nonneg h_nn hd.le, ?_⟩
  simp only [bellmanSemiconcaveConstant]
  field_simp
  ring

/-- **The closed form is exactly the invariance threshold — and the least
one.** A modulus `Sg` reproduces itself under the image recursion iff it is
at least `Sg*`.  So nothing smaller is invariant: the constant is sharp, not
a convenient over-estimate. -/
theorem semiconcave_image_modulus_le_iff {β ghi ψ K M_state Sg : ℝ}
    (h_contract : β * ghi ^ 2 < 1) :
    ψ + β * (Sg * ghi ^ 2 + K * M_state) ≤ Sg
      ↔ bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg := by
  have hd : 0 < 1 - β * ghi ^ 2 := by linarith
  rw [bellmanSemiconcaveConstant, div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith [h]

/-! ## 4. The Riccati step

The one-step curvature bookkeeping, over a completely general successor
section `G`.  This is the theorem the affine route was avoiding.

It is assembled from two pieces and nothing else: the **composition rule**
of `Foundations/SemiconcaveComposition.lean`, re-read along the state
coordinate, and the additivity of semiconcavity.  In particular the
chord-squaring step is *not* reproved here — it is the same lemma that
prices the sanction direction, applied to a different section. -/

/-- **State-direction composition, Lipschitz form** (general in the
successor map `G`; round BG-1, 2026-10-06, item BG1.3).  `y ↦ V (G y)` is
semiconcave with modulus `Sg·ghi² + K·M_state` when `V` is nondecreasing,
`K`-Lipschitz and `Sg`-semiconcave on `[0,1]`, and `G` maps `[0,1]` into
itself, is `M_state`-semiconcave, and moves by at most `ghi` per unit of
state, in absolute value.

This is `SemiconcaveComposition.semiconcave_comp_of_lipschitz` read along the
state coordinate, at the constant-in-its-first-argument law `fun _ s => G s`,
so the two coordinate directions are priced by one rule.  Against the band
form `semiconcave_comp_state_of_band` it drops the lower rate `glo` and its
sign (only the absolute bound is read, and `glo` never enters the modulus)
and `0 ≤ K` (the Lipschitz bound gives it). -/
theorem semiconcave_comp_state_of_lipschitz
    {V G : ℝ → ℝ} {Sg K ghi M_state : ℝ}
    (hSg : 0 ≤ Sg) (hM : 0 ≤ M_state)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |G y₁ - G y₂| ≤ ghi * |y₁ - y₂|)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state) :
    SemiconcaveOnSet (fun y => V (G y)) (Icc (0 : ℝ) 1)
      (Sg * ghi ^ 2 + K * M_state) :=
  Sanctions.SemiconcaveComposition.semiconcave_comp_of_lipschitz
    (F := fun _ s => G s) (x := 0) hSg hM
    (fun z₁ hz₁ z₂ hz₂ h => hV_mono z₁ hz₁ z₂ hz₂ h) hV_lip hV_sc
    ⟨le_rfl, zero_le_one⟩ (fun _ _ s hs => hG_maps s hs) hG_lip (fun _ _ => hG_sc)

/-- **State-direction composition** (general in the successor map `G`).
`y ↦ V (G y)` is semiconcave with modulus `Sg·ghi² + K·M_state`.

The two-sided band `StateChordBand G glo ghi` with `0 ≤ glo` is read only
through the absolute bound it implies (`abs_sub_le_of_stateChordBand`), so
since BG1.3 (2026-10-06) this is a wrapper of
`semiconcave_comp_state_of_lipschitz`, with its statement unchanged; `0 ≤ K`
(now `_hK`) is not used. -/
theorem semiconcave_comp_state_of_band
    {V G : ℝ → ℝ} {Sg K glo ghi M_state : ℝ}
    (hSg : 0 ≤ Sg) (_hK : 0 ≤ K) (hglo : 0 ≤ glo) (hM : 0 ≤ M_state)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_band : StateChordBand G glo ghi)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state) :
    SemiconcaveOnSet (fun y => V (G y)) (Icc (0 : ℝ) 1)
      (Sg * ghi ^ 2 + K * M_state) :=
  semiconcave_comp_state_of_lipschitz hSg hM hV_mono hV_lip hV_sc hG_maps
    (fun _ hy₁ _ hy₂ => abs_sub_le_of_stateChordBand hglo hG_band hy₁ hy₂) hG_sc

/-- **Semiconcavity of a Bellman image under a non-affine successor map,
Lipschitz form** (general in the successor map `G`; round BG-1, 2026-10-06,
item BG1.3).  The Bellman image `W y = stage y + β · V (G y)` is semiconcave
with modulus `ψ + β·(Sg·ghi² + K·M_state)` when `stage` is `ψ`-semiconcave,
`V` is `Sg`-semiconcave, `K`-Lipschitz and nondecreasing, and `G` maps `[0,1]`
into itself, is `M_state`-semiconcave and is `ghi`-Lipschitz.

Against `bellman_semiconcave_step` it drops the lower band rate `glo`, its
sign, and `0 ≤ K`: the band is read only through the absolute bound, and the
Lipschitz bound on `V` gives `0 ≤ K`. -/
theorem bellman_semiconcave_step_of_lipschitz
    {stage V G : ℝ → ℝ} {β ψ Sg K ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hSg : 0 ≤ Sg) (hM : 0 ≤ M_state)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |G y₁ - G y₂| ≤ ghi * |y₁ - y₂|)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet (fun y => stage y + β * V (G y)) (Icc (0 : ℝ) 1)
      (ψ + β * (Sg * ghi ^ 2 + K * M_state)) :=
  hstage.add_smul
    (semiconcave_comp_state_of_lipschitz hSg hM hV_mono hV_lip hV_sc
      hG_maps hG_lip hG_sc) hβ

/-- **Semiconcavity of a Bellman image under a non-affine successor map.**

Let

* `stage` be `ψ`-semiconcave on `[0,1]` (the stage payoff at the pinned
  action — its own upward curvature ceiling);
* `G` map `[0,1]` into `[0,1]`, obey the two-sided chord band
  `[glo, ghi]` with `0 ≤ glo`, and be `M_state`-semiconcave (the successor
  section `y ↦ F y 1`, with `M_state = 0` exactly in the affine case);
* `V` be `Sg`-semiconcave, `K`-Lipschitz and **nondecreasing** on `[0,1]`
  (the carrier clauses).

Then the Bellman image at the pinned action,

    `W y = stage y + β · V (G y)`,

is semiconcave on `[0,1]` with modulus

    `ψ + β·(Sg·ghi² + K·M_state)`.

The three summands are the three curvature sources named in the header:
the stage payoff's own curvature; the continuation's curvature seen through
a successor map that contracts squared state gaps by at most `ghi²`; and the
Lipschitz price of the successor map's own bend, which the affine route
never paid.

No differentiability is used, `G` need not be monotone in any stronger sense
than the band gives, and no interiority or argmax information is required —
the action is pinned, so this is a pure composition estimate.

General in the successor map `G`.  Since BG1.3 (2026-10-06) this is a wrapper
of `bellman_semiconcave_step_of_lipschitz`, with its statement unchanged: the
band enters only through `abs_sub_le_of_stateChordBand`, and `0 ≤ K` (now
`_hK`) is not used. -/
theorem bellman_semiconcave_step
    {stage V G : ℝ → ℝ} {β ψ Sg K glo ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hSg : 0 ≤ Sg) (_hK : 0 ≤ K)
    (hglo : 0 ≤ glo) (hM : 0 ≤ M_state)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_band : StateChordBand G glo ghi)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet (fun y => stage y + β * V (G y)) (Icc (0 : ℝ) 1)
      (ψ + β * (Sg * ghi ^ 2 + K * M_state)) :=
  bellman_semiconcave_step_of_lipschitz hβ hSg hM hG_maps
    (fun _ hy₁ _ hy₂ => abs_sub_le_of_stateChordBand hglo hG_band hy₁ hy₂) hG_sc
    hstage hV_sc hV_lip hV_mono

/-! ## 5. Carrier invariance -/

/-- **The semiconcavity clause is Bellman-invariant above the threshold,
Lipschitz form** (general in the successor map `G`; round BG-1, 2026-10-06,
item BG1.3).  Same data as `bellman_semiconcave_step_of_lipschitz`, with the
carrier modulus `Sg` required only to clear the closed form
`Sg* = (ψ + β·K·M_state)/(1 − β·ghi²)`; the image is again `Sg`-semiconcave.

Against `bellman_semiconcave_invariant` it drops the lower band rate `glo`,
its sign, and `0 ≤ K`.  `0 ≤ Sg` is derived, as there. -/
theorem bellman_semiconcave_invariant_of_lipschitz
    {stage V G : ℝ → ℝ} {β ψ Sg K ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hSg_ge : bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |G y₁ - G y₂| ≤ ghi * |y₁ - y₂|)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet (fun y => stage y + β * V (G y)) (Icc (0 : ℝ) 1) Sg := by
  have hSg0 : 0 ≤ Sg :=
    le_trans
      (bellman_closed_form_semiconcave_margin h_num h_contract).1 hSg_ge
  exact (bellman_semiconcave_step_of_lipschitz hβ hSg0 hM hG_maps hG_lip hG_sc
      hstage hV_sc hV_lip hV_mono).mono_modulus
    ((semiconcave_image_modulus_le_iff h_contract).mpr hSg_ge)

/-- **The semiconcavity clause is Bellman-invariant above the threshold.**

Same data as `bellman_semiconcave_step`, with the carrier modulus `Sg`
required only to clear the closed form
`Sg* = (ψ + β·K·M_state)/(1 − β·ghi²)`.  The conclusion is membership of the
*same* clause the carrier demands — this is the invariance leg, not merely
an estimate.

Note `0 ≤ Sg` is derived, not assumed: it follows from `Sg* ≤ Sg` and the
nonnegativity of the numerator.

General in the successor map `G`.  Since BG1.3 (2026-10-06) this is a wrapper
of `bellman_semiconcave_invariant_of_lipschitz`, with its statement unchanged:
the band enters only through `abs_sub_le_of_stateChordBand`, and `0 ≤ K` (now
`_hK`) is not used. -/
theorem bellman_semiconcave_invariant
    {stage V G : ℝ → ℝ} {β ψ Sg K glo ghi M_state : ℝ}
    (hβ : 0 ≤ β) (_hK : 0 ≤ K) (hglo : 0 ≤ glo) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hSg_ge : bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_band : StateChordBand G glo ghi)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet (fun y => stage y + β * V (G y)) (Icc (0 : ℝ) 1) Sg :=
  bellman_semiconcave_invariant_of_lipschitz hβ hM h_num h_contract hSg_ge hG_maps
    (fun _ hy₁ _ hy₂ => abs_sub_le_of_stateChordBand hglo hG_band hy₁ hy₂) hG_sc
    hstage hV_sc hV_lip hV_mono

/-- **The threshold itself is invariant, exactly.**  At `Sg = Sg*` the
image is `Sg*`-semiconcave, and by `bellman_closed_form_semiconcave_margin`
the image modulus produced by the step lemma *equals* `Sg*` — there is no
slack absorbed by `mono_modulus`.  So the fixed point of the Riccati
recursion is attained, not merely bracketed. -/
theorem bellman_semiconcave_invariant_atThreshold
    {stage V G : ℝ → ℝ} {β ψ K glo ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hglo : 0 ≤ glo) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_band : StateChordBand G glo ghi)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant β ghi ψ K M_state))
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet (fun y => stage y + β * V (G y)) (Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant β ghi ψ K M_state) :=
  bellman_semiconcave_invariant hβ hK hglo hM h_num h_contract le_rfl
    hG_maps hG_band hG_sc hstage hV_sc hV_lip hV_mono

/-- **The threshold itself is invariant, exactly — Lipschitz form** (general in
the successor map `G`; BG1.3, 2026-10-06).  As
`bellman_semiconcave_invariant_atThreshold`, without the lower band rate
`glo`, its sign, or `0 ≤ K`. -/
theorem bellman_semiconcave_invariant_atThreshold_of_lipschitz
    {stage V G : ℝ → ℝ} {β ψ K ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |G y₁ - G y₂| ≤ ghi * |y₁ - y₂|)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant β ghi ψ K M_state))
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet (fun y => stage y + β * V (G y)) (Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant β ghi ψ K M_state) :=
  bellman_semiconcave_invariant_of_lipschitz hβ hM h_num h_contract le_rfl
    hG_maps hG_lip hG_sc hstage hV_sc hV_lip hV_mono

/-- **The consumer-facing form: invariance from a composition rule.**

The Bellman operator does not hand back a literal lambda; it hands back an
image function together with a *composition rule* saying what that image
equals on the state space (in this development: the corner-collapse
identity `Image y = stage y + β·V(clipS'(F y 1))`, valid on `[0,1]`).  This
restatement consumes exactly that: an equation on `[0,1]`, not a
definitional match. -/
theorem bellman_semiconcave_invariant_of_image_eq
    {Image stage V G : ℝ → ℝ} {β ψ Sg K glo ghi M_state : ℝ}
    (h_compose : ∀ y ∈ Icc (0 : ℝ) 1, Image y = stage y + β * V (G y))
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hglo : 0 ≤ glo) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hSg_ge : bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_band : StateChordBand G glo ghi)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet Image (Icc (0 : ℝ) 1) Sg :=
  (bellman_semiconcave_invariant hβ hK hglo hM h_num h_contract hSg_ge
      hG_maps hG_band hG_sc hstage hV_sc hV_lip hV_mono).congr_on
    (convex_Icc _ _) (fun y hy => (h_compose y hy).symm)

/-- **Invariance from a composition rule — Lipschitz form** (general in the
successor map `G`; BG1.3, 2026-10-06).  As
`bellman_semiconcave_invariant_of_image_eq`, without the lower band rate
`glo`, its sign, or `0 ≤ K`. -/
theorem bellman_semiconcave_invariant_of_image_eq_of_lipschitz
    {Image stage V G : ℝ → ℝ} {β ψ Sg K ghi M_state : ℝ}
    (h_compose : ∀ y ∈ Icc (0 : ℝ) 1, Image y = stage y + β * V (G y))
    (hβ : 0 ≤ β) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hSg_ge : bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg)
    (hG_maps : ∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1)
    (hG_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |G y₁ - G y₂| ≤ ghi * |y₁ - y₂|)
    (hG_sc : SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V z₁ - V z₂| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V z₁ ≤ V z₂) :
    SemiconcaveOnSet Image (Icc (0 : ℝ) 1) Sg :=
  (bellman_semiconcave_invariant_of_lipschitz hβ hM h_num h_contract hSg_ge
      hG_maps hG_lip hG_sc hstage hV_sc hV_lip hV_mono).congr_on
    (convex_Icc _ _) (fun y hy => (h_compose y hy).symm)

/-! ## 6. The `clipS'`-composed restatement

The carrier's members are bounded continuous functions on `↥S = [0,1]`, and
the Bellman image evaluates them at the *clipped* successor.  Because the
successor section maps `[0,1]` into `[0,1]`, instantiating the abstract
lemma at `V := fun z => V (clipS' z)` reproduces the composed form on the
nose — this corollary is a definitional restatement, carrying no new
content, and exists only so the consumer need not perform the substitution
by hand. -/

/-- `bellman_semiconcave_invariant`, stated at the shape the Sender carrier
actually meets: `W y = stage y + β · V (clipS' (F y 1))`. -/
theorem bellman_semiconcave_invariant_clip
    {stage : ℝ → ℝ} {V : ↥(Sanctions.S : Set ℝ) → ℝ} {F : ℝ → ℝ → ℝ}
    {β ψ Sg K glo ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hglo : 0 ≤ glo) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hSg_ge : bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg)
    (hF_maps : ∀ y ∈ Icc (0 : ℝ) 1, F y 1 ∈ Icc (0 : ℝ) 1)
    (hF_band : StateChordBand (fun y => F y 1) glo ghi)
    (hF_sc : SemiconcaveOnSet (fun y => F y 1) (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet (fun z => V (Sanctions.clipS' z))
      (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V (Sanctions.clipS' z₁) - V (Sanctions.clipS' z₂)| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V (Sanctions.clipS' z₁) ≤ V (Sanctions.clipS' z₂)) :
    SemiconcaveOnSet
      (fun y => stage y + β * V (Sanctions.clipS' (F y 1)))
      (Icc (0 : ℝ) 1) Sg :=
  bellman_semiconcave_invariant (V := fun z => V (Sanctions.clipS' z))
    (G := fun y => F y 1) hβ hK hglo hM h_num h_contract hSg_ge
    hF_maps hF_band hF_sc hstage hV_sc hV_lip hV_mono

/-- `bellman_semiconcave_invariant_of_lipschitz` at the shape the Sender
carrier meets, `W y = stage y + β · V (clipS' (F y 1))` (general in `F`;
BG1.3, 2026-10-06).  As `bellman_semiconcave_invariant_clip`, with the corner
section's state band replaced by the absolute bound
`|F y₁ 1 − F y₂ 1| ≤ ghi·|y₁ − y₂|`, and without `0 ≤ K`. -/
theorem bellman_semiconcave_invariant_clip_of_lipschitz
    {stage : ℝ → ℝ} {V : ↥(Sanctions.S : Set ℝ) → ℝ} {F : ℝ → ℝ → ℝ}
    {β ψ Sg K ghi M_state : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M_state)
    (h_num : 0 ≤ ψ + β * K * M_state)
    (h_contract : β * ghi ^ 2 < 1)
    (hSg_ge : bellmanSemiconcaveConstant β ghi ψ K M_state ≤ Sg)
    (hF_maps : ∀ y ∈ Icc (0 : ℝ) 1, F y 1 ∈ Icc (0 : ℝ) 1)
    (hF_lip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |F y₁ 1 - F y₂ 1| ≤ ghi * |y₁ - y₂|)
    (hF_sc : SemiconcaveOnSet (fun y => F y 1) (Icc (0 : ℝ) 1) M_state)
    (hstage : SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ)
    (hV_sc : SemiconcaveOnSet (fun z => V (Sanctions.clipS' z))
      (Icc (0 : ℝ) 1) Sg)
    (hV_lip : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V (Sanctions.clipS' z₁) - V (Sanctions.clipS' z₂)| ≤ K * |z₁ - z₂|)
    (hV_mono : ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V (Sanctions.clipS' z₁) ≤ V (Sanctions.clipS' z₂)) :
    SemiconcaveOnSet
      (fun y => stage y + β * V (Sanctions.clipS' (F y 1)))
      (Icc (0 : ℝ) 1) Sg :=
  bellman_semiconcave_invariant_of_lipschitz (V := fun z => V (Sanctions.clipS' z))
    (G := fun y => F y 1) hβ hM h_num h_contract hSg_ge
    hF_maps hF_lip hF_sc hstage hV_sc hV_lip hV_mono

end Sanctions.Semiconcave

end
