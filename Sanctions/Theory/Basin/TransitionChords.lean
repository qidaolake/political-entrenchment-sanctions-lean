/-
Sanctions/Theory/Basin/TransitionChords.lean

**Wiring the abstract sanction-side chord regularity to `Params`.**

`Foundations/TransitionChords.lean` states the chord predicates over a
bare two-variable map and proves what follows from them alone. This file
is the Rule-19 wiring layer: it names them at `Params`, derives the
game's `StrictAdjustment` primitive from the lower chord, and discharges
the whole bundle at the affine law.

## Why this matters for the assumption surface

The project's affine-restricted results are gated on
`hF : p.F = affineF p.δ`, a condition on all of `[0,1]²`. Every theorem
in this file's bundle is implied by that hypothesis
(`affine_transitionChordPack`), so restating a result over the chords is
a **generalisation**: its affine instance is a one-line corollary in the
Rule-5 parametric-first pattern.

The bundle is not free, and the direction of the trade must be stated
honestly in both directions:

* **Versus `hF` it shrinks the surface.** The chords admit genuinely
  non-affine laws — `quadBumpF` is in, and is provably not affine.
* **Versus `StrictAdjustment` alone it widens the surface.** A positive
  lower chord *implies* strict adjustment (`strictAdjustment_of_sanctionLowerChord`)
  but is strictly stronger: transitions tangent to the diagonal adjust
  strictly with vanishing first-order sanction response, and carry no
  positive chord rate.

The discipline that follows, recorded in Rule 22: **never restate a
strict-adjustment-only theorem over the chord.** Consume the chord only
where the quantitative rate is genuinely needed. Otherwise a build goes
green because a hypothesis was strengthened, which is exactly what
Rule 13's drift fence exists to catch.
-/

import Sanctions.Foundations.TransitionChords
import Sanctions.Postulates.AbstractGame

namespace Sanctions.AbstractGame

open Set Sanctions.TransitionChords

namespace Params

variable (p : Params)

/-! ## 1. The predicates, named at `Params` -/

/-- The Sender's sanction moves next period's political state at a rate
of at least `d`. This is the quantitative content the corner-pinning
margin is priced against. -/
def SanctionLowerChordWith (d : ℝ) : Prop :=
  Sanctions.TransitionChords.SanctionLowerChord p.F d

/-- The matching ceiling: the sanction moves the state by at most `d` per
unit. Consumed only where an adverse continuation movement must be
bounded above. -/
def SanctionUpperChordWith (d : ℝ) : Prop :=
  Sanctions.TransitionChords.SanctionUpperChord p.F d

/-- Along the full-sanction section alone, the transition is the
normalised affine map with state weight `γ`. One line of the square. -/
def CornerSectionTopWith (γ : ℝ) : Prop :=
  Sanctions.TransitionChords.CornerSectionTop p.F γ

/-- Curvature ceiling in the sanction, in chord form. -/
def SanctionSemiconcaveWith (M : ℝ) : Prop :=
  Sanctions.TransitionChords.SanctionSemiconcave p.F M

/-! ## 2. The lower chord derives strict adjustment -/

/-- **A positive sanction chord makes the transition strictly adjusting.**

If raising the sanction always raises the successor at a positive rate,
then a sanction below the current state strictly lowers it and a sanction
above it strictly raises it — because the diagonal is fixed. So the chord
*replaces* `StrictAdjustment` as an assumption rather than adding to it.

Strict positivity is load-bearing: at `d = 0` both branches fail. -/
theorem strictAdjustment_of_sanctionLowerChord {d : ℝ} (hd : 0 < d)
    (h : p.SanctionLowerChordWith d) : p.StrictAdjustment := by
  refine ⟨fun x s hx hs hsx => ?_, fun x s hx hs hxs => ?_⟩
  · have hc := h hx hs hx hsx.le
    have hp := mul_pos hd (sub_pos.mpr hsx)
    rw [p.F_diag x] at hc; linarith
  · have hc := h hx hx hs hxs.le
    have hp := mul_pos hd (sub_pos.mpr hxs)
    rw [p.F_diag x] at hc; linarith

/-- **The general-`F` shock condition follows too.** Full sanctions
strictly raise every non-maximal state, which is the single extra
hypothesis the general-transition shock-entry headlines consume. -/
theorem hF_top_of_sanctionLowerChord {d : ℝ} (hd : 0 < d)
    (h : p.SanctionLowerChordWith d) :
    ∀ x ∈ Ico (0 : ℝ) 1, x < p.F x 1 :=
  (p.strictAdjustment_of_sanctionLowerChord hd h).hF_top

/-- The chord rate is bounded by the corner section's state weight:
`d ≤ 1 − γ`. A weak bound only: equality does not force the law affine (the
docstring of `sanctionLowerChord_le_of_cornerTop` in
`Foundations/TransitionChords.lean` exhibits a non-affine law attaining it), so
no non-affine member is thereby shown to face a harder corner margin
(corrected 2026-09-11, the reader's C04). -/
theorem sanctionLowerChord_le_of_cornerSectionTop {d γ : ℝ}
    (hcorner : p.CornerSectionTopWith γ) (h : p.SanctionLowerChordWith d) :
    d ≤ 1 - γ :=
  sanctionLowerChord_le_of_cornerTop (p.F_diag 0) hcorner h

/-! ## 3. The affine law discharges the whole bundle -/

end Params

end Sanctions.AbstractGame
