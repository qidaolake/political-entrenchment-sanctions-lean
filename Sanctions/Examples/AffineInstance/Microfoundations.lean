/-
Sanctions/Examples/AffineInstance/Microfoundations.lean

**The affine transition as a worked instance: where it comes from.**

Two `rfl` bridges, moved out of `Sanctions/Theory/Microfoundations/` on
2026-08-20d for the same reason as the rest of `AffineInstance/`: each names
the affine law in its statement, so under Rule 22 each is affine-restricted by
construction and belongs with the instance rather than with the general theory.

What they say, in English: the four-group polity's general-`F` parameter
constructor, fed the affine law and its five regularity discharges, is
*definitionally* the affine parameter constructor; and the contest polity's
induced transition, under the diagonal normalisation, *is* `affineF`. Together
they are why every affine economy in this development is already
microfounded --- the affine law is not an assumption bolted onto the model, it
is what these two microfoundations produce.

`toParams` itself moved here on 2026-08-22: `toParamsF` in `Theory/` was
re-based to be self-contained, so the general constructor no longer depends on
the affine one. That inversion is what let the affine constructor leave
`Theory/` --- previously the general sibling was *defined* as a record update
over it, which made the general theory formally depend on the affine
instance.

Nothing here has a consumer in `Theory/`; all are cited from witness files.
-/

import Sanctions.Theory.Microfoundations.FourGroupPolity
import Sanctions.Theory.Microfoundations.KaempferLowenbergContest

namespace Sanctions
namespace KaempferLowenberg

open Sanctions.MilgromShannon

namespace FourGroup

variable (G : FourGroup)

/-- **The four-group polity under the affine transition law.** The `affineF δ`
member of the general family `toParamsF`, obtained by feeding it the affine law
together with its five structural discharges --- membership, continuity,
monotonicity in each coordinate, and the diagonal fixed point. Moved out of
`Theory/Microfoundations/FourGroupPolity.lean` on 2026-08-22 (Rule 22 axis 3:
a constructor that hard-wires `F` is affine by instantiation).

Economically this is the four-group polity in which one unit of sanction moves
next period's political state by exactly `δ`, the same amount at every state
and every sanction level. The general constructor lets that rate vary with
where the polity currently sits; this one pins it.

Nothing is lost by the relocation: `toParamsF` in `Theory/` proves everything
this did about `U_S`, `U_T` and `σ`, because no field outside the transition
block mentions `F`. -/
noncomputable def toParams (δ β_T β_S : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hβT : β_T ∈ Set.Ico (0 : ℝ) 1)
    (hβS : β_S ∈ Set.Ico (0 : ℝ) 1) :
    Sanctions.AbstractGame.Params :=
  G.toParamsF δ β_T β_S hδ hβT hβS (Sanctions.AbstractGame.affineF δ)
    (Sanctions.AbstractGame.affineF_continuous _)
    (Sanctions.AbstractGame.affineF_mono_x hδ)
    (Sanctions.AbstractGame.affineF_mono_s hδ)
    (Sanctions.AbstractGame.affineF_diag _)

/-- **The affine four-group polity has a continuous static Sender selector.** The
clipped vertex `sigmaSel` is jointly continuous in the state and the compliance level
(`sigmaSel_continuous`), as for every member of `toParamsF`. Affine-restricted, as the
constructor is (`F := affineF δ`); the general-`F` parent is
`toParamsF_staticSelectorContinuous`. Round BJ5.1 (2026-10-07): selector continuity left
`Params` for the class `Params.StaticSelectorContinuous`; this wrapper needs its own
instance because instance search does not unfold it. -/
instance toParams_staticSelectorContinuous (δ β_T β_S : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hβT : β_T ∈ Set.Ico (0 : ℝ) 1)
    (hβS : β_S ∈ Set.Ico (0 : ℝ) 1) :
    (G.toParams δ β_T β_S hδ hβT hβS).StaticSelectorContinuous :=
  ⟨G.sigmaSel_continuous⟩

/-- **`toParams` is the `affineF δ` member of the `toParamsF` family.** Rule 5:
the affine constructor is a one-line corollary of the parametric one, not a
separate construction.

The equality is *definitional* (`rfl`), which is what makes this a
zero-breakage refactor: every existing `rfl` / `show` proof stated against
`toParams` — `fgcParams_F` (`Examples/FourGroupCertWitness.lean:141`),
`fgcParamsGen_F` (`Examples/FeedbackComparativeStatics.lean:203`), and the
`hF : p.F = affineF p.δ` discharges spelled `rfl` at
`Examples/C1WitnessEnvelope.lean:554` and `Examples/FourGroupWitness.lean:118`
— keeps working untouched. In the other direction, a general-`F` theorem
proved at `toParamsF` specialises to the affine four-group witnesses by
rewriting with this equation. -/
theorem toParamsF_affineF (δ β_T β_S : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hβT : β_T ∈ Set.Ico (0 : ℝ) 1)
    (hβS : β_S ∈ Set.Ico (0 : ℝ) 1) :
    G.toParamsF δ β_T β_S hδ hβT hβS (Sanctions.AbstractGame.affineF δ)
        (Sanctions.AbstractGame.affineF_continuous _)
        (Sanctions.AbstractGame.affineF_mono_x hδ)
        (Sanctions.AbstractGame.affineF_mono_s hδ)
        (Sanctions.AbstractGame.affineF_diag _)
      = G.toParams δ β_T β_S hδ hβT hβS := rfl

end FourGroup

namespace ContestPolity

variable (G : ContestPolity)

/-- **The induced transition IS the affine law**: under the diagonal
normalization the contest-microfounded transition coincides with
`AbstractGame.affineF δ` — so any existing affine-transition `Params` is
contest-microfounded with zero change downstream. -/
theorem toPolity_inducedF_eq_affineF (δ : ℝ) :
    G.toPolity.inducedF δ = Sanctions.AbstractGame.affineF δ := rfl

end ContestPolity

end KaempferLowenberg
end Sanctions

/-! ## Axiom hygiene (Rule 10) -/

#print axioms Sanctions.KaempferLowenberg.FourGroup.toParamsF_affineF
#print axioms Sanctions.KaempferLowenberg.ContestPolity.toPolity_inducedF_eq_affineF
