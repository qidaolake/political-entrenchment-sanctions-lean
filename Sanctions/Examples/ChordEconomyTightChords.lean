/-
Sanctions/Examples/ChordEconomyTightChords.lean

**At the collapse the transition is the affine law on the feasible square**
(round BD, 2026-10-01).

The collapse theorem (`PlacableSenderCollapseEquilibrium.lean`,
`collapse_equilibrium_threshold`) is marked *affine by hypothesis* (Rule 22): its
fourteen equalities include the tight sanction chords `d_lo = d_hi` and the tight
state chords `g_lo = g_hi`. The `ChordEconomy` docstring and the collapse
docstring said that these pin the affine law; this file proves it, by applying
`Foundations/TightChords.lean` to the chord economy's own chord fields
(`hSlo`, `hShi`, `hbandAll`) and the fixed diagonal `F_diag`.

* `F_eq_affineF_of_tight_sanction` — `d_lo = d_hi` alone gives
  `F x s = affineF d_lo x s` on `[0,1]²`.
* `F_eq_affineF_of_tight_state` — `g_lo = g_hi` alone gives
  `F x s = affineF (1 − g_lo) x s` on `[0,1]²`.
* `glo_add_dlo_eq_one_of_tight'` — with both, the rates sum to one (the
  existing `glo_add_dlo_eq_one_of_tight` read off the two closed forms).

The statements are confined to the feasible square, where the chord fields
quantify; off the square the class says nothing about `F`. Rule 3: no new
assumption — every hypothesis is one of the collapse theorem's equalities.
-/
import Sanctions.Examples.ChordEconomy
import Sanctions.Foundations.TightChords

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.TightChords

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Tight sanction chords make the transition affine on the square.** If the
lower and upper sanction rates coincide, `d_lo = d_hi`, the transition is the
affine law at rate `d_lo` at every feasible state and sanction. -/
theorem F_eq_affineF_of_tight_sanction (hd : E.dlo = E.dhi) {x s : ℝ}
    (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    E.F x s = affineF E.dlo x s := by
  have hhi : Sanctions.TransitionChords.SanctionUpperChord E.F E.dlo := by
    rw [hd]; exact E.hShi
  rw [eq_of_sanctionChords_tight E.hSlo hhi (fun y _ => E.F_diag y) hx hs]
  rfl

/-- **Tight state chords make the transition affine on the square.** If the
lower and upper state rates coincide, `g_lo = g_hi`, the transition is the affine
law at rate `1 − g_lo` at every feasible state and sanction. -/
theorem F_eq_affineF_of_tight_state (hg : E.glo = E.ghi) {x s : ℝ}
    (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    E.F x s = affineF (1 - E.glo) x s := by
  have hband : Sanctions.Semiconcave.StateChordBandAll E.F E.glo E.glo := by
    have h := E.hbandAll
    rw [← hg] at h
    exact h
  rw [eq_of_stateChordBandAll_tight hband (fun y _ => E.F_diag y) hx hs, affineF]
  ring

/-- **The two tight pairs agree**: with `g_lo = g_hi` and `d_lo = d_hi` the
closed forms coincide, so `g_lo + d_lo = 1`. -/
theorem glo_add_dlo_eq_one_of_tight' (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi) :
    E.glo + E.dlo = 1 := by
  have hhi : Sanctions.TransitionChords.SanctionUpperChord E.F E.dlo := by
    rw [hd]; exact E.hShi
  have hband : Sanctions.Semiconcave.StateChordBandAll E.F E.glo E.glo := by
    have h := E.hbandAll
    rw [← hg] at h
    exact h
  exact add_eq_one_of_tight E.hSlo hhi hband (fun y _ => E.F_diag y)

end ChordEconomy

end Examples
end Sanctions

#print axioms Sanctions.Examples.ChordEconomy.F_eq_affineF_of_tight_sanction
#print axioms Sanctions.Examples.ChordEconomy.F_eq_affineF_of_tight_state
#print axioms Sanctions.Examples.ChordEconomy.glo_add_dlo_eq_one_of_tight'
