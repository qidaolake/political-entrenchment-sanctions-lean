/-
Sanctions/Foundations/TightChords.lean

**A chord pair with equal ends pins the functional form in that coordinate**
(round BD, 2026-10-01).

The chord class of `Foundations/TransitionChords.lean` and
`Foundations/SemiconcaveRiccati.lean` bounds how fast a two-variable law moves in
each argument, from below and from above, and admits non-affine laws as long as
the two bounds differ. This file proves the converse direction that the project
has stated in prose since the Rule-22 audit (CLAUDE.md Rule 3, the
transition-class clause; the `ChordEconomy` docstring): when the lower and upper
rates **coincide**, the chords leave no room, and together with the fixed
diagonal `F x x = x` they determine the law on the whole feasible square.

* `eq_of_sanctionChords_tight` — a lower and an upper sanction chord at the same
  rate `d` force `F x s = (1 − d)·x + d·s` on `[0,1]²`.
* `eq_of_stateChordBandAll_tight` — a state chord band with equal ends `g`, along
  every sanction section, forces `F x s = g·x + (1 − g)·s` on `[0,1]²`.

So the general route's two sanction rates `d_lo ≤ d_hi` (and its two state rates
`g_lo ≤ g_hi`) are what buy generality: collapsing either pair to one rate is
re-assuming the affine law. Each statement needs only its own pair and the
diagonal; neither needs the other pair, monotonicity or continuity.

No `Params`, no sanctions structure (Rule 19); the conclusion is written out
rather than through `AbstractGame.affineF`, which the wiring supplies.
-/
import Sanctions.Foundations.SemiconcaveJointComposition

namespace Sanctions.TightChords

open Set Sanctions.TransitionChords Sanctions.Semiconcave

/-- **Tight sanction chords pin the affine law.** If raising the sanction from
`s₁` to `s₂ ≥ s₁` moves `F x ·` by at least and at most `d·(s₂ − s₁)` on the
feasible square, and `F` fixes the diagonal there, then
`F x s = (1 − d)·x + d·s` at every feasible `(x, s)`: compare `F x s` with
`F x x = x` along the sanction section through `x`. -/
theorem eq_of_sanctionChords_tight {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hlo : SanctionLowerChord F d) (hhi : SanctionUpperChord F d)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, F x x = x)
    {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    F x s = (1 - d) * x + d * s := by
  have hxx := hdiag x hx
  rcases le_total x s with hxs | hsx
  · have h1 := hlo hx hx hs hxs
    have h2 := hhi hx hx hs hxs
    rw [hxx] at h1 h2
    linarith
  · have h1 := hlo hx hs hx hsx
    have h2 := hhi hx hs hx hsx
    rw [hxx] at h1 h2
    linarith

/-- **Tight state chords pin the affine law.** If along every sanction section the
state chord band has equal ends `g` — raising the state from `y₁` to `y₂ ≥ y₁`
moves `F · s` by exactly `g·(y₂ − y₁)` — and `F` fixes the diagonal, then
`F x s = g·x + (1 − g)·s` at every feasible `(x, s)`: compare `F x s` with
`F s s = s` along the state section through `s`. -/
theorem eq_of_stateChordBandAll_tight {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hband : StateChordBandAll F g g)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, F x x = x)
    {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    F x s = g * x + (1 - g) * s := by
  have hss := hdiag s hs
  rcases le_total s x with hsx | hxs
  · obtain ⟨h1, h2⟩ := hband s hs s hs x hx hsx
    simp only at h1 h2
    rw [hss] at h1 h2
    linarith
  · obtain ⟨h1, h2⟩ := hband s hs x hx s hs hxs
    simp only at h1 h2
    rw [hss] at h1 h2
    linarith

/-- **Both tight pairs agree only on rates summing to one.** If the sanction pair
is tight at `d` and the state pair at `g`, the two closed forms coincide on the
square, which at `(0, 1)` reads `d = 1 − g`. -/
theorem add_eq_one_of_tight {F : ℝ → ℝ → ℝ} {d g : ℝ}
    (hlo : SanctionLowerChord F d) (hhi : SanctionUpperChord F d)
    (hband : StateChordBandAll F g g)
    (hdiag : ∀ x ∈ Icc (0 : ℝ) 1, F x x = x) : g + d = 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e1 := eq_of_sanctionChords_tight hlo hhi hdiag h0 h1
  have e2 := eq_of_stateChordBandAll_tight hband hdiag h0 h1
  linarith

end Sanctions.TightChords

#print axioms Sanctions.TightChords.eq_of_sanctionChords_tight
#print axioms Sanctions.TightChords.eq_of_stateChordBandAll_tight
#print axioms Sanctions.TightChords.add_eq_one_of_tight
