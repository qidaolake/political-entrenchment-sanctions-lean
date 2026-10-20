/-
Sanctions/Examples/PlacableSenderLooseModulusMember.lean

**The rally margin is a certificate condition, not a property of the game**
(round L, doc 80 M9; the reader's round-K validation package, 2026-09-10,
document 03 §1).

`placableQuadDiag` carries the state-section semiconvexity modulus `M_cx = 0`
(its state sections are convex), so `σ_C = 0` and the rally margin (RM) reads
`0 ≤ r`. The same transition is also `4`-semiconvex — a larger modulus is a
weaker cap (`SemiconvexOnSet.mono`) — and re-certified with `M_cx = 4` the
derived `σ_C` is `1500/287` and the left side of (RM) is `270/287 > 1/2 = r`:
the margin fails. Nothing physical has changed: the stage payoffs, the
transition, the discounts, the Sender carrier, the Sender operator and its fixed
point `VSstar` read none of `M_cx`, so the response at defiance of the loose
member is the same function as at `placableQuadDiag` (`rfl`), where it is
proved monotone through (RM). Hence a member of `PlacableEconomyF` at which (RM)
fails and the response is monotone (`exists_member_response_monotone_not_margin`).

What this settles and what it does not. It refutes "the rally margin is
necessary for a monotone response on the class" — a theorem-level margin cannot
be necessary when a looser certificate of the same economy violates it — and it
answers doc 79's question Q1.3 at the level of the supplied moduli. It says
nothing about the *tight*-modulus question at `placableRallyBinding`, where
(RM) binds with `σ_C` at a modulus the transition needs; whether the response
there stays monotone under a smaller `r` is open and recorded as such (doc 80
§3, M14).

Rule 9: an existence certificate and nothing more. Rule 3: no assumption.
Rule 22: the transition is `quadDiagF`, not affine at any rate.
-/
import Sanctions.Examples.PlacableSenderWitnesses

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords

noncomputable section

/-- `placableQuadDiag` re-certified with the state-section modulus `4`: every
field but `Mcx` and its two witnesses is inherited verbatim. -/
def placableQuadDiagLoose : PlacableEconomyF :=
  { placableQuadDiag with
    Mcx := 4
    hMcx0 := by norm_num
    hFcx := fun s hs => (quadDiagF_cx s hs).mono (by norm_num) }

/-- The derived continuation semiconvexity at the loose modulus. -/
theorem placableQuadDiagLoose_SigC : placableQuadDiagLoose.SigC = 1500/287 := by
  norm_num [PlacableEconomyF.SigC, plSigC, PlacableEconomyF.KS, plKS, placableQuadDiagLoose,
    placableQuadDiag]

/-- **The rally margin fails at the loose certificate**: its left side is
`270/287 > 1/2 = r`. -/
theorem placableQuadDiagLoose_not_margin :
    ¬ (placableQuadDiagLoose.βS * (placableQuadDiagLoose.SigC * placableQuadDiagLoose.ghi
          * placableQuadDiagLoose.dhi
        + (placableQuadDiagLoose.KS + 2 * placableQuadDiagLoose.SigC)
          * placableQuadDiagLoose.Mmix)
      ≤ placableQuadDiagLoose.r) := by
  rw [placableQuadDiagLoose_SigC]
  norm_num [PlacableEconomyF.KS, plKS, placableQuadDiagLoose, placableQuadDiag]

/-- **Same game**: the `Params` of the two certificates are the same term. -/
theorem placableQuadDiagLoose_toParams :
    placableQuadDiagLoose.toParams = placableQuadDiag.toParams := rfl

/-- **Same response**: the constructed Sender value and the response at defiance
read none of `M_cx`. -/
theorem placableQuadDiagLoose_responsePath :
    placableQuadDiagLoose.toChord.responsePath placableQuadDiagLoose.toChord.VSstar
      = placableQuadDiag.toChord.responsePath placableQuadDiag.toChord.VSstar := rfl

/-- **The response at the loose member is monotone** — by the flat route at
`placableQuadDiag`, whose response it is. -/
theorem placableQuadDiagLoose_responsePath_monotone :
    MonotoneOn (placableQuadDiagLoose.toChord.responsePath placableQuadDiagLoose.toChord.VSstar)
      (Icc (0 : ℝ) 1) := by
  rw [placableQuadDiagLoose_responsePath]
  exact placableQuadDiag.toChord.responsePath_monotoneOn_of_margin placableQuadDiag_rallyMargin

/-- The rally margin fails at the loose certificate read as a chord economy. -/
theorem placableQuadDiagLoose_not_chordMargin :
    ¬ (placableQuadDiagLoose.toChord.β_S * (placableQuadDiagLoose.toChord.SigC
          * placableQuadDiagLoose.toChord.ghi * placableQuadDiagLoose.toChord.dhi
        + (placableQuadDiagLoose.toChord.KS + 2 * placableQuadDiagLoose.toChord.SigC)
          * placableQuadDiagLoose.toChord.Mmix)
      ≤ placableQuadDiagLoose.toChord.rlo) := by
  rw [PlacableEconomyF.toChord_SigC]
  exact placableQuadDiagLoose_not_margin

/-- The transition is not affine at any rate. -/
theorem placableQuadDiagLoose_F_ne_affineF (δ : ℝ) :
    placableQuadDiagLoose.F ≠ AbstractGame.affineF δ :=
  quadDiagF_ne_affineF δ

/-- **(RM) is not necessary for a monotone response on the class** (Rule 11): a
two-sided chord economy at which the rally margin fails and the response at the
constructed Sender value is nondecreasing in the state. Existence only
(Rule 9). The member's transition is not affine (`placableQuadDiagLoose_F_ne_affineF`).
Renovation item BJ3.1 (2026-10-07): the rally margin reads the two-sided curvature data,
which left the base class for `ChordEconomyTwoSided`, so the witness is stated there;
until then it was `∃ E : ChordEconomy`, the same member. -/
theorem exists_member_response_monotone_not_margin :
    ∃ E : ChordEconomyTwoSided,
      ¬ (E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) ∧
      MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1) :=
  ⟨placableQuadDiagLoose.toChord.toChordEconomyTwoSided, placableQuadDiagLoose_not_chordMargin,
    placableQuadDiagLoose_responsePath_monotone⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.placableQuadDiagLoose_not_margin
#print axioms Sanctions.Examples.placableQuadDiagLoose_responsePath_monotone
#print axioms Sanctions.Examples.exists_member_response_monotone_not_margin

end Examples
end Sanctions
