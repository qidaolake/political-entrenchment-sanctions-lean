/-
Sanctions/Examples/PlacableSenderCollapseWitness.lean

**The collapse is inhabited on both sides of its threshold** (round BB,
2026-09-28; doc 110, item R11 (c); Rule 9: existence certificates and nothing
more).

`collapse_equilibrium_threshold` (`PlacableSenderCollapseEquilibrium.lean`)
characterises, under placability and fourteen tightness equalities, when a
full-defiance top-selector equilibrium exists. Two earlier members carry the
collapse's data (`placableBoundary` and `placableReliefOnly`: affine, `r = n = 0`,
`σ_V = 0`), but no Lean statement had checked any member against the collapse
hypotheses or placed one on either side of the threshold, so the joint
satisfiability of the bundle, and the inhabitation of each side, were unproved
(Rule 9B; Rule 11). This file proves both, on a one-parameter family of members.

`collapseAffine b` is the pinned affine member `placableAffineCs` with the
Sender's rally cross rate `r` and its supplied carrier modulus `σ_V` set to
zero and the Target's discount factor set to `b`: transition
`affineF (1/2)`, Sender stage payoff with curvature `q = 3`, appetite floor
`u₀ = 1`, placation rate `k = 3`, state slope `w = 1`; Target with compliance
cost `ℓ = 1`, pain `c = 4`, no rally softening (`n = 0`) and state valuation
`v = 30`. At every `b` all fourteen equalities hold and the member is placable
(`collapseAffine_collapse`, `collapseAffine_placable`), and the threshold is
`β_T* = 3/(15 + 3/2) = 2/11` (`collapseAffine_betaStar`). So:

* at `b = 1/2` a full-defiance equilibrium exists
  (`collapseAffine_half_defiance`), and
* at `b = 1/8` no top-selector equilibrium has full defiance
  (`collapseAffine_eighth_no_defiance`).

Both conditions of the threshold theorem are therefore met by some economy, and
both of its sides are inhabited. That is all this file shows: nothing about how
typical the collapse is, and nothing off the affine law.

**Rule 22: AFFINE.** The members' transition is `affineF (1/2)`, as the
collapse's tight chords force. **Rule 3.** No field, no hypothesis: every
statement is about a concrete member. The one `Prop` the members are checked
against, `Placable`, is a `def` over the data (`A ≤ k_lo`), not a field.
-/
import Sanctions.Examples.PlacableSenderCollapseEquilibrium
import Sanctions.Examples.PlacableSenderWitnesses

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-- **The rally-free, tight-modulus affine member at Target discount factor
`b`**: `placableAffine` with the Sender's cross rate `r = 0`, the supplied
carrier modulus `σ_V = 0` and `β_T = b`, every other field as
`placableAffine`. -/
def collapseAffineF (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : PlacableEconomyF :=
  { placableAffine with
    r := 0
    SigV := 0
    βT := b
    hβT0 := hb0
    hβT1 := hb1
    hr := le_refl 0
    hCurv := by norm_num [plKS, placableAffine]
    hSigV := by norm_num [plSigImg, plSig, plRho, plMu, plKS, placableAffine] }

/-- The same member in the enriched subclass (sanction-section modulus `0`,
the affine law's). -/
def collapseAffineCs (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : PlacableEconomyFcs where
  toPlacableEconomyF := collapseAffineF b hb0 hb1
  Mcs := 0
  hMcs0 := le_refl 0
  hFcs := affineF_half_cs

/-- The member as an enriched chord economy. -/
abbrev collapseAffine (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : ChordEconomyCs :=
  (collapseAffineCs b hb0 hb1).toChordCs

variable {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)

/-- **The fourteen tightness equalities hold at every member.** -/
theorem collapseAffine_collapse :
    (collapseAffine b hb0 hb1).SigV = 0 ∧ (collapseAffine b hb0 hb1).Ms = 0
      ∧ (collapseAffine b hb0 hb1).τx = 0 ∧ (collapseAffine b hb0 hb1).Mcx = 0
      ∧ (collapseAffine b hb0 hb1).Mcs = 0 ∧ (collapseAffine b hb0 hb1).Mmix = 0
      ∧ (collapseAffine b hb0 hb1).Qbar = (collapseAffine b hb0 hb1).q
      ∧ (collapseAffine b hb0 hb1).klo = (collapseAffine b hb0 hb1).khi
      ∧ (collapseAffine b hb0 hb1).ℓlo = (collapseAffine b hb0 hb1).ℓhi
      ∧ (collapseAffine b hb0 hb1).plo = (collapseAffine b hb0 hb1).c
      ∧ (collapseAffine b hb0 hb1).vlo = (collapseAffine b hb0 hb1).vhi
      ∧ (collapseAffine b hb0 hb1).nhi = 0
      ∧ (collapseAffine b hb0 hb1).glo = (collapseAffine b hb0 hb1).ghi
      ∧ (collapseAffine b hb0 hb1).dlo = (collapseAffine b hb0 hb1).dhi := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  change (4 : ℝ) - 0 = 4
  norm_num

/-- **Every member is placable**: the appetite `A = 1 + (1/2)·(4/3)·(1/2) = 4/3`
is at most the placation rate `k = 3`. -/
theorem collapseAffine_placable : (collapseAffine b hb0 hb1).Placable := by
  change (collapseAffineF b hb0 hb1).Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [collapseAffineF, placableAffine]

/-- **Every member is interior**: the appetite `A = 4/3` is below `q = 3` (a field of the
family until renovation item BJ2.3, 2026-10-07, now a hypothesis). Affine-restricted. -/
theorem collapseAffine_interior : (collapseAffine b hb0 hb1).Interior := by
  change (collapseAffineF b hb0 hb1).Interior
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [collapseAffineF, placableAffine]

/-- **Every member satisfies the stage relief margin**: `ℓ·q = 3 < 12 = k·(c − n)` (a
field of the family until renovation item BJ2.3, now a hypothesis). Affine-restricted. -/
theorem collapseAffine_stageRelief : (collapseAffine b hb0 hb1).StageRelief := by
  change (collapseAffineF b hb0 hb1).StageRelief
  unfold PlacableEconomyF.StageRelief
  norm_num [collapseAffineF, placableAffine]

/-- The Target's discount factor of the member is `b`. -/
theorem collapseAffine_βT : (collapseAffine b hb0 hb1).β_T = b := rfl

/-- **The threshold at every member is `2/11`**: `D = c − ℓ q/k = 3`,
`β_T* = D/(δ v + (1 − δ) D) = 3/(15 + 3/2)`. -/
theorem collapseAffine_betaStar : (collapseAffine b hb0 hb1).betaStar = 2 / 11 := by
  change (4 - 1 * 3 / 3) / (1 / 2 * 30 + (1 - 1 / 2) * (4 - 1 * 3 / 3)) = (2 / 11 : ℝ)
  norm_num

/-- **The threshold theorem at the member**: `collapse_equilibrium_threshold`
applied with the member's fourteen equalities and placability. Away from
`b = 2/11`, a full-defiance equilibrium exists exactly when `2/11 < b`. -/
theorem collapseAffine_threshold (hne : b ≠ 2 / 11) :
    (∃ Eq : (collapseAffine b hb0 hb1).toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ↔ 2 / 11 < b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    collapseAffine_collapse hb0 hb1
  have hne' : (collapseAffine b hb0 hb1).β_T ≠ (collapseAffine b hb0 hb1).betaStar := by
    rw [collapseAffine_βT, collapseAffine_betaStar]; exact hne
  have h := (collapseAffine b hb0 hb1).collapse_equilibrium_threshold
    (collapseAffine_interior hb0 hb1) (collapseAffine_stageRelief hb0 hb1)
    (collapseAffine_placable hb0 hb1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hne'
  rwa [collapseAffine_βT, collapseAffine_betaStar] at h

/-- The member at `β_T = 1/2`, above the threshold. -/
abbrev collapseAffineHalf : ChordEconomyCs := collapseAffine (1 / 2) (by norm_num) (by norm_num)

/-- The member at `β_T = 1/8`, below the threshold. -/
abbrev collapseAffineEighth : ChordEconomyCs := collapseAffine (1 / 8) (by norm_num) (by norm_num)

/-- **Above the threshold: at `β_T = 1/2` a full-defiance equilibrium exists.** -/
theorem collapseAffine_half_defiance :
    ∃ Eq : collapseAffineHalf.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  (collapseAffine_threshold (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)

/-- **Below the threshold: at `β_T = 1/8` no top-selector equilibrium has full
defiance.** -/
theorem collapseAffine_eighth_no_defiance
    (Eq : collapseAffineEighth.toParams.FeedbackStackelbergEquilibriumTop) :
    ¬ ∀ x ∈ Sanctions.I, Eq.α x = 0 := fun hα =>
  absurd ((collapseAffine_threshold (b := 1 / 8) (by norm_num) (by norm_num) (by norm_num)).1
    ⟨Eq, hα⟩) (by norm_num)

/-- **The collapse class is inhabited on both sides of its threshold**
(Rule 9: an existence certificate). There are two enriched chord economies,
each placable and satisfying the fourteen tightness equalities of
`collapse_equilibrium_threshold`, in the first of which a full-defiance
top-selector equilibrium exists and in the second of which none does. -/
theorem exists_collapse_both_sides :
    ∃ E₁ E₂ : ChordEconomyCs,
      (∀ E ∈ ({E₁, E₂} : Set ChordEconomyCs),
        E.Placable ∧ E.SigV = 0 ∧ E.Ms = 0 ∧ E.τx = 0 ∧ E.Mcx = 0 ∧ E.Mcs = 0
          ∧ E.Mmix = 0 ∧ E.Qbar = E.q ∧ E.klo = E.khi ∧ E.ℓlo = E.ℓhi ∧ E.plo = E.c
          ∧ E.vlo = E.vhi ∧ E.nhi = 0 ∧ E.glo = E.ghi ∧ E.dlo = E.dhi)
      ∧ (∃ Eq : E₁.toParams.FeedbackStackelbergEquilibriumTop,
          ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ∧ ¬ (∃ Eq : E₂.toParams.FeedbackStackelbergEquilibriumTop,
          ∀ x ∈ Sanctions.I, Eq.α x = 0) := by
  refine ⟨collapseAffineHalf, collapseAffineEighth, ?_,
    collapseAffine_half_defiance,
    fun ⟨Eq, hα⟩ => collapseAffine_eighth_no_defiance Eq hα⟩
  rintro E (rfl | rfl)
  · exact ⟨collapseAffine_placable _ _, collapseAffine_collapse _ _⟩
  · exact ⟨collapseAffine_placable _ _, collapseAffine_collapse _ _⟩

end

#print axioms Sanctions.Examples.collapseAffine_collapse
#print axioms Sanctions.Examples.collapseAffine_placable
#print axioms Sanctions.Examples.collapseAffine_βT
#print axioms Sanctions.Examples.collapseAffine_betaStar
#print axioms Sanctions.Examples.collapseAffine_threshold
#print axioms Sanctions.Examples.collapseAffine_half_defiance
#print axioms Sanctions.Examples.collapseAffine_eighth_no_defiance
#print axioms Sanctions.Examples.exists_collapse_both_sides

end Examples
end Sanctions
