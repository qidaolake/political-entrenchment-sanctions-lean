/-
Sanctions/Examples/PlacableSenderEqualityMember.lean

**Placability at equality does not force full compliance: a member of the
enriched family with `A = k` whose constructed Sender-only equilibrium has the
Target complying strictly partially at every state** (doc 70, L1; the reader's
package `2026-09-07-round-DE-validation`, doc 01 §2; read through the chord
economy since round AV, 2026-09-25, doc 104).

`PlacableSenderBoundaryMember.lean` exhibits a member with `A = k` at which the
zero level is `a* ≡ 1`. The hypothesis census once recorded that as "at
equality the zero level is full compliance" — a universal read off one witness
(Rule 9). It is false. At the member below — the affine transition at rate
`1/2`, both discounts `1/2`, `SigV = 1`, coefficients
`q = 3, u₀ = 1, k = 2, r = 1/2, w = 1, ℓ = 1, c = 4, n = 0, v = 30` —
placability holds with equality (`A = 2 = k`), every other margin holds
strictly, the relief margin holds (`6 < 8`), and the zero level is
`a*(x) = 2/3 + x/4 ∈ [2/3, 11/12]`: strictly interior at every state.

Why the certificate has slack at equality: with a positive state coefficient
`r` the appetite `A = u₀ + r + β_S K_S d_hi` prices the state at its top, while
the actual zero level at state `x` prices it at `x`; the difference
`r(1 − x) + β_S δ r/(1 − β_S(1 − δ))` is positive even at `x = 1`. Equality of
`A` and `k` is equality of an upper certificate, not of the sanction appetite
at every state.

Nothing is posited: `VS01 = 4x/3` is identified through the relaxed operator's
fixed-point uniqueness, the response `max(0, 4/9 + x/6 − 2a/3)` is the unique
maximiser of the quadratic objective (two completed-square cases), and `a*` is
the least zero of that response. Rule 9: an existence certificate that refutes
one universal; it says nothing about the zero level on the family. Rule 22:
affine-restricted and marked so.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and
stage relief fields (only the sign field `hcn : n < c`); the member's interiority is the
lemma `placableEqualityBase_interior`, and its chord form `equalityChord_interior` feeds the
results below, whose statements are unchanged.
-/
import Sanctions.Examples.PlacableSenderRegime01

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.TransitionChords
  Sanctions.Mechanism

noncomputable section

/-- The base member: the affine member with the equality coefficients. -/
def placableEqualityBase : PlacableEconomyF :=
  { placableAffine with
    q := 3
    u₀ := 1
    k := 2
    r := 1 / 2
    w := 1
    ℓ := 1
    c := 4
    n := 0
    v := 30
    SigV := 1
    hu₀ := by norm_num
    hr := by norm_num
    hw := by norm_num
    hℓ := by norm_num
    hn := by norm_num
    hCurv := by unfold plKS; norm_num [placableAffine]
    hSigV := by unfold plSigImg plSig plRho plMu plKS; norm_num [placableAffine]
    hk := by norm_num
    hv := by norm_num
    hcn := by norm_num }

/-- Placability at `placableEqualityBase` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableEqualityBase_placable : placableEqualityBase.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableEqualityBase, placableAffine]

/-- The loss-offset margin at `placableEqualityBase` (a hypothesis since round AP). -/
theorem placableEqualityBase_margin : placableEqualityBase.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableEqualityBase, placableAffine]

/-- Interiority at `placableEqualityBase` (a field of the family until renovation item
BJ2.3, 2026-10-07, now a hypothesis). Affine-restricted. -/
theorem placableEqualityBase_interior : placableEqualityBase.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableEqualityBase, placableAffine]

/-- The equality member of the enriched subclass (sanction-section modulus `0`). -/
def placableEquality : PlacableEconomyFcs where
  toPlacableEconomyF := placableEqualityBase
  Mcs := 0
  hMcs0 := by norm_num
  hFcs := affineF_half_cs

/-- The equality member as an enriched chord economy. -/
abbrev equalityChord : ChordEconomyCs := placableEquality.toChordCs

theorem equalityChord_placable : equalityChord.Placable := placableEqualityBase_placable

/-- The member's interiority in the chord form (renovation item BJ2.3). Affine-restricted. -/
theorem equalityChord_interior : equalityChord.Interior :=
  placableEquality.toChordCs_interior placableEqualityBase_interior

theorem equalityChord_neutral : equalityChord.ZeroSanctionNeutral :=
  placableEqualityBase.toChord_zeroSanctionNeutral

theorem placableEquality_F : placableEquality.F = affineF (1 / 2) := rfl

/-- **Placability at equality**: `A = 2 = k`. -/
theorem placableEquality_A_eq_k : equalityChord.A = equalityChord.klo := by
  norm_num [ChordEconomy.A, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableEquality, placableEqualityBase, placableAffine]

theorem equalityChord_Mtot : equalityChord.Mtot = 3 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableEquality,
    placableEqualityBase, placableAffine]

/-- The relief margin: `6 < 8`. -/
theorem placableEquality_relief :
    2 * equalityChord.ℓhi * max equalityChord.Mtot equalityChord.klo
      < equalityChord.klo * equalityChord.plo := by
  rw [equalityChord_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableEquality,
    placableEqualityBase, placableAffine]

/-- The myopic placation level is `1/2 + x/4`. -/
theorem placableEquality_myopicPolicy {x : ℝ} (hx : x ∈ Sanctions.I) :
    equalityChord.myopicPolicy x = 1 / 2 + x / 4 := by
  change placableEqualityBase.toChord.myopicPolicy x = 1 / 2 + x / 4
  rw [placableEqualityBase.toChord_myopicPolicy placableEqualityBase_placable hx]
  norm_num [placableEqualityBase, placableAffine]; ring

/-! ## The Sender's value is `4x/3` -/

/-- The candidate. -/
def equalityW : ChordEconomy.Val := ChordEconomy.affBCF (4 / 3) 0

theorem equality_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    equalityChord.toParams.F x s ∈ (Sanctions.S : Set ℝ) := by
  change affineF (1 / 2) x s ∈ (Sanctions.S : Set ℝ)
  unfold affineF
  constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

theorem equalityW_fixed : equalityChord.relaxOp equalityW = equalityW := by
  ext y
  rw [ChordEconomyCs.relaxOp_apply]
  have hmem := equality_F_mem y.property (show (0:ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
  unfold equalityW
  rw [ChordEconomy.affBCF_apply, ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hmem]
  change symU_S 3 1 2 (1 / 2) 1 y.val 0 0 + (1 / 2) * (4 / 3 * affineF (1 / 2) y.val 0 + 0)
    = 4 / 3 * y.val + 0
  unfold symU_S affineF
  ring

/-- **Identification**: the constructed Sender-only value is `4x/3`, by
uniqueness of the fixed point of the contraction `relaxOp`. -/
theorem placableEquality_VS01 : equalityChord.VS01 = equalityW :=
  ContractingWith.fixedPoint_unique' equalityChord.relaxOp_contracting
    equalityChord.VS01_fix equalityW_fixed

/-! ## The response is `max(0, 4/9 + x/6 − 2a/3)` and the zero level is `2/3 + x/4` -/

/-- The Sender's objective at the identified value, on the square:
`−(3/2)s² + s(4/3 + x/2 − 2a) + 4x/3`. -/
theorem equality_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) :
    equalityChord.senderObj equalityChord.VS01 x a s
      = -(3 / 2) * s ^ 2 + s * (4 / 3 + x / 2 - 2 * a) + 4 / 3 * x := by
  rw [placableEquality_VS01]
  unfold ChordEconomy.senderObj equalityW
  have hmem := equality_F_mem hx hs
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hmem]
  change symU_S 3 1 2 (1 / 2) 1 x a s + (1 / 2) * (4 / 3 * affineF (1 / 2) x s + 0)
    = -(3 / 2) * s ^ 2 + s * (4 / 3 + x / 2 - 2 * a) + 4 / 3 * x
  unfold symU_S affineF
  ring

/-- **The response is the clipped vertex** `max(0, 4/9 + x/6 − 2a/3)`: for a
nonnegative vertex the objective gap is `(3/2)(s − v)²`; for a negative vertex
the gap at `0` is `(3/2)s² − 3vs ≥ 0` with equality only at `s = 0`. -/
theorem equality_response {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    equalityChord.response equalityChord.VS01 x a
      = max 0 (4 / 9 + x / 6 - 2 / 3 * a) := by
  set ρ := equalityChord.response equalityChord.VS01 x a with hρ
  have hρmem : ρ ∈ Sanctions.I := equalityChord.response_mem _ x a
  have hvle : 4 / 9 + x / 6 - 2 / 3 * a ≤ 11 / 18 := by linarith [hx.2, ha.1]
  have hcmem : max 0 (4 / 9 + x / 6 - 2 / 3 * a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (by linarith)⟩
  have hmax := equalityChord.response_isMaxOn equalityChord.VS01 x a hcmem
  simp only [Set.mem_setOf_eq] at hmax
  rw [← hρ] at hmax
  rw [equality_senderObj hx a hcmem, equality_senderObj hx a hρmem] at hmax
  rcases le_or_gt 0 (4 / 9 + x / 6 - 2 / 3 * a) with h0 | h0
  · rw [max_eq_right h0] at hmax ⊢
    have hsq : (ρ - (4 / 9 + x / 6 - 2 / 3 * a)) ^ 2 ≤ 0 := by nlinarith
    have : ρ - (4 / 9 + x / 6 - 2 / 3 * a) = 0 := by
      nlinarith [sq_nonneg (ρ - (4 / 9 + x / 6 - 2 / 3 * a))]
    linarith
  · rw [max_eq_left h0.le] at hmax ⊢
    have hρ0 : ρ ≤ 0 := by
      nlinarith [mul_nonneg hρmem.1 (neg_nonneg.mpr h0.le), hρmem.1]
    exact le_antisymm hρ0 hρmem.1

/-- The zero set is the interval `[2/3 + x/4, 1]`. -/
theorem equality_zeroSet {x : ℝ} (hx : x ∈ Sanctions.I) :
    equalityChord.zeroSet x = Set.Icc (2 / 3 + x / 4) 1 := by
  ext a
  constructor
  · rintro ⟨ha, hz⟩
    simp only [Set.mem_setOf_eq] at hz
    rw [equality_response hx ha] at hz
    have hv : 4 / 9 + x / 6 - 2 / 3 * a ≤ 0 := max_eq_left_iff.mp hz
    exact ⟨by linarith, ha.2⟩
  · rintro ⟨h1, h2⟩
    have ha : a ∈ Sanctions.I := ⟨by linarith [hx.1], h2⟩
    refine ⟨ha, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [equality_response hx ha]
    exact max_eq_left (by linarith)

/-- The zero level is `2/3 + x/4`. -/
theorem equality_zeroLevel {x : ℝ} (hx : x ∈ Sanctions.I) :
    equalityChord.zeroLevel x = 2 / 3 + x / 4 := by
  rw [ChordEconomyCs.zeroLevel_eq_sInf, equality_zeroSet hx, csInf_Icc (by linarith [hx.2])]

/-- **Strictly partial compliance at the constructed Sender-only equilibrium**,
at every feasible state: the policy is `2/3 + x/4`, strictly inside `(0, 1)`,
while the myopic placation level is `1/2 + x/4`. -/
theorem placableEquality_partial_compliance :
    ∀ x ∈ Sanctions.I,
      ((equalityChord.senderOnlyEquilibriumTop equalityChord_interior
          equalityChord_placable) placableEquality_relief
          equalityChord_neutral).α x = 2 / 3 + x / 4 ∧
      0 < ((equalityChord.senderOnlyEquilibriumTop equalityChord_interior
          equalityChord_placable) placableEquality_relief
          equalityChord_neutral).α x ∧
      ((equalityChord.senderOnlyEquilibriumTop equalityChord_interior
          equalityChord_placable) placableEquality_relief
          equalityChord_neutral).α x < 1 ∧
      equalityChord.myopicPolicy x = 1 / 2 + x / 4 := by
  intro x hx
  have hα : ((equalityChord.senderOnlyEquilibriumTop equalityChord_interior
      equalityChord_placable) placableEquality_relief
      equalityChord_neutral).α x
      = 2 / 3 + x / 4 := by
    change equalityChord.α01 x = 2 / 3 + x / 4
    rw [equalityChord.α01_eq hx]
    exact equality_zeroLevel hx
  refine ⟨hα, ?_, ?_, placableEquality_myopicPolicy hx⟩
  · rw [hα]; linarith [hx.1]
  · rw [hα]; linarith [hx.2]

/-- **Rule 9 form**: there is an admissible member of the enriched family, with
the relief margin, at which placability holds with equality and whose
constructed Sender-only equilibrium has the Target complying strictly
partially at every feasible state. So "at equality the zero level is full
compliance" is not a property of the reading `01`: equality of
the certificate `A ≤ k` is compatible with full compliance
(`exists_sender_only_full_compliance`) and with strictly partial compliance. -/
theorem exists_equality_placability_partial_compliance :
    ∃ (E : ChordEconomyCs) (hInt : E.Interior) (hP : E.Placable)
      (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral),
      E.A = E.klo ∧
      ∀ x ∈ Sanctions.I,
        0 < (E.senderOnlyEquilibriumTop hInt hP hrelief hN).α x ∧
        (E.senderOnlyEquilibriumTop hInt hP hrelief hN).α x < 1 :=
  ⟨equalityChord, equalityChord_interior, equalityChord_placable,
      placableEquality_relief, equalityChord_neutral,
    placableEquality_A_eq_k,
    fun x hx => ⟨(placableEquality_partial_compliance x hx).2.1,
      (placableEquality_partial_compliance x hx).2.2.1⟩⟩

end

#print axioms Sanctions.Examples.placableEquality_VS01
#print axioms Sanctions.Examples.placableEquality_partial_compliance
#print axioms Sanctions.Examples.exists_equality_placability_partial_compliance

end Examples
end Sanctions
