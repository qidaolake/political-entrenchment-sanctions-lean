/-
Sanctions/Examples/PlacableSenderBoundaryMember.lean

**Complete relief need not be partial compliance: a boundary member of the
enriched family whose constructed Sender-only equilibrium has the Target fully
complying** (doc 68, L2; the reader's finding A; read through the chord
economy since round AV, 2026-09-25, doc 104).

The Sender-only reading proves `a⁰⁰(x) < a*(x) ≤ 1` and nothing more about the
level of `a*`. The manuscript once said the myopic Target buys complete relief
"through partial compliance even from a forward-looking Sender". At the member
below — the affine transition at rate `1/2`, both discounts `1/2`, coefficients
`q = 2, u₀ = w = c = 1, k = 4/3, r = n = 0, ℓ = 1/10, v = 4` — placability
holds with equality (`A = k = 4/3`), and the zero level is `a*(x) = 1` at every
state: the forward-looking Sender is placated only by full compliance. Nothing
is posited: `VS01 = 4x/3` is identified through the relaxed operator's
fixed-point uniqueness, the response `(2/3)(1 − a)` is the unique maximiser of
the quadratic objective, and `a* = 1` is the least zero of that response.

Rule 9: this is an existence certificate that refutes one adjective; it does not
say the zero level is full compliance on the family. Rule 22: affine-restricted
and marked so.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and
stage relief fields (only the sign field `hcn : n < c`); the member's interiority is the
lemma `placableBoundaryBase_interior`, and its chord form `boundaryChord_interior` feeds the
results below, whose statements are unchanged.
-/
import Sanctions.Examples.PlacableSenderRegime01

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.TransitionChords
  Sanctions.Mechanism

noncomputable section

/-- The base member: the affine member with the boundary coefficients. -/
def placableBoundaryBase : PlacableEconomyF :=
  { placableAffine with
    q := 2
    u₀ := 1
    k := 4 / 3
    r := 0
    w := 1
    ℓ := 1 / 10
    c := 1
    n := 0
    v := 4
    SigV := 0
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

/-- Placability at `placableBoundaryBase` (a hypothesis of the family since round AP, doc 102 J2). -/
theorem placableBoundaryBase_placable : placableBoundaryBase.Placable := by
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableBoundaryBase, placableAffine]

/-- The loss-offset margin at `placableBoundaryBase` (a hypothesis since round AP). -/
theorem placableBoundaryBase_margin : placableBoundaryBase.LossOffset := by
  unfold PlacableEconomyF.LossOffset plGTn
  norm_num [placableBoundaryBase, placableAffine]

/-- Interiority at `placableBoundaryBase` (a field of the family until renovation item
BJ2.3, 2026-10-07, now a hypothesis). Affine-restricted. -/
theorem placableBoundaryBase_interior : placableBoundaryBase.Interior := by
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableBoundaryBase, placableAffine]

/-- The boundary member of the enriched subclass (sanction-section modulus `0`). -/
def placableBoundary : PlacableEconomyFcs where
  toPlacableEconomyF := placableBoundaryBase
  Mcs := 0
  hMcs0 := by norm_num
  hFcs := affineF_half_cs

/-- The boundary member as an enriched chord economy. -/
abbrev boundaryChord : ChordEconomyCs := placableBoundary.toChordCs

theorem boundaryChord_placable : boundaryChord.Placable := placableBoundaryBase_placable

/-- The member's interiority in the chord form (renovation item BJ2.3). Affine-restricted. -/
theorem boundaryChord_interior : boundaryChord.Interior :=
  placableBoundary.toChordCs_interior placableBoundaryBase_interior

theorem boundaryChord_neutral : boundaryChord.ZeroSanctionNeutral :=
  placableBoundaryBase.toChord_zeroSanctionNeutral

theorem placableBoundary_F : placableBoundary.F = affineF (1 / 2) := rfl

theorem boundaryChord_F : boundaryChord.F = affineF (1 / 2) := rfl

theorem placableBoundary_A_eq_k : boundaryChord.A = boundaryChord.klo := by
  norm_num [ChordEconomy.A, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableBoundary, placableBoundaryBase, placableAffine]

theorem boundaryChord_Mtot : boundaryChord.Mtot = 2 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableBoundary,
    placableBoundaryBase, placableAffine]

/-- The relief margin: `2/5 < 4/3`. -/
theorem placableBoundary_relief :
    2 * boundaryChord.ℓhi * max boundaryChord.Mtot boundaryChord.klo
      < boundaryChord.klo * boundaryChord.plo := by
  rw [boundaryChord_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableBoundary,
    placableBoundaryBase, placableAffine]

/-- The myopic placation level is `3/4`. -/
theorem placableBoundary_myopicPolicy {x : ℝ} (hx : x ∈ Sanctions.I) :
    boundaryChord.myopicPolicy x = 3 / 4 := by
  change placableBoundaryBase.toChord.myopicPolicy x = 3 / 4
  rw [placableBoundaryBase.toChord_myopicPolicy placableBoundaryBase_placable hx]
  norm_num [placableBoundaryBase, placableAffine]

/-! ## The Sender's value is `4x/3` -/

/-- The candidate. -/
def boundaryW : ChordEconomy.Val := ChordEconomy.affBCF (4 / 3) 0

theorem boundary_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    boundaryChord.toParams.F x s ∈ (Sanctions.S : Set ℝ) := by
  change affineF (1 / 2) x s ∈ (Sanctions.S : Set ℝ)
  unfold affineF
  constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

theorem boundaryW_fixed : boundaryChord.relaxOp boundaryW = boundaryW := by
  ext y
  rw [ChordEconomyCs.relaxOp_apply]
  have hmem := boundary_F_mem y.property (show (0:ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
  unfold boundaryW
  rw [ChordEconomy.affBCF_apply, ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hmem]
  change symU_S 2 1 (4 / 3) 0 1 y.val 0 0 + (1 / 2) * (4 / 3 * affineF (1 / 2) y.val 0 + 0)
    = 4 / 3 * y.val + 0
  unfold symU_S affineF
  ring

/-- **Identification**: the constructed Sender-only value is `4x/3`, by
uniqueness of the fixed point of the contraction `relaxOp`. -/
theorem placableBoundary_VS01 : boundaryChord.VS01 = boundaryW :=
  ContractingWith.fixedPoint_unique' boundaryChord.relaxOp_contracting
    boundaryChord.VS01_fix boundaryW_fixed

/-! ## The response is `(2/3)(1 − a)` and the zero level is `1` -/

/-- The Sender's objective at the identified value, on the square. -/
theorem boundary_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) :
    boundaryChord.senderObj boundaryChord.VS01 x a s
      = -(s ^ 2) + s * (4 / 3 - 4 / 3 * a) + 4 / 3 * x := by
  rw [placableBoundary_VS01]
  unfold ChordEconomy.senderObj boundaryW
  have hmem := boundary_F_mem hx hs
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hmem]
  change symU_S 2 1 (4 / 3) 0 1 x a s + (1 / 2) * (4 / 3 * affineF (1 / 2) x s + 0)
    = -(s ^ 2) + s * (4 / 3 - 4 / 3 * a) + 4 / 3 * x
  unfold symU_S affineF
  ring

theorem boundary_response {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    boundaryChord.response boundaryChord.VS01 x a = 2 / 3 * (1 - a) := by
  set ρ := boundaryChord.response boundaryChord.VS01 x a with hρ
  have hρmem : ρ ∈ Sanctions.I := boundaryChord.response_mem _ x a
  have hcmem : (2 / 3 * (1 - a) : ℝ) ∈ Sanctions.I := by
    constructor <;> nlinarith [ha.1, ha.2]
  have hmax := boundaryChord.response_isMaxOn boundaryChord.VS01 x a hcmem
  simp only [Set.mem_setOf_eq] at hmax
  rw [← hρ] at hmax
  rw [boundary_senderObj hx a hcmem, boundary_senderObj hx a hρmem] at hmax
  -- the gap identity: objective(ρ) − objective(c) = −(ρ − c)² ≤ 0, so ρ = c
  have hsq : (ρ - 2 / 3 * (1 - a)) ^ 2 ≤ 0 := by nlinarith
  have : ρ - 2 / 3 * (1 - a) = 0 := by nlinarith [sq_nonneg (ρ - 2 / 3 * (1 - a))]
  linarith

theorem boundary_zeroSet {x : ℝ} (hx : x ∈ Sanctions.I) :
    boundaryChord.zeroSet x = {1} := by
  ext a
  constructor
  · rintro ⟨ha, hz⟩
    simp only [Set.mem_setOf_eq] at hz
    rw [boundary_response hx ha] at hz
    simp only [Set.mem_singleton_iff]
    linarith
  · intro ha
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [boundary_response hx ⟨zero_le_one, le_rfl⟩]; ring

theorem boundary_zeroLevel {x : ℝ} (hx : x ∈ Sanctions.I) :
    boundaryChord.zeroLevel x = 1 := by
  rw [ChordEconomyCs.zeroLevel_eq_sInf, boundary_zeroSet hx, csInf_singleton]

/-- **Full compliance at the constructed Sender-only equilibrium**, at every
feasible state, while the myopic placation level is `3/4`. -/
theorem placableBoundary_full_compliance :
    ∀ x ∈ Sanctions.I,
      ((boundaryChord.senderOnlyEquilibriumTop boundaryChord_interior
          boundaryChord_placable) placableBoundary_relief
        boundaryChord_neutral).α x = 1 ∧
      boundaryChord.myopicPolicy x = 3 / 4 := by
  intro x hx
  refine ⟨?_, placableBoundary_myopicPolicy hx⟩
  change boundaryChord.α01 x = 1
  rw [boundaryChord.α01_eq hx]
  exact boundary_zeroLevel hx

/-- **Rule 9 form**: there is an admissible enriched chord economy, with the
relief margin and zero-sanction neutrality, whose constructed Sender-only
equilibrium has the Target fully complying at every feasible state. So
"complete relief through partial compliance" is not a property of the reading
`01`. -/
theorem exists_sender_only_full_compliance :
    ∃ (E : ChordEconomyCs) (hInt : E.Interior) (hP : E.Placable)
      (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral),
      ∀ x ∈ Sanctions.I, (E.senderOnlyEquilibriumTop hInt hP hrelief hN).α x = 1 :=
  ⟨boundaryChord, boundaryChord_interior, boundaryChord_placable,
      placableBoundary_relief, boundaryChord_neutral,
    fun x hx => (placableBoundary_full_compliance x hx).1⟩

end

#print axioms Sanctions.Examples.placableBoundary_VS01
#print axioms Sanctions.Examples.placableBoundary_full_compliance
#print axioms Sanctions.Examples.exists_sender_only_full_compliance

end Examples
end Sanctions
