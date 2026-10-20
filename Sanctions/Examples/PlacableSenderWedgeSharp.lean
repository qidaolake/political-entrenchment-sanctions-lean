/-
Sanctions/Examples/PlacableSenderWedgeSharp.lean

**The closed-form Sender wedge is attained** (round AE, 2026-09-20; doc 94,
item T2; the outside reader's inspection package, 01_MATHEMATICS §5 T2; read
through the chord economy since round AV, 2026-09-25, doc 104).

`responsePath_ge_stage_add_wedge` bounds the forward-looking response below by
the stage selector plus `β_S·w_lo·d_lo/(Q̄·(1−β_S·g_lo))`. At the boundary member
`placableBoundaryBase` — the affine law at rate `1/2`, both discounts `1/2`,
`q = 2`, `u₀ = w = 1`, `r = 0` — the bound holds **with equality at every
state**: the constructed Sender value is `4x/3 + 8/9`, the forward-looking
response to defiance is `2/3`, the stage vertex is `1/2` and the wedge is `1/6`
(`placableBoundary_wedge_attained`). Hence no constant larger than one can
multiply the wedge in a bound valid for every chord economy
(`wedge_coefficient_cannot_be_raised`).

Nothing is posited (Rule 15): the value is identified by uniqueness of the fixed
point of the Sender's Bellman contraction on the ambient value space — the
member's Sender side at defiance coincides with that of `lossOffsetParams`,
whose constructed equilibrium carries the fixed-point identity — and the
response is the unique maximiser of a quadratic.

Rule 9: an existence certificate. It licenses "the bound is attained, so its
coefficient cannot be improved uniformly over the family"; it does not say the
bound is tight at any other member, and it says nothing about magnitudes.
Rule 22: affine-restricted, and marked so.
-/
import Sanctions.Examples.PlacableSenderWedge
import Sanctions.Examples.PlacableSenderBoundaryMember
import Sanctions.Examples.LossOffsetConverseCounterexample

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-- The boundary member as a chord economy. -/
abbrev boundaryC : ChordEconomy := placableBoundaryBase.toChord.toChordEconomy

/-- The boundary member's Sender objective at defiance and the value `loVS`, on
the square: the quadratic `−s² + (4/3)s + (4/3)x + 4/9`. -/
theorem boundary_senderObj_loVS {x : ℝ} (hx : x ∈ Sanctions.I) {s : ℝ} (hs : s ∈ Sanctions.I) :
    boundaryC.senderObj loVS x 0 s
      = -(s ^ 2) + s * (4 / 3) + 4 / 3 * x + 4 / 9 := by
  have hF : boundaryC.F x s ∈ Sanctions.I := boundaryC.F_mem _ _ hx hs
  unfold ChordEconomy.senderObj loVS
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hF]
  change symU_S 2 1 (4 / 3) 0 1 x 0 s + 1 / 2 * (4 / 3 * affineF (1 / 2) x s + 8 / 9) = _
  unfold symU_S affineF
  ring

/-- `loVS` is a fixed point of the boundary member's Sender Bellman operator at
the defiance policy. -/
theorem boundary_bellmanS_loVS :
    boundaryC.toParams.bellmanS_BCF (fun _ => 0) continuous_const loVS = loVS := by
  ext y
  change sSup ((fun s => boundaryC.senderObj loVS y.val 0 s) '' Sanctions.I) = loVS y
  have hgt : IsGreatest ((fun s => boundaryC.senderObj loVS y.val 0 s) '' Sanctions.I)
      (loVS y) := by
    refine ⟨⟨2 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
    · dsimp only
      rw [boundary_senderObj_loVS y.property ⟨by norm_num, by norm_num⟩]
      unfold loVS; rw [ChordEconomy.affBCF_apply]; ring
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [boundary_senderObj_loVS y.property hs]
      unfold loVS; rw [ChordEconomy.affBCF_apply]
      nlinarith [sq_nonneg (s - 2 / 3)]
  exact hgt.csSup_eq

/-- **The boundary member's constructed Sender value is `4x/3 + 8/9`.** -/
theorem placableBoundary_VSstar : boundaryC.VSstar = loVS :=
  (boundaryC.toParams.bellmanS_BCF_contracting (α := fun _ => 0)
    continuous_const).fixedPoint_unique' boundaryC.VSstar_fix boundary_bellmanS_loVS

/-- **The forward-looking response to defiance is `2/3`** at every feasible state. -/
theorem placableBoundary_responsePath {x : ℝ} (hx : x ∈ Sanctions.I) :
    boundaryC.responsePath boundaryC.VSstar x = 2 / 3 := by
  set t := boundaryC.responsePath boundaryC.VSstar x with ht
  have htmem : t ∈ Sanctions.I := boundaryC.responsePath_mem _ _
  have h23 : (2 / 3 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hmax := boundaryC.response_isMaxOn boundaryC.VSstar x 0 h23
  simp only [Set.mem_setOf_eq] at hmax
  rw [placableBoundary_VSstar] at hmax
  have ht' : boundaryC.response loVS x 0 = t := by
    rw [ht, ChordEconomy.responsePath, placableBoundary_VSstar]
  rw [ht', boundary_senderObj_loVS hx h23, boundary_senderObj_loVS hx htmem] at hmax
  have : t - 2 / 3 = 0 := by nlinarith [sq_nonneg (t - 2 / 3)]
  linarith

/-- **The wedge bound is attained at the boundary member, at every state**: the
response `2/3` is the stage selector `1/2` plus the wedge `1/6`. -/
theorem placableBoundary_wedge_attained {x : ℝ} (hx : x ∈ Sanctions.I) :
    boundaryC.responsePath boundaryC.VSstar x = boundaryC.σ x 0 + boundaryC.wedge := by
  rw [placableBoundary_responsePath hx]
  have hv : boundaryC.σ x 0 = 1 / 2 := by
    rw [placableBoundaryBase.toChord_σ_zero placableBoundaryBase_interior hx]
    change (1 + 0 * x) / 2 = 1 / 2
    ring
  have hw : boundaryC.wedge = 1 / 6 := by
    rw [boundaryC.wedge_eq]
    change (1 / 2 : ℝ) * 1 * (1 / 2) / (2 * (1 - 1 / 2 * (1 / 2))) = 1 / 6
    norm_num
  rw [hv, hw]
  norm_num

/-- **The wedge's coefficient cannot be raised uniformly.** No constant `c > 1`
makes `σ(x,0) + c·wedge` a lower bound for the forward-looking response at every
chord economy and every feasible state. -/
theorem wedge_coefficient_cannot_be_raised :
    ¬ ∃ c : ℝ, 1 < c ∧ ∀ (E : ChordEconomy) (x : ℝ), x ∈ Sanctions.I →
        E.σ x 0 + c * E.wedge ≤ E.responsePath E.VSstar x := by
  rintro ⟨c, hc, h⟩
  have h0 : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hb := h boundaryC 0 h0
  rw [placableBoundary_wedge_attained h0] at hb
  have hpos := boundaryC.wedge_pos
  nlinarith

end

#print axioms placableBoundary_VSstar
#print axioms placableBoundary_wedge_attained
#print axioms wedge_coefficient_cannot_be_raised

end Examples
end Sanctions
