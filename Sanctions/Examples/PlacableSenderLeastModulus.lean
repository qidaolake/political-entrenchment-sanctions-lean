/-
Sanctions/Examples/PlacableSenderLeastModulus.lean

**The supplied semiconcavity modulus is derivable: the least root of the
Riccati quadratic is a certificate, it is below every certificate, and every
derived constant is sharpest there** (round AJ, 2026-09-22; doc 98 B11, on the
user's word).

A chord economy carries one supplied scalar, `σ_V`, closed by the Riccati
inequality `chSigImg(σ_V) ≤ σ_V` and bounded by the curvature margin
`β_S(σ_V d_hi² + K_S M_s) < q` (on the abstract payoffs since round AV,
2026-09-25, doc 104: the closure carries the stage's own state modulus `σ_x`
and the upper cross rate `r_hi`). Round M showed that *some* such `σ_V ≥ 0`
exists iff a discriminant condition on the primitives holds
(`chSigV_feasible_iff`), and
that the vertex `L/(2D)` then certifies; round P showed that certificates are
not interchangeable, because every quantitative bound is evaluated at the
member's own modulus (`placableAffineVertex_LloopSharp`).

This file closes the question of *which* modulus to take. With the denominator
cleared, closure is the quadratic inequality `D·σ² − L·σ + N ≤ 0`
(`riccati_cleared_eq`), whose solution set is the interval between the two
roots. Its **least root**

    σ₋ = (L − √(L² − 4DN)) / (2D)                      (`chSigLeast`)

is nonnegative, satisfies curvature and closure (the latter with equality), and
is at most every feasible modulus (`sigLeast_core`; on a member,
`sigVLeast_nonneg`, `sigVLeast_curv`, `sigVLeast_closure`, `sigVLeast_least`, in
particular `sigVLeast_le_SigV`). The member re-certified at `σ₋`
(`withLeastModulus`) has the same primitives and a **larger** strong-concavity
modulus `μ`, a **smaller** cross modulus `ϱ`, a smaller response Lipschitz
constant and a smaller sharp loop constant (`mu_le_withLeastModulus`,
`rho_withLeastModulus_le`, `Lresp_withLeastModulus_le`,
`LloopSharp_withLeastModulus_le`): the derived constants are monotone in the
modulus, so the least root is where every bound of the manuscript is tightest.

**What this changes and what it does not.** The structure keeps its field
(the members supply the rational `σ_V = 1` so that the displayed constants stay
rational — at the affine member `σ₋ = 10 − 7√2`). But the paper-facing
statement no longer needs to say "a supplied modulus completes the data": the
data are the primitives, the discriminant condition is the admissibility
condition, and the modulus is the least root, with the members' `σ_V = 1` a
convenient dominating choice. Rule 3: no field, hypothesis or structure is
added; a scalar that was supplied is now derived.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderRegimes

namespace Sanctions
namespace Examples

open Set

noncomputable section

/-! ## The scalar core -/

/-- The cleared Riccati form is the quadratic `−(D·t² − L·t + N)`, with `L` and
`N` the closed forms of `riccati_feasible_iff`. -/
theorem riccati_cleared_eq {a D Q B₀ C₀ H₀ : ℝ} (hHaD : H₀ ^ 2 = a * D) (t : ℝ) :
    ((1 - a) * t - B₀) * (Q - D * t) - (C₀ + H₀ * t) ^ 2
      = -(D * t ^ 2 - ((1 - a) * Q + B₀ * D - 2 * C₀ * H₀) * t + (B₀ * Q + C₀ ^ 2)) := by
  linear_combination (-(t ^ 2)) * hHaD

/-- **The least root of `D·t² − L·t + N`** under `D > 0`, `L > 0`, `N ≥ 0` and
`L² ≥ 4DN`: it is nonnegative, at most the vertex `L/(2D)`, a root, and below
every `t` at which the quadratic is nonpositive. -/
theorem sigLeast_core {D L N : ℝ} (hD : 0 < D) (hL : 0 < L) (hN : 0 ≤ N)
    (hdisc : 4 * D * N ≤ L ^ 2) :
    0 ≤ (L - Real.sqrt (L ^ 2 - 4 * D * N)) / (2 * D) ∧
    (L - Real.sqrt (L ^ 2 - 4 * D * N)) / (2 * D) ≤ L / (2 * D) ∧
    D * ((L - Real.sqrt (L ^ 2 - 4 * D * N)) / (2 * D)) ^ 2
      - L * ((L - Real.sqrt (L ^ 2 - 4 * D * N)) / (2 * D)) + N = 0 ∧
    ∀ t : ℝ, D * t ^ 2 - L * t + N ≤ 0 → (L - Real.sqrt (L ^ 2 - 4 * D * N)) / (2 * D) ≤ t := by
  set s := Real.sqrt (L ^ 2 - 4 * D * N) with hs
  have hdisc' : 0 ≤ L ^ 2 - 4 * D * N := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L ^ 2 - 4 * D * N := Real.sq_sqrt hdisc'
  have hsL : s ≤ L := by
    have h1 : L ^ 2 - 4 * D * N ≤ L ^ 2 := by nlinarith [mul_nonneg hD.le hN]
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hL.le] at h2
    exact h2
  have h2D : 0 < 2 * D := by linarith
  refine ⟨div_nonneg (by linarith) h2D.le, ?_, ?_, ?_⟩
  · apply div_le_div_of_nonneg_right _ h2D.le
    linarith
  · field_simp
    linear_combination hs2
  · intro t ht
    by_contra hlt
    have hlt : t < (L - s) / (2 * D) := not_le.mp hlt
    have hlt' : 2 * D * t < L - s := by
      rw [lt_div_iff₀ h2D] at hlt
      linarith
    -- `D t² − L t + N = D (t − t₋)(t − t₊)` with `t₋ ≤ t₊`, positive left of `t₋`
    have hfac : D * t ^ 2 - L * t + N
        = (1 / (4 * D)) * ((2 * D * t - (L - s)) * (2 * D * t - (L + s))) := by
      field_simp
      linear_combination hs2
    have hneg1 : 2 * D * t - (L - s) < 0 := by linarith
    have hneg2 : 2 * D * t - (L + s) < 0 := by linarith
    have hpos : 0 < (2 * D * t - (L - s)) * (2 * D * t - (L + s)) :=
      mul_pos_of_neg_of_neg hneg1 hneg2
    have : 0 < D * t ^ 2 - L * t + N := by
      rw [hfac]
      exact mul_pos (by positivity) hpos
    linarith

/-- The least root, in the chord economy's closed forms. -/
def chSigLeast (βS q rhi σx ghi dhi KS Mx Mm Ms : ℝ) : ℝ :=
  (chRicL βS q rhi σx ghi dhi KS Mx Mm Ms
    - Real.sqrt (chRicL βS q rhi σx ghi dhi KS Mx Mm Ms ^ 2
        - 4 * plRicD βS dhi * chRicN βS q rhi σx KS Mx Mm Ms))
    / (2 * plRicD βS dhi)

/-! ## On a member -/

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

theorem dhi_pos : 0 < E.dhi := lt_of_lt_of_le E.hdlo0 E.hdlo_dhi

/-- **Every member satisfies the discriminant condition**, since its own
modulus certifies. -/
theorem discriminant :
    0 < plRicQ E.β_S E.q E.KS E.Ms ∧ 0 < chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms
        ∧
    chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms < 2 * plRicQ E.β_S E.q E.KS E.Ms ∧
    4 * plRicD E.β_S E.dhi * chRicN E.β_S E.q E.rhi E.σx E.KS E.Mx E.Mm E.Ms
      ≤ chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms ^ 2 :=
  (chSigV_feasible_iff E.hβS0 E.dhi_pos E.ghi_nonneg E.βS_ghi_sq_lt_one E.KS_nonneg E.hMx0
    E.hMm0 E.rhi_nonneg E.hσx0).mp ⟨E.SigV, E.hSigV0, E.hCurv, E.hSigV⟩

/-- The member's least modulus. -/
def sigVLeast : ℝ := chSigLeast E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms

theorem plRicD_pos : 0 < plRicD E.β_S E.dhi := by
  unfold plRicD; exact mul_pos E.hβS0 (pow_pos E.dhi_pos 2)

theorem chRicN_nonneg : 0 ≤ chRicN E.β_S E.q E.rhi E.σx E.KS E.Mx E.Mm E.Ms := by
  unfold chRicN chRicB
  have hQ := E.discriminant.1
  have := E.KS_nonneg
  have := E.hMx0
  have := E.hσx0
  have h1 : 0 ≤ (E.σx + E.β_S * E.KS * E.Mx) * plRicQ E.β_S E.q E.KS E.Ms := by
    apply mul_nonneg _ hQ.le
    have := E.hβS0.le; positivity
  have h2 : 0 ≤ plRicC E.β_S E.rhi E.KS E.Mm ^ 2 := sq_nonneg _
  linarith

/-- The cleared quadratic at a modulus `t`, in the member's closed forms. -/
theorem cleared_eq (t : ℝ) :
    ((1 - plRicA E.β_S E.ghi) * t - chRicB E.β_S E.σx E.KS E.Mx)
        * (plRicQ E.β_S E.q E.KS E.Ms - plRicD E.β_S E.dhi * t)
      - (plRicC E.β_S E.rhi E.KS E.Mm + plRicH E.β_S E.ghi E.dhi * t) ^ 2
      = -(plRicD E.β_S E.dhi * t ^ 2 - chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms *
          t
          + chRicN E.β_S E.q E.rhi E.σx E.KS E.Mx E.Mm E.Ms) := by
  have hHaD : plRicH E.β_S E.ghi E.dhi ^ 2 = plRicA E.β_S E.ghi * plRicD E.β_S E.dhi := by
    unfold plRicH plRicA plRicD; ring
  unfold chRicL chRicN
  exact riccati_cleared_eq hHaD t

theorem sigLeast_facts :
    0 ≤ E.sigVLeast ∧
    E.sigVLeast ≤ chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms / (2 * plRicD E.β_S
        E.dhi) ∧
    plRicD E.β_S E.dhi * E.sigVLeast ^ 2
      - chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms * E.sigVLeast
      + chRicN E.β_S E.q E.rhi E.σx E.KS E.Mx E.Mm E.Ms = 0 ∧
    ∀ t : ℝ, plRicD E.β_S E.dhi * t ^ 2
      - chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms * t
      + chRicN E.β_S E.q E.rhi E.σx E.KS E.Mx E.Mm E.Ms ≤ 0 → E.sigVLeast ≤ t :=
  sigLeast_core E.plRicD_pos E.discriminant.2.1 E.chRicN_nonneg E.discriminant.2.2.2

theorem sigVLeast_nonneg : 0 ≤ E.sigVLeast := E.sigLeast_facts.1

/-- **The least modulus satisfies the curvature margin.** -/
theorem sigVLeast_curv : E.β_S * (E.sigVLeast * E.dhi ^ 2 + E.KS * E.Ms) < E.q := by
  have h := E.sigLeast_facts.2.1
  have hL2 := E.discriminant.2.2.1
  have hD := E.plRicD_pos
  have hDt : plRicD E.β_S E.dhi * E.sigVLeast < plRicQ E.β_S E.q E.KS E.Ms := by
    have : plRicD E.β_S E.dhi * E.sigVLeast
        ≤ chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms / 2 := by
      have h' := mul_le_mul_of_nonneg_left h hD.le
      have e : plRicD E.β_S E.dhi
          * (chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms / (2 * plRicD E.β_S E.dhi))
          = chRicL E.β_S E.q E.rhi E.σx E.ghi E.dhi E.KS E.Mx E.Mm E.Ms / 2 := by
        field_simp
      linarith
    linarith
  unfold plRicD plRicQ at hDt
  linarith

theorem sigVLeast_mu_pos : 0 < plMu E.β_S E.q E.sigVLeast E.dhi E.KS E.Ms := by
  have := E.sigVLeast_curv
  unfold plMu; linarith

/-- **The least modulus satisfies the Riccati closure** (with equality). -/
theorem sigVLeast_closure :
    chSigImg E.β_S E.q E.rhi E.σx E.sigVLeast E.ghi E.dhi E.KS E.Mx E.Mm E.Ms ≤ E.sigVLeast := by
  rw [chSigImg_le_iff_cleared E.sigVLeast_mu_pos]
  have h := E.cleared_eq E.sigVLeast
  have hroot := E.sigLeast_facts.2.2.1
  rw [hroot] at h
  linarith

/-- **The least modulus is at most every feasible modulus.** -/
theorem sigVLeast_least {t : ℝ} (hc : E.β_S * (t * E.dhi ^ 2 + E.KS * E.Ms) < E.q)
    (hcl : chSigImg E.β_S E.q E.rhi E.σx t E.ghi E.dhi E.KS E.Mx E.Mm E.Ms ≤ t) :
    E.sigVLeast ≤ t := by
  have hμ : 0 < plMu E.β_S E.q t E.dhi E.KS E.Ms := by unfold plMu; linarith
  rw [chSigImg_le_iff_cleared hμ] at hcl
  have h := E.cleared_eq t
  exact E.sigLeast_facts.2.2.2 t (by linarith)

/-- The member's own modulus dominates the least one. -/
theorem sigVLeast_le_SigV : E.sigVLeast ≤ E.SigV := E.sigVLeast_least E.hCurv E.hSigV

/-! ## Re-certification at another modulus, and the monotone constants -/

/-- The member with its modulus replaced by any feasible `t`: every other field
is unchanged. -/
def withModulus (t : ℝ) (hc : E.β_S * (t * E.dhi ^ 2 + chKS E.β_S E.ghi E.whi * E.Ms) < E.q)
    (hcl : chSigImg E.β_S E.q E.rhi E.σx t E.ghi E.dhi (chKS E.β_S E.ghi E.whi) E.Mx E.Mm E.Ms
      ≤ t) :
    ChordEconomyRelief :=
  { E with SigV := t, hCurv := hc, hSigV := hcl }

/-- **The member re-certified at its least modulus.** -/
def withLeastModulus : ChordEconomyRelief :=
  E.withModulus E.sigVLeast E.sigVLeast_curv E.sigVLeast_closure

@[simp] theorem withLeastModulus_SigV : E.withLeastModulus.SigV = E.sigVLeast := rfl
@[simp] theorem withLeastModulus_KS : E.withLeastModulus.KS = E.KS := rfl
@[simp] theorem withLeastModulus_SigC : E.withLeastModulus.SigC = E.SigC := rfl

/-- **The strong-concavity modulus is largest at the least modulus.** -/
theorem mu_le_withLeastModulus : E.mu ≤ E.withLeastModulus.mu := by
  unfold mu plMu
  simp only [withLeastModulus, withModulus, KS]
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right E.sigVLeast_le_SigV
    (sq_nonneg E.dhi)) E.hβS0.le
  linarith

/-- **The cross modulus is smallest at the least modulus.** -/
theorem rho_withLeastModulus_le : E.withLeastModulus.rho ≤ E.rho := by
  unfold rho plRho
  simp only [withLeastModulus, withModulus, KS]
  have hgd : 0 ≤ E.ghi * E.dhi := mul_nonneg E.ghi_nonneg E.dhi_nonneg
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right E.sigVLeast_le_SigV E.ghi_nonneg) E.dhi_nonneg) E.hβS0.le
  linarith

/-- **The response Lipschitz constant is smallest at the least modulus.** -/
theorem Lresp_withLeastModulus_le : E.withLeastModulus.Lresp ≤ E.Lresp := by
  unfold Lresp plLresp
  simp only [withLeastModulus, withModulus, KS, SigC]
  have hmax : max E.sigVLeast (chSigC E.β_S E.τx (chKS E.β_S E.ghi E.whi) E.Mcx E.ghi)
      ≤ max E.SigV (chSigC E.β_S E.τx (chKS E.β_S E.ghi E.whi) E.Mcx E.ghi) :=
    max_le_max_right _ E.sigVLeast_le_SigV
  have hgd : 0 ≤ E.ghi * E.dhi := mul_nonneg E.ghi_nonneg E.dhi_nonneg
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax E.ghi_nonneg)
    E.dhi_nonneg
  have h2 := mul_le_mul_of_nonneg_right (add_le_add_left (mul_le_mul_of_nonneg_left hmax
    (by norm_num : (0 : ℝ) ≤ 2)) (chKS E.β_S E.ghi E.whi)) E.hMmix0
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) E.hβS0.le
  linarith

/-- **The sharp loop constant is smallest at the least modulus.** -/
theorem LloopSharp_withLeastModulus_le : E.withLeastModulus.LloopSharp ≤ E.LloopSharp := by
  unfold LloopSharp
  have hμ := E.mu_pos
  have hμ' : 0 < E.withLeastModulus.mu := lt_of_lt_of_le hμ E.mu_le_withLeastModulus
  have hL := E.Lresp_withLeastModulus_le
  have hLnn := E.withLeastModulus.Lresp_nonneg
  have hghi : E.withLeastModulus.ghi = E.ghi := rfl
  have hdhi : E.withLeastModulus.dhi = E.dhi := rfl
  rw [hghi, hdhi]
  have hdiv : E.withLeastModulus.Lresp / E.withLeastModulus.mu ≤ E.Lresp / E.mu :=
    calc E.withLeastModulus.Lresp / E.withLeastModulus.mu
        ≤ E.Lresp / E.withLeastModulus.mu := div_le_div_of_nonneg_right hL hμ'.le
      _ ≤ E.Lresp / E.mu := div_le_div_of_nonneg_left E.Lresp_nonneg hμ E.mu_le_withLeastModulus
  have := mul_le_mul_of_nonneg_left hdiv E.dhi_nonneg
  linarith

end ChordEconomyRelief

end

#print axioms Sanctions.Examples.sigLeast_core
#print axioms Sanctions.Examples.ChordEconomyRelief.sigVLeast_closure
#print axioms Sanctions.Examples.ChordEconomyRelief.sigVLeast_least
#print axioms Sanctions.Examples.ChordEconomyRelief.LloopSharp_withLeastModulus_le

end Examples
end Sanctions
