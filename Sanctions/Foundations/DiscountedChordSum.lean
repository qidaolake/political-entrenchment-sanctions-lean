/-
Sanctions/Foundations/DiscountedChordSum.lean

**Discounted sums of bounded sequences: a chord recursion and a supersolution
bound** (round BB, 2026-09-28; doc 110 item C2a, the Target's security bound).

Two statements about real sequences, with a geometric discount `0 ≤ β < 1` and
bounded terms (so every series here converges absolutely):

* **The chord-sum inequality** (`head_add_mul_tsum_le`). If a gap sequence
  grows at least by a chord recursion,

    `g·e t + d·s t ≤ e (t+1)`   at every date,

  then its discounted sum dominates the discounted sum of the driving sequence:

    `e 0 + β·d·Σ β^t s t ≤ (1 − β·g)·Σ β^t e t`.

  Weighting the recursion by `β^(t+1)` and summing is the whole proof: the left
  side of the summed recursion is `Σ β^t e t − e 0`. No sign condition on `g`,
  `d`, `e` or `s` is used; the consumer reads it with `e 0 = 0`, `s ≥ 0` and
  `β·g < 1`, where it says the discounted gap is at least
  `β·d/(1 − β·g)` times the discounted drive.

* **The supersolution bound** (`tsum_pow_mul_le_of_le_add_mul_succ`). A bounded
  sequence `V` with `u t + β·V (t+1) ≤ V t` at every date dominates the
  discounted sum of `u`: `Σ β^t u t ≤ V 0`. The tail sums `P n = Σ_k β^k u (n+k)`
  solve `P n = u n + β·P (n+1)`, so `V − P` satisfies
  `β·(V − P)(n+1) ≤ (V − P)(n)` and is bounded, hence nonnegative by the
  discounted-extremum lemma (`DiscountedExtremum.nonneg_of_mul_comp_le`). This is
  the infinite-horizon half of the verification argument (Stokey–Lucas–Prescott
  §4.1) along a single sequence, with no terminal-limit step: boundedness does
  the work. Its finite-horizon counterpart is
  `FiniteDiscountedTelescope.sum_add_terminal_add_residual_le`.

Rule 19: statements about real sequences only; the consumer is
`Examples/PlacableSenderSecurity.lean`. Rule 3: no hypothesis beyond the stated
bounds and recursion.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Sanctions.Foundations.DiscountedExtremum

namespace Sanctions
namespace Foundations
namespace DiscountedChordSum

/-- A bounded sequence is summable against a geometric discount `0 ≤ β < 1`. -/
theorem summable_pow_mul_of_abs_le {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → ℝ}
    (hf : ∀ t, |f t| ≤ M) : Summable (fun t : ℕ => β ^ t * f t) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => M * β ^ t)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left _) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_comm]
  exact mul_le_mul_of_nonneg_right (hf t) (pow_nonneg hβ0 t)

/-- The discounted sum of a sequence bounded by `M` is bounded by `M/(1 − β)`. -/
theorem abs_tsum_pow_mul_le {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → ℝ}
    (hf : ∀ t, |f t| ≤ M) : |∑' t, β ^ t * f t| ≤ M / (1 - β) := by
  have hs := summable_pow_mul_of_abs_le hβ0 hβ1 hf
  have hg := (summable_geometric_of_lt_one hβ0 hβ1).mul_left M
  have hgeo : ∑' t : ℕ, M * β ^ t = M / (1 - β) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
  have hup : ∑' t, β ^ t * f t ≤ ∑' t : ℕ, M * β ^ t :=
    Summable.tsum_le_tsum (fun t => by
      have := mul_le_mul_of_nonneg_left (abs_le.mp (hf t)).2 (pow_nonneg hβ0 t)
      linarith) hs hg
  have hlo : ∑' t : ℕ, -(M * β ^ t) ≤ ∑' t, β ^ t * f t :=
    Summable.tsum_le_tsum (fun t => by
      have := mul_le_mul_of_nonneg_left (abs_le.mp (hf t)).1 (pow_nonneg hβ0 t)
      linarith) hg.neg hs
  rw [tsum_neg] at hlo
  rw [abs_le]
  constructor <;> linarith

/-- **The head-and-shift identity**: `Σ β^t f t = f 0 + β·Σ β^t f (t+1)`. -/
theorem tsum_pow_mul_eq_head_add {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → ℝ}
    (hf : ∀ t, |f t| ≤ M) :
    ∑' t, β ^ t * f t = f 0 + β * ∑' t, β ^ t * f (t + 1) := by
  rw [(summable_pow_mul_of_abs_le hβ0 hβ1 hf).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul]
  congr 1
  exact tsum_congr fun t => by ring

/-- **The chord-sum inequality.** If bounded sequences `e`, `s` satisfy the
chord recursion `g·e t + d·s t ≤ e (t+1)` at every date, then
`e 0 + β·d·Σ β^t s t ≤ (1 − β·g)·Σ β^t e t`, for every discount `0 ≤ β < 1`. -/
theorem head_add_mul_tsum_le {β g d M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {e s : ℕ → ℝ} (he : ∀ t, |e t| ≤ M) (hs : ∀ t, |s t| ≤ M)
    (hstep : ∀ t, g * e t + d * s t ≤ e (t + 1)) :
    e 0 + β * d * ∑' t, β ^ t * s t ≤ (1 - β * g) * ∑' t, β ^ t * e t := by
  have hse := summable_pow_mul_of_abs_le hβ0 hβ1 he
  have hss := summable_pow_mul_of_abs_le hβ0 hβ1 hs
  have hse1 := summable_pow_mul_of_abs_le hβ0 hβ1 (f := fun t => e (t + 1)) (fun t => he (t + 1))
  have hshift := tsum_pow_mul_eq_head_add hβ0 hβ1 he
  have hsum : Summable (fun t : ℕ => β ^ t * (g * e t + d * s t)) :=
    ((hse.mul_left g).add (hss.mul_left d)).congr fun t => by ring
  have hsplit : ∑' t, β ^ t * (g * e t + d * s t)
      = g * ∑' t, β ^ t * e t + d * ∑' t, β ^ t * s t := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hse.mul_left g).tsum_add (hss.mul_left d)]
    exact tsum_congr fun t => by ring
  have hcmp : ∑' t, β ^ t * (g * e t + d * s t) ≤ ∑' t, β ^ t * e (t + 1) :=
    Summable.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hstep t) (pow_nonneg hβ0 t)) hsum hse1
  rw [hsplit] at hcmp
  have h1 := mul_le_mul_of_nonneg_left hcmp hβ0
  linarith

/-- **The supersolution bound.** A bounded `V` with `u t + β·V (t+1) ≤ V t` at
every date, for a bounded `u` and `0 ≤ β < 1`, dominates the discounted sum of
`u`: `Σ β^t u t ≤ V 0`. -/
theorem tsum_pow_mul_le_of_le_add_mul_succ {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {V u : ℕ → ℝ} (hV : ∀ t, |V t| ≤ M) (hu : ∀ t, |u t| ≤ M)
    (hstep : ∀ t, u t + β * V (t + 1) ≤ V t) :
    ∑' t, β ^ t * u t ≤ V 0 := by
  let P : ℕ → ℝ := fun n => ∑' t, β ^ t * u (n + t)
  have hP : ∀ n, P n = u n + β * P (n + 1) := by
    intro n
    have h := tsum_pow_mul_eq_head_add hβ0 hβ1 (f := fun t => u (n + t)) (fun t => hu (n + t))
    simp only [P]
    rw [h]
    simp only [add_zero]
    congr 2
    exact tsum_congr fun t => by rw [show n + (t + 1) = n + 1 + t by omega]
  have hPb : ∀ n, |P n| ≤ M / (1 - β) := fun n =>
    abs_tsum_pow_mul_le hβ0 hβ1 (fun t => hu (n + t))
  have hbdd : BddBelow (Set.range (fun n => V n - P n)) := by
    refine ⟨-(M + M / (1 - β)), ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 := abs_le.mp (hV n)
    have h2 := abs_le.mp (hPb n)
    simp only
    linarith
  have hnn := DiscountedExtremum.nonneg_of_mul_comp_le (f := fun n => V n - P n)
    (φ := Nat.succ) hβ0 hβ1 hbdd
    (fun n => by
      have h1 := hstep n
      have h2 := hP n
      change β * (V (n + 1) - P (n + 1)) ≤ V n - P n
      linarith) 0
  have hP0 : P 0 = ∑' t, β ^ t * u t := by simp only [P, zero_add]
  simp only at hnn
  linarith

end DiscountedChordSum
end Foundations
end Sanctions

#print axioms Sanctions.Foundations.DiscountedChordSum.summable_pow_mul_of_abs_le
#print axioms Sanctions.Foundations.DiscountedChordSum.abs_tsum_pow_mul_le
#print axioms Sanctions.Foundations.DiscountedChordSum.tsum_pow_mul_eq_head_add
#print axioms Sanctions.Foundations.DiscountedChordSum.head_add_mul_tsum_le
#print axioms Sanctions.Foundations.DiscountedChordSum.tsum_pow_mul_le_of_le_add_mul_succ
