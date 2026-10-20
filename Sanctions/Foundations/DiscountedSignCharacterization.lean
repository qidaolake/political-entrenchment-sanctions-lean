/-
Sanctions/Foundations/DiscountedSignCharacterization.lean

**When is a discounted series `Σ_t β^t (C − B·d_t)` positive at every discount
factor?** For a sequence `d` with `d 0 = 0`, `d t ∈ [0,1]` and `d t → 1`, the
series is positive for every `β ∈ [0,1)` **iff** `0 < C` and `B ≤ C`.

At `β = 0` only the date-zero term `C` survives, so `C > 0` is necessary. If
`C < B`, the terms are eventually below `−(B − C)/2` and a discount close
enough to one lets the tail dominate the finitely many early terms, so `B ≤ C`
is necessary. Conversely, if `0 < C` and `B ≤ C` then every term is
nonnegative — `C − B·d_t ≥ C − B ≥ 0` for `B ≥ 0`, and `≥ C` for `B < 0` — and
the date-zero term is `C > 0`.

The convergence `d t → 1` is what the necessity direction uses and cannot be
dropped: with `d ≡ 0`, `C = 1`, `B = 2` the series is `1/(1−β) > 0` for every
`β` although `B > C` (`not_necessary_without_tendsto`).

Nothing here mentions the sanctions model (Rule 19); the consumer is the
general-transition welfare accounting of
`Theory/Microfoundations/FourGroupPlanner.lean`, where `d_t = e_t − y_t` is
the separation of the two endpoint state paths and strict adjustment supplies
`d_t → 1`. Round U, 2026-09-15 (doc 87 W6; the reader's 09-12 package,
document 02 §5, supplied the statement and the proof).
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace Sanctions
namespace DiscountedSign

open Filter Topology Finset

/-- The discounted series of a bounded sequence is summable for `β ∈ [0,1)`. -/
theorem summable_discounted {β C B : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {d : ℕ → ℝ}
    (hd : ∀ t, d t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun t : ℕ => β ^ t * (C - B * d t)) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => (|C| + |B|) * β ^ t)
    ((summable_geometric_of_lt_one hβ.1 hβ.2).mul_left _) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.1]
  have hdt := hd t
  have hBd : |B * d t| ≤ |B| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith [hdt.1], hdt.2⟩)
  have h1 : |C - B * d t| ≤ |C| + |B| := (abs_sub _ _).trans (by linarith)
  have hp : 0 ≤ β ^ t := pow_nonneg hβ.1 t
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]

/-- **Sufficiency**: `0 < C` and `B ≤ C` make every term nonnegative and the
date-zero term positive. -/
theorem tsum_pos_of_lt_of_le {β C B : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {d : ℕ → ℝ}
    (hd0 : d 0 = 0) (hd : ∀ t, d t ∈ Set.Icc (0 : ℝ) 1) (hC : 0 < C) (hBC : B ≤ C) :
    0 < ∑' t : ℕ, β ^ t * (C - B * d t) := by
  have hs := summable_discounted (C := C) (B := B) hβ hd
  have hterm : ∀ t, 0 ≤ β ^ t * (C - B * d t) := by
    intro t
    have hdt := hd t
    apply mul_nonneg (pow_nonneg hβ.1 t)
    rcases le_or_gt 0 B with hB | hB
    · nlinarith [mul_le_mul_of_nonneg_left hdt.2 hB]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hB.le) hdt.1]
  have h0 : β ^ 0 * (C - B * d 0) = C := by simp [hd0]
  calc (0 : ℝ) < C := hC
    _ = β ^ 0 * (C - B * d 0) := h0.symm
    _ ≤ ∑' t : ℕ, β ^ t * (C - B * d t) := hs.le_tsum 0 (fun j _ => hterm j)

/-- At `β = 0` the series is its date-zero term. -/
theorem tsum_at_zero {C B : ℝ} {d : ℕ → ℝ} (hd0 : d 0 = 0) :
    (∑' t : ℕ, (0 : ℝ) ^ t * (C - B * d t)) = C := by
  rw [tsum_eq_single 0]
  · simp [hd0]
  · intro t ht
    simp [zero_pow ht]

/-- **Necessity**: positivity at every discount forces `0 < C` and `B ≤ C`,
given `d t → 1`. The proof splits the series at the date `N` after which
`d t > 1 − (B − C)/(2B)`, bounds the head by `C·(1 − β^N)/(1 − β)` and the
tail by `−ε·β^N/(1 − β)` with `ε = (B − C)/2`, and takes `β = 1 − η` with
`η` small enough that Bernoulli's inequality gives `(C + ε)·β^N > C`. -/
theorem lt_and_le_of_tsum_pos_all {C B : ℝ} {d : ℕ → ℝ} (hd0 : d 0 = 0)
    (hd : ∀ t, d t ∈ Set.Icc (0 : ℝ) 1) (hlim : Tendsto d atTop (𝓝 1))
    (h : ∀ β ∈ Set.Ico (0 : ℝ) 1, 0 < ∑' t : ℕ, β ^ t * (C - B * d t)) :
    0 < C ∧ B ≤ C := by
  have hC : 0 < C := by
    have h0 := h 0 ⟨le_rfl, by norm_num⟩
    rwa [tsum_at_zero hd0] at h0
  refine ⟨hC, ?_⟩
  by_contra hlt
  have hCB : C < B := lt_of_not_ge hlt
  set ε := (B - C) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hBpos : 0 < B := by linarith
  -- after some date N the tail terms are below −ε
  have hev : ∀ᶠ t in atTop, 1 - ε / B < d t :=
    hlim.eventually (lt_mem_nhds (by
      have : 0 < ε / B := div_pos hεpos hBpos
      linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have htail : ∀ t, N ≤ t → C - B * d t ≤ -ε := by
    intro t ht
    have h1 := hN t ht
    have : B * (1 - ε / B) < B * d t := mul_lt_mul_of_pos_left h1 hBpos
    have h2 : B * (1 - ε / B) = B - ε := by field_simp
    rw [hε] at h2 ⊢
    nlinarith [h2, this]
  have hhead : ∀ t, C - B * d t ≤ C := by
    intro t
    have := hd t
    nlinarith [mul_nonneg hBpos.le this.1]
  -- the discount: β = 1 − η with 0 < η ≤ 1/2 and N·η ≤ ε/(2(C+ε))
  set η := min (1 / 2) (ε / (2 * (N + 1) * (C + ε))) with hη
  have hCε : 0 < C + ε := by linarith
  have hη0 : 0 < η := lt_min (by norm_num) (div_pos hεpos (by positivity))
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηN : η * (N + 1) ≤ ε / (2 * (C + ε)) := by
    have := min_le_right (1 / 2 : ℝ) (ε / (2 * (N + 1) * (C + ε)))
    rw [← hη] at this
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    calc η * (N + 1) ≤ ε / (2 * (N + 1) * (C + ε)) * (N + 1) :=
          mul_le_mul_of_nonneg_right this hN1.le
      _ = ε / (2 * (C + ε)) := by field_simp
  set β := 1 - η with hβdef
  have hβ : β ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hsum := h β hβ
  -- Bernoulli: β^N ≥ 1 − N·η, hence (C + ε)·β^N > C
  have hbern : 1 - (N : ℝ) * η ≤ β ^ N := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -η by linarith) N
    simpa [hβdef, sub_eq_add_neg, mul_neg, mul_comm] using this
  have hpowN : C < (C + ε) * β ^ N := by
    have h1 : (C + ε) * (1 - N * η) ≤ (C + ε) * β ^ N :=
      mul_le_mul_of_nonneg_left hbern hCε.le
    have h2 : (C + ε) * (N * η) ≤ ε / 2 := by
      have : (N : ℝ) * η ≤ η * (N + 1) := by nlinarith [hη0]
      calc (C + ε) * (N * η) ≤ (C + ε) * (η * (N + 1)) :=
            mul_le_mul_of_nonneg_left this hCε.le
        _ ≤ (C + ε) * (ε / (2 * (C + ε))) := mul_le_mul_of_nonneg_left hηN hCε.le
        _ = ε / 2 := by field_simp
    nlinarith [h1, h2]
  -- split the series at N and bound both parts
  have hs := summable_discounted (β := β) (C := C) (B := B) hβ hd
  have hsplit := hs.sum_add_tsum_nat_add N
  have h1β : (0 : ℝ) < 1 - β := by linarith
  have hgeom : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.1 hβ.2
  have hhead_le : (∑ t ∈ range N, β ^ t * (C - B * d t)) ≤ C * ((1 - β ^ N) / (1 - β)) := by
    have : (∑ t ∈ range N, β ^ t * (C - B * d t)) ≤ ∑ t ∈ range N, β ^ t * C :=
      sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hhead t) (pow_nonneg hβ.1 t))
    have hg : (∑ t ∈ range N, β ^ t * C) = C * ((1 - β ^ N) / (1 - β)) := by
      rw [← sum_mul, geom_sum_eq (by linarith : β ≠ 1) N]
      have hq : (β ^ N - 1) / (β - 1) = (1 - β ^ N) / (1 - β) := by
        rw [div_eq_div_iff (by linarith : β - 1 ≠ 0) (by linarith : (1 : ℝ) - β ≠ 0)]
        ring
      rw [hq]
      ring
    linarith [this, hg]
  have htail_le : (∑' t : ℕ, β ^ (t + N) * (C - B * d (t + N))) ≤ -ε * (β ^ N / (1 - β)) := by
    have hsN : Summable (fun t : ℕ => β ^ (t + N) * (C - B * d (t + N))) :=
      (summable_nat_add_iff N).mpr hs
    have hgN : Summable (fun t : ℕ => β ^ (t + N) * (-ε)) := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using
        ((hgeom.mul_left (β ^ N)).mul_right (-ε))
    have hle : ∀ t, β ^ (t + N) * (C - B * d (t + N)) ≤ β ^ (t + N) * (-ε) :=
      fun t => mul_le_mul_of_nonneg_left (htail (t + N) (by omega)) (pow_nonneg hβ.1 _)
    calc (∑' t : ℕ, β ^ (t + N) * (C - B * d (t + N)))
        ≤ ∑' t : ℕ, β ^ (t + N) * (-ε) := hsN.tsum_le_tsum hle hgN
      _ = -ε * (β ^ N / (1 - β)) := by
          simp only [pow_add]
          rw [show (fun t : ℕ => β ^ t * β ^ N * (-ε)) = fun t : ℕ => (β ^ N * (-ε)) * β ^ t by
                funext t; ring]
          rw [tsum_mul_left, tsum_geometric_of_lt_one hβ.1 hβ.2]
          field_simp
  -- combine: the series is at most (C − (C+ε)β^N)/(1 − β) < 0
  have : (∑' t : ℕ, β ^ t * (C - B * d t)) ≤ (C - (C + ε) * β ^ N) / (1 - β) := by
    rw [← hsplit]
    have := add_le_add hhead_le htail_le
    calc _ ≤ C * ((1 - β ^ N) / (1 - β)) + -ε * (β ^ N / (1 - β)) := this
      _ = (C - (C + ε) * β ^ N) / (1 - β) := by field_simp; ring
  have hneg : (C - (C + ε) * β ^ N) / (1 - β) < 0 :=
    div_neg_of_neg_of_pos (by linarith) h1β
  linarith

/-- **The characterization**: for a sequence starting at zero, valued in
`[0,1]` and converging to one, the discounted series `Σ β^t (C − B d_t)` is
positive at every `β ∈ [0,1)` iff `0 < C` and `B ≤ C`. -/
theorem tsum_pos_all_discounts_iff {C B : ℝ} {d : ℕ → ℝ} (hd0 : d 0 = 0)
    (hd : ∀ t, d t ∈ Set.Icc (0 : ℝ) 1) (hlim : Tendsto d atTop (𝓝 1)) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1, 0 < ∑' t : ℕ, β ^ t * (C - B * d t)) ↔ (0 < C ∧ B ≤ C) :=
  ⟨lt_and_le_of_tsum_pos_all hd0 hd hlim,
   fun ⟨hC, hBC⟩ β hβ => tsum_pos_of_lt_of_le (β := β) hβ hd0 hd hC hBC⟩

/-- **Refutation boundary (Rule 11)**: without `d t → 1` the necessity direction
fails. With `d ≡ 0`, `C = 1`, `B = 2` the series is `1/(1 − β) > 0` at every
discount although `B > C`. -/
theorem not_necessary_without_tendsto :
    (∀ β ∈ Set.Ico (0 : ℝ) 1, 0 < ∑' t : ℕ, β ^ t * ((1 : ℝ) - 2 * (fun _ : ℕ => (0 : ℝ)) t))
      ∧ ¬ ((2 : ℝ) ≤ 1) := by
  refine ⟨fun β hβ => ?_, by norm_num⟩
  have h : (fun t : ℕ => β ^ t * ((1 : ℝ) - 2 * (fun _ : ℕ => (0 : ℝ)) t))
      = fun t : ℕ => β ^ t := by
    funext t; simp
  rw [h, tsum_geometric_of_lt_one hβ.1 hβ.2]
  have : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  positivity

end DiscountedSign

#print axioms DiscountedSign.tsum_pos_all_discounts_iff
#print axioms DiscountedSign.lt_and_le_of_tsum_pos_all
#print axioms DiscountedSign.not_necessary_without_tendsto

end Sanctions
