/-
Sanctions/Examples/Counterexamples/SemiconcaveRiccatiMonotone.lean

**ROLE: NECESSITY.**

`bellman_semiconcave_step` carries a hypothesis that the continuation value is
nondecreasing. That looks like a regularity convenience and is not: drop it and
the conclusion is false, so the hypothesis is load-bearing.

The economy that breaks it is built from parts that are each as well behaved as
one could ask --- a flat stage payoff, a transition that is concave, monotone and
1-Lipschitz, a discount factor of one half --- with the single defect that the
continuation `V z = -z` is *decreasing*. The image then has a convex kink, and a
convex kink admits no finite semiconcavity modulus at all: chord-comparing
either side of it gives a defect of order `eps` against a budget of order
`eps^2`. The failure is entirely on the continuation side, which is what makes
it informative rather than a knife-edge of the transition.

Rule 11: this is the disprove gate, run before the theorem was trusted. Rule 9:
it refutes one hypothesis-dropping, and says nothing about how much weaker a
replacement for monotonicity could be.

Relocated 2026-08-27 from `Foundations/SemiconcaveRiccati.lean`. Statement
byte-identical, namespace unchanged.
-/
import Sanctions.Foundations.SemiconcaveRiccati

noncomputable section
open Set

namespace Sanctions.Semiconcave

/-! ## 5b. The fence: monotonicity of the continuation cannot be dropped

`M_state`-semiconcavity of the successor section is a **one-sided** bound:
it says the realized successor is not far *below* the chord, and says
nothing about how far above it may sit.  So a Lipschitz bound on `V` alone
cannot price the off-chord displacement — the displacement is only `O(Δy)`,
not `O(Δy²)`, and no finite modulus can absorb an `O(Δy)` charge.  What
rescues the estimate is that `V` is nondecreasing, which makes the adverse
branch free.

This is recorded as a refutation, not a remark: dropping `hV_mono` from
`bellman_semiconcave_step` makes the conclusion **false**, and here is the
economy that breaks it. -/

/-- **`hV_mono` is necessary.** Every other hypothesis of
`bellman_semiconcave_step` holds at

* `stage ≡ 0` (no stage curvature, `ψ = 0`);
* `V z = −z` — `1`-Lipschitz and linear hence `0`-semiconcave, but
  *decreasing*;
* `G y = min y (1/2)` — maps `[0,1]` into `[0,1]`, obeys the band
  `[glo, ghi] = [0, 1]`, and is concave hence `0`-semiconcave;
* `β = 1/2 < 1`;

and yet the image `y ↦ 0 + (1/2)·(−min y (1/2))` has a convex kink at
`y = 1/2` and therefore admits **no** finite semiconcavity modulus at all.
Chord-comparing at `1/2 ∓ ε` gives a defect of order `ε` against a budget
of order `ε²`.

Note this is not a knife-edge of the transition: `G` here is as regular as
one could ask (concave, `1`-Lipschitz, monotone). The failure is entirely on
the continuation side. -/
theorem bellman_semiconcave_step_needs_monotone :
    ∃ (stage V G : ℝ → ℝ) (β ψ Sg K glo ghi M_state : ℝ),
      0 ≤ β ∧ 0 ≤ Sg ∧ 0 ≤ K ∧ 0 ≤ glo ∧ 0 ≤ M_state ∧ β < 1 ∧
      0 ≤ ghi ∧ ghi ≤ 1 ∧
      (∀ y ∈ Icc (0 : ℝ) 1, G y ∈ Icc (0 : ℝ) 1) ∧
      StateChordBand G glo ghi ∧
      SemiconcaveOnSet G (Icc (0 : ℝ) 1) M_state ∧
      SemiconcaveOnSet stage (Icc (0 : ℝ) 1) ψ ∧
      SemiconcaveOnSet V (Icc (0 : ℝ) 1) Sg ∧
      (∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
        |V z₁ - V z₂| ≤ K * |z₁ - z₂|) ∧
      ¬ ∃ c : ℝ,
        SemiconcaveOnSet (fun y => stage y + β * V (G y))
          (Icc (0 : ℝ) 1) c := by
  refine ⟨fun _ => 0, fun z => -z, fun y => min y (1/2),
    1/2, 0, 0, 1, 0, 1, 0,
    by norm_num, le_rfl, by norm_num, le_rfl, le_rfl, by norm_num,
    by norm_num, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `G` maps `[0,1]` into `[0,1]`.
    intro y hy
    exact ⟨le_min hy.1 (by norm_num), le_trans (min_le_right _ _) (by norm_num)⟩
  · -- `G` obeys the band `[0, 1]`.
    intro y₁ _ y₂ _ hle
    refine ⟨by
      simp only [zero_mul]; simp only [sub_nonneg]
      exact min_le_min hle le_rfl, ?_⟩
    simp only [one_mul]
    rcases le_total y₂ (1/2 : ℝ) with h | h
    · rw [min_eq_left h, min_eq_left (le_trans hle h)]
    · rw [min_eq_right h]
      rcases le_total y₁ (1/2 : ℝ) with h' | h'
      · rw [min_eq_left h']; linarith
      · rw [min_eq_right h']; linarith
  · -- `G` is concave, hence `0`-semiconcave.
    intro y₁ _ y₂ _ t ht0 ht1
    have hle : t * min y₁ (1/2) + (1 - t) * min y₂ (1/2)
        ≤ min (t * y₁ + (1 - t) * y₂) (1/2) := by
      refine le_min ?_ ?_
      · have h1 : t * min y₁ (1/2) ≤ t * y₁ :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) ht0
        have h2 : (1 - t) * min y₂ (1/2) ≤ (1 - t) * y₂ :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
        linarith
      · have h1 : t * min y₁ (1/2) ≤ t * (1/2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
        have h2 : (1 - t) * min y₂ (1/2) ≤ (1 - t) * (1/2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
        linarith
    have hP : (0 : ℝ) ≤ t * (1 - t) * (y₁ - y₂) ^ 2 :=
      mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
    simp only
    linarith
  · -- `stage ≡ 0` is `0`-semiconcave.
    intro y₁ _ y₂ _ t ht0 ht1
    have hP : (0 : ℝ) ≤ t * (1 - t) * (y₁ - y₂) ^ 2 :=
      mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
    simp only
    linarith
  · -- `V z = −z` is linear, hence `0`-semiconcave.
    intro z₁ _ z₂ _ t ht0 ht1
    have hP : (0 : ℝ) ≤ t * (1 - t) * (z₁ - z₂) ^ 2 :=
      mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
    simp only
    nlinarith [hP]
  · -- `V` is `1`-Lipschitz.
    intro z₁ _ z₂ _
    simp only [one_mul]
    rw [show -z₁ - -z₂ = -(z₁ - z₂) by ring, abs_neg]
  · -- ... and yet the image admits no finite semiconcavity modulus.
    rintro ⟨c, hc⟩
    -- Chord at `y₁ = 1/2 − ε`, `y₂ = 1/2 + ε`, weight `1/2`: the kink of
    -- the image at `y = 1/2` produces a defect of order `ε`, while the
    -- semiconcavity budget is only of order `ε²`.
    have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ 2 * c * ε ^ 2 := by
      intro ε hε hε2
      have h := hc (1/2 - ε) ⟨by linarith, by linarith⟩ (1/2 + ε)
        ⟨by linarith, by linarith⟩ (1/2) (by norm_num) (by norm_num)
      simp only [show (1:ℝ)/2 * (1/2 - ε) + (1 - 1/2) * (1/2 + ε) = 1/2 by ring,
        min_self, min_eq_left (by linarith : (1:ℝ)/2 - ε ≤ 1/2),
        min_eq_right (by linarith : (1:ℝ)/2 ≤ 1/2 + ε)] at h
      nlinarith [h]
    have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → 1 ≤ 2 * c * ε := by
      intro ε hε hε2
      nlinarith [key ε hε hε2]
    have hc1 : (1:ℝ) ≤ c := by
      have := hstep (1/2) (by norm_num) le_rfl; linarith
    have hcpos : (0:ℝ) < c := by linarith
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hle : 1 / (4 * c) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * c)]
      linarith
    have h2 := hstep (1 / (4 * c)) (by positivity) hle
    have hval : 2 * c * (1 / (4 * c)) = 1 / 2 := by field_simp; ring
    rw [hval] at h2
    linarith

end Sanctions.Semiconcave

end
