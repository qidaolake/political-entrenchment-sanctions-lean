/-
Sanctions/Examples/Counterexamples/CornerChordAttained.lean

**ROLE: FAILURE OF CONVERSE (the corner-chord bound is attained off the affine
law).**

`sanctionLowerChord_le_of_cornerTop` (`Foundations/TransitionChords.lean`)
proves `d ≤ 1 − γ`: a lower sanction chord rate never exceeds the corner
section's responsiveness. Its docstring once added "with equality exactly when
the sanction section is affine", which is false; round P (2026-09-11, the
reader's C03–C04) corrected the words, and this file is the Rule-11 object
behind the correction (round Q1): a transition that attains the bound,
`d = 1 − γ = 1/2`, and is not the affine law at that rate.

The law is `hookF x s = (x + s)/2 − (max (clip x − clip s) 0)²/10`: the affine
law at rate `1/2` minus a bump that is active only above the diagonal
(`x > s`) and vanishes on it. On the square the clip is the identity, the bump
is nonincreasing in the sanction, so every sanction section has chord slope at
least `1/2`; along `s = 1` the bump is inactive, so the top section is
`(x + 1)/2`; and `hookF 1 0 = 2/5`, where the affine law at rate `1/2` gives
`1/2`. Clipping the bump's arguments while the linear part stays unclipped is
the device of `quadDiagF`: the law is monotone in each argument on the whole
line, fixes the diagonal everywhere, is continuous, and maps the square into
itself — every transition primitive of `Params` — though no `Params` is built
here, because the predicates the file is about live on bare transitions.

Rule 9: existence only — one law attaining the bound off the affine class,
which says nothing about how large that set is. Rule 22: the counterexample is
the point that a chord *equality* does not pin the functional form; the
predicates it uses are the scoped ones of `Foundations/TransitionChords.lean`.
-/
import Sanctions.Foundations.TransitionChords
import Sanctions.Domain.UnitIntervalProjection
import Sanctions.Postulates.AbstractGame

namespace Sanctions.TransitionChords

open Set

/-- The affine law at rate `1/2` minus a bump active above the diagonal. -/
noncomputable def hookF (x s : ℝ) : ℝ :=
  (x + s) / 2 - (max (Sanctions.clipS x - Sanctions.clipS s) 0) ^ 2 / 10

theorem clipS_eq_self {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : Sanctions.clipS y = y := by
  unfold Sanctions.clipS
  rw [min_eq_right hy.2, max_eq_right hy.1]

/-- On the square the law reads `(x + s)/2 − max(x − s, 0)²/10`. -/
theorem hookF_of_mem {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    hookF x s = (x + s) / 2 - (max (x - s) 0) ^ 2 / 10 := by
  unfold hookF
  rw [clipS_eq_self hx, clipS_eq_self hs]

/-- The diagonal is fixed everywhere: the bump vanishes at `x = s`. -/
theorem hookF_diag (x : ℝ) : hookF x x = x := by
  unfold hookF
  simp

/-- **The lower chord rate `1/2` holds**: the bump is nonincreasing in the
sanction, so a sanction section rises at least as fast as the affine part. -/
theorem hookF_lowerChord : SanctionLowerChord hookF (1 / 2) := by
  intro x s₁ s₂ hx hs₁ hs₂ h
  rw [hookF_of_mem hx hs₁, hookF_of_mem hx hs₂]
  have hm : max (x - s₂) 0 ≤ max (x - s₁) 0 := max_le_max (by linarith) le_rfl
  have hb : (max (x - s₂) 0) ^ 2 ≤ (max (x - s₁) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) hm 2
  linarith

/-- **The top section is the normalised affine map with weight `1/2`**: at
`s = 1` the bump is inactive. -/
theorem hookF_cornerTop : CornerSectionTop hookF (1 / 2) := by
  intro y hy
  rw [hookF_of_mem hy ⟨zero_le_one, le_rfl⟩]
  have : max (y - 1) 0 = 0 := max_eq_right (by linarith [hy.2])
  rw [this]
  ring

theorem hookF_zero : hookF 0 0 = 0 := hookF_diag 0

/-- Off the diagonal the bump bites: `hookF 1 0 = 2/5`, not the affine `1/2`. -/
theorem hookF_one_zero : hookF 1 0 = 2 / 5 := by
  rw [hookF_of_mem ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩]
  norm_num

/-- **The law is not the affine law at rate `1/2`**, the rate its corner
section and its lower chord share. -/
theorem hookF_ne_affineF : hookF ≠ AbstractGame.affineF (1 / 2) := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  rw [hookF_one_zero] at h10
  norm_num [AbstractGame.affineF] at h10

/-- Feasible on the square: the bump is at most `x/10`. -/
theorem hookF_mem {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    hookF x s ∈ Icc (0 : ℝ) 1 := by
  rw [hookF_of_mem hx hs]
  have hm0 : 0 ≤ max (x - s) 0 := le_max_right _ _
  have hm1 : max (x - s) 0 ≤ x := max_le (by linarith [hs.1]) hx.1
  have hsq : (max (x - s) 0) ^ 2 ≤ max (x - s) 0 := by
    have : max (x - s) 0 ≤ 1 := le_trans hm1 hx.2
    nlinarith
  constructor
  · nlinarith [hx.1, hs.1]
  · nlinarith [hx.2, hs.2]

/-- Nondecreasing in the sanction on the whole line (the bump only falls). -/
theorem hookF_mono_s (x : ℝ) : Monotone (fun s => hookF x s) := by
  intro s₁ s₂ h
  show (x + s₁) / 2 - (max (Sanctions.clipS x - Sanctions.clipS s₁) 0) ^ 2 / 10
    ≤ (x + s₂) / 2 - (max (Sanctions.clipS x - Sanctions.clipS s₂) 0) ^ 2 / 10
  have hc := Sanctions.clipS_mono h
  have hm : max (Sanctions.clipS x - Sanctions.clipS s₂) 0
      ≤ max (Sanctions.clipS x - Sanctions.clipS s₁) 0 :=
    max_le_max (by linarith) le_rfl
  have hb := pow_le_pow_left₀ (le_max_right _ _) hm 2
  linarith

/-- Nondecreasing in the state on the whole line: the bump rises at most at
rate `2/10` (its argument moves at most as fast as the clip, and the square of
a quantity in `[0,1]` moves at most twice as fast), below the linear `1/2`. -/
theorem hookF_mono_x (s : ℝ) : Monotone (fun x => hookF x s) := by
  intro x₁ x₂ h
  show (x₁ + s) / 2 - (max (Sanctions.clipS x₁ - Sanctions.clipS s) 0) ^ 2 / 10
    ≤ (x₂ + s) / 2 - (max (Sanctions.clipS x₂ - Sanctions.clipS s) 0) ^ 2 / 10
  set c := Sanctions.clipS s with hc
  have hclip : Sanctions.clipS x₂ - Sanctions.clipS x₁ ≤ x₂ - x₁ := by
    have := Sanctions.clipS_lipschitz_abs x₂ x₁
    have h' := Sanctions.clipS_mono h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
    exact this
  set m₁ := max (Sanctions.clipS x₁ - c) 0 with hm₁
  set m₂ := max (Sanctions.clipS x₂ - c) 0 with hm₂
  have hm₁0 : 0 ≤ m₁ := le_max_right _ _
  have hm₂0 : 0 ≤ m₂ := le_max_right _ _
  have hm12 : m₁ ≤ m₂ := max_le_max (by linarith [Sanctions.clipS_mono h]) le_rfl
  have hm₂1 : m₂ ≤ 1 := by
    have h1 := (Sanctions.clipS_mem x₂).2
    have h2 := (Sanctions.clipS_mem s).1
    exact max_le (by rw [hc]; linarith) zero_le_one
  have hdiff : m₂ - m₁ ≤ x₂ - x₁ := by
    rcases le_or_gt (Sanctions.clipS x₂ - c) 0 with h0 | h0
    · have : m₂ = 0 := max_eq_right h0
      linarith
    · have e2 : m₂ = Sanctions.clipS x₂ - c := max_eq_left h0.le
      have e1 : Sanctions.clipS x₁ - c ≤ m₁ := le_max_left _ _
      linarith
  have hsq : m₂ ^ 2 - m₁ ^ 2 ≤ 2 * (x₂ - x₁) := by
    have : m₂ ^ 2 - m₁ ^ 2 = (m₂ - m₁) * (m₂ + m₁) := by ring
    rw [this]
    have h1 : m₂ + m₁ ≤ 2 := by linarith
    have h2 : 0 ≤ m₂ - m₁ := by linarith
    calc (m₂ - m₁) * (m₂ + m₁) ≤ (m₂ - m₁) * 2 := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ (x₂ - x₁) * 2 := mul_le_mul_of_nonneg_right hdiff (by norm_num)
      _ = 2 * (x₂ - x₁) := by ring
  linarith

theorem hookF_continuous : Continuous (fun p : ℝ × ℝ => hookF p.1 p.2) := by
  unfold hookF
  have h1 : Continuous (fun p : ℝ × ℝ => Sanctions.clipS p.1 - Sanctions.clipS p.2) :=
    (Sanctions.clipS_continuous.comp continuous_fst).sub
      (Sanctions.clipS_continuous.comp continuous_snd)
  have h2 : Continuous (fun p : ℝ × ℝ => max (Sanctions.clipS p.1 - Sanctions.clipS p.2) 0) :=
    h1.max continuous_const
  exact ((continuous_fst.add continuous_snd).div_const 2).sub ((h2.pow 2).div_const 10)

/-- **The corner-chord bound is attained off the affine law.** There is a
transition with `F 0 0 = 0`, a corner section of weight `γ`, and a lower
sanction chord at exactly the rate `1 − γ` the bound allows, which is not the
affine law at that rate. So equality in `sanctionLowerChord_le_of_cornerTop`
does not force affineness. -/
theorem exists_nonaffine_attaining_cornerChord_bound :
    ∃ (F : ℝ → ℝ → ℝ) (d γ : ℝ), F 0 0 = 0 ∧ CornerSectionTop F γ ∧
      SanctionLowerChord F d ∧ d = 1 - γ ∧ F ≠ AbstractGame.affineF (1 - γ) := by
  refine ⟨hookF, 1 / 2, 1 / 2, hookF_zero, hookF_cornerTop, hookF_lowerChord, by norm_num, ?_⟩
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [this]
  exact hookF_ne_affineF

#print axioms Sanctions.TransitionChords.exists_nonaffine_attaining_cornerChord_bound

end Sanctions.TransitionChords
