/-
Sanctions/Examples/ReflectionSymmetricWitness.lean

**A non-affine reflection-symmetric transition** (round BD, 2026-10-01; Rule 9B
for `Theory/LockIn/EntryExitComparison.lean` and
`Theory/Microfoundations/FourGroupPlannerStateChord.lean`).

The entry/exit comparison is proved for every transition with
`F(1 − x, 1 − s) = 1 − F(x, s)` on the square, and the affine law is one. To show
that the hypothesis says more than the affine law, this file exhibits

`cubicReflectF x s = (x + s)/2 + (clip s − clip x)³/10`,

a transition in the `Params` class (continuous, nondecreasing in each argument on
all of `ℝ`, fixing the diagonal) that is reflection-symmetric on the square
(`cubicReflectF_reflect`), adjusts strictly (`reflectParams_strictAdjustment`) and
is **not** the affine law at any rate (`cubicReflectF_ne_affineF`). The
comparison theorem therefore applies at a non-affine economy
(`reflectParams_entryBound_lt_exitBound_iff`): there too the exit bound exceeds
the entry bound exactly when the threshold is below one half.

The same transition has the endpoint corner chords at `g = 2/5`
(`cubicReflectF_cornerChords`), so the sharpened welfare-gap bound
`pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords` also applies off the affine
law.

Existence certificates only (Rule 9A): nothing here says reflection symmetry is
typical, and the stage payoffs are `eeCertParams`'s, unchanged.
-/
import Sanctions.Examples.EECertWitness
import Sanctions.Theory.LockIn.EntryExitComparison
import Sanctions.Theory.Microfoundations.FourGroupPlannerStateChord

namespace Sanctions
namespace Examples

open Set AbstractGame

noncomputable section

/-- The cubic reflection-symmetric transition. -/
def cubicReflectF (x s : ℝ) : ℝ :=
  (x + s) / 2 + (Sanctions.clipS s - Sanctions.clipS x) ^ 3 / 10

private theorem clipS_eq_self {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Sanctions.clipS t = t := by
  unfold Sanctions.clipS
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- On the square the clips are inactive. -/
theorem cubicReflectF_sq {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    cubicReflectF x s = (x + s) / 2 + (s - x) ^ 3 / 10 := by
  unfold cubicReflectF
  rw [clipS_eq_self hx, clipS_eq_self hs]

theorem cubicReflectF_continuous :
    Continuous (fun (xs : ℝ × ℝ) => cubicReflectF xs.1 xs.2) := by
  unfold cubicReflectF Sanctions.clipS
  fun_prop

theorem cubicReflectF_diag : ∀ x : ℝ, cubicReflectF x x = x := by
  intro x
  unfold cubicReflectF
  ring

private theorem cube_le_cube {a b : ℝ} (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have hq : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hq]

/-- Monotone in the sanction: both terms rise with `s`. -/
theorem cubicReflectF_mono_s : ∀ x : ℝ, Monotone (fun s => cubicReflectF x s) := by
  intro x s₁ s₂ hle
  unfold cubicReflectF
  have h := cube_le_cube (sub_le_sub_right (Sanctions.clipS_mono hle) (Sanctions.clipS x))
  simp only
  linarith

/-- Monotone in the state: the cubic's state chord is at most `3/10 < 1/2`. -/
theorem cubicReflectF_mono_x : ∀ s : ℝ, Monotone (fun x => cubicReflectF x s) := by
  intro s x₁ x₂ hle
  unfold cubicReflectF
  set c₁ := Sanctions.clipS x₁
  set c₂ := Sanctions.clipS x₂
  set cs := Sanctions.clipS s
  have hc₁ : c₁ ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem x₁
  have hc₂ : c₂ ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem x₂
  have hcs : cs ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem s
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ x₂ - x₁ := by
    have := Sanctions.clipS_lipschitz_abs x₂ x₁
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c₂ - c₁),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x₂ - x₁)] at this
    linarith
  -- a = cs − c₁ ≥ b = cs − c₂, both in [−1,1]; a³ − b³ = (a − b)(a² + ab + b²) ≤ 3(a − b).
  have hkey : (cs - c₁) ^ 3 - (cs - c₂) ^ 3
      = (c₂ - c₁) * ((cs - c₁) ^ 2 + (cs - c₁) * (cs - c₂) + (cs - c₂) ^ 2) := by ring
  have hq : (cs - c₁) ^ 2 + (cs - c₁) * (cs - c₂) + (cs - c₂) ^ 2 ≤ 3 := by
    nlinarith [hc₁.1, hc₁.2, hc₂.1, hc₂.2, hcs.1, hcs.2]
  have hprod := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ c₂ - c₁)
  simp only
  nlinarith

/-- **The witness economy**: `eeCertParams` with the transition replaced. -/
def reflectParams : Params :=
  { eeCertParams with
    F := cubicReflectF
    F_continuous := cubicReflectF_continuous
    F_mono_x := cubicReflectF_mono_x
    F_mono_s := cubicReflectF_mono_s
    F_diag := cubicReflectF_diag }

@[simp] theorem reflectParams_F : reflectParams.F = cubicReflectF := rfl

/-- **Reflection symmetry on the square.** -/
theorem cubicReflectF_reflect :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      cubicReflectF (1 - x) (1 - s) = 1 - cubicReflectF x s := by
  intro x hx s hs
  rw [cubicReflectF_sq ⟨by linarith [hx.2], by linarith [hx.1]⟩
      ⟨by linarith [hs.2], by linarith [hs.1]⟩, cubicReflectF_sq hx hs]
  ring

/-- **Strict adjustment**: `F(x,s) − x = (s − x)(1/2 + (s − x)²/10)` has the sign
of `s − x` on the square. -/
theorem reflectParams_strictAdjustment : reflectParams.StrictAdjustment := by
  refine ⟨fun x s hx hs hlt => ?_, fun x s hx hs hlt => ?_⟩ <;>
    rw [reflectParams_F, cubicReflectF_sq hx hs]
  · nlinarith [sq_nonneg (s - x), mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hlt)]
  · nlinarith [sq_nonneg (s - x), mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hlt)]

/-- **Not the affine law at any rate.** `F(0,1) = 3/5` forces `δ = 3/5`, and then
`F(0, 1/2) = 21/80` misses `3/10`. -/
theorem cubicReflectF_ne_affineF (δ : ℝ) : cubicReflectF ≠ affineF δ := by
  intro h
  have h1 : cubicReflectF 0 1 = affineF δ 0 1 := by rw [h]
  have h2 : cubicReflectF 0 (1 / 2) = affineF δ 0 (1 / 2) := by rw [h]
  rw [cubicReflectF_sq (by norm_num) (by norm_num)] at h1 h2
  unfold affineF at h1 h2
  norm_num at h1 h2
  linarith

/-- **The entry/exit comparison at a non-affine economy.** At `reflectParams`, for
`0 < x̄ < 1`, the exit bound exceeds the entry bound iff `x̄ < 1/2`. -/
theorem reflectParams_entryBound_lt_exitBound_iff {xbar : ℝ} (h0 : 0 < xbar) (h1 : xbar < 1) :
    xbar / reflectParams.fullShockMinDrift xbar
        < (1 - xbar) / reflectParams.fullReliefMinDrift xbar ↔ xbar < 1 / 2 :=
  reflectParams.entryBound_lt_exitBound_iff_lt_half reflectParams_strictAdjustment
    (fun x hx s hs => by rw [reflectParams_F]; exact cubicReflectF_reflect x hx s hs) h0 h1

/-- **The endpoint corner chords at `g = 2/5`**, so the sharpened welfare-gap
bound applies to this non-affine transition:
`F(y,0) − (2/5)y = y(1 − y²)/10 ≥ 0` and
`1 − F(e,1) − (2/5)(1 − e) = (1 − e)(1 − (1 − e)²)/10 ≥ 0`. -/
theorem cubicReflectF_cornerChords :
    (∀ y ∈ Icc (0 : ℝ) 1, 2 / 5 * y ≤ cubicReflectF y 0) ∧
      ∀ e ∈ Icc (0 : ℝ) 1, 2 / 5 * (1 - e) ≤ 1 - cubicReflectF e 1 := by
  refine ⟨fun y hy => ?_, fun e he => ?_⟩
  · rw [cubicReflectF_sq hy ⟨le_rfl, zero_le_one⟩]
    nlinarith [hy.1, hy.2, mul_nonneg hy.1 (mul_nonneg hy.1 (sub_nonneg.mpr hy.2))]
  · rw [cubicReflectF_sq he ⟨zero_le_one, le_rfl⟩]
    have h1 : 0 ≤ 1 - e := by linarith [he.2]
    have h2 : 1 - e ≤ 1 := by linarith [he.1]
    nlinarith [mul_nonneg h1 (mul_nonneg h1 (sub_nonneg.mpr h2))]

end

end Examples
end Sanctions

#print axioms Sanctions.Examples.cubicReflectF_mono_x
#print axioms Sanctions.Examples.cubicReflectF_mono_s
#print axioms Sanctions.Examples.cubicReflectF_reflect
#print axioms Sanctions.Examples.reflectParams_strictAdjustment
#print axioms Sanctions.Examples.cubicReflectF_ne_affineF
#print axioms Sanctions.Examples.reflectParams_entryBound_lt_exitBound_iff
#print axioms Sanctions.Examples.cubicReflectF_cornerChords
