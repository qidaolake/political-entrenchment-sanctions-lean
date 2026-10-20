/-
Sanctions/Examples/ChordInvarianceWitnesses.lean

**Non-vacuity and necessity witnesses for the two-sided chord carrier.**

Every declaration in this file was proved in
`Sanctions/Theory/Bellman/ChordInvariance.lean` and moved here on 2026-08-22
under Rule 22. Nothing is new mathematics and nothing is deleted: these are the
concrete numeric exhibits that keep the general theory honest, and Rule 9 is
what they discharge.

Two probes, answering two different questions about
`mem_valLipGainBall_bellman_chord` --- the theorem that keeps a value function
inside its carrier when the transition is controlled only by a two-sided chord
band, rather than by an exact closed form.

* **`ZZProbe` --- the class is not empty, and it is genuinely wider than the
  affine one.** A transition whose corner section `y` maps to `1/2 + y/4 + y^2/4`
  is quadratic, so no constant rate describes it (`Fnf_not_cornerSectionTop`:
  there is no `gamma` making it affine along the corner). It nonetheless
  satisfies the band with `glo = 1/4` strictly below `ghi = 3/4`, and carries a
  cone with `g = 8/7` strictly below `K = 8/5` (`probe_g_lt_K`) --- so the
  carrier is two-sided rather than slope-pinned. This is the Rule 9B generality
  witness: the class is inhabited *outside* the affine case it generalises.
* **`Escape` --- one hypothesis is load-bearing, not decorative.** Rule 11
  necessity: `Fesc x s = x + s` satisfies the chord band but sends its corner
  section out of `[0,1]`, and its Bellman image then leaves the carrier
  (`Wesc_not_mem`). So the interval-preservation side condition cannot be
  dropped from the general theorem.

The numeric constants are what makes these witnesses, and per Rule 9A that is
all they license: the class is inhabited and the side condition is necessary.
They support no universal, no genericity claim, and no statement about the
magnitudes themselves.

**Why this is in `Examples/` and not `Theory/`.** The two general theorems these
probe --- `mem_valLipGainBall_bellman_chord` and `valueLipschitz_bellman_chord`
--- stay in `Theory/`, general in the transition and free of numerals. The
probes are concrete economies, which is what `Examples/` is for. Checked before
the move: the block has no consumer outside itself, and no citation in `paper/`.
-/

import Sanctions.Theory.Bellman.ChordInvariance

/-!
Rule-9 non-vacuity probe for CORE 2, at a genuinely NON-AFFINE corner section.

Corner section:  F y 1 = 1/2 + y/4 + y²/4.   F 1 1 = 1, F 0 1 = 1/2.
Chord band:      glo = 1/4, ghi = 3/4   (chord factor (1 + y₁ + y₂)/4 ∈ [1/4, 3/4]).
Scalars:         β = 1/2, stage y = y (L_U = g_U = M_U = 1, c₀ = 0).
Carrier:         M = 2, K = 8/5, g = 8/7.   g < K, so the cone is genuinely two-sided.
-/

open Set

namespace ZZProbe

open Sanctions Sanctions.TransitionChords Sanctions.AbstractGame.Params

/-- A genuinely non-affine transition. -/
noncomputable def Fnf : ℝ → ℝ → ℝ :=
  fun x s => s * (1/2 + x/4 + x^2/4) + (1 - s) * x

theorem Fnf_corner (y : ℝ) : Fnf y 1 = 1/2 + y/4 + y^2/4 := by
  simp only [Fnf]; ring

/-- The corner section satisfies the two-sided band with `glo = 1/4 < 3/4 = ghi`. -/
theorem Fnf_chord : CornerStateChord Fnf (1/4) (3/4) := by
  intro y₁ y₂ h₁ h₂ hle
  rw [Fnf_corner, Fnf_corner]
  constructor
  · nlinarith [h₁.1, h₁.2, h₂.1, h₂.2, sub_nonneg.mpr hle]
  · nlinarith [h₁.1, h₁.2, h₂.1, h₂.2, sub_nonneg.mpr hle]

/-- It is **not** affine along the corner: no `γ` makes it `CornerSectionTop`. -/
theorem Fnf_not_cornerSectionTop : ¬ ∃ γ : ℝ, CornerSectionTop Fnf γ := by
  rintro ⟨γ, h⟩
  have h0 := h 0 ⟨le_refl 0, zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one, le_refl 1⟩
  have h2 := h (1/2) ⟨by norm_num, by norm_num⟩
  rw [Fnf_corner] at h0 h1 h2
  norm_num at h0 h1 h2
  linarith

/-- The corner section maps `[0,1]` into itself — derived from the chord alone
(`cornerSection_mapsTo_of_chord`), not assumed. -/
theorem Fnf_mapsTo : ∀ y ∈ Icc (0:ℝ) 1, Fnf y 1 ∈ Icc (0:ℝ) 1 :=
  cornerSection_mapsTo_of_chord (by norm_num) (by norm_num)
    (by rw [Fnf_corner]; norm_num) Fnf_chord

/-! ### The carrier is genuinely two-sided (not slope-pinned) -/

theorem probe_g_lt_K :
    StokeyLucas.bellmanLowerSlopeConstant (1/2) (1/4) 1
      < StokeyLucas.bellmanLipConstant (1/2) (3/4) 1 := by
  simp only [StokeyLucas.bellmanLowerSlopeConstant, StokeyLucas.bellmanLipConstant]
  norm_num

/-! ### A concrete incoming value and its Bellman image -/

/-- `V(y) = (6/5)·y`, inside the two-sided cone `M = 2, K = 8/5, g = 8/7`. -/
noncomputable def Vlin : Val :=
  BoundedContinuousFunction.mkOfCompact ⟨fun y => (6/5) * y.val, by fun_prop⟩

@[simp] theorem Vlin_apply (y : ↥(Sanctions.S : Set ℝ)) : Vlin y = (6/5) * y.val := rfl

theorem Vlin_mem : Vlin ∈ valLipGainBall 2 (8/5) (8/7) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 2)]
    intro y
    have hy : y.val ∈ Icc (0:ℝ) 1 := y.property
    rw [Vlin_apply, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [hy.1, hy.2]; linarith [hy.1, hy.2]]
  · intro y₁ y₂
    rw [Vlin_apply, Vlin_apply, Subtype.dist_eq, Real.dist_eq]
    rcases le_total y₁.val y₂.val with h | h
    · rw [abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 6/5 * y₂.val - 6/5 * y₁.val)]
      linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y₁.val - y₂.val),
        abs_of_nonpos (by linarith : 6/5 * y₂.val - 6/5 * y₁.val ≤ 0)]
      linarith
  · intro y₁ y₂ _ _ hle
    have h : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [Vlin_apply, Vlin_apply, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    linarith

/-- The corner-pinned Bellman image of `Vlin`, built as a BCF directly from the
formula, so that the `himg` hypothesis is `rfl`. -/
noncomputable def Wimg : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => 0 + y.val + (1/2) * Vlin (Sanctions.clipS' (Fnf y.val 1)),
      by
        refine Continuous.add (Continuous.add continuous_const continuous_subtype_val)
          (Continuous.mul continuous_const ?_)
        exact Vlin.continuous.comp
          (Sanctions.clipS'_continuous.comp (by simp only [Fnf_corner]; fun_prop))⟩

theorem Wimg_apply (y : ↥(Sanctions.S : Set ℝ)) :
    Wimg y = 0 + y.val + (1/2) * Vlin (Sanctions.clipS' (Fnf y.val 1)) := rfl

/-- **End-to-end non-vacuity certificate.** At a genuinely non-affine corner
section, the Bellman image of a two-sided-cone member is again in the cone. -/
theorem Wimg_mem : Wimg ∈ valLipGainBall 2 (8/5) (8/7) 0 := by
  refine mem_valLipGainBall_bellman_chord
    (β := 1/2) (glo := 1/4) (ghi := 3/4) (c₀ := 0)
    (L_U := 1) (g_U := 1) (M_U := 1) (M := 2) (K := 8/5) (g := 8/7)
    (stage := fun y => y) (F := Fnf)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_ ?_ Fnf_mapsTo Fnf_chord
    (by simp [StokeyLucas.bellmanNormBound]; norm_num)
    (by simp [StokeyLucas.bellmanLipConstant]; norm_num)
    (by simp [StokeyLucas.bellmanLowerSlopeConstant]; norm_num)
    Vlin_mem Wimg_apply
  · intro y hy; rw [abs_le]; constructor <;> [linarith [hy.1]; linarith [hy.2]]
  · intro y₁ _ y₂ _; simp
  · intro y₁ _ y₂ _ _; simp

end ZZProbe

/-! ## Rule-11 necessity probe: `hF_mem` is load-bearing, not decorative.

Take the escaping corner section `F y 1 = y + 1`, which satisfies the band
exactly (`glo = ghi = 1`) but leaves `[0,1]` — equivalently, it violates the
top-state normalisation `F 1 1 = 1` that `cornerSection_mapsTo_of_chord` uses.
All scalar margins still hold, yet the Bellman image leaves the carrier: the
clip flattens the continuation, destroying the lower slope. -/

namespace Escape

open Sanctions Sanctions.TransitionChords Sanctions.AbstractGame.Params

noncomputable def Fesc : ℝ → ℝ → ℝ := fun x s => x + s

theorem Fesc_chord : CornerStateChord Fesc 1 1 := by
  intro y₁ y₂ _ _ _; constructor <;> (simp only [Fesc]; ring_nf) <;> linarith

theorem Fesc_escapes : Fesc 1 1 ∉ Icc (0:ℝ) 1 := by
  simp only [Fesc]; norm_num

noncomputable def Vesc : Val :=
  BoundedContinuousFunction.mkOfCompact ⟨fun y => 2 * y.val, by fun_prop⟩

@[simp] theorem Vesc_apply (y : ↥(Sanctions.S : Set ℝ)) : Vesc y = 2 * y.val := rfl

theorem Vesc_mem : Vesc ∈ valLipGainBall 2 2 2 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 2)]
    intro y
    have hy : y.val ∈ Icc (0:ℝ) 1 := y.property
    rw [Vesc_apply, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  · intro y₁ y₂
    rw [Vesc_apply, Vesc_apply, Subtype.dist_eq, Real.dist_eq]
    rcases le_total y₁.val y₂.val with h | h
    · rw [abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * y₂.val - 2 * y₁.val)]; linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y₁.val - y₂.val),
        abs_of_nonpos (by linarith : 2 * y₂.val - 2 * y₁.val ≤ 0)]; linarith
  · intro y₁ y₂ _ _ hle
    have h : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [Vesc_apply, Vesc_apply, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    linarith

noncomputable def Wesc : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => 0 + y.val + (1/2) * Vesc (Sanctions.clipS' (Fesc y.val 1)),
      by
        refine Continuous.add (Continuous.add continuous_const continuous_subtype_val)
          (Continuous.mul continuous_const ?_)
        exact Vesc.continuous.comp
          (Sanctions.clipS'_continuous.comp (by simp only [Fesc]; fun_prop))⟩

theorem Wesc_apply (y : ↥(Sanctions.S : Set ℝ)) :
    Wesc y = 0 + y.val + (1/2) * Vesc (Sanctions.clipS' (Fesc y.val 1)) := rfl

/-- **Counterexample.** Every hypothesis of `mem_valLipGainBall_bellman_chord`
except `hF_mem` holds here, and the conclusion is FALSE. -/
theorem Wesc_not_mem : Wesc ∉ valLipGainBall 2 2 2 0 := by
  intro hW
  have h0 : (0:ℝ) ∈ (Sanctions.S : Set ℝ) := by norm_num
  have h1 : (1:ℝ) ∈ (Sanctions.S : Set ℝ) := by norm_num
  have hslope := hW.2.2 ⟨0, h0⟩ ⟨1, h1⟩ (by norm_num) (by norm_num)
    (Subtype.coe_le_coe.mp (by norm_num))
  rw [Subtype.dist_eq, Real.dist_eq] at hslope
  norm_num [Wesc_apply, Fesc, Sanctions.clipS] at hslope

end Escape

#print axioms ZZProbe.Wimg_mem
#print axioms ZZProbe.Fnf_not_cornerSectionTop
#print axioms Escape.Wesc_not_mem
#print axioms Escape.Fesc_chord
#print axioms ZZProbe.probe_g_lt_K
