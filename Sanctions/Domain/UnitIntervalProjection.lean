/-
Sanctions/Foundations/ClipS.lean

**Clip a real number into `↥S = [0, 1]`.**

Extracted from `Theory/Bilateral/BellmanT.lean` (deleted as part of the
2026-05-23 AbstractGame refactor). `clipS` / `clipS'` are foundational
utilities used throughout the abstract Bellman theory.
-/

import Sanctions.Domain.UnitInterval
import Mathlib.Topology.Order.Compact

namespace Sanctions

open Set Filter Topology

noncomputable section

/-! ## State space setup -/

theorem S_isCompact : IsCompact (S : Set ℝ) := isCompact_Icc

theorem S_nonempty : (S : Set ℝ).Nonempty := ⟨0, by simp [S, I]⟩

instance : CompactSpace ↥(S : Set ℝ) :=
  isCompact_iff_compactSpace.mp S_isCompact

instance : Nonempty ↥(S : Set ℝ) :=
  ⟨⟨0, by simp [S, I]⟩⟩

/-! ## Clipping ℝ into ↥S -/

/-- Clip a real into `S` via projection onto `[0, 1]`. -/
@[simp] def clipS (y : ℝ) : ℝ := max 0 (min 1 y)

theorem clipS_mem (y : ℝ) : clipS y ∈ (S : Set ℝ) := by
  refine ⟨le_max_left _ _, ?_⟩
  refine max_le ?_ (min_le_left _ _); linarith

theorem clipS_continuous : Continuous clipS := by
  unfold clipS; fun_prop

/-- `clipS` is monotone non-decreasing in its real argument. -/
theorem clipS_mono : Monotone clipS := by
  intro y₁ y₂ hle
  unfold clipS
  exact max_le_max (le_refl _) (min_le_min (le_refl _) hle)

/-- The clipped point, packaged as an element of `↥S`. -/
@[simp] def clipS' (y : ℝ) : ↥(S : Set ℝ) := ⟨clipS y, clipS_mem y⟩

theorem clipS'_continuous : Continuous clipS' :=
  clipS_continuous.subtype_mk _

/-- `clipS'` is monotone non-decreasing (subtype order inherited from ℝ). -/
theorem clipS'_mono : Monotone clipS' := by
  intro y₁ y₂ hle
  exact clipS_mono hle

/-- `clipS'` is the identity in value on the physical state interval. -/
theorem clipS'_val_eq_of_mem {y : ℝ} (hy : y ∈ (S : Set ℝ)) :
    (clipS' y).val = y := by
  change clipS y = y
  unfold clipS
  rw [min_eq_right hy.2, max_eq_right hy.1]

/-- `clipS` is 1-Lipschitz: clipping cannot increase distances. -/
theorem clipS_lipschitz_abs (y₁ y₂ : ℝ) :
    |clipS y₁ - clipS y₂| ≤ |y₁ - y₂| := by
  unfold clipS
  -- max 0 (min 1 y₁) vs max 0 (min 1 y₂)
  -- Outer max with fixed first arg 0: |max 0 a - max 0 b| ≤ max |0 - 0| |a - b| = |a - b|
  have h_max := abs_max_sub_max_le_max (0 : ℝ) (min 1 y₁) 0 (min 1 y₂)
  have h_max0 : max |(0 : ℝ) - 0| |min 1 y₁ - min 1 y₂| = |min 1 y₁ - min 1 y₂| := by
    simp
  rw [h_max0] at h_max
  -- Inner min with fixed first arg 1: |min 1 y₁ - min 1 y₂| ≤ max |1 - 1| |y₁ - y₂| = |y₁ - y₂|
  have h_min := abs_min_sub_min_le_max (1 : ℝ) y₁ 1 y₂
  have h_min0 : max |(1 : ℝ) - 1| |y₁ - y₂| = |y₁ - y₂| := by
    simp
  rw [h_min0] at h_min
  exact le_trans h_max h_min

/-- `clipS'` is 1-Lipschitz on the subtype (inheriting distance from ℝ). -/
theorem clipS'_lipschitz_dist (y₁ y₂ : ℝ) :
    dist (clipS' y₁) (clipS' y₂) ≤ |y₁ - y₂| := by
  rw [Subtype.dist_eq, Real.dist_eq]
  exact clipS_lipschitz_abs y₁ y₂

end -- noncomputable section

/-! ## Mathlib's projection

`clipS` was written by hand before it was noticed that Mathlib already has this
map. `Set.projIcc a b h` is the same construction --- literally `max a (min b x)`
at the pinned revision --- so the two agree definitionally, and the identities
below record that rather than leaving it to be rediscovered.

The definition is deliberately **not** re-founded on `Set.projIcc`. `clipS` is
`@[simp]` and is unfolded in 141 files; changing what it reduces to would change
simp-normal forms across the tree for no mathematical gain. What is worth having
is the bridge, which lets a future proof reach Mathlib's `projIcc` API ---
`monotone_projIcc`, `continuous_projIcc`, `projIcc_of_mem`, `IccExtend` and the
rest --- without anything being restated.

Rule 3: both are provable from what is already here, and neither adds a
hypothesis to anything.
-/

/-- `clipS` **is** Mathlib's projection onto `[0,1]`, in value. -/
theorem clipS_eq_coe_projIcc (y : ℝ) :
    clipS y = (Set.projIcc (0 : ℝ) 1 zero_le_one y : ℝ) :=
  (Set.coe_projIcc 0 1 zero_le_one y).symm

/-- And `clipS'` is that projection as a subtype element. -/
theorem clipS'_eq_projIcc (y : ℝ) :
    clipS' y = Set.projIcc (0 : ℝ) 1 zero_le_one y :=
  Subtype.ext (clipS_eq_coe_projIcc y)

end Sanctions
