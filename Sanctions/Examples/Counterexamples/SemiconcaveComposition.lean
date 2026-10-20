/-
Sanctions/Examples/Counterexamples/SemiconcaveComposition.lean

**ROLE: NECESSITY, with the non-vacuity and sharpness witnesses it shares a
test function with.**

`Foundations/SemiconcaveComposition.lean` proves that composing a semiconcave
value with a transition satisfying a two-sided chord band is semiconcave, with
modulus `Sigma * dhi^2 + K * M`. Three questions the statement cannot answer are
answered here by construction, and all three run through the same reference
value `v y = y^2/2`, which is exactly `1`-semiconcave and so makes each bound
bite:

* **Necessity.** Drop the lower chord and the composition rule is false, so the
  hypothesis is load-bearing rather than decorative --- a Rule 11 disprove gate,
  run before the theorem was trusted.
* **Non-vacuity, and not secretly affine.** The affine law is recovered as the
  degenerate `dlo = dhi` member, and a genuinely non-affine transition
  `F x s = s(3 - s)/2` satisfies the band with `dlo < dhi` and makes the rule
  fire. So the hypothesis class is not the affine class in disguise (Rule 22).
* **Sharpness.** The modulus is attained, so `Sigma * dhi^2` cannot be improved.

Rule 9: each is a single existential or a single refutation. None licenses a
claim about how the rule behaves at any other transition.

Relocated 2026-08-27 from `Foundations/SemiconcaveComposition.lean`, whose
general chord bounds and composition rule remain there. Moving these also
removes the last edge by which a `Foundations` file consumed an affine
discharger. Statements are byte-identical and the namespace is unchanged, so
every fully-qualified name is preserved.
-/

import Sanctions.Foundations.SemiconcaveComposition
import Sanctions.Examples.AffineInstance.TransitionChords

noncomputable section

open Set

namespace Sanctions.SemiconcaveComposition

open Sanctions.Semiconcave Sanctions.TransitionChords

/-! ## 3. A reference value, used on both sides of the gate

`v y = y²/2` is the sharp test function: nondecreasing on `[0,1]`,
`1`-Lipschitz there, and *exactly* `1`-semiconcave (its chord defect
attains the budget). It is what makes the refutation below bite, and what
makes the modulus in §5 sharp. -/

/-- `y ↦ y²/2` is nondecreasing on `[0,1]`. -/
theorem sqHalf_monotoneOn : MonotoneOn (fun y : ℝ => y ^ 2 / 2) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  simp only
  nlinarith [ha.1, hb.1]

/-- `y ↦ y²/2` is `1`-Lipschitz on `[0,1]` (its slope there is `y ≤ 1`). -/
theorem sqHalf_lipschitz :
    ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |(fun y : ℝ => y ^ 2 / 2) y₁ - (fun y : ℝ => y ^ 2 / 2) y₂|
        ≤ 1 * |y₁ - y₂| := by
  intro y₁ hy₁ y₂ hy₂
  simp only
  rcases abs_cases (y₁ ^ 2 / 2 - y₂ ^ 2 / 2) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (y₁ - y₂) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
      rw [h1, h2] <;> nlinarith [hy₁.1, hy₁.2, hy₂.1, hy₂.2]

/-- `y ↦ y²/2` is `1`-semiconcave, with the chord defect **attaining**
the budget — this is what pins every constant derived from it. -/
theorem sqHalf_semiconcave :
    SemiconcaveOnSet (fun y : ℝ => y ^ 2 / 2) (Icc (0 : ℝ) 1) 1 := by
  intro y₁ _ y₂ _ t _ _
  change t * (y₁ ^ 2 / 2) + (1 - t) * (y₂ ^ 2 / 2)
      - (t * y₁ + (1 - t) * y₂) ^ 2 / 2
    ≤ (1 : ℝ) / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)
  nlinarith [sq_nonneg (y₁ - y₂)]

/-! ## 4. Rule-11 disprove gate: the lower chord is not decorative

The refutation of the upper-chord-only statement. Kept in the tree so a
later round cannot "simplify" the hypothesis list back to the false one.
See the file header for the diagnosis. -/

/-- **Dropping the lower chord makes the composition rule false.**

The refuting instance is `v y = y²/2` against the reflection
`F x s = 1 − s`. The reflection satisfies `SanctionUpperChord F 0`
vacuously (its chords are negative) and is affine, so
`SanctionSemiconcave F 0`. The claimed modulus is then `0`, i.e.
concavity of `s ↦ (1−s)²/2` — which is strictly convex.

This is why `semiconcave_comp_of_chords` carries `SanctionLowerChord F dlo`
with `0 ≤ dlo`: the squaring step in `sq_sub_comp_le_of_chords` needs a
two-sided chord bound, and an upper chord alone does not bound how fast a
section may *fall* in the sanction. -/
theorem composition_without_lower_chord_is_false :
    ¬ (∀ (v : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (σV K dhi M x : ℝ),
        0 ≤ σV → 0 ≤ K → 0 ≤ dhi → 0 ≤ M →
        MonotoneOn v (Icc (0 : ℝ) 1) →
        (∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
          |v y₁ - v y₂| ≤ K * |y₁ - y₂|) →
        SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV →
        x ∈ Icc (0 : ℝ) 1 →
        (∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1) →
        SanctionUpperChord F dhi →
        SanctionSemiconcave F M →
        SemiconcaveOnSet (fun s => v (F x s)) (Icc (0 : ℝ) 1)
          (σV * dhi ^ 2 + K * M)) := by
  intro H
  have key := H (fun y => y ^ 2 / 2) (fun _ s => 1 - s) 1 1 0 0 0
    zero_le_one zero_le_one le_rfl le_rfl
    sqHalf_monotoneOn sqHalf_lipschitz sqHalf_semiconcave
    ⟨le_rfl, zero_le_one⟩
    (by intro y _ s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    (by intro y s₁ s₂ _ _ _ h; change (1 - s₂) - (1 - s₁) ≤ 0 * (s₂ - s₁); linarith)
    (by
      intro y _ s₁ _ s₂ _ t _ _
      change t * (1 - s₁) + (1 - t) * (1 - s₂) - (1 - (t * s₁ + (1 - t) * s₂))
        ≤ (0 : ℝ) / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
      nlinarith [])
  have bad := key 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ (1/2)
    (by norm_num) (by norm_num)
  norm_num at bad

/-! ## 5. Non-vacuity: the affine reference point, and a strictly wider band -/

/-- **The affine transition is in scope.** At `F x s = (1−δ)·x + δ·s`
with `δ ∈ [0,1]` the band collapses (`dlo = dhi = δ`) and the transition
curvature vanishes (`M = 0`), so the composition modulus is `Σ·δ²`. This
is the case the abandoned corner-equality route handled, recovered as a
one-line corollary — confirming the band route is a strict
generalisation, not a replacement. -/
theorem affine_comp_semiconcave {v : ℝ → ℝ} {σV K δ x : ℝ}
    (hσV : 0 ≤ σV) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    SemiconcaveOnSet (fun s => v ((1 - δ) * x + δ * s)) (Icc (0 : ℝ) 1)
      (σV * δ ^ 2) := by
  have h := semiconcave_comp_of_chords (v := v)
    (F := fun x s => (1 - δ) * x + δ * s)
    (σV := σV) (K := K) (dlo := δ) (dhi := δ) (M := 0) (x := x)
    hσV hK hδ0 le_rfl hmono hlip hsc hx
    (by
      intro y hy s hs
      exact ⟨by nlinarith [hy.1, hs.1], by nlinarith [hy.2, hs.2]⟩)
    (affine_sanctionLowerChord δ) (affine_sanctionUpperChord δ)
    (affine_sanctionSemiconcave δ)
  simpa using h

/-- **The modulus `Σ·dhi²` is attained, not an over-estimate.** At
`v y = y²/2` (exactly `1`-semiconcave) composed with the affine section
of slope `δ`, the composite is `s ↦ ((1−δ)x + δs)²/2`, whose chord defect
*equals* `(δ²/2)·t(1−t)·(s₁−s₂)²`. Recorded so no later round "improves"
the first channel's constant below `Σ·dhi²`. -/
theorem affine_comp_modulus_sharp (δ x t s₁ s₂ : ℝ) :
    t * (((1 - δ) * x + δ * s₁) ^ 2 / 2)
        + (1 - t) * (((1 - δ) * x + δ * s₂) ^ 2 / 2)
        - ((1 - δ) * x + δ * (t * s₁ + (1 - t) * s₂)) ^ 2 / 2
      = (1 * δ ^ 2) / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := by
  ring

/-- **The band is strictly wider than the affine class.** The section
`F x s = s·(3 − s)/2` — a strictly *concave* response of the successor
state to the sanction, i.e. diminishing returns — is genuinely
non-affine, maps the square into `[0,1]`, and carries chords in the band
`[1/2, 3/2]`: a **strictly positive** lower chord strictly below the
upper chord, `0 < dlo < dhi`. Being concave in `s` it is `0`-semiconcave,
so `M = 0`.

This is the point of the whole redesign. Under the abandoned corner
*equality* this section is excluded outright; under the band it is an
ordinary member, and the composition modulus it produces is `Σ·(3/2)²`
rather than the affine `Σ·δ²`. The hypothesis class of
`semiconcave_comp_of_chords` is therefore not the affine class in
disguise. -/
theorem chord_band_nonempty :
    SanctionLowerChord (fun _ s => s * (3 - s) / 2) (1/2)
      ∧ SanctionUpperChord (fun _ s => s * (3 - s) / 2) (3/2)
      ∧ SanctionSemiconcave (fun _ s => s * (3 - s) / 2) 0
      ∧ (∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          (fun (_ : ℝ) (s : ℝ) => s * (3 - s) / 2) y s ∈ Icc (0 : ℝ) 1)
      ∧ (1 : ℝ)/2 < 3/2 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · intro y s₁ s₂ _ hs₁ hs₂ h
    change 1/2 * (s₂ - s₁) ≤ s₂ * (3 - s₂) / 2 - s₁ * (3 - s₁) / 2
    nlinarith [hs₁.2, hs₂.2, sub_nonneg.mpr h]
  · intro y s₁ s₂ _ hs₁ hs₂ h
    change s₂ * (3 - s₂) / 2 - s₁ * (3 - s₁) / 2 ≤ 3/2 * (s₂ - s₁)
    nlinarith [hs₁.1, hs₂.1, sub_nonneg.mpr h]
  · intro y _ s₁ _ s₂ _ t ht0 ht1
    change t * (s₁ * (3 - s₁) / 2) + (1 - t) * (s₂ * (3 - s₂) / 2)
        - (t * s₁ + (1 - t) * s₂) * (3 - (t * s₁ + (1 - t) * s₂)) / 2
      ≤ (0 : ℝ) / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
    nlinarith [sq_nonneg (s₁ - s₂), mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - t)]
  · intro y _ s hs
    exact ⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩

/-- **End-to-end non-vacuity of the composition rule itself.**

The hypothesis bundle of `semiconcave_comp_of_chords` is *jointly*
satisfiable at a genuinely non-affine transition, and the theorem then
fires and delivers a concrete modulus. Composing the reference value
`v y = y²/2` (`Σ = 1`, `K = 1`) with the concave section
`F x s = s·(3 − s)/2` (`dlo = 1/2`, `dhi = 3/2`, `M = 0`) yields

    s ↦ (s·(3 − s)/2)² / 2    semiconcave on [0,1] with modulus 9/4,

i.e. `Σ·dhi² + K·M = 1·(3/2)² + 1·0 = 9/4`. Nothing here is affine and
nothing is assumed: this is the rule discharging on data that the
abandoned corner-equality route could not express at all. -/
theorem nonaffine_comp_semiconcave :
    SemiconcaveOnSet (fun s : ℝ => (s * (3 - s) / 2) ^ 2 / 2) (Icc (0 : ℝ) 1)
      (9/4) := by
  obtain ⟨hlo, hhi, hFsc, hFmaps, -⟩ := chord_band_nonempty
  have h := semiconcave_comp_of_chords (v := fun y : ℝ => y ^ 2 / 2)
    (F := fun _ s => s * (3 - s) / 2)
    (σV := 1) (K := 1) (dlo := 1/2) (dhi := 3/2) (M := 0) (x := 0)
    zero_le_one zero_le_one (by norm_num) le_rfl
    sqHalf_monotoneOn sqHalf_lipschitz sqHalf_semiconcave
    ⟨le_rfl, zero_le_one⟩ hFmaps hlo hhi hFsc
  have hmod : (1 : ℝ) * (3/2) ^ 2 + 1 * 0 = 9/4 := by norm_num
  rw [hmod] at h
  exact h

end Sanctions.SemiconcaveComposition

end
