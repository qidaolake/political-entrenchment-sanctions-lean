/-
Sanctions/Foundations/SemiconcaveComposition.lean

**The chord-form composition rule: semiconcavity survives an inner
transition, with modulus `Σ·dhi² + K·M`.**

This is the keystone of the two-sided-band carrier. Where the abandoned
slope-pinned route pinned the corner section by an *equality*
(`F y 1 = γ·y + (1 − γ)`), forcing the realised path affine and the
carrier's value exactly affine, the band route keeps the corner section
free and must instead *propagate curvature through the composition*
`s ↦ v (F x s)`. That propagation is what this file supplies.

Everything is stated in **chord form** over a bare `v : ℝ → ℝ` and
`F : ℝ → ℝ → ℝ`. There is no derivative anywhere, hence no smoothness
hypothesis on `F` — which is the whole point: the author requires `F`
general, affine and non-affine alike, and requires it for the *realised*
dynamics. No `Params`, no sanctions content, so Rule 19 puts it in
`Foundations/`.

## The statement, in English

If the value `v` is nondecreasing, `K`-Lipschitz and `Σ`-semiconcave on
`[0,1]`, and the transition section `F x ·` maps `[0,1]` into `[0,1]`,
moves with chords in the band `[dlo, dhi]` with `dlo ≥ 0`, and is itself
`M`-semiconcave in the sanction, then the composite `s ↦ v (F x s)` is
semiconcave on `[0,1]` with modulus

    Σ · dhi² + K · M.

Two channels, priced separately and additively: the value's own upward
bulge, charged at the square of the transition's fastest chord; plus the
transition's own upward bulge, charged at the value's Lipschitz rate.
Both degenerate correctly — an affine `F` has `M = 0` and `dlo = dhi = δ`,
returning the familiar `Σ·δ²`; a linear `v` has `Σ = 0`, returning `K·M`.

## Rule 11 — what the disprove gate found, and what it cost

The rule was first attempted **without** the lower chord, on the
hypothesis list "`v` monotone, Lipschitz, semiconcave; `F` into `[0,1]`,
`SanctionUpperChord dhi`, `SanctionSemiconcave M`". That statement is
**false**, and `composition_without_lower_chord_is_false` below refutes
it in Lean rather than in prose.

The refutation is not delicate. Take `v y = y²/2` (nondecreasing,
`1`-Lipschitz, exactly `1`-semiconcave on `[0,1]`) and the *reflection*
`F x s = 1 − s`. A reflection satisfies `SanctionUpperChord F 0` — every
chord is `≤ 0 ≤ 0·Δs` — and is affine, so `SanctionSemiconcave F 0`. The
claimed modulus is therefore `1·0² + 1·0 = 0`, i.e. the composite would
have to be concave. But the composite is `s ↦ (1−s)²/2`, which is
strictly convex; at `s₁ = 0`, `s₂ = 1`, `t = 1/2` the chord defect is
`1/8` against a budget of `0`.

The diagnosis is exact. The sketch's first step bounds the value's own
defect by `(Σ/2)·t(1−t)·(F s₁ − F s₂)²` and then replaces
`(F s₁ − F s₂)²` by `dhi²·(s₁ − s₂)²`. That replacement **squares** the
chord, so it needs `|F s₁ − F s₂| ≤ dhi·|s₁ − s₂|` — a *two-sided* bound.
`SanctionUpperChord` alone bounds the chord from above only; a section
that falls arbitrarily fast in `s` satisfies it with `dhi = 0` while
having an unbounded squared chord.

The repair is the smallest available one, and it costs the project
nothing new: `SanctionLowerChord F dlo` with `0 ≤ dlo` is already the
standing regularity on the transition in this development — the "engine"
of `Foundations/TransitionChords.lean`, normally carried with `dlo > 0`.
Together with the upper chord it sandwiches the section,
`0 ≤ dlo·Δs ≤ F x s₂ − F x s₁ ≤ dhi·Δs`, which is exactly the two-sided
bound the squaring step needs. Callers already holding `0 < dlo` pass
`hdlo := hdlo_pos.le`.

## The Lipschitz form (round BG-1, 2026-10-06, item BG1.3)

The chords are read only through that two-sided bound, and only on the one
section `F x ·` being composed; `dlo` never reaches the conclusion. So the
primary statement is now `semiconcave_comp_of_lipschitz`, which assumes just
`|F x s₁ − F x s₂| ≤ dhi·|s₁ − s₂|` on that section. It needs no sign on the
section and no lower chord, so it also covers sections that fall in the
sanction (the reflection `1 − s` qualifies, with `dhi = 1`). The refutation
above is not affected: there the reflection carried the one-sided upper chord
at rate `0`, and `|Δ| ≤ 0·|Δs|` is false for it. `0 ≤ K` is not assumed
either, because a `K`-Lipschitz bound on `[0,1]` forces it
(`nonneg_of_lipschitz_Icc`). `semiconcave_comp_of_chords` is now a wrapper,
with an unchanged statement.

## Where monotonicity of `v` is load-bearing

Not in the first channel — there it is idle. It is the *second* channel
that needs it, and it is the one place a sign error would hide.

The second channel is `v(t·F s₁ + (1−t)·F s₂) − v(F(t·s₁ + (1−t)·s₂))`,
the transition's own chord defect transported by the value.
`SanctionSemiconcave` bounds that displacement **on one side only**:
`t·F s₁ + (1−t)·F s₂ − F(t·s₁+(1−t)·s₂) ≤ (M/2)·t(1−t)·(s₁−s₂)²`. In the
other direction the displacement is unbounded — a section may be as
concave in `s` as it likes. So `K·|displacement|` is *not* available, and
a proof reaching for `|·|` here would be bounding a quantity nothing
controls.

Splitting on the sign is what works, and monotonicity covers the branch
Lipschitz cannot:

* if the chord average lies **below** the transported midpoint, `v`
  being nondecreasing makes the difference `≤ 0`, hence below the
  (nonnegative) budget with nothing else needed;
* if it lies **above**, the displacement is nonnegative and *equal* to
  its own absolute value, so the Lipschitz bound applies to the
  one-sided semiconcavity bound directly.

Only the second branch consumes `K`; only the first consumes
monotonicity. Neither branch ever bounds `|displacement|`.

## Non-vacuity

`affine_comp_semiconcave` instantiates the rule at the affine transition,
where `dlo = dhi = δ` and `M = 0`, and `affine_comp_modulus_sharp`
records that the resulting modulus `Σ·δ²` is *attained* at `v y = y²/2` —
so the constant is not a convenient over-estimate. `chord_band_nonempty`
exhibits a genuinely **non-affine** section satisfying the band with
`0 < dlo < dhi`, confirming the hypothesis class is strictly wider than
the affine one it replaces.

## Where the evidence lives

That the lower chord is necessary, that the chord band is not the affine class
in disguise, and that the composition modulus is attained are all established
by construction in `Examples/Counterexamples/SemiconcaveComposition.lean`,
moved there 2026-08-27. The affine law's own discharge of the chord predicates
is in `Examples/AffineInstance/TransitionChords.lean`.
-/

import Sanctions.Foundations.TransitionChords

noncomputable section

open Set

namespace Sanctions.SemiconcaveComposition

open Sanctions.Semiconcave Sanctions.TransitionChords

/-! ## 1. The two-sided chord bound

`SanctionUpperChord` bounds a section's chord from above; on its own it
says nothing about how fast the section may *fall*. Paired with a
**nonnegative** lower chord it becomes a genuine Lipschitz bound on the
section, which is what any step that squares the chord requires. -/

/-- **A nonnegative lower chord upgrades the upper chord to a modulus.**
On the feasible square, a section sandwiched between chords `dlo ≥ 0` and
`dhi` moves by at most `dhi` per unit of sanction, in absolute value. -/
theorem abs_sub_comp_le_of_chords {F : ℝ → ℝ → ℝ} {dlo dhi x s₁ s₂ : ℝ}
    (hdlo : 0 ≤ dlo) (hlo : SanctionLowerChord F dlo)
    (hhi : SanctionUpperChord F dhi)
    (hx : x ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    |F x s₁ - F x s₂| ≤ dhi * |s₁ - s₂| := by
  rcases le_total s₁ s₂ with h | h
  · have h1 := hlo hx hs₁ hs₂ h
    have h2 := hhi hx hs₁ hs₂ h
    have hnn : 0 ≤ dlo * (s₂ - s₁) := mul_nonneg hdlo (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := hlo hx hs₂ hs₁ h
    have h2 := hhi hx hs₂ hs₁ h
    have hnn : 0 ≤ dlo * (s₁ - s₂) := mul_nonneg hdlo (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **The squared form**, which is what the semiconcavity budget is
denominated in. This is the step that fails outright without the lower
chord — see `composition_without_lower_chord_is_false`. -/
theorem sq_sub_comp_le_of_chords {F : ℝ → ℝ → ℝ} {dlo dhi x s₁ s₂ : ℝ}
    (hdlo : 0 ≤ dlo) (hlo : SanctionLowerChord F dlo)
    (hhi : SanctionUpperChord F dhi)
    (hx : x ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    (F x s₁ - F x s₂) ^ 2 ≤ dhi ^ 2 * (s₁ - s₂) ^ 2 := by
  have habs := abs_sub_comp_le_of_chords hdlo hlo hhi hx hs₁ hs₂
  have hnn : 0 ≤ |F x s₁ - F x s₂| := abs_nonneg _
  calc (F x s₁ - F x s₂) ^ 2 = |F x s₁ - F x s₂| ^ 2 := (sq_abs _).symm
    _ ≤ (dhi * |s₁ - s₂|) ^ 2 := by nlinarith
    _ = dhi ^ 2 * (s₁ - s₂) ^ 2 := by rw [mul_pow, sq_abs]

/-- The band is coherent: a nonnegative lower chord never exceeds the
upper chord, so `0 ≤ dlo ≤ dhi` whenever both hold. -/
theorem lower_le_upper_chord {F : ℝ → ℝ → ℝ} {dlo dhi : ℝ}
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi) :
    dlo ≤ dhi := by
  have h1 := hlo (x := 0) (s₁ := 0) (s₂ := 1)
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have h2 := hhi (x := 0) (s₁ := 0) (s₂ := 1)
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  linarith

/-- **A Lipschitz constant on `[0,1]` is nonnegative.** At the endpoints the
bound reads `0 ≤ |v 0 − v 1| ≤ K·|0 − 1| = K`. So `0 ≤ K` never has to be
assumed next to a `K`-Lipschitz bound on `[0,1]` (round BG-1, 2026-10-06). No
transition appears, so the lemma is trivially general in `F`. -/
theorem nonneg_of_lipschitz_Icc {v : ℝ → ℝ} {K : ℝ}
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |v y₁ - v y₂| ≤ K * |y₁ - y₂|) :
    0 ≤ K := by
  have h := hlip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
  rw [zero_sub, abs_neg, abs_one, mul_one] at h
  exact le_trans (abs_nonneg _) h

/-- **Squaring a two-sided Lipschitz bound.** `|a| ≤ d·|b|` gives
`a² ≤ d²·b²`. No sign on `d` is needed, since the bound itself forces
`d·|b| ≥ 0`. This is the squaring step of the composition rule with the
chords taken out (round BG-1, 2026-10-06). -/
theorem sq_le_of_abs_le_mul_abs {a b d : ℝ} (h : |a| ≤ d * |b|) :
    a ^ 2 ≤ d ^ 2 * b ^ 2 := by
  have hnn : 0 ≤ |a| := abs_nonneg _
  calc a ^ 2 = |a| ^ 2 := (sq_abs _).symm
    _ ≤ (d * |b|) ^ 2 := by nlinarith
    _ = d ^ 2 * b ^ 2 := by rw [mul_pow, sq_abs]

/-! ## 2. The composition rule -/

/-- **Section form of the composition rule: `Σ·dhi² + K·M` from a
two-sided Lipschitz bound** (general in `F`; round BG-1, 2026-10-06, item
BG1.3).

Let `v` be nondecreasing, `K`-Lipschitz and `Σ`-semiconcave on `[0,1]`, let
`F` map the unit square into `[0,1]` and be `M`-semiconcave in the sanction,
and let the one section `F x ·` move by at most `dhi` per unit of sanction,
in absolute value. Then `s ↦ v (F x s)` is semiconcave on `[0,1]` with modulus
`Σ·dhi² + K·M`.

This is what the chord form actually uses. The sanction chord band
`[dlo, dhi]` with `dlo ≥ 0`, global over the square, is replaced by the
two-sided bound on the one section, which the band implies
(`abs_sub_comp_le_of_chords`) and which also admits sections that fall in the
sanction. `0 ≤ K` is derived (`nonneg_of_lipschitz_Icc`). Monotonicity of `v`
stays: it covers the branch where the transition's chord defect points the
way `SanctionSemiconcave` does *not* bound (see the file header), and it
cannot be dropped (`bellman_semiconcave_step_needs_monotone`). -/
theorem semiconcave_comp_of_lipschitz
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV K dhi M x : ℝ}
    (hσV : 0 ≤ σV) (hM : 0 ≤ M)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hsec : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1,
      |F x s₁ - F x s₂| ≤ dhi * |s₁ - s₂|)
    (hFsc : SanctionSemiconcave F M) :
    SemiconcaveOnSet (fun s => v (F x s)) (Icc (0 : ℝ) 1)
      (σV * dhi ^ 2 + K * M) := by
  have hK : 0 ≤ K := nonneg_of_lipschitz_Icc hlip
  intro s₁ hs₁ s₂ hs₂ t ht0 ht1
  change t * v (F x s₁) + (1 - t) * v (F x s₂) - v (F x (t * s₁ + (1 - t) * s₂))
      ≤ (σV * dhi ^ 2 + K * M) / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  have htt : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 ht1'
  -- The four points the chords are evaluated at, all in the state range.
  have hy₁ : F x s₁ ∈ Icc (0 : ℝ) 1 := hFmaps x hx s₁ hs₁
  have hy₂ : F x s₂ ∈ Icc (0 : ℝ) 1 := hFmaps x hx s₂ hs₂
  have hsm : t * s₁ + (1 - t) * s₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hs₂.1], by nlinarith [hs₁.2, hs₂.2]⟩
  have hym : F x (t * s₁ + (1 - t) * s₂) ∈ Icc (0 : ℝ) 1 := hFmaps x hx _ hsm
  have hyavg : t * F x s₁ + (1 - t) * F x s₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hy₁.1, hy₂.1], by nlinarith [hy₁.2, hy₂.2]⟩
  ---------------------------------------------------------------------
  -- Channel A: the value's own chord defect, charged at the squared
  -- transition chord.
  ---------------------------------------------------------------------
  have hA : t * v (F x s₁) + (1 - t) * v (F x s₂)
        - v (t * F x s₁ + (1 - t) * F x s₂)
      ≤ σV / 2 * (t * (1 - t) * (F x s₁ - F x s₂) ^ 2) :=
    hsc _ hy₁ _ hy₂ t ht0 ht1
  have hsq : (F x s₁ - F x s₂) ^ 2 ≤ dhi ^ 2 * (s₁ - s₂) ^ 2 :=
    sq_le_of_abs_le_mul_abs (hsec s₁ hs₁ s₂ hs₂)
  have hA' : t * v (F x s₁) + (1 - t) * v (F x s₂)
        - v (t * F x s₁ + (1 - t) * F x s₂)
      ≤ σV / 2 * (t * (1 - t) * (dhi ^ 2 * (s₁ - s₂) ^ 2)) :=
    hA.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsq htt) (by linarith : (0 : ℝ) ≤ σV / 2))
  ---------------------------------------------------------------------
  -- Channel B: the transition's own chord defect, transported by `v`.
  -- `SanctionSemiconcave` bounds the displacement on ONE side only, so
  -- the sign split is mandatory: monotonicity covers the branch where
  -- the Lipschitz bound has nothing to bound.
  ---------------------------------------------------------------------
  have hFdef : t * F x s₁ + (1 - t) * F x s₂ - F x (t * s₁ + (1 - t) * s₂)
      ≤ M / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := hFsc x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hKM : (0 : ℝ) ≤ K * M / 2 := by nlinarith [mul_nonneg hK hM]
  have hbudget : (0 : ℝ) ≤ K * M / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) :=
    mul_nonneg hKM (mul_nonneg htt (sq_nonneg _))
  have hB : v (t * F x s₁ + (1 - t) * F x s₂)
        - v (F x (t * s₁ + (1 - t) * s₂))
      ≤ K * M / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := by
    rcases le_total (t * F x s₁ + (1 - t) * F x s₂)
        (F x (t * s₁ + (1 - t) * s₂)) with h | h
    · -- The chord average sits below the transported midpoint. `v` is
      -- nondecreasing, so the difference is `≤ 0`: no `K` is spent, and
      -- no absolute value of the displacement is ever taken.
      have hv := hmono hyavg hym h
      linarith
    · -- The chord average sits above. Now the displacement is
      -- nonnegative, equal to its own absolute value, and the one-sided
      -- semiconcavity bound is exactly what Lipschitz needs.
      have hl := hlip _ hyavg _ hym
      have habs : |t * F x s₁ + (1 - t) * F x s₂
            - F x (t * s₁ + (1 - t) * s₂)|
          = t * F x s₁ + (1 - t) * F x s₂ - F x (t * s₁ + (1 - t) * s₂) :=
        abs_of_nonneg (by linarith)
      rw [habs] at hl
      calc v (t * F x s₁ + (1 - t) * F x s₂)
            - v (F x (t * s₁ + (1 - t) * s₂))
          ≤ |v (t * F x s₁ + (1 - t) * F x s₂)
              - v (F x (t * s₁ + (1 - t) * s₂))| := le_abs_self _
        _ ≤ K * (t * F x s₁ + (1 - t) * F x s₂
              - F x (t * s₁ + (1 - t) * s₂)) := hl
        _ ≤ K * (M / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)) :=
            mul_le_mul_of_nonneg_left hFdef hK
        _ = K * M / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := by ring
  ---------------------------------------------------------------------
  -- The two channels are additive: the intermediate value cancels.
  ---------------------------------------------------------------------
  have hring : (σV * dhi ^ 2 + K * M) / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
      = σV / 2 * (t * (1 - t) * (dhi ^ 2 * (s₁ - s₂) ^ 2))
        + K * M / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := by ring
  rw [hring]
  linarith

/-- **Chord-form composition: `Σ·dhi² + K·M`** (general in `F`).

Let `v` be nondecreasing, `K`-Lipschitz and `Σ`-semiconcave on `[0,1]`,
and let the section `F x ·` map `[0,1]` into `[0,1]`, carry chords in the
band `[dlo, dhi]` with `dlo ≥ 0`, and be `M`-semiconcave in the sanction.
Then `s ↦ v (F x s)` is semiconcave on `[0,1]` with modulus
`Σ·dhi² + K·M`.

No derivatives, no smoothness on `F`, no functional form: every
hypothesis is a chord inequality, so genuinely non-affine sections
qualify. The two additive terms are the two channels — the value's own
curvature charged at the squared transition chord, and the transition's
own curvature charged at the value's Lipschitz rate.

Since BG1.3 (2026-10-06) this is a wrapper of `semiconcave_comp_of_lipschitz`,
with its statement unchanged so that call sites are untouched: the band is
read only through the two-sided bound it implies on the section at `x`
(`abs_sub_comp_le_of_chords`), and `0 ≤ K` (now `_hK`) is not used, because
the Lipschitz bound gives it. -/
theorem semiconcave_comp_of_chords
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV K dlo dhi M x : ℝ}
    (hσV : 0 ≤ σV) (_hK : 0 ≤ K) (hdlo : 0 ≤ dlo) (hM : 0 ≤ M)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi)
    (hFsc : SanctionSemiconcave F M) :
    SemiconcaveOnSet (fun s => v (F x s)) (Icc (0 : ℝ) 1)
      (σV * dhi ^ 2 + K * M) :=
  semiconcave_comp_of_lipschitz hσV hM hmono hlip hsc hx hFmaps
    (fun _ hs₁ _ hs₂ => abs_sub_comp_le_of_chords hdlo hlo hhi hx hs₁ hs₂) hFsc

end Sanctions.SemiconcaveComposition

end
