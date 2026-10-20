/-
Sanctions/Examples/WobbleCornerCertWitness.lean

**A transition whose REALIZED dynamics are genuinely non-affine.**

The corner-pinned recursion this project's certified family actually runs
is `x_{t+1} = F(x_t, 1)`: the Sender sits at the sanction corner
`σ_dyn ≡ 1`, so the only slice of the transition that ever executes is the
**corner section** `y ↦ F y 1`. Pinning that section by an equality
(`CornerSectionTop F γ`, i.e. `F y 1 = γ·y + (1 − γ)`) therefore makes the
realized path affine, however non-affine `F` may be elsewhere on the
square. That is exactly the restriction the two-sided **state band**

    glo·(y₂ − y₁) ≤ F y₂ 1 − F y₁ 1 ≤ ghi·(y₂ − y₁)     (y₁ ≤ y₂ in [0,1])

removes, and this file is the existence certificate that the removal is
real: it exhibits a transition satisfying every `Params` obligation whose
corner section is a genuine parabola, carries a **strictly** two-sided band
`glo < ghi`, and is **excluded outright** by the equality route.

## Why the existing non-affine witness does not settle this

`quadBumpF` (`Examples/QuadBumpCertWitnessMS.lean`) is non-affine on the
square, but its bump carries a transience factor `(1 − clipS s)` that
**vanishes at full sanction**, so `quadBumpF x 1 = (x + 1)/2` — its corner
section is affine and its realized path is the affine one. It exercises the
incentive layer, not the realized dynamics.

## The construction

    wobbleF dd κ x s = (1 − dd)·x + dd·s + κ·(clipS s − clipS x)²

— the quadratic bump with the transience factor **deleted**, so it does not
vanish at `s = 1`. The squared clip difference is what keeps `F_diag`
(`F x x = x`) true globally on `ℝ`, which is the binding obligation: it kills
every bump that is not anchored on the diagonal. The clips are inactive on
the feasible square, where `F x s = (1 − dd)·x + dd·s + κ·(s − x)²`.

Two margins, and only two, make the whole bundle work:

    2κ ≤ dd        (the bump never overturns `F_mono_s`)
    2κ ≤ 1 − dd    (the bump never overturns `F_mono_x`)

Given those, feasibility `F : [0,1]² → [0,1]` is free — the map is monotone
in both arguments and the diagonal pins both corners, `F 0 0 = 0`,
`F 1 1 = 1`.

## The rates, and that they are exact

Two exact chord identities (`wobbleF_sanction_chord_eq`,
`wobbleF_corner_chord_eq`) drive everything:

    F x s₂ − F x s₁ = (s₂ − s₁)·(dd + κ·(s₁ + s₂ − 2x))
    F y₂ 1 − F y₁ 1 = (y₂ − y₁)·((1 − dd) − κ·(2 − y₁ − y₂))

so the four rates are read off the ranges of the brackets:

| object | rate | at `(dd, κ) = (1/2, 1/10)` |
|---|---|---|
| corner state band, lower `glo` | `1 − dd − 2κ` | `3/10` |
| corner state band, upper `ghi` | `1 − dd`      | `1/2`  |
| sanction lower chord `dlo`     | `dd − 2κ`     | `3/10` |
| sanction upper chord `dhi`     | `dd + 2κ`     | `7/10` |
| sanction curvature `M`         | `2κ`          | `1/5`  |
| corner-section curvature       | `2κ`          | `1/5`  |

Both bands are **strict** (`glo < ghi`, `dlo < dhi`) whenever `κ > 0`, and
all four rates are proved *exact* — no larger `glo`, no smaller `ghi`, no
larger `dlo`, no smaller `dhi` satisfies the corresponding condition
(`wobbleF_stateChordBand_sharp`, `wobbleF_sanctionChords_sharp`). The two
curvature moduli are attained with equality, so neither is an over-estimate.

## Rule 9 status

This is an **existence certificate** and nothing more (Rule 9A): it shows
the band's hypothesis class contains a transition with a genuinely
non-affine realized recursion. It does not show that such transitions are
generic, typical, or that any particular economy has one. Every constant
was located numerically first with exact `fractions.Fraction` arithmetic and
snapped to rationals before any Lean was written (Rule 9C); the admissible
region is an open interval `0 < κ < 1/4` at `dd = 1/2`, so the witness is
not a knife-edge. No hypothesis is opaque: every discharged predicate is a
chord inequality written directly over `wobbleF`'s own data, so there is no
`Prop`-valued field a supplier could set to `True` (Rule 14).

Rule 3: **no new assumption**. Every predicate discharged here already
exists in the tree (`SanctionLowerChord`, `SanctionUpperChord`,
`SanctionSemiconcave`, `CornerSectionTop` in
`Foundations/TransitionChords.lean`; `StateChordBand`,
`SemiconcaveOnSet` in `Foundations/SemiconcaveRiccati.lean` and
`Foundations/SemiconcaveSup.lean`). Rule 5: every structural fact is proved
parametrically in `(dd, κ)`; the concrete witness is a one-line
specialization.
-/

import Sanctions.Theory.Basin.TransitionChords
import Sanctions.Foundations.SemiconcaveRiccati
import Sanctions.Examples.EECertWitness

namespace Sanctions

namespace Examples

open Set AbstractGame Sanctions.TransitionChords Sanctions.Semiconcave

noncomputable section

/-! ## 1. The transition with a persistent corner bump -/

/-- **The wobble transition.** An affine blend plus a quadratic bump in the
sanction–state gap. Unlike `quadBumpF`, the bump carries **no** transience
factor, so it survives at `s = 1` and bends the realized corner section.

Clip-wrapped so the `Params` monotonicity fields — which quantify over all
of `ℝ` — hold globally; on the feasible square the clips are the identity
and `F(x,s) = (1 − dd)·x + dd·s + κ·(s − x)²`. -/
def wobbleF (dd κ : ℝ) (x s : ℝ) : ℝ :=
  (1 - dd) * x + dd * s + κ * (Sanctions.clipS s - Sanctions.clipS x) ^ 2

/-- The clip is inactive on the feasible interval. -/
private theorem clipS_self {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Sanctions.clipS t = t := by
  unfold Sanctions.clipS
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- **On-square closed form**: both clips are the identity. -/
theorem wobbleF_sq {dd κ x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    wobbleF dd κ x s = (1 - dd) * x + dd * s + κ * (s - x) ^ 2 := by
  unfold wobbleF
  rw [clipS_self hx, clipS_self hs]

/-- **The diagonal is fixed, globally on `ℝ`.** The bump is anchored on the
diagonal by construction — `clipS x − clipS x = 0` for every real `x`,
clipped or not — which is what makes the `F_diag` obligation survive. This
is the constraint that rules out every bump of the shape
`κ·clipS s·clipS x·(1 − clipS x)`. -/
theorem wobbleF_diag (dd κ : ℝ) : ∀ x : ℝ, wobbleF dd κ x x = x := by
  intro x
  unfold wobbleF
  ring

/-- **Rule 11 — the shape was forced, not chosen.** The first candidate one
reaches for when deleting the transience factor is a bump that is a product
of the two clipped arguments, e.g. `κ·(clipS s)·(clipS x)·(1 − clipS x)`.
It does not vanish at `s = 1`, which is what we want, but it is **not
anchored on the diagonal**, and `F_diag` refutes it outright: at `x = 1/2`
the map returns `1/2 + 1/80`, not `1/2`.

This is why the bump must be a function of the *gap* `clipS s − clipS x`
that vanishes to second order there. Recorded as a theorem rather than a
comment so a later round cannot quietly re-try the refuted shape. -/
theorem naive_product_bump_fails_F_diag :
    ¬ (∀ x : ℝ, (1 - (1 : ℝ) / 2) * x + (1 : ℝ) / 2 * x
        + (1 : ℝ) / 10 * Sanctions.clipS x * Sanctions.clipS x
            * (1 - Sanctions.clipS x) = x) := by
  intro h
  have hx := h (1 / 2)
  rw [show Sanctions.clipS ((1 : ℝ) / 2) = 1 / 2 from
    clipS_self ⟨by norm_num, by norm_num⟩] at hx
  norm_num at hx

/-- **The realized corner section**: `y ↦ (1 − dd)·y + dd + κ·(1 − y)²`.
A genuine parabola — this is the map the certified family's realized
recursion `x_{t+1} = F(x_t, 1)` actually iterates. -/
theorem wobbleF_corner (dd κ : ℝ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    wobbleF dd κ y 1 = (1 - dd) * y + dd + κ * (1 - y) ^ 2 := by
  rw [wobbleF_sq hy ⟨zero_le_one, le_refl 1⟩]
  ring

/-! ## 2. The five `Params` obligations -/

/-- **Feasibility.** `F` maps the square into `[0,1]`. Both margins are
consumed: the bump is charged against `(1 − dd)(1 − x)` above the diagonal
and against `dd(1 − s)` below it. -/
theorem wobbleF_mem {dd κ : ℝ} (hκ : 0 ≤ κ) (hs2 : 2 * κ ≤ dd)
    (hx2 : 2 * κ ≤ 1 - dd) :
    ∀ x s : ℝ, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      wobbleF dd κ x s ∈ Icc (0 : ℝ) 1 := by
  intro x s hx hs
  have hdd0 : (0 : ℝ) ≤ dd := by linarith
  have hdd1 : dd ≤ 1 := by linarith
  rw [wobbleF_sq hx hs]
  constructor
  · nlinarith [hx.1, hs.1, mul_nonneg hκ (sq_nonneg (s - x))]
  · rcases le_total x s with h | h
    · -- above the diagonal: `(s − x)² ≤ (s − x) ≤ (1 − x)`, charged to `(1 − dd)(1 − x)`
      have hgap := mul_nonneg (sub_nonneg.mpr h)
        (by linarith [hs.2, hx.1] : (0 : ℝ) ≤ 1 - s + x)
      have hA : (s - x) ^ 2 ≤ 1 - x := by nlinarith [hgap, hs.2]
      have hB : κ * (s - x) ^ 2 ≤ κ * (1 - x) := mul_le_mul_of_nonneg_left hA hκ
      have hC : κ * (1 - x) ≤ (1 - dd) * (1 - x) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith [hx.2])
      have hD : dd * s ≤ dd * 1 := mul_le_mul_of_nonneg_left hs.2 hdd0
      linarith [hB, hC, hD]
    · -- below the diagonal: `(x − s)² ≤ (x − s) ≤ (1 − s)`, charged to `dd(1 − s)`
      have hgap := mul_nonneg (sub_nonneg.mpr h)
        (by linarith [hx.2, hs.1] : (0 : ℝ) ≤ 1 - x + s)
      have hA : (s - x) ^ 2 ≤ 1 - s := by nlinarith [hgap, hx.2]
      have hB : κ * (s - x) ^ 2 ≤ κ * (1 - s) := mul_le_mul_of_nonneg_left hA hκ
      have hC : κ * (1 - s) ≤ dd * (1 - s) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith [hs.2])
      have hD : (1 - dd) * x ≤ (1 - dd) * 1 :=
        mul_le_mul_of_nonneg_left hx.2 (by linarith)
      linarith [hB, hC, hD]

/-- Joint continuity (the clips are continuous). -/
theorem wobbleF_continuous (dd κ : ℝ) :
    Continuous (fun (xs : ℝ × ℝ) => wobbleF dd κ xs.1 xs.2) := by
  unfold wobbleF Sanctions.clipS
  fun_prop

/-- **Power persists**: `F` is non-decreasing in the inherited state,
globally on `ℝ`. The bump's state chord is bounded below by `−2κ`, which the
margin `2κ ≤ 1 − dd` absorbs into the affine term. -/
theorem wobbleF_mono_x {dd κ : ℝ} (hκ : 0 ≤ κ) (hx2 : 2 * κ ≤ 1 - dd) :
    ∀ s : ℝ, Monotone (fun x => wobbleF dd κ x s) := by
  intro s x₁ x₂ hle
  unfold wobbleF
  set c₁ := Sanctions.clipS x₁ with hc₁
  set c₂ := Sanctions.clipS x₂ with hc₂
  set cs := Sanctions.clipS s with hcs
  have hc₁m : c₁ ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem x₁
  have hc₂m : c₂ ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem x₂
  have hcsm : cs ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem s
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ x₂ - x₁ := by
    have h := Sanctions.clipS_lipschitz_abs x₂ x₁
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c₂ - c₁),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x₂ - x₁)] at h
    linarith
  simp only
  -- `(cs − c₂)² − (cs − c₁)² = (c₁ − c₂)·(2cs − c₁ − c₂) ≥ −2·(c₂ − c₁)`
  have hkey : (cs - c₂) ^ 2 - (cs - c₁) ^ 2 = (c₁ - c₂) * (2 * cs - c₁ - c₂) := by
    ring
  have hbr : 2 * cs - c₁ - c₂ ≤ 2 := by linarith [hcsm.2, hc₁m.1, hc₂m.1]
  have hlow : (c₁ - c₂) * 2 ≤ (c₁ - c₂) * (2 * cs - c₁ - c₂) :=
    mul_le_mul_of_nonpos_left hbr (by linarith)
  nlinarith [hlow, hkey, hclip, hκ]

/-- **Sanctions raise the baseline power**: `F` is non-decreasing in the
sanction, globally on `ℝ`. The bump's sanction chord is bounded below by
`−2κ`, which the margin `2κ ≤ dd` absorbs. -/
theorem wobbleF_mono_s {dd κ : ℝ} (hκ : 0 ≤ κ) (hs2 : 2 * κ ≤ dd) :
    ∀ x : ℝ, Monotone (fun s => wobbleF dd κ x s) := by
  intro x s₁ s₂ hle
  unfold wobbleF
  set c₁ := Sanctions.clipS s₁ with hc₁
  set c₂ := Sanctions.clipS s₂ with hc₂
  set cx := Sanctions.clipS x with hcx
  have hc₁m : c₁ ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem s₁
  have hc₂m : c₂ ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem s₂
  have hcxm : cx ∈ Icc (0 : ℝ) 1 := Sanctions.clipS_mem x
  have hcord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hclip : c₂ - c₁ ≤ s₂ - s₁ := by
    have h := Sanctions.clipS_lipschitz_abs s₂ s₁
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c₂ - c₁),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₂ - s₁)] at h
    linarith
  simp only
  -- `(c₂ − cx)² − (c₁ − cx)² = (c₂ − c₁)·(c₁ + c₂ − 2cx) ≥ −2·(c₂ − c₁)`
  have hkey : (c₂ - cx) ^ 2 - (c₁ - cx) ^ 2 = (c₂ - c₁) * (c₁ + c₂ - 2 * cx) := by
    ring
  have hbr : (-2 : ℝ) ≤ c₁ + c₂ - 2 * cx := by
    linarith [hc₁m.1, hc₂m.1, hcxm.2]
  have hlow : (c₂ - c₁) * (-2 : ℝ) ≤ (c₂ - c₁) * (c₁ + c₂ - 2 * cx) :=
    mul_le_mul_of_nonneg_left hbr (by linarith)
  nlinarith [hlow, hkey, hclip, hκ]

/-! ## 3. The two exact chord identities

Everything quantitative below is read off these two lines. Stating them as
*identities* rather than bounds is what makes the rates provably exact
rather than merely sufficient. -/

/-- **Sanction-direction chord, exactly.** The bracket
`dd + κ·(s₁ + s₂ − 2x)` ranges over `[dd − 2κ, dd + 2κ]` on the square. -/
theorem wobbleF_sanction_chord_eq {dd κ x s₁ s₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    wobbleF dd κ x s₂ - wobbleF dd κ x s₁
      = (s₂ - s₁) * (dd + κ * (s₁ + s₂ - 2 * x)) := by
  rw [wobbleF_sq hx hs₁, wobbleF_sq hx hs₂]
  ring

/-- **State-direction chord on the realized corner section, exactly.** The
bracket `(1 − dd) − κ·(2 − y₁ − y₂)` ranges over `[1 − dd − 2κ, 1 − dd]`. -/
theorem wobbleF_corner_chord_eq {dd κ y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc (0 : ℝ) 1)
    (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
    wobbleF dd κ y₂ 1 - wobbleF dd κ y₁ 1
      = (y₂ - y₁) * ((1 - dd) - κ * (2 - y₁ - y₂)) := by
  rw [wobbleF_corner dd κ hy₁, wobbleF_corner dd κ hy₂]
  ring

/-! ## 4. The chord bundle -/

/-- **Sanction lower chord at rate `dd − 2κ`.** Positive whenever
`2κ < dd`, which is what makes the transition strictly adjusting. -/
theorem wobbleF_sanctionLowerChord {dd κ : ℝ} (hκ : 0 ≤ κ) :
    SanctionLowerChord (wobbleF dd κ) (dd - 2 * κ) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  rw [wobbleF_sanction_chord_eq hx hs₁ hs₂]
  have hbr : dd - 2 * κ ≤ dd + κ * (s₁ + s₂ - 2 * x) := by
    nlinarith [hs₁.1, hs₂.1, hx.2, hκ]
  nlinarith [sub_nonneg.mpr hle, hbr]

/-- **Sanction upper chord at rate `dd + 2κ`.** -/
theorem wobbleF_sanctionUpperChord {dd κ : ℝ} (hκ : 0 ≤ κ) :
    SanctionUpperChord (wobbleF dd κ) (dd + 2 * κ) := by
  intro x s₁ s₂ hx hs₁ hs₂ hle
  rw [wobbleF_sanction_chord_eq hx hs₁ hs₂]
  have hbr : dd + κ * (s₁ + s₂ - 2 * x) ≤ dd + 2 * κ := by
    nlinarith [hs₁.2, hs₂.2, hx.1, hκ]
  nlinarith [sub_nonneg.mpr hle, hbr]

/-- **The realized corner section carries a two-sided state band.**

This is the predicate the design brief calls `CornerStateChord F glo ghi`,
written with the strict-implicit binders of the `Foundations` chord
predicates so that it *is* that predicate definitionally once the name
lands. `StateChordBand` (already in the tree) follows immediately below.

Rates: `glo = 1 − dd − 2κ`, `ghi = 1 − dd`. **Strictly** separated whenever
`κ > 0`, so the carrier this band supports is a genuine two-sided cone, not
a slope-pinned line. -/
theorem wobbleF_cornerStateChord {dd κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ ⦃y₁ y₂ : ℝ⦄, y₁ ∈ Icc (0 : ℝ) 1 → y₂ ∈ Icc (0 : ℝ) 1 → y₁ ≤ y₂ →
      (1 - dd - 2 * κ) * (y₂ - y₁) ≤ wobbleF dd κ y₂ 1 - wobbleF dd κ y₁ 1
        ∧ wobbleF dd κ y₂ 1 - wobbleF dd κ y₁ 1 ≤ (1 - dd) * (y₂ - y₁) := by
  intro y₁ y₂ hy₁ hy₂ hle
  rw [wobbleF_corner_chord_eq hy₁ hy₂]
  have hd : (0 : ℝ) ≤ y₂ - y₁ := by linarith
  constructor
  · have hbr : 1 - dd - 2 * κ ≤ (1 - dd) - κ * (2 - y₁ - y₂) := by
      nlinarith [mul_nonneg hκ (by linarith [hy₁.1, hy₂.1] : (0 : ℝ) ≤ y₁ + y₂)]
    nlinarith [hd, hbr]
  · have hbr : (1 - dd) - κ * (2 - y₁ - y₂) ≤ 1 - dd := by
      nlinarith [hy₁.2, hy₂.2, hκ]
    nlinarith [hd, hbr]

/-- The same band in the tree's landed spelling
(`Foundations/SemiconcaveRiccati.lean`), over the one-variable corner
section `y ↦ F y 1`. -/
theorem wobbleF_stateChordBand {dd κ : ℝ} (hκ : 0 ≤ κ) :
    StateChordBand (fun y => wobbleF dd κ y 1) (1 - dd - 2 * κ) (1 - dd) := by
  intro y₁ hy₁ y₂ hy₂ hle
  exact wobbleF_cornerStateChord hκ hy₁ hy₂ hle

/-- **Sanction-direction curvature is exactly `2κ`.** The chord defect meets
the budget with equality — the modulus is attained, not an over-estimate. -/
theorem wobbleF_sanctionSemiconcave (dd κ : ℝ) :
    SanctionSemiconcave (wobbleF dd κ) (2 * κ) := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hmid : t * s₁ + (1 - t) * s₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hs₂.1], by nlinarith [hs₁.2, hs₂.2]⟩
  change t * wobbleF dd κ x s₁ + (1 - t) * wobbleF dd κ x s₂
      - wobbleF dd κ x (t * s₁ + (1 - t) * s₂)
    ≤ 2 * κ / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
  rw [wobbleF_sq hx hs₁, wobbleF_sq hx hs₂, wobbleF_sq hx hmid]
  have hEq : t * ((1 - dd) * x + dd * s₁ + κ * (s₁ - x) ^ 2)
      + (1 - t) * ((1 - dd) * x + dd * s₂ + κ * (s₂ - x) ^ 2)
      - ((1 - dd) * x + dd * (t * s₁ + (1 - t) * s₂)
          + κ * ((t * s₁ + (1 - t) * s₂) - x) ^ 2)
    = 2 * κ / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := by ring
  linarith [hEq]

/-- **The realized corner section's own curvature is exactly `2κ`.** This is
the `M_state` modulus the two-sided carrier's semiconcavity leg is priced
against (`Foundations/SemiconcaveRiccati.lean`). Again attained with
equality. -/
theorem wobbleF_corner_semiconcave (dd κ : ℝ) :
    SemiconcaveOnSet (fun y => wobbleF dd κ y 1) (Icc (0 : ℝ) 1) (2 * κ) := by
  intro y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hmid : t * y₁ + (1 - t) * y₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hy₁.1, hy₂.1], by nlinarith [hy₁.2, hy₂.2]⟩
  change t * wobbleF dd κ y₁ 1 + (1 - t) * wobbleF dd κ y₂ 1
      - wobbleF dd κ (t * y₁ + (1 - t) * y₂) 1
    ≤ 2 * κ / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)
  rw [wobbleF_corner dd κ hy₁, wobbleF_corner dd κ hy₂, wobbleF_corner dd κ hmid]
  have hEq : t * ((1 - dd) * y₁ + dd + κ * (1 - y₁) ^ 2)
      + (1 - t) * ((1 - dd) * y₂ + dd + κ * (1 - y₂) ^ 2)
      - ((1 - dd) * (t * y₁ + (1 - t) * y₂) + dd
          + κ * (1 - (t * y₁ + (1 - t) * y₂)) ^ 2)
    = 2 * κ / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2) := by ring
  linarith [hEq]

/-! ## 5. The corner section is genuinely non-affine

This is the whole point: the abandoned equality route
(`CornerSectionTop F γ`) *excludes* this transition, while the band admits
it. So the generalisation from equality to band is not cosmetic. -/

/-- **No affine map agrees with the realized corner section on `[0,1]`.**
The obstruction is exhibited at the midpoint: the section sits `κ/4` below
its own endpoint chord. -/
theorem wobbleF_corner_not_affine {dd κ : ℝ} (hκ : 0 < κ) :
    ¬ ∃ a b : ℝ, ∀ y ∈ Icc (0 : ℝ) 1, wobbleF dd κ y 1 = a * y + b := by
  rintro ⟨a, b, h⟩
  have h0 := h 0 ⟨le_refl 0, zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one, le_refl 1⟩
  have hh := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [wobbleF_corner dd κ ⟨le_refl 0, zero_le_one⟩] at h0
  rw [wobbleF_corner dd κ ⟨zero_le_one, le_refl 1⟩] at h1
  rw [wobbleF_corner dd κ ⟨by norm_num, by norm_num⟩] at hh
  norm_num at h0 h1 hh
  linarith

/-- **The equality route excludes this transition.** No `γ` makes the
corner section the normalised affine map — so a certified family pinned by
`CornerSectionTop` cannot contain this economy, while the two-sided band
contains it with `glo = 1 − dd − 2κ < 1 − dd = ghi`. -/
theorem wobbleF_not_cornerSectionTop {dd κ : ℝ} (hκ : 0 < κ) :
    ¬ ∃ γ : ℝ, CornerSectionTop (wobbleF dd κ) γ := by
  rintro ⟨γ, hγ⟩
  exact wobbleF_corner_not_affine hκ ⟨γ, 1 - γ, fun y hy => hγ y hy⟩

/-- The transition is not the affine law either, for any weight. -/
theorem wobbleF_ne_affineF {dd κ : ℝ} (hκ : 0 < κ) (δ : ℝ) :
    wobbleF dd κ ≠ AbstractGame.affineF δ := by
  intro h
  refine wobbleF_not_cornerSectionTop (dd := dd) (κ := κ) hκ ⟨1 - δ, ?_⟩
  intro y _
  rw [h]
  unfold AbstractGame.affineF
  ring

/-! ## 6. The rates are exact

Not merely sufficient: no larger `glo`, no smaller `ghi`, no larger `dlo`
and no smaller `dhi` works. Each argument evaluates the exact chord
identity on a shrinking pair at the relevant endpoint. -/

/-- A shrinking-`ε` closure: if `a ≤ b + κ·ε` for every small positive `ε`,
then `a ≤ b`. -/
private theorem le_of_forall_small {a b κ : ℝ} (hκ : 0 < κ)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → a ≤ b + κ * ε) : a ≤ b := by
  by_contra hlt
  rw [not_le] at hlt
  have hab : 0 < a - b := by linarith
  set ε := min 1 ((a - b) / (2 * κ)) with hε
  have hεpos : 0 < ε := lt_min zero_lt_one (div_pos hab (by linarith))
  have hεle : ε ≤ 1 := min_le_left _ _
  have hεq : ε ≤ (a - b) / (2 * κ) := min_le_right _ _
  have hmul : κ * ε ≤ (a - b) / 2 := by
    have h2 : κ * ε ≤ κ * ((a - b) / (2 * κ)) :=
      mul_le_mul_of_nonneg_left hεq hκ.le
    have h3 : κ * ((a - b) / (2 * κ)) = (a - b) / 2 := by
      field_simp
    rw [h3] at h2
    exact h2
  have hfin := h ε hεpos hεle
  linarith

/-- **The corner state band's rates cannot be improved.** Any band on the
realized corner section has `glo ≤ 1 − dd − 2κ` and `ghi ≥ 1 − dd`. In
particular the strict separation `glo < ghi` is forced by the transition, not
an artifact of a slack estimate. -/
theorem wobbleF_stateChordBand_sharp {dd κ glo ghi : ℝ} (hκ : 0 < κ)
    (h : StateChordBand (fun y => wobbleF dd κ y 1) glo ghi) :
    glo ≤ 1 - dd - 2 * κ ∧ 1 - dd ≤ ghi := by
  constructor
  · refine le_of_forall_small hκ (fun ε hε0 hε1 => ?_)
    have hεm : ε ∈ Icc (0 : ℝ) 1 := ⟨hε0.le, hε1⟩
    have hlo := (h 0 ⟨le_refl 0, zero_le_one⟩ ε hεm hε0.le).1
    rw [wobbleF_corner_chord_eq ⟨le_refl 0, zero_le_one⟩ hεm] at hlo
    have hstep : glo * ε ≤ (1 - dd - 2 * κ + κ * ε) * ε := by nlinarith [hlo]
    exact le_of_mul_le_mul_right (by linarith [hstep]) hε0
  · refine le_of_forall_small hκ (fun ε hε0 hε1 => ?_)
    have hεm : 1 - ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hhi := (h (1 - ε) hεm 1 ⟨zero_le_one, le_refl 1⟩ (by linarith)).2
    rw [wobbleF_corner_chord_eq hεm ⟨zero_le_one, le_refl 1⟩] at hhi
    have hstep : (1 - dd - κ * ε) * ε ≤ ghi * ε := by nlinarith [hhi]
    exact le_of_mul_le_mul_right (by linarith [hstep]) hε0

/-- **The sanction chord rates cannot be improved either.** Any lower chord
rate is `≤ dd − 2κ`; any upper chord rate is `≥ dd + 2κ`. -/
theorem wobbleF_sanctionChords_sharp {dd κ dlo dhi : ℝ} (hκ : 0 < κ)
    (hlo : SanctionLowerChord (wobbleF dd κ) dlo)
    (hhi : SanctionUpperChord (wobbleF dd κ) dhi) :
    dlo ≤ dd - 2 * κ ∧ dd + 2 * κ ≤ dhi := by
  constructor
  · refine le_of_forall_small hκ (fun ε hε0 hε1 => ?_)
    have hεm : ε ∈ Icc (0 : ℝ) 1 := ⟨hε0.le, hε1⟩
    have h := hlo (x := 1) (s₁ := 0) (s₂ := ε) ⟨zero_le_one, le_refl 1⟩
      ⟨le_refl 0, zero_le_one⟩ hεm hε0.le
    rw [wobbleF_sanction_chord_eq ⟨zero_le_one, le_refl 1⟩
      ⟨le_refl 0, zero_le_one⟩ hεm] at h
    have hstep : dlo * ε ≤ (dd - 2 * κ + κ * ε) * ε := by nlinarith [h]
    exact le_of_mul_le_mul_right (by linarith [hstep]) hε0
  · refine le_of_forall_small hκ (fun ε hε0 hε1 => ?_)
    have hεm : 1 - ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := hhi (x := 0) (s₁ := 1 - ε) (s₂ := 1) ⟨le_refl 0, zero_le_one⟩
      hεm ⟨zero_le_one, le_refl 1⟩ (by linarith)
    rw [wobbleF_sanction_chord_eq ⟨le_refl 0, zero_le_one⟩ hεm
      ⟨zero_le_one, le_refl 1⟩] at h
    have hstep : (dd + 2 * κ - κ * ε) * ε ≤ dhi * ε := by nlinarith [h]
    exact le_of_mul_le_mul_right (by linarith [hstep]) hε0

/-! ## 7. The concrete witness: `dd = 1/2`, `κ = 1/10`

Located by exact-rational sweep before any Lean was written (Rule 9C). The
admissible region at `dd = 1/2` is the open interval `0 < κ < 1/4`; `1/10`
sits in its interior with both margins equal to `3/10`, so nothing here is
knife-edge. -/

/-- The witness transition: `F(x,s) = x/2 + s/2 + (s − x)²/10` on the
square. -/
def wbF : ℝ → ℝ → ℝ := wobbleF (1 / 2) (1 / 10)

/-- **The witness `Params`**: the Eaton-Engers stage economy of
`eeCertParams` with the wobble transition in place of the affine law. All
five transition obligations are discharged from the parametric lemmas. -/
def wobbleParams : AbstractGame.Params :=
  { eeCertParams with
    F := wbF
    F_continuous := wobbleF_continuous _ _
    F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
    F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
    F_diag := wobbleF_diag _ _ }

@[simp] theorem wobbleParams_F : wobbleParams.F = wobbleF (1 / 2) (1 / 10) := rfl
@[simp] theorem wobbleParams_δ : wobbleParams.δ = 1 / 2 := rfl
@[simp] theorem wobbleParams_β_S : wobbleParams.β_S = 1 / 2 := rfl
@[simp] theorem wobbleParams_β_T : wobbleParams.β_T = 9 / 10 := rfl

/-- Closed form on the square. -/
theorem wobbleParams_F_sq {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    wobbleParams.F x s = x / 2 + s / 2 + (s - x) ^ 2 / 10 := by
  rw [wobbleParams_F, wobbleF_sq hx hs]
  ring

/-- **The witness is the incumbent economy perturbed at the same `δ`.** On
the feasible square the transition is the affine law `affineF p.δ` — the very
one `eeCertParams` carries — plus a gap-square bump of size `κ = 1/10`. So
the `δ` field is not stale decoration left over from the affine instance: the
affine part of the wobble transition really does run at weight `δ = 1/2`, and
the only change relative to `eeCertParams` is the added curvature. -/
theorem wobbleParams_eq_affine_add_bump {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    wobbleParams.F x s
      = AbstractGame.affineF wobbleParams.δ x s + (s - x) ^ 2 / 10 := by
  rw [wobbleParams_F, wobbleF_sq hx hs, wobbleParams_δ]
  unfold AbstractGame.affineF
  ring

/-- **The realized recursion**: `x_{t+1} = x_t/2 + 1/2 + (1 − x_t)²/10`.
A parabola, not a line. -/
theorem wobbleParams_realized (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
    wobbleParams.F y 1 = y / 2 + 1 / 2 + (1 - y) ^ 2 / 10 := by
  rw [wobbleParams_F, wobbleF_corner _ _ hy]
  ring

/-- Sanction lower chord `dlo = 3/10 > 0`. -/
theorem wobbleParams_sanctionLowerChord :
    wobbleParams.SanctionLowerChordWith (3 / 10) := by
  have h := wobbleF_sanctionLowerChord (dd := 1 / 2) (κ := 1 / 10) (by norm_num)
  have hr : (1 : ℝ) / 2 - 2 * (1 / 10) = 3 / 10 := by norm_num
  rw [hr] at h
  exact h

/-- Sanction upper chord `dhi = 7/10`. -/
theorem wobbleParams_sanctionUpperChord :
    wobbleParams.SanctionUpperChordWith (7 / 10) := by
  have h := wobbleF_sanctionUpperChord (dd := 1 / 2) (κ := 1 / 10) (by norm_num)
  have hr : (1 : ℝ) / 2 + 2 * (1 / 10) = 7 / 10 := by norm_num
  rw [hr] at h
  exact h

/-- Sanction-direction curvature `M = 1/5`. -/
theorem wobbleParams_sanctionSemiconcave :
    wobbleParams.SanctionSemiconcaveWith (1 / 5) := by
  have h := wobbleF_sanctionSemiconcave (1 / 2) (1 / 10)
  have hr : 2 * ((1 : ℝ) / 10) = 1 / 5 := by norm_num
  rw [hr] at h
  exact h

/-- **The realized corner section's two-sided band**: `glo = 3/10`,
`ghi = 1/2`, strictly separated. -/
theorem wobbleParams_stateChordBand :
    StateChordBand (fun y => wobbleParams.F y 1) (3 / 10) (1 / 2) := by
  have h := wobbleF_stateChordBand (dd := 1 / 2) (κ := 1 / 10) (by norm_num)
  have hlo : (1 : ℝ) - 1 / 2 - 2 * (1 / 10) = 3 / 10 := by norm_num
  have hhi : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hlo, hhi] at h
  exact h

/-- The corner section's own curvature `M_state = 1/5`. -/
theorem wobbleParams_corner_semiconcave :
    SemiconcaveOnSet (fun y => wobbleParams.F y 1) (Icc (0 : ℝ) 1) (1 / 5) := by
  have h := wobbleF_corner_semiconcave (1 / 2) (1 / 10)
  have hr : 2 * ((1 : ℝ) / 10) = 1 / 5 := by norm_num
  rw [hr] at h
  exact h

/-- **The band is strictly two-sided.** `glo = 3/10 < 1/2 = ghi`, so the
carrier it supports has `g < K`: a genuine cone, never slope-pinned. -/
theorem wobbleParams_band_strict : (3 : ℝ) / 10 < 1 / 2 := by norm_num

/-- The sanction band is strictly two-sided too: `dlo = 3/10 < 7/10 = dhi`. -/
theorem wobbleParams_sanction_band_strict : (3 : ℝ) / 10 < 7 / 10 := by norm_num

/-- **The witness is excluded by the equality route.** -/
theorem wobbleParams_not_cornerSectionTop :
    ¬ ∃ γ : ℝ, wobbleParams.CornerSectionTopWith γ :=
  wobbleF_not_cornerSectionTop (by norm_num)

/-- The witness transition is not affine, for any weight. -/
theorem wobbleParams_F_ne_affineF (δ : ℝ) :
    wobbleParams.F ≠ AbstractGame.affineF δ :=
  wobbleF_ne_affineF (by norm_num) δ

/-- **Strict adjustment is derived, not assumed**, from the positive lower
chord via `strictAdjustment_of_sanctionLowerChord`. -/
theorem wobbleParams_strictAdjustment : wobbleParams.StrictAdjustment :=
  wobbleParams.strictAdjustment_of_sanctionLowerChord (by norm_num)
    wobbleParams_sanctionLowerChord

/-- Full sanctions strictly raise every non-maximal state — the general-`F`
route's `hF_top`. -/
theorem wobbleParams_hF_top : ∀ x ∈ Ico (0 : ℝ) 1, x < wobbleParams.F x 1 :=
  wobbleParams.hF_top_of_sanctionLowerChord (by norm_num)
    wobbleParams_sanctionLowerChord

/-! ## 8. The bundle, in one statement -/

/-- **The whole deliverable, bundled.** A single `Params` satisfying every
transition obligation, carrying a **strictly** two-sided state band on the
section its realized dynamics actually iterate, with the sanction chords,
both curvature moduli, strict adjustment and the corner-ascent condition —
and provably outside the reach of the corner-equality route.

Reading the conjuncts in order: the corner section admits no affine
representative; its two-sided band is `[3/10, 1/2]` and is strict; the
sanction chords are `[3/10, 7/10]` and are strict; sanction curvature and
corner curvature are both `1/5`; the transition adjusts strictly toward the
current sanction; and full sanctions strictly raise every non-maximal
state. -/
theorem wobbleParams_generalF_bundle :
    (¬ ∃ γ : ℝ, wobbleParams.CornerSectionTopWith γ)
    ∧ StateChordBand (fun y => wobbleParams.F y 1) (3 / 10) (1 / 2)
    ∧ (3 : ℝ) / 10 < 1 / 2
    ∧ wobbleParams.SanctionLowerChordWith (3 / 10)
    ∧ wobbleParams.SanctionUpperChordWith (7 / 10)
    ∧ (3 : ℝ) / 10 < 7 / 10
    ∧ wobbleParams.SanctionSemiconcaveWith (1 / 5)
    ∧ SemiconcaveOnSet (fun y => wobbleParams.F y 1) (Icc (0 : ℝ) 1) (1 / 5)
    ∧ wobbleParams.StrictAdjustment
    ∧ (∀ x ∈ Ico (0 : ℝ) 1, x < wobbleParams.F x 1) :=
  ⟨wobbleParams_not_cornerSectionTop, wobbleParams_stateChordBand,
    wobbleParams_band_strict, wobbleParams_sanctionLowerChord,
    wobbleParams_sanctionUpperChord, wobbleParams_sanction_band_strict,
    wobbleParams_sanctionSemiconcave, wobbleParams_corner_semiconcave,
    wobbleParams_strictAdjustment, wobbleParams_hF_top⟩

/-- **The rates in the bundle are the exact ones.** Nothing above is slack:
any admissible corner band has `glo ≤ 3/10` and `ghi ≥ 1/2`; any admissible
sanction chord pair has `dlo ≤ 3/10` and `dhi ≥ 7/10`. -/
theorem wobbleParams_rates_exact
    {glo ghi dlo dhi : ℝ}
    (hband : StateChordBand (fun y => wobbleParams.F y 1) glo ghi)
    (hlo : wobbleParams.SanctionLowerChordWith dlo)
    (hhi : wobbleParams.SanctionUpperChordWith dhi) :
    glo ≤ 3 / 10 ∧ (1 : ℝ) / 2 ≤ ghi ∧ dlo ≤ 3 / 10 ∧ (7 : ℝ) / 10 ≤ dhi := by
  obtain ⟨hg, hG⟩ :=
    wobbleF_stateChordBand_sharp (dd := 1 / 2) (κ := 1 / 10) (by norm_num) hband
  obtain ⟨hd, hD⟩ :=
    wobbleF_sanctionChords_sharp (dd := 1 / 2) (κ := 1 / 10) (by norm_num) hlo hhi
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## 9. Non-vacuity spot checks (Rule 9B)

Concrete evaluations, so the reader can see the section is not the affine
one without unfolding a proof. The affine law with the same corner
endpoints would give `3/4` at the midpoint; the wobble section gives
`31/40`, a defect of `1/40 = κ/4`. -/

example : wobbleParams.F 0 1 = 3 / 5 := by
  rw [wobbleParams_realized 0 ⟨le_refl 0, zero_le_one⟩]; norm_num

example : wobbleParams.F 1 1 = 1 := by
  rw [wobbleParams_realized 1 ⟨zero_le_one, le_refl 1⟩]; norm_num

example : wobbleParams.F (1 / 2) 1 = 31 / 40 := by
  rw [wobbleParams_realized (1 / 2) ⟨by norm_num, by norm_num⟩]; norm_num

/-- The midpoint defect against the endpoint chord is `−1/40 = −κ/4`: the
realized section sits strictly **below** its own endpoint chord, which is
the convex side. Sign check for the audit: the corner section
`y ↦ y/2 + 1/2 + (1 − y)²/10` has second derivative `+1/5 = 2κ > 0`, so it
is strictly convex, and a convex function lies below its chords. Its
*semiconcavity* modulus is correspondingly the positive number `2κ = 1/5` —
semiconcavity bounds upward bulge from above, and a convex function spends
that budget in full (`wobbleF_corner_semiconcave` holds with equality). -/
example :
    wobbleParams.F (1 / 2) 1
      - (wobbleParams.F 0 1
          + (1 / 2) * (wobbleParams.F 1 1 - wobbleParams.F 0 1))
    = -(1 / 40) := by
  rw [wobbleParams_realized 0 ⟨le_refl 0, zero_le_one⟩,
    wobbleParams_realized 1 ⟨zero_le_one, le_refl 1⟩,
    wobbleParams_realized (1 / 2) ⟨by norm_num, by norm_num⟩]
  norm_num

end -- noncomputable section

end Examples

end Sanctions
