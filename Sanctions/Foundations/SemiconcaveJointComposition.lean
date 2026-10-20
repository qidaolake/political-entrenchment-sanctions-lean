/-
Sanctions/Foundations/SemiconcaveJointComposition.lean

**Joint (state–sanction) semiconcavity of a value composed with a two-argument
transition, from chords alone.**

`Foundations/SemiconcaveComposition.lean` bounds the curvature of `s ↦ v (F x s)`
at a *fixed* state — the one-dimensional estimate that controls the curvature
of the Sender's *action objective* in the sanction. A corner-pinned Bellman
image is a different object: with the sanction fixed at the corner it is the
single composition `x ↦ v (F x s̄)` along a fixed-action section, and its
regularity in the inherited state is governed by that section's state chords
(wording corrected 2026-09-11, the reader's C14). An *interior* Bellman image
is a supremum over the sanction, and
`Foundations/SemiconcaveSup.lean` shows that such a supremum inherits
semiconcavity from a **joint** chord bound on the objective in the
state–sanction plane, with the Schur modulus `σ + ρ²/q` — the sufficient route
the proof uses, not a necessary condition for every supremum (wording
corrected 2026-09-15). This file supplies the joint bound for the continuation
term `v ∘ F`.

## What is proved

If `v` is nondecreasing, `K`-Lipschitz and `σV`-semiconcave on `[0,1]`, and the
transition `F` maps `[0,1]²` into `[0,1]` with

* a state chord band `[glo, ghi]` at **every** sanction (`StateChordBandAll`),
* a sanction chord band `[dlo, dhi]` (`SanctionLowerChord`, `SanctionUpperChord`),
* a joint chord semiconcavity `JointSemiconcaveOn F … Mx Mm (−Ms)` — the
  two-variable analogue of `SanctionSemiconcave`, whose action slot is written
  `−Ms` because `JointSemiconcaveOn` charges the action at rate `−q`,

then `(x, s) ↦ v (F x s)` is jointly semiconcave with

```
state modulus   σV·ghi²     + K·Mx
cross modulus   σV·ghi·dhi  + K·Mm
action modulus  −(σV·dhi²   + K·Ms)
```

Each modulus is the sum of the same two channels the one-dimensional lemma has:
the value's own curvature charged at the product of the relevant transition
chords, and the transition's own curvature charged at the value's Lipschitz rate.
Under the affine law every `M` vanishes and the three moduli are `σV` times the
entries of the Gram matrix of `(1−δ, δ)`.

The two chord bands are read only through the absolute bounds they imply,
`|F y₁ s − F y₂ s| ≤ ghi·|y₁ − y₂|` and `|F y s₁ − F y s₂| ≤ dhi·|s₁ − s₂|`; the
lower rates `glo`, `dlo` never reach a conclusion. So the primary statement is
`jointSemiconcave_comp_of_lipschitz`, which assumes those two Lipschitz bounds
and neither lower rate nor `0 ≤ K` (round BG-1, 2026-10-06, item BG1.3);
`jointSemiconcave_comp_of_chords` is its wrapper, with an unchanged statement.

## Where it is used

The interior-Sender family (`Examples/PlacableSenderFamilyF.lean`) feeds this into
`sup_semiconcave_of_joint_unitInterval` to show the Sender Bellman operator
carries a semiconcave carrier into itself when the sanction is interior. The
corner families never needed it: their image is not a supremum.

No derivatives, no functional form: every hypothesis is a chord inequality
(Rule 22), and nothing here mentions `Params` (Rule 19).
-/
import Sanctions.Foundations.SemiconcaveSup
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.SemiconcaveRiccati

noncomputable section
open Set

namespace Sanctions.Semiconcave

open Sanctions.TransitionChords

/-- The state chord band `[glo, ghi]` holds along **every** sanction section, not
only along `s = 1` as `CornerStateChord` requires. -/
def StateChordBandAll (F : ℝ → ℝ → ℝ) (glo ghi : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, StateChordBand (fun y => F y s) glo ghi

/-- **The band's rates are ordered along every section**, hence
`glo ≤ ghi` follows from `StateChordBandAll` (round P, 2026-09-11; the reader's
R2). The chord economy and the quadratic–linear family derive their
`hglo_ghi` (`g_lo ≤ g_hi`) from this lemma. -/
theorem StateChordBandAll.rates_le {F : ℝ → ℝ → ℝ} {glo ghi : ℝ}
    (h : StateChordBandAll F glo ghi) : glo ≤ ghi :=
  (h 0 ⟨le_rfl, zero_le_one⟩).rates_le

/-- **The two lower rates sum to at most one.** With `F 0 0 = 0` and
`F 1 1 = 1`, the state band at sanction `0` gives `glo ≤ F 1 0`, and the lower
sanction chord at state `1` gives `dlo ≤ 1 − F 1 0` (round P, 2026-09-11; the
step of the reader's R7 that clears the loss offset's denominator). -/
theorem lower_rates_add_le_one {F : ℝ → ℝ → ℝ} {glo ghi dlo : ℝ}
    (hband : StateChordBandAll F glo ghi) (hlo : SanctionLowerChord F dlo)
    (h00 : F 0 0 = 0) (h11 : F 1 1 = 1) : glo + dlo ≤ 1 := by
  have h1 := (hband 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ 1
    ⟨zero_le_one, le_rfl⟩ zero_le_one).1
  have h2 := hlo (x := 1) (s₁ := 0) (s₂ := 1) ⟨zero_le_one, le_rfl⟩
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [sub_zero, mul_one] at h1 h2
  rw [h00] at h1
  rw [h11] at h2
  linarith

/-- A nonnegative-band state chord bounds the absolute state increment by the
upper rate. -/
theorem abs_sub_le_of_stateBand {G : ℝ → ℝ} {glo ghi : ℝ} (hglo : 0 ≤ glo)
    (hband : StateChordBand G glo ghi) {y₁ y₂ : ℝ}
    (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
    |G y₁ - G y₂| ≤ ghi * |y₁ - y₂| := by
  rcases le_total y₁ y₂ with h | h
  · obtain ⟨hlo, hhi⟩ := hband y₁ hy₁ y₂ hy₂ h
    have h1 : 0 ≤ glo * (y₂ - y₁) := mul_nonneg hglo (by linarith)
    rw [abs_sub_comm (G y₁), abs_of_nonneg (by linarith), abs_sub_comm y₁,
      abs_of_nonneg (by linarith)]
    exact hhi
  · obtain ⟨hlo, hhi⟩ := hband y₂ hy₂ y₁ hy₁ h
    have h1 : 0 ≤ glo * (y₁ - y₂) := mul_nonneg hglo (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact hhi

/-- A nonnegative-band sanction chord bounds the absolute sanction increment by
the upper rate. -/
theorem abs_sub_le_of_sanctionChords {F : ℝ → ℝ → ℝ} {dlo dhi : ℝ} (hdlo : 0 ≤ dlo)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi) {x s₁ s₂ : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    |F x s₁ - F x s₂| ≤ dhi * |s₁ - s₂| := by
  rcases le_total s₁ s₂ with h | h
  · have hl := hlo hx hs₁ hs₂ h
    have hu := hhi hx hs₁ hs₂ h
    have h1 : 0 ≤ dlo * (s₂ - s₁) := mul_nonneg hdlo (by linarith)
    rw [abs_sub_comm (F x s₁), abs_of_nonneg (by linarith), abs_sub_comm s₁,
      abs_of_nonneg (by linarith)]
    exact hu
  · have hl := hlo hx hs₂ hs₁ h
    have hu := hhi hx hs₂ hs₁ h
    have h1 : 0 ≤ dlo * (s₁ - s₂) := mul_nonneg hdlo (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact hu

/-- **Joint semiconcavity of `v ∘ F` from two Lipschitz bounds** (general in
`F`; round BG-1, 2026-10-06, item BG1.3). If `v` is nondecreasing, `K`-Lipschitz
and `σV`-semiconcave on `[0,1]`, and `F` maps `[0,1]²` into `[0,1]`, is jointly
semiconcave with moduli `(Mx, Mm, −Ms)`, and moves by at most `ghi` per unit of
state along every sanction section and by at most `dhi` per unit of sanction
along every state section (in absolute value), then `(x, s) ↦ v (F x s)` has
the three moduli of the file header.

Against `jointSemiconcave_comp_of_chords` it drops the state band and the
sanction chord pair in favour of the two absolute bounds they imply, together
with the lower rates `glo`, `dlo` and their signs, and `0 ≤ K` (the Lipschitz
bound on `v` gives it). Monotonicity of `v` stays: it covers the branch of the
transition's chord defect that the one-sided joint bound does not control. -/
theorem jointSemiconcave_comp_of_lipschitz
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV K ghi dhi Mx Mm Ms : ℝ}
    (hσV : 0 ≤ σV) (hMx : 0 ≤ Mx) (hMm : 0 ≤ Mm) (hMs : 0 ≤ Ms)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hFx_lip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |F y₁ s - F y₂ s| ≤ ghi * |y₁ - y₂|)
    (hFs_lip : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1,
      |F y s₁ - F y s₂| ≤ dhi * |s₁ - s₂|)
    (hFsc : JointSemiconcaveOn F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) Mx Mm (-Ms)) :
    JointSemiconcaveOn (fun x s => v (F x s)) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
      (σV * ghi ^ 2 + K * Mx) (σV * ghi * dhi + K * Mm)
      (-(σV * dhi ^ 2 + K * Ms)) := by
  have hK : 0 ≤ K := Sanctions.SemiconcaveComposition.nonneg_of_lipschitz_Icc hlip
  intro x₁ hx₁ x₂ hx₂ s₁ hs₁ s₂ hs₂ t ht0 ht1
  show t * v (F x₁ s₁) + (1 - t) * v (F x₂ s₂)
      - v (F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂))
    ≤ t * (1 - t) / 2
        * ((σV * ghi ^ 2 + K * Mx) * (x₁ - x₂) ^ 2
          + 2 * (σV * ghi * dhi + K * Mm) * |x₁ - x₂| * |s₁ - s₂|
          - (-(σV * dhi ^ 2 + K * Ms)) * (s₁ - s₂) ^ 2)
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  have htt : (0 : ℝ) ≤ t * (1 - t) := mul_nonneg ht0 ht1'
  -- The points at which chords are evaluated, all in the state range.
  have hxm : t * x₁ + (1 - t) * x₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hx₁.1, hx₂.1], by nlinarith [hx₁.2, hx₂.2]⟩
  have hsm : t * s₁ + (1 - t) * s₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hs₁.1, hs₂.1], by nlinarith [hs₁.2, hs₂.2]⟩
  have hy₁ : F x₁ s₁ ∈ Icc (0 : ℝ) 1 := hFmaps x₁ hx₁ s₁ hs₁
  have hy₂ : F x₂ s₂ ∈ Icc (0 : ℝ) 1 := hFmaps x₂ hx₂ s₂ hs₂
  have hym : F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂) ∈ Icc (0 : ℝ) 1 :=
    hFmaps _ hxm _ hsm
  have hyavg : t * F x₁ s₁ + (1 - t) * F x₂ s₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hy₁.1, hy₂.1], by nlinarith [hy₁.2, hy₂.2]⟩
  ---------------------------------------------------------------------
  -- Channel A: the value's own chord defect, charged at the squared
  -- image displacement, which the two chord bands bound by
  -- `ghi·|Δx| + dhi·|Δs|`.
  ---------------------------------------------------------------------
  have hA : t * v (F x₁ s₁) + (1 - t) * v (F x₂ s₂)
        - v (t * F x₁ s₁ + (1 - t) * F x₂ s₂)
      ≤ σV / 2 * (t * (1 - t) * (F x₁ s₁ - F x₂ s₂) ^ 2) :=
    hsc _ hy₁ _ hy₂ t ht0 ht1
  have hstate : |F x₁ s₁ - F x₂ s₁| ≤ ghi * |x₁ - x₂| := hFx_lip s₁ hs₁ x₁ hx₁ x₂ hx₂
  have hsanc : |F x₂ s₁ - F x₂ s₂| ≤ dhi * |s₁ - s₂| := hFs_lip x₂ hx₂ s₁ hs₁ s₂ hs₂
  have htri : |F x₁ s₁ - F x₂ s₂| ≤ ghi * |x₁ - x₂| + dhi * |s₁ - s₂| :=
    (abs_sub_le (F x₁ s₁) (F x₂ s₁) (F x₂ s₂)).trans (add_le_add hstate hsanc)
  have hsq : (F x₁ s₁ - F x₂ s₂) ^ 2 ≤ (ghi * |x₁ - x₂| + dhi * |s₁ - s₂|) ^ 2 := by
    rw [← sq_abs (F x₁ s₁ - F x₂ s₂)]
    exact pow_le_pow_left₀ (abs_nonneg _) htri 2
  have hexp : (ghi * |x₁ - x₂| + dhi * |s₁ - s₂|) ^ 2
      = ghi ^ 2 * (x₁ - x₂) ^ 2 + 2 * ghi * dhi * |x₁ - x₂| * |s₁ - s₂|
        + dhi ^ 2 * (s₁ - s₂) ^ 2 := by
    rw [add_sq, mul_pow, mul_pow, sq_abs, sq_abs]; ring
  have hA' : t * v (F x₁ s₁) + (1 - t) * v (F x₂ s₂)
        - v (t * F x₁ s₁ + (1 - t) * F x₂ s₂)
      ≤ σV / 2 * (t * (1 - t)
          * (ghi ^ 2 * (x₁ - x₂) ^ 2 + 2 * ghi * dhi * |x₁ - x₂| * |s₁ - s₂|
              + dhi ^ 2 * (s₁ - s₂) ^ 2)) := by
    rw [← hexp]
    exact hA.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsq htt) (by linarith))
  ---------------------------------------------------------------------
  -- Channel B: the transition's own joint chord defect, transported by
  -- `v`. As in the one-dimensional lemma the bound is one-sided, so
  -- monotonicity covers the branch where Lipschitz has nothing to bound.
  ---------------------------------------------------------------------
  have hFdef : t * F x₁ s₁ + (1 - t) * F x₂ s₂
        - F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂)
      ≤ t * (1 - t) / 2
          * (Mx * (x₁ - x₂) ^ 2 + 2 * Mm * |x₁ - x₂| * |s₁ - s₂|
              - (-Ms) * (s₁ - s₂) ^ 2) :=
    hFsc x₁ hx₁ x₂ hx₂ s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hbudget_nn : 0 ≤ Mx * (x₁ - x₂) ^ 2 + 2 * Mm * |x₁ - x₂| * |s₁ - s₂|
      - (-Ms) * (s₁ - s₂) ^ 2 := by
    have h1 := mul_nonneg hMx (sq_nonneg (x₁ - x₂))
    have h2 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hMm)
      (abs_nonneg (x₁ - x₂))) (abs_nonneg (s₁ - s₂))
    have h3 := mul_nonneg hMs (sq_nonneg (s₁ - s₂))
    nlinarith
  have hD_nn : 0 ≤ t * (1 - t) / 2
      * (Mx * (x₁ - x₂) ^ 2 + 2 * Mm * |x₁ - x₂| * |s₁ - s₂|
          - (-Ms) * (s₁ - s₂) ^ 2) :=
    mul_nonneg (by positivity) hbudget_nn
  have hB : v (t * F x₁ s₁ + (1 - t) * F x₂ s₂)
        - v (F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂))
      ≤ K * (t * (1 - t) / 2
          * (Mx * (x₁ - x₂) ^ 2 + 2 * Mm * |x₁ - x₂| * |s₁ - s₂|
              - (-Ms) * (s₁ - s₂) ^ 2)) := by
    rcases le_total (t * F x₁ s₁ + (1 - t) * F x₂ s₂)
        (F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂)) with h | h
    · have hv := hmono hyavg hym h
      have := mul_nonneg hK hD_nn
      linarith
    · have hl := hlip _ hyavg _ hym
      have habs : |t * F x₁ s₁ + (1 - t) * F x₂ s₂
            - F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂)|
          = t * F x₁ s₁ + (1 - t) * F x₂ s₂
            - F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂) :=
        abs_of_nonneg (by linarith)
      rw [habs] at hl
      calc v (t * F x₁ s₁ + (1 - t) * F x₂ s₂)
            - v (F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂))
          ≤ |v (t * F x₁ s₁ + (1 - t) * F x₂ s₂)
              - v (F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂))| :=
            le_abs_self _
        _ ≤ K * (t * F x₁ s₁ + (1 - t) * F x₂ s₂
              - F (t * x₁ + (1 - t) * x₂) (t * s₁ + (1 - t) * s₂)) := hl
        _ ≤ _ := mul_le_mul_of_nonneg_left hFdef hK
  ---------------------------------------------------------------------
  -- Assemble: the two channels sum to exactly the three stated moduli.
  ---------------------------------------------------------------------
  have hgoal : t * (1 - t) / 2
        * ((σV * ghi ^ 2 + K * Mx) * (x₁ - x₂) ^ 2
          + 2 * (σV * ghi * dhi + K * Mm) * |x₁ - x₂| * |s₁ - s₂|
          - (-(σV * dhi ^ 2 + K * Ms)) * (s₁ - s₂) ^ 2)
      = σV / 2 * (t * (1 - t)
          * (ghi ^ 2 * (x₁ - x₂) ^ 2 + 2 * ghi * dhi * |x₁ - x₂| * |s₁ - s₂|
              + dhi ^ 2 * (s₁ - s₂) ^ 2))
        + K * (t * (1 - t) / 2
          * (Mx * (x₁ - x₂) ^ 2 + 2 * Mm * |x₁ - x₂| * |s₁ - s₂|
              - (-Ms) * (s₁ - s₂) ^ 2)) := by ring
  rw [hgoal]
  linarith [hA', hB]

/-- **Joint semiconcavity of `v ∘ F` from chords** (general in `F`). See the
file header for the three moduli and their reading.

Since BG1.3 (2026-10-06) this is a wrapper of
`jointSemiconcave_comp_of_lipschitz`, with its statement unchanged: the state
band and the sanction chords enter only through the absolute bounds
`abs_sub_le_of_stateBand` and `abs_sub_le_of_sanctionChords`, and `0 ≤ K` (now
`_hK`) is not used. -/
theorem jointSemiconcave_comp_of_chords
    {v : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {σV K glo ghi dlo dhi Mx Mm Ms : ℝ}
    (hσV : 0 ≤ σV) (_hK : 0 ≤ K) (hglo : 0 ≤ glo) (hdlo : 0 ≤ dlo)
    (hMx : 0 ≤ Mx) (hMm : 0 ≤ Mm) (hMs : 0 ≤ Ms)
    (hmono : MonotoneOn v (Icc (0 : ℝ) 1))
    (hlip : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1,
      |v y₁ - v y₂| ≤ K * |y₁ - y₂|)
    (hsc : SemiconcaveOnSet v (Icc (0 : ℝ) 1) σV)
    (hFmaps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F y s ∈ Icc (0 : ℝ) 1)
    (hband : StateChordBandAll F glo ghi)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi)
    (hFsc : JointSemiconcaveOn F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) Mx Mm (-Ms)) :
    JointSemiconcaveOn (fun x s => v (F x s)) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
      (σV * ghi ^ 2 + K * Mx) (σV * ghi * dhi + K * Mm)
      (-(σV * dhi ^ 2 + K * Ms)) :=
  jointSemiconcave_comp_of_lipschitz hσV hMx hMm hMs hmono hlip hsc hFmaps
    (fun s hs _ hy₁ _ hy₂ => abs_sub_le_of_stateBand hglo (hband s hs) hy₁ hy₂)
    (fun _ hy _ hs₁ _ hs₂ => abs_sub_le_of_sanctionChords hdlo hlo hhi hy hs₁ hs₂) hFsc

/-! ## Algebra of joint semiconcavity

The chord defect is linear in the objective, so joint semiconcavity adds and
scales by nonnegative constants, modulus by modulus. These are what a Bellman
integrand — stage payoff plus discounted continuation — needs. -/

theorem JointSemiconcaveOn.add {Φ Ψ : ℝ → ℝ → ℝ} {X A : Set ℝ} {σ₁ ρ₁ q₁ σ₂ ρ₂ q₂ : ℝ}
    (hΦ : JointSemiconcaveOn Φ X A σ₁ ρ₁ q₁) (hΨ : JointSemiconcaveOn Ψ X A σ₂ ρ₂ q₂) :
    JointSemiconcaveOn (fun x a => Φ x a + Ψ x a) X A (σ₁ + σ₂) (ρ₁ + ρ₂) (q₁ + q₂) := by
  intro x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  have h1 := hΦ x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  have h2 := hΨ x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  have : t * (Φ x₁ a₁ + Ψ x₁ a₁) + (1 - t) * (Φ x₂ a₂ + Ψ x₂ a₂)
        - (Φ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂)
          + Ψ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂))
      = (t * Φ x₁ a₁ + (1 - t) * Φ x₂ a₂ - Φ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂))
        + (t * Ψ x₁ a₁ + (1 - t) * Ψ x₂ a₂
          - Ψ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂)) := by ring
  rw [this]
  have hr : t * (1 - t) / 2
        * ((σ₁ + σ₂) * (x₁ - x₂) ^ 2 + 2 * (ρ₁ + ρ₂) * |x₁ - x₂| * |a₁ - a₂|
          - (q₁ + q₂) * (a₁ - a₂) ^ 2)
      = t * (1 - t) / 2
          * (σ₁ * (x₁ - x₂) ^ 2 + 2 * ρ₁ * |x₁ - x₂| * |a₁ - a₂| - q₁ * (a₁ - a₂) ^ 2)
        + t * (1 - t) / 2
          * (σ₂ * (x₁ - x₂) ^ 2 + 2 * ρ₂ * |x₁ - x₂| * |a₁ - a₂| - q₂ * (a₁ - a₂) ^ 2) := by
    ring
  rw [hr]
  exact add_le_add h1 h2

theorem JointSemiconcaveOn.const_mul {Φ : ℝ → ℝ → ℝ} {X A : Set ℝ} {σ ρ q β : ℝ}
    (hβ : 0 ≤ β) (hΦ : JointSemiconcaveOn Φ X A σ ρ q) :
    JointSemiconcaveOn (fun x a => β * Φ x a) X A (β * σ) (β * ρ) (β * q) := by
  intro x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  have h := hΦ x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  have hl : t * (β * Φ x₁ a₁) + (1 - t) * (β * Φ x₂ a₂)
        - β * Φ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂)
      = β * (t * Φ x₁ a₁ + (1 - t) * Φ x₂ a₂
          - Φ (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂)) := by ring
  have hr : t * (1 - t) / 2
        * (β * σ * (x₁ - x₂) ^ 2 + 2 * (β * ρ) * |x₁ - x₂| * |a₁ - a₂|
          - β * q * (a₁ - a₂) ^ 2)
      = β * (t * (1 - t) / 2
          * (σ * (x₁ - x₂) ^ 2 + 2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2)) := by
    ring
  rw [hl, hr]
  exact mul_le_mul_of_nonneg_left h hβ

/-- Rewrite the moduli of a joint semiconcavity bound. -/
theorem JointSemiconcaveOn.congr_moduli {Φ : ℝ → ℝ → ℝ} {X A : Set ℝ} {σ ρ q σ' ρ' q' : ℝ}
    (h : JointSemiconcaveOn Φ X A σ ρ q) (hσ : σ = σ') (hρ : ρ = ρ') (hq : q = q') :
    JointSemiconcaveOn Φ X A σ' ρ' q' := by
  rw [← hσ, ← hρ, ← hq]; exact h

end Sanctions.Semiconcave

end
