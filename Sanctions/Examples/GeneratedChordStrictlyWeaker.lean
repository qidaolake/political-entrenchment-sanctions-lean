/-
Sanctions/Examples/GeneratedChordStrictlyWeaker.lean

**The generated-chord condition really is weaker than the all-chord condition.**

`SenderContinuationIncreasingChordsAt` asks the Sender's composite continuation
term to have non-decreasing increments across *every* chord of `[0,1]`. For a
continuous function that is convexity, so it cannot be weakened while the whole
family is kept. `SenderContinuationGeneratedChordAt` keeps only the chords the
decision problem generates, and `senderContinuationGeneratedChord_of_increasingChords`
proves the all-chord form implies it. Until now the converse was open, and the
ladder rung was recorded as "not yet witnessed as strictly weaker" (Rule 9B).

This file closes that. The construction follows from reading the generated
condition properly. Writing `Δ = σ(x,aL) − σ(x,aH)` for the placation gap and
substituting `u = σ(x,aH) + z`, the condition says exactly

    T(u + Δ) − T(u) ≤ T(u' + Δ) − T(u')   for u ≤ u' in [0, 1−Δ],

i.e. the **`Δ`-difference of the continuation term is non-decreasing**. A single
lag — and that lag is the placation gap. So anything whose `Δ`-difference is
*constant* satisfies it, and a `Δ`-periodic function has `Δ`-difference
identically zero while being as far from convex as one likes.

**The economy.** The Sender's ideal sanction falls with compliance,

    U_S x a s = -(s - (3/4 - a/2))^2,

so its genuine stage argmax is `σ x a = clip(3/4 - a/2)` — an optimisation
result, decreasing in compliance, so placation is maintained (Rule 1). At
`aL = 0` and `aH = 1` the two responses are `3/4` and `1/4`, so the gap is
exactly `Δ = 1/2`. The transition adjusts fully, `F x s = s`, which makes the
composite continuation term `β_S · V_S(s)`; a positive discount factor scales
both conditions and changes neither.

The continuation value is the `W`-shape

    φ(s) = ‖ ‖s − 1/2‖ − 1/4 ‖,

which is `1/2`-periodic on `[0,1]`: for `u ∈ [0,1/2]`, `φ(u + 1/2) = |u − 1/4|`
and `φ(u) = |(1/2 − u) − 1/4| = |1/4 − u|`. Its `1/2`-difference therefore
vanishes identically, so the generated condition holds. It is not convex — it
rises, falls, rises, falls — and the all-chord condition fails visibly at
`u = 1/4`, `v = 1/2`, `h = 1/4`, where the increment drops from `1/4` to `−1/4`.

**What this licenses, and what it does not** (Rule 9A). It refutes a universal:
the generated condition does not imply the all-chord condition, so the implication
proved in `TwoSidedForwardLooking.lean` is strict and the weaker rung is a genuine
weakening. It says nothing about which condition holds in any economy of interest,
nothing about whether the weakening is ever *useful* at a calibrated point, and
nothing about magnitudes. Per Rule 9A a witness is an existence certificate and
nothing more.

Rule 3: no new assumption; every field below is discharged from concrete data.
Rule 22: the transition here is affine deliberately — the obstruction is about
the continuation shape, not about the transition, and using the simplest possible
transition is what isolates it.
-/
import Sanctions.Theory.LockIn.TwoSidedForwardLooking
import Sanctions.Examples.SelectorShapeNotPreserved

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame

/-- The `W`-shaped continuation value: `1/2`-periodic on `[0,1]`, and nowhere
near convex. -/
def wShape (s : ℝ) : ℝ := |(|s - 1 / 2| - 1 / 4)|

theorem wShape_continuous : Continuous wShape := by
  unfold wShape; fun_prop

/-- **The period identity.** On the lower half interval, shifting by `1/2` leaves
the value unchanged: both sides reduce to `|u - 1/4|`. -/
theorem wShape_half_period {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    wShape (u + 1 / 2) = wShape u := by
  unfold wShape
  have hL : |u + 1 / 2 - 1 / 2| = u := by
    rw [show u + 1 / 2 - 1 / 2 = u from by ring, abs_of_nonneg h0]
  have hR : |u - 1 / 2| = 1 / 2 - u := by
    rw [abs_of_nonpos (by linarith), neg_sub]
  rw [hL, hR, show (1 : ℝ) / 2 - u - 1 / 4 = -(u - 1 / 4) from by ring, abs_neg]

/-- The Sender's ideal sanction at compliance `a`, falling in `a`. -/
def peakGap (a : ℝ) : ℝ := 3 / 4 - a / 2

/-- **The clamped ideal sanction is the Sender's stage argmax**, reusing the
nearest-feasible-point lemma. -/
theorem clipS_peakGap_isMaxOn (a : ℝ) :
    IsMaxOn (fun s => -(s - peakGap a) ^ 2) (Icc (0 : ℝ) 1)
      (Sanctions.clipS (peakGap a)) := by
  intro s hs
  have := Sanctions.AbstractGame.clipS_sq_le (peakGap a) hs
  simpa using neg_le_neg this

namespace Params

/-- **Full adjustment, with a compliance-decreasing clamped optimal sanction.**

`F x s = s`; the Sender's stage loss is single-peaked at `3/4 - a/2`, so the
stage argmax is the clamp, which falls with compliance. -/
def periodicGapSender (p : Params) : Params :=
  { p with
    -- `Params` only gives `β_S ∈ [0,1)`, which admits `β_S = 0`. At that value
    -- the continuation term vanishes identically and is trivially convex, so the
    -- all-chord condition would hold and there would be nothing to separate.
    -- Pinning a positive value here keeps the conclusion unconditional rather
    -- than carrying `0 < β_S` as a hypothesis (Rule 3: no assumption is added
    -- to a witness that can discharge it from concrete data).
    β_S := 1 / 2
    β_S_mem := by constructor <;> norm_num
    F := fun _ s => s
    F_continuous := continuous_snd
    F_mono_x := fun _ _ _ _ => le_rfl
    F_mono_s := fun _ _ _ h => h
    F_diag := fun _ => rfl
    U_S := fun _ a s => -(s - peakGap a) ^ 2
    U_S_continuous := by unfold peakGap; fun_prop
    σ := fun _ a => Sanctions.clipS (peakGap a)
    σ_mem := fun _ a => Sanctions.clipS_mem (peakGap a)
    σ_isMaxOn_U_S := fun _ a => clipS_peakGap_isMaxOn a }

/-- **`periodicGapSender` has a continuous static Sender selector.** A transformation with
the full-adjustment transition `F x s = s` (the extreme point of the affine family); the
selector, the clamp of `3/4 - a/2`, does not read the transition. The proof is the one
that was the economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the
condition left `Params` for the class `Params.StaticSelectorContinuous`; the
myopic-comparator and static-Sender results can use it at this economy. -/
instance periodicGapSender_staticSelectorContinuous (p : Params) :
    (periodicGapSender p).StaticSelectorContinuous where
  σ_continuous := by
    have h : Continuous (fun xa : ℝ × ℝ => peakGap xa.2) := by
      unfold peakGap; fun_prop
    exact Sanctions.clipS_continuous.comp h

variable {p : Params}

@[simp] theorem periodicGapSender_F (x s : ℝ) :
    p.periodicGapSender.F x s = s := rfl

@[simp] theorem periodicGapSender_sigma (x a : ℝ) :
    p.periodicGapSender.σ x a = Sanctions.clipS (peakGap a) := rfl

/-- The two responses that set the gap: `3/4` at zero compliance. -/
theorem periodicGapSender_sigma_zero (x : ℝ) :
    p.periodicGapSender.σ x 0 = 3 / 4 := by
  change Sanctions.clipS (peakGap 0) = 3 / 4
  have h : peakGap 0 = 3 / 4 := by unfold peakGap; norm_num
  rw [h]; simp only [Sanctions.clipS]; norm_num

/-- And `1/4` at full compliance, so the placation gap is exactly `1/2`. -/
theorem periodicGapSender_sigma_one (x : ℝ) :
    p.periodicGapSender.σ x 1 = 1 / 4 := by
  change Sanctions.clipS (peakGap 1) = 1 / 4
  have h : peakGap 1 = 1 / 4 := by unfold peakGap; norm_num
  rw [h]; simp only [Sanctions.clipS]; norm_num

end Params
end AbstractGame

/-- The `W`-shape packaged as a bounded continuous function on the state
space. -/
noncomputable def wShapeBCF : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => Sanctions.AbstractGame.wShape y.val,
      Sanctions.AbstractGame.wShape_continuous.comp continuous_subtype_val⟩

@[simp] theorem wShapeBCF_apply (y : ↥(Sanctions.S : Set ℝ)) :
    wShapeBCF y = Sanctions.AbstractGame.wShape y.val := rfl

namespace AbstractGame
namespace Params

variable {p : Params}

/-- The composite continuation term is the discount factor times the `W`-shape,
because the transition adjusts fully and feasible sanctions are unclipped. -/
theorem periodicGapSender_continuationTerm {s : ℝ} (hs : s ∈ Sanctions.I) (x : ℝ) :
    p.periodicGapSender.senderContinuationTerm wShapeBCF x s
      = 1 / 2 * wShape s := by
  change (1 : ℝ) / 2 * wShapeBCF (Sanctions.clipS' s) = 1 / 2 * wShape s
  rw [wShapeBCF_apply]
  congr 1
  change wShape (Sanctions.clipS s) = wShape s
  obtain ⟨h0, h1⟩ := hs
  simp only [Sanctions.clipS]
  rw [min_eq_right h1, max_eq_right h0]

/-- **The generated chord condition holds at the two extreme compliance
levels.**

Every point the condition touches has the form `σ(x,1) + z = z + 1/4` or
`σ(x,0) + z = z + 3/4` with `z` in the window `[-1/4, 1/4]`, and the two differ
by exactly the placation gap `1/2`. Periodicity makes both sides of the required
inequality equal, so it holds with equality rather than merely holding. -/
theorem periodicGapSender_generatedChord (x : ℝ) :
    p.periodicGapSender.SenderContinuationGeneratedChordAt wShapeBCF x 0 1 := by
  intro z hz z' hz' _
  have hwin : ∀ w ∈ p.periodicGapSender.responseWindow x 0 1,
      -(1 / 4 : ℝ) ≤ w ∧ w ≤ 1 / 4 := by
    intro w hw
    have hw' : w ∈ Set.Icc (-(p.periodicGapSender.σ x 1))
        (1 - p.periodicGapSender.σ x 0) := hw
    rw [periodicGapSender_sigma_zero, periodicGapSender_sigma_one] at hw'
    exact ⟨by linarith [hw'.1], by linarith [hw'.2]⟩
  -- Both base points, rewritten as numbers.
  have hbase : ∀ w : ℝ,
      p.periodicGapSender.σ x 1 + w = w + 1 / 4
      ∧ p.periodicGapSender.σ x 0 + w = w + 3 / 4 := by
    intro w
    rw [periodicGapSender_sigma_zero, periodicGapSender_sigma_one]
    constructor <;> ring
  -- Each of the four points is feasible, so the continuation term is `β_S · φ`.
  have hmem : ∀ w : ℝ, -(1 / 4 : ℝ) ≤ w → w ≤ 1 / 4 →
      (w + 1 / 4 ∈ Sanctions.I ∧ w + 3 / 4 ∈ Sanctions.I) := by
    intro w h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨hz1, hz2⟩ := hwin z hz
  obtain ⟨hz'1, hz'2⟩ := hwin z' hz'
  obtain ⟨hzL, hzH⟩ := hmem z hz1 hz2
  obtain ⟨hz'L, hz'H⟩ := hmem z' hz'1 hz'2
  rw [(hbase z).1, (hbase z).2, (hbase z').1, (hbase z').2,
    periodicGapSender_continuationTerm hzL,
    periodicGapSender_continuationTerm hz'L,
    periodicGapSender_continuationTerm hzH,
    periodicGapSender_continuationTerm hz'H]
  -- Periodicity: `φ(u + 3/4) = φ((u + 1/4) + 1/2) = φ(u + 1/4)`.
  have hper : ∀ w : ℝ, -(1 / 4 : ℝ) ≤ w → w ≤ 1 / 4 →
      wShape (w + 3 / 4) = wShape (w + 1 / 4) := by
    intro w h1 h2
    have h : w + 3 / 4 = (w + 1 / 4) + 1 / 2 := by ring
    rw [h]
    exact wShape_half_period (by linarith) (by linarith)
  rw [hper z hz1 hz2, hper z' hz'1 hz'2]

/-- **But the all-chord condition fails.**

At base points `1/4` and `1/2` with chord length `1/4`, the increment falls from
`1/4` to `-1/4`: the `W`-shape turns over at `1/2`. Since increasing chords for a
continuous function on an interval is convexity, this is the sense in which the
continuation term is not convex. -/
theorem periodicGapSender_not_increasingChords (x : ℝ) :
    ¬ p.periodicGapSender.SenderContinuationIncreasingChordsAt wShapeBCF x := by
  intro h
  have h14 : (1 / 4 : ℝ) ∈ Sanctions.I := by constructor <;> norm_num
  have h12 : (1 / 2 : ℝ) ∈ Sanctions.I := by constructor <;> norm_num
  have h34 : (3 / 4 : ℝ) ∈ Sanctions.I := by constructor <;> norm_num
  have hle : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have key := h h14 h12
    (by rw [show (1:ℝ)/4 + 1/4 = 1/2 from by norm_num]; exact h12)
    (by rw [show (1:ℝ)/2 + 1/4 = 3/4 from by norm_num]; exact h34)
    hle (by norm_num : (0:ℝ) ≤ 1/4)
  rw [show (1:ℝ)/4 + 1/4 = 1/2 from by norm_num,
    show (1:ℝ)/2 + 1/4 = 3/4 from by norm_num,
    periodicGapSender_continuationTerm h12,
    periodicGapSender_continuationTerm h14,
    periodicGapSender_continuationTerm h34] at key
  -- `φ(1/4) = 0`, `φ(1/2) = 1/4`, `φ(3/4) = 0`.
  have e14 : wShape (1 / 4 : ℝ) = 0 := by
    unfold wShape; rw [show (1:ℝ)/4 - 1/2 = -(1/4) from by norm_num]
    rw [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]; norm_num
  have e12 : wShape (1 / 2 : ℝ) = 1 / 4 := by
    unfold wShape; norm_num
  have e34 : wShape (3 / 4 : ℝ) = 0 := by
    unfold wShape; rw [show (3:ℝ)/4 - 1/2 = 1/4 from by norm_num]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]; norm_num
  rw [e14, e12, e34] at key
  norm_num at key

/-- **So the generated-chord condition is strictly weaker than the all-chord
condition.**

The Rule 9B obligation on `SenderContinuationGeneratedChordAt`, discharged. There
is an economy — with a genuine stage-optimal Sender response that placates, and a
transition in the maintained class — whose composite continuation term satisfies
the restricted condition the ordinal argument consumes while failing the full
chord condition that would have implied it.

Per Rule 9A this licenses exactly one thing: the implication
`senderContinuationGeneratedChord_of_increasingChords` does not reverse. It says
nothing about which condition holds at any economy of interest, and it does not
claim the weaker rung is ever the binding one in practice. -/
theorem generatedChord_strictly_weaker (p₀ : Params) :
    ∃ (q : Params) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x aL aH : ℝ),
      q.SenderContinuationGeneratedChordAt V_S x aL aH
        ∧ ¬ q.SenderContinuationIncreasingChordsAt V_S x :=
  ⟨p₀.periodicGapSender, wShapeBCF, 0, 0, 1,
    periodicGapSender_generatedChord 0,
    periodicGapSender_not_increasingChords 0⟩

end Params
end AbstractGame

end

end Sanctions
