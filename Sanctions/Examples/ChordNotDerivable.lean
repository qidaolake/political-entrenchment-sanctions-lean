/-
Sanctions/Examples/ChordNotDerivable.lean

**Why the sanction chords cannot be derived from the transition primitives.**

`Params` constrains the transition through exactly five fields:

  F_mem         F maps the feasible square into [0,1]
  F_continuous  F is jointly continuous
  F_mono_x      F is monotone in the inherited state
  F_mono_s      F is monotone in the sanction
  F_diag        F x x = x

and nothing else. In particular `δ` is **inert**: no field relates it to `F`
(`Postulates/AbstractGame.lean` records this).

The general-`F` certificate route asks the transition for two *quantitative*
facts the five fields do not supply:

  SanctionLowerChord F dlo   dlo * (s₂ - s₁) ≤ F x s₂ - F x s₁      (dlo > 0)
  SanctionUpperChord F d     F x s₂ - F x s₁ ≤ d   * (s₂ - s₁)      (d finite)

This file proves both are **underivable**, so the Rule-3 additions that carry
them are genuinely new content and not a restatement of what `Params` already
says. Each direction fails for its own reason, and the two reasons are
independent:

* the lower chord fails because monotone does not mean *strictly* increasing —
  a transition may be flat in the sanction and still satisfy all five fields;
* the upper chord fails because continuous does not mean *Lipschitz* — a
  transition may have unbounded sanction-sensitivity near a corner.

Both witnesses already existed in the development for other purposes; this file
only records what they settle about derivability.
-/

import Sanctions.Theory.Basin.WeakFloorBasin
import Sanctions.Examples.GeneralFNonLipschitzCounterexample
import Sanctions.Foundations.TransitionChords

namespace Sanctions
namespace Examples

open Set

/-! ## 1. No positive lower chord

`flatTransition x s = x` ignores the sanction entirely. It satisfies every
transition primitive — it is into `[0,1]`, continuous, monotone in both
arguments (constantly so in the sanction), and fixes the diagonal — and it
moves the state by exactly `0` however far the sanction is raised. So the only
lower-chord rate it admits is `dlo ≤ 0`, and the Target leg of the certificate
needs `dlo > 0` for its margin `c_T ≤ β_T · g_T · dlo` to say anything.

Economically: a polity whose entrenchment simply does not respond to sanctions
is consistent with every structural assumption the model makes about `F`. -/

theorem flatTransition_lower_chord_forces_nonpos
    {dlo : ℝ}
    (h : Sanctions.TransitionChords.SanctionLowerChord
          Sanctions.AbstractGame.Params.flatTransition dlo) :
    dlo ≤ 0 := by
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have := h h01 h01 h11 zero_le_one
  simpa [Sanctions.AbstractGame.Params.flatTransition] using this

/-- **The five transition primitives do not yield a positive sanction lower
chord.** There is a transition satisfying all of them at which every admissible
lower-chord rate is nonpositive. -/
theorem no_positive_lower_chord_from_primitives :
    ∃ F : ℝ → ℝ → ℝ,
      (∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
        F x s ∈ Set.Icc (0 : ℝ) 1)
      ∧ Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2)
      ∧ (∀ s, Monotone (fun x => F x s))
      ∧ (∀ x, Monotone (fun s => F x s))
      ∧ (∀ x, F x x = x)
      ∧ ∀ dlo : ℝ,
          Sanctions.TransitionChords.SanctionLowerChord F dlo → dlo ≤ 0 :=
  ⟨Sanctions.AbstractGame.Params.flatTransition,
   Sanctions.AbstractGame.Params.flatTransition_mem,
   Sanctions.AbstractGame.Params.flatTransition_continuous,
   Sanctions.AbstractGame.Params.flatTransition_mono_x,
   Sanctions.AbstractGame.Params.flatTransition_mono_s,
   Sanctions.AbstractGame.Params.flatTransition_diag,
   fun _ h => flatTransition_lower_chord_forces_nonpos h⟩

/-! ## 2. No finite upper chord

The square-root mean transition `((√x + √s)/2)²` satisfies the same five
primitives (`Params.sqrtMeanTransitionParams` builds a full parameter vector on
it) and has unbounded sanction-sensitivity at the top state: near `s = 0` the
map `s ↦ F 1 s` behaves like `√s`, whose slope diverges.

`sqrtMeanTransitionParams_no_finite_action_lipschitz` already proves exactly
this — no finite `L` bounds `|F x s - F x t|` by `L · |s - t|` on the feasible
square — and a `SanctionUpperChord F d` is that bound with `L := d` on the
ordered pairs. The Sender leg's margin `β_S · K_S · d < m_S` therefore has no
`d` to be stated at.

Economically: entrenchment may respond to the first unit of sanction
arbitrarily sharply, which no structural assumption in `Params` rules out. -/

theorem upper_chord_needs_more_than_primitives
    (p : Sanctions.AbstractGame.Params) :
    ¬ ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ (Sanctions.S : Set ℝ), ∀ s ∈ Sanctions.I, ∀ t ∈ Sanctions.I,
        |(Sanctions.clipS'
            ((Sanctions.AbstractGame.Params.sqrtMeanTransitionParams p).F x s)).val
          - (Sanctions.clipS'
              ((Sanctions.AbstractGame.Params.sqrtMeanTransitionParams p).F x t)).val|
          ≤ L * |s - t| :=
  Sanctions.AbstractGame.Params.sqrtMeanTransitionParams_no_finite_action_lipschitz
    (p := p)

/-! ## 3. Strict adjustment is NOT enough — the rate is a separate assumption

A natural reading of "the sanction moves the state" is the project's own
`Params.StrictAdjustment`:

  `s < x → F x s < x`   and   `x < s → x < F x s`

— if the sanction exceeds the inherited state, the state rises next period.
That is a real condition, it is used (Goal 3 consumes it), and it *does* rule
out the flat transition of §1. It is still not enough.

`strictAdjustment_of_sanctionLowerChord` proves the implication runs one way
only: a positive lower chord gives strict adjustment (via `F_diag`), and the
converse fails. Strict adjustment fixes the **sign** of the response; the chord
fixes its **rate**, uniformly. Between them sits every transition whose response
is strictly positive but not bounded below by any fixed multiple of the sanction
increment.

The witness below is one, and it is economically ordinary: **the state moves
toward the sanction, but by at most `1/2` per period** — a speed limit on
political adjustment. It satisfies all five transition primitives, it is
strictly adjusting in both directions, and it still admits no positive lower
chord, because past the cap the response is flat: at `x = 0` the states reached
from `s = 1/2` and from `s = 1` are the same.

So a certificate hypothesis of the form `c_T ≤ β_T · g_T · d_lo` is not a
restatement of "sanctions bite". It is the strictly stronger claim that they
bite at a rate bounded away from zero, uniformly over the square. -/
/-- Clamp to `[-c, c]`. -/
noncomputable def clamp2 (c u : ℝ) : ℝ := max (-c) (min c u)

theorem clamp2_mono {c : ℝ} {u v : ℝ} (h : u ≤ v) : clamp2 c u ≤ clamp2 c v := by
  unfold clamp2
  exact max_le_max le_rfl (min_le_min le_rfl h)

theorem clamp2_lip {c : ℝ} {u v : ℝ} (h : u ≤ v) : clamp2 c v - clamp2 c u ≤ v - u := by
  unfold clamp2
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- **The state moves toward the sanction, but by at most `1/2` per period.** -/
noncomputable def cappedTransition (x s : ℝ) : ℝ := x + clamp2 (1/2) (s - x)

theorem cappedTransition_diag (x : ℝ) : cappedTransition x x = x := by
  unfold cappedTransition clamp2; norm_num

theorem cappedTransition_mem : ∀ x s, x ∈ Icc (0:ℝ) 1 → s ∈ Icc (0:ℝ) 1 →
    cappedTransition x s ∈ Icc (0:ℝ) 1 := by
  rintro x s ⟨hx0, hx1⟩ ⟨hs0, hs1⟩
  unfold cappedTransition clamp2
  constructor
  · have h : -x ≤ max (-(1/2:ℝ)) (min (1/2:ℝ) (s - x)) := by
      rcases le_total x (1/2 : ℝ) with hx | hx
      · refine le_trans ?_ (le_max_right _ _)
        exact le_min (by linarith) (by linarith)
      · exact le_trans (by linarith) (le_max_left _ _)
    linarith
  · have h : max (-(1/2:ℝ)) (min (1/2:ℝ) (s - x)) ≤ 1 - x :=
      max_le (by linarith) (le_trans (min_le_right _ _) (by linarith))
    linarith

theorem cappedTransition_mono_s : ∀ x, Monotone (fun s => cappedTransition x s) := by
  intro x a b hab
  have := clamp2_mono (c := (1/2:ℝ)) (show a - x ≤ b - x by linarith)
  unfold cappedTransition; linarith

theorem cappedTransition_mono_x : ∀ s, Monotone (fun x => cappedTransition x s) := by
  intro s a b hab
  have := clamp2_lip (c := (1/2:ℝ)) (show s - b ≤ s - a by linarith)
  unfold cappedTransition; linarith

theorem cappedTransition_continuous :
    Continuous (fun (xs : ℝ × ℝ) => cappedTransition xs.1 xs.2) := by
  unfold cappedTransition clamp2; fun_prop

/-- **Strictly adjusting**: a sanction above the inherited state raises it. -/
theorem cappedTransition_strictAdjustment_up {x s : ℝ} (hxs : x < s) :
    x < cappedTransition x s := by
  unfold cappedTransition clamp2
  have h1 : (0:ℝ) < min (1/2 : ℝ) (s - x) := lt_min (by norm_num) (by linarith)
  have h2 := le_max_right (-(1/2:ℝ)) (min (1/2 : ℝ) (s - x))
  linarith

/-- …and a sanction below it lowers it. -/
theorem cappedTransition_strictAdjustment_down {x s : ℝ} (hsx : s < x) :
    cappedTransition x s < x := by
  unfold cappedTransition clamp2
  have h1 : min (1/2 : ℝ) (s - x) < 0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h2 : max (-(1/2:ℝ)) (min (1/2 : ℝ) (s - x)) < 0 := max_lt (by norm_num) h1
  linarith

/-- **…and yet no positive lower chord.** Beyond the cap the state stops
responding, so the rate is `0` on `[1/2, 1]` at `x = 0`. -/
theorem cappedTransition_no_positive_lower_chord {dlo : ℝ}
    (h : Sanctions.TransitionChords.SanctionLowerChord cappedTransition dlo) :
    dlo ≤ 0 := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hh : (1/2:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have key := h h0 hh h1 (by norm_num)
  unfold cappedTransition clamp2 at key
  norm_num at key
  linarith

/-- **Strict adjustment does not deliver a positive lower chord.** A transition
satisfying every primitive *and* strictly adjusting in both directions, at which
every admissible lower-chord rate is still nonpositive. -/
theorem strictAdjustment_insufficient_for_lower_chord :
    ∃ F : ℝ → ℝ → ℝ,
      (∀ x s, x ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 → F x s ∈ Set.Icc (0:ℝ) 1)
      ∧ Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2)
      ∧ (∀ s, Monotone (fun x => F x s))
      ∧ (∀ x, Monotone (fun s => F x s))
      ∧ (∀ x, F x x = x)
      ∧ (∀ x s : ℝ, s < x → F x s < x)
      ∧ (∀ x s : ℝ, x < s → x < F x s)
      ∧ ∀ dlo : ℝ,
          Sanctions.TransitionChords.SanctionLowerChord F dlo → dlo ≤ 0 :=
  ⟨cappedTransition, cappedTransition_mem, cappedTransition_continuous,
   cappedTransition_mono_x, cappedTransition_mono_s, cappedTransition_diag,
   fun _ _ h => cappedTransition_strictAdjustment_down h,
   fun _ _ h => cappedTransition_strictAdjustment_up h,
   fun _ h => cappedTransition_no_positive_lower_chord h⟩

/-! ## 4. Nor is STRICT monotonicity enough

The natural next proposal is to forbid "raise the sanction, nothing happens" at
the primitive layer — to strengthen `F_mono_s` from `Monotone` to `StrictMono`.
That would exclude both witnesses above: the flat transition of §1 and the
speed-capped one of §3.

**It still would not deliver the chord.** Strict monotonicity says the response
is never exactly zero; the chord says it is never *close* to zero, uniformly.
Those differ, and the gap between them is not exotic.

The witness below is a cubic response near the diagonal — the state moves toward
the sanction, but the response is flat *to first order* where the two coincide:

  `F x s = x + φ(s − x)`,  `φ(u) = u³/3` on `[−1,1]`, slope 1 outside.

It satisfies all five primitives, is **strictly** monotone in the sanction
everywhere, is strictly adjusting, and still admits no positive lower chord —
because near `s = x` the difference quotient behaves like `(s−x)²`, which no
fixed positive rate bounds below.

(The slope-1 continuation outside `[−1,1]` is not decoration. `F_mono_x`
quantifies over **all reals**, not just the feasible square, and the pure cubic
`x + (s−x)³/3` fails it once `|s − x| > √3`. The continuation keeps the response
slope in `[0,1]` globally, which is exactly what monotonicity in *both*
arguments demands of a transition of the form `x + φ(s − x)`.)

**What this means for the primitive surface.** Upgrading `F_mono_s` to
`StrictMono` would be a genuine strengthening of the model class — it would cost
us the flat and capped transitions as admissible economies — and it would buy
*none* of what the certificate route needs. The rate has to be assumed as a
rate. There is no qualitative strengthening of monotonicity that yields it. -/
/-- Cubic response near the diagonal, slope-1 continuation far from it. -/
noncomputable def softResponse (u : ℝ) : ℝ :=
  (clamp2 1 u) ^ 3 / 3 + (u - clamp2 1 u)

private theorem clamp2_bounds (u : ℝ) : -1 ≤ clamp2 1 u ∧ clamp2 1 u ≤ 1 := by
  unfold clamp2
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- The cubic part never outruns its argument: `φ` is 1-Lipschitz from above. -/
private theorem softResponse_lip {u v : ℝ} (h : u ≤ v) :
    softResponse v - softResponse u ≤ v - u := by
  obtain ⟨hu0, hu1⟩ := clamp2_bounds u
  obtain ⟨hv0, hv1⟩ := clamp2_bounds v
  have hc : clamp2 1 u ≤ clamp2 1 v := clamp2_mono h
  have hq : 0 ≤ 3 - (clamp2 1 v)^2 - (clamp2 1 v)*(clamp2 1 u) - (clamp2 1 u)^2 := by
    nlinarith [sq_nonneg (clamp2 1 v + clamp2 1 u)]
  unfold softResponse
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hq]

private theorem softResponse_strictMono : StrictMono softResponse := by
  intro u v huv
  obtain ⟨hu0, hu1⟩ := clamp2_bounds u
  obtain ⟨hv0, hv1⟩ := clamp2_bounds v
  have hc : clamp2 1 u ≤ clamp2 1 v := clamp2_mono huv.le
  have hlip : clamp2 1 v - clamp2 1 u ≤ v - u := clamp2_lip huv.le
  rcases eq_or_lt_of_le hc with heq | hlt
  · unfold softResponse; rw [heq]; linarith
  · have h3 : (clamp2 1 u) ^ 3 < (clamp2 1 v) ^ 3 := Odd.strictMono_pow (by decide) hlt
    unfold softResponse; linarith

@[simp] private theorem softResponse_zero : softResponse 0 = 0 := by
  unfold softResponse clamp2; norm_num

private theorem softResponse_of_mem {u : ℝ} (h0 : -1 ≤ u) (h1 : u ≤ 1) :
    softResponse u = u ^ 3 / 3 := by
  have hc : clamp2 1 u = u := by
    unfold clamp2; rw [min_eq_right h1, max_eq_right h0]
  unfold softResponse; rw [hc]; ring

/-- **Strictly monotone in the sanction, and still no positive lower chord.** -/
noncomputable def softTransition (x s : ℝ) : ℝ := x + softResponse (s - x)

theorem softTransition_diag (x : ℝ) : softTransition x x = x := by
  unfold softTransition; simp

theorem softTransition_strictMono_s (x : ℝ) :
    StrictMono (fun s => softTransition x s) := fun a b hab => by
  unfold softTransition
  have := softResponse_strictMono (show a - x < b - x by linarith)
  linarith

theorem softTransition_mono_s : ∀ x, Monotone (fun s => softTransition x s) :=
  fun x => (softTransition_strictMono_s x).monotone

theorem softTransition_mono_x : ∀ s, Monotone (fun x => softTransition x s) := by
  intro s a b hab
  unfold softTransition
  have := softResponse_lip (show s - b ≤ s - a by linarith)
  linarith

theorem softTransition_mem : ∀ x s, x ∈ Icc (0:ℝ) 1 → s ∈ Icc (0:ℝ) 1 →
    softTransition x s ∈ Icc (0:ℝ) 1 := by
  rintro x s ⟨hx0, hx1⟩ ⟨hs0, hs1⟩
  have hu0 : (-1:ℝ) ≤ s - x := by linarith
  have hu1 : s - x ≤ 1 := by linarith
  unfold softTransition
  rw [softResponse_of_mem hu0 hu1]
  rcases le_total x s with h | h
  · have hc : (s - x) ^ 3 ≤ s - x := by nlinarith [sq_nonneg (s - x)]
    have hp : (0:ℝ) ≤ (s - x) ^ 3 := pow_nonneg (by linarith) 3
    exact ⟨by linarith, by linarith⟩
  · have hc : s - x ≤ (s - x) ^ 3 := by nlinarith [sq_nonneg (s - x)]
    have hn : (s - x) ^ 3 ≤ 0 := by nlinarith [sq_nonneg (s - x)]
    exact ⟨by linarith, by linarith⟩

theorem softTransition_continuous :
    Continuous (fun (xs : ℝ × ℝ) => softTransition xs.1 xs.2) := by
  unfold softTransition softResponse clamp2; fun_prop

theorem softTransition_strictAdjustment_up {x s : ℝ} (h : x < s) :
    x < softTransition x s := by
  have := softResponse_strictMono (show (0:ℝ) < s - x by linarith)
  rw [softResponse_zero] at this
  unfold softTransition; linarith

/-- …and a sanction below the inherited state lowers it. The witness is
strictly adjusting in **both** directions, not just upward. -/
theorem softTransition_strictAdjustment_down {x s : ℝ} (h : s < x) :
    softTransition x s < x := by
  have := softResponse_strictMono (show s - x < (0:ℝ) by linarith)
  rw [softResponse_zero] at this
  unfold softTransition; linarith

theorem softTransition_no_positive_lower_chord {dlo : ℝ}
    (h : Sanctions.TransitionChords.SanctionLowerChord softTransition dlo) :
    dlo ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  set t : ℝ := min 1 dlo with ht
  have ht0 : 0 < t := lt_min one_pos hpos
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t ≤ dlo := min_le_right _ _
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hti : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le, ht1⟩
  have key := h h0 h0 hti ht0.le
  unfold softTransition at key
  simp only [sub_zero, zero_add, softResponse_zero, add_zero] at key
  rw [softResponse_of_mem (by linarith) ht1] at key
  have hsq : t * t ≤ dlo * t := mul_le_mul_of_nonneg_right htd ht0.le
  have hpos2 : 0 < t * t := mul_pos ht0 ht0
  nlinarith [key, hsq, hpos2, ht0, ht1]

/-- **Strict monotonicity in the sanction does not deliver a positive lower
chord.** A transition satisfying every primitive, *strictly* monotone in the
sanction, and strictly adjusting — at which every admissible lower-chord rate is
still nonpositive. -/
theorem strictMono_insufficient_for_lower_chord :
    ∃ F : ℝ → ℝ → ℝ,
      (∀ x s, x ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 → F x s ∈ Set.Icc (0:ℝ) 1)
      ∧ Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2)
      ∧ (∀ s, Monotone (fun x => F x s))
      ∧ (∀ x, StrictMono (fun s => F x s))
      ∧ (∀ x, F x x = x)
      ∧ (∀ x s : ℝ, s < x → F x s < x)
      ∧ (∀ x s : ℝ, x < s → x < F x s)
      ∧ ∀ dlo : ℝ,
          Sanctions.TransitionChords.SanctionLowerChord F dlo → dlo ≤ 0 :=
  ⟨softTransition, softTransition_mem, softTransition_continuous,
   softTransition_mono_x, softTransition_strictMono_s, softTransition_diag,
   fun _ _ h => softTransition_strictAdjustment_down h,
   fun _ _ h => softTransition_strictAdjustment_up h,
   fun _ h => softTransition_no_positive_lower_chord h⟩

end Examples
end Sanctions

#print axioms Sanctions.Examples.no_positive_lower_chord_from_primitives
#print axioms Sanctions.Examples.upper_chord_needs_more_than_primitives
#print axioms Sanctions.Examples.strictAdjustment_insufficient_for_lower_chord
#print axioms Sanctions.Examples.strictMono_insufficient_for_lower_chord
