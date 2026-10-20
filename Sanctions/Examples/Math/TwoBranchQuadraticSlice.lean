/-
Sanctions/Examples/Math/TwoBranchQuadraticSlice.lean

**ROLE: FAILURE OF IMPLICATION.**

A symbolic two-branch quadratic family, introduced for one purpose: to hold
the interval dominance order apart from single crossing, so that neither can
be quietly substituted for the other. Its coefficients stay free, but a family
chosen to separate two conditions is a witness however symbolic it is --- which
is why it belongs here and not in the library it separates.

Rule 9: it refutes one implication. It says nothing about which of the two
conditions holds in any economy in this development.

Relocated 2026-08-27 from `Foundations/TwoBranchQuadraticSlice.lean`.

# Two-branch quadratic slice families: single-peakedness holds, single
# crossing fails

**External / general theory (Rule 19).** Nothing in this file mentions
the Sender-Target game. It is a self-contained separation result about
a family of real-valued objectives indexed by a scalar parameter, of the
form

  `f(s, x) = A(x) − (λ(x)/2)·((p(x) − s)⁺)² − (ρ(x)/2)·((s − p(x))⁺)²`,

a *two-branch quadratic glued C¹ at a state-dependent peak* `p(x)`, with
left curvature `λ(x) > 0`, right curvature `ρ(x) > 0`, and an arbitrary
level term `A(x)` depending on the parameter alone.  Read economically:
`s` is a choice (a sanction realisation), `x` is a parameter (a political
state), each slice is single-peaked at `p(x)`, and the two curvatures say
how fast payoff falls away from that peak on each side.

## What the file separates

The family is designed to pull apart two comparative-statics conditions
that are often conflated:

* **The ordinal condition survives.** Whenever the peak `p` is
  nondecreasing in the parameter and both curvatures are strictly
  positive, the family satisfies
  `Sanctions.IntervalDominanceOrder.MonotoneTransferOn` — on any choice
  interval where the LOWER slice is nondecreasing, the HIGHER slice
  weakly (indeed strictly) rises across the interval endpoints.  This is
  the interval-dominance-order route to a monotone argmax and it needs
  *no* restriction whatsoever on the curvatures beyond positivity
  (`monotoneTransferOn_slice`).

* **The cardinal condition fails.** Milgrom-Shannon single crossing
  compares LEVELS, not just directions, and levels see the curvatures.
  Fix the peak across a parameter pair `x₁ ≤ x₂` and let the *curvature
  ratio* `ρ/λ` strictly increase — the right wing steepens relative to
  the left wing.  Then single crossing is refuted by an explicitly
  constructed pair of choices straddling the peak
  (`not_singleCrossingOn_slice_of_ratio_lt`).

So on this family the interval-dominance route is strictly more
permissive than the single-crossing route, and the gap is a *symbolic*
inequality between existing primitives — `ρ(x₁)/λ(x₁) < ρ(x₂)/λ(x₂)` —
not a hand-picked numeric configuration.

## The refutation, in one line of algebra

At the low parameter `x₁`, put the low choice at
`s' = p̄ − √(ρ(x₁)/λ(x₁))·(s'' − p̄)`, the point on the left branch whose
quadratic loss exactly matches that of the high choice `s'' > p̄` on the
right branch.  Then `f(s', x₁) = f(s'', x₁)`, so the weak single-crossing
premise holds with equality.  At the high parameter `x₂` the same two
choices give

  `f(s'', x₂) − f(s', x₂) = ½·(λ(x₂)·ρ(x₁)/λ(x₁) − ρ(x₂))·(s'' − p̄)²`,

strictly negative exactly when `ρ(x₁)/λ(x₁) < ρ(x₂)/λ(x₂)`.  The high
parameter therefore *reverses* a comparison the low parameter accepted,
which is precisely what single crossing forbids.
-/

import Sanctions.Foundations.MilgromShannon
import Sanctions.Foundations.IntervalDominanceOrder

namespace Sanctions
namespace TwoBranchQuadratic

/-! ## §1 The family -/

/-- **The two-branch quadratic slice family.**  `slice A lam rho p s x`
is the payoff of choice `s` at parameter `x`: a level `A x` that depends
on the parameter alone, minus a quadratic loss away from the peak `p x`
whose curvature is `lam x` to the left of the peak and `rho x` to the
right.  The two branches are glued at `s = p x`, where both losses
vanish, so the slice is `C¹` there and attains `A x` exactly at its
peak. -/
noncomputable def slice (A lam rho p : ℝ → ℝ) (s x : ℝ) : ℝ :=
  A x - (lam x / 2) * (max (p x - s) 0) ^ 2
      - (rho x / 2) * (max (s - p x) 0) ^ 2

variable {A lam rho p : ℝ → ℝ}

/-- Left-branch closed form: below the peak only the `lam` loss bites. -/
theorem slice_left (x : ℝ) {s : ℝ} (h : s ≤ p x) :
    slice A lam rho p s x = A x - (lam x / 2) * (p x - s) ^ 2 := by
  unfold slice
  rw [max_eq_left (by linarith : (0:ℝ) ≤ p x - s),
      max_eq_right (by linarith : s - p x ≤ 0)]
  ring

/-- Right-branch closed form: above the peak only the `rho` loss bites. -/
theorem slice_right (x : ℝ) {s : ℝ} (h : p x ≤ s) :
    slice A lam rho p s x = A x - (rho x / 2) * (s - p x) ^ 2 := by
  unfold slice
  rw [max_eq_right (by linarith : p x - s ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ s - p x)]
  ring

/-- At its own peak the slice attains its level term. -/
theorem slice_peak (x : ℝ) : slice A lam rho p (p x) x = A x := by
  rw [slice_left x (le_refl _)]; ring

/-! ## §2 Strict single-peakedness

Each slice strictly rises up to its peak and strictly falls after it.
Only positivity of the relevant curvature is used; the level term `A` is
irrelevant because it is constant along the choice axis. -/

/-- **Strictly rising left of the peak.**  If the higher of two choices
still lies weakly below the peak, the higher choice is strictly better. -/
theorem slice_lt_of_le_peak (x : ℝ) (hlam : 0 < lam x) {u v : ℝ}
    (hv : v ≤ p x) (huv : u < v) :
    slice A lam rho p u x < slice A lam rho p v x := by
  have hu : u ≤ p x := le_trans huv.le hv
  rw [slice_left x hu, slice_left x hv]
  nlinarith [mul_pos (sub_pos.2 huv)
    (show (0:ℝ) < 2 * p x - u - v by linarith)]

/-- **Strictly falling right of the peak.**  If the lower of two choices
already lies weakly above the peak, the lower choice is strictly
better. -/
theorem slice_lt_of_peak_le (x : ℝ) (hrho : 0 < rho x) {u v : ℝ}
    (hu : p x ≤ u) (huv : u < v) :
    slice A lam rho p v x < slice A lam rho p u x := by
  have hv : p x ≤ v := le_trans hu huv.le
  rw [slice_right x hu, slice_right x hv]
  nlinarith [mul_pos (sub_pos.2 huv)
    (show (0:ℝ) < u + v - 2 * p x by linarith)]

/-! ## §3 The ordinal side survives: monotonicity transfer

This is the interval-dominance-order input
(`Sanctions.IntervalDominanceOrder.MonotoneTransferOn`), and it holds for
*every* admissible curvature pair.  The mechanism is purely ordinal: the
`MonotoneOn` gate forces the choice interval to sit weakly left of the
lower slice's peak (otherwise the lower slice would strictly fall on
part of it), the peak never falls as the parameter rises, so the
interval sits weakly left of the higher slice's peak too — and there
every slice strictly rises. -/

/-- **Monotonicity transfer holds at every two-branch quadratic slice
family with nondecreasing peaks.**  Hypotheses: both curvatures are
strictly positive on the parameter set `T`, and the peak map `p` is
nondecreasing on `T`.  No comparison between the curvatures at different
parameters is required — which is exactly why this route survives where
single crossing dies (§4). -/
theorem monotoneTransferOn_slice {S T : Set ℝ}
    (hlam : ∀ x ∈ T, 0 < lam x) (hrho : ∀ x ∈ T, 0 < rho x)
    (hp : MonotoneOn p T) :
    IntervalDominanceOrder.MonotoneTransferOn S T (slice A lam rho p) := by
  intro t t' ht ht' htt s' s'' _hs' _hs'' hss hmono
  rcases eq_or_lt_of_le hss with heq | hlt
  · subst heq
    exact ⟨le_refl _, fun h => absurd h (lt_irrefl _)⟩
  · -- The monotone gate confines the interval weakly left of `p t`.
    have hs''pt : s'' ≤ p t := by
      by_contra hcon
      have hcon' := not_le.mp hcon
      have hs0_mem : max s' (p t) ∈ Set.Icc s' s'' :=
        ⟨le_max_left _ _, max_le hss hcon'.le⟩
      have hs''_mem : s'' ∈ Set.Icc s' s'' := ⟨hss, le_refl _⟩
      have hmono_le := hmono hs0_mem hs''_mem (max_le hss hcon'.le)
      have hanti : slice A lam rho p s'' t < slice A lam rho p (max s' (p t)) t :=
        slice_lt_of_peak_le t (hrho t ht) (le_max_right _ _) (max_lt hlt hcon')
      simp only at hmono_le
      linarith
    -- Peaks do not fall, so the same interval is left of `p t'` too.
    have hlt' : slice A lam rho p s' t' < slice A lam rho p s'' t' :=
      slice_lt_of_le_peak t' (hlam t' ht') (le_trans hs''pt (hp ht ht' htt)) hlt
    exact ⟨hlt'.le, fun _ => hlt'⟩

/-! ## §4 The cardinal side fails: refuting single crossing

Single crossing compares payoff LEVELS across a parameter pair, so it
sees the curvatures.  The refutation below straddles the peak: a low
choice on the left branch and a high choice on the right branch.  The
left branch charges `lam`, the right branch charges `rho`, so a
parameter shift that raises `rho` relative to `lam` makes the high
choice worse *relative to* the low one — a reversal single crossing
forbids. -/

/-- **Core single-crossing refutation (no square roots, no chosen
magnitudes).**  Suppose the peak is common to the two parameters
(`p x₁ = p x₂`) and the two choices straddle it (`s' ≤ p x₁ ≤ s''`).  If

* the low parameter's left-branch loss at `s'` is at least its
  right-branch loss at `s''` (`hprem`) — so the low parameter weakly
  prefers the HIGH choice, and
* the high parameter's left-branch loss at `s'` is strictly less than
  its right-branch loss at `s''` (`hfail`) — so the high parameter
  strictly prefers the LOW choice,

then Milgrom-Shannon single crossing fails on `S × T`: the comparison
`s' ≼ s''` accepted at `x₁` is strictly reversed at `x₂`.

The two hypotheses are strict inequalities between the family's own
symbolic data; nothing here is a numeric choice. -/
theorem not_singleCrossingOn_slice {S T : Set ℝ} {x₁ x₂ s' s'' : ℝ}
    (hx₁ : x₁ ∈ T) (hx₂ : x₂ ∈ T) (hx : x₁ ≤ x₂)
    (hs' : s' ∈ S) (hs'' : s'' ∈ S)
    (hpeak : p x₁ = p x₂)
    (hle : s' ≤ p x₁) (hge : p x₁ ≤ s'')
    (hprem : rho x₁ * (s'' - p x₁) ^ 2 ≤ lam x₁ * (p x₁ - s') ^ 2)
    (hfail : lam x₂ * (p x₁ - s') ^ 2 < rho x₂ * (s'' - p x₁) ^ 2) :
    ¬ MilgromShannon.SingleCrossingOn S T (slice A lam rho p) := by
  intro h
  have hss : s' ≤ s'' := le_trans hle hge
  have hle₂ : s' ≤ p x₂ := hpeak ▸ hle
  have hge₂ : p x₂ ≤ s'' := hpeak ▸ hge
  have hprem' : slice A lam rho p s' x₁ ≤ slice A lam rho p s'' x₁ := by
    rw [slice_left x₁ hle, slice_right x₁ hge]; linarith
  have hconc := (h hs' hs'' hss hx₁ hx₂ hx).1 hprem'
  rw [slice_left x₂ hle₂, slice_right x₂ hge₂, ← hpeak] at hconc
  linarith

/-- **Constructive refutation: a strictly increasing curvature ratio
kills single crossing.**  Fix any high choice `s''` strictly above the
common peak `p x₁ = p x₂`, and put the low choice at the point on the
left branch whose quadratic loss exactly matches the high choice's
right-branch loss at the low parameter,

  `s' = p x₁ − √(ρ(x₁)/λ(x₁))·(s'' − p x₁)`.

Then the low parameter is exactly indifferent between the two choices,
while the high parameter strictly prefers the low choice as soon as the
curvature ratio has risen: `ρ(x₁)/λ(x₁) < ρ(x₂)/λ(x₂)`.  Hence single
crossing fails on `S × T`.

Economically: the peak (the direction signal) has not moved, but the
right wing has steepened relative to the left wing (the level signal has
moved), and single crossing — unlike interval dominance — reads levels.

Every input is symbolic: the free data are the two curvature pairs
constrained only by the strict ratio inequality, the common peak, and
the high choice `s''`. -/
theorem not_singleCrossingOn_slice_of_ratio_lt {S T : Set ℝ} {x₁ x₂ s'' : ℝ}
    (hx₁ : x₁ ∈ T) (hx₂ : x₂ ∈ T) (hx : x₁ ≤ x₂)
    (hs'' : s'' ∈ S)
    (hs' : p x₁ - Real.sqrt (rho x₁ / lam x₁) * (s'' - p x₁) ∈ S)
    (hpeak : p x₁ = p x₂)
    (hlam₁ : 0 < lam x₁) (hlam₂ : 0 < lam x₂) (hrho₁ : 0 ≤ rho x₁)
    (hratio : rho x₁ / lam x₁ < rho x₂ / lam x₂)
    (hgt : p x₁ < s'') :
    ¬ MilgromShannon.SingleCrossingOn S T (slice A lam rho p) := by
  set q := Real.sqrt (rho x₁ / lam x₁) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = rho x₁ / lam x₁ :=
    Real.sq_sqrt (div_nonneg hrho₁ hlam₁.le)
  have hd : 0 < s'' - p x₁ := by linarith
  have hdsq : 0 < (s'' - p x₁) ^ 2 := by positivity
  have hle : p x₁ - q * (s'' - p x₁) ≤ p x₁ := by nlinarith
  -- The matched left-branch displacement, squared.
  have hsq : (p x₁ - (p x₁ - q * (s'' - p x₁))) ^ 2
      = rho x₁ / lam x₁ * (s'' - p x₁) ^ 2 := by
    rw [← hq2]; ring
  refine not_singleCrossingOn_slice hx₁ hx₂ hx hs' hs'' hpeak hle hgt.le ?_ ?_
  · -- Low parameter: exact indifference, so the weak premise holds.
    rw [hsq]
    have : lam x₁ * (rho x₁ / lam x₁ * (s'' - p x₁) ^ 2)
        = rho x₁ * (s'' - p x₁) ^ 2 := by
      field_simp
    linarith [this]
  · -- High parameter: the steeper right wing strictly reverses it.
    rw [hsq]
    have hr₂ : rho x₂ * (s'' - p x₁) ^ 2
        = rho x₂ / lam x₂ * lam x₂ * (s'' - p x₁) ^ 2 := by
      field_simp
    rw [hr₂]
    nlinarith [mul_pos (mul_pos (sub_pos.2 hratio) hlam₂) hdsq]

end TwoBranchQuadratic
end Sanctions
