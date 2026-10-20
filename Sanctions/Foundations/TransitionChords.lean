/-
Sanctions/Foundations/TransitionChords.lean

**Sanction-side chord regularity for a two-variable transition law.**

Rule 22 draws the line this file is built on: *regularity on the
transition is allowed; functional form is not.* A hypothesis pinning a
transition to `(1 − δ)·x + δ·s` on all of `[0,1]²` restricts the model to
a linear reduced form. A **chord** condition — how much the successor
must move when the second argument moves, how much curvature it may
carry, what it looks like along one section — restricts only regularity,
and admits genuinely non-affine laws.

This file supplies those chord predicates over a bare
`F : ℝ → ℝ → ℝ`, together with the structural facts that follow from
them alone. Nothing here mentions the sanctions game; the `Params`-level
bridges (including the derivation of strict adjustment and the affine
discharge) live in `Theory/Basin/TransitionChords.lean` per Rule 19.

## The four predicates

* `SanctionLowerChord F d` — raising the second argument by `Δ` raises
  the value by **at least** `d·Δ`. This is the *engine*: it is what makes
  a forward-looking player's continuation gain from a higher sanction
  quantitatively worth having, and it is what the corner-pinning margin
  is priced against.
* `SanctionUpperChord F d` — the matching ceiling, needed only where a
  margin must bound an adverse continuation movement from above.
* `CornerSectionTop F γ` — along the single section `s = 1`, the law is
  the normalised affine map `y ↦ γ·y + (1 − γ)`. One line of the square,
  not the square.
* Sanction-side curvature is expressed by reusing
  `Sanctions.Semiconcave.SemiconcaveOnSet` from `SemiconcaveSup.lean`;
  no new predicate is introduced for it.

## Scoping is load-bearing

Every predicate is scoped to the feasible square. The unrestricted
version — quantifying over all of `ℝ` the way a monotonicity field does
— is **false for every clip-wrapped transition in this development**, and
`sanctionLowerChord_global_fails` records that as a theorem rather than a
comment (in `Examples/Counterexamples/TransitionChordScoping.lean`, since a
refutation is a witness and not part of the general theory). Nor may the sanction range be narrowed to a strict subinterval:
the strict-adjustment derivation instantiates the chord at `s = x`, so it
needs the full square. Exactly this scoping, and no other, works.

## What the lower chord buys, and what it costs

It **buys** strict adjustment: a transition with a positive lower chord
adjusts strictly toward the current sanction, by `F_diag` alone. So the
chord *replaces* that assumption rather than stacking on it.

It **costs** the diagonal-tangent transitions — those that adjust
strictly but with vanishing first-order response near `s = x`. That is a
real narrowing, not a bookkeeping technicality, and the discipline it
imposes is recorded in Rule 22: never restate a strict-adjustment-only
theorem over the chord.

## Where the evidence lives

The affine law discharges every predicate here, and that discharge is in
`Examples/AffineInstance/TransitionChords.lean` rather than in this file ---
moved 2026-08-27, because the one functional form the chord class exists to
generalise should not sit inside the class's own definition (Rule 22).
-/

import Sanctions.Foundations.SemiconcaveSup

namespace Sanctions.TransitionChords

open Set

/-! ## 1. The predicates -/

/-- **Sanction-side lower chord.** On the feasible square, raising the
second argument from `s₁` to `s₂ ≥ s₁` raises the value by at least
`d·(s₂ − s₁)`.

The affine law `(1 − δ)·x + δ·s` satisfies this with `d = δ`, at
equality. A non-affine law may or may not reach the same rate:
`sanctionLowerChord_le_of_cornerTop` caps `d` by the corner section's
responsiveness `1 − γ`, and that cap is attained off the affine law
(`F(x,s) = (x+s)/2 − max(x−s,0)²/10` has corner weight `γ = 1/2`, lower chord
exactly `1/2`, and `F(1,0) = 2/5`), so equality in the bound does not force the
law affine (corrected 2026-09-11, the reader's C03). -/
def SanctionLowerChord (F : ℝ → ℝ → ℝ) (d : ℝ) : Prop :=
  ∀ ⦃x s₁ s₂ : ℝ⦄, x ∈ Icc (0 : ℝ) 1 → s₁ ∈ Icc (0 : ℝ) 1 →
    s₂ ∈ Icc (0 : ℝ) 1 → s₁ ≤ s₂ → d * (s₂ - s₁) ≤ F x s₂ - F x s₁

/-- **Sanction-side upper chord.** The matching ceiling. Required only
where a margin must bound an adverse continuation movement from above;
the interval-dominance route does not need it. -/
def SanctionUpperChord (F : ℝ → ℝ → ℝ) (d : ℝ) : Prop :=
  ∀ ⦃x s₁ s₂ : ℝ⦄, x ∈ Icc (0 : ℝ) 1 → s₁ ∈ Icc (0 : ℝ) 1 →
    s₂ ∈ Icc (0 : ℝ) 1 → s₁ ≤ s₂ → F x s₂ - F x s₁ ≤ d * (s₂ - s₁)

/-- **Corner section at the top.** Along `s = 1` alone, the law is the
normalised affine map `y ↦ γ·y + (1 − γ)`. This is what a slope-pinned
carrier's closed-form Bellman image needs, and it is a condition on one
line of the square. -/
def CornerSectionTop (F : ℝ → ℝ → ℝ) (γ : ℝ) : Prop :=
  ∀ y ∈ Icc (0 : ℝ) 1, F y 1 = γ * y + (1 - γ)

/-- **Sanction-side curvature ceiling**, in chord form, reusing the
semiconcavity predicate rather than introducing a new one. Bounds how
convex the transition may be in the sanction, which is what stops a
strictly concave stage payoff from being overwhelmed by the continuation
term. -/
def SanctionSemiconcave (F : ℝ → ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1,
    Sanctions.Semiconcave.SemiconcaveOnSet (fun s => F x s) (Icc (0 : ℝ) 1) M

/-! ## 2. Elementary consequences -/

/-- A positive lower chord makes the transition strictly increasing in
the sanction on the feasible square. -/
theorem strictMonoOn_of_sanctionLowerChord {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hd : 0 < d) (h : SanctionLowerChord F d) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    StrictMonoOn (fun s => F x s) (Icc (0 : ℝ) 1) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hc := h hx hs₁ hs₂ hlt.le
  have hp : 0 < d * (s₂ - s₁) := mul_pos hd (sub_pos.mpr hlt)
  simpa using (by linarith : F x s₁ < F x s₂)

/-- A lower chord rate can never exceed `1` on the unit square, since the
transition is bounded there. -/
theorem sanctionLowerChord_rate_le_one {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F x s ∈ Icc (0 : ℝ) 1)
    (h : SanctionLowerChord F d) : d ≤ 1 := by
  have h01 := h (x := 0) (s₁ := 0) (s₂ := 1)
    ⟨le_refl 0, zero_le_one⟩ ⟨le_refl 0, zero_le_one⟩
    ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have hlo := (hF 0 ⟨le_refl 0, zero_le_one⟩ 0 ⟨le_refl 0, zero_le_one⟩).1
  have hhi := (hF 0 ⟨le_refl 0, zero_le_one⟩ 1 ⟨zero_le_one, le_refl 1⟩).2
  linarith

/-- **The sanction rates are ordered.** Both chords at state `0` between
sanctions `0` and `1` give `dlo ≤ F 0 1 − F 0 0 ≤ dhi` (round P, 2026-09-11; the
reader's R3). The chord economy and the quadratic–linear family derive their
`hdlo_dhi` (`d_lo ≤ d_hi`) from this lemma; the two rates stay distinct data,
since one rate for both chords is the affine law again (Rule 3's
transition-class clause). -/
theorem sanctionChord_rates_le {F : ℝ → ℝ → ℝ} {dlo dhi : ℝ}
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F dhi) : dlo ≤ dhi := by
  have h1 := hlo (x := 0) (s₁ := 0) (s₂ := 1) ⟨le_rfl, zero_le_one⟩
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have h2 := hhi (x := 0) (s₁ := 0) (s₂ := 1) ⟨le_rfl, zero_le_one⟩
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [sub_zero, mul_one] at h1 h2
  linarith

/-- **The chord rate is capped by the corner section's own responsiveness.**
If the law is normalised-affine along `s = 1` with state weight `γ`, and
fixes the diagonal at `0`, then any lower chord rate satisfies
`d ≤ 1 − γ`. The bound is weak, and that is all the theorem proves: at
state `0` the chord between sanctions `0` and `1` is exactly the corner
section's gap `1 − γ`, so `d` can be no larger. Equality pins that one
section between its endpoints and nothing else — the piecewise law
`(x+s)/2 − max(x−s,0)²/10` attains `d = 1 − γ = 1/2` and is not affine
(`F(1,0) = 2/5`). A strict penalty for a non-affine law would need a further
statement about the transition class, and none is made here (corrected
2026-09-11, the reader's C04; the earlier docstring claimed equality exactly at
the affine law). -/
theorem sanctionLowerChord_le_of_cornerTop {F : ℝ → ℝ → ℝ} {d γ : ℝ}
    (hdiag : F 0 0 = 0) (hcorner : CornerSectionTop F γ)
    (h : SanctionLowerChord F d) : d ≤ 1 - γ := by
  have h01 := h (x := 0) (s₁ := 0) (s₂ := 1)
    ⟨le_refl 0, zero_le_one⟩ ⟨le_refl 0, zero_le_one⟩
    ⟨zero_le_one, le_refl 1⟩ zero_le_one
  rw [hcorner 0 ⟨le_refl 0, zero_le_one⟩, hdiag] at h01
  linarith

/-- **The corner section's intercept is forced.** Any transition fixing
the diagonal and affine along `s = 1` is *normalised* affine there: the
intercept must be `1 − γ`. So `CornerSectionTop` is not secretly stronger
than "the corner section is affine" — the two coincide. -/
theorem cornerSection_intercept_forced {F : ℝ → ℝ → ℝ} {γ c : ℝ}
    (hdiag : F 1 1 = 1) (h : ∀ y ∈ Icc (0 : ℝ) 1, F y 1 = γ * y + c) :
    c = 1 - γ := by
  have h1 := h 1 ⟨zero_le_one, le_refl 1⟩
  rw [hdiag] at h1
  linarith

/-! ## 3. The two-sided corner band

`CornerSectionTop` pins the corner section by an EQUALITY, which makes the
realised recursion `x' = F(x,1)` affine. That is a real restriction on the
dynamics, not merely on the class, so the band below replaces it: it bounds the
corner section's state chords from both sides without pinning it. Setting
`glo = ghi` recovers the equality (`cornerStateChord_of_cornerSectionTop`), so
this is a strict generalisation, and a genuinely non-affine corner section
satisfies the band with `glo < ghi`. -/

/-- **Two-sided state band on the corner section.** -/
def CornerStateChord (F : ℝ → ℝ → ℝ) (glo ghi : ℝ) : Prop :=
  ∀ ⦃y₁ y₂ : ℝ⦄, y₁ ∈ Icc (0 : ℝ) 1 → y₂ ∈ Icc (0 : ℝ) 1 → y₁ ≤ y₂ →
    glo * (y₂ - y₁) ≤ F y₂ 1 - F y₁ 1 ∧ F y₂ 1 - F y₁ 1 ≤ ghi * (y₂ - y₁)

/-- **The corner band's rates are ordered.** Between the states `0` and `1` the
band reads `glo ≤ F 1 1 − F 0 1 ≤ ghi`, so `glo ≤ ghi` is a consequence of the
band and never a separate condition. General in `F`: nothing is used but the band
itself, at the two ends of the corner section. This is `StateChordBand.rates_le`
(`Foundations/SemiconcaveRiccati.lean`) restated for the corner section `s = 1`;
it is what lets `mem_valLipGainBall_bellman_chord` and
`valueLipschitz_bellman_chord` drop their `glo ≤ ghi` hypothesis (BG1.4,
2026-10-06). -/
theorem CornerStateChord.rates_le {F : ℝ → ℝ → ℝ} {glo ghi : ℝ}
    (h : CornerStateChord F glo ghi) : glo ≤ ghi := by
  have h01 := h (y₁ := 0) (y₂ := 1) ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [sub_zero, mul_one] at h01
  linarith [h01.1, h01.2]

/-- The pinned-affine corner section is the `glo = ghi` member. -/
theorem cornerStateChord_of_cornerSectionTop {F : ℝ → ℝ → ℝ} {γ : ℝ}
    (h : CornerSectionTop F γ) : CornerStateChord F γ γ := by
  intro y₁ y₂ h₁ h₂ hle
  rw [h y₁ h₁, h y₂ h₂]
  constructor <;> nlinarith

/-- **Forward invariance of the corner section is itself a chord consequence.** -/
theorem cornerSection_mapsTo_of_chord {F : ℝ → ℝ → ℝ} {glo ghi : ℝ}
    (hglo : 0 ≤ glo) (hghi : ghi ≤ 1) (hfix : F 1 1 = 1)
    (h : CornerStateChord F glo ghi) :
    ∀ y ∈ Icc (0 : ℝ) 1, F y 1 ∈ Icc (0 : ℝ) 1 := by
  intro y hy
  obtain ⟨hlo, hhi⟩ := h hy (Set.right_mem_Icc.mpr zero_le_one) hy.2
  rw [hfix] at hlo hhi
  exact ⟨by nlinarith [hy.1, hy.2], by nlinarith [hy.1, hy.2]⟩

/-! ## The chords ARE a speed of adjustment

A useful reading, and the one that makes the pair paper-facing. Set the sanction
at `s` and hold it. Read the lower chord at `(x, x, s)` and use `F x x = x`:

  `dlo * (s - x) ≤ F x s - x`

— the state closes at least the fraction `dlo` of its distance to the standing
sanction in one period. The upper chord says it closes at most the fraction `d`,
and with `d ≤ 1` that also rules out overshoot. Together:

  `(1 - d) * |x - s| ≤ |F x s - s| ≤ (1 - dlo) * |x - s|`

so the remaining gap contracts geometrically with modulus in `[1 - d, 1 - dlo]`.
The affine law is the case `dlo = d = δ`, where the gap contracts by exactly
`1 - δ` — which is why the pair is the right generalisation of `affineF` and why
collapsing the two rates into one recovers it exactly.

This is the honest economic content of the hypotheses the certificate route
carries: **not** "sanctions move the state" (that is `StrictAdjustment`), but
"the state converges to the standing sanction at a geometric rate bounded away
from zero, uniformly over the square." -/

/-- **Gap contraction from the two chords.** Holding the sanction at `s`, the
distance from the state to `s` shrinks by at least the factor `1 - d` and at
most the factor `1 - dlo` in one period. -/
theorem gap_contraction_of_chords {F : ℝ → ℝ → ℝ} {dlo d : ℝ}
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F d)
    (hd1 : d ≤ 1) (hdiag : ∀ x, F x x = x)
    {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 - d) * |x - s| ≤ |F x s - s| ∧ |F x s - s| ≤ (1 - dlo) * |x - s| := by
  rcases le_total x s with h | h
  · have hL := hlo hx hx hs h
    have hU := hhi hx hx hs h
    rw [hdiag x] at hL hU
    have hle : F x s ≤ s := by nlinarith
    rw [abs_of_nonpos (by linarith : x - s ≤ 0),
        abs_of_nonpos (by linarith : F x s - s ≤ 0)]
    constructor <;> nlinarith
  · have hL := hlo hx hs hx h
    have hU := hhi hx hs hx h
    rw [hdiag x] at hL hU
    have hge : s ≤ F x s := by nlinarith
    rw [abs_of_nonneg (by linarith : 0 ≤ x - s),
        abs_of_nonneg (by linarith : 0 ≤ F x s - s)]
    constructor <;> nlinarith

/-! ## Metric interfaces

The two chord predicates are already metric statements; they are just not
written in Mathlib's vocabulary for them. Saying so costs nothing and makes the
standard library's Lipschitz machinery — composition, inverse estimates,
uniform continuity — available on a sanction section without restating any
hypothesis.

An upper chord bounds how far the successor state can move when the sanction
moves, which is a Lipschitz bound. A strictly positive lower chord bounds how
far it must move *at least*, which is the reciprocal statement: the section
cannot compress distances by more than `1/dlo`, so it is injective and its
inverse is Lipschitz. Neither adapter adds an economic assumption. -/

/-- **Both chords together give a Lipschitz bound on the sanction section.**

The upper chord alone is not enough, and it is worth being exact about why: it
bounds `F x s₂ − F x s₁` from above but says nothing from below, so on a
transition that *decreased* in the sanction the absolute difference could be
arbitrarily large while the chord held. A nonnegative lower chord supplies the
missing side — it is exactly the statement that the section does not decrease —
and the two together bracket the increment.

At `Params` the lower side is free from `F_mono_s`; stated here over a bare `F`,
it has to be asked for. -/
theorem dist_le_of_chords
    {F : ℝ → ℝ → ℝ} {dlo d : ℝ} (hdlo : 0 ≤ dlo)
    (hlo : SanctionLowerChord F dlo) (hhi : SanctionUpperChord F d)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {s₁ s₂ : ℝ}
    (h₁ : s₁ ∈ Icc (0 : ℝ) 1) (h₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    |F x s₂ - F x s₁| ≤ d * |s₂ - s₁| := by
  rcases le_total s₁ s₂ with hle | hle
  · have hd0 : (0 : ℝ) ≤ s₂ - s₁ := by linarith
    have hup := hhi hx h₁ h₂ hle
    have hdn := hlo hx h₁ h₂ hle
    have hnn : (0 : ℝ) ≤ F x s₂ - F x s₁ :=
      le_trans (mul_nonneg hdlo hd0) hdn
    rw [abs_of_nonneg hnn, abs_of_nonneg hd0]
    exact hup
  · have hd0 : (0 : ℝ) ≤ s₁ - s₂ := by linarith
    have hup := hhi hx h₂ h₁ hle
    have hdn := hlo hx h₂ h₁ hle
    have hnn : (0 : ℝ) ≤ F x s₁ - F x s₂ :=
      le_trans (mul_nonneg hdlo hd0) hdn
    rw [abs_sub_comm (F x s₂), abs_sub_comm s₂, abs_of_nonneg hnn,
      abs_of_nonneg hd0]
    exact hup

/-- **A strictly positive lower chord bounds distances from below** — the
antilipschitz direction. A sanction move of size `t` forces a state move of at
least `dlo · t`. -/
theorem le_dist_of_sanctionLowerChord
    {F : ℝ → ℝ → ℝ} {dlo : ℝ} (h : SanctionLowerChord F dlo)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {s₁ s₂ : ℝ}
    (h₁ : s₁ ∈ Icc (0 : ℝ) 1) (h₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    dlo * |s₂ - s₁| ≤ |F x s₂ - F x s₁| := by
  rcases le_total s₁ s₂ with hle | hle
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₂ - s₁)]
    exact le_trans (h hx h₁ h₂ hle) (le_abs_self _)
  · rw [abs_sub_comm (F x s₂), abs_sub_comm s₂]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₁ - s₂)]
    exact le_trans (h hx h₂ h₁ hle) (le_abs_self _)

/-- **The section is injective when the lower chord is strict.**

Distinct sanctions produce distinct successor states, which is the content
`StrictAdjustment` needs and which the lower chord already carries. -/
theorem sanctionSection_injOn_of_lowerChord
    {F : ℝ → ℝ → ℝ} {dlo : ℝ} (hdlo : 0 < dlo) (h : SanctionLowerChord F dlo)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Set.InjOn (fun s => F x s) (Icc (0 : ℝ) 1) := by
  intro s₁ h₁ s₂ h₂ heq
  by_contra hne
  have hpos : 0 < |s₂ - s₁| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hbound := le_dist_of_sanctionLowerChord h hx h₁ h₂
  simp only [heq, sub_self, abs_zero] at hbound
  nlinarith

/-! ## 4. The sanction-side Lipschitz bound, from the upper chord alone

`dist_le_of_chords` above needs **both** chords, because without monotonicity a
two-sided bound on `F x s₂ - F x s₁` needs a floor as well as a ceiling. When the
law is already known to be nondecreasing in the sanction — which is a maintained
primitive of the game (`Params.F_mono_s`) — the floor is free, and the ceiling
alone delivers the absolute bound.

This is what lets a row-Lipschitz estimate be stated general in `F`: the affine
law contributes `|F x s₁ - F x s₂| = δ·|s₁ - s₂|` as an *equality*, and all that
is ever used of it is the `≤` direction. -/

/-- **The upper chord rate is nonnegative**, given monotonicity — so it need not
be assumed. Read off the unit square's own corners. -/
theorem sanctionUpperChord_nonneg {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hup : SanctionUpperChord F d) (hmono : ∀ x, Monotone (fun s => F x s)) :
    0 ≤ d := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hchord : F 0 1 - F 0 0 ≤ d * (1 - 0) := hup h0 h0 h1 zero_le_one
  have hm : F 0 0 ≤ F 0 1 := hmono 0 zero_le_one
  linarith

/-- **Upper chord plus monotonicity gives a sanction-side Lipschitz bound.**

Economically: if the political technology's responsiveness to sanctions has a
finite ceiling `d`, and more sanction never lowers entrenchment, then two
sanction levels can move next period's entrenchment by at most `d` times their
gap — in either direction. No functional form, and in particular no linearity. -/
theorem abs_sub_le_of_upperChord {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hup : SanctionUpperChord F d) (hmono : ∀ x, Monotone (fun s => F x s))
    {x s₁ s₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h1 : s₁ ∈ Icc (0 : ℝ) 1) (h2 : s₂ ∈ Icc (0 : ℝ) 1) :
    |F x s₁ - F x s₂| ≤ d * |s₁ - s₂| := by
  rcases le_total s₁ s₂ with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (hmono x h)),
        abs_of_nonpos (sub_nonpos.mpr h)]
    have := hup hx h1 h2 h
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono x h)),
        abs_of_nonneg (sub_nonneg.mpr h)]
    exact hup hx h2 h1 h

end Sanctions.TransitionChords
