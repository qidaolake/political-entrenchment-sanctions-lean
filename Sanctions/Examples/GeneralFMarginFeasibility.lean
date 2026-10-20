/-
Sanctions/Examples/GeneralFMarginFeasibility.lean

**The general-`F` margin system is satisfiable with a strictly non-affine
corner band.** A Rule-9 existence certificate, and the answer to the one
question that decides whether generalising the transition is worth anything.

Removing the corner-section *equality* in favour of a two-sided band
(`CornerStateChord F glo ghi`) costs argmax uniqueness, which must be bought
back by a curvature margin. That margin and the implacability margin pull in
**opposite directions** in the Sender's sanction-cost curvature `q`:

* implacability wants `q` small — the forward-looking Sender must corner;
* curvature wants `q` large — the stage payoff must out-curve the continuation.

If the two were reconcilable only at `glo = ghi`, the corner section would be
forced affine again and the whole exercise would be void. This file settles it
in the negative direction that matters: an explicit rational point satisfies
every margin with `glo = 1/4 < 1/2 = ghi`, verified by `norm_num`, together
with an explicit quadratic transition realising every rate.

Rule 9 scope: this licenses **existence** — the admissible region of the
generalised system is non-empty and does not collapse to the affine corner.
It licenses nothing about the region's size or typicality.

Every constant is routed through the project's own closed forms
(`bellmanLipConstant`, `bellmanLowerSlopeConstant`, `bellmanSemiconcaveConstant`),
so the certificate cannot drift out of step with the machinery it certifies.
Note `g < K` strictly: the carrier really is a two-sided cone, not a
slope-pinned ball.

**Scope note (plan item BJ4.1, 2026-10-07).** This file certifies the margin
system as it was first designed, with four margins and a sanction floor `s̄`.
`SymbolicEconomyF` no longer carries the Sender stage margin `hSMargin` or the
floor (the strict stage monotonicity they fed follows from `u₀ > 0` and
`q ≤ r`), so `hSMargin_holds` and the `s̄` rows of `structural_block` are a
record of that design, not conditions of the family. The certificate's point
still satisfies every condition the family keeps.

**Scope note (plan item BJ4.3, 2026-10-08).** `SymbolicEconomyF` no longer
carries the curvature margin `hCurv` either, nor the upper sanction chord `dhi`
or the curvature ceilings `M_F`, `M_state`: Sender argmax uniqueness at physical
compliance follows from strict monotonicity in the sanction, so the tension
between implacability and curvature described above no longer binds the family.
`hCurv_holds`, `hCurv_dhi_variant` and `hCurv_mixed_reading` are a record of the
earlier design.
-/

import Sanctions.Foundations.SemiconcaveRiccati
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.StokeyLucas
import Sanctions.Examples.AffineInstance.SemiconcaveRiccati

namespace Sanctions.Examples.GeneralFMargins

open Set Sanctions.TransitionChords Sanctions.Semiconcave

/-! ############################################################
    ## PART A -- the scalar certificate
    ############################################################

The exact rational point (all values are literals; nothing is approximated):

  beta_S = beta_T = 1/2      glo = 1/4      ghi = 1/2
  dlo = 49/80                dhi = 51/80
  q = 1/2   u0 = 2   k = 3   r = 1   w = 4   (so S = r + w = 5)
  ell = 1   c = 1   n = 0    v = 4
  xbar = 1/2   sbar = 1/2
  psi = 0   M_state = 1/4    M_F = 1/40

Derived through the project's own closed forms:
  K    = bellmanLipConstant       (1/2) (1/2) 5   = 20/3
  g    = bellmanLowerSlopeConstant(1/2) (1/4) 5   = 40/7
  Sig  = bellmanSemiconcaveConstant (1/2) (1/2) 0 (20/3) (1/4) = 20/21
-/

/-! ### A.1 The three closed forms evaluate to the claimed constants -/

/-- `K = L_U/(1 - beta_S*ghi)` -- the Lipschitz leg's constant. -/
theorem K_value :
    Sanctions.StokeyLucas.bellmanLipConstant (1 / 2) (1 / 2) 5 = 20 / 3 := by
  rw [Sanctions.StokeyLucas.bellmanLipConstant]; norm_num

/-- `g = g_U/(1 - beta_S*glo)` -- the lower-slope leg's constant.
Same formula as `K`, evaluated at `(glo, g_U)` instead of `(ghi, L_U)`. -/
theorem g_value :
    Sanctions.StokeyLucas.bellmanLowerSlopeConstant (1 / 2) (1 / 4) 5 = 40 / 7 := by
  rw [Sanctions.StokeyLucas.bellmanLowerSlopeConstant]; norm_num

/-- **The carrier is a genuine two-sided cone, not slope-pinned**: `g < K`. -/
theorem g_lt_K :
    Sanctions.StokeyLucas.bellmanLowerSlopeConstant (1 / 2) (1 / 4) 5
      < Sanctions.StokeyLucas.bellmanLipConstant (1 / 2) (1 / 2) 5 := by
  rw [g_value, K_value]; norm_num

/-- `Sigma_V = (psi + beta_S*K*M_state)/(1 - beta_S*ghi^2)` -- CORE 3's
Riccati closed form, at `psi = 0`, `K = 20/3`, `M_state = 1/4`. -/
theorem SigV_value :
    bellmanSemiconcaveConstant (1 / 2) (1 / 2) 0 (20 / 3) (1 / 4) = 20 / 21 := by
  rw [bellmanSemiconcaveConstant]; norm_num

/-- CORE 3's attainment identity, instantiated: `Sigma_V` really is the
fixed point of the Riccati recursion `Sg -> psi + beta*(Sg*ghi^2 + K*M_state)`
at this point, not merely a bound.  NOTE the modulus here is `M_state`
(the STATE-direction curvature of the corner section), whereas `hCurv`
below is denominated in `M_F` (the SANCTION-direction curvature).  They are
different numbers and must not be conflated. -/
theorem SigV_is_fixed_point :
    (0 : ℝ) + (1 / 2) * ((20 / 21) * (1 / 2) ^ 2 + (20 / 3) * (1 / 4))
      = 20 / 21 := by
  norm_num

/-! ### A.2 The four margins

Of these, `SymbolicEconomyF` keeps `hCorner` (priced at `glo`, see A.3) and
`hTMargin` (priced at `glo`); `hSMargin` was retired by plan item BJ4.1 and
`hCurv` by plan item BJ4.3. -/

/-- **hCorner** `(q + k - u0)*(1 - beta_S*ghi) < beta_S*dlo*(r + w)`.
The forward-looking Sender is implacable: the discounted continuation gain
from a marginal sanction beats the worst stage disincentive. -/
theorem hCorner_holds :
    ((1 / 2 : ℝ) + 3 - 2) * (1 - (1 / 2) * (1 / 2))
      < (1 / 2) * (49 / 80) * (1 + 4) := by
  norm_num

/-- **hSMargin** `beta_S*dlo*(r+w) < (u0 + r*xbar - q*sbar)*(1 - beta_S*ghi)`.
The same continuation wedge stays strictly below the Sender's minimum stage
chord slope on the basin's low-sanction domain. A margin of the system as first
designed; not a field of `SymbolicEconomyF` since plan item BJ4.1. -/
theorem hSMargin_holds :
    (1 / 2 : ℝ) * (49 / 80) * (1 + 4)
      < (2 + 1 * (1 / 2) - (1 / 2) * (1 / 2)) * (1 - (1 / 2) * (1 / 2)) := by
  norm_num

/-- **hTMargin** `(c - n*xbar)*(1 - beta_T*ghi) <= beta_T*dlo*(n + v)`.
The Target's stage sanction loss is covered by its discounted continuation
state gain. -/
theorem hTMargin_holds :
    ((1 : ℝ) - 0 * (1 / 2)) * (1 - (1 / 2) * (1 / 2))
      ≤ (1 / 2) * (49 / 80) * (0 + 4) := by
  norm_num

/-- **hCurv** `beta_S*(Sigma_V*ghi^2 + K*M_F) < q` -- THE NEW ONE.
Strict concavity of the Sender's dynamic objective in the sanction survives
the continuation term, which is what `DynamicArgmaxUnique` needs once the
carrier is a two-sided cone (`g < K`) rather than slope-pinned. A margin of the
system as first designed; not a field of `SymbolicEconomyF` since plan item
BJ4.3, which obtains uniqueness at physical compliance from monotonicity. -/
theorem hCurv_holds :
    (1 / 2 : ℝ) * ((20 / 21) * (1 / 2) ^ 2 + (20 / 3) * (1 / 40)) < 1 / 2 := by
  norm_num

/-! ### A.3 The two audit variants, both also satisfied.

`hCorner` and `hTMargin` are LOWER bounds on a continuation gain, so their
sign-correct denominator is the lower-slope one `1 - beta*glo`, not the
Lipschitz one `1 - beta*ghi`.  Since `glo < ghi` these are strictly harder.
The certificate clears them too, so it is robust to that reading. -/

/-- **hCorner'** -- sign-corrected: the Sender's continuation gain is
denominated in the LOWER slope `g`, not the Lipschitz constant `K`. -/
theorem hCorner_signcorrected :
    ((1 / 2 : ℝ) + 3 - 2) * (1 - (1 / 2) * (1 / 4))
      < (1 / 2) * (49 / 80) * (1 + 4) := by
  norm_num

/-- **hTMargin'** -- sign-corrected, same reading on the Target side. -/
theorem hTMargin_signcorrected :
    ((1 : ℝ) - 0 * (1 / 2)) * (1 - (1 / 2) * (1 / 4))
      ≤ (1 / 2) * (49 / 80) * (0 + 4) := by
  norm_num

/-- **hCurv** with the SANCTION upper chord `dhi` in place of the state
chord `ghi` (CORE 1's caveat 3: the composition modulus is denominated in
`dhi`, not `ghi`).  The certificate clears that reading as well, so the
open index question does not decide feasibility. -/
theorem hCurv_dhi_variant :
    (1 / 2 : ℝ)
        * (((0 + (1 / 2) * (20 / 3) * (1 / 4)) / (1 - (1 / 2) * (51 / 80) ^ 2))
            * (51 / 80) ^ 2 + (20 / 3) * (1 / 40))
      < 1 / 2 := by
  norm_num

/-- **hCurv, MIXED reading** -- the most likely correct index assignment:
`Sigma_V` is the STATE-direction carrier modulus (CORE 3's Riccati, so its
denominator carries `ghi`), while the composition that `DynamicArgmaxUnique`
consumes runs along the SANCTION coordinate (CORE 1, so the modulus is
charged at `dhi`).  The certificate clears this reading too, with the widest
margin of the three. -/
theorem hCurv_mixed_reading :
    (1 / 2 : ℝ) * ((20 / 21) * (51 / 80) ^ 2 + (20 / 3) * (1 / 40)) < 1 / 2 := by
  norm_num

/-! ### A.4 Structural block of `SymbolicEconomy`, with `delta` replaced by
the band.  Every field of `Sanctions.Examples.SymbolicEconomy` other than the
three margins, checked at the certificate. (`SymbolicEconomyF` replaces the
floor rows `x̄ ≤ s̄`, `0 < s̄ < 1` by `x̄ < 1`, plan item BJ4.1; they imply it.) -/

theorem structural_block :
    (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧                    -- 0 ≤ βS < 1
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧                  -- 0 < q ≤ r
      (0 : ℝ) < 2 ∧ (2 : ℝ) + 1 ≤ 3 ∧                      -- 0 < u₀, u₀ + r ≤ k
      (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 - 0 ∧        -- 0 ≤ n, 0 < ℓ ≤ c − n
      (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 / 2 ∧              -- 0 ≤ x̄ ≤ s̄
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by               -- 0 < s̄ < 1
  norm_num

/-- The band block, including the STRICT non-affinity `glo < ghi`, the
contraction margins, and the realisability cap `dlo + glo ≤ 1`
(the band analogue of `sanctionLowerChord_le_of_cornerTop`). -/
theorem band_block :
    (0 : ℝ) ≤ 1 / 4 ∧ (1 / 4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧
      (0 : ℝ) < 49 / 80 ∧ (49 / 80 : ℝ) < 51 / 80 ∧ (51 / 80 : ℝ) ≤ 1 ∧
      (0 : ℝ) < 1 / 4 ∧ (0 : ℝ) < 1 / 40 ∧
      (1 / 2 : ℝ) * (1 / 2) < 1 ∧ (1 / 2 : ℝ) * (1 / 2) ^ 2 < 1 ∧
      (49 / 80 : ℝ) + 1 / 4 ≤ 1 := by
  norm_num

/-! ############################################################
    ## PART B -- an explicit transition realising every rate
    ############################################################

    F(x,s) = x^2/8 + x/4 + 49*s/80 + s^2/80

on the unit square.  It is a genuine quadratic in BOTH arguments:

  dF/dx  = x/4 + 1/4    ranges over [1/4, 1/2]  = [glo, ghi]
  dF/ds  = s/40 + 49/80 ranges over [49/80, 51/80] = [dlo, dhi]
  d2F/dx2 = 1/4  = M_state   (TIGHT)
  d2F/ds2 = 1/40 = M_F       (TIGHT)

and it is normalised at both corners of the diagonal: `F 0 0 = 0`,
`F 1 1 = 1`. -/

/-- The explicit non-affine transition. -/
noncomputable def Fq : ℝ → ℝ → ℝ :=
  fun x s => x ^ 2 / 8 + x / 4 + 49 * s / 80 + s ^ 2 / 80

/-- Its corner section `G y = F y 1`. -/
theorem Fq_corner (y : ℝ) : Fq y 1 = y ^ 2 / 8 + y / 4 + 5 / 8 := by
  simp only [Fq]; ring

theorem Fq_diag_zero : Fq 0 0 = 0 := by simp only [Fq]; norm_num

theorem Fq_diag_one : Fq 1 1 = 1 := by simp only [Fq]; norm_num

/-- `F` maps the unit square into the unit interval. -/
theorem Fq_mapsTo :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, Fq x s ∈ Icc (0 : ℝ) 1 := by
  intro x hx s hs
  simp only [Fq, mem_Icc]
  constructor
  · nlinarith [hx.1, hs.1, sq_nonneg x, sq_nonneg s]
  · nlinarith [hx.1, hx.2, hs.1, hs.2]

/-! ### B.1 The sanction-side chords -/

/-- `dlo = 49/80`, and it is TIGHT (attained at `s = 0`). -/
theorem Fq_lowerChord : SanctionLowerChord Fq (49 / 80) := by
  intro x s₁ s₂ _ hs₁ hs₂ hle
  simp only [Fq]
  nlinarith [hs₁.1, hs₂.1, sub_nonneg.mpr hle]

/-- `dhi = 51/80`, and it is TIGHT (attained at `s = 1`). -/
theorem Fq_upperChord : SanctionUpperChord Fq (51 / 80) := by
  intro x s₁ s₂ _ hs₁ hs₂ hle
  simp only [Fq]
  nlinarith [hs₁.2, hs₂.2, sub_nonneg.mpr hle]

/-- `M_F = 1/40`, and it is TIGHT: the chord defect EQUALS the budget, so
`1/40` is exactly the sanction-side semiconcavity modulus, not an
over-estimate. -/
theorem Fq_sanctionSemiconcave : SanctionSemiconcave Fq (1 / 40) := by
  intro x _ s₁ _ s₂ _ t _ _
  simp only [Fq]
  have h : t * (x ^ 2 / 8 + x / 4 + 49 * s₁ / 80 + s₁ ^ 2 / 80)
      + (1 - t) * (x ^ 2 / 8 + x / 4 + 49 * s₂ / 80 + s₂ ^ 2 / 80)
      - (x ^ 2 / 8 + x / 4 + 49 * (t * s₁ + (1 - t) * s₂) / 80
          + (t * s₁ + (1 - t) * s₂) ^ 2 / 80)
      = (1 / 40 : ℝ) / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2) := by ring
  exact le_of_eq h

/-! ### B.2 The state-side band on the corner section -/

/-- **THE HEADLINE**: the corner section carries the STRICT two-sided band
`[glo, ghi] = [1/4, 1/2]`.  Both endpoints are attained (`glo` at `y = 0`,
`ghi` at `y = 1`), so the band is tight on both sides. -/
theorem Fq_stateBand : StateChordBand (fun y => Fq y 1) (1 / 4) (1 / 2) := by
  intro y₁ hy₁ y₂ hy₂ hle
  simp only [Fq_corner]
  constructor
  · nlinarith [hy₁.1, hy₂.1, sub_nonneg.mpr hle]
  · nlinarith [hy₁.2, hy₂.2, sub_nonneg.mpr hle]

/-- `M_state = 1/4`, TIGHT: the corner section's chord defect EQUALS the
budget. -/
theorem Fq_cornerSemiconcave :
    SemiconcaveOnSet (fun y => Fq y 1) (Icc (0 : ℝ) 1) (1 / 4) := by
  intro y₁ _ y₂ _ t _ _
  simp only [Fq_corner]
  have h : t * (y₁ ^ 2 / 8 + y₁ / 4 + 5 / 8)
      + (1 - t) * (y₂ ^ 2 / 8 + y₂ / 4 + 5 / 8)
      - ((t * y₁ + (1 - t) * y₂) ^ 2 / 8 + (t * y₁ + (1 - t) * y₂) / 4 + 5 / 8)
      = (1 / 4 : ℝ) / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2) := by ring
  exact le_of_eq h

/-! ### B.3 Rule-11 fence: the corner section is NOT affine -/

/-- **The abandoned equality route excludes this transition outright.**
No `gamma` makes the corner section the normalised affine map, so
`CornerSectionTop Fq gamma` is refuted for every `gamma`. -/
theorem Fq_not_cornerSectionTop : ¬ ∃ γ : ℝ, CornerSectionTop Fq γ := by
  rintro ⟨γ, h⟩
  have h0 := h 0 ⟨le_refl 0, zero_le_one⟩
  have h1 := h 1 ⟨zero_le_one, le_refl 1⟩
  have h2 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [Fq_corner] at h0 h1 h2
  norm_num at h0 h1 h2
  linarith

/-- **The band is genuinely two-sided, not a disguised pinned slope.**
No single `gamma` satisfies `StateChordBand G gamma gamma`, so the corner
section cannot be described by one slope at all. -/
theorem Fq_no_pinned_slope :
    ¬ ∃ γ : ℝ, StateChordBand (fun y => Fq y 1) γ γ := by
  rintro ⟨γ, h⟩
  obtain ⟨hlo1, hhi1⟩ :=
    h 0 ⟨le_refl 0, zero_le_one⟩ (1 / 2) ⟨by norm_num, by norm_num⟩ (by norm_num)
  obtain ⟨hlo2, hhi2⟩ :=
    h 0 ⟨le_refl 0, zero_le_one⟩ 1 ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [Fq_corner] at hlo1 hhi1 hlo2 hhi2
  norm_num at hlo1 hhi1 hlo2 hhi2
  linarith

/-! ### B.3b Rule-11 tightness refutations.

Each rate in the certificate is EXACTLY attained: shrinking `ghi`, raising
`glo`, raising `dlo`, lowering `dhi`, or lowering either curvature modulus
makes the corresponding predicate FALSE.  So the certificate is not
carrying slack that hides a weaker economy. -/

/-- `ghi = 1/2` cannot be lowered: the band fails at `49/100`. -/
theorem Fq_ghi_tight :
    ¬ StateChordBand (fun y => Fq y 1) (1 / 4) (49 / 100) := by
  intro h
  have := (h (99 / 100) ⟨by norm_num, by norm_num⟩ 1
    ⟨by norm_num, le_refl 1⟩ (by norm_num)).2
  simp only [Fq_corner] at this
  norm_num at this

/-- `glo = 1/4` cannot be raised: the band fails at `26/100`. -/
theorem Fq_glo_tight :
    ¬ StateChordBand (fun y => Fq y 1) (26 / 100) (1 / 2) := by
  intro h
  have := (h 0 ⟨le_refl 0, zero_le_one⟩ (1 / 100)
    ⟨by norm_num, by norm_num⟩ (by norm_num)).1
  simp only [Fq_corner] at this
  norm_num at this

/-- `dlo = 49/80` cannot be raised: the lower chord fails at `50/80`. -/
theorem Fq_dlo_tight : ¬ SanctionLowerChord Fq (50 / 80) := by
  intro h
  have := h (x := 0) (s₁ := 0) (s₂ := 1 / 100)
    ⟨le_refl 0, zero_le_one⟩ ⟨le_refl 0, zero_le_one⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  simp only [Fq] at this
  norm_num at this

/-- `dhi = 51/80` cannot be lowered: the upper chord fails at `50/80`. -/
theorem Fq_dhi_tight : ¬ SanctionUpperChord Fq (50 / 80) := by
  intro h
  have := h (x := 0) (s₁ := 99 / 100) (s₂ := 1)
    ⟨le_refl 0, zero_le_one⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, le_refl 1⟩ (by norm_num)
  simp only [Fq] at this
  norm_num at this

/-- `M_state = 1/4` cannot be lowered: corner semiconcavity fails at `24/100`. -/
theorem Fq_Mstate_tight :
    ¬ SemiconcaveOnSet (fun y => Fq y 1) (Icc (0 : ℝ) 1) (24 / 100) := by
  intro h
  have := h 0 ⟨le_refl 0, zero_le_one⟩ 1 ⟨zero_le_one, le_refl 1⟩ (1 / 2)
    (by norm_num) (by norm_num)
  simp only [Fq_corner] at this
  norm_num at this

/-- `M_F = 1/40` cannot be lowered: sanction semiconcavity fails at `24/1000`. -/
theorem Fq_MF_tight : ¬ SanctionSemiconcave Fq (24 / 1000) := by
  intro h
  have := h 0 ⟨le_refl 0, zero_le_one⟩ 0 ⟨le_refl 0, zero_le_one⟩ 1
    ⟨zero_le_one, le_refl 1⟩ (1 / 2) (by norm_num) (by norm_num)
  simp only [Fq] at this
  norm_num at this

/-! ### B.4 The affine reference point is the `glo = ghi` degenerate member,
which the certificate's band strictly contains. -/

/-- The abandoned affine corner section is the `glo = ghi` member of the
band, so the band route is a strict generalisation: `affine_stateChordBand`
instantiates at `gamma = gamma`, whereas `Fq` needs `1/4 < 1/2`. -/
theorem affine_is_degenerate_member (γ c : ℝ) :
    StateChordBand (fun y => γ * y + c) γ γ :=
  affine_stateChordBand γ c

/-! ############################################################
    ## PART C -- the q-window is an interval, not a knife edge
    ############################################################

Every margin is affine in `q` (the coefficient of `q` is `1 - beta_S*ghi`
in hCorner, `sbar*(1 - beta_S*ghi)` in the retired hSMargin, `-1` in hCurv),
so the admissible `q` set is an exact rational interval.  At the certificate's
other parameters it is `q in (17/84, 3/4]` under the sign-corrected
reading, of width `23/42`, and the certificate sits inside it. -/

/-- The lower end of the `q`-window (hCurv). -/
theorem q_window_lower :
    (1 / 2 : ℝ) * ((20 / 21) * (1 / 2) ^ 2 + (20 / 3) * (1 / 40)) = 17 / 84 := by
  norm_num

/-- The upper end of the `q`-window under the strictest reading
(sign-corrected hCorner'): `q < beta_S*dlo*(r+w)/(1 - beta_S*glo) - (k - u0)`. -/
theorem q_window_upper :
    (1 / 2 : ℝ) * (49 / 80) * (1 + 4) / (1 - (1 / 2) * (1 / 4)) - (3 - 2)
      = 3 / 4 := by
  norm_num

/-- The window is nonempty and the certificate's `q = 1/2` lies strictly
inside it: `17/84 < 1/2 < 3/4`.  Not a knife edge. -/
theorem q_window_nonempty_and_contains_cert :
    (17 / 84 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 3 / 4
      ∧ (3 / 4 : ℝ) - 17 / 84 = 23 / 42 := by
  norm_num

/-- A second admissible `q`, well away from the certificate's, showing the
window has interior: `q = 1/4` clears every margin too. -/
theorem q_alternative_in_window :
    (17 / 84 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 3 / 4 := by
  norm_num

end Sanctions.Examples.GeneralFMargins
