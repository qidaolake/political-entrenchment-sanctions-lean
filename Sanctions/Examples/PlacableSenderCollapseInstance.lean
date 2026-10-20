/-
Sanctions/Examples/PlacableSenderCollapseInstance.lean

**At the collapse the exact defiance threshold is `β_T*`, from nine conditions and without
(T6)** (renovation item BH3.8, 2026-10-06).

`collapse_equilibrium_threshold_le` (`PlacableSenderDefianceClosed.lean`) shows that on the
enriched subclass `ChordEconomyCs`, under placability and fourteen tightness equalities, a
full-defiance top-selector equilibrium exists exactly when `β_T* ≤ β_T`. Nothing tied it to
the general defiance interval of `PlacableSenderExactThresholds.lean`, whose lower end `β_D`
is not computed there. This file does two things.

1. **Five of the fourteen equalities are certificate choices** (`collapseRecert`). The tight
   sanction chords `d_lo = d_hi` pin the transition to the affine law `affineF d_lo` on the
   unit square (`F_eq_affineF_of_tight_sanction`). That law is certified by the state band
   `g_lo = g_hi = 1 − d_lo` and by zero moduli `M_s = M_cx = M_mix = M_cs = 0`
   (§1, the affine-on-square lemmas at a general rate `d`, generalising the rate-`1/2`
   lemmas of `PlacableSenderWitnesses.lean`). With `σ_V = 0` the Riccati closure still holds.
   So any relief economy with `σ_V = 0` and `d_lo = d_hi` is re-certified as an enriched
   economy with the same game (`toParams`) and the same `β_T*`; interiority and placability
   carry over, because the new Lipschitz constant `K_S` is no larger (`1 − d_lo ≤ g_hi`).
   The threshold theorem therefore holds on the relief extension under nine conditions:
   `σ_V`, `τ_x`, `n_hi` zero and `Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`,
   `v_lo = v_hi`, `d_lo = d_hi` (`collapse_equilibrium_threshold_le_tight`). The dropped
   conditions are `M_s`, `M_cx`, `M_cs`, `M_mix` zero and `g_lo = g_hi`; with them goes the
   enriched subclass and its sanction-section semiconvexity (T6).
2. **The collapse is an instance of the exact thresholds.** Under the nine conditions the
   discounts with a full-defiance equilibrium are exactly `[β_T*, 1)`
   (`collapse_defianceExistenceSet`; `0 < β_T*` is `betaStar_pos_of_collapse`), and the
   general interval theorem `ChordEconomyRelief.defianceExistenceSet_eq_Ico` applies, at the
   re-certified member, with its two hypotheses discharged by `L_resp = 0`. So
   `β_D = β_T*` whenever `β_T* < 1` (`collapse_exact_thresholds`): the collapse threshold is
   the closed form of the exact defiance threshold, as `aw_exact_thresholds`
   (`AffineWindowInstance.lean`) is at the affine window.
3. **Rule 9.** The nine conditions, interiority, the stage relief margin and placability hold
   together at the collapse members of `PlacableSenderCollapseWitness.lean`, where the set is
   `[2/11, 1)` (`collapseAffine_defianceExistenceSet`).

**Rule 22: AFFINE BY HYPOTHESIS.** `d_lo = d_hi` pins `F = affineF d_lo` on the unit square;
every theorem here that carries it is the affine collapse, stated over the general relief
class. The lemmas of §1 are about transitions equal to `affineF d` on the square (AFFINE);
`one_sub_dhi_le_ghi` and `chKS_le_of_le` are general. **Rule 3.** No assumption is
introduced: every hypothesis is one of `collapse_equilibrium_threshold_le`'s, and
`β_T* < 1` in `collapse_exact_thresholds` is the case in which `β_D` is defined by a
nonempty set. The generality gained is in the certificates: a relief economy whose game is a
collapse game but whose chord constants are loose (`g_lo < g_hi`, or positive `M_s`, `M_cx`,
`M_mix`) is now covered; the class of games is not enlarged, since the re-certified member is
the same game.
-/
import Sanctions.Examples.PlacableSenderExactThresholds
import Sanctions.Examples.PlacableSenderCollapseWitness
import Sanctions.Examples.ChordEconomyTightChords

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.Semiconcave Sanctions.TransitionChords

noncomputable section

/-! ## 1. Affine on the square at a general rate

The chord predicates of the class quantify over the unit square only, so a transition that
equals the affine law `affineF d` there carries the affine law's certificates: state chords
`1 − d` on both sides, zero joint, state-section, sanction-section and mixed moduli. These
are the rate-`1/2` lemmas `affineF_half_*` of `PlacableSenderWitnesses.lean` at a general
rate and for any transition affine on the square. -/

/-- **A transition affine on the square has the state chord band `[1 − d, 1 − d]`.** AFFINE:
`F` equals `affineF d` on the unit square. -/
theorem stateChordBandAll_of_eqOn_affineF {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F x s = affineF d x s) :
    StateChordBandAll F (1 - d) (1 - d) := by
  intro s hs y₁ hy₁ y₂ hy₂ _
  have e : F y₂ s - F y₁ s = (1 - d) * (y₂ - y₁) := by
    rw [hF y₂ hy₂ s hs, hF y₁ hy₁ s hs]
    unfold affineF
    ring
  exact ⟨e.ge, e.le⟩

/-- **A transition affine on the square is jointly semiconcave** with any nonnegative state
and cross moduli and any nonpositive sanction modulus: its chord defect is zero. AFFINE. -/
theorem jointSemiconcaveOn_of_eqOn_affineF {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F x s = affineF d x s)
    {σ ρ q : ℝ} (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) (hq : q ≤ 0) :
    JointSemiconcaveOn F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) σ ρ q := by
  intro x₁ hx₁ x₂ hx₂ a₁ ha₁ a₂ ha₂ t ht0 ht1
  rw [hF x₁ hx₁ a₁ ha₁, hF x₂ hx₂ a₂ ha₂,
    hF _ (mem_Icc_convexComb hx₁ hx₂ ht0 ht1) _ (mem_Icc_convexComb ha₁ ha₂ ht0 ht1)]
  have e : t * affineF d x₁ a₁ + (1 - t) * affineF d x₂ a₂
      - affineF d (t * x₁ + (1 - t) * x₂) (t * a₁ + (1 - t) * a₂) = 0 := by
    unfold affineF
    ring
  rw [e]
  have h1 : 0 ≤ t * (1 - t) / 2 := by
    have := sub_nonneg.2 ht1
    positivity
  have h2 : 0 ≤ σ * (x₁ - x₂) ^ 2 + 2 * ρ * |x₁ - x₂| * |a₁ - a₂| - q * (a₁ - a₂) ^ 2 := by
    have k1 := mul_nonneg hσ (sq_nonneg (x₁ - x₂))
    have k2 := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hρ) (abs_nonneg (x₁ - x₂)))
      (abs_nonneg (a₁ - a₂))
    have k3 := mul_nonneg (neg_nonneg.2 hq) (sq_nonneg (a₁ - a₂))
    nlinarith
  exact mul_nonneg h1 h2

/-- **The state sections of a transition affine on the square are `0`-semiconvex.**
AFFINE. -/
theorem semiconvexOnSet_state_of_eqOn_affineF {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F x s = affineF d x s) :
    ∀ s ∈ Icc (0 : ℝ) 1, SemiconvexOnSet (fun y => F y s) (Icc (0 : ℝ) 1) 0 := by
  intro s hs y₁ hy₁ y₂ hy₂ t ht0 ht1
  simp only
  rw [hF y₁ hy₁ s hs, hF y₂ hy₂ s hs, hF _ (mem_Icc_convexComb hy₁ hy₂ ht0 ht1) s hs]
  have e : affineF d (t * y₁ + (1 - t) * y₂) s
      - (t * affineF d y₁ s + (1 - t) * affineF d y₂ s) = 0 := by
    unfold affineF
    ring
  rw [e]
  simp

/-- **The sanction sections of a transition affine on the square are `0`-semiconvex.**
AFFINE. -/
theorem semiconvexOnSet_sanction_of_eqOn_affineF {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F x s = affineF d x s) :
    ∀ x ∈ Icc (0 : ℝ) 1, SemiconvexOnSet (fun s => F x s) (Icc (0 : ℝ) 1) 0 := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  simp only
  rw [hF x hx s₁ hs₁, hF x hx s₂ hs₂, hF x hx _ (mem_Icc_convexComb hs₁ hs₂ ht0 ht1)]
  have e : affineF d x (t * s₁ + (1 - t) * s₂)
      - (t * affineF d x s₁ + (1 - t) * affineF d x s₂) = 0 := by
    unfold affineF
    ring
  rw [e]
  simp

/-- **A transition affine on the square has no mixed curvature.** AFFINE. -/
theorem mixedChordBound_of_eqOn_affineF {F : ℝ → ℝ → ℝ} {d : ℝ}
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, F x s = affineF d x s) :
    MixedChordBound F 0 := by
  intro x₁ x₂ s₁ s₂ hx₁ hx₂ hs₁ hs₂
  rw [hF x₂ hx₂ s₂ hs₂, hF x₁ hx₁ s₂ hs₂, hF x₂ hx₂ s₁ hs₁, hF x₁ hx₁ s₁ hs₁]
  have e : (affineF d x₂ s₂ - affineF d x₁ s₂) - (affineF d x₂ s₁ - affineF d x₁ s₁) = 0 := by
    unfold affineF
    ring
  rw [e]
  simp

/-- **`K_S` is monotone in the upper state chord**: `w/(1 − β g') ≤ w/(1 − β g)` for
`g' ≤ g`, `β, w ≥ 0` and `β g < 1`. Pure real arithmetic. -/
theorem chKS_le_of_le {βS g g' w : ℝ} (hβ : 0 ≤ βS) (hw : 0 ≤ w) (hpos : 0 < 1 - βS * g)
    (hg : g' ≤ g) : chKS βS g' w ≤ chKS βS g w := by
  unfold chKS
  apply div_le_div_of_nonneg_left hw hpos
  nlinarith [mul_le_mul_of_nonneg_left hg hβ]

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **The upper state chord covers what the upper sanction chord leaves**: `1 − d_hi ≤ g_hi`.
The upper sanction chord from `(0,0)` to `(0,1)` gives `F(0,1) ≤ d_hi`, and the upper state
chord at sanction one from `(0,1)` to `(1,1)` gives `1 − F(0,1) ≤ g_hi` (`F_diag`). General
in `F`. -/
theorem one_sub_dhi_le_ghi : 1 - E.dhi ≤ E.ghi := by
  have h1 := E.hShi zero_mem_I zero_mem_I one_mem_I zero_le_one
  have h2 := (E.hbandAll 1 one_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one).2
  have h3 := E.F_diag 0
  have h4 := E.F_diag 1
  simp only [sub_zero, mul_one] at h1 h2
  linarith

end ChordEconomy

/-! ## 2. Re-certification at the collapse -/

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The collapse economy re-certified** (renovation item BH3.8, 2026-10-06). Given a zero
supplied Sender modulus (`σ_V = 0`) and tight sanction chords (`d_lo = d_hi`), the same game
as an enriched chord economy with the affine law's certificates: state chords
`g_lo = g_hi = 1 − d_lo` and zero moduli `M_s = M_cx = M_mix = M_cs = 0`; every other field,
the game (`toParams`) included, is `E`'s. The chord fields hold because `d_lo = d_hi` makes
`F = affineF d_lo` on the square (`F_eq_affineF_of_tight_sanction`, §1); the curvature
margin and the Riccati closure hold because `σ_V = 0` makes `r_hi = σ_x = M_x = M_m = 0`
(`zeros_of_SigV_eq_zero`). AFFINE BY HYPOTHESIS (`d_lo = d_hi`). -/
def collapseRecert (hSigV : E.SigV = 0) (hd : E.dlo = E.dhi) : ChordEconomyCs :=
  { E with
    glo := 1 - E.dlo
    ghi := 1 - E.dlo
    Ms := 0
    Mcx := 0
    Mmix := 0
    SigV := 0
    hbandAll := stateChordBandAll_of_eqOn_affineF
      (fun _ hx _ hs => E.F_eq_affineF_of_tight_sanction hd hx hs)
    hFjsc := jointSemiconcaveOn_of_eqOn_affineF
      (fun _ hx _ hs => E.F_eq_affineF_of_tight_sanction hd hx hs) E.hMx0 E.hMm0 neg_zero.le
    hglo0 := by linarith [E.glo_add_dlo_le_one, E.hglo0]
    hghi1 := by linarith [E.hdlo0]
    hMs0 := le_rfl
    hMcx0 := le_rfl
    hFcx := semiconvexOnSet_state_of_eqOn_affineF
      (fun _ hx _ hs => E.F_eq_affineF_of_tight_sanction hd hx hs)
    hFmix := mixedChordBound_of_eqOn_affineF
      (fun _ hx _ hs => E.F_eq_affineF_of_tight_sanction hd hx hs)
    hCurv := by simpa using E.hq
    hSigV := by
      obtain ⟨hr, hσ, hMx, hMm⟩ := E.zeros_of_SigV_eq_zero hSigV
      simp [chSigImg, chSig, plRho, plMu, hr, hσ, hMx, hMm]
    Mcs := 0
    hMcs0 := le_rfl
    hFcs := semiconvexOnSet_sanction_of_eqOn_affineF
      (fun _ hx _ hs => E.F_eq_affineF_of_tight_sanction hd hx hs) }

variable {E}

/-- **Interiority carries over to the re-certified economy**: its Lipschitz constant
`K_S = w_hi/(1 − β_S(1 − d_lo))` is at most `E`'s, since `1 − d_lo ≤ g_hi`
(`one_sub_dhi_le_ghi` with `d_lo = d_hi`). AFFINE BY HYPOTHESIS. -/
theorem collapseRecert_interior (hSigV : E.SigV = 0) (hd : E.dlo = E.dhi)
    (hInt : E.Interior) : (E.collapseRecert hSigV hd).Interior := by
  have hg : 1 - E.dlo ≤ E.ghi := by rw [hd]; exact E.one_sub_dhi_le_ghi
  have hK := chKS_le_of_le E.hβS0.le E.whi_pos.le E.one_sub_βS_ghi_pos hg
  have hb : 0 ≤ E.β_S * E.dhi := mul_nonneg E.hβS0.le E.dhi_nonneg
  have hInt' : E.uhi + E.β_S * chKS E.β_S E.ghi E.whi * E.dhi < E.q := hInt
  change E.uhi + E.β_S * chKS E.β_S (1 - E.dlo) E.whi * E.dhi < E.q
  nlinarith [mul_le_mul_of_nonneg_left hK hb]

/-- **Placability carries over to the re-certified economy**: its appetite
`A = u_hi + β_S K_S d_hi` is at most `E`'s, as in `collapseRecert_interior`. AFFINE BY
HYPOTHESIS. -/
theorem collapseRecert_placable (hSigV : E.SigV = 0) (hd : E.dlo = E.dhi)
    (hP : E.Placable) : (E.collapseRecert hSigV hd).Placable := by
  have hg : 1 - E.dlo ≤ E.ghi := by rw [hd]; exact E.one_sub_dhi_le_ghi
  have hK := chKS_le_of_le E.hβS0.le E.whi_pos.le E.one_sub_βS_ghi_pos hg
  have hb : 0 ≤ E.β_S * E.dhi := mul_nonneg E.hβS0.le E.dhi_nonneg
  have hP' : E.uhi + E.β_S * chKS E.β_S E.ghi E.whi * E.dhi ≤ E.klo := hP
  change E.uhi + E.β_S * chKS E.β_S (1 - E.dlo) E.whi * E.dhi ≤ E.klo
  nlinarith [mul_le_mul_of_nonneg_left hK hb]

/-- **The exact closed threshold at the collapse, from nine conditions and without (T6)**
(renovation item BH3.8, 2026-10-06). Let a relief economy satisfy interiority, the stage
relief margin, placability and nine tightness conditions: the supplied Sender modulus, the
Sender's state semiconvexity and the Target's upper envelope slope vanish
(`σ_V = τ_x = n_hi = 0`), and the pairs `Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`,
`v_lo = v_hi` and `d_lo = d_hi` are tight. Then a top-selector equilibrium with full
defiance at every feasible state exists **if and only if** `β_T* ≤ β_T`. It is
`collapse_equilibrium_threshold_le` at the re-certified member `collapseRecert`, which has
the same game and the same `β_T*`. Dropped against that theorem: `M_s`, `M_cx`, `M_cs`,
`M_mix` zero and `g_lo = g_hi`, and the enriched subclass (T6); all five are certificate
choices, not conditions on the game. AFFINE BY HYPOTHESIS: `d_lo = d_hi` pins
`F = affineF d_lo` on the square. -/
theorem collapse_equilibrium_threshold_le_tight (hInt : E.Interior) (hSR : E.StageRelief)
    (hP : E.Placable) (hSigV : E.SigV = 0) (hτ : E.τx = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hd : E.dlo = E.dhi) :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ↔ E.betaStar ≤ E.β_T :=
  (E.collapseRecert hSigV hd).collapse_equilibrium_threshold_le
    (collapseRecert_interior hSigV hd hInt) hSR (collapseRecert_placable hSigV hd hP)
    rfl rfl hτ rfl rfl rfl hQ hk hℓ hp hv hnhi rfl hd

/-! ## 3. The collapse as an instance of the exact defiance threshold -/

/-- **The collapse threshold is positive.** Under the stage relief margin and the tight pairs
`Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`, the margin reads `ℓ_lo q < k_hi c`, so
`D = c − ℓ_lo q/k_hi > 0`; with `0 < d_lo ≤ 1` and `v_lo > 0` the denominator
`d_lo v_lo + (1 − d_lo) D` of `β_T*` is positive too. General in `F`. -/
theorem betaStar_pos_of_collapse (hSR : E.StageRelief) (hQ : E.Qbar = E.q) (hk : E.klo = E.khi)
    (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) : 0 < E.betaStar := by
  have hsr : E.ℓlo * E.q < E.khi * E.c := by
    have h := hSR
    unfold StageRelief at h
    rw [hQ, hk, hp, ← hℓ] at h
    exact h
  have hkhi := E.khi_pos
  have hD : 0 < E.c - E.ℓlo * E.q / E.khi := by
    rw [sub_pos, div_lt_iff₀ hkhi]
    linarith [mul_comm E.c E.khi]
  have hd1 : E.dlo ≤ 1 := by linarith [E.glo_add_dlo_le_one, E.hglo0]
  unfold betaStar
  apply div_pos hD
  nlinarith [mul_pos E.hdlo0 E.hvlo, mul_nonneg (sub_nonneg.2 hd1) hD.le]

/-- **At the collapse the discounts with full defiance are exactly `[β_T*, 1)`** (renovation
item BH3.8, 2026-10-06). Under interiority, the stage relief margin, placability and the nine
tightness conditions of `collapse_equilibrium_threshold_le_tight`, the base family's
existence set is the interval `[β_T*, 1)`. The threshold theorem applies at every member
`E.withβT b`: neither the conditions nor `β_T*` read `β_T`. With no condition on `β_T*`: if
`β_T* ≥ 1` both sides are empty. AFFINE BY HYPOTHESIS (`d_lo = d_hi`). -/
theorem collapse_defianceExistenceSet (hInt : E.Interior) (hSR : E.StageRelief)
    (hP : E.Placable) (hSigV : E.SigV = 0) (hτ : E.τx = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hd : E.dlo = E.dhi) :
    E.defianceExistenceSet = Ico E.betaStar 1 := by
  have hpos := betaStar_pos_of_collapse hSR hQ hk hℓ hp
  ext b
  constructor
  · rintro ⟨⟨h0, h1⟩, hex⟩
    exact ⟨((E.withβT b h0 h1).collapse_equilibrium_threshold_le_tight hInt hSR hP hSigV hτ hQ
      hk hℓ hp hv hnhi hd).1 hex, h1⟩
  · rintro ⟨hb, h1⟩
    have h0 : 0 < b := lt_of_lt_of_le hpos hb
    exact ⟨⟨h0, h1⟩, ((E.withβT b h0 h1).collapse_equilibrium_threshold_le_tight hInt hSR hP
      hSigV hτ hQ hk hℓ hp hv hnhi hd).2 hb⟩

/-- **The collapse is an instance of the exact defiance threshold: `β_D = β_T*`**
(renovation item BH3.8, 2026-10-06). Under interiority, the stage relief margin, placability
and the nine tightness conditions, with an interior threshold `β_T* < 1`: the existence set
is the interval `[β_D, 1)` that the general theorem
`ChordEconomyRelief.defianceExistenceSet_eq_Ico` gives, and its lower end is
`β_D = β_T*`. The general theorem is applied at the re-certified member, whose existence set
is `E`'s (the same game); there `L_resp = 0` (`collapse_Lresp'`) gives both of its
hypotheses, a monotone response (`responsePath_monotoneOn_of_Lresp_eq_zero`) and the weak
balance, `c·0/μ = 0 ≤ v_lo + n_lo·σ(0,0)`. The lower end is read off
`collapse_defianceExistenceSet`. The affine window's counterpart is `aw_exact_thresholds`.
AFFINE BY HYPOTHESIS (`d_lo = d_hi`). -/
theorem collapse_exact_thresholds (hInt : E.Interior) (hSR : E.StageRelief)
    (hP : E.Placable) (hSigV : E.SigV = 0) (hτ : E.τx = 0) (hQ : E.Qbar = E.q)
    (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c) (hv : E.vlo = E.vhi)
    (hnhi : E.nhi = 0) (hd : E.dlo = E.dhi) (hβ1 : E.betaStar < 1) :
    E.defianceExistenceSet = Ico (sInf E.defianceExistenceSet) 1 ∧
      sInf E.defianceExistenceSet = E.betaStar := by
  have hset := collapse_defianceExistenceSet hInt hSR hP hSigV hτ hQ hk hℓ hp hv hnhi hd
  have hinf : sInf E.defianceExistenceSet = E.betaStar := by
    rw [hset]
    exact csInf_Ico hβ1
  refine ⟨?_, hinf⟩
  set E' := E.collapseRecert hSigV hd with hE'
  have hL : E'.Lresp = 0 := E'.collapse_Lresp' rfl hτ rfl rfl
  have hsame : E'.toChordEconomyRelief.defianceExistenceSet = E.defianceExistenceSet := rfl
  have hbal : E'.c * (E'.Lresp / E'.mu) ≤ E'.vlo + E'.nlo * E'.sfloor := by
    rw [hL, zero_div, mul_zero]
    have := mul_nonneg E'.hnlo E'.sfloor_mem.1
    linarith [E'.hvlo]
  have h := E'.toChordEconomyRelief.defianceExistenceSet_eq_Ico
    (E'.toChordEconomyRelief.responsePath_monotoneOn_of_Lresp_eq_zero hL) hbal
    (by rw [hsame, hinf]; exact betaStar_pos_of_collapse hSR hQ hk hℓ hp)
  rwa [hsame] at h

end ChordEconomyRelief

/-! ## 4. Rule 9: the collapse members -/

variable {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)

/-- **The nine-condition instance at the collapse members** (Rule 9: the hypotheses of
`collapse_defianceExistenceSet` hold together). At every member `collapseAffine b` of
`PlacableSenderCollapseWitness.lean` (affine law at rate `1/2`, `β_T* = 2/11`) the discounts
with a full-defiance equilibrium are exactly `[2/11, 1)`, so `β_D = 2/11`. AFFINE: the
members' transition is `affineF (1/2)`. -/
theorem collapseAffine_defianceExistenceSet :
    (collapseAffine b hb0 hb1).defianceExistenceSet = Ico (2 / 11) 1 ∧
      sInf (collapseAffine b hb0 hb1).defianceExistenceSet = 2 / 11 := by
  obtain ⟨h1, -, h3, -, -, -, h7, h8, h9, h10, h11, h12, -, h14⟩ :=
    collapseAffine_collapse hb0 hb1
  have hset := (collapseAffine b hb0 hb1).toChordEconomyRelief.collapse_defianceExistenceSet
    (collapseAffine_interior hb0 hb1) (collapseAffine_stageRelief hb0 hb1)
    (collapseAffine_placable hb0 hb1)
    h1 h3 h7 h8 h9 h10 h11 h12 h14
  rw [ChordEconomyCs.defianceExistenceSet_eq_toChordEconomy, hset, collapseAffine_betaStar]
  exact ⟨rfl, csInf_Ico (by norm_num)⟩

end

#print axioms Sanctions.Examples.stateChordBandAll_of_eqOn_affineF
#print axioms Sanctions.Examples.jointSemiconcaveOn_of_eqOn_affineF
#print axioms Sanctions.Examples.semiconvexOnSet_state_of_eqOn_affineF
#print axioms Sanctions.Examples.semiconvexOnSet_sanction_of_eqOn_affineF
#print axioms Sanctions.Examples.mixedChordBound_of_eqOn_affineF
#print axioms Sanctions.Examples.chKS_le_of_le
#print axioms Sanctions.Examples.ChordEconomy.one_sub_dhi_le_ghi
#print axioms Sanctions.Examples.ChordEconomyRelief.collapseRecert
#print axioms Sanctions.Examples.ChordEconomyRelief.collapseRecert_interior
#print axioms Sanctions.Examples.ChordEconomyRelief.collapseRecert_placable
#print axioms Sanctions.Examples.ChordEconomyRelief.collapse_equilibrium_threshold_le_tight
#print axioms Sanctions.Examples.ChordEconomyRelief.betaStar_pos_of_collapse
#print axioms Sanctions.Examples.ChordEconomyRelief.collapse_defianceExistenceSet
#print axioms Sanctions.Examples.ChordEconomyRelief.collapse_exact_thresholds
#print axioms Sanctions.Examples.collapseAffine_defianceExistenceSet

end Examples
end Sanctions
