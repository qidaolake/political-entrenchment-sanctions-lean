/-
Sanctions/Examples/ChordEconomy.lean

**The chord economy: the placable-Sender class with both stage payoffs
abstract** (round AU, 2026-09-25; doc 104, the rate-bound programme; sign-offs
M1–M4 given on the user's word, 2026-09-25).

## What this file is

A `ChordEconomy` is an abstract game `AbstractGame.Params` — both stage payoffs
`U_S`, `U_T` free functions on `ℝ³`, a continuous stage-argmax selector `σ`
(its joint continuity is the class's own field `σ_continuous` since renovation
round BJ5.1), a general transition `F` — together with **rate conditions**. Every
place a proof of the placable programme used to read the quadratic–linear forms

```
U_S(x, a, s) = −(q/2)·s² + s·(u₀ − k·a + r·x) + w·x
U_T(x, a, s) = −ℓ·a + s·(n·x − c) + v·x
```

now reads a one-sided bound instead (the inventory of doc 104 §2–§4, all 35
consumer files). The conditions come in **lower/upper pairs**:

* the Sender's state slope `w_lo ≤ ∂ₓU_S ≤ w_hi` (the lower bound at every
  compliance level, the upper one at full defiance, as are the state moduli
  `σ_x`, `τ_x`);
* its sanction curvature `q ≤ −∂²ₛU_S ≤ Q̄` (strong concavity and a ceiling);
* its state–sanction cross rate (the rally): at least `r_lo` at full defiance,
  at most `r_hi` in absolute value at every compliance level;
* its placation rate `k_lo ≤ −∂²ₐₛU_S ≤ k_hi`;
* its marginal return to the first unit of sanction, `u_lo` (the floor) and
  `u_hi` (the appetite);
* the Target's compliance cost `ℓ_lo ≤ −∂ₐU_T ≤ ℓ_hi`;
* its sanction pain `p_lo ≤ −∂ₛU_T ≤ c`;
* its state slope `v_lo + n_lo·s ≤ ∂ₓU_T ≤ v_hi + n_hi·s` at sanction `s`:
  sanction-indexed bounds on the value of entrenchment. They are envelopes, not
  cross rates: they do not sign `∂²ₓₛU_T`, so they do not say that entrenchment
  softens the sanction's marginal pain, and `n_lo > n_hi` is allowed (the quartic
  member has it). On the family `n_lo = n_hi = n` is the rally softening of the
  pain, a genuine cross rate there (the outside reader's A3, 2026-09-27).

A pair with equal ends pins the functional form in that coordinate, exactly as
`dlo = dhi` pins an affine transition on the square (proved:
`F_eq_affineF_of_tight_sanction`, `ChordEconomyTightChords.lean`; CLAUDE.md
Rule 3, the transition-class clause: where a named scalar carries generality,
name it). Two moduli are new:
the Sender's state semiconcavity `σ_x` and semiconvexity `τ_x`, zero before
because the Sender payoff was affine in the state. Every condition is written
directly over `U_S`, `U_T` and a named scalar — no opaque `Prop` field (Rule 14).

The quadratic–linear family `PlacableEconomyF` is an instance
(`PlacableEconomyF.toChord`, `PlacableSenderFamilyF.lean`). Its pairs are tight
except three: the Sender's state slope (`w_lo = w`, `w_hi = w + r`), its marginal
return to the first unit of sanction (`u_lo = u₀`, `u_hi = u₀ + r`), and the
Target's pain (`p_lo = c − n`, upper rate `c`).

## What is *not* a field

* The two payoff bounds are **suprema over the cube** (sign-off M1): `MU`, `MT₀`
  below, which exist by continuity on a compact set.
* **Zero-sanction neutrality** — a concession is worth nothing to the Sender when
  it imposes no sanction, `U_S(x,a,0) = U_S(x,0,0)` — is the predicate
  `ZeroSanctionNeutral`, a hypothesis of the relief-side theorems only
  (sign-off M2). Its one-sided forms are what the all-equilibria wedge floor
  (`ZeroSanctionAntitone`: at zero sanction the Sender's payoff is nonincreasing
  in compliance) and relief participation (`ZeroSanctionNoGain`: no compliance
  level beats defiance at zero sanction) read. The defiance side and the
  monotone-class uniqueness never see any of them.
* Placability and the loss-offset margin stay hypotheses of the results that
  read them (round AP).
* **Interiority** (`Interior`: the appetite `A = u_hi + β_S·K_S·d_hi` is below
  the curvature `q`) and the **stage relief margin**
  (`ChordEconomyRelief.StageRelief`: `ℓ_hi·Q̄ < k_lo·p_lo`) are hypotheses of the
  results that read them, since round BC (2026-09-29; doc 110 R4). Until then
  they were fields.

## The relief extension

Round BC (doc 110 R5) split the class in two. The base `ChordEconomy` carries
the defiance side: the Target's lower compliance cost `ℓ_lo`, its upper pain
`c` and its lower state envelope `v_lo + n_lo·s`. `ChordEconomyRelief` adds the
rates only the relief side reads: `ℓ_hi` (T3), `p_lo > 0` (T5), the upper state
envelope `v_hi + n_hi·s` (T7), and the Sender's upper cross rate `r_hi` at every
compliance level (S9). `ChordEconomyCs` extends `ChordEconomyRelief`. The lower
and upper pairs listed above are therefore split across the structures.

## The two-sided extension and the placation ceiling (round BJ)

Renovation round BJ (2026-10-07; audit items X1-1, X1-2, X1-4; checklist 14, 15
and 17, user-approved) slimmed the base class three ways.

* **BJ3.1.** The two-sided curvature data leave the base class for
  `ChordEconomyTwoSided`, which `ChordEconomyRelief` now extends: the Sender's
  state semiconvexity modulus `τ_x` with S7, the transition's state-section
  semiconvexity `M_cx` and its mixed chord `M_mix`. Two carriers read them. One is
  the two-sided carrier (`carrierS2`, modulus `σ_C`), with what is built on it: the
  rally margin route to a monotone response and the response Lipschitz constant
  `L_resp`. The other is the policy-class carrier of `PlacableSenderPolicyClass.lean`
  (`carrierPol`, whose modulus `SigCpol` reads `M_cx`), with the margin of its
  increasing-differences step, which reads `M_mix`: the route to a monotone rule from
  conditions on the policy.
* **BJ2.2.** The upper placation rate (S10u) is the predicate
  `PlacationCeiling k_hi`, a hypothesis of the base results that read it; the
  rate `k_hi` and its field move to `ChordEconomyRelief`.
* **BJ2.1.** `q > 0` is a theorem (`hq`), derived from the curvature margin.

Every member exhibited in the tree satisfies the two-sided extension and the
placation ceiling, so this extra generality of the base class is unwitnessed
(Rule 9B): the base results say more than before only once a member outside
those extensions is exhibited.

## Scope in compliance

The stage payoffs are functions on `ℝ³` because `Params` is; the conditions
constrain them on the cube `[0,1]³`, with one exception: strong concavity in the
sanction (S4) is required at **every real** compliance level, because the
state-local argmax-uniqueness predicate `DynamicArgmaxUnique` of the abstract
layer quantifies over all `a`. Off `[0,1]` compliance is formal; an instance may
clip it.

## The carrier

As in the quadratic family (rounds F–AP): the Sender carrier
`{‖V‖ ≤ M_S, K_S-Lipschitz, g_S-lower-slope, SigV-semiconcave}`, now with
`K_S = w_hi/(1 − β_S g_hi)`, `g_S = w_lo/(1 − β_S g_lo)`, `M_S = 2·M_U/(1 − β_S)`,
and the Riccati closure's constant term raised by the stage state modulus
`σ_x ≥ 0` (sign-off M4: a Sender strongly concave in the state satisfies the
condition with `σ_x = 0`, the positive part). The two-sided carrier, on
`ChordEconomyTwoSided`, adds `SigC`-semiconvexity
with `SigC = (τ_x + β_S K_S M_cx)/(1 − β_S g_hi²)`.
-/
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralF
import Sanctions.Foundations.SemiconcaveJointComposition
import Sanctions.Foundations.StrongConcaveArgmaxStability
import Sanctions.Foundations.SemiconvexComposition
import Sanctions.Foundations.CrossDifferenceSemiconvex
import Sanctions.Theory.LockIn.SenderInvestment
import Sanctions.Theory.Mechanism.ContinuationChangesChoice
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFCertificate

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords

noncomputable section

/-! ## 0. Scalar constants and the Riccati algebra (payoff-independent)

`plMu`, `plRho`, `plRicD/A/Q/C/H` and `riccati_feasible_iff` moved here from
`PlacableSenderFamilyF.lean` (round AU), unchanged: they never depended on the
payoff form. The state modulus of the closure, which the quadratic family fixed
at zero, is now the argument `σx` of `chSig`, `chSigImg`, `chRicB`, `chRicL`,
`chRicN`. -/

/-- Strong-concavity modulus of the Sender's dynamic objective in the
sanction: its own curvature `q` less the continuation's sanction curvature. -/
def plMu (βS q SigV dhi KS Ms : ℝ) : ℝ := q - βS * (SigV * dhi ^ 2 + KS * Ms)

/-- Cross modulus of the Sender's dynamic objective in `(x, s)`. -/
def plRho (βS r SigV ghi dhi KS Mm : ℝ) : ℝ := r + βS * (SigV * ghi * dhi + KS * Mm)

/-- `K_S = w_hi/(1 − β_S·g_hi)`: the stage payoff's state-Lipschitz rate
compounded through the transition's upper state chord. -/
def chKS (βS ghi whi : ℝ) : ℝ := whi / (1 - βS * ghi)

/-- `g_S = w_lo/(1 − β_S·g_lo)`: the stage payoff's lower state slope compounded
through the lower state chord. -/
def chGS (βS glo wlo : ℝ) : ℝ := wlo / (1 - βS * glo)

/-- State modulus of the Sender's dynamic objective in `(x, s)`: the stage's
own state semiconcavity `σx` plus the continuation's. -/
def chSig (βS σx SigV ghi KS Mx : ℝ) : ℝ := σx + βS * (SigV * ghi ^ 2 + KS * Mx)

/-- Semiconcavity of the Sender Bellman image, the Schur modulus `σ + ρ²/μ`,
with the stage state modulus `σx`. At `σx = 0` it is the quadratic family's
`plSigImg`. -/
def chSigImg (βS q rhi σx SigV ghi dhi KS Mx Mm Ms : ℝ) : ℝ :=
  chSig βS σx SigV ghi KS Mx
    + plRho βS rhi SigV ghi dhi KS Mm ^ 2 / plMu βS q SigV dhi KS Ms

/-- The carrier's semiconvexity modulus: the fixed point of the linear closure
`σ ↦ τx + β_S(σ·g_hi² + K_S·M_cx)`. Zero when the stage is convex in the state
(`τx = 0`) and the transition's state sections are convex (`M_cx = 0`). -/
def chSigC (βS τx KS Mcx ghi : ℝ) : ℝ := (τx + βS * KS * Mcx) / (1 - βS * ghi ^ 2)

/-- `D = β_S d_hi²`. -/
def plRicD (βS dhi : ℝ) : ℝ := βS * dhi ^ 2
/-- `a = β_S g_hi²`. -/
def plRicA (βS ghi : ℝ) : ℝ := βS * ghi ^ 2
/-- `Q = q − β_S K_S M_s`. -/
def plRicQ (βS q KS Ms : ℝ) : ℝ := q - βS * KS * Ms
/-- `C₀ = r + β_S K_S M_m`. -/
def plRicC (βS r KS Mm : ℝ) : ℝ := r + βS * KS * Mm
/-- `H₀ = β_S g_hi d_hi`. -/
def plRicH (βS ghi dhi : ℝ) : ℝ := βS * ghi * dhi
/-- `B₀ = σx + β_S K_S M_x` (the stage state modulus enters here). -/
def chRicB (βS σx KS Mx : ℝ) : ℝ := σx + βS * KS * Mx
/-- `L = (1 − a)Q + B₀D − 2C₀H₀`. -/
def chRicL (βS q rhi σx ghi dhi KS Mx Mm Ms : ℝ) : ℝ :=
  (1 - plRicA βS ghi) * plRicQ βS q KS Ms + chRicB βS σx KS Mx * plRicD βS dhi
    - 2 * plRicC βS rhi KS Mm * plRicH βS ghi dhi
/-- `N = B₀Q + C₀²`. -/
def chRicN (βS q rhi σx KS Mx Mm Ms : ℝ) : ℝ :=
  chRicB βS σx KS Mx * plRicQ βS q KS Ms + plRicC βS rhi KS Mm ^ 2

/-- **The scalar core.** A downward quadratic `((1 − a)t − B₀)(Q − Dt) − (C₀ + H₀t)²`
is nonnegative at some `t ≥ 0` with `Dt < Q` exactly when `Q > 0`, `0 < L < 2Q`
and `L² ≥ 4DN`; the vertex `L/(2D)` is then such a `t`. -/
theorem riccati_feasible_iff {a D Q B₀ C₀ H₀ : ℝ} (hD : 0 < D) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hB : 0 ≤ B₀) (hC : 0 ≤ C₀) (hH : 0 ≤ H₀) (hHaD : H₀ ^ 2 = a * D) :
    (∃ t : ℝ, 0 ≤ t ∧ D * t < Q ∧
        (C₀ + H₀ * t) ^ 2 ≤ ((1 - a) * t - B₀) * (Q - D * t)) ↔
      (0 < Q ∧ 0 < (1 - a) * Q + B₀ * D - 2 * C₀ * H₀ ∧
        (1 - a) * Q + B₀ * D - 2 * C₀ * H₀ < 2 * Q ∧
        4 * D * (B₀ * Q + C₀ ^ 2) ≤ ((1 - a) * Q + B₀ * D - 2 * C₀ * H₀) ^ 2) := by
  set L := (1 - a) * Q + B₀ * D - 2 * C₀ * H₀ with hL
  set N := B₀ * Q + C₀ ^ 2 with hN
  have hid : ∀ t : ℝ, ((1 - a) * t - B₀) * (Q - D * t) - (C₀ + H₀ * t) ^ 2
      = -D * t ^ 2 + L * t - N := by
    intro t; rw [hL, hN]; linear_combination (-(t ^ 2)) * hHaD
  constructor
  · rintro ⟨t, ht0, hDt, hcl⟩
    have hp : 0 ≤ -D * t ^ 2 + L * t - N := by rw [← hid]; linarith
    have hDt0 : 0 ≤ D * t := mul_nonneg hD.le ht0
    have hQpos : 0 < Q := by linarith
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have hB_le : B₀ ≤ (1 - a) * t := by
      by_contra hcon
      have hneg : (1 - a) * t - B₀ < 0 := by linarith [not_le.mp hcon]
      have hpos : 0 < Q - D * t := by linarith
      have := mul_neg_of_neg_of_pos hneg hpos
      nlinarith [sq_nonneg (C₀ + H₀ * t)]
    have hLpos : 0 < L := by
      rcases eq_or_lt_of_le ht0 with h0 | hpos
      · rw [← h0] at hp
        have hNz : N = 0 := by nlinarith
        have hC0 : C₀ = 0 := by
          have h2 : C₀ ^ 2 = 0 := by nlinarith [mul_nonneg hB hQpos.le]
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        have hB0 : B₀ = 0 := by
          have h2 : B₀ * Q = 0 := by nlinarith [hC0]
          rcases mul_eq_zero.mp h2 with h | h
          · exact h
          · linarith
        rw [hL, hB0, hC0]; nlinarith [mul_pos (sub_pos.2 ha1) hQpos]
      · by_contra hcon
        have hL0 : L ≤ 0 := not_lt.mp hcon
        have h1 : L * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL0 hpos.le
        have h2 : 0 < D * t ^ 2 := by positivity
        nlinarith
    have hL2Q : L < 2 * Q := by
      have h1 : B₀ * D ≤ (1 - a) * t * D := mul_le_mul_of_nonneg_right hB_le hD.le
      have h2 : (1 - a) * (D * t) < (1 - a) * Q :=
        mul_lt_mul_of_pos_left hDt (by linarith)
      have h3 : 0 ≤ C₀ * H₀ := mul_nonneg hC hH
      have h4 : 0 ≤ a * Q := mul_nonneg ha0 hQpos.le
      rw [hL]; nlinarith
    have hdisc : 4 * D * N ≤ L ^ 2 := by
      have h1 : 0 ≤ D * (-D * t ^ 2 + L * t - N) := mul_nonneg hD.le hp
      nlinarith [sq_nonneg (2 * D * t - L)]
    exact ⟨hQpos, hLpos, hL2Q, hdisc⟩
  · rintro ⟨hQpos, hLpos, hL2Q, hdisc⟩
    have h2D : 0 < 2 * D := by positivity
    set t := L / (2 * D) with ht_def
    have ht : t * (2 * D) = L := div_mul_cancel₀ _ h2D.ne'
    refine ⟨t, div_nonneg hLpos.le h2D.le, ?_, ?_⟩
    · have hDt : D * t = L / 2 := by linarith [ht]
      rw [hDt]; linarith
    · rw [← sub_nonneg, hid]
      have hkey : 4 * D * (-D * t ^ 2 + L * t - N) = L ^ 2 - 4 * D * N := by
        linear_combination (-(2 * D * t - L)) * ht
      have hpos : 0 < 4 * D := by positivity
      nlinarith [hkey, hdisc, hpos]

/-- **Closure with its denominator cleared**, with the stage state modulus. -/
theorem chSigImg_le_iff_cleared {βS q rhi σx t ghi dhi KS Mx Mm Ms : ℝ}
    (hμ : 0 < plMu βS q t dhi KS Ms) :
    chSigImg βS q rhi σx t ghi dhi KS Mx Mm Ms ≤ t ↔
      (plRicC βS rhi KS Mm + plRicH βS ghi dhi * t) ^ 2
        ≤ ((1 - plRicA βS ghi) * t - chRicB βS σx KS Mx)
            * (plRicQ βS q KS Ms - plRicD βS dhi * t) := by
  have e1 : plRho βS rhi t ghi dhi KS Mm = plRicC βS rhi KS Mm + plRicH βS ghi dhi * t := by
    unfold plRho plRicC plRicH; ring
  have e2 : t - chSig βS σx t ghi KS Mx = (1 - plRicA βS ghi) * t - chRicB βS σx KS Mx := by
    unfold chSig plRicA chRicB; ring
  have e3 : plMu βS q t dhi KS Ms = plRicQ βS q KS Ms - plRicD βS dhi * t := by
    unfold plMu plRicQ plRicD; ring
  unfold chSigImg
  rw [← e1, ← e2, ← e3]
  constructor
  · intro h
    have h1 : plRho βS rhi t ghi dhi KS Mm ^ 2 / plMu βS q t dhi KS Ms
        ≤ t - chSig βS σx t ghi KS Mx := by linarith
    exact (div_le_iff₀ hμ).mp h1
  · intro h
    have h1 := (div_le_iff₀ hμ).mpr h
    linarith

/-- **A certificate modulus exists iff the discriminant condition holds**, with
the stage state modulus `σx ≥ 0` in `B₀` (round AU; the quadratic family's
`sigV_feasible_iff` is the case `σx = 0`). -/
theorem chSigV_feasible_iff {βS q rhi σx ghi dhi KS Mx Mm Ms : ℝ}
    (hβS : 0 < βS) (hdhi : 0 < dhi) (hghi : 0 ≤ ghi) (ha : βS * ghi ^ 2 < 1)
    (hKS : 0 ≤ KS) (hMx : 0 ≤ Mx) (hMm : 0 ≤ Mm) (hr : 0 ≤ rhi) (hσx : 0 ≤ σx) :
    (∃ t : ℝ, 0 ≤ t ∧ βS * (t * dhi ^ 2 + KS * Ms) < q ∧
        chSigImg βS q rhi σx t ghi dhi KS Mx Mm Ms ≤ t) ↔
      (0 < plRicQ βS q KS Ms ∧ 0 < chRicL βS q rhi σx ghi dhi KS Mx Mm Ms ∧
        chRicL βS q rhi σx ghi dhi KS Mx Mm Ms < 2 * plRicQ βS q KS Ms ∧
        4 * plRicD βS dhi * chRicN βS q rhi σx KS Mx Mm Ms
          ≤ chRicL βS q rhi σx ghi dhi KS Mx Mm Ms ^ 2) := by
  have hD : 0 < plRicD βS dhi := by unfold plRicD; positivity
  have ha0 : 0 ≤ plRicA βS ghi := by unfold plRicA; positivity
  have ha1 : plRicA βS ghi < 1 := by unfold plRicA; exact ha
  have hB : 0 ≤ chRicB βS σx KS Mx := by unfold chRicB; positivity
  have hC : 0 ≤ plRicC βS rhi KS Mm := by unfold plRicC; positivity
  have hH : 0 ≤ plRicH βS ghi dhi := by unfold plRicH; positivity
  have hHaD : plRicH βS ghi dhi ^ 2 = plRicA βS ghi * plRicD βS dhi := by
    unfold plRicH plRicA plRicD; ring
  have hcurv : ∀ t : ℝ, (βS * (t * dhi ^ 2 + KS * Ms) < q) ↔
      plRicD βS dhi * t < plRicQ βS q KS Ms := by
    intro t; unfold plRicD plRicQ; constructor <;> intro h <;> linarith
  have hμ : ∀ t : ℝ, plRicD βS dhi * t < plRicQ βS q KS Ms → 0 < plMu βS q t dhi KS Ms := by
    intro t h; unfold plMu; unfold plRicD plRicQ at h; linarith
  have core := riccati_feasible_iff (Q := plRicQ βS q KS Ms) hD ha0 ha1 hB hC hH hHaD
  unfold chRicL chRicN
  rw [← core]
  constructor
  · rintro ⟨t, ht0, hc, hcl⟩
    have hDt := (hcurv t).mp hc
    exact ⟨t, ht0, hDt, (chSigImg_le_iff_cleared (hμ t hDt)).mp hcl⟩
  · rintro ⟨t, ht0, hDt, hq⟩
    exact ⟨t, ht0, (hcurv t).mpr hDt, (chSigImg_le_iff_cleared (hμ t hDt)).mpr hq⟩

/-- `σ_V ≥ 0` from the Riccati closure with the curvature margin, for any
nonnegative `K_S` and stage state modulus `σx ≥ 0`. -/
theorem chSigV_nonneg_of_closure {βS q rhi σx SigV ghi dhi KS Mx Mm Ms : ℝ}
    (hβS0 : 0 < βS) (hβS1 : βS < 1) (hghi0 : 0 ≤ ghi) (hghi1 : ghi ≤ 1)
    (hKS : 0 ≤ KS) (hMx : 0 ≤ Mx) (hσx : 0 ≤ σx)
    (hCurv : βS * (SigV * dhi ^ 2 + KS * Ms) < q)
    (hSigV : chSigImg βS q rhi σx SigV ghi dhi KS Mx Mm Ms ≤ SigV) : 0 ≤ SigV := by
  have hmu : 0 < plMu βS q SigV dhi KS Ms := by unfold plMu; linarith
  have hsq : 0 ≤ plRho βS rhi SigV ghi dhi KS Mm ^ 2 / plMu βS q SigV dhi KS Ms :=
    div_nonneg (sq_nonneg _) hmu.le
  have hMx' : 0 ≤ βS * (KS * Mx) := mul_nonneg hβS0.le (mul_nonneg hKS hMx)
  have hsq1 : ghi ^ 2 ≤ 1 := by nlinarith
  have hcoef : 0 < 1 - βS * ghi ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq1 hβS0.le
    linarith
  unfold chSigImg chSig at hSigV
  have key : 0 ≤ (1 - βS * ghi ^ 2) * SigV := by nlinarith
  by_contra hneg
  have := mul_neg_of_pos_of_neg hcoef (not_le.mp hneg)
  linarith

/-! ## 1. The structure -/

/-- **A chord economy.** An abstract game (`AbstractGame.Params`: both stage
payoffs free, a stage-argmax selector, a general transition) whose selector is
jointly continuous (`σ_continuous`), with chord regularity on the transition, rate
conditions on both payoffs, and a
supplied Sender-carrier modulus with its curvature and Riccati closure. See the
file header for the reading of each condition. Interiority (`Interior`) and the
stage relief margin (`ChordEconomyRelief.StageRelief`) were fields until round
BC (2026-09-29, doc 110 R4); they are now hypotheses of the results that read
them. The relief-side rates are in `ChordEconomyRelief`. Since renovation round BJ
(2026-10-07) the two-sided curvature data are in `ChordEconomyTwoSided` (BJ3.1), the
upper placation rate is the predicate `PlacationCeiling` (BJ2.2), and `q > 0` is the
theorem `hq`, derived from the curvature margin (BJ2.1).

**Generality (Rule 9B).** The base class is strictly larger than the relief
extension: `ChordEconomyBaseOnlyWitness.lean` (renovation item BH5.6(b)) exhibits a
member whose Target feels no sanction pain at the top state. Every member exhibited in
the tree satisfies the two-sided extension and the placation ceiling, so the further
generality that BJ3.1 and BJ2.2 give the base class is as yet unwitnessed: the theorems
stated over it are true, and they say more than their predecessors only once a member
outside those extensions is exhibited. -/
structure ChordEconomy extends AbstractGame.Params where
  /-- **The Sender's static best response varies continuously with the state and the
  compliance level**, jointly on `ℝ × ℝ`. General in `F`. It was a field of
  `AbstractGame.Params` until renovation round BJ5.1 (2026-10-07, user-approved,
  checklist 21), which made it the class `Params.StaticSelectorContinuous`. It is kept on
  the chord class, with the same name and statement, because the class's four-cell and
  regime results compare against the static Sender; it supplies the instance
  `ChordEconomy.staticSelectorContinuous`. This relocates an existing condition: the
  chord class assumes exactly what it did before. -/
  σ_continuous : Continuous (fun (xa : ℝ × ℝ) => σ xa.1 xa.2)
  -- The transition's chords (as on the quadratic family).
  /-- Lower and upper state chords, sanction chords, joint-curvature moduli. -/
  glo : ℝ
  ghi : ℝ
  dlo : ℝ
  dhi : ℝ
  Mx : ℝ
  Mm : ℝ
  Ms : ℝ
  hbandAll : StateChordBandAll F glo ghi
  hSlo : SanctionLowerChord F dlo
  hShi : SanctionUpperChord F dhi
  hFjsc : JointSemiconcaveOn F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) Mx Mm (-Ms)
  hglo0 : 0 ≤ glo
  hghi1 : ghi ≤ 1
  hdlo0 : 0 < dlo
  hMx0 : 0 ≤ Mx
  hMm0 : 0 ≤ Mm
  hMs0 : 0 ≤ Ms
  /-- Both governments discount strictly. -/
  hβS0 : 0 < β_S
  hβT0 : 0 < β_T
  -- The Sender's rates.
  /-- Lower and upper state slopes of the Sender's stage payoff. -/
  wlo : ℝ
  whi : ℝ
  /-- Sanction curvature: strong concavity `q` and ceiling `Qbar`. -/
  q : ℝ
  Qbar : ℝ
  /-- State semiconcavity modulus of the Sender's stage payoff (the semiconvexity
  modulus `τx` is in the two-sided extension). -/
  σx : ℝ
  /-- Lower and upper state–sanction cross rates (the Sender's rally). -/
  rlo : ℝ
  rhi : ℝ
  /-- Lower placation rate (the upper rate `khi` is in the relief extension; on the
  base class it is the predicate `PlacationCeiling`). -/
  klo : ℝ
  /-- The appetite and the floor: upper and lower marginal return to the first
  unit of sanction at full defiance. -/
  uhi : ℝ
  ulo : ℝ
  /-- **S2. State Lipschitz at defiance**: the stage payoff moves at most `w_hi`
  per unit of state. -/
  hUS_stateLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
    |U_S x₂ 0 s - U_S x₁ 0 s| ≤ whi * |x₂ - x₁|
  /-- **S3. State lower slope, at every compliance level**: the Sender values
  entrenchment at rate at least `w_lo > 0`. -/
  hUS_stateSlope : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, x₁ ≤ x₂ → wlo * (x₂ - x₁) ≤ U_S x₂ a s - U_S x₁ a s
  /-- **S4. Strong concavity in the sanction**, at every state and every real
  compliance level (see the header on scope). -/
  hUS_concave : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a : ℝ,
    SemiconcaveOnSet (fun s => U_S x a s) (Icc (0 : ℝ) 1) (-q)
  /-- **S5. Curvature ceiling in the sanction**: `U_S(x,a,·)` is
  `Qbar`-semiconvex. -/
  hUS_convex : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    SemiconvexOnSet (fun s => U_S x a s) (Icc (0 : ℝ) 1) Qbar
  /-- **S6. Joint semiconcavity at defiance** in (state, sanction), with state
  modulus `σx`, cross modulus `rhi`, sanction concavity `q`. -/
  hUS_joint : JointSemiconcaveOn (fun x s => U_S x 0 s) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
    σx rhi q
  /-- **S8. Increasing differences at defiance**: the rally raises the marginal
  return to sanctioning at rate at least `r_lo`. -/
  hUS_crossLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ s' ∈ Icc (0 : ℝ) 1, x ≤ x' → s ≤ s' →
      rlo * ((x' - x) * (s' - s)) ≤ (U_S x' 0 s' - U_S x' 0 s) - (U_S x 0 s' - U_S x 0 s)
  /-- **S10. Placation**: compliance lowers the marginal return to sanctioning
  at rate at least `k_lo > 0` (decreasing differences in compliance and
  sanction). -/
  hUS_placLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' → s ≤ s' →
      (U_S x a' s' - U_S x a' s) - (U_S x a s' - U_S x a s) ≤ -(klo * ((a' - a) * (s' - s)))
  /-- **S11. The appetite**: at defiance the marginal return to sanctioning is at
  most `u_hi`, in the chord form with the curvature `q`. -/
  hUS_appetite : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
    (s - t) * (q * (s + t) / 2 - uhi) ≤ U_S x 0 t - U_S x 0 s
  /-- **S12. The floor**: at defiance the marginal return to sanctioning is at
  least `u_lo`, in the chord form with the ceiling `Qbar`. -/
  hUS_floor : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
    (s - t) * (ulo - Qbar * (s + t) / 2) ≤ U_S x 0 s - U_S x 0 t
  hwlo : 0 < wlo
  hσx0 : 0 ≤ σx
  hrlo : 0 ≤ rlo
  hklo : 0 < klo
  hulo : 0 < ulo
  -- The Target's rates.
  /-- Lower compliance cost rate (the upper rate `ℓhi` is in the relief
  extension). -/
  ℓlo : ℝ
  /-- Upper sanction pain rate (the lower rate `plo` is in the relief
  extension). -/
  c : ℝ
  /-- State slope `vlo + nlo·s` from below: a sanction-indexed envelope on the
  value of entrenchment, not a cross rate (on the family, `nlo = n` is the rally
  softening of the pain). The upper envelope is in the relief extension. -/
  vlo : ℝ
  nlo : ℝ
  /-- **T2. Compliance costs at least `ℓ_lo > 0` per unit.** -/
  hUT_costLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1,
    ∀ a₂ ∈ Icc (0 : ℝ) 1, a₁ ≤ a₂ → U_T x a₂ s - U_T x a₁ s ≤ -(ℓlo * (a₂ - a₁))
  /-- **T4. Sanction pain at most `c` per unit.** -/
  hUT_painHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1,
    ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ → U_T x a s₁ - U_T x a s₂ ≤ c * (s₂ - s₁)
  /-- **T6. State lower slope, indexed by the sanction**: the Target values the
  state at rate at least `v_lo + n_lo·s` at sanction `s`. An envelope, not a
  cross rate: it does not sign how entrenchment moves the sanction's marginal
  pain. -/
  hUT_stateLo : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, x₁ ≤ x₂ → (vlo + nlo * s) * (x₂ - x₁) ≤ U_T x₂ a s - U_T x₁ a s
  hℓlo : 0 < ℓlo
  hvlo : 0 < vlo
  hnlo : 0 ≤ nlo
  -- The carrier modulus and its two margins.
  /-- The supplied Sender-carrier semiconcavity modulus (a derived internal
  handle closed by `hSigV`, Rule 3). -/
  SigV : ℝ
  /-- **Curvature margin.** -/
  hCurv : β_S * (SigV * dhi ^ 2 + chKS β_S ghi whi * Ms) < q
  /-- **Riccati closure**, with the stage state modulus `σx`. -/
  hSigV : chSigImg β_S q rhi σx SigV ghi dhi (chKS β_S ghi whi) Mx Mm Ms ≤ SigV

/-- **Every chord economy has a continuous static Sender selector.** The instance
`Params.StaticSelectorContinuous` for the chord class, read off its field `σ_continuous`
(renovation round BJ5.1, 2026-10-07). The static-Sender regime `10`, the myopic policy and
the stage response read the condition through this instance, so no chord-class statement
changes, and the two-sided, relief and enriched extensions inherit it. General in `F`. -/
instance ChordEconomy.staticSelectorContinuous (E : ChordEconomy) :
    E.toParams.StaticSelectorContinuous :=
  ⟨E.σ_continuous⟩

/-- **The two-sided extension** (renovation item BJ3.1, 2026-10-07; audit item X1-1,
user-approved, checklist 17). The chord economy together with the curvature data that
only the Sender's semiconvex carriers read (the two-sided carrier `carrierS2` and the
policy-class carrier `carrierPol`):
- the transition's state-section semiconvexity `M_cx` (`hFcx`);
- its two-sided mixed chord `M_mix` (`hFmix`);
- the Sender's state semiconvexity modulus `τ_x` at defiance (S7).

They bound the carrier's semiconvexity modulus `σ_C` (`SigC`), and through it the rally
margin route to a monotone response (`responsePath_monotoneOn_of_margin`) and the
response Lipschitz constant `L_resp`. They are also read by the policy-class carrier of
`PlacableSenderPolicyClass.lean`: its semiconvexity modulus `SigCpol` (and so
`carrierPol`) reads `M_cx`, and the margin of its increasing-differences step
(`senderObj_increasingDifferences_pol`, `rule_monotoneOn_of_policy_bounds`,
`unique_equilibrium_of_policy_bounds`) reads `M_mix`. The defiance side, the invariance
of the one-sided carrier `carrierS`, the argmax uniqueness, the Sender's constructed
value and the monotone-response route never read them; until round BJ they were fields
of `ChordEconomy` itself. General in `F`. -/
structure ChordEconomyTwoSided extends ChordEconomy where
  /-- State-section semiconvexity of the transition. -/
  Mcx : ℝ
  hMcx0 : 0 ≤ Mcx
  hFcx : ∀ s ∈ Icc (0 : ℝ) 1, SemiconvexOnSet (fun y => F y s) (Icc (0 : ℝ) 1) Mcx
  /-- Two-sided mixed chord of the transition. -/
  Mmix : ℝ
  hFmix : MixedChordBound F Mmix
  /-- State semiconvexity modulus of the Sender's stage payoff. -/
  τx : ℝ
  /-- **S7. State semiconvexity at defiance.** -/
  hUS_stateConvex : ∀ s ∈ Icc (0 : ℝ) 1,
    SemiconvexOnSet (fun x => U_S x 0 s) (Icc (0 : ℝ) 1) τx
  hτx0 : 0 ≤ τx

/-- **The relief extension** (round BC, 2026-09-29; doc 110 R5, user-approved).
The two-sided chord economy together with the rates that only the relief side of the
bracket reads:
- the Target's upper compliance cost `ℓ_hi` (T3);
- its lower sanction pain `p_lo > 0` (T5);
- its upper state envelope `v_hi + n_hi·s` (T7);
- the Sender's upper state–sanction cross rate `r_hi` at every compliance level
  (S9);
- the Sender's upper placation rate `k_hi` (S10u; renovation item BJ2.2,
  2026-10-07: on the base class it is the predicate `ChordEconomy.PlacationCeiling`).

The defiance side, the monotone-class uniqueness, branch invariance, the sharp
defiance bound and the wedge floor are stated over the base `ChordEconomy` and
never see these fields. Until round BC they were fields of `ChordEconomy`
itself. Since renovation item BJ3.1 (2026-10-07) it extends the two-sided extension
`ChordEconomyTwoSided`, whose curvature data the relief side reads through the
two-sided carrier. -/
structure ChordEconomyRelief extends ChordEconomyTwoSided where
  /-- Upper compliance cost rate. -/
  ℓhi : ℝ
  /-- Lower sanction pain rate. -/
  plo : ℝ
  /-- Upper state envelope `vhi + nhi·s`. -/
  vhi : ℝ
  nhi : ℝ
  /-- Upper placation rate. -/
  khi : ℝ
  /-- **S9. The cross rate is at most `r_hi`, at every compliance level.** -/
  hUS_crossHi : ∀ a ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |(U_S x' a s' - U_S x' a s) - (U_S x a s' - U_S x a s)|
        ≤ rhi * (|x' - x| * |s' - s|)
  /-- **S10u. The placation rate is at most `k_hi`** (renovation item BJ2.2: moved here
  from `ChordEconomy`; it is `ChordEconomy.PlacationCeiling` at `k_hi`,
  `ChordEconomyRelief.placationCeiling`). -/
  hUS_placHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' →
      |(U_S x a' s' - U_S x a' s) - (U_S x a s' - U_S x a s)| ≤ khi * ((a' - a) * |s' - s|)
  /-- **T3. Compliance costs at most `ℓ_hi` per unit.** -/
  hUT_costHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1,
    ∀ a₂ ∈ Icc (0 : ℝ) 1, a₁ ≤ a₂ → -(ℓhi * (a₂ - a₁)) ≤ U_T x a₂ s - U_T x a₁ s
  /-- **T5. Sanction pain at least `p_lo > 0` per unit.** -/
  hUT_painLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1,
    ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ → plo * (s₂ - s₁) ≤ U_T x a s₁ - U_T x a s₂
  /-- **T7. State Lipschitz `v_hi + n_hi·s`** at sanction `s`, the upper
  envelope. -/
  hUT_stateHi : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, |U_T x₂ a s - U_T x₁ a s| ≤ (vhi + nhi * s) * |x₂ - x₁|
  hplo : 0 < plo

/-- **The enriched subclass**: sanction-section semiconvexity of the transition,
read by the relief rate (the reading `01`, the bracket's relief side). Extends
the relief extension, since every result stated over it also reads the relief
rates. -/
structure ChordEconomyCs extends ChordEconomyRelief where
  Mcs : ℝ
  hMcs0 : 0 ≤ Mcs
  hFcs : ∀ x ∈ Icc (0 : ℝ) 1, SemiconvexOnSet (fun s => F x s) (Icc (0 : ℝ) 1) Mcs

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Interiority** (a hypothesis since round BC, 2026-09-29, doc 110 R4; until
then the field `hInterior`). The appetite `A = u_hi + β_S·K_S·d_hi` is below the
curvature `q`: the Sender never sanctions fully. Written over the class's own
data (Rule 14). -/
def Interior : Prop := E.uhi + E.β_S * chKS E.β_S E.ghi E.whi * E.dhi < E.q

/-- **The placation ceiling** (renovation item BJ2.2, 2026-10-07; audit item X1-4,
user-approved, checklist 15; until then the field `hUS_placHi`, S10u). Compliance
changes the Sender's marginal return to sanctioning by at most `khi` in absolute value,
per unit of compliance and per unit of sanction: at every state,
`|Δ_a Δ_s U_S| ≤ khi·(a' − a)·|s' − s|`. The bound is two-sided, so it caps changes in
either direction; with the placation floor S10 the difference is negative, and the
ceiling caps how fast compliance lowers the return. A hypothesis of the base results
that read it; the relief extension carries it as a field
(`ChordEconomyRelief.placationCeiling`). General in `F`. Written over the class's own
data (Rule 14). -/
def PlacationCeiling (khi : ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' →
      |(E.U_S x a' s' - E.U_S x a' s) - (E.U_S x a s' - E.U_S x a s)|
        ≤ khi * ((a' - a) * |s' - s|)

/-! ## 1b. Derived signs and orderings -/

theorem hβS1 : E.β_S < 1 := E.β_S_mem.2
theorem hβT1 : E.β_T < 1 := E.β_T_mem.2

theorem hglo_ghi : E.glo ≤ E.ghi := E.hbandAll.rates_le
theorem hdlo_dhi : E.dlo ≤ E.dhi := sanctionChord_rates_le E.hSlo E.hShi
theorem ghi_nonneg : 0 ≤ E.ghi := le_trans E.hglo0 E.hglo_ghi
theorem dhi_nonneg : 0 ≤ E.dhi := le_trans E.hdlo0.le E.hdlo_dhi

theorem F_maps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, E.F y s ∈ Icc (0 : ℝ) 1 :=
  fun y hy s hs => E.F_mem y s hy hs

theorem zero_mem_I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
theorem one_mem_I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩

/-- `w_lo ≤ w_hi`: the two state rates at defiance, between the states `0` and `1`. -/
theorem wlo_le_whi : E.wlo ≤ E.whi := by
  have h1 := E.hUS_stateSlope 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one
  have h2 := E.hUS_stateLip 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
  simp only [sub_zero, abs_one, mul_one] at h1 h2
  linarith [le_abs_self (E.U_S 1 0 0 - E.U_S 0 0 0)]

theorem whi_pos : 0 < E.whi := lt_of_lt_of_le E.hwlo E.wlo_le_whi

/-- `q ≤ Q̄`: strong concavity and the ceiling, on one chord. -/
theorem q_le_Qbar : E.q ≤ E.Qbar := by
  have h1 := E.hUS_concave 0 zero_mem_I 0 0 zero_mem_I 1 one_mem_I (1 / 2)
    (by norm_num) (by norm_num)
  have h2 := E.hUS_convex 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I (1 / 2)
    (by norm_num) (by norm_num)
  simp only at h1 h2
  nlinarith

/-- `k_lo ≤ k_hi`, for any placation ceiling `k_hi`. General in `F`. Renovation item
BJ2.2 (2026-10-07): the upper placation rate is no longer a field of the base class, so
the ceiling is the hypothesis `hPC`; the relief extension's form, at its field `k_hi`, is
`ChordEconomyRelief.klo_le_khi`. -/
theorem klo_le_khi {khi : ℝ} (hPC : E.PlacationCeiling khi) : E.klo ≤ khi := by
  have h1 := E.hUS_placLo 0 zero_mem_I 0 zero_mem_I 1 one_mem_I 0 zero_mem_I 1
    one_mem_I zero_le_one zero_le_one
  have h2 := hPC 0 zero_mem_I 0 zero_mem_I 1 one_mem_I 0 zero_mem_I 1
    one_mem_I zero_le_one
  simp only [sub_zero, abs_one, mul_one] at h1 h2
  have := neg_abs_le ((E.U_S 0 1 1 - E.U_S 0 1 0) - (E.U_S 0 0 1 - E.U_S 0 0 0))
  linarith

/-- A placation ceiling is positive. General in `F`; the ceiling `hPC` is a hypothesis
since renovation item BJ2.2 (2026-10-07). -/
theorem khi_pos {khi : ℝ} (hPC : E.PlacationCeiling khi) : 0 < khi :=
  lt_of_lt_of_le E.hklo (E.klo_le_khi hPC)

/-- `u_lo ≤ u_hi`: the floor and the appetite at the state `0`, on shrinking
chords from zero. -/
theorem ulo_le_uhi : E.ulo ≤ E.uhi := by
  by_contra hlt
  have hd : 0 < E.ulo - E.uhi := by linarith [not_le.mp hlt]
  set K := (E.Qbar - E.q) / 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith [E.q_le_Qbar]
  set s := min 1 ((E.ulo - E.uhi) / (2 * (K + 1))) with hs_def
  have hs0 : 0 < s := lt_min zero_lt_one (div_pos hd (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, hs1⟩
  have h1 := E.hUS_appetite 0 zero_mem_I 0 zero_mem_I s hsI hs0.le
  have h2 := E.hUS_floor 0 zero_mem_I 0 zero_mem_I s hsI hs0.le
  simp only [sub_zero, add_zero] at h1 h2
  -- `s·(u_lo − Q̄ s/2) ≤ s·(u_hi − q s/2)`, so `u_lo − u_hi ≤ K·s`.
  have h3 : s * (E.ulo - E.Qbar * s / 2) ≤ s * (E.uhi - E.q * s / 2) := by linarith
  have h4 : E.ulo - E.uhi ≤ K * s := by
    have := le_of_mul_le_mul_left h3 hs0
    rw [hK]; linarith
  have h5 : K * s ≤ K * ((E.ulo - E.uhi) / (2 * (K + 1))) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hK0
  have h6 : K * ((E.ulo - E.uhi) / (2 * (K + 1))) < E.ulo - E.uhi := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos hd (by linarith : (0 : ℝ) < K + 2)]
  linarith

theorem uhi_pos : 0 < E.uhi := lt_of_lt_of_le E.hulo E.ulo_le_uhi

/-! ## 2. Derived constants -/

/-- `K_S`. -/
def KS : ℝ := chKS E.β_S E.ghi E.whi
/-- `g_S`. -/
def gS : ℝ := chGS E.β_S E.glo E.wlo
/-- `μ`. -/
def mu : ℝ := plMu E.β_S E.q E.SigV E.dhi E.KS E.Ms
/-- `ρ`. -/
def rho : ℝ := plRho E.β_S E.rhi E.SigV E.ghi E.dhi E.KS E.Mm
/-- The appetite `A = u_hi + β_S·K_S·d_hi`: the upper bound on the Sender's
dynamic marginal return to the first unit of sanction at full defiance. -/
def A : ℝ := E.uhi + E.β_S * E.KS * E.dhi

theorem βS_ghi_lt_one : E.β_S * E.ghi < 1 := by
  have := E.hβS1; have := E.hghi1; have := E.hβS0; have := E.hglo0; have := E.hglo_ghi
  nlinarith

theorem βS_glo_lt_one : E.β_S * E.glo < 1 := by
  have := E.βS_ghi_lt_one; have := E.hβS0; have := E.hglo_ghi
  nlinarith

theorem one_sub_βS_ghi_pos : 0 < 1 - E.β_S * E.ghi := by linarith [E.βS_ghi_lt_one]
theorem one_sub_βS_glo_pos : 0 < 1 - E.β_S * E.glo := by linarith [E.βS_glo_lt_one]

theorem βS_ghi_sq_lt_one : E.β_S * E.ghi ^ 2 < 1 := by
  have h := E.βS_ghi_lt_one
  have hsq : E.ghi ^ 2 ≤ E.ghi := by
    have := mul_nonneg E.ghi_nonneg (sub_nonneg.2 E.hghi1)
    nlinarith
  have := mul_le_mul_of_nonneg_left hsq E.hβS0.le
  linarith

theorem βT_glo_lt_one : E.β_T * E.glo < 1 := by
  have := E.hβT1; have := E.hβT0; have := E.hglo0; have := E.hglo_ghi; have := E.hghi1
  nlinarith

theorem KS_pos : 0 < E.KS := by
  unfold KS chKS
  exact div_pos E.whi_pos E.one_sub_βS_ghi_pos

theorem KS_nonneg : 0 ≤ E.KS := E.KS_pos.le

theorem KS_mul : E.KS * (1 - E.β_S * E.ghi) = E.whi := by
  unfold KS chKS; field_simp [E.one_sub_βS_ghi_pos.ne']

theorem gS_pos : 0 < E.gS := by
  unfold gS chGS
  exact div_pos E.hwlo E.one_sub_βS_glo_pos

theorem gS_mul : E.gS * (1 - E.β_S * E.glo) = E.wlo := by
  unfold gS chGS; field_simp [E.one_sub_βS_glo_pos.ne']

theorem hSigV0 : 0 ≤ E.SigV :=
  chSigV_nonneg_of_closure E.hβS0 E.hβS1 E.ghi_nonneg E.hghi1 E.KS_nonneg E.hMx0 E.hσx0
    E.hCurv E.hSigV

/-- **The Sender's stage payoff is strongly concave in the sanction: `q > 0`**
(renovation item BJ2.1, 2026-10-07; audit item X1-2, user-approved, checklist 14).
General in `F`. Until then `0 < q` was the field `hq`. It follows from the curvature
margin `hCurv`, which puts `q` above `β_S·(σ_V·d_hi² + K_S·M_s)`, a sum of nonnegative
terms (`σ_V ≥ 0` from the Riccati closure, `hSigV0`). In plain terms, the stage
curvature has to beat the continuation's sanction curvature, so it is positive. -/
theorem hq : 0 < E.q := by
  have hc : E.β_S * (E.SigV * E.dhi ^ 2 + E.KS * E.Ms) < E.q := E.hCurv
  have h1 : 0 ≤ E.SigV * E.dhi ^ 2 := mul_nonneg E.hSigV0 (sq_nonneg _)
  have h2 : 0 ≤ E.KS * E.Ms := mul_nonneg E.KS_nonneg E.hMs0
  have h3 : 0 ≤ E.β_S * (E.SigV * E.dhi ^ 2 + E.KS * E.Ms) :=
    mul_nonneg E.hβS0.le (add_nonneg h1 h2)
  linarith

/-- The curvature ceiling is positive (placed after `hq`, renovation item BJ2.1). -/
theorem Qbar_pos : 0 < E.Qbar := lt_of_lt_of_le E.hq E.q_le_Qbar

theorem mu_pos : 0 < E.mu := by
  unfold mu plMu
  have := E.hCurv
  unfold KS; linarith

theorem A_pos : 0 < E.A := by
  unfold A
  have := mul_nonneg (mul_nonneg E.hβS0.le E.KS_nonneg) E.dhi_nonneg
  linarith [E.uhi_pos]

theorem A_lt_q (hInt : E.Interior) : E.A < E.q := by unfold A KS; exact hInt

theorem uhi_lt_q (hInt : E.Interior) : E.uhi < E.q := by
  have := mul_nonneg (mul_nonneg E.hβS0.le E.KS_nonneg) E.dhi_nonneg
  have := E.A_lt_q hInt; unfold A at this; linarith

/-! ### The two payoff bounds, as suprema over the cube (sign-off M1) -/

/-- The cube `[0,1]³`. -/
abbrev cube : Set (ℝ × ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

theorem cube_isCompact : IsCompact cube :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- `M_U`, the Sender's stage payoff bound: `sup |U_S|` over the cube. -/
def MU : ℝ := sSup ((fun p : ℝ × ℝ × ℝ => |E.U_S p.1 p.2.1 p.2.2|) '' cube)

/-- `M_T₀`, the Target's stage payoff bound: `sup |U_T|` over the cube. -/
def MT₀ : ℝ := sSup ((fun p : ℝ × ℝ × ℝ => |E.U_T p.1 p.2.1 p.2.2|) '' cube)

theorem MU_bdd : BddAbove ((fun p : ℝ × ℝ × ℝ => |E.U_S p.1 p.2.1 p.2.2|) '' cube) :=
  (cube_isCompact.image (continuous_abs.comp E.U_S_continuous)).bddAbove

theorem MT₀_bdd : BddAbove ((fun p : ℝ × ℝ × ℝ => |E.U_T p.1 p.2.1 p.2.2|) '' cube) :=
  (cube_isCompact.image (continuous_abs.comp E.U_T_continuous)).bddAbove

theorem abs_U_S_le_MU {x a s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : |E.U_S x a s| ≤ E.MU :=
  le_csSup E.MU_bdd ⟨(x, a, s), ⟨hx, ha, hs⟩, rfl⟩

theorem abs_U_T_le_MT₀ {x a s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : |E.U_T x a s| ≤ E.MT₀ :=
  le_csSup E.MT₀_bdd ⟨(x, a, s), ⟨hx, ha, hs⟩, rfl⟩

theorem MU_nonneg : 0 ≤ E.MU :=
  (abs_nonneg _).trans (E.abs_U_S_le_MU zero_mem_I zero_mem_I zero_mem_I)

theorem MT₀_nonneg : 0 ≤ E.MT₀ :=
  (abs_nonneg _).trans (E.abs_U_T_le_MT₀ zero_mem_I zero_mem_I zero_mem_I)

/-- `M_S = 2·M_U/(1 − β_S)`, the Sender carrier's sup-norm radius. -/
def MS : ℝ := 2 * E.MU / (1 - E.β_S)

/-- `w_lo ≤ 2·M_U`: the lower state slope is bounded by the payoff's range. -/
theorem wlo_le_two_MU : E.wlo ≤ 2 * E.MU := by
  have h1 := E.hUS_stateSlope 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one
  simp only [sub_zero, mul_one] at h1
  have h2 := E.abs_U_S_le_MU one_mem_I zero_mem_I zero_mem_I
  have h3 := E.abs_U_S_le_MU zero_mem_I zero_mem_I zero_mem_I
  linarith [le_abs_self (E.U_S 1 0 0), neg_abs_le (E.U_S 0 0 0)]

/-! ## 3. The stage payoffs: chains through a mixed point -/

/-- **Decreasing differences in `(s, a)`** (placation, S10 with `k_lo ≥ 0`). -/
theorem stage_decreasingDifferences (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => E.U_S x a s) := by
  intro s₁ s₂ a a' hs₁ hs₂ hs ha ha' hle
  have h := E.hUS_placLo x hx a ha a' ha' s₁ hs₁ s₂ hs₂ hle hs
  have : 0 ≤ E.klo * ((a' - a) * (s₂ - s₁)) :=
    mul_nonneg E.hklo.le (mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hs))
  simp only
  linarith

/-- The appetite chord at any compliance level: compliance only lowers the
marginal return (S10), so S11 at defiance bounds every compliance level. -/
theorem stage_chord_slope {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
      (s - t) * (E.q * (s + t) / 2 - E.uhi) ≤ E.U_S x a t - E.U_S x a s := by
  intro t ht s hs hts
  have h0 := E.hUS_appetite x hx t ht s hs hts
  have hdd := E.hUS_placLo x hx 0 zero_mem_I a ha t ht s hs ha.1 hts
  have : 0 ≤ E.klo * ((a - 0) * (s - t)) :=
    mul_nonneg E.hklo.le (mul_nonneg (by linarith [ha.1]) (sub_nonneg.2 hts))
  linarith

/-- The stage payoff is strictly concave in the sanction, at every state and
every real compliance level (S4). -/
theorem stage_strictConcaveOn {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (a : ℝ) :
    StrictConcaveOn ℝ Sanctions.I (fun s => E.U_S x a s) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p₁ p₂ hp₁ hp₂ hsum
  have hp2 : p₂ = 1 - p₁ := by linarith
  subst hp2
  have hsq : 0 < (s₁ - s₂) ^ 2 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hP : 0 < p₁ * (1 - p₁) * (s₁ - s₂) ^ 2 := mul_pos (mul_pos hp₁ (by linarith)) hsq
  have h := E.hUS_concave x hx a s₁ hs₁ s₂ hs₂ p₁ hp₁.le (by linarith)
  simp only [smul_eq_mul]
  nlinarith [mul_pos E.hq hP]

/-- **The stage argmax is unique**: every stage maximiser is `σ x a`. -/
theorem stage_argmax_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) (hmax : IsMaxOn (fun t => E.U_S x a t) Sanctions.I s) :
    s = E.σ x a :=
  Sanctions.Foundations.Berge.isMaxOn_unique_of_strictConcaveOn (E.stage_strictConcaveOn hx a)
    hs (E.σ_mem x a) hmax (E.σ_isMaxOn_U_S x a)

/-- **The stage argmax at defiance is nondecreasing in the state** (Topkis, from
the increasing differences S8 and uniqueness). -/
theorem stage_argmax_mono {x x' : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx' : x' ∈ Icc (0 : ℝ) 1)
    (hxx' : x ≤ x') : E.σ x 0 ≤ E.σ x' 0 := by
  by_contra hlt
  have hlt : E.σ x' 0 < E.σ x 0 := not_le.mp hlt
  have hs := E.σ_mem x 0
  have hs' := E.σ_mem x' 0
  have hID := E.hUS_crossLo x hx x' hx' (E.σ x' 0) hs' (E.σ x 0) hs hxx' hlt.le
  have hID0 : 0 ≤ E.rlo * ((x' - x) * (E.σ x 0 - E.σ x' 0)) :=
    mul_nonneg E.hrlo (mul_nonneg (sub_nonneg.2 hxx') (sub_nonneg.2 hlt.le))
  have hmx : E.U_S x 0 (E.σ x' 0) ≤ E.U_S x 0 (E.σ x 0) := (E.σ_isMaxOn_U_S x 0) hs'
  have hmax' : IsMaxOn (fun t => E.U_S x' 0 t) Sanctions.I (E.σ x 0) := by
    intro t ht
    have h1 : E.U_S x' 0 t ≤ E.U_S x' 0 (E.σ x' 0) := (E.σ_isMaxOn_U_S x' 0) ht
    change E.U_S x' 0 t ≤ E.U_S x' 0 (E.σ x 0)
    linarith
  have := E.stage_argmax_eq hx' 0 hs hmax'
  linarith

/-- The sanction floor: the stage argmax at defiance at the least-entrenched
state, `b = σ(0, 0)` (it replaces the quadratic family's `u₀/q`). -/
def sfloor : ℝ := E.σ 0 0

theorem sfloor_mem : E.sfloor ∈ Sanctions.I := E.σ_mem 0 0

theorem sfloor_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : E.sfloor ≤ E.σ x 0 :=
  E.stage_argmax_mono zero_mem_I hx hx.1

/-- **A defiant Target is sanctioned at every state**: the stage argmax at
defiance is positive (S12 with `u_lo > 0`). -/
theorem stage_argmax_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 < E.σ x 0 := by
  by_contra hle
  have h0 : E.σ x 0 = 0 := le_antisymm (not_lt.mp hle) (E.σ_mem x 0).1
  set s := min 1 (E.ulo / E.Qbar) with hs_def
  have hs0 : 0 < s := lt_min zero_lt_one (div_pos E.hulo E.Qbar_pos)
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.le, min_le_left _ _⟩
  have hfl := E.hUS_floor x hx 0 zero_mem_I s hsI hs0.le
  have hmax : E.U_S x 0 s ≤ E.U_S x 0 (E.σ x 0) := (E.σ_isMaxOn_U_S x 0) hsI
  rw [h0] at hmax
  have hQs : E.Qbar * s ≤ E.ulo := by
    have := mul_le_mul_of_nonneg_left (min_le_right 1 (E.ulo / E.Qbar)) E.Qbar_pos.le
    rw [mul_div_cancel₀ _ E.Qbar_pos.ne'] at this
    exact this
  have hpos : 0 < s * (E.ulo - E.Qbar * (s + 0) / 2) := by
    apply mul_pos hs0; linarith [E.hulo, hQs]
  simp only [sub_zero] at hfl
  linarith

theorem sfloor_pos : 0 < E.sfloor := E.stage_argmax_pos zero_mem_I

/-- **The stage argmax at defiance is below one**, under the stage appetite
`u_hi < q`. General in `F`. Renovation item BH3.1 (2026-10-06): the hypothesis was
interiority `E.Interior` (the dynamic appetite `A = u_hi + β_S·K_S·d_hi < q`); the
proof reads only its stage part `u_hi < q` (`uhi_lt_q`), so that is now the binder.
A defiant Target is never sanctioned fully at the stage once the Sender's marginal
return to sanction, `u_hi`, is below the curvature `q`; the continuation plays no
role here. -/
theorem stage_argmax_lt_one (hS : E.uhi < E.q) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    E.σ x 0 < 1 := by
  have h := argmax_le_cap_of_chord_slope_lipschitz (g := fun u => E.U_S x 0 u)
    (h := fun _ => (0 : ℝ)) E.hq (L := 0) (by linarith [E.uhi_pos])
    (E.stage_chord_slope hx zero_mem_I) (fun t _ s _ => by simp)
    (E.σ_mem x 0) (by
      have := E.σ_isMaxOn_U_S x 0
      simpa using this)
  have : (E.uhi + 0) / E.q < 1 := by rw [add_zero, div_lt_one E.hq]; exact hS
  linarith

/-! ### The Target's stage payoff: chains through a mixed point -/

/-- **More compliance and less sanction, bounded above** (T2 at the lower
sanction, T4 at the lower compliance): the loss-offset side. -/
theorem UT_sub_le {x a₁ a₂ ρ₁ ρ₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha₁ : a₁ ∈ Icc (0 : ℝ) 1)
    (ha₂ : a₂ ∈ Icc (0 : ℝ) 1) (hρ₁ : ρ₁ ∈ Icc (0 : ℝ) 1) (hρ₂ : ρ₂ ∈ Icc (0 : ℝ) 1)
    (ha : a₁ ≤ a₂) (hρ : ρ₂ ≤ ρ₁) :
    E.U_T x a₂ ρ₂ - E.U_T x a₁ ρ₁ ≤ -(E.ℓlo * (a₂ - a₁)) + E.c * (ρ₁ - ρ₂) := by
  have h1 := E.hUT_costLo x hx ρ₂ hρ₂ a₁ ha₁ a₂ ha₂ ha
  have h2 := E.hUT_painHi x hx a₁ ha₁ ρ₂ hρ₂ ρ₁ hρ₁ hρ
  linarith

/-- **The state–sanction chord of the Target's payoff** (T6 at the lower
sanction, T4 at the higher state). -/
theorem UT_state_chord_ge {y₁ y₂ a ρ₁ ρ₂ : ℝ} (hy₁ : y₁ ∈ Icc (0 : ℝ) 1)
    (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) (hρ₁ : ρ₁ ∈ Icc (0 : ℝ) 1)
    (hρ₂ : ρ₂ ∈ Icc (0 : ℝ) 1) (hy : y₁ ≤ y₂) (hρ : ρ₁ ≤ ρ₂) :
    (E.vlo + E.nlo * ρ₁) * (y₂ - y₁) - E.c * (ρ₂ - ρ₁)
      ≤ E.U_T y₂ a ρ₂ - E.U_T y₁ a ρ₁ := by
  have h1 := E.hUT_stateLo a ha ρ₁ hρ₁ y₁ hy₁ y₂ hy₂ hy
  have h2 := E.hUT_painHi y₂ hy₂ a ha ρ₁ hρ₁ ρ₂ hρ₂ hρ
  linarith

/-! ## 4. The Sender carrier -/

/-- Value-function type. -/
abbrev Val : Type := ↥(Sanctions.S : Set ℝ) →ᵇ ℝ

theorem gS_le_KS : E.gS ≤ E.KS := by
  unfold gS KS chGS chKS
  rw [div_le_div_iff₀ E.one_sub_βS_glo_pos E.one_sub_βS_ghi_pos]
  have h1 := E.wlo_le_whi
  have h2 : E.β_S * E.glo ≤ E.β_S * E.ghi := mul_le_mul_of_nonneg_left E.hglo_ghi E.hβS0.le
  have h3 : E.wlo * (1 - E.β_S * E.ghi) ≤ E.wlo * (1 - E.β_S * E.glo) :=
    mul_le_mul_of_nonneg_left (by linarith) E.hwlo.le
  have h4 : E.wlo * (1 - E.β_S * E.glo) ≤ E.whi * (1 - E.β_S * E.glo) :=
    mul_le_mul_of_nonneg_right h1 E.one_sub_βS_glo_pos.le
  linarith

theorem gS_le_MS : E.gS ≤ E.MS := by
  unfold gS MS chGS
  have h1 := E.one_sub_βS_glo_pos
  have h2 : 0 < 1 - E.β_S := by linarith [E.hβS1]
  rw [div_le_div_iff₀ h1 h2]
  have hglo1 : E.glo ≤ 1 := E.hglo_ghi.trans E.hghi1
  have h3 := E.wlo_le_two_MU
  have h4 : 1 - E.β_S ≤ 1 - E.β_S * E.glo := by
    have := mul_le_mul_of_nonneg_left hglo1 E.hβS0.le
    linarith
  have h5 : E.wlo * (1 - E.β_S) ≤ E.wlo * (1 - E.β_S * E.glo) :=
    mul_le_mul_of_nonneg_left h4 E.hwlo.le
  have h6 : E.wlo * (1 - E.β_S * E.glo) ≤ 2 * E.MU * (1 - E.β_S * E.glo) :=
    mul_le_mul_of_nonneg_right h3 h1.le
  linarith

/-- **The Sender carrier**: bounded, `KS`-Lipschitz, `gS`-lower-slope on all of
`[0,1]`, and `SigV`-semiconcave through the clip. -/
def carrierS : Set Val :=
  {V : Val | V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0 ∧
    SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) E.SigV}

theorem carrierS_isClosed : IsClosed E.carrierS := by
  unfold carrierS
  exact IsClosed.inter (AbstractGame.Params.valLipGainBall_isClosed _ _ _ _)
    (SymbolicEconomyF.semiconcaveClause_isClosed E.SigV)

/-- The semiconvex clause is closed. -/
theorem semiconvexClause_isClosed (c : ℝ) :
    IsClosed {V : Val |
      SemiconvexOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) c} := by
  rw [show {V : Val |
        SemiconvexOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) c}
      = ⋂ (z₁ : ℝ) (_ : z₁ ∈ Icc (0 : ℝ) 1) (z₂ : ℝ)
            (_ : z₂ ∈ Icc (0 : ℝ) 1) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1),
          {V : Val | V (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))
              - (t * V (Sanctions.clipS' z₁) + (1 - t) * V (Sanctions.clipS' z₂))
            ≤ c / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2)} from ?_]
  · apply isClosed_iInter; intro z₁
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro z₂
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro t
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro _
    have h₁ : Continuous (fun V : Val => V (Sanctions.clipS' z₁)) :=
      ContinuousEvalConst.continuous_eval_const _
    have h₂ : Continuous (fun V : Val => V (Sanctions.clipS' z₂)) :=
      ContinuousEvalConst.continuous_eval_const _
    have h₃ : Continuous
        (fun V : Val => V (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))) :=
      ContinuousEvalConst.continuous_eval_const _
    exact isClosed_le
      (h₃.sub ((continuous_const.mul h₁).add (continuous_const.mul h₂)))
      continuous_const
  · ext V
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h z₁ hz₁ z₂ hz₂ t ht0 ht1; exact h z₁ hz₁ z₂ hz₂ t ht0 ht1
    · intro h z₁ hz₁ z₂ hz₂ t ht0 ht1; exact h z₁ hz₁ z₂ hz₂ t ht0 ht1

/-- Every carrier member is nondecreasing through the clip on `[0,1]`. -/
theorem clip_mono {V : Val}
    (hV : V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V (Sanctions.clipS' z₁) ≤ V (Sanctions.clipS' z₂) := by
  intro z₁ hz₁ z₂ hz₂ hle
  have h := hV.2.2 (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₁]; exact hz₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₂]; exact hz₂)
    (Sanctions.clipS'_mono hle)
  have hd : (0 : ℝ) ≤ E.gS * dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) :=
    mul_nonneg E.gS_pos.le dist_nonneg
  linarith

theorem clip_monotoneOn {V : Val}
    (hV : V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0) :
    MonotoneOn (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) :=
  fun z₁ hz₁ z₂ hz₂ hle => E.clip_mono hV z₁ hz₁ z₂ hz₂ hle

/-- Every carrier member is `K_S`-Lipschitz through the clip. -/
theorem clip_lip {V : Val}
    (hV : V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V (Sanctions.clipS' z₁) - V (Sanctions.clipS' z₂)| ≤ E.KS * |z₁ - z₂| := by
  intro z₁ _ z₂ _
  have h := hV.2.1 (Sanctions.clipS' z₂) (Sanctions.clipS' z₁)
  have hd : dist (Sanctions.clipS' z₂) (Sanctions.clipS' z₁) ≤ |z₁ - z₂| := by
    have h2 := Sanctions.clipS'_lipschitz_dist z₂ z₁
    rwa [abs_sub_comm] at h2
  exact le_trans h (mul_le_mul_of_nonneg_left hd E.KS_pos.le)

/-- Every carrier member is strictly increasing through the clip on `[0,1]`. -/
theorem clip_strictMono {V : Val}
    (hV : V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ < z₂ →
      V (Sanctions.clipS' z₁) < V (Sanctions.clipS' z₂) := by
  intro z₁ hz₁ z₂ hz₂ hlt
  have h := hV.2.2 (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₁]; exact hz₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₂]; exact hz₂)
    (Sanctions.clipS'_mono hlt.le)
  have hdist : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = z₂ - z₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hz₁,
      Sanctions.clipS'_val_eq_of_mem hz₂, abs_sub_comm, abs_of_pos (by linarith)]
  rw [hdist] at h
  have : 0 < E.gS * (z₂ - z₁) := mul_pos E.gS_pos (by linarith)
  linarith

/-- Lower slope through the clip. -/
theorem clip_lowerSlope {V : Val}
    (hV : V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      E.gS * (z₂ - z₁) ≤ V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) := by
  intro z₁ hz₁ z₂ hz₂ hle
  have h := hV.2.2 (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₁]; exact hz₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₂]; exact hz₂)
    (Sanctions.clipS'_mono hle)
  have hdist : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = z₂ - z₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hz₁,
      Sanctions.clipS'_val_eq_of_mem hz₂, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdist] at h
  exact h

theorem carrierS_nonempty : E.carrierS.Nonempty :=
  ⟨affineBCF E.gS,
    SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le E.gS_le_KS E.gS_le_MS,
    SymbolicEconomyF.affineBCF_clip_semiconcave E.hSigV0⟩

/-- The affine member is semiconvex through the clip with any nonnegative
modulus. -/
theorem affineBCF_clip_semiconvex {c σ : ℝ} (hσ : 0 ≤ σ) :
    SemiconvexOnSet (fun z => affineBCF c (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) σ := by
  intro z₁ hz₁ z₂ hz₂ t ht0 ht1
  have hm := mem_Icc_convexComb hz₁ hz₂ ht0 ht1
  have hP : (0 : ℝ) ≤ t * (1 - t) * (z₁ - z₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  change affineBCF c (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))
      - (t * affineBCF c (Sanctions.clipS' z₁) + (1 - t) * affineBCF c (Sanctions.clipS' z₂))
    ≤ σ / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2)
  rw [affineBCF_apply, affineBCF_apply, affineBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hz₁, Sanctions.clipS'_val_eq_of_mem hz₂,
    Sanctions.clipS'_val_eq_of_mem hm]
  nlinarith [mul_nonneg hσ hP]

/-! ## 5. The continuation's sanction curvature and argmax uniqueness -/

/-- The one-variable sanction semiconcavity, read off the joint chord at zero
state displacement. -/
theorem F_sanctionSemiconcave : SanctionSemiconcave E.F E.Ms := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have h := E.hFjsc x hx x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  simp only [sub_self, abs_zero, mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, zero_add, zero_sub, neg_mul, neg_neg] at h
  change t * E.F x s₁ + (1 - t) * E.F x s₂ - E.F x (t * s₁ + (1 - t) * s₂)
      ≤ E.Ms / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
  have hmid : t * x + (1 - t) * x = x := by ring
  rw [hmid] at h
  linarith [h]

/-- **The continuation is semiconcave in the sanction** with modulus
`SigV·dhi² + K_S·Ms`. -/
theorem carrier_comp_semiconcave {V : Val} (hV : V ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    SemiconcaveOnSet (fun s => V (Sanctions.clipS' (E.F x s)))
      (Icc (0 : ℝ) 1) (E.SigV * E.dhi ^ 2 + E.KS * E.Ms) :=
  Sanctions.SemiconcaveComposition.semiconcave_comp_of_chords
    (v := fun z => V (Sanctions.clipS' z)) (F := E.F)
    (σV := E.SigV) (K := E.KS) (dlo := E.dlo) (dhi := E.dhi) (M := E.Ms) (x := x)
    E.hSigV0 E.KS_pos.le E.hdlo0.le E.hMs0
    (E.clip_monotoneOn hV.1) (E.clip_lip hV.1) hV.2 hx E.F_maps
    E.hSlo E.hShi E.F_sanctionSemiconcave

/-- **The Sender's dynamic objective is strictly concave in the sanction** for
every carrier value, every state and every real compliance level: the stage
curvature `q` (S4) beats `β_S` times the continuation's, by `hCurv`. -/
theorem senderObj_strictConcaveOn {V : Val} (hV : V ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (a : ℝ) :
    StrictConcaveOn ℝ Sanctions.I
      (fun s => E.U_S x a s + E.β_S * V (Sanctions.clipS' (E.F x s))) := by
  have hcomp := E.carrier_comp_semiconcave hV hx
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p₁ p₂ hp₁ hp₂ hsum
  have hp2 : p₂ = 1 - p₁ := by linarith
  subst hp2
  have hsq : 0 < (s₁ - s₂) ^ 2 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hP : 0 < p₁ * (1 - p₁) * (s₁ - s₂) ^ 2 :=
    mul_pos (mul_pos hp₁ (by linarith)) hsq
  have hsc := hcomp s₁ hs₁ s₂ hs₂ p₁ hp₁.le (by linarith)
  have hD := mul_le_mul_of_nonneg_left hsc E.hβS0.le
  have hU := E.hUS_concave x hx a s₁ hs₁ s₂ hs₂ p₁ hp₁.le (by linarith)
  have hgap : 0 < E.q - E.β_S * (E.SigV * E.dhi ^ 2 + E.KS * E.Ms) := by
    have := E.hCurv; unfold KS; linarith
  have hkey : 0 < (E.q - E.β_S * (E.SigV * E.dhi ^ 2 + E.KS * E.Ms)) / 2
      * (p₁ * (1 - p₁) * (s₁ - s₂) ^ 2) := by positivity
  simp only [smul_eq_mul]
  nlinarith [hD, hkey, hU]

/-- **State-local Sender argmax uniqueness on the carrier.** -/
theorem DAU_on_carrier {V : Val} (hV : V ∈ E.carrierS) :
    E.toParams.DynamicArgmaxUnique V := by
  apply E.toParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  exact E.senderObj_strictConcaveOn hV hx a

/-! ## 6. The Sender Bellman image at the defiance policy -/

/-- The Sender Bellman image at `α ≡ 0`, evaluated at an attained argmax, with
sup-domination of every feasible sanction. -/
theorem bellmanS_spec (V : Val) (y : ↥(Sanctions.S : Set ℝ)) :
    ∃ sStar ∈ Sanctions.I,
      E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V y
        = E.U_S y.val 0 sStar + E.β_S * V (Sanctions.clipS' (E.F y.val sStar))
      ∧ ∀ s ∈ Sanctions.I,
          E.U_S y.val 0 s + E.β_S * V (Sanctions.clipS' (E.F y.val s))
          ≤ E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V y := by
  have hmax := E.toParams.σ_dyn_isMaxOn V y.val 0
  have hmem := E.toParams.σ_dyn_mem V y.val 0
  have heq := WitnessKit.bellmanS_image_of_isMaxOn (p := E.toParams)
    (α := fun _ => 0) continuous_const V y hmem hmax
  refine ⟨_, hmem, heq, ?_⟩
  intro s hs
  rw [heq]
  exact hmax hs

/-- **Norm leg.** `M_U + β_S·M_S ≤ M_S` since `1 + β_S ≤ 2`. -/
theorem bellmanS_norm_le {V : Val} (hV : V ∈ E.carrierS) :
    ‖E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V‖ ≤ E.MS := by
  have h := E.toParams.bellmanS_BCF_norm_le (α := fun _ => 0) continuous_const
    (fun _ => ⟨le_refl 0, zero_le_one⟩) V
    (cube_S := E.MU) (R_S := E.MS) hV.1.1
    (fun x hx a ha s hs => E.abs_U_S_le_MU hx ha hs)
  refine h.trans ?_
  have h2 : 0 < 1 - E.β_S := by linarith [E.hβS1]
  have h2' : (1 - E.β_S) ≠ 0 := h2.ne'
  have hkey : E.MU + E.β_S * E.MS = E.MU * (1 + E.β_S) / (1 - E.β_S) := by
    unfold MS; field_simp; ring
  rw [hkey]
  unfold MS
  apply div_le_div_of_nonneg_right _ h2.le
  nlinarith [E.MU_nonneg, E.hβS1]

/-- **Lower-slope leg**: at every sanction a rise in the state raises the stage
payoff by at least `w_lo` per unit (S3) and the successor by at least `glo`
per unit. -/
theorem bellmanS_lowerSlope {V : Val} (hV : V ∈ E.carrierS) :
    AbstractGame.Params.LowerSlopeOnValueOn
      (E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V) (Icc (0 : ℝ) 1) E.gS := by
  apply E.toParams.bellmanS_BCF_preserves_lowerSlopeCone_generalF
  · intro s hs y₁ hy₁ y₂ hy₂ hle
    have hband := (E.hbandAll s hs) y₁ hy₁ y₂ hy₂ hle
    have hFlo : E.glo * (y₂ - y₁) ≤ E.F y₂ s - E.F y₁ s := hband.1
    have hU := E.hUS_stateSlope 0 zero_mem_I s hs y₁ hy₁ y₂ hy₂ hle
    have hgSy : E.wlo * (y₂ - y₁)
        = E.gS * (y₂ - y₁) - E.β_S * E.gS * (E.glo * (y₂ - y₁)) := by
      rw [← E.gS_mul]; ring
    have h1 : 0 ≤ E.β_S * E.gS := mul_nonneg E.hβS0.le E.gS_pos.le
    have h2 := mul_le_mul_of_nonneg_left hFlo h1
    change E.gS * (y₂ - y₁)
      ≤ (E.U_S y₂ 0 s - E.U_S y₁ 0 s) + E.β_S * E.gS * (E.F y₂ s - E.F y₁ s)
    nlinarith [hU, hgSy, h2]
  · exact hV.1.2.2

/-- **Lipschitz leg**, by cross-evaluating attained argmaxes (S2). -/
theorem bellmanS_lipschitz {V : Val} (hV : V ∈ E.carrierS) :
    AbstractGame.Params.ValueLipschitzWith
      (E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V) E.KS := by
  have key : ∀ u v : ↥(Sanctions.S : Set ℝ),
      E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V v
        - E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V u
      ≤ E.KS * dist u v := by
    intro u v
    obtain ⟨sv, hsvI, heqv, _⟩ := E.bellmanS_spec V v
    obtain ⟨_, _, _, hdomu⟩ := E.bellmanS_spec V u
    have hle := hdomu sv hsvI
    have hFu : E.F u.val sv ∈ Icc (0:ℝ) 1 := E.F_mem _ _ u.property hsvI
    have hFv : E.F v.val sv ∈ Icc (0:ℝ) 1 := E.F_mem _ _ v.property hsvI
    have hWd := E.clip_lip hV.1 (E.F v.val sv) hFv (E.F u.val sv) hFu
    have hF : |E.F v.val sv - E.F u.val sv| ≤ E.ghi * |v.val - u.val| :=
      abs_sub_le_of_stateBand E.hglo0 (E.hbandAll sv hsvI) v.property u.property
    have hcont : V (Sanctions.clipS' (E.F v.val sv)) - V (Sanctions.clipS' (E.F u.val sv))
        ≤ E.KS * (E.ghi * |v.val - u.val|) :=
      (le_abs_self _).trans (hWd.trans (mul_le_mul_of_nonneg_left hF E.KS_pos.le))
    have hstage : E.U_S v.val 0 sv - E.U_S u.val 0 sv ≤ E.whi * |v.val - u.val| :=
      (le_abs_self _).trans (E.hUS_stateLip sv hsvI u.val u.property v.val v.property)
    have hdist : dist u v = |v.val - u.val| := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [heqv, hdist]
    have hwhi : E.whi * |v.val - u.val|
        = E.KS * |v.val - u.val| - E.β_S * (E.KS * (E.ghi * |v.val - u.val|)) := by
      rw [← E.KS_mul]; ring
    have hc2 := mul_le_mul_of_nonneg_left hcont E.hβS0.le
    nlinarith [hle, hc2, hstage, hwhi]
  intro y₁ y₂
  rw [abs_sub_le_iff]
  constructor
  · exact key y₁ y₂
  · have h := key y₂ y₁
    rwa [dist_comm] at h

/-! ## 7. The semiconcave leg -/

/-- **The Sender's dynamic objective is jointly semiconcave** in `(x, s)` on a
carrier value, with moduli `(chSig, plRho, plMu)`. -/
theorem senderObj_jointSemiconcave {V : Val} (hV : V ∈ E.carrierS) :
    JointSemiconcaveOn
      (fun x s => E.U_S x 0 s + E.β_S * V (Sanctions.clipS' (E.F x s)))
      (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
      (chSig E.β_S E.σx E.SigV E.ghi E.KS E.Mx)
      (plRho E.β_S E.rhi E.SigV E.ghi E.dhi E.KS E.Mm)
      (plMu E.β_S E.q E.SigV E.dhi E.KS E.Ms) := by
  have hcont := jointSemiconcave_comp_of_chords
    (v := fun z => V (Sanctions.clipS' z)) (F := E.F)
    (σV := E.SigV) (K := E.KS) (glo := E.glo) (ghi := E.ghi) (dlo := E.dlo) (dhi := E.dhi)
    (Mx := E.Mx) (Mm := E.Mm) (Ms := E.Ms)
    E.hSigV0 E.KS_pos.le E.hglo0 E.hdlo0.le E.hMx0 E.hMm0 E.hMs0
    (E.clip_monotoneOn hV.1) (E.clip_lip hV.1) hV.2 E.F_maps
    E.hbandAll E.hSlo E.hShi E.hFjsc
  have hsum := JointSemiconcaveOn.add E.hUS_joint (hcont.const_mul E.hβS0.le)
  refine hsum.congr_moduli ?_ ?_ ?_
  · unfold chSig; ring
  · unfold plRho; ring
  · unfold plMu; ring

/-- The Bellman image evaluated through the clip is the greatest value of the
objective over the sanction interval. -/
theorem bellmanS_isGreatest (V : Val) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IsGreatest
      ((fun s => E.U_S x 0 s + E.β_S * V (Sanctions.clipS' (E.F x s))) '' Icc (0 : ℝ) 1)
      (E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' x)) := by
  obtain ⟨sStar, hsI, heq, hdom⟩ := E.bellmanS_spec V (Sanctions.clipS' x)
  have hval : (Sanctions.clipS' x).val = x := Sanctions.clipS'_val_eq_of_mem hx
  refine ⟨⟨sStar, hsI, ?_⟩, ?_⟩
  · rw [heq, hval]
  · rintro _ ⟨s, hs, rfl⟩
    have := hdom s hs
    rw [hval] at this
    exact this

/-- **Semiconcave leg.** The image's semiconcavity through the clip is the
Schur modulus, which `hSigV` bounds by `SigV`. -/
theorem bellmanS_semiconcave {V : Val} (hV : V ∈ E.carrierS) :
    SemiconcaveOnSet
      (fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
      (Icc (0 : ℝ) 1) E.SigV := by
  have hsup := sup_semiconcave_of_joint_unitInterval
    (Φ := fun x s => E.U_S x 0 s + E.β_S * V (Sanctions.clipS' (E.F x s)))
    (v := fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
    E.mu_pos (E.senderObj_jointSemiconcave hV) (fun x hx => E.bellmanS_isGreatest V hx)
  refine hsup.mono_modulus ?_
  have h := E.hSigV
  unfold chSigImg at h
  unfold KS
  exact h

/-! ## 8. Carrier invariance -/

/-- **The Sender carrier is Bellman-invariant at the defiance policy.** -/
theorem bellmanS_mem {V : Val} (hV : V ∈ E.carrierS) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V ∈ E.carrierS :=
  ⟨⟨E.bellmanS_norm_le hV, E.bellmanS_lipschitz hV, E.bellmanS_lowerSlope hV⟩,
    E.bellmanS_semiconcave hV⟩

end ChordEconomy

/-! ## 8b. The two-sided extension: the carrier's semiconvexity (renovation item BJ3.1)

The declarations below read the two-sided curvature data `τ_x`, `M_cx`, `M_mix`, so since
renovation item BJ3.1 (2026-10-07) they are stated on `ChordEconomyTwoSided`; until then
they were in the `ChordEconomy` namespace, otherwise unchanged. General in `F`. Every
relief economy is a two-sided one, so the relief-side results read them through the
parent projection. -/

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

theorem hMmix0 : 0 ≤ E.Mmix := E.hFmix.nonneg

/-- `σ_C`, the carrier's semiconvexity modulus. -/
def SigC : ℝ := chSigC E.β_S E.τx E.KS E.Mcx E.ghi

theorem SigC_nonneg : 0 ≤ E.SigC := by
  unfold SigC chSigC
  apply div_nonneg
  · have := mul_nonneg (mul_nonneg E.hβS0.le E.KS_nonneg) E.hMcx0
    linarith [E.hτx0]
  · linarith [E.βS_ghi_sq_lt_one]

/-- **Linear closure**: `τ_x + β_S·(σ_C·g_hi² + K_S·M_cx) = σ_C`. -/
theorem SigC_closure : E.τx + E.β_S * (E.SigC * E.ghi ^ 2 + E.KS * E.Mcx) ≤ E.SigC := by
  have hpos : 0 < 1 - E.β_S * E.ghi ^ 2 := by linarith [E.βS_ghi_sq_lt_one]
  apply le_of_eq
  unfold SigC chSigC
  field_simp
  ring

/-- **The two-sided Sender carrier**: the carrier, plus `σ_C`-semiconvexity
through the clip. -/
def carrierS2 : Set Val :=
  {V : Val | V ∈ E.carrierS ∧
    SemiconvexOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) E.SigC}

theorem carrierS2_isClosed : IsClosed E.carrierS2 :=
  IsClosed.inter E.carrierS_isClosed (semiconvexClause_isClosed E.SigC)

theorem carrierS2_subset : E.carrierS2 ⊆ E.carrierS := fun _ hV => hV.1

theorem carrierS2_nonempty : E.carrierS2.Nonempty :=
  ⟨affineBCF E.gS,
    ⟨SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le E.gS_le_KS E.gS_le_MS,
      SymbolicEconomyF.affineBCF_clip_semiconcave E.hSigV0⟩,
    affineBCF_clip_semiconvex E.SigC_nonneg⟩

/-- **Semiconvex leg** on the two-sided carrier: each state section of the
objective is `τ_x + β_S(σ_C·g_hi² + K_S·M_cx)`-semiconvex (S7 and the
composition rule), the supremum keeps that modulus, and the linear closure
bounds it by `σ_C`. -/
theorem bellmanS_semiconvex {V : Val} (hV : V ∈ E.carrierS2) :
    SemiconvexOnSet
      (fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
      (Icc (0 : ℝ) 1) E.SigC := by
  have hsec : ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet
        (fun x => E.U_S x 0 s + E.β_S * V (Sanctions.clipS' (E.F x s)))
        (Icc (0 : ℝ) 1) (E.τx + E.β_S * (E.SigC * E.ghi ^ 2 + E.KS * E.Mcx)) := by
    intro s hs
    have hcomp := semiconvexOnSet_comp_of_stateChord
      (v := fun z => V (Sanctions.clipS' z)) (G := fun y => E.F y s)
      E.SigC_nonneg E.KS_nonneg E.hglo0 E.hMcx0
      (E.clip_monotoneOn hV.1.1) (E.clip_lip hV.1.1) hV.2
      (fun y hy => E.F_maps y hy s hs) (E.hbandAll s hs) (E.hFcx s hs)
    exact (E.hUS_stateConvex s hs).add (hcomp.const_mul E.hβS0.le)
  have hsup := sup_semiconvexOnSet
    (Φ := fun x s => E.U_S x 0 s + E.β_S * V (Sanctions.clipS' (E.F x s)))
    (v := fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
    hsec (fun x hx => E.bellmanS_isGreatest V hx)
  exact hsup.mono E.SigC_closure

/-- **The two-sided carrier is Bellman-invariant** at the defiance policy. -/
theorem bellmanS_mem2 {V : Val} (hV : V ∈ E.carrierS2) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V ∈ E.carrierS2 :=
  ⟨E.bellmanS_mem hV.1, E.bellmanS_semiconvex hV⟩

end ChordEconomyTwoSided

/-! ## 9. Placability, the margin, and zero-sanction neutrality -/

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Placability**: the placation rate covers the appetite,
`u_hi + β_S·K_S·d_hi ≤ k_lo`, so a fully compliant Target is not sanctioned at
all. A hypothesis of the results that read it (round AP). -/
def Placable : Prop := E.A ≤ E.klo

/-- `g_T`, the Target value's lower state slope, floor-refined: the state rate
`v_lo + n_lo·b` at the sanction floor `b = σ(0,0)`, compounded through the lower
state chord. -/
def gT : ℝ := (E.vlo + E.nlo * E.sfloor) / (1 - E.β_T * E.glo)

theorem gT_pos : 0 < E.gT := by
  unfold gT
  have h : 0 ≤ E.nlo * E.sfloor := mul_nonneg E.hnlo E.sfloor_mem.1
  exact div_pos (by linarith [E.hvlo]) (by linarith [E.βT_glo_lt_one])

/-- The slope identity `g_T·(1 − β_T·glo) = v_lo + n_lo·b`. -/
theorem gT_mul : E.gT * (1 - E.β_T * E.glo) = E.vlo + E.nlo * E.sfloor := by
  unfold gT
  have h : (1 - E.β_T * E.glo) ≠ 0 := by linarith [E.βT_glo_lt_one]
  exact div_mul_cancel₀ _ h

/-- **The loss-offset margin**: the Target's sanction pain `c` per unit is
covered by the discounted continuation gain at the value slope `g_T`. A
hypothesis of the results that read it (round AP). -/
def LossOffset : Prop := E.c ≤ E.β_T * E.dlo * E.gT

/-- **Zero-sanction neutrality** (doc 104 §5 N1, sign-off M2): a concession is
worth nothing to the Sender when it imposes no sanction. Read by the relief
equilibrium and the Sender-only regime, whose Sender value is built before the
Target's policy. -/
def ZeroSanctionNeutral : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, E.U_S x a 0 = E.U_S x 0 0

/-- **Its one-sided form against defiance**: no compliance level raises the
Sender's payoff above defiance's at zero sanction. Read by relief
participation. -/
def ZeroSanctionNoGain : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, E.U_S x a 0 ≤ E.U_S x 0 0

/-- **Its pairwise one-sided form**: at zero sanction the Sender's payoff is
nonincreasing in compliance — a larger concession is never worth more to the
Sender in itself. Implied by neutrality, and implies `ZeroSanctionNoGain`. Read
by the all-equilibria wedge floor, whose policy chord compares two compliance
levels neither of which need be zero. -/
def ZeroSanctionAntitone : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1, a ≤ a' →
    E.U_S x a' 0 ≤ E.U_S x a 0

theorem ZeroSanctionNeutral.antitone {E : ChordEconomy} (h : E.ZeroSanctionNeutral) :
    E.ZeroSanctionAntitone :=
  fun x hx a ha a' ha' _ => le_of_eq ((h x hx a' ha').trans (h x hx a ha).symm)

theorem ZeroSanctionAntitone.noGain {E : ChordEconomy} (h : E.ZeroSanctionAntitone) :
    E.ZeroSanctionNoGain :=
  fun x hx a ha => h x hx 0 zero_mem_I a ha ha.1

theorem ZeroSanctionNeutral.noGain {E : ChordEconomy} (h : E.ZeroSanctionNeutral) :
    E.ZeroSanctionNoGain :=
  fun x hx a ha => (h x hx a ha).le

/-- **Compliance never raises the Sender's payoff** at any fixed sanction, under
the one-sided neutrality: placation (S10) makes the difference decrease in the
sanction from its value at zero. -/
theorem US_antitone_a (hN : E.ZeroSanctionNoGain) {x a s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : E.U_S x a s ≤ E.U_S x 0 s := by
  have hdd := E.hUS_placLo x hx 0 zero_mem_I a ha 0 zero_mem_I s hs ha.1 hs.1
  have h0 := hN x hx a ha
  have : 0 ≤ E.klo * ((a - 0) * (s - 0)) :=
    mul_nonneg E.hklo.le (mul_nonneg (by linarith [ha.1]) (by linarith [hs.1]))
  linarith

/-- **Compliance never raises the Sender's payoff at any fixed sanction, pairwise**,
under the pairwise one-sided neutrality: placation (S10) lowers the sanction's
return as compliance rises, and at zero sanction compliance is worth nothing
more. -/
theorem US_antitone (hN : E.ZeroSanctionAntitone) {x a a' s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (ha' : a' ∈ Icc (0 : ℝ) 1) (haa' : a ≤ a')
    (hs : s ∈ Icc (0 : ℝ) 1) : E.U_S x a' s ≤ E.U_S x a s := by
  have hdd := E.hUS_placLo x hx a ha a' ha' 0 zero_mem_I s hs haa' hs.1
  have h0 := hN x hx a ha a' ha' haa'
  have : 0 ≤ E.klo * ((a' - a) * (s - 0)) :=
    mul_nonneg E.hklo.le (mul_nonneg (by linarith) (by linarith [hs.1]))
  linarith

/-- **The stage return to a higher sanction at any compliance, from below**: the
floor (S12) at the least-entrenched state, the lower cross rate (S8) up to the
state, and the upper placation rate (S10u) out to the compliance give, for
`s ≤ s₀` in `[0,1]` and any placation ceiling `k_hi`,
`U_S(x,a,s₀) − U_S(x,a,s) ≥ (s₀ − s)·(u_lo + r_lo·x − k_hi·a − Q̄·(s₀ + s)/2)`.
No neutrality is used. General in `F`. Renovation item BJ2.2 (2026-10-07): the upper
placation rate is the hypothesis `hPC` (`PlacationCeiling`), no longer a field of the
base class. -/
theorem US_sanction_gain_ge {khi : ℝ} (hPC : E.PlacationCeiling khi) {x a s s₀ : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
    (hle : s ≤ s₀) :
    (s₀ - s) * (E.ulo + E.rlo * x - khi * a - E.Qbar * (s₀ + s) / 2)
      ≤ E.U_S x a s₀ - E.U_S x a s := by
  have hfl := E.hUS_floor 0 zero_mem_I s hs s₀ hs₀ hle
  have hcr := E.hUS_crossLo 0 zero_mem_I x hx s hs s₀ hs₀ hx.1 hle
  have hpl := (abs_le.mp (hPC x hx 0 zero_mem_I a ha s hs s₀ hs₀ ha.1)).1
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s₀ - s)] at hpl
  have e1 : E.rlo * ((x - 0) * (s₀ - s)) = (s₀ - s) * (E.rlo * x) := by ring
  have e2 : khi * ((a - 0) * (s₀ - s)) = (s₀ - s) * (khi * a) := by ring
  have e3 : (s₀ - s) * (E.ulo + E.rlo * x - khi * a - E.Qbar * (s₀ + s) / 2)
      = (s₀ - s) * (E.ulo - E.Qbar * (s₀ + s) / 2) + (s₀ - s) * (E.rlo * x)
        - (s₀ - s) * (khi * a) := by ring
  rw [e1] at hcr
  rw [e2] at hpl
  rw [e3]
  linarith

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy

variable (E : ChordEconomyRelief)

/-- **The stage relief margin** (a hypothesis since round BC, 2026-09-29, doc 110
R4; until then the field `hStageRelief`). A unit of compliance costs at most
`ℓ_hi`, buys at least `k_lo/Q̄` units of stage sanction relief below the placation
level, each worth at least `p_lo`: `ℓ_hi·Q̄ < k_lo·p_lo`. What the myopic reading
needs. Written over the class's own data (Rule 14). -/
def StageRelief : Prop := E.ℓhi * E.Qbar < E.klo * E.plo

/-- **The relief extension's placation ceiling** (renovation item BJ2.2, 2026-10-07): its
field S10u is `ChordEconomy.PlacationCeiling` at its own rate `k_hi`. Definitional;
general in `F`. -/
theorem placationCeiling : E.PlacationCeiling E.khi := E.hUS_placHi

/-- `k_lo ≤ k_hi` on the relief extension, at its own upper placation rate (the base
form `ChordEconomy.klo_le_khi` at `placationCeiling`). General in `F`. -/
theorem klo_le_khi : E.klo ≤ E.khi := E.toChordEconomy.klo_le_khi E.placationCeiling

/-- `0 < k_hi` on the relief extension. General in `F`. -/
theorem khi_pos : 0 < E.khi := E.toChordEconomy.khi_pos E.placationCeiling

/-! ### Derived orderings of the relief rates (moved from `ChordEconomy`, round BC) -/

/-- `r_lo ≤ r_hi`, and so `0 ≤ r_hi`. -/
theorem rlo_le_rhi : E.rlo ≤ E.rhi := by
  have h1 := E.hUS_crossLo 0 zero_mem_I 1 one_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one zero_le_one
  have h2 := E.hUS_crossHi 0 zero_mem_I 0 zero_mem_I 1 one_mem_I 0 zero_mem_I 1
    one_mem_I
  simp only [sub_zero, abs_one, mul_one] at h1 h2
  linarith [le_abs_self ((E.U_S 1 0 1 - E.U_S 1 0 0) - (E.U_S 0 0 1 - E.U_S 0 0 0))]

theorem rhi_nonneg : 0 ≤ E.rhi := le_trans E.hrlo E.rlo_le_rhi

/-- `ℓ_lo ≤ ℓ_hi`. -/
theorem ℓlo_le_ℓhi : E.ℓlo ≤ E.ℓhi := by
  have h1 := E.hUT_costLo 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one
  have h2 := E.hUT_costHi 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one
  simp only [sub_zero, mul_one] at h1 h2
  linarith

theorem ℓhi_pos : 0 < E.ℓhi := lt_of_lt_of_le E.hℓlo E.ℓlo_le_ℓhi

/-- `p_lo ≤ c`, and so `0 < c`. -/
theorem plo_le_c : E.plo ≤ E.c := by
  have h1 := E.hUT_painHi 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one
  have h2 := E.hUT_painLo 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
    zero_le_one
  simp only [sub_zero, mul_one] at h1 h2
  linarith

theorem c_pos : 0 < E.c := lt_of_lt_of_le E.hplo E.plo_le_c

/-- The two state rates of the Target are ordered at every sanction. -/
theorem vlo_le_vhi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    E.vlo + E.nlo * s ≤ E.vhi + E.nhi * s := by
  have h1 := E.hUT_stateLo 0 zero_mem_I s hs 0 zero_mem_I 1 one_mem_I zero_le_one
  have h2 := E.hUT_stateHi 0 zero_mem_I s hs 0 zero_mem_I 1 one_mem_I
  simp only [sub_zero, abs_one, mul_one] at h1 h2
  linarith [le_abs_self (E.U_T 1 0 s - E.U_T 0 0 s)]

/-- **More compliance and less sanction, bounded below** (T3 at the lower
sanction, T5 at the lower compliance): the relief side. -/
theorem UT_sub_ge {x a₁ a₂ ρ₁ ρ₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha₁ : a₁ ∈ Icc (0 : ℝ) 1)
    (ha₂ : a₂ ∈ Icc (0 : ℝ) 1) (hρ₁ : ρ₁ ∈ Icc (0 : ℝ) 1) (hρ₂ : ρ₂ ∈ Icc (0 : ℝ) 1)
    (ha : a₁ ≤ a₂) (hρ : ρ₂ ≤ ρ₁) :
    -(E.ℓhi * (a₂ - a₁)) + E.plo * (ρ₁ - ρ₂) ≤ E.U_T x a₂ ρ₂ - E.U_T x a₁ ρ₁ := by
  have h1 := E.hUT_costHi x hx ρ₂ hρ₂ a₁ ha₁ a₂ ha₂ ha
  have h2 := E.hUT_painLo x hx a₁ ha₁ ρ₂ hρ₂ ρ₁ hρ₁ hρ
  linarith

/-- The Target's payoff is `c`-Lipschitz in the sanction (T4 and T5, `p_lo ≥ 0`). -/
theorem UT_sanction_lip {x a s₁ s₂ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) :
    |E.U_T x a s₂ - E.U_T x a s₁| ≤ E.c * |s₂ - s₁| := by
  rcases le_total s₁ s₂ with h | h
  · have h1 := E.hUT_painHi x hx a ha s₁ hs₁ s₂ hs₂ h
    have h2 := E.hUT_painLo x hx a ha s₁ hs₁ s₂ hs₂ h
    have h3 : 0 ≤ E.plo * (s₂ - s₁) := mul_nonneg E.hplo.le (sub_nonneg.2 h)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (sub_nonneg.2 h)]
    linarith
  · have h1 := E.hUT_painHi x hx a ha s₂ hs₂ s₁ hs₁ h
    have h2 := E.hUT_painLo x hx a ha s₂ hs₂ s₁ hs₁ h
    have h3 : 0 ≤ E.plo * (s₁ - s₂) := mul_nonneg E.hplo.le (sub_nonneg.2 h)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

end ChordEconomyRelief

end

end Examples
end Sanctions
