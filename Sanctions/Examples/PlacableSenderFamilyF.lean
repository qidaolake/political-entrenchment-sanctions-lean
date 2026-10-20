/-
Sanctions/Examples/PlacableSenderFamilyF.lean

**The placable-Sender family: a general-transition, coefficient-parametric class
of sanctions economies on which, under interiority (the predicate `Interior`, a
hypothesis of the results that read it, not a membership condition) and the margins
below, the Sender's equilibrium sanction is INTERIOR, the Target corner-flips, and
BOTH continuation channels change equilibrium behaviour.**

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

The results here are universals over a family, quantified over every admissible
member `(E : PlacableEconomyF)`. They license universal statements about the
family; Rule 9's "a witness proves only existence" restriction does not apply to
them. The file sits under `Examples/` because the family fixes a functional form
with free coefficients — the same reason `SymbolicCertifiedFamily` does.

## What this family is, against the corner families

`SymbolicEconomyF` (the general-`F` corner family) pins the Sender at the full
sanction by an implacability margin `hCorner` and the Target at full defiance by
a loss-offset margin `hTMargin`. Both channels are then *inert as behaviour*: the
Sender sanctions fully with or without a future, and the Target defies with or
without one (doc 44 §3.5; Rung 1, 2026-09-02).

This family drops `hCorner`. Its results about an interior Sender assume instead an
**interiority** margin (`Interior`; a field `hInterior` until renovation item BJ2.3,
now a hypothesis `hInt` of the results that read it, so membership alone no longer
gives it): the Sender's dynamic marginal appetite at the top of the state space is
strictly below its own cost curvature `q`, so its argmax is interior and strictly
above the stage argmax by exactly the continuation wedge. The Target
keeps the loss-offset margin (since round J in its floor-refined form: the
Target value slope carries the rally term `n` at the response floor `u₀/q`,
which the previous form discarded; since round AP, 2026-09-23, doc 102 J2, it
is the *hypothesis* `LossOffset` of the results that read it, not a field, so
that its complement — the relief side of the general-transition bracket — is
inhabited on the same structure), so the forward-looking Target still defies
under it — but now
the *stage* objective rewards compliance at the margin (`StageRelief`; a field
`hStageRelief` until renovation item BJ2.3, now a hypothesis, the family keeping only
its sign `n < c` as the field `hcn`; the
endpoint form, the stage flip `ℓq < u₀(c − n)`, is a hypothesis of the
activation results since round Q2, not a field): an interior Sender is
**placable**
(`Placable`, since round AP a hypothesis in the same way: full compliance
drives the sanction to zero), so complying buys
sanction relief today. The Target's stage argmax leaves zero while its dynamic
argmax stays there. Both channels are live, and the Target channel is live
*because* the Sender became responsive.

This is the Rule 5 promotion of `Examples/DualBasinSelectionWitness.lean`
(`dualParams`), which exhibits an interior Sender with a semiconcave carrier at
one affine point with the Target channel cancelled by a knife edge.

## What is symbolic here

Stage payoffs are the corner family's (`symU_S`, `symU_T`), with the Sender's
rally slope `r ≥ 0` kept general:

```
U_S(x, a, s) = −(q/2)·s² + s·(u₀ − k·a + r·x) + w·x
U_T(x, a, s) = −ℓ·a + s·(n·x − c) + v·x
```

No Target curvature term: the Target corner-flips rather than sitting interior,
so a curvature scalar would never be consumed (Rule 3, symbol economy). The
transition `F` is general (Rule 22), constrained only by chords:

* state band `[glo, ghi]` at every sanction (`StateChordBandAll`);
* sanction band `[dlo, dhi]`;
* a joint chord semiconcavity `JointSemiconcaveOn F … Mx Mm (−Ms)`;
* (Rung 3) state-section semiconvexity `Mcx` and a mixed chord bound `Mmix`;
* (doc 63 / doc 65) sanction-section semiconvexity `Mcs` — **not a field of
  the base family**: it lives on the subclass `PlacableEconomyFcs` below,
  consumed by the reading `01`, the four-cell theorem
  (`PlacableSenderRegime01`) and, since round Q2, the flip-free activation
  theorem (`PlacableSenderReliefActivation`, headline row 47). Every result
  stated over `PlacableEconomyF` never reads it.

Under the affine law every `M` is zero. The non-affine member is
`quadDiagF` (proved `≠ affineF` at every rate, `quadDiagF_ne_affineF` in
`PlacableSenderWitnesses`).

## The carrier and the one supplied modulus

The Sender carrier is `{‖V‖ ≤ MS, KS-Lipschitz, gS-lower-slope, SigV-semiconcave}`.
`KS`, `gS`, `MS` are closed forms. `SigV` is **supplied**, with a closure
inequality `hSigV`: the image's semiconcavity, computed through
`sup_semiconcave_of_joint_unitInterval` (the Schur modulus `σ + ρ²/q`) and
`jointSemiconcave_comp_of_chords`, is at most `SigV`. This is a quadratic
Riccati inequality in `SigV`; the corner family's was linear because its image
was not a supremum. Rule 3 permits a derived internal handle with a closure
inequality; the paper-facing statement carries no gap symbol.

## Rule 9C

Every margin was located and perturbed in exact rational arithmetic before any
Lean was written: `docs/archive/workflow-scratch/rung2/placable_family_feasibility_v2.py`.
The affine point below sits in an open ball of relative radius one-tenth; the
`quadDiagF` point clears every margin with its exact chord constants.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BJ2.3 (2026-10-07; audit item X1-3, user-approved, checklist 16 and
Rule 3 item 5): the family itself followed. Its interiority field `hInterior` and its
stage relief field `hStageRelief` are gone. Interiority is the predicate `Interior`
and the stage relief margin the predicate `StageRelief`, hypotheses `hInt`, `hSR` of
the results that read them; the family keeps only the sign of the latter, the field
`hcn : n < c` (the sanction hurts the Target at every state), which is strictly weaker.
`0 < q` now follows from the curvature margin (`hq`), as on `ChordEconomy`. The bridges
to the chord economy take exactly what they read: interiority (`toChord_interior`, the
vertex), the stage relief margin (`toChord_stageRelief`), or only the floor condition
`u₀ ≤ q`, i.e. `u₀/q ≤ 1` (`toChord_sfloor`, `toChord_lossOffset`, `toChord_flip_iff`).
With no rally softening, `n = 0`, the loss-offset bridge needs none of them
(`toChord_lossOffset_of_n_eq_zero`).
Where a result already assumes the sharp relief margin (RL), the stage relief margin
comes from it (`ChordEconomyCs.stageRelief_of_reliefSharp`, BG3.2). General in `F`.
-/
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralF
import Sanctions.Foundations.SemiconcaveJointComposition
import Sanctions.Foundations.StrongConcaveArgmaxStability
import Sanctions.Foundations.SemiconvexComposition
import Sanctions.Foundations.CrossDifferenceSemiconvex
import Sanctions.Theory.LockIn.SenderInvestment
import Sanctions.Theory.Mechanism.ContinuationChangesChoice
import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFCertificate
import Sanctions.Examples.ChordEconomy

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave Sanctions.TransitionChords

noncomputable section

/-! ## 0. Closed-form constants (standalone, so the margins can cite them) -/

/-- Sender value Lipschitz constant, `(r + w)/(1 − β_S·ghi)`: the stage
payoff's state-Lipschitz rate `r·s + w ≤ r + w` compounded through the
transition's upper state chord. -/
def plKS (βS ghi r w : ℝ) : ℝ := (r + w) / (1 - βS * ghi)

/-- Sender value lower state-slope, `w/(1 − β_S·glo)`: the stage floor `w`
(at `s = 0`) compounded through the lower state chord. -/
def plGS (βS glo w : ℝ) : ℝ := w / (1 - βS * glo)

/-- Sup-norm radius of the Sender carrier: the stage payoff's cube bound
`q/2 + u₀ + k + r + w`, geometrically summed. -/
def plMS (βS q u₀ k r w : ℝ) : ℝ := (q / 2 + u₀ + k + r + w) / (1 - βS)

/-- State modulus of the Sender's dynamic objective in `(x, s)`. -/
def plSig (βS SigV ghi KS Mx : ℝ) : ℝ := βS * (SigV * ghi ^ 2 + KS * Mx)

/-- Semiconcavity of the Sender Bellman image, the Schur modulus
`σ + ρ²/μ` of `Foundations/SemiconcaveSup`. Through round P the argument list
carried an unread `glo`; round Q1 dropped it (doc 85 §2.2), and the printed
type of the field `hSigV` moved with it, a Rule-18 rebaseline accepted on the
user's word. -/
def plSigImg (βS q r SigV ghi dhi KS Mx Mm Ms : ℝ) : ℝ :=
  plSig βS SigV ghi KS Mx
    + plRho βS r SigV ghi dhi KS Mm ^ 2 / plMu βS q SigV dhi KS Ms

/-- An upper bound on the Sender's dynamic marginal appetite for the first unit
of sanction at full defiance, `u₀ + r + β_S·KS·dhi`: the stage slope at the top
state plus the continuation's largest possible slope (`K_S` through the upper
sanction chord). A certificate, not the derivative of a value that need not be
differentiable. -/
def plAppetite (βS u₀ r KS dhi : ℝ) : ℝ := u₀ + r + βS * KS * dhi

/-! ### The curvature–closure pair as one condition on the primitives
(round M, doc 82 P2; the reader's round-K validation package, document 03 §4)

`hCurv` and `hSigV` are two inequalities in a *supplied* modulus `σ_V`. Once
the positive denominator `μ = Q − Dσ_V` is cleared, closure is a quadratic
inequality in `σ_V`, so "some `σ_V ≥ 0` satisfies both" is one condition on the
primitives. With `a = β_S g_hi²`, `D = β_S d_hi²`, `Q = q − β_S K_S M_s`,
`B₀ = β_S K_S M_x`, `C₀ = r + β_S K_S M_m`, `H₀ = β_S g_hi d_hi` (so
`H₀² = aD`), `L = (1 − a)Q + B₀D − 2C₀H₀` and `N = B₀Q + C₀²`:

    (∃ σ_V ≥ 0, curvature ∧ closure)  ⟺  Q > 0 ∧ 0 < L < 2Q ∧ L² ≥ 4DN,

and the vertex `σ_V = L/(2D)` is then a certificate. The two necessities a bare
discriminant misses are `L > 0` (from `p(t) ≥ 0` at the certificate, with the
corner `t = 0` forcing `B₀ = C₀ = 0`) and `L < 2Q` (closure gives
`B₀ ≤ (1 − a)t` and curvature `Dt < Q`). The structure keeps its supplied
modulus — the members use `σ_V = 1`, one such certificate, and the derived
constants of the manuscript depend on it — so this is a theorem about the
class, not a change to it: the paper-facing condition can be stated in the
primitives alone. -/

/-- `B₀ = β_S K_S M_x`. -/
def plRicB (βS KS Mx : ℝ) : ℝ := βS * KS * Mx
/-- `L = (1 − a)Q + B₀D − 2C₀H₀`. -/
def plRicL (βS q r ghi dhi KS Mx Mm Ms : ℝ) : ℝ :=
  (1 - plRicA βS ghi) * plRicQ βS q KS Ms + plRicB βS KS Mx * plRicD βS dhi
    - 2 * plRicC βS r KS Mm * plRicH βS ghi dhi
/-- `N = B₀Q + C₀²`. -/
def plRicN (βS q r KS Mx Mm Ms : ℝ) : ℝ :=
  plRicB βS KS Mx * plRicQ βS q KS Ms + plRicC βS r KS Mm ^ 2

/- `plMu`, `plRho`, `plRicD/A/Q/C/H` and the scalar core `riccati_feasible_iff`
moved to `ChordEconomy.lean` (round AU, 2026-09-25), unchanged: they never
depended on the payoff form. -/

/-- **Closure with its denominator cleared.** Under curvature (`μ > 0`), the
closure inequality `plSigImg ≤ σ_V` is `(C₀ + H₀σ_V)² ≤ ((1 − a)σ_V − B₀)(Q − Dσ_V)`. -/
theorem plSigImg_le_iff_cleared {βS q r t ghi dhi KS Mx Mm Ms : ℝ}
    (hμ : 0 < plMu βS q t dhi KS Ms) :
    plSigImg βS q r t ghi dhi KS Mx Mm Ms ≤ t ↔
      (plRicC βS r KS Mm + plRicH βS ghi dhi * t) ^ 2
        ≤ ((1 - plRicA βS ghi) * t - plRicB βS KS Mx) * (plRicQ βS q KS Ms - plRicD βS dhi * t) := by
  have e1 : plRho βS r t ghi dhi KS Mm = plRicC βS r KS Mm + plRicH βS ghi dhi * t := by
    unfold plRho plRicC plRicH; ring
  have e2 : t - plSig βS t ghi KS Mx = (1 - plRicA βS ghi) * t - plRicB βS KS Mx := by
    unfold plSig plRicA plRicB; ring
  have e3 : plMu βS q t dhi KS Ms = plRicQ βS q KS Ms - plRicD βS dhi * t := by
    unfold plMu plRicQ plRicD; ring
  unfold plSigImg
  rw [← e1, ← e2, ← e3]
  constructor
  · intro h
    have h1 : plRho βS r t ghi dhi KS Mm ^ 2 / plMu βS q t dhi KS Ms ≤ t - plSig βS t ghi KS Mx := by
      linarith
    exact (div_le_iff₀ hμ).mp h1
  · intro h
    have h1 := (div_le_iff₀ hμ).mpr h
    linarith

/-- **A certificate modulus exists iff the discriminant condition holds** on the
primitives: some `σ_V ≥ 0` satisfies the curvature margin and the Riccati closure
of `PlacableEconomyF` exactly when `Q > 0`, `0 < L < 2Q` and `L² ≥ 4DN`, in the
closed forms `plRicQ`, `plRicL`, `plRicN`, `plRicD`. Sign hypotheses as the
family supplies them. -/
theorem sigV_feasible_iff {βS q r ghi dhi KS Mx Mm Ms : ℝ}
    (hβS : 0 < βS) (hdhi : 0 < dhi) (hghi : 0 ≤ ghi) (ha : βS * ghi ^ 2 < 1)
    (hKS : 0 ≤ KS) (hMx : 0 ≤ Mx) (hMm : 0 ≤ Mm) (hr : 0 ≤ r) :
    (∃ t : ℝ, 0 ≤ t ∧ βS * (t * dhi ^ 2 + KS * Ms) < q ∧
        plSigImg βS q r t ghi dhi KS Mx Mm Ms ≤ t) ↔
      (0 < plRicQ βS q KS Ms ∧ 0 < plRicL βS q r ghi dhi KS Mx Mm Ms ∧
        plRicL βS q r ghi dhi KS Mx Mm Ms < 2 * plRicQ βS q KS Ms ∧
        4 * plRicD βS dhi * plRicN βS q r KS Mx Mm Ms
          ≤ plRicL βS q r ghi dhi KS Mx Mm Ms ^ 2) := by
  have hD : 0 < plRicD βS dhi := by unfold plRicD; positivity
  have ha0 : 0 ≤ plRicA βS ghi := by unfold plRicA; positivity
  have ha1 : plRicA βS ghi < 1 := by unfold plRicA; exact ha
  have hB : 0 ≤ plRicB βS KS Mx := by unfold plRicB; positivity
  have hC : 0 ≤ plRicC βS r KS Mm := by unfold plRicC; positivity
  have hH : 0 ≤ plRicH βS ghi dhi := by unfold plRicH; positivity
  have hHaD : plRicH βS ghi dhi ^ 2 = plRicA βS ghi * plRicD βS dhi := by
    unfold plRicH plRicA plRicD; ring
  have hcurv : ∀ t : ℝ, (βS * (t * dhi ^ 2 + KS * Ms) < q) ↔ plRicD βS dhi * t < plRicQ βS q KS Ms := by
    intro t; unfold plRicD plRicQ; constructor <;> intro h <;> linarith
  have hμ : ∀ t : ℝ, plRicD βS dhi * t < plRicQ βS q KS Ms → 0 < plMu βS q t dhi KS Ms := by
    intro t h; unfold plMu; unfold plRicD plRicQ at h; linarith
  have core := riccati_feasible_iff (Q := plRicQ βS q KS Ms) hD ha0 ha1 hB hC hH hHaD
  unfold plRicL plRicN
  rw [← core]
  constructor
  · rintro ⟨t, ht0, hc, hcl⟩
    have hDt := (hcurv t).mp hc
    exact ⟨t, ht0, hDt, (plSigImg_le_iff_cleared (hμ t hDt)).mp hcl⟩
  · rintro ⟨t, ht0, hDt, hq⟩
    exact ⟨t, ht0, (hcurv t).mpr hDt, (plSigImg_le_iff_cleared (hμ t hDt)).mpr hq⟩

/-- **The vertex modulus certifies** whenever the condition holds. -/
theorem exists_SigV_of_discriminant {βS q r ghi dhi KS Mx Mm Ms : ℝ}
    (hβS : 0 < βS) (hdhi : 0 < dhi) (hghi : 0 ≤ ghi) (ha : βS * ghi ^ 2 < 1)
    (hKS : 0 ≤ KS) (hMx : 0 ≤ Mx) (hMm : 0 ≤ Mm) (hr : 0 ≤ r)
    (hQ : 0 < plRicQ βS q KS Ms) (hL : 0 < plRicL βS q r ghi dhi KS Mx Mm Ms)
    (hL2 : plRicL βS q r ghi dhi KS Mx Mm Ms < 2 * plRicQ βS q KS Ms)
    (hdisc : 4 * plRicD βS dhi * plRicN βS q r KS Mx Mm Ms
      ≤ plRicL βS q r ghi dhi KS Mx Mm Ms ^ 2) :
    ∃ t : ℝ, 0 ≤ t ∧ βS * (t * dhi ^ 2 + KS * Ms) < q ∧
      plSigImg βS q r t ghi dhi KS Mx Mm Ms ≤ t :=
  (sigV_feasible_iff hβS hdhi hghi ha hKS hMx hMm hr).mpr ⟨hQ, hL, hL2, hdisc⟩

/-- Target value lower state-slope, `v/(1 − β_T·glo)`: the Target's direct
valuation of the state compounded through the lower state chord. The corner
family's slope; on the placable family it is the `n = 0` case of `plGTn`. -/
def plGT (βT glo v : ℝ) : ℝ := v / (1 - βT * glo)

/-- **Target value lower state-slope, floor-refined** (round J, doc 77 K2):
`(v + n·u₀/q)/(1 − β_T·glo)`. The Target's stage payoff `s(nx − c) + vx` rises
in the state at the rate `v + n·s`, and the Sender's response at defiance is
never below the stage floor `u₀/q` on either carrier (`responsePath_ge_b`,
`stageResp_ge_b`), so the rate `v + n·u₀/q` compounds through the lower state
chord. Under the loss-offset margin a rally-induced sanction increase is a net gain for the
Target's value slope, so no further rally correction appears. At `n = 0` this
is `plGT`. -/
def plGTn (βT glo v n u₀ q : ℝ) : ℝ := (v + n * u₀ / q) / (1 - βT * glo)

/-- The previous loss-offset form, at the slope `plGT`, implies the floor-refined
one at the slope `plGTn` (round J): the refined slope is larger by
`n·u₀/(q(1 − β_T·glo)) ≥ 0`. -/
theorem hTMargin_of_old {βT glo dlo v n u₀ q c : ℝ} (hβT : 0 ≤ βT) (hdlo : 0 ≤ dlo)
    (hden : 0 < 1 - βT * glo) (hn : 0 ≤ n) (hu₀ : 0 ≤ u₀) (hq : 0 < q)
    (h : c ≤ βT * dlo * plGT βT glo v) : c ≤ βT * dlo * plGTn βT glo v n u₀ q := by
  unfold plGT at h
  unfold plGTn
  have h1 : 0 ≤ n * u₀ / q := div_nonneg (mul_nonneg hn hu₀) hq.le
  have h2 : v / (1 - βT * glo) ≤ (v + n * u₀ / q) / (1 - βT * glo) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  exact h.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hβT hdlo))

/-- **The semiconvexity modulus of the Sender carrier, closed form** (Rung 3):
the fixed point of the linear closure `σ ↦ βS·(σ·ghi² + KS·Mcx)`. Zero when the
transition's state sections are convex (`Mcx = 0`). -/
def plSigC (βS KS Mcx ghi : ℝ) : ℝ := βS * KS * Mcx / (1 - βS * ghi ^ 2)

/-- **The loss offset as a valuation threshold** (round L, doc 80 M10): the
floor-refined loss offset `c ≤ β_T·d_lo·g_T` is equivalent to
`v ≥ c(1 − β_T g_lo)/(β_T d_lo) − n·u₀/q` — the Target incumbent's valuation of
the state must cover the sanction's per-unit loss discounted through the two
lower chords, net of the rally softening at the response floor. A
rearrangement of the field, not a new condition; a sufficient-valuation
threshold, not a behavioural characterisation
(`loss_offset_converse_counterexample`). -/
theorem lossOffset_iff_v_ge {βT glo dlo v n u₀ q c : ℝ} (hβT : 0 < βT) (hdlo : 0 < dlo)
    (hglo : βT * glo < 1) :
    c ≤ βT * dlo * plGTn βT glo v n u₀ q ↔
      c * (1 - βT * glo) / (βT * dlo) - n * u₀ / q ≤ v := by
  have h1 : 0 < 1 - βT * glo := by linarith
  have h2 : 0 < βT * dlo := mul_pos hβT hdlo
  unfold plGTn
  rw [mul_div_assoc', le_div_iff₀ h1, sub_le_iff_le_add, div_le_iff₀ h2]
  constructor <;> intro h <;> linarith

/-- **The `n`-interval with the family's stage relief margin** (round Q2): the
sign, the stage relief margin `ℓq < k(c − n)`, the floor-refined loss offset and
the sharp relief margin hold together exactly when
`max(0, n_min) ≤ n < c − ℓ·M_tot/k`; with `q ≤ M_tot` the stage margin is the
weaker of the two accommodation margins and drops out of the upper end. -/
theorem rally_softening_interval_iff' {βT glo dlo v u₀ q c ℓ k Mtot n : ℝ}
    (hβT : 0 < βT) (hdlo : 0 < dlo) (hglo : βT * glo < 1) (hq : 0 < q) (hu₀ : 0 < u₀)
    (hk : 0 < k) (hℓ : 0 < ℓ) (hqM : q ≤ Mtot) :
    (0 ≤ n ∧ ℓ * q < k * (c - n) ∧ c ≤ βT * dlo * plGTn βT glo v n u₀ q ∧
        ℓ * Mtot < k * (c - n)) ↔
      (max 0 ((c * (1 - βT * glo) / (βT * dlo) - v) * q / u₀) ≤ n ∧
        n < c - ℓ * Mtot / k) := by
  have hstage : ℓ * Mtot < k * (c - n) → ℓ * q < k * (c - n) := by
    intro h
    have := mul_le_mul_of_nonneg_left hqM hℓ.le
    linarith
  have hA : (c * (1 - βT * glo) / (βT * dlo) - v) * q / u₀ ≤ n ↔
      c * (1 - βT * glo) / (βT * dlo) - n * u₀ / q ≤ v := by
    rw [div_le_iff₀ hu₀, ← le_div_iff₀ hq, sub_le_comm]
  have hC : n < c - ℓ * Mtot / k ↔ ℓ * Mtot < k * (c - n) := by
    rw [lt_sub_comm, div_lt_iff₀ hk, mul_comm (c - n) k]
  rw [lossOffset_iff_v_ge hβT hdlo hglo, max_le_iff, hA, hC]
  constructor
  · rintro ⟨h1, _, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h3⟩, h4⟩
    exact ⟨h1, hstage h4, h3, h4⟩

/-- **The rally softening `n` as one interval** (round L, doc 80 M10; the
reader's round-K validation package, document 03 §6.2). With the other data
fixed, the four restrictions that mention `n` — its sign, the stage flip
`ℓq < u₀(c − n)`, the floor-refined loss offset, and the sharp relief margin
`ℓ·M_tot < k(c − n)` — hold together exactly when
`max(0, n_min) ≤ n < min(c − ℓq/u₀, c − ℓM_tot/k)` with
`n_min = (c(1 − β_T g_lo)/(β_T d_lo) − v)·q/u₀`. So a larger rally softening
relaxes the loss offset (its lower end) and tightens the two accommodation
margins (its upper end). An interval of certificates, not the set of economies
in which defiance occurs. With the family's own condition since round Q2 —
the stage relief margin `ℓq < k(c − n)` in place of the flip — the interval is
`max(0, n_min) ≤ n < c − ℓM_tot/k` (`rally_softening_interval_iff'` above),
since `q ≤ M_tot` makes the stage margin the weaker of the two. -/
theorem rally_softening_interval_iff {βT glo dlo v u₀ q c ℓ k Mtot n : ℝ}
    (hβT : 0 < βT) (hdlo : 0 < dlo) (hglo : βT * glo < 1) (hq : 0 < q) (hu₀ : 0 < u₀)
    (hk : 0 < k) :
    (0 ≤ n ∧ ℓ * q < u₀ * (c - n) ∧ c ≤ βT * dlo * plGTn βT glo v n u₀ q ∧
        ℓ * Mtot < k * (c - n)) ↔
      (max 0 ((c * (1 - βT * glo) / (βT * dlo) - v) * q / u₀) ≤ n ∧
        n < min (c - ℓ * q / u₀) (c - ℓ * Mtot / k)) := by
  have hA : (c * (1 - βT * glo) / (βT * dlo) - v) * q / u₀ ≤ n ↔
      c * (1 - βT * glo) / (βT * dlo) - n * u₀ / q ≤ v := by
    rw [div_le_iff₀ hu₀, ← le_div_iff₀ hq, sub_le_comm]
  have hB : n < c - ℓ * q / u₀ ↔ ℓ * q < u₀ * (c - n) := by
    rw [lt_sub_comm, div_lt_iff₀ hu₀, mul_comm (c - n) u₀]
  have hC : n < c - ℓ * Mtot / k ↔ ℓ * Mtot < k * (c - n) := by
    rw [lt_sub_comm, div_lt_iff₀ hk, mul_comm (c - n) k]
  rw [lossOffset_iff_v_ge hβT hdlo hglo, max_le_iff, lt_min_iff, hA, hB, hC]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    exact ⟨h1, h2, h3, h4⟩

/-! ## 1. The structure -/

/-- **An admissible member of the placable-Sender family.** See the file
header. Every field is either a chord regularity on `F`, a coefficient sign, or
an inequality among the coefficients and the closed-form constants above. Since
renovation item BJ2.3 (2026-10-07) interiority and the stage relief margin are not
fields: they are the predicates `Interior` and `StageRelief`, hypotheses of the
results that read them, and the family keeps only the sign `hcn : n < c`. General in
`F`. -/
structure PlacableEconomyF where
  /-- The transition. -/
  F : ℝ → ℝ → ℝ
  F_continuous : Continuous (fun p : ℝ × ℝ => F p.1 p.2)
  F_mono_x : ∀ s, Monotone (fun x => F x s)
  F_mono_s : ∀ x, Monotone (fun s => F x s)
  F_diag : ∀ x, F x x = x
  /-- Chord constants. -/
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
  /-- **State-section semiconvexity of the transition** (Rung 3, chord form):
  each section `x ↦ F x s` lies above its chords by at most
  `Mcx/2·t(1−t)·Δx²`. Zero for the affine law and for convex sections. -/
  Mcx : ℝ
  hMcx0 : 0 ≤ Mcx
  hFcx : ∀ s ∈ Icc (0 : ℝ) 1, SemiconvexOnSet (fun y => F y s) (Icc (0 : ℝ) 1) Mcx
  /-- **Two-sided mixed chord of the transition** (Rung 3): the state increment
  changes by at most `Mmix·|Δx|·|Δs|` across a sanction increment. Zero for the
  affine law and for every additively separable transition. -/
  Mmix : ℝ
  hFmix : MixedChordBound F Mmix
  /-- Discounting. `δ` is carried for `Params` and is inert under a general
  transition (Rule 22). -/
  δ : ℝ
  βS : ℝ
  βT : ℝ
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hβS0 : 0 < βS
  hβS1 : βS < 1
  hβT0 : 0 < βT
  hβT1 : βT < 1
  /-- Payoff coefficients. -/
  q : ℝ
  u₀ : ℝ
  k : ℝ
  r : ℝ
  w : ℝ
  ℓ : ℝ
  c : ℝ
  n : ℝ
  v : ℝ
  hu₀ : 0 < u₀
  hr : 0 ≤ r
  hw : 0 < w
  hℓ : 0 < ℓ
  hn : 0 ≤ n
  /-- The supplied Sender-carrier semiconcavity modulus (Rule 3: a derived
  internal handle, closed by `hSigV`; its sign `0 ≤ SigV` is the theorem
  `hSigV0`, from closure and curvature). -/
  SigV : ℝ
  /-- **Curvature margin.** The Sender's own cost curvature out-curves the
  continuation's sanction curvature, so the dynamic objective is strictly
  concave in the sanction and the argmax is unique. -/
  hCurv : βS * (SigV * dhi ^ 2 + plKS βS ghi r w * Ms) < q
  /-- **Riccati closure.** The image's Schur semiconcavity is at most `SigV`. -/
  hSigV : plSigImg βS q r SigV ghi dhi (plKS βS ghi r w) Mx Mm Ms ≤ SigV
  /-- The placation rate is positive. Through round AM this sign was derived
  from placability `A ≤ k`; since round AP (2026-09-23, doc 102 J2, on the
  user's word) placability is a hypothesis of the results that read it, so
  the sign is a primitive of the family, as the paper states it. -/
  hk : 0 < k
  /-- The Target's direct valuation of the state is positive. Through round
  AM this sign was derived from the loss-offset margin; since round AP the
  margin is a hypothesis of the results that read it (doc 102 J2). -/
  hv : 0 < v
  /-- **The sanction hurts the Target at every state**: the rally softening `n`
  of the sanction pain is below the pain `c` itself, so the Target's net pain
  `c − n·x` per unit of sanction is positive on `[0, 1]`. Renovation item BJ2.3
  (2026-10-07; audit item X1-3, Rule 3 item 5, user-approved): this sign replaces
  the stage relief field `hStageRelief : ℓ·q < k·(c − n)`, which implied it
  (`ℓ, q, k > 0`) and is now the hypothesis `StageRelief` of the results that read
  it. Through round Q1 that field was the stage flip `ℓ·q < u₀·(c − n)`, a
  hypothesis since round Q2 (doc 85 §3.2, S2). -/
  hcn : n < c

/-- **Placability** — since round AP a hypothesis, not a field: the placation
rate covers the upper appetite `A = u₀ + r + β_S·K_S·d_hi`, so a fully
compliant Target is not sanctioned at all. Results that read it take
`(hP : E.Placable)`; the non-placable case `k < A` is treated on the same
structure (doc 102 §1 row 6). -/
def PlacableEconomyF.Placable (E : PlacableEconomyF) : Prop :=
  plAppetite E.βS E.u₀ E.r (plKS E.βS E.ghi E.r E.w) E.dhi ≤ E.k

/-- **Loss-offset margin, floor-refined form** (round J, doc 77 K2; a field
through round AM, a hypothesis since round AP, doc 102 J2, on the user's
word). The Target's sanction pain `c` per unit of sanction is covered by the
discounted continuation gain at the value slope
`g_T = (v + n·u₀/q)/(1 − β_T·glo)`: the direct state valuation `v`, plus the
rally term `n` evaluated at the response floor `u₀/q`, compounded through the
lower state chord. So the forward-looking Target defies — and, by the same
inequality, a rally-induced sanction increase is a net gain for the Target's
value slope. Results that read it take `(hTM : E.LossOffset)`; its complement
is the relief side of the general-transition bracket (doc 102 §2). -/
def PlacableEconomyF.LossOffset (E : PlacableEconomyF) : Prop :=
  E.c ≤ E.βT * E.dlo * plGTn E.βT E.glo E.v E.n E.u₀ E.q

/-- **Interiority** — a field `hInterior` until renovation item BJ2.3 (2026-10-07;
audit item X1-3, user-approved), now a hypothesis of the results that read it: the
upper appetite bound `A = u₀ + r + β_S·K_S·d_hi` at full defiance is below the cost
curvature `q`, so the Sender never sanctions fully. It is the chord economy's
`ChordEconomy.Interior` at `toChord` (`toChord_interior`). Results that read it take
`(hInt : E.Interior)`; most read only `u₀ ≤ q` through it (`u₀_le_q`). General in
`F`. -/
def PlacableEconomyF.Interior (E : PlacableEconomyF) : Prop :=
  plAppetite E.βS E.u₀ E.r (plKS E.βS E.ghi E.r E.w) E.dhi < E.q

/-- **The stage relief margin** — a field `hStageRelief` until renovation item BJ2.3
(2026-10-07; audit item X1-3, user-approved), now a hypothesis of the results that
read it; the family keeps only its sign `hcn : n < c`. At the margin, a unit of
compliance costs `ℓ` and, below the placation level, buys `k/q` units of stage
sanction relief worth at least `c − n` each: `ℓ·q < k·(c − n)`. It is what the
myopic reading needs, and it is the chord economy's `ChordEconomyRelief.StageRelief`
at `toChord` (`toChord_stageRelief`). On the enriched subclass the sharp relief margin
(RL) implies it, since `q ≤ M_tot` (`ChordEconomyCs.stageRelief_of_reliefSharp`,
BG3.2). General in `F`. -/
def PlacableEconomyF.StageRelief (E : PlacableEconomyF) : Prop :=
  E.ℓ * E.q < E.k * (E.c - E.n)

/-- **The enriched subclass: a placable member whose transition also has
semiconvex sanction sections** (Rule 3, authorized by the user 2026-09-05, doc
63; moved off the base family 2026-09-05, doc 65, so that no result stated over
`PlacableEconomyF` carries a hypothesis it never reads). Each section
`s ↦ F x s` lies above its chords by at most `Mcs/2·t(1−t)·Δs²`. Zero for the
affine law and for every convex sanction section; `1/5` at `quadDiagF`.
Consumed by the reading `01` and the four-cell theorem
(`PlacableSenderRegime01`), where it bounds the Sender objective's curvature
from below and so the response's relief rate in compliance, and since round Q2
by the flip-free activation theorem (`PlacableSenderReliefActivation`,
headline row 47; the "only" of the earlier wording corrected 2026-09-15). -/
structure PlacableEconomyFcs extends PlacableEconomyF where
  Mcs : ℝ
  hMcs0 : 0 ≤ Mcs
  hFcs : ∀ x ∈ Icc (0 : ℝ) 1, SemiconvexOnSet (fun s => F x s) (Icc (0 : ℝ) 1) Mcs

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-! ## 1b. The derived fields (round Q1, 2026-09-11; doc 85 §2.1)

Seven facts that were proof fields of the structure through round P became
theorems of it from round Q1: feasibility of `F` on the square, the two chord
orderings `glo ≤ ghi` and `dlo ≤ dhi`, the sign `0 ≤ Mmix`, and the signs
`0 < q`, `0 ≤ σ_V`, `0 < v`. Since round AP (2026-09-23) the last, `0 < v`, is
a field again (`hv`), together with `0 < k` (`hk`), because the two conditions
that implied them — the loss-offset margin and placability — are hypotheses
of the results that read them rather than fields; `k_pos` keeps its name and
reads the field. Each follows from the fields that remain (the
reader's validation package of 2026-09-11, document 01; doc 84 §2.2), and each
keeps the name it had as a field, so a consumer written `E.hq` or `E.F_mem`
reads the theorem. The scalar helpers are stated over raw data with no member
binder, so none can reach for the fact it derives; `derived_fields` bundles the
seven for the manuscript (panel C of the admissibility appendix). Round P had
carried the seven as fields with a raw-data constructor filling them
(`Raw.toEconomy`, retired here); deleting them moved nine contract rows, a
Rule-18 rebaseline accepted on the user's word (doc 85 Q1). Since renovation item
BJ2.3 (2026-10-07) `0 < q` comes from the curvature margin and `σ_V ≥ 0`
(`hq`), as on `ChordEconomy` (BJ2.1), because interiority, from which it was derived
(`plq_pos_of_interior`, kept), is no longer a field. -/

/-- `K_S > 0` from the signs and the band ceiling, over raw data. -/
theorem plKS_pos_of {βS ghi r w : ℝ} (hβS0 : 0 < βS) (hβS1 : βS < 1)
    (hghi1 : ghi ≤ 1) (hr : 0 ≤ r) (hw : 0 < w) : 0 < plKS βS ghi r w := by
  have hβg : βS * ghi ≤ βS * 1 := mul_le_mul_of_nonneg_left hghi1 hβS0.le
  unfold plKS
  exact div_pos (by linarith) (by linarith)

/-- **`q > 0` from interiority** (R5). The appetite `A = u₀ + r + β_S·K_S·d_hi`
is positive, and interiority puts `q` above it. Since renovation item BJ2.3 the
member's `hq` no longer uses it (interiority is not a field); kept as a raw-data
fact. -/
theorem plq_pos_of_interior {βS ghi dhi u₀ r w q : ℝ} (hβS0 : 0 < βS) (hβS1 : βS < 1)
    (hghi1 : ghi ≤ 1) (hdhi : 0 ≤ dhi) (hu₀ : 0 < u₀) (hr : 0 ≤ r) (hw : 0 < w)
    (hInt : plAppetite βS u₀ r (plKS βS ghi r w) dhi < q) : 0 < q := by
  have hKS := plKS_pos_of hβS0 hβS1 hghi1 hr hw
  have h1 : 0 ≤ βS * plKS βS ghi r w * dhi :=
    mul_nonneg (mul_nonneg hβS0.le hKS.le) hdhi
  unfold plAppetite at hInt
  linarith

/-- **`σ_V ≥ 0` from the Riccati closure** (R6). Closure reads
`β_S(σ_V g_hi² + K_S M_x) + ϱ²/μ ≤ σ_V`; with `μ > 0` (the curvature margin) the
last term is nonnegative, so `(1 − β_S g_hi²)·σ_V ≥ 0`, and the coefficient is
positive. Stated for any nonnegative `KS`. Keep the curvature margin: it is
what makes the division go the right way. And do not strengthen to
`0 < σ_V`: `σ_V = 0` is a legitimate boundary modulus. -/
theorem plSigV_nonneg_of_closure {βS q r SigV ghi dhi KS Mx Mm Ms : ℝ}
    (hβS0 : 0 < βS) (hβS1 : βS < 1) (hghi0 : 0 ≤ ghi) (hghi1 : ghi ≤ 1)
    (hKS : 0 ≤ KS) (hMx : 0 ≤ Mx)
    (hCurv : βS * (SigV * dhi ^ 2 + KS * Ms) < q)
    (hSigV : plSigImg βS q r SigV ghi dhi KS Mx Mm Ms ≤ SigV) : 0 ≤ SigV := by
  have hmu : 0 < plMu βS q SigV dhi KS Ms := by unfold plMu; linarith
  have hsq : 0 ≤ plRho βS r SigV ghi dhi KS Mm ^ 2 / plMu βS q SigV dhi KS Ms :=
    div_nonneg (sq_nonneg _) hmu.le
  have hMx' : 0 ≤ βS * (KS * Mx) := mul_nonneg hβS0.le (mul_nonneg hKS hMx)
  have hsq1 : ghi ^ 2 ≤ 1 := by nlinarith
  have hcoef : 0 < 1 - βS * ghi ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq1 hβS0.le
    linarith
  unfold plSigImg plSig at hSigV
  have key : 0 ≤ (1 - βS * ghi ^ 2) * SigV := by nlinarith
  by_contra hneg
  have := mul_neg_of_pos_of_neg hcoef (not_le.mp hneg)
  linarith

/-- **`v > 0` from the loss offset** (R7). Clearing the positive denominator of
`g_T = (v + n·u₀/q)/(1 − β_T g_lo)`, the offset `c ≤ β_T d_lo g_T` reads
`c(1 − β_T g_lo) ≤ β_T d_lo (v + n u₀/q)`. Since `g_lo + d_lo ≤ 1`, the left
factor exceeds `β_T d_lo` by at least `1 − β_T > 0`, so with `c > 0`,
`c < v + n u₀/q ≤ v + n`, i.e. `v > c − n > 0`. The sign `c > n` is the family's
field `hcn` since renovation item BJ2.3 (from round Q2 it came from the stage relief
field `ℓq < k(c − n)`, through round Q1 from the stage flip); on the enriched subclass
(RL) implies it. -/
theorem plv_pos_of_lossOffset {βT glo dlo v n u₀ q c : ℝ} (hβT0 : 0 < βT) (hβT1 : βT < 1)
    (hdlo0 : 0 < dlo) (hsum : glo + dlo ≤ 1) (hq : 0 < q) (hu₀q : u₀ < q) (hn : 0 ≤ n)
    (hcn : 0 < c - n) (hT : c ≤ βT * dlo * plGTn βT glo v n u₀ q) : 0 < v := by
  have hglo1 : glo < 1 := by linarith
  have hD : 0 < 1 - βT * glo := by
    have := mul_pos hβT0 (sub_pos.2 hglo1)
    linarith
  have hB : 0 < βT * dlo := mul_pos hβT0 hdlo0
  have hc : 0 < c := by linarith
  have hT' : c * (1 - βT * glo) ≤ βT * dlo * (v + n * u₀ / q) := by
    unfold plGTn at hT
    rw [← mul_div_assoc, le_div_iff₀ hD] at hT
    exact hT
  have hsum' : βT * (glo + dlo) ≤ βT * 1 := mul_le_mul_of_nonneg_left hsum hβT0.le
  have hDB : βT * dlo < 1 - βT * glo := by linarith
  have h1 : c * (βT * dlo) < c * (1 - βT * glo) := mul_lt_mul_of_pos_left hDB hc
  have h2 : c < v + n * u₀ / q := by
    have h := lt_of_lt_of_le h1 hT'
    rw [mul_comm c] at h
    exact lt_of_mul_lt_mul_left h hB.le
  have h3 : n * u₀ / q ≤ n := by
    rw [div_le_iff₀ hq]
    exact mul_le_mul_of_nonneg_left hu₀q.le hn
  linarith

/-- `glo ≤ ghi`: the state band between the states `0` and `1`, at any sanction. -/
theorem hglo_ghi : E.glo ≤ E.ghi := E.hbandAll.rates_le

/-- `dlo ≤ dhi`: the two sanction chords at state `0` between sanctions `0` and `1`. -/
theorem hdlo_dhi : E.dlo ≤ E.dhi := sanctionChord_rates_le E.hSlo E.hShi

/-- `0 ≤ Mmix`: the absolute mixed bound at the corners. -/
theorem hMmix0 : 0 ≤ E.Mmix := E.hFmix.nonneg

/-- The transition maps the square into itself: monotonicity in each argument
and the fixed diagonal (`Params.F_mem_derived` is the abstract form). -/
theorem F_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → E.F x s ∈ Icc (0 : ℝ) 1 :=
  fun _ _ hx hs => Sanctions.mem_Icc_of_mono_of_diag E.F_mono_x E.F_mono_s E.F_diag hx hs

theorem ghi_nonneg : 0 ≤ E.ghi := le_trans E.hglo0 E.hglo_ghi
theorem dhi_nonneg : 0 ≤ E.dhi := le_trans E.hdlo0.le E.hdlo_dhi

/-- `0 ≤ σ_V`: the Riccati closure with the curvature margin. -/
theorem hSigV0 : 0 ≤ E.SigV :=
  plSigV_nonneg_of_closure E.hβS0 E.hβS1 E.ghi_nonneg E.hghi1
    (plKS_pos_of E.hβS0 E.hβS1 E.hghi1 E.hr E.hw).le E.hMx0 E.hCurv E.hSigV

/-- **`0 < q` from the curvature margin** (renovation item BJ2.3, 2026-10-07; general
in `F`). The margin puts `q` above `β_S·(σ_V·d_hi² + K_S·M_s)`, a sum of nonnegative
terms (`σ_V ≥ 0` from the Riccati closure, `hSigV0`): the Sender's stage curvature has
to beat the continuation's sanction curvature, so it is positive. Until BJ2.3 it was
derived from the interiority field, which the family no longer carries; the statement
is unchanged. -/
theorem hq : 0 < E.q := by
  have hKS := plKS_pos_of E.hβS0 E.hβS1 E.hghi1 E.hr E.hw
  have h1 : 0 ≤ E.SigV * E.dhi ^ 2 := mul_nonneg E.hSigV0 (sq_nonneg _)
  have h2 : 0 ≤ plKS E.βS E.ghi E.r E.w * E.Ms := mul_nonneg hKS.le E.hMs0
  have h3 : 0 ≤ E.βS * (E.SigV * E.dhi ^ 2 + plKS E.βS E.ghi E.r E.w * E.Ms) :=
    mul_nonneg E.hβS0.le (add_nonneg h1 h2)
  linarith [E.hCurv]

/-- **The six derived fields, bundled** for the manuscript's panel C: what a
member no longer supplies (seven through round AM; `0 < v` is a field again
since round AP, because the margin that implied it is no longer a field). -/
theorem derived_fields :
    (∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → E.F x s ∈ Icc (0 : ℝ) 1) ∧
    E.glo ≤ E.ghi ∧ E.dlo ≤ E.dhi ∧ 0 ≤ E.Mmix ∧ 0 < E.q ∧ 0 ≤ E.SigV :=
  ⟨E.F_mem, E.hglo_ghi, E.hdlo_dhi, E.hMmix0, E.hq, E.hSigV0⟩

/-! ## 2. Derived constants and elementary consequences -/

/-- `K_S`. -/
def KS : ℝ := plKS E.βS E.ghi E.r E.w
/-- `g_S`. -/
def gS : ℝ := plGS E.βS E.glo E.w
/-- `M_S`. -/
def MS : ℝ := plMS E.βS E.q E.u₀ E.k E.r E.w
/-- `μ`. -/
def mu : ℝ := plMu E.βS E.q E.SigV E.dhi E.KS E.Ms
/-- `ρ`. -/
def rho : ℝ := plRho E.βS E.r E.SigV E.ghi E.dhi E.KS E.Mm
/-- `g_T`, floor-refined: `(v + n·u₀/q)/(1 − β_T·glo)` (round J). -/
def gT : ℝ := plGTn E.βT E.glo E.v E.n E.u₀ E.q

theorem βS_ghi_lt_one : E.βS * E.ghi < 1 := by
  have := E.hβS1; have := E.hghi1; have := E.hβS0; have := E.hglo0; have := E.hglo_ghi
  nlinarith

theorem βS_glo_lt_one : E.βS * E.glo < 1 := by
  have := E.βS_ghi_lt_one; have := E.hβS0; have := E.hglo_ghi
  nlinarith

theorem one_sub_βS_ghi_pos : 0 < 1 - E.βS * E.ghi := by linarith [E.βS_ghi_lt_one]
theorem one_sub_βS_glo_pos : 0 < 1 - E.βS * E.glo := by linarith [E.βS_glo_lt_one]

theorem KS_pos : 0 < E.KS := by
  unfold KS plKS
  exact div_pos (by linarith [E.hr, E.hw]) E.one_sub_βS_ghi_pos

theorem KS_nonneg : 0 ≤ E.KS := E.KS_pos.le

theorem gS_pos : 0 < E.gS := by
  unfold gS plGS
  exact div_pos E.hw E.one_sub_βS_glo_pos

theorem mu_pos : 0 < E.mu := by
  unfold mu plMu
  have := E.hCurv
  unfold KS; linarith

theorem k_pos : 0 < E.k := E.hk

/-- The Target's net sanction pain at the top state is positive: the field `hcn`
(renovation item BJ2.3; until then derived from the stage relief field). -/
theorem c_sub_n_pos : 0 < E.c - E.n := sub_pos.2 E.hcn

/-- **The stage relief margin implies the sign field** `n < c` (renovation item BJ2.3):
`ℓ, q, k > 0`, so `ℓ·q < k·(c − n)` forces `c − n > 0`. So `hcn` is weaker than the
stage relief field it replaced. General in `F`. -/
theorem hcn_of_stageRelief (hSR : E.StageRelief) : E.n < E.c := by
  have hℓq : 0 < E.ℓ * E.q := mul_pos E.hℓ E.hq
  by_contra hcon
  have : E.k * (E.c - E.n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos E.k_pos.le (by linarith [not_lt.mp hcon])
  unfold PlacableEconomyF.StageRelief at hSR
  linarith

theorem βT_glo_lt_one : E.βT * E.glo < 1 := by
  have := E.hβT1; have := E.hβT0; have := E.hglo0; have := E.hglo_ghi; have := E.hghi1
  nlinarith

theorem gT_pos : 0 < E.gT := by
  unfold gT plGTn
  have h : 0 ≤ E.n * E.u₀ / E.q := div_nonneg (mul_nonneg E.hn E.hu₀.le) E.hq.le
  exact div_pos (by linarith [E.hv]) (by linarith [E.βT_glo_lt_one])

/-- The slope identity `g_T·(1 − β_T·glo) = v + n·u₀/q`. -/
theorem gT_mul : E.gT * (1 - E.βT * E.glo) = E.v + E.n * E.u₀ / E.q := by
  unfold gT plGTn
  have h : (1 - E.βT * E.glo) ≠ 0 := by linarith [E.βT_glo_lt_one]
  exact div_mul_cancel₀ _ h

/-- The floor `u₀/q` is below one: from interiority, `u₀ < A < q`. Since renovation
item BJ2.3 interiority is the hypothesis `hInt`, no longer a field. General in `F`. -/
theorem u₀_lt_q (hInt : E.Interior) : E.u₀ < E.q := by
  have h := hInt
  unfold PlacableEconomyF.Interior plAppetite at h
  have h1 : 0 ≤ E.βS * E.KS * E.dhi :=
    mul_nonneg (mul_nonneg E.hβS0.le E.KS_nonneg) (by linarith [E.hdlo0, E.hdlo_dhi])
  unfold KS at h1
  linarith [E.hr]

/-- The floor condition `u₀ ≤ q`, i.e. `u₀/q ≤ 1`, from interiority (renovation item
BJ2.3): the form in which most bridges to the chord economy read interiority. General
in `F`. -/
theorem u₀_le_q (hInt : E.Interior) : E.u₀ ≤ E.q := (E.u₀_lt_q hInt).le

/-! ## 3. The `Params` -/

/-- `σ_C`, the carrier's semiconvexity modulus (Rung 3). -/
def SigC : ℝ := plSigC E.βS E.KS E.Mcx E.ghi

theorem βS_ghi_sq_lt_one : E.βS * E.ghi ^ 2 < 1 := by
  have h := E.βS_ghi_lt_one
  have hghi0 : 0 ≤ E.ghi := le_trans E.hglo0 E.hglo_ghi
  have hsq : E.ghi ^ 2 ≤ E.ghi := by
    have := mul_nonneg hghi0 (sub_nonneg.2 E.hghi1)
    nlinarith
  have := mul_le_mul_of_nonneg_left hsq E.hβS0.le
  linarith

theorem SigC_nonneg : 0 ≤ E.SigC := by
  unfold SigC plSigC
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg E.hβS0.le E.KS_nonneg) E.hMcx0
  · linarith [E.βS_ghi_sq_lt_one]

/-- **Linear closure**: the image modulus `βS·(σ_C·ghi² + KS·Mcx)` is exactly
`σ_C`. -/
theorem SigC_closure : E.βS * (E.SigC * E.ghi ^ 2 + E.KS * E.Mcx) ≤ E.SigC := by
  have hpos : 0 < 1 - E.βS * E.ghi ^ 2 := by linarith [E.βS_ghi_sq_lt_one]
  have hne : 1 - E.βS * E.ghi ^ 2 ≠ 0 := hpos.ne'
  apply le_of_eq
  unfold SigC plSigC
  field_simp
  ring

/-- **The family's `Params`.** The stage payoffs and the derived static
selector are the corner family's; the transition is `E.F`. -/
def toParams : AbstractGame.Params where
  δ := E.δ
  δ_mem := ⟨E.hδ0, E.hδ1⟩
  β_T := E.βT
  β_T_mem := ⟨E.hβT0.le, E.hβT1⟩
  β_S := E.βS
  β_S_mem := ⟨E.hβS0.le, E.hβS1⟩
  U_T := symU_T E.ℓ E.c E.n E.v
  U_S := symU_S E.q E.u₀ E.k E.r E.w
  σ := symσ E.q E.u₀ E.k E.r
  σ_mem := symσ_mem _ _ _ _
  σ_isMaxOn_U_S := symσ_isMaxOn E.hq _ _ _ _
  U_T_continuous := symU_T_continuous _ _ _ _
  U_S_continuous := symU_S_continuous _ _ _ _ _
  F := E.F
  F_continuous := E.F_continuous
  F_mono_x := E.F_mono_x
  F_mono_s := E.F_mono_s
  F_diag := E.F_diag

/-- **`E.toParams` has a continuous static Sender selector.** General in `F`: derived from
the closed form of the family's selector (`symσ_continuous`), whatever the transition
`E.F`. The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance toParams_staticSelectorContinuous :
    E.toParams.StaticSelectorContinuous where
  σ_continuous := symσ_continuous _ _ _ _

@[simp] theorem toParams_U_S : E.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
@[simp] theorem toParams_U_T : E.toParams.U_T = symU_T E.ℓ E.c E.n E.v := rfl
@[simp] theorem toParams_σ : E.toParams.σ = symσ E.q E.u₀ E.k E.r := rfl
@[simp] theorem toParams_β_S : E.toParams.β_S = E.βS := rfl
@[simp] theorem toParams_β_T : E.toParams.β_T = E.βT := rfl
@[simp] theorem toParams_F : E.toParams.F = E.F := rfl

theorem F_maps : ∀ y ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, E.F y s ∈ Icc (0 : ℝ) 1 :=
  fun y hy s hs => E.F_mem y s hy hs

/-- The one-variable sanction semiconcavity, read off the joint chord at zero
state displacement. -/
theorem F_sanctionSemiconcave : SanctionSemiconcave E.F E.Ms := by
  intro x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  have h := E.hFjsc x hx x hx s₁ hs₁ s₂ hs₂ t ht0 ht1
  simp only [sub_self, abs_zero, mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, zero_add, zero_sub, neg_mul, neg_neg] at h
  show t * E.F x s₁ + (1 - t) * E.F x s₂ - E.F x (t * s₁ + (1 - t) * s₂)
      ≤ E.Ms / 2 * (t * (1 - t) * (s₁ - s₂) ^ 2)
  have hmid : t * x + (1 - t) * x = x := by ring
  rw [hmid] at h
  linarith [h]

/-! ## 4. The Sender carrier -/

/-- Value-function type. -/
abbrev Val : Type := ↥(Sanctions.S : Set ℝ) →ᵇ ℝ

/-- **The Sender carrier**: bounded, `KS`-Lipschitz, `gS`-lower-slope on all of
`[0,1]`, and `SigV`-semiconcave through the clip. -/
def carrierS : Set Val :=
  {V : Val | V ∈ AbstractGame.Params.valLipGainBall E.MS E.KS E.gS 0 ∧
    SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) E.SigV}

theorem carrierS_isClosed : IsClosed E.carrierS := by
  unfold carrierS
  exact IsClosed.inter (AbstractGame.Params.valLipGainBall_isClosed _ _ _ _)
    (SymbolicEconomyF.semiconcaveClause_isClosed E.SigV)

/-- **The two-sided Sender carrier** (Rung 3): the carrier, plus
`σ_C`-semiconvexity through the clip. -/
def carrierS2 : Set Val :=
  {V : Val | V ∈ E.carrierS ∧
    SemiconvexOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) E.SigC}

/-- The semiconvex clause is closed: an intersection of closed half-spaces in
the sup norm (mirror of `semiconcaveClause_isClosed`). -/
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

theorem carrierS2_isClosed : IsClosed E.carrierS2 :=
  IsClosed.inter E.carrierS_isClosed (semiconvexClause_isClosed E.SigC)

theorem carrierS2_subset : E.carrierS2 ⊆ E.carrierS := fun _ hV => hV.1

/-! ### Carrier-membership consequences, extracted once -/

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

/-- Every carrier member is strictly increasing through the clip on `[0,1]`
(the wedge Rung 1's strict Sender theorem needs). -/
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

/-! ### Non-vacuity of the carrier -/

theorem gS_le_KS : E.gS ≤ E.KS := by
  unfold gS KS plGS plKS
  have h1 := E.one_sub_βS_glo_pos
  have h2 := E.one_sub_βS_ghi_pos
  rw [div_le_div_iff₀ h1 h2]
  have := mul_nonneg E.hβS0.le (sub_nonneg.mpr E.hglo_ghi)
  nlinarith [E.hr, E.hw, mul_nonneg E.hr (by linarith : (0:ℝ) ≤ 1 - E.βS * E.glo)]

theorem gS_le_MS : E.gS ≤ E.MS := by
  unfold gS MS plGS plMS
  have h1 := E.one_sub_βS_glo_pos
  have h2 : 0 < 1 - E.βS := by linarith [E.hβS1]
  rw [div_le_div_iff₀ h1 h2]
  have hglo1 : E.glo ≤ 1 := E.hglo_ghi.trans E.hghi1
  have hA : 0 ≤ (E.q / 2 + E.u₀ + E.k + E.r) * (1 - E.βS * E.glo) :=
    mul_nonneg (by linarith [E.hq, E.hu₀, E.k_pos, E.hr]) h1.le
  have hB : 0 ≤ E.w * E.βS * (1 - E.glo) :=
    mul_nonneg (mul_nonneg E.hw.le E.hβS0.le) (sub_nonneg.mpr hglo1)
  nlinarith [hA, hB]

theorem carrierS_nonempty : E.carrierS.Nonempty :=
  ⟨affineBCF E.gS,
    SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le E.gS_le_KS E.gS_le_MS,
    SymbolicEconomyF.affineBCF_clip_semiconcave E.hSigV0⟩

/-- The affine member is semiconvex through the clip with any nonnegative
modulus: it is affine on `[0,1]`, so its chord defect is zero. -/
theorem affineBCF_clip_semiconvex {c σ : ℝ} (hσ : 0 ≤ σ) :
    SemiconvexOnSet (fun z => affineBCF c (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) σ := by
  intro z₁ hz₁ z₂ hz₂ t ht0 ht1
  have hm := mem_Icc_convexComb hz₁ hz₂ ht0 ht1
  have hP : (0 : ℝ) ≤ t * (1 - t) * (z₁ - z₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  show affineBCF c (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))
      - (t * affineBCF c (Sanctions.clipS' z₁) + (1 - t) * affineBCF c (Sanctions.clipS' z₂))
    ≤ σ / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2)
  rw [affineBCF_apply, affineBCF_apply, affineBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hz₁, Sanctions.clipS'_val_eq_of_mem hz₂,
    Sanctions.clipS'_val_eq_of_mem hm]
  nlinarith [mul_nonneg hσ hP]

theorem carrierS2_nonempty : E.carrierS2.Nonempty :=
  ⟨affineBCF E.gS,
    ⟨SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le E.gS_le_KS E.gS_le_MS,
      SymbolicEconomyF.affineBCF_clip_semiconcave E.hSigV0⟩,
    affineBCF_clip_semiconvex E.SigC_nonneg⟩

/-! ## 5. The continuation's sanction curvature and argmax uniqueness -/

/-- **The continuation is semiconcave in the sanction** with modulus
`SigV·dhi² + K_S·Ms`, the one-dimensional composition rule. -/
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
curvature `q` beats `β_S` times the continuation's, by `hCurv`. -/
theorem senderObj_strictConcaveOn {V : Val} (hV : V ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (a : ℝ) :
    StrictConcaveOn ℝ Sanctions.I
      (fun s => E.toParams.U_S x a s
        + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F x s))) := by
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
  have hsc : p₁ * V (Sanctions.clipS' (E.F x s₁))
        + (1 - p₁) * V (Sanctions.clipS' (E.F x s₂))
        - V (Sanctions.clipS' (E.F x (p₁ * s₁ + (1 - p₁) * s₂)))
      ≤ (E.SigV * E.dhi ^ 2 + E.KS * E.Ms) / 2
          * (p₁ * (1 - p₁) * (s₁ - s₂) ^ 2) :=
    hcomp s₁ hs₁ s₂ hs₂ p₁ hp₁.le (by linarith)
  have hD : E.βS * (p₁ * V (Sanctions.clipS' (E.F x s₁))
        + (1 - p₁) * V (Sanctions.clipS' (E.F x s₂))
        - V (Sanctions.clipS' (E.F x (p₁ * s₁ + (1 - p₁) * s₂))))
      ≤ E.βS * ((E.SigV * E.dhi ^ 2 + E.KS * E.Ms) / 2
          * (p₁ * (1 - p₁) * (s₁ - s₂) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsc E.hβS0.le
  have hgap : 0 < E.q - E.βS * (E.SigV * E.dhi ^ 2 + E.KS * E.Ms) := by
    have := E.hCurv; unfold KS; linarith
  have hkey : 0 < (E.q - E.βS * (E.SigV * E.dhi ^ 2 + E.KS * E.Ms)) / 2
      * (p₁ * (1 - p₁) * (s₁ - s₂) ^ 2) := by positivity
  simp only [smul_eq_mul, toParams_U_S, symU_S, toParams_β_S, toParams_F]
  nlinarith [hD, hkey]

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
        = E.toParams.U_S y.val 0 sStar
          + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F y.val sStar))
      ∧ ∀ s ∈ Sanctions.I,
          E.toParams.U_S y.val 0 s
            + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F y.val s))
          ≤ E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V y := by
  have hmax := E.toParams.σ_dyn_isMaxOn V y.val 0
  have hmem := E.toParams.σ_dyn_mem V y.val 0
  have heq := WitnessKit.bellmanS_image_of_isMaxOn (p := E.toParams)
    (α := fun _ => 0) continuous_const V y hmem hmax
  refine ⟨_, hmem, heq, ?_⟩
  intro s hs
  rw [heq]
  exact hmax hs

/-- The stage payoff's cube bound at the defiance policy. -/
theorem symU_S_abs_le (x a s : ℝ) (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I)
    (hs : s ∈ Sanctions.I) :
    |symU_S E.q E.u₀ E.k E.r E.w x a s| ≤ E.q / 2 + E.u₀ + E.k + E.r + E.w := by
  unfold symU_S
  rw [abs_le]
  have hq := E.hq; have hu := E.hu₀; have hk := E.k_pos; have hr := E.hr; have hw := E.hw
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have hsa : s * a ≤ 1 := by nlinarith [hs.1, hs.2, ha.1, ha.2]
  have hsa0 : 0 ≤ s * a := mul_nonneg hs.1 ha.1
  have hsx : s * x ≤ 1 := by nlinarith [hs.1, hs.2, hx.1, hx.2]
  have hsx0 : 0 ≤ s * x := mul_nonneg hs.1 hx.1
  have hq2 : E.q / 2 * s ^ 2 ≤ E.q / 2 := by nlinarith [hq, hs2]
  have hq0 : 0 ≤ E.q / 2 * s ^ 2 := by positivity
  have hks : E.k * (s * a) ≤ E.k := by nlinarith [hk, hsa]
  have hks0 : 0 ≤ E.k * (s * a) := mul_nonneg hk.le hsa0
  have hrs : E.r * (s * x) ≤ E.r := by nlinarith [hr, hsx]
  have hrs0 : 0 ≤ E.r * (s * x) := mul_nonneg hr hsx0
  have hus : E.u₀ * s ≤ E.u₀ := by nlinarith [hu, hs.2]
  have hus0 : 0 ≤ E.u₀ * s := mul_nonneg hu.le hs.1
  have hwx : E.w * x ≤ E.w := by nlinarith [hw, hx.2]
  have hwx0 : 0 ≤ E.w * x := mul_nonneg hw.le hx.1
  have hexp : -(E.q / 2) * s ^ 2 + s * (E.u₀ - E.k * a + E.r * x) + E.w * x
      = -(E.q / 2 * s ^ 2) + E.u₀ * s - E.k * (s * a) + E.r * (s * x) + E.w * x := by ring
  rw [hexp]
  constructor <;> linarith [hq2, hq0, hks, hks0, hrs, hrs0, hus, hus0, hwx, hwx0]

/-- **Norm leg.** -/
theorem bellmanS_norm_le {V : Val} (hV : V ∈ E.carrierS) :
    ‖E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V‖ ≤ E.MS := by
  have h := E.toParams.bellmanS_BCF_norm_le (α := fun _ => 0) continuous_const
    (fun _ => ⟨le_refl 0, zero_le_one⟩) V
    (cube_S := E.q / 2 + E.u₀ + E.k + E.r + E.w) (R_S := E.MS) hV.1.1
    (fun x hx a ha s hs => by
      rw [toParams_U_S]; exact E.symU_S_abs_le x a s hx ha hs)
  refine h.trans (le_of_eq ?_)
  rw [toParams_β_S]
  unfold MS plMS
  have h2 : (1 - E.βS) ≠ 0 := by linarith [E.hβS1]
  field_simp
  ring

/-- **Lower-slope leg**, from the general-`F` cone theorem: at every sanction,
a rise in the state raises the stage payoff by at least `w` per unit and the
successor by at least `glo` per unit. -/
theorem bellmanS_lowerSlope {V : Val} (hV : V ∈ E.carrierS) :
    AbstractGame.Params.LowerSlopeOnValueOn
      (E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V) (Icc (0 : ℝ) 1) E.gS := by
  apply E.toParams.bellmanS_BCF_preserves_lowerSlopeCone_generalF
  · intro s hs y₁ hy₁ y₂ hy₂ hle
    have hband := (E.hbandAll s hs) y₁ hy₁ y₂ hy₂ hle
    have hFlo : E.glo * (y₂ - y₁) ≤ E.F y₂ s - E.F y₁ s := hband.1
    have hU : E.toParams.U_S y₂ 0 s - E.toParams.U_S y₁ 0 s = (E.r * s + E.w) * (y₂ - y₁) := by
      rw [toParams_U_S]; unfold symU_S; ring
    rw [hU, toParams_β_S, toParams_F]
    have hrs : 0 ≤ E.r * s := mul_nonneg E.hr hs.1
    have hdy : 0 ≤ y₂ - y₁ := by linarith
    have hgS : E.gS * (1 - E.βS * E.glo) = E.w := by
      unfold gS plGS; field_simp [E.one_sub_βS_glo_pos.ne']
    have h1 : 0 ≤ E.βS * E.gS := mul_nonneg E.hβS0.le E.gS_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hFlo h1, mul_nonneg hrs hdy]
  · exact hV.1.2.2

/-- **Lipschitz leg**, by cross-evaluating attained argmaxes. -/
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
    have hstage : E.toParams.U_S v.val 0 sv - E.toParams.U_S u.val 0 sv
        ≤ (E.r + E.w) * |v.val - u.val| := by
      rw [toParams_U_S]; unfold symU_S
      have h1 : (E.r * sv + E.w) * (v.val - u.val) ≤ (E.r + E.w) * |v.val - u.val| := by
        have hrs : 0 ≤ E.r * sv := mul_nonneg E.hr hsvI.1
        have hrs1 : E.r * sv ≤ E.r := by nlinarith [E.hr, hsvI.2]
        have hab := le_abs_self (v.val - u.val)
        have hab0 := abs_nonneg (v.val - u.val)
        nlinarith [mul_le_mul_of_nonneg_left hab (by linarith [E.hw] : (0:ℝ) ≤ E.r * sv + E.w),
          mul_le_mul_of_nonneg_right hrs1 hab0]
      linarith [h1]
    have hdist : dist u v = |v.val - u.val| := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [heqv, hdist]
    have hKS : E.KS * (1 - E.βS * E.ghi) = E.r + E.w := by
      unfold KS plKS; field_simp [E.one_sub_βS_ghi_pos.ne']
    rw [toParams_β_S, toParams_F] at hle ⊢
    nlinarith [hle, hcont, hstage, mul_le_mul_of_nonneg_left hcont E.hβS0.le,
      abs_nonneg (v.val - u.val), E.KS_pos]
  intro y₁ y₂
  rw [abs_sub_le_iff]
  constructor
  · exact key y₁ y₂
  · have h := key y₂ y₁
    rwa [dist_comm] at h

/-! ## 7. The semiconcave leg: the image is a supremum, so the joint chord rules -/

/-- **The stage payoff is jointly semiconcave** at the defiance policy with
moduli `(0, r, q)`: no state curvature, cross modulus the rally slope, action
concavity the cost curvature. This is the quadratic model of
`Foundations/SemiconcaveSup`. -/
theorem stage_jointSemiconcave :
    JointSemiconcaveOn (fun x s => symU_S E.q E.u₀ E.k E.r E.w x 0 s)
      (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) 0 E.r E.q := by
  intro x₁ _ x₂ _ s₁ _ s₂ _ t ht0 ht1
  have htt : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have hD : t * symU_S E.q E.u₀ E.k E.r E.w x₁ 0 s₁
        + (1 - t) * symU_S E.q E.u₀ E.k E.r E.w x₂ 0 s₂
        - symU_S E.q E.u₀ E.k E.r E.w (t * x₁ + (1 - t) * x₂) 0 (t * s₁ + (1 - t) * s₂)
      = t * (1 - t) * (-(E.q / 2) * (s₁ - s₂) ^ 2 + E.r * ((x₁ - x₂) * (s₁ - s₂))) := by
    unfold symU_S; ring
  have habs : (x₁ - x₂) * (s₁ - s₂) ≤ |x₁ - x₂| * |s₁ - s₂| := by
    rw [← abs_mul]; exact le_abs_self _
  have hslack : 0 ≤ t * (1 - t) * E.r * (|x₁ - x₂| * |s₁ - s₂| - (x₁ - x₂) * (s₁ - s₂)) :=
    mul_nonneg (mul_nonneg htt E.hr) (sub_nonneg.mpr habs)
  show t * symU_S E.q E.u₀ E.k E.r E.w x₁ 0 s₁
        + (1 - t) * symU_S E.q E.u₀ E.k E.r E.w x₂ 0 s₂
        - symU_S E.q E.u₀ E.k E.r E.w (t * x₁ + (1 - t) * x₂) 0 (t * s₁ + (1 - t) * s₂)
      ≤ t * (1 - t) / 2
          * (0 * (x₁ - x₂) ^ 2 + 2 * E.r * |x₁ - x₂| * |s₁ - s₂| - E.q * (s₁ - s₂) ^ 2)
  rw [hD]
  nlinarith [hslack]

/-- **The Sender's dynamic objective is jointly semiconcave** in `(x, s)` on a
carrier value, with the family's moduli `(plSig, plRho, plMu)`. -/
theorem senderObj_jointSemiconcave {V : Val} (hV : V ∈ E.carrierS) :
    JointSemiconcaveOn
      (fun x s => symU_S E.q E.u₀ E.k E.r E.w x 0 s
        + E.βS * V (Sanctions.clipS' (E.F x s)))
      (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
      (plSig E.βS E.SigV E.ghi E.KS E.Mx)
      (plRho E.βS E.r E.SigV E.ghi E.dhi E.KS E.Mm)
      (plMu E.βS E.q E.SigV E.dhi E.KS E.Ms) := by
  have hcont := jointSemiconcave_comp_of_chords
    (v := fun z => V (Sanctions.clipS' z)) (F := E.F)
    (σV := E.SigV) (K := E.KS) (glo := E.glo) (ghi := E.ghi) (dlo := E.dlo) (dhi := E.dhi)
    (Mx := E.Mx) (Mm := E.Mm) (Ms := E.Ms)
    E.hSigV0 E.KS_pos.le E.hglo0 E.hdlo0.le E.hMx0 E.hMm0 E.hMs0
    (E.clip_monotoneOn hV.1) (E.clip_lip hV.1) hV.2 E.F_maps
    E.hbandAll E.hSlo E.hShi E.hFjsc
  have hsum := JointSemiconcaveOn.add E.stage_jointSemiconcave
    (hcont.const_mul E.hβS0.le)
  refine hsum.congr_moduli ?_ ?_ ?_
  · unfold plSig; ring
  · unfold plRho; ring
  · unfold plMu; ring

/-- The Bellman image evaluated through the clip is the greatest value of the
objective over the sanction interval. -/
theorem bellmanS_isGreatest (V : Val) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IsGreatest
      ((fun s => symU_S E.q E.u₀ E.k E.r E.w x 0 s
        + E.βS * V (Sanctions.clipS' (E.F x s))) '' Icc (0 : ℝ) 1)
      (E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' x)) := by
  obtain ⟨sStar, hsI, heq, hdom⟩ := E.bellmanS_spec V (Sanctions.clipS' x)
  have hval : (Sanctions.clipS' x).val = x := Sanctions.clipS'_val_eq_of_mem hx
  refine ⟨⟨sStar, hsI, ?_⟩, ?_⟩
  · rw [heq, hval]; rfl
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
    (Φ := fun x s => symU_S E.q E.u₀ E.k E.r E.w x 0 s
      + E.βS * V (Sanctions.clipS' (E.F x s)))
    (v := fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
    E.mu_pos (E.senderObj_jointSemiconcave hV) (fun x hx => E.bellmanS_isGreatest V hx)
  refine hsup.mono_modulus ?_
  have h := E.hSigV
  unfold plSigImg at h
  unfold KS
  exact h

/-! ## 8. Carrier invariance -/

/-- **The Sender carrier is Bellman-invariant at the defiance policy.** Four
legs: norm, Lipschitz, lower slope, semiconcavity. -/
theorem bellmanS_mem {V : Val} (hV : V ∈ E.carrierS) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V ∈ E.carrierS :=
  ⟨⟨E.bellmanS_norm_le hV, E.bellmanS_lipschitz hV, E.bellmanS_lowerSlope hV⟩,
    E.bellmanS_semiconcave hV⟩

/-! ## 9. The two-sided carrier is invariant (Rung 3) -/

/-- The stage payoff is affine in the state at each sanction, hence
`0`-semiconvex. -/
theorem stage_semiconvex_x (s : ℝ) :
    SemiconvexOnSet (fun x => symU_S E.q E.u₀ E.k E.r E.w x 0 s) (Icc (0 : ℝ) 1) 0 := by
  intro y₁ _ y₂ _ t _ _
  simp only
  have h : symU_S E.q E.u₀ E.k E.r E.w (t * y₁ + (1 - t) * y₂) 0 s
      - (t * symU_S E.q E.u₀ E.k E.r E.w y₁ 0 s
        + (1 - t) * symU_S E.q E.u₀ E.k E.r E.w y₂ 0 s) = 0 := by
    unfold symU_S; ring
  rw [h]; simp

/-- **Semiconvex leg.** On the two-sided carrier the Bellman image is
`σ_C`-semiconvex through the clip: each state section of the objective is
`βS·(σ_C·ghi² + KS·Mcx)`-semiconvex by composition, the supremum keeps that
modulus with no Schur term, and the linear closure bounds it by `σ_C`. -/
theorem bellmanS_semiconvex {V : Val} (hV : V ∈ E.carrierS2) :
    SemiconvexOnSet
      (fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
      (Icc (0 : ℝ) 1) E.SigC := by
  have hsec : ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet
        (fun x => symU_S E.q E.u₀ E.k E.r E.w x 0 s + E.βS * V (Sanctions.clipS' (E.F x s)))
        (Icc (0 : ℝ) 1) (0 + E.βS * (E.SigC * E.ghi ^ 2 + E.KS * E.Mcx)) := by
    intro s hs
    have hcomp := semiconvexOnSet_comp_of_stateChord
      (v := fun z => V (Sanctions.clipS' z)) (G := fun y => E.F y s)
      E.SigC_nonneg E.KS_nonneg E.hglo0 E.hMcx0
      (E.clip_monotoneOn hV.1.1) (E.clip_lip hV.1.1) hV.2
      (fun y hy => E.F_maps y hy s hs) (E.hbandAll s hs) (E.hFcx s hs)
    exact (E.stage_semiconvex_x s).add (hcomp.const_mul E.hβS0.le)
  have hsup := sup_semiconvexOnSet
    (Φ := fun x s => symU_S E.q E.u₀ E.k E.r E.w x 0 s + E.βS * V (Sanctions.clipS' (E.F x s)))
    (v := fun z => E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V (Sanctions.clipS' z))
    hsec (fun x hx => E.bellmanS_isGreatest V hx)
  refine hsup.mono ?_
  linarith [E.SigC_closure]

/-- **The two-sided carrier is Bellman-invariant** at the defiance policy. -/
theorem bellmanS_mem2 {V : Val} (hV : V ∈ E.carrierS2) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V ∈ E.carrierS2 :=
  ⟨E.bellmanS_mem hV.1, E.bellmanS_semiconvex hV⟩

end PlacableEconomyF

/-! ## 10. The quadratic–linear family is a chord economy (round AU, 2026-09-25)

Every rate condition of `ChordEconomy` (`ChordEconomy.lean`, doc 104 §2) holds for
the family's payoffs at these rates, tight except the state slope, the marginal
return to the first unit of sanction and the pain:
`w_lo = w`, `w_hi = r + w`, `q = Q̄ = q`, `σ_x = τ_x = 0`, `r_lo = r_hi = r`,
`k_lo = k_hi = k`, `u_hi = u₀ + r`, `u_lo = u₀`, `ℓ_lo = ℓ_hi = ℓ`, pain rates
`c` and `c − n`, and state rates `v + n·s` from both sides. Each discharge is an
identity on `symU_S` or `symU_T` followed by the family's own signs, stated once
for the whole family; no member needs arithmetic of its own. -/

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

theorem symU_S_stateLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
    |symU_S E.q E.u₀ E.k E.r E.w x₂ 0 s - symU_S E.q E.u₀ E.k E.r E.w x₁ 0 s|
      ≤ (E.r + E.w) * |x₂ - x₁| := by
  intro s hs x₁ _ x₂ _
  have hid : symU_S E.q E.u₀ E.k E.r E.w x₂ 0 s - symU_S E.q E.u₀ E.k E.r E.w x₁ 0 s
      = (E.r * s + E.w) * (x₂ - x₁) := by unfold symU_S; ring
  rw [hid, abs_mul]
  have h0 : 0 ≤ E.r * s + E.w := by nlinarith [E.hr, hs.1, E.hw]
  rw [abs_of_nonneg h0]
  have h1 : E.r * s + E.w ≤ E.r + E.w := by nlinarith [E.hr, hs.2]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem symU_S_stateSlope : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, x₁ ≤ x₂ →
      E.w * (x₂ - x₁)
        ≤ symU_S E.q E.u₀ E.k E.r E.w x₂ a s - symU_S E.q E.u₀ E.k E.r E.w x₁ a s := by
  intro a _ s hs x₁ _ x₂ _ hle
  have hid : symU_S E.q E.u₀ E.k E.r E.w x₂ a s - symU_S E.q E.u₀ E.k E.r E.w x₁ a s
      = (E.r * s + E.w) * (x₂ - x₁) := by unfold symU_S; ring
  rw [hid]
  have := mul_nonneg (mul_nonneg E.hr hs.1) (sub_nonneg.2 hle)
  nlinarith

theorem symU_S_concave : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a : ℝ,
    SemiconcaveOnSet (fun s => symU_S E.q E.u₀ E.k E.r E.w x a s) (Icc (0 : ℝ) 1) (-E.q) := by
  intro x _ a s₁ _ s₂ _ t _ _
  apply le_of_eq
  simp only [symU_S]; ring

theorem symU_S_convex : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    SemiconvexOnSet (fun s => symU_S E.q E.u₀ E.k E.r E.w x a s) (Icc (0 : ℝ) 1) E.q := by
  intro x _ a _ s₁ _ s₂ _ t _ _
  apply le_of_eq
  simp only [symU_S]; ring

theorem symU_S_crossLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ s' ∈ Icc (0 : ℝ) 1, x ≤ x' → s ≤ s' →
      E.r * ((x' - x) * (s' - s)) ≤
        (symU_S E.q E.u₀ E.k E.r E.w x' 0 s' - symU_S E.q E.u₀ E.k E.r E.w x' 0 s)
          - (symU_S E.q E.u₀ E.k E.r E.w x 0 s' - symU_S E.q E.u₀ E.k E.r E.w x 0 s) := by
  intro x _ x' _ s _ s' _ _ _
  apply le_of_eq
  unfold symU_S; ring

theorem symU_S_crossHi : ∀ a ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |(symU_S E.q E.u₀ E.k E.r E.w x' a s' - symU_S E.q E.u₀ E.k E.r E.w x' a s)
          - (symU_S E.q E.u₀ E.k E.r E.w x a s' - symU_S E.q E.u₀ E.k E.r E.w x a s)|
        ≤ E.r * (|x' - x| * |s' - s|) := by
  intro a _ x _ x' _ s _ s' _
  have hid : (symU_S E.q E.u₀ E.k E.r E.w x' a s' - symU_S E.q E.u₀ E.k E.r E.w x' a s)
      - (symU_S E.q E.u₀ E.k E.r E.w x a s' - symU_S E.q E.u₀ E.k E.r E.w x a s)
      = E.r * ((x' - x) * (s' - s)) := by unfold symU_S; ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg E.hr]

theorem symU_S_placLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' → s ≤ s' →
      (symU_S E.q E.u₀ E.k E.r E.w x a' s' - symU_S E.q E.u₀ E.k E.r E.w x a' s)
          - (symU_S E.q E.u₀ E.k E.r E.w x a s' - symU_S E.q E.u₀ E.k E.r E.w x a s)
        ≤ -(E.k * ((a' - a) * (s' - s))) := by
  intro x _ a _ a' _ s _ s' _ _ _
  apply le_of_eq
  unfold symU_S; ring

theorem symU_S_placHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' →
      |(symU_S E.q E.u₀ E.k E.r E.w x a' s' - symU_S E.q E.u₀ E.k E.r E.w x a' s)
          - (symU_S E.q E.u₀ E.k E.r E.w x a s' - symU_S E.q E.u₀ E.k E.r E.w x a s)|
        ≤ E.k * ((a' - a) * |s' - s|) := by
  intro x _ a _ a' _ s _ s' _ ha
  have hid : (symU_S E.q E.u₀ E.k E.r E.w x a' s' - symU_S E.q E.u₀ E.k E.r E.w x a' s)
      - (symU_S E.q E.u₀ E.k E.r E.w x a s' - symU_S E.q E.u₀ E.k E.r E.w x a s)
      = -(E.k * ((a' - a) * (s' - s))) := by unfold symU_S; ring
  rw [hid, abs_neg, abs_mul, abs_mul, abs_of_pos E.k_pos, abs_of_nonneg (sub_nonneg.2 ha)]

theorem symU_S_appetite : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    t ≤ s →
      (s - t) * (E.q * (s + t) / 2 - (E.u₀ + E.r))
        ≤ symU_S E.q E.u₀ E.k E.r E.w x 0 t - symU_S E.q E.u₀ E.k E.r E.w x 0 s := by
  intro x hx t _ s _ hts
  have hid : symU_S E.q E.u₀ E.k E.r E.w x 0 t - symU_S E.q E.u₀ E.k E.r E.w x 0 s
      = (s - t) * (E.q * (s + t) / 2 - (E.u₀ + E.r * x)) := by unfold symU_S; ring
  rw [hid]
  have hrx : E.r * x ≤ E.r := by nlinarith [E.hr, hx.2]
  exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 hts)

theorem symU_S_floor : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    t ≤ s →
      (s - t) * (E.u₀ - E.q * (s + t) / 2)
        ≤ symU_S E.q E.u₀ E.k E.r E.w x 0 s - symU_S E.q E.u₀ E.k E.r E.w x 0 t := by
  intro x hx t _ s _ hts
  have hid : symU_S E.q E.u₀ E.k E.r E.w x 0 s - symU_S E.q E.u₀ E.k E.r E.w x 0 t
      = (s - t) * (E.u₀ + E.r * x - E.q * (s + t) / 2) := by unfold symU_S; ring
  rw [hid]
  have hrx : 0 ≤ E.r * x := mul_nonneg E.hr hx.1
  exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 hts)

theorem symU_T_costLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1,
    ∀ a₂ ∈ Icc (0 : ℝ) 1, a₁ ≤ a₂ →
      symU_T E.ℓ E.c E.n E.v x a₂ s - symU_T E.ℓ E.c E.n E.v x a₁ s ≤ -(E.ℓ * (a₂ - a₁)) := by
  intro x _ s _ a₁ _ a₂ _ _
  apply le_of_eq; unfold symU_T; ring

theorem symU_T_costHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1,
    ∀ a₂ ∈ Icc (0 : ℝ) 1, a₁ ≤ a₂ →
      -(E.ℓ * (a₂ - a₁)) ≤ symU_T E.ℓ E.c E.n E.v x a₂ s - symU_T E.ℓ E.c E.n E.v x a₁ s := by
  intro x _ s _ a₁ _ a₂ _ _
  apply le_of_eq; unfold symU_T; ring

theorem symU_T_painHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1,
    ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      symU_T E.ℓ E.c E.n E.v x a s₁ - symU_T E.ℓ E.c E.n E.v x a s₂ ≤ E.c * (s₂ - s₁) := by
  intro x hx a _ s₁ _ s₂ _ hs
  have hid : symU_T E.ℓ E.c E.n E.v x a s₁ - symU_T E.ℓ E.c E.n E.v x a s₂
      = (s₂ - s₁) * (E.c - E.n * x) := by unfold symU_T; ring
  rw [hid]
  have hnx : 0 ≤ E.n * x := mul_nonneg E.hn hx.1
  nlinarith [mul_nonneg (sub_nonneg.2 hs) hnx]

theorem symU_T_painLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1,
    ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      (E.c - E.n) * (s₂ - s₁) ≤ symU_T E.ℓ E.c E.n E.v x a s₁ - symU_T E.ℓ E.c E.n E.v x a s₂ := by
  intro x hx a _ s₁ _ s₂ _ hs
  have hid : symU_T E.ℓ E.c E.n E.v x a s₁ - symU_T E.ℓ E.c E.n E.v x a s₂
      = (s₂ - s₁) * (E.c - E.n * x) := by unfold symU_T; ring
  rw [hid]
  have hnx : E.n * x ≤ E.n := by nlinarith [E.hn, hx.2]
  nlinarith [mul_le_mul_of_nonneg_left hnx (sub_nonneg.2 hs)]

theorem symU_T_stateLo : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, x₁ ≤ x₂ →
      (E.v + E.n * s) * (x₂ - x₁)
        ≤ symU_T E.ℓ E.c E.n E.v x₂ a s - symU_T E.ℓ E.c E.n E.v x₁ a s := by
  intro a _ s _ x₁ _ x₂ _ _
  apply le_of_eq; unfold symU_T; ring

theorem symU_T_stateHi : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1,
      |symU_T E.ℓ E.c E.n E.v x₂ a s - symU_T E.ℓ E.c E.n E.v x₁ a s|
        ≤ (E.v + E.n * s) * |x₂ - x₁| := by
  intro a _ s hs x₁ _ x₂ _
  have hid : symU_T E.ℓ E.c E.n E.v x₂ a s - symU_T E.ℓ E.c E.n E.v x₁ a s
      = (E.v + E.n * s) * (x₂ - x₁) := by unfold symU_T; ring
  have h0 : (0 : ℝ) ≤ E.v + E.n * s := by nlinarith [E.hv, E.hn, hs.1]
  rw [hid, abs_mul, abs_of_nonneg h0]

/-- The quadratic family's closure is the chord closure at `σ_x = 0`. -/
theorem chSigImg_zero_eq (βS q r SigV ghi dhi KS Mx Mm Ms : ℝ) :
    chSigImg βS q r 0 SigV ghi dhi KS Mx Mm Ms = plSigImg βS q r SigV ghi dhi KS Mx Mm Ms := by
  unfold chSigImg chSig plSigImg plSig; ring

/-- **The quadratic–linear member as a chord economy**, with its relief rates
(round BC: a `ChordEconomyRelief`, since the family carries every relief-side
rate; the base-class results apply through the parent projection). Since renovation
round BJ (2026-10-07) it supplies the two-sided curvature data through
`ChordEconomyTwoSided` (BJ3.1) and its placation ceiling `k` as the relief field (BJ2.2);
`q > 0` is no longer supplied, since the chord economy derives it (BJ2.1). Its lower
sanction pain `p_lo = c − n > 0` reads the family's sign field `hcn` (BJ2.3). The
selector continuity that the chord class carries as its field `σ_continuous` (BJ5.1) is
derived from the family's closed-form selector (`symσ_continuous`). -/
def toChord : ChordEconomyRelief where
  toParams := E.toParams
  σ_continuous := symσ_continuous _ _ _ _
  glo := E.glo
  ghi := E.ghi
  dlo := E.dlo
  dhi := E.dhi
  Mx := E.Mx
  Mm := E.Mm
  Ms := E.Ms
  hbandAll := E.hbandAll
  hSlo := E.hSlo
  hShi := E.hShi
  hFjsc := E.hFjsc
  hglo0 := E.hglo0
  hghi1 := E.hghi1
  hdlo0 := E.hdlo0
  hMx0 := E.hMx0
  hMm0 := E.hMm0
  hMs0 := E.hMs0
  Mcx := E.Mcx
  hMcx0 := E.hMcx0
  hFcx := E.hFcx
  Mmix := E.Mmix
  hFmix := E.hFmix
  hβS0 := E.hβS0
  hβT0 := E.hβT0
  wlo := E.w
  whi := E.r + E.w
  q := E.q
  Qbar := E.q
  σx := 0
  τx := 0
  rlo := E.r
  rhi := E.r
  klo := E.k
  khi := E.k
  uhi := E.u₀ + E.r
  ulo := E.u₀
  hUS_stateLip := E.symU_S_stateLip
  hUS_stateSlope := E.symU_S_stateSlope
  hUS_concave := E.symU_S_concave
  hUS_convex := E.symU_S_convex
  hUS_joint := E.stage_jointSemiconcave
  hUS_stateConvex := fun s _ => E.stage_semiconvex_x s
  hUS_crossLo := E.symU_S_crossLo
  hUS_crossHi := E.symU_S_crossHi
  hUS_placLo := E.symU_S_placLo
  hUS_placHi := E.symU_S_placHi
  hUS_appetite := E.symU_S_appetite
  hUS_floor := E.symU_S_floor
  hwlo := E.hw
  hσx0 := le_refl 0
  hτx0 := le_refl 0
  hrlo := E.hr
  hklo := E.hk
  hulo := E.hu₀
  ℓlo := E.ℓ
  ℓhi := E.ℓ
  c := E.c
  plo := E.c - E.n
  vlo := E.v
  nlo := E.n
  vhi := E.v
  nhi := E.n
  hUT_costLo := E.symU_T_costLo
  hUT_costHi := E.symU_T_costHi
  hUT_painHi := E.symU_T_painHi
  hUT_painLo := E.symU_T_painLo
  hUT_stateLo := E.symU_T_stateLo
  hUT_stateHi := E.symU_T_stateHi
  hℓlo := E.hℓ
  hplo := E.c_sub_n_pos
  hvlo := E.hv
  hnlo := E.hn
  SigV := E.SigV
  hCurv := E.hCurv
  hSigV := by
    have h := E.hSigV
    rw [← chSigImg_zero_eq] at h
    exact h

/-- The family's interiority is the chord economy's interiority hypothesis
(`ChordEconomy.Interior`, a hypothesis since round BC); definitional. Since renovation
item BJ2.3 (2026-10-07) the family's interiority is the hypothesis `hInt` too, no longer
the field `hInterior`. General in `F`. -/
theorem toChord_interior_iff : E.toChord.Interior ↔ E.Interior := Iff.rfl

/-- The chord economy's interiority from the family's (renovation item BJ2.3: the
family's interiority is now the hypothesis `hInt`, no longer a field). General in
`F`. -/
theorem toChord_interior (hInt : E.Interior) : E.toChord.Interior := hInt

/-- The family's stage relief margin is the chord economy's
(`ChordEconomyRelief.StageRelief`, a hypothesis since round BC); definitional. Since
renovation item BJ2.3 the family's is the hypothesis `hSR` too, no longer the field
`hStageRelief`. General in `F`. -/
theorem toChord_stageRelief_iff : E.toChord.StageRelief ↔ E.StageRelief := Iff.rfl

/-- The chord economy's stage relief margin from the family's (renovation item BJ2.3:
the family's stage relief margin is now the hypothesis `hSR`, no longer a field).
General in `F`. -/
theorem toChord_stageRelief (hSR : E.StageRelief) : E.toChord.StageRelief := hSR

@[simp] theorem toChord_toParams : E.toChord.toParams = E.toParams := rfl

theorem toChord_KS : E.toChord.KS = E.KS := rfl
theorem toChord_gS : E.toChord.gS = E.gS := rfl
theorem toChord_mu : E.toChord.mu = E.mu := rfl

theorem toChord_SigC : E.toChord.SigC = E.SigC := by
  have h : E.toChord.SigC = (0 + E.βS * E.KS * E.Mcx) / (1 - E.βS * E.ghi ^ 2) := rfl
  rw [h, zero_add]
  rfl

/-- The chord economy's sanction floor `σ(0,0)` is the family's `u₀/q`, when the
floor is at most full sanction, `u₀ ≤ q`. Renovation item BJ2.3 (2026-10-07): that
condition is the hypothesis `hu`; until then the interiority field supplied it (and
`u₀_le_q` still derives it from `hInt`). Without it the clipped floor is `min 1 (u₀/q)`.
General in `F`. -/
theorem toChord_sfloor (hu : E.u₀ ≤ E.q) : E.toChord.sfloor = E.u₀ / E.q := by
  change symσ E.q E.u₀ E.k E.r 0 0 = E.u₀ / E.q
  unfold symσ
  simp only [mul_zero, sub_zero, add_zero]
  have h1 : E.u₀ / E.q ≤ 1 := by rw [div_le_one E.hq]; exact hu
  have h0 : 0 ≤ E.u₀ / E.q := div_nonneg E.hu₀.le E.hq.le
  rw [min_eq_right h1, max_eq_right h0]

/-- The chord economy's Target value slope is the family's, given `u₀ ≤ q` (the floor
condition, renovation item BJ2.3). General in `F`. -/
theorem toChord_gT (hu : E.u₀ ≤ E.q) : E.toChord.gT = E.gT := by
  have h : E.toChord.gT = (E.v + E.n * E.toChord.sfloor) / (1 - E.βT * E.glo) := rfl
  rw [h, toChord_sfloor E hu]
  unfold gT plGTn
  ring

/-- The two margins read the same on the family and on its chord economy, given the
floor condition `u₀ ≤ q` (the hypothesis `hu` since renovation item BJ2.3; until then
the interiority field supplied it). General in `F`. -/
theorem toChord_lossOffset_iff (hu : E.u₀ ≤ E.q) : E.toChord.LossOffset ↔ E.LossOffset := by
  unfold ChordEconomy.LossOffset LossOffset
  rw [toChord_gT E hu]
  rfl

theorem toChord_placable_iff : E.toChord.Placable ↔ E.Placable := Iff.rfl

/-- The chord economy's loss-offset margin from the family's, given the floor condition
`u₀ ≤ q` (renovation item BJ2.3: the hypothesis `hu`, which interiority implies,
`u₀_le_q`). General in `F`. -/
theorem toChord_lossOffset (hu : E.u₀ ≤ E.q) (h : E.LossOffset) : E.toChord.LossOffset :=
  (E.toChord_lossOffset_iff hu).2 h

/-- The chord economy's loss-offset margin from the family's when the Target has no
rally softening, `n = 0`, with no floor condition. The family's Target value slope
carries the rally term `n·u₀/q`, the chord economy's carries `n·σ(0,0)` at the clipped
floor; with `n = 0` both vanish and the two slopes are `v/(1 − β_T g_lo)`. Renovation
item BJ2.3 (2026-10-07): the planner results on the boundary `r = n = 0` reach the chord
economy through this, so they need neither interiority nor `u₀ ≤ q`. General in `F`. -/
theorem toChord_lossOffset_of_n_eq_zero (hn : E.n = 0) (h : E.LossOffset) :
    E.toChord.LossOffset := by
  have hg : E.toChord.gT = E.gT := by
    have h1 : E.toChord.gT = (E.v + E.n * E.toChord.sfloor) / (1 - E.βT * E.glo) := rfl
    rw [h1]
    unfold gT plGTn
    rw [hn]
    ring
  unfold ChordEconomy.LossOffset
  rw [hg]
  exact h

theorem toChord_placable (h : E.Placable) : E.toChord.Placable :=
  (E.toChord_placable_iff).2 h

/-- The family satisfies zero-sanction neutrality: compliance enters its Sender
payoff only through the placation term `−k·a·s`. -/
theorem toChord_zeroSanctionNeutral : E.toChord.ZeroSanctionNeutral := by
  intro x _ a _
  change symU_S E.q E.u₀ E.k E.r E.w x a 0 = symU_S E.q E.u₀ E.k E.r E.w x 0 0
  unfold symU_S; ring

/-! ### The stage vertex: the family's closed form of the stage selector at defiance

The abstract theory reads the stage selector `σ(x, 0)` through its rate bounds only.
On this family it has the closed form `(u₀ + r·x)/q`, which the family-only results
(the closed-form steady state, the cross-economy comparisons in `r`; sign-off M6)
consume through `toChord_σ_zero`. -/

/-- **The stage vertex** `(u₀ + r·x)/q`. -/
def vertex (x : ℝ) : ℝ := (E.u₀ + E.r * x) / E.q

/-- `u₀ + r < q`: the family's appetite `u_hi = u₀ + r` is below the curvature, under
interiority (the hypothesis `hInt` since renovation item BJ2.3). General in `F`. -/
theorem u₀_r_lt_q (hInt : E.Interior) : E.u₀ + E.r < E.q :=
  E.toChord.uhi_lt_q (E.toChord_interior hInt)

/-- `r < q` under interiority (renovation item BJ2.3: the hypothesis `hInt`, until then a
field). General in `F`. -/
theorem r_lt_q (hInt : E.Interior) : E.r < E.q := by linarith [E.u₀_r_lt_q hInt, E.hu₀]

theorem vertex_nonneg {x : ℝ} (hx : x ∈ Sanctions.I) : 0 ≤ E.vertex x := by
  unfold vertex
  exact div_nonneg (by nlinarith [E.hu₀, E.hr, hx.1]) E.hq.le

/-- The vertex is below full sanction, under interiority (the hypothesis `hInt` since
renovation item BJ2.3, until then a field). General in `F`. -/
theorem vertex_lt_one (hInt : E.Interior) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.vertex x < 1 := by
  unfold vertex
  rw [div_lt_one E.hq]
  have hrx : E.r * x ≤ E.r := by nlinarith [E.hr, hx.2]
  linarith [E.u₀_r_lt_q hInt]

/-- The vertex is a feasible sanction, under interiority (the hypothesis `hInt` since
renovation item BJ2.3, until then a field). General in `F`. -/
theorem vertex_mem (hInt : E.Interior) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.vertex x ∈ Sanctions.I :=
  ⟨E.vertex_nonneg hx, (E.vertex_lt_one hInt hx).le⟩

/-- The vertex is never below its value `u₀/q` at the lowest state. -/
theorem vertex_ge_floor {x : ℝ} (hx : x ∈ Sanctions.I) : E.u₀ / E.q ≤ E.vertex x := by
  unfold vertex
  apply div_le_div_of_nonneg_right _ E.hq.le
  nlinarith [E.hr, hx.1]

/-- **On the family the stage selector at defiance is the vertex**, under interiority
(the hypothesis `hInt` since renovation item BJ2.3; it keeps the vertex below full
sanction). General in `F`. -/
theorem toChord_σ_zero (hInt : E.Interior) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toChord.σ x 0 = E.vertex x := by
  change symσ E.q E.u₀ E.k E.r x 0 = E.vertex x
  have h1 : (E.u₀ + E.r * x) / E.q < 1 := by
    have := E.vertex_lt_one hInt hx; unfold vertex at this; exact this
  have h0 : 0 ≤ (E.u₀ + E.r * x) / E.q := by
    have := E.vertex_nonneg hx; unfold vertex at this; exact this
  unfold symσ vertex
  rw [mul_zero, sub_zero, min_eq_right h1.le, max_eq_right h0]

/-- The family's stage flip `ℓ·q < u₀·(c − n)` is the chord economy's
`ℓ_hi < b·p_lo`, with `b = u₀/q` and `p_lo = c − n`, given the floor condition
`u₀ ≤ q` (the hypothesis `hu` since renovation item BJ2.3). General in `F`. -/
theorem toChord_flip_iff (hu : E.u₀ ≤ E.q) :
    E.toChord.ℓhi < E.toChord.sfloor * E.toChord.plo ↔ E.ℓ * E.q < E.u₀ * (E.c - E.n) := by
  rw [toChord_sfloor E hu]
  change E.ℓ < E.u₀ / E.q * (E.c - E.n) ↔ _
  rw [div_mul_eq_mul_div, lt_div_iff₀ E.hq]

/-- The family's rally margin is the chord economy's (`r_lo = r`). -/
theorem toChord_margin
    (h : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r) :
    E.toChord.β_S * (E.toChord.SigC * E.toChord.ghi * E.toChord.dhi
      + (E.toChord.KS + 2 * E.toChord.SigC) * E.toChord.Mmix) ≤ E.toChord.rlo := by
  rw [E.toChord_SigC]; exact h

end PlacableEconomyF

namespace PlacableEconomyFcs

/-- **The enriched quadratic–linear member as an enriched chord economy.** -/
def toChordCs (E : PlacableEconomyFcs) : ChordEconomyCs :=
  { E.toPlacableEconomyF.toChord with
    Mcs := E.Mcs
    hMcs0 := E.hMcs0
    hFcs := E.hFcs }

@[simp] theorem toChordCs_toChord (E : PlacableEconomyFcs) :
    E.toChordCs.toChordEconomyRelief = E.toPlacableEconomyF.toChord := rfl

@[simp] theorem toChordCs_toChordEconomy (E : PlacableEconomyFcs) :
    E.toChordCs.toChordEconomy = E.toPlacableEconomyF.toChord.toChordEconomy := rfl

/-- The enriched member's interiority, from the family's (renovation item BJ2.3: the
hypothesis `hInt`, no longer a field). General in `F`. -/
theorem toChordCs_interior (E : PlacableEconomyFcs) (hInt : E.Interior) :
    E.toChordCs.Interior :=
  E.toPlacableEconomyF.toChord_interior hInt

/-- The enriched member's stage relief margin, from the family's (renovation item
BJ2.3: the hypothesis `hSR`, no longer a field). General in `F`. -/
theorem toChordCs_stageRelief (E : PlacableEconomyFcs) (hSR : E.StageRelief) :
    E.toChordCs.StageRelief :=
  E.toPlacableEconomyF.toChord_stageRelief hSR

end PlacableEconomyFcs

end

end Examples
end Sanctions
