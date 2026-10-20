/-
Sanctions/Theory/Certificates/StandardComplianceLocalDischargers.lean

**Dischargers and smart constructors for the carrier-local compliance
certificates** — split out of `StandardComplianceLocal.lean` in the
2026-07-07 restructure so the certificate *definitions* and the
three-goals *engines* (which stay in the core file) are separated from
the machinery that discharges or packages their fields.

Contents (all previously in the core file, statements unchanged):

* field dischargers — relevant-action-region Sender slope, local
  myopic ceiling, C¹ partial-derivative dischargers for the Target
  loss and Sender slope fields, carrier Lipschitz from `valLipBall`,
  the `hSC_on` dischargers (cross-partial saturated-α ×2, choice-axis
  strict-mono IDO, Sender combined monotonicity, strong-rally
  primitives), and the B2-route `hIDO_on` discharger from
  quasiconcavity + monotone transfer;
* smart constructors — `with_KS_closed_form`, `with_hSC_on_derived`,
  and the `with_strict_slope_wedge` family (base / canonical /
  `s̄`-default).

Zero new content: this is a Rule-13 readability split. The core file
(`StandardComplianceLocal.lean`) does not depend on anything here.

**Round BJ5.1 (2026-10-07).** The discharger
`StandardComplianceLocalCoreCertificate_MS.of_transition_adjusted_chord` builds
an MS certificate, whose type takes `[p.StaticSelectorContinuous]` (its myopic
ceiling names the canonical myopic equilibrium), so it takes the binder too.
That class is the static-selector continuity condition, the joint continuity of
the static Sender selector `σ`, which was the `Params` field `σ_continuous`.
General in `F`.
-/

import Sanctions.Theory.Certificates.StandardComplianceLocal

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Audit-49 follow-up: relevant-action-region discharger for `h_stage_sender_on`

The region-restricted formulation `RelevantActionRegionSenderSlope`
(in `Theory/Basin/RelevantActionRegion.lean`) is an economically
interpretable sufficient condition for the carrier-local field
`h_stage_sender_on`. It is useful when the Sender lower-slope
condition is plausible only for low-compliance / hardline Target
actions (`a ≤ abar(x)`); a downstream **cooperation hypothesis**
`hα_region` then certifies that the equilibrium selector lies in
that region on the basin.

This is **not** a pure logical weakening of `h_stage_sender_on`: the
direct `h_stage_sender_on` field is itself evaluated at the
*selected* carrier-local Target action `D.α_on V_T V_S x`, not
uniform-in-`a` over `Sanctions.I`. The discharger replaces that
direct selected-action condition with a region-level primitive
(`RelevantActionRegionSenderSlope`: lower slope for every action in
`[0, abar(x)]`) plus the additional cooperation hypothesis
`hα_region` (a *new economic content* — a behavioral fact about the
equilibrium selector, not derivable from the existing primitives and
must be supplied). It is a useful **alternative** sufficient
condition, not a uniformly weaker reformulation. -/

/-- **Audit-49 follow-up: carrier-local Sender slope from region-restricted
slope + cooperation hypothesis.** From a `RelevantActionRegionSenderSlope`
(slope only for `a ≤ abar(x)`) plus the cooperation hypothesis
(`D.α_on V_T V_S x ≤ abar x` on the basin), produce the carrier-local
`h_stage_sender_on` field that
`StandardComplianceLocalCertificate` requires. Use this when the
Sender slope is economically plausible only in a hardline-action
region. -/
theorem stage_sender_on_from_relevant_action_region
    (D : p.ValueClass2)
    {xS sbar mS : ℝ} {abar : ℝ → ℝ}
    (_hxS_mem : xS ∈ Sanctions.I)
    (h_region : p.RelevantActionRegionSenderSlope xS sbar mS abar)
    (hα_region :
      ∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS,
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          D.α_on V_T V_S x ≤ abar x) :
    ∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS,
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS := by
  intro V_T V_S x hx
  have hα_feas : D.α_on V_T V_S x ∈ Sanctions.I := by
    -- α_on takes values in Sanctions.I at all states x ∈ ℝ.
    exact D.α_on_mem V_T V_S x
  exact h_region x hx (D.α_on V_T V_S x) hα_feas (hα_region V_T V_S x hx)

/-! ## Audit-49 follow-up Fix-5: local myopic-ceiling discharger

The `StandardComplianceLocalCertificate` field `hMyoCeiling` is
direct ($\sigma(x,M.\alpha\,x)\le\max(x,\bar s)$ on the basin). For
paper-facing presentation it is more interpretable to decompose it
into:

* a **compliance threshold** `τ : ℝ → ℝ`;
* an **α-floor** on the myopic comparator (`τ x ≤ M.α x` on the
  basin — the myopic Target complies at least up to `τ`);
* `σ`-**antitone** in compliance (`σ` decreases in the Target
  action on `Sanctions.I`);
* a **σ-ceiling at τ** (`σ(x, τ(x)) ≤ max x sbar` on the basin).

The lemma below produces the `hMyoCeiling` field from these
four primitives. It is a one-line delegation to the homogeneous
discharger
`Sanctions.AbstractGame.Params.myopicCeiling_of_alpha_floor_and_sigma_antitoneOn`
(in `Theory/LockIn/DifferentPolicyComparator.lean`), exposed here
under the canonical paper-facing local-certificate naming. -/

/-- **Audit-49 follow-up Fix-5: local myopic-ceiling discharger.**
Produces the `hMyoCeiling` field of
`StandardComplianceLocalCertificate` from the compliance-threshold
decomposition. -/
theorem myopicCeiling_local_of_alpha_floor_and_sigma_antitoneOn
    (M : p.MyopicFeedbackEquilibrium)
    {xT xS sbar : ℝ}
    {τ : ℝ → ℝ}
    (hτ_mem :
      ∀ x ∈ Set.Icc (max xT xS) 1, τ x ∈ Sanctions.I)
    (hM_mem :
      ∀ x ∈ Set.Icc (max xT xS) 1, M.α x ∈ Sanctions.I)
    (hα_floor :
      ∀ x ∈ Set.Icc (max xT xS) 1, τ x ≤ M.α x)
    (hσ_antitone :
      ∀ x ∈ Set.Icc (max xT xS) 1,
        AntitoneOn (fun a => p.σ x a) Sanctions.I)
    (hσ_ceiling_at_τ :
      ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (τ x) ≤ max x sbar) :
    ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (M.α x) ≤ max x sbar :=
  p.myopicCeiling_of_alpha_floor_and_sigma_antitoneOn
    hτ_mem hM_mem hα_floor hσ_antitone hσ_ceiling_at_τ

/-! ## Round-11 Priority 1: certificate-facing C¹ discharger for `h_stage_target_loss_on`

The carrier-local stage Target loss condition `h_stage_target_loss_on`
(a field of `StandardComplianceLocalCoreCertificate` until round BJ1.4,
2026-10-07, which deleted the Target loss-offset stack from it; it is now an
input of `Target_combined_chord_of_decomposition_lowerChord`) is a synthetic
discrete-chord predicate quantified over the carrier-local Target selector. For paper-facing
presentation it is more interpretable to supply a single C¹
partial-derivative lower bound on the Target stage payoff:

> The Target's per-period sanction-marginal disutility is bounded:
> `∂U_T/∂s(x, a, s) ≥ −cT` for all `(x, a, s)`.

The wrapper below converts this paper-stateable C¹ primitive into
the carrier-local quantified `LowerLossSlopeOn` field required by
the certificate. One-line delegation to
`LowerLossSlopeOn.of_hasDerivAt_lowerBound` (in
`Theory/Certificates/TargetSanctionLossOffset.lean`).

## Rule compliance
* Rule 1 (optimal strategies): structural — no strategy fixings.
* Rule 3: pure discharger (no new certificate field; user replaces
  the synthetic discrete-chord Prop with a strictly weaker C¹
  primitive, a category-2 weakening).
* Rule 5: fully parametric over `(D, xT, sbar, cT, U_T_s)`.
* Rule 8: human-language paraphrase above.
* Rule 9: non-vacuity witness in
  `Sanctions/Examples/JointPositiveSanctions.lean`. -/

/-- **Round-11 Priority 1: certificate-facing C¹ discharger for
`h_stage_target_loss_on`.**

From a user-supplied derivative function `U_T_s : ℝ → ℝ → ℝ → ℝ`
representing `∂U_T/∂s`, the `HasDerivAt` witness at every
`(x, a, s)`, and the pointwise lower bound `−cT ≤ U_T_s x a s`,
produce the carrier-local quantified `LowerLossSlopeOn` condition that
`Target_combined_chord_of_decomposition_lowerChord` consumes (formerly a field
of `StandardComplianceLocalCoreCertificate`; round BJ1.4, 2026-10-07).

The user supplies one C¹ primitive on the stage Target payoff;
the discharger handles the carrier-local quantification over
`(V_T, V_S, x)`. -/
theorem h_stage_target_loss_on_of_partial_deriv
    (D : p.ValueClass2)
    {xT sbar cT : ℝ}
    {U_T_s : ℝ → ℝ → ℝ → ℝ}
    (h_hasDerivAt :
      ∀ x a s, HasDerivAt (fun t => p.U_T x a t) (U_T_s x a s) s)
    (h_lower : ∀ x a s, -cT ≤ U_T_s x a s) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn
          (fun s => p.U_T x (D.α_on V_T V_S x) s)
          (Set.Icc (max x sbar) 1) cT := by
  intro V_T V_S x _hx
  apply LowerLossSlopeOn.of_hasDerivAt_lowerBound
    (f' := fun s => U_T_s x (D.α_on V_T V_S x) s)
  · exact convex_Icc _ _
  · intro s _; exact h_hasDerivAt x (D.α_on V_T V_S x) s
  · intro s _; exact h_lower x (D.α_on V_T V_S x) s

/-! ## Round-13 Priority 3: certificate-facing wrappers for the Sender side

Parallel to Round-11 Priority 1 (Target loss-offset wrapper above),
Priority 3 discharges the Sender high-sanction-incentive primitives:

* `hV_S_lip_carrier_of_valLipBall_via_toValueClass2` — auto-discharges
  the per-`V_S` Lipschitz field `hV_S_lip_carrier` when the Sender
  carrier is `valLipBall M KS` (the `KS`-Lipschitz constant defining
  the carrier IS the certificate's `KS`).
* `h_stage_sender_on_of_partial_deriv` — discharges the
  carrier-local `LowerSlopeOn` field from a single C¹ partial
  derivative bound `∂U_S/∂s(x, a, s) ≥ mS`.

Both are pure dischargers (Rule-3 cat-2 weakening or no-new-assumption).

## Rule compliance
* Rule 1 (optimal strategies): structural — no strategy fixings.
* Rule 3: pure dischargers. The Lipschitz wrapper requires no extra
  hypothesis beyond the carrier choice (no-new-assumption). The
  slope wrapper recasts a discrete-chord Prop as a strictly weaker
  C¹ primitive (cat-2 weakening).
* Rule 5: fully parametric over `(D, xS, sbar, mS, KS, M, U_S_s)`.
* Rule 8: human-language paraphrase in docstrings + paper paragraph.
* Rule 9: non-vacuity witnesses in
  `Sanctions/Examples/JointPositiveSanctions.lean`. -/

/-- **Round-13 Priority 3, sub-wrapper (a): `hV_S_lip_carrier`
auto-discharge from `valLipBall` membership.**

When the asymmetric value class's Sender carrier is the Lipschitz
ball `valLipBall M KS`, every `V_S` in the carrier is automatically
`KS`-Lipschitz — the constant defining the carrier IS the
certificate's `KS`. The user supplies one carrier equation; the
field discharges trivially.

This is the Sender-side mirror of the existing
`ofLipBall_V_T_lipschitz_carrier` in
`Theory/Bellman/InvariantLipBall.lean`. -/
theorem hV_S_lip_carrier_of_valLipBall
    {D : p.ValueClass2} {M KS : ℝ}
    (hD_carrier_S : D.carrier_S = valLipBall M KS) :
    ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS := by
  intro V_S hV_S
  rw [hD_carrier_S] at hV_S
  exact hV_S.2

/-- **Round-13 Priority 3, sub-wrapper (b): certificate-facing C¹
discharger for `h_stage_sender_on`.**

From a user-supplied derivative function `U_S_s : ℝ → ℝ → ℝ → ℝ`
representing `∂U_S/∂s`, the `HasDerivAt` witness at every
`(x, a, s)`, and the pointwise lower bound `mS ≤ U_S_s x a s`,
produce the carrier-local quantified `LowerSlopeOn` field required
by `StandardComplianceLocalCoreCertificate`.

Parallel to `h_stage_target_loss_on_of_partial_deriv` (above) for
the Sender side. The user supplies one paper-stateable C¹ primitive
("Sender's per-period sanction-marginal welfare is at least `mS`");
the wrapper handles the carrier-local quantification over
`(V_T, V_S, x)`. -/
theorem h_stage_sender_on_of_partial_deriv
    (D : p.ValueClass2)
    {xS sbar mS : ℝ}
    {U_S_s : ℝ → ℝ → ℝ → ℝ}
    (h_hasDerivAt :
      ∀ x a s, HasDerivAt (fun t => p.U_S x a t) (U_S_s x a s) s)
    (h_lower : ∀ x a s, mS ≤ U_S_s x a s) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS := by
  intro V_T V_S x _hx
  apply LowerSlopeOn.of_hasDerivAt_lowerBound
    (f' := fun s => U_S_s x (D.α_on V_T V_S x) s)
  · exact convex_Icc _ _
  · intro s _; exact h_hasDerivAt x (D.α_on V_T V_S x) s
  · intro s _; exact h_lower x (D.α_on V_T V_S x) s

/-! ## Round-29 Priority 7: certificate-facing C¹ cross-partial discharger
for `hSC_on` under the saturated-α regime

The `StandardComplianceLocalCoreCertificate` field `hSC_on` is the
Milgrom-Shannon single-crossing-on-a-rectangle property for the Sender
dynamic objective evaluated at the carrier-local Target selector
`D.α_on V_T V_S`:

```
hSC_on V_T V_S : SingleCrossingOn I (Icc (max xT xS) 1)
                   (fun s x => senderDynObjective V_S.val x
                                 (D.α_on V_T V_S x) s)
```

In its raw form `hSC_on` is a chord-style Prop quantified over the
basin rectangle. For paper-facing presentation the cleanest sufficient
condition is the **smooth cross-partial** criterion (Milgrom-Shannon
1994 Theorem 6; Curtat 1996 Lemma 1; Topkis 1998 Theorem 2.6.1):

> If `g(s, x)` is C¹ in `x`, with `∂g/∂x` non-decreasing in `s` on the
> rectangle, then `g` has increasing differences on the rectangle, which
> implies single crossing.

The wrapper `hSC_on_of_cross_partial_nonneg_saturatedAlpha` takes the
**saturated-α regime** as a structural hypothesis (the leader selector
`D.α_on V_T V_S x` is constant in `x` on the basin
`[max xT xS, 1]`) plus a paper-stateable C² primitive on the Sender
dynamic objective in the saturated form (one user-supplied derivative
function `g_x : V_T → V_S → ℝ → ℝ → ℝ` representing `∂g/∂x` at the
saturated action, the `HasDerivAt` witnesses, and the cross-partial
monotonicity `s ≤ s' ⇒ g_x s ≤ g_x s'`), and produces the carrier-local
`hSC_on` field.

### The saturated-α regime

When the leader selector `α_on V_T V_S` is constant in `x` on the
basin (the **saturated** regime — the equilibrium leader plays a
fixed compliance action `α₀` on the entire basin, e.g. minimal
compliance `α₀ = 0` under a strong-sanctions regime), the Sender
dynamic objective in `(s, x)` becomes:

```
g(s, x) = U_S(x, α₀(V_T,V_S), s) + β_S · V_S(clipS'((1-δ)x + δs))
```

The `x`-dependence of `α_on` drops out, so the cross-partial criterion
applies to a function of two scalar variables. This is a Rule-3-FREE
regime: no new economic hypothesis beyond the structural fact that
the leader selector is saturated (a consequence of the Bellman
optimality + the basin geometry).

### Continuation-term caveat

The cross-partial of `g` decomposes as:

```
∂²g/∂s∂x = ∂²U_S/∂s∂x(x, α₀, s)
           + β_S · δ · (1-δ) · V_S''(clipS'((1-δ)x + δs))
```

Two cases:

* **Linear-V_S (LQ) regime**: `V_S''(·) = 0` so the continuation term
  vanishes and the criterion reduces to checking `∂²U_S/∂s∂x ≥ 0`
  on the rectangle — purely a primitive-payoff condition.
* **General-V_S regime**: the continuation term contributes; the
  criterion needs the sum to be non-negative. Bounding
  `|V_S''| ≤ K_S''` and requiring `β_S · δ · (1-δ) · K_S'' ≤
  ∂²U_S/∂s∂x` (a margin in the spirit of `β_S · K_S · δ < m_S`).

The wrapper exposes only the *abstract* `g_x` and cross-partial
monotonicity — the user discharges these from whichever regime
applies. The saturated-α restriction is the only Rule-3 boundary
modeled directly here; the non-saturated α-monotone variant routes
through the increasing-differences-on (IDO) framework of Round 30.

## Rule compliance

* Rule 1 (optimal strategies): structural — no strategy fixings.
  `D.α_on V_T V_S` is the carrier-local leader argmax produced by
  `ValueClass2`. The saturated-α hypothesis is an *equilibrium*
  property (the optimal selector happens to be constant on the
  basin), not an assumption that overrides Rule 1.
* Rule 3: pure cat-2 discharger. The user replaces the chord
  hypothesis `hSC_on` with a strictly weaker C¹ + cross-partial
  primitive plus the saturated-α structural fact. No new
  certificate fields are added.
* Rule 5: fully parametric over `(D, xT, xS, V_T, V_S, g_x, α₀)`.
* Rule 8: human-language paraphrase in docstrings + paper paragraph.
* Rule 9: non-vacuity witness in
  `Sanctions/Examples/JointPositiveSanctions.lean`. -/

/-- **Round-29 Priority 7: certificate-facing C¹ cross-partial discharger
for `hSC_on` (saturated-α variant).**

Under the *saturated-α regime* — the carrier-local leader selector
`D.α_on V_T V_S` is constant in `x` on the basin
`[max xT xS, 1]` — the Sender dynamic objective in `(s, x)` becomes a
genuine function of two scalar variables (the leader-action argument
drops its `x`-dependence on the basin). The Milgrom-Shannon Theorem 6
/ Topkis Theorem 2.6.1 / Curtat Lemma 1 cross-partial criterion then
discharges the single-crossing field `hSC_on` from a paper-stateable
C² primitive: `∂(g_x)/∂s ≥ 0` on the rectangle, where `g_x` is the
user-supplied derivative function for `∂g/∂x`.

The wrapper produces the carrier-local `hSC_on` field of
`StandardComplianceLocalCoreCertificate` from:

1. The saturated-α hypothesis `h_saturated` (a `V_T, V_S`-indexed
   constant `α₀ V_T V_S` such that `D.α_on V_T V_S x = α₀ V_T V_S`
   for every `x ∈ [max xT xS, 1]`).
2. A pointwise `HasDerivAt` witness for `(fun x => g V_T V_S s x)` at
   every `(V_T, V_S, s ∈ I, x ∈ [max xT xS, 1])`, where
   `g V_T V_S s x = senderDynObjective V_S.val x (α₀ V_T V_S) s`.
3. The cross-partial monotonicity hypothesis: for every
   `V_T, V_S, x ∈ [max xT xS, 1]`, `s ≤ s' in I` implies
   `g_x V_T V_S s x ≤ g_x V_T V_S s' x`.

One-line delegation pattern: package the two paper-stateable
hypotheses, apply
`IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on` (the
Foundations/MilgromShannon.lean discharger), then bridge via
`IncreasingDifferencesOn.toSingleCrossingOn`. -/
theorem hSC_on_of_cross_partial_nonneg_saturatedAlpha
    (D : p.ValueClass2)
    {xT xS : ℝ}
    {α₀ : D.CarrierT → D.CarrierS → ℝ}
    {g_x : D.CarrierT → D.CarrierS → ℝ → ℝ → ℝ}
    (h_saturated :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          D.α_on V_T V_S x = α₀ V_T V_S)
    (h_hasDerivAt :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ s ∈ Sanctions.I,
          ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
            HasDerivAt
              (fun y => p.senderDynObjective V_S.val y (α₀ V_T V_S) s)
              (g_x V_T V_S s x) x)
    (h_cross :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I, s ≤ s' →
            g_x V_T V_S s x ≤ g_x V_T V_S s' x) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) := by
  intro V_T V_S
  -- Rewrite the target SC using the saturated-α hypothesis: on the basin,
  -- `D.α_on V_T V_S x` reduces to the constant `α₀ V_T V_S`, so the
  -- objective coincides with the C² saturated form.
  have h_eq :
      ∀ s ∈ Sanctions.I,
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s
            = p.senderDynObjective V_S.val x (α₀ V_T V_S) s := by
    intro s _ x hx
    rw [h_saturated V_T V_S x hx]
  -- Step 1: increasing differences on `I × [max xT xS, 1]` for the
  -- saturated-form objective `g(s, x) := senderDynObjective V_S x α₀ s`.
  have hID :
      Sanctions.MilgromShannon.IncreasingDifferencesOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (α₀ V_T V_S) s) := by
    apply Sanctions.MilgromShannon.IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on
      (f_x := fun s x => g_x V_T V_S s x)
    · exact convex_Icc _ _
    · intro s hs x hx; exact h_hasDerivAt V_T V_S s hs x hx
    · intro x hx s hs s' hs' hss
      exact h_cross V_T V_S x hx s hs s' hs' hss
  -- Step 2: ID ⇒ SC on the localized rectangle.
  have hSC_sat := hID.toSingleCrossingOn
  -- Step 3: transfer SC from the saturated-form objective to the
  -- original `D.α_on`-form via the saturated-α equality on the basin.
  intro x y t t' hx hy hxy ht ht' htt
  -- All four evaluations of the original objective at points
  -- (x, t), (y, t), (x, t'), (y, t') with `x, y ∈ I` and `t, t' ∈ [max xT xS, 1]`
  -- coincide with the saturated-form evaluations.
  have h1 :
      p.senderDynObjective V_S.val t (D.α_on V_T V_S t) x
        = p.senderDynObjective V_S.val t (α₀ V_T V_S) x := h_eq x hx t ht
  have h2 :
      p.senderDynObjective V_S.val t (D.α_on V_T V_S t) y
        = p.senderDynObjective V_S.val t (α₀ V_T V_S) y := h_eq y hy t ht
  have h3 :
      p.senderDynObjective V_S.val t' (D.α_on V_T V_S t') x
        = p.senderDynObjective V_S.val t' (α₀ V_T V_S) x := h_eq x hx t' ht'
  have h4 :
      p.senderDynObjective V_S.val t' (D.α_on V_T V_S t') y
        = p.senderDynObjective V_S.val t' (α₀ V_T V_S) y := h_eq y hy t' ht'
  have hSC_pair := hSC_sat hx hy hxy ht ht' htt
  -- `hSC_pair` is stated on the saturated objective `(fun s x ↦
  -- p.senderDynObjective V_S.val x (α₀ V_T V_S) s)`; the original SC
  -- consumer pattern uses `(fun s x ↦ p.senderDynObjective V_S.val x
  -- (D.α_on V_T V_S x) s)`. Beta-reducing both lambdas and applying
  -- `h1`–`h4` (the saturated-α equalities on the basin) transfers SC
  -- from the saturated form to the `D.α_on` form.
  simp only at hSC_pair
  refine ⟨fun h_weak => ?_, fun h_strict => ?_⟩
  · simp only at h_weak
    have h_weak' :
        p.senderDynObjective V_S.val t (α₀ V_T V_S) x
          ≤ p.senderDynObjective V_S.val t (α₀ V_T V_S) y := by
      rw [← h1, ← h2]; exact h_weak
    have hres := hSC_pair.1 h_weak'
    simp only
    rw [h3, h4]; exact hres
  · simp only at h_strict
    have h_strict' :
        p.senderDynObjective V_S.val t (α₀ V_T V_S) x
          < p.senderDynObjective V_S.val t (α₀ V_T V_S) y := by
      rw [← h1, ← h2]; exact h_strict
    have hres := hSC_pair.2 h_strict'
    simp only
    rw [h3, h4]; exact hres

/-! ## Round 43 Phase B — α_0 auto-extraction in the saturated-α
    discharger

The R29 discharger `hSC_on_of_cross_partial_nonneg_saturatedAlpha`
takes `α₀ : D.CarrierT → D.CarrierS → ℝ` as a separate input — the
constant value of `D.α_on V_T V_S` on the basin. When the saturated
regime holds (`D.α_on V_T V_S` is constant in `x` on the basin), the
value `α₀ V_T V_S` is determined by the equilibrium: it equals
`D.α_on V_T V_S y` for *any* basin point `y`. Round 43 Phase B
extracts `α₀` automatically at the canonical pivot
`y := max(xT, xS)`, removing it from the user-facing input surface.

The user now supplies only the structural saturation hypothesis
`∀ V_T V_S, ∀ x ∈ basin, D.α_on V_T V_S x = D.α_on V_T V_S (max xT xS)`
(α is constant on the basin equal to its value at the joint pivot)
plus the C¹ cross-partial inputs. The `α₀` function is constructed
internally as `fun V_T V_S => D.α_on V_T V_S (max xT xS)`.

## Rule compliance
* Rule 3 symbol-economy: `α₀` is identified with an existing
  equilibrium quantity at the canonical basin pivot; no new modeling
  content is introduced.
* Rule 5: parametric.
* Rule 8: human-language paraphrase below. -/

/-- **Round 43 Phase B: `α₀`-auto-extracted saturated-α discharger.**

    Sibling of `hSC_on_of_cross_partial_nonneg_saturatedAlpha` that
    extracts `α₀ V_T V_S := D.α_on V_T V_S (max xT xS)` automatically
    from the equilibrium. The user supplies only:

    1. `h_saturated_pivot` — `D.α_on V_T V_S x = D.α_on V_T V_S (max xT xS)`
       for every `x` on the basin (the saturation property, stated
       relative to the canonical pivot).
    2. `h_hasDerivAt` — the pointwise derivative-existence witness for
       the saturated-form objective at the extracted `α₀`.
    3. `h_cross` — the cross-partial monotonicity in `s`.

    The conclusion is the same single-crossing carrier-local field
    used by `StandardComplianceLocalCoreCertificate.hSC_on`. -/
theorem hSC_on_of_cross_partial_nonneg_saturatedAlpha_auto_extract
    (D : p.ValueClass2) {xT xS : ℝ}
    {g_x : D.CarrierT → D.CarrierS → ℝ → ℝ → ℝ}
    (h_saturated_pivot :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          D.α_on V_T V_S x = D.α_on V_T V_S (max xT xS))
    (h_hasDerivAt :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ s ∈ Sanctions.I,
          ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
            HasDerivAt
              (fun y => p.senderDynObjective V_S.val y
                (D.α_on V_T V_S (max xT xS)) s)
              (g_x V_T V_S s x) x)
    (h_cross :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I, s ≤ s' →
            g_x V_T V_S s x ≤ g_x V_T V_S s' x) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) :=
  p.hSC_on_of_cross_partial_nonneg_saturatedAlpha D
    (α₀ := fun V_T V_S => D.α_on V_T V_S (max xT xS))
    h_saturated_pivot h_hasDerivAt h_cross

/-! ## Round-30: Interval-Dominance-Order discharger for `hSC_on`
(non-saturated regime, α-monotone-free)

The Round-29 discharger
`hSC_on_of_cross_partial_nonneg_saturatedAlpha` covers the
**saturated**-α regime, where the carrier-local leader selector
`D.α_on V_T V_S x` collapses to a `V_T, V_S`-indexed constant on the
basin. The natural complement is the **non-saturated**-α regime where
`D.α_on V_T V_S x` genuinely varies with `x`. The previous
analysis-of-record route to `hSC_on` in this regime required
**strict-SC + α-monotone** as a primitive hypothesis: α-monotonicity
is a strong (and Rule-3-flagged) behavioral assumption on the leader
selector that the literature provides no clean discharger for.

Quah-Strulovici (2007, *Comparative Statics with the Interval
Dominance Order: Some Extensions*, file
`PaperRefer/MathTheory/IntervalDominanceOrderExtensions-QuahStrulovici.md`;
the UNPUBLISHED companion notes — its numbering differs from the published
Econometrica 2009 paper, see the hazard note in
`Foundations/IntervalDominanceOrder.lean`)
Proposition 6 + Theorem 1 give a **strictly weaker** sufficient
condition: I-quasisupermodularity from sign-preservation of the
choice-axis partial. The scalar specialisation used here lives in
`Sanctions/Foundations/IntervalDominanceOrder.lean`; the composite
discharger `SingleCrossingOn.of_choice_strictMono` produces
`SingleCrossingOn` directly from **choice-axis strict monotonicity
of every member of the parameter family** (every `F(·, t)` strict-
mono on the choice interval `S`), with NO α-monotonicity required.

For the project's `senderDynObjective`, choice-axis strict
monotonicity in `s` (Sender prefers more sanctions at the relevant
range) is exactly what
`senderDynObjective_strictMono_of_stage_strictMono_and_V_mono` (in
`JointPreferenceBasin.lean`) already derives from the *stage* Sender
slope primitive `h_stage_sender_on` plus monotone continuation
`V_S`. So the IDO route discharges `hSC_on` from primitives
that the certificate already carries — without any new field, and
without strict-SC or α-monotone as primitives.

### Rule compliance

* Rule 1 (optimal strategies): structural — discharger only rewrites
  the assumption side; no strategy fixings.
* Rule 3 (assumption surface): pure cat-2 weakening — the user
  replaces the chord-style `hSC_on` with the strictly-weaker
  choice-axis monotonicity primitive (already available via
  `h_stage_sender_on` chain). No new certificate fields. No
  α-monotonicity primitive introduced.
* Rule 5 (parametric): fully parametric over `(D, xT, xS)` and the
  carrier-local choice-monotonicity hypothesis.
* Rule 8 (human-language): paraphrase above + below.
* Rule 9 (non-vacuity): sibling example in
  `Sanctions/Examples/JointPositiveSanctions.lean`.
* Rule 19 (Foundations vs Theory split): the IDO theory lives in
  `Foundations/IntervalDominanceOrder.lean`; this wrapper is the
  thin Params-level adapter.

### Caveat per Round 30 plan

Per the round plan's "recommend (b)" clause: this discharger is a
**SIBLING** that produces the same `SingleCrossingOn`-typed output as
the existing `hSC_on_of_cross_partial_nonneg_saturatedAlpha`. The
downstream consumer
`dynamicTopRealizedRule_mono_of_singleCrossingOn` (in
`Theory/Basin/JointPreferenceBasin.lean`) is unchanged. -/

/-- **Round-30: IDO-route certificate-facing discharger for `hSC_on`
(non-saturated regime).**

Strictly weaker replacement for the previous strict-SC + α-monotone
combination. Takes only:

1. The carrier-local choice-axis strict monotonicity of
   `senderDynObjective V_S.val · (D.α_on V_T V_S x) ·` on
   `Sanctions.I` for every `x ∈ [max xT xS, 1]`.

Returns the `hSC_on` field of
`StandardComplianceLocalCoreCertificate` — i.e. the localised
single-crossing Prop on `I × [max xT xS, 1]` for the parameter
family `(s, x) ↦ senderDynObjective V_S.val x (D.α_on V_T V_S x) s`.

NO α-monotonicity is required. The choice-monotonicity hypothesis is
the one already produced by
`senderDynObjective_strictMono_of_stage_strictMono_and_V_mono` from
the stage primitive `h_stage_sender_on` plus monotone `V_S`. -/
theorem hSC_on_of_choice_strictMono_IDO
    (D : p.ValueClass2)
    {xT xS : ℝ}
    (h_choice_strictMono :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          StrictMonoOn
            (fun s => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
            Sanctions.I) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) := by
  intro V_T V_S
  apply Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono
    (S := Sanctions.I)
    (T := Set.Icc (max xT xS) 1)
    (F := fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
  · -- Sanctions.I = [0, 1] is convex.
    exact convex_Icc _ _
  · -- Per-parameter strict monotonicity of the choice axis: this is
    -- exactly the user-supplied hypothesis.
    intro x hx
    exact h_choice_strictMono V_T V_S x hx

/-! ## Sender basin combined-monotonicity (dynamic-dominance regime)

The Sender twin of `TargetCombinedChordOn`. Issue-1 (referee) asks that
the single-crossing field `hSC_on` be *derived from a regime
characterisation* rather than assumed at the equilibrium action. A
disprove-first numerical study (`docs/archive/workflow-scratch/probe_concavity_sc.lean`,
`probe_bellman_invariance.lean`, `probe_sender_policy.lean`) established:

* convexity of `V_S` gives single crossing unconditionally but is
  near-vacuous (standard DP yields *concave* value, SLP Thm 4.8);
* the cardinal increasing-differences class is Bellman-invariant and
  *attracting* under a sufficient rally (Hopenhayn-Prescott 1992 §6.B
  cc-class, Prop 2), so the equilibrium is *constructed* inside the
  regime, not assumed into it;
* but the *ordinal* single crossing `hSC_on` actually needs only the
  weaker **combined-monotonicity**: at the constructed equilibrium the
  Sender plays the high-sanction corner (`σ* ≡ 1` on the basin) because
  the realised dynamic objective is increasing in `s` — even though the
  stage `U_S` is *not* monotone in `s` and the value `V_S` is *not*
  monotone. The clean two-scalar margin `cS ≤ β_S·gS·δ` (the literal
  Target twin) fails precisely because `V_S` is non-monotone, so the
  honest form is the combined chord itself, exactly as the Target side
  states `TargetCombinedChordOn` directly. -/

/-- **Sender basin combined-monotonicity** (Sender twin of
`TargetCombinedChordOn`). On the basin high-sanction range the realised
forward-looking Sender objective `senderDynObjective V_S x (α x) ·` —
current stage payoff `U_S` plus discounted continuation
`β_S · V_S(F(x,·))` — is *strictly increasing in the sanction `s`* for
every carrier pair and every basin state `x ∈ [max xT xS, 1]`.

Economically this is the **dynamic-dominance regime**: the forward-looking
continuation gain from entrenching the political state outweighs any
current sanction-loss, so the Sender's best response is the high-sanction
corner. It is strictly *weaker* than the existing `hSC_on` routes — it
requires neither the stage payoff `U_S` to be monotone in `s` (it may
fall) nor the continuation value `V_S` to be monotone (it may be
non-monotone); only their *sum* need rise. -/
def SenderCombinedMonotoneOn (D : p.ValueClass2) (xT xS : ℝ) : Prop :=
  ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
    ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
      StrictMonoOn
        (fun s => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
        Sanctions.I

/-- **`hSC_on` from basin combined-monotonicity.** The
`SenderCombinedMonotoneOn` regime condition discharges the carrier-local
single-crossing field `hSC_on` of `StandardComplianceLocalCoreCertificate`
— the Milgrom-Shannon single crossing of the dynamic Sender objective in
`(s, x)` on `I × [max xT xS, 1]`. The proof is a one-line specialisation
of `hSC_on_of_choice_strictMono_IDO` (which reduces single crossing to
choice-axis strict monotonicity via the Interval-Dominance-Order route in
`Foundations/IntervalDominanceOrder.lean`); no α-monotonicity, no value
convexity, and no curvature margin are required. -/
theorem hSC_on_of_senderCombinedMonotone
    (D : p.ValueClass2) {xT xS : ℝ}
    (hmono : p.SenderCombinedMonotoneOn D xT xS) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) :=
  p.hSC_on_of_choice_strictMono_IDO D hmono

/-- **General-`F` discharge of Sender combined monotonicity from an
exact transition-adjusted chord.**

For every carrier pair, basin state, and ordered sanction pair, the
stage-payoff increase is required to dominate the largest continuation
loss permitted by the carrier's `KS`-Lipschitz bound, evaluated at the
actual successor states generated by `F`. This derives
`SenderCombinedMonotoneOn` without assuming an affine transition or
introducing a separate sanction-Lipschitz modulus for `F`. -/
theorem senderCombinedMonotoneOn_of_transition_adjusted_chord_and_carrier_lipschitz
    (D : p.ValueClass2)
    {xT xS KS : ℝ}
    (hV_S_lip : ∀ V_S : D.CarrierS, ValueLipschitzWith V_S.val KS)
    (h_transition_adjusted_chord :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
            p.β_S * KS *
                dist (Sanctions.clipS' (p.F x s₁))
                     (Sanctions.clipS' (p.F x s₂))
              < p.U_S x (D.α_on V_T V_S x) s₂ -
                  p.U_S x (D.α_on V_T V_S x) s₁) :
    p.SenderCombinedMonotoneOn D xT xS := by
  intro V_T V_S x hx
  have hmax : max x (1 : ℝ) = 1 := max_eq_right hx.2
  have hchord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x 1),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x 1), s₁ < s₂ →
          p.β_S * KS *
              dist (Sanctions.clipS' (p.F x s₁))
                   (Sanctions.clipS' (p.F x s₂))
            < p.U_S x (D.α_on V_T V_S x) s₂ -
                p.U_S x (D.α_on V_T V_S x) s₁ := by
    rw [hmax]
    exact h_transition_adjusted_chord V_T V_S x hx
  have hmono :=
    p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
      (V_S := V_S.val) (α := D.α_on V_T V_S) (x := x) (sbar := 1)
      (K := KS) hchord (hV_S_lip V_S)
  rw [hmax] at hmono
  exact hmono

/-- **Slim general-`F` certificate from the exact transition-adjusted
Sender chord.**

This constructor packages the non-affine quantitative route into
`StandardComplianceLocalCoreCertificate_MS`. The exact chord performs
two jobs. First, because its continuation-loss allowance is
non-negative, it implies that the Sender's stage payoff is strictly
increasing on the certificate's low sanction range. Second, together
with the carrier's `KS`-Lipschitz value bound, it makes the full Sender
dynamic objective strictly increasing on the basin; this supplies the
certificate's interval-dominance field.

The constructor introduces no sanction-Lipschitz modulus for `F`.
Callers may set
`KS = L_U_S / (1 - β_S * γ_F)` using the optional inherited-state
regularity route, but the sanction comparison always evaluates the
actual displacement `dist (F(x,s₁)) (F(x,s₂))`. -/
def StandardComplianceLocalCoreCertificate_MS.of_transition_adjusted_chord
    [p.StaticSelectorContinuous]
    (D : p.ValueClass2)
    (h_inv : D.IsInvariant)
    (β_T β_S L_TS L_ST : ℝ)
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1)
    (hsuff_S : β_S + L_ST < 1)
    (xT xS : ℝ)
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hpivot_mem : max xT xS ∈ Set.Ioo (0 : ℝ) 1)
    (KS : ℝ)
    (hKS_nonneg : 0 ≤ KS)
    (hV_S_lip_carrier :
      ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS)
    (h_transition_adjusted_chord :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
            p.β_S * KS *
                dist (Sanctions.clipS' (p.F x s₁))
                     (Sanctions.clipS' (p.F x s₂))
              < p.U_S x (D.α_on V_T V_S x) s₂ -
                  p.U_S x (D.α_on V_T V_S x) s₁)
    (h_target_combined : p.TargetCombinedChordOn D xT (max xT xS))
    (hV_S_mono_carrier : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1,
        p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
          ≤ max x (max xT xS)) :
    p.StandardComplianceLocalCoreCertificate_MS where
  D := D
  h_inv := h_inv
  β_T := β_T
  β_S := β_S
  L_TS := L_TS
  L_ST := L_ST
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hL_TS_nn := hL_TS_nn
  hL_ST_nn := hL_ST_nn
  hT_T_op := hT_T_op
  hT_S_op := hT_S_op
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S
  xT := xT
  xS := xS
  hxT_mem := hxT_mem
  hxS_mem := hxS_mem
  hpivot_mem := hpivot_mem
  h_stage_sender_strictMono := by
    intro V_T V_S x hx
    apply p.stageSenderObjective_strictMono_of_transition_adjusted_chord
      p.β_S_mem.1 hKS_nonneg
    intro s₁ hs₁ s₂ hs₂ hlt
    have hmax_le : max x (max xT xS) ≤ 1 :=
      max_le hx.2 (le_of_lt hpivot_mem.2)
    exact h_transition_adjusted_chord V_T V_S x hx s₁
      ⟨hs₁.1, hs₁.2.trans hmax_le⟩ s₂
      ⟨hs₂.1, hs₂.2.trans hmax_le⟩ hlt
  hIDO_on := by
    have hcombined : p.SenderCombinedMonotoneOn D xT xS := by
      apply p.senderCombinedMonotoneOn_of_transition_adjusted_chord_and_carrier_lipschitz
        D (fun V_S => hV_S_lip_carrier V_S.val V_S.property)
      intro V_T V_S x hx
      apply h_transition_adjusted_chord V_T V_S x
      exact ⟨le_trans (le_max_right xT xS) hx.1, hx.2⟩
    intro V_T V_S
    exact Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (p.hSC_on_of_senderCombinedMonotone D hcombined V_T V_S)
  h_target_combined := h_target_combined
  hV_S_mono_carrier := hV_S_mono_carrier
  hMyoCeiling := hMyoCeiling


/-- **B2 field-level discharger: `hIDO_on` from quasiconcavity +
monotonicity transfer.** Produces exactly the certificate field type of
`StandardComplianceLocalCoreCertificate.hIDO_on` (and its `_MS`/Schur
siblings) in the regime single crossing cannot reach. -/
theorem hIDO_on_of_quasiconcave_monotoneTransfer
    (D : p.ValueClass2) {xT xS : ℝ}
    (hQC : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        QuasiconcaveOn ℝ Sanctions.I
          (fun s => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (hMT : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.MonotoneTransferOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) :=
  fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_quasiconcave_monotoneTransfer
      (convex_Icc 0 1) (fun x hx => hQC V_T V_S x hx) (hMT V_T V_S)

/-! ## Round-25 Priority 6: smart constructor with closed-form `KS`

The default `StandardComplianceLocalCoreCertificate` builder requires
the user to compute the Sender carrier Lipschitz constant `KS` by hand
and supply both `KS` itself and the Sender wedge
`β_S · KS · δ < mS` as primitive scalars.

Hinderer 4.2(c) (Benveniste-Scheinkman envelope; see
`Foundations/StokeyLucas.lean`'s `bellmanLipConstant`) gives the
closed-form constant `K_S := L_U_S / (1 − β_S · γ_F)` under stage
payoff Lipschitz `L_U_S` and transition Lipschitz `γ_F` with
contraction margin `β_S · γ_F < 1`. The smart constructor
`with_KS_closed_form` below accepts the underlying Hinderer 4.2(c) inputs
(`L_U_S`, `γ_F`, `0 < 1 − β_S · γ_F`, and the rewritten wedge
`β_S · L_U_S · δ < mS · (1 − β_S · γ_F)`) plus a per-`V_S`
Lipschitz hypothesis at the closed-form constant, and produces a
`StandardComplianceLocalCoreCertificate` whose primitive `KS` field
is `bellmanLipConstant p.β_S γ_F L_U_S`.

This eliminates `KS` as a free primitive scalar — the user now
supplies economically interpretable inputs (the stage payoff
Lipschitz coefficient and the contraction margin) and the
certificate's Sender Lipschitz constant is computed in closed form.

## Rule compliance
* Rule 1: structural, no strategy fixings.
* Rule 3: pure cat-2 weakening — no new certificate fields are
  added; the original `KS`, `hKS_nonneg`, `hS_margin` are
  derived from `(L_U_S, γ_F, h_denom_pos, h_wedge_closed)`.
* Rule 5: fully parametric.
* Rule 8: human-language paraphrase in this docstring.
* Rule 9: numeric non-vacuity witness in
  `Sanctions/Examples/StandardCompliancePolynomialSkeleton.lean`. -/


end Params
end AbstractGame

end

end Sanctions
