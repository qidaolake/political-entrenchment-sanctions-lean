/-
Sanctions/Theory/Bridges/JETBridgeC1System.lean

**Audit-39 Gap 1 closure: paper-facing C¹-Bellman-System three-goals bridge.**

**STILL FROZEN / LEGACY (status reaffirmed 2026-07-12).** The C¹
*witness* layer was partially unfrozen elsewhere
(`Examples/C1WitnessEnvelope.lean` inhabits the C¹ carrier at two
pinned exact fixed points, and the paper cites the resulting shadow
prices), but **this legacy bridge is not part of that unfreeze**: the
shipped C¹ endpoint runs through
`Certificates/StandardComplianceLocalC1.lean`, and despite the
"paper-facing" framing below, no paper claim cites this bridge. Known
deficiencies recorded, not repaired: `c1distPair` is a pseudo-metric
(`V'` stored on all of `ℝ`), and completeness
(`ValueClass_C1Complete`) is consumed per-certificate, not derived. Revival order if ever needed: (1) the
within-set uniform-limits-of-derivatives theorem (a mathlib gap, not
an analytic one — `Foundations/` candidate), (2) the `V'`-domain
refactor, (3) asymmetric duplication only once a consumer exists.

The audit-39 critique observes that the prior `JETBridgeC1` theorem
`jet_C1_existence_and_three_goals` keeps the C¹ Cauchy iteration and
the BCF three-goal equilibrium as *independent* outputs, requiring an
implicit "extraction primitive" to identify the C¹ fixed point with
the BCF equilibrium. The audit-37 `C1BellmanSystem` work
(`C1BellmanSystem.feedbackStackelbergEquilibriumTop_of_complete`)
removed the need for that primitive by giving a *theorem-level*
C¹-to-BCF lift.

This file packages the lift into a **paper-facing C¹-system three-goals
bridge**: the produced `FeedbackStackelbergEquilibriumTop` is *the same*
equilibrium that satisfies the three goal conclusions. No extraction
primitive is exposed.

## What this fixes

The prior `jet_C1_existence_and_three_goals` had two independent
outputs:

```text
(C¹ Cauchy iteration) ∧ (BCF three-goal equilibrium ∃ E)
```

with no Lean-side identification between the C¹ fixed point and the
BCF E. The audit-39 critique flagged this as stale post-`C1BellmanSystem`.

This file's bridges instead bundle:

```text
∃ E : FeedbackStackelbergEquilibriumTop,
  E comes from the C¹ Bellman system's c1distPair-fixed point,
  AND E satisfies the three goal conclusions.
```

**Only the compliance bridges remain.** The original
`jet_C1BellmanSystem_three_goals` was sign-correct only under the
resistance / noncompliance reading of `a`, and its distinguishing
hypothesis was that the myopic Target policy lies pointwise below the
policy of *every* equilibrium the game admits. Nothing consumed it once
the certificate that bundled its inputs was removed, and it was deleted
on 2026-08-17 together with that certificate family. What survives are
`jet_C1BellmanSystem_three_goals_compliance_on` and
`..._compliance_statewise`, which derive rule dominance from a myopic
ceiling plus a floor and are sign-correct under literal compliance.

## Rule compliance

**Rule 1.** The produced `E` is the C¹-to-BCF lift of the C¹ Bellman
system's fixed point — equilibrium-derived end-to-end.

**Rule 3.** No new hypotheses. The bridges compose
`feedbackStackelbergEquilibriumTop_of_complete` (iter 21) with the
goal-specific loss-offset bridges of `Bridges/JETBridge.lean`.

**Rule 5.** Fully parametric.
-/

import Sanctions.Theory.Bridges.JETBridge
import Sanctions.Theory.Bellman.C1BellmanSystem

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Audit-44 C¹ compliance bridge (localized + floor/ceiling)

The audit-44 follow-up applies the same tightening to the C¹
compliance bridge:

* `LowerSlopeOnValueOn V_T (Icc xT 1) gT` (localized) instead of
  global `LowerSlopeOnValue V_T gT`.
* `hMyoCeiling` (myopic ceiling) + internally-derived dynamic floor,
  instead of directly-assumed rule dominance.
* `hDyn_basin_E` derived from floor + `σ_dyn_top ∈ I`. -/


end Params
end AbstractGame

end -- noncomputable section

end Sanctions
