/-
Sanctions/Theory/Bridges/SenderResponse.lean

**HISTORICAL INTERFACE — no consumers (moved from `Postulates/`
2026-07-24, user decision, option b).**

The `JointMPE.SenderResponse` structure was designed to plug a
Sender-response function into the joint Bellman operator, but that
purpose never materialized: repo-wide, nothing takes a `SenderResponse`
as input — the joint Bellman machinery works off `σ_dyn` and the value
classes directly, and the optimality content is carried by the
`Params.σ_isMaxOn_U_S` field plus the Berge machinery. The two
instances below (static and dynamic, each with an argmax certification)
remain in `Theory/Equilibrium/{HeSunMPE,BergeContinuity}.lean` as the
audit-#11 closure artifacts. Kept here, out of the postulate layer, so
`Postulates/` contains only live assumption surface; do not build new
consumers without review.

The structure carries the data: the response itself, membership in
`[0, 1]`, and joint continuity in `(x, a)`.

**Instances at the abstract layer.** The static (stage-argmax) Sender
response from `AbstractGame.Params` lifts to a concrete instance via
`Sanctions.AbstractGame.Params.staticSenderResponse` in
`Theory/Equilibrium/HeSunMPE.lean` — it ignores `V_S` and uses the
abstract `σ` directly, with continuity discharged from
`p.σ_continuous` (under the instance `[p.StaticSelectorContinuous]`, a `Params`
field until round BJ5.1, 2026-10-07). The forward-looking argmax `σ_dyn` (defined in
`Theory/Equilibrium/JointMPE.lean` via `Classical.choose`) becomes an
instance of this interface under a local uniqueness hypothesis: see
`Sanctions.AbstractGame.Params.dynamicSenderResponse` in
`Theory/Equilibrium/BergeContinuity.lean`, which discharges the joint
`(x, a)`-continuity via the full Berge maximum theorem
(`σ_dyn_continuous_of_unique`). The canonical sufficient condition
for the uniqueness hypothesis is strict concavity of the **complete
dynamic Sender objective** in `s`. Strict concavity of `U_S` alone
delivers only uniqueness of the stage argmax; the continuation term
can undo that curvature.

This file contains ONLY the structure definition.
-/

import Sanctions.Foundations.Basic
import Sanctions.Domain.UnitIntervalProjection
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions

open Set Filter Topology

namespace JointMPE

/-- The data needed to plug an arbitrary Sender-response function into
the joint Bellman operator. -/
structure SenderResponse where
  σ : (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) →
      (x : ℝ) → (a : ℝ) → ℝ
  σ_mem : ∀ V_S x a, σ V_S x a ∈ I
  σ_continuous : ∀ V_S, Continuous (fun (xa : ℝ × ℝ) => σ V_S xa.1 xa.2)

end JointMPE
end Sanctions
