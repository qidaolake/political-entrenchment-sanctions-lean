/-
Sanctions/Theory/Equilibrium/JointIntegrandCongruence.lean

**The two Target integrands agree wherever the Sender's argmax is unique.**

The development carries two Target objectives that differ only in which Sender
selector they evaluate. `joint_T_integrand` uses `σ_dyn`, the `Classical.choose`
selector; `joint_T_top_integrand` uses `σ_dyn_top`, the *greatest* maximiser that
the equilibrium concept actually fixes. Where the Sender's dynamic argmax is
single-valued the two selectors coincide (`σ_dyn_eq_σ_dyn_top_of_unique`), so the
two objectives coincide, and any statement proved against one transfers to the
other.

That is the whole content of this file: three transfers — pointwise, at the
bounded-continuous-function level, and for leader maximisers.

## Why it is here rather than beside a witness

These statements quantify over an **arbitrary** `p : Params`. They fix no payoff
coefficients, no transition, no discount factors and no numerical constants, so
under Rule 19 they belong in `Theory/`.

They lived in `Examples/C1WitnessEnvelope.lean` until 2026-08-16, filed there for
the historical reason that the C¹ witness pins were the first consumer. Nothing
about them was witness-specific, and the misfiling had a cost: a layer audit that
classified results by directory read them as witness material. Moved on that
finding; the witness file now imports them.

## What consumes them

The W2 value pins are stated at `jointTarget_BCF_on_S`, which is built on
`σ_dyn`, while `C1BellmanSystem.T_value_eq_target` wants the supremum of the
`σ_dyn_top` integrand. `jointTarget_BCF_on_S_eq_sSup_top` is exactly that bridge.
`isMaxOn_joint_T_top_of_isMaxOn_joint` carries a Target optimality proof across
the same gap, which is what an equilibrium's `α_opt_top` field needs.

## Scope

`DynamicArgmaxUnique V_S` — the Sender's dynamic argmax is a singleton at every
physical state and every compliance level — is an existing project predicate,
carried by the standard compliance certificates. It is consumed here, not
introduced: nothing in this file widens the assumption surface.

Round BJ4.3 (2026-10-08) adds the compliance-local siblings
`jointTarget_BCF_on_S_eq_sSup_top_of_uniqueOnI` and
`isMaxOn_joint_T_top_of_isMaxOn_joint_of_uniqueOnI`, which need uniqueness only
at physical compliance levels (`DynamicArgmaxUniqueOnI`, the form a
`ValueClass2` carries). The BCF-level bridge is now the instance of the first
at `h_unique_on.toOnI`.
-/

import Sanctions.Theory.Equilibrium.JointExistenceFromPrimitives
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.LockIn.SigmaDynComparison

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Integrand congruence under uniqueness.** At every physical state
`x ∈ S`, the `σ_dyn`-based Target integrand equals the
`σ_dyn_top`-based one: per-`(x,a)` argmax uniqueness makes the two
Sender selectors coincide. -/
theorem joint_T_integrand_eq_top_of_unique_on
    (V_T V_S : Val) (h_unique_on : p.DynamicArgmaxUnique V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    p.joint_T_integrand V_T V_S x a
      = p.joint_T_top_integrand V_T V_S x a := by
  change p.U_T x a (p.σ_dyn V_S x a)
      + p.β_T * V_T (Sanctions.clipS' (p.F x (p.σ_dyn V_S x a)))
    = p.U_T x a (p.σ_dyn_top V_S x a)
      + p.β_T * V_T (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)))
  rw [p.σ_dyn_eq_σ_dyn_top_of_unique V_S x a (h_unique_on x hx a)]

/-- **BCF-level congruence at physical compliance (round BJ4.3,
2026-10-08)**: the state-local joint Target Bellman value
(`jointTarget_BCF_on_S`, built on `σ_dyn`) equals the sSup of the
`σ_dyn_top`-based integrand, under compliance-local Sender uniqueness
(`DynamicArgmaxUniqueOnI`). General in `F`. The supremum reads the two
integrands only at compliance levels in `I`, where they agree
(`joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI`), so uniqueness at
compliance levels outside `[0,1]` is not needed. -/
theorem jointTarget_BCF_on_S_eq_sSup_top_of_uniqueOnI
    (V_T V_S : Val) (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.jointTarget_BCF_on_S V_T V_S h_unique_on x
      = sSup ((fun a => p.joint_T_top_integrand V_T V_S x.val a)
                '' Sanctions.I) := by
  rw [p.jointTarget_BCF_on_S_apply V_T V_S h_unique_on x]
  exact congrArg sSup (Set.image_congr fun _a ha =>
    (p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI h_unique_on
      x.property ha).symm)

/-- **BCF-level congruence**: the state-local joint Target Bellman
value (`jointTarget_BCF_on_S`, built on `σ_dyn`) equals the sSup of
the `σ_dyn_top`-based integrand — the exact right-hand side that
`C1BellmanSystem.T_value_eq_target` requires.

Since round BJ4.3 (2026-10-08) the state-local operator takes compliance-local
uniqueness, so it is applied to `h_unique_on.toOnI`, and this is the instance of
`jointTarget_BCF_on_S_eq_sSup_top_of_uniqueOnI` at that proof. General in
`F`. -/
theorem jointTarget_BCF_on_S_eq_sSup_top
    (V_T V_S : Val) (h_unique_on : p.DynamicArgmaxUnique V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.jointTarget_BCF_on_S V_T V_S h_unique_on.toOnI x
      = sSup ((fun a => p.joint_T_top_integrand V_T V_S x.val a)
                '' Sanctions.I) :=
  p.jointTarget_BCF_on_S_eq_sSup_top_of_uniqueOnI V_T V_S h_unique_on.toOnI x

/-- **Leader-argmax transfer along the congruence**: a maximizer of the
`σ_dyn`-based integrand is a maximizer of the `σ_dyn_top`-based one. -/
theorem isMaxOn_joint_T_top_of_isMaxOn_joint
    (V_T V_S : Val) (h_unique_on : p.DynamicArgmaxUnique V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) {a₀ : ℝ}
    (h : IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a)
          Sanctions.I a₀) :
    IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
      Sanctions.I a₀ := by
  rw [isMaxOn_iff] at h ⊢
  intro a ha
  rw [← p.joint_T_integrand_eq_top_of_unique_on V_T V_S h_unique_on hx a,
      ← p.joint_T_integrand_eq_top_of_unique_on V_T V_S h_unique_on hx a₀]
  exact h a ha

/-- **Leader-argmax transfer at physical compliance (round BJ4.3,
2026-10-08)**: under compliance-local Sender uniqueness, a feasible maximizer
of the `σ_dyn`-based integrand is a maximizer of the `σ_dyn_top`-based one.
General in `F`. Compliance-local sibling of
`isMaxOn_joint_T_top_of_isMaxOn_joint`: uniqueness at compliance levels
outside `[0,1]` is dropped, and the maximizer is required to be feasible
(`ha₀`), so that the two integrands are compared only on `I`. -/
theorem isMaxOn_joint_T_top_of_isMaxOn_joint_of_uniqueOnI
    (V_T V_S : Val) (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) {a₀ : ℝ} (ha₀ : a₀ ∈ Sanctions.I)
    (h : IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a)
          Sanctions.I a₀) :
    IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
      Sanctions.I a₀ := by
  rw [isMaxOn_iff] at h ⊢
  intro a ha
  rw [p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI h_unique_on hx ha,
      p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI h_unique_on hx ha₀]
  exact h a ha

end Params
end AbstractGame

end

end Sanctions
