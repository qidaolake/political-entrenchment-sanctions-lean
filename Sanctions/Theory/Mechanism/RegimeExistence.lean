/-
Sanctions/Theory/Mechanism/RegimeExistence.lean

**The factorial splits in half, and the split is the whole difficulty.**

Before any comparison of the four continuation regimes means anything, the four
regimes have to exist. That is an *existence obligation*, not an assumption, and
it turns out to be the binding constraint on the whole mechanism programme.

The split is clean, and it is structural rather than a gap in effort:

| regime | Sender's response | what is constructed |
|---|---|---|
| `00` | `p.σ` — a `Params` field | a `MyopicFeedbackEquilibrium` (`myopicFeedbackEquilibrium_exists_of_continuity`) |
| `10` | `p.σ` — a `Params` field | a **Target programme** against `p.σ` (this file); **on the placable-Sender family, a full equilibrium** (`target_only_regime_generalF`, headline row 37) |
| `01` | `σ_dyn V_S` — depends on `V_S` | nothing in general; **on the placable-Sender family, constructed** (`Examples/PlacableSenderRegime01`, the reading in which the Sender looks ahead and the Target does not, under (RL)) |
| `11` | `σ_dyn V_S` — depends on `V_S` | nothing in general; **on the placable-Sender family, constructed** (`Examples/PlacableSenderEquilibrium`, `equilibriumTop_of_margin`) |

Since round BJ5.1 (2026-10-07) the `00` and `10` constructions take
`[p.StaticSelectorContinuous]`, the joint continuity of `p.σ`, which was a
`Params` field before.

**Update (Rung 5, 2026-09-04).** The general frontier below is unchanged: no
construction is offered over arbitrary `Params`. On the placable-Sender family
(`Examples/PlacableSenderFamilyF` and successors) the loop *is* closed — the
`11` equilibrium is constructed given one coefficient inequality, and the `00`
equilibrium is constructed as a genuine `RegimeEquilibrium p00`
(`Examples/PlacableSenderRegimes`, `myopicEquilibriumTop`), through the
selector-identity bridge `Theory/Mechanism/ZeroDiscountSelector` under strict
stage concavity; the two mixed readings and their four-cell composition
followed (`target_only_regime_generalF`, `sender_only_regime_generalF`,
`four_cell_generalF` — headline rows 37, 40, 39; table updated 2026-09-11).
Read "nothing" in this table as "nothing over arbitrary `Params`": the family
constructions do not discharge generic existence, and the numerical cycling
recorded below is evidence about one iteration at one economy, not an
obstruction theorem (Rule 9D).

**Correction (2026-08-31).** An earlier version of this table read
"**unconditional**" in the third column for `00` and `10`, and the
`RegimeEquilibrium` docstring below claimed that
`FeedbackStackelbergEquilibriumTop` "is inhabited by the constructions above"
for those two regimes. That was false for *both* of them, and the third column
has been rewritten to say what is actually built. Neither construction produces
a `FeedbackStackelbergEquilibriumTop`: `00` produces a `MyopicFeedbackEquilibrium`,
a different and weaker structure, and `10` produces a Target value and Target
policy only. See the `RegimeEquilibrium` docstring for the outstanding
obligations.

The reason is visible in the middle column. When the Sender is myopic its
response is the *static* best reply `p.σ`, which is a primitive of the model.
Its joint continuity was a `Params` field until round BJ5.1 (2026-10-07) and is
now the instance `[p.StaticSelectorContinuous]`, which the regime-`00` and
regime-`10` constructions take. The Target then faces a single-agent dynamic
programme against a fixed, exogenous response — an ordinary contraction, whose
fixed point `targetDynValue` this development already constructs from primitives
(Rule 15), with a maximiser supplied by compactness.

When the Sender is forward-looking that fails, and not for want of technique.
The Sender's response reads `V_S`, which is the value of following the Target's
policy `α`, which is chosen against the Sender's response. The circle closes and
there is no single contraction to run. That is the same circularity the coupled
route has always faced, and the numerical evidence of 2026-08-29
(`docs/WITNESS-PROPERTY-MAP.md`) says it bites here: at a genuine-conflict
economy the two Sender-forward regimes cycle under best-response iteration,
while the two Sender-myopic regimes converge in 2 and 109 iterations. **Damping
and impatience both fail to fix it**, and the coefficient driving the cycle is
the sanction–state complementarity — the very feature that gives the Sender a
reason to look ahead.

## What this means for the programme

`suggestions/32` asks for four direct effects and two spillovers. Read against
the table above, they are not equally available:

* `d¹⁰ ≥ d⁰⁰` — the **Target channel**, comparing two regimes that both
  provably exist. This comparison can in principle be unconditional, and is
  therefore where the mechanism programme should start.
* `R⁰¹ ≥ R⁰⁰` and `R¹¹ ≥ R¹⁰` — the **Sender channel**. Every one of these
  touches a regime with no construction, so any theorem about them is
  conditional on a supplied equilibrium until that changes.

Per Rule 9D, none of this is a proof that the Sender-forward regimes fail to
exist. It says they are not *constructed*, that the obvious route does not
apply, and that the numerical evidence is discouraging. A theorem consuming them
must be named conditional (Rule 15), and this file names them so.
-/

import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Mechanism.ContinuationProfile

namespace Sanctions
namespace AbstractGame
namespace Params

open Set Sanctions.Mechanism
open BoundedContinuousFunction

variable (p : Params)

/-! ## Regime `10` — the Target looks ahead, the Sender does not

The Sender's myopic response is `p.σ`, a `Params` field. Its joint continuity
was the `Params` field `σ_continuous` until round BJ5.1 (2026-10-07) and is now
the instance `[p.StaticSelectorContinuous]`, which every declaration below
takes: the regime-`10` value is a Banach fixed point of an operator that
preserves continuity only when `σ` is continuous. Everything below is that
observation applied to machinery that already exists. General in `F`. -/

/-- **The Target's forward-looking value against a myopic Sender.**

`targetDynValue` at the *static* response — a Banach fixed point constructed
from primitives, not a consumed hypothesis. This is regime `10`'s Target value,
and it exists at every `Params` whose static selector is continuous
(`[p.StaticSelectorContinuous]`, a `Params` field until round BJ5.1). General
in `F`. -/
noncomputable def regime10TargetValue [p.StaticSelectorContinuous] : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  p.targetDynValue p.σ p.σ_continuous

/-- The regime-`10` Target value solves its Bellman equation. Immediate from the
construction; stated so the regime can be recognised without unfolding. -/
theorem regime10TargetValue_bellman [p.StaticSelectorContinuous] (x : ↥(Sanctions.S : Set ℝ)) :
    p.regime10TargetValue x =
      sSup ((fun a => p.U_T x.val a (p.σ x.val a)
              + p.β_T * p.regime10TargetValue
                  (Sanctions.clipS' (p.F x.val (p.σ x.val a)))) ''
              Sanctions.I) :=
  p.targetDynValue_bellman_eq p.σ p.σ_continuous x

/-- **The regime-`10` Target policy exists at every state.**

Weierstrass on a compact action set, against a continuous objective — the exact
argument `myopic_stage_argmax_exists` runs for regime `00`, with the dynamic
integrand in place of the stage one. No selection principle beyond
`Classical.choose` is needed, and no uniqueness is assumed. -/
theorem regime10_argmax_exists [p.StaticSelectorContinuous] (x : ℝ) :
    ∃ a ∈ Sanctions.I,
      IsMaxOn (fun a' => p.targetDynIntegrand p.σ p.regime10TargetValue x a')
        Sanctions.I a := by
  apply IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by simp⟩
  exact (p.targetDynIntegrand_continuous_in_a p.σ p.regime10TargetValue
    p.σ_continuous x).continuousOn

/-- **A canonical regime-`10` Target policy**, chosen state by state. -/
noncomputable def regime10Policy [p.StaticSelectorContinuous] : ℝ → ℝ :=
  fun x => Classical.choose (p.regime10_argmax_exists x)

theorem regime10Policy_mem [p.StaticSelectorContinuous] (x : ℝ) :
    p.regime10Policy x ∈ Sanctions.I :=
  (Classical.choose_spec (p.regime10_argmax_exists x)).1

/-- **Rule 1.** The regime-`10` policy is an argmax of the Target's complete
forward-looking objective, not a chosen constant. -/
theorem regime10Policy_isMaxOn [p.StaticSelectorContinuous] (x : ℝ) :
    IsMaxOn (fun a' => p.targetDynIntegrand p.σ p.regime10TargetValue x a')
      Sanctions.I (p.regime10Policy x) :=
  (Classical.choose_spec (p.regime10_argmax_exists x)).2

/-- **The regime-`10` Target programme is solvable at every economy with a
continuous static selector.**

Value constructed by contraction, policy by compactness, both from primitives
(Rule 15) — so this is a single-agent result with no equilibrium hypothesis
(its one condition is the static-selector continuity instance), and it is the
strongest thing the Sender-myopic column currently supports. General in `F`.
Since round BJ5.1 (2026-10-07) it takes `[p.StaticSelectorContinuous]`, the
former `Params` field `σ_continuous`; the statement is otherwise unchanged.

**What it is not (corrected 2026-08-31).** This was previously named
`regime10_exists` and read as regime-`10` *equilibrium* existence. It is not.
What is constructed is a Target Bellman value and a statewise Target maximizer
**against the primitive static selector `p.σ`**. A
`FeedbackStackelbergEquilibriumTop` additionally requires a Sender value `V_S`,
the Sender Bellman fixed-point condition, continuity of the Target policy
(`hα`), and agreement between `p.σ` and `σ_dyn_top`. None of the four is
supplied here, and `regime10Policy` is a pointwise `Classical.choose`, so `hα`
in particular is not available. -/
theorem regime10_targetProgram_exists [p.StaticSelectorContinuous] :
    ∃ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ),
      (∀ x : ↥(Sanctions.S : Set ℝ), V x =
        sSup ((fun a => p.U_T x.val a (p.σ x.val a)
                + p.β_T * V (Sanctions.clipS' (p.F x.val (p.σ x.val a)))) ''
                Sanctions.I))
      ∧ (∀ x, α x ∈ Sanctions.I)
      ∧ (∀ x, IsMaxOn (fun a' => p.targetDynIntegrand p.σ V x a')
                Sanctions.I (α x)) :=
  ⟨p.regime10TargetValue, p.regime10Policy,
    p.regime10TargetValue_bellman, p.regime10Policy_mem, p.regime10Policy_isMaxOn⟩

/-! ## The Sender-forward half

No construction is offered for regimes `01` and `11`, and the naming below says
so rather than hiding it behind a definition.

What blocks it is not a missing lemma. The Sender's dynamic response
`σ_dyn V_S` reads `V_S`; `V_S` is the value of the Target's policy `α` against
that response; `α` is chosen against the response. There is no single operator
to contract, and the joint operator is not isotone — which is precisely why the
existing general-`F` existence result
(`Theory/Equilibrium/BasinCornerExistence.lean`) buys its equilibrium by
*pinning the Target at a corner*, severing the loop rather than closing it.

A theorem about these regimes must therefore either consume a supplied
equilibrium — and be named conditional, per Rule 15 — or restrict to a class
where the loop is severed. Both are legitimate; neither may be presented as a
construction. -/

/-- **The conditional form.** A regime-`c` equilibrium is
`FeedbackStackelbergEquilibriumTop` read at the profile view — no new structure
is needed (see `Theory/Mechanism/ContinuationProfile.lean`).

**Inhabitation over arbitrary `Params` is open at every one of the four
profiles (corrected 2026-08-31; on the placable-Sender family `p00` and `p11`
are inhabited since Rung 5, see the update above).** An earlier version of this docstring said the type is inhabited
for `c ∈ {p00, p10}` "by the constructions above." It is not, and the error was
in both halves:

* `p00` — `myopicFeedbackEquilibrium_exists_of_continuity` inhabits
  `MyopicFeedbackEquilibrium`, which is a *different and weaker* structure. It
  carries no Sender fixed-point condition, so it is not this type.
* `p10` — `regime10_targetProgram_exists` constructs a Target value and Target
  policy against `p.σ`, and neither a Sender value, a Sender fixed point, nor
  `Continuous α`.
* `p01`, `p11` — nothing is constructed, for the structural reason given above.

So every theorem quantifying over `RegimeEquilibrium` is conditional on being
supplied one, at all four profiles, and must be named and read that way
(Rule 15). Closing the `p10` case needs a selector-identity bridge
(`p.σ = σ_dyn_top V_S` on feasible pairs — note that `β_S = 0` does *not* give
this when the static argmax is not a singleton) plus Target-policy regularity.
The bridge now exists under a unique stage argmax
(`σ_dyn_top_eq_σ_of_βS_zero`, `Theory/Mechanism/ZeroDiscountSelector`); the
regularity is open, and neither may be assumed without a Rule-3 stop. -/
abbrev RegimeEquilibrium (c : ContinuationProfile) : Type :=
  (p.withProfile c).FeedbackStackelbergEquilibriumTop

end Params
end AbstractGame
end Sanctions
