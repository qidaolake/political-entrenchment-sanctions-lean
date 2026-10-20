/-
Sanctions/Examples/MyopicPolicyNotAntitone.lean

**The baseline does not fix the sign of the Target's state dependence.**

Ordering the two regimes' *state paths* needs the realised sanction rule
`R(x) = σ(x, α(x))` to be non-decreasing in the state. `TwoSidedForwardLooking`
§11 and §16 take that as a hypothesis, and
`dynamicTopRealizedRule_mono_of_singleCrossingOn` discharges it from a single
crossing condition on the *composite* — the Sender's objective with the Target's
policy already substituted in. That formulation is deliberate, and this file is
why it cannot be replaced by the more obvious one.

The tempting route is to derive monotonicity of `R` from monotonicity of the two
policies separately. It does not work. Writing the derivative informally,

    R'(x) = σ_x(x, α(x)) + σ_a(x, α(x)) · α'(x),

so the sign of `R'` depends on the Target's own state dependence `α'` through the
Sender's response to compliance `σ_a`. This model assumes `σ_a ≤ 0` throughout —
*compliance placates*, the hypothesis written `hσ_antiOn_a` at 64 sites — which
is exactly the strategic-substitutes configuration in which the second term
works against the first. The composition is then favourable when `α' ≤ 0`, a more
entrenched Target being more defiant, and indeterminate otherwise.

So the question is whether the baseline forces `α` to be non-increasing. It does
not, and the counterexample is about as simple as it could be. Give the Target
the stage payoff

    U_T x a s = -(a - x)^2,

which does not mention the sanction at all, so the Sender's behaviour is
irrelevant to the Target's stage problem. The myopic Target's genuine stage
argmax is then `α(x) = x`: it matches its compliance to the political state. That
policy is *strictly increasing*, and every field of the baseline holds.

**What this licenses, and what it does not** (Rule 9). It refutes a universal:
there is no theorem deriving `AntitoneOn α` from the maintained hypotheses, so
the composition route to closed-loop monotonicity is not available in general and
`hDynMono` must be assumed or discharged some other way. It does *not* exhibit an
economy in which the closed-loop rule fails to be monotone — that would need the
Sender's placation to be strong enough to overturn the direct state effect, which
is a further construction. And it says nothing about whether `α` is increasing,
decreasing, or neither in any economy of interest.

Rule 1: the policy is the stage argmax of the Target's own payoff, not a posited
rule. Rule 3: no new assumption — the surgeon replaces one payoff field and
discharges the rest from the concrete data. Rule 22: the transition is untouched,
so this says nothing about `F`.
-/
import Sanctions.Theory.LockIn.DifferentPolicyComparator

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame

/-- **A Target that wants its compliance to match the political state.**

Replaces only the Target's stage payoff by `-(a - x)^2`, which does not depend on
the sanction, so the Sender's response cannot influence the Target's stage
problem. Everything else — the transition, the Sender's payoff and response, both
discount factors — is left untouched. -/
def Params.selfMatchingTarget (p : Params) : Params :=
  { p with
    U_T := fun x a _ => -(a - x) ^ 2
    U_T_continuous := by fun_prop }

namespace Params

variable (p : Params)

@[simp] theorem selfMatchingTarget_U_T (x a s : ℝ) :
    p.selfMatchingTarget.U_T x a s = -(a - x) ^ 2 := rfl

/-- **Matching the state is the myopic Target's genuine stage argmax.**

Not a posited policy (Rule 1): `α x = x` maximises `U_T x · (σ x ·)` on `[0,1]`
because the payoff is a downward parabola centred on `x`, and `x` is feasible. -/
def selfMatchingMyopic : p.selfMatchingTarget.MyopicFeedbackEquilibrium where
  α := fun x => x
  α_mem := fun _ hx => hx
  α_opt := by
    intro x _ a _
    change -(a - x) ^ 2 ≤ -(x - x) ^ 2
    simp only [sub_self]
    nlinarith [sq_nonneg (a - x)]

@[simp] theorem selfMatchingMyopic_alpha (x : ℝ) :
    (p.selfMatchingMyopic).α x = x := rfl

/-- **The myopic compliance policy is strictly increasing here.**

The positive reading: a Target whose stage payoff rewards matching the state
complies *more* the more entrenched it is. -/
theorem selfMatchingMyopic_strictMonoOn :
    StrictMonoOn (p.selfMatchingMyopic).α Sanctions.I :=
  fun _ _ _ _ h => h

/-- **The baseline does not force the Target's policy to be non-increasing.**

The refutation this file exists for. Since `hσ_antiOn_a` — compliance placates —
is maintained throughout the development, a non-increasing `α` is what would make
the closed-loop rule monotone for free; this economy shows the baseline does not
supply it. -/
theorem selfMatchingMyopic_not_antitoneOn :
    ¬ AntitoneOn (p.selfMatchingMyopic).α Sanctions.I := by
  intro h
  have h01 := h (by constructor <;> norm_num : (0 : ℝ) ∈ Sanctions.I)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Sanctions.I) (by norm_num)
  simp only [selfMatchingMyopic_alpha] at h01
  linarith

/-- **So closed-loop monotonicity is not derivable from the maintained
hypotheses by way of the Target's policy.**

Stated as the existential it is: there is a parameter vector and a myopic
equilibrium at which the Target's policy rises in the state. Any route to
`MonotoneOn (dynamicTopRealizedRule ...)` that argues from `α` being
non-increasing must therefore assume that separately — which is why the
development discharges the closed-loop condition from a single-crossing property
of the *composite* instead, where the Target's policy is already substituted in
and the two channels are not separated. -/
theorem exists_myopic_policy_not_antitone (p₀ : Params) :
    ∃ (q : Params) (M : q.MyopicFeedbackEquilibrium),
      ¬ AntitoneOn M.α Sanctions.I :=
  ⟨p₀.selfMatchingTarget, p₀.selfMatchingMyopic,
    p₀.selfMatchingMyopic_not_antitoneOn⟩

end Params
end AbstractGame

end

end Sanctions
