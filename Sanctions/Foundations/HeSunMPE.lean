/-
Sanctions/Foundations/HeSunMPE.lean

**Stationary single-player policy extraction (Skolemization step).**

⚠ **Scope and limitations** (correcting an earlier overstatement, per
audit feedback):

He-Sun (JET 2017) Theorem 1 is about the existence of a *stationary
Markov perfect equilibrium* in a stochastic game — i.e., a strategy
profile in which **each player's strategy is a best response to the
others**. The proof is non-trivial: it uses Dynkin-Evstigneev's
measurable-selection theorem on conditional expectations of
correspondences, applied to a *correspondence on policy profiles* whose
fixed point delivers the coupled equilibrium.

**This module does NOT prove He-Sun Theorem 1.** What it provides is a
Skolemization step:

> Given a single agent's per-state ∃-argmax statement on a compact
> action set, extract a global stationary policy via classical choice.

This is one *building block* used inside a full equilibrium-existence
argument (the existence side, after the per-state argmax has been
established via compactness and continuity of the per-stage objective).
The substantive content of He-Sun's theorem — the coupled fixed-point
argument and the measurable-selection machinery handling stochastic
kernels — is **not** in this module.

In particular: the application of this theorem at the abstract layer
(`Sanctions.Theory.Equilibrium.HeSunMPE`) constructs the **Target's**
optimal stationary policy *against the static Sender response `σ`*.
That downstream module relies on the structural hypothesis
`p.σ_isMaxOn_U_S` (carried by `AbstractGame.Params`) to certify that
σ IS the Sender's stage-game argmax on `[0, 1]`. The combination
(Target policy α) + (Sender stage best-response σ) is packaged as the
`StaticSenderStationaryProfile` structure — a genuine coupled
stationary MPE iff the Sender's equilibrium response coincides with
the stage argmax (e.g. `β_S = 0`); otherwise it is the myopic
projection.

For the forward-looking joint MPE (with `β_S > 0` and equilibrium
Sender response `σ_dyn` rather than σ), the conditional row-Lipschitz
template in `Sanctions.Theory.Equilibrium.JointMPE` is the existence
theorem. This module *does not* handle that case.

The naming `HeSunMPE` is retained because the module is cited from the
He-Sun paper, but the content it formalizes is strictly weaker than
He-Sun's Theorem 1.
-/

import Sanctions.Foundations.Basic

noncomputable section

namespace Sanctions
namespace HeSun

/-- **Stationary single-player policy extraction (Skolemization).**

Given a state space `↥S`, an action set `A ⊆ ℝ`, a per-stage objective
`J : ↥S → ℝ → ℝ`, and a value function `V : ↥S → ℝ`, suppose at every
state `x : ↥S` the maximum of `J(x, ·)` over `A` is attained and equals
`V x` — i.e., the per-state argmax exists:

  `∀ x : ↥S, ∃ a ∈ A, J x a = V x`.

Then a *global* stationary policy `α : ↥S → ℝ` exists with values in `A`
satisfying `J x (α x) = V x` at every state.

The proof is `Classical.choose` (via mathlib's `choose` tactic). This
is *one ingredient* of equilibrium-existence arguments in dynamic
programming, but **it is not** He-Sun's Theorem 1 (which is about
coupled MPE existence via Dynkin-Evstigneev measurable selection on a
correspondence over policy profiles). The hard work — establishing the
per-state ∃-argmax `h_per_state` from primitive compactness, continuity,
and Bellman fixed-point arguments — lives elsewhere (e.g.
`Sanctions.Theory.Bellman.BellmanT` + `verification_target_exists` in
`Sanctions.Theory.Bellman.Verification`). This theorem just packages
the final Skolemization step. -/
theorem stationary_policy_exists
    {S : Set ℝ} (A : Set ℝ)
    (J : ↥S → ℝ → ℝ) (V : ↥S → ℝ)
    (h_per_state : ∀ x : ↥S, ∃ a ∈ A, J x a = V x) :
    ∃ α : ↥S → ℝ,
      (∀ x : ↥S, α x ∈ A) ∧
      (∀ x : ↥S, J x (α x) = V x) := by
  choose α hα_in hα_eq using h_per_state
  exact ⟨α, hα_in, hα_eq⟩

/-- **Variant: stationary-policy extraction with bundled subtype.**
Same as `stationary_policy_exists`, but the policy `α` is built into a
subtype `↥A`. Useful when the action set has a fixed witness term. -/
theorem stationary_policy_exists_subtype
    {S A : Set ℝ}
    (J : ↥S → ℝ → ℝ) (V : ↥S → ℝ)
    (h_per_state : ∀ x : ↥S, ∃ a : ↥A, J x a.val = V x) :
    ∃ α : ↥S → ↥A, ∀ x : ↥S, J x (α x).val = V x := by
  choose α hα_eq using h_per_state
  exact ⟨α, hα_eq⟩

end HeSun
end Sanctions

end
