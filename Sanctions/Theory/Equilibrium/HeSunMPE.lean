/-
Sanctions/Theory/Equilibrium/HeSunMPE.lean

**Static-Sender stationary profile (He-Sun-style construction).**

Builds, at the abstract layer, a stationary profile that pairs:

* the Sender's stage-game (static / myopic) argmax response `σ`, and
* a Target stationary policy `α` that is Bellman-optimal against `σ`.

For the *myopic Sender setting* (`β_S = 0`, or equivalently any
setting where the Sender ignores future continuations and the
equilibrium Sender response coincides with the stage argmax), this
profile is a genuine **coupled stationary Markov perfect equilibrium**:
both players play best responses against each other.

For `β_S > 0` with a forward-looking Sender, the equilibrium Sender
response is the *dynamic* argmax `σ_dyn` (see
`Theory/Equilibrium/JointMPE.lean`), and the static profile produced here
is the myopic projection — *not* a joint MPE in the literal sense.
The structure name `StaticSenderStationaryProfile` reflects this:
it is unconditionally a profile, and it is an MPE exactly when the
Sender's true equilibrium response is the stage argmax.

**Rule-1 compliance.** Every theorem uses the equilibrium-derived
Sender stage response (via `p.σ_isMaxOn_U_S`) and the optimization-
derived Target policy (existence via `verification_target_exists`).

**Rule-3 compliance.** No new external hypothesis.

**Round BJ5.1 (2026-10-07).** Everything here is built on `V_T`, the Target's
value against the static Sender selector, or packages that selector as a
continuous response, so the profile structure and all four declarations take
`[p.StaticSelectorContinuous]` (joint continuity of `σ`, formerly the `Params`
field `σ_continuous`). General in `F`. The condition moved from every `Params`
to these binders.

**Rule-5 compliance.** Parametric. No witness-specific content.

**Audit #11 closure (abstract layer).** Provides
`staticSenderResponse` as a concrete instance of
`Sanctions.JointMPE.SenderResponse` populated by the abstract σ +
σ_isMaxOn_U_S certification.
-/

import Sanctions.Theory.Bellman.Verification
import Sanctions.Foundations.HeSunMPE
import Sanctions.Theory.Bridges.SenderResponse

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame

/-- **Static-Sender stationary profile for the abstract game.** Bundles:

* `α` — Target's stationary policy on `↥S` with values in `I`;
* `hα_optimal_target` — Target's Bellman optimality at `p.V_T`
  against the static Sender response σ;
* `hσ_stage_best_response` — σ is the Sender's stage-game argmax on
  `I` for every `(x, a)` (abstracted as `p.σ_isMaxOn_U_S`).

The profile is a *genuine* coupled stationary Markov perfect
equilibrium exactly when the Sender's equilibrium response is the
stage argmax (e.g. `β_S = 0`). For `β_S > 0` with a forward-looking
Sender, the equilibrium Sender response is `σ_dyn` (see
`Theory/Equilibrium/JointMPE.lean`), and this structure is the myopic
projection rather than the joint MPE. General in `F`. It takes
`[p.StaticSelectorContinuous]` (round BJ5.1, 2026-10-07: formerly the `Params`
field `σ_continuous`) because its optimality field is stated at `p.V_T`, the
Target's value against the static selector, which is built from that
continuity. -/
structure StaticSenderStationaryProfile (p : Sanctions.AbstractGame.Params)
    [p.StaticSelectorContinuous] where
  α : ↥(Sanctions.S : Set ℝ) → ℝ
  hα_in_I : ∀ x : ↥(Sanctions.S : Set ℝ), α x ∈ Sanctions.I
  hα_optimal_target :
    ∀ x : ↥(Sanctions.S : Set ℝ),
      p.U_T x.val (α x) (p.σ x.val (α x))
        + p.β_T * p.V_T (Sanctions.clipS'
            (p.F x.val (p.σ x.val (α x))))
        = p.V_T x
  hσ_stage_best_response :
    ∀ (x a : ℝ),
      IsMaxOn (fun s => p.U_S x a s) (Set.Icc (0 : ℝ) 1) (p.σ x a)

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Target stationary optimal policy against the abstract σ.**
Existence of the Target's stationary optimal policy. -/
theorem target_optimal_policy_against_static_σ [p.StaticSelectorContinuous] :
    ∃ α : ↥(Sanctions.S : Set ℝ) → ℝ,
      (∀ x : ↥(Sanctions.S : Set ℝ), α x ∈ Sanctions.I) ∧
      ∀ x : ↥(Sanctions.S : Set ℝ),
        p.U_T x.val (α x) (p.σ x.val (α x))
          + p.β_T * p.V_T (Sanctions.clipS'
              (p.F x.val (p.σ x.val (α x))))
          = p.V_T x :=
  Sanctions.HeSun.stationary_policy_exists
    (S := (Sanctions.S : Set ℝ))
    (A := (Sanctions.I : Set ℝ))
    (J := fun x a => p.U_T x.val a (p.σ x.val a)
                    + p.β_T * p.V_T (Sanctions.clipS'
                        (p.F x.val (p.σ x.val a))))
    (V := fun x => p.V_T x)
    p.verification_target_exists

/-- **Existence of the static-Sender stationary profile.** For any
`AbstractGame.Params`, the profile `(α, σ)` exists where α is Target-
Bellman-optimal at `V_T` and σ is the Sender stage argmax (the latter
discharged via the structural `σ_isMaxOn_U_S` hypothesis of `Params`).
This profile is a coupled stationary MPE iff the Sender's equilibrium
response coincides with the stage argmax (e.g. `β_S = 0`); for
`β_S > 0` with a forward-looking Sender, the genuine joint MPE uses
`σ_dyn` and is constructed in `Theory/Equilibrium/JointMPE.lean` under
explicit Lipschitz hypotheses. -/
noncomputable def staticSenderStationaryProfile_exists [p.StaticSelectorContinuous] :
    StaticSenderStationaryProfile p :=
  let h := p.target_optimal_policy_against_static_σ
  { α := h.choose
    hα_in_I := h.choose_spec.1
    hα_optimal_target := h.choose_spec.2
    hσ_stage_best_response := p.σ_isMaxOn_U_S }

/-- **Abstract concrete `SenderResponse` instance** (audit #11 closure
at the abstract layer). The myopic Sender response σ from
`AbstractGame.Params`, lifted to the `JointMPE.SenderResponse`
interface. Ignores `V_S` (forward-looking continuation absent in the
myopic regime). General in `F`. Takes `[p.StaticSelectorContinuous]` (round
BJ5.1): the interface asks for a jointly continuous response, and the static
selector is continuous exactly under that instance (formerly a `Params`
field). -/
noncomputable def staticSenderResponse [p.StaticSelectorContinuous] :
    Sanctions.JointMPE.SenderResponse where
  σ _V_S x a := p.σ x a
  σ_mem _V_S x a := p.σ_mem x a
  σ_continuous _V_S := p.σ_continuous

/-- **Argmax certification of the abstract `staticSenderResponse`.**
The response packaged in `staticSenderResponse` IS the Sender stage
argmax — discharged via `p.σ_isMaxOn_U_S`. -/
theorem staticSenderResponse_isMaxOn [p.StaticSelectorContinuous]
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsMaxOn (fun s => p.U_S x a s) (Set.Icc (0 : ℝ) 1)
      (p.staticSenderResponse.σ V_S x a) :=
  p.σ_isMaxOn_U_S x a

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
