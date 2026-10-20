/-
Sanctions/Theory/Shocked/HeSunShockExistence.lean

**He–Sun road, capstone: shocked corner equilibrium from a concrete kernel.**

Combines `HeSunShock` (the concrete atomless kernel `κ`, deriving the smoothing
operator and its nonexpansiveness from `∫κ = 1`) with `ShockedEquilibrium` (the
shocked-game equilibrium and its non-vacuous corner instance). The result: given
a He–Sun atomless shock kernel, the shocked-game feedback-Stackelberg **corner**
equilibrium exists, with the shock smoothing now *derived from the kernel* and
every value function *constructed* as a Banach fixed point.

This is the cleanest form of the "He–Sun road" available without formalising
He–Sun's measurable-selection theorem: the shock is a concrete economic
primitive (the transition noise density), its nonexpansiveness is machine-checked
from the kernel, and existence is the easy Banach route. Only the leader
corner-optimality is consumed conditionally (as in the deterministic corner).
-/

import Sanctions.Theory.Shocked.HeSunShock
import Sanctions.Theory.Shocked.ShockedEquilibrium

namespace Sanctions
namespace AbstractGame
namespace HeSunShockParams

open Set BoundedContinuousFunction

noncomputable section

variable (hsp : Sanctions.AbstractGame.HeSunShockParams)

/-- **He–Sun shocked corner equilibrium.** From a concrete He–Sun atomless
kernel `κ`, with a constant corner policy `α ≡ c`, continuity of the shocked
Sender selector, and leader corner-optimality against the shocked Target
integrand, the shocked-game equilibrium exists with `α ≡ c`. The shock smoothing
`smear` is the kernel-derived `smearBCF` (nonexpansiveness proved from `∫κ = 1`);
both value functions are constructed Banach fixed points. -/
theorem heSun_shocked_corner_existence
    (c : ℝ) (hc : c ∈ Sanctions.I)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      hsp.toShockedParams.toParams.σ_dyn_top
        (hsp.toShockedParams.smear
          (hsp.toShockedParams.V_S_shock (fun _ => c) continuous_const)) xa.1 xa.2))
    (h_corner_shock : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => hsp.toShockedParams.toParams.joint_T_top_integrand
        (hsp.toShockedParams.smear
          (hsp.toShockedParams.V_T_dyn_shock
            (hsp.toShockedParams.V_S_shock (fun _ => c) continuous_const) hσc))
        (hsp.toShockedParams.smear
          (hsp.toShockedParams.V_S_shock (fun _ => c) continuous_const)) x a)
        Sanctions.I c) :
    ∃ E : hsp.toShockedParams.ShockedFeedbackStackelbergEquilibriumTop,
      E.α = (fun _ => c) :=
  hsp.toShockedParams.shockedFeedbackStackelbergTop_of_constant_corner c hc hσc h_corner_shock

end -- noncomputable section
end HeSunShockParams
end AbstractGame
end Sanctions
