/-
Sanctions/Theory/Shocked/ShockedSlavedExistence.lean

**Banach slaved-existence bridge — the shocked (purified) interior route.**

This is the Banach analogue of `SlavedExistence.feedbackStackelbergTop_of_slaved_orderHom_decode`.
The deterministic route was forced onto Knaster–Tarski (an abstract complete
*lattice* carrier `L`) because the Sender value space `SBCF = ↥S →ᵇ ℝ` is only a
*lattice*, not a complete lattice, and because the deterministic slaved operator
is not a contraction (the selector is Hölder-½ in `V_S`). Under the atomless
purification shock (`ShockedParams`) the slaved operator becomes a genuine
**contraction** in sup-norm — the shock convolves the continuation, upgrading the
Sender/leader argmaxes from Hölder-½ to Lipschitz in `V_S`. Then existence is
**plain Banach** on `SBCF` directly (a complete metric space), with no abstract
carrier and no monotonicity:

  `Φ` a contraction  ⟹  `∃ V_S, Φ V_S = V_S`  (Banach)  ⟹  equilibrium.

This module delivers the bridge: it *consumes* the slaved operator as a
**contraction** `ContractingWith K Φ` (this is what the shock supplies; the
from-shock discharge of the contraction — i.e. that the slaved leader argmax is
Lipschitz in `V_S` — is the remaining analytic step, isolated as the contraction
hypothesis exactly as the Tarski bridge isolated monotonicity), constructs the
Sender fixed point by Banach, and reconstructs the `FeedbackStackelbergEquilibriumTop`
fields verbatim from the deterministic decode bridge.

**Rule-15.** The Sender fixed point is *constructed* by the in-repo Banach engine
`ContractingWith.fixedPoint`, not consumed. **Rule-1.** Every realized strategic
object is equilibrium-derived (Sender Bellman fixed point, slaved Banach Target
value `V_T_dyn`, greatest selector, leader top-argmax). **Rule-3.** The bridge is
parametric in `(p, Φ, …)`; the shock primitive lives in `ShockedParams`, the
contraction is a theorem parameter — no new field is added here.
-/

import Sanctions.Theory.Equilibrium.SlavedExistence
import Sanctions.Theory.Shocked.ShockedBellman

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Banach slaved-existence bridge.**

Given a slaved Sender operator `Φ : SBCF → SBCF` that is a **contraction**
(`ContractingWith K Φ`, `K < 1` — this is what the atomless shock buys), a
continuous feasible leader policy `α`, continuity `hσc` of the greatest Sender
selector at any fixed point, the **slaved consistency at the fixed point**
(`h_fix_consistency`: a fixed point of `Φ` equals the Sender Bellman image under
`α`), and leader top-optimality at the fixed point (`h_top_opt`), there exists a
`FeedbackStackelbergEquilibriumTop`.

The Sender fixed point is constructed by Banach (`ContractingWith.fixedPoint`);
the contraction, consistency, leader continuity/feasibility/top-optimality, and
selector continuity are consumed. This is the exact Banach mirror of the Tarski
`feedbackStackelbergTop_of_slaved_orderHom_decode` (with `decode = id`, the
concrete `SBCF` carrier). -/
theorem feedbackStackelbergTop_of_slaved_contraction
    {K : ℝ≥0} (Φ : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
    (hΦ : ContractingWith K Φ)
    (α : ℝ → ℝ) (hα : Continuous α)
    (hα_mem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, Φ V = V →
      Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top V xa.1 xa.2))
    (h_fix_consistency : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ, Φ V = V →
      V = p.bellmanS_BCF α hα V)
    (h_top_opt : ∀ (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (hV : Φ V = V),
      ∀ x ∈ Sanctions.S, IsMaxOn (fun a => p.joint_T_top_integrand
        (p.V_T_dyn V (hσc V hV)) V x a) Sanctions.I (α x)) :
    Nonempty p.FeedbackStackelbergEquilibriumTop := by
  -- Banach: the slaved Sender operator has a fixed point on `SBCF`.
  set V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := ContractingWith.fixedPoint Φ hΦ with hVdef
  have hfix : Φ V = V := ContractingWith.fixedPoint_isFixedPt hΦ
  -- The follower fixed-point condition from slaved consistency.
  have hVS_fix : V = p.bellmanS_BCF α hα V := h_fix_consistency V hfix
  -- Package the equilibrium with the slaved Target value `V_T_dyn`.
  refine ⟨{
    V_T := p.V_T_dyn V (hσc V hfix)
    V_S := V
    α := α
    hα := hα
    α_mem := hα_mem
    V_S_fix := hVS_fix
    V_T_fix_top := p.V_T_dyn_bellman_eq V (hσc V hfix)
    α_opt_top := h_top_opt V hfix }⟩

end Params

/-! ## Scope: the generic bridge is for the deterministic equilibrium object

The bridge above is over a generic contraction `Φ` whose fixed point satisfies
the **deterministic** Sender Bellman equation `V = bellmanS_BCF α V` — exactly the
`FeedbackStackelbergEquilibriumTop.V_S_fix` field. Its non-vacuous use is the
*corner* equilibrium with `Φ := bellmanS_BCF (fun _ => c)` (a deterministic
contraction whose fixed point satisfies that equation): it gives a **Banach**
construction of the corner equilibrium, replacing the Tarski / `consume-h_corner`
route.

It is **not** directly applicable to the shocked operator, and this is a genuine
modeling point (verified, not glossed): the shocked Sender fixed point satisfies
the **shocked** equation `V = bellmanS_shock α V = bellmanS_BCF α (smear V)`, which
is *not* the deterministic `V_S_fix`. The atomless shock changes the *game* (both
players' continuations are smeared), so the shocked equilibrium is an equilibrium
of the *shocked* game and requires its **own** structure
`ShockedFeedbackStackelbergEquilibriumTop` with the shocked Bellman equations
(`V_S = bellmanS_shock α V_S`, and a shocked Target side `σ_dyn_top` / `V_T_dyn` /
`joint_T_top_integrand` built on `smear`). That shocked-equilibrium object — and
the discharge that the slaved leader argmax is Lipschitz in `V_S` under
`smear_lipschitz`, which makes the *slaved* (policy-varying) shocked operator a
contraction — is the remaining wiring. What is machine-checked here and in
`ShockedBellman` is the load-bearing mechanism: **the shock makes the Sender
operator a `β_S`-contraction** (`bellmanS_shock_contracting`), so its value
`V_S_shock` is a *constructed* Banach fixed point, and the Banach engine is the
correct existence route under the shock. -/

end AbstractGame

end -- noncomputable section

end Sanctions
