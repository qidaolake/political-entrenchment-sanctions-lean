/-
Sanctions/Theory/Shocked/ShockedBellman.lean

**The shock-smoothed Sender Bellman operator is a `β_S`-contraction.**

The atomless purification shock (`ShockedParams.smear`) enters the Sender Bellman
operator at exactly one point: the continuation value `V` is replaced by its
shock-smoothed version `smear V`. Hence the shocked operator is literally the
deterministic operator pre-composed with `smear`:

  `bellmanS_shock sp α V  =  bellmanS_BCF (sp.toParams) α (smear V)`.

Because `smear` is sup-norm **nonexpansive** (`smear_nonexpansive`, the `∫κ = 1`
property), the deterministic `β_S`-contraction (`bellmanS_BCF_pointwise_dist`)
carries through verbatim: the shocked operator is still a `β_S`-contraction, so
its Banach fixed point `V_S_shock` exists. This is the "contraction survives the
shock" half — clean and unconditional on any new regularity (it uses only
`smear_nonexpansive`). The *regularizing* property `smear_lipschitz` is used
later (the slaved/policy-channel argument), not here.

**Rule-15.** The fixed point is *constructed* by applying the in-repo Banach
engine (`ContractingWith.fixedPoint`) to a proved contraction — not consumed as
a hypothesis.
-/

import Sanctions.Postulates.ShockedParams
import Sanctions.Theory.Bellman.BellmanS

namespace Sanctions
namespace AbstractGame
namespace ShockedParams

open scoped NNReal
open BoundedContinuousFunction

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- The **shock-smoothed Sender Bellman operator**: the deterministic Sender
Bellman operator applied to the shock-smoothed continuation `smear V`. -/
noncomputable def bellmanS_shock
    (α : ℝ → ℝ) (hα : Continuous α) (V : SBCF) : SBCF :=
  sp.toParams.bellmanS_BCF α hα (sp.smear V)

/-- **The shocked operator is a `β_S`-contraction, pointwise.** Continuation
channel (β_S, from `bellmanS_BCF_pointwise_dist`) composed with the nonexpansive
smoothing (`smear_nonexpansive`). -/
theorem bellmanS_shock_pointwise_dist
    {α : ℝ → ℝ} (hα : Continuous α) (V W : SBCF)
    (x : ↥(Sanctions.S : Set ℝ)) :
    dist (sp.bellmanS_shock α hα V x) (sp.bellmanS_shock α hα W x)
      ≤ sp.toParams.β_S * dist V W := by
  have h1 : dist (sp.bellmanS_shock α hα V x) (sp.bellmanS_shock α hα W x)
      ≤ sp.toParams.β_S * dist (sp.smear V) (sp.smear W) :=
    sp.toParams.bellmanS_BCF_pointwise_dist hα (sp.smear V) (sp.smear W) x
  have h2 : sp.toParams.β_S * dist (sp.smear V) (sp.smear W)
      ≤ sp.toParams.β_S * dist V W :=
    mul_le_mul_of_nonneg_left (sp.smear_nonexpansive V W) sp.toParams.β_S_mem.1
  exact le_trans h1 h2

/-- The shocked operator is `LipschitzWith β_S`. -/
theorem bellmanS_shock_lipschitz
    {α : ℝ → ℝ} (hα : Continuous α) :
    LipschitzWith sp.toParams.β_S_nnreal (sp.bellmanS_shock α hα) := by
  apply Sanctions.lipschitzWith_of_pointwise_dist_le
  intro V W x
  exact sp.bellmanS_shock_pointwise_dist hα V W x

/-- The shocked operator is `ContractingWith β_S`. -/
theorem bellmanS_shock_contracting
    {α : ℝ → ℝ} (hα : Continuous α) :
    ContractingWith sp.toParams.β_S_nnreal (sp.bellmanS_shock α hα) :=
  ⟨sp.toParams.β_S_nnreal_lt_one, sp.bellmanS_shock_lipschitz hα⟩

/-- **The shocked Sender value function** at a fixed Target policy `α`:
the Banach fixed point of the shocked operator (constructed, Rule-15). -/
noncomputable def V_S_shock (α : ℝ → ℝ) (hα : Continuous α) : SBCF :=
  ContractingWith.fixedPoint (sp.bellmanS_shock α hα) (sp.bellmanS_shock_contracting hα)

/-- `V_S_shock` is a fixed point of the shocked operator. -/
theorem V_S_shock_isFixedPoint
    {α : ℝ → ℝ} (hα : Continuous α) :
    sp.bellmanS_shock α hα (sp.V_S_shock α hα) = sp.V_S_shock α hα := by
  unfold V_S_shock
  exact ContractingWith.fixedPoint_isFixedPt _

end ShockedParams
end AbstractGame
end Sanctions
