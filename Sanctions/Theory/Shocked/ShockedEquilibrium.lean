/-
Sanctions/Theory/Shocked/ShockedEquilibrium.lean

**The shocked-game feedback-Stackelberg equilibrium and its Bellman equations.**

The atomless purification shock (`ShockedParams`) changes the *game*: both
players' continuations are smeared, so the equilibrium is an equilibrium of the
*shocked* game, with **shocked Bellman equations** that carry `smear`. This module
builds that object, reusing the deterministic machinery through one structural
fact:

> the shock is a continuation **pre-smoothing**, so every shocked object is the
> deterministic object evaluated at `smear V` instead of `V`.

Concretely:
* shocked Sender Bellman fixed point `V_S = bellmanS_shock α V_S`
  (`= bellmanS_BCF α (smear V_S)`, from `ShockedBellman`);
* shocked Sender response = `σ_dyn_top (smear V_S)` (the deterministic greatest
  selector at the smeared value);
* shocked Target integrand = `joint_T_top_integrand (smear V_T) (smear V_S)` (the
  deterministic Target integrand at the smeared values);
* shocked Target value `V_T_dyn_shock` = Banach fixed point of the **shocked
  Target Bellman operator** `targetDynBCF ρ (smear V_T)`, a `β_T`-contraction by
  exactly the Sender-side argument (smoothing is nonexpansive).

The shocked equilibrium structure `ShockedFeedbackStackelbergEquilibriumTop`
records the two shocked Bellman fixed-point conditions plus leader optimality. A
**non-vacuous corner instance** is constructed (`…_of_constant_corner`),
mirroring `BasinCornerExistence.feedbackStackelbergTop_of_constant_corner_optimal`:
the only *constructed* objects are the two Banach fixed points `V_S_shock` and
`V_T_dyn_shock` (Rule-15); leader corner-optimality against the shocked integrand
is consumed conditionally.

**Rule-1.** Every realized strategic object is equilibrium-derived. **Rule-3.**
The shock primitive lives in `ShockedParams`; no new field is added here.
**Rule-9/15.** The structure is inhabited by the corner constructor (non-vacuous),
and the fixed points are constructed, not assumed.
-/

import Sanctions.Theory.Shocked.ShockedBellman
import Sanctions.Theory.Equilibrium.BasinCornerExistence

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-! ## The shocked Target Bellman operator and value -/

/-- **Shocked Target Bellman operator** at a continuous Sender selector `ρ`:
the deterministic Target Bellman operator applied to the smeared continuation. -/
noncomputable def targetDynBCF_shock
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  sp.toParams.targetDynBCF ρ hρc (sp.smear V_T)

/-- The shocked Target operator is a `β_T`-contraction, pointwise (the smoothing
is nonexpansive, so the deterministic `β_T`-contraction carries through). -/
theorem targetDynBCF_shock_pointwise_dist
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) :
    dist (sp.targetDynBCF_shock ρ hρc V x) (sp.targetDynBCF_shock ρ hρc W x)
      ≤ sp.toParams.β_T * dist V W := by
  have h1 : dist (sp.targetDynBCF_shock ρ hρc V x) (sp.targetDynBCF_shock ρ hρc W x)
      ≤ sp.toParams.β_T * dist (sp.smear V) (sp.smear W) :=
    sp.toParams.targetDynBCF_pointwise_dist ρ hρc (sp.smear V) (sp.smear W) x
  exact le_trans h1 (mul_le_mul_of_nonneg_left (sp.smear_nonexpansive V W) sp.toParams.β_T_mem.1)

/-- **Shocked Target value** at Sender selector `ρ`: the Banach fixed point of the
shocked Target Bellman operator (constructed, Rule-15). -/
noncomputable def targetDynValue_shock
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  ContractingWith.fixedPoint (sp.targetDynBCF_shock ρ hρc) (by
    refine ⟨sp.toParams.β_T_nnreal_lt_one, ?_⟩
    apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := sp.targetDynBCF_shock_pointwise_dist ρ hρc V W x
    convert h using 2)

theorem targetDynValue_shock_isFixedPoint
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) :
    sp.targetDynBCF_shock ρ hρc (sp.targetDynValue_shock ρ hρc)
      = sp.targetDynValue_shock ρ hρc := by
  unfold targetDynValue_shock
  exact ContractingWith.fixedPoint_isFixedPt _

/-- **Shocked Target Bellman equation** in the `U_T + β_T·(smear V)` shape. -/
theorem targetDynValue_shock_bellman_eq
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (x : ↥(Sanctions.S : Set ℝ)) :
    sp.targetDynValue_shock ρ hρc x =
      sSup ((fun a => sp.toParams.U_T x.val a (ρ x.val a)
              + sp.toParams.β_T * (sp.smear (sp.targetDynValue_shock ρ hρc))
                  (Sanctions.clipS' (sp.toParams.F x.val (ρ x.val a)))) ''
              Sanctions.I) := by
  have h := sp.targetDynValue_shock_isFixedPoint ρ hρc
  have hx : sp.targetDynBCF_shock ρ hρc (sp.targetDynValue_shock ρ hρc) x
              = sp.targetDynValue_shock ρ hρc x := by rw [h]
  rw [← hx]
  unfold targetDynBCF_shock
  rw [Sanctions.AbstractGame.Params.targetDynBCF_apply,
      Sanctions.AbstractGame.Params.targetDynBellmanOn]
  rfl

/-! ## The slaved shocked Target value and its Bellman equation -/

/-- **Slaved shocked Target value at a Sender value**: the shocked Target value at
the shocked Sender response `σ_dyn_top (smear V_S)`. -/
noncomputable def V_T_dyn_shock
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S) xa.1 xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  sp.targetDynValue_shock (sp.toParams.σ_dyn_top (sp.smear V_S)) hσc

/-- **Shocked Target Bellman equation in the `joint_T_top_integrand` shape**
required by the shocked equilibrium structure: the continuation is the *smeared*
Target value and the Sender response is the *shocked* selector
`σ_dyn_top (smear V_S)`. -/
theorem V_T_dyn_shock_bellman_eq
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S) xa.1 xa.2))
    (x : ↥(Sanctions.S : Set ℝ)) :
    sp.V_T_dyn_shock V_S hσc x =
      sSup ((fun a => sp.toParams.joint_T_top_integrand
              (sp.smear (sp.V_T_dyn_shock V_S hσc)) (sp.smear V_S) x.val a)
              '' Sanctions.I) := by
  simp only [Sanctions.AbstractGame.Params.joint_T_top_integrand, V_T_dyn_shock]
  exact sp.targetDynValue_shock_bellman_eq (sp.toParams.σ_dyn_top (sp.smear V_S)) hσc x

/-! ## State-local slaved shocked Target value -/

/-- **Slaved shocked Target value from physical-state Sender continuity.**
The generic Target Bellman constructor expects a selector on all real states, so
we feed it the continuous clipped extension `σ_dyn_top_clamped`. On every state
the economic model can reach, that extension equals the original dynamic greatest
argmax; the resulting value therefore satisfies the original shocked Bellman
equation on `S`. -/
noncomputable def V_T_dyn_shock_local
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S) xa.1.val xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  sp.targetDynValue_shock
    (sp.toParams.σ_dyn_top_clamped (sp.smear V_S))
    (sp.toParams.σ_dyn_top_clamped_continuous (sp.smear V_S) hσc)

/-- The locally constructed Target value solves the same shocked leader Bellman
equation as `V_T_dyn_shock`, because the clipped selector and the original
equilibrium-derived selector coincide at every physical state. -/
theorem V_T_dyn_shock_local_bellman_eq
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S) xa.1.val xa.2))
    (x : ↥(Sanctions.S : Set ℝ)) :
    sp.V_T_dyn_shock_local V_S hσc x =
      sSup ((fun a => sp.toParams.joint_T_top_integrand
              (sp.smear (sp.V_T_dyn_shock_local V_S hσc))
              (sp.smear V_S) x.val a) '' Sanctions.I) := by
  have h := sp.targetDynValue_shock_bellman_eq
    (sp.toParams.σ_dyn_top_clamped (sp.smear V_S))
    (sp.toParams.σ_dyn_top_clamped_continuous (sp.smear V_S) hσc) x
  simpa only [V_T_dyn_shock_local,
    Sanctions.AbstractGame.Params.joint_T_top_integrand,
    sp.toParams.σ_dyn_top_clamped_eq_of_mem (sp.smear V_S) x.property] using h

/-! ## The shocked-game equilibrium -/

/-- **Shocked feedback-Stackelberg equilibrium (top selector).** Equilibrium of
the *shocked* game: the Bellman fixed-point conditions carry the shock smoothing
`smear`. The Sender value solves the shocked Sender Bellman equation; the Target
value solves the shocked Target Bellman equation against the shocked Sender
response `σ_dyn_top (smear V_S)`; and `α` attains the shocked Target integrand
argmax. -/
structure ShockedFeedbackStackelbergEquilibriumTop where
  /-- Target (leader) value function. -/
  V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- Sender (follower) value function. -/
  V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- Target (leader) feedback policy. -/
  α : ℝ → ℝ
  /-- Continuity of α. -/
  hα : Continuous α
  /-- α is feasible at every feasible state. -/
  α_mem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I
  /-- **Shocked follower fixed point.** `V_S` is the *shocked* Sender Bellman
  fixed point under leader policy `α` (continuation smeared by the shock). -/
  V_S_fix_shock : V_S = sp.bellmanS_shock α hα V_S
  /-- **Shocked leader fixed point (top).** `V_T` solves the *shocked* Target
  Bellman equation against the shocked Sender response, with smeared continuation. -/
  V_T_fix_shock : ∀ x : ↥(Sanctions.S : Set ℝ),
    V_T x = sSup ((fun a => sp.toParams.joint_T_top_integrand
              (sp.smear V_T) (sp.smear V_S) x.val a) '' Sanctions.I)
  /-- **Shocked leader optimality (top).** `α` attains the shocked Target
  integrand argmax at every feasible state. -/
  α_opt_shock : ∀ x ∈ Sanctions.S,
    IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
      (sp.smear V_T) (sp.smear V_S) x a) Sanctions.I (α x)

/-- **Non-vacuous shocked corner equilibrium.** Mirrors
`feedbackStackelbergTop_of_constant_corner_optimal` for the shocked game. Given a
constant corner policy `α ≡ c`, the shocked Sender value `V_S_shock (fun _ => c)`,
continuity `hσc` of the shocked Sender selector, and leader corner-optimality
`h_corner_shock` against the shocked Target integrand, a
`ShockedFeedbackStackelbergEquilibriumTop` with `α ≡ c` exists. The only
constructed objects are the two Banach fixed points; `h_corner_shock` is consumed
conditionally (Rule-15). -/
theorem shockedFeedbackStackelbergTop_of_constant_corner
    (c : ℝ) (hc : c ∈ Sanctions.I)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top
        (sp.smear (sp.V_S_shock (fun _ => c) continuous_const)) xa.1 xa.2))
    (h_corner_shock : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock (sp.V_S_shock (fun _ => c) continuous_const) hσc))
        (sp.smear (sp.V_S_shock (fun _ => c) continuous_const)) x a) Sanctions.I c) :
    ∃ E : sp.ShockedFeedbackStackelbergEquilibriumTop, E.α = (fun _ => c) :=
  ⟨{ V_T := sp.V_T_dyn_shock (sp.V_S_shock (fun _ => c) continuous_const) hσc
     V_S := sp.V_S_shock (fun _ => c) continuous_const
     α := fun _ => c
     hα := continuous_const
     α_mem := fun _ _ => hc
     V_S_fix_shock := (sp.V_S_shock_isFixedPoint continuous_const).symm
     V_T_fix_shock := fun x =>
       sp.V_T_dyn_shock_bellman_eq (sp.V_S_shock (fun _ => c) continuous_const) hσc x
     α_opt_shock := h_corner_shock }, rfl⟩

end ShockedParams
end AbstractGame

end -- noncomputable section

end Sanctions
