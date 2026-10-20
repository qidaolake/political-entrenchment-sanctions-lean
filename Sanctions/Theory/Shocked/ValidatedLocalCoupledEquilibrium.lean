/-
Sanctions/Theory/Shocked/ValidatedLocalCoupledEquilibrium.lean

Local validated-Perov packaging for the coupled shocked equilibrium.

This file does not introduce a model assumption or a new equilibrium concept.
It combines the generic closed-ball fixed-point certificate from
`ValidatedLocalPerov` with the existing
`ShockedFeedbackStackelbergEquilibriumTop` structure.  The eventual concrete
witness must still verify that its local operator is exactly the two shocked
Bellman rows and that its supplied Target policy is feasible and optimal
throughout the validated balls.
-/

import Sanctions.Foundations.ValidatedLocalPerov
import Sanctions.Theory.Shocked.ShockedEquilibrium

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Validated local coupled shocked equilibrium.**

An approximate fixed point, local two-row Perov bounds, radius self-map
inequalities, and the strict Schur margin produce an exact fixed point inside
the two certified closed balls.  If, on those balls, the two rows are the
actual shocked Target and Sender Bellman operators and the supplied Target
policy is feasible and optimal, that fixed point packages directly as the
existing two-sided shocked feedback-Stackelberg equilibrium.

The theorem deliberately takes the local row-identification and policy
certificates as proof obligations.  It therefore does not turn a numerical
iteration, an approximate residual, or an optimizer conjecture into an
equilibrium assumption.

2026-10-06 (round BG1.1 follow-up): the Target-row diagonal bound `a < 1` was
dropped. With the four sign conditions it follows from the Sender-row bound
`d < 1` and the Schur margin (`Foundations.Perov.lt_one_of_schur_margin`), so
the local certificate no longer asks for it. General in `F`: the transition
enters only through the shocked Bellman rows of `sp`. -/
theorem shockedFeedbackStackelbergTop_exists_of_local_perov_certificate
    (T : SBCF × SBCF → SBCF × SBCF)
    (V_T0 V_S0 : SBCF)
    (rT rS εT εS : ℝ) {a b c d : ℝ}
    (hrT : 0 ≤ rT) (hrS : 0 ≤ rS)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hresT : dist (T (V_T0, V_S0)).1 V_T0 ≤ εT)
    (hresS : dist (T (V_T0, V_S0)).2 V_S0 ≤ εS)
    (hrowT : ∀ z z' : SBCF × SBCF,
      dist z.1 V_T0 ≤ rT → dist z.2 V_S0 ≤ rS →
      dist z'.1 V_T0 ≤ rT → dist z'.2 V_S0 ≤ rS →
      dist (T z).1 (T z').1 ≤
        a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hrowS : ∀ z z' : SBCF × SBCF,
      dist z.1 V_T0 ≤ rT → dist z.2 V_S0 ≤ rS →
      dist z'.1 V_T0 ≤ rT → dist z'.2 V_S0 ≤ rS →
      dist (T z).2 (T z').2 ≤
        c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hRadT : εT + a * rT + b * rS ≤ rT)
    (hRadS : εS + c * rT + d * rS ≤ rS)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d))
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S x, x ∈ Sanctions.S →
      lead V_T V_S x ∈ Sanctions.I)
    (hσc : ∀ V_S : SBCF, dist V_S V_S0 ≤ rS →
      Continuous (fun xs : ↥(Sanctions.S : Set ℝ) × ℝ =>
        sp.toParams.σ_dyn_top (sp.smear V_S) xs.1.val xs.2))
    (h_target_row : ∀ z : SBCF × SBCF,
      ∀ (_hzT : dist z.1 V_T0 ≤ rT) (hzS : dist z.2 V_S0 ≤ rS),
      (T z).1 =
        sp.targetDynBCF_shock
          (sp.toParams.σ_dyn_top_clamped (sp.smear z.2))
          (sp.toParams.σ_dyn_top_clamped_continuous
            (sp.smear z.2) (hσc z.2 hzS))
          z.1)
    (h_sender_row : ∀ z : SBCF × SBCF,
      dist z.1 V_T0 ≤ rT → dist z.2 V_S0 ≤ rS →
      (T z).2 =
        sp.bellmanS_shock (lead z.1 z.2) (lead_cont z.1 z.2) z.2)
    (lead_opt : ∀ z : SBCF × SBCF,
      dist z.1 V_T0 ≤ rT → dist z.2 V_S0 ≤ rS →
      ∀ x, x ∈ Sanctions.S →
        IsMaxOn
          (fun α => sp.toParams.joint_T_top_integrand
            (sp.smear z.1) (sp.smear z.2) x α)
          Sanctions.I (lead z.1 z.2 x)) :
    ∃ E : sp.ShockedFeedbackStackelbergEquilibriumTop,
      dist E.V_T V_T0 ≤ rT ∧
      dist E.V_S V_S0 ≤ rS ∧
      E.α = lead E.V_T E.V_S := by
  obtain ⟨z, hz, -⟩ :=
    Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint_in_closedBalls_of_residual
      T V_T0 V_S0 rT rS εT εS
      hrT hrS ha_nn hb_nn hc_nn hd_nn
      hresT hresS hrowT hrowS hRadT hRadS hd_lt hSchur
  rcases hz with ⟨hz_fix, hzT, hzS⟩
  have hz_fix_T : (T z).1 = z.1 := congrArg Prod.fst hz_fix
  have hz_fix_S : (T z).2 = z.2 := congrArg Prod.snd hz_fix
  have hT_bellman :
      sp.targetDynBCF_shock
          (sp.toParams.σ_dyn_top_clamped (sp.smear z.2))
          (sp.toParams.σ_dyn_top_clamped_continuous
            (sp.smear z.2) (hσc z.2 hzS))
          z.1 = z.1 := by
    rw [← h_target_row z hzT hzS]
    exact hz_fix_T
  have hS_bellman :
      sp.bellmanS_shock (lead z.1 z.2) (lead_cont z.1 z.2) z.2 = z.2 := by
    rw [← h_sender_row z hzT hzS]
    exact hz_fix_S
  refine ⟨{
    V_T := z.1
    V_S := z.2
    α := lead z.1 z.2
    hα := lead_cont z.1 z.2
    α_mem := lead_mem z.1 z.2
    V_S_fix_shock := hS_bellman.symm
    V_T_fix_shock := ?_
    α_opt_shock := lead_opt z hzT hzS
  }, hzT, hzS, rfl⟩
  intro x
  have hx := congrArg (fun V : SBCF => V x) hT_bellman
  calc
    z.1 x =
        sp.targetDynBCF_shock
          (sp.toParams.σ_dyn_top_clamped (sp.smear z.2))
          (sp.toParams.σ_dyn_top_clamped_continuous
            (sp.smear z.2) (hσc z.2 hzS))
          z.1 x := hx.symm
    _ = sSup ((fun α => sp.toParams.joint_T_top_integrand
        (sp.smear z.1) (sp.smear z.2) x.val α) '' Sanctions.I) := by
      simp only [targetDynBCF_shock,
        Sanctions.AbstractGame.Params.targetDynBCF_apply,
        Sanctions.AbstractGame.Params.targetDynBellmanOn,
        Sanctions.AbstractGame.Params.targetDynIntegrand,
        Sanctions.AbstractGame.Params.joint_T_top_integrand,
        sp.toParams.σ_dyn_top_clamped_eq_of_mem (sp.smear z.2) x.property]

end ShockedParams
end AbstractGame

end

end Sanctions
