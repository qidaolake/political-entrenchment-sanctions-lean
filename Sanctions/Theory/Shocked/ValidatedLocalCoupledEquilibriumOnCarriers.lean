/-
Sanctions/Theory/Shocked/ValidatedLocalCoupledEquilibriumOnCarriers.lean

Carrier-restricted local validated-Perov packaging for the coupled shocked
equilibrium.

This file introduces no model assumption or new equilibrium concept. It lifts
the generic carrier-ball fixed-point theorem from
`ValidatedLocalPerovOnCarriers` to the existing
`ShockedFeedbackStackelbergEquilibriumTop` structure. The eventual concrete
discharge must still prove carrier preservation, the two local row estimates,
the exact shocked Bellman-row identities, and local feasibility, continuity,
and optimality of the endogenous Target policy.
-/

import Sanctions.Foundations.ValidatedLocalPerovOnCarriers
import Sanctions.Theory.Shocked.ShockedEquilibrium

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Validated local coupled shocked equilibrium on closed carriers.**

An approximate fixed point, carrier-restricted two-row Perov estimates,
radius self-map inequalities, and a strict Schur margin produce an exact
fixed point in the product of two closed carrier-ball intersections. If, on
that restricted product, the rows are the actual shocked Target and Sender
Bellman operators and the supplied Target policy is continuous, feasible, and
optimal, the fixed point packages as the existing fully two-sided shocked
feedback-Stackelberg equilibrium.

The conclusion also records uniqueness of the value fixed point among points
in the two carrier-ball intersections. It does not claim global uniqueness or
uniqueness of policies beyond the supplied locally optimal selector.

2026-10-06 (round BG1.1 follow-up): the Target-row diagonal bound `a < 1` was
dropped. With the four sign conditions it follows from the Sender-row bound
`d < 1` and the Schur margin (`Foundations.Perov.lt_one_of_schur_margin`), so
the local certificate no longer asks for it. General in `F`: the transition
enters only through the shocked Bellman rows of `sp`. -/
theorem shockedFeedbackStackelbergTop_exists_of_local_perov_on_carriers_certificate
    (C_T C_S : Set SBCF) (hC_T : IsClosed C_T) (hC_S : IsClosed C_S)
    (T : SBCF × SBCF → SBCF × SBCF)
    (V_T0 V_S0 : SBCF)
    (rT rS εT εS : ℝ) {a b c d : ℝ}
    (hV_T0 : V_T0 ∈ C_T) (hV_S0 : V_S0 ∈ C_S)
    (hrT : 0 ≤ rT) (hrS : 0 ≤ rS)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hresT : dist (T (V_T0, V_S0)).1 V_T0 ≤ εT)
    (hresS : dist (T (V_T0, V_S0)).2 V_S0 ≤ εS)
    (hmapT : ∀ z : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS → (T z).1 ∈ C_T)
    (hmapS : ∀ z : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS → (T z).2 ∈ C_S)
    (hrowT : ∀ z z' : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS →
      z'.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z'.2 ∈ C_S ∩ Metric.closedBall V_S0 rS →
      dist (T z).1 (T z').1 ≤
        a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hrowS : ∀ z z' : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS →
      z'.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z'.2 ∈ C_S ∩ Metric.closedBall V_S0 rS →
      dist (T z).2 (T z').2 ≤
        c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hRadT : εT + a * rT + b * rS ≤ rT)
    (hRadS : εS + c * rT + d * rS ≤ rS)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d))
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S,
      V_T ∈ C_T ∩ Metric.closedBall V_T0 rT →
      V_S ∈ C_S ∩ Metric.closedBall V_S0 rS →
      Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S,
      V_T ∈ C_T ∩ Metric.closedBall V_T0 rT →
      V_S ∈ C_S ∩ Metric.closedBall V_S0 rS →
      ∀ x, x ∈ Sanctions.S → lead V_T V_S x ∈ Sanctions.I)
    (hσc : ∀ V_S : SBCF,
      V_S ∈ C_S ∩ Metric.closedBall V_S0 rS →
      Continuous (fun xs : ↥(Sanctions.S : Set ℝ) × ℝ =>
        sp.toParams.σ_dyn_top (sp.smear V_S) xs.1.val xs.2))
    (h_target_row : ∀ z : SBCF × SBCF,
      ∀ (_hzT : z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT)
        (hzS : z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS),
      (T z).1 =
        sp.targetDynBCF_shock
          (sp.toParams.σ_dyn_top_clamped (sp.smear z.2))
          (sp.toParams.σ_dyn_top_clamped_continuous
            (sp.smear z.2) (hσc z.2 hzS))
          z.1)
    (h_sender_row : ∀ z : SBCF × SBCF,
      ∀ (hzT : z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT)
        (hzS : z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS),
      (T z).2 =
        sp.bellmanS_shock
          (lead z.1 z.2) (lead_cont z.1 z.2 hzT hzS) z.2)
    (lead_opt : ∀ z : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS →
      ∀ x, x ∈ Sanctions.S →
        IsMaxOn
          (fun α => sp.toParams.joint_T_top_integrand
            (sp.smear z.1) (sp.smear z.2) x α)
          Sanctions.I (lead z.1 z.2 x)) :
    ∃ E : sp.ShockedFeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C_T ∩ Metric.closedBall V_T0 rT ∧
      E.V_S ∈ C_S ∩ Metric.closedBall V_S0 rS ∧
      E.α = lead E.V_T E.V_S ∧
      ∀ z : SBCF × SBCF,
        T z = z →
        z.1 ∈ C_T ∩ Metric.closedBall V_T0 rT →
        z.2 ∈ C_S ∩ Metric.closedBall V_S0 rS →
        z = (E.V_T, E.V_S) := by
  obtain ⟨z, hz, huniq⟩ :=
    Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint_in_closedCarrierBalls_of_residual
      C_T C_S hC_T hC_S T V_T0 V_S0 rT rS εT εS
      hV_T0 hV_S0 hrT hrS ha_nn hb_nn hc_nn hd_nn
      hresT hresS hmapT hmapS hrowT hrowS hRadT hRadS hd_lt hSchur
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
      sp.bellmanS_shock
          (lead z.1 z.2) (lead_cont z.1 z.2 hzT hzS) z.2 = z.2 := by
    rw [← h_sender_row z hzT hzS]
    exact hz_fix_S
  refine ⟨{
    V_T := z.1
    V_S := z.2
    α := lead z.1 z.2
    hα := lead_cont z.1 z.2 hzT hzS
    α_mem := lead_mem z.1 z.2 hzT hzS
    V_S_fix_shock := hS_bellman.symm
    V_T_fix_shock := ?_
    α_opt_shock := lead_opt z hzT hzS
  }, hzT, hzS, rfl, ?_⟩
  · intro x
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
  · intro w hw hwT hwS
    exact huniq w ⟨hw, hwT, hwS⟩

/-- **Validated local coupled equilibrium with canonical Perov radii.**

The Target and Sender validation radii are constructed from the actual
Bellman residual vector at the reference value pair and the symbolic
two-row matrix. No radius, residual allowance, or numerical slack is an
input. The remaining premises are exactly the carrier preservation, local
row estimates, row identities, and optimal-policy facts needed to identify
the fixed point as the existing two-sided shocked feedback-Stackelberg
equilibrium.

2026-10-06 (round BG1.1 follow-up): `a < 1` was dropped, as in
`shockedFeedbackStackelbergTop_exists_of_local_perov_on_carriers_certificate`;
it is implied by the signs, `d < 1` and the Schur margin. General in `F`. -/
theorem shockedFeedbackStackelbergTop_exists_of_canonical_local_perov_on_carriers
    (C_T C_S : Set SBCF) (hC_T : IsClosed C_T) (hC_S : IsClosed C_S)
    (T : SBCF × SBCF → SBCF × SBCF)
    (V_T0 V_S0 : SBCF) {a b c d : ℝ}
    (hV_T0 : V_T0 ∈ C_T) (hV_S0 : V_S0 ∈ C_S)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hmapT : ∀ z : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      (T z).1 ∈ C_T)
    (hmapS : ∀ z : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      (T z).2 ∈ C_S)
    (hrowT : ∀ z z' : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      z'.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z'.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      dist (T z).1 (T z').1 ≤
        a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hrowS : ∀ z z' : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      z'.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z'.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      dist (T z).2 (T z').2 ≤
        c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d))
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S,
      V_T ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      V_S ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S,
      V_T ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      V_S ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      ∀ x, x ∈ Sanctions.S → lead V_T V_S x ∈ Sanctions.I)
    (hσc : ∀ V_S : SBCF,
      V_S ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      Continuous (fun xs : ↥(Sanctions.S : Set ℝ) × ℝ =>
        sp.toParams.σ_dyn_top (sp.smear V_S) xs.1.val xs.2))
    (h_target_row : ∀ z : SBCF × SBCF,
      ∀ (_hzT : z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d))
        (hzS : z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d)),
      (T z).1 =
        sp.targetDynBCF_shock
          (sp.toParams.σ_dyn_top_clamped (sp.smear z.2))
          (sp.toParams.σ_dyn_top_clamped_continuous
            (sp.smear z.2) (hσc z.2 hzS))
          z.1)
    (h_sender_row : ∀ z : SBCF × SBCF,
      ∀ (hzT : z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d))
        (hzS : z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d)),
      (T z).2 =
        sp.bellmanS_shock
          (lead z.1 z.2) (lead_cont z.1 z.2 hzT hzS) z.2)
    (lead_opt : ∀ z : SBCF × SBCF,
      z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
      z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
      ∀ x, x ∈ Sanctions.S →
        IsMaxOn
          (fun α => sp.toParams.joint_T_top_integrand
            (sp.smear z.1) (sp.smear z.2) x α)
          Sanctions.I (lead z.1 z.2 x)) :
    ∃ E : sp.ShockedFeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) ∧
      E.V_S ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) ∧
      E.α = lead E.V_T E.V_S ∧
      ∀ z : SBCF × SBCF,
        T z = z →
        z.1 ∈ C_T ∩ Metric.closedBall V_T0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d) →
        z.2 ∈ C_S ∩ Metric.closedBall V_S0
          (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d) →
        z = (E.V_T, E.V_S) := by
  obtain ⟨hrT0, hrS0, hRadT0, hRadS0⟩ :=
    Sanctions.Foundations.Perov.perov2_canonicalRadii_spec
      (a := a) (b := b) (c := c) (d := d)
      (εX := dist (T (V_T0, V_S0)).1 V_T0)
      (εY := dist (T (V_T0, V_S0)).2 V_S0)
      (by exact dist_nonneg) (by exact dist_nonneg)
      hb_nn hc_nn hd_lt hSchur
  have hrT :
      0 ≤ Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d := by
    simpa only [Sanctions.Foundations.Perov.perov2ResidualRadiusX] using
      hrT0
  have hrS :
      0 ≤ Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d := by
    simpa only [Sanctions.Foundations.Perov.perov2ResidualRadiusY] using
      hrS0
  have hRadT :
      dist (T (V_T0, V_S0)).1 V_T0 +
          a * Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d +
          b * Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d ≤
        Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d := by
    simpa only [Sanctions.Foundations.Perov.perov2ResidualRadiusX,
      Sanctions.Foundations.Perov.perov2ResidualRadiusY] using
      hRadT0.le
  have hRadS :
      dist (T (V_T0, V_S0)).2 V_S0 +
          c * Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d +
          d * Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d ≤
        Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d := by
    simpa only [Sanctions.Foundations.Perov.perov2ResidualRadiusX,
      Sanctions.Foundations.Perov.perov2ResidualRadiusY] using
      hRadS0.le
  exact
    sp.shockedFeedbackStackelbergTop_exists_of_local_perov_on_carriers_certificate
      C_T C_S hC_T hC_S T V_T0 V_S0
      (Sanctions.Foundations.Perov.perov2ResidualRadiusX T V_T0 V_S0 a b c d)
      (Sanctions.Foundations.Perov.perov2ResidualRadiusY T V_T0 V_S0 a b c d)
      (dist (T (V_T0, V_S0)).1 V_T0)
      (dist (T (V_T0, V_S0)).2 V_S0)
      hV_T0 hV_S0 hrT hrS ha_nn hb_nn hc_nn hd_nn
      (by exact le_rfl) (by exact le_rfl) hmapT hmapS hrowT hrowS
      hRadT hRadS hd_lt hSchur
      lead lead_cont lead_mem hσc h_target_row h_sender_row lead_opt

end ShockedParams
end AbstractGame

end

end Sanctions

