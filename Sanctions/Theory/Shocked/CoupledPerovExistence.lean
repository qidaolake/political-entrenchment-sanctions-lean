/-
Sanctions/Theory/Shocked/CoupledPerovExistence.lean

Parametric two-value construction for the shocked infinite-horizon game.

This file moves the coupled Perov assembly out of the low-delta witness.  It
works on arbitrary closed nonempty Target and Sender value carriers.  The
Target row uses the endogenous shocked Sender response, the Sender row uses a
carrier-defined Target selector, and the fixed point is packaged as a
`ShockedFeedbackStackelbergEquilibriumTop`.

The results are deliberately named `conditional`: carrier invariance, the two
row estimates, and optimality of the supplied carrier selector remain explicit
inputs.  Thus this file is generic infrastructure, not an unconditional
existence claim and not a new assumption on `ShockedParams`.
-/

import Sanctions.Theory.Shocked.ShockedEquilibrium
import Sanctions.Foundations.PerovContraction

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- The shocked Target Bellman row on an arbitrary pair of carrier values.
The Sender response is the equilibrium-derived greatest dynamic selector at
the smeared Sender value. -/
noncomputable def coupledTargetBCF
    {carrierT carrierS : Set SBCF}
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (V_T : ↥carrierT) (V_S : ↥carrierS) : SBCF :=
  sp.targetDynBCF_shock
    (sp.toParams.σ_dyn_top_clamped (sp.smear V_S.val))
    (sp.toParams.σ_dyn_top_clamped_continuous (sp.smear V_S.val) (hσc V_S))
    V_T.val

/-- The shocked Sender Bellman row at the carrier-defined Target selector. -/
noncomputable def coupledSenderBCF
    {carrierT carrierS : Set SBCF}
    (lead : ↥carrierT → ↥carrierS → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (V_T : ↥carrierT) (V_S : ↥carrierS) : SBCF :=
  sp.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S.val

/-- The simultaneous two-row shocked Bellman operator restricted to two
invariant carriers. -/
noncomputable def coupledJointOp
    {carrierT carrierS : Set SBCF}
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (lead : ↥carrierT → ↥carrierS → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (h_invT : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledTargetBCF hσc V_T V_S ∈ carrierT)
    (h_invS : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledSenderBCF lead lead_cont V_T V_S ∈ carrierS)
    (z : ↥carrierT × ↥carrierS) : ↥carrierT × ↥carrierS :=
  (⟨sp.coupledTargetBCF hσc z.1 z.2, h_invT z.1 z.2⟩,
   ⟨sp.coupledSenderBCF lead lead_cont z.1 z.2, h_invS z.1 z.2⟩)

/-! ## Retaining Sender-selector regularity at a carrier equilibrium -/

/-- **Carrier membership recovers the constructed Sender-selector
continuity.**  The coupled construction already requires joint continuity of
the shocked greatest Sender argmax at every Sender-carrier value.  Therefore,
once an equilibrium's Sender value is returned together with its carrier
membership proof, the same continuity statement follows directly; it need not
be added as a field of `ShockedFeedbackStackelbergEquilibriumTop`.

The state coordinate is the physical subtype `↥S`, exactly the domain visited
by the stochastic state law. -/
theorem coupledShocked_senderSelector_continuous_of_mem
    {carrierS : Set SBCF}
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ carrierS) :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear E.V_S) xa.1.val xa.2) :=
  hσc ⟨E.V_S, hVS⟩

/-- The retained joint Sender selector is Borel measurable.  This is a direct
corollary of the continuity already consumed by the carrier construction, not
a separate measurable-selection assumption. -/
theorem coupledShocked_senderSelector_measurable_of_mem
    {carrierS : Set SBCF}
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ carrierS) :
    Measurable (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear E.V_S) xa.1.val xa.2) :=
  (sp.coupledShocked_senderSelector_continuous_of_mem hσc E hVS).measurable

/-- The retained physical-state continuity also gives the continuous
whole-line clipped extension used by generic Target-Bellman interfaces.  On
every physical state this extension equals the original equilibrium-derived
greatest Sender argmax. -/
theorem coupledShocked_senderSelectorClamped_continuous_of_mem
    {carrierS : Set SBCF}
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hVS : E.V_S ∈ carrierS) :
    Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top_clamped (sp.smear E.V_S) xa.1 xa.2) :=
  sp.toParams.σ_dyn_top_clamped_continuous (sp.smear E.V_S)
    (sp.coupledShocked_senderSelector_continuous_of_mem hσc E hVS)

/-- **Conditional parametric coupled shocked fixed point.**

On arbitrary closed nonempty carriers, two componentwise Lipschitz rows and the
strict two-by-two Schur margin construct a unique simultaneous fixed point.
Both cross-value channels may be nonzero; no row-sum condition is imposed.

2026-10-06 (round BG1.1): the Target-row diagonal bound `βTrow < 1` was
dropped. With the four sign conditions it follows from `βSrow < 1` and the
Schur margin (`Foundations.Perov.lt_one_of_schur_margin`), so the Perov engine
no longer asks for it. General in `F`: the transition enters only through the
shocked Bellman rows of `sp`. -/
theorem coupledShocked_existsUnique_fixedPoint_conditional
    {carrierT carrierS : Set SBCF}
    (hclosedT : IsClosed carrierT) (hclosedS : IsClosed carrierS)
    (hneT : carrierT.Nonempty) (hneS : carrierS.Nonempty)
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (lead : ↥carrierT → ↥carrierS → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (h_invT : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledTargetBCF hσc V_T V_S ∈ carrierT)
    (h_invS : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledSenderBCF lead lead_cont V_T V_S ∈ carrierS)
    {βTrow LTS LST βSrow : ℝ}
    (hβTrow_nn : 0 ≤ βTrow) (hLTS_nn : 0 ≤ LTS)
    (hLST_nn : 0 ≤ LST) (hβSrow_nn : 0 ≤ βSrow)
    (hrowT : ∀ z z',
      dist (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z).1
          (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z').1
        ≤ βTrow * dist z.1 z'.1 + LTS * dist z.2 z'.2)
    (hrowS : ∀ z z',
      dist (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z).2
          (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z').2
        ≤ LST * dist z.1 z'.1 + βSrow * dist z.2 z'.2)
    (hβSrow_lt : βSrow < 1)
    (hSchur : LTS * LST < (1 - βTrow) * (1 - βSrow)) :
    ∃! z : ↥carrierT × ↥carrierS,
      sp.coupledJointOp hσc lead lead_cont h_invT h_invS z = z := by
  haveI : CompleteSpace ↥carrierT := hclosedT.completeSpace_coe
  haveI : CompleteSpace ↥carrierS := hclosedS.completeSpace_coe
  haveI : Nonempty ↥carrierT := hneT.to_subtype
  haveI : Nonempty ↥carrierS := hneS.to_subtype
  exact Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint
    (T := sp.coupledJointOp hσc lead lead_cont h_invT h_invS)
    hβTrow_nn hLTS_nn hLST_nn hβSrow_nn hrowT hrowS
    hβSrow_lt hSchur

/-- **Conditional parametric two-player shocked equilibrium.**

The unique simultaneous carrier fixed point is packaged as a shocked
feedback-Stackelberg equilibrium.  The Target selector is carrier-defined,
continuous, feasible, and optimal for the complete shocked Target objective;
the Sender action remains the endogenous greatest dynamic Bellman response.
The conclusion is an infinite-horizon equilibrium because both value
coordinates satisfy their shocked Bellman fixed-point equations.

2026-10-06 (round BG1.1): `βTrow < 1` was dropped, as in
`coupledShocked_existsUnique_fixedPoint_conditional`; it is implied by the
signs, `βSrow < 1` and the Schur margin. General in `F`. -/
theorem coupledShockedFeedbackStackelbergTop_exists_conditional
    {carrierT carrierS : Set SBCF}
    (hclosedT : IsClosed carrierT) (hclosedS : IsClosed carrierS)
    (hneT : carrierT.Nonempty) (hneS : carrierS.Nonempty)
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (lead : ↥carrierT → ↥carrierS → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S x, x ∈ Sanctions.S → lead V_T V_S x ∈ Sanctions.I)
    (lead_opt : ∀ V_T V_S x, x ∈ Sanctions.S →
      IsMaxOn
        (fun a => sp.toParams.joint_T_top_integrand
          (sp.smear V_T.val) (sp.smear V_S.val) x a)
        Sanctions.I (lead V_T V_S x))
    (h_invT : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledTargetBCF hσc V_T V_S ∈ carrierT)
    (h_invS : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledSenderBCF lead lead_cont V_T V_S ∈ carrierS)
    {βTrow LTS LST βSrow : ℝ}
    (hβTrow_nn : 0 ≤ βTrow) (hLTS_nn : 0 ≤ LTS)
    (hLST_nn : 0 ≤ LST) (hβSrow_nn : 0 ≤ βSrow)
    (hrowT : ∀ z z',
      dist (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z).1
          (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z').1
        ≤ βTrow * dist z.1 z'.1 + LTS * dist z.2 z'.2)
    (hrowS : ∀ z z',
      dist (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z).2
          (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z').2
        ≤ LST * dist z.1 z'.1 + βSrow * dist z.2 z'.2)
    (hβSrow_lt : βSrow < 1)
    (hSchur : LTS * LST < (1 - βTrow) * (1 - βSrow)) :
    ∃ E : sp.ShockedFeedbackStackelbergEquilibriumTop,
      ∃ hVT : E.V_T ∈ carrierT, ∃ hVS : E.V_S ∈ carrierS,
        E.α = lead ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ := by
  obtain ⟨z, hz, -⟩ :=
    sp.coupledShocked_existsUnique_fixedPoint_conditional
      hclosedT hclosedS hneT hneS hσc lead lead_cont h_invT h_invS
      hβTrow_nn hLTS_nn hLST_nn hβSrow_nn hrowT hrowS
      hβSrow_lt hSchur
  have hz_T :
      sp.coupledTargetBCF hσc z.1 z.2 = z.1.val := by
    exact congrArg (fun w : ↥carrierT × ↥carrierS => w.1.val) hz
  have hz_S :
      sp.coupledSenderBCF lead lead_cont z.1 z.2 = z.2.val := by
    exact congrArg (fun w : ↥carrierT × ↥carrierS => w.2.val) hz
  refine ⟨{
    V_T := z.1.val
    V_S := z.2.val
    α := lead z.1 z.2
    hα := lead_cont z.1 z.2
    α_mem := lead_mem z.1 z.2
    V_S_fix_shock := hz_S.symm
    V_T_fix_shock := ?_
    α_opt_shock := lead_opt z.1 z.2
  }, z.1.property, z.2.property, rfl⟩
  intro x
  have hx := congrArg (fun V : SBCF => V x) hz_T
  calc
    z.1.val x = sp.coupledTargetBCF hσc z.1 z.2 x := hx.symm
    _ = sSup ((fun a => sp.toParams.joint_T_top_integrand
        (sp.smear z.1.val) (sp.smear z.2.val) x.val a) '' Sanctions.I) := by
      simp only [coupledTargetBCF, targetDynBCF_shock,
        Sanctions.AbstractGame.Params.targetDynBCF_apply,
        Sanctions.AbstractGame.Params.targetDynBellmanOn,
        Sanctions.AbstractGame.Params.targetDynIntegrand,
        Sanctions.AbstractGame.Params.joint_T_top_integrand,
        sp.toParams.σ_dyn_top_clamped_eq_of_mem (sp.smear z.2.val) x.property]

/-- An equilibrium represented by the carrier selector is a fixed point of the
simultaneous carrier operator.  This is the converse bridge used for
within-carrier equilibrium uniqueness. -/
theorem coupledJointOp_fixed_of_shockedFeedbackStackelbergTop
    {carrierT carrierS : Set SBCF}
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (lead : ↥carrierT → ↥carrierS → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (h_invT : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledTargetBCF hσc V_T V_S ∈ carrierT)
    (h_invS : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledSenderBCF lead lead_cont V_T V_S ∈ carrierS)
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ carrierT) (hVS : E.V_S ∈ carrierS)
    (hα : E.α = lead ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) :
    sp.coupledJointOp hσc lead lead_cont h_invT h_invS
        (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩)
      = (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    ext x
    change sp.coupledTargetBCF hσc ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ x = E.V_T x
    rw [E.V_T_fix_shock x]
    simp only [coupledTargetBCF, targetDynBCF_shock,
      Sanctions.AbstractGame.Params.targetDynBCF_apply,
      Sanctions.AbstractGame.Params.targetDynBellmanOn,
      Sanctions.AbstractGame.Params.targetDynIntegrand,
      Sanctions.AbstractGame.Params.joint_T_top_integrand,
      sp.toParams.σ_dyn_top_clamped_eq_of_mem (sp.smear E.V_S) x.property]
  · apply Subtype.ext
    change sp.bellmanS_shock
        (lead ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
        (lead_cont ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) E.V_S = E.V_S
    calc
      sp.bellmanS_shock
          (lead ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
          (lead_cont ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) E.V_S =
          sp.bellmanS_shock E.α E.hα E.V_S := by
        unfold bellmanS_shock
        exact sp.toParams.bellmanS_BCF_congr_α hα.symm
          (lead_cont ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) E.hα (sp.smear E.V_S)
      _ = E.V_S := E.V_S_fix_shock.symm

/-- **Conditional uniqueness in the supplied carrier class.**

Under the same two-row Schur certificate, two shocked equilibria whose values
belong to the carriers and whose policies coincide with the supplied
carrier-defined selector have identical Target values, Sender values, and
policies.  This is not global equilibrium uniqueness outside that class.

2026-10-06 (round BG1.1): `βTrow < 1` was dropped, as in
`coupledShocked_existsUnique_fixedPoint_conditional`; it is implied by the
signs, `βSrow < 1` and the Schur margin. General in `F`. -/
theorem coupledShockedFeedbackStackelbergTop_unique_in_carriers_conditional
    {carrierT carrierS : Set SBCF}
    (hclosedT : IsClosed carrierT) (hclosedS : IsClosed carrierS)
    (hneT : carrierT.Nonempty) (hneS : carrierS.Nonempty)
    (hσc : ∀ V_S : ↥carrierS, Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear V_S.val) xa.1.val xa.2))
    (lead : ↥carrierT → ↥carrierS → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S, Continuous (lead V_T V_S))
    (h_invT : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledTargetBCF hσc V_T V_S ∈ carrierT)
    (h_invS : ∀ (V_T : ↥carrierT) (V_S : ↥carrierS),
      sp.coupledSenderBCF lead lead_cont V_T V_S ∈ carrierS)
    {βTrow LTS LST βSrow : ℝ}
    (hβTrow_nn : 0 ≤ βTrow) (hLTS_nn : 0 ≤ LTS)
    (hLST_nn : 0 ≤ LST) (hβSrow_nn : 0 ≤ βSrow)
    (hrowT : ∀ z z',
      dist (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z).1
          (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z').1
        ≤ βTrow * dist z.1 z'.1 + LTS * dist z.2 z'.2)
    (hrowS : ∀ z z',
      dist (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z).2
          (sp.coupledJointOp hσc lead lead_cont h_invT h_invS z').2
        ≤ LST * dist z.1 z'.1 + βSrow * dist z.2 z'.2)
    (hβSrow_lt : βSrow < 1)
    (hSchur : LTS * LST < (1 - βTrow) * (1 - βSrow))
    (E E' : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ carrierT) (hVS : E.V_S ∈ carrierS)
    (hVT' : E'.V_T ∈ carrierT) (hVS' : E'.V_S ∈ carrierS)
    (hα : E.α = lead ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hα' : E'.α = lead ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α := by
  obtain ⟨z, -, hunique⟩ :=
    sp.coupledShocked_existsUnique_fixedPoint_conditional
      hclosedT hclosedS hneT hneS hσc lead lead_cont h_invT h_invS
      hβTrow_nn hLTS_nn hLST_nn hβSrow_nn hrowT hrowS
      hβSrow_lt hSchur
  let zE : ↥carrierT × ↥carrierS := (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩)
  let zE' : ↥carrierT × ↥carrierS := (⟨E'.V_T, hVT'⟩, ⟨E'.V_S, hVS'⟩)
  have hzE :
      sp.coupledJointOp hσc lead lead_cont h_invT h_invS zE = zE := by
    exact sp.coupledJointOp_fixed_of_shockedFeedbackStackelbergTop
      hσc lead lead_cont h_invT h_invS E hVT hVS hα
  have hzE' :
      sp.coupledJointOp hσc lead lead_cont h_invT h_invS zE' = zE' := by
    exact sp.coupledJointOp_fixed_of_shockedFeedbackStackelbergTop
      hσc lead lead_cont h_invT h_invS E' hVT' hVS' hα'
  have hpairs : zE = zE' := (hunique zE hzE).trans (hunique zE' hzE').symm
  have hvaluesT : E.V_T = E'.V_T :=
    congrArg (fun w : ↥carrierT × ↥carrierS => w.1.val) hpairs
  have hvaluesS : E.V_S = E'.V_S :=
    congrArg (fun w : ↥carrierT × ↥carrierS => w.2.val) hpairs
  have hlead :
      lead ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ =
        lead ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩ :=
    congrArg (fun w : ↥carrierT × ↥carrierS => lead w.1 w.2) hpairs
  exact ⟨hvaluesT, hvaluesS, hα.trans (hlead.trans hα'.symm)⟩

end ShockedParams
end AbstractGame

end -- noncomputable section

end Sanctions
