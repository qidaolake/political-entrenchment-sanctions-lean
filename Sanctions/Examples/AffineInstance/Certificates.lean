/-
Sanctions/Examples/AffineInstance/Certificates.lean

**The affine transition as a worked instance: chords, margins, certificates.**

Companion to `Kinematics.lean`, and the same story one layer up. Every
declaration here was proved in `Sanctions/Theory/` and moved out on
2026-08-20d, once the general-`F` route had absorbed what used to need it.
None was deleted then, because each still earned its keep as an *exhibit*: the
affine law is an admissible instance of the transition (Rule 22), and these say
what that instance discharges for free. Round BG (2026-10-06) deleted one, the
goal-2 wrapper `goal2_dominance_of_affine`: its body was
`goal2_dominance_generalF p C` verbatim and it read neither `hF` nor `0 ≤ g_T`,
so it exhibited nothing; its three witness call sites now call the general
theorem directly.

Two kinds of thing live here.

* **Chord discharges.** The general route asks the transition for inequalities
  --- a sanction lower chord at rate `dlo` (one more unit of sanction raises
  next period's political state by at least `dlo`), a range-restricted upper
  chord at rate `d` (it raises it by at most `d`), a state-coordinate Lipschitz
  bound, an increasing-differences sign. The affine law satisfies every one of
  them *at equality*, with `dlo = d = delta`. These are the discharges.
* **Affine recoveries of the general theorems (Rule 5 / Rule 13).** Each
  general-`F` certificate result has an affine sibling obtained by feeding it
  those discharges. They are the machine-checked drift fence: they show that
  deleting `hF : p.F = affineF p.delta` from the general statements cost
  nothing, because the affine conclusion is still derivable --- as an instance,
  from strictly weaker hypotheses.

**Why this is in `Examples/` and not `Theory/`.** Every declaration below
carries `hF`, so under Rule 22 each is affine-restricted by construction, and
none is load-bearing for any general result --- that was checked declaration by
declaration before the move. Leaving them in `Theory/` made the theory layer
read as more affine than it is.

One consumer relationship survives the move and is worth naming:
`affine_sender_chord_on` discharges the `hF_chord` field of every pinned
economy's certificate, so the five witness files that build one now import this
module. That is the correct direction --- a witness is an instance, and so is
this.
-/

import Sanctions.Theory.Certificates.GeneralFDischargers
import Sanctions.Theory.Basin.TransitionChords
import Sanctions.Theory.Bellman.ValueLipschitz
import Sanctions.Theory.Bellman.SenderLowerSlopeCone
import Sanctions.Theory.Certificates.ConvexValueRoute
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

open Sanctions.TransitionChords

variable (p : Params)

/-- **Affine transitions satisfy every chord predicate**, at
`(d_lo, d_hi, γ, M) = (δ, δ, 1 − δ, 0)`. Consequently any theorem
restated over the bundle is at least as general as its `hF`-gated
predecessor, and the affine version is recovered by this lemma. -/
theorem affine_transitionChordPack {δ : ℝ} (hF : p.F = affineF δ) :
    p.SanctionLowerChordWith δ ∧ p.SanctionUpperChordWith δ
      ∧ p.CornerSectionTopWith (1 - δ) ∧ p.SanctionSemiconcaveWith 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [SanctionLowerChordWith, hF, affineF] using affine_sanctionLowerChord δ
  · simpa [SanctionUpperChordWith, hF, affineF] using affine_sanctionUpperChord δ
  · simpa [CornerSectionTopWith, hF, affineF] using affine_cornerSectionTop δ
  · simpa [SanctionSemiconcaveWith, hF, affineF] using affine_sanctionSemiconcave δ

/-- Strict adjustment for an affine transition, routed through the chord
rather than through the bespoke affine lemma — a consistency check that
the chord route subsumes the affine one. -/
theorem strictAdjustment_of_affine_via_chord {δ : ℝ} (hδ : 0 < δ)
    (hF : p.F = affineF δ) : p.StrictAdjustment :=
  p.strictAdjustment_of_sanctionLowerChord hδ (p.affine_transitionChordPack hF).1

/-- **The affine transition satisfies the optional general-`F`
state-Lipschitz condition.**

When `F(x,s) = (1-δ)x + δs`, holding the sanction fixed transmits an
inherited-state difference with the exact coefficient `1-δ`. Thus the
general modulus `γ_F` specializes to the affine persistence weight,
not to the sanction pass-through coefficient `δ`. -/
theorem transitionStateLipschitzWith_of_affine
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    p.TransitionStateLipschitzWith (1 - p.δ) := by
  intro x₁ x₂ s _hs
  rw [hF]
  unfold Sanctions.AbstractGame.affineF
  have hdiff :
      ((1 - p.δ) * x₂ + p.δ * s) - ((1 - p.δ) * x₁ + p.δ * s) =
        (1 - p.δ) * (x₂ - x₁) := by
    ring
  rw [hdiff, abs_mul]
  have h_one_sub_delta_nn : 0 ≤ 1 - p.δ := by
    linarith [p.δ_mem.2]
  rw [abs_of_nonneg h_one_sub_delta_nn]

/-- **Drift fence (Rule 13): the affine hypotheses imply the general one.**

The stage state-chord at rate `m`, the sub-solution inequality
`g ≤ m + β_S·g·(1−δ)`, and the affine law together give the joint chord consumed
by `bellmanS_BCF_preserves_lowerSlopeCone_generalF`. So the general theorem
covers every case the affine one did, and nothing was lost by deleting `hF`.

The converse fails: the joint chord permits the stage payoff to make up for a
flat stretch of the transition, which the separated pair cannot express. -/
theorem joint_state_chord_of_stage_chord_and_affine
    {α : ℝ → ℝ}
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m g : ℝ}
    (h_stage_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_cone : g ≤ m + p.β_S * g * (1 - p.δ)) :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      g * (y₂ - y₁)
        ≤ (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
          + p.β_S * g * (p.F y₂ s - p.F y₁ s) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have hdiff_nn : (0:ℝ) ≤ y₂ - y₁ := by linarith
  have hU := h_stage_state_slope s hs y₁ hy₁ y₂ hy₂ hle
  -- Under the affine law the state increment is exactly `(1 − δ)·(y₂ − y₁)`.
  have hFdiff : p.F y₂ s - p.F y₁ s = (1 - p.δ) * (y₂ - y₁) := by
    rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
  have hcone_scaled : g * (y₂ - y₁)
      ≤ (m + p.β_S * g * (1 - p.δ)) * (y₂ - y₁) :=
    mul_le_mul_of_nonneg_right h_cone hdiff_nn
  rw [hFdiff]
  nlinarith [hU, hcone_scaled]

/-- **Drift fence (Rule 13): the affine law satisfies the order condition.**
An affine transition is modular — its cross-difference in `(state, sanction)` is
identically zero — so `hF_super` holds with equality and the general theorem
covers the affine one. -/
theorem affine_transition_increasingDifferences {δ : ℝ}
    (hF : p.F = Sanctions.AbstractGame.affineF δ) :
    ∀ x : ℝ, ∀ x' : ℝ, x ≤ x' → ∀ s₁ : ℝ, ∀ s₂ : ℝ, s₁ ≤ s₂ →
      p.F x s₂ - p.F x s₁ ≤ p.F x' s₂ - p.F x' s₁ := by
  intro x x' _ s₁ s₂ _
  rw [hF]
  unfold Sanctions.AbstractGame.affineF
  linarith [le_refl ((1 - δ) * x + δ * s₂)]

/-- **Affine recovery (Rule 5 / Rule 13 drift fence).** The affine constructor
`of_stage_lowerSlopes_compliance_target_on` is the `d = dlo = p.δ` instance of
the general one: `affine_sanctionLowerChord` discharges the Target chord and the
affine displacement identity discharges the Sender chord. Nothing is lost by
deleting `hF`.

The single asymmetry is `hg_nn` (`0 ≤ g`, the Target value function's minimum
upward state slope is nonnegative), which the affine route does not need because
its transition step is an equality rather than an inequality. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on_recovered
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith V_S KS)
    {c g : ℝ}
    (h_stage_loss_T :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (α x) s)
          (Set.Icc (max x sbar) 1) c)
    (hV_T_gain_on : LowerSlopeOnValueOn V_T (Set.Icc xT 1) g)
    (hg_nn : 0 ≤ g)
    (h_margin : c ≤ p.β_T * g * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS) :
    p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar := by
  refine OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on_generalF
    p (dlo := p.δ) (d := p.δ) ?_ hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin ?_
    hV_S_lip h_stage_loss_T hV_T_gain_on hg_nn h_margin h_stage_sender
  · rw [hF]; exact Sanctions.TransitionChords.affine_sanctionLowerChord _
  · intro x _ s₁ _ s₂ _ hs
    have hδ : (0 : ℝ) ≤ p.δ := le_of_lt p.δ_mem.1
    have hval : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval]
    exact le_of_eq (abs_of_nonneg (mul_nonneg hδ (by linarith)))

/-- **Affine specialisation check (Rule 13 drift fence).**  With
`p.F = affineF p.δ` and `dlo := p.δ` the new discharger delivers the same
conclusion as the legacy affine combined-chord discharger (retired 2026-08-21,
zero consumers once this route replaced it), so nothing
was lost by deleting `hF`.

One hypothesis is deliberately *not* shared, and the asymmetry is substantive.
The general-`F` route needs `hgT_nn` (`0 ≤ g_T` — the Target value function's
minimum upward state slope is nonnegative) because the transition enters only
through the *inequality* `dlo·(s₂ − s₁) ≤ F(x,s₂) − F(x,s₁)`, and scaling an
inequality by `g_T` reverses it when `g_T < 0`.  Under the affine law that step
is an *equality*, so the sign cannot matter and the legacy discharger carries no
such hypothesis (2026-08-16: it was present but unused, and was removed).
Generality in `F` is exactly what makes the sign of the continuation-gain rate
load-bearing. -/
theorem Target_combined_chord_of_decomposition_lowerChord_affine
    {D : p.ValueClass2} {xT sbar : ℝ}
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hxT_mem : xT ∈ Sanctions.I)
    {cT gT : ℝ} (hgT_nn : 0 ≤ gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_target_loss_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xT (1 : ℝ),
          LowerLossSlopeOn (fun s => p.U_T x (D.α_on V_T V_S x) s)
            (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on_carrier :
      ∀ V_T ∈ D.carrier_T, LowerSlopeOnValueOn V_T (Set.Icc xT 1) gT) :
    p.TargetCombinedChordOn D xT sbar :=
  p.Target_combined_chord_of_decomposition_lowerChord hxT_mem
    (dlo := p.δ) (by rw [hF]; exact affine_sanctionLowerChord p.δ)
    hgT_nn hT_loss_margin h_stage_target_loss_on hV_T_gain_on_carrier

/-- **The affine transition satisfies the Sender-side range-restricted upper
chord at rate `delta`.** Discharges the `hF_chord` hypothesis of the general-`F`
threshold constructor at the affine instance, which is what lets an affine
witness travel the general route unchanged. -/
theorem affine_sender_chord_on
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) (xS sbar : ℝ) :
    ∀ x ∈ Set.Icc xS (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ ≤ s₂ →
          |p.F x s₂ - p.F x s₁| ≤ p.δ * (s₂ - s₁) := by
  intro x _ s₁ _ s₂ _ hs
  have hδ : (0 : ℝ) ≤ p.δ := le_of_lt p.δ_mem.1
  have hval : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
    rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
  rw [hval]
  exact le_of_eq (abs_of_nonneg (mul_nonneg hδ (by linarith)))

namespace StandardComplianceLocalCoreCertificate

-- Round BG (2026-10-06): the goal-2 wrapper `goal2_dominance_of_affine` that stood here was
-- deleted. Goal 2 mentions no transition, and the wrapper's body was
-- `goal2_dominance_generalF p C` with its `hF` and `0 ≤ g_T` binders unread; the witnesses
-- call `goal2_dominance_generalF` (`Theory/Certificates/GeneralFDischargers.lean`) directly.

/-- **Affine recovery for Goal 3 (Rule 5).** At `d = p.δ` the general-`F`
shock theorem reproduces the affine one from the certificate's own Sender
margin field (the Target-leg rate `dlo` and its margin left the certificate in
round BJ1.4, 2026-10-07). `hAdj` is discharged from `hF` rather than assumed, which is what makes
the swap a weakening. -/
theorem goal3_shock_of_affine
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ∃ N : ℕ, ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock N) n ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N)) :=
  goal3_shock_generalF p C
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF)

/-- **Affine recovery for all three goals (Rule 5).** At `d = p.δ` the
general-`F` bundle reproduces the affine one, consuming only the certificate's
own `hS_margin` field (its former `hT_loss_margin` field was deleted in round
BJ1.4, 2026-10-07, as read by no goal); `hAdj` is derived from `hF`, not
assumed. Every existing affine witness travels this route unchanged. -/
theorem three_goals_of_affine
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1)
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ, ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock N) n ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N)) :=
  three_goals_generalF p C
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF)

/-- **Affine recovery for the full conclusion set (Rule 5 / Rule 13).** At
`d = p.δ` the general-`F` bundle reproduces
`three_goals_local_uniform_starts` over the general-`F` trajectory objects,
consuming only the certificate's own margin fields; `hAdj` is *derived* from
`hF`, not assumed. Every existing affine witness travels this route unchanged,
and at an affine economy the two trajectory families coincide pointwise by
`dynamicTopLockInPath_eq_pathF_of_affine` and `shockPath_eq_shockPathF_of_affine`. -/
theorem three_goals_local_uniform_starts_full_of_affine
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                            (p.shockPathF x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) :=
  three_goals_local_uniform_starts_generalF p C
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF)

end StandardComplianceLocalCoreCertificate

end Params
end AbstractGame

end

end Sanctions

/-! ## Axiom hygiene (Rule 10) -/

#print axioms Sanctions.AbstractGame.Params.affine_transitionChordPack
#print axioms Sanctions.AbstractGame.Params.strictAdjustment_of_affine_via_chord
#print axioms Sanctions.AbstractGame.Params.transitionStateLipschitzWith_of_affine
#print axioms Sanctions.AbstractGame.Params.joint_state_chord_of_stage_chord_and_affine
#print axioms Sanctions.AbstractGame.Params.affine_transition_increasingDifferences
#print axioms
  Sanctions.AbstractGame.Params.Target_combined_chord_of_decomposition_lowerChord_affine
#print axioms Sanctions.AbstractGame.Params.affine_sender_chord_on
#print axioms
  Sanctions.AbstractGame.Params.OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on_recovered
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.goal3_shock_of_affine
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.three_goals_of_affine
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts_full_of_affine
