/-
Sanctions/Examples/QuadBumpSenderCone.lean

**The first instantiation of the general-`F` Sender lower-slope cone.**

`bellmanS_BCF_preserves_lowerSlopeCone_generalF`
(`Theory/Bellman/SenderLowerSlopeCone.lean`) drops the affine hypothesis `hF`
from its twin `bellmanS_BCF_preserves_lowerSlopeCone` and replaces the separated
pair -- stage state chord `m` plus the sub-solution inequality
`g <= m + beta_S*g*(1-delta)` -- by a single **joint** state chord in existing
primitives.  Until this file it had no consumer and no instance, while its affine
twin had two.

This file supplies the instance at `qbParams` (`Examples/QuadBumpCertWitnessMS.lean`),
whose transition

  `F(x,s) = x/2 + s/2 + (1/100)*(s - x)^2*(1 - s)`

is proved genuinely non-affine (`qbParams_F_ne_affine`).  So the general theorem's
first instance is a **non-affine** one, not a restatement of the affine case.

## What is proved

* `quadBumpF_state_chord_eq` -- the exact state-chord factorisation of the
  quadratic-bump transition on the feasible square.
* `quadBumpF_state_lowerChord` -- raising the inherited political state by `D`
  raises next period's state by at least `(12/25)*D`, at every feasible sanction.
  (The true infimum of the chord factor is `99/200 = 0.495`, attained as
  `y1, y2 -> 0` at `s = 1/2`; `12/25 = 0.48` is the slack bound the proof uses.)
* `qbParams_joint_state_chord` -- the joint chord at the derived leader policy
  `qbAlpha == 0`, at slope `g = 15/4`.  The stage payoff contributes `s + 3 >= 3`
  per unit of state and the discounted transition contributes at least
  `beta_S*g*(12/25) = 9/10`, so the joint chord clears `15/4` with margin `3/20`.
* `qbParams_bellmanS_preserves_cone` -- hence the Sender Bellman operator carries
  the cone `{V | V rises at rate at least 15/4 in the state}` into itself at this
  non-affine economy.
* `qbParams_cone_preserved_at_derived_policy` -- the same statement at the
  *derived* leader policy `qbCertClass.alpha_on`, not at a hand-picked constant.

`g = 15/4` is not knife-edge.  The largest admissible slope here is exactly `4`
(binding at `s = 0`, where the bump vanishes and the transition is the affine
half-blend); `41/10` already fails, and at `15/4` the minimum of the chord's
right-hand side per unit of state is `12601/3200 ~ 3.938`.

## Rule compliance

* **Rule 1** -- `qbAlpha == 0` is not posited.  `qbCert_zero_isMaxOn_joint`
  (`QuadBumpCertWitnessMS.lean`) proves full defiance maximises the joint Target
  integrand, and `qbCert_alpha_on_eq_zero` proves the *derived* leader policy
  `qbCertClass.alpha_on V_T V_S` equals it for every carrier pair.
* **Rule 3** -- no new assumption surface: `g` is a theorem-bound scalar and every
  hypothesis is discharged from `qbParams`'s own data.
* **Rule 5** -- all content is a specialisation of the parametric theorem in
  `Theory/Bellman/SenderLowerSlopeCone.lean`; nothing is re-proved by hand.
* **Rule 9** -- an existence certificate: the general-`F` cone preserver is
  inhabited, at a non-affine economy.
* **Rule 22** -- no `hF` anywhere, and the transition is proved non-affine.
-/

import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Theory.Bellman.SenderLowerSlopeCone

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The state-side chord of the quadratic-bump transition -/

/-- **Exact state-chord factorisation on the feasible square.**  The affine part
contributes `1/2` per unit of state; the transience bump contributes the
state-dependent correction `(1/100)*(1-s)*(y1+y2-2s)`, which is positive when the
sanction sits below the pair's midpoint and negative when it sits above. -/
theorem quadBumpF_state_chord_eq {x₁ x₂ s : ℝ}
    (hx₁ : x₁ ∈ Set.Icc (0:ℝ) 1) (hx₂ : x₂ ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) :
    quadBumpF x₂ s - quadBumpF x₁ s
      = (x₂ - x₁) * (1/2 + 1/100 * (1 - s) * (x₁ + x₂ - 2*s)) := by
  rw [quadBumpF_sq hx₁ hs, quadBumpF_sq hx₂ hs]
  ring

/-- **State-side lower chord of the quadratic-bump transition.**  A deeper
inherited political state carries forward at rate at least `12/25`, uniformly in
the sanction.  The bump can subtract at most `2/100` from the affine rate `1/2`,
because `(1-s)` is at most one and the midpoint gap `y1+y2-2s` is at least `-2`. -/
theorem quadBumpF_state_lowerChord {x₁ x₂ s : ℝ}
    (hx₁ : x₁ ∈ Set.Icc (0:ℝ) 1) (hx₂ : x₂ ∈ Set.Icc (0:ℝ) 1)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (hle : x₁ ≤ x₂) :
    12/25 * (x₂ - x₁) ≤ quadBumpF x₂ s - quadBumpF x₁ s := by
  have hΔ : (0:ℝ) ≤ x₂ - x₁ := sub_nonneg.mpr hle
  have hbr : (12/25 : ℝ) ≤ 1/2 + 1/100 * (1 - s) * (x₁ + x₂ - 2*s) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
        (show (0:ℝ) ≤ x₁ + x₂ - 2*s + 2 by linarith [hx₁.1, hx₂.1, hs.2]),
      hs.1]
  rw [quadBumpF_state_chord_eq hx₁ hx₂ hs]
  linarith [mul_le_mul_of_nonneg_left hbr hΔ]

/-! ## 2. The derived leader policy, as a named function -/

/-- Full defiance.  This is the *derived* leader policy at `qbParams`, not a
posit: see `qbCert_α_on_eq_qbAlpha` immediately below. -/
def qbAlpha : ℝ → ℝ := fun _ => 0

theorem qbAlpha_continuous : Continuous qbAlpha := continuous_const

/-- **Rule 1.**  The certificate's derived leader policy at `qbParams` *is*
`qbAlpha`, at every carrier pair -- a restatement of `qbCert_α_on_eq_zero`, which
rests on `qbCert_zero_isMaxOn_joint` (full defiance maximises the joint Target
integrand). -/
theorem qbCert_α_on_eq_qbAlpha (V_T : qbCertClass.CarrierT)
    (V_S : qbCertClass.CarrierS) :
    qbCertClass.α_on V_T V_S = qbAlpha :=
  qbCert_α_on_eq_zero V_T V_S

/-! ## 3. The joint state chord, and the cone instance -/

/-- **The joint state chord at `qbParams`, at slope `g = 15/4`.**

Raising the inherited political state by `D` raises the Sender's stage payoff by
`(s+3)*D >= 3*D` and the discounted value of the induced rise in next period's
state by at least `beta_S * (15/4) * (12/25) * D = (9/10)*D`; together that is
`(39/10)*D`, which covers `(15/4)*D`.

No hypothesis constrains `F` on its own -- the transition enters only through this
chord and, inside the general theorem, through `F_mono_x`, which `Params` already
carries. -/
theorem qbParams_joint_state_chord :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (15/4 : ℝ) * (y₂ - y₁)
        ≤ (qbParams.U_S y₂ (qbAlpha y₂) s - qbParams.U_S y₁ (qbAlpha y₁) s)
          + qbParams.β_S * (15/4) * (qbParams.F y₂ s - qbParams.F y₁ s) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have hΔ : (0:ℝ) ≤ y₂ - y₁ := sub_nonneg.mpr hle
  have hU : qbParams.U_S y₂ (qbAlpha y₂) s - qbParams.U_S y₁ (qbAlpha y₁) s
      = (s + 3) * (y₂ - y₁) := by
    show eecU_S y₂ 0 s - eecU_S y₁ 0 s = (s + 3) * (y₂ - y₁)
    unfold eecU_S
    ring
  have hFc : (12/25 : ℝ) * (y₂ - y₁) ≤ qbParams.F y₂ s - qbParams.F y₁ s :=
    quadBumpF_state_lowerChord hy₁ hy₂ hs hle
  rw [hU, qbParams_β_S]
  nlinarith [hFc, hΔ, mul_nonneg hs.1 hΔ]

/-- **FIRST INSTANCE of the general-`F` Sender cone preserver.**  At the
non-affine economy `qbParams`, the Sender Bellman operator carries the lower-slope
cone at `g = 15/4` into itself. -/
theorem qbParams_bellmanS_preserves_cone
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) (15/4)) :
    LowerSlopeOnValueOn (qbParams.bellmanS_BCF qbAlpha qbAlpha_continuous V)
      (Set.Icc (0:ℝ) 1) (15/4) :=
  qbParams.bellmanS_BCF_preserves_lowerSlopeCone_generalF qbAlpha_continuous
    qbParams_joint_state_chord hV

/-- and the same at the **derived** leader policy, so nothing here rests on a
hand-chosen constant strategy (Rule 1). -/
theorem qbParams_cone_preserved_at_derived_policy
    (V_T : qbCertClass.CarrierT) (V_S : qbCertClass.CarrierS)
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) (15/4)) :
    LowerSlopeOnValueOn
      (qbParams.bellmanS_BCF (qbCertClass.α_on V_T V_S)
        (qbCertClass.α_on_continuous V_T V_S) V) (Set.Icc (0:ℝ) 1) (15/4) := by
  rw [WitnessKit.bellmanS_BCF_congr_α (qbCert_α_on_eq_qbAlpha V_T V_S)
    (qbCertClass.α_on_continuous V_T V_S) qbAlpha_continuous V]
  exact qbParams_bellmanS_preserves_cone hV

/-! ## 4. The constructed Sender value at `qbParams` lies in the cone

Requires `V_S_mem_lowerSlopeCone_generalF` (`Theory/Bellman/SenderLowerSlopeCone.lean`). -/

/-- **The constructed Sender Bellman fixed point at the non-affine economy has
state slope at least `15/4`.**  Existence is not hypothesised: `qbParams.V_S` is by
definition the Banach fixed point of `bellmanS_BCF`, and cone membership is derived
by trapping the iteration in the closed cone. -/
theorem qbParams_V_S_mem_lowerSlopeCone :
    LowerSlopeOnValueOn (qbParams.V_S qbAlpha qbAlpha_continuous)
      (Set.Icc (0:ℝ) 1) (15/4) :=
  qbParams.V_S_mem_lowerSlopeCone_generalF qbAlpha_continuous
    qbParams_joint_state_chord

/-- and it is therefore not the zero function: the Sender's equilibrium
continuation value at this non-affine economy strictly rewards deeper
entrenchment. -/
theorem qbParams_V_S_ne_zero : qbParams.V_S qbAlpha qbAlpha_continuous ≠ 0 := by
  intro hzero
  have hcone := qbParams_V_S_mem_lowerSlopeCone
  rw [hzero] at hcone
  exact zero_not_mem_lowerSlopeCone (by norm_num) hcone

end -- noncomputable section

/-! ## Axiom hygiene (Rule 10) -/

#print axioms quadBumpF_state_lowerChord
#print axioms qbCert_α_on_eq_qbAlpha
#print axioms qbParams_joint_state_chord
#print axioms qbParams_bellmanS_preserves_cone
#print axioms qbParams_cone_preserved_at_derived_policy

end Examples

end Sanctions
