/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.CoupledRoute.LowDeltaCarrierLocalEquilibriumFrontier
import Sanctions.Examples.CoupledRoute.LowDeltaStaticPolicyTargetSelectorFrontier

/-!
# The `69/200` Target localization cannot be tightened enough to close the packet

**Rule-11 refutation (2026-07-28).**  The coupled low-adjustment route needs the
Target-policy centre-displacement bound tightened from the proved
`69/200 = 0.345` down inside the proved Sender residual slack
`lowDeltaCarrierLocalSenderPolicySlack = 4.976989…e-3`, a factor of `69.32`
(`gate2_tightening_factor`).  This file proves that cannot be done by
sharpening the existing derivation.

## Two independent floors

**(A) The inequality itself admits a large solution.**
`gate2_localization_floor` exhibits, at the state `x = 1`, a *feasible* action
satisfying the project's own `LowDeltaStaticPolicyTargetLocalizationInequality`
whose displacement from the static policy is exactly `3447/10000`.  So no
reworking of the derivation *from that inequality* can produce any radius below
`0.3447` — and `gate2_localization_floor_gt_slack` records that this floor
exceeds `69` times the available slack.  The published `69/200` overshoots the
exact root of the governing quadratic by only `0.07%`
(`gate2_quadratic_satisfied_at_3447`, `gate2_quadratic_violated_at_69_200`):
**the final step has essentially no slop left to recover.**

**(B) A modulus-only argument cannot localize within the slack.**
`gate2_modulus_information_floor` takes the extremal perturbation
`-(a-c)^2 + L*|a-c|`, whose deviation from the static quadratic is *exactly*
the shape of the project's continuation-error bound (`gate2Counter_deviation`),
and shows it has **two** global maximizers at `c ± L/2`, both feasible, with
`L/2` more than ten times the slack.  Hence no argument whose only input is
"the Target value is Lipschitz with the stated modulus" can succeed, whatever
the constant is polished to.  `gate2_required_target_modulus` records how far
that modulus would have to fall even granting an ideal first-order gain.

## Why this is a route refutation, not a claim about the true displacement

Nothing here shows the *actual* equilibrium displacement is large.  What is
refuted is that **this derivation, against this packet**, can reach the target.
The distinction matters: the slop in `69/200` is real but bounded, while the
requirement is not.

The constructive reading is to **enlarge the slack rather than sharpen the
localization**.  The slack is linear in the validation packet's radii, and the
packet `r_T = 4/5, r_S = 3/20` is *already documented in
`LowDeltaCarrierLocalEquilibriumFrontier` as a retained diagnostic* whose former
conditional-existence wrapper "exposed numerical policy bounds that were not
derived from the economy" and was removed.  That file names the replacement
route: derive the radii analytically from the actual residual vector and the
symbolic Perov matrix, via `Foundations/ValidatedLocalPerovOnCarriers`.

So the target this refutation kills is one the project had already superseded
architecturally.  Re-deriving the radii is the intended path; polishing
`69/200` against the old diagnostic packet is not.

No new assumption, parameter field, or carrier condition is introduced here.
-/

namespace Sanctions
namespace Examples

open Set

noncomputable section

/-- Constant term of the refined localization quadratic `q^2 ≤ C + L q`. -/
noncomputable def gate2C : ℝ :=
  2 * ((16362665 / 4046689 : ℝ) / 120) +
    (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) *
      (2 * ((16362665 / 4046689 : ℝ) / 120))

/-- Linear coefficient of the refined localization quadratic. -/
noncomputable def gate2L : ℝ :=
  (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) * (5 / 12)

theorem gate2L_nonneg : (0 : ℝ) ≤ gate2L := by norm_num [gate2L]

/-! ## (A) The published `69/200` is already the sharp root of its own quadratic -/

/-- The refined quadratic inequality is still SATISFIED at `q = 3447/10000`. -/
theorem gate2_quadratic_satisfied_at_3447 :
    (3447 / 10000 : ℝ) ^ 2 ≤ gate2C + gate2L * (3447 / 10000) := by
  norm_num [gate2C, gate2L]

/-- ... and violated at `69/200`.  So the published constant overshoots the
exact root by less than `4/10000`. -/
theorem gate2_quadratic_violated_at_69_200 :
    gate2C + gate2L * (69 / 200 : ℝ) < (69 / 200 : ℝ) ^ 2 := by
  norm_num [gate2C, gate2L]

theorem lowDeltaStaticTargetPolicy_one' :
    lowDeltaStaticTargetPolicy 1 = (63 / 116 : ℝ) := by
  rw [lowDeltaStaticTargetPolicy_eq]
  norm_num [max_eq_right]

/-- Any nonnegative `q` satisfying the quadratic gives a point at distance `q`
from the static policy that satisfies the project's localization inequality. -/
theorem gate2_localization_floor_general (x α q : ℝ)
    (hα : lowDeltaStaticTargetPolicy x = α) (hq : 0 ≤ q)
    (hquad : q ^ 2 ≤ gate2C + gate2L * q) :
    LowDeltaStaticPolicyTargetLocalizationInequality x (α + q) := by
  unfold LowDeltaStaticPolicyTargetLocalizationInequality
  rw [hα, show α + q - α = q by ring, abs_of_nonneg hq]
  have hexp :
      gate2C + gate2L * q =
        2 * ((16362665 / 4046689 : ℝ) / 120) +
          (9 / 10 : ℝ) * (3855250 / 142269) * (1 / 100) *
            (2 * ((16362665 / 4046689 : ℝ) / 120) + (5 / 12 : ℝ) * q) := by
    unfold gate2C gate2L; ring
  linarith [hquad, hexp.symm.le, hexp.le]

/-- **Localization floor.**  At the state `x = 1` the project's own refined
localization inequality is satisfied by a feasible action whose displacement
from the static policy is `3447/10000`.  Hence no reworking of the *derivation*
from that inequality can produce a radius below `3447/10000`. -/
theorem gate2_localization_floor :
    ∃ a : ℝ, a ∈ Sanctions.I ∧
      LowDeltaStaticPolicyTargetLocalizationInequality 1 a ∧
      |a - lowDeltaStaticTargetPolicy 1| = 3447 / 10000 := by
  refine ⟨63 / 116 + 3447 / 10000, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · exact
      gate2_localization_floor_general 1 (63 / 116) (3447 / 10000)
        lowDeltaStaticTargetPolicy_one' (by norm_num)
        gate2_quadratic_satisfied_at_3447
  · rw [lowDeltaStaticTargetPolicy_one',
      show (63 / 116 + 3447 / 10000 : ℝ) - 63 / 116 = 3447 / 10000 by ring,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3447 / 10000)]

/-- The floor is more than 69 times the available Sender residual slack. -/
theorem gate2_localization_floor_gt_slack :
    69 * lowDeltaCarrierLocalSenderPolicySlack < 3447 / 10000 := by
  rw [lowDeltaCarrierLocalSenderPolicySlack_eq]
  norm_num

/-! ## (B) Even the idealised first-order argument is short by a factor > 10 -/

/-- The modulus-only extremal objective: an exact `lam`-Lipschitz perturbation
of the static quadratic. -/
noncomputable def gate2CounterObjective (c lam a : ℝ) : ℝ :=
  -(a - c) ^ 2 + lam * |a - c|

/-- Its deviation from the static quadratic is exactly `lam * |a - c|` —
precisely the shape of the project's continuation-error bound. -/
theorem gate2Counter_deviation (c lam a : ℝ) (hlam : 0 ≤ lam) :
    |gate2CounterObjective c lam a - (-(a - c) ^ 2)| = lam * |a - c| := by
  simp only [gate2CounterObjective]
  rw [show -(a - c) ^ 2 + lam * |a - c| - -(a - c) ^ 2 = lam * |a - c| by ring,
    abs_mul, abs_abs, abs_of_nonneg hlam]

theorem gate2Counter_le (c lam a : ℝ) :
    gate2CounterObjective c lam a ≤ lam ^ 2 / 4 := by
  have h := sq_nonneg (|a - c| - lam / 2)
  have hsq : |a - c| ^ 2 = (a - c) ^ 2 := sq_abs _
  simp only [gate2CounterObjective]
  nlinarith

theorem gate2Counter_right_eq (c lam : ℝ) (hlam : 0 ≤ lam) :
    gate2CounterObjective c lam (c + lam / 2) = lam ^ 2 / 4 := by
  simp only [gate2CounterObjective]
  rw [show c + lam / 2 - c = lam / 2 by ring,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ lam / 2)]
  ring

theorem gate2Counter_left_eq (c lam : ℝ) (hlam : 0 ≤ lam) :
    gate2CounterObjective c lam (c - lam / 2) = lam ^ 2 / 4 := by
  simp only [gate2CounterObjective]
  rw [show c - lam / 2 - c = -(lam / 2) by ring, abs_neg,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ lam / 2)]
  ring

theorem gate2Counter_right_isMaxOn (c lam : ℝ) (hlam : 0 ≤ lam) :
    IsMaxOn (gate2CounterObjective c lam) Sanctions.I (c + lam / 2) := by
  refine isMaxOn_iff.mpr ?_
  intro a _
  rw [gate2Counter_right_eq c lam hlam]
  exact gate2Counter_le c lam a

theorem gate2Counter_left_isMaxOn (c lam : ℝ) (hlam : 0 ≤ lam) :
    IsMaxOn (gate2CounterObjective c lam) Sanctions.I (c - lam / 2) := by
  refine isMaxOn_iff.mpr ?_
  intro a _
  rw [gate2Counter_left_eq c lam hlam]
  exact gate2Counter_le c lam a

/-- **Modulus-information floor.**  A perturbation of the static quadratic
whose deviation obeys exactly the project's own continuation-error modulus
`gate2L * |a - c|` has TWO global maximizers on the feasible action interval,
each displaced by exactly `gate2L / 2` from the static optimum — and that
displacement exceeds ten times the available Sender residual slack. -/
theorem gate2_modulus_information_floor :
    IsMaxOn (gate2CounterObjective (1 / 2) gate2L) Sanctions.I
        (1 / 2 + gate2L / 2) ∧
      IsMaxOn (gate2CounterObjective (1 / 2) gate2L) Sanctions.I
        (1 / 2 - gate2L / 2) ∧
      (1 / 2 + gate2L / 2) ∈ Sanctions.I ∧
      (1 / 2 - gate2L / 2) ∈ Sanctions.I ∧
      (∀ a : ℝ,
        |gate2CounterObjective (1 / 2) gate2L a - (-(a - 1 / 2) ^ 2)| =
          gate2L * |a - 1 / 2|) ∧
      10 * lowDeltaCarrierLocalSenderPolicySlack < gate2L / 2 := by
  refine ⟨gate2Counter_right_isMaxOn _ _ gate2L_nonneg,
    gate2Counter_left_isMaxOn _ _ gate2L_nonneg,
    ⟨by norm_num [gate2L], by norm_num [gate2L]⟩,
    ⟨by norm_num [gate2L], by norm_num [gate2L]⟩,
    fun a => gate2Counter_deviation _ _ _ gate2L_nonneg, ?_⟩
  rw [lowDeltaCarrierLocalSenderPolicySlack_eq]
  norm_num [gate2L]

/-! ## (C) What the Target modulus would have to become -/

/-- Even granting the ideal factor-two first-order gain, the Target
continuation-value Lipschitz modulus would have to be smaller than one tenth
of the proved cellwise-sharp value `3855250/142269 ≈ 27.098`. -/
theorem gate2_required_target_modulus :
    2 * lowDeltaCarrierLocalSenderPolicySlack /
        ((9 / 10 : ℝ) * (1 / 100) * (5 / 12)) <
      (3855250 / 142269 : ℝ) / 10 := by
  rw [lowDeltaCarrierLocalSenderPolicySlack_eq]
  norm_num

/-- Sanity: the exact slack is the stated rational, and the required tightening
factor of `69/200` is `69.31...`, not seven orders of magnitude. -/
theorem gate2_tightening_factor :
    69 * lowDeltaCarrierLocalSenderPolicySlack < (69 / 200 : ℝ) ∧
      (69 / 200 : ℝ) < 70 * lowDeltaCarrierLocalSenderPolicySlack := by
  rw [lowDeltaCarrierLocalSenderPolicySlack_eq]
  constructor <;> norm_num

end

/-! ## Axiom hygiene (Rule 10)

Both floors and the tightening-factor sanity check depend only on the three
standard axioms. -/

#print axioms gate2_localization_floor
#print axioms gate2_localization_floor_gt_slack
#print axioms gate2_modulus_information_floor
#print axioms gate2_required_target_modulus
#print axioms gate2_tightening_factor

end Examples
end Sanctions
