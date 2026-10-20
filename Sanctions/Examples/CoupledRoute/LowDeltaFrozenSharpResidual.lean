/-
Sanctions/Examples/CoupledRoute/LowDeltaFrozenSharpResidual.lean

Sharp continuum Sender-row residual at the frozen static-policy center.

The earlier residual bound used the generic norm-over-window modulus.  The
piecewise stage calculation supplies the exact smaller state-Lipschitz
constant `3272533/807360` for the smoothed frozen Sender center.  Propagating
that constant through the existing `1/100` transition displacement and
Sender discount `1/2` gives the exact bound `3272533/161472000`.

No numerical convergence premise or new model assumption is used.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaFrozenResidual
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenStageLipschitz

namespace Sanctions
namespace Examples

open Set
open AbstractGame
open BoundedContinuousFunction

/-- A feasible maximizer realizes the supremum of its image. -/
private theorem lowDeltaSharp_sSup_image_eq_of_mem_isMaxOn
    {f : ℝ → ℝ} {K : Set ℝ} {a : ℝ}
    (ha : a ∈ K) (h : IsMaxOn f K a) :
    sSup (f '' K) = f a := by
  have hbdd : BddAbove (f '' K) := by
    refine ⟨f a, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact h hz
  have hne : (f '' K).Nonempty := ⟨f a, ⟨a, ha, rfl⟩⟩
  apply le_antisymm
  · exact csSup_le hne (by
      rintro _ ⟨z, hz, rfl⟩
      exact h hz)
  · exact le_csSup hbdd ⟨a, ha, rfl⟩

/-- Sharp one-step movement of the smoothed frozen Sender center. -/
theorem lowDeltaFrozenSenderCenter_transition_sharp_le
    (x : ↥(Sanctions.S : Set ℝ))
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter
          (Sanctions.clipS' (lowDeltaParams.F x.val s)) -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter x|
      ≤ (3272533 / 80736000 : ℝ) := by
  rw [abs_sub_comm]
  calc
    _ ≤ (3272533 / 807360 : ℝ) *
        dist (Sanctions.clipS' (lowDeltaParams.F x.val s)) x :=
      lowDeltaFrozenSenderSmear_sharp_valueLipschitz _ _
    _ ≤ (3272533 / 807360 : ℝ) * (1 / 100) := by
      exact mul_le_mul_of_nonneg_left
        (lowDelta_transition_dist_state_le x s hs) (by norm_num)
    _ = (3272533 / 80736000 : ℝ) := by norm_num

/-- Sharp frozen-versus-actual Sender-integrand residual at the static Target
policy. -/
theorem lowDeltaFrozenSender_integrand_residual_sharp
    (x : ↥(Sanctions.S : Set ℝ))
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |lowDeltaParams.integrandS lowDeltaStaticTargetPolicy
          (fun y => Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter y) (x.val, s) -
        (mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s +
          (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter x)|
      ≤ (3272533 / 161472000 : ℝ) := by
  have h := lowDeltaFrozenSenderCenter_transition_sharp_le x s hs
  simp only [Params.integrandS, lowDeltaParams_U_S,
    lowDeltaParams_β_S]
  rw [show
      mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s +
          (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter
              (Sanctions.clipS' (lowDeltaParams.F x.val s)) -
        (mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s +
          (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter x) =
        (1 / 2) *
          (Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter
              (Sanctions.clipS' (lowDeltaParams.F x.val s)) -
            Sanctions.movAvgBCF lowDeltaH_pos
              lowDeltaFrozenSenderCenter x) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith

/-- Sharp pointwise Sender Bellman residual at the frozen center and static
Target policy. -/
theorem lowDeltaFrozenSenderCenter_bellman_residual_pointwise_sharp
    (x : ↥(Sanctions.S : Set ℝ)) :
    |lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaFrozenSenderCenter x -
        lowDeltaFrozenSenderCenter x|
      ≤ (3272533 / 161472000 : ℝ) := by
  let f : ℝ → ℝ := fun s =>
    lowDeltaParams.integrandS lowDeltaStaticTargetPolicy
      (fun y => Sanctions.movAvgBCF lowDeltaH_pos
        lowDeltaFrozenSenderCenter y) (x.val, s)
  let g : ℝ → ℝ := lowDeltaFrozenSenderObjective x
  have hf_bdd : BddAbove (f '' Sanctions.I) := by
    dsimp only [f]
    exact lowDeltaParams.integrandS_image_bddAbove
      lowDeltaStaticTargetPolicy_continuous
      (Sanctions.movAvgBCF lowDeltaH_pos
        lowDeltaFrozenSenderCenter).continuous x.val
  have hgmax : IsMaxOn g Sanctions.I
      (lowDeltaStaticSenderPolicy x.val) := by
    simpa only [g] using lowDeltaFrozenSenderObjective_isMaxOn x
  have hg_bdd : BddAbove (g '' Sanctions.I) := by
    refine ⟨g (lowDeltaStaticSenderPolicy x.val), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hgmax hs
  have hsup :
      |sSup (f '' Sanctions.I) - sSup (g '' Sanctions.I)|
        ≤ (3272533 / 161472000 : ℝ) := by
    apply Sanctions.abs_sSup_image_sub_sSup_image_le
      (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
      (hf_bdd := hf_bdd) (hg_bdd := hg_bdd)
    intro s hs
    simpa only [f, g, lowDeltaFrozenSenderObjective] using
      lowDeltaFrozenSender_integrand_residual_sharp x s hs
  have hgSup :
      sSup (g '' Sanctions.I) =
        g (lowDeltaStaticSenderPolicy x.val) :=
    lowDeltaSharp_sSup_image_eq_of_mem_isMaxOn
      (lowDeltaStaticSenderPolicy_mem x.val) hgmax
  change
    |sSup (f '' Sanctions.I) - lowDeltaFrozenSenderCenter x|
      ≤ (3272533 / 161472000 : ℝ)
  rw [lowDeltaFrozenSenderCenter_eq]
  change
    |sSup (f '' Sanctions.I) -
      g (lowDeltaStaticSenderPolicy x.val)|
        ≤ (3272533 / 161472000 : ℝ)
  rw [← hgSup]
  exact hsup

/-- Sup-norm form of the sharp frozen-center Sender residual. -/
theorem lowDeltaFrozenSenderCenter_bellman_residual_sharp :
    dist
        (lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaFrozenSenderCenter)
        lowDeltaFrozenSenderCenter
      ≤ (3272533 / 161472000 : ℝ) := by
  rw [BoundedContinuousFunction.dist_le (by norm_num)]
  intro x
  rw [Real.dist_eq]
  exact lowDeltaFrozenSenderCenter_bellman_residual_pointwise_sharp x

end Examples
end Sanctions
