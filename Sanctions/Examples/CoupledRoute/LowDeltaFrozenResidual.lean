/-
Sanctions/Examples/CoupledRoute/LowDeltaFrozenResidual.lean

Exact first residual estimates around the Banach-constructed frozen-transition
center.

The low-adjustment affine law moves the inherited state by at most `1/100`
in one period.  Combining that identity with the exact smoothing budgets from
`LowDeltaFrozenReferenceCenter` yields a fully formal Sender-row residual at
the static Target policy.  This is a genuine Bellman supremum estimate, not a
finite-grid or numerical-iteration claim.

The theorem here deliberately keeps the Target policy fixed at the proved
static Stackelberg policy.  Replacing it by the realized dynamic Target policy
is a separate coupled-policy perturbation obligation.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaFrozenReferenceCenter

namespace Sanctions
namespace Examples

open Set
open AbstractGame
open BoundedContinuousFunction

/-- A feasible maximizer realizes the supremum of its image. -/
private theorem lowDelta_sSup_image_eq_of_mem_isMaxOn
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

/-! ## Exact one-step displacement -/

/-- Under the low-adjustment affine law, every feasible sanction moves a
physical state by at most `1/100`. -/
theorem lowDelta_transition_dist_state_le
    (x : ↥(Sanctions.S : Set ℝ))
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    dist (Sanctions.clipS' (lowDeltaParams.F x.val s)) x ≤ 1 / 100 := by
  have hF : lowDeltaParams.F x.val s ∈ Sanctions.S :=
    lowDeltaParams.F_mem x.val s x.property hs
  have hsx : |s - x.val| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [hs.1, hs.2, x.property.1, x.property.2]
  rw [Subtype.dist_eq, Real.dist_eq,
    Sanctions.clipS'_val_eq_of_mem hF,
    lowDeltaParams_F]
  unfold Sanctions.AbstractGame.affineF
  rw [show
      (1 - (1 / 100 : ℝ)) * x.val + (1 / 100) * s - x.val =
        (1 / 100) * (s - x.val) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  nlinarith

/-- The smoothed frozen Target center changes by at most `2` over a single
low-adjustment transition. -/
theorem lowDeltaFrozenTargetCenter_transition_le
    (x : ↥(Sanctions.S : Set ℝ))
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenTargetCenter
          (Sanctions.clipS' (lowDeltaParams.F x.val s)) -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenTargetCenter x|
      ≤ 2 := by
  calc
    _ ≤ 200 *
        dist (Sanctions.clipS' (lowDeltaParams.F x.val s)) x :=
      lowDeltaFrozenTargetCenter_smear_lipschitz _ _
    _ ≤ 200 * (1 / 100) := by
      exact mul_le_mul_of_nonneg_left
        (lowDelta_transition_dist_state_le x s hs) (by norm_num)
    _ = 2 := by norm_num

/-- The smoothed frozen Sender center changes by at most `523/1600` over a
single low-adjustment transition. -/
theorem lowDeltaFrozenSenderCenter_transition_le
    (x : ↥(Sanctions.S : Set ℝ))
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter
          (Sanctions.clipS' (lowDeltaParams.F x.val s)) -
        Sanctions.movAvgBCF lowDeltaH_pos lowDeltaFrozenSenderCenter x|
      ≤ 523 / 1600 := by
  calc
    _ ≤ (523 / 16) *
        dist (Sanctions.clipS' (lowDeltaParams.F x.val s)) x :=
      lowDeltaFrozenSenderCenter_smear_lipschitz _ _
    _ ≤ (523 / 16) * (1 / 100) := by
      exact mul_le_mul_of_nonneg_left
        (lowDelta_transition_dist_state_le x s hs) (by norm_num)
    _ = 523 / 1600 := by norm_num

/-! ## Frozen-versus-actual Sender Bellman row -/

/-- The actual low-adjustment Sender integrand at the frozen center is
uniformly within `523/3200` of its frozen-transition version. -/
theorem lowDeltaFrozenSender_integrand_residual
    (x : ↥(Sanctions.S : Set ℝ))
    (s : ℝ) (hs : s ∈ Sanctions.I) :
    |lowDeltaParams.integrandS lowDeltaStaticTargetPolicy
          (fun y => Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter y) (x.val, s) -
        (mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s +
          (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos
            lowDeltaFrozenSenderCenter x)|
      ≤ 523 / 3200 := by
  have h := lowDeltaFrozenSenderCenter_transition_le x s hs
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

/-- The frozen Sender objective whose continuation state is held at the
current inherited state. -/
noncomputable def lowDeltaFrozenSenderObjective
    (x : ↥(Sanctions.S : Set ℝ)) (s : ℝ) : ℝ :=
  mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s +
    (1 / 2) * Sanctions.movAvgBCF lowDeltaH_pos
      lowDeltaFrozenSenderCenter x

/-- The exact static Sender policy maximizes the frozen Sender objective. -/
theorem lowDeltaFrozenSenderObjective_isMaxOn
    (x : ↥(Sanctions.S : Set ℝ)) :
    IsMaxOn (lowDeltaFrozenSenderObjective x) Sanctions.I
      (lowDeltaStaticSenderPolicy x.val) := by
  rw [isMaxOn_iff]
  intro s hs
  have hU :
      mwU_S x.val (lowDeltaStaticTargetPolicy x.val) s ≤
        mwU_S x.val (lowDeltaStaticTargetPolicy x.val)
          (mwσ x.val (lowDeltaStaticTargetPolicy x.val)) := by
    exact
      (mwσ_isMaxOn x.val (lowDeltaStaticTargetPolicy x.val)) hs
  unfold lowDeltaFrozenSenderObjective lowDeltaStaticSenderPolicy
  exact add_le_add hU (le_refl _)

/-- **Exact frozen-center Sender residual at the static Target policy.**
The actual shocked Sender Bellman supremum differs from the
Banach-constructed frozen reference value by at most `523/3200` pointwise. -/
theorem lowDeltaFrozenSenderCenter_bellman_residual_pointwise
    (x : ↥(Sanctions.S : Set ℝ)) :
    |lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaFrozenSenderCenter x -
        lowDeltaFrozenSenderCenter x|
      ≤ 523 / 3200 := by
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
        ≤ 523 / 3200 := by
    apply Sanctions.abs_sSup_image_sub_sSup_image_le
      (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
      (hf_bdd := hf_bdd) (hg_bdd := hg_bdd)
    intro s hs
    simpa only [f, g, lowDeltaFrozenSenderObjective] using
      lowDeltaFrozenSender_integrand_residual x s hs
  have hgSup :
      sSup (g '' Sanctions.I) =
        g (lowDeltaStaticSenderPolicy x.val) :=
    lowDelta_sSup_image_eq_of_mem_isMaxOn
      (lowDeltaStaticSenderPolicy_mem x.val) hgmax
  change
    |sSup (f '' Sanctions.I) - lowDeltaFrozenSenderCenter x|
      ≤ 523 / 3200
  rw [lowDeltaFrozenSenderCenter_eq]
  change
    |sSup (f '' Sanctions.I) -
      g (lowDeltaStaticSenderPolicy x.val)| ≤ 523 / 3200
  rw [← hgSup]
  exact hsup

/-- Sup-norm form of the exact frozen-center Sender residual. -/
theorem lowDeltaFrozenSenderCenter_bellman_residual :
    dist
        (lowDeltaShocked.bellmanS_shock
          lowDeltaStaticTargetPolicy
          lowDeltaStaticTargetPolicy_continuous
          lowDeltaFrozenSenderCenter)
        lowDeltaFrozenSenderCenter
      ≤ 523 / 3200 := by
  rw [BoundedContinuousFunction.dist_le (by norm_num)]
  intro x
  rw [Real.dist_eq]
  exact lowDeltaFrozenSenderCenter_bellman_residual_pointwise x

end Examples
end Sanctions
