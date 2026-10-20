import Sanctions.Examples.CoupledRoute.LowDeltaStaticPerturbation
import Sanctions.Examples.CoupledRoute.LowDeltaFrozenResidual

/-!
# Exact coupled-policy localization at the frozen low-delta center

The estimates here connect the forward-looking Sender selector and the reduced
Target objective to the exact static Stackelberg reference.  They expose the
constant budget transparently: the current coarse Target smoothing modulus is
formally sufficient for a valid bound, but not yet for a useful small local
carrier.  No numerical iteration is used.
-/

namespace Sanctions
namespace Examples

open Set
open Sanctions.AbstractGame

/-! ## Primitive Target sanction channel -/

/-- On physical states and feasible Target actions, the Target stage payoff is
globally one-Lipschitz in the realized sanction. -/
theorem lowDeltaTargetStage_abs_sub_le
    {x a s t : ℝ}
    (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    |mwU_T x a s - mwU_T x a t| ≤ |s - t| := by
  rcases hx with ⟨hx0, hx1⟩
  rcases ha with ⟨ha0, ha1⟩
  have hc :
      |(1 / 2 : ℝ) - (1 / 2) * a - x| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [show
      mwU_T x a s - mwU_T x a t =
        -(s - t) * ((1 / 2 : ℝ) - (1 / 2) * a - x) by
      unfold mwU_T
      ring,
    abs_mul, abs_neg]
  calc
    |s - t| * |(1 / 2 : ℝ) - (1 / 2) * a - x|
        ≤ |s - t| * 1 :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = |s - t| := by ring

/-! ## Generic exact coupled localization -/

/-- With Lipschitz continuation moduli `K_T` and `K_S`, the reduced dynamic
Target objective is uniformly close to the static Stackelberg objective plus
the action-independent continuation baseline at the inherited state.

The two error channels are exact:

* `K_S / 120` from the dynamic Sender policy displacement;
* `(9/10) * (K_T/100)` from the Target continuation displacement.

Witness-specific (Rule 22).  The former premises `0 ≤ K_T` and `0 ≤ K_S` are
dropped: they follow from the two Lipschitz bounds.
-/
theorem lowDelta_jointTarget_close_static_add
    (W_T W_S : SBCF) {K_T K_S : ℝ}
    (hWT : Sanctions.AbstractGame.Params.ValueLipschitzWith W_T K_T)
    (hWS : Sanctions.AbstractGame.Params.ValueLipschitzWith W_S K_S)
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I) :
    |lowDeltaParams.joint_T_top_integrand W_T W_S x a -
        (lowDeltaStaticTargetObjective x a +
          (9 / 10 : ℝ) * W_T ⟨x, hx⟩)| ≤
      K_S / 120 + (9 / 10 : ℝ) * (K_T / 100) := by
  have hKT : 0 ≤ K_T := hWT.nonneg
  let sd := lowDeltaParams.σ_dyn_top W_S x a
  let ss := mwσ x a
  let xs : ↥(Sanctions.S : Set ℝ) := ⟨x, hx⟩
  let yd := Sanctions.clipS' (lowDeltaParams.F x sd)
  have hsdmem : sd ∈ Sanctions.I :=
    lowDeltaParams.σ_dyn_top_mem_I W_S x a
  have hsPolicy :
      |sd - ss| ≤ K_S / 120 := by
    simpa [sd, ss] using
      lowDelta_sigmaDynTop_abs_sub_staticSender_le
        W_S hWS x a
  have hstage :
      |mwU_T x a sd - mwU_T x a ss| ≤ K_S / 120 :=
    (lowDeltaTargetStage_abs_sub_le hx ha).trans hsPolicy
  have htrans :
      dist yd xs ≤ 1 / 100 := by
    simpa [yd, xs, sd] using
      lowDelta_transition_dist_state_le xs sd hsdmem
  have hWTabs :
      |W_T yd - W_T xs| ≤ K_T / 100 := by
    calc
      |W_T yd - W_T xs| ≤ K_T * dist xs yd := hWT xs yd
      _ = K_T * dist yd xs := by rw [dist_comm]
      _ ≤ K_T * (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left htrans hKT
      _ = K_T / 100 := by ring
  simp only [AbstractGame.Params.joint_T_top_integrand,
    lowDeltaStaticTargetObjective, lowDeltaParams_U_T,
    lowDeltaParams_β_T]
  rw [show
      mwU_T x a (lowDeltaParams.σ_dyn_top W_S x a) +
            (9 / 10 : ℝ) * W_T
              (Sanctions.clipS'
                (lowDeltaParams.F x
                  (lowDeltaParams.σ_dyn_top W_S x a))) -
          (mwU_T x a (mwσ x a) +
            (9 / 10 : ℝ) * W_T ⟨x, hx⟩) =
        (mwU_T x a (lowDeltaParams.σ_dyn_top W_S x a) -
          mwU_T x a (mwσ x a)) +
        (9 / 10 : ℝ) *
          (W_T (Sanctions.clipS'
            (lowDeltaParams.F x
              (lowDeltaParams.σ_dyn_top W_S x a))) -
            W_T ⟨x, hx⟩) by ring]
  change
    |(mwU_T x a sd - mwU_T x a ss) +
        (9 / 10 : ℝ) * (W_T yd - W_T xs)| ≤
      K_S / 120 + (9 / 10 : ℝ) * (K_T / 100)
  calc
    |(mwU_T x a sd - mwU_T x a ss) +
        (9 / 10 : ℝ) * (W_T yd - W_T xs)|
        ≤ |mwU_T x a sd - mwU_T x a ss| +
            |(9 / 10 : ℝ) * (W_T yd - W_T xs)| :=
      abs_add_le _ _
    _ =
        |mwU_T x a sd - mwU_T x a ss| +
          (9 / 10 : ℝ) * |W_T yd - W_T xs| := by
      rw [abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10)]
    _ ≤ K_S / 120 + (9 / 10 : ℝ) * (K_T / 100) :=
      add_le_add hstage
        (mul_le_mul_of_nonneg_left hWTabs (by norm_num))

/-- Every maximizer of the reduced dynamic Target objective obeys the exact
squared-distance budget inherited from the static modulus-one theorem.
Witness-specific (Rule 22).  The former premises `0 ≤ K_T` and `0 ≤ K_S` are
dropped: they follow from the two Lipschitz bounds. -/
theorem lowDelta_jointTarget_maximizer_sq_le_static
    (W_T W_S : SBCF) {K_T K_S : ℝ}
    (hWT : Sanctions.AbstractGame.Params.ValueLipschitzWith W_T K_T)
    (hWS : Sanctions.AbstractGame.Params.ValueLipschitzWith W_S K_S)
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax :
      IsMaxOn
        (lowDeltaParams.joint_T_top_integrand W_T W_S x)
        Sanctions.I a) :
    (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤
      2 * (K_S / 120 + (9 / 10 : ℝ) * (K_T / 100)) := by
  exact
    lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation_add
      (ε := K_S / 120 + (9 / 10 : ℝ) * (K_T / 100))
      (c := (9 / 10 : ℝ) * W_T ⟨x, hx⟩)
      hx ha hmax
      (fun z hz =>
        lowDelta_jointTarget_close_static_add
          W_T W_S hWT hWS hx hz)

/-! ## Specialization to the exact frozen center -/

/-- The frozen Target center's smeared continuation has modulus `200`. -/
theorem lowDeltaFrozenTargetSmear_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaShocked.smear lowDeltaFrozenTargetCenter) 200 := by
  intro y₁ y₂
  rw [lowDeltaShocked_smear]
  simpa [dist_comm] using
    lowDeltaFrozenTargetCenter_smear_lipschitz y₂ y₁

/-- The frozen Sender center's smeared continuation has modulus `523/16`. -/
theorem lowDeltaFrozenSenderSmear_valueLipschitz :
    Sanctions.AbstractGame.Params.ValueLipschitzWith
      (lowDeltaShocked.smear lowDeltaFrozenSenderCenter)
      (523 / 16) := by
  intro y₁ y₂
  rw [lowDeltaShocked_smear]
  simpa [dist_comm] using
    lowDeltaFrozenSenderCenter_smear_lipschitz y₂ y₁

/-- At the exact frozen center the dynamic Sender selector lies within
`523/1920` of the static Sender selector, uniformly in state and Target
action. -/
theorem lowDeltaFrozenSenderSelector_abs_sub_static_le
    (x a : ℝ) :
    |lowDeltaParams.σ_dyn_top
        (lowDeltaShocked.smear lowDeltaFrozenSenderCenter) x a -
      mwσ x a| ≤ 523 / 1920 := by
  have h :=
    lowDelta_sigmaDynTop_abs_sub_staticSender_le
      (V := lowDeltaShocked.smear lowDeltaFrozenSenderCenter)
      (K := 523 / 16)
      lowDeltaFrozenSenderSmear_valueLipschitz
      x a
  norm_num at h ⊢
  exact h

/-- The exact frozen-center specialization of the reduced Target localization
budget.  It is valid but deliberately recorded before claiming it is useful
for a local carrier. -/
theorem lowDeltaFrozen_jointTarget_maximizer_sq_le_static
    {x a : ℝ} (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax :
      IsMaxOn
        (lowDeltaParams.joint_T_top_integrand
          (lowDeltaShocked.smear lowDeltaFrozenTargetCenter)
          (lowDeltaShocked.smear lowDeltaFrozenSenderCenter) x)
        Sanctions.I a) :
    (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤ 3979 / 960 := by
  have h :=
    lowDelta_jointTarget_maximizer_sq_le_static
      (lowDeltaShocked.smear lowDeltaFrozenTargetCenter)
      (lowDeltaShocked.smear lowDeltaFrozenSenderCenter)
      (K_T := 200) (K_S := 523 / 16)
      lowDeltaFrozenTargetSmear_valueLipschitz
      lowDeltaFrozenSenderSmear_valueLipschitz
      hx ha hmax
  norm_num at h ⊢
  exact h

/-- The current frozen-center Target bound is larger than the whole feasible
unit-square displacement budget.  Thus the exact theorem above is not yet a
small-carrier certificate; the Target continuation modulus must be sharpened
or the reference center redesigned. -/
theorem lowDeltaFrozen_jointTarget_budget_gt_one :
    (1 : ℝ) < 3979 / 960 := by
  norm_num

end Examples
end Sanctions
