/-
Sanctions/Theory/Shocked/HeSunShock.lean

**The He–Sun-style atomless shock kernel as a concrete parameter.**

He–Sun (JET 2017) obtain stationary MPE existence by adding an atomless
idiosyncratic component to the transition kernel. This module realizes exactly
that as a *concrete* parameter: a probability measure `κ` on the state shock
`η`, with the smoothed continuation

  `smear V (y) = ∫ η, V(clipS'(y + η)) ∂κ`.

From `κ` being a **probability** measure (`∫κ = 1`) we **derive** — rather than
postulate — that `smear` is a well-defined bounded-continuous-function operator
and is sup-norm **nonexpansive**. A `HeSunShockParams` therefore *produces* a
`ShockedParams` (`toShockedParams`), so the entire shocked development (the
`β_S`/`β_T`-contractions, the shocked Bellman equations, and the non-vacuous
shocked corner equilibrium) applies from a concrete He–Sun kernel — with the
shock's nonexpansiveness now machine-checked from the kernel, not assumed.

This is the "He–Sun road": the existence engine stays **Banach** (the easy
route the shock unlocks), and the shock is a genuine economic primitive (an
atomless transition noise density). The harder He–Sun *theorem* (Fan–Glicksberg
+ measurable selection for the coupled game) is *not* needed for the corner
case; the *interior* (non-corner) case additionally needs a kernel-regularity
(Lipschitz-density) property, introduced separately.

**Rule-3.** `κ` (a probability measure) is the He–Sun shock primitive, approved
2026-06-19; the nonexpansiveness it must satisfy is *derived*, not a new
hypothesis. **Rule-15.** All fixed points downstream are constructed (Banach).

**Formal-vs-narrative precision (2026-07-24).** The formal requirement on `κ`
is ONLY `IsProbabilityMeasure` (`∫κ = 1`) — "atomless" is the He–Sun
*interpretation*, realized by the uniform-density box-kernel witness
(`MovingAverageShock`) but consumed by **no proof in the tree**; every
shocked result needs only `∫κ = 1`. No `NoAtoms` hypothesis exists or is
needed anywhere.
-/

import Sanctions.Postulates.ShockedParams
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Sanctions
namespace AbstractGame

open MeasureTheory BoundedContinuousFunction

noncomputable section

/-- **`Params` with a concrete He–Sun atomless shock kernel** `κ` (a probability
measure on the state shock `η`, giving `x' = clipS'(F(x,s) + η)`). -/
structure HeSunShockParams extends Params where
  /-- The He–Sun idiosyncratic-shock kernel, as a probability measure.
  (The formal requirement is only `IsProbabilityMeasure`; atomlessness is
  the He–Sun narrative interpretation and is consumed by no proof.) -/
  κ : Measure ℝ
  /-- `κ` is a probability measure (`∫κ = 1`) — the source of nonexpansiveness. -/
  κ_prob : IsProbabilityMeasure κ

namespace HeSunShockParams

variable (hsp : HeSunShockParams)

attribute [instance] HeSunShockParams.κ_prob

/-- The kernel-smeared continuation as a function `ℝ → ℝ`. -/
noncomputable def smearReal (V : SBCF) (y : ℝ) : ℝ :=
  ∫ η, V (Sanctions.clipS' (y + η)) ∂hsp.κ

theorem hc_eta (y : ℝ) : Continuous (fun η => Sanctions.clipS' (y + η)) :=
  Sanctions.clipS'_continuous.comp (continuous_const.add continuous_id)

theorem hc_y (η : ℝ) : Continuous (fun y => Sanctions.clipS' (y + η)) :=
  Sanctions.clipS'_continuous.comp (continuous_id.add continuous_const)

/-- The smeared integrand is integrable against `κ` (bounded by `‖V‖`, finite measure). -/
theorem smear_integrable (V : SBCF) (y : ℝ) :
    Integrable (fun η => V (Sanctions.clipS' (y + η))) hsp.κ :=
  (integrable_const ‖V‖).mono'
    ((V.continuous.comp (hc_eta y)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun η => V.norm_coe_le_norm _))

/-- `smearReal` is bounded by `‖V‖`. -/
theorem smearReal_bdd (V : SBCF) (y : ℝ) : |hsp.smearReal V y| ≤ ‖V‖ := by
  unfold smearReal
  rw [← Real.norm_eq_abs]
  calc ‖∫ η, V (Sanctions.clipS' (y + η)) ∂hsp.κ‖
      ≤ ∫ η, ‖V (Sanctions.clipS' (y + η))‖ ∂hsp.κ := norm_integral_le_integral_norm _
    _ ≤ ∫ _η, ‖V‖ ∂hsp.κ :=
        integral_mono (hsp.smear_integrable V y).norm (integrable_const _)
          (fun η => V.norm_coe_le_norm _)
    _ = ‖V‖ := by simp

/-- `smearReal` is continuous in `y` (dominated convergence; the BCF crux). -/
theorem smearReal_continuous (V : SBCF) : Continuous (hsp.smearReal V) := by
  unfold smearReal
  apply continuous_of_dominated (bound := fun _ => ‖V‖)
  · intro y; exact (V.continuous.comp (hc_eta y)).aestronglyMeasurable
  · intro y; exact Filter.Eventually.of_forall (fun η => V.norm_coe_le_norm _)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun η => V.continuous.comp (hc_y η))

/-- `smearReal` restricted to the state space `↥S`. -/
noncomputable def smearOnS (V : SBCF) : ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => hsp.smearReal V x.val

theorem smearOnS_continuous (V : SBCF) : Continuous (hsp.smearOnS V) :=
  (hsp.smearReal_continuous V).comp continuous_subtype_val

/-- **The kernel-derived smoothing operator** as a bounded continuous function. -/
noncomputable def smearBCF (V : SBCF) : SBCF :=
  BoundedContinuousFunction.mkOfCompact ⟨hsp.smearOnS V, hsp.smearOnS_continuous V⟩

@[simp] theorem smearBCF_apply (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) :
    hsp.smearBCF V x = hsp.smearReal V x.val := rfl

/-- **Nonexpansiveness of the kernel smoothing**, derived from `∫κ = 1`. -/
theorem smearBCF_nonexpansive (V W : SBCF) :
    dist (hsp.smearBCF V) (hsp.smearBCF W) ≤ dist V W := by
  rw [BoundedContinuousFunction.dist_le dist_nonneg]
  intro x
  rw [smearBCF_apply, smearBCF_apply, Real.dist_eq]
  unfold smearReal
  rw [← integral_sub (hsp.smear_integrable V x.val) (hsp.smear_integrable W x.val),
      ← Real.norm_eq_abs]
  have hpt : ∀ η, ‖V (Sanctions.clipS' (x.val + η)) - W (Sanctions.clipS' (x.val + η))‖
      ≤ dist V W := by
    intro η
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist _
  calc ‖∫ η, (V (Sanctions.clipS' (x.val + η)) - W (Sanctions.clipS' (x.val + η))) ∂hsp.κ‖
      ≤ ∫ η, ‖V (Sanctions.clipS' (x.val + η)) - W (Sanctions.clipS' (x.val + η))‖ ∂hsp.κ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _η, dist V W ∂hsp.κ :=
        integral_mono ((hsp.smear_integrable V x.val).sub (hsp.smear_integrable W x.val)).norm
          (integrable_const _) hpt
    _ = dist V W := by simp

/-- **A He–Sun kernel param produces a `ShockedParams`** — the abstract shock
smoothing is *realized* by the concrete kernel, with nonexpansiveness derived
from `∫κ = 1`. Every shocked result (contractions, shocked Bellman equations,
non-vacuous shocked corner equilibrium) then applies from the He–Sun kernel. -/
noncomputable def toShockedParams : Sanctions.AbstractGame.ShockedParams where
  toParams := hsp.toParams
  smear := hsp.smearBCF
  smear_nonexpansive := hsp.smearBCF_nonexpansive

end HeSunShockParams
end -- noncomputable section

end AbstractGame
end Sanctions
