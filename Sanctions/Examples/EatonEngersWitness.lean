/-
Sanctions/Examples/EatonEngersWitness.lean

**Eaton-Engers × Kaempfer-Lowenberg concrete witness (point P2).**

A concrete `AbstractGame.Params` instantiating the dynamic public-choice
sanctions model with payoffs fused from the literature (see
`docs/archive/WITNESS-FEASIBILITY-2026-06-12.md`):

  U_S(x,a,s) = a − ¼·s² − s·(1/10 + ½·a − 3/2·x)
  U_T(x,a,s) = −a² − a − s·(1/2 − ½·a − x)
  F(x,s)     = (4/5)·x + (1/5)·s          (δ = 1/5)
  β_S = 1/2,  β_T = 9/10

Provenance of each term:
* `+ (3/2)·s·x` in U_S, `+ s·x` in U_T — the **Kaempfer-Lowenberg
  1988 rally** (∂²U/∂s∂x > 0): at higher hardline state the marginal
  value of sanctions rises for both players (the sanctions-strengthen-
  the-regime "rally around the flag").
* `− ½·s·a` in U_S — the **Eaton-Engers 1992 uniqueness condition
  G_S > 0** = the project's R28 "compliance placates" sign
  (∂²U_S/∂s∂a ≤ 0).
* `− a²` in U_T — strict concavity in `a` ⇒ a unique *derived* Target
  compliance (Curtat-style diagonal dominance, one follower).
* `− ¼·s²` in U_S — strict concavity in `s` ⇒ the static Sender
  selector `σ` is the *continuous* clipped vertex of the parabola
  (needed for `σ_continuous`); chosen small (¼) so the dynamic
  equilibrium still locks the realized sanction at the corner `s = 1`
  on the basin, keeping the value functions affine there (the LQ
  closed-form route, NDP/Puterman).

This file delivers **Phase 1**: the object is a valid `Params`
(non-vacuity of the abstract structure at an economically-motivated,
flip-bearing payoff — unlike the prior linear witnesses, here
∂²U_S/∂s∂x and ∂²U_T/∂s∂x are *strictly* positive). The static Sender
selector is the closed-form clip
`σ(x,a) = clip(3x − 1/5 − a, 0, 1)`, proved to be the stage argmax
(Rule-1 coupling) and jointly continuous, directly — no Berge
machinery.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.StageFlipDischargers
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Theory.Microfoundations.KaempferLowenbergPolity
import Sanctions.Examples.WitnessKit
import Sanctions.Examples.AffineInstance.ComplianceTower

namespace Sanctions
namespace Examples

open Set

/-- Sender stage payoff at the witness point.
`∂²/∂s∂x = 3/2 > 0` (rally), `∂²/∂s∂a = −1/2 ≤ 0` (R28),
`∂²/∂s² = −1/2 < 0` (strict concavity in `s`). -/
noncomputable def eeU_S (x a s : ℝ) : ℝ :=
  a - (1/4) * s^2 - s * (1/10 + (1/2) * a - (3/2) * x)

/-- Target stage payoff. `∂²/∂s∂x = 1 > 0` (rally),
`∂²/∂a² = −2 < 0` (unique compliance). -/
noncomputable def eeU_T (x a s : ℝ) : ℝ :=
  -a^2 - a - s * (1/2 - (1/2) * a - x)

/-- Static Sender selector: the clipped vertex of the concave parabola
`U_S(x,a,·)`. The vertex is `s* = 3x − 1/5 − a`. -/
noncomputable def eeσ (x a : ℝ) : ℝ :=
  max 0 (min 1 (3 * x - 1/5 - a))

theorem eeσ_mem (x a : ℝ) : eeσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem eeσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => eeσ xa.1 xa.2) := by
  unfold eeσ
  fun_prop

theorem eeU_S_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => eeU_S xas.1 xas.2.1 xas.2.2) := by
  unfold eeU_S
  fun_prop

theorem eeU_T_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => eeU_T xas.1 xas.2.1 xas.2.2) := by
  unfold eeU_T
  fun_prop

/-- **Rule-1 coupling.** The clipped vertex `eeσ x a` maximizes the
concave parabola `U_S(x,a,·)` on `[0,1]`. Proof: `U_S(x,a,s) = C(x,a)
− ¼·(s − s*)²` with vertex `s* = 3x − 1/5 − a`; the maximizer on
`[0,1]` is the point of `[0,1]` closest to `s*`, which is the clip.
Case split on `s*` vs the interval endpoints. -/
theorem eeσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => eeU_S x a s) (Set.Icc (0 : ℝ) 1) (eeσ x a) := by
  -- WitnessKit C6: vertex form `U_S(x,a,s) = C − ¼·(s − t)²`.
  unfold eeσ
  exact WitnessKit.clipVertex_isMaxOn (k := 1/4)
    (C := a + (1/4) * (3 * x - 1/5 - a) ^ 2)
    (t := 3 * x - 1/5 - a)
    (by norm_num) (fun s => by unfold eeU_S; ring)

/-- **The Kaempfer-Lowenberg two-group polity behind the witness's transition.**
The rally that the stage payoffs encode as the hand-chosen cross-partial
`+(3/2)·s·x` is here the *market* primitive: strong rally (`rally s = s`), no
offsetting empowerment, linear market clearing `x*(s) = s`. The witness is in the
**lock-in regime**, so its transition's entrenchment sign `F_mono_s` is *derived*
from `xstar_mono_of_lockIn` (below) rather than asserted via `affineF_mono_s`. -/
noncomputable def eatonEngersPolity : Sanctions.KaempferLowenberg.Polity where
  b := fun x => -x
  hb := fun _ _ h => neg_lt_neg h
  rally := fun s => s
  incid := fun _ => 0
  empower := fun _ => 0
  xstar := fun s => s
  hroot := fun s => by ring

/-- The witness sits in the lock-in (net-entrenchment) regime. -/
theorem eatonEngersPolity_lockIn : eatonEngersPolity.LockIn := by
  intro a b h
  simp only [Sanctions.KaempferLowenberg.Polity.netChannel, eatonEngersPolity]
  linarith

/-- **The Eaton-Engers × Kaempfer-Lowenberg witness `Params` (P2).**
The transition is *induced by* `eatonEngersPolity` (partial adjustment toward the
clearing entrenchment): `F(x,s) = (4/5)·x + (1/5)·x*(s)` with `x*(s) = s`, so it is
the affine law `affineF (1/5)` (def-eq), but `F_mono_s` is now sourced from the
two-group market's lock-in regime, not assumed. -/
noncomputable def eatonEngersParams : Sanctions.AbstractGame.Params where
  δ := 1 / 5
  δ_mem := by constructor <;> norm_num
  β_T := 9 / 10
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := eeU_T
  U_S := eeU_S
  σ := eeσ
  σ_mem := eeσ_mem
  σ_isMaxOn_U_S := eeσ_isMaxOn
  U_T_continuous := eeU_T_continuous
  U_S_continuous := eeU_S_continuous
  -- Transition consumed from the K-L polity (def-eq to `affineF (1/5)`):
  F := eatonEngersPolity.inducedF (1 / 5)
  F_continuous := eatonEngersPolity.inducedF_continuous continuous_id
  F_mono_x := eatonEngersPolity.inducedF_mono_x (by norm_num)
  -- F_mono_s is DERIVED from the lock-in regime, not asserted:
  F_mono_s := eatonEngersPolity.inducedF_mono_s eatonEngersPolity_lockIn (by norm_num)
  F_diag := eatonEngersPolity.inducedF_diag (fun _ => rfl)

/-- **`eatonEngersParams` has a continuous static Sender selector.** A concrete member
whose transition is the polity-induced law `eatonEngersPolity.inducedF (1/5)`; the
selector itself does not read the transition. The proof is the one that was the economy's
`σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left `Params` for
the class `Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender
results can use it at this economy. -/
instance eatonEngersParams_staticSelectorContinuous :
    eatonEngersParams.StaticSelectorContinuous where
  σ_continuous := eeσ_continuous

@[simp] theorem eatonEngersParams_U_S : eatonEngersParams.U_S = eeU_S := rfl
@[simp] theorem eatonEngersParams_U_T : eatonEngersParams.U_T = eeU_T := rfl
@[simp] theorem eatonEngersParams_δ : eatonEngersParams.δ = 1 / 5 := rfl
@[simp] theorem eatonEngersParams_β_S : eatonEngersParams.β_S = 1 / 2 := rfl
@[simp] theorem eatonEngersParams_β_T : eatonEngersParams.β_T = 9 / 10 := rfl

/-- The Eaton-Engers × Kaempfer-Lowenberg transition satisfies strict
adjustment because its induced transition is definitionally the affine
partial-adjustment law with interior weight `1/5`. -/
theorem eatonEngersParams_strictAdjustment :
    eatonEngersParams.StrictAdjustment :=
  AbstractGame.strictAdjustment_of_F_eq_affineF
    eatonEngersParams eatonEngersParams.δ_mem rfl

/-! ## Stage-flip primitives discharged from the constant cross-partials

The whole economic point of this witness: unlike the prior linear
witnesses (`jointPositiveParams`, `polyComplianceParams`, where
`∂²U/∂s∂x = 0`), here the rally complementarities are *strictly*
positive constants, so the order-language stage-flip primitives hold
outright. Each chord identity collapses to a single nonnegative
product. -/

/-- **SenderStageID** at the witness: `∂²U_S/∂s∂x = 3/2 > 0`. The
chord difference equals `(3/2)·(s'−s)·(x'−x) ≥ 0`. -/
theorem eatonEngersParams_SenderStageID :
    eatonEngersParams.SenderStageID := by
  intro a _ha s s' x x' _hs _hs' hss _hx _hx' hxx'
  simp only [eatonEngersParams_U_S, eeU_S]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s' - s)
    (by linarith : (0:ℝ) ≤ x' - x)]

/-- **TargetStageID** at the witness: `∂²U_T/∂s∂x = 1 > 0` (the
Kaempfer-Lowenberg rally). Chord difference `= (s'−s)·(x'−x) ≥ 0`. -/
theorem eatonEngersParams_TargetStageID :
    eatonEngersParams.TargetStageID := by
  intro a _ha s s' x x' _hs _hs' hss _hx _hx' hxx'
  simp only [eatonEngersParams_U_T, eeU_T]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s' - s)
    (by linarith : (0:ℝ) ≤ x' - x)]

/-- **SenderActionDD** at the witness: `∂²U_S/∂s∂a = −1/2 ≤ 0` (R28
"compliance placates" = Eaton-Engers' `G_S > 0`). Chord difference
`= −(1/2)·(s'−s)·(a'−a) ≤ 0`. -/
theorem eatonEngersParams_SenderActionDD :
    eatonEngersParams.SenderActionDD := by
  intro x _hx s s' a a' _hs _hs' hss _ha _ha' haa'
  simp only [eatonEngersParams_U_S, eeU_S]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s' - s)
    (by linarith : (0:ℝ) ≤ a' - a)]

/-- **SenderStageIDStrict** at the witness — the *strict*
complementarity the design emphasizes. Each proper sanction chord has
state-slope `(3/2)·(s₂−s₁) > 0`. -/
theorem eatonEngersParams_SenderStageIDStrict :
    eatonEngersParams.SenderStageIDStrict := by
  intro a _ha s₁ _hs₁ s₂ _hs₂ hss x _hx x' _hx' hxx
  simp only [eatonEngersParams_U_S, eeU_S]
  nlinarith [mul_pos (by linarith : (0:ℝ) < s₂ - s₁)
    (by linarith : (0:ℝ) < x' - x)]

/-- **TargetStageIDStrict** at the witness. Sanction chord state-slope
`= (s₂−s₁) > 0` (the strict Kaempfer-Lowenberg rally). -/
theorem eatonEngersParams_TargetStageIDStrict :
    eatonEngersParams.TargetStageIDStrict := by
  intro a _ha s₁ _hs₁ s₂ _hs₂ hss x _hx x' _hx' hxx
  simp only [eatonEngersParams_U_T, eeU_T]
  nlinarith [mul_pos (by linarith : (0:ℝ) < s₂ - s₁)
    (by linarith : (0:ℝ) < x' - x)]

/-- **SenderChordConcaveInS** at the witness (R44 route extension):
equal-width sanction increments rise when shifted down, the chord
consequence of the `−¼·s²` strict concavity. Difference
`= ½·c·(s₂−s₁) ≥ 0`. -/
theorem eatonEngersParams_SenderChordConcaveInS :
    eatonEngersParams.SenderChordConcaveInS := by
  intro x _hx a _ha s₁ s₂ c hc _hs₁c hss _hs₂
  simp only [eatonEngersParams_U_S, eeU_S]
  nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ s₂ - s₁)]

/-! ## Conditional headline close (Rule 15)

The witness's headline application is stated *conditional on the value
class*, which is honest: the one piece not delivered unconditionally is
a valid `ValueClass2` at the witness (carrier + Bellman invariance +
Sender/Target argmax uniqueness). For this **non-smooth flip
equilibrium** that is a Curtat-style value-function regularity result —
a deferred research round — *numerically verified to exist* (an
argmax-uniqueness scan over the converged equilibrium found `0`
separated second maxima, so `DynamicArgmaxUnique` holds at the fixed
point; see `docs/archive/WITNESS-FEASIBILITY-2026-06-12.md`). The witness discharges
the stage-flip inputs of the certificate **unconditionally and
axiom-clean** (`eatonEngersParams_SenderStageID` / `_TargetStageID`
fed below); the residual inputs are all carrier-dependent (operator
Lipschitz bounds on the value class, `h_diag`, `hV_T_mono_carrier`,
`hSC_on`, `hMyoCeiling`) plus the value-class existence itself. -/

/-- **Conditional three-goals headline at the witness (honest close).**
Given a full compliance certificate `C` at `eatonEngersParams` — which
bundles the one open piece, the value class `C.D` and its invariance,
the deferred Curtat-style regularity round for this non-smooth flip
equilibrium — the headline *dominance* goal holds: on the basin the
forward-looking realized sanction dominates the myopic stage response.
The witness discharges the certificate's stage-flip complementarity
inputs **unconditionally and axiom-clean**
(`eatonEngersParams_SenderStageID` / `_TargetStageID` /
`_SenderActionDD` and the strict variants); a builder of `C` supplies
only the carrier-dependent data and the value-class existence. This
theorem makes the witness's conditional status a compiling artifact
rather than prose. -/
theorem eatonEngersParams_three_goals_conditional
    (C : eatonEngersParams.StandardComplianceLocalCoreCertificate) :
    ∃ E : eatonEngersParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           eatonEngersParams.σ x (C.M.α x)
             ≤ eatonEngersParams.dynamicTopRealizedRule E.V_S E.α x) := by
  have hF : eatonEngersParams.F = Sanctions.AbstractGame.affineF eatonEngersParams.δ := rfl
  obtain ⟨E, hVT, hVS, _hGoal1, hGoal2, _hGoal3⟩ :=
    C.three_goals_local_uniform_starts (p := eatonEngersParams) hF
  exact ⟨E, hVT, hVS, hGoal2⟩

end Examples
end Sanctions
