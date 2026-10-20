/-
Sanctions/Examples/MechanismWitness.lean

**Mechanism-active witness (point P3): the two forces visibly ON.**

A second concrete `AbstractGame.Params`, a perturbation of the Eaton-Engers
witness (`EatonEngersWitness.lean`) tuned so that — unlike P2, where the
realised sanction locks at the corner `s = 1` and the forces are numerically
invisible (the paper's Caveat 2) — the dynamic equilibrium is genuinely
INTERIOR on the lower basin while remaining persistent:

  U_S(x,a,s) = a − (3/5)·s² − s·(1/10 + (1/2)·a − (27/20)·x) + (2/5)·x
  U_T(x,a,s) = −a² + 2·x·a − a − s·(1/2 − (1/2)·a − x)
  F(x,s)     = (4/5)·x + (1/5)·s            (δ = 1/5)
  β_S = 1/2,  β_T = 9/10

Provenance / what each perturbation buys (vs P2):
* `q_S = 6/5` (the `−(3/5)·s²` curvature, vs P2's `−¼·s²`) — stronger
  diminishing returns to sanctioning, so the static Sender vertex
  `σ = clip(9x/8 − 1/12 − 5a/12)` is INTERIOR on the lower basin
  `[1/2, ~0.77]` rather than pinned at the corner: this is what makes the
  forward-looking-minus-myopic Sender wedge a STRICT realised gap, not a
  corner-masked one (Force 1 visible).
* `r_S = 27/20` (rally slope, vs P2's `3/2`) — kept high enough that the
  forward-looking realised `s*(x) ≥ x` on the basin (persistence preserved),
  while the MYOPIC `s_M(x) < x` everywhere on the basin: myopia would forfeit
  the basin; the continuation wedge is exactly what sustains it.
* `+ 2·x·a` in U_T (the `k_T = 2` Target rally, vs P2's `0`) — makes the
  Target's optimal compliance INTERIOR and reluctant on the basin (Force 2
  visible), instead of the degenerate corner `α ≡ 0`. No `s`-dependence, so it
  perturbs NO structural cross-partial.
* `+ (2/5)·x` in U_S (the `c_S = 2/5` Sender state-stake) — keeps `V_S`
  strongly state-dependent (basin slope ≈ 3.6) even off the `s`-channel
  (Force 1 continuation gain). No `s`/`a`-dependence, so it perturbs no
  structural condition.

**Existence is He-Sun-cited, NOT constructed.** Numerically (six independent
solvers; see `docs/archive/workflow-scratch/`), the interior-leader equilibrium here is a TRUE
best-response cycle — order-reversal gap ≈ 0.06–0.52 — so deterministic value /
policy / Newton iteration limit-cycles and a *constructed* deterministic-policy
fixed point does not exist; only the purified (softmax/He-Sun, Kakutani-over-
behavioural-strategies) fixed point exists, where the two forces are fully
active. The headline at this witness is therefore stated CONDITIONAL on the
value class (Rule 15), exactly as for P2; the mechanism activity is a paper-side
numerical exhibit, not a Lean construction.

This file delivers the same Phase-1 content as P2: a valid `Params` with
*strictly positive* sanction-state cross-partials (`∂²U_S/∂s∂x = 27/20`,
`∂²U_T/∂s∂x = 1`) and the "compliance placates" sign (`∂²U_S/∂s∂a = −1/2`),
plus the conditional three-goals close.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.StageFlipDischargers
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Examples.WitnessKit
import Sanctions.Examples.AffineInstance.ComplianceTower

namespace Sanctions
namespace Examples

open Set

/-- Sender stage payoff at the mechanism witness.
`∂²/∂s∂x = 27/20 > 0` (rally), `∂²/∂s∂a = −1/2 ≤ 0` (compliance placates),
`∂²/∂s² = −6/5 < 0` (strict concavity in `s`); the `+(2/5)x` state-stake has
no `s`/`a`-dependence. -/
noncomputable def mwU_S (x a s : ℝ) : ℝ :=
  a - (3/5) * s^2 - s * (1/10 + (1/2) * a - (27/20) * x) + (2/5) * x

/-- Target stage payoff. `∂²/∂s∂x = 1 > 0` (rally), `∂²/∂a² = −2 < 0`
(unique compliance); the `+2·x·a` Target rally has no `s`-dependence. -/
noncomputable def mwU_T (x a s : ℝ) : ℝ :=
  -a^2 + 2 * x * a - a - s * (1/2 - (1/2) * a - x)

/-- Static Sender selector: the clipped vertex of the concave parabola
`U_S(x,a,·)`. Vertex `s* = (27x/20 − 1/10 − a/2)/(6/5) = 9x/8 − 1/12 − 5a/12`. -/
noncomputable def mwσ (x a : ℝ) : ℝ :=
  max 0 (min 1 ((9/8) * x - 1/12 - (5/12) * a))

theorem mwσ_mem (x a : ℝ) : mwσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem mwσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => mwσ xa.1 xa.2) := by
  unfold mwσ
  fun_prop

theorem mwU_S_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => mwU_S xas.1 xas.2.1 xas.2.2) := by
  unfold mwU_S
  fun_prop

theorem mwU_T_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => mwU_T xas.1 xas.2.1 xas.2.2) := by
  unfold mwU_T
  fun_prop

/-- **Rule-1 coupling.** The clipped vertex `mwσ x a` maximizes the concave
parabola `U_S(x,a,·)` on `[0,1]`. Proof: `U_S(x,a,s) = C(x,a) − (3/5)·(s − t)²`
with vertex `t = 9x/8 − 1/12 − 5a/12`; the maximizer on `[0,1]` is the point of
`[0,1]` closest to `t`, the clip. Case split on `t` vs the endpoints. -/
theorem mwσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => mwU_S x a s) (Set.Icc (0 : ℝ) 1) (mwσ x a) := by
  -- WitnessKit C6: vertex form `U_S(x,a,s) = C − (3/5)·(s − t)²`.
  unfold mwσ
  exact WitnessKit.clipVertex_isMaxOn (k := 3/5)
    (C := a + (2/5) * x + (3/5) * ((9/8) * x - 1/12 - (5/12) * a) ^ 2)
    (t := (9/8) * x - 1/12 - (5/12) * a)
    (by norm_num) (fun s => by unfold mwU_S; ring)

/-- **The mechanism-active witness `Params` (P3).** -/
noncomputable def mechanismWitnessParams : Sanctions.AbstractGame.Params where
  δ := 1 / 5
  δ_mem := by constructor <;> norm_num
  β_T := 9 / 10
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := mwU_T
  U_S := mwU_S
  σ := mwσ
  σ_mem := mwσ_mem
  σ_isMaxOn_U_S := mwσ_isMaxOn
  U_T_continuous := mwU_T_continuous
  U_S_continuous := mwU_S_continuous
  F := Sanctions.AbstractGame.affineF (1 / 5)
  F_continuous := Sanctions.AbstractGame.affineF_continuous _
  F_mono_x := Sanctions.AbstractGame.affineF_mono_x (by constructor <;> norm_num)
  F_mono_s := Sanctions.AbstractGame.affineF_mono_s (by constructor <;> norm_num)
  F_diag := Sanctions.AbstractGame.affineF_diag _

/-- **`mechanismWitnessParams` has a continuous static Sender selector.**
Affine-restricted: a concrete member with the affine transition `affineF (1/5)`; the
selector itself does not read the transition. The proof is the one that was the economy's
`σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left `Params` for
the class `Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender
results can use it at this economy. -/
instance mechanismWitnessParams_staticSelectorContinuous :
    mechanismWitnessParams.StaticSelectorContinuous where
  σ_continuous := mwσ_continuous

@[simp] theorem mechanismWitnessParams_U_S : mechanismWitnessParams.U_S = mwU_S := rfl
@[simp] theorem mechanismWitnessParams_U_T : mechanismWitnessParams.U_T = mwU_T := rfl
@[simp] theorem mechanismWitnessParams_δ : mechanismWitnessParams.δ = 1 / 5 := rfl
@[simp] theorem mechanismWitnessParams_β_S : mechanismWitnessParams.β_S = 1 / 2 := rfl
@[simp] theorem mechanismWitnessParams_β_T : mechanismWitnessParams.β_T = 9 / 10 := rfl
@[simp] theorem mechanismWitnessParams_F :
    mechanismWitnessParams.F = Sanctions.AbstractGame.affineF (1 / 5) := rfl

/-! ## Stage-flip primitives (identical signs to P2, different constants)

The strictly-positive rally complementarities and the compliance-placates sign
carry over verbatim from P2; only the numerical coefficients change. The two new
terms (`+2·x·a` in U_T, `+(2/5)·x` in U_S) have no `s`-dependence, so they vanish
from every sanction-chord identity below. -/

/-- **SenderStageID**: `∂²U_S/∂s∂x = 27/20 > 0`. Chord `= (27/20)·(s'−s)·(x'−x) ≥ 0`. -/
theorem mechanismWitnessParams_SenderStageID :
    mechanismWitnessParams.SenderStageID := by
  intro a _ha s s' x x' _hs _hs' hss _hx _hx' hxx'
  simp only [mechanismWitnessParams_U_S, mwU_S]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s' - s)
    (by linarith : (0:ℝ) ≤ x' - x)]

/-- **TargetStageID**: `∂²U_T/∂s∂x = 1 > 0`. Chord `= (s'−s)·(x'−x) ≥ 0`
(the `+2·x·a` term is `s`-free, cancels). -/
theorem mechanismWitnessParams_TargetStageID :
    mechanismWitnessParams.TargetStageID := by
  intro a _ha s s' x x' _hs _hs' hss _hx _hx' hxx'
  simp only [mechanismWitnessParams_U_T, mwU_T]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s' - s)
    (by linarith : (0:ℝ) ≤ x' - x)]

/-- **SenderActionDD**: `∂²U_S/∂s∂a = −1/2 ≤ 0` (compliance placates).
Chord `= −(1/2)·(s'−s)·(a'−a) ≤ 0`. -/
theorem mechanismWitnessParams_SenderActionDD :
    mechanismWitnessParams.SenderActionDD := by
  intro x _hx s s' a a' _hs _hs' hss _ha _ha' haa'
  simp only [mechanismWitnessParams_U_S, mwU_S]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s' - s)
    (by linarith : (0:ℝ) ≤ a' - a)]

/-- **SenderStageIDStrict**: each proper sanction chord has state-slope
`(27/20)·(s₂−s₁) > 0`. -/
theorem mechanismWitnessParams_SenderStageIDStrict :
    mechanismWitnessParams.SenderStageIDStrict := by
  intro a _ha s₁ _hs₁ s₂ _hs₂ hss x _hx x' _hx' hxx
  simp only [mechanismWitnessParams_U_S, mwU_S]
  nlinarith [mul_pos (by linarith : (0:ℝ) < s₂ - s₁)
    (by linarith : (0:ℝ) < x' - x)]

/-- **TargetStageIDStrict**: sanction chord state-slope `= (s₂−s₁) > 0`. -/
theorem mechanismWitnessParams_TargetStageIDStrict :
    mechanismWitnessParams.TargetStageIDStrict := by
  intro a _ha s₁ _hs₁ s₂ _hs₂ hss x _hx x' _hx' hxx
  simp only [mechanismWitnessParams_U_T, mwU_T]
  nlinarith [mul_pos (by linarith : (0:ℝ) < s₂ - s₁)
    (by linarith : (0:ℝ) < x' - x)]

/-- **SenderChordConcaveInS**: equal-width sanction increments rise when shifted
down (the `−(3/5)·s²` strict concavity). Difference `= (6/5)·c·(s₂−s₁) ≥ 0`. -/
theorem mechanismWitnessParams_SenderChordConcaveInS :
    mechanismWitnessParams.SenderChordConcaveInS := by
  intro x _hx a _ha s₁ s₂ c hc _hs₁c hss _hs₂
  simp only [mechanismWitnessParams_U_S, mwU_S]
  nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ s₂ - s₁)]

/-! ## Conditional headline close (Rule 15)

Identical to P2: existence at this interior-leader witness is He-Sun-cited (a
true order-reversal cycle, numerically confirmed; no constructed deterministic
fixed point), so the headline is stated conditional on a value-class certificate
`C`. The witness discharges the stage-flip complementarity inputs unconditionally
and axiom-clean. -/

/-- **Conditional three-goals headline at the mechanism witness.** Given a
compliance certificate `C` at `mechanismWitnessParams`, the dominance goal holds:
on the basin the forward-looking realised sanction dominates the myopic stage
response. The mechanism *activity* (interior reluctant leader, strict
forward-looking Sender wedge, persistence that myopia forfeits) is the paper-side
numerical exhibit at the purified equilibrium. -/
theorem mechanismWitnessParams_three_goals_conditional
    (C : mechanismWitnessParams.StandardComplianceLocalCoreCertificate) :
    ∃ E : mechanismWitnessParams.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           mechanismWitnessParams.σ x (C.M.α x)
             ≤ mechanismWitnessParams.dynamicTopRealizedRule E.V_S E.α x) := by
  have hF : mechanismWitnessParams.F
      = Sanctions.AbstractGame.affineF mechanismWitnessParams.δ := rfl
  obtain ⟨E, hVT, hVS, _hGoal1, hGoal2, _hGoal3⟩ :=
    C.three_goals_local_uniform_starts (p := mechanismWitnessParams) hF
  exact ⟨E, hVT, hVS, hGoal2⟩

end Examples
end Sanctions
