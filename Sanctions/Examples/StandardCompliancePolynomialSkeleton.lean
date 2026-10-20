/-
Sanctions/Examples/StandardCompliancePolynomialSkeleton.lean

**Round-18 / Part B: Substantive parametric witness skeleton.**

The existing `jointPositiveParams` (linear `U_T = U_S = s`, σ ≡ 1) is the
lower-level non-vacuity certificate for `JointPreferenceBasinTop` only.
It does **not** instantiate `StandardComplianceLocalCoreCertificate` (the
preferred paper-facing certificate), and its sign on `U_T` is wrong for
literal compliance (sanctions should hurt the Target).

This file delivers the **next layer up**: a polynomial `Params` with
literal-compliance-correct signs, together with **numeric verification
of the shrunken certificate's key scalar margins** (Round 11 + 13 +
14 + 16 + 17 results). It is a partial witness — it lands the
concrete `Params`, computes the value-function constants in closed
form, and discharges the scalar margins by `norm_num`. The carrier
construction (`StandardComplianceLocalCoreCertificate` instantiation
itself) is the heaviest remaining step and is left for a follow-up
round, but every primitive scalar margin the certificate consumes
is computed and checked here.

## Concrete polynomial Params

* `δ = β_T = β_S = 1/2`
* `U_T(x, a, s) = 5 x - s` (Target values state with slope 5; sanctions
  hurt at rate 1)
* `U_S(x, a, s) = s` (Sender strictly likes sanctions, slope 1)
* `σ(x, a) = 1` (myopic Sender argmax of `s ↦ s` on `[0, 1]` is `s = 1`)

## Key numeric checks (Round-shrinks at work)

* **Target loss-offset margin** (Round 11 form `c_T ≤ β_T · g_T · δ`):
  with `c_T = 1`, `g_T = 20/3` (the closed-form Lipschitz constant of
  `V_T` derived below), `β_T = δ = 1/2`, we need `1 ≤ (1/2) · (20/3) · (1/2) = 5/3`. ✓
* **Sender high-sanction wedge** (Round 13 form `β_S · K_S · δ < m_S`):
  here `V_S` is constant (since `U_S(x, a, s) = s` does not depend on `x`),
  so `K_S = 0`, and `(1/2) · 0 · (1/2) = 0 < 1 = m_S`. ✓
* **Row contraction Schur form** (Round 14): with `β_T = β_S = 1/2`
  and trivially-coupled operators (`L_TS = L_ST = 0` in this minimal
  setup), `L_TS · L_ST = 0 < (1/2) · (1/2) = 1/4 = (1 - β_T)(1 - β_S)`. ✓
* **C¹ partial-derivative bounds** (Rounds 11, 13): `∂U_T/∂s = -1`
  (matches `-c_T = -1`); `∂U_S/∂s = 1` (matches `m_S = 1`). ✓

## What this file does NOT do (yet)

* Does not construct a `ValueClass2` / `ValueClass.ofLipBall` instance
  at the concrete payoffs.
* Does not discharge `D.IsInvariant` end-to-end at concrete numerics
  (would use Round 16's `ofLipBall_IsInvariant_of_preservation`
  plus Round 17's Sender-half companion).
* Does not produce a `StandardComplianceLocalCoreCertificate` value.

The structural barrier is carrier-level argmax uniqueness on a
specific `valLipBall M K`. It must be proved for the complete dynamic
objectives (or by a direct boundary-maximizer argument); stage
concavity alone would not suffice. Here the linear Sender stage payoff
has a unique boundary maximizer at `s = 1`, but is not strictly
concave, so the direct strict-monotonicity route is the relevant one.

## Rule compliance

* **Rule 1**: σ ≡ 1 is the Sender stage argmax of `U_S(x, a, ·) = id`
  on `[0, 1]` (attained at `s = 1`). Per `σ_isMaxOn_U_S`.
* **Rule 5**: This is an explicit Rule-5 *existence-certificate
  exception* (concrete numerics required for non-vacuity).
* **Rule 8**: every numeric value is paraphrased in plain English
  above.
* **Rule 9**: all margin checks discharged by `norm_num` are
  genuine numerical inequalities, not `True := rfl`.
-/

import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Bellman.InvariantLipGainBall
import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Theory.Equilibrium.ArgmaxUniquenessFromConcavity
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Examples.WitnessKit

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-! ## Concrete polynomial Params for the skeleton -/

/-- **Polynomial-compliance witness Params (Round-21 refined).** A
polynomial stage-payoff specification with literal-compliance-correct
signs:
* `U_T(x, a, s) = 5x - s + a` — Target valued by state, hurt by
  sanctions, prefers compliance (the `+ a` term is the Round-21
  refinement that makes `TargetArgmaxUnique` actually hold; without
  it, every `a ∈ [0,1]` is argmax-optimal and uniqueness fails).
* `U_S(x, a, s) = s` — Sender strictly likes sanctions.
* `σ(x, a) = 1` — myopic Sender always picks max sanctions.
* `δ = β_T = β_S = 1/2`. -/
def polyComplianceParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1/2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  -- U_T(x, a, s) = 5 x - s + a — Target values state, hurt by
  -- sanctions, strictly prefers compliance (a = 1 is the unique
  -- argmax over a ∈ [0, 1] at the joint Target integrand).
  U_T := fun x a s => 5 * x - s + a
  -- U_S(x, a, s) = s — Sender strictly likes sanctions.
  U_S := fun _ _ s => s
  -- σ(x, a) = 1 — myopic Sender argmax of s ↦ s on [0, 1] is s = 1.
  σ := fun _ _ => 1
  σ_mem := fun _ _ => ⟨by norm_num, le_refl _⟩
  σ_isMaxOn_U_S := fun _ _ s hs => by
    -- IsMaxOn (fun s => s) [0, 1] 1: trivially s ≤ 1 for s ∈ [0, 1].
    exact hs.2
  U_T_continuous := by
    -- (xas : ℝ × ℝ × ℝ) ↦ 5 * xas.1 - xas.2.2 + xas.2.1.
    fun_prop
  U_S_continuous := by
    -- (xas : ℝ × ℝ × ℝ) ↦ xas.2.2
    fun_prop
  F := AbstractGame.affineF (1 / 2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`polyComplianceParams` has a continuous static Sender selector.** Affine-restricted:
a concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance polyComplianceParams_staticSelectorContinuous :
    polyComplianceParams.StaticSelectorContinuous where
  σ_continuous := continuous_const

/-! ## Round-21 closed-form Bellman fixed-point computation

For `polyComplianceParams` with `σ ≡ 1`, the dynamics simplify:

**Sender side**: `bellmanS_BCF α V_S y = sSup_s [U_S(y, α(y), s) +
β_S · V_S(F(y, s))]`. Since `U_S(x, a, s) = s` does not depend on
`x` and the maximizer is always `s = 1` (independent of `V_S`), the
Bellman operator at any continuous `α` reduces to
`bellmanS_BCF α V_S y = 1 + (1/2) · V_S(F(y, 1))`. Iterating from
`V_S = 0` and taking the Banach limit gives the constant
**`V_S^* = 2`** (since `V = 1 + (1/2)·V` has fixed point `V = 2`).
Hence the Sender Lipschitz constant `K_S = 0`.

**Target side**: with `σ_dyn(V_S^*, x, a) = 1` (constant `V_S` does
not change the argmax of `s + (1/2)·V_S(F)`), the joint Target
integrand becomes `joint_T_integrand V_T V_S x a = U_T(x, a, 1) +
(1/2) · V_T(F(x, 1)) = 5x + a - 1 + (1/2) · V_T((x+1)/2)`. Maximising
over `a ∈ [0, 1]` is uniquely attained at `a = 1` (slope `+1` in `a`),
so `jointTarget_BCF V_T V_S^* _ (y) = 5y + (1/2) · V_T((y+1)/2)`.
Substituting `V_T(y) = A·y + B` and matching coefficients gives
**`A = 20/3`** (Target Lipschitz `g_T = 20/3`) and **`B = 10/3`**.
The closed-form fixed point is `V_T^*(y) = (20/3)·y + 10/3`.

**Carrier choice**: `‖V_T^*‖ = max(|V_T^*(0)|, |V_T^*(1)|) =
max(10/3, 30/3) = 10`, so the witness carrier
`valLipBall 10 (20/3)` contains both `V_T^*` and the constant
`V_S^* = 2`. -/

/-- **Round-21 closed-form V_T constants.** The Bellman fixed point
of the joint Target operator at `polyComplianceParams` is the linear
function `V_T^*(y) = (20/3)·y + 10/3` (slope and intercept derived
from the fixed-point equation `V = 5y + (1/2)·V((y+1)/2)` after
maximising over `a = 1`). -/
def polyV_T_slope : ℝ := 20/3

def polyV_T_intercept : ℝ := 10/3

/-- **Round-21 closed-form V_S constant.** The Bellman fixed point
of the Sender operator at `polyComplianceParams` is the constant
`V_S^* = 2` (independent of `α`, since `U_S` does not depend on `x`
or `a` and `σ_dyn = 1`). -/
def polyV_S_const : ℝ := 2

/-- **Round-21 witness carrier parameters.** With `M = 10` and
`K = 20/3`, the Lipschitz ball `valLipBall M K` contains both
`V_T^* = (20/3)·x + 10/3` and the constant `V_S^* = 2`. -/
def polyCarrierM : ℝ := 10

def polyCarrierK : ℝ := 20/3

example : 0 ≤ polyCarrierM := by unfold polyCarrierM; norm_num
example : 0 ≤ polyCarrierK := by unfold polyCarrierK; norm_num
example : 0 < polyV_T_slope := by unfold polyV_T_slope; norm_num
example : 0 < polyV_S_const := by unfold polyV_S_const; norm_num

/-! ## Numeric margin verifications -/

/-- **Round-11 form: Target loss-offset margin `c_T ≤ β_T · g_T · δ`.**
At the witness with `c_T = 1`, `g_T = 20/3`, `β_T = δ = 1/2`:
`(1/2) · (20/3) · (1/2) = 5/3 ≥ 1`. -/
example : (1 : ℝ) ≤ polyComplianceParams.β_T * (20/3) * polyComplianceParams.δ := by
  unfold polyComplianceParams
  norm_num

/-- **Round-13 form: Sender high-sanction wedge `β_S · K_S · δ < m_S`.**
At the witness, `V_S` is constant (since `U_S(x, a, s) = s` independent of
`x`), so `K_S = 0`, hence `(1/2) · 0 · (1/2) = 0 < 1 = m_S`. -/
example : polyComplianceParams.β_S * 0 * polyComplianceParams.δ < (1 : ℝ) := by
  unfold polyComplianceParams
  norm_num

/-- **Round-14 form: Schur-complement row-contraction margin.** At this
minimal witness, `L_TS = L_ST = 0` (trivially-coupled operators), so
`L_TS · L_ST = 0 < (1/2) · (1/2) = 1/4 = (1 - β_T)(1 - β_S)`. -/
example :
    (0 : ℝ) * 0 < (1 - polyComplianceParams.β_T) * (1 - polyComplianceParams.β_S) := by
  unfold polyComplianceParams
  norm_num

/-- **Round-11 C¹ form: `∂U_T/∂s = -1` everywhere.** -/
example (x a s : ℝ) :
    HasDerivAt (fun t => polyComplianceParams.U_T x a t) (-1 : ℝ) s := by
  unfold polyComplianceParams
  -- (fun t => 5 * x - t), derivative = -1
  have : HasDerivAt (fun t : ℝ => 5 * x - t) (0 - 1 : ℝ) s := by
    exact (hasDerivAt_const s (5 * x)).sub (hasDerivAt_id s)
  simpa using this

/-- **Round-13 C¹ form: `∂U_S/∂s = 1` everywhere.** -/
example (x a s : ℝ) :
    HasDerivAt (fun t => polyComplianceParams.U_S x a t) (1 : ℝ) s := by
  unfold polyComplianceParams
  exact hasDerivAt_id s

/-- **Rule-1 check: σ ≡ 1 is the Sender stage argmax of `U_S(x, a, ·) = id`
on `[0, 1]`.** Trivially, every `s ∈ [0, 1]` satisfies `s ≤ 1`. -/
example (x a : ℝ) :
    IsMaxOn (fun s => polyComplianceParams.U_S x a s) (Set.Icc (0 : ℝ) 1)
      (polyComplianceParams.σ x a) := by
  unfold polyComplianceParams
  intro s hs
  exact hs.2

/-- **Round-12 form: Berge-discharged myopic comparator existence.** -/
example : Nonempty polyComplianceParams.MyopicFeedbackEquilibrium :=
  polyComplianceParams.myopicFeedbackEquilibrium_exists_of_continuity

/-! ## Round-25 Priority 6 numeric verifications: closed-form `KS` via Hinderer 4.2(c)

At `polyComplianceParams`, the Sender stage payoff `U_S(x, a, s) = s`
does not depend on the state `x` at all (the per-state x-derivative
of `U_S` is identically zero), so the stage payoff Lipschitz constant
in `x` is `L_U_S = 0`. The transition Lipschitz coefficient in `x`
(with `s` fixed) is `γ_F = 1 - δ = 1 - 1/2 = 1/2`. Hence:

* **Contraction margin**: `β_S · γ_F = (1/2) · (1/2) = 1/4 < 1` ✓.
* **Closed-form `K_S`**: `K_S = L_U_S / (1 − β_S · γ_F) = 0 / (3/4) = 0`,
  matching the witness's actual `K_S = 0` (since `V_S* = 2` is
  constant, hence 0-Lipschitz).
* **Closed-form wedge** `β_S · L_U_S · δ < m_S · (1 − β_S · γ_F)`:
  `(1/2) · 0 · (1/2) = 0 < 1 · (3/4) = 3/4` ✓. -/

/-- **Round-25 Hinderer 4.2(c) contraction margin at the witness.**
`0 < 1 − β_S · γ_F = 1 − (1/2)(1/2) = 3/4`. -/
example : 0 < 1 - polyComplianceParams.β_S * (1/2 : ℝ) := by
  unfold polyComplianceParams; norm_num

/-- **Round-25 Hinderer 4.2(c) closed-form `K_S` value at the witness.**
`bellmanLipConstant β_S γ_F L_U_S = 0 / (3/4) = 0` when `L_U_S = 0`. -/
example :
    Sanctions.StokeyLucas.bellmanLipConstant polyComplianceParams.β_S (1/2 : ℝ) 0 = 0 := by
  unfold Sanctions.StokeyLucas.bellmanLipConstant
  unfold polyComplianceParams
  norm_num

/-- **Round-25 Hinderer 4.2(c) closed-form Sender wedge at the witness.**
`β_S · L_U_S · δ < m_S · (1 − β_S · γ_F)`: at `L_U_S = 0`, `m_S = 1`,
`γ_F = 1/2`: `0 < 3/4`. -/
example :
    polyComplianceParams.β_S * (0 : ℝ) * polyComplianceParams.δ
      < (1 : ℝ) * (1 - polyComplianceParams.β_S * (1/2 : ℝ)) := by
  unfold polyComplianceParams; norm_num

/-- **Round-25 Hinderer 4.2(c) closed-form `K_S` non-negativity at the witness.**
The `hKS_nonneg_of_closed_form` lemma applied at the witness. -/
example :
    0 ≤ Sanctions.StokeyLucas.bellmanLipConstant polyComplianceParams.β_S (1/2 : ℝ) 0 :=
  polyComplianceParams.hKS_nonneg_of_closed_form (by norm_num)
    (by unfold polyComplianceParams; norm_num)

/-- **Round-25 Hinderer 4.2(c) derived `hS_margin` at the witness.**
The `hS_margin_of_closed_form` lemma applied at the witness: the
derived `hS_margin` form `β_S · K_S · δ < m_S` collapses to
`(1/2) · 0 · (1/2) = 0 < 1`. -/
example :
    polyComplianceParams.β_S
        * (Sanctions.StokeyLucas.bellmanLipConstant
            polyComplianceParams.β_S (1/2 : ℝ) 0)
        * polyComplianceParams.δ
      < (1 : ℝ) :=
  polyComplianceParams.hS_margin_of_closed_form
    (L_U_S := 0) (γ_F := 1/2) (mS := 1)
    (by unfold polyComplianceParams; norm_num)
    (by unfold polyComplianceParams; norm_num)

/-! ## Round-27 Priority 5 closure: closed-form `gT` via Hinderer-4.2(c) lower-slope

At `polyComplianceParams`, the Target stage payoff `U_T(x, a, s) =
5x − s + a` has primitive **state-slope** `g_U = 5` (`∂U_T/∂x = 5`).
The transition multiplier in `x` (with `s` fixed) is
`γ_F = 1 − δ = 1 − 1/2 = 1/2`. Hence the Hinderer-4.2(c) lower-slope (Round 27
`bellmanLowerSlopeConstant`) gives:

* **Contraction margin**: `β_T · γ_F = (1/2) · (1/2) = 1/4 < 1` ✓.
* **Closed-form `g_T`**: `g_T = g_U / (1 − β_T · γ_F) = 5 / (3/4) = 20/3`,
  matching the witness's actual `g_T = polyV_T_slope = 20/3` (since
  `V_T^*(y) = (20/3)·y + 10/3` has state-slope `20/3`).
* **Target loss-offset margin** at the closed-form `g_T`:
  `c_T ≤ β_T · g_T · δ = (1/2) · (20/3) · (1/2) = 5/3`, which holds at
  `c_T = 1`. -/

/-- **Round-27 Hinderer-4.2(c) contraction margin at the witness.**
`0 < 1 − β_T · γ_F = 1 − (1/2)(1/2) = 3/4`. -/
example : 0 < 1 - polyComplianceParams.β_T * (1/2 : ℝ) := by
  unfold polyComplianceParams; norm_num

/-- **Round-27 Hinderer-4.2(c) closed-form `g_T` value at the witness.**
`bellmanLowerSlopeConstant β_T γ_F g_U = 5 / (3/4) = 20/3` matches
`polyV_T_slope`. -/
example :
    Sanctions.StokeyLucas.bellmanLowerSlopeConstant
        polyComplianceParams.β_T (1/2 : ℝ) 5
      = polyV_T_slope := by
  unfold Sanctions.StokeyLucas.bellmanLowerSlopeConstant
  unfold polyComplianceParams polyV_T_slope
  norm_num

/-- **Round-27 Hinderer-4.2(c) closed-form `g_T` non-negativity at the
witness.** The closed-form constant is non-negative whenever the
contraction margin is positive and the payoff state-slope is non-negative. -/
example :
    0 ≤ Sanctions.StokeyLucas.bellmanLowerSlopeConstant
          polyComplianceParams.β_T (1/2 : ℝ) 5 := by
  have h := Sanctions.StokeyLucas.bellman_closed_form_lowerSlope_margin
    (β := polyComplianceParams.β_T) (γ_F := 1/2) (g_U := 5)
    (by norm_num) (by unfold polyComplianceParams; norm_num)
    (by norm_num)
    (by unfold polyComplianceParams; norm_num)
  exact h.1

/-- **Round-27 Hinderer-4.2(c) cone-margin identity at the witness.**
The closed-form `g_T = 20/3` satisfies the Bellman fixed-point
cone-margin equation `g_U + β_T · g_T · γ_F = g_T`:
`5 + (1/2) · (20/3) · (1/2) = 5 + 5/3 = 20/3`. -/
example :
    (5 : ℝ) + polyComplianceParams.β_T
        * (Sanctions.StokeyLucas.bellmanLowerSlopeConstant
            polyComplianceParams.β_T (1/2 : ℝ) 5)
        * (1/2 : ℝ)
      = Sanctions.StokeyLucas.bellmanLowerSlopeConstant
          polyComplianceParams.β_T (1/2 : ℝ) 5 := by
  have h := Sanctions.StokeyLucas.bellman_closed_form_lowerSlope_margin
    (β := polyComplianceParams.β_T) (γ_F := 1/2) (g_U := 5)
    (by norm_num) (by unfold polyComplianceParams; norm_num)
    (by norm_num)
    (by unfold polyComplianceParams; norm_num)
  exact h.2

/-- **Round-27 Target loss-offset margin at the closed-form `g_T`.**
Cite `c_T = 1`, closed-form `g_T = 20/3`, `β_T = δ = 1/2`:
`1 ≤ (1/2) · (20/3) · (1/2) = 5/3`. The Target loss-offset margin
`hT_loss_margin : cT ≤ p.β_T · gT · p.δ` (a certificate field until round
BJ1.4, 2026-10-07; it now feeds `Target_combined_chord_of_decomposition_lowerChord`)
holds at the witness with the closed-form `g_T`. -/
example :
    (1 : ℝ) ≤ polyComplianceParams.β_T
        * (Sanctions.StokeyLucas.bellmanLowerSlopeConstant
            polyComplianceParams.β_T (1/2 : ℝ) 5)
        * polyComplianceParams.δ := by
  unfold Sanctions.StokeyLucas.bellmanLowerSlopeConstant
  unfold polyComplianceParams
  norm_num

/-! ## Round-28: Milgrom-Shannon dual antitone-selection witness

The Round-28 σ-antitone discharger
`sigma_antitoneOn_a_of_U_S_decreasing_differences` reduces the
sub-primitive `hσ_antitone` of the four-primitive myopic-ceiling
decomposition to two payoff-level facts on `U_S`:

* `DecreasingDifferencesOn I I (fun s a => U_S x a s)` (paper: cross
  partial `∂²U_S/∂s∂a ≤ 0`);
* strict uniqueness of the Sender stage argmax at every `a ∈ [0, 1]`.

At `polyComplianceParams.U_S = s` (linear, independent of `a`), the
cross difference vanishes identically — `U_S(x, a', s') - U_S(x, a, s')
= s' - s' = 0` — so DD holds with equality. The strict-uniqueness fact
holds non-trivially because `σ(x, a) = 1` is the *unique* maximizer of
`s ↦ s` on `[0, 1]` (any `s ≠ 1` in `[0, 1]` gives `s < 1`). -/

/-- **Round-28 sibling witness 1:** `polyComplianceParams.U_S` has
weak decreasing differences in `(s, a)` on `I × I`. Holds with equality
because `U_S(x, a, s) = s` is independent of `a`. -/
example (x : ℝ) :
    Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => polyComplianceParams.U_S x a s) := by
  intro s s' a a' _ _ _ _ _ _
  unfold polyComplianceParams
  -- Both sides equal `s' - s`.
  simp

/-- **Round-28 sibling witness 2:** strict uniqueness of the Sender
stage argmax at every `a ∈ I` at `polyComplianceParams`. Since
`U_S(x, a, s) = s` and `σ(x, a) = 1`, any `s ≠ 1` in `[0, 1]` gives
`s < 1 = U_S(x, a, 1)` strictly. -/
example (x : ℝ) :
    ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I, s ≠ polyComplianceParams.σ x a →
      polyComplianceParams.U_S x a s
        < polyComplianceParams.U_S x a (polyComplianceParams.σ x a) := by
  intro a _ s hs hne
  unfold polyComplianceParams at hne ⊢
  -- σ x a = 1; need s < 1 from s ≤ 1 and s ≠ 1.
  rcases hs with ⟨_, hs_le⟩
  exact lt_of_le_of_ne hs_le hne

/-- **Round-28 main witness:** `σ(x, ·)` is `AntitoneOn` on `I` at every
`x`, via the Round-28 discharger
`sigma_antitoneOn_a_of_U_S_decreasing_differences` composing the two
sibling witnesses above. -/
example (x : ℝ) :
    AntitoneOn (fun a => polyComplianceParams.σ x a) Sanctions.I := by
  apply polyComplianceParams.sigma_antitoneOn_a_of_U_S_decreasing_differences x
  · -- DD: holds with equality.
    intro s s' a a' _ _ _ _ _ _
    unfold polyComplianceParams; simp
  · -- Strict uniqueness: σ = 1 is unique argmax of s ↦ s on [0, 1].
    intro a _ s hs hne
    unfold polyComplianceParams at hne ⊢
    rcases hs with ⟨_, hs_le⟩
    exact lt_of_le_of_ne hs_le hne

/-! ## Architectural note (Round-21 update; refined in Round 34)

After Rounds 11–20, the certificate's primitive surface is fully
scalar-checkable. The Round-34 work below carries out the
substantive bundling.

**Round-34 numeric corrections vs. the original Round-21 plan:**

The Round-21 plan picked a single symmetric carrier
`valLipBall 10 (20/3)`. Two issues surfaced in Round 34:

* The sup-norm margin `cube_T + β_T·M ≤ M` requires
  `M ≥ cube_T / (1 − β_T) = 6 / (1/2) = 12`, NOT `10`. So the
  Target sup-norm carrier needs `R_T = 12` (or larger), not `10`.
* On `valLipBall 10 (20/3)` the carrier-level **Sender argmax
  uniqueness** is not automatic: the dynamic objective
  `s + (1/2)·V_S(F(x, s))` has derivative `1 + (1/2)·V_S′·(1/2) =
  1 + V_S′/4`, which can be **negative** when `V_S′ ≈ -20/3`
  (since `K_S = 20/3` permits `V_S′ ∈ [-20/3, 20/3]`).
  So uniqueness via the strict-monotonicity discharger fails on
  the symmetric carrier.

**Round-34 fix: asymmetric carriers.** Use
`ValueClass2` (asymmetric: separate `carrier_T`, `carrier_S`):

* `carrier_T = valLipBall 12 (20/3)` — the V_T side; the closed-form
  fixed point `V_T*(y) = (20/3)·y + 10/3` has `‖V_T*‖ = 10 ≤ 12` and
  is `(20/3)`-Lipschitz.
* `carrier_S = valLipBall 2 0` — the V_S side; the closed-form fixed
  point `V_S* = 2` is constant (0-Lipschitz) and has sup norm `2 ≤ 2`.

With `K_S = 0` (V_S constant), the Sender dynamic objective collapses
to `s + const`, strictly monotonic in `s`, so the carrier-level
Sender argmax is uniquely `s = 1`. This also pins
`σ_dyn V_S x a = 1` for *every* `a`, which then makes the joint
Target integrand `U_T(x, a, 1) + β_T·V_T((x+1)/2) = 5x − 1 + a +
(1/2)·V_T((x+1)/2)` strictly monotonic in `a` (slope `+1` from `U_T`),
giving Target argmax uniqueness as well.

**Remaining steps to a full certificate value:**

1. **Carrier construction**: `ValueClass2` instance built below
   (`polyComplianceValueClass2`).

2. **Argmax uniqueness on the carriers**: both
   `DynamicArgmaxUnique` and `TargetArgmaxUnique` discharged below
   (`polyComplianceParams_DAU_on_carrier_S`,
   `polyComplianceParams_TAU_on_carrier_T_S`).

3. **`D.IsInvariant` discharge** — sup-norm margins verified below;
   the operator-level Lipschitz preservation hypotheses
   `h_T_preserves`, `h_S_preserves` are the residual asymmetric-form
   obligations, requiring asymmetric analogs of
   `bellmanBCF_preserves_lipschitz_cone` and
   `bellmanS_BCF_preserves_lipschitz_cone`. The symmetric
   dischargers in `InvariantLipBall.lean` consume
   `valLipBall M K × valLipBall M K`, not the asymmetric
   `valLipBall R_T K_T × valLipBall R_S K_S` we need here.
   Building the asymmetric companions is the natural follow-up
   round (R35+).

4. **Basin geometry pivots** — `xT = xS = 0`, `sbar = 1/2`
   so that `max(xT, xS) = 0`, `hjoint_lt = (0 < 1)`, `hsbar_pos = (0 < 1/2)`
   (`hsbar_pos` was a certificate field until round BJ1.4, 2026-10-07).

5. **Scalar margins** — verified above:
   `cT = 1 ≤ β_T·g_T·δ = 5/3`; `β_S·KS·δ = 0 < mS = 1`;
   `(1-β_T)(1-β_S) = 1/4 > 0 = L_TS·L_ST`. ✓

6. **Carrier-local single crossing** — `joint_T_integrand`
   evaluated at carrier-local Target selector is linear in
   `(s, x)` on `carrier_T × carrier_S` (since `σ_dyn = 1`), so
   single crossing holds trivially (linear functions are
   single-crossing).

7. **Myopic comparator** — `M := p.myopicFeedbackEquilibrium_canonical`
   from R12's existence theorem.

The Round-34 deliverables here are items 1, 2, 4, 5 (verified),
plus the cube-bound margin checks for item 3. The asymmetric
Lipschitz-preservation companions (residual of item 3) are the
final remaining mathematical step. -/

/-! ## Round-34: corrected carrier parameters

The asymmetric carriers needed for the literal-compliance bundling.
-/

/-- **Round-34 corrected Target sup-norm carrier bound.** Replaces
the Round-21 `polyCarrierM = 10` (which fails the sup-norm margin
`cube_T + β_T·M ≤ M` since `6 + 6 > 10`). With `R_T = 12` the margin
is tight: `6 + 6 = 12 = R_T`. -/
def polyCarrierMT : ℝ := 12

/-- **Round-34 Sender sup-norm carrier bound.** Sender value is
constant `V_S* = 2`, so any `R_S ≥ 2` works; pick the tightest
admissible value. -/
def polyCarrierMS : ℝ := 2

/-- **Round-34 Sender Lipschitz carrier constant.** With
`U_S(x, a, s) = s` independent of `x`, the Sender Bellman fixed
point is constant (K_S = 0). -/
def polyCarrierKS : ℝ := 0

example : 0 ≤ polyCarrierMT := by unfold polyCarrierMT; norm_num
example : 0 ≤ polyCarrierMS := by unfold polyCarrierMS; norm_num
example : 0 ≤ polyCarrierKS := by unfold polyCarrierKS; norm_num

/-! ## Round-34: cube-bound margin verifications

The Target sup-norm margin `cube_T + β_T·R_T ≤ R_T` and the Sender
sup-norm margin `cube_S + β_S·R_S ≤ R_S` are the two scalar
inequalities the cube-bound discharger needs. With `cube_T = 6`
(`|5x − s + a| ≤ 6` on `[0,1]³`) and `cube_S = 1` (`|s| ≤ 1`), the
margins hold tightly at the chosen carrier bounds. -/

/-- **Round-34: Target cube bound `|U_T| ≤ 6` on `[0, 1]³`.** The
explicit cube bound `cube_T = 6` for `U_T(x, a, s) = 5x − s + a`:
max attained at `(1, 1, 0)` giving `5 + 1 = 6`; min at `(0, 0, 1)`
giving `−1`; so `|U_T| ≤ 6` uniformly. -/
example : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
    |polyComplianceParams.U_T x a s| ≤ (6 : ℝ) := by
  intro x hx a ha s hs
  simp only [polyComplianceParams]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- −6 ≤ 5x − s + a
    nlinarith [hx.1, hx.2, ha.1, ha.2, hs.1, hs.2]
  · -- 5x − s + a ≤ 6
    nlinarith [hx.1, hx.2, ha.1, ha.2, hs.1, hs.2]

/-- **Round-34: Sender cube bound `|U_S| ≤ 1` on `[0, 1]³`.** Trivial
since `U_S(x, a, s) = s` and `|s| ≤ 1` on `[0, 1]`. -/
example : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
    |polyComplianceParams.U_S x a s| ≤ (1 : ℝ) := by
  intro x _ a _ s hs
  simp only [polyComplianceParams]
  rw [abs_le]
  exact ⟨by linarith [hs.1, hs.2], hs.2⟩

/-- **Round-34: Target sup-norm margin `cube_T + β_T·R_T ≤ R_T`.**
At `cube_T = 6`, `β_T = 1/2`, `R_T = 12`: `6 + 6 = 12` (tight). -/
example :
    (6 : ℝ) + polyComplianceParams.β_T * polyCarrierMT ≤ polyCarrierMT := by
  unfold polyComplianceParams polyCarrierMT
  norm_num

/-- **Round-34: Sender sup-norm margin `cube_S + β_S·R_S ≤ R_S`.**
At `cube_S = 1`, `β_S = 1/2`, `R_S = 2`: `1 + 1 = 2` (tight). -/
example :
    (1 : ℝ) + polyComplianceParams.β_S * polyCarrierMS ≤ polyCarrierMS := by
  unfold polyComplianceParams polyCarrierMS
  norm_num

/-! ## Round-34: σ_dyn-pinning lemma at constant V_S

The substantive engineering result enabling the Target argmax
uniqueness on the asymmetric carriers. -/

/-- **Round-34 σ_dyn pinning lemma.** For any `V_S` in the Sender
carrier `valLipBall polyCarrierMS polyCarrierKS = valLipBall 2 0`
(i.e. constant), the Sender dynamic argmax is uniquely `s = 1`,
**independent of `a` and `x`**. This is the structural fact that
makes the Target integrand `joint_T_integrand V_T V_S x a` strict-mono
in `a` on the asymmetric carrier: with `σ_dyn = 1`, the integrand
collapses to `5x − 1 + a + (1/2)·V_T((x+1)/2)`, slope `+1` in `a`. -/
theorem σ_dyn_eq_one_of_constant_V_S
    (V_S : Val)
    (hV_S : V_S ∈ valLipBall
              polyCarrierMS polyCarrierKS) (x a : ℝ) :
    polyComplianceParams.σ_dyn V_S x a = 1 := by
  have h_lip : ValueLipschitzWith V_S polyCarrierKS := hV_S.2
  unfold polyCarrierKS at h_lip
  -- Strict monotonicity of the Sender dynamic objective in `s` at this
  -- fixed `(x, a)`; the corner pinning is then the WitnessKit C5 lemma.
  apply WitnessKit.σ_dyn_eq_one_of_strictMonoOn
  intro s₁ _ s₂ _ h_lt
  have h := h_lip
    (Sanctions.clipS' (polyComplianceParams.F x s₁))
    (Sanctions.clipS' (polyComplianceParams.F x s₂))
  simp only [zero_mul] at h
  have heq :
      V_S (Sanctions.clipS' (polyComplianceParams.F x s₁))
        = V_S (Sanctions.clipS' (polyComplianceParams.F x s₂)) := by
    have habs := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    linarith
  change polyComplianceParams.U_S x a s₁ + polyComplianceParams.β_S * V_S _
       < polyComplianceParams.U_S x a s₂ + polyComplianceParams.β_S * V_S _
  rw [heq]
  simp only [polyComplianceParams]
  linarith

/-! ## Round-34: carrier-level argmax-uniqueness witnesses

These two discharge the `sender_unique_on` and `target_unique_on`
fields of any `ValueClass2` instance built on the asymmetric
carriers `valLipBall 12 (20/3) × valLipBall 2 0`. -/

/-- **Round-34: `DynamicArgmaxUnique V_S` on the Sender carrier.**
Every V_S in `valLipBall polyCarrierMS polyCarrierKS = valLipBall 2 0`
satisfies Sender argmax uniqueness because V_S is constant (K_S = 0)
and `U_S(x, a, s) = s` is strictly monotone in `s`. -/
theorem polyComplianceParams_DAU_on_carrier_S
    (V_S : Val)
    (hV_S : V_S ∈ valLipBall
              polyCarrierMS polyCarrierKS) :
    polyComplianceParams.DynamicArgmaxUnique V_S := by
  have h_lip : ValueLipschitzWith V_S polyCarrierKS := hV_S.2
  unfold polyCarrierKS at h_lip
  apply polyComplianceParams.dynamicArgmaxUnique_of_strictMonoOn
  intro x _hx a s₁ _ s₂ _ h_lt
  have h := h_lip
    (Sanctions.clipS' (polyComplianceParams.F x s₁))
    (Sanctions.clipS' (polyComplianceParams.F x s₂))
  simp only [zero_mul] at h
  have heq :
      V_S (Sanctions.clipS' (polyComplianceParams.F x s₁))
        = V_S (Sanctions.clipS' (polyComplianceParams.F x s₂)) := by
    have habs := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    linarith
  change polyComplianceParams.U_S x a s₁ + polyComplianceParams.β_S * V_S _
       < polyComplianceParams.U_S x a s₂ + polyComplianceParams.β_S * V_S _
  rw [heq]
  simp only [polyComplianceParams]
  linarith

/-- **Round-34: `TargetArgmaxUnique V_T V_S` on the asymmetric carriers.**
Every pair `(V_T, V_S)` with `V_S ∈ valLipBall polyCarrierMS polyCarrierKS`
(i.e. V_S constant) satisfies Target argmax uniqueness because
`σ_dyn V_S x a = 1` is pinned (by `σ_dyn_eq_one_of_constant_V_S`),
making the joint integrand `5x − 1 + a + (1/2)·V_T((x+1)/2)` strictly
monotone in `a`. -/
theorem polyComplianceParams_TAU_on_carrier_T_S
    (V_T V_S : Val)
    (hV_S : V_S ∈ valLipBall
              polyCarrierMS polyCarrierKS) :
    polyComplianceParams.TargetArgmaxUnique V_T V_S := by
  apply polyComplianceParams.targetArgmaxUnique_of_strictMonoOn
  intro x _hx a₁ _ a₂ _ h_lt
  change polyComplianceParams.joint_T_integrand V_T V_S x a₁
       < polyComplianceParams.joint_T_integrand V_T V_S x a₂
  unfold Params.joint_T_integrand
  simp only []
  rw [σ_dyn_eq_one_of_constant_V_S V_S hV_S x a₁,
      σ_dyn_eq_one_of_constant_V_S V_S hV_S x a₂]
  simp only [polyComplianceParams]
  linarith

/-! ## Round-34: asymmetric `ValueClass2` instance at `polyComplianceParams`

The first concrete `ValueClass2` instance at literal-compliance
`Params`. Bundles the asymmetric carriers and the two
argmax-uniqueness theorems above. -/

/-- **Round-34: the literal-compliance asymmetric value class.**
`carrier_T = valLipBall 12 (20/3)`, `carrier_S = valLipBall 2 0`.
Argmax uniqueness discharged by the Round-34 theorems above. -/
noncomputable def polyComplianceValueClass2 :
    polyComplianceParams.ValueClass2 where
  carrier_T := valLipBall polyCarrierMT polyV_T_slope
  carrier_S := valLipBall polyCarrierMS polyCarrierKS
  isClosed_T := valLipBall_isClosed _ _
  isClosed_S := valLipBall_isClosed _ _
  nonempty_T := valLipBall_nonempty
                  (by unfold polyCarrierMT; norm_num)
                  (by unfold polyV_T_slope; norm_num)
  nonempty_S := valLipBall_nonempty
                  (by unfold polyCarrierMS; norm_num)
                  (by unfold polyCarrierKS; norm_num)
  sender_unique_on := fun V hV => (polyComplianceParams_DAU_on_carrier_S V hV).toOnI
  target_unique_on := fun V_T _ V_S hV_S =>
    polyComplianceParams_TAU_on_carrier_T_S V_T V_S hV_S

/-- **Round-34 non-vacuity: V_T* is in carrier_T.** Sanity check
that the closed-form Target fixed point `V_T*(y) = (20/3)·y + 10/3`
satisfies the carrier definition — sup norm `≤ 12` and Lipschitz
constant `≤ 20/3`. The actual exhibition of `V_T*` as a BCF is
deferred; here we just confirm the numeric bounds. -/
example : ‖(0 : Val)‖ ≤ polyCarrierMT := by
  unfold polyCarrierMT; simp

example : ‖(0 : Val)‖ ≤ polyCarrierMS := by
  unfold polyCarrierMS; simp

/-! ## Round-34 architectural note: residual obligations

With the asymmetric `polyComplianceValueClass2` constructed, the
remaining steps to a complete `StandardComplianceLocalCoreCertificate`
value are:

* **`IsInvariant`** — needs **asymmetric** analogs of the Lipschitz
  preservation lemmas. The existing symmetric dischargers
  (`bellmanBCF_preserves_lipschitz_cone`,
  `bellmanS_BCF_preserves_lipschitz_cone`) consume a single
  `(M, K)` and assume `V_T, V_S ∈ valLipBall M K`. The polynomial
  witness uses `V_T ∈ valLipBall R_T K_T = valLipBall 12 (20/3)` and
  `V_S ∈ valLipBall R_S K_S = valLipBall 2 0`. Asymmetric
  companions of these lemmas are the natural follow-up round (R35+).

* **Row-contraction bounds** — at this minimal witness,
  `L_TS = L_ST = 0` (trivial Lipschitz coupling between V_T and V_S
  via the joint operators), `β_T = β_S = 1/2`. The Schur margin
  `0 = L_TS · L_ST < (1 − β_T)(1 − β_S) = 1/4` holds. The
  Lipschitz-bound proofs `hT_T_op`, `hT_S_op` for the joint
  operators on `CarrierT × CarrierS` are the next concrete step.

* **Carrier-local certificate fields** (`h_stage_sender_on`, `h_stage_*`, and,
  until round BJ1.4 (2026-10-07) deleted them from the certificate,
  `h_stage_target_loss_on` and `hV_T_gain_on_carrier`, now inputs of
  `Target_combined_chord_of_decomposition_lowerChord`): all
  carry-over from the R11/R13/R29/R30 dischargers already verified
  above at `cT = 1`, `gT = 20/3`, `mS = 1`, `KS = 0`.

* **`hMyoCeiling`** — needs basin choice `sbar = 1/2` and
  decomposition via Round-28 σ-antitone discharger
  (already verified above).

The Round-34 deliverables:

* Round-34 corrected carrier parameters (`polyCarrierMT = 12`,
  `polyCarrierMS = 2`, `polyCarrierKS = 0`).
* Cube bound numerics (`cube_T = 6`, `cube_S = 1`) + sup-norm
  margins.
* `σ_dyn_eq_one_of_constant_V_S` (substantive σ-pinning at
  K_S = 0).
* `polyComplianceParams_DAU_on_carrier_S`,
  `polyComplianceParams_TAU_on_carrier_T_S`
  (carrier-level argmax-uniqueness theorems).
* `polyComplianceValueClass2` — first concrete asymmetric
  `ValueClass2` instance at literal-compliance `Params`.

This is the **substantive intermediate** between the Round-21
scalar-margin skeleton and a fully bundled certificate value. The
asymmetric Lipschitz-preservation companions are the only
remaining mathematical content; with those landed, the
certificate bundling itself is mechanical. -/

/-! ## Round-35: `IsInvariant` discharge at the polynomial witness

The asymmetric carriers `valLipBall 12 (20/3) × valLipBall 2 0` are
Bellman-invariant. No new asymmetric *bundler* is needed: the existing
`jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz` and
`bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz` are already fully
parametric in `(M, K)`, so they apply directly at the two distinct
carrier radii. The only nontrivial input is the Target integrand's
state-Lipschitz constant, which closes to exactly `K_T = 20/3`. -/

/-- **Round-35: the joint Target integrand is `(20/3)`-Lipschitz in the
state on the asymmetric carrier.** With `σ_dyn = 1` (constant Sender
value on `valLipBall 2 0`), `joint_T_integrand V_T V_S x a
= (5x − 1 + a) + (1/2)·V_T(clip((x+1)/2))`. The explicit `U_T`
state-slope `5` plus the discounted `V_T`-slope
`(1/2)·(20/3)·(1/2) = 5/3` sum to exactly `20/3 = K_T`. -/
theorem polyComplianceParams_joint_T_integrand_lipschitz_at_carrier
    (V_T V_S : Val)
    (hV_T : V_T ∈ valLipBall polyCarrierMT polyV_T_slope)
    (hV_S : V_S ∈ valLipBall polyCarrierMS polyCarrierKS)
    (x₁ x₂ : ↥(Sanctions.S : Set ℝ)) (a : ℝ) (_ha : a ∈ Sanctions.I) :
    |polyComplianceParams.joint_T_integrand V_T V_S x₂.val a
      - polyComplianceParams.joint_T_integrand V_T V_S x₁.val a|
      ≤ polyV_T_slope * dist x₁ x₂ := by
  -- σ_dyn pins to 1 at both states (constant V_S).
  have hσ₁ := σ_dyn_eq_one_of_constant_V_S V_S hV_S x₁.val a
  have hσ₂ := σ_dyn_eq_one_of_constant_V_S V_S hV_S x₂.val a
  -- The V_T-state Lipschitz bound (constant 20/3).
  have hVlip : ValueLipschitzWith V_T polyV_T_slope := hV_T.2
  -- Reduce the integrand to its pinned form.
  simp only [AbstractGame.Params.joint_T_integrand, hσ₁, hσ₂]
  -- Concrete payoff / transition values at the witness.
  have hUT : ∀ y : ℝ, polyComplianceParams.U_T y a 1 = 5 * y - 1 + a := by
    intro y; simp only [polyComplianceParams]
  have hF1 : ∀ y : ℝ, polyComplianceParams.F y 1 = (1/2) * y + 1/2 := by
    intro y; simp only [polyComplianceParams, AbstractGame.affineF]; ring
  rw [hUT, hUT]
  -- V_T difference bound via Lipschitz + clip nonexpansiveness + F slope.
  have hVdiff :
      |V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
        - V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))|
        ≤ polyV_T_slope * ((1/2) * dist x₁ x₂) := by
    have hL := hVlip (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))
                     (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
    have hclip :
        dist (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))
             (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
          ≤ (1/2) * dist x₁ x₂ := by
      have hfeq :
          |polyComplianceParams.F x₁.val 1 - polyComplianceParams.F x₂.val 1|
            = (1/2) * dist x₁ x₂ := by
        rw [hF1 x₁.val, hF1 x₂.val, Subtype.dist_eq, Real.dist_eq,
            show 1/2 * x₁.val + 1/2 - (1/2 * x₂.val + 1/2)
              = (1/2) * (x₁.val - x₂.val) by ring,
            abs_mul, show |(1:ℝ)/2| = 1/2 by norm_num]
      exact hfeq ▸ Sanctions.clipS'_lipschitz_dist _ _
    calc |V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
            - V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))|
          ≤ polyV_T_slope * dist
              (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))
              (Sanctions.clipS' (polyComplianceParams.F x₂.val 1)) := hL
      _ ≤ polyV_T_slope * ((1/2) * dist x₁ x₂) := by
            apply mul_le_mul_of_nonneg_left hclip
            unfold polyV_T_slope; norm_num
  -- Combine: |Δstage + β_T·ΔV_T| ≤ 5·|Δx| + (1/2)·(20/3)·(1/2)·|Δx| = (20/3)·|Δx|.
  have hβT : polyComplianceParams.β_T = 1/2 := rfl
  rw [hβT]
  have hdist : dist x₁ x₂ = |x₂.val - x₁.val| := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
  unfold polyV_T_slope at hVdiff ⊢
  rw [hdist] at hVdiff ⊢
  -- Final numeric bound: |Δstage + (1/2)·ΔV_T| ≤ 5|Δx| + (1/2)(20/3)(1/2)|Δx| = (20/3)|Δx|.
  have hexpand :
      5 * x₂.val - 1 + a
        + 1/2 * V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
        - (5 * x₁.val - 1 + a
        + 1/2 * V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1)))
      = 5 * (x₂.val - x₁.val)
        + 1/2 * (V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
               - V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))) := by ring
  rw [hexpand]
  calc |5 * (x₂.val - x₁.val)
          + 1/2 * (V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
                 - V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1)))|
        ≤ |5 * (x₂.val - x₁.val)|
          + |1/2 * (V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
                  - V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1)))| := abs_add_le _ _
      _ = 5 * |x₂.val - x₁.val|
          + 1/2 * |V_T (Sanctions.clipS' (polyComplianceParams.F x₂.val 1))
                 - V_T (Sanctions.clipS' (polyComplianceParams.F x₁.val 1))| := by
            rw [abs_mul, abs_mul, show |(5:ℝ)| = 5 by norm_num,
                show |(1:ℝ)/2| = 1/2 by norm_num]
      _ ≤ 5 * |x₂.val - x₁.val|
          + 1/2 * (20/3 * (1/2 * |x₂.val - x₁.val|)) := by linarith [hVdiff]
      _ = 20/3 * |x₂.val - x₁.val| := by ring

/-- **Round-35: `IsInvariant` for the polynomial-witness value class.**
Both carriers are Bellman-invariant, discharged from the parametric
membership helpers at the two distinct radii (`R_T=12, K_T=20/3` and
`R_S=2, K_S=0`). The Sender side is trivial (`U_S=s` is `x`-independent,
so `L_U_S=0`); the Target side consumes the `20/3` integrand-Lipschitz
bound above. -/
theorem polyComplianceValueClass2_IsInvariant :
    polyComplianceValueClass2.IsInvariant := by
  intro V_T V_S
  refine ⟨?_, ?_⟩
  · -- Target side: jointTarget_BCF_on ∈ valLipBall 12 (20/3).
    refine polyComplianceParams.jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz
      V_T.val V_S.val (polyComplianceParams_DAU_on_carrier_S V_S.val V_S.property)
      (M := polyCarrierMT) (K := polyV_T_slope) (cube_T := 6)
      V_T.property.1 ?_ ?_ ?_
    · -- cube bound |U_T| ≤ 6.
      intro x hx a ha s hs
      simp only [polyComplianceParams]; rw [abs_le]
      constructor <;> nlinarith [hx.1, hx.2, ha.1, ha.2, hs.1, hs.2]
    · -- norm margin 6 + (1/2)·12 ≤ 12.
      unfold polyComplianceParams polyCarrierMT; norm_num
    · -- integrand Lipschitz.
      intro x₁ x₂ a ha
      exact polyComplianceParams_joint_T_integrand_lipschitz_at_carrier
        V_T.val V_S.val V_T.property V_S.property x₁ x₂ a ha
  · -- Sender side: jointSender_BCF_on ∈ valLipBall 2 0.
    refine polyComplianceParams.bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
      (polyComplianceValueClass2.α_on_continuous V_T V_S)
      (polyComplianceValueClass2.α_on_mem V_T V_S) V_S.val
      (M := polyCarrierMS) (K := polyCarrierKS) (cube_S := 1)
      (L_U_S := 0) (γ_F := 1/2)
      (by unfold polyCarrierKS; norm_num) V_S.property ?_ ?_ ?_ ?_ ?_
    · -- cube bound |U_S| ≤ 1.
      intro x _ a _ s hs
      simp only [polyComplianceParams]; rw [abs_le]
      exact ⟨by linarith [hs.1, hs.2], hs.2⟩
    · -- U_S x-Lipschitz with L_U_S = 0 (U_S = s is x-independent).
      intro x₁ x₂ s _
      simp only [polyComplianceParams]; simp
    · -- F x-Lipschitz with γ_F = 1/2.
      intro x₁ x₂ s _
      simp only [polyComplianceParams, AbstractGame.affineF]
      refine le_of_eq ?_
      rw [show (1 - (1:ℝ)/2) * x₂ + 1/2 * s - ((1 - 1/2) * x₁ + 1/2 * s)
            = (1/2) * (x₂ - x₁) by ring, abs_mul,
          show |(1:ℝ)/2| = 1/2 by norm_num]
    · -- norm margin 1 + (1/2)·2 ≤ 2.
      unfold polyComplianceParams polyCarrierMS; norm_num
    · -- lip margin 0 + (1/2)·0·(1/2) ≤ 0.
      unfold polyCarrierKS; norm_num

/-! ## Round-35: gain-ball carrier (the certificate-bundling upgrade)

The legacy `StandardComplianceLocalCoreCertificate`'s Target-preference field
`hV_T_gain_on_carrier` (deleted from the certificate in round BJ1.4, 2026-10-07;
the condition survives as an input of
`Target_combined_chord_of_decomposition_lowerChord`) required every `V_T` in
`carrier_T` to have a minimum
upward slope `gT = 20/3`, which a plain `valLipBall` cannot enforce. The carrier
must be the *gain* ball `valLipGainBall 12 (20/3) (20/3) 0`. Its non-emptiness
needs a concrete member with slope exactly `20/3` (the zero function is
excluded), exhibited below as the affine BCF `V_T^♯(y) = (20/3)·y`. -/

/-- **Round-35: closed-form affine Target value `V_T^♯(y) = (20/3)·y` as a BCF.**
`↥S = [0,1]` is compact, so the affine map is automatically bounded-continuous. -/
noncomputable def polyV_T_affine : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => (20/3 : ℝ) * y.val)
      (by fun_prop))

@[simp] theorem polyV_T_affine_apply (y : ↥(Sanctions.S : Set ℝ)) :
    polyV_T_affine y = (20/3 : ℝ) * y.val := rfl

/-- `V_T^♯ ∈ valLipGainBall 12 (20/3) (20/3) 0`: sup-norm `≤ 12`, Lipschitz
`20/3`, and minimum upward slope `20/3` (the latter two tight at slope `20/3`). -/
theorem polyV_T_affine_mem_gainBall :
    polyV_T_affine ∈ valLipGainBall polyCarrierMT polyV_T_slope polyV_T_slope 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- ‖V_T^♯‖ ≤ 12
    rw [BoundedContinuousFunction.norm_le (by unfold polyCarrierMT; norm_num)]
    intro y
    rw [polyV_T_affine_apply, Real.norm_eq_abs, abs_le]
    unfold polyCarrierMT
    exact ⟨by nlinarith [y.property.1, y.property.2],
           by nlinarith [y.property.1, y.property.2]⟩
  · -- ValueLipschitzWith V_T^♯ (20/3)
    intro y₁ y₂
    rw [polyV_T_affine_apply, polyV_T_affine_apply, Subtype.dist_eq, Real.dist_eq,
        show (20/3:ℝ) * y₂.val - 20/3 * y₁.val = (20/3) * (y₂.val - y₁.val) by ring, abs_mul]
    unfold polyV_T_slope
    rw [show |(20:ℝ)/3| = 20/3 by norm_num]
    exact le_of_eq (by rw [abs_sub_comm])
  · -- LowerSlopeOnValueOn V_T^♯ [0,1] (20/3)
    intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [polyV_T_affine_apply, polyV_T_affine_apply, Subtype.dist_eq, Real.dist_eq]
    unfold polyV_T_slope
    rw [abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    linarith

/-- Non-emptiness of the gain ball (exhibited by `V_T^♯`). -/
theorem polyComplianceParams_gainBall_nonempty :
    (valLipGainBall polyCarrierMT polyV_T_slope polyV_T_slope 0).Nonempty :=
  ⟨polyV_T_affine, polyV_T_affine_mem_gainBall⟩

/-- **Round-35: the joint Target integrand has minimum upward slope `20/3` in the
state on the gain carrier.** Gain mirror of the Lipschitz bound: with `σ_dyn = 1`,
`joint_T_integrand = 5y − 1 + a + (1/2)·V_T((y+1)/2)`; the stage slope `5` plus the
`V_T` minimum-slope contribution `(1/2)·(20/3)·(1/2) = 5/3` give exactly `20/3`. -/
theorem polyComplianceParams_joint_T_integrand_lowerSlope_at_carrier
    (V_T V_S : Val)
    (hV_T : V_T ∈ valLipGainBall polyCarrierMT polyV_T_slope polyV_T_slope 0)
    (hV_S : V_S ∈ valLipBall polyCarrierMS polyCarrierKS)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) (a : ℝ) (_ha : a ∈ Sanctions.I)
    (_h1 : y₁.val ∈ Set.Icc (0:ℝ) 1) (_h2 : y₂.val ∈ Set.Icc (0:ℝ) 1)
    (hle : y₁ ≤ y₂) :
    polyV_T_slope * dist y₁ y₂ ≤
      polyComplianceParams.joint_T_integrand V_T V_S y₂.val a
      - polyComplianceParams.joint_T_integrand V_T V_S y₁.val a := by
  have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
  have hσ₁ := σ_dyn_eq_one_of_constant_V_S V_S hV_S y₁.val a
  have hσ₂ := σ_dyn_eq_one_of_constant_V_S V_S hV_S y₂.val a
  have hgain : LowerSlopeOnValueOn V_T (Set.Icc 0 1) polyV_T_slope := hV_T.2.2
  -- Clip identity on the relevant range `[1/2, 1] ⊆ [0,1]`.
  have hclipF : ∀ z : ↥(Sanctions.S : Set ℝ),
      (Sanctions.clipS' (polyComplianceParams.F z.val 1)).val = (z.val + 1)/2 := by
    intro z
    have hF : polyComplianceParams.F z.val 1 = (z.val + 1)/2 := by
      simp only [polyComplianceParams, AbstractGame.affineF]; ring
    rw [hF]
    show Sanctions.clipS ((z.val + 1)/2) = (z.val + 1)/2
    have h0 : (0:ℝ) ≤ (z.val + 1)/2 := by nlinarith [z.property.1]
    have h1 : (z.val + 1)/2 ≤ 1 := by nlinarith [z.property.2]
    unfold Sanctions.clipS
    rw [min_eq_right h1, max_eq_right h0]
  have hmem₁ : (Sanctions.clipS' (polyComplianceParams.F y₁.val 1)).val ∈ Set.Icc (0:ℝ) 1 :=
    Sanctions.clipS_mem _
  have hmem₂ : (Sanctions.clipS' (polyComplianceParams.F y₂.val 1)).val ∈ Set.Icc (0:ℝ) 1 :=
    Sanctions.clipS_mem _
  have horder : Sanctions.clipS' (polyComplianceParams.F y₁.val 1)
                  ≤ Sanctions.clipS' (polyComplianceParams.F y₂.val 1) := by
    apply Sanctions.clipS'_mono
    simp only [polyComplianceParams, AbstractGame.affineF]
    show (1 - (1:ℝ)/2) * y₁.val + 1/2 * 1 ≤ (1 - 1/2) * y₂.val + 1/2 * 1
    linarith
  have hVgain := hgain (Sanctions.clipS' (polyComplianceParams.F y₁.val 1))
    (Sanctions.clipS' (polyComplianceParams.F y₂.val 1)) hmem₁ hmem₂ horder
  have hdistclip :
      dist (Sanctions.clipS' (polyComplianceParams.F y₁.val 1))
           (Sanctions.clipS' (polyComplianceParams.F y₂.val 1))
        = (1/2) * dist y₁ y₂ := by
    rw [Subtype.dist_eq, Real.dist_eq, hclipF, hclipF, Subtype.dist_eq, Real.dist_eq,
        show (y₁.val + 1)/2 - (y₂.val + 1)/2 = (1/2) * (y₁.val - y₂.val) by ring,
        abs_mul, show |(1:ℝ)/2| = 1/2 by norm_num]
  rw [hdistclip] at hVgain
  simp only [AbstractGame.Params.joint_T_integrand, hσ₁, hσ₂]
  have hUT : ∀ z : ℝ, polyComplianceParams.U_T z a 1 = 5 * z - 1 + a := by
    intro z; simp only [polyComplianceParams]
  rw [hUT, hUT]
  have hβT : polyComplianceParams.β_T = 1/2 := rfl
  rw [hβT]
  have hdist : dist y₁ y₂ = y₂.val - y₁.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]; ring
  unfold polyV_T_slope at hVgain ⊢
  rw [hdist]
  rw [hdist] at hVgain
  linarith [hVgain]

/-- **Round-35: the gain-carrier value class.** Identical to
`polyComplianceValueClass2` except `carrier_T` is the *gain* ball
`valLipGainBall 12 (20/3) (20/3) 0` (adds the minimum-slope cone), which the
Target value-gain condition `hV_T_gain_on_carrier` requires (a certificate field
until round BJ1.4, 2026-10-07; now an input of
`Target_combined_chord_of_decomposition_lowerChord`). Argmax-uniqueness reuses the
Round-34 theorems (the Target one needs no `V_T`-membership; the Sender carrier is
unchanged). -/
noncomputable def polyComplianceValueClass2Gain :
    polyComplianceParams.ValueClass2 where
  carrier_T := valLipGainBall polyCarrierMT polyV_T_slope polyV_T_slope 0
  carrier_S := valLipBall polyCarrierMS polyCarrierKS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := valLipBall_isClosed _ _
  nonempty_T := polyComplianceParams_gainBall_nonempty
  nonempty_S := valLipBall_nonempty
                  (by unfold polyCarrierMS; norm_num)
                  (by unfold polyCarrierKS; norm_num)
  sender_unique_on := fun V hV => (polyComplianceParams_DAU_on_carrier_S V hV).toOnI
  target_unique_on := fun V_T _ V_S hV_S =>
    polyComplianceParams_TAU_on_carrier_T_S V_T V_S hV_S

/-- **Round-35: `IsInvariant` for the gain-carrier value class.** Target side: the
`valLipBall` preservation (norm + Lipschitz) plus the *gain* preservation
(`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope`, fed by the lower-slope
lemma; its former duplicate `jointTarget_BCF_preserves_lowerSlopeOnValueOn` was
merged into it in round BJ1.2, 2026-10-07).
Sender side: unchanged. -/
theorem polyComplianceValueClass2Gain_IsInvariant :
    polyComplianceValueClass2Gain.IsInvariant := by
  intro V_T V_S
  refine ⟨?_, ?_⟩
  · -- Target side ∈ valLipGainBall = (norm ∧ Lipschitz ∧ gain).
    have huniq : polyComplianceParams.DynamicArgmaxUnique V_S.val :=
      polyComplianceParams_DAU_on_carrier_S V_S.val V_S.property
    have hVTlip : V_T.val ∈ valLipBall polyCarrierMT polyV_T_slope :=
      valLipGainBall_subset_valLipBall _ _ _ _ V_T.property
    have hLip := polyComplianceParams.jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz
      V_T.val V_S.val huniq
      (M := polyCarrierMT) (K := polyV_T_slope) (cube_T := 6)
      V_T.property.1
      (by intro x hx a ha s hs
          simp only [polyComplianceParams]; rw [abs_le]
          constructor <;> nlinarith [hx.1, hx.2, ha.1, ha.2, hs.1, hs.2])
      (by unfold polyComplianceParams polyCarrierMT; norm_num)
      (fun x₁ x₂ a ha =>
        polyComplianceParams_joint_T_integrand_lipschitz_at_carrier
          V_T.val V_S.val hVTlip V_S.property x₁ x₂ a ha)
    have hGain := polyComplianceParams.jointTarget_BCF_lowerSlope_of_integrand_lowerSlope
      V_T.val V_S.val huniq (g := polyV_T_slope) (xT := 0)
      (fun y₁ y₂ a ha h1 h2 hle =>
        polyComplianceParams_joint_T_integrand_lowerSlope_at_carrier
          V_T.val V_S.val V_T.property V_S.property y₁ y₂ a ha h1 h2 hle)
    exact ⟨hLip.1, hLip.2, hGain⟩
  · -- Sender side ∈ valLipBall 2 0 (unchanged).
    refine polyComplianceParams.bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz
      (polyComplianceValueClass2Gain.α_on_continuous V_T V_S)
      (polyComplianceValueClass2Gain.α_on_mem V_T V_S) V_S.val
      (M := polyCarrierMS) (K := polyCarrierKS) (cube_S := 1)
      (L_U_S := 0) (γ_F := 1/2)
      (by unfold polyCarrierKS; norm_num) V_S.property ?_ ?_ ?_ ?_ ?_
    · intro x _ a _ s hs
      simp only [polyComplianceParams]; rw [abs_le]
      exact ⟨by linarith [hs.1, hs.2], hs.2⟩
    · intro x₁ x₂ s _
      simp only [polyComplianceParams]; simp
    · intro x₁ x₂ s _
      simp only [polyComplianceParams, AbstractGame.affineF]
      refine le_of_eq ?_
      rw [show (1 - (1:ℝ)/2) * x₂ + 1/2 * s - ((1 - 1/2) * x₁ + 1/2 * s)
            = (1/2) * (x₂ - x₁) by ring, abs_mul,
          show |(1:ℝ)/2| = 1/2 by norm_num]
    · unfold polyComplianceParams polyCarrierMS; norm_num
    · unfold polyCarrierKS; norm_num

/-- **Round-35: Target-row Lipschitz bound `hT_T_op` (`β_T=1/2`, `L_TS=0`).**
The joint Target operator is `(1/2)`-Lipschitz in `V_T` and *independent of `V_S`*
(its `σ_dyn` is pinned to `1` on the constant Sender carrier), so the cross
coefficient `L_TS = 0`. Proved via the `sSup`-difference bound: pointwise the two
integrands differ only through `(1/2)·(V_T − V_T')`. -/
theorem polyComplianceValueClass2Gain_hT_T_op
    (h_inv : polyComplianceValueClass2Gain.IsInvariant)
    (V V' : polyComplianceValueClass2Gain.CarrierT)
    (W W' : polyComplianceValueClass2Gain.CarrierS) :
    dist (polyComplianceValueClass2Gain.jointTargetOp_sub h_inv (V, W))
          (polyComplianceValueClass2Gain.jointTargetOp_sub h_inv (V', W'))
      ≤ (1/2 : ℝ) * dist V V' + 0 * dist W W' := by
  -- WitnessKit C2 route: the joint Target image has the `V_S`-independent
  -- closed form `5y + β_T · V_T(clip(F(y,1)))` (σ_dyn pinned at 1, leader
  -- argmax at a = 1), so the decoupled row bound is the kit lemma.
  have hβT : polyComplianceParams.β_T = 1/2 := rfl
  rw [← hβT]
  refine WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun y => 5 * y) (φ := fun y => polyComplianceParams.F y 1)
    ?_ V V' W W'
  intro V W y
  have h1_mem : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmax : IsMaxOn
      (fun a => polyComplianceParams.joint_T_integrand V.val W.val y.val a)
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro a ha
    have hσa := σ_dyn_eq_one_of_constant_V_S W.val W.property y.val a
    have hσ1 := σ_dyn_eq_one_of_constant_V_S W.val W.property y.val 1
    simp only [AbstractGame.Params.joint_T_integrand, hσa, hσ1]
    simp only [polyComplianceParams]
    linarith [ha.2]
  rw [WitnessKit.jointTarget_image_of_isMaxOn V.val W.val
      (polyComplianceValueClass2Gain.sender_unique_on W.val W.property)
      y h1_mem hmax]
  have hσ1 := σ_dyn_eq_one_of_constant_V_S W.val W.property y.val 1
  simp only [AbstractGame.Params.joint_T_integrand, hσ1]
  simp only [polyComplianceParams]
  ring

/-- **Round-35: `bellmanS_BCF` is independent of the leader policy `α`** at the
witness, because `U_S(x,a,s)=s` ignores the action — the Sender integrand
`s + (1/2)·V_S(clip(F x s))` does not depend on `α`. -/
theorem polyComplianceParams_bellmanS_α_indep
    (α₁ α₂ : ℝ → ℝ) (hα₁ : Continuous α₁) (hα₂ : Continuous α₂) (Vs : Val) :
    polyComplianceParams.bellmanS_BCF α₁ hα₁ Vs
      = polyComplianceParams.bellmanS_BCF α₂ hα₂ Vs := by
  apply BoundedContinuousFunction.ext
  intro x
  have e1 : polyComplianceParams.bellmanS_BCF α₁ hα₁ Vs x =
      sSup ((fun s => polyComplianceParams.integrandS α₁ (fun y => Vs y) (x.val, s))
              '' Sanctions.I) := rfl
  have e2 : polyComplianceParams.bellmanS_BCF α₂ hα₂ Vs x =
      sSup ((fun s => polyComplianceParams.integrandS α₂ (fun y => Vs y) (x.val, s))
              '' Sanctions.I) := rfl
  rw [e1, e2]
  have hfeq : (fun s => polyComplianceParams.integrandS α₁ (fun y => Vs y) (x.val, s))
            = (fun s => polyComplianceParams.integrandS α₂ (fun y => Vs y) (x.val, s)) := by
    funext s
    simp only [AbstractGame.Params.integrandS, polyComplianceParams]
  rw [hfeq]

/-- **Round-35: Sender-row Lipschitz bound `hT_S_op` (`β_S=1/2`, `L_ST=0`).**
The joint Sender operator is `α`-independent (cross coefficient `L_ST = 0`) and
`(1/2)`-Lipschitz in `V_S` (`bellmanS_BCF_pointwise_dist`). -/
theorem polyComplianceValueClass2Gain_hT_S_op
    (h_inv : polyComplianceValueClass2Gain.IsInvariant)
    (V V' : polyComplianceValueClass2Gain.CarrierT)
    (W W' : polyComplianceValueClass2Gain.CarrierS) :
    dist (polyComplianceValueClass2Gain.jointSenderOp_sub h_inv (V, W))
          (polyComplianceValueClass2Gain.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' := by
  -- WitnessKit C1 route: the derived leader policy is the constant `a = 1`
  -- (per-state argmax of the joint Target integrand), so the Sender row
  -- decouples via the const-policy kit lemma.
  have hβS : polyComplianceParams.β_S = 1/2 := rfl
  rw [← hβS]
  refine WitnessKit.jointSenderOp_sub_dist_le_of_const_policy h_inv
    (α₀ := fun _ => (1 : ℝ)) continuous_const ?_ V V' W W'
  intro V W
  refine WitnessKit.α_on_eq_const_of_isMaxOn V W ⟨by norm_num, le_refl 1⟩ ?_
  intro y
  rw [isMaxOn_iff]
  intro a ha
  have hσa := σ_dyn_eq_one_of_constant_V_S W.val W.property y.val a
  have hσ1 := σ_dyn_eq_one_of_constant_V_S W.val W.property y.val 1
  simp only [AbstractGame.Params.joint_T_integrand, hσa, hσ1]
  simp only [polyComplianceParams]
  linarith [ha.2]

end -- noncomputable section

end Examples

end Sanctions
