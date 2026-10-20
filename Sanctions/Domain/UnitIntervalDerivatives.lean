/-
Sanctions/Foundations/DerivativeOnS.lean

**C¹ subspace foundations: derivative infrastructure for `↥S → ℝ`
bounded continuous functions (first iteration of multi-iteration
C¹ migration for audit-33 Gap 2/3 substantive closure).**

**PARTIALLY UNFROZEN (2026-07-12; supersedes the 2026-07-04 A6 freeze
for the witness layer only).** The *witness* layer now carries
paper-facing load: `Examples/C1WitnessEnvelope.lean` inhabits `C1Val`,
`ValueClass_C1`, `ValueClass_C1Complete` and `C1BellmanSystem` at the
two pinned exact Bellman fixed points (eeCert, fourGroup), and the
paper's shadow-price passage cites the resulting equilibrium slopes.
At those witnesses the completeness field is *proved*
(`eeC1Class_complete` / `fgcC1Class_complete` — a singleton carrier is
trivially complete) and `T = id`, so the `c1distPair`-fixed point is a
genuine fixed point: no assumed-completeness postulate and no
pseudo-metric artefact enters any shipped result. No headline row
fences the C¹ layer.

The *abstract* layer STAYS FROZEN: each general form (the
`SmoothSanctionClass` IFT Prop fields, an abstract
`ValueClass_C1Complete` derivation, general-`F` RZS-style statements)
would need new differentiability hypotheses (Rule 3). Both structural
deficiencies persist at abstract generality: `c1distPair` is a
pseudo-metric (`V'` stored on all of `ℝ`), and completeness
(`ValueClass_C1Complete`) is consumed per-certificate, not derived. Revival order if ever needed: (1) the within-set
uniform-limits-of-derivatives theorem (a mathlib gap, not an analytic
one — `Foundations/` candidate), (2) the `V'`-domain refactor,
(3) asymmetric duplication only once a consumer exists.

The audit-33 substantive Gap 2/3 closure requires `σ_dyn V_S` to be
**Lipschitz** in `V_S`, but in general BCF (sup-norm topology) it
is only Hölder-1/2 (substantively documented in
`StrongConcaveHolder.lean`). Genuine Lipschitz requires `V_S` in a
C¹-on-`↥S` subspace where the IFT-at-FOC argument can be applied.

This file is the **first step** of the multi-iteration C¹ migration:
it provides the basic differentiability infrastructure for
`↥S →ᵇ ℝ` (BCF) functions, via mathlib's `HasDerivWithinAt` applied
to the natural extension to all of `ℝ`.

## Definitions

* `bcfExtendToR V` — extend `V : ↥S →ᵇ ℝ` to a function `ℝ → ℝ` by
  composing with `clipS'` (the projection of `ℝ` onto `↥S`).
* `HasDerivOnS V V'` — `bcfExtendToR V` has the derivative function
  `V' : ℝ → ℝ` at every point of `Sanctions.S` (within S).
* `HasBoundedDerivOnS V V' K_d` — additionally the derivative is
  uniformly bounded by `K_d`.

These primitives are used in subsequent iterations to define the C¹
subspace (with C¹ norm `‖V‖_C1 = ‖V‖ + ‖V'‖_∞`) and re-instantiate
the abstract value-function infrastructure there.

## Rule compliance

**Rule 1.** No strategic objects; pure derivative infrastructure. All
declarations constructive, zero `sorry`.

**Rule 3.** No new `Params` fields. The derivative function `V'` is
a theorem-parameter primitive supplied by the user (or derived at
concrete payoff classes).

**Rule 5.** Fully parametric.

**Rule 6.** Consulted `Mathlib.Analysis.Calculus.Deriv.Basic` for
`HasDerivWithinAt`; selected the within-set form because
`Sanctions.S = [0, 1]` has boundary and two-sided derivatives at
endpoints don't exist in the standard sense.

## Why this file lives in Foundations (moved 2026-07-24, Rule 19)

Generic derivative infrastructure: mathlib's `HasDerivWithinAt`
machinery applied to bounded continuous functions on the unit interval
extended through clipping. Its only non-mathlib dependencies —
`Sanctions.S` (`Foundations/Basic.lean`) and `clipS'`
(`Foundations/ClipS.lean`) — are themselves Foundations citizens, and
nothing here mentions `AbstractGame.Params`, `ValueClass`, or any
economic object. (The file previously sat in `Theory/Bellman/` with a
rationale calling `S` and `clipS'` "project-specific" — factually
wrong under the project's own layering; corrected with the move. Its
sole consumer remains `Theory/Bellman/C1Val.lean`.)
-/

import Sanctions.Domain.UnitIntervalProjection
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

/-! ## Extension of `↥S →ᵇ ℝ` to `ℝ → ℝ` -/

/-- **Extension of a BCF `V : ↥S →ᵇ ℝ` to a function `ℝ → ℝ`** via
composition with `clipS'`. Agrees with `V` on `↥S` (since `clipS'`
is the identity on `S`) and is continuous on all of `ℝ`. -/
noncomputable def bcfExtendToR
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : ℝ → ℝ :=
  fun y => V (Sanctions.clipS' y)

theorem bcfExtendToR_continuous
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    Continuous (bcfExtendToR V) :=
  V.continuous.comp Sanctions.clipS'_continuous

/-- On `↥S`, the extension agrees with the original BCF (because
`clipS'` is the identity on `↥S`). -/
theorem bcfExtendToR_coe
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (x : ↥(Sanctions.S : Set ℝ)) :
    bcfExtendToR V x.val = V x := by
  unfold bcfExtendToR
  congr 1
  -- clipS' x.val = ⟨clipS x.val, _⟩; x = ⟨x.val, x.property⟩.
  -- Equal iff clipS x.val = x.val (which holds for x ∈ S).
  apply Subtype.ext
  have hx_mem : x.val ∈ Sanctions.S := x.property
  change Sanctions.clipS x.val = x.val
  unfold Sanctions.clipS
  rcases hx_mem with ⟨h0, h1⟩
  rw [min_eq_right h1, max_eq_right h0]

/-! ## Derivative-on-S primitives

A BCF `V : ↥S →ᵇ ℝ` has a **derivative function** `V' : ℝ → ℝ` on
`Sanctions.S` if for every `x ∈ Sanctions.S`, the extension
`bcfExtendToR V` has derivative `V' x` at `x` within `S`. -/

/-- **`V` has derivative function `V'` on `Sanctions.S`** —
the within-set derivative of the BCF extension. -/
def HasDerivOnS
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (V' : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Sanctions.S →
    HasDerivWithinAt (bcfExtendToR V) (V' x) Sanctions.S x

/-- **`V` has a bounded derivative function on `Sanctions.S`** —
derivative function exists and is uniformly bounded by `K_d`. -/
def HasBoundedDerivOnS
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (V' : ℝ → ℝ) (K_d : ℝ) : Prop :=
  HasDerivOnS V V' ∧ ∀ x ∈ Sanctions.S, |V' x| ≤ K_d

/-- Bounded-derivative ⇒ derivative-on-S (forgetful projection). -/
theorem HasBoundedDerivOnS.hasDerivOnS
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {V' : ℝ → ℝ} {K_d : ℝ}
    (h : HasBoundedDerivOnS V V' K_d) :
    HasDerivOnS V V' := h.1

theorem HasBoundedDerivOnS.bound
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {V' : ℝ → ℝ} {K_d : ℝ}
    (h : HasBoundedDerivOnS V V' K_d) :
    ∀ x ∈ Sanctions.S, |V' x| ≤ K_d := h.2

/-! ## Basic properties

Zero function has zero derivative. -/

/-- The zero function has zero derivative on `Sanctions.S`. -/
theorem zero_hasDerivOnS :
    HasDerivOnS (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (fun _ => 0) := by
  intro x _hx
  have h_zero_ext :
      bcfExtendToR (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) = (fun _ : ℝ => (0 : ℝ)) := by
    funext y
    change (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (Sanctions.clipS' y) = 0
    rfl
  rw [h_zero_ext]
  exact hasDerivWithinAt_const x Sanctions.S 0

/-- The zero function has bounded derivative `0` with bound `0`. -/
theorem zero_hasBoundedDerivOnS :
    HasBoundedDerivOnS (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
      (fun _ => 0) 0 := by
  refine ⟨zero_hasDerivOnS, ?_⟩
  intro x _hx
  simp

end -- noncomputable section

end Sanctions
