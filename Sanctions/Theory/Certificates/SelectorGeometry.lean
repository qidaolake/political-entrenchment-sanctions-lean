/-
Sanctions/Theory/Certificates/SelectorGeometry.lean

**The coupled selector-geometry certificate, in the weakest form that works.**

A Perov/Schur existence argument needs the two Bellman rows to be *linearly*
Lipschitz in the pair of value functions. The Target row can be had for nothing
— a maximum moves by at most the sup-norm movement of what is maximised
(`Foundations/SupDiff.abs_sSup_image_sub_sSup_image_le`). The Sender's cross-row
cannot: the Sender's objective reads the Target's *policy*, so it needs a bound
on how far that policy moves when the value functions move.

`Foundations/ArgmaxSensitivity.argmax_lipschitz_two_coordinates_of_quadraticGrowth`
supplies exactly that bound from two ingredients — quadratic growth of each
realized problem, and an action-chord bound on the objective difference. This
file packages them as a certificate.

## What this certificate is, and what it is not

It is **not** a discharge of the Schur margin from payoff primitives. Calling it
one would contradict four theorems in this tree. What it does is move the
assumption from the *composed Bellman operators*, where the row constants
currently sit as bare fields nobody can check without redoing the derivation, to
*objective geometry*, which is inspectable. That is an auditability gain and not
a logical one, and the limitations section should say so.

## The refutations that fix the form of every field

Each field below is stated in the weakest form the consuming theorem actually
reads, because the natural stronger form is **false** here:

* `not_coupledTargetQuadraticGrowthAt` — no positive modulus satisfies
  carrier-uniform quadratic growth over *all* actions on the coupled Target
  carrier. So `growth` is asked for on a supplied set `A`, and a user who wants
  the theorem must localise it.
* `not_coupledTargetQuadraticGrowthLipCarrierAt` — the same after redesigning
  the carrier for regularity. The obstruction is a tie in the objective, not a
  defect of the carrier: see `Foundations/TiltStability`.
* `not_coupledLeaderObj_sender_uniform_advertised` — the action chord is false as
  a carrier-uniform *all-actions* estimate. Its own docstring records that this
  "does not independently refute the ... weaker realized-leader-only premise",
  and `chord` below is exactly that weaker premise: it constrains the objective
  difference **only at the two realized selectors**.
* `coupledLeaderObj_diff_lip_in_VT` — by contrast the Target-value channel of the
  chord is *proved*. Only the Sender channel is open.

## What the growth field is really assuming

`TiltStability.eq_of_growth_of_isMaxOn` makes it explicit: a positive growth
modulus at a point already asserts that the point is the *unique* maximizer on
the set. So `growth` is a uniqueness assumption wearing a quantitative coat, and
`forces_unique_selector` below states that consequence directly rather than
leaving a reader to discover it.
-/

import Sanctions.Foundations.ArgmaxSensitivity
import Sanctions.Foundations.TiltStability
import Sanctions.Foundations.SupDiff

namespace Sanctions
namespace SelectorGeometry

open Set

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **Coupled selector geometry.**

A theorem-local certificate — deliberately *not* a `Params` field — bundling the
two facts that turn value-function closeness into policy closeness. `objective`
is the complete objective as a function of the two value coordinates and the
action; `select` is the realized policy.

`chord` is the load-bearing field and the one with no discharger anywhere in this
tree, at any parameter point. Note its quantifiers: it is read **only at the two
realized selectors**, never at arbitrary action pairs. -/
structure Geometry (objective : X → Y → ℝ → ℝ) (select : X → Y → ℝ)
    (A : Set ℝ) where
  /-- Growth modulus of each realized problem on `A`. -/
  q : ℝ
  /-- Sensitivity of the objective difference to the first value coordinate. -/
  Lx : ℝ
  /-- Sensitivity of the objective difference to the second value coordinate. -/
  Ly : ℝ
  q_pos : 0 < q
  Lx_nonneg : 0 ≤ Lx
  Ly_nonneg : 0 ≤ Ly
  /-- The realized policy is feasible. -/
  select_mem : ∀ x y, select x y ∈ A
  /-- **Quadratic growth at the realized selector**, on `A`. Asked for on the
  supplied set rather than on all feasible actions, because the all-actions form
  is refuted (`not_coupledTargetQuadraticGrowthAt`). -/
  growth : ∀ x y, ∀ a ∈ A,
    q * (a - select x y) ^ 2 ≤ objective x y (select x y) - objective x y a
  /-- **The action chord, at the realized selectors only.** The all-actions form
  is refuted (`not_coupledLeaderObj_sender_uniform_advertised`); this weaker
  premise is the one that refutation explicitly does not reach, and it is what
  the argmax-sensitivity theorem reads. -/
  chord : ∀ x x' y y',
    |(objective x y (select x y) - objective x' y' (select x y))
        - (objective x y (select x' y') - objective x' y' (select x' y'))|
      ≤ (Lx * dist x x' + Ly * dist y y') * |select x y - select x' y'|

namespace Geometry

variable {objective : X → Y → ℝ → ℝ} {select : X → Y → ℝ} {A : Set ℝ}

/-- **The selector is Lipschitz in both value coordinates.**

The Rule 5 promotion: the content of the witness-level `coupled_lead_lipschitz`,
with that theorem's pinned rationals replaced by the certificate's symbols. -/
theorem selector_lipschitz (G : Geometry objective select A) (x x' : X) (y y' : Y) :
    |select x y - select x' y'|
      ≤ (G.Lx * dist x x' + G.Ly * dist y y') / (2 * G.q) :=
  Sanctions.argmax_lipschitz_two_coordinates_of_quadraticGrowth
    objective select G.q_pos G.Lx_nonneg G.Ly_nonneg x x' y y'
    (G.select_mem x y) (G.select_mem x' y')
    (fun a ha => G.growth x y a ha) (fun a ha => G.growth x' y' a ha)
    (G.chord x x' y y')

/-- **The growth field is a uniqueness assumption.**

Anything that maximizes a realized problem on `A` *is* the realized selector.
Stated so that a reader of the certificate sees the commitment rather than
inferring it: `Foundations/TiltStability.eq_of_growth_of_isMaxOn` is the general
fact, and it is also why a tie in the objective refutes growth outright. -/
theorem forces_unique_selector (G : Geometry objective select A)
    (x : X) (y : Y) {b : ℝ} (hb : b ∈ A)
    (hmax : IsMaxOn (objective x y) A b) :
    b = select x y :=
  Sanctions.TiltStability.eq_of_growth_of_isMaxOn G.q_pos
    (fun a ha => G.growth x y a ha) (G.select_mem x y) hb hmax

/-- First derived row coefficient, named so the matrix entry has a provenance
rather than appearing as a constant. -/
noncomputable def kappaX (G : Geometry objective select A) : ℝ :=
  G.Lx / (2 * G.q)

/-- Second derived row coefficient. -/
noncomputable def kappaY (G : Geometry objective select A) : ℝ :=
  G.Ly / (2 * G.q)

theorem kappaX_nonneg (G : Geometry objective select A) : 0 ≤ G.kappaX :=
  div_nonneg G.Lx_nonneg (by nlinarith [G.q_pos])

theorem kappaY_nonneg (G : Geometry objective select A) : 0 ≤ G.kappaY :=
  div_nonneg G.Ly_nonneg (by nlinarith [G.q_pos])

/-- The selector bound in the separated form a Perov row consumes. -/
theorem selector_lipschitz_split (G : Geometry objective select A)
    (x x' : X) (y y' : Y) :
    |select x y - select x' y'|
      ≤ G.kappaX * dist x x' + G.kappaY * dist y y' := by
  have hq : (0 : ℝ) < 2 * G.q := by nlinarith [G.q_pos]
  calc |select x y - select x' y'|
      ≤ (G.Lx * dist x x' + G.Ly * dist y y') / (2 * G.q) :=
        G.selector_lipschitz x x' y y'
    _ = G.Lx / (2 * G.q) * dist x x' + G.Ly / (2 * G.q) * dist y y' := by
        field_simp

end Geometry
end SelectorGeometry
end Sanctions
