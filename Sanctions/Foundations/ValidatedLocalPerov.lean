/-
Sanctions/Foundations/ValidatedLocalPerov.lean

A residual-and-radius localization of the two-coordinate Perov contraction
principle.  This is abstract fixed-point infrastructure: it does not mention
the sanctions model and it adds no economic assumption.

The theorem below turns five independently checkable certificates into a
fixed point inside a prescribed pair of closed balls:

* the two radii are nonnegative;
* the residual of the proposed center is bounded in each coordinate;
* the operator obeys local two-row Lipschitz estimates on the balls;
* the residual plus the propagated radii fit back inside the balls; and
* the nonnegative row matrix satisfies the existing Schur/Perov condition.

The proof restricts the operator to the two complete closed-ball subtypes and
then invokes `perov2_existsUnique_fixedPoint`.  The output is unique only among
fixed points in the validated neighborhood; it makes no global uniqueness
claim.
-/

import Mathlib.Algebra.Order.Floor.Semiring
import Sanctions.Foundations.PerovContraction

namespace Sanctions
namespace Foundations
namespace Perov

/-- The uniform real mesh with nodes `k / n`, for `0 ≤ k ≤ n`. -/
noncomputable def unitIntervalMesh (n : ℕ) : Set ℝ :=
  {y | ∃ k : ℕ, k ≤ n ∧ y = (k : ℝ) / (n : ℝ)}

/-- Every point of `[0,1]` is within one mesh width of a node of the uniform
`n`-mesh.  The one-sided `1 / n` radius keeps the exact certificate elementary;
a nearest-node refinement to `1 / (2n)` is unnecessary for soundness. -/
theorem unitIntervalMesh_cover {n : ℕ} (hn : 0 < n) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∃ m ∈ unitIntervalMesh n, dist x m ≤ 1 / (n : ℝ) := by
  intro x hx
  let k : ℕ := ⌊(n : ℝ) * x⌋₊
  let m : ℝ := (k : ℝ) / (n : ℝ)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnx0 : 0 ≤ (n : ℝ) * x := mul_nonneg hnR.le hx.1
  have hfloorLower : (k : ℝ) ≤ (n : ℝ) * x := by
    simpa [k] using (Nat.floor_le hnx0)
  have hfloorUpper : (k : ℝ) ≤ (n : ℝ) := by
    calc
      (k : ℝ) ≤ (n : ℝ) * x := hfloorLower
      _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hx.2 hnR.le
      _ = (n : ℝ) := mul_one _
  have hk : k ≤ n := by exact_mod_cast hfloorUpper
  refine ⟨m, ⟨k, hk, rfl⟩, ?_⟩
  have hmle : m ≤ x := by
    apply (div_le_iff₀ hnR).2
    simpa [m, mul_comm] using hfloorLower
  have hfloorUpperStrict : (n : ℝ) * x < (k : ℝ) + 1 := by
    simpa [k] using (Nat.lt_floor_add_one ((n : ℝ) * x))
  have hxlt : x < ((k : ℝ) + 1) / (n : ℝ) := by
    apply (lt_div_iff₀ hnR).2
    simpa [mul_comm] using hfloorUpperStrict
  have hsplit : ((k : ℝ) + 1) / (n : ℝ) = m + 1 / (n : ℝ) := by
    simp only [m]
    ring
  rw [hsplit] at hxlt
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmle)]
  linarith

/-- The pointwise distance between two state-dependent objects has modulus at
most the sum of their two state moduli.  Applied to a candidate value and its
Bellman image, this supplies the residual modulus consumed by the mesh
certificate below. -/
theorem dist_residual_modulus
    {Z W : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace W]
    (f g : Z → W) {domain : Set Z} {Kf Kg : ℝ}
    (hf : ∀ x ∈ domain, ∀ y ∈ domain,
      dist (f x) (f y) ≤ Kf * dist x y)
    (hg : ∀ x ∈ domain, ∀ y ∈ domain,
      dist (g x) (g y) ≤ Kg * dist x y) :
    ∀ x ∈ domain, ∀ y ∈ domain,
      |dist (f x) (g x) - dist (f y) (g y)| ≤
        (Kf + Kg) * dist x y := by
  intro x hx y hy
  rw [← Real.dist_eq]
  calc
    dist (dist (f x) (g x)) (dist (f y) (g y)) ≤
        dist (f x) (f y) + dist (g x) (g y) :=
      dist_dist_dist_le _ _ _ _
    _ ≤ Kf * dist x y + Kg * dist x y :=
      add_le_add (hf x hx y hy) (hg x hx y hy)
    _ = (Kf + Kg) * dist x y := by ring

/-- **Covering-net residual bound.**

If every point of `domain` is within `h` of a checked point in `mesh`, and the
real-valued residual has modulus `K` between those points, then a mesh bound
`ε` lifts to the whole domain with error `K * h`.

The set named `mesh` need not be finite in this abstract lemma.  In a concrete
validated computation, finiteness makes each premise an exact finite
arithmetic obligation. -/
theorem residual_le_of_net
    {Z : Type*} [PseudoMetricSpace Z]
    (residual : Z → ℝ) {domain mesh : Set Z} {ε K h : ℝ}
    (hK : 0 ≤ K)
    (hcover : ∀ z ∈ domain, ∃ m ∈ mesh, dist z m ≤ h)
    (hLip : ∀ z ∈ domain, ∀ m ∈ mesh,
      |residual z - residual m| ≤ K * dist z m)
    (hmesh : ∀ m ∈ mesh, residual m ≤ ε) :
    ∀ z ∈ domain, residual z ≤ ε + K * h := by
  intro z hz
  obtain ⟨m, hm, hdist⟩ := hcover z hz
  have hosc := hLip z hz m hm
  have hmul : K * dist z m ≤ K * h := mul_le_mul_of_nonneg_left hdist hK
  have hdiff : residual z - residual m ≤ K * dist z m :=
    le_trans (le_abs_self _) hosc
  linarith [hmesh m hm]

/-- Uniform-unit-interval specialization of `residual_le_of_net`. Exact
residual checks at the nodes `k / n` plus a modulus `K` imply the continuum
bound `ε + K / n`. -/
theorem residual_le_on_unitInterval_of_mesh
    (n : ℕ) (hn : 0 < n) (residual : ℝ → ℝ) {ε K : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ m ∈ unitIntervalMesh n,
      |residual x - residual m| ≤ K * dist x m)
    (hmesh : ∀ m ∈ unitIntervalMesh n, residual m ≤ ε) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, residual x ≤ ε + K * (1 / (n : ℝ)) :=
  residual_le_of_net residual hK (unitIntervalMesh_cover hn) hLip hmesh

/-- **Validated local Perov certificate.**

Let `(x₀, y₀)` be an approximate fixed point of a two-coordinate operator
`T`.  If its coordinate residuals are at most `εX, εY`, the local row
Lipschitz matrix is `((a,b),(c,d))`, and

`εX + a * rX + b * rY ≤ rX`,
`εY + c * rX + d * rY ≤ rY`,

then the product of the two closed balls is invariant.  The Schur condition
then gives a fixed point there, unique among fixed points in those balls.

All substantive premises remain obligations of the eventual model-specific
witness; this theorem does not assume an optimizer, policy, carrier
invariance, or equilibrium.

2026-10-06 (round BG1.1 follow-up): the first diagonal bound `a < 1` was
dropped from the signature. With `0 ≤ b`, `0 ≤ c` and `d < 1`, the Schur
margin already forces it (`lt_one_of_schur_margin`), and the Perov engine no
longer asks for it, so a witness has one fewer inequality to certify. F-free:
abstract metric-space content, valid for every transition law. -/
theorem perov2_existsUnique_fixedPoint_in_closedBalls_of_residual
    {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y)
    (rX rY εX εY : ℝ) {a b c d : ℝ}
    (hrX : 0 ≤ rX) (hrY : 0 ≤ rY)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hresX : dist (T (x₀, y₀)).1 x₀ ≤ εX)
    (hresY : dist (T (x₀, y₀)).2 y₀ ≤ εY)
    (hX : ∀ z z' : X × Y,
      dist z.1 x₀ ≤ rX → dist z.2 y₀ ≤ rY →
      dist z'.1 x₀ ≤ rX → dist z'.2 y₀ ≤ rY →
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      dist z.1 x₀ ≤ rX → dist z.2 y₀ ≤ rY →
      dist z'.1 x₀ ≤ rX → dist z'.2 y₀ ≤ rY →
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hRadX : εX + a * rX + b * rY ≤ rX)
    (hRadY : εY + c * rX + d * rY ≤ rY)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃! z : X × Y, T z = z ∧ dist z.1 x₀ ≤ rX ∧ dist z.2 y₀ ≤ rY := by
  let BX : Set X := Metric.closedBall x₀ rX
  let BY : Set Y := Metric.closedBall y₀ rY
  let Xloc := {x : X // x ∈ BX}
  let Yloc := {y : Y // y ∈ BY}
  have hx₀ : x₀ ∈ BX := by simp [BX, hrX]
  have hy₀ : y₀ ∈ BY := by simp [BY, hrY]
  letI : Nonempty Xloc := ⟨⟨x₀, hx₀⟩⟩
  letI : Nonempty Yloc := ⟨⟨y₀, hy₀⟩⟩
  letI : CompleteSpace Xloc := Metric.isClosed_closedBall.completeSpace_coe
  letI : CompleteSpace Yloc := Metric.isClosed_closedBall.completeSpace_coe
  have hmapX (z : Xloc × Yloc) : (T (z.1.1, z.2.1)).1 ∈ BX := by
    have hzX := z.1.2
    have hzY := z.2.2
    change dist z.1.1 x₀ ≤ rX at hzX
    change dist z.2.1 y₀ ≤ rY at hzY
    have hrow := hX (z.1.1, z.2.1) (x₀, y₀) hzX hzY
      (by simpa using hrX) (by simpa using hrY)
    have hax := mul_le_mul_of_nonneg_left hzX ha_nn
    have hby := mul_le_mul_of_nonneg_left hzY hb_nn
    change dist (T (z.1.1, z.2.1)).1 x₀ ≤ rX
    calc
      dist (T (z.1.1, z.2.1)).1 x₀ ≤
          dist (T (z.1.1, z.2.1)).1 (T (x₀, y₀)).1 +
            dist (T (x₀, y₀)).1 x₀ := dist_triangle _ _ _
      _ ≤ (a * dist z.1.1 x₀ + b * dist z.2.1 y₀) + εX :=
        add_le_add hrow hresX
      _ ≤ εX + a * rX + b * rY := by linarith
      _ ≤ rX := hRadX
  have hmapY (z : Xloc × Yloc) : (T (z.1.1, z.2.1)).2 ∈ BY := by
    have hzX := z.1.2
    have hzY := z.2.2
    change dist z.1.1 x₀ ≤ rX at hzX
    change dist z.2.1 y₀ ≤ rY at hzY
    have hrow := hY (z.1.1, z.2.1) (x₀, y₀) hzX hzY
      (by simpa using hrX) (by simpa using hrY)
    have hcx := mul_le_mul_of_nonneg_left hzX hc_nn
    have hdy := mul_le_mul_of_nonneg_left hzY hd_nn
    change dist (T (z.1.1, z.2.1)).2 y₀ ≤ rY
    calc
      dist (T (z.1.1, z.2.1)).2 y₀ ≤
          dist (T (z.1.1, z.2.1)).2 (T (x₀, y₀)).2 +
            dist (T (x₀, y₀)).2 y₀ := dist_triangle _ _ _
      _ ≤ (c * dist z.1.1 x₀ + d * dist z.2.1 y₀) + εY :=
        add_le_add hrow hresY
      _ ≤ εY + c * rX + d * rY := by linarith
      _ ≤ rY := hRadY
  let Tlocal : Xloc × Yloc → Xloc × Yloc := fun z =>
    (⟨(T (z.1.1, z.2.1)).1, hmapX z⟩, ⟨(T (z.1.1, z.2.1)).2, hmapY z⟩)
  have hlocalX : ∀ z z' : Xloc × Yloc,
      dist (Tlocal z).1 (Tlocal z').1 ≤
        a * dist z.1 z'.1 + b * dist z.2 z'.2 := by
    intro z z'
    have hzX := z.1.2
    have hzY := z.2.2
    have hzX' := z'.1.2
    have hzY' := z'.2.2
    change dist z.1.1 x₀ ≤ rX at hzX
    change dist z.2.1 y₀ ≤ rY at hzY
    change dist z'.1.1 x₀ ≤ rX at hzX'
    change dist z'.2.1 y₀ ≤ rY at hzY'
    exact hX (z.1.1, z.2.1) (z'.1.1, z'.2.1) hzX hzY hzX' hzY'
  have hlocalY : ∀ z z' : Xloc × Yloc,
      dist (Tlocal z).2 (Tlocal z').2 ≤
        c * dist z.1 z'.1 + d * dist z.2 z'.2 := by
    intro z z'
    have hzX := z.1.2
    have hzY := z.2.2
    have hzX' := z'.1.2
    have hzY' := z'.2.2
    change dist z.1.1 x₀ ≤ rX at hzX
    change dist z.2.1 y₀ ≤ rY at hzY
    change dist z'.1.1 x₀ ≤ rX at hzX'
    change dist z'.2.1 y₀ ≤ rY at hzY'
    exact hY (z.1.1, z.2.1) (z'.1.1, z'.2.1) hzX hzY hzX' hzY'
  obtain ⟨w, hw, huniq⟩ := perov2_existsUnique_fixedPoint Tlocal
    ha_nn hb_nn hc_nn hd_nn hlocalX hlocalY hd_lt hSchur
  have hfixX : (T (w.1.1, w.2.1)).1 = w.1.1 := by
    have := congrArg (fun q : Xloc × Yloc => q.1.1) hw
    simpa [Tlocal] using this
  have hfixY : (T (w.1.1, w.2.1)).2 = w.2.1 := by
    have := congrArg (fun q : Xloc × Yloc => q.2.1) hw
    simpa [Tlocal] using this
  have hfix : T (w.1.1, w.2.1) = (w.1.1, w.2.1) := Prod.ext hfixX hfixY
  refine ⟨(w.1.1, w.2.1), ⟨hfix, ?_, ?_⟩, ?_⟩
  · have hwX := w.1.2
    change dist w.1.1 x₀ ≤ rX at hwX
    exact hwX
  · have hwY := w.2.2
    change dist w.2.1 y₀ ≤ rY at hwY
    exact hwY
  · intro z hz
    let wz : Xloc × Yloc :=
      (⟨z.1, by change dist z.1 x₀ ≤ rX; exact hz.2.1⟩,
       ⟨z.2, by change dist z.2 y₀ ≤ rY; exact hz.2.2⟩)
    have hwz : Tlocal wz = wz := by
      apply Prod.ext
      · apply Subtype.ext
        simpa [Tlocal, wz] using congrArg Prod.fst hz.1
      · apply Subtype.ext
        simpa [Tlocal, wz] using congrArg Prod.snd hz.1
    have heq : wz = w := huniq wz hwz
    apply Prod.ext
    · exact congrArg (fun q : Xloc × Yloc => q.1.1) heq
    · exact congrArg (fun q : Xloc × Yloc => q.2.1) heq

/-- The first coordinate of the canonical residual radius
`(I - M)⁻¹ ε` for a two-row Perov matrix `M = ((a,b),(c,d))`. -/
noncomputable def perov2CanonicalRadiusX
    (a b c d εX εY : ℝ) : ℝ :=
  ((1 - d) * εX + b * εY) / ((1 - a) * (1 - d) - b * c)

/-- The second coordinate of the canonical residual radius
`(I - M)⁻¹ ε` for a two-row Perov matrix `M = ((a,b),(c,d))`. -/
noncomputable def perov2CanonicalRadiusY
    (a b c d εX εY : ℝ) : ℝ :=
  (c * εX + (1 - a) * εY) / ((1 - a) * (1 - d) - b * c)

/-- **Canonical-radius identities.** Under non-negative residuals and row
coefficients plus the strict Schur condition, the two closed-form radii are
non-negative and solve `(I - M) r = ε` exactly.

This constructs the radii analytically; it does not assume that suitable
numerical radii exist.

2026-10-06 (round BG1.1 follow-up): the hypothesis `a < 1` was dropped. The
proof derives it from `0 ≤ b`, `0 ≤ c`, `d < 1` and the Schur margin
(`lt_one_of_schur_margin`), so the identities hold under one fewer stated
assumption. F-free: pure real arithmetic. -/
theorem perov2_canonicalRadii_spec
    {a b c d εX εY : ℝ}
    (hεX : 0 ≤ εX) (hεY : 0 ≤ εY)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    0 ≤ perov2CanonicalRadiusX a b c d εX εY ∧
      0 ≤ perov2CanonicalRadiusY a b c d εX εY ∧
      εX + a * perov2CanonicalRadiusX a b c d εX εY
          + b * perov2CanonicalRadiusY a b c d εX εY
        = perov2CanonicalRadiusX a b c d εX εY ∧
      εY + c * perov2CanonicalRadiusX a b c d εX εY
          + d * perov2CanonicalRadiusY a b c d εX εY
        = perov2CanonicalRadiusY a b c d εX εY := by
  have ha_lt : a < 1 := lt_one_of_schur_margin hb hc hd_lt hSchur
  have hdet : 0 < (1 - a) * (1 - d) - b * c := by linarith
  have h1a : 0 ≤ 1 - a := by linarith
  have h1d : 0 ≤ 1 - d := by linarith
  have hnumX : 0 ≤ (1 - d) * εX + b * εY :=
    add_nonneg (mul_nonneg h1d hεX) (mul_nonneg hb hεY)
  have hnumY : 0 ≤ c * εX + (1 - a) * εY :=
    add_nonneg (mul_nonneg hc hεX) (mul_nonneg h1a hεY)
  constructor
  · exact div_nonneg hnumX (le_of_lt hdet)
  constructor
  · exact div_nonneg hnumY (le_of_lt hdet)
  constructor
  · unfold perov2CanonicalRadiusX perov2CanonicalRadiusY
    ring_nf at hdet ⊢
    field_simp [ne_of_gt hdet]
    ring
  · unfold perov2CanonicalRadiusX perov2CanonicalRadiusY
    ring_nf at hdet ⊢
    field_simp [ne_of_gt hdet]
    ring

/-- **Admissible Perov validation radius vectors.**

The pairs `(rX, rY)` that pass the two Perov self-map budget checks for a
residual vector `ε = (εX, εY)` and a row matrix `M = ((a,b),(c,d))`: the
residual plus the propagated radii must fit back inside the same radii. In
plain terms, this is exactly the set of radius pairs for which the product of
the two closed balls around the proposed centre is carried into itself. Every
hand-chosen radius packet in the development is, by definition, a claim of
membership in this set.

Pure scaffolding for the minimality statement below; it is never taken as a
hypothesis of any theorem, so it widens no assumption surface. -/
def perov2AdmissibleRadii (a b c d εX εY : ℝ) : Set (ℝ × ℝ) :=
  {r | εX + a * r.1 + b * r.2 ≤ r.1 ∧ εY + c * r.1 + d * r.2 ≤ r.2}

/-- **The canonical radii are componentwise below every admissible radius
pair.**

If any pair `(rX, rY)` — for instance a hand-picked numerical packet — passes
the two Perov self-map budget checks, then the closed-form radii
`(I - M)⁻¹ ε` are componentwise no larger. So a chosen radius packet can never
be *better* than the derived one; it can only be the derived one plus slack.

The proof is the linear algebra of `I - M`: the two budget inequalities say
`εX ≤ (1-a) rX - b rY` and `εY ≤ (1-d) rY - c rX`; taking the combination
`(1-d)·(first) + b·(second)` collapses the `rY` terms and leaves
`(1-d) εX + b εY ≤ ((1-a)(1-d) - bc) · rX`, which is the claim after dividing
by the Schur determinant. The other coordinate is the combination
`c·(first) + (1-a)·(second)`.

Note what is *not* assumed: neither the residuals nor the comparison radii
need be nonnegative. Only `b, c ≥ 0`, `a, d < 1` and the strict Schur
determinant condition are used.

2026-10-06 (round BG1.1 follow-up): `a < 1` is redundant here — it follows
from `b, c ≥ 0`, `d < 1` and the Schur margin (`lt_one_of_schur_margin`) —
but the binder is kept because callers in `Examples/CoupledRoute` pass it
positionally. F-free: pure real arithmetic. -/
theorem perov2_canonicalRadii_le_of_mem_admissible
    {a b c d εX εY : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha_lt : a < 1) (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d))
    {r : ℝ × ℝ} (hr : r ∈ perov2AdmissibleRadii a b c d εX εY) :
    perov2CanonicalRadiusX a b c d εX εY ≤ r.1 ∧
      perov2CanonicalRadiusY a b c d εX εY ≤ r.2 := by
  obtain ⟨hbudX, hbudY⟩ := hr
  have hdet : 0 < (1 - a) * (1 - d) - b * c := by linarith
  have h1a : (0 : ℝ) ≤ 1 - a := by linarith
  have h1d : (0 : ℝ) ≤ 1 - d := by linarith
  have hXd : (1 - d) * εX ≤ (1 - d) * ((1 - a) * r.1 - b * r.2) :=
    mul_le_mul_of_nonneg_left (by linarith) h1d
  have hYb : b * εY ≤ b * ((1 - d) * r.2 - c * r.1) :=
    mul_le_mul_of_nonneg_left (by linarith) hb
  have hXc : c * εX ≤ c * ((1 - a) * r.1 - b * r.2) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have hYa : (1 - a) * εY ≤ (1 - a) * ((1 - d) * r.2 - c * r.1) :=
    mul_le_mul_of_nonneg_left (by linarith) h1a
  refine ⟨?_, ?_⟩
  · rw [perov2CanonicalRadiusX, div_le_iff₀ hdet]
    nlinarith [hXd, hYb]
  · rw [perov2CanonicalRadiusY, div_le_iff₀ hdet]
    nlinarith [hXc, hYa]

/-- **The canonical radii are the least admissible radius vector.**

Bundles the three facts a caller needs in order to stop choosing radii:

* the closed-form pair `(I - M)⁻¹ ε` is itself admissible — it satisfies both
  Perov self-map budget inequalities, and does so *with equality*, so no room
  is wasted (this half is `perov2_canonicalRadii_spec`); and
* it is componentwise `≤` every other admissible pair, in the product order on
  `ℝ × ℝ` (this half is `perov2_canonicalRadii_le_of_mem_admissible`).

Consequence for the development: a radius is not a modelling choice. Given the
row matrix and the residual, the smallest validated neighbourhood is
determined, and any numeral a witness file writes down is either that value or
that value plus unused slack. Nonnegativity of the canonical radii — also in
`perov2_canonicalRadii_spec` — comes from nonnegativity of the residuals, which
holds automatically when `ε` is a distance.

**Honest scope.** This removes the *radii* from the chosen-magnitude surface.
It does not remove the residual vector `ε`: that is still evaluated at a
constructed centre and, in the concrete witnesses, is still a rational number
obtained from an explicit centre and an explicit Bellman operator. What the
lemma buys is that once `ε` is pinned, nothing further is chosen.

2026-10-06 (round BG1.1 follow-up): the hypothesis `a < 1` was dropped; it is
derived from `0 ≤ b`, `0 ≤ c`, `d < 1` and the Schur margin
(`lt_one_of_schur_margin`). F-free: pure real arithmetic. -/
theorem perov2_canonicalRadii_isLeast
    {a b c d εX εY : ℝ}
    (hεX : 0 ≤ εX) (hεY : 0 ≤ εY)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    IsLeast (perov2AdmissibleRadii a b c d εX εY)
      (perov2CanonicalRadiusX a b c d εX εY,
        perov2CanonicalRadiusY a b c d εX εY) := by
  obtain ⟨_, _, hEqX, hEqY⟩ :=
    perov2_canonicalRadii_spec hεX hεY hb hc hd_lt hSchur
  refine ⟨⟨le_of_eq hEqX, le_of_eq hEqY⟩, ?_⟩
  intro r hr
  rw [Prod.le_def]
  exact perov2_canonicalRadii_le_of_mem_admissible hb hc
    (lt_one_of_schur_margin hb hc hd_lt hSchur) hd_lt hSchur hr

/-- **Validated local Perov theorem with analytically constructed radii.**

The caller supplies only the residual vector and local row matrix.  The two
ball radii are the closed-form coordinates of `(I - M)⁻¹ ε`; the theorem
therefore has no free or hand-tuned radius parameters.

2026-10-06 (round BG1.1 follow-up): the hypothesis `a < 1` was dropped, as in
`perov2_existsUnique_fixedPoint_in_closedBalls_of_residual`; the signs,
`d < 1` and the Schur margin imply it. F-free: abstract metric-space
content. -/
theorem perov2_existsUnique_fixedPoint_in_canonical_closedBalls_of_residual
    {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y)
    (εX εY : ℝ) {a b c d : ℝ}
    (hεX : 0 ≤ εX) (hεY : 0 ≤ εY)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hresX : dist (T (x₀, y₀)).1 x₀ ≤ εX)
    (hresY : dist (T (x₀, y₀)).2 y₀ ≤ εY)
    (hX : ∀ z z' : X × Y,
      dist z.1 x₀ ≤ perov2CanonicalRadiusX a b c d εX εY →
      dist z.2 y₀ ≤ perov2CanonicalRadiusY a b c d εX εY →
      dist z'.1 x₀ ≤ perov2CanonicalRadiusX a b c d εX εY →
      dist z'.2 y₀ ≤ perov2CanonicalRadiusY a b c d εX εY →
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      dist z.1 x₀ ≤ perov2CanonicalRadiusX a b c d εX εY →
      dist z.2 y₀ ≤ perov2CanonicalRadiusY a b c d εX εY →
      dist z'.1 x₀ ≤ perov2CanonicalRadiusX a b c d εX εY →
      dist z'.2 y₀ ≤ perov2CanonicalRadiusY a b c d εX εY →
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃! z : X × Y, T z = z ∧
      dist z.1 x₀ ≤ perov2CanonicalRadiusX a b c d εX εY ∧
      dist z.2 y₀ ≤ perov2CanonicalRadiusY a b c d εX εY := by
  obtain ⟨hrX, hrY, hRadX, hRadY⟩ :=
    perov2_canonicalRadii_spec hεX hεY hb_nn hc_nn hd_lt hSchur
  exact perov2_existsUnique_fixedPoint_in_closedBalls_of_residual
    T x₀ y₀
    (perov2CanonicalRadiusX a b c d εX εY)
    (perov2CanonicalRadiusY a b c d εX εY)
    εX εY hrX hrY ha_nn hb_nn hc_nn hd_nn hresX hresY hX hY
    (le_of_eq hRadX) (le_of_eq hRadY) hd_lt hSchur

end Perov
end Foundations
end Sanctions
