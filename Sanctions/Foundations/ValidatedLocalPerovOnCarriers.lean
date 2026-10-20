/-
Sanctions/Foundations/ValidatedLocalPerovOnCarriers.lean

A carrier-restricted localization of the two-coordinate Perov contraction
principle. This is abstract fixed-point infrastructure: it does not mention
the sanctions model and it adds no economic assumption.

Unlike the closed-ball theorem in `ValidatedLocalPerov`, the row estimates
below are required only where each coordinate lies in both its closed carrier
and its prescribed closed ball. The proof makes those intersections into
complete metric spaces and applies the existing two-row Perov theorem there.
-/

import Sanctions.Foundations.ValidatedLocalPerov

namespace Sanctions
namespace Foundations
namespace Perov

/-- **Validated local Perov certificate on closed carriers.**

Let `(x₀, y₀)` be an approximate fixed point of a two-coordinate operator
`T`, with each center in a closed carrier. Assume that:

* `T` preserves carrier membership on the product of the carrier-ball
  intersections;
* its two row estimates hold only on that restricted product;
* the center residuals and propagated radii fit back inside the two balls; and
* the nonnegative row matrix satisfies the Schur condition.

Then `T` has a fixed point in the product of the two carrier-ball
intersections, unique among fixed points in that restricted product. The
theorem derives ball invariance from the residual and radius inequalities;
only carrier preservation is supplied separately.

2026-10-06 (round BG1.1 follow-up): the first diagonal bound `a < 1` was
dropped from the signature. With `0 ≤ b`, `0 ≤ c` and `d < 1`, the Schur
margin already forces it (`lt_one_of_schur_margin`), and the Perov engine no
longer asks for it, so a witness has one fewer inequality to certify. F-free:
abstract metric-space content, valid for every transition law. -/
theorem perov2_existsUnique_fixedPoint_in_closedCarrierBalls_of_residual
    {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (CX : Set X) (CY : Set Y) (hCX : IsClosed CX) (hCY : IsClosed CY)
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y)
    (rX rY εX εY : ℝ) {a b c d : ℝ}
    (hx₀ : x₀ ∈ CX) (hy₀ : y₀ ∈ CY)
    (hrX : 0 ≤ rX) (hrY : 0 ≤ rY)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hresX : dist (T (x₀, y₀)).1 x₀ ≤ εX)
    (hresY : dist (T (x₀, y₀)).2 y₀ ≤ εY)
    (hmapX : ∀ z : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀ rX →
      z.2 ∈ CY ∩ Metric.closedBall y₀ rY → (T z).1 ∈ CX)
    (hmapY : ∀ z : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀ rX →
      z.2 ∈ CY ∩ Metric.closedBall y₀ rY → (T z).2 ∈ CY)
    (hX : ∀ z z' : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀ rX →
      z.2 ∈ CY ∩ Metric.closedBall y₀ rY →
      z'.1 ∈ CX ∩ Metric.closedBall x₀ rX →
      z'.2 ∈ CY ∩ Metric.closedBall y₀ rY →
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀ rX →
      z.2 ∈ CY ∩ Metric.closedBall y₀ rY →
      z'.1 ∈ CX ∩ Metric.closedBall x₀ rX →
      z'.2 ∈ CY ∩ Metric.closedBall y₀ rY →
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hRadX : εX + a * rX + b * rY ≤ rX)
    (hRadY : εY + c * rX + d * rY ≤ rY)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃! z : X × Y,
      T z = z ∧ z.1 ∈ CX ∩ Metric.closedBall x₀ rX ∧
        z.2 ∈ CY ∩ Metric.closedBall y₀ rY := by
  let BX : Set X := CX ∩ Metric.closedBall x₀ rX
  let BY : Set Y := CY ∩ Metric.closedBall y₀ rY
  let Xloc := {x : X // x ∈ BX}
  let Yloc := {y : Y // y ∈ BY}
  have hx₀loc : x₀ ∈ BX := ⟨hx₀, by simp [hrX]⟩
  have hy₀loc : y₀ ∈ BY := ⟨hy₀, by simp [hrY]⟩
  have hBX : IsClosed BX := hCX.inter Metric.isClosed_closedBall
  have hBY : IsClosed BY := hCY.inter Metric.isClosed_closedBall
  letI : Nonempty Xloc := ⟨⟨x₀, hx₀loc⟩⟩
  letI : Nonempty Yloc := ⟨⟨y₀, hy₀loc⟩⟩
  letI : CompleteSpace Xloc := hBX.completeSpace_coe
  letI : CompleteSpace Yloc := hBY.completeSpace_coe
  have hmapLocalX (z : Xloc × Yloc) : (T (z.1.1, z.2.1)).1 ∈ BX := by
    refine ⟨hmapX (z.1.1, z.2.1) z.1.2 z.2.2, ?_⟩
    have hzX : dist z.1.1 x₀ ≤ rX := by
      simpa [Metric.mem_closedBall] using z.1.2.2
    have hzY : dist z.2.1 y₀ ≤ rY := by
      simpa [Metric.mem_closedBall] using z.2.2.2
    have hrow :=
      hX (z.1.1, z.2.1) (x₀, y₀) z.1.2 z.2.2 hx₀loc hy₀loc
    change dist (T (z.1.1, z.2.1)).1 x₀ ≤ rX
    calc
      dist (T (z.1.1, z.2.1)).1 x₀ ≤
          dist (T (z.1.1, z.2.1)).1 (T (x₀, y₀)).1 +
            dist (T (x₀, y₀)).1 x₀ := dist_triangle _ _ _
      _ ≤ (a * dist z.1.1 x₀ + b * dist z.2.1 y₀) + εX :=
        add_le_add hrow hresX
      _ ≤ εX + a * rX + b * rY := by
        have hax := mul_le_mul_of_nonneg_left hzX ha_nn
        have hby := mul_le_mul_of_nonneg_left hzY hb_nn
        linarith
      _ ≤ rX := hRadX
  have hmapLocalY (z : Xloc × Yloc) : (T (z.1.1, z.2.1)).2 ∈ BY := by
    refine ⟨hmapY (z.1.1, z.2.1) z.1.2 z.2.2, ?_⟩
    have hzX : dist z.1.1 x₀ ≤ rX := by
      simpa [Metric.mem_closedBall] using z.1.2.2
    have hzY : dist z.2.1 y₀ ≤ rY := by
      simpa [Metric.mem_closedBall] using z.2.2.2
    have hrow :=
      hY (z.1.1, z.2.1) (x₀, y₀) z.1.2 z.2.2 hx₀loc hy₀loc
    change dist (T (z.1.1, z.2.1)).2 y₀ ≤ rY
    calc
      dist (T (z.1.1, z.2.1)).2 y₀ ≤
          dist (T (z.1.1, z.2.1)).2 (T (x₀, y₀)).2 +
            dist (T (x₀, y₀)).2 y₀ := dist_triangle _ _ _
      _ ≤ (c * dist z.1.1 x₀ + d * dist z.2.1 y₀) + εY :=
        add_le_add hrow hresY
      _ ≤ εY + c * rX + d * rY := by
        have hcx := mul_le_mul_of_nonneg_left hzX hc_nn
        have hdy := mul_le_mul_of_nonneg_left hzY hd_nn
        linarith
      _ ≤ rY := hRadY
  let Tlocal : Xloc × Yloc → Xloc × Yloc := fun z =>
    (⟨(T (z.1.1, z.2.1)).1, hmapLocalX z⟩,
     ⟨(T (z.1.1, z.2.1)).2, hmapLocalY z⟩)
  have hlocalX : ∀ z z' : Xloc × Yloc,
      dist (Tlocal z).1 (Tlocal z').1 ≤
        a * dist z.1 z'.1 + b * dist z.2 z'.2 := by
    intro z z'
    exact hX (z.1.1, z.2.1) (z'.1.1, z'.2.1) z.1.2 z.2.2 z'.1.2 z'.2.2
  have hlocalY : ∀ z z' : Xloc × Yloc,
      dist (Tlocal z).2 (Tlocal z').2 ≤
        c * dist z.1 z'.1 + d * dist z.2 z'.2 := by
    intro z z'
    exact hY (z.1.1, z.2.1) (z'.1.1, z'.2.1) z.1.2 z.2.2 z'.1.2 z'.2.2
  obtain ⟨w, hw, huniq⟩ := perov2_existsUnique_fixedPoint Tlocal
    ha_nn hb_nn hc_nn hd_nn hlocalX hlocalY hd_lt hSchur
  have hfixX : (T (w.1.1, w.2.1)).1 = w.1.1 := by
    have := congrArg (fun q : Xloc × Yloc => q.1.1) hw
    simpa [Tlocal] using this
  have hfixY : (T (w.1.1, w.2.1)).2 = w.2.1 := by
    have := congrArg (fun q : Xloc × Yloc => q.2.1) hw
    simpa [Tlocal] using this
  have hfix : T (w.1.1, w.2.1) = (w.1.1, w.2.1) := Prod.ext hfixX hfixY
  refine ⟨(w.1.1, w.2.1), ⟨hfix, w.1.2, w.2.2⟩, ?_⟩
  intro z hz
  let wz : Xloc × Yloc := (⟨z.1, hz.2.1⟩, ⟨z.2, hz.2.2⟩)
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

/-! ## Carrier theorem with radii constructed from a residual bound

The theorem below is the entry point a witness should use. Its caller supplies
the row matrix `M = ((a,b),(c,d))`, a bound `ε = (εX, εY)` on the two centre
residuals, and the Schur condition — and **no radius at all**. The radii are
the closed-form coordinates of `(I - M)⁻¹ ε`, which
`perov2_canonicalRadii_isLeast` proves are the componentwise smallest pair
passing the two self-map budget checks. So a witness can no longer choose a
radius: it can only choose worse.

Honest scope: the residual vector `ε` is *not* eliminated by this. It is still
evaluated at a constructed centre, and in the concrete witnesses it is still a
rational number read off an explicit centre and an explicit Bellman operator.
What disappears is the separate radius packet that used to be tuned until the
two budget inequalities happened to close. -/

/-- **Carrier-local Perov theorem with radii derived from a residual bound.**

Same shape as `perov2_existsUnique_fixedPoint_in_closedCarrierBalls_of_residual`,
except that the two ball radii are no longer parameters: they are
`perov2CanonicalRadiusX/Y a b c d εX εY`, the exact solution of
`(I - M) r = ε`. Consequently the two radius self-map hypotheses `hRadX`,
`hRadY` disappear from the signature — they hold as identities
(`perov2_canonicalRadii_spec`) rather than as numerical obligations the caller
must discharge.

The caller therefore supplies only: the two closed carriers and the centre's
membership in them; the nonnegative row matrix with `d < 1` and the Schur
determinant condition; a bound on each coordinate residual at the centre; and
the carrier-preservation and row-Lipschitz estimates on the resulting
carrier-ball product.

Nonnegativity of `εX, εY` is required only because it is what makes the derived
radii nonnegative; it is automatic whenever `ε` bounds a distance.

2026-10-06 (round BG1.1 follow-up): the hypothesis `a < 1` was dropped; the
signs, `d < 1` and the Schur margin imply it (`lt_one_of_schur_margin`).
F-free: abstract metric-space content. -/
theorem perov2_existsUnique_fixedPoint_in_canonical_closedCarrierBalls_of_residual
    {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (CX : Set X) (CY : Set Y) (hCX : IsClosed CX) (hCY : IsClosed CY)
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y)
    (εX εY : ℝ) {a b c d : ℝ}
    (hx₀ : x₀ ∈ CX) (hy₀ : y₀ ∈ CY)
    (hεX : 0 ≤ εX) (hεY : 0 ≤ εY)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hresX : dist (T (x₀, y₀)).1 x₀ ≤ εX)
    (hresY : dist (T (x₀, y₀)).2 y₀ ≤ εY)
    (hmapX : ∀ z : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) →
      (T z).1 ∈ CX)
    (hmapY : ∀ z : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) →
      (T z).2 ∈ CY)
    (hX : ∀ z z' : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) →
      z'.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) →
      z'.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) →
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) →
      z'.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) →
      z'.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) →
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃! z : X × Y,
      T z = z ∧
        z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2CanonicalRadiusX a b c d εX εY) ∧
        z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2CanonicalRadiusY a b c d εX εY) := by
  obtain ⟨hrX, hrY, hRadX, hRadY⟩ :=
    perov2_canonicalRadii_spec hεX hεY hb_nn hc_nn hd_lt hSchur
  exact
    perov2_existsUnique_fixedPoint_in_closedCarrierBalls_of_residual
      CX CY hCX hCY T x₀ y₀
      (perov2CanonicalRadiusX a b c d εX εY)
      (perov2CanonicalRadiusY a b c d εX εY)
      εX εY hx₀ hy₀ hrX hrY ha_nn hb_nn hc_nn hd_nn hresX hresY
      hmapX hmapY hX hY (le_of_eq hRadX) (le_of_eq hRadY)
      hd_lt hSchur

/-! ## Carrier theorem with radii constructed from the actual residual -/

/-- The Target-coordinate validation radius obtained by substituting the
operator's actual center residuals into the existing canonical formula
`(I - M)⁻¹ ε`. -/
noncomputable def perov2ResidualRadiusX
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y) (a b c d : ℝ) : ℝ :=
  perov2CanonicalRadiusX a b c d
    (dist (T (x₀, y₀)).1 x₀) (dist (T (x₀, y₀)).2 y₀)

/-- The Sender-coordinate validation radius obtained by substituting the
operator's actual center residuals into the existing canonical formula
`(I - M)⁻¹ ε`. -/
noncomputable def perov2ResidualRadiusY
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y) (a b c d : ℝ) : ℝ :=
  perov2CanonicalRadiusY a b c d
    (dist (T (x₀, y₀)).1 x₀) (dist (T (x₀, y₀)).2 y₀)

/-- **Carrier-local Perov theorem with analytically constructed radii.**

The validation radii are not inputs. They are the two coordinates of
`(I - M)⁻¹ ε`, where `ε` is the operator's actual residual vector at the
chosen center. Thus the two radius self-map inequalities are identities,
not numerical obligations supplied by a witness.

2026-10-06 (round BG1.1 follow-up): the hypothesis `a < 1` was dropped; the
signs, `d < 1` and the Schur margin imply it (`lt_one_of_schur_margin`).
F-free: abstract metric-space content. -/
theorem perov2_existsUnique_fixedPoint_in_canonical_closedCarrierBalls
    {X Y : Type*} [MetricSpace X] [CompleteSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (CX : Set X) (CY : Set Y) (hCX : IsClosed CX) (hCY : IsClosed CY)
    (T : X × Y → X × Y) (x₀ : X) (y₀ : Y) {a b c d : ℝ}
    (hx₀ : x₀ ∈ CX) (hy₀ : y₀ ∈ CY)
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hmapX : ∀ z : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) →
      (T z).1 ∈ CX)
    (hmapY : ∀ z : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) →
      (T z).2 ∈ CY)
    (hX : ∀ z z' : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) →
      z'.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) →
      z'.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) →
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) →
      z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) →
      z'.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) →
      z'.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) →
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃! z : X × Y,
      T z = z ∧
        z.1 ∈ CX ∩ Metric.closedBall x₀
          (perov2ResidualRadiusX T x₀ y₀ a b c d) ∧
        z.2 ∈ CY ∩ Metric.closedBall y₀
          (perov2ResidualRadiusY T x₀ y₀ a b c d) := by
  let εX := dist (T (x₀, y₀)).1 x₀
  let εY := dist (T (x₀, y₀)).2 y₀
  obtain ⟨hrX, hrY, hRadX, hRadY⟩ :=
    perov2_canonicalRadii_spec
      (a := a) (b := b) (c := c) (d := d) (εX := εX) (εY := εY)
      (by exact dist_nonneg) (by exact dist_nonneg)
      hb_nn hc_nn hd_lt hSchur
  have hrX' : 0 ≤ perov2ResidualRadiusX T x₀ y₀ a b c d := by
    simpa only [perov2ResidualRadiusX, εX, εY] using hrX
  have hrY' : 0 ≤ perov2ResidualRadiusY T x₀ y₀ a b c d := by
    simpa only [perov2ResidualRadiusY, εX, εY] using hrY
  have hRadX' :
      εX + a * perov2ResidualRadiusX T x₀ y₀ a b c d +
          b * perov2ResidualRadiusY T x₀ y₀ a b c d ≤
        perov2ResidualRadiusX T x₀ y₀ a b c d := by
    simpa only [perov2ResidualRadiusX, perov2ResidualRadiusY, εX, εY] using
      hRadX.le
  have hRadY' :
      εY + c * perov2ResidualRadiusX T x₀ y₀ a b c d +
          d * perov2ResidualRadiusY T x₀ y₀ a b c d ≤
        perov2ResidualRadiusY T x₀ y₀ a b c d := by
    simpa only [perov2ResidualRadiusX, perov2ResidualRadiusY, εX, εY] using
      hRadY.le
  exact
    perov2_existsUnique_fixedPoint_in_closedCarrierBalls_of_residual
      CX CY hCX hCY T x₀ y₀
      (perov2ResidualRadiusX T x₀ y₀ a b c d)
      (perov2ResidualRadiusY T x₀ y₀ a b c d)
      εX εY hx₀ hy₀ hrX' hrY' ha_nn hb_nn hc_nn hd_nn
      (by exact le_rfl) (by exact le_rfl) hmapX hmapY hX hY
      hRadX' hRadY' hd_lt hSchur

end Perov
end Foundations
end Sanctions
