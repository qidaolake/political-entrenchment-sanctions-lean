/-
Sanctions/Examples/ChordEconomyQuarticWitness.lean

**A chord economy non-affine in every coordinate** (round AW, 2026-09-25;
doc 104 §6, Rule 9B generality).

## What this file is

The chord economy (`Examples/ChordEconomy`) states the placable-Sender class
through one-sided rate bounds on both stage payoffs. Every member built before
this file came from the quadratic–linear family through `toChord`, so the class
was certified inhabited only at points of the case it generalises: non-vacuity,
not generality (Rule 9B). This file builds a member outside the family in every
coordinate:

* the Sender's payoff is quartic in the sanction and quadratic in compliance and
  in the state,
  `U_S = −(3/2)s² − s⁴/8 + s(1 − 3a − a²/4 + x/2 + x²/8) + x − x²/10`;
* the Target's payoff is quadratic in compliance and in the sanction, with a
  state-dependent rally,
  `U_T = −a − a²/8 − 4s − s²/4 + xs/2 + x²s/8 + 30x − x²`;
* the transition is `quadDiagF` (proved not the affine law at any rate);
* the stage selector `σ` is the Berge argmax of the Sender's strictly concave
  stage payoff (`Foundations/Berge`), defined as an argmax rather than by a
  formula (its first-order condition is a cubic in the sanction).

Ten lower/upper rate pairs are strictly split (`qw_pairs_split`: `w`, `q`/`Q̄`,
`r`, `k`, `u`, `ℓ`, `p_lo`/`c`, `v`, `g`, `d`); the Target's envelope slopes are
ordered the other way, `n_lo = 3/4 > n_hi = 1/2`, as envelopes with different
intercepts may be. Neither
payoff is of the quadratic–linear form at any coefficients
(`qwU_S_ne_symU_S`, `qwU_T_ne_symU_T`).

## The rates, each a theorem here

Sender: `w_lo = 4/5`, `w_hi = 31/20`, `σ_x = 1/20`, `τ_x = 1/5`, `r_lo = 1/2`,
`r_hi = 3/4`, `q = 3`, `Q̄ = 9/2`, `k_lo = 3`, `k_hi = 7/2`, `u_hi = 13/8`,
`u_lo = 1`. Target: `ℓ_lo = 1`, `ℓ_hi = 5/4`, `p_lo = 27/8`, `c = 9/2`,
`v_lo = 28`, `n_lo = 3/4`, `v_hi = 30`, `n_hi = 1/2`. Transition (`quadDiagF`):
`g_lo = d_lo = 2/5`, `g_hi = d_hi = 3/5`, `M_x = 1/5`, `M_cs = 1/5`, the other
moduli zero. Carrier modulus `SigV = 1` (closure slack `3183/13160`).

## What is shown at the two members

* **`β_T = 1/30`, the relief side** (`qwRelief`): the relief equilibrium exists
  (`qwRelief_reliefEquilibrium`), its realised sanction is zero at every state,
  and it is the only equilibrium whose Sender value lies in the carrier class
  (`qwRelief_unique_in_carrier_class`, round AV's M9 theorem).
* **`β_T = 1/2`, the defiance side** (`qwDefiance`): the loss-offset margin and
  the rally margin hold, the four cells hold (`qwDefiance_four_cells`, the paper's
  Theorem 1), and both continuation channels are active at the constructed
  equilibrium (`qwDefiance_both_channels`).

## Scope (Rule 9A)

An existence certificate and nothing more: the class of `Examples/ChordEconomy`
contains a member that is quadratic–linear in none of its payoff coordinates and
affine in none of its transition coordinates, and the headline results apply
there. It licenses no claim about how common such members are, and nothing
about magnitudes. The numbers were located and checked in exact rational
arithmetic before this file was written (Rule 9C; the probes are archived under
`docs/archive/workflow-scratch/abstract_payoffs_*`). The chord conditions are
proved here from exact chord-gap identities, not by grid enumeration (Rule 13).

## Rule 9B vacuity checks

`ChordEconomy` and `ChordEconomyCs` have no `Prop`-typed data fields, so the
`w.f = True` check has no field to apply to. Every field is a proof of a
statement about the concrete data. The witness is a `def` reducing to concrete
data, and the joint satisfiability of each theorem's hypotheses is the member
itself.
-/
import Sanctions.Examples.PlacableSenderReliefUniqueness
import Sanctions.Examples.PlacableSenderReliefActivation
import Sanctions.Foundations.Berge

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave

noncomputable section

/-! ## 1. The payoffs and the exact chord gaps -/

/-- The witness's Sender stage payoff: quartic in the sanction, quadratic in
compliance and in the state. -/
def qwU_S (x a s : ℝ) : ℝ :=
  -(3 / 2) * s ^ 2 - s ^ 4 / 8 + s * (1 - 3 * a - a ^ 2 / 4 + x / 2 + x ^ 2 / 8) + x - x ^ 2 / 10

/-- The witness's Target stage payoff: quadratic in compliance and in the
sanction, with a state-dependent rally. -/
def qwU_T (x a s : ℝ) : ℝ :=
  -a - a ^ 2 / 8 - 4 * s - s ^ 2 / 4 + x * s / 2 + x ^ 2 * s / 8 + 30 * x - x ^ 2

theorem qwU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => qwU_S xas.1 xas.2.1 xas.2.2) := by
  unfold qwU_S; fun_prop

theorem qwU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => qwU_T xas.1 xas.2.1 xas.2.2) := by
  unfold qwU_T; fun_prop

/-- The weight in the chord gap of `z ↦ z⁴`. -/
def quarticWeight (a b t : ℝ) : ℝ :=
  (t ^ 2 + t + 1) * a ^ 2 + (-2 * t ^ 2 + 2 * t + 2) * (a * b) + (t ^ 2 - 3 * t + 3) * b ^ 2

/-- **The chord gap of `z ↦ z⁴`, exactly**:
`t a⁴ + (1−t) b⁴ − (ta + (1−t)b)⁴ = t(1−t)(a−b)²·W(a,b,t)`. -/
theorem quartic_chord_gap (a b t : ℝ) :
    t * a ^ 4 + (1 - t) * b ^ 4 - (t * a + (1 - t) * b) ^ 4
      = t * (1 - t) * (a - b) ^ 2 * quarticWeight a b t := by
  unfold quarticWeight; ring

theorem quarticWeight_coeffs {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t ^ 2 + t + 1 ∧ 0 ≤ -2 * t ^ 2 + 2 * t + 2 ∧ 0 ≤ t ^ 2 - 3 * t + 3 := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem quarticWeight_nonneg {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ quarticWeight a b t := by
  obtain ⟨h1, h2, h3⟩ := quarticWeight_coeffs ht0 ht1
  unfold quarticWeight
  have := mul_nonneg h1 (sq_nonneg a)
  have := mul_nonneg h2 (mul_nonneg ha hb)
  have := mul_nonneg h3 (sq_nonneg b)
  linarith

theorem quarticWeight_le_six {a b t : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : quarticWeight a b t ≤ 6 := by
  obtain ⟨h1, h2, h3⟩ := quarticWeight_coeffs ht0 ht1
  unfold quarticWeight
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hab : a * b ≤ 1 := by nlinarith [ha.1, ha.2, hb.1, hb.2]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
  have e1 := mul_le_mul_of_nonneg_left ha2 h1
  have e2 := mul_le_mul_of_nonneg_left hab h2
  have e3 := mul_le_mul_of_nonneg_left hb2 h3
  nlinarith [e1, e2, e3]

/-- The Sender's state increment at a fixed compliance and sanction. -/
theorem qwU_S_state_diff (x₁ x₂ a s : ℝ) :
    qwU_S x₂ a s - qwU_S x₁ a s = (x₂ - x₁) * (1 + s / 2 + (x₁ + x₂) * (s / 8 - 1 / 10)) := by
  unfold qwU_S; ring

theorem qw_stateRate_bounds {x₁ x₂ s : ℝ} (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (hx₂ : x₂ ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    4 / 5 ≤ 1 + s / 2 + (x₁ + x₂) * (s / 8 - 1 / 10) ∧
      1 + s / 2 + (x₁ + x₂) * (s / 8 - 1 / 10) ≤ 31 / 20 := by
  have hS0 : 0 ≤ x₁ + x₂ := add_nonneg hx₁.1 hx₂.1
  have hS2 : x₁ + x₂ ≤ 2 := by linarith [hx₁.2, hx₂.2]
  have h1 := mul_nonneg hS0 hs.1
  have h2 := mul_le_mul_of_nonneg_left hs.2 hS0
  have hB : 1 + s / 2 + (x₁ + x₂) * (s / 8 - 1 / 10)
      = 1 + s / 2 + (x₁ + x₂) * s / 8 - (x₁ + x₂) / 10 := by ring
  rw [hB]
  constructor
  · linarith [hs.1]
  · linarith [hs.2]

/-- The Sender's sanction chord gap at a fixed state and compliance. -/
theorem qwU_S_sanction_gap (x a s₁ s₂ t : ℝ) :
    t * qwU_S x a s₁ + (1 - t) * qwU_S x a s₂ - qwU_S x a (t * s₁ + (1 - t) * s₂)
      = -(3 / 2) * (t * (1 - t) * (s₁ - s₂) ^ 2)
        - t * (1 - t) * (s₁ - s₂) ^ 2 * quarticWeight s₁ s₂ t / 8 := by
  unfold qwU_S quarticWeight; ring

/-- The Sender's joint chord gap at defiance, in (state, sanction). -/
theorem qwU_S_joint_gap (x₁ x₂ s₁ s₂ t : ℝ) :
    t * qwU_S x₁ 0 s₁ + (1 - t) * qwU_S x₂ 0 s₂
        - qwU_S (t * x₁ + (1 - t) * x₂) 0 (t * s₁ + (1 - t) * s₂)
      = t * (1 - t) * (-(3 / 2) * (s₁ - s₂) ^ 2 - quarticWeight s₁ s₂ t * (s₁ - s₂) ^ 2 / 8
          + (1 / 2) * ((x₁ - x₂) * (s₁ - s₂))
          + ((x₁ - x₂) * (s₁ - s₂) * (x₁ + x₂) + (x₁ - x₂) ^ 2 * (t * s₁ + (1 - t) * s₂)) / 8
          - (x₁ - x₂) ^ 2 / 10) := by
  unfold qwU_S quarticWeight; ring

/-- The Sender's state chord gap at defiance and a fixed sanction. -/
theorem qwU_S_state_gap (s x₁ x₂ t : ℝ) :
    qwU_S (t * x₁ + (1 - t) * x₂) 0 s - (t * qwU_S x₁ 0 s + (1 - t) * qwU_S x₂ 0 s)
      = (1 / 10 - s / 8) * (t * (1 - t) * (x₁ - x₂) ^ 2) := by
  unfold qwU_S; ring

/-- The Sender's (state; sanction) cross difference, at any compliance. -/
theorem qwU_S_cross_xs (x x' a s s' : ℝ) :
    (qwU_S x' a s' - qwU_S x' a s) - (qwU_S x a s' - qwU_S x a s)
      = (x' - x) * (s' - s) * (1 / 2 + (x + x') / 8) := by
  unfold qwU_S; ring

/-- The Sender's (compliance; sanction) cross difference, at any state. -/
theorem qwU_S_cross_as (x a a' s s' : ℝ) :
    (qwU_S x a' s' - qwU_S x a' s) - (qwU_S x a s' - qwU_S x a s)
      = -((a' - a) * (s' - s) * (3 + (a + a') / 4)) := by
  unfold qwU_S; ring

/-- The Sender's sanction increment at defiance. -/
theorem qwU_S_sanction_diff (x t s : ℝ) :
    qwU_S x 0 s - qwU_S x 0 t
      = (s - t) * ((1 + x / 2 + x ^ 2 / 8) - (3 / 2) * (s + t) - (s + t) * (s ^ 2 + t ^ 2) / 8) :=
          by
  unfold qwU_S; ring

/-! ## 2. The Sender's rate conditions -/

theorem qw_US_stateLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
    |qwU_S x₂ 0 s - qwU_S x₁ 0 s| ≤ 31 / 20 * |x₂ - x₁| := by
  intro s hs x₁ hx₁ x₂ hx₂
  obtain ⟨hlo, hhi⟩ := qw_stateRate_bounds hx₁ hx₂ hs
  have hpos : 0 < 1 + s / 2 + (x₁ + x₂) * (s / 8 - 1 / 10) := by linarith
  rw [qwU_S_state_diff, abs_mul, abs_of_pos hpos]
  have := mul_le_mul_of_nonneg_left hhi (abs_nonneg (x₂ - x₁))
  linarith

theorem qw_US_stateSlope : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, x₁ ≤ x₂ → 4 / 5 * (x₂ - x₁) ≤ qwU_S x₂ a s - qwU_S x₁ a s := by
  intro a _ s hs x₁ hx₁ x₂ hx₂ hle
  obtain ⟨hlo, -⟩ := qw_stateRate_bounds hx₁ hx₂ hs
  rw [qwU_S_state_diff]
  have := mul_le_mul_of_nonneg_left hlo (sub_nonneg.2 hle)
  linarith

theorem qw_US_concave : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a : ℝ,
    SemiconcaveOnSet (fun s => qwU_S x a s) (Icc (0 : ℝ) 1) (-3) := by
  intro x _ a s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hgap := qwU_S_sanction_gap x a s₁ s₂ t
  have hT : 0 ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have hP := quarticWeight_nonneg hs₁.1 hs₂.1 ht0 ht1
  have := mul_nonneg hT hP
  simp only
  linarith

theorem qw_US_convex : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    SemiconvexOnSet (fun s => qwU_S x a s) (Icc (0 : ℝ) 1) (9 / 2) := by
  intro x _ a _ s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hgap := qwU_S_sanction_gap x a s₁ s₂ t
  have hT : 0 ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have hP := quarticWeight_le_six hs₁ hs₂ ht0 ht1
  have := mul_le_mul_of_nonneg_left hP hT
  simp only
  linarith

theorem qw_US_joint :
    JointSemiconcaveOn (fun x s => qwU_S x 0 s) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
      (1 / 20) (3 / 4) 3 := by
  intro x₁ hx₁ x₂ hx₂ s₁ hs₁ s₂ hs₂ t ht0 ht1
  simp only
  rw [qwU_S_joint_gap]
  have htt : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have hP := quarticWeight_nonneg hs₁.1 hs₂.1 ht0 ht1
  have hPs := mul_nonneg hP (sq_nonneg (s₁ - s₂))
  -- the cross coefficient `1/2 + (x₁ + x₂)/8 ∈ [1/2, 3/4]`
  have hc0 : 0 ≤ 1 / 2 + (x₁ + x₂) / 8 := by linarith [hx₁.1, hx₂.1]
  have hc1 : 1 / 2 + (x₁ + x₂) / 8 ≤ 3 / 4 := by linarith [hx₁.2, hx₂.2]
  have hprod : (x₁ - x₂) * (s₁ - s₂) ≤ |x₁ - x₂| * |s₁ - s₂| := by
    rw [← abs_mul]; exact le_abs_self _
  have habs : 0 ≤ |x₁ - x₂| * |s₁ - s₂| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hcross : (1 / 2 + (x₁ + x₂) / 8) * ((x₁ - x₂) * (s₁ - s₂))
      ≤ 3 / 4 * (|x₁ - x₂| * |s₁ - s₂|) := by
    calc (1 / 2 + (x₁ + x₂) / 8) * ((x₁ - x₂) * (s₁ - s₂))
        ≤ (1 / 2 + (x₁ + x₂) / 8) * (|x₁ - x₂| * |s₁ - s₂|) :=
          mul_le_mul_of_nonneg_left hprod hc0
      _ ≤ 3 / 4 * (|x₁ - x₂| * |s₁ - s₂|) := mul_le_mul_of_nonneg_right hc1 habs
  -- the state coefficient: `m_s ≤ 1`
  have hms : t * s₁ + (1 - t) * s₂ ≤ 1 := by nlinarith [hs₁.2, hs₂.2]
  have hms' := mul_le_mul_of_nonneg_left hms (sq_nonneg (x₁ - x₂))
  have key : -(3 / 2) * (s₁ - s₂) ^ 2 - quarticWeight s₁ s₂ t * (s₁ - s₂) ^ 2 / 8
        + (1 / 2) * ((x₁ - x₂) * (s₁ - s₂))
        + ((x₁ - x₂) * (s₁ - s₂) * (x₁ + x₂) + (x₁ - x₂) ^ 2 * (t * s₁ + (1 - t) * s₂)) / 8
        - (x₁ - x₂) ^ 2 / 10
      ≤ 1 / 2 * (1 / 20 * (x₁ - x₂) ^ 2 + 2 * (3 / 4) * |x₁ - x₂| * |s₁ - s₂|
          - 3 * (s₁ - s₂) ^ 2) := by
    nlinarith [hcross, hms', hPs]
  calc t * (1 - t) * (-(3 / 2) * (s₁ - s₂) ^ 2 - quarticWeight s₁ s₂ t * (s₁ - s₂) ^ 2 / 8
          + (1 / 2) * ((x₁ - x₂) * (s₁ - s₂))
          + ((x₁ - x₂) * (s₁ - s₂) * (x₁ + x₂) + (x₁ - x₂) ^ 2 * (t * s₁ + (1 - t) * s₂)) / 8
          - (x₁ - x₂) ^ 2 / 10)
      ≤ t * (1 - t) * (1 / 2 * (1 / 20 * (x₁ - x₂) ^ 2 + 2 * (3 / 4) * |x₁ - x₂| * |s₁ - s₂|
          - 3 * (s₁ - s₂) ^ 2)) := mul_le_mul_of_nonneg_left key htt
    _ = t * (1 - t) / 2 * (1 / 20 * (x₁ - x₂) ^ 2 + 2 * (3 / 4) * |x₁ - x₂| * |s₁ - s₂|
          - 3 * (s₁ - s₂) ^ 2) := by ring

theorem qw_US_stateConvex : ∀ s ∈ Icc (0 : ℝ) 1,
    SemiconvexOnSet (fun x => qwU_S x 0 s) (Icc (0 : ℝ) 1) (1 / 5) := by
  intro s hs x₁ _ x₂ _ t ht0 ht1
  simp only
  rw [qwU_S_state_gap]
  have hT : 0 ≤ t * (1 - t) * (x₁ - x₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have := mul_nonneg hs.1 hT
  nlinarith

theorem qw_US_crossLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ s' ∈ Icc (0 : ℝ) 1, x ≤ x' → s ≤ s' →
      1 / 2 * ((x' - x) * (s' - s)) ≤ (qwU_S x' 0 s' - qwU_S x' 0 s) - (qwU_S x 0 s' - qwU_S x 0 s)
          := by
  intro x hx x' hx' s _ s' _ hxx' hss'
  rw [qwU_S_cross_xs]
  have hP : 0 ≤ (x' - x) * (s' - s) := mul_nonneg (by linarith) (by linarith)
  have := mul_nonneg hP (by linarith [hx.1, hx'.1] : (0 : ℝ) ≤ (x + x') / 8)
  nlinarith

theorem qw_US_crossHi : ∀ a ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |(qwU_S x' a s' - qwU_S x' a s) - (qwU_S x a s' - qwU_S x a s)|
        ≤ 3 / 4 * (|x' - x| * |s' - s|) := by
  intro a _ x hx x' hx' s _ s' _
  rw [qwU_S_cross_xs, abs_mul, abs_mul, abs_of_nonneg (by linarith [hx.1, hx'.1] :
    (0 : ℝ) ≤ 1 / 2 + (x + x') / 8)]
  have hc1 : 1 / 2 + (x + x') / 8 ≤ 3 / 4 := by linarith [hx.2, hx'.2]
  have habs : 0 ≤ |x' - x| * |s' - s| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

theorem qw_US_placLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' → s ≤ s' →
      (qwU_S x a' s' - qwU_S x a' s) - (qwU_S x a s' - qwU_S x a s) ≤ -(3 * ((a' - a) * (s' - s)))
          := by
  intro x _ a ha a' ha' s _ s' _ haa' hss'
  rw [qwU_S_cross_as]
  have hP : 0 ≤ (a' - a) * (s' - s) := mul_nonneg (by linarith) (by linarith)
  have := mul_nonneg hP (by linarith [ha.1, ha'.1] : (0 : ℝ) ≤ (a + a') / 4)
  nlinarith

theorem qw_US_placHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, a ≤ a' →
      |(qwU_S x a' s' - qwU_S x a' s) - (qwU_S x a s' - qwU_S x a s)|
        ≤ 7 / 2 * ((a' - a) * |s' - s|) := by
  intro x _ a ha a' ha' s _ s' _ haa'
  rw [qwU_S_cross_as, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a' - a),
    abs_of_nonneg (by linarith [ha.1, ha'.1] : (0 : ℝ) ≤ 3 + (a + a') / 4)]
  have hc1 : 3 + (a + a') / 4 ≤ 7 / 2 := by linarith [ha.2, ha'.2]
  have hP : 0 ≤ (a' - a) * |s' - s| := mul_nonneg (by linarith) (abs_nonneg _)
  nlinarith

theorem qw_US_appetite : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
    (s - t) * (3 * (s + t) / 2 - 13 / 8) ≤ qwU_S x 0 t - qwU_S x 0 s := by
  intro x hx t ht s hs hts
  have h := qwU_S_sanction_diff x t s
  have hd : 0 ≤ s - t := by linarith
  have hx8 : 1 + x / 2 + x ^ 2 / 8 ≤ 13 / 8 := by nlinarith [hx.1, hx.2]
  have hq : 0 ≤ (s + t) * (s ^ 2 + t ^ 2) / 8 := by
    have := mul_nonneg (add_nonneg hs.1 ht.1) (add_nonneg (sq_nonneg s) (sq_nonneg t))
    linarith
  have e1 := mul_le_mul_of_nonneg_left hx8 hd
  have e2 := mul_nonneg hd hq
  nlinarith

theorem qw_US_floor : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s →
    (s - t) * (1 - 9 / 2 * (s + t) / 2) ≤ qwU_S x 0 s - qwU_S x 0 t := by
  intro x hx t ht s hs hts
  rw [qwU_S_sanction_diff]
  have hd : 0 ≤ s - t := by linarith
  have hx0 : 0 ≤ x / 2 + x ^ 2 / 8 := by nlinarith [hx.1]
  have hsq : s ^ 2 + t ^ 2 ≤ 6 := by nlinarith [hs.1, hs.2, ht.1, ht.2]
  have hst : 0 ≤ s + t := add_nonneg hs.1 ht.1
  have hq : (s + t) * (s ^ 2 + t ^ 2) / 8 ≤ 3 / 4 * (s + t) := by nlinarith
  have hbr : 1 - 9 / 2 * (s + t) / 2
      ≤ (1 + x / 2 + x ^ 2 / 8) - (3 / 2) * (s + t) - (s + t) * (s ^ 2 + t ^ 2) / 8 := by
    linarith
  exact mul_le_mul_of_nonneg_left hbr hd

/-! ## 3. The Target's rate conditions -/

theorem qwU_T_compliance_diff (x a₁ a₂ s : ℝ) :
    qwU_T x a₂ s - qwU_T x a₁ s = -((a₂ - a₁) * (1 + (a₁ + a₂) / 8)) := by
  unfold qwU_T; ring

theorem qwU_T_sanction_diff (x a s₁ s₂ : ℝ) :
    qwU_T x a s₁ - qwU_T x a s₂ = (s₂ - s₁) * (4 + (s₁ + s₂) / 4 - x / 2 - x ^ 2 / 8) := by
  unfold qwU_T; ring

theorem qwU_T_state_diff (x₁ x₂ a s : ℝ) :
    qwU_T x₂ a s - qwU_T x₁ a s
      = (x₂ - x₁) * (s / 2 + (x₁ + x₂) * s / 8 + 30 - (x₁ + x₂)) := by
  unfold qwU_T; ring

theorem qw_UT_costLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1,
    ∀ a₂ ∈ Icc (0 : ℝ) 1, a₁ ≤ a₂ → qwU_T x a₂ s - qwU_T x a₁ s ≤ -(1 * (a₂ - a₁)) := by
  intro x _ s _ a₁ ha₁ a₂ ha₂ hle
  rw [qwU_T_compliance_diff]
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ a₂ - a₁) (by linarith [ha₁.1, ha₂.1] :
    (0 : ℝ) ≤ (a₁ + a₂) / 8)
  nlinarith

theorem qw_UT_costHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1,
    ∀ a₂ ∈ Icc (0 : ℝ) 1, a₁ ≤ a₂ → -(5 / 4 * (a₂ - a₁)) ≤ qwU_T x a₂ s - qwU_T x a₁ s := by
  intro x _ s _ a₁ ha₁ a₂ ha₂ hle
  rw [qwU_T_compliance_diff]
  have := mul_le_mul_of_nonneg_left (by linarith [ha₁.2, ha₂.2] : (a₁ + a₂) / 8 ≤ 1 / 4)
    (by linarith : (0 : ℝ) ≤ a₂ - a₁)
  nlinarith

theorem qw_UT_painHi : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1,
    ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ → qwU_T x a s₁ - qwU_T x a s₂ ≤ 9 / 2 * (s₂ - s₁) := by
  intro x hx a _ s₁ hs₁ s₂ hs₂ hle
  rw [qwU_T_sanction_diff]
  have hbr : 4 + (s₁ + s₂) / 4 - x / 2 - x ^ 2 / 8 ≤ 9 / 2 := by
    nlinarith [hs₁.2, hs₂.2, hx.1]
  have := mul_le_mul_of_nonneg_left hbr (by linarith : (0 : ℝ) ≤ s₂ - s₁)
  linarith

theorem qw_UT_painLo : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1,
    ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ → 27 / 8 * (s₂ - s₁) ≤ qwU_T x a s₁ - qwU_T x a s₂ := by
  intro x hx a _ s₁ hs₁ s₂ hs₂ hle
  rw [qwU_T_sanction_diff]
  have hbr : 27 / 8 ≤ 4 + (s₁ + s₂) / 4 - x / 2 - x ^ 2 / 8 := by
    nlinarith [hs₁.1, hs₂.1, hx.1, hx.2]
  have := mul_le_mul_of_nonneg_left hbr (by linarith : (0 : ℝ) ≤ s₂ - s₁)
  linarith

theorem qw_UT_stateLo : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, x₁ ≤ x₂ → (28 + 3 / 4 * s) * (x₂ - x₁) ≤ qwU_T x₂ a s - qwU_T x₁ a s := by
  intro a _ s hs x₁ hx₁ x₂ hx₂ hle
  rw [qwU_T_state_diff, mul_comm]
  have hbr : 28 + 3 / 4 * s ≤ s / 2 + (x₁ + x₂) * s / 8 + 30 - (x₁ + x₂) := by
    have h := mul_nonneg (by linarith [hx₁.2, hx₂.2] : (0 : ℝ) ≤ 2 - (x₁ + x₂))
      (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s / 8)
    nlinarith
  exact mul_le_mul_of_nonneg_left hbr (by linarith)

theorem qw_UT_stateHi : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1,
    ∀ x₂ ∈ Icc (0 : ℝ) 1, |qwU_T x₂ a s - qwU_T x₁ a s| ≤ (30 + 1 / 2 * s) * |x₂ - x₁| := by
  intro a _ s hs x₁ hx₁ x₂ hx₂
  have hS0 : 0 ≤ x₁ + x₂ := add_nonneg hx₁.1 hx₂.1
  have hlo : 0 < s / 2 + (x₁ + x₂) * s / 8 + 30 - (x₁ + x₂) := by
    nlinarith [hx₁.2, hx₂.2, mul_nonneg hS0 hs.1, hs.1]
  have hhi : s / 2 + (x₁ + x₂) * s / 8 + 30 - (x₁ + x₂) ≤ 30 + 1 / 2 * s := by
    have := mul_nonneg hS0 (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s / 8)
    nlinarith
  rw [qwU_T_state_diff, abs_mul, abs_of_pos hlo, mul_comm]
  exact mul_le_mul_of_nonneg_right hhi (abs_nonneg _)

/-! ## 4. The stage selector, through Berge -/

theorem qw_sanction_strictConcave (θ : ℝ × ℝ) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (fun s => qwU_S θ.1 θ.2 s) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p₁ p₂ hp₁ hp₂ hsum
  have hp2 : p₂ = 1 - p₁ := by linarith
  subst hp2
  have hsq : 0 < (s₁ - s₂) ^ 2 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hT : 0 < p₁ * (1 - p₁) * (s₁ - s₂) ^ 2 := mul_pos (mul_pos hp₁ (by linarith)) hsq
  have hgap := qwU_S_sanction_gap θ.1 θ.2 s₁ s₂ p₁
  have hP := quarticWeight_nonneg hs₁.1 hs₂.1 hp₁.le (by linarith)
  have := mul_nonneg hT.le hP
  simp only [smul_eq_mul]
  nlinarith

theorem qw_sanction_continuousOn (θ : ℝ × ℝ) :
    ContinuousOn (fun s => qwU_S θ.1 θ.2 s) (Icc (0 : ℝ) 1) := by
  unfold qwU_S; fun_prop

theorem qw_Icc_nonempty : (Icc (0 : ℝ) 1).Nonempty := ⟨0, le_rfl, zero_le_one⟩

/-- **The witness's stage selector**: the unique maximiser of the Sender's
strictly concave stage payoff on `[0,1]`, through Berge; defined as an argmax, not
by a formula (its first-order condition is a cubic in the sanction). -/
def qwσ (x a : ℝ) : ℝ :=
  Foundations.Berge.argmax isCompact_Icc qw_Icc_nonempty qw_sanction_continuousOn
    qw_sanction_strictConcave (x, a)

theorem qwσ_mem (x a : ℝ) : qwσ x a ∈ Icc (0 : ℝ) 1 :=
  Foundations.Berge.argmax_mem isCompact_Icc qw_Icc_nonempty qw_sanction_continuousOn
    qw_sanction_strictConcave (x, a)

theorem qwσ_isMaxOn (x a : ℝ) : IsMaxOn (fun s => qwU_S x a s) (Icc (0 : ℝ) 1) (qwσ x a) :=
  Foundations.Berge.argmax_isMaxOn isCompact_Icc qw_Icc_nonempty qw_sanction_continuousOn
    qw_sanction_strictConcave (x, a)

theorem qwσ_continuous : Continuous (fun xa : ℝ × ℝ => qwσ xa.1 xa.2) := by
  have hjoint : Continuous (fun θa : (ℝ × ℝ) × ℝ => qwU_S θa.1.1 θa.1.2 θa.2) := by
    unfold qwU_S; fun_prop
  exact Foundations.Berge.argmax_continuous isCompact_Icc qw_Icc_nonempty
    qw_sanction_continuousOn qw_sanction_strictConcave hjoint

/-! ## 5. The members -/

/-- The witness's `Params` at a Target discount `β_T ∈ (0,1)`. -/
def qwParams (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := βT
  β_T_mem := ⟨h0.le, h1⟩
  β_S := 1 / 2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := qwU_T
  U_S := qwU_S
  σ := qwσ
  σ_mem := qwσ_mem
  σ_isMaxOn_U_S := qwσ_isMaxOn
  U_T_continuous := qwU_T_continuous
  U_S_continuous := qwU_S_continuous
  F := quadDiagF
  F_continuous := quadDiagF_continuous
  F_mono_x := quadDiagF_mono_x
  F_mono_s := quadDiagF_mono_s
  F_diag := quadDiagF_diag

/-- **`qwParams` has a continuous static Sender selector.** A concrete member with the
non-affine transition `quadDiagF`; the selector itself does not read the transition. The
proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance qwParams_staticSelectorContinuous (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwParams βT h0 h1).StaticSelectorContinuous where
  σ_continuous := qwσ_continuous

/-- **The witness as a chord economy** (enriched), at a Target discount
`β_T ∈ (0,1)`. -/
def qwChordCs (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) : ChordEconomyCs where
  toParams := qwParams βT h0 h1
  σ_continuous := qwσ_continuous
  glo := 2 / 5
  ghi := 3 / 5
  dlo := 2 / 5
  dhi := 3 / 5
  Mx := 1 / 5
  Mm := 0
  Ms := 0
  hbandAll := quadDiagF_bandAll
  hSlo := quadDiagF_lo
  hShi := quadDiagF_hi
  hFjsc := quadDiagF_jsc
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  hMx0 := by norm_num
  hMm0 := by norm_num
  hMs0 := by norm_num
  Mcx := 0
  hMcx0 := le_rfl
  hFcx := quadDiagF_cx
  Mmix := 0
  hFmix := quadDiagF_mix
  hβS0 := by change (0 : ℝ) < 1 / 2; norm_num
  hβT0 := h0
  wlo := 4 / 5
  whi := 31 / 20
  q := 3
  Qbar := 9 / 2
  σx := 1 / 20
  τx := 1 / 5
  rlo := 1 / 2
  rhi := 3 / 4
  klo := 3
  khi := 7 / 2
  uhi := 13 / 8
  ulo := 1
  hUS_stateLip := qw_US_stateLip
  hUS_stateSlope := qw_US_stateSlope
  hUS_concave := qw_US_concave
  hUS_convex := qw_US_convex
  hUS_joint := qw_US_joint
  hUS_stateConvex := qw_US_stateConvex
  hUS_crossLo := qw_US_crossLo
  hUS_crossHi := qw_US_crossHi
  hUS_placLo := qw_US_placLo
  hUS_placHi := qw_US_placHi
  hUS_appetite := qw_US_appetite
  hUS_floor := qw_US_floor
  hwlo := by norm_num
  hσx0 := by norm_num
  hτx0 := by norm_num
  hrlo := by norm_num
  hklo := by norm_num
  hulo := by norm_num
  ℓlo := 1
  ℓhi := 5 / 4
  c := 9 / 2
  plo := 27 / 8
  vlo := 28
  nlo := 3 / 4
  vhi := 30
  nhi := 1 / 2
  hUT_costLo := qw_UT_costLo
  hUT_costHi := qw_UT_costHi
  hUT_painHi := qw_UT_painHi
  hUT_painLo := qw_UT_painLo
  hUT_stateLo := qw_UT_stateLo
  hUT_stateHi := qw_UT_stateHi
  hℓlo := by norm_num
  hplo := by norm_num
  hvlo := by norm_num
  hnlo := by norm_num
  SigV := 1
  hCurv := by
    change (1 / 2 : ℝ) * (1 * (3 / 5) ^ 2 + chKS (1 / 2) (3 / 5) (31 / 20) * 0) < 3
    norm_num [chKS]
  hSigV := by
    change chSigImg (1 / 2) 3 (3 / 4) (1 / 20) 1 (3 / 5) (3 / 5) (chKS (1 / 2) (3 / 5) (31 / 20))
      (1 / 5) 0 0 ≤ 1
    norm_num [chSigImg, chSig, plRho, plMu, chKS]
  Mcs := 1 / 5
  hMcs0 := by norm_num
  hFcs := quadDiagF_cs

/-- **Interiority at the witness** (a hypothesis since round BC; until then a
field): `u_hi + β_S·K_S·d_hi = 13/8 + (1/2)·K_S·(3/5) < 3 = q`. -/
theorem qwChordCs_interior (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).Interior := by
  change (13 / 8 : ℝ) + 1 / 2 * chKS (1 / 2) (3 / 5) (31 / 20) * (3 / 5) < 3
  norm_num [chKS]

/-- **The stage relief margin at the witness** (a hypothesis since round BC):
`ℓ_hi·Q̄ = (5/4)(9/2) < 3·(27/8) = k_lo·p_lo`. -/
theorem qwChordCs_stageRelief (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).StageRelief := by
  change (5 / 4 : ℝ) * (9 / 2) < 3 * (27 / 8)
  norm_num

/-- **The relief member**, `β_T = 1/30`. -/
abbrev qwRelief : ChordEconomyCs := qwChordCs (1 / 30) (by norm_num) (by norm_num)

/-- **The defiance member**, `β_T = 1/2`. -/
abbrev qwDefiance : ChordEconomyCs := qwChordCs (1 / 2) (by norm_num) (by norm_num)

/-! ## 6. Generality (Rule 9B): outside the quadratic–linear family and the affine law -/

/-- **The transition is not the affine law at any rate.** -/
theorem qw_F_ne_affineF (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) (δ : ℝ) :
    (qwChordCs βT h0 h1).F ≠ AbstractGame.affineF δ :=
  quadDiagF_ne_affineF δ

/-- **The Sender's payoff is not quadratic–linear at any coefficients.** -/
theorem qwU_S_ne_symU_S (q u₀ k r w : ℝ) : qwU_S ≠ symU_S q u₀ k r w := by
  intro h
  have h1 := congrFun (congrFun (congrFun h 0) 0) 1
  have h2 := congrFun (congrFun (congrFun h 0) 0) (-1)
  have h3 := congrFun (congrFun (congrFun h 0) 0) 2
  simp only [qwU_S, symU_S] at h1 h2 h3
  norm_num at h1 h2 h3
  linarith

/-- **The Target's payoff is not quadratic–linear at any coefficients.** -/
theorem qwU_T_ne_symU_T (ℓ c n v : ℝ) : qwU_T ≠ symU_T ℓ c n v := by
  intro h
  have h1 := congrFun (congrFun (congrFun h 0) 1) 0
  have h2 := congrFun (congrFun (congrFun h 0) (-1)) 0
  simp only [qwU_T, symU_T] at h1 h2
  norm_num at h1 h2
  linarith

/-- **Ten lower/upper rate pairs are strictly split**: `w`, `q`/`Q̄`, `r`, `k`, `u`,
`ℓ`, `p_lo`/`c`, `v`, `g`, `d`. The envelope slopes `n_lo > n_hi` are not a
lower/upper pair in this sense. -/
theorem qw_pairs_split (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).wlo < (qwChordCs βT h0 h1).whi ∧
    (qwChordCs βT h0 h1).q < (qwChordCs βT h0 h1).Qbar ∧
    (qwChordCs βT h0 h1).rlo < (qwChordCs βT h0 h1).rhi ∧
    (qwChordCs βT h0 h1).klo < (qwChordCs βT h0 h1).khi ∧
    (qwChordCs βT h0 h1).ulo < (qwChordCs βT h0 h1).uhi ∧
    (qwChordCs βT h0 h1).ℓlo < (qwChordCs βT h0 h1).ℓhi ∧
    (qwChordCs βT h0 h1).plo < (qwChordCs βT h0 h1).c ∧
    (qwChordCs βT h0 h1).vlo < (qwChordCs βT h0 h1).vhi ∧
    (qwChordCs βT h0 h1).glo < (qwChordCs βT h0 h1).ghi ∧
    (qwChordCs βT h0 h1).dlo < (qwChordCs βT h0 h1).dhi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [qwChordCs]

/-! ## 7. The constants -/

theorem qw_neutral (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).ZeroSanctionNeutral := by
  intro x _ a _
  change qwU_S x a 0 = qwU_S x 0 0
  unfold qwU_S
  ring

theorem qw_KS (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) : (qwChordCs βT h0 h1).KS = 31 / 14 := by
  change chKS (1 / 2) (3 / 5) (31 / 20) = 31 / 14
  norm_num [chKS]

theorem qw_SigC (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) : (qwChordCs βT h0 h1).SigC = 10 / 41 := by
  change chSigC (1 / 2) (1 / 5) (qwChordCs βT h0 h1).KS 0 (3 / 5) = 10 / 41
  rw [qw_KS]
  norm_num [chSigC]

theorem qw_mu (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) : (qwChordCs βT h0 h1).mu = 141 / 50 := by
  change plMu (1 / 2) 3 1 (3 / 5) (qwChordCs βT h0 h1).KS 0 = 141 / 50
  rw [qw_KS]
  norm_num [plMu]

theorem qw_Lresp (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).Lresp = 93 / 100 := by
  change ChordEconomy.plLresp (3 / 4) (1 / 2) (max 1 (qwChordCs βT h0 h1).SigC) (3 / 5) (3 / 5)
    (qwChordCs βT h0 h1).KS 0 = 93 / 100
  rw [qw_SigC, qw_KS, max_eq_left (by norm_num : (10 / 41 : ℝ) ≤ 1)]
  norm_num [ChordEconomy.plLresp]

theorem qw_Mtot (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).Mtot = 27353 / 5740 := by
  change 9 / 2 + 1 / 2 * ((qwChordCs βT h0 h1).SigC * (3 / 5) ^ 2
    + (qwChordCs βT h0 h1).KS * (1 / 5)) = 27353 / 5740
  rw [qw_SigC, qw_KS]
  norm_num

theorem qw_LloopSharp (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).LloopSharp = 3 / 5 + 3 / 5 * (93 / 100 / (141 / 50)) := by
  change 3 / 5 + 3 / 5 * ((qwChordCs βT h0 h1).Lresp / (qwChordCs βT h0 h1).mu) = _
  rw [qw_Lresp, qw_mu]

theorem qw_placable (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) : (qwChordCs βT h0 h1).Placable := by
  change 13 / 8 + 1 / 2 * (qwChordCs βT h0 h1).KS * (3 / 5) ≤ 3
  rw [qw_KS]
  norm_num

/-- `β_T·γ_T < 1` for every `β_T < 1`. -/
theorem qw_γ (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).β_T * (qwChordCs βT h0 h1).LloopSharp < 1 := by
  rw [qw_LloopSharp]
  change βT * (3 / 5 + 3 / 5 * (93 / 100 / (141 / 50))) < 1
  have hc0 : (0 : ℝ) < 3 / 5 + 3 / 5 * (93 / 100 / (141 / 50)) := by norm_num
  have hc1 : (3 / 5 : ℝ) + 3 / 5 * (93 / 100 / (141 / 50)) < 1 := by norm_num
  have := mul_lt_mul_of_pos_right h1 hc0
  linarith

/-- The sharp relief margin `ℓ_hi·M_tot < k_lo·p_lo`, at every `β_T`. -/
theorem qw_reliefSharp (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).ℓhi * (qwChordCs βT h0 h1).Mtot
      < (qwChordCs βT h0 h1).klo * (qwChordCs βT h0 h1).plo := by
  rw [qw_Mtot]
  norm_num [qwChordCs]

/-- The rally margin, at every `β_T`. -/
theorem qw_rallyMargin (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).β_S * ((qwChordCs βT h0 h1).SigC * (qwChordCs βT h0 h1).ghi
        * (qwChordCs βT h0 h1).dhi
      + ((qwChordCs βT h0 h1).KS + 2 * (qwChordCs βT h0 h1).SigC) * (qwChordCs βT h0 h1).Mmix)
      ≤ (qwChordCs βT h0 h1).rlo := by
  rw [qw_SigC, qw_KS]
  norm_num [qwChordCs, qwParams]

/-! ## 8. The relief member (`β_T = 1/30`) -/

theorem qwRelief_KTrel : qwRelief.KTrel = (30 + 5 / 4 * (27353 / 5740 * (93 / 100) / (3 * (141 /
    50))))
    / (1 - 1 / 30 * (3 / 5)) := by
  change (30 + 5 / 4 * qwRelief.Lalpha) / (1 - 1 / 30 * (3 / 5)) = _
  change (30 + 5 / 4 * (qwRelief.Mtot * qwRelief.Lresp / (3 * qwRelief.mu)))
    / (1 - 1 / 30 * (3 / 5)) = _
  rw [qw_Mtot, qw_Lresp, qw_mu]

theorem qwRelief_KT : qwRelief.KT = (max 30 (30 + 1 / 2) + 9 / 2 * (93 / 100 / (141 / 50)))
    / (1 - 1 / 30 * (3 / 5 + 3 / 5 * (93 / 100 / (141 / 50)))) := by
  change (max 30 (30 + 1 / 2) + 9 / 2 * (qwRelief.Lresp / qwRelief.mu))
    / (1 - 1 / 30 * qwRelief.LloopSharp) = _
  rw [qw_Lresp, qw_mu, qw_LloopSharp]

/-- The relief side, existence form (`K_T^rel`), at `β_T = 1/30`. -/
theorem qwRelief_relief_exists :
    qwRelief.ℓhi * qwRelief.Mtot
      < qwRelief.klo * (qwRelief.plo - qwRelief.β_T * qwRelief.dhi * qwRelief.KTrel) := by
  rw [qwRelief_KTrel, qw_Mtot]
  norm_num [qwChordCs, qwParams]

/-- The relief side, defiance-refutation form (`K_T`), at `β_T = 1/30`. -/
theorem qwRelief_relief_notdef :
    qwRelief.ℓhi * qwRelief.Mtot
      < qwRelief.klo * (qwRelief.plo - qwRelief.β_T * qwRelief.dhi * qwRelief.KT) := by
  rw [qwRelief_KT, qw_Mtot]
  norm_num [qwChordCs, qwParams]

/-- **The relief equilibrium off the quadratic–linear family and the affine
law.** -/
noncomputable def qwRelief_reliefEquilibrium : qwRelief.toParams.FeedbackStackelbergEquilibriumTop
    :=
  qwRelief.reliefEquilibriumTop (qwChordCs_interior _ _ _) (qw_placable _ _ _)
      qwRelief_relief_exists (qw_neutral _ _ _)

theorem qwRelief_rule_zero :
    ∀ x ∈ Sanctions.I,
      qwRelief.toParams.dynamicEquilibriumRule qwRelief_reliefEquilibrium x = 0 :=
  fun _ hx => qwRelief.reliefEquilibriumTop_rule_eq_zero (qwChordCs_interior _ _ _) (qw_placable _
      _ _)
    qwRelief_relief_exists (qw_neutral _ _ _) hx

/-- **Uniqueness on the relief side at the witness**: the relief equilibrium is
the only equilibrium whose Sender value lies in the carrier class. -/
theorem qwRelief_unique_in_carrier_class :
    qwRelief_reliefEquilibrium.V_S ∈ qwRelief.carrierS2 ∧
    ∀ Eq : qwRelief.toParams.FeedbackStackelbergEquilibriumTop, Eq.V_S ∈ qwRelief.carrierS2 →
      (∀ x ∈ Sanctions.I, Eq.α x = qwRelief_reliefEquilibrium.α x) ∧
      Eq.V_S = qwRelief_reliefEquilibrium.V_S ∧ Eq.V_T = qwRelief_reliefEquilibrium.V_T :=
  qwRelief.reliefEquilibriumTop_unique_in_carrier_class (qwChordCs_interior _ _ _) (qw_placable _ _
      _) (qw_γ _ _ _)
    qwRelief_relief_exists qwRelief_relief_notdef (qw_neutral _ _ _)

/-! ## 9. The defiance member (`β_T = 1/2`) -/

/-- The loss-offset margin at `β_T = 1/2`: `c = 9/2 ≤ β_T d_lo g_T`, since
`g_T ≥ v_lo/(1 − β_T g_lo) = 35`. -/
theorem qwDefiance_lossOffset : qwDefiance.LossOffset := by
  have hs : 0 ≤ qwDefiance.sfloor := (qwDefiance.σ_mem 0 0).1
  change (9 / 2 : ℝ) ≤ 1 / 2 * (2 / 5) * ((28 + 3 / 4 * qwDefiance.sfloor) / (1 - 1 / 2 * (2 / 5)))
  have e : (1 / 2 : ℝ) * (2 / 5) * ((28 + 3 / 4 * qwDefiance.sfloor) / (1 - 1 / 2 * (2 / 5)))
      = 7 + 3 / 16 * qwDefiance.sfloor := by ring
  rw [e]
  linarith

/-- **The four cells off the quadratic–linear family and the affine law** (the
paper's Theorem 1 at the witness): the state washes out under the readings in
which the Target does not look ahead, converges to a positive fixed point of
the stage rule when only the Target does, and to a strictly higher state when
both do. -/
theorem qwDefiance_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((qwDefiance.myopicPath (qwChordCs_interior _ _ _)
        (qwChordCs_stageRelief _ _ _) (qw_placable _ _ _)) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((qwDefiance.senderOnlyPath' (qwChordCs_interior _ _ _)
        (qw_placable _ _ _))
      (qw_reliefSharp _ _ _) (qw_neutral _ _ _) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, qwDefiance.σ z₁₀ 0 = z₁₀ ∧
      qwDefiance.responsePath qwDefiance.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto ((qwDefiance.targetOnlyPath qwDefiance_lossOffset) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((qwDefiance.dynamicPath qwDefiance_lossOffset) (qw_rallyMargin _ _ _) x₀)
        atTop (𝓝 z)) :=
  qwDefiance.four_cell_generalF' (qwChordCs_interior _ _ _)
      qwDefiance_lossOffset (qw_placable _ _ _) (qw_rallyMargin _ _ _)
    (qw_reliefSharp _ _ _) (qw_neutral _ _ _)

/-- **Both continuation channels are active at the constructed equilibrium**
off the quadratic–linear family and the affine law (through the relief margin,
with no stage flip). -/
theorem qwDefiance_both_channels :
    ∀ x ∈ Sanctions.I,
      qwDefiance.toParams.ContinuationChangesSenderChoiceAt
          (qwDefiance.equilibriumTop_of_margin qwDefiance_lossOffset (qw_rallyMargin _ _ _)).V_S x
          ((qwDefiance.equilibriumTop_of_margin qwDefiance_lossOffset (qw_rallyMargin _ _ _)).α x)
        ∧ qwDefiance.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => qwDefiance.response
            (qwDefiance.equilibriumTop_of_margin qwDefiance_lossOffset (qw_rallyMargin _ _ _)).V_S y
                b)
          (qwDefiance.equilibriumTop_of_margin qwDefiance_lossOffset (qw_rallyMargin _ _ _)).V_T x
              :=
  qwDefiance.both_channels_active_of_relief (qwChordCs_interior _ _ _) qwDefiance_lossOffset
      (qw_rallyMargin _ _ _)
    (qw_reliefSharp _ _ _)

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.qwChordCs
#print axioms Sanctions.Examples.qw_pairs_split
#print axioms Sanctions.Examples.qwU_S_ne_symU_S
#print axioms Sanctions.Examples.qwU_T_ne_symU_T
#print axioms Sanctions.Examples.qwRelief_unique_in_carrier_class
#print axioms Sanctions.Examples.qwDefiance_four_cells
#print axioms Sanctions.Examples.qwDefiance_both_channels

end Examples
end Sanctions
