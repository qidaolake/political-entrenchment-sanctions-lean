import Sanctions.Examples.CoupledRoute.LowDeltaStaticStackelberg
import Sanctions.Foundations.TiltStability

/-!
# Exact perturbation bounds around the low-delta static Stackelberg policy

This file supplies the quantitative bridge from the exact static reference to
the forward-looking Sender problem.  It uses only the already-defined
low-delta economy.  In particular, no numerical fixed point and no additional
model assumption enter any statement.
-/

namespace Sanctions
namespace Examples

open Set
open Sanctions.AbstractGame

/-! ## Static Sender growth -/

/-- The clipped static Sender response has a global quadratic-growth modulus
`3/5` on the feasible sanction interval.  At a boundary response the objective
gap is weakly larger than the interior parabola gap. -/
theorem lowDeltaStaticSenderPolicy_quadraticGrowth
    {x a s : ℝ} (hs : s ∈ Sanctions.I) :
    (3 / 5 : ℝ) * (s - mwσ x a) ^ 2 ≤
      mwU_S x a (mwσ x a) - mwU_S x a s := by
  rcases hs with ⟨hs0, hs1⟩
  let t : ℝ := lowDeltaSenderInteriorVertex 0 x a
  have htdef :
      t = (9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a := by
    simp [t, lowDeltaSenderInteriorVertex]
  by_cases ht0 : t ≤ 0
  · have hσ : mwσ x a = 0 := by
      unfold mwσ
      rw [min_eq_right (by rw [← htdef]; linarith),
        max_eq_left (by rwa [← htdef])]
    rw [hσ]
    unfold mwU_S
    rw [htdef] at ht0
    nlinarith [mul_nonneg hs0 (by
      linarith :
        0 ≤ s -
          ((9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a))]
  · have ht0' : 0 ≤ t := le_of_not_ge ht0
    by_cases ht1 : 1 ≤ t
    · have hσ : mwσ x a = 1 := by
        unfold mwσ
        rw [min_eq_left (by rwa [← htdef]),
          max_eq_right (by norm_num)]
      rw [hσ]
      unfold mwU_S
      rw [htdef] at ht1
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - s) (by
        linarith :
          0 ≤
            ((9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a) - s)]
    · have ht1' : t ≤ 1 := le_of_not_ge ht1
      have hσ : mwσ x a = t := by
        unfold mwσ
        rw [← htdef, min_eq_right ht1', max_eq_right ht0']
      rw [hσ]
      unfold mwU_S
      rw [htdef]
      nlinarith [sq_nonneg
        (s - ((9 / 8 : ℝ) * x - 1 / 12 - (5 / 12) * a))]

/-! ## Target localization modulo an action-independent constant -/

/-- Target localization is unchanged if the comparison objective contains an
action-independent constant.  This is the useful form when comparing a dynamic
objective to a frozen-state continuation baseline. -/
theorem lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation_add
    {f : ℝ → ℝ} {x a ε c : ℝ}
    (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn f Sanctions.I a)
    (hclose :
      ∀ z ∈ Sanctions.I,
        |f z - (lowDeltaStaticTargetObjective x z + c)| ≤ ε) :
    (a - lowDeltaStaticTargetPolicy x) ^ 2 ≤ 2 * ε := by
  have hαmem := lowDeltaStaticTargetPolicy_mem hx
  have hopt :=
    (isMaxOn_iff.mp hmax) (lowDeltaStaticTargetPolicy x) hαmem
  have hgap := lowDeltaStaticTargetPolicy_quadraticGrowth hx ha
  have hcloseα := abs_le.mp
    (hclose (lowDeltaStaticTargetPolicy x) hαmem)
  have hclosea := abs_le.mp (hclose a ha)
  linarith

/-- Radius form of
`lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation_add`. -/
theorem lowDeltaStaticTargetPolicy_maximizer_mem_Ioo_of_uniform_perturbation_add
    {f : ℝ → ℝ} {x a ε c r : ℝ}
    (hx : x ∈ Sanctions.S) (ha : a ∈ Sanctions.I)
    (hr : 0 ≤ r)
    (hmax : IsMaxOn f Sanctions.I a)
    (hclose :
      ∀ z ∈ Sanctions.I,
        |f z - (lowDeltaStaticTargetObjective x z + c)| ≤ ε)
    (hsmall : 2 * ε < r ^ 2) :
    a ∈ Set.Ioo
      (lowDeltaStaticTargetPolicy x - r)
      (lowDeltaStaticTargetPolicy x + r) := by
  have hsq :=
    lowDeltaStaticTargetPolicy_maximizer_sq_le_of_uniform_perturbation_add
      hx ha hmax hclose
  constructor <;>
    nlinarith [sq_nonneg (a - lowDeltaStaticTargetPolicy x)]

/-! ## Linear tilts of a quadratic-growth objective -/

/-- **A Lipschitz tilt moves a quadratic-growth maximizer only linearly.**

General (Rule 22): a statement about real functions on a set `A`, with no
transition and no economy.  If `f` falls off quadratically at rate `γ` around
`a₀` on `A`, and `a₁` maximizes the tilted objective `f + h` on `A`, where the
tilt `h` is `L`-Lipschitz on `A`, then `γ·|a₁ − a₀| ≤ L`.  Optimality of `a₁`
gives `f a₀ − f a₁ ≤ h a₁ − h a₀ ≤ L·|a₁ − a₀|`, and growth bounds the left side
below by `γ·|a₁ − a₀|²`.

`TiltStability.sq_displacement_le_of_growth` knows only `|h| ≤ ε` and gets a
square-root bound; a Lipschitz tilt gives a linear one.  The premise `0 ≤ L` is
kept: when `A` is a single point it is not implied (then `a₁ = a₀` and the
conclusion reads `0 ≤ L`). -/
theorem growth_mul_abs_le_of_linear_tilt
    {f h : ℝ → ℝ} {A : Set ℝ} {a₀ a₁ γ L : ℝ}
    (hgrowth : TiltStability.QuadraticGrowthAt f A a₀ γ)
    (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (hL : 0 ≤ L)
    (hlip : ∀ a ∈ A, ∀ b ∈ A, |h a - h b| ≤ L * |a - b|)
    (hmax : IsMaxOn (fun a => f a + h a) A a₁) :
    γ * |a₁ - a₀| ≤ L := by
  have hopt : f a₀ + h a₀ ≤ f a₁ + h a₁ := hmax ha₀
  have hg := hgrowth a₁ ha₁
  have ht : h a₁ - h a₀ ≤ L * |a₁ - a₀| :=
    (le_abs_self _).trans (hlip a₁ ha₁ a₀ ha₀)
  have hkey : γ * |a₁ - a₀| ^ 2 ≤ L * |a₁ - a₀| := by
    rw [sq_abs]
    linarith
  rcases (abs_nonneg (a₁ - a₀)).eq_or_lt with hz | hpos
  · rw [← hz, mul_zero]
    exact hL
  · nlinarith

/-- **Dynamic-versus-static Sender displacement, general in `F`.**

General in `F` (Rule 22): any economy `p`.  The transition enters only through
a sanction chord at the given state `x`, `|F x s − F x s'| ≤ L_F·|s − s'|` for
feasible `s, s'`; no chord on the whole square is asked.  If the static Sender
objective `U_S x a` has quadratic growth at rate `q` around the static response
`σ x a`, and the continuation value `V` is `K`-Lipschitz, then the greatest
dynamic response is displaced from the static one by at most `β_S·K·L_F/q`,
stated in the multiplied form `q·|σ_dyn_top − σ| ≤ β_S·K·L_F`.

The continuation term `β_S·V(clip(F x s))` is a tilt of the static objective
with Lipschitz modulus `β_S·K·L_F` (clipping is nonexpansive), so this is
`growth_mul_abs_le_of_linear_tilt`.  No nonnegativity premise is assumed:
`0 ≤ K` follows from the Lipschitz bound, and `0 ≤ L_F` from the chord at the
sanctions `0` and `1`. -/
theorem σ_dyn_top_abs_sub_le_of_quadraticGrowth
    (p : Params) (V : SBCF) {K L_F q : ℝ}
    (hV : Params.ValueLipschitzWith V K) (x a : ℝ)
    (hchord : ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I,
      |p.F x s - p.F x s'| ≤ L_F * |s - s'|)
    (hgrowth :
      TiltStability.QuadraticGrowthAt (p.U_S x a) Sanctions.I (p.σ x a) q) :
    q * |p.σ_dyn_top V x a - p.σ x a| ≤ p.β_S * K * L_F := by
  have hK : 0 ≤ K := hV.nonneg
  have hβ : 0 ≤ p.β_S := p.β_S_mem.1
  have hLF : 0 ≤ L_F := by
    have h01 := hchord 0 (by simp [Sanctions.I]) 1 (by simp [Sanctions.I])
    norm_num at h01
    exact (abs_nonneg _).trans h01
  refine growth_mul_abs_le_of_linear_tilt
    (h := fun s => p.β_S * V (Sanctions.clipS' (p.F x s)))
    hgrowth (p.σ_mem x a) (p.σ_dyn_top_mem_I V x a)
    (mul_nonneg (mul_nonneg hβ hK) hLF) ?_ (p.σ_dyn_top_isMaxOn V x a)
  intro s hs s' hs'
  change |p.β_S * V (Sanctions.clipS' (p.F x s))
      - p.β_S * V (Sanctions.clipS' (p.F x s'))|
    ≤ p.β_S * K * L_F * |s - s'|
  calc
    |p.β_S * V (Sanctions.clipS' (p.F x s))
        - p.β_S * V (Sanctions.clipS' (p.F x s'))|
        = p.β_S * |V (Sanctions.clipS' (p.F x s))
            - V (Sanctions.clipS' (p.F x s'))| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hβ]
    _ ≤ p.β_S * (K * dist (Sanctions.clipS' (p.F x s'))
          (Sanctions.clipS' (p.F x s))) :=
        mul_le_mul_of_nonneg_left (hV _ _) hβ
    _ ≤ p.β_S * (K * |p.F x s' - p.F x s|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Sanctions.clipS'_lipschitz_dist _ _) hK) hβ
    _ ≤ p.β_S * (K * (L_F * |s' - s|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hchord s' hs' s hs) hK) hβ
    _ = p.β_S * K * L_F * |s - s'| := by
        rw [abs_sub_comm s' s]
        ring

/-! ## Forward-looking Sender localization -/

/-- Any greatest dynamic Sender response to a `K`-Lipschitz continuation value
lies within `K/120` of the exact static response.  The constant is exact for
the existing primitives:

* static quadratic growth `3/5`;
* Sender discount `1/2`;
* transition action slope `1/100`;
* nonexpansiveness of state clipping.

The result is deterministic and contains no numerical convergence premise.
Witness-specific (Rule 22): the instance of the general-`F`
`σ_dyn_top_abs_sub_le_of_quadraticGrowth` at `q = 3/5`, `L_F = 1/100`,
`β_S = 1/2`, so that `β_S·K·L_F/q = K/120`.  The former premise `0 ≤ K` is
dropped: it follows from the Lipschitz bound. -/
theorem lowDelta_sigmaDynTop_abs_sub_staticSender_le
    (V : SBCF) {K : ℝ}
    (hV : Sanctions.AbstractGame.Params.ValueLipschitzWith V K)
    (x a : ℝ) :
    |lowDeltaParams.σ_dyn_top V x a - mwσ x a| ≤ K / 120 := by
  have hchord : ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I,
      |lowDeltaParams.F x s - lowDeltaParams.F x s'|
        ≤ (1 / 100) * |s - s'| := by
    intro s _ s' _
    have heq : lowDeltaParams.F x s - lowDeltaParams.F x s'
        = (1 / 100) * (s - s') := by
      simp only [lowDeltaParams_F, AbstractGame.affineF]
      ring
    rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  have h := σ_dyn_top_abs_sub_le_of_quadraticGrowth lowDeltaParams V hV x a
    hchord (q := 3 / 5)
    (fun s hs => lowDeltaStaticSenderPolicy_quadraticGrowth (x := x) (a := a) hs)
  have h' : (3 / 5 : ℝ) * |lowDeltaParams.σ_dyn_top V x a - mwσ x a|
      ≤ 1 / 2 * K * (1 / 100) := h
  linarith

end Examples
end Sanctions
