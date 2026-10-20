/-
Sanctions/Examples/BaselineTwoSidedOrderingUndetermined.lean

**The baseline does not determine the two-sided Target-policy order: an actual
dynamic game in which the ordering REVERSES (Rule-11 refutation).**

`SenderSwitchSignUndetermined.lean` refutes the sign of the Sender-switch channel
at the level of abstract objectives. That is a statement about what a list of
hypotheses entails; it exhibits no game. This file closes the gap with a real
economy carrying real equilibria, in which

    alpha^MM(x) = 0  <  1 = alpha^FF(x)   at every feasible state,

so the *forward-looking* Target complies **strictly more** than the myopic one —
the exact reverse of the paper's intended Target-reluctance ordering.

## Why the mechanism is the transition's curvature

`Foundations/ArgmaxSensitivity.lean` proves the general fact this witness
instantiates (`argmax_shift_le_of_concaveOn`): when a maximizer is centred on a
translating loss and perturbed by a *concave* term, it moves by **at most** the
shift, so the gap between it and the centre does not shrink. For the Sender, the
centre is the static response, the perturbation is the discounted continuation
`beta_S * V_S (F x .)`, and the gap is what the switch channel reads.

So the widening gap here comes from `F` being **strictly concave in the
sanction** — not from any curvature in `V_S`, which is deliberately *linear*
(`V_S y = 2y`). The Sender's value has no curvature to blame. That is the point:
the adverse channel is produced by the transition alone.

The transition is

    F(x,s) = x + (s - x)/2 - (1/8)(s - x)^2

(clipped in the squared term only, so the `Params` monotonicity fields, which are
global on `R`, hold while `F(x,x) = x` stays exact). It is **non-affine at every
`delta`** — every `affineF delta` has vanishing second derivative in `s`, and
this one has `-1/4` — and it has **genuine inheritance**, `dF/dx >= 1/4 > 0`,
unlike the no-inheritance corner `F(x,s) = s` where the gap would be constant.

## What the witness verifies

At `alpha^FF = 1` both Bellman equations hold exactly, the Sender's static and
forward-looking responses are interior to `[0,1]` at every feasible state, both
responses strictly fall in compliance, the forward-looking one is the harder, and
the response gap `d - m = 1/6 + a/18 + x/9` strictly **widens** in compliance.
The channel accounting then shows the Target-continuation channel is favourable
and the Sender-switch channel is adverse and larger.

## What it licenses, and what it does not

It licenses exactly one claim (Rule 9A):

> the baseline primitives, together with several natural monotonicity and
> optimality properties, do not logically determine the two-sided Target-policy
> order.

It does **not** say the intended ordering typically fails, or that it fails in
calibrated sanctions economies, or anything about genericity. It is a scope
delimiter that makes the cross-response condition of
`Theory/LockIn/TwoSidedForwardLooking.lean` a *logically required* addition
rather than a convenience.

## Two honest caveats

The `x`-dependent shifts in the two stage payoffs (`ntShiftS`, `ntShiftT`) are
**reverse-engineered**: they are chosen so the proposed value functions solve the
Bellman equations exactly. That is standard for a witness and it is how the
economy is built, but they carry no independent economic motivation and are not
presented as if they did.

The properties checked below are **equilibrium-level**, not the carrier-quantified
forms of the paper's A1/A2. No claim is made that this economy satisfies those.

Rule 9C: every constant was located and verified in exact rational arithmetic
before any Lean was written --- see
`docs/archive/workflow-scratch/negative_test_concaveF.py` and its recorded output.
-/

import Sanctions.Examples.WitnessKit
import Sanctions.Theory.LockIn.TwoSidedForwardLooking
import Mathlib.Tactic

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction

/-! ## 1. The transition: strictly concave in the sanction, non-affine, with
inheritance -/

/-- `F(x,s) = x + (s-x)/2 - (1/8)(s-x)^2`, with the squared term read through the
clip so the global `Params` monotonicity fields hold. On the unit square the
clips are the identity and this is the plain quadratic. -/
noncomputable def ntF (x s : ℝ) : ℝ :=
  x + (s - x) / 2 - (1 / 8) * (Sanctions.clipS s - Sanctions.clipS x) ^ 2

/-- The clip is inert on the feasible interval. -/
theorem ntClipS_eq {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1) : Sanctions.clipS y = y := by
  obtain ⟨h0, h1⟩ := hy
  simp only [Sanctions.clipS]
  rw [min_eq_right h1, max_eq_right h0]

/-- On the feasible square the clips collapse. -/
theorem ntF_of_mem {x s : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ntF x s = x + (s - x) / 2 - (1 / 8) * (s - x) ^ 2 := by
  unfold ntF
  rw [ntClipS_eq hs, ntClipS_eq hx]

/-- `F(x,x) = x`: the bump vanishes on the diagonal identically, clipped or
not. -/
theorem ntF_diag : ∀ x : ℝ, ntF x x = x := by
  intro x; unfold ntF; ring

theorem ntF_mem : ∀ x s : ℝ, x ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 →
    ntF x s ∈ Set.Icc (0:ℝ) 1 := by
  intro x s hx hs
  rw [ntF_of_mem hx hs]
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hs0, hs1⟩ := hs
  constructor <;> nlinarith [sq_nonneg (s - x), sq_nonneg (s + x), sq_nonneg (1 - s)]

theorem ntF_continuous : Continuous (fun xs : ℝ × ℝ => ntF xs.1 xs.2) := by
  unfold ntF
  have hc2 : Continuous (fun xs : ℝ × ℝ => Sanctions.clipS xs.2) :=
    Sanctions.clipS_continuous.comp continuous_snd
  have hc1 : Continuous (fun xs : ℝ × ℝ => Sanctions.clipS xs.1) :=
    Sanctions.clipS_continuous.comp continuous_fst
  exact (continuous_fst.add ((continuous_snd.sub continuous_fst).div_const 2)).sub
    (((hc2.sub hc1).pow 2).const_mul (1 / 8))

theorem ntF_mono_s : ∀ x : ℝ, Monotone (fun s => ntF x s) := by
  intro x s₁ s₂ hle
  unfold ntF
  set c₁ := Sanctions.clipS s₁ with hc₁
  set c₂ := Sanctions.clipS s₂ with hc₂
  set cx := Sanctions.clipS x with hcx
  have h1 := Sanctions.clipS_mem s₁
  have h2 := Sanctions.clipS_mem s₂
  have hxm := Sanctions.clipS_mem x
  have hord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hlip : c₂ - c₁ ≤ s₂ - s₁ := by
    have h := Sanctions.clipS_lipschitz_abs s₂ s₁
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ s₂ - s₁)] at h
    linarith
  simp only
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨hxa, hxb⟩ := hxm
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁)
    (by linarith : (0:ℝ) ≤ 2 - (c₂ + c₁ - 2 * cx))]

theorem ntF_mono_x : ∀ s : ℝ, Monotone (fun x => ntF x s) := by
  intro s x₁ x₂ hle
  unfold ntF
  set cs := Sanctions.clipS s with hcs
  set c₁ := Sanctions.clipS x₁ with hc₁
  set c₂ := Sanctions.clipS x₂ with hc₂
  have hsm := Sanctions.clipS_mem s
  have h1 := Sanctions.clipS_mem x₁
  have h2 := Sanctions.clipS_mem x₂
  have hord : c₁ ≤ c₂ := Sanctions.clipS_mono hle
  have hlip : c₂ - c₁ ≤ x₂ - x₁ := by
    have h := Sanctions.clipS_lipschitz_abs x₂ x₁
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ x₂ - x₁)] at h
    linarith
  simp only
  obtain ⟨hsa, hsb⟩ := hsm
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c₂ - c₁)
    (by linarith : (0:ℝ) ≤ 2 - (2 * cs - c₁ - c₂))]

/-- **The transition is strictly concave in the sanction on the feasible square**
--- the curvature that drives the widening response gap, and simultaneously an
outright proof that it is not `affineF delta` for any `delta`, since every affine
law has vanishing second difference. -/
theorem ntF_strictConcave_chord {x s₁ s₂ : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hs₁ : s₁ ∈ Set.Icc (0:ℝ) 1) (hs₂ : s₂ ∈ Set.Icc (0:ℝ) 1)
    (hne : s₁ ≠ s₂) (hmid : (s₁ + s₂) / 2 ∈ Set.Icc (0:ℝ) 1) :
    ntF x s₁ / 2 + ntF x s₂ / 2 < ntF x ((s₁ + s₂) / 2) := by
  rw [ntF_of_mem hx hs₁, ntF_of_mem hx hs₂, ntF_of_mem hx hmid]
  have hne' : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < (s₁ - s₂) ^ 2 := by
    rcases lt_or_gt_of_ne hne' with h | h <;> nlinarith
  nlinarith [hpos]

/-! ## 2. The static Sender response, and the two stage payoffs -/

/-- The Sender's stage bliss point: `m(a) = (1-a)/2`, strictly falling in
compliance. -/
noncomputable def ntIdeal (a : ℝ) : ℝ := (1 - a) / 2

/-- The static Sender response, the bliss point clipped into `[0,1]`. On the
feasible action range the clip is inert. -/
noncomputable def ntSigma (_x a : ℝ) : ℝ := Sanctions.clipS (ntIdeal a)

theorem ntIdeal_mem {a : ℝ} (ha : a ∈ Sanctions.I) : ntIdeal a ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ha
  constructor <;> · unfold ntIdeal; linarith

theorem ntSigma_of_mem {x a : ℝ} (ha : a ∈ Sanctions.I) : ntSigma x a = ntIdeal a := by
  unfold ntSigma
  exact ntClipS_eq (ntIdeal_mem ha)

/-- The reverse-engineered state shift in the Sender's stage payoff. Chosen so
`V_S y = 2y` solves the Sender Bellman equation exactly along `alpha = 1`; it
carries no independent economic content. -/
noncomputable def ntShiftS (x : ℝ) : ℝ := x ^ 2 / 9 + 13 * x / 9 - 1 / 18

/-- The reverse-engineered state shift in the Target's stage payoff, chosen so
`V_T y = y/8` solves the Target Bellman equation exactly along `alpha = 1`. -/
noncomputable def ntShiftT (x : ℝ) : ℝ :=
  x ^ 2 / 162 - 31 * x / 1296 - 1841 / 2592

/-- Sender stage payoff: a strictly concave loss around the bliss point, plus a
state shift. -/
noncomputable def ntU_S (x a s : ℝ) : ℝ := -(s - ntIdeal a) ^ 2 + ntShiftS x

/-- Target stage payoff: linear in compliance and in the sanction, plus a state
shift. The Target likes the sanction (coefficient `1`) and likes complying
(coefficient `13/27`). -/
noncomputable def ntU_T (x a s : ℝ) : ℝ := (13 / 27) * a + s + ntShiftT x

theorem ntSigma_mem (x a : ℝ) : ntSigma x a ∈ Set.Icc (0:ℝ) 1 :=
  Sanctions.clipS_mem _

theorem ntSigma_continuous : Continuous (fun xa : ℝ × ℝ => ntSigma xa.1 xa.2) := by
  unfold ntSigma ntIdeal
  exact Sanctions.clipS_continuous.comp (by fun_prop)

theorem ntSigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => ntU_S x a s) Sanctions.I (ntSigma x a) := by
  refine WitnessKit.clipVertex_isMaxOn (k := (1:ℝ)) (C := ntShiftS x) (t := ntIdeal a)
    (U := fun s => ntU_S x a s) (by norm_num) ?_
  intro s
  unfold ntU_S
  ring

theorem ntU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => ntU_S xas.1 xas.2.1 xas.2.2) := by
  unfold ntU_S ntIdeal ntShiftS
  fun_prop

theorem ntU_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => ntU_T xas.1 xas.2.1 xas.2.2) := by
  unfold ntU_T ntShiftT
  fun_prop

/-! ## 3. The economy

`delta` is supplied because `Params` requires it; nothing below reads it, and the
transition is not affine, so it is inert here (Rule 22). -/

/-- The negative-test economy. -/
noncomputable def ntParams : AbstractGame.Params where
  δ := 1 / 2
  δ_mem := by constructor <;> norm_num
  β_T := 1 / 2
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := ntU_T
  U_S := ntU_S
  σ := ntSigma
  σ_mem := ntSigma_mem
  σ_isMaxOn_U_S := ntSigma_isMaxOn
  U_T_continuous := ntU_T_continuous
  U_S_continuous := ntU_S_continuous
  F := ntF
  F_continuous := ntF_continuous
  F_mono_x := ntF_mono_x
  F_mono_s := ntF_mono_s
  F_diag := ntF_diag

/-- **`ntParams` has a continuous static Sender selector.** A concrete member with the
non-affine transition `ntF`; the selector itself does not read the transition. The proof
is the one that was the economy's `σ_continuous` field until round BJ5.1 (2026-10-07),
when the condition left `Params` for the class `Params.StaticSelectorContinuous`; the
myopic-comparator and static-Sender results can use it at this economy. -/
instance ntParams_staticSelectorContinuous :
    ntParams.StaticSelectorContinuous where
  σ_continuous := ntSigma_continuous

@[simp] theorem ntParams_β_S : ntParams.β_S = 1 / 2 := rfl
@[simp] theorem ntParams_β_T : ntParams.β_T = 1 / 2 := rfl
@[simp] theorem ntParams_F : ntParams.F = ntF := rfl
@[simp] theorem ntParams_σ : ntParams.σ = ntSigma := rfl
@[simp] theorem ntParams_U_S : ntParams.U_S = ntU_S := rfl
@[simp] theorem ntParams_U_T : ntParams.U_T = ntU_T := rfl


/-! ## 4. Values, and the forward-looking Sender response

Both value functions are **linear** — `V_S y = 2y`, `V_T y = y/8`. That is
deliberate: the Sender's value has no curvature, so nothing in the widening
response gap below can be attributed to it. The curvature is the transition's. -/

/-- A linear bounded-continuous value on the feasible state space. -/
noncomputable def ntLinBCF (c : ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => c * y.val) (by fun_prop))

@[simp] theorem ntLinBCF_apply (c : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    ntLinBCF c y = c * y.val := rfl

/-- Sender value: linear and strictly increasing. -/
noncomputable def ntV_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := ntLinBCF 2

/-- Target value: linear and strictly increasing. -/
noncomputable def ntV_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := ntLinBCF (1 / 8)

theorem ntV_S_mono : Monotone ntV_S := by
  intro y z hyz
  simp only [ntV_S, ntLinBCF_apply]
  have : y.val ≤ z.val := hyz
  linarith

theorem ntV_T_mono : Monotone ntV_T := by
  intro y z hyz
  simp only [ntV_T, ntLinBCF_apply]
  have : y.val ≤ z.val := hyz
  linarith

theorem nt_V_S_at {y : ℝ} (hy : y ∈ (Sanctions.S : Set ℝ)) :
    ntV_S (Sanctions.clipS' y) = 2 * y := by
  simp only [ntV_S, ntLinBCF_apply]
  rw [Sanctions.clipS'_val_eq_of_mem hy]

theorem nt_V_T_at {y : ℝ} (hy : y ∈ (Sanctions.S : Set ℝ)) :
    ntV_T (Sanctions.clipS' y) = (1 / 8) * y := by
  simp only [ntV_T, ntLinBCF_apply]
  rw [Sanctions.clipS'_val_eq_of_mem hy]

/-- **The forward-looking Sender response.** Interior to `[0,1]` at every
feasible state and action. -/
noncomputable def ntD (x a : ℝ) : ℝ := (6 - 4 * a + x) / 9

theorem ntD_mem {x a : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) (ha : a ∈ Sanctions.I) :
    ntD x a ∈ Sanctions.I := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha0, ha1⟩ := ha
  constructor <;> · unfold ntD; linarith

/-- The Sender's complete dynamic objective, written out on the feasible square.
The continuation term collapses because `V_S` is linear and the successor state
is feasible. -/
theorem nt_dynObj_eq {x s : ℝ} (a : ℝ)
    (hx : x ∈ (Sanctions.S : Set ℝ)) (hs : s ∈ Sanctions.I) :
    ntParams.U_S x a s + ntParams.β_S * ntV_S (Sanctions.clipS' (ntParams.F x s))
      = -(s - ntIdeal a) ^ 2 + ntShiftS x
        + (x + (s - x) / 2 - (1 / 8) * (s - x) ^ 2) := by
  have hFmem : ntF x s ∈ (Sanctions.S : Set ℝ) := ntF_mem x s hx hs
  show ntU_S x a s + (1 / 2 : ℝ) * ntV_S (Sanctions.clipS' (ntF x s)) = _
  rw [nt_V_S_at hFmem, ntF_of_mem hx hs]
  unfold ntU_S
  ring

/-- **The greatest forward-looking Sender response is exactly `ntD`.**

The complete dynamic objective is a downward parabola in the sanction with
vertex `ntD x a`; its gap to the vertex is `(9/8)(ntD x a - s)^2`, so any other
maximizer would have to sit at the vertex too. -/
theorem nt_top_eq_ntD {x a : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ)) (ha : a ∈ Sanctions.I) :
    ntParams.σ_dyn_top ntV_S x a = ntD x a := by
  have hd : ntD x a ∈ Sanctions.I := ntD_mem hx ha
  have htop : ntParams.σ_dyn_top ntV_S x a ∈ Sanctions.I :=
    ntParams.σ_dyn_top_mem_I ntV_S x a
  have hmax := ntParams.σ_dyn_top_isMaxOn ntV_S x a
  rw [isMaxOn_iff] at hmax
  have hcomp := hmax (ntD x a) hd
  rw [nt_dynObj_eq a hx hd, nt_dynObj_eq a hx htop] at hcomp
  -- the parabola identity, then squeeze
  unfold ntD
  unfold ntD ntIdeal at hcomp
  nlinarith [sq_nonneg (ntParams.σ_dyn_top ntV_S x a - (6 - 4 * a + x) / 9)]

/-! ## 5. The response gap widens in compliance

Both responses strictly fall as the Target complies more, the forward-looking one
is the harder of the two, and yet the **gap between them grows**. That is the
whole mechanism: the switch channel reads the gap, not the level. -/

theorem nt_gap_eq {x a : ℝ} (ha : a ∈ Sanctions.I) :
    ntD x a - ntSigma x a = 1 / 6 + a / 18 + x / 9 := by
  rw [ntSigma_of_mem ha]
  unfold ntD ntIdeal
  ring

/-- **The gap strictly widens in compliance.** -/
theorem nt_gap_strictMono {x a₁ a₂ : ℝ}
    (h₁ : a₁ ∈ Sanctions.I) (h₂ : a₂ ∈ Sanctions.I) (hlt : a₁ < a₂) :
    ntD x a₁ - ntSigma x a₁ < ntD x a₂ - ntSigma x a₂ := by
  rw [nt_gap_eq h₁, nt_gap_eq h₂]; linarith

/-- Both responses strictly fall in compliance. -/
theorem nt_responses_strictAnti {x a₁ a₂ : ℝ}
    (h₁ : a₁ ∈ Sanctions.I) (h₂ : a₂ ∈ Sanctions.I) (hlt : a₁ < a₂) :
    ntSigma x a₂ < ntSigma x a₁ ∧ ntD x a₂ < ntD x a₁ := by
  rw [ntSigma_of_mem h₁, ntSigma_of_mem h₂]
  unfold ntIdeal ntD
  constructor <;> linarith

/-- The forward-looking Sender sanctions strictly harder at the same action. -/
theorem nt_dynamic_gt_static {x a : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ)) (ha : a ∈ Sanctions.I) :
    ntSigma x a < ntD x a := by
  have h := nt_gap_eq (x := x) ha
  obtain ⟨hx0, _⟩ := hx
  obtain ⟨ha0, _⟩ := ha
  linarith

/-! ## 6. The two equilibria -/

/-- The forward-looking Target complies fully. -/
noncomputable def ntAlpha : ℝ → ℝ := fun _ => 1

theorem ntAlpha_mem (x : ℝ) : ntAlpha x ∈ Sanctions.I := by
  constructor <;> norm_num [ntAlpha]

theorem nt_sender_value_fix :
    ntV_S = ntParams.bellmanS_BCF ntAlpha continuous_const ntV_S := by
  ext y
  have hy : y.val ∈ (Sanctions.S : Set ℝ) := y.property
  have hdmem : ntD y.val 1 ∈ Sanctions.I := ntD_mem hy (by constructor <;> norm_num)
  have hmax : IsMaxOn
      (fun s => ntParams.U_S y.val (ntAlpha y.val) s
        + ntParams.β_S * ntV_S (Sanctions.clipS' (ntParams.F y.val s)))
      Sanctions.I (ntD y.val 1) := by
    rw [isMaxOn_iff]
    intro s hs
    rw [nt_dynObj_eq _ hy hs, nt_dynObj_eq _ hy hdmem]
    show _ ≤ -(ntD y.val 1 - ntIdeal (ntAlpha y.val)) ^ 2 + _ + _
    unfold ntAlpha ntD ntIdeal
    nlinarith [sq_nonneg (s - (6 - 4 * 1 + y.val) / 9)]
  have himage := WitnessKit.bellmanS_image_of_isMaxOn
    (p := ntParams) (α := ntAlpha) continuous_const ntV_S y hdmem hmax
  rw [himage, nt_dynObj_eq _ hy hdmem]
  simp only [ntV_S, ntLinBCF_apply, ntAlpha, ntD, ntIdeal, ntShiftS]
  ring

theorem nt_joint_eq {x a : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ)) (ha : a ∈ Sanctions.I) :
    ntParams.joint_T_top_integrand ntV_T ntV_S x a
      = -a ^ 2 / 648 - a * x / 162 + a / 36 + 85 * x / 648 - 17 / 648 := by
  have hd : ntD x a ∈ Sanctions.I := ntD_mem hx ha
  have hFmem : ntF x (ntD x a) ∈ (Sanctions.S : Set ℝ) := ntF_mem x _ hx hd
  show ntParams.U_T x a (ntParams.σ_dyn_top ntV_S x a)
      + ntParams.β_T * ntV_T (Sanctions.clipS' (ntParams.F x (ntParams.σ_dyn_top ntV_S x a)))
      = _
  rw [nt_top_eq_ntD hx ha]
  show ntU_T x a (ntD x a) + (1 / 2 : ℝ) * ntV_T (Sanctions.clipS' (ntF x (ntD x a))) = _
  rw [nt_V_T_at hFmem, ntF_of_mem hx hd]
  unfold ntU_T ntShiftT ntD
  ring

/-- **Full compliance is optimal for the forward-looking Target**, at every
feasible state. The gap to any other action is `(1-a)(17-a-4x)/648 ≥ 0`. -/
theorem nt_target_policy_optimal {x : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) :
    IsMaxOn (fun a => ntParams.joint_T_top_integrand ntV_T ntV_S x a)
      Sanctions.I (ntAlpha x) := by
  rw [isMaxOn_iff]
  intro a ha
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha0, ha1⟩ := ha
  rw [nt_joint_eq ⟨hx0, hx1⟩ ⟨ha0, ha1⟩]
  show _ ≤ ntParams.joint_T_top_integrand ntV_T ntV_S x (ntAlpha x)
  rw [show ntAlpha x = 1 from rfl, nt_joint_eq ⟨hx0, hx1⟩ (by constructor <;> norm_num)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) (by linarith : (0:ℝ) ≤ 17 - a - 4 * x)]

theorem nt_target_value_fix_top (x : ↥(Sanctions.S : Set ℝ)) :
    ntV_T x = sSup ((fun a => ntParams.joint_T_top_integrand ntV_T ntV_S x.val a)
      '' Sanctions.I) := by
  have hx : x.val ∈ (Sanctions.S : Set ℝ) := x.property
  have hgreatest : IsGreatest
      ((fun a => ntParams.joint_T_top_integrand ntV_T ntV_S x.val a) '' Sanctions.I)
      (ntParams.joint_T_top_integrand ntV_T ntV_S x.val 1) := by
    constructor
    · exact ⟨1, by constructor <;> norm_num, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      have := nt_target_policy_optimal hx ha
      simpa [ntAlpha] using this
  rw [hgreatest.csSup_eq, nt_joint_eq hx (by constructor <;> norm_num)]
  simp only [ntV_T, ntLinBCF_apply]
  ring

/-- **The fully forward-looking equilibrium.** -/
noncomputable def ntEquilibrium : ntParams.FeedbackStackelbergEquilibriumTop where
  V_T := ntV_T
  V_S := ntV_S
  α := ntAlpha
  hα := continuous_const
  α_mem := fun x _ => ntAlpha_mem x
  V_S_fix := nt_sender_value_fix
  V_T_fix_top := nt_target_value_fix_top
  α_opt_top := fun _ hx => nt_target_policy_optimal hx

/-- **Full defiance is optimal for the myopic Target.** Its objective falls in
compliance at rate `1/54`. -/
theorem nt_myopic_policy_optimal (x : ℝ) :
    IsMaxOn (fun a => ntParams.U_T x a (ntParams.σ x a)) Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  show ntU_T x a (ntSigma x a) ≤ ntU_T x 0 (ntSigma x 0)
  rw [ntSigma_of_mem ha, ntSigma_of_mem (by constructor <;> norm_num : (0:ℝ) ∈ Sanctions.I)]
  obtain ⟨ha0, _⟩ := ha
  unfold ntU_T ntIdeal
  linarith

/-- **The independently optimized myopic equilibrium.** -/
noncomputable def ntMyopic : ntParams.MyopicFeedbackEquilibrium where
  α := fun _ => 0
  α_mem := fun x _ => by constructor <;> norm_num
  α_opt := fun x _ => nt_myopic_policy_optimal x

/-! ## 7. The reversal -/

/-- **At this economy the forward-looking Target complies STRICTLY MORE than the
myopic one**, at every feasible state — the exact reverse of the intended
Target-reluctance ordering. -/
theorem nt_ordering_reversed (x : ℝ) :
    ntMyopic.α x < ntEquilibrium.α x := by
  show (0:ℝ) < 1
  norm_num

/-- **The baseline does not determine the two-sided Target-policy order.**

There is no theorem ordering the two regimes' policies from the model primitives
alone: this economy satisfies them and orders the other way. Rule 11 — definitive,
not inconclusive, and the reason the cross-response condition of
`Theory/LockIn/TwoSidedForwardLooking.lean` is *logically required* rather than a
convenience.

Rule 9A: this licenses the failure of the universal and nothing more. It says
nothing about whether the intended ordering holds in typical or calibrated
sanctions economies. -/
theorem baseline_does_not_determine_two_sided_order :
    ¬ ∀ (p : AbstractGame.Params) (E : p.FeedbackStackelbergEquilibriumTop)
        (M : p.MyopicFeedbackEquilibrium) (x : ℝ), x ∈ (Sanctions.S : Set ℝ) →
        E.α x ≤ M.α x := by
  intro h
  have := h ntParams ntEquilibrium ntMyopic (1 / 2) (by constructor <;> norm_num)
  have hrev := nt_ordering_reversed (1 / 2)
  linarith


/-! ## 8. The wedge condition itself fails here

`TwoSidedForwardLooking.lean` derives the Target ordering from a strictly
*decreasing* total forward-looking wedge. At this economy the wedge strictly
**rises**, so that condition fails — which is what makes it a genuine restriction
on the model class rather than a property the primitives already deliver. -/

theorem nt_totalWedge_eq {x a : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ)) (ha : a ∈ Sanctions.I) :
    ntParams.totalForwardWedge ntEquilibrium x a
      = -a ^ 2 / 648 - a * x / 162 + 5 * a / 108
        - x ^ 2 / 162 + 67 * x / 432 + 53 / 288 := by
  show ntParams.joint_T_top_integrand ntV_T ntV_S x a - ntU_T x a (ntSigma x a) = _
  rw [nt_joint_eq hx ha, ntSigma_of_mem ha]
  unfold ntU_T ntShiftT ntIdeal
  ring

/-- **The total forward-looking wedge strictly rises in compliance** — the
adverse Sender-switch channel outweighs the favourable Target-continuation
channel. -/
theorem nt_totalWedge_strictMono {x a₁ a₂ : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ))
    (h₁ : a₁ ∈ Sanctions.I) (h₂ : a₂ ∈ Sanctions.I) (hlt : a₁ < a₂) :
    ntParams.totalForwardWedge ntEquilibrium x a₁
      < ntParams.totalForwardWedge ntEquilibrium x a₂ := by
  rw [nt_totalWedge_eq hx h₁, nt_totalWedge_eq hx h₂]
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha10, ha11⟩ := h₁
  obtain ⟨ha20, ha21⟩ := h₂
  nlinarith [mul_pos (by linarith : (0:ℝ) < a₂ - a₁)
    (by linarith : (0:ℝ) < 30 - a₁ - a₂ - 4 * x)]

/-- **The strictly-decreasing-wedge condition fails at this economy.**

So that condition is a real restriction on the model class, not something the
baseline primitives already supply. Together with `nt_ordering_reversed` this is
the pair the design package asked for: the condition cannot be dropped, and
without it the ordering can go the other way. -/
theorem nt_wedge_condition_fails {x : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) :
    ¬ ntParams.DynamicVsMyopicStrictDecreasingDifferencesAt ntEquilibrium x := by
  intro h
  have h0 : (0:ℝ) ∈ Sanctions.I := by constructor <;> norm_num
  have h1 : (1:ℝ) ∈ Sanctions.I := by constructor <;> norm_num
  have hdec := h 0 h0 1 h1 (by norm_num)
  have hmono := nt_totalWedge_strictMono hx h0 h1 (by norm_num)
  linarith

/-! ## 9. The witness instantiates the general curvature mechanism

Everything above computes the reversal by direct algebra, which is the stronger
witness-specific statement but leaves open whether the general machinery in
`Foundations/ArgmaxSensitivity.lean` and `TwoSidedForwardLooking.lean` §12 is
actually *about* this economy. This section closes that: the four hypotheses of
`responseGap_monotoneOn_of_senderContinuationConcaveAt` are discharged here, and
the general theorem then re-derives the widening gap that `nt_gap_strictMono`
proves by hand.

The economy lands in the **concave** — adverse — case, and the reason is exactly
the one the round claims. `V_S` is linear, so it contributes no curvature at all;
the composite `s ↦ β_S · V_S(F(x,s))` collapses to `F(x, ·)` itself, whose
strict concavity in the sanction is the transition's doing alone. -/

/-- The Sender's stage payoff at this economy is a translated loss: compliance
relocates the Sender's stage problem without reshaping it. `g` here is the same
downward parabola at every compliance level, centred on the static response. -/
theorem nt_translatedLoss (x : ℝ) :
    ntParams.TranslatedLossSenderAt x (fun u => -u ^ 2 + ntShiftS x) := by
  intro a ha s
  show ntU_S x a s = -(s - ntSigma x a) ^ 2 + ntShiftS x
  rw [ntSigma_of_mem ha]
  unfold ntU_S
  ring

/-- **The composite Sender continuation term is concave in the sanction.**

And it is the transition alone that makes it so: `V_S y = 2y` is linear and
`β_S = 1/2`, so the composite is `F(x, ·)` on the nose, whose second difference
in the sanction is `-1/4`. Stated on the composite, per the §12 discipline —
never inferred from curvature of one factor. -/
theorem nt_senderContinuationConcaveAt {x : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) :
    ntParams.SenderContinuationConcaveAt ntV_S x := by
  have key : ∀ s ∈ Sanctions.I,
      ntParams.senderContinuationTerm ntV_S x s
        = x + (s - x) / 2 - (1 / 8) * (s - x) ^ 2 := by
    intro s hs
    show (1 / 2 : ℝ) * ntV_S (Sanctions.clipS' (ntF x s)) = _
    rw [nt_V_S_at (ntF_mem x s hx hs), ntF_of_mem hx hs]
    ring
  refine ⟨convex_Icc 0 1, fun s₁ hs₁ s₂ hs₂ c d hc hd hcd => ?_⟩
  have hmid : c • s₁ + d • s₂ ∈ Sanctions.I := convex_Icc 0 1 hs₁ hs₂ hc hd hcd
  simp only [smul_eq_mul] at hmid ⊢
  rw [key s₁ hs₁, key s₂ hs₂, key _ hmid]
  -- The linear part is exact; the quadratic gap is `c·d·(s₁-s₂)²/8`.
  have hd' : d = 1 - c := by linarith
  subst hd'
  nlinarith [mul_nonneg (mul_nonneg hc hd) (sq_nonneg (s₁ - s₂))]

/-- The static Sender response falls in compliance: placation, at this economy. -/
theorem nt_sigma_antitoneOn (x : ℝ) :
    AntitoneOn (fun a => ntParams.σ x a) Sanctions.I := by
  intro a₁ h₁ a₂ h₂ hle
  show ntSigma x a₂ ≤ ntSigma x a₁
  rw [ntSigma_of_mem h₁, ntSigma_of_mem h₂]
  unfold ntIdeal
  linarith

/-- **The translated response candidates stay feasible.** Both responses are
interior at every feasible state and action, with room to spare, so translating
either by the movement of the static response cannot leave `[0,1]`. -/
theorem nt_responseTranslatesFeasible {x : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) :
    ntParams.ResponseTranslatesFeasibleAt ntV_S x := by
  intro a₁ h₁ a₂ h₂ hle
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨ha10, ha11⟩ := h₁
  obtain ⟨ha20, ha21⟩ := h₂
  simp only [ntParams_σ]
  rw [nt_top_eq_ntD ⟨hx0, hx1⟩ ⟨ha10, ha11⟩, nt_top_eq_ntD ⟨hx0, hx1⟩ ⟨ha20, ha21⟩,
    ntSigma_of_mem ⟨ha10, ha11⟩, ntSigma_of_mem ⟨ha20, ha21⟩]
  unfold ntD ntIdeal
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **The general mechanism delivers the widening gap.**

`nt_gap_strictMono` proves the same movement by direct algebra and proves it
*strictly*; this derives the weak form from
`responseGap_monotoneOn_of_senderContinuationConcaveAt` instead, so the abstract
curvature route is visibly instantiated rather than merely asserted to cover this
case. The direct computation stays as the stronger witness-specific result. -/
theorem nt_gap_monotoneOn_via_general_mechanism {x : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ)) :
    MonotoneOn (fun a => ntParams.σ_dyn_top ntV_S x a - ntParams.σ x a)
      Sanctions.I :=
  ntParams.responseGap_monotoneOn_of_senderContinuationConcaveAt ntV_S
    (nt_translatedLoss x).toDifferences (nt_senderContinuationConcaveAt hx)
    (nt_sigma_antitoneOn x) (nt_responseTranslatesFeasible hx)

end Examples
end Sanctions
