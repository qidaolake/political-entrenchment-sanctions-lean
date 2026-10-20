/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.NonAffineSenderChannelCounterexample
import Sanctions.Theory.Equilibrium.AbsorbingTopObstruction

/-!
# A linear Sender stake in the political state admits no equilibrium at `α ≡ 1/2`

**Rule-11 refutation (2026-07-28), user-authorized perturbation.**  The sibling
file `NonAffineSenderChannelCounterexample` refutes an *increasing* Sender value
*conditionally*, taking `Monotone` and a positive top slope as hypotheses.  This
file removes those hypotheses for the concrete authorized payoff.

`raU_S c x a s := niU_S x a s + c * x` — the Sender's per-period payoff rises
linearly in the entrenchment state, which is the paper's own "sanctions are
investments in political power" thesis.  `raParams c` takes **every** other
field verbatim from `niParams`.  This is *not* a self-cancellation trick: the
added term depends on `x` only, never on `s` and never on `F x s`, so it cannot
annihilate `β_S * V_S (F x s)` the way `maU_T`'s `-(9/10) * clipS (F x s)` term
annihilates `β_T * V_T (F x s)` in the mechanism-active witness.

## The headline

`ra_no_equilibrium_with_alpha_half` — for **every** `c > 0`, `raParams c` has no
feedback Stackelberg equilibrium whose Target policy is the constant interior
`α ≡ 1/2`.  It consumes only `V_S_fix` and `α_opt_top`, never `V_T_fix_top` or
`α_mem`, so it refutes an even *weaker* equilibrium notion than the full
structure.  Banach uniqueness (`V_S_unique`) forces any such equilibrium's
Sender value to be `raV_S c`, which is why no side hypothesis on `E.V_S` is
needed.

Existence is **constructed, not consumed** (Rule 15): `raV_S c` is the Banach
fixed point of the `β_S = 1/2` contraction `bellmanS_BCF`.

## Reading the auxiliary bounds correctly (Rule 1)

`raV_S c` is the Sender Bellman fixed point *at the fixed policy* `α ≡ 1/2` —
a policy this file proves is **not** optimal for any `c > 0`.  The intermediate
facts below (`raV_S_one : V_S 1 = 2 * c`, the slope-to-top bound, and the
response comparison at `1/2 + t`) are therefore statements about a *hypothetical
non-equilibrium policy*, and are load-bearing only as steps toward the
refutation.

**They must not be cited as equilibrium behaviour.**  In particular
`ra_response_strictly_exceeds_static_ideal` says the Sender would levy above its
stage-optimal sanction *were the Target to play the refuted constant policy*; it
is not evidence that any equilibrium of this economy has an active Sender
continuation channel.  Reading it that way would be exactly the Rule-1 error of
treating an assumed strategy as an optimization result.

## What the obstruction actually is

At `x = 1` the state is absorbing (`quadBumpF 1 1 = 1`) with zero stage loss, so
the Sender value there is pinned at `c / (1 - β_S) = 2c`.  That forces a
positive slope into the top of the state space, which pins the greatest dynamic
response at the corner `1` across a right-neighbourhood of `a = 1/2`.  The
Target's ideal `niIdeal 1 a = 9/8 - a/4` *falls* in `a`, so raising compliance
by `t` yields exactly `t/4 - t^2` — strictly positive for `t ∈ (0, 1/4)`.  The
constant policy is therefore not a maximizer.  This is the general absorbing-top
obstruction `AbsorbingTop.no_equilibrium_of_slope_and_top_gain` (which holds for
every transition `F`) at the witness's numbers, and the headline is proved as that
corollary (`ra_no_equilibrium_via_general`).

Sharpness: at `c = 0` the economy *is* `niParams`, `raV_S 0 = niV0 = 0`, and the
original equilibrium is restored.  The fence bites precisely on `c > 0`.

## Honest scope

* The replacement policy is **not** constructed.  This file proves `α(1) ≠ 1/2`;
  whether `raParams c` admits *any* equilibrium with a re-derived nonconstant
  `α` is open, and is a joint-existence problem, not a repair.
* All proved behavioural bite is at the corner `x = 1`.  The interior case is
  not established in Lean.
* `ra_no_affine_solution` refutes the Bellman recursion with the response
  *pinned* at `(x+1)/2`.  The true Sender Bellman is a supremum over feasible
  sanctions, so this does **not** establish "no affine `V_S` solves the Bellman
  equation"; it rules out the pinned surrogate only.
* `ra_cone_hypothesis_fails` shows the project's own monotone-cone tool
  (`V_S_monotone_of_integrand_monotone`) is unavailable here for every `c < 1`,
  because the required stage-payoff monotonicity has slope `c - 1` at worst.
  The bounds below are proved by a sup-norm sandwich instead.

No new assumption, parameter field, or carrier condition is introduced. The only
assumption-surface change is the authorized Sender state payoff.
-/

namespace Sanctions
namespace Examples
namespace SenderStake

open Set AbstractGame AbstractGame.Params Sanctions.Examples

noncomputable section

/-! ############################################################
    ## PART (a).  There is NO exact affine closed form.
    ############################################################ -/

/-- The realized successor state along the base-economy response
`s = niIdeal x (1/2) = (x+1)/2`. -/
theorem quadBump_at_ideal {x : ℝ} (hx : x ∈ Sanctions.S) :
    quadBumpF x ((x + 1) / 2) = (3 * x + 1) / 4 + (1 - x) ^ 3 / 800 := by
  have hmem : ((x + 1) / 2) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> [linarith [hx.1, hx.2]; linarith [hx.1, hx.2]]
  rw [quadBumpF_sq hx hmem]
  ring

/-- **Exact Bellman residual of an affine candidate.**  For `V(x) = A + B·x`,
the residual of the Route-A Sender recursion evaluated along the base-economy
realized response `s = (x+1)/2` is a linear part plus the *cubic bump*
`-B(1-x)^3/1600` contributed by the non-affine transition. -/
theorem ra_affine_residual (A B c : ℝ) {x : ℝ} (hx : x ∈ Sanctions.S) :
    (A + B * x)
      - ((niU_S x (1 / 2) ((x + 1) / 2) + c * x)
          + (1 / 2) * (A + B * quadBumpF x ((x + 1) / 2)))
      = (A / 2 - B / 8) + x * (5 * B / 8 - c) - B * (1 - x) ^ 3 / 1600 := by
  rw [quadBump_at_ideal hx]
  unfold niU_S
  rw [niIdeal_at_half]
  ring

/-- **PART (a) ANSWER.**  No affine `V(x) = A + B·x` solves the Route-A Sender
Bellman recursion (even along the *unshifted* base response), unless `c = 0` —
and then `V ≡ 0`, i.e. the base witness.  The obstruction is exactly the cubic
term `(1-x)^3/800` of `quadBumpF`. -/
theorem ra_no_affine_solution (A B c : ℝ)
    (h : ∀ x ∈ Sanctions.S,
      (A + B * x)
        = (niU_S x (1 / 2) ((x + 1) / 2) + c * x)
          + (1 / 2) * (A + B * quadBumpF x ((x + 1) / 2))) :
    B = 0 ∧ A = 0 ∧ c = 0 := by
  have key : ∀ x ∈ Sanctions.S,
      (A / 2 - B / 8) + x * (5 * B / 8 - c) - B * (1 - x) ^ 3 / 1600 = 0 := by
    intro x hx
    rw [← ra_affine_residual A B c hx, h x hx]
    ring
  have k0 := key 0 ⟨le_refl 0, by norm_num⟩
  have k1 := key 1 ⟨by norm_num, le_refl 1⟩
  have kh := key (1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num at k0 k1 kh
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ############################################################
    ## PART (b).  The Route-A economy.
    ############################################################ -/

/-- Route-A Sender stage payoff: the base concave loss plus a linear stake
`c·x` in the entrenchment state.  Independent of `s`. -/
def raU_S (c x a s : ℝ) : ℝ := niU_S x a s + c * x

theorem raU_S_isMaxOn (c x a : ℝ) :
    IsMaxOn (fun s => raU_S c x a s) Sanctions.I (niSigma x a) := by
  have h := niSigma_isMaxOn x a
  rw [isMaxOn_iff] at h ⊢
  intro s hs
  have := h s hs
  simp only [raU_S]
  simp only [] at this ⊢
  linarith

theorem raU_S_continuous (c : ℝ) :
    Continuous (fun xas : ℝ × ℝ × ℝ => raU_S c xas.1 xas.2.1 xas.2.2) := by
  unfold raU_S niU_S niIdeal
  fun_prop

/-- **The Route-A economy.**  Identical to `niParams` in every field except the
Sender stage payoff, which carries the extra state term `c·x`. -/
def raParams (c : ℝ) : AbstractGame.Params where
  δ := niParams.δ
  δ_mem := niParams.δ_mem
  β_T := niParams.β_T
  β_T_mem := niParams.β_T_mem
  β_S := niParams.β_S
  β_S_mem := niParams.β_S_mem
  U_T := niU_T
  U_S := raU_S c
  σ := niSigma
  σ_mem := niSigma_mem
  σ_isMaxOn_U_S := raU_S_isMaxOn c
  U_T_continuous := niU_T_continuous
  U_S_continuous := raU_S_continuous c
  F := niParams.F
  F_continuous := niParams.F_continuous
  F_mono_x := niParams.F_mono_x
  F_mono_s := niParams.F_mono_s
  F_diag := niParams.F_diag

/-- **`raParams` has a continuous static Sender selector.** A family with `niParams`'s
non-affine transition `quadBumpF`; the selector `niSigma` does not read the transition.
The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance raParams_staticSelectorContinuous (c : ℝ) :
    (raParams c).StaticSelectorContinuous where
  σ_continuous := niSigma_continuous

@[simp] theorem raParams_β_S (c : ℝ) : (raParams c).β_S = 1 / 2 := rfl
@[simp] theorem raParams_β_T (c : ℝ) : (raParams c).β_T = 9 / 10 := rfl
@[simp] theorem raParams_F (c : ℝ) : (raParams c).F = quadBumpF := rfl
@[simp] theorem raParams_U_S (c : ℝ) : (raParams c).U_S = raU_S c := rfl
@[simp] theorem raParams_U_T (c : ℝ) : (raParams c).U_T = niU_T := rfl

theorem raParams_F_ne_affine (c : ℝ) :
    (raParams c).F ≠ AbstractGame.affineF (1 / 2) := niParams_F_ne_affine

/-! ### Generic Bellman-fixed-point handles (parametric, Rule 5) -/

/-- Any feasible sanction gives a lower bound on the Sender value. -/
theorem V_S_ge_integrand (p : Params) {α : ℝ → ℝ} (hα : Continuous α)
    (x : ↥(Sanctions.S : Set ℝ)) {s : ℝ} (hs : s ∈ Sanctions.I) :
    p.U_S x.val (α x.val) s
        + p.β_S * p.V_S α hα (Sanctions.clipS' (p.F x.val s))
      ≤ p.V_S α hα x := by
  rw [p.V_S_bellman_eq hα x]
  exact le_csSup
    (p.integrandS_image_bddAbove hα (p.V_S α hα).continuous x.val) ⟨s, hs, rfl⟩

/-- A uniform bound on the integrand gives an upper bound on the Sender value. -/
theorem V_S_le_of_forall (p : Params) {α : ℝ → ℝ} (hα : Continuous α)
    (x : ↥(Sanctions.S : Set ℝ)) {B : ℝ}
    (h : ∀ s ∈ Sanctions.I, p.U_S x.val (α x.val) s
        + p.β_S * p.V_S α hα (Sanctions.clipS' (p.F x.val s)) ≤ B) :
    p.V_S α hα x ≤ B := by
  rw [p.V_S_bellman_eq hα x]
  refine csSup_le ⟨_, ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩⟩ ?_
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- **Uniqueness of the Banach Sender fixed point.**  Any bounded-continuous
solution of the Sender Bellman equation at policy `α` IS the constructed
`p.V_S α hα`. -/
theorem V_S_unique (p : Params) {α : ℝ → ℝ} (hα : Continuous α)
    (W : Params.Val) (hW : W = p.bellmanS_BCF α hα W) :
    W = p.V_S α hα := by
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) :=
    p.bellmanS_BCF_contracting hα
  have hfp : Function.IsFixedPt (p.bellmanS_BCF α hα) W := hW.symm
  have hu := hcontr.fixedPoint_unique hfp
  rw [hu]
  rfl

/-- **The project's existing monotone-cone tool is NOT available for small `c`.**
`V_S_monotone_of_integrand_monotone` (`Sanctions/Theory/Bellman/BellmanS.lean:275`)
requires `h_U_S_mono` — that `x ↦ U_S(x, α(x), s)` is nondecreasing on `S` for
EVERY `s ∈ I`.  For Route A that slope is `(s − x/2 − 1/2) + c`, whose minimum
over the square is `c − 1`, so the hypothesis FAILS for every `c < 1`
(witness: `s = 0`, `x = c`, `y = 1`; the gap is `3(1−c)²/4 > 0`).
Everything below therefore bypasses the cone entirely and uses a sup-norm
sandwich instead, which works for EVERY `c > 0`. -/
theorem ra_cone_hypothesis_fails (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬ (∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
        x ≤ y → (raParams c).U_S x (niAlpha x) s
          ≤ (raParams c).U_S y (niAlpha y) s) := by
  intro h
  have hstep := h 0 ⟨le_refl 0, by norm_num⟩ c ⟨hc0, hc1.le⟩ 1
    ⟨by norm_num, le_refl 1⟩ hc1.le
  have hval : (raParams c).U_S c (niAlpha c) 0 = -(c + 1) ^ 2 / 4 + c * c := by
    show raU_S c c (1 / 2) 0 = _
    unfold raU_S niU_S
    rw [niIdeal_at_half]
    ring
  have hval1 : (raParams c).U_S 1 (niAlpha 1) 0 = -1 + c := by
    show raU_S c 1 (1 / 2) 0 = _
    unfold raU_S niU_S
    rw [niIdeal_at_half]
    ring
  rw [hval, hval1] at hstep
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - c) (by linarith : (0 : ℝ) < 1 - c)]

/-! ### The constructed Route-A Sender value function (Rule 15) -/

/-- **EXISTENCE, CONSTRUCTED FROM PRIMITIVES (Rule 15).**  `raV_S c` is the
Banach fixed point of the `β_S = 1/2` contraction `bellmanS_BCF` at the
constant Target policy `α ≡ 1/2`.  It is *not* hypothesized. -/
def raV_S (c : ℝ) : Params.Val :=
  (raParams c).V_S niAlpha niAlpha_continuous

theorem raV_S_bellman (c : ℝ) :
    raV_S c = (raParams c).bellmanS_BCF niAlpha niAlpha_continuous (raV_S c) :=
  ((raParams c).V_S_isFixedPoint niAlpha_continuous).symm

/-- The top state as an element of the state space. -/
def raOne : ↥(Sanctions.S : Set ℝ) := ⟨1, ⟨by norm_num, le_refl 1⟩⟩

theorem raU_S_at_ideal (c x : ℝ) : raU_S c x (1 / 2) ((x + 1) / 2) = c * x := by
  unfold raU_S niU_S
  rw [niIdeal_at_half]
  ring

/-- Every integrand value at state `y` is bounded by `c·y + (1/2)·(bound on V)`. -/
theorem raV_S_le_of_bound (c : ℝ) (M : ℝ)
    (hM : ∀ z : ↥(Sanctions.S : Set ℝ), raV_S c z ≤ M)
    (y : ↥(Sanctions.S : Set ℝ)) :
    raV_S c y ≤ c * y.val + (1 / 2) * M := by
  refine V_S_le_of_forall (raParams c) niAlpha_continuous y ?_
  intro s hs
  have hb := hM (Sanctions.clipS' (quadBumpF y.val s))
  have hgoal : (raParams c).U_S y.val (niAlpha y.val) s
      + (raParams c).β_S * (raParams c).V_S niAlpha niAlpha_continuous
          (Sanctions.clipS' ((raParams c).F y.val s))
      = -(s - niIdeal y.val (1 / 2)) ^ 2 + c * y.val
        + (1 / 2) * raV_S c (Sanctions.clipS' (quadBumpF y.val s)) := rfl
  rw [hgoal]
  nlinarith [sq_nonneg (s - niIdeal y.val (1 / 2)), hb]

/-- Lower bound at state `y` from the (always feasible) ideal sanction. -/
theorem raV_S_ge_of_bound (c : ℝ) (L : ℝ)
    (hL : ∀ z : ↥(Sanctions.S : Set ℝ), L ≤ raV_S c z)
    (y : ↥(Sanctions.S : Set ℝ)) :
    c * y.val + (1 / 2) * L ≤ raV_S c y := by
  have hmem : ((y.val + 1) / 2) ∈ Sanctions.I := by
    constructor <;> [linarith [y.property.1, y.property.2];
                     linarith [y.property.1, y.property.2]]
  have h := V_S_ge_integrand (raParams c) niAlpha_continuous y hmem
  have hgoal : (raParams c).U_S y.val (niAlpha y.val) ((y.val + 1) / 2)
      + (raParams c).β_S * (raParams c).V_S niAlpha niAlpha_continuous
          (Sanctions.clipS' ((raParams c).F y.val ((y.val + 1) / 2)))
      = raU_S c y.val (1 / 2) ((y.val + 1) / 2)
        + (1 / 2) * raV_S c
            (Sanctions.clipS' (quadBumpF y.val ((y.val + 1) / 2))) := rfl
  rw [hgoal, raU_S_at_ideal] at h
  have h' : c * y.val
      + (1 / 2) * raV_S c (Sanctions.clipS' (quadBumpF y.val ((y.val + 1) / 2)))
      ≤ raV_S c y := h
  have := hL (Sanctions.clipS' (quadBumpF y.val ((y.val + 1) / 2)))
  linarith

/-- **Sup-norm bound `‖V_S‖ ≤ 2c`.**  Derived, not assumed. -/
theorem raV_S_norm_le (c : ℝ) (hc : 0 ≤ c) : ‖raV_S c‖ ≤ 2 * c := by
  set N := ‖raV_S c‖ with hNdef
  have hNnn : (0 : ℝ) ≤ N := norm_nonneg _
  have hup : ∀ z : ↥(Sanctions.S : Set ℝ), raV_S c z ≤ N := by
    intro z
    have := (raV_S c).norm_coe_le_norm z
    rw [Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hdn : ∀ z : ↥(Sanctions.S : Set ℝ), -N ≤ raV_S c z := by
    intro z
    have := (raV_S c).norm_coe_le_norm z
    rw [Real.norm_eq_abs] at this
    exact le_trans (neg_le_neg this) (neg_abs_le _)
  have key : ∀ z : ↥(Sanctions.S : Set ℝ), ‖raV_S c z‖ ≤ c + N / 2 := by
    intro z
    have h1 := raV_S_le_of_bound c N hup z
    have h2 := raV_S_ge_of_bound c (-N) hdn z
    have hz0 := z.property.1
    have hz1 := z.property.2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  have hfin : N ≤ c + N / 2 :=
    (BoundedContinuousFunction.norm_le (by linarith)).mpr key
  linarith

/-- **Pointwise upper bound `V_S(x) ≤ c·x + c`.** -/
theorem raV_S_le (c : ℝ) (hc : 0 ≤ c) (y : ↥(Sanctions.S : Set ℝ)) :
    raV_S c y ≤ c * y.val + c := by
  have hup : ∀ z : ↥(Sanctions.S : Set ℝ), raV_S c z ≤ 2 * c := by
    intro z
    have := (raV_S c).norm_coe_le_norm z
    rw [Real.norm_eq_abs] at this
    have h2 := raV_S_norm_le c hc
    have := le_trans (le_abs_self _) this
    linarith
  have := raV_S_le_of_bound c (2 * c) hup y
  linarith

/-- **Exact top value `V_S(1) = 2c`.**  The state `x = 1` is absorbing under the
Sender's own ideal sanction (`F(1,1) = 1`) and the stage loss there is zero, so
the geometric sum `c·(1 + β_S + β_S² + …) = c/(1-β_S) = 2c` is exact. -/
theorem raV_S_one (c : ℝ) (hc : 0 ≤ c) : raV_S c raOne = 2 * c := by
  have hone : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hclip : Sanctions.clipS' (quadBumpF (1 : ℝ) ((1 + 1) / 2)) = raOne := by
    apply Subtype.ext
    rw [Sanctions.clipS'_val_eq_of_mem]
    · rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, quadBumpF_one]
      norm_num [raOne]
    · rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, quadBumpF_one]
      constructor <;> norm_num
  refine le_antisymm ?_ ?_
  · have := raV_S_le c hc raOne
    simp only [raOne] at this ⊢
    linarith
  · have hmem : (((1 : ℝ) + 1) / 2) ∈ Sanctions.I := by norm_num
    have h := V_S_ge_integrand (raParams c) niAlpha_continuous raOne hmem
    have hgoal : (raParams c).U_S raOne.val (niAlpha raOne.val) (((1 : ℝ) + 1) / 2)
        + (raParams c).β_S * (raParams c).V_S niAlpha niAlpha_continuous
            (Sanctions.clipS' ((raParams c).F raOne.val (((1 : ℝ) + 1) / 2)))
        = raU_S c 1 (1 / 2) (((1 : ℝ) + 1) / 2)
          + (1 / 2) * raV_S c (Sanctions.clipS' (quadBumpF 1 (((1 : ℝ) + 1) / 2))) := rfl
    rw [hgoal, raU_S_at_ideal, hclip] at h
    change c * 1 + (1 / 2) * raV_S c raOne ≤ raV_S c raOne at h
    linarith

/-- **THE ROUTE-A PAYOFF: a genuine positive slope up to the top state.**
`V_S(1) − V_S(y) ≥ c·(1 − y)` for EVERY feasible `y` — no closed form, no cone
hypothesis, no monotonicity assumption. -/
theorem raV_S_slope_to_top (c : ℝ) (hc : 0 ≤ c) (y : ↥(Sanctions.S : Set ℝ)) :
    c * (1 - y.val) ≤ raV_S c raOne - raV_S c y := by
  have h1 := raV_S_one c hc
  have h2 := raV_S_le c hc y
  linarith

/-- **`V_S` is NONCONSTANT** for every `c > 0`: `V_S(1) − V_S(0) ≥ c > 0`. -/
theorem raV_S_nonconstant (c : ℝ) (hc : 0 < c) :
    raV_S c ⟨0, ⟨le_refl 0, by norm_num⟩⟩ < raV_S c raOne := by
  have h := raV_S_slope_to_top c hc.le ⟨0, ⟨le_refl 0, by norm_num⟩⟩
  simp only at h
  linarith

/-! ############################################################
    ## The Rule-1 crux:  does `α ≡ 1/2` survive?
    ############################################################ -/

/-- **Corner pin from a slope-to-the-top bound alone.**  No global
`Monotone V_S` and no restriction of the slope to `[31/32, 1]` — only the
one-sided bound `m·(1 − y) ≤ V_S(1) − V_S(y)`, and no `t ≤ 1/8`.  These
hypotheses are *incomparable* with those of the Rule-11 gate's
`corner_pin_of_slope` at the same `m` (the one-sided bound is required from
every state, not only on `[31/32, 1]`), so this is not a weakening of that
lemma.  The gate's bundle does imply this one at the smaller rate
`m·(1 − lo)`: see `slope_to_top_of_monotone_topSlope`.  Witness-specific: the
transition is the non-affine `quadBumpF`. -/
theorem corner_pin_of_slope_to_top
    (p : Params) (hβS : p.β_S = 1 / 2) (hF : p.F = quadBumpF)
    (g1 : ℝ) (hUS : ∀ a s, p.U_S 1 a s = niU_S 1 a s + g1)
    (V_S : Params.Val) (m : ℝ) (hm : 0 ≤ m)
    (one : ↥(Sanctions.S : Set ℝ)) (hone : one.val = 1)
    (hslope : ∀ y : ↥(Sanctions.S : Set ℝ), m * (1 - y.val) ≤ V_S one - V_S y)
    (t : ℝ) (htm : t ≤ 49 * m / 100) :
    p.σ_dyn_top V_S 1 (1 / 2 + t) = 1 := by
  have honeI : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hclipone : Sanctions.clipS' (1 : ℝ) = one :=
    Subtype.ext (by rw [Sanctions.clipS'_val_eq_of_mem honeI, hone])
  have hmax : IsMaxOn (fun s' => p.U_S 1 (1 / 2 + t) s'
      + p.β_S * V_S (Sanctions.clipS' (p.F 1 s'))) Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rw [hUS, hUS, hβS, hF]
    have hqb1 : quadBumpF 1 1 = 1 := by rw [quadBumpF_one]; norm_num
    have hqbs : quadBumpF 1 s
        = 1 / 2 * 1 + 1 / 2 * s + 1 / 100 * (s - 1) ^ 2 * (1 - s) :=
      quadBumpF_sq honeI hs
    have hqbmem : quadBumpF 1 s ∈ Set.Icc (0 : ℝ) 1 := quadBumpF_mem 1 s honeI hs
    have hvs : (Sanctions.clipS' (quadBumpF 1 s)).val = quadBumpF 1 s :=
      Sanctions.clipS'_val_eq_of_mem hqbmem
    -- slope bound at the successor state
    have hsl := hslope (Sanctions.clipS' (quadBumpF 1 s))
    rw [hvs] at hsl
    rw [hqb1, hclipone]
    -- `1 - quadBumpF 1 s ≥ 49 (1-s) / 100`
    have hu0 : 0 ≤ 1 - s := by linarith [hs.2]
    have hu1 : 1 - s ≤ 1 := by linarith [hs.1]
    have hcube : (1 - s) ^ 3 ≤ 1 - s := by nlinarith
    have hgap : 49 * (1 - s) / 100 ≤ 1 - quadBumpF 1 s := by
      rw [hqbs]; nlinarith
    unfold niU_S niIdeal
    nlinarith [hsl, hgap, hu0, sq_nonneg (1 - s),
      mul_nonneg (sub_nonneg.mpr htm) hu0,
      mul_nonneg hm hu0, sq_nonneg (s - 1 + t / 4)]
  have hmem : (1 : ℝ) ∈ p.dynamicArgmaxSet V_S 1 (1 / 2 + t) := ⟨honeI, hmax⟩
  refine le_antisymm ?_ ?_
  · exact csSup_le ⟨1, hmem⟩ (fun b hb => hb.1.2)
  · exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S 1 (1 / 2 + t)) hmem

/-- The Route-A Sender response IS pinned at the corner on a right-neighbourhood
of `a = 1/2` at the top state. -/
theorem ra_corner_pin (c : ℝ) (hc : 0 ≤ c) {t : ℝ}
    (htm : t ≤ 49 * c / 100) :
    (raParams c).σ_dyn_top (raV_S c) 1 (1 / 2 + t) = 1 :=
  corner_pin_of_slope_to_top (raParams c) rfl rfl c
    (fun a s => by simp only [raParams_U_S, raU_S]; ring)
    (raV_S c) c hc raOne rfl (raV_S_slope_to_top c hc) t htm

/-- **RULE-16(a) DIRECTIONAL WITNESS — the Sender continuation channel is
BEHAVIOURALLY ACTIVE.**  At the top state, for every action `a = 1/2 + t` in a
right-neighbourhood of `1/2`, the Sender's *dynamic* greatest response strictly
EXCEEDS its static/myopic ideal `niIdeal 1 a = 1 − t/4`.  Sanctions are being
levied above the stage-optimal level purely to buy future entrenchment. -/
theorem ra_response_strictly_exceeds_static_ideal (c : ℝ) (hc : 0 < c) {t : ℝ}
    (ht0 : 0 < t) (htm : t ≤ 49 * c / 100) :
    niIdeal 1 (1 / 2 + t) < (raParams c).σ_dyn_top (raV_S c) 1 (1 / 2 + t) := by
  rw [ra_corner_pin c hc.le htm]
  unfold niIdeal
  linarith

/-- **EXPLICIT DEVIATION GAIN (Rule 16(a) directional witness).**  Under the
corner pin, the Target's joint top integrand at `x = 1` moves from `a = 1/2` to
`a = 1/2 + t` by exactly `t/4 − t²`.  The `V_T` continuation term cancels
identically (both actions lead to the same successor state `1`), so the gain is
independent of `V_T`; it is strictly positive for every `t ∈ (0, 1/4)`.
This is the *first-order* profitable deviation that destroys `α ≡ 1/2`. -/
theorem ra_target_gain_at_one (c : ℝ) (hc : 0 < c) (V_T : Params.Val) {t : ℝ}
    (htm : t ≤ 49 * c / 100) :
    (raParams c).joint_T_top_integrand V_T (raV_S c) 1 (1 / 2 + t)
      - (raParams c).joint_T_top_integrand V_T (raV_S c) 1 (1 / 2)
      = t / 4 - t ^ 2 := by
  have h0 : (raParams c).σ_dyn_top (raV_S c) 1 (1 / 2) = 1 := by
    have := ra_corner_pin c hc.le (t := 0) (by linarith)
    simpa using this
  have ht : (raParams c).σ_dyn_top (raV_S c) 1 (1 / 2 + t) = 1 :=
    ra_corner_pin c hc.le htm
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [h0, ht]
  show (niU_T 1 (1 / 2 + t) 1 + _) - (niU_T 1 (1 / 2) 1 + _) = _
  unfold niU_T niIdeal
  ring

/-! ## Rule-5: the witness obstruction is the general one, specialized -/

/-- Top-state transition responsiveness of `quadBumpF`: `κ = 49/100`.  A
one-line alias of `Sanctions.Examples.quadBumpF_top_transition`, proved in the
sibling gate file, whose refutation uses the same input.
Witness-specific: a fact about the non-affine transition `quadBumpF` only. -/
theorem quadBump_top_transition (s : ℝ) (hs : s ∈ Sanctions.I) :
    (49 / 100 : ℝ) * (1 - s) ≤ 1 - quadBumpF 1 s :=
  quadBumpF_top_transition s hs

/-- Static shading bound at the top state: at Target action `1/2 + t` the
Sender's static gain from shading the sanction is at most `(t/2)(1-s)`. -/
theorem ra_shade_bound (c t : ℝ) (s : ℝ) (hs : s ∈ Sanctions.I) :
    (raParams c).U_S 1 (1 / 2 + t) s - (raParams c).U_S 1 (1 / 2 + t) 1
      ≤ (t / 2) * (1 - s) := by
  show raU_S c 1 (1 / 2 + t) s - raU_S c 1 (1 / 2 + t) 1 ≤ (t / 2) * (1 - s)
  unfold raU_S niU_S niIdeal
  nlinarith [sq_nonneg (1 - s - t / 4), hs.1, hs.2]

/-- **Rule-5 corollary: the witness obstruction IS the general one.**

`ra_no_equilibrium_with_alpha_half` (below) is this theorem at the deviation size
`t = min (49c/100) (1/8)`.  It instantiates the general absorbing-top obstruction
`AbsorbingTop.no_equilibrium_of_slope_and_top_gain` (general in `F`) with

* `m = c` — the Sender's stake is exactly its value's slope to the top;
* `κ = 49/100` — the quadratic-bump transition's top responsiveness;
* shading bound `t/2`,

whereupon the general binding condition `c_shade ≤ β_S · m · κ` becomes
`t/2 ≤ (1/2) · c · (49/100)`, i.e. the witness's own `t ≤ 49c/100`. -/
theorem ra_no_equilibrium_via_general (c : ℝ) (hc : 0 < c)
    (E : (raParams c).FeedbackStackelbergEquilibriumTop) (hα : E.α = niAlpha)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1 / 4) (htm : t ≤ 49 * c / 100) :
    False := by
  have hfix : E.V_S = (raParams c).bellmanS_BCF niAlpha niAlpha_continuous E.V_S := by
    rw [← AbstractGame.Params.bellmanS_BCF_congr_α (raParams c) hα E.hα
      niAlpha_continuous E.V_S]
    exact E.V_S_fix
  have hVS : E.V_S = raV_S c :=
    V_S_unique (raParams c) niAlpha_continuous E.V_S hfix
  have hα1 : E.α 1 = 1 / 2 := by rw [hα]; rfl
  refine Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain
    (raParams c) E c (49 / 100) (t / 2) t hc.le raOne rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y; rw [hVS]; exact raV_S_slope_to_top c hc.le y
  · intro s hs; exact quadBump_top_transition s hs
  · intro s hs
    rw [hα1]
    have h := ra_shade_bound c 0 s hs
    simp only [add_zero] at h
    have hu0 : 0 ≤ 1 - s := by linarith [hs.2]
    nlinarith [h, mul_nonneg ht0.le hu0]
  · intro s hs; rw [hα1]; exact ra_shade_bound c t s hs
  · show (t / 2 : ℝ) ≤ (raParams c).β_S * c * (49 / 100)
    have : (raParams c).β_S = 1 / 2 := rfl
    rw [this]; linarith
  · rw [hα1]; exact ⟨by linarith, by linarith⟩
  · rw [hα1]
    show (raParams c).U_T 1 (1 / 2) 1 < (raParams c).U_T 1 (1 / 2 + t) 1
    show niU_T 1 (1 / 2) 1 < niU_T 1 (1 / 2 + t) 1
    unfold niU_T niIdeal
    nlinarith

/-- **RULE-1 VERDICT FOR ROUTE A (a refutation, not a witness).**
For every `c > 0`, the Route-A economy `raParams c` has **NO** top-selector
feedback Stackelberg equilibrium whose Target policy is the constant `α ≡ 1/2`.

The proof is unconditional on the equilibrium's value functions: the Sender
fixed point at `α ≡ 1/2` is unique (Banach), hence equals the constructed
`raV_S c`, which has slope `≥ c > 0` up to the top state; that pins the Sender
response at the corner `s = 1` on `a ∈ [1/2, 1/2 + 49c/100]`, and the Target's
own ideal sanction `niIdeal 1 a = 9/8 − a/4` falls in `a`, so raising `a` buys
the Target a first-order gain `t/4` at second-order cost `t²`.

It is `ra_no_equilibrium_via_general` at `t = min (49c/100) (1/8)`, so it is a
corollary of the general absorbing-top obstruction
`AbsorbingTop.no_equilibrium_of_slope_and_top_gain`, which holds for every
transition `F`.  Only the witness numbers (the non-affine `quadBumpF`, the
stake `c`) are specific to this economy. -/
theorem ra_no_equilibrium_with_alpha_half (c : ℝ) (hc : 0 < c)
    (E : (raParams c).FeedbackStackelbergEquilibriumTop)
    (hα : E.α = niAlpha) : False :=
  ra_no_equilibrium_via_general c hc E hα (min (49 * c / 100) (1 / 8))
    (lt_min (by linarith) (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num))
    (min_le_left _ _)

/-! ### Non-vacuity / sharpness (Rule 11) -/

/-- **Sharpness at `c = 0`.**  Everything above degenerates exactly at `c = 0`:
the Route-A economy IS the base economy, `V_S ≡ 0`, and `α ≡ 1/2` is restored
as the equilibrium policy.  So the refutation bites precisely on `c > 0`. -/
theorem raParams_zero_eq_niParams : raParams 0 = niParams := by
  have hU : raU_S 0 = niU_S := by
    funext x a s; simp [raU_S]
  unfold raParams niParams
  simp only [hU]

theorem raV_S_zero : raV_S 0 = niV0 := by
  have h : niV0 = (raParams 0).bellmanS_BCF niAlpha niAlpha_continuous niV0 := by
    rw [raParams_zero_eq_niParams]
    exact ni_sender_value_fix
  exact (V_S_unique (raParams 0) niAlpha_continuous niV0 h).symm

/-- The base equilibrium `niEquilibrium` discharges every hypothesis of
`ra_no_equilibrium_with_alpha_half` except `0 < c`. -/
theorem ra_refutation_sharp_at_zero :
    niEquilibrium.α = niAlpha ∧ raV_S 0 = niEquilibrium.V_S := by
  exact ⟨rfl, raV_S_zero⟩

#print axioms ra_no_affine_solution
#print axioms ra_cone_hypothesis_fails
#print axioms raV_S_norm_le
#print axioms raV_S_one
#print axioms raV_S_slope_to_top
#print axioms raV_S_nonconstant
#print axioms corner_pin_of_slope_to_top
#print axioms ra_corner_pin
#print axioms ra_response_strictly_exceeds_static_ideal
#print axioms ra_target_gain_at_one
#print axioms ra_no_equilibrium_with_alpha_half
#print axioms ra_refutation_sharp_at_zero
#print axioms quadBump_top_transition
#print axioms ra_shade_bound
#print axioms ra_no_equilibrium_via_general

end

end SenderStake
end Examples
end Sanctions
