/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.NonAffineMechanismActiveWitness
import Sanctions.Theory.Equilibrium.AbsorbingTopObstruction

/-!
# The Sender continuation channel cannot be switched on at this economy

**Rule-11 refutation (2026-07-28).**  The non-affine mechanism-active witness
`maEquilibrium` has everything a two-sided nonvacuity certificate wants except
one thing: its Sender value `maV_S` is identically zero, so the Sender's
continuation channel moves no sanction and both cross-value rows vanish.

The obvious repair is to give the Sender a stake in the political state — a
state-only stage payoff `g x`, which is exactly the paper's "sanctions are
investments in political power" thesis.  **This file proves that repair
impossible**, for *every* continuous `g`.

## The mechanism, in words

A state-only payoff `g x` is invisible to both of the Sender's argmaxes
(`dynamicArgmaxSet_indep_of_state_payoff`), because it is constant in the
Sender's own action.  Its only channel is the Sender Bellman fixed point: it
acts *solely* by making `V_S` nonconstant.

But at the top state `x = 1` the sanction floor forces the greatest dynamic
Sender response to be exactly `1`, with **zero slack**.  A `V_S` carrying any
uniform positive slope near `1` pins that response at `1` not just at `a = 1/2`
but across a whole right-neighbourhood of it.  The Target's ideal sanction
`niIdeal 1 a = 9/8 - a/4` *falls* in `a`, so raising compliance by `t` buys the
Target a first-order gain `t/4` at only second-order cost `t^2`.  Hence
`a = 1/2` stops being a maximizer, contradicting `α_opt_top` — the
equilibrium's own Target-optimality field.

Economically: **making the Sender's continuation channel behaviourally active
destroys the Target's optimality.**  That is a Rule-1 collision, not a
technical gap.

## Scope, and why this is not vacuous

`gate4_no_increasing_V_S` consumes only `α_opt_top`.  It does *not* touch the
basin, so it stands even if invariance, the floor, and monotone sanctions were
established by some route other than `JointPreferenceBasinTop`.

The refutation is a corollary of the general absorbing-top obstruction
`AbsorbingTop.no_equilibrium_of_slope_and_top_gain`, which holds for every
transition `F`.  `slope_to_top_of_monotone_topSlope` turns `Monotone` plus a
top-segment slope `m` on `[31/32, 1]` into the obstruction's slope-to-the-top
bound with constant `m/32`; the witness then supplies only its own numbers
(`κ = 49/100` for `quadBumpF`, and the shading bound `t/2`).

Non-vacuity is pinned two ways.  `refutation_is_sharp_at_zero_slope` discharges
every hypothesis except `0 < m` from the *existing* `maEquilibrium`, whose
Sender value is `0` and hence has slope exactly `m = 0`.  And
`base_witness_response_is_not_corner_pinned` shows precisely why that witness
survives: its response `1 - t/4` falls in `a` at exactly the rate the Target's
ideal does, so no deviation gain opens up.  The fence bites at `m > 0` and
nowhere else.

## What survives

`ideal_is_top_of_value_maximal_at_successor` is the escape hatch: if `V_S`
attains its maximum at the realized successor state, the static ideal is the
unique dynamic argmax, so `σ_dyn_top` never moves and every proof goes through
with a nonconstant `V_S`.  Such a `V_S` has no uniform positive slope, so it
dodges the refutation — but it is behaviourally inert, its variation sitting in
a dead zone off every equilibrium path.  It satisfies the letter of the target
and none of its economics.

**Consequence.**  An active Sender channel at this economy requires giving up
one of: the interior policy `α ≡ 1/2`; the `x = 1` corner of the sanction
floor; or the `niU_T` form, whose `- niIdeal x a` term is what makes the
Target's ideal fall in `a` and creates the deviation gain in the first place.

No new assumption, parameter field, or carrier condition is introduced here.
`TopSlope` is a local predicate appearing only on the *refuted* side of a
negative result.
-/

namespace Sanctions
namespace Examples

open Set AbstractGame AbstractGame.Params Sanctions.Examples

noncomputable section

/-! ## Q1.  A state-only Sender payoff `g x` is invisible to BOTH argmaxes. -/

/-- Adding a constant to the objective does not move any argmax. -/
theorem isMaxOn_add_const {f : ℝ → ℝ} {c : ℝ} {T : Set ℝ} {t : ℝ} :
    IsMaxOn (fun s => f s + c) T t ↔ IsMaxOn f T t := by
  simp only [isMaxOn_iff]
  constructor <;> intro h s hs <;> have := h s hs <;> linarith

/-- **Q1 answer (static).** For any `(x,a)`, the STATIC Sender argmax set of
`U_S x a · + g x` is literally the static argmax set of `U_S x a ·`. -/
theorem static_argmax_indep_of_state_payoff
    (US : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x a : ℝ) (t : ℝ) :
    IsMaxOn (fun s => US x a s + g x) Sanctions.I t
      ↔ IsMaxOn (fun s => US x a s) Sanctions.I t :=
  isMaxOn_add_const

/-- **Q1 answer (dynamic).** For a FIXED continuation value `V_S`, the DYNAMIC
Sender argmax set of the `g`-perturbed economy equals that of the base economy,
as sets.  So `σ_dyn_top` is literally unchanged.  The state payoff `g` has
*no* direct channel: its only channel is the Bellman fixed point for `V_S`. -/
theorem dynamicArgmaxSet_indep_of_state_payoff
    (p : Params) (g : ℝ → ℝ) (US' : ℝ → ℝ → ℝ → ℝ)
    (hUS : ∀ y b s, US' y b s = p.U_S y b s + g y)
    (V_S : Params.Val) (x a : ℝ) :
    {s | s ∈ Sanctions.I ∧
        IsMaxOn (fun s' => US' x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) Sanctions.I s}
      = p.dynamicArgmaxSet V_S x a := by
  ext s
  simp only [Set.mem_setOf_eq, dynamicArgmaxSet, and_congr_right_iff]
  intro _
  have hfun : (fun s' => US' x a s' + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
      = (fun s' => (p.U_S x a s' + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) + g x) := by
    funext s'; rw [hUS]; ring
  rw [hfun]
  exact isMaxOn_add_const

/-! ## The concrete `g`-perturbed economy (Rule-3: only the authorized
Sender state payoff is added). -/

/-- Perturbed Sender stage payoff: `niU_S` plus a state-only term. -/
def gU_S (g : ℝ → ℝ) (x a s : ℝ) : ℝ := niU_S x a s + g x

theorem gU_S_isMaxOn (g : ℝ → ℝ) (x a : ℝ) :
    IsMaxOn (fun s => gU_S g x a s) Sanctions.I (niSigma x a) := by
  have := niSigma_isMaxOn x a
  exact isMaxOn_add_const.mpr this

/-- The `g`-perturbed economy: identical to `niParams` except that the Sender
stage payoff carries the extra state term `g x`. -/
def gParams (g : ℝ → ℝ) (hg : Continuous g) : AbstractGame.Params where
  δ := niParams.δ
  δ_mem := niParams.δ_mem
  β_T := niParams.β_T
  β_T_mem := niParams.β_T_mem
  β_S := niParams.β_S
  β_S_mem := niParams.β_S_mem
  U_T := niU_T
  U_S := gU_S g
  σ := niSigma
  σ_mem := niSigma_mem
  σ_isMaxOn_U_S := gU_S_isMaxOn g
  U_T_continuous := niU_T_continuous
  U_S_continuous := by
    unfold gU_S niU_S niIdeal
    exact ((by fun_prop : Continuous
      (fun xas : ℝ × ℝ × ℝ => -(xas.2.2 - (xas.1 / 2 + 5 / 8 - xas.2.1 / 4)) ^ 2)).add
      (hg.comp continuous_fst))
  F := niParams.F
  F_continuous := niParams.F_continuous
  F_mono_x := niParams.F_mono_x
  F_mono_s := niParams.F_mono_s
  F_diag := niParams.F_diag

/-- **`gParams` has a continuous static Sender selector.** A family with `niParams`'s
non-affine transition `quadBumpF`; the selector `niSigma` does not read the transition.
The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance gParams_staticSelectorContinuous (g : ℝ → ℝ) (hg : Continuous g) :
    (gParams g hg).StaticSelectorContinuous where
  σ_continuous := niSigma_continuous

@[simp] theorem gParams_β_S (g hg) : (gParams g hg).β_S = 1 / 2 := rfl
@[simp] theorem gParams_F (g hg) : (gParams g hg).F = quadBumpF := rfl
@[simp] theorem gParams_U_T (g hg) : (gParams g hg).U_T = niU_T := rfl
@[simp] theorem gParams_U_S (g hg) : (gParams g hg).U_S = gU_S g := rfl

/-- **Q1, concrete.** `σ_dyn_top` in the perturbed economy is definitionally the
`σ_dyn_top` of the base economy, at every `(x, a)` and every `V_S`. -/
theorem gParams_σ_dyn_top_eq (g : ℝ → ℝ) (hg : Continuous g)
    (V_S : Params.Val) (x a : ℝ) :
    (gParams g hg).σ_dyn_top V_S x a = niParams.σ_dyn_top V_S x a := by
  unfold AbstractGame.Params.σ_dyn_top
  congr 1
  exact dynamicArgmaxSet_indep_of_state_payoff niParams g (gU_S g)
    (fun _ _ _ => rfl) V_S x a

/-! ## Q2 / Q3.  The `x = 1` corner pin.

If `V_S` is increasing with a *uniform* positive lower slope `m`, then at the
top state `x = 1` the Sender's greatest dynamic response is pinned at the corner
`s = 1` not just at `a = 1/2` but on a whole right-neighbourhood `a ∈ [1/2, 1/2+t]`.
The Target's ideal sanction `niIdeal 1 a` strictly *falls* in `a`, so raising `a`
buys the Target a first-order gain `t/4` at only second-order cost `t²`. -/

/-- Positive lower slope of a value function, required only on the TOP segment
`[lo, 1]` of the state space. -/
def TopSlope (V : Params.Val) (m lo : ℝ) : Prop :=
  ∀ y y' : ↥(Sanctions.S : Set ℝ), lo ≤ y.val → y.val ≤ y'.val →
    m * (y'.val - y.val) ≤ V y' - V y

/-- **Monotone plus a top-segment slope gives a slope to the top state.**
If `V` is nondecreasing and rises at rate at least `m` on the top segment
`[lo, 1]`, then from *every* state `y` the value rises to the top state at rate
at least `m·(1 - lo)`: `m·(1 - lo)·(1 - y) ≤ V 1 - V y`.  On the segment this is
the slope bound itself (the factor `1 - lo ≤ 1` only weakens it); below it,
monotonicity gives `V y ≤ V lo`, and the segment already rises by `m·(1 - lo)`.
No sign condition on `m` is assumed: for `m < 0` the left side is nonpositive and
monotonicity alone makes the right side nonnegative.

This is the bridge from the gate's hypotheses (`Monotone` and `TopSlope`) to the
slope-to-the-top hypothesis of the general absorbing-top obstruction.  It is a
statement about value functions alone: no transition, payoff or equilibrium
enters, so it is general in `F`.  The two hypothesis bundles are incomparable at
the same rate `m`; this lemma shows the gate's bundle implies the obstruction's
at the smaller rate `m·(1 - lo)`. -/
theorem slope_to_top_of_monotone_topSlope (V : Params.Val) {m lo : ℝ}
    (hlo : lo ∈ Sanctions.S) (hmono : Monotone V)
    (hslope : TopSlope V m lo)
    (one : ↥(Sanctions.S : Set ℝ)) (hone : one.val = 1) :
    ∀ y : ↥(Sanctions.S : Set ℝ), m * (1 - lo) * (1 - y.val) ≤ V one - V y := by
  intro y
  have hy0 : 0 ≤ y.val := y.property.1
  have hy1 : y.val ≤ 1 := y.property.2
  have hlo0 : 0 ≤ lo := hlo.1
  have hlo1 : lo ≤ 1 := hlo.2
  rcases lt_or_ge m 0 with hneg | hm
  · -- A negative rate: the left side is `≤ 0`, and `V y ≤ V 1` by monotonicity.
    have hyle : y.val ≤ one.val := by rw [hone]; exact hy1
    have hmon : V y ≤ V one := hmono (Subtype.coe_le_coe.mp hyle)
    have hpos : 0 ≤ (1 - lo) * (1 - y.val) := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg (neg_nonneg.mpr hneg.le) hpos]
  · rcases le_or_gt lo y.val with hly | hly
    · -- On the top segment: the slope bound itself, weakened by `1 - lo ≤ 1`.
      have h := hslope y one hly (by rw [hone]; exact hy1)
      rw [hone] at h
      have hw : 0 ≤ m * (1 - y.val) := mul_nonneg hm (by linarith)
      nlinarith [mul_nonneg hw hlo0]
    · -- Below the segment: monotonicity down to `lo`, then the slope on `[lo, 1]`.
      let l : ↥(Sanctions.S : Set ℝ) := ⟨lo, hlo⟩
      have h := hslope l one le_rfl (by rw [hone]; exact hlo1)
      rw [hone] at h
      have hmon : V y ≤ V l := hmono (Subtype.coe_le_coe.mp hly.le)
      have hw : 0 ≤ m * (1 - lo) := mul_nonneg hm (by linarith)
      have hl : (l : ℝ) = lo := rfl
      rw [hl] at h
      nlinarith [mul_nonneg hw hy0]

/-- **Corner pin.**  If `V_S` is nondecreasing and has slope at least `m > 0`
on the top segment `[31/32, 1]`, then at `x = 1` the greatest dynamic Sender
response equals `1` for every `a ∈ [1/2, 1/2 + t]` with
`t ≤ min (49m/100) (1/8)`.

Only `V_S`'s behaviour on `[31/32, 1]` and its global monotonicity are used.
The refutation below does not use this lemma (it goes through the general
absorbing-top obstruction, at the smaller neighbourhood `t ≤ 49m/3200`); the
lemma records the sharper neighbourhood `t ≤ 49m/100`. -/
theorem corner_pin_of_slope
    (p : Params) (hβS : p.β_S = 1 / 2) (hF : p.F = quadBumpF)
    (g1 : ℝ) (hUS : ∀ a s, p.U_S 1 a s = niU_S 1 a s + g1)
    (V_S : Params.Val) (m : ℝ) (hm : 0 < m)
    (hmono : Monotone V_S) (hslope : TopSlope V_S m (31 / 32))
    (t : ℝ) (ht0 : 0 ≤ t) (htm : t ≤ 49 * m / 100) (ht8 : t ≤ 1 / 8) :
    p.σ_dyn_top V_S 1 (1 / 2 + t) = 1 := by
  have hone : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl _⟩
  -- `1` is a dynamic maximizer at `(x, a) = (1, 1/2 + t)`.
  have hmax : IsMaxOn (fun s' => p.U_S 1 (1 / 2 + t) s'
      + p.β_S * V_S (Sanctions.clipS' (p.F 1 s'))) Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rw [hUS, hUS, hβS, hF]
    have hqb1 : quadBumpF 1 1 = 1 := by rw [quadBumpF_one]; norm_num
    have hqbs : quadBumpF 1 s = 1 / 2 * 1 + 1 / 2 * s + 1 / 100 * (s - 1) ^ 2 * (1 - s) :=
      quadBumpF_sq hone hs
    have hqbmem : quadBumpF 1 s ∈ Set.Icc (0 : ℝ) 1 := quadBumpF_mem 1 s hone hs
    have hv1 : (Sanctions.clipS' (1 : ℝ)).val = 1 :=
      Sanctions.clipS'_val_eq_of_mem hone
    have hvs : (Sanctions.clipS' (quadBumpF 1 s)).val = quadBumpF 1 s :=
      Sanctions.clipS'_val_eq_of_mem hqbmem
    have hclipLe : Sanctions.clipS' (quadBumpF 1 s) ≤ Sanctions.clipS' (1 : ℝ) :=
      Sanctions.clipS'_mono hqbmem.2
    have hmono' : V_S (Sanctions.clipS' (quadBumpF 1 s))
        ≤ V_S (Sanctions.clipS' (1 : ℝ)) := hmono hclipLe
    rw [hqb1]
    unfold niU_S niIdeal
    have hu0 : 0 ≤ 1 - s := by linarith [hs.2]
    have hu1 : 1 - s ≤ 1 := by linarith [hs.1]
    have hcube : (1 - s) ^ 3 ≤ (1 - s) := by nlinarith [hu0, hu1]
    rcases le_or_gt (t / 2) (1 - s) with hbig | hsmall
    · -- Far from the corner: the quadratic stage loss alone dominates.
      nlinarith [hmono', hu0, hbig]
    · -- Near the corner: use the top-segment slope bound.
      have hqlow : (31 : ℝ) / 32 ≤ quadBumpF 1 s := by
        rw [hqbs]
        nlinarith [hu0, hcube, hsmall, ht8,
          mul_nonneg (sq_nonneg (s - 1)) hu0]
      have hslope' : m * (1 - quadBumpF 1 s)
          ≤ V_S (Sanctions.clipS' (1 : ℝ))
            - V_S (Sanctions.clipS' (quadBumpF 1 s)) := by
        have := hslope (Sanctions.clipS' (quadBumpF 1 s)) (Sanctions.clipS' (1 : ℝ))
          (by rw [hvs]; exact hqlow) (by rw [hv1, hvs]; exact hqbmem.2)
        rw [hv1, hvs] at this
        exact this
      have hlow : 49 * m / 100 * (1 - s) ≤ m * (1 - quadBumpF 1 s) := by
        rw [hqbs]; nlinarith [hm.le, hu0, hcube]
      nlinarith [hslope', hlow, hu0, sq_nonneg (1 - s), hm.le,
        mul_nonneg ht0 hu0]
  have hmem : (1 : ℝ) ∈ p.dynamicArgmaxSet V_S 1 (1 / 2 + t) := ⟨hone, hmax⟩
  refine le_antisymm ?_ ?_
  · exact csSup_le ⟨1, hmem⟩ (fun b hb => hb.1.2)
  · exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S 1 (1 / 2 + t)) hmem

/-- **Target deviation at the top state.**  Whenever the Sender's greatest
dynamic response is pinned at `1` both at `a = 1/2` and at `a = 1/2 + t`
for some `t ∈ (0, 1/4)`, the Target policy `a = 1/2` is NOT Bellman-optimal
at `x = 1`.  The `V_T` continuation term cancels exactly (same successor
state), so this holds for EVERY `V_T`.

It is an instance of the general deviation half
`AbsorbingTop.target_deviation_of_pinned` (no hypothesis on `F`), fed the
witness's stage gain `niU_T 1 (1/2 + t) 1 - niU_T 1 (1/2) 1 = t/4 - t^2 > 0`. -/
theorem target_deviation_at_one
    (p : Params) (c : ℝ) (hUT : ∀ a, p.U_T 1 a 1 = niU_T 1 a 1 + c)
    (V_T V_S : Params.Val) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1 / 4)
    (h0 : p.σ_dyn_top V_S 1 (1 / 2) = 1)
    (ht : p.σ_dyn_top V_S 1 (1 / 2 + t) = 1) :
    ¬ IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S 1 a)
        Sanctions.I (1 / 2) := by
  have hdev : (1 / 2 + t) ∈ Sanctions.I := ⟨by linarith, by linarith⟩
  refine AbsorbingTop.target_deviation_of_pinned p V_T V_S (1 / 2) (1 / 2 + t) hdev h0 ht ?_
  rw [hUT, hUT]
  unfold niU_T niIdeal
  nlinarith [mul_pos ht0 (by linarith : (0 : ℝ) < 1 / 4 - t)]

/-- **Top-state responsiveness of `quadBumpF`.**  Shading the sanction below
the corner by `1 - s` pushes the successor of the top state down by at least
`(49/100)·(1 - s)`.  Witness-specific: this is a fact about the non-affine
transition `quadBumpF` only, and it is the `κ = 49/100` input of the general
absorbing-top obstruction. -/
theorem quadBumpF_top_transition (s : ℝ) (hs : s ∈ Sanctions.I) :
    (49 / 100 : ℝ) * (1 - s) ≤ 1 - quadBumpF 1 s := by
  have honeI : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hqbs : quadBumpF 1 s
      = 1 / 2 * 1 + 1 / 2 * s + 1 / 100 * (s - 1) ^ 2 * (1 - s) :=
    quadBumpF_sq honeI hs
  have hu0 : 0 ≤ 1 - s := by linarith [hs.2]
  have hu1 : 1 - s ≤ 1 := by linarith [hs.1]
  have hcube : (1 - s) ^ 3 ≤ 1 - s := by nlinarith
  rw [hqbs]; nlinarith

/-- **Static shading bound at the top state.**  At Target action `1/2 + t`, the
Sender's static gain from shading the sanction from `1` down to `s` is at most
`(t/2)·(1 - s)`: the exact difference is `(t/2)·(1 - s) - (1 - s)^2`.  A
statement about the payoff `niU_S` alone (no transition enters), and it holds
for every real `s` and `t`. -/
theorem niU_S_top_shade (t s : ℝ) :
    niU_S 1 (1 / 2 + t) s - niU_S 1 (1 / 2 + t) 1 ≤ (t / 2) * (1 - s) := by
  unfold niU_S niIdeal
  nlinarith [sq_nonneg (1 - s)]

/-! ## The refutation. -/

/-- **REFUTATION (Rule 11).**  There is NO Gate-4 witness whose Sender value has
a uniform positive lower slope.

Take any economy `p` that (i) keeps the base discount `β_S = 1/2` and the
nonlinear transition `quadBumpF`, (ii) whose Sender stage payoff at the top
state is `niU_S` plus a state-only constant `g1` (this is exactly the authorized
"add a Sender state payoff `g x`" perturbation — evaluated at `x = 1`), and
(iii) whose Target stage payoff at `(1, ·, 1)` is `niU_T` plus a constant `c`
(satisfied by BOTH `niU_T` with `c = 0` and `maU_T` with `c = 1/10`).

If such a `p` has a `FeedbackStackelbergEquilibriumTop` with the SAME interior
Target policy `α ≡ 1/2`, then its Sender value `V_S` cannot have any uniform
positive lower slope.

It is a corollary of the general absorbing-top obstruction
`AbsorbingTop.no_equilibrium_of_slope_and_top_gain` (general in `F`),
instantiated with slope `m/32` (from `slope_to_top_of_monotone_topSlope`
at `lo = 31/32`), top responsiveness `κ = 49/100` (`quadBumpF_top_transition`),
shading bound `t/2` (`niU_S_top_shade`) and `t = min (49m/3200) (1/8)`.  Only
the witness numbers are specific to the non-affine economy `quadBumpF`. -/
theorem no_uniformly_increasing_sender_value
    (p : Params) (hβS : p.β_S = 1 / 2) (hF : p.F = quadBumpF)
    (g1 c : ℝ)
    (hUS : ∀ a s, p.U_S 1 a s = niU_S 1 a s + g1)
    (hUT : ∀ a, p.U_T 1 a 1 = niU_T 1 a 1 + c)
    (E : p.FeedbackStackelbergEquilibriumTop) (hα : E.α = niAlpha)
    (m : ℝ) (hm : 0 < m) (hmono : Monotone E.V_S)
    (hslope : TopSlope E.V_S m (31 / 32)) : False := by
  set t : ℝ := min (49 * m / 3200) (1 / 8) with ht_def
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have htm : t ≤ 49 * m / 3200 := min_le_left _ _
  have ht18 : t ≤ 1 / 8 := min_le_right _ _
  have hα1 : E.α 1 = 1 / 2 := by rw [hα]; rfl
  refine AbsorbingTop.no_equilibrium_of_slope_and_top_gain p E (m / 32) (49 / 100) (t / 2) t
    (by positivity) ⟨1, ⟨by norm_num, le_refl _⟩⟩ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- slope to the top at rate `m/32`, from `Monotone` and the slope on `[31/32, 1]`
    intro y
    have h := slope_to_top_of_monotone_topSlope E.V_S
      (show (31 / 32 : ℝ) ∈ Sanctions.S by constructor <;> norm_num) hmono hslope
      ⟨1, ⟨by norm_num, le_refl _⟩⟩ rfl y
    have hc : m / 32 * (1 - y.val) = m * (1 - 31 / 32) * (1 - y.val) := by ring
    rw [hc]
    exact h
  · -- top responsiveness `κ = 49/100` of `quadBumpF`
    intro s hs
    rw [hF]
    exact quadBumpF_top_transition s hs
  · -- shading bound at `a = 1/2`
    intro s hs
    rw [hα1, hUS, hUS]
    have h := niU_S_top_shade 0 s
    rw [add_zero] at h
    have hu0 : 0 ≤ 1 - s := by linarith [hs.2]
    nlinarith [h, mul_nonneg ht0.le hu0]
  · -- shading bound at `a = 1/2 + t`
    intro s hs
    rw [hα1, hUS, hUS]
    have h := niU_S_top_shade t s
    linarith
  · -- binding condition `t/2 ≤ β_S · (m/32) · (49/100)`
    rw [hβS]
    linarith
  · -- the deviation `1/2 + t` is feasible
    rw [hα1]
    exact ⟨by linarith, by linarith⟩
  · -- the Target's stage gain at the corner sanction: `t/4 - t^2 > 0`
    rw [hα1, hUT, hUT]
    unfold niU_T niIdeal
    nlinarith [mul_pos ht0 (by linarith : (0 : ℝ) < 1 / 4 - t)]

/-! ## The refutation applies to the two existing base economies. -/

/-- `niParams`: `hUS` holds with `g1 = 0`, `hUT` with `c = 0`. -/
theorem niParams_hyps :
    niParams.β_S = 1 / 2 ∧ niParams.F = quadBumpF
    ∧ (∀ a s, niParams.U_S 1 a s = niU_S 1 a s + 0)
    ∧ (∀ a, niParams.U_T 1 a 1 = niU_T 1 a 1 + 0) :=
  ⟨rfl, rfl, fun _ _ => by simp, fun _ => by simp⟩

/-- `maParams`: same Sender primitives (`g1 = 0`); the Target stage payoff
differs at `(1, ·, 1)` only by the constant `c = 1/10`. -/
theorem maParams_hyps :
    maParams.β_S = 1 / 2 ∧ maParams.F = quadBumpF
    ∧ (∀ a s, maParams.U_S 1 a s = niU_S 1 a s + 0)
    ∧ (∀ a, maParams.U_T 1 a 1 = niU_T 1 a 1 + 1 / 10) := by
  refine ⟨rfl, rfl, fun _ _ => by simp [maParams], fun a => ?_⟩
  show maU_T 1 a 1 = niU_T 1 a 1 + 1 / 10
  unfold maU_T
  rw [quadBumpF_one]
  norm_num [Sanctions.clipS]
  ring

/-- The perturbed economy `gParams g hg` also satisfies the hypotheses, with
`g1 = g 1` and `c = 0`.  So the refutation covers exactly the authorized
Gate-4 perturbation class. -/
theorem gParams_hyps (g : ℝ → ℝ) (hg : Continuous g) :
    (gParams g hg).β_S = 1 / 2 ∧ (gParams g hg).F = quadBumpF
    ∧ (∀ a s, (gParams g hg).U_S 1 a s = niU_S 1 a s + g 1)
    ∧ (∀ a, (gParams g hg).U_T 1 a 1 = niU_T 1 a 1 + 0) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => by simp⟩

/-- **The Gate-4 refutation, specialised to the authorized perturbation.**
No continuous Sender state payoff `g` produces a top-selector Stackelberg
equilibrium with `α ≡ 1/2` and a uniformly-increasing Sender value. -/
theorem gate4_no_increasing_V_S
    (g : ℝ → ℝ) (hg : Continuous g)
    (E : (gParams g hg).FeedbackStackelbergEquilibriumTop) (hα : E.α = niAlpha)
    (m : ℝ) (hm : 0 < m) (hmono : Monotone E.V_S)
    (hslope : TopSlope E.V_S m (31 / 32)) : False :=
  no_uniformly_increasing_sender_value (gParams g hg) rfl rfl (g 1) 0
    (fun _ _ => rfl) (fun _ => by simp) E hα m hm hmono hslope

/-! ## The ESCAPE HATCH: why this is not a TOTAL refutation.

A `V_S` that is nonconstant but attains its maximum on the whole set of
*realized successor states* leaves `σ_dyn_top` exactly at the static ideal.
Every `ni` / `ma` proof then goes through verbatim, with a nonconstant `V_S`.
Such a `V_S` has NO uniform positive slope, so it dodges the refutation above —
but it is also behaviourally inert (the Sender continuation channel does not
move a single sanction). -/

/-- **Escape hatch.**  If `V_S` is maximized at the successor state of the
static ideal, the static ideal is the UNIQUE dynamic argmax, hence
`σ_dyn_top = niIdeal x a` exactly as in the unperturbed economy. -/
theorem ideal_is_top_of_value_maximal_at_successor
    (p : Params) (V_S : Params.Val) (x a g1 : ℝ)
    (hUS : ∀ b s, p.U_S x b s = niU_S x b s + g1)
    (hideal : niIdeal x a ∈ Sanctions.I)
    (hmaxV : ∀ y : ↥(Sanctions.S : Set ℝ),
      V_S y ≤ V_S (Sanctions.clipS' (p.F x (niIdeal x a)))) :
    p.σ_dyn_top V_S x a = niIdeal x a := by
  have hβ : 0 ≤ p.β_S := p.β_S_mem.1
  have hmax : IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) Sanctions.I (niIdeal x a) := by
    rw [isMaxOn_iff]
    intro s hs
    rw [hUS, hUS]
    unfold niU_S
    have hV := mul_le_mul_of_nonneg_left
      (hmaxV (Sanctions.clipS' (p.F x s))) hβ
    nlinarith [sq_nonneg (s - niIdeal x a), hV]
  have hmem : niIdeal x a ∈ p.dynamicArgmaxSet V_S x a := ⟨hideal, hmax⟩
  refine le_antisymm ?_ (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a) hmem)
  refine csSup_le ⟨_, hmem⟩ ?_
  rintro b ⟨hbI, hbmax⟩
  by_contra hlt
  rw [not_le] at hlt
  have h : p.U_S x a (niIdeal x a)
      + p.β_S * V_S (Sanctions.clipS' (p.F x (niIdeal x a)))
      ≤ p.U_S x a b + p.β_S * V_S (Sanctions.clipS' (p.F x b)) := hbmax hideal
  rw [hUS, hUS] at h
  unfold niU_S at h
  have hV := mul_le_mul_of_nonneg_left
    (hmaxV (Sanctions.clipS' (p.F x b))) hβ
  nlinarith [h, hV, hlt]

/-- The infimum of the realized successor states `F(x, niIdeal x a)` over the
feasible square is `9645/51200 ≈ 0.18838` (attained at `x = 0`, `a = 1`).  So a
`V_S` bump confined to `[0, 9645/51200)` is invisible to every on-path decision:
that is the whole corridor left open by the refutation. -/
theorem successor_of_ideal_lower_bound :
    quadBumpF 0 (niIdeal 0 1) = 9645 / 51200 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hI : niIdeal 0 1 = 3 / 8 := by unfold niIdeal; norm_num
  rw [hI, quadBumpF_sq h0 ⟨by norm_num, by norm_num⟩]
  norm_num

/-! ## Rule-11 non-vacuity: the fence is sharp at `m = 0`. -/

/-- **Sharpness.** EVERY hypothesis of `no_uniformly_increasing_sender_value`
except `0 < m` is discharged by the EXISTING `maEquilibrium` witness (whose
Sender value is the zero function, i.e. slope exactly `m = 0`).  So the
refutation is not vacuous and not over-strong: it bites precisely on `m > 0`. -/
theorem refutation_is_sharp_at_zero_slope :
    maParams.β_S = 1 / 2
    ∧ maParams.F = quadBumpF
    ∧ (∀ a s, maParams.U_S 1 a s = niU_S 1 a s + 0)
    ∧ (∀ a, maParams.U_T 1 a 1 = niU_T 1 a 1 + 1 / 10)
    ∧ maEquilibrium.α = niAlpha
    ∧ Monotone maEquilibrium.V_S
    ∧ TopSlope maEquilibrium.V_S 0 (31 / 32) := by
  obtain ⟨h1, h2, h3, h4⟩ := maParams_hyps
  refine ⟨h1, h2, h3, h4, rfl, ?_, ?_⟩
  · intro y y' _
    simp [maEquilibrium, maV_S, niV0]
  · intro y y' _ _
    simp [maEquilibrium, maV_S, niV0]

/-- **Why the base witness escapes.**  At `maEquilibrium` the Sender response is
NOT corner-pinned off `a = 1/2`: it tracks the static ideal `1 - t/4`, which
falls exactly as fast as the Target's ideal.  That is the precise mechanism the
`m > 0` perturbation destroys. -/
theorem base_witness_response_is_not_corner_pinned
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 4) :
    maParams.σ_dyn_top maV_S 1 (1 / 2 + t) = 1 - t / 4 := by
  have hmem : niIdeal 1 (1 / 2 + t) ∈ Sanctions.I := by
    constructor <;> · unfold niIdeal; linarith
  rw [ma_sigma_dyn_top_eq, ni_top_eq_ideal_of_mem hmem]
  unfold niIdeal
  ring

#print axioms refutation_is_sharp_at_zero_slope
#print axioms base_witness_response_is_not_corner_pinned
#print axioms corner_pin_of_slope
#print axioms slope_to_top_of_monotone_topSlope
#print axioms quadBumpF_top_transition
#print axioms niU_S_top_shade
#print axioms target_deviation_at_one
#print axioms no_uniformly_increasing_sender_value
#print axioms gate4_no_increasing_V_S
#print axioms gParams_σ_dyn_top_eq
#print axioms ideal_is_top_of_value_maximal_at_successor

end

end Examples
end Sanctions
