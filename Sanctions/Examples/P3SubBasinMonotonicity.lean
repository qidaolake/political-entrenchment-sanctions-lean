/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.P3WeakFloorSpreadBound
import Sanctions.Theory.LockIn.SubintervalLockIn

/-!
# P3 does ratchet --- on a sub-basin ending at its steady state

The full-width `P₃` economy cannot satisfy the strong ratchet floor on any basin
reaching the top state: its top sanction is interior for every equilibrium
(`mwShockedOne_no_top_floor`), and `no_upper_basin_floor_of_top_lt_one` then
closes that route universally.  It was natural to conclude that a monotone
sanction path is unavailable there.  **That conclusion was wrong**, and this file
settles the question.

## The positive result

For the constructed equilibrium `mwEqEquilibrium`, the interval
`[a, mwEqFixedState]` carries *both* the ratchet and forward invariance for every
`2/5 ≤ a`, and the resulting paths are **strictly** increasing --- the direct
slope `9/8` strictly beats the indirect slope through the Target's best response,
so the ratchet never stalls.  In the cleanest form, with entirely rational data
in the hypotheses:

`p3_monotone_sanctions_from_rational_start` --- from any start
`x₀ ∈ [2/5, 1129/2000]`, the state path and the realised sanction path are both
`StrictMono`, forever.

So sanctions *do* ratchet at `P₃`.  What fails is only the extension of that
ratchet to the ceiling --- which is exactly what the absorbing-boundary dichotomy
predicts, and not a defect of the construction.

## Why the endpoint is where it is

`dynamicTopLockIn_subinterval_forces_fixed_endpoint` (in
`Theory/LockIn/SubintervalLockIn`) shows the right endpoint of any working
interval must be a fixed point of the realised rule.  Here that fixed point is
`mwEqFixedState`, and the gap `R(x) - x` is affine and strictly decreasing
(`mwEq_gap_identity`), so it is *unique*.  It is bracketed in exact rationals,
`1129/2000 < mwEqFixedState < 2823/5000`, from the IVT-proved spread window
alone --- no numerical input.

## The endpoint is irrational, and what that does and does not settle

`mwEqFixedState_irrational` shows the endpoint is not rational.  The route avoids
quartic irreducibility: a rational endpoint would force the spread to satisfy a
rational quadratic as well as the quartic, and dividing one by the other leaves a
remainder whose linear coefficient is a nonzero constant, so the spread would be
rational outright --- excluded by a rational-root argument on denominators
dividing the leading coefficient.

Read the consequence carefully.  `p3_no_rational_ratchet_invariant_subinterval`
refutes the existence of a rational-endpoint interval carried by **every**
equilibrium; it is discharged by one instantiation at the constructed
equilibrium.  It does **not** show that no equilibrium whatsoever has a
rational-endpoint sub-basin.  Since the project's persistence conclusion is
*existential* in the equilibrium, the ∀E-orientation is not the form the
economics turns on --- the load-bearing statement here is the positive one.

## Scope

The positive results are about `mwEqEquilibrium`, the one explicitly constructed
`P₃` equilibrium; there is no uniqueness theorem for that economy, so they are not
claimed for an arbitrary equilibrium.  No pointwise interior bound on the Target
policy was assumed --- none was needed, because the constructed equilibrium's
policy is explicit and argmax-certified --- and the absence of such a bound in
the tree remains a genuine open gap for arbitrary equilibria.

Every constant in every statement is an exact rational.  Decimals appear only in
docstrings, as orientation.
-/

namespace Sanctions

open Set BoundedContinuousFunction

namespace Examples

open AbstractGame

noncomputable section

/-! ## PART 2 — THE EXACT P3 STEADY STATE

`mwEqEquilibrium` (`Examples/MechanismWitnessShockedUnconditional.lean`) is the
explicitly constructed full-width P3 shocked equilibrium; both strategies are proved
optimizers (`α_opt_shock`; the Sender plays `σ_dyn_top`), so Rule 1 is met.  Its
realized rule is affine in the state off the clips, with one unknown scalar
`S = mwEqSenderSpread` (a root of `mwEqQuartic`).  Hence `s − id` is affine and
STRICTLY DECREASING, so it has exactly one zero — `mwEqFixedState`. -/

/-- **The P3 steady state**, exactly: the unique state at which the constructed
equilibrium's realized sanction rule equals the state itself. -/
def mwEqFixedState : ℝ :=
  (-9 * mwEqSenderSpread ^ 2 + 10340 * mwEqSenderSpread - 9357) / 15686

theorem mwEqFixedState_spec :
    15686 * mwEqFixedState
      = -9 * mwEqSenderSpread ^ 2 + 10340 * mwEqSenderSpread - 9357 := by
  unfold mwEqFixedState; ring

/-- The steady state is bracketed by rationals: `0.5645 < x* < 0.5646`.
Derived from the proved spread window `S ∈ [441/250, 17641/10000]` alone. -/
theorem mwEqFixedState_bracket :
    (1129 / 2000 : ℝ) < mwEqFixedState ∧ mwEqFixedState < 2823 / 5000 := by
  obtain ⟨hlo, hhi⟩ := mwEqSenderSpread_bounds
  have hspec := mwEqFixedState_spec
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  · nlinarith [sq_nonneg (mwEqSenderSpread - 441 / 250)]

theorem mwEqFixedState_mem_S : mwEqFixedState ∈ Sanctions.S := by
  have := mwEqFixedState_bracket
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Off the lower `α`-clip, the gap `s(x) − x` is affine with strictly negative slope
and vanishes exactly at `mwEqFixedState`. -/
theorem mwEq_gap_identity {x : ℝ} (hnc : 0 ≤ mwEqLeaderVertex x) :
    64032 * (mwEqSenderVertex x (mwEqLeaderPolicy x) - x)
      = 15686 * (mwEqFixedState - x) := by
  have hspec := mwEqFixedState_spec
  have hraw : 64032 * (mwEqSenderVertex x (mwEqLeaderPolicy x) - x)
      = -9 * mwEqSenderSpread ^ 2 + 10340 * mwEqSenderSpread - 15686 * x - 9357 := by
    unfold mwEqLeaderPolicy
    rw [max_eq_right hnc]
    unfold mwEqSenderVertex mwEqLeaderVertex mwEqTargetSpread
    ring
  linarith

/-- Above `0.5645` the Target's unconstrained best response is interior, so the `α`
lower clip is inactive. -/
theorem mwEqLeaderVertex_nonneg_of_ge {x : ℝ} (hx : 1129 / 2000 ≤ x) :
    0 ≤ mwEqLeaderVertex x := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  unfold mwEqLeaderVertex
  linarith

/-! ### The sign facts on the Sender vertex -/

theorem mwEq_vertex_ge_state_of_le_fixed {x : ℝ}
    (hx0 : 2 / 5 ≤ x) (hle : x ≤ mwEqFixedState) :
    x ≤ mwEqSenderVertex x (mwEqLeaderPolicy x) := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  by_cases hnc : 0 ≤ mwEqLeaderVertex x
  · have := mwEq_gap_identity hnc; linarith
  · rw [not_le] at hnc
    unfold mwEqLeaderPolicy
    rw [max_eq_left hnc.le]
    unfold mwEqSenderVertex
    linarith

theorem mwEq_vertex_gt_state_of_lt_fixed {x : ℝ}
    (hx0 : 2 / 5 ≤ x) (hlt : x < mwEqFixedState) :
    x < mwEqSenderVertex x (mwEqLeaderPolicy x) := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  by_cases hnc : 0 ≤ mwEqLeaderVertex x
  · have := mwEq_gap_identity hnc; linarith
  · rw [not_le] at hnc
    unfold mwEqLeaderPolicy
    rw [max_eq_left hnc.le]
    unfold mwEqSenderVertex
    linarith

theorem mwEq_vertex_lt_state_of_gt_fixed {x : ℝ} (hgt : mwEqFixedState < x) :
    mwEqSenderVertex x (mwEqLeaderPolicy x) < x := by
  have hbr := mwEqFixedState_bracket
  have hnc : 0 ≤ mwEqLeaderVertex x :=
    mwEqLeaderVertex_nonneg_of_ge (by linarith [hbr.1])
  have := mwEq_gap_identity hnc; linarith

theorem mwEq_vertex_eq_at_fixed :
    mwEqSenderVertex mwEqFixedState (mwEqLeaderPolicy mwEqFixedState)
      = mwEqFixedState := by
  have hbr := mwEqFixedState_bracket
  have hnc : 0 ≤ mwEqLeaderVertex mwEqFixedState :=
    mwEqLeaderVertex_nonneg_of_ge (le_of_lt hbr.1)
  have := mwEq_gap_identity hnc; linarith

/-! ### … lifted through the clips to the realized equilibrium rule -/

theorem mwEq_rule_ge_self_of_le_fixed {x : ℝ}
    (hx0 : 2 / 5 ≤ x) (hle : x ≤ mwEqFixedState) :
    x ≤ mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x := by
  have hbr := mwEqFixedState_bracket
  have hxS : x ∈ Sanctions.S := ⟨by linarith, by linarith [hbr.2]⟩
  rw [mwEqDynamicTopRealizedRule_eq hxS]
  unfold mwEqSenderRule
  exact le_trans (le_min (by linarith [hbr.2])
    (mwEq_vertex_ge_state_of_le_fixed hx0 hle)) (le_max_right _ _)

theorem mwEq_rule_gt_self_of_lt_fixed {x : ℝ}
    (hx0 : 2 / 5 ≤ x) (hlt : x < mwEqFixedState) :
    x < mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x := by
  have hbr := mwEqFixedState_bracket
  have hxS : x ∈ Sanctions.S := ⟨by linarith, by linarith [hbr.2]⟩
  rw [mwEqDynamicTopRealizedRule_eq hxS]
  unfold mwEqSenderRule
  exact lt_of_lt_of_le (lt_min (by linarith [hbr.2])
    (mwEq_vertex_gt_state_of_lt_fixed hx0 hlt)) (le_max_right _ _)

theorem mwEq_rule_lt_self_of_gt_fixed {x : ℝ}
    (hgt : mwEqFixedState < x) (hx1 : x ≤ 1) :
    mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x < x := by
  have hbr := mwEqFixedState_bracket
  have hxS : x ∈ Sanctions.S := ⟨by linarith [hbr.1], hx1⟩
  rw [mwEqDynamicTopRealizedRule_eq hxS]
  unfold mwEqSenderRule
  exact max_lt (by linarith [hbr.1])
    (lt_of_le_of_lt (min_le_right _ _) (mwEq_vertex_lt_state_of_gt_fixed hgt))

/-- **The P3 steady state is an exact fixed point of the realized equilibrium rule.** -/
theorem mwEq_rule_eq_self_at_fixed :
    mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy mwEqFixedState
      = mwEqFixedState := by
  have hbr := mwEqFixedState_bracket
  rw [mwEqDynamicTopRealizedRule_eq mwEqFixedState_mem_S]
  unfold mwEqSenderRule
  rw [mwEq_vertex_eq_at_fixed, min_eq_right (by linarith [hbr.2]),
    max_eq_right (by linarith [hbr.1])]

/-- **Uniqueness.**  On the whole upper region `[2/5, 1]` the realized rule has exactly
one fixed point. -/
theorem mwEq_fixed_point_unique {x : ℝ} (hx0 : 2 / 5 ≤ x) (hx1 : x ≤ 1)
    (hfix : mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x = x) :
    x = mwEqFixedState := by
  rcases lt_trichotomy x mwEqFixedState with h | h | h
  · exact absurd hfix (ne_of_gt (mwEq_rule_gt_self_of_lt_fixed hx0 h))
  · exact h
  · exact absurd hfix (ne_of_lt (mwEq_rule_lt_self_of_gt_fixed h hx1))

/-! ### Strictness: below the steady state the state strictly rises and stays below -/

theorem mwEq_vertex_lt_fixed_of_lt_fixed {x : ℝ} (hlt : x < mwEqFixedState) :
    mwEqSenderVertex x (mwEqLeaderPolicy x) < mwEqFixedState := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  have hbr := mwEqFixedState_bracket
  by_cases hnc : 0 ≤ mwEqLeaderVertex x
  · have := mwEq_gap_identity hnc; linarith
  · rw [not_le] at hnc
    have hxup : 515 * x < 200 + 9 * mwEqTargetSpread - 5 * mwEqSenderSpread := by
      unfold mwEqLeaderVertex at hnc; linarith
    unfold mwEqLeaderPolicy
    rw [max_eq_left hnc.le]
    unfold mwEqSenderVertex
    linarith [hbr.1]

theorem mwEq_rule_lt_fixed_of_lt_fixed {x : ℝ}
    (hx0 : 2 / 5 ≤ x) (hlt : x < mwEqFixedState) :
    mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x < mwEqFixedState := by
  have hbr := mwEqFixedState_bracket
  have hxS : x ∈ Sanctions.S := ⟨by linarith, by linarith [hbr.2]⟩
  rw [mwEqDynamicTopRealizedRule_eq hxS]
  unfold mwEqSenderRule
  exact max_lt (by linarith [hbr.1])
    (lt_of_le_of_lt (min_le_right _ _) (mwEq_vertex_lt_fixed_of_lt_fixed hlt))

/-- One step from strictly below the steady state: strictly up, still strictly below. -/
theorem mwEq_stepF_strict {x : ℝ} (hx0 : 2 / 5 ≤ x) (hlt : x < mwEqFixedState) :
    x < mechanismWitnessParams.dynamicTopLockInStepF
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x ∧
      mechanismWitnessParams.dynamicTopLockInStepF
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x < mwEqFixedState := by
  have hup := mwEq_rule_gt_self_of_lt_fixed hx0 hlt
  have hdn := mwEq_rule_lt_fixed_of_lt_fixed hx0 hlt
  constructor <;>
    · show _ < _
      simp only [AbstractGame.Params.dynamicTopLockInStepF, mechanismWitnessParams_F,
        AbstractGame.affineF]
      linarith

/-! ## PART 3 — POSITIVE: `[a, mwEqFixedState]` carries the whole package

Every hypothesis of the PART 1 machinery is discharged from proved facts about the
constructed equilibrium — no assumed bound anywhere. -/

theorem mwEqEquilibrium_V_S : mwEqEquilibrium.V_S = mwEqSenderValue := rfl

theorem mwEqEquilibrium_alpha : mwEqEquilibrium.α = mwEqLeaderPolicy := rfl

theorem mwEq_rule_monotoneOn_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    MonotoneOn (mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy) (Set.Icc a b) :=
  mwEqDynamicTopRealizedRule_monotoneOn.mono
    (fun _ hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩)

/-- **The ratchet holds on `[a, x*]`.** -/
theorem mwEq_ratchet_on_Icc_fixed {a : ℝ} (ha : 2 / 5 ≤ a) :
    ∀ x ∈ Set.Icc a mwEqFixedState,
      x ≤ mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x :=
  fun _ hx => mwEq_rule_ge_self_of_le_fixed (le_trans ha hx.1) hx.2

/-- **`[a, x*]` is forward invariant.** -/
theorem mwEq_invariant_on_Icc_fixed {a : ℝ} (ha : 2 / 5 ≤ a) :
    ∀ x ∈ Set.Icc a mwEqFixedState,
      mechanismWitnessParams.dynamicTopLockInStepF
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x
        ∈ Set.Icc a mwEqFixedState := by
  have hbr := mwEqFixedState_bracket
  intro x hx
  exact mechanismWitnessParams.dynamicTopLockInStepF_mem_subinterval _ _
    (mwEq_ratchet_on_Icc_fixed ha)
    (mwEq_rule_monotoneOn_Icc (by linarith) (by linarith [hbr.2]))
    (le_of_eq mwEq_rule_eq_self_at_fixed) hx

/-- **Monotone state path** on `[a, x*]`. -/
theorem mwEq_path_mono {a x₀ : ℝ} (ha : 2 / 5 ≤ a)
    (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) :
    Monotone (mechanismWitnessParams.dynamicTopLockInPathF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀) := by
  have hbr := mwEqFixedState_bracket
  exact mechanismWitnessParams.dynamicTopLockInPathF_mono_subinterval _ _
    (mwEq_ratchet_on_Icc_fixed ha)
    (mwEq_rule_monotoneOn_Icc (by linarith) (by linarith [hbr.2]))
    (le_of_eq mwEq_rule_eq_self_at_fixed) hx₀

/-- **Monotone sanctions** on `[a, x*]`: the realized equilibrium sanction sequence is
non-decreasing forever. -/
theorem mwEq_sanctions_mono {a x₀ : ℝ} (ha : 2 / 5 ≤ a)
    (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) :
    Monotone (mechanismWitnessParams.dynamicTopLockInSanctionsF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀) := by
  have hbr := mwEqFixedState_bracket
  exact mechanismWitnessParams.dynamicTopLockInSanctionsF_mono_subinterval _ _
    (mwEq_ratchet_on_Icc_fixed ha)
    (mwEq_rule_monotoneOn_Icc (by linarith) (by linarith [hbr.2]))
    (le_of_eq mwEq_rule_eq_self_at_fixed) hx₀

/-- **The headline positive.**  The P3 economy *does* carry a non-degenerate
ratcheting, forward-invariant sub-basin — with right endpoint bracketed by explicit
rationals — on which both the state path and the realized sanction path are monotone. -/
theorem p3_exists_ratchet_invariant_subinterval :
    ∃ b : ℝ, 1129 / 2000 < b ∧ b < 2823 / 5000 ∧
      (∀ x ∈ Set.Icc (2 / 5 : ℝ) b,
          x ≤ mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x) ∧
      (∀ x ∈ Set.Icc (2 / 5 : ℝ) b,
          mechanismWitnessParams.dynamicTopLockInStepF
            (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x
            ∈ Set.Icc (2 / 5 : ℝ) b) ∧
      (∀ x₀ ∈ Set.Icc (2 / 5 : ℝ) b,
          Monotone (mechanismWitnessParams.dynamicTopLockInPathF
            (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x₀) ∧
          Monotone (mechanismWitnessParams.dynamicTopLockInSanctionsF
            (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x₀)) := by
  have hbr := mwEqFixedState_bracket
  refine ⟨mwEqFixedState, hbr.1, hbr.2, mwEq_ratchet_on_Icc_fixed le_rfl,
    mwEq_invariant_on_Icc_fixed le_rfl, fun x₀ hx₀ =>
      ⟨mwEq_path_mono le_rfl hx₀, mwEq_sanctions_mono le_rfl hx₀⟩⟩

/-- Strictly increasing until the steady state: the path never reaches `x*`, and every
step is a strict increase. -/
theorem mwEq_path_strictMono {x₀ : ℝ} (h0 : 2 / 5 ≤ x₀) (h1 : x₀ < mwEqFixedState) :
    (∀ n, mechanismWitnessParams.dynamicTopLockInPathF
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n < mwEqFixedState) ∧
      StrictMono (mechanismWitnessParams.dynamicTopLockInPathF
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀) := by
  have hbr := mwEqFixedState_bracket
  have hmem : x₀ ∈ Set.Icc (2 / 5 : ℝ) mwEqFixedState := ⟨h0, le_of_lt h1⟩
  have hlow : ∀ n, 2 / 5 ≤ mechanismWitnessParams.dynamicTopLockInPathF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n := fun n =>
    (mechanismWitnessParams.dynamicTopLockInPathF_mem_subinterval _ _
      (mwEq_ratchet_on_Icc_fixed le_rfl)
      (mwEq_rule_monotoneOn_Icc (by norm_num) (by linarith [hbr.2]))
      (le_of_eq mwEq_rule_eq_self_at_fixed) hmem n).1
  have hbelow : ∀ n, mechanismWitnessParams.dynamicTopLockInPathF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n < mwEqFixedState := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [AbstractGame.Params.dynamicTopLockInPathF_succ]
      exact (mwEq_stepF_strict (hlow n) ih).2
  refine ⟨hbelow, strictMono_nat_of_lt_succ fun n => ?_⟩
  rw [AbstractGame.Params.dynamicTopLockInPathF_succ]
  exact (mwEq_stepF_strict (hlow n) (hbelow n)).1

/-! ### Sanctions ratchet STRICTLY up

The equilibrium Sender vertex is strictly increasing in the state: its direct slope
`9/8` strictly dominates the indirect slope through the Target's best response,
`(5/12)·(515/580)`.  On `[2/5, x*]` neither clip binds, so the realized rule inherits
strict monotonicity and the sanction sequence strictly increases forever. -/

theorem mwEqLeaderPolicy_slope_bound {u v : ℝ} (huv : u ≤ v) :
    mwEqLeaderPolicy v - mwEqLeaderPolicy u ≤ (515 / 580) * (v - u) := by
  unfold mwEqLeaderPolicy mwEqLeaderVertex
  rcases le_or_gt ((5 * mwEqSenderSpread - 9 * mwEqTargetSpread + 515 * u - 200) / 580)
    0 with h | h
  · rw [max_eq_left h]
    rcases le_or_gt ((5 * mwEqSenderSpread - 9 * mwEqTargetSpread + 515 * v - 200) / 580)
      0 with h2 | h2
    · rw [max_eq_left h2]; linarith
    · rw [max_eq_right h2.le]; linarith
  · rw [max_eq_right h.le, max_eq_right
      (show (0 : ℝ) ≤ (5 * mwEqSenderSpread - 9 * mwEqTargetSpread + 515 * v - 200) / 580
        by linarith)]
    linarith

theorem mwEq_vertex_strictMono {u v : ℝ} (huv : u < v) :
    mwEqSenderVertex u (mwEqLeaderPolicy u) < mwEqSenderVertex v (mwEqLeaderPolicy v) := by
  have h := mwEqLeaderPolicy_slope_bound (le_of_lt huv)
  unfold mwEqSenderVertex
  linarith

theorem mwEq_vertex_le_fixed_of_le_fixed {x : ℝ} (hle : x ≤ mwEqFixedState) :
    mwEqSenderVertex x (mwEqLeaderPolicy x) ≤ mwEqFixedState := by
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]; exact le_of_eq mwEq_vertex_eq_at_fixed
  · exact le_of_lt (mwEq_vertex_lt_fixed_of_lt_fixed h)

/-- On `[2/5, x*]` the realized equilibrium rule is STRICTLY increasing. -/
theorem mwEq_rule_strictMonoOn {u v : ℝ} (hu : 2 / 5 ≤ u) (huv : u < v)
    (hv : v ≤ mwEqFixedState) :
    mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy u
      < mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy v := by
  have hbr := mwEqFixedState_bracket
  have hv0 : 2 / 5 ≤ v := le_trans hu (le_of_lt huv)
  have huS : u ∈ Sanctions.S := ⟨by linarith, by linarith [hv.trans hbr.2.le, hbr.2]⟩
  have hvS : v ∈ Sanctions.S := ⟨by linarith, by linarith [hbr.2]⟩
  rw [mwEqDynamicTopRealizedRule_eq huS, mwEqDynamicTopRealizedRule_eq hvS]
  unfold mwEqSenderRule
  have hlu : u ≤ mwEqSenderVertex u (mwEqLeaderPolicy u) :=
    mwEq_vertex_ge_state_of_le_fixed hu (le_of_lt (lt_of_lt_of_le huv hv))
  have hlv : v ≤ mwEqSenderVertex v (mwEqLeaderPolicy v) :=
    mwEq_vertex_ge_state_of_le_fixed hv0 hv
  have hru := mwEq_vertex_le_fixed_of_le_fixed (le_of_lt (lt_of_lt_of_le huv hv))
  have hrv := mwEq_vertex_le_fixed_of_le_fixed hv
  rw [min_eq_right (by linarith [hbr.2]), min_eq_right (by linarith [hbr.2]),
    max_eq_right (by linarith), max_eq_right (by linarith)]
  exact mwEq_vertex_strictMono huv

/-- **Sanctions ratchet strictly upward, forever.** -/
theorem mwEq_sanctions_strictMono {x₀ : ℝ} (h0 : 2 / 5 ≤ x₀) (h1 : x₀ < mwEqFixedState) :
    StrictMono (mechanismWitnessParams.dynamicTopLockInSanctionsF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀) := by
  have hbr := mwEqFixedState_bracket
  have hmem : x₀ ∈ Set.Icc (2 / 5 : ℝ) mwEqFixedState := ⟨h0, le_of_lt h1⟩
  obtain ⟨hbelow, hstrict⟩ := mwEq_path_strictMono h0 h1
  have hin := mechanismWitnessParams.dynamicTopLockInPathF_mem_subinterval _ _
    (mwEq_ratchet_on_Icc_fixed le_rfl)
    (mwEq_rule_monotoneOn_Icc (by norm_num) (by linarith [hbr.2]))
    (le_of_eq mwEq_rule_eq_self_at_fixed) hmem
  intro m n hmn
  exact mwEq_rule_strictMonoOn (hin m).1 (hstrict hmn) (hin n).2

/-- **The headline positive with fully rational data.**  From any state in the RATIONAL
interval `[2/5, 1129/2000]` — no irrational constant anywhere in the hypotheses — the
realized equilibrium state path and sanction path are both STRICTLY increasing forever,
and the state never leaves `[2/5, 1]`. -/
theorem p3_monotone_sanctions_from_rational_start {x₀ : ℝ}
    (h0 : 2 / 5 ≤ x₀) (h1 : x₀ ≤ 1129 / 2000) :
    StrictMono (mechanismWitnessParams.dynamicTopLockInPathF
        (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x₀) ∧
      StrictMono (mechanismWitnessParams.dynamicTopLockInSanctionsF
        (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x₀) ∧
      (∀ n, mechanismWitnessParams.dynamicTopLockInPathF
        (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x₀ n
          ∈ Set.Icc (2 / 5 : ℝ) 1) := by
  have hbr := mwEqFixedState_bracket
  have hlt : x₀ < mwEqFixedState := by linarith [hbr.1]
  have hmem : x₀ ∈ Set.Icc (2 / 5 : ℝ) mwEqFixedState := ⟨h0, le_of_lt hlt⟩
  refine ⟨(mwEq_path_strictMono h0 hlt).2, mwEq_sanctions_strictMono h0 hlt, fun n => ?_⟩
  show mechanismWitnessParams.dynamicTopLockInPathF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n ∈ Set.Icc (2 / 5 : ℝ) 1
  have hin := mechanismWitnessParams.dynamicTopLockInPathF_mem_subinterval _ _
    (mwEq_ratchet_on_Icc_fixed le_rfl)
    (mwEq_rule_monotoneOn_Icc (by norm_num) (by linarith [hbr.2]))
    (le_of_eq mwEq_rule_eq_self_at_fixed) hmem n
  exact ⟨hin.1, by linarith [hin.2, hbr.2]⟩

/-! ## PART 4 — NEGATIVE, SHARP: the right endpoint is pinned to `mwEqFixedState`

The PART 1 obstruction plus the uniqueness of the fixed point leave exactly one
candidate right endpoint. -/

theorem mwEq_subinterval_forces_fixed_endpoint {a b : ℝ}
    (ha : 2 / 5 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hr : ∀ x ∈ Set.Icc a b, x ≤ mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x)
    (hi : ∀ x ∈ Set.Icc a b, mechanismWitnessParams.dynamicTopLockInStepF
      (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x ∈ Set.Icc a b) :
    b = mwEqFixedState := by
  have hstrict : StrictMono fun s => mechanismWitnessParams.F b s := by
    intro u v huv
    simp only [mechanismWitnessParams_F, AbstractGame.affineF]
    linarith
  exact mwEq_fixed_point_unique (le_trans ha hab) hb1
    (mechanismWitnessParams.dynamicTopLockIn_subinterval_forces_fixed_endpoint _ _
      hab hstrict hr hi)

/-- **REFUTATION.**  For the constructed P3 equilibrium, NO sub-interval whose right
endpoint differs from the steady state carries both the ratchet and forward invariance.
This strictly sharpens the previous band refutations: the surviving set of right
endpoints is the single point `mwEqFixedState`. -/
theorem p3_no_ratchet_invariant_subinterval_of_ne_fixed :
    ¬ ∃ a b : ℝ, 2 / 5 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b ≠ mwEqFixedState ∧
      ∀ E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Set.Icc a b, x ≤ mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne E.V_S) E.α x) ∧
        (∀ x ∈ Set.Icc a b, mechanismWitnessParams.dynamicTopLockInStepF
            (mwSenderValueOne E.V_S) E.α x ∈ Set.Icc a b) := by
  rintro ⟨a, b, ha, hab, hb1, hne, hall⟩
  exact hne (mwEq_subinterval_forces_fixed_endpoint ha (le_of_lt hab) hb1
    (hall mwEqEquilibrium).1 (hall mwEqEquilibrium).2)

/-- **The exact characterization.**  A sub-interval of `[2/5, 1]` carries the
ratchet-plus-invariance package **iff** its right endpoint is the steady state. -/
theorem p3_subinterval_iff {a b : ℝ} (ha : 2 / 5 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ((∀ x ∈ Set.Icc a b, x ≤ mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x) ∧
      (∀ x ∈ Set.Icc a b, mechanismWitnessParams.dynamicTopLockInStepF
        (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α x ∈ Set.Icc a b))
      ↔ b = mwEqFixedState := by
  constructor
  · rintro ⟨hr, hi⟩
    exact mwEq_subinterval_forces_fixed_endpoint ha hab hb1 hr hi
  · rintro rfl
    exact ⟨mwEq_ratchet_on_Icc_fixed ha, mwEq_invariant_on_Icc_fixed ha⟩

/-! ## PART 5 — THE STEADY STATE IS IRRATIONAL

Hence no *rational* sub-interval carries the package: the single surviving right
endpoint is not a rational number.

The route is elementary and uses no polynomial-irreducibility machinery.  If
`x* = b ∈ ℚ`, then the defining identity for `x*` says the Sender spread `S` satisfies
the RATIONAL QUADRATIC `9S² − 10340S + (9357 + 15686b) = 0`.  Dividing the quartic
`mwEqQuartic` by that quadratic leaves the remainder
`−4783446528·S + c² − 178150·c + 11351103145` with `c := 9357 + 15686b`, whose
`S`-coefficient is a NONZERO CONSTANT.  So `S` itself is rational; but the quartic has
no rational root in the proved window `[441/250, 17641/10000]` (the denominator of any
rational root divides the leading coefficient `81`, and none of `1,3,9,27,81` scales the
window to contain an integer). -/

/-- No integer/denominator pair with `d ≤ 81` places `n/d` in `[441/250, 17641/10000]`.

Rule-13 note: the caller supplies `d ∣ 81`, but only the *bound* `d ≤ 81` is consumed, so
the hypothesis is stated at that strength. -/
theorem mwEq_no_int_pair (n : ℤ) (d : ℕ) (hle : d ≤ 81) (hd0 : 0 < d)
    (i1 : 441 * (d : ℤ) ≤ 250 * n) (i2 : 10000 * n ≤ 17641 * (d : ℤ)) : False := by
  interval_cases d <;> omega

/-- **`mwEqQuartic` has no rational root in the proved spread window.** -/
theorem mwEq_no_rat_root_in_window (r : ℚ) (hq : mwEqQuartic (r : ℝ) = 0)
    (hlo : 441 / 250 ≤ (r : ℝ)) (hhi : (r : ℝ) ≤ 17641 / 10000) : False := by
  unfold mwEqQuartic at hq
  have hqQ : 81 * r ^ 4 - 186120 * r ^ 3 + 108518950 * r ^ 2 - 6625517528 * r
      + 11351103145 = 0 := by
    have : ((81 * r ^ 4 - 186120 * r ^ 3 + 108518950 * r ^ 2 - 6625517528 * r
        + 11351103145 : ℚ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hloQ : (441 / 250 : ℚ) ≤ r := by
    have h : ((441 / 250 : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hhiQ : r ≤ (17641 / 10000 : ℚ) := by
    have h : ((r : ℚ) : ℝ) ≤ ((17641 / 10000 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hdpos : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  have hdne : ((r.den : ℚ)) ≠ 0 := ne_of_gt hdpos
  have hnum : (r.num : ℚ) = r * (r.den : ℚ) := (div_eq_iff hdne).mp (Rat.num_div_den r)
  have keyQ : (81 * (r.num : ℚ) ^ 4 - 186120 * (r.num : ℚ) ^ 3 * (r.den : ℚ)
      + 108518950 * (r.num : ℚ) ^ 2 * (r.den : ℚ) ^ 2
      - 6625517528 * (r.num : ℚ) * (r.den : ℚ) ^ 3
      + 11351103145 * (r.den : ℚ) ^ 4) = 0 := by
    rw [hnum]; linear_combination ((r.den : ℚ)) ^ 4 * hqQ
  have keyZ : (81 * r.num ^ 4 - 186120 * r.num ^ 3 * (r.den : ℤ)
      + 108518950 * r.num ^ 2 * (r.den : ℤ) ^ 2
      - 6625517528 * r.num * (r.den : ℤ) ^ 3
      + 11351103145 * (r.den : ℤ) ^ 4) = 0 := by exact_mod_cast keyQ
  have hdvdZ : (r.den : ℤ) ∣ 81 * r.num ^ 4 :=
    ⟨186120 * r.num ^ 3 - 108518950 * r.num ^ 2 * (r.den : ℤ)
      + 6625517528 * r.num * (r.den : ℤ) ^ 2 - 11351103145 * (r.den : ℤ) ^ 3,
     by linear_combination keyZ⟩
  have hdvdN : r.den ∣ 81 * r.num.natAbs ^ 4 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvdZ
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have hcop : Nat.Coprime r.den (r.num.natAbs ^ 4) := (r.reduced.symm).pow_right 4
  have hdvd81 : r.den ∣ 81 := hcop.dvd_of_dvd_mul_right hdvdN
  have i1 : 441 * (r.den : ℤ) ≤ 250 * r.num := by
    have : (441 : ℚ) * (r.den : ℚ) ≤ 250 * (r.num : ℚ) := by rw [hnum]; nlinarith
    exact_mod_cast this
  have i2 : 10000 * r.num ≤ 17641 * (r.den : ℤ) := by
    have : (10000 : ℚ) * (r.num : ℚ) ≤ 17641 * (r.den : ℚ) := by rw [hnum]; nlinarith
    exact_mod_cast this
  exact mwEq_no_int_pair r.num r.den (Nat.le_of_dvd (by norm_num) hdvd81) r.den_pos i1 i2

/-- **The equilibrium Sender endpoint spread is irrational.** -/
theorem mwEqSenderSpread_irrational : Irrational mwEqSenderSpread := by
  rintro ⟨q, hq⟩
  obtain ⟨hlo, hhi⟩ := mwEqSenderSpread_bounds
  rw [← hq] at hlo hhi
  exact mwEq_no_rat_root_in_window q (by rw [hq]; exact mwEqSenderSpread_quartic) hlo hhi

/-- **The P3 steady state is irrational.** -/
theorem mwEqFixedState_irrational : Irrational mwEqFixedState := by
  rintro ⟨b, hb⟩
  have hquad : 9 * mwEqSenderSpread ^ 2 - 10340 * mwEqSenderSpread
      + (9357 + 15686 * (b : ℝ)) = 0 := by
    have h := mwEqFixedState_spec
    rw [← hb] at h
    linarith
  have hquart := mwEqSenderSpread_quartic
  unfold mwEqQuartic at hquart
  have hlin : 4783446528 * mwEqSenderSpread
      = (9357 + 15686 * (b : ℝ)) ^ 2 - 178150 * (9357 + 15686 * (b : ℝ))
        + 11351103145 := by
    linear_combination (-1 : ℝ) * hquart
      + (9 * mwEqSenderSpread ^ 2 - 10340 * mwEqSenderSpread
          - (9357 + 15686 * (b : ℝ)) + 178150) * hquad
  refine mwEqSenderSpread_irrational
    ⟨((9357 + 15686 * b) ^ 2 - 178150 * (9357 + 15686 * b) + 11351103145)
        / 4783446528, ?_⟩
  push_cast
  rw [div_eq_iff (by norm_num : (4783446528 : ℝ) ≠ 0)]
  linarith

/-- **No rational-endpoint sub-interval works for EVERY shocked equilibrium.**

Read the quantifiers carefully; the name is easy to over-read.  What is proved is the
negation of

  `∃ a, ∃ b : ℚ, … ∧ ∀ E, (ratchet on [a,b] ∧ invariance of [a,b])`,

i.e. *no rational-endpoint interval is carried by all equilibria simultaneously*.  It is
discharged by a single instantiation at the constructed equilibrium `mwEqEquilibrium`,
whose unique admissible right endpoint `mwEqFixedState` is irrational.

It is therefore **NOT** the statement that no rational-endpoint sub-interval works for
*any* equilibrium (`∀ a b : ℚ, ∀ E, ¬ …`), which is strictly stronger and is **not proved
here**.  For an arbitrary `E` the only spread information available is
`Δ_S ∈ [17/10, 45/16]`, not the tight IVT window that pins the constructed equilibrium's
fixed state, so that stronger form is open.

Note also that the project's persistence conclusion is *existential* in the equilibrium,
so this ∀E-orientation is not the form the economics turns on; the load-bearing positive
result is `p3_exists_ratchet_invariant_subinterval` below. -/
theorem p3_no_rational_ratchet_invariant_subinterval :
    ¬ ∃ (a : ℝ) (b : ℚ), 2 / 5 ≤ a ∧ a < (b : ℝ) ∧ (b : ℝ) ≤ 1 ∧
      ∀ E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Set.Icc a (b : ℝ), x ≤ mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne E.V_S) E.α x) ∧
        (∀ x ∈ Set.Icc a (b : ℝ), mechanismWitnessParams.dynamicTopLockInStepF
            (mwSenderValueOne E.V_S) E.α x ∈ Set.Icc a (b : ℝ)) := by
  rintro ⟨a, b, ha, hab, hb1, hall⟩
  exact mwEqFixedState_irrational
    ⟨b, mwEq_subinterval_forces_fixed_endpoint ha (le_of_lt hab) hb1
      (hall mwEqEquilibrium).1 (hall mwEqEquilibrium).2⟩

/-! ## PART 6 — NON-VACUITY PROBES AND CROSS-CHECKS (Rule 11)

Each probe is a compiling `example`, not prose. -/

/-- The sub-basin is non-degenerate: its left endpoint is strictly below its right. -/
example : (2 / 5 : ℝ) < mwEqFixedState := by linarith [mwEqFixedState_bracket.1]

/-- The positive result is instantiable at an explicit rational start. -/
example : StrictMono (mechanismWitnessParams.dynamicTopLockInSanctionsF
    (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α (1 / 2)) :=
  (p3_monotone_sanctions_from_rational_start (by norm_num) (by norm_num)).2.1

example : StrictMono (mechanismWitnessParams.dynamicTopLockInPathF
    (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α (2 / 5)) :=
  (p3_monotone_sanctions_from_rational_start le_rfl (by norm_num)).1

/-- Cross-check vs. the level-floor route's reach `5329/10230`: the steady state lies
STRICTLY beyond it, which is why the floor route could not reach the answer. -/
example : (5329 / 10230 : ℝ) < mwEqFixedState := by linarith [mwEqFixedState_bracket.1]

/-- Cross-check vs. `mwShockedOne_no_top_floor` (`rule(1) < 1`, every equilibrium): the
sub-basin stops strictly short of the top state, so there is no contradiction. -/
example : mwEqFixedState < 1 := by linarith [mwEqFixedState_bracket.2]

/-- Cross-check: the surviving right endpoint sits inside the `10⁻⁴` sliver that the
disprove gate could not close, and nowhere else. -/
example : mwEqFixedState ∈ Set.Ioo (1129 / 2000 : ℝ) (2823 / 5000) :=
  ⟨mwEqFixedState_bracket.1, mwEqFixedState_bracket.2⟩

/-- Rule 11 self-refutation probe: the positive and the negative are jointly consistent
only because the admissible endpoint is irrational — exhibited, not asserted. -/
example : ¬ ∃ q : ℚ, (q : ℝ) = mwEqFixedState := mwEqFixedState_irrational

/-! ## AXIOM SCAN (Rule 10) -/

#print axioms p3_exists_ratchet_invariant_subinterval
#print axioms p3_monotone_sanctions_from_rational_start
#print axioms mwEq_path_strictMono
#print axioms mwEq_sanctions_strictMono
#print axioms mwEq_rule_strictMonoOn
#print axioms p3_subinterval_iff
#print axioms p3_no_ratchet_invariant_subinterval_of_ne_fixed
#print axioms p3_no_rational_ratchet_invariant_subinterval
#print axioms mwEqFixedState_irrational
#print axioms mwEqSenderSpread_irrational
#print axioms mwEqFixedState_bracket
#print axioms mwEq_rule_eq_self_at_fixed
#print axioms mwEq_fixed_point_unique
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockIn_subinterval_iff
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockInSanctionsF_mono_subinterval
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockIn_subinterval_forces_fixed_endpoint

end

end Examples

end Sanctions
