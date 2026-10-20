/-
Sanctions/Foundations/FeynmanKacVerification.lean

Generic Feynman--Kac verification for time-inhomogeneous Markov pullbacks.

The observable space is abstract. Each one-step pullback is positive, unital,
and real-linear; the initial-state evaluator (or initial probability law) has
the same properties. A pullback prefix sends a time-n observable back to time
zero. Applying that prefix to each Bellman row gives a finite telescope.
Order bounds by scalar multiples of the constant-one observable give
summability and a geometric terminal estimate, so the comparison passes to the
infinite `tsum`.

The final section constructs the abstract operators from the concrete
closed-loop box pullback on bounded continuous functions. This file adds no
field or hypothesis to any sanctions-model parameter or equilibrium structure.
-/

import Sanctions.Foundations.InfiniteHorizonVerification
import Sanctions.Foundations.ClosedLoopBoxTransfer

noncomputable section

open Filter Finset
open scoped Topology

namespace Sanctions
namespace FeynmanKacVerification

/-- A positive, unital, real-linear endomorphism of an ordered observable space. -/
structure PositiveUnitalLinearPullback (E : Type*) [Add E] [SMul Real E]
    [One E] [LE E] where
  toFun : E -> E
  map_add : forall f g, toFun (f + g) = toFun f + toFun g
  map_smul : forall (c : Real) f, toFun (c • f) = c • toFun f
  map_one : toFun 1 = 1
  monotone : forall {f g : E}, f <= g -> toFun f <= toFun g

instance {E : Type*} [Add E] [SMul Real E] [One E] [LE E] :
    CoeFun (PositiveUnitalLinearPullback E) (fun _ => E -> E) :=
  { coe := PositiveUnitalLinearPullback.toFun }

/-- A positive, unital, real-linear functional, such as evaluation at an
initial state or integration against an initial probability law. -/
structure PositiveUnitalLinearFunctional (E : Type*) [Add E] [SMul Real E]
    [One E] [LE E] where
  toFun : E -> Real
  map_add : forall f g, toFun (f + g) = toFun f + toFun g
  map_smul : forall (c : Real) f, toFun (c • f) = c * toFun f
  map_one : toFun 1 = 1
  monotone : forall {f g : E}, f <= g -> toFun f <= toFun g

instance {E : Type*} [Add E] [SMul Real E] [One E] [LE E] :
    CoeFun (PositiveUnitalLinearFunctional E) (fun _ => E -> Real) :=
  { coe := PositiveUnitalLinearFunctional.toFun }

section OrderedObservable

variable {E : Type*} [Add E] [SMul Real E] [One E] [LE E]

/-- A time-inhomogeneous sequence of one-step Markov pullbacks. -/
abbrev PullbackSequence (E : Type*) [Add E] [SMul Real E] [One E] [LE E] :=
  Nat -> PositiveUnitalLinearPullback E

/-- Pull a time-n observable back through periods 0 through n-1. -/
def pullbackPrefix (P : PullbackSequence E) : Nat -> E -> E
  | 0, f => f
  | n + 1, f => pullbackPrefix P n (P n f)

@[simp] theorem pullbackPrefix_zero (P : PullbackSequence E) (f : E) :
    pullbackPrefix P 0 f = f :=
  rfl

@[simp] theorem pullbackPrefix_succ (P : PullbackSequence E) (n : Nat) (f : E) :
    pullbackPrefix P (n + 1) f = pullbackPrefix P n (P n f) :=
  rfl

theorem pullbackPrefix_add (P : PullbackSequence E) (n : Nat) (f g : E) :
    pullbackPrefix P n (f + g) = pullbackPrefix P n f + pullbackPrefix P n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      rw [pullbackPrefix_succ, (P n).map_add, ih]
      rfl

theorem pullbackPrefix_smul (P : PullbackSequence E) (n : Nat) (c : Real)
    (f : E) :
    pullbackPrefix P n (c • f) = c • pullbackPrefix P n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [pullbackPrefix_succ, (P n).map_smul, ih]
      rfl

theorem pullbackPrefix_one (P : PullbackSequence E) (n : Nat) :
    pullbackPrefix P n (1 : E) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pullbackPrefix_succ, (P n).map_one, ih]

theorem pullbackPrefix_mono (P : PullbackSequence E) (n : Nat)
    {f g : E} (hfg : f <= g) :
    pullbackPrefix P n f <= pullbackPrefix P n g := by
  induction n generalizing f g with
  | zero => exact hfg
  | succ n ih =>
      rw [pullbackPrefix_succ, pullbackPrefix_succ]
      exact ih ((P n).monotone hfg)

/-- The order-unit form of a uniform absolute bound: `f` lies between the
constant observables `-M` and `M`. -/
def OrderBoundedByOne (f : E) (M : Real) : Prop :=
  (-M) • (1 : E) <= f /\ f <= M • (1 : E)

/-- Positive unital prefixes and a positive unital initial functional preserve
an order-unit bound as a scalar absolute-value bound. -/
theorem abs_functional_pullbackPrefix_le_of_orderBounded
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (n : Nat) (f : E) (M : Real) (h_bound : OrderBoundedByOne f M) :
    |L (pullbackPrefix P n f)| <= M := by
  have h_lower_prefix :=
    pullbackPrefix_mono P n h_bound.1
  have h_upper_prefix :=
    pullbackPrefix_mono P n h_bound.2
  have h_lower := L.monotone h_lower_prefix
  have h_upper := L.monotone h_upper_prefix
  rw [pullbackPrefix_smul, pullbackPrefix_one, L.map_smul, L.map_one] at h_lower
  rw [pullbackPrefix_smul, pullbackPrefix_one, L.map_smul, L.map_one] at h_upper
  have h_lower' : -M <= L (pullbackPrefix P n f) := by
    simpa using h_lower
  have h_upper' : L (pullbackPrefix P n f) <= M := by
    simpa using h_upper
  exact abs_le.mpr (And.intro h_lower' h_upper')

/-- The discounted time-zero expectation of the period-n flow observable. -/
def expectedStage (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E) (n : Nat) : Real :=
  beta ^ n * L (pullbackPrefix P n (u n))

/-- The expected payoff over periods 0 through N-1. -/
def finiteExpectedPayoff (P : PullbackSequence E)
    (L : PositiveUnitalLinearFunctional E) (beta : Real)
    (u : Nat -> E) (N : Nat) : Real :=
  (range N).sum fun n => expectedStage P L beta u n

/-- The infinite expected discounted payoff, defined by `tsum`. -/
def expectedDiscountedPayoff (P : PullbackSequence E)
    (L : PositiveUnitalLinearFunctional E) (beta : Real)
    (u : Nat -> E) : Real :=
  tsum fun n : Nat => expectedStage P L beta u n

/-- The time-zero expected discounted continuation observable after N periods. -/
def expectedTerminal (P : PullbackSequence E)
    (L : PositiveUnitalLinearFunctional E) (beta : Real)
    (V : E) (N : Nat) : Real :=
  beta ^ N * L (pullbackPrefix P N V)

/-! ## Finite Feynman--Kac telescope -/

/-- A Bellman supersolution gives one discounted expected telescoping step. -/
theorem expected_bellman_step_le
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E) (V : E)
    (hbeta : 0 <= beta)
    (h_bellman : forall n, u n + beta • P n V <= V)
    (n : Nat) :
    expectedStage P L beta u n + expectedTerminal P L beta V (n + 1) <=
      expectedTerminal P L beta V n := by
  have h_row_observable :=
    pullbackPrefix_mono P n (h_bellman n)
  have h_row := L.monotone h_row_observable
  rw [pullbackPrefix_add, pullbackPrefix_smul, L.map_add, L.map_smul] at h_row
  have h_scaled := mul_le_mul_of_nonneg_left h_row (pow_nonneg hbeta n)
  simpa [expectedStage, expectedTerminal, pow_succ, mul_add, mul_assoc] using h_scaled

/-- Finite expected payoff plus the expected terminal value is below a Bellman
supersolution. -/
theorem finiteExpectedPayoff_add_terminal_le_value
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E) (V : E)
    (hbeta : 0 <= beta)
    (h_bellman : forall n, u n + beta • P n V <= V) :
    forall N : Nat,
      finiteExpectedPayoff P L beta u N + expectedTerminal P L beta V N <= L V := by
  intro N
  induction N with
  | zero =>
      simp [finiteExpectedPayoff, expectedTerminal]
  | succ N ih =>
      calc
        finiteExpectedPayoff P L beta u (N + 1) +
              expectedTerminal P L beta V (N + 1) =
            finiteExpectedPayoff P L beta u N +
              (expectedStage P L beta u N + expectedTerminal P L beta V (N + 1)) := by
                simp only [finiteExpectedPayoff, sum_range_succ]
                ring
        _ <= finiteExpectedPayoff P L beta u N + expectedTerminal P L beta V N := by
          have hstep := expected_bellman_step_le P L beta u V hbeta h_bellman N
          linarith
        _ <= L V := ih

/-- Bellman equality in every time row gives the exact finite Feynman--Kac
telescope. -/
theorem finiteExpectedPayoff_add_terminal_eq_value
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E) (V : E)
    (h_bellman : forall n, u n + beta • P n V = V) :
    forall N : Nat,
      finiteExpectedPayoff P L beta u N + expectedTerminal P L beta V N = L V := by
  intro N
  induction N with
  | zero =>
      simp [finiteExpectedPayoff, expectedTerminal]
  | succ N ih =>
      have h_row_observable :=
        congrArg (pullbackPrefix P N) (h_bellman N)
      have h_row := congrArg L h_row_observable
      rw [pullbackPrefix_add, pullbackPrefix_smul, L.map_add, L.map_smul] at h_row
      have h_scaled := congrArg (fun z : Real => beta ^ N * z) h_row
      have hstep :
          expectedStage P L beta u N + expectedTerminal P L beta V (N + 1) =
            expectedTerminal P L beta V N := by
        simpa [expectedStage, expectedTerminal, pow_succ, mul_add, mul_assoc] using h_scaled
      calc
        finiteExpectedPayoff P L beta u (N + 1) +
              expectedTerminal P L beta V (N + 1) =
            finiteExpectedPayoff P L beta u N +
              (expectedStage P L beta u N + expectedTerminal P L beta V (N + 1)) := by
                simp only [finiteExpectedPayoff, sum_range_succ]
                ring
        _ = finiteExpectedPayoff P L beta u N + expectedTerminal P L beta V N := by
          rw [hstep]
        _ = L V := ih

/-! ## Uniform bounds and the infinite horizon -/

/-- An order-unit stage bound makes the expected discounted stage series
summable. -/
theorem expectedStage_summable_of_order_bounds
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E)
    (hbeta : 0 <= beta) (hbeta_lt : beta < 1)
    (M : Real) (h_bound : forall n, OrderBoundedByOne (u n) M) :
    Summable (expectedStage P L beta u) := by
  have h_geom : Summable (fun n : Nat => beta ^ n) :=
    summable_geometric_of_lt_one hbeta hbeta_lt
  have h_majorant : Summable (fun n : Nat => beta ^ n * M) := h_geom.mul_right M
  apply Summable.of_norm_bounded h_majorant
  intro n
  rw [expectedStage, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hbeta]
  exact mul_le_mul_of_nonneg_left
    (abs_functional_pullbackPrefix_le_of_orderBounded P L n (u n) M (h_bound n))
    (pow_nonneg hbeta n)

/-- An order-unit value bound gives the explicit geometric terminal estimate. -/
theorem abs_expectedTerminal_le_of_order_bound
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (V : E)
    (hbeta : 0 <= beta) (M : Real) (h_bound : OrderBoundedByOne V M)
    (N : Nat) :
    |expectedTerminal P L beta V N| <= beta ^ N * M := by
  rw [expectedTerminal, abs_mul, abs_pow, abs_of_nonneg hbeta]
  exact mul_le_mul_of_nonneg_left
    (abs_functional_pullbackPrefix_le_of_orderBounded P L N V M h_bound)
    (pow_nonneg hbeta N)

/-- An order-unit bounded value has a vanishing discounted expected terminal
remainder. -/
theorem expectedTerminal_tendsto_zero_of_order_bound
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (V : E)
    (hbeta : 0 <= beta) (hbeta_lt : beta < 1)
    (M : Real) (h_bound : OrderBoundedByOne V M) :
    Tendsto (expectedTerminal P L beta V) atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun n : Nat => beta ^ n * M)
  · intro n
    simpa [Real.norm_eq_abs] using
      abs_expectedTerminal_le_of_order_bound P L beta V hbeta M h_bound n
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hbeta hbeta_lt).mul_const M

/-- A Bellman supersolution bounds every infinite expected discounted payoff
whose stage and candidate-value observables have order-unit bounds. -/
theorem expectedDiscountedPayoff_le_value_of_order_bounds
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E) (V : E)
    (hbeta : 0 <= beta) (hbeta_lt : beta < 1)
    (h_bellman : forall n, u n + beta • P n V <= V)
    (M_u M_V : Real)
    (h_u_bound : forall n, OrderBoundedByOne (u n) M_u)
    (h_V_bound : OrderBoundedByOne V M_V) :
    expectedDiscountedPayoff P L beta u <= L V := by
  have h_summable :=
    expectedStage_summable_of_order_bounds P L beta u hbeta hbeta_lt M_u h_u_bound
  have h_partial :
      Tendsto (finiteExpectedPayoff P L beta u) atTop
        (nhds (expectedDiscountedPayoff P L beta u)) := by
    simpa [finiteExpectedPayoff, expectedDiscountedPayoff] using
      h_summable.tendsto_sum_tsum_nat
  have h_terminal :
      Tendsto (expectedTerminal P L beta V) atTop (nhds 0) :=
    expectedTerminal_tendsto_zero_of_order_bound
      P L beta V hbeta hbeta_lt M_V h_V_bound
  have h_total :
      Tendsto
        (fun N => finiteExpectedPayoff P L beta u N + expectedTerminal P L beta V N)
        atTop (nhds (expectedDiscountedPayoff P L beta u)) := by
    simpa using h_partial.add h_terminal
  exact le_of_tendsto' h_total
    (finiteExpectedPayoff_add_terminal_le_value P L beta u V hbeta h_bellman)

/-- Exact Bellman attainment identifies the infinite expected discounted payoff
with the candidate value under the same order-unit bounds. -/
theorem expectedDiscountedPayoff_eq_value_of_order_bounds
    (P : PullbackSequence E) (L : PositiveUnitalLinearFunctional E)
    (beta : Real) (u : Nat -> E) (V : E)
    (hbeta : 0 <= beta) (hbeta_lt : beta < 1)
    (h_bellman : forall n, u n + beta • P n V = V)
    (M_u M_V : Real)
    (h_u_bound : forall n, OrderBoundedByOne (u n) M_u)
    (h_V_bound : OrderBoundedByOne V M_V) :
    expectedDiscountedPayoff P L beta u = L V := by
  have h_summable :=
    expectedStage_summable_of_order_bounds P L beta u hbeta hbeta_lt M_u h_u_bound
  have h_partial :
      Tendsto (finiteExpectedPayoff P L beta u) atTop
        (nhds (expectedDiscountedPayoff P L beta u)) := by
    simpa [finiteExpectedPayoff, expectedDiscountedPayoff] using
      h_summable.tendsto_sum_tsum_nat
  have h_terminal :
      Tendsto (expectedTerminal P L beta V) atTop (nhds 0) :=
    expectedTerminal_tendsto_zero_of_order_bound
      P L beta V hbeta hbeta_lt M_V h_V_bound
  have h_total :
      Tendsto
        (fun N => finiteExpectedPayoff P L beta u N + expectedTerminal P L beta V N)
        atTop (nhds (expectedDiscountedPayoff P L beta u)) := by
    simpa using h_partial.add h_terminal
  apply le_antisymm
  · exact le_of_tendsto' h_total fun N =>
      le_of_eq (finiteExpectedPayoff_add_terminal_eq_value P L beta u V h_bellman N)
  · exact ge_of_tendsto' h_total fun N =>
      le_of_eq (finiteExpectedPayoff_add_terminal_eq_value P L beta u V h_bellman N).symm

end OrderedObservable

/-! ## Concrete closed-loop box pullbacks -/

/-- The bounded-continuous observable space on the sanctions state interval. -/
abbrev StateBCF :=
  BoundedContinuousFunction (Subtype Sanctions.S) Real

private theorem movAvgReal_add_observable
    (h : Real)
    (U W : BoundedContinuousFunction (Subtype Sanctions.S) Real) (y : Real) :
    Sanctions.movAvgReal h (U + W) y =
      Sanctions.movAvgReal h U y + Sanctions.movAvgReal h W y := by
  unfold Sanctions.movAvgReal
  change (1 / (2 * h)) * ∫ z in (y - h)..(y + h),
      U (Sanctions.clipS' z) + W (Sanctions.clipS' z) = _
  have h_add :
      (∫ z in (y - h)..(y + h),
          U (Sanctions.clipS' z) + W (Sanctions.clipS' z)) =
        (∫ z in (y - h)..(y + h), U (Sanctions.clipS' z)) +
          ∫ z in (y - h)..(y + h), W (Sanctions.clipS' z) :=
    intervalIntegral.integral_add
      ((Sanctions.clipComp_cont U).intervalIntegrable _ _)
      ((Sanctions.clipComp_cont W).intervalIntegrable _ _)
  rw [h_add]
  ring_nf
  rfl

private theorem movAvgReal_smul_observable
    (h : Real) (c : Real)
    (U : BoundedContinuousFunction (Subtype Sanctions.S) Real) (y : Real) :
    Sanctions.movAvgReal h (c • U) y = c * Sanctions.movAvgReal h U y := by
  unfold Sanctions.movAvgReal
  change (1 / (2 * h)) * ∫ z in (y - h)..(y + h),
      c * U (Sanctions.clipS' z) = _
  rw [intervalIntegral.integral_const_mul]
  ring_nf
  rfl

private theorem movAvgReal_one_observable
    (h : Real) (hh : 0 < h) (y : Real) :
    Sanctions.movAvgReal h (1 : StateBCF) y = 1 := by
  unfold Sanctions.movAvgReal
  change (1 / (2 * h)) * ∫ _z in (y - h)..(y + h), (1 : Real) = 1
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

private theorem movAvgReal_mono_observable
    (h : Real) (hh : 0 < h)
    {U W : BoundedContinuousFunction (Subtype Sanctions.S) Real}
    (hUW : U <= W) (y : Real) :
    Sanctions.movAvgReal h U y <= Sanctions.movAvgReal h W y := by
  unfold Sanctions.movAvgReal
  apply mul_le_mul_of_nonneg_left
  · exact intervalIntegral.integral_mono_on
      (by linarith : y - h <= y + h)
      ((Sanctions.clipComp_cont U).intervalIntegrable _ _)
      ((Sanctions.clipComp_cont W).intervalIntegrable _ _)
      (fun z _hz => hUW (Sanctions.clipS' z))
  · positivity

/-- Evaluation at a state is a positive, unital, real-linear functional. -/
def pointEvaluation (x0 : Subtype Sanctions.S) :
    PositiveUnitalLinearFunctional StateBCF where
  toFun f := f x0
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_one := rfl
  monotone hfg := hfg x0

/-- The concrete box-noise closed-loop pullback is positive, unital, and
real-linear whenever its deterministic drift is continuous. -/
def closedLoopPullbackOperator
    (g : Subtype Sanctions.S -> Real) (hg : Continuous g)
    (h : Real) (hh : 0 < h) :
    PositiveUnitalLinearPullback StateBCF where
  toFun := Sanctions.closedLoopPullback g hg h hh
  map_add U W := by
    ext x
    exact movAvgReal_add_observable h U W (g x)
  map_smul c U := by
    ext x
    exact movAvgReal_smul_observable h c U (g x)
  map_one := by
    ext x
    exact movAvgReal_one_observable h hh (g x)
  monotone := by
    intro U W hUW x
    exact movAvgReal_mono_observable h hh hUW (g x)

/-- A time-indexed family of continuous drifts produces the abstract pullback
sequence used by the Feynman--Kac telescope. -/
def closedLoopPullbackSequence
    (g : Nat -> Subtype Sanctions.S -> Real)
    (hg : forall n, Continuous (g n))
    (h : Real) (hh : 0 < h) :
    PullbackSequence StateBCF :=
  fun n => closedLoopPullbackOperator (g n) (hg n) h hh

end FeynmanKacVerification
end Sanctions
