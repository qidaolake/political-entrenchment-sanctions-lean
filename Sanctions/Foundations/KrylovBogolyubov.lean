/-
# Krylov–Bogolyubov: existence of an invariant probability law

External-theory source (Rule 19): Krylov–Bogolyubov (1937), "La théorie
générale de la mesure dans son application à l'étude des systèmes dynamiques
de la mécanique non linéaire"; textbook form Stokey–Lucas–Prescott,
*Recursive Methods in Economic Dynamics*, Theorem 12.10 (existence of an
invariant probability measure for a Feller Markov operator on a compact
state space, via Cesàro averages of the iterates).

This file supplies the ONE assembly lemma absent from mathlib (grep
`Krylov|Bogolyubov` over the pinned revision: zero declarations; no
Markov–Kakutani / Schauder either): a Markov operator on the probability
measures of a compact metric space has an invariant law.

## Design

The operator is taken **unbundled** (`T : Measure E → Measure E`) with two
hypotheses that together say "T is a Feller Markov operator":

* `hTprob` — T maps probability measures to probability measures;
* `hadj`  — T has a **Feller adjoint** `S` on bounded continuous functions:
  `∫ f d(T μ) = ∫ (S f) dμ` for every probability `μ` and every
  `f : E →ᵇ ℝ`.

The adjoint hypothesis does double duty. It replaces *linearity* of T (the
Cesàro telescoping is performed on real integrals through `S`, never on
measures, so no `ℝ≥0∞`-subtraction issues arise), and it replaces *weak
continuity* of T (the limit exchange `∫ f d(T μ*) = ∫ (S f) dμ*` is the
adjoint identity itself, applied at the cluster point). This matches
exactly what the project has already proved for the box transfer operator
(`boxTransfer_adjoint`, `Foundations/BoxTransfer.lean`).

## Proof (SLP Thm 12.10, Cesàro route)

Starting from `μ₀ = dirac x₀`, form the iterates `ν n = T^[n] μ₀` and the
Cesàro averages `A_N = (N+1)⁻¹ • ∑_{n ≤ N} ν n` (probability measures).
`ProbabilityMeasure E` is compact (Prokhorov, mathlib) and metrizable
(Lévy–Prokhorov, mathlib), hence sequentially compact: extract
`A_{φ k} → μ*` weakly. For each `f : E →ᵇ ℝ`, the adjoint gives the
telescoping identity

  `∫ (S f) dA_N − ∫ f dA_N = (N+1)⁻¹ ((∫ f dν_{N+1}) − (∫ f dν₀))`,

whose absolute value is at most `2‖f‖/(N+1) → 0`; weak convergence sends
the left side to `∫ (S f) dμ* − ∫ f dμ*`, so the two limits agree
(`tendsto_nhds_unique`) and `∫ (S f) dμ* = ∫ f dμ*`. The adjoint identity
at `μ*` then gives `∫ f d(T μ*) = ∫ f dμ*` for every bounded continuous
`f`, and the metric determining-class lemma
(`ext_of_forall_integral_eq_of_IsFiniteMeasure`) closes `T μ* = μ*`.

## Box wiring

`boxTransfer_exists_invariant` discharges the two hypotheses from the
existing `boxTransfer_isProb` / `boxTransfer_adjoint` (with adjoint
`S := boxPullback δ h hh`). Combined with the existing uniqueness
(`boxTransfer_unique_invariant`) and geometric convergence
(`boxTransfer_dualKR_geometric`), the headline
`boxTransfer_existsUnique_invariant_attracting` states: the box-shocked
sanction dynamics admit exactly one invariant probability law, and every
probability start converges to it geometrically at rate `(1−δ)` in the
dual Kantorovich–Rubinstein distance. This retires the last cited
(non-machine-checked) step of the wash-out regime: existence is now
constructed, not cited.

No new assumptions are introduced (Rule 3): the box headline's hypotheses
(`0 < h`, `0 < δ`, `δ < 1`) cover everything the existing box lemmas need.
Since round BH-2 (item BH2.11) the contraction, uniqueness and geometric box
lemmas need only `δ ≤ 1`; the headline keeps `δ < 1` by its pinned statement
and passes `hδ1.le`, so its `δ < 1` is stronger than its proof uses. For a
general transition, the constant-sanction chain
`x' = clipS'(F(x, s̄) + η)` has the same three properties at rate `ghiⁿ` when
its section `y ↦ F(y, s̄)` lies in a state chord band with `0 ≤ glo` and
`ghi < 1` (`closedLoopBoxTransfer_existsUnique_invariant_attracting_of_stateChordBand`,
`Foundations/ClosedLoopBoxTransfer.lean`).
-/
import Sanctions.Foundations.BoxTransfer
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sanctions

open MeasureTheory BoundedContinuousFunction Filter Topology

open scoped ENNReal NNReal

noncomputable section

/-! ## Cesàro averages of a sequence of measures -/

/-- The `N`-th Cesàro average `(N+1)⁻¹ • (ν 0 + ⋯ + ν N)` of a sequence of
measures. For a sequence of probability measures this is again a
probability measure (`cesaroAverage_isProbabilityMeasure`). -/
def cesaroAverage {E : Type*} [MeasurableSpace E] (ν : ℕ → Measure E) (N : ℕ) :
    Measure E :=
  ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N + 1), ν n

/-- A Cesàro average of probability measures is a probability measure. -/
theorem cesaroAverage_isProbabilityMeasure {E : Type*} [MeasurableSpace E]
    {ν : ℕ → Measure E} (hν : ∀ n, IsProbabilityMeasure (ν n)) (N : ℕ) :
    IsProbabilityMeasure (cesaroAverage ν N) := by
  refine ⟨?_⟩
  rw [cesaroAverage, Measure.smul_apply, Measure.finset_sum_apply,
    Finset.sum_congr rfl fun n _ => (hν n).measure_univ,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Nat.succ_ne_zero N)
    (ENNReal.natCast_ne_top _)

/-- The Bochner integral of a bounded continuous function against a Cesàro
average is the arithmetic mean of the integrals against the summands. -/
theorem integral_cesaroAverage {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {ν : ℕ → Measure E} (hν : ∀ n, IsProbabilityMeasure (ν n))
    (f : E →ᵇ ℝ) (N : ℕ) :
    ∫ x, f x ∂(cesaroAverage ν N)
      = ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), ∫ x, f x ∂(ν n) := by
  have hint : ∀ n ∈ Finset.range (N + 1), Integrable f (ν n) := fun n _ => by
    haveI := hν n
    exact f.integrable (ν n)
  have hcoef : (((N + 1 : ℕ) : ℝ≥0∞)⁻¹).toReal = ((N : ℝ) + 1)⁻¹ := by
    rw [ENNReal.toReal_inv]
    norm_cast
  rw [cesaroAverage, integral_smul_measure, integral_finset_sum_measure hint,
    hcoef, smul_eq_mul]

/-! ## The Krylov–Bogolyubov existence lemma -/

/-- **Krylov–Bogolyubov / SLP Theorem 12.10.** A Feller Markov operator on
the probability measures of a nonempty compact metric space has an
invariant probability law.

The operator is unbundled: `hTprob` says `T` preserves probability
measures, and `hadj` says `T` has a Feller adjoint `S` on bounded
continuous functions (`∫ f d(T μ) = ∫ (S f) dμ`). The adjoint hypothesis
subsumes both the linearity and the weak continuity of a Markov operator
(see the file docstring); it is exactly the identity the box transfer
operator already satisfies (`boxTransfer_adjoint`). -/
theorem exists_invariant_of_adjoint
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E]
    [SecondCountableTopology E] [BorelSpace E] [Nonempty E]
    (T : Measure E → Measure E) (S : (E →ᵇ ℝ) → (E →ᵇ ℝ))
    (hTprob : ∀ μ : Measure E, IsProbabilityMeasure μ → IsProbabilityMeasure (T μ))
    (hadj : ∀ μ : Measure E, IsProbabilityMeasure μ →
      ∀ f : E →ᵇ ℝ, (∫ x, f x ∂(T μ)) = ∫ x, (S f) x ∂μ) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ T μ = μ := by
  classical
  -- Compile-time instance asserts: the space of probability laws on a
  -- compact metric space is compact (Prokhorov) and first countable
  -- (Lévy–Prokhorov metrizability), so sequences have convergent
  -- subsequences.
  haveI : CompactSpace (ProbabilityMeasure E) := inferInstance
  haveI : FirstCountableTopology (ProbabilityMeasure E) := inferInstance
  obtain ⟨x₀⟩ := (inferInstance : Nonempty E)
  -- The iterates of the point mass at `x₀`.
  set ν : ℕ → Measure E := fun n => T^[n] (Measure.dirac x₀) with hν_def
  have hνsucc : ∀ n, ν (n + 1) = T (ν n) := fun n =>
    Function.iterate_succ_apply' T n (Measure.dirac x₀)
  have hν : ∀ n, IsProbabilityMeasure (ν n) := by
    intro n
    induction n with
    | zero => change IsProbabilityMeasure (Measure.dirac x₀); infer_instance
    | succ n ih => rw [hνsucc n]; exact hTprob _ ih
  have hA : ∀ N, IsProbabilityMeasure (cesaroAverage ν N) :=
    cesaroAverage_isProbabilityMeasure hν
  -- Extract a weak cluster point of the Cesàro averages.
  set PA : ℕ → ProbabilityMeasure E := fun N => ⟨cesaroAverage ν N, hA N⟩ with hPA
  obtain ⟨μstar, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq PA
  -- Weak convergence, read through integrals of bounded continuous functions.
  have hint : ∀ g : E →ᵇ ℝ,
      Tendsto (fun k => ∫ x, g x ∂(cesaroAverage ν (φ k))) atTop
        (𝓝 (∫ x, g x ∂(μstar : Measure E))) := by
    intro g
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
    simpa [hPA, Function.comp] using h
  -- The cluster point is adjoint-invariant on every test function.
  have key : ∀ f : E →ᵇ ℝ,
      (∫ x, (S f) x ∂(μstar : Measure E)) = ∫ x, f x ∂(μstar : Measure E) := by
    intro f
    -- Telescoping identity at each Cesàro index.
    have htel : ∀ N : ℕ,
        (∫ x, (S f) x ∂(cesaroAverage ν N)) - ∫ x, f x ∂(cesaroAverage ν N)
          = ((N : ℝ) + 1)⁻¹
              * ((∫ x, f x ∂(ν (N + 1))) - ∫ x, f x ∂(ν 0)) := by
      intro N
      rw [integral_cesaroAverage hν (S f) N, integral_cesaroAverage hν f N,
        ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      have hstep : ∀ n ∈ Finset.range (N + 1),
          (∫ x, (S f) x ∂(ν n)) - ∫ x, f x ∂(ν n)
            = (∫ x, f x ∂(ν (n + 1))) - ∫ x, f x ∂(ν n) := by
        intro n _
        have hStoT : (∫ x, (S f) x ∂(ν n)) = ∫ x, f x ∂(ν (n + 1)) := by
          rw [← hadj (ν n) (hν n) f, ← hνsucc n]
        rw [hStoT]
      calc ∑ n ∈ Finset.range (N + 1),
              ((∫ x, (S f) x ∂(ν n)) - ∫ x, f x ∂(ν n))
          = ∑ n ∈ Finset.range (N + 1),
              ((∫ x, f x ∂(ν (n + 1))) - ∫ x, f x ∂(ν n)) :=
            Finset.sum_congr rfl hstep
        _ = (∫ x, f x ∂(ν (N + 1))) - ∫ x, f x ∂(ν 0) :=
            Finset.sum_range_sub (fun m => ∫ x, f x ∂(ν m)) (N + 1)
    -- The telescoped difference is `O(1/N)`.
    have hbound : ∀ N : ℕ,
        |(∫ x, (S f) x ∂(cesaroAverage ν N)) - ∫ x, f x ∂(cesaroAverage ν N)|
          ≤ 2 * ‖f‖ * ((N : ℝ) + 1)⁻¹ := by
      intro N
      have hAbs : ∀ m : ℕ, |∫ x, f x ∂(ν m)| ≤ ‖f‖ := fun m => by
        haveI := hν m
        simpa [Real.norm_eq_abs] using norm_integral_le_norm (ν m) f
      have hdiff : |(∫ x, f x ∂(ν (N + 1))) - ∫ x, f x ∂(ν 0)| ≤ 2 * ‖f‖ := by
        have h := abs_sub (∫ x, f x ∂(ν (N + 1))) (∫ x, f x ∂(ν 0))
        have h1 := hAbs (N + 1)
        have h0 := hAbs 0
        linarith
      rw [htel N, abs_mul, abs_inv, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ) + 1)]
      calc ((N : ℝ) + 1)⁻¹ * |(∫ x, f x ∂(ν (N + 1))) - ∫ x, f x ∂(ν 0)|
          ≤ ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖) := by gcongr
        _ = 2 * ‖f‖ * ((N : ℝ) + 1)⁻¹ := by ring
    -- Along the convergent subsequence the difference tends both to
    -- `∫ (S f) dμ* − ∫ f dμ*` and (by the `O(1/N)` bound) to `0`.
    have hg : Tendsto
        (fun k => (∫ x, (S f) x ∂(cesaroAverage ν (φ k)))
          - ∫ x, f x ∂(cesaroAverage ν (φ k))) atTop
        (𝓝 ((∫ x, (S f) x ∂(μstar : Measure E))
          - ∫ x, f x ∂(μstar : Measure E))) :=
      (hint (S f)).sub (hint f)
    have hbnd2 : ∀ k : ℕ,
        ‖(∫ x, (S f) x ∂(cesaroAverage ν (φ k)))
          - ∫ x, f x ∂(cesaroAverage ν (φ k))‖
          ≤ 2 * ‖f‖ * ((k : ℝ) + 1)⁻¹ := by
      intro k
      rw [Real.norm_eq_abs]
      refine (hbound (φ k)).trans ?_
      have hle : ((k : ℝ) + 1) ≤ ((φ k : ℝ) + 1) := by
        have hk : k ≤ φ k := hφ.le_apply
        exact_mod_cast Nat.succ_le_succ hk
      gcongr
    have hzero : Tendsto
        (fun k => (∫ x, (S f) x ∂(cesaroAverage ν (φ k)))
          - ∫ x, f x ∂(cesaroAverage ν (φ k))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      have hg0 : Tendsto (fun k : ℕ => 2 * ‖f‖ * ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        simpa using h1.const_mul (2 * ‖f‖)
      exact squeeze_zero_norm hbnd2 hg0
    have hEq := tendsto_nhds_unique hg hzero
    linarith
  -- Conclude `T μ* = μ*` from the determining class of bounded continuous
  -- functions on a (pseudo-)metrizable space.
  have hμP : IsProbabilityMeasure (μstar : Measure E) := μstar.prop
  refine ⟨(μstar : Measure E), hμP, ?_⟩
  haveI := hμP
  haveI : IsProbabilityMeasure (T (μstar : Measure E)) := hTprob _ hμP
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [hadj _ hμP f]
  exact key f

/-! ## Wiring: the box transfer operator has an invariant law -/

/-- **Existence of an invariant law for the box transfer operator**
(Krylov–Bogolyubov applied at `T := boxTransfer δ h` with Feller adjoint
`S := boxPullback δ h hh`). Both hypotheses of the abstract lemma are the
existing box lemmas `boxTransfer_isProb` and `boxTransfer_adjoint`; the
typeclass requirements are automatic on the compact state space `↥S`. -/
theorem boxTransfer_exists_invariant (δ h : ℝ) (hh : 0 < h) :
    ∃ μ : Measure ↥(Sanctions.S : Set ℝ),
      IsProbabilityMeasure μ ∧ boxTransfer δ h μ = μ :=
  exists_invariant_of_adjoint (boxTransfer δ h) (boxPullback δ h hh)
    (fun μ hμ => by haveI := hμ; exact boxTransfer_isProb δ h hh μ)
    (fun μ hμ f => by haveI := hμ; exact boxTransfer_adjoint δ h hh μ f)

/-- Iterates of the box transfer operator preserve probability. -/
theorem boxTransfer_iterate_isProb (δ h : ℝ) (hh : 0 < h)
    (μ0 : Measure ↥(Sanctions.S : Set ℝ)) (hμ0 : IsProbabilityMeasure μ0) :
    ∀ n : ℕ, IsProbabilityMeasure ((boxTransfer δ h)^[n] μ0) := by
  intro n
  induction n with
  | zero => simpa using hμ0
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    haveI := ih
    exact boxTransfer_isProb δ h hh _

/-- **The wash-out headline, fully machine-checked**: for `0 < h`,
`0 < δ < 1`, the box-shocked sanction dynamics admit an invariant
probability law `lam` that is

* **existent** — constructed by Krylov–Bogolyubov (no citation left);
* **unique** — any invariant probability law equals `lam`
  (`boxTransfer_unique_invariant`);
* **globally attracting at geometric rate** — from every probability
  start `μ0`, the iterates approach `lam` at rate `(1 − δ)ⁿ` in the dual
  Kantorovich–Rubinstein distance (`boxTransfer_dualKR_geometric`).

No new assumptions: the hypothesis surface is exactly that of the
pre-existing uniqueness and contraction lemmas. -/
theorem boxTransfer_existsUnique_invariant_attracting
    (δ h : ℝ) (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ lam : Measure ↥(Sanctions.S : Set ℝ),
      (IsProbabilityMeasure lam ∧ boxTransfer δ h lam = lam)
      ∧ (∀ ν : Measure ↥(Sanctions.S : Set ℝ),
          IsProbabilityMeasure ν → boxTransfer δ h ν = ν → ν = lam)
      ∧ ∀ μ0 : Measure ↥(Sanctions.S : Set ℝ), IsProbabilityMeasure μ0 →
          ∀ n : ℕ, dualKR ((boxTransfer δ h)^[n] μ0) lam
            ≤ (1 - δ) ^ n * dualKR μ0 lam := by
  obtain ⟨lam, hlamP, hlamFix⟩ := boxTransfer_exists_invariant δ h hh
  refine ⟨lam, ⟨hlamP, hlamFix⟩, ?_, ?_⟩
  · intro ν hν hfix
    haveI := hν; haveI := hlamP
    exact boxTransfer_unique_invariant δ h hh hδ0 hδ1.le ν lam hfix hlamFix
  · intro μ0 hμ0 n
    haveI := hlamP
    have hgeom := boxTransfer_dualKR_geometric δ h hh hδ1.le
      (fun m => (boxTransfer δ h)^[m] μ0) lam
      (boxTransfer_iterate_isProb δ h hh μ0 hμ0)
      (fun m => Function.iterate_succ_apply' (boxTransfer δ h) m μ0) hlamFix n
    simpa using hgeom

end

end Sanctions
