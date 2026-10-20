/-
Sanctions/Foundations/ClosedLoopBoxTransfer.lean

**The box transfer operator with STATE-DEPENDENT drift, its Feller adjoint,
Krylov–Bogolyubov existence of an invariant law, and the conditional
(`Lip(g) < 1`) dual-Kantorovich uniqueness/attraction route.**

`Foundations/BoxTransfer.lean` constructs the box-noise transfer operator for
the CONSTANT-sanction drift `x' = clipS'((1−δ)·x + δ + η)` and proves its
adjoint identity, `(1−δ)`-contraction, uniqueness, and geometric attraction;
`Foundations/KrylovBogolyubov.lean` constructs existence. This file supplies
the missing generalization: the same chain with an **arbitrary drift**
`g : ↥S → ℝ`,

  `x' = clipS'(g(x) + η)`,   `η ~ boxNoise h`  (uniform on `[−h, h]`),

which is the closed-loop form of an *equilibrium-driven* (endogenous) state
chain `g(x) = F(x, s_real(x))` for a realized-sanction rule `s_real` (the
project wiring lives in `Sanctions/Examples/ClosedLoopInvariantLaw.lean`; per
Rule 19 this file stays generic — no economics beyond the already-Foundations
state space `↥S`, clip `clipS'`, and the Foundations chord predicates on a
transition `F` (`StateChordBand`, `SanctionLowerChord`), all general in `F`).

Contents:
* `closedLoopBoxTransfer g h` — pushforward of `μ ⊗ boxNoise h` under
  `(x, η) ↦ clipS'(g x + η)` (mirrors `boxTransfer`, drift generalized);
* `closedLoopBoxTransfer_isProb` — probability preservation (continuous `g`);
* `closedLoopPullback` — the Feller adjoint `f ↦ movAvgReal h f ∘ g` on test
  functions, with the adjoint identity `closedLoopBoxTransfer_adjoint`
  (mirrors `boxTransfer_adjoint`: `integral_map` + Bochner Fubini + the
  translation change of variables — no dominated convergence needed, since
  the smear `movAvgReal h f` is already Lipschitz-continuous on `ℝ` and the
  adjoint is its composition with the continuous drift);
* **`closedLoopBoxTransfer_exists_invariant`** — for EVERY continuous drift
  the chain has an invariant probability law (Krylov–Bogolyubov engine
  `exists_invariant_of_adjoint`, unconditional in the drift's slope);
* the CONDITIONAL contraction route: if `g` is `L`-Lipschitz with `L < 1`
  then `closedLoopPullback` maps 1-Lipschitz test functions to `L`-Lipschitz
  ones (`closedLoopPullback_lipschitz`), so the operator is an
  `L`-contraction in `dualKR` (`closedLoopBoxTransfer_dualKR_contraction`),
  the invariant law is unique (`closedLoopBoxTransfer_unique_invariant`),
  attraction is geometric at rate `Lⁿ`
  (`closedLoopBoxTransfer_dualKR_geometric`), and the package assembles as
  `closedLoopBoxTransfer_existsUnique_invariant_attracting`. No sign
  condition on `L` is assumed: `0 ≤ L` follows from the Lipschitz bound
  itself (`closedLoopDrift_lipConst_nonneg`; round BH-2, item BH2.11). This
  is honest generality: the route fires only when the drift contracts;
* **general transition, constant sanction**
  (`closedLoopBoxTransfer_existsUnique_invariant_attracting_of_stateChordBand`):
  if the section `y ↦ F(y, s̄)` lies in a state chord band with `0 ≤ glo` and
  `ghi < 1`, the chain `x' = clipS'(F(x, s̄) + η)` has a unique invariant law
  attracting at rate `ghiⁿ` — the wash-out law for any such `F`;
* **when the route is blocked** (`closedLoop_lipConst_ge_of_diagonal_crossing`,
  `closedLoop_not_contracting_of_diagonal_crossing`): if the rule `R` of a
  drift `g(x) = F(x, R(x))` crosses the diagonal and rises above it at
  excess slope `k ≥ 0`, then with `F x x = x` and a sanction lower chord
  `d ≥ 0` every Lipschitz constant of `g` is at least `1 + d·k`, so no
  `L < 1` exists. At the strong-rally witness rule (the P3 myopic rule
  `clip((9/8)x − 1/12)` under `affineF δ`) `k = 1/8` and `d = δ`, so the
  closed-loop slope is at least `1 + δ/8`, above `1` for `δ > 0`
  (`affineP3ClosedLoopDrift_lipConst_ge`, `p3ClosedLoopDrift_lipConst_ge` in
  the Examples wiring): there existence stands and uniqueness is honestly open.
  No equilibrium realized-sanction drift is checked against these hypotheses;
* compatibility: at the constant-sanction affine drift
  `g(x) = (1−δ)·x + δ` the new operator IS `boxTransfer`
  (`closedLoopBoxTransfer_affine_const`, definitional), so the wash-out
  headline's object is the constant-drift special case.

No new assumptions (Rule 3): every declaration is a `def` or a theorem whose
hypotheses (`Continuous g`, `0 < h`, a Lipschitz bound on `g` for the
conditional route; the chord predicates of `Foundations/SemiconcaveRiccati.lean`
and `Foundations/TransitionChords.lean` for the general-`F` statements) are
theorem-level inputs discharged by consumers.
-/

import Sanctions.Foundations.KrylovBogolyubov
import Sanctions.Foundations.SemiconcaveRiccati

open MeasureTheory BoundedContinuousFunction

namespace Sanctions

noncomputable section

/-! ## The closed-loop-plus-noise map and transfer operator -/

/-- The closed-loop-plus-noise map `↥S × ℝ → ↥S` with **state-dependent
drift** `g`: `(x, η) ↦ clipS'(g x + η)`. Generalizes `boxLoopMap` (whose
drift is the constant-sanction affine `(1−δ)·x + δ`). -/
noncomputable def closedLoopMap (g : ↥(Sanctions.S) → ℝ) :
    ↥(Sanctions.S) × ℝ → ↥(Sanctions.S) :=
  fun p => Sanctions.clipS' (g p.1 + p.2)

theorem closedLoopMap_continuous (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g) :
    Continuous (closedLoopMap g) := by
  unfold closedLoopMap
  exact Sanctions.clipS'_continuous.comp ((hg.comp continuous_fst).add continuous_snd)

/-- **Closed-loop box transfer operator** `T*μ`: the law of `clipS'(g(X) + η)`
when `X ~ μ` and the noise `η ~ boxNoise h` are independent, realised as the
pushforward of the product `μ ⊗ boxNoise h`. For an equilibrium-driven chain,
`g(x) = F(x, s_real(x))` is the pre-noise next state under the realized
policy; this operator is the endogenous counterpart of `boxTransfer`. -/
noncomputable def closedLoopBoxTransfer (g : ↥(Sanctions.S) → ℝ) (h : ℝ)
    (μ : Measure ↥(Sanctions.S)) : Measure ↥(Sanctions.S) :=
  Measure.map (closedLoopMap g) (μ.prod (boxNoise h))

/-- The closed-loop transfer operator preserves probability measures. -/
theorem closedLoopBoxTransfer_isProb (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 < h) (μ : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (closedLoopBoxTransfer g h μ) := by
  have : IsProbabilityMeasure (boxNoise h) := boxNoise_isProb h hh
  rw [closedLoopBoxTransfer]
  exact Measure.isProbabilityMeasure_map (closedLoopMap_continuous g hg).measurable.aemeasurable

/-! ## The Feller adjoint -/

/-- **Closed-loop dual pullback (Feller adjoint)** on test functions over `↥S`:
`(closedLoopPullback g hg h hh f)(x) = movAvgReal h f (g x)` — the box smear of
`f` evaluated along the drift `g`. Generalizes `boxPullback` (the same smear
evaluated along the constant-sanction affine loop). Continuity is free: the
smear is Lipschitz on `ℝ` (`movAvgReal_continuous`) and `g` is continuous. -/
noncomputable def closedLoopPullback (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 < h) (f : ↥(Sanctions.S) →ᵇ ℝ) : ↥(Sanctions.S) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Sanctions.movAvgReal h f (g x),
     (Sanctions.movAvgReal_continuous hh f).comp hg⟩

@[simp] theorem closedLoopPullback_apply (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 < h) (f : ↥(Sanctions.S) →ᵇ ℝ) (x : ↥(Sanctions.S)) :
    closedLoopPullback g hg h hh f x = Sanctions.movAvgReal h f (g x) := rfl

/-- **Inner noise integral = the smear at the drift.** Integrating a test
function `f` along the closed loop with box noise equals the moving-average
pullback evaluated at `g x`, by a translation change of variables (mirrors
`boxNoise_integral_eq_boxPullback` with `c := g x`). -/
theorem closedLoopNoise_integral_eq_pullback (g : ↥(Sanctions.S) → ℝ)
    (hg : Continuous g) (h : ℝ) (hh : 0 < h)
    (f : ↥(Sanctions.S) →ᵇ ℝ) (x : ↥(Sanctions.S)) :
    (∫ η, f (Sanctions.clipS' (g x + η)) ∂(boxNoise h))
      = closedLoopPullback g hg h hh f x := by
  rw [closedLoopPullback_apply]
  set c := g x with hc
  rw [boxNoise, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (2 * h)),
      smul_eq_mul, movAvgReal]
  congr 1
  -- ∫ η in Icc(-h,h), f(clipS'(c+η)) = ∫ z in (c-h)..(c+h), f(clipS' z)
  rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  have hcomp := intervalIntegral.integral_comp_add_left
    (f := fun z => f (Sanctions.clipS' z)) (a := -h) (b := h) c
  rw [hcomp, show c + -h = c - h by ring]

/-- **The closed-loop transfer-operator adjoint identity.** For any bounded
continuous test function `f`, integrating `f` against the push-forward `T*μ`
equals integrating the drift-composed smear `closedLoopPullback f` against
`μ`. This is the Feller-adjoint hypothesis of both the Krylov–Bogolyubov
engine (`exists_invariant_of_adjoint`) and the dual-Kantorovich contraction
(`dualKR_le_of_adjoint_lipschitz`), discharged concretely (mirrors
`boxTransfer_adjoint`). -/
theorem closedLoopBoxTransfer_adjoint (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 < h)
    (μ : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ]
    (f : ↥(Sanctions.S) →ᵇ ℝ) :
    (∫ y, f y ∂(closedLoopBoxTransfer g h μ))
      = ∫ x, closedLoopPullback g hg h hh f x ∂μ := by
  have hprob : IsProbabilityMeasure (boxNoise h) := boxNoise_isProb h hh
  have hGmeas : AEMeasurable (closedLoopMap g) (μ.prod (boxNoise h)) :=
    (closedLoopMap_continuous g hg).measurable.aemeasurable
  have hInt : Integrable (fun p => f (closedLoopMap g p)) (μ.prod (boxNoise h)) :=
    ⟨(f.continuous.comp (closedLoopMap_continuous g hg)).aestronglyMeasurable,
     HasFiniteIntegral.of_bounded (C := ‖f‖)
       (Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm (closedLoopMap g p)))⟩
  rw [closedLoopBoxTransfer, integral_map hGmeas f.continuous.aestronglyMeasurable,
      integral_prod _ hInt]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact closedLoopNoise_integral_eq_pullback g hg h hh f x

/-! ## Existence of an invariant law (unconditional in the drift's slope) -/

/-- **Existence of an invariant law for every continuous drift**
(Krylov–Bogolyubov applied at `T := closedLoopBoxTransfer g h` with Feller
adjoint `S := closedLoopPullback g hg h hh`). The box-noise chain
`x' = clipS'(g(x) + η)` admits an invariant probability law for **any**
continuous drift `g` — in particular for the equilibrium closed-loop drift
`g(x) = F(x, s_real(x))` of an endogenous state chain, with no restriction
on the drift's Lipschitz slope. Uniqueness/attraction need the separate
conditional contraction route below. -/
theorem closedLoopBoxTransfer_exists_invariant (g : ↥(Sanctions.S) → ℝ)
    (hg : Continuous g) (h : ℝ) (hh : 0 < h) :
    ∃ μ : Measure ↥(Sanctions.S),
      IsProbabilityMeasure μ ∧ closedLoopBoxTransfer g h μ = μ :=
  exists_invariant_of_adjoint (closedLoopBoxTransfer g h) (closedLoopPullback g hg h hh)
    (fun μ hμ => by haveI := hμ; exact closedLoopBoxTransfer_isProb g hg h hh μ)
    (fun μ hμ f => by haveI := hμ; exact closedLoopBoxTransfer_adjoint g hg h hh μ f)

/-! ## The conditional contraction route (`Lip(g) < 1` only) -/

/-- **A Lipschitz constant of a drift on the state space is nonnegative.** The
state space `↥S = [0,1]` has two points at distance `1`, so the bound
`|g x − g y| ≤ L·dist x y` at `x = 0`, `y = 1` reads `0 ≤ |g 0 − g 1| ≤ L`. This is
why the conditional route below carries no separate `0 ≤ L` or `0 < L` binder
(round BH-2, item BH2.11). Generic: no transition law is involved. -/
theorem closedLoopDrift_lipConst_nonneg {g : ↥(Sanctions.S) → ℝ} {L : ℝ}
    (hgL : ∀ x y : ↥(Sanctions.S), |g x - g y| ≤ L * dist x y) : 0 ≤ L := by
  have h := hgL ⟨0, by norm_num [Sanctions.S, Sanctions.I]⟩
    ⟨1, by norm_num [Sanctions.S, Sanctions.I]⟩
  rw [Subtype.dist_eq, Real.dist_eq] at h
  norm_num at h
  exact le_trans (abs_nonneg _) h

/-- **The closed-loop pullback maps 1-Lipschitz test functions to
`L`-Lipschitz ones when the drift is `L`-Lipschitz** — the `hS` hypothesis of
`dualKR_le_of_adjoint_lipschitz_of_nonneg` at factor `L`. The smear preserves the
test function's Lipschitz constant (`movAvgReal_valueLipschitz`, window-width
independent: the box smear is exactly W₁-nonexpansive, so no `h`-margin
exists in this route), and composition with the `L`-Lipschitz drift scales it
by `L`. Generic in the drift. The former binder `0 ≤ L` is derived from the
bound (`closedLoopDrift_lipConst_nonneg`; round BH-2, item BH2.11). -/
theorem closedLoopPullback_lipschitz (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g)
    (h : ℝ) (hh : 0 < h) {L : ℝ}
    (hgL : ∀ x y : ↥(Sanctions.S), |g x - g y| ≤ L * dist x y)
    (f : ↥(Sanctions.S) →ᵇ ℝ) (hf : LipschitzWith 1 f) :
    LipschitzWith (Real.toNNReal L) (closedLoopPullback g hg h hh f) := by
  have hL0 : 0 ≤ L := closedLoopDrift_lipConst_nonneg hgL
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [closedLoopPullback_apply, closedLoopPullback_apply, Real.dist_eq,
      Real.coe_toNNReal _ hL0]
  have hfK : ∀ z₁ z₂ : ↥(Sanctions.S), |f z₂ - f z₁| ≤ (1:ℝ) * dist z₁ z₂ := by
    intro z₁ z₂
    have hd := hf.dist_le_mul z₁ z₂
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at hd
    rw [one_mul, abs_sub_comm]; exact hd
  have h1 := Sanctions.movAvgReal_valueLipschitz hh f (by norm_num : (0:ℝ) ≤ 1)
    hfK (g x) (g y)
  calc |Sanctions.movAvgReal h f (g x) - Sanctions.movAvgReal h f (g y)|
      ≤ 1 * |g x - g y| := h1
    _ = |g x - g y| := one_mul _
    _ ≤ L * dist x y := hgL x y

/-- **The closed-loop transfer operator is an `L`-contraction in `dualKR`
when the drift is `L`-Lipschitz** (take `L < 1` downstream for
uniqueness/attraction). Mirrors `boxTransfer_dualKR_contraction` with factor
`L` in place of `1 − δ`. Generic in the drift. The former binder `0 < L` is
dropped: `0 ≤ L` follows from the bound, and the dual contraction accepts the
factor `0` (round BH-2, item BH2.11). -/
theorem closedLoopBoxTransfer_dualKR_contraction (g : ↥(Sanctions.S) → ℝ)
    (hg : Continuous g) (h : ℝ) (hh : 0 < h) {L : ℝ}
    (hgL : ∀ x y : ↥(Sanctions.S), |g x - g y| ≤ L * dist x y)
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dualKR (closedLoopBoxTransfer g h μ) (closedLoopBoxTransfer g h ν)
      ≤ L * dualKR μ ν :=
  dualKR_le_of_adjoint_lipschitz_of_nonneg μ ν (closedLoopBoxTransfer g h μ)
    (closedLoopBoxTransfer g h ν) (closedLoopPullback g hg h hh)
    (closedLoopDrift_lipConst_nonneg hgL)
    (fun f hf => closedLoopPullback_lipschitz g hg h hh hgL f hf)
    (closedLoopBoxTransfer_adjoint g hg h hh μ)
    (closedLoopBoxTransfer_adjoint g hg h hh ν)

/-- **Conditional uniqueness of the invariant law.** If the drift is
`L`-Lipschitz with `L < 1`, two `closedLoopBoxTransfer`-invariant
probability measures coincide. Generic in the drift; the former binder
`0 < L` is dropped (round BH-2, item BH2.11). Honest boundary: at the
project's strong-rally witnesses the closed-loop slope is at least
`1 + δ/8 > 1`, so this hypothesis is provably unavailable there
(`closedLoop_not_contracting_of_diagonal_crossing` below, and
`p3ClosedLoopDrift_lipConst_ge` in the Examples wiring) — existence
(`closedLoopBoxTransfer_exists_invariant`) does not need it. -/
theorem closedLoopBoxTransfer_unique_invariant (g : ↥(Sanctions.S) → ℝ)
    (hg : Continuous g) (h : ℝ) (hh : 0 < h) {L : ℝ} (hL1 : L < 1)
    (hgL : ∀ x y : ↥(Sanctions.S), |g x - g y| ≤ L * dist x y)
    (μ ν : Measure ↥(Sanctions.S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : closedLoopBoxTransfer g h μ = μ) (hν : closedLoopBoxTransfer g h ν = ν) :
    μ = ν := by
  apply eq_of_dualKR_eq_zero
  refine dualKR_eq_zero_of_invariant_of_nonneg μ ν (closedLoopPullback g hg h hh)
    (c := L) (closedLoopDrift_lipConst_nonneg hgL) hL1
    (fun f hf => closedLoopPullback_lipschitz g hg h hh hgL f hf) ?_ ?_
  · intro f; rw [← closedLoopBoxTransfer_adjoint g hg h hh μ f, hμ]
  · intro f; rw [← closedLoopBoxTransfer_adjoint g hg h hh ν f, hν]

/-- **Conditional geometric attraction.** If `seq` is generated by iterating
`closedLoopBoxTransfer` at an `L`-Lipschitz drift and `lam` is invariant, the
dual distance to `lam` contracts as `Lⁿ` (attracting for `L < 1`). Generic in
the drift; the former binder `0 < L` is dropped (round BH-2, item BH2.11). -/
theorem closedLoopBoxTransfer_dualKR_geometric (g : ↥(Sanctions.S) → ℝ)
    (hg : Continuous g) (h : ℝ) (hh : 0 < h) {L : ℝ}
    (hgL : ∀ x y : ↥(Sanctions.S), |g x - g y| ≤ L * dist x y)
    (seq : ℕ → Measure ↥(Sanctions.S)) (lam : Measure ↥(Sanctions.S))
    (hseq : ∀ n, IsProbabilityMeasure (seq n)) [IsProbabilityMeasure lam]
    (hstep : ∀ n, seq (n + 1) = closedLoopBoxTransfer g h (seq n))
    (hlam : closedLoopBoxTransfer g h lam = lam) :
    ∀ n, dualKR (seq n) lam ≤ L ^ n * dualKR (seq 0) lam := by
  apply dualKR_geometric seq lam (closedLoopDrift_lipConst_nonneg hgL)
  intro n
  haveI := hseq n
  have hc := closedLoopBoxTransfer_dualKR_contraction g hg h hh hgL (seq n) lam
  rw [hlam] at hc
  rw [hstep n]
  exact hc

/-- Iterates of the closed-loop transfer operator preserve probability. -/
theorem closedLoopBoxTransfer_iterate_isProb (g : ↥(Sanctions.S) → ℝ)
    (hg : Continuous g) (h : ℝ) (hh : 0 < h)
    (μ0 : Measure ↥(Sanctions.S)) (hμ0 : IsProbabilityMeasure μ0) :
    ∀ n : ℕ, IsProbabilityMeasure ((closedLoopBoxTransfer g h)^[n] μ0) := by
  intro n
  induction n with
  | zero => simpa using hμ0
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    haveI := ih
    exact closedLoopBoxTransfer_isProb g hg h hh _

/-- **The conditional closed-loop headline**: for a continuous `L`-Lipschitz
drift with `L < 1` and noise half-width `0 < h`, the closed-loop chain
`x' = clipS'(g(x) + η)` admits an invariant probability law `lam` that is
existent (Krylov–Bogolyubov, constructed), unique, and globally attracting at
geometric rate `Lⁿ` in the dual Kantorovich–Rubinstein distance. At constant-
sanction drift this recovers the wash-out headline
(`boxTransfer_existsUnique_invariant_attracting`, rate `1 − δ`); at the
strong-rally witness rule (the P3 myopic rule under `affineF δ`) the `L < 1`
hypothesis provably fails (`closedLoop_lipConst_ge_of_diagonal_crossing`,
`closedLoop_not_contracting_of_diagonal_crossing`; instance
`p3ClosedLoopDrift_lipConst_ge` in the Examples wiring) and only the
unconditional existence half applies. Generic in the drift. The former binder `0 < L` is
dropped: `0 ≤ L` follows from the Lipschitz bound (round BH-2, item BH2.11). -/
theorem closedLoopBoxTransfer_existsUnique_invariant_attracting
    (g : ↥(Sanctions.S) → ℝ) (hg : Continuous g) (h : ℝ) (hh : 0 < h)
    {L : ℝ} (hL1 : L < 1)
    (hgL : ∀ x y : ↥(Sanctions.S), |g x - g y| ≤ L * dist x y) :
    ∃ lam : Measure ↥(Sanctions.S),
      (IsProbabilityMeasure lam ∧ closedLoopBoxTransfer g h lam = lam)
      ∧ (∀ ν : Measure ↥(Sanctions.S),
          IsProbabilityMeasure ν → closedLoopBoxTransfer g h ν = ν → ν = lam)
      ∧ ∀ μ0 : Measure ↥(Sanctions.S), IsProbabilityMeasure μ0 →
          ∀ n : ℕ, dualKR ((closedLoopBoxTransfer g h)^[n] μ0) lam
            ≤ L ^ n * dualKR μ0 lam := by
  obtain ⟨lam, hlamP, hlamFix⟩ := closedLoopBoxTransfer_exists_invariant g hg h hh
  refine ⟨lam, ⟨hlamP, hlamFix⟩, ?_, ?_⟩
  · intro ν hν hfix
    haveI := hν; haveI := hlamP
    exact closedLoopBoxTransfer_unique_invariant g hg h hh hL1 hgL ν lam hfix hlamFix
  · intro μ0 hμ0 n
    haveI := hlamP
    have hgeom := closedLoopBoxTransfer_dualKR_geometric g hg h hh hgL
      (fun m => (closedLoopBoxTransfer g h)^[m] μ0) lam
      (closedLoopBoxTransfer_iterate_isProb g hg h hh μ0 hμ0)
      (fun m => Function.iterate_succ_apply' (closedLoopBoxTransfer g h) m μ0) hlamFix n
    simpa using hgeom

/-! ## General transition, constant sanction: the wash-out law over a chord band

At a constant sanction `s̄` the closed-loop drift is the section `y ↦ F(y, s̄)`.
When that section lies in a state chord band `StateChordBand (F · s̄) glo ghi`
with `0 ≤ glo` and `ghi < 1`, it is `ghi`-Lipschitz on the state space, so the
conditional route fires with `L := ghi`. General in `F`. The affine wash-out
chain `boxTransfer δ h` is the case `F = affineF δ`, `s̄ = 1`,
`glo = ghi = 1 − δ`; headline row 17 keeps its own affine statement (round BH-2,
item BH2.11). -/

/-- **Under a general transition, the constant-sanction chain has a unique,
geometrically attracting invariant law.** General in `F`. For a constant
sanction `s̄` whose section `y ↦ F(y, s̄)` satisfies the state chord band with
`0 ≤ glo` and `ghi < 1`, and box noise of half-width `0 < h`, the chain
`x' = clipS'(F(x, s̄) + η)` has an invariant probability law that is unique and
attracts every start at rate `ghiⁿ` in the dual Kantorovich–Rubinstein distance.
The band replaces the affine law's `δ ∈ (0,1)`: it asks only that a higher state
today mean a higher state tomorrow, by less than one for one. `s̄` need not be
feasible; continuity of the drift comes from the band. -/
theorem closedLoopBoxTransfer_existsUnique_invariant_attracting_of_stateChordBand
    (F : ℝ → ℝ → ℝ) (s : ℝ) {glo ghi : ℝ} (hglo : 0 ≤ glo) (hghi1 : ghi < 1)
    (hband : Semiconcave.StateChordBand (fun y => F y s) glo ghi) (h : ℝ) (hh : 0 < h) :
    ∃ lam : Measure ↥(Sanctions.S),
      (IsProbabilityMeasure lam ∧ closedLoopBoxTransfer (fun x => F x.val s) h lam = lam)
      ∧ (∀ ν : Measure ↥(Sanctions.S), IsProbabilityMeasure ν →
          closedLoopBoxTransfer (fun x => F x.val s) h ν = ν → ν = lam)
      ∧ ∀ μ0 : Measure ↥(Sanctions.S), IsProbabilityMeasure μ0 →
          ∀ n : ℕ, dualKR ((closedLoopBoxTransfer (fun x => F x.val s) h)^[n] μ0) lam
            ≤ ghi ^ n * dualKR μ0 lam := by
  have hghi0 : 0 ≤ ghi := le_trans hglo hband.rates_le
  have hgL : ∀ x y : ↥(Sanctions.S), |F x.val s - F y.val s| ≤ ghi * dist x y := by
    intro x y
    rw [Subtype.dist_eq, Real.dist_eq]
    exact Semiconcave.abs_sub_le_of_stateChordBand hglo hband x.property y.property
  have hg : Continuous (fun x : ↥(Sanctions.S) => F x.val s) := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal ghi) fun x y => ?_).continuous
    rw [Real.dist_eq, Real.coe_toNNReal _ hghi0]
    exact hgL x y
  exact closedLoopBoxTransfer_existsUnique_invariant_attracting _ hg h hh hghi1 hgL

/-! ## When the contraction route is blocked: a diagonal crossing with excess slope

The conditional route needs a drift Lipschitz constant `L < 1`. At an
equilibrium-driven drift `g(x) = F(x, R(x))` that requirement can fail for a
structural reason. Suppose the realized-sanction rule `R` crosses the diagonal
at `x*` (`R x* = x*`) and, above it, exceeds the diagonal at excess slope
`k ≥ 0` (`R y − y ≥ k·(y − x*)`). With `F x x = x` and a sanction-side lower
chord `d ≥ 0`, the drift then rises at least at rate `1 + d·k` across
`[x*, y]`, so no Lipschitz constant below `1 + d·k`, and in particular none
below `1`, is available. General in `F`: only the diagonal identity and one
sanction chord are read (round BH-2, item BH2.11). Economically: when the
Sender's rule escalates faster than the state rises, each step amplifies a
state difference instead of shrinking it. -/

/-- **The drift's chord across a diagonal crossing.** General in `F`. If the rule
`R` fixes `x*`, lies above the diagonal at `y ≥ x*` with excess slope `k ≥ 0`
(`k·(y − x*) ≤ R y − y`) and `R y ≤ 1`, and `F` fixes the diagonal on `[0,1]` and
has a sanction-side lower chord `d ≥ 0`, then the drift `g(x) = F(x, R(x))` rises
from `x*` to `y` by at least `(1 + d·k)·(y − x*)`. -/
theorem closedLoopDrift_sub_ge_of_diagonal_crossing
    {F : ℝ → ℝ → ℝ} {R : ↥(Sanctions.S) → ℝ} {d k : ℝ}
    (hdiag : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x x = x)
    (hd0 : 0 ≤ d) (hchord : TransitionChords.SanctionLowerChord F d) (hk : 0 ≤ k)
    {xs y : ↥(Sanctions.S)} (hxy : xs.val ≤ y.val) (hfix : R xs = xs.val)
    (hcross : k * (y.val - xs.val) ≤ R y - y.val) (hRy : R y ≤ 1) :
    (1 + d * k) * (y.val - xs.val) ≤ F y.val (R y) - F xs.val (R xs) := by
  have hy : y.val ∈ Set.Icc (0 : ℝ) 1 := y.property
  have hxs : xs.val ∈ Set.Icc (0 : ℝ) 1 := xs.property
  have hge : y.val ≤ R y := by
    have := mul_nonneg hk (sub_nonneg.mpr hxy)
    linarith
  have hRmem : R y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hy.1 hge, hRy⟩
  have hc := hchord hy hy hRmem hge
  rw [hdiag y.val hy] at hc
  rw [hfix, hdiag xs.val hxs]
  have hdk : d * (k * (y.val - xs.val)) ≤ d * (R y - y.val) :=
    mul_le_mul_of_nonneg_left hcross hd0
  linarith

/-- **A diagonal crossing with excess slope `k` forces `L ≥ 1 + d·k`.** General in
`F`. Under the hypotheses of `closedLoopDrift_sub_ge_of_diagonal_crossing` at a
point `y > x*`, every Lipschitz constant `L` of the drift `g(x) = F(x, R(x))` on
`↥S` satisfies `1 + d·k ≤ L`. So the bound `hgL` of the conditional route
genuinely fails for every `L < 1 + d·k`; this refutes the hypothesis itself, not
one upper estimate of it. -/
theorem closedLoop_lipConst_ge_of_diagonal_crossing
    {F : ℝ → ℝ → ℝ} {R : ↥(Sanctions.S) → ℝ} {d k L : ℝ}
    (hdiag : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x x = x)
    (hd0 : 0 ≤ d) (hchord : TransitionChords.SanctionLowerChord F d) (hk : 0 ≤ k)
    {xs y : ↥(Sanctions.S)} (hxy : xs.val < y.val) (hfix : R xs = xs.val)
    (hcross : k * (y.val - xs.val) ≤ R y - y.val) (hRy : R y ≤ 1)
    (hgL : ∀ x y : ↥(Sanctions.S), |F x.val (R x) - F y.val (R y)| ≤ L * dist x y) :
    1 + d * k ≤ L := by
  have hpos : 0 < y.val - xs.val := sub_pos.mpr hxy
  have hchordg := closedLoopDrift_sub_ge_of_diagonal_crossing hdiag hd0 hchord hk
    hxy.le hfix hcross hRy
  have hb := hgL y xs
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos hpos] at hb
  have h1 : (1 + d * k) * (y.val - xs.val) ≤ L * (y.val - xs.val) :=
    le_trans hchordg (le_trans (le_abs_self _) hb)
  exact le_of_mul_le_mul_right h1 hpos

/-- **The conditional contraction route is unavailable at a diagonal crossing.**
General in `F`. Under the crossing hypotheses at a point `y > x*`, the drift
`g(x) = F(x, R(x))` has no Lipschitz constant below `1`, so the `L < 1`
hypothesis of `closedLoopBoxTransfer_unique_invariant` and
`closedLoopBoxTransfer_existsUnique_invariant_attracting` cannot be met. -/
theorem closedLoop_not_contracting_of_diagonal_crossing
    {F : ℝ → ℝ → ℝ} {R : ↥(Sanctions.S) → ℝ} {d k : ℝ}
    (hdiag : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x x = x)
    (hd0 : 0 ≤ d) (hchord : TransitionChords.SanctionLowerChord F d) (hk : 0 ≤ k)
    {xs y : ↥(Sanctions.S)} (hxy : xs.val < y.val) (hfix : R xs = xs.val)
    (hcross : k * (y.val - xs.val) ≤ R y - y.val) (hRy : R y ≤ 1) :
    ¬ ∃ L < 1, ∀ x y : ↥(Sanctions.S),
      |F x.val (R x) - F y.val (R y)| ≤ L * dist x y := by
  rintro ⟨L, hL1, hgL⟩
  have hL := closedLoop_lipConst_ge_of_diagonal_crossing hdiag hd0 hchord hk hxy hfix
    hcross hRy hgL
  linarith [mul_nonneg hd0 hk]

/-! ## Compatibility with the constant-drift box operator -/

/-- **Compatibility: at the constant-sanction affine drift
`g(x) = (1−δ)·x + δ`, the closed-loop operator IS the box transfer
operator** — definitionally. The wash-out chain (headline row 15's object) is
the constant-drift special case of the closed-loop chain. -/
theorem closedLoopBoxTransfer_affine_const (δ h : ℝ) (μ : Measure ↥(Sanctions.S)) :
    closedLoopBoxTransfer (fun x => (1 - δ) * x.val + δ) h μ = boxTransfer δ h μ :=
  rfl

/-- Adjoint-side compatibility: at the constant-sanction affine drift the
closed-loop pullback IS `boxPullback` — definitionally (proof irrelevance in
the continuity certificate). -/
theorem closedLoopPullback_affine_const (δ h : ℝ) (hh : 0 < h)
    (hg : Continuous (fun x : ↥(Sanctions.S) => (1 - δ) * x.val + δ))
    (f : ↥(Sanctions.S) →ᵇ ℝ) :
    closedLoopPullback (fun x => (1 - δ) * x.val + δ) hg h hh f
      = boxPullback δ h hh f :=
  rfl

end

end Sanctions
