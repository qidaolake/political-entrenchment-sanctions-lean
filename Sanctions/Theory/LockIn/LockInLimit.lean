/-
Sanctions/Theory/LockIn/LockInLimit.lean

**Round E2: the long-run lock-in limit is an equilibrium-consistent
steady state, and the steady-state band of the realized rule.**

The persistence machinery delivers a monotone, basin-trapped state
path under the upper-dynamic equilibrium rule. This file characterizes
its long run — at zero new assumption cost (every hypothesis is an
output of already-proved theorems):

1. `dynamicTopLockInPath_tendsto_steadyState` — the path converges to
   some `x* ∈ [x̄, 1]`; the realized sanction sequence converges to
   the SAME limit (`σ_n = (x_{n+1} − (1−δ)x_n)/δ → x*`); and `x*` is
   an **equilibrium-consistent steady state**: `x*` itself is an
   optimal sanction at the limit state
   (`x* ∈ dynamicArgmaxSet V_S x* (α x*)`), so the configuration
   "state `x*`, sanction `x*`" reproduces itself forever under an
   optimal Sender selection. Engine: monotone-bounded convergence
   plus the sequential Berge closed-graph of the argmax
   (`Foundations.Berge.isMaxOn_of_tendsto_of_isMaxOn`). SLP §6.1
   template; identified by the 2026-06-11 enhancement sweep (T8).

2. `dynamicTopLockInStep_exists_least_fixedPoint` — under monotone
   realized rule (available from the certificate's single-crossing
   field via `dynamicTopRealizedRule_mono_of_singleCrossingOn`), the
   step map `G(x) = (1−δ)x + δ·σ_real(x)` has a least fixed point on
   the basin (scalar Knaster-Tarski,
   `Foundations.MonotoneThreshold.exists_least_fixedPoint_of_monotoneOn_Icc`),
   and at ANY fixed point the realized sanction equals the state:
   `σ_real(x*) = x*` — the sanction level exactly sustains the
   political state that sustains it (the Eaton-Engers interior
   steady-state reading).

3. **General-`F` siblings** (`…PathF_tendsto_steadyState`,
   `…StepF_fixedPoint_of_realizedRule_eq_self`,
   `dynamicTop_F_eq_self_on_band_of_stepF_fixedPoint`,
   `…StepF_exists_least_fixedPoint`) — the same long-run results on
   the abstract-transition path `x_{n+1} = F(x_n, σ_n)`. Under the
   bare weakly-monotone `Params` interface, only a convergent sanction
   subsequence is identified, and the `σ_real(x*) = x*` cancellation
   weakens to flatness of `F(x*, ·)` on the band
   `[x*, σ_real(x*)]`.

4. **Strict-adjustment general-`F` upgrades**
   (`…PathF_tendsto_steadyState_full_of_strictAdjustment`,
   `…Rule_eq_self_of_stepF_fixedPoint_of_strictAdjustment`,
   `…StepF_exists_least_fixedPoint_of_strictAdjustment`) — the
   maintained phase-line condition (`s < x → F(x,s) < x` and
    `x < s → x < F(x,s)`) collapses every self-reproducing pair
   `F(x*, s*) = x*` to `s* = x*`. Compactness then makes every
   sanction subsequence admit a further subsequence with that same
   limit, so the full equilibrium sanction sequence converges to
   `x*` without reverting to the affine formula.

## Rule compliance

**Rule 1** ✓ — all paths/limits are under the equilibrium-derived
upper selector; the steady-state membership is an argmax statement.
**Rule 3** ✓ — zero new assumptions: hypotheses are the basin level
condition and (for the band) monotonicity of the realized rule, both
outputs of the existing certificate machinery. **Rule 5** ✓ —
parametric over `(p, V_S, α, x̄, s̄, x₀)`. **Rule 19** ✓ — generic
limit/fixed-point content in `Foundations/`; this file is wiring.
-/

import Sanctions.Theory.LockIn.DynamicTopLockIn
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Foundations.Berge
import Sanctions.Foundations.MonotoneThreshold

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **The lock-in limit is an equilibrium-consistent steady state
(Round E2).** From any basin start, under the basin level condition
(`σ_real ≥ max(x, s̄)` on `[x̄, 1]` — the output of the certificate
machinery), the upper-dynamic state path converges to some
`x* ∈ [x̄, 1]`; the realized sanction sequence converges to the same
`x*`; and `x*` is itself an optimal sanction at the limit state —
the pair (state `x*`, sanction `x*`) is a self-reproducing optimal
configuration. -/
theorem dynamicTopLockInPath_tendsto_steadyState
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      Tendsto (p.dynamicTopLockInPath V_S α x₀) atTop (𝓝 xs) ∧
      Tendsto (p.dynamicTopLockInSanctions V_S α x₀) atTop (𝓝 xs) ∧
      xs ∈ p.dynamicArgmaxSet V_S xs (α xs) ∧
      xs ≤ p.dynamicTopRealizedRule V_S α xs := by
  set path := p.dynamicTopLockInPath V_S α x₀ with hpath_def
  have hmono : Monotone path :=
    p.dynamicTopLockInPath_mono V_S α h_level_top hx₀
  have hmem : ∀ n, path n ∈ Set.Icc xbar 1 :=
    p.dynamicTopLockInPath_mem_basin V_S α h_level_top hx₀
  have hbdd : BddAbove (Set.range path) := by
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (hmem n).2
  have htend : Tendsto path atTop (𝓝 (⨆ n, path n)) :=
    tendsto_atTop_ciSup hmono hbdd
  set xs := ⨆ n, path n with hxs_def
  have hxs_mem : xs ∈ Set.Icc xbar 1 := by
    constructor
    · exact le_trans (hmem 0).1 (le_ciSup hbdd 0)
    · exact ciSup_le (fun n => (hmem n).2)
  -- The sanction sequence: σ_n = (path (n+1) − (1−δ)·path n)/δ.
  have hδ_pos : (0 : ℝ) < p.δ := p.δ_mem.1
  have hδ_ne : p.δ ≠ 0 := ne_of_gt hδ_pos
  have hstep : ∀ n, path (n + 1)
      = (1 - p.δ) * path n
        + p.δ * p.dynamicTopLockInSanctions V_S α x₀ n := by
    intro n
    simp only [hpath_def, dynamicTopLockInPath_succ]
    rfl
  have hσ_eq : ∀ n, p.dynamicTopLockInSanctions V_S α x₀ n
      = (path (n + 1) - (1 - p.δ) * path n) / p.δ := by
    intro n
    rw [hstep n]
    field_simp
    ring
  have hσtend : Tendsto (p.dynamicTopLockInSanctions V_S α x₀)
      atTop (𝓝 xs) := by
    have h1 : Tendsto (fun n => path (n + 1)) atTop (𝓝 xs) :=
      htend.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto
        (fun n => (path (n + 1) - (1 - p.δ) * path n) / p.δ)
        atTop (𝓝 ((xs - (1 - p.δ) * xs) / p.δ)) :=
      (h1.sub (htend.const_mul _)).div_const _
    have hxx : (xs - (1 - p.δ) * xs) / p.δ = xs := by
      field_simp
      ring
    rw [hxx] at h2
    exact Tendsto.congr (fun n => (hσ_eq n).symm) h2
  -- Joint continuity of the Sender dynamic objective in (x, s).
  have hΦcont : Continuous fun q : ℝ × ℝ =>
      p.U_S q.1 (α q.1) q.2
        + p.β_S * V_S (Sanctions.clipS' (p.F q.1 q.2)) := by
    have hUS : Continuous fun q : ℝ × ℝ => p.U_S q.1 (α q.1) q.2 := by
      have htriple : Continuous fun q : ℝ × ℝ =>
          ((q.1, α q.1, q.2) : ℝ × ℝ × ℝ) :=
        continuous_fst.prodMk
          ((hα_cont.comp continuous_fst).prodMk continuous_snd)
      exact p.U_S_continuous.comp htriple
    have haff : Continuous fun q : ℝ × ℝ =>
        p.F q.1 q.2 :=
      p.F_continuous
    have hVS : Continuous fun q : ℝ × ℝ =>
        V_S (Sanctions.clipS' (p.F q.1 q.2)) :=
      V_S.continuous.comp (Sanctions.clipS'_continuous.comp haff)
    exact hUS.add (continuous_const.mul hVS)
  -- Each σ_n is a maximizer at (path n); pass to the limit.
  have hmax : ∀ n, IsMaxOn
      (fun s => p.U_S (path n) (α (path n)) s
        + p.β_S * V_S (Sanctions.clipS'
            (p.F (path n) s)))
      Sanctions.I (p.dynamicTopLockInSanctions V_S α x₀ n) :=
    fun n => p.σ_dyn_top_isMaxOn V_S (path n) (α (path n))
  have hmemI : ∀ n,
      p.dynamicTopLockInSanctions V_S α x₀ n ∈ Sanctions.I :=
    fun n => p.dynamicTopRealizedRule_mem V_S α (path n)
  obtain ⟨hssI, hssmax⟩ :=
    Sanctions.Foundations.Berge.isMaxOn_of_tendsto_of_isMaxOn
      (Φ := fun x s => p.U_S x (α x) s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      hΦcont isClosed_Icc htend hσtend hmemI hmax
  have hargmax : xs ∈ p.dynamicArgmaxSet V_S xs (α xs) := ⟨hssI, hssmax⟩
  refine ⟨xs, hxs_mem, htend, hσtend, hargmax, ?_⟩
  exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S xs (α xs)) hargmax

/-- **At every fixed point of the lock-in step map, the realized
sanction equals the state.** If `G(y) = (1−δ)·y + δ·σ_real(y) = y`,
then `σ_real(y) = y` — pure `δ > 0` cancellation, with no basin,
monotonicity, or level hypothesis. This is the universally-quantified
form of the per-least-fixed-point clause of
`dynamicTopLockInStep_exists_least_fixedPoint` below (which consumes
it): the paper's steady-state-band prose asserts the
sanction-sustains-state identity at *every* fixed point of `G`, and
this lemma is that statement. -/
theorem dynamicTopRealizedRule_eq_self_of_step_fixedPoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {y : ℝ}
    (hfix : p.dynamicTopLockInStep V_S α y = y) :
    p.dynamicTopRealizedRule V_S α y = y := by
  have hδ_pos : (0 : ℝ) < p.δ := p.δ_mem.1
  unfold dynamicTopLockInStep at hfix
  nlinarith [hfix, sq_nonneg (p.dynamicTopRealizedRule V_S α y - y)]

/-- **Steady-state band of the realized rule (Round E2).** Under the
basin level condition and monotonicity of the realized rule on the
basin (the output of the certificate's single-crossing field via
`dynamicTopRealizedRule_mono_of_singleCrossingOn`), the step map
`G(x) = (1−δ)x + δ·σ_real(x)` has a least fixed point on `[x̄, 1]` —
and at every fixed point the realized sanction equals the state:
`σ_real(x*) = x*` (the universal form is
`dynamicTopRealizedRule_eq_self_of_step_fixedPoint` above). The
sanction level exactly sustains the political state that sustains
it. -/
theorem dynamicTopLockInStep_exists_least_fixedPoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar : ℝ} (hxbar_le : xbar ≤ 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
        (Set.Icc xbar 1)) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStep V_S α xs = xs ∧
      p.dynamicTopRealizedRule V_S α xs = xs ∧
      ∀ y ∈ Set.Icc xbar 1,
        p.dynamicTopLockInStep V_S α y = y → xs ≤ y := by
  have hδ_pos : (0 : ℝ) < p.δ := p.δ_mem.1
  have h1δ_nn : (0 : ℝ) ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  have hG_mono : MonotoneOn (p.dynamicTopLockInStep V_S α)
      (Set.Icc xbar 1) := by
    intro x hx y hy hxy
    unfold dynamicTopLockInStep
    have h1 : (1 - p.δ) * x ≤ (1 - p.δ) * y :=
      mul_le_mul_of_nonneg_left hxy h1δ_nn
    have h2 : p.δ * p.dynamicTopRealizedRule V_S α x
        ≤ p.δ * p.dynamicTopRealizedRule V_S α y :=
      mul_le_mul_of_nonneg_left (hrule_mono hx hy hxy) hδ_pos.le
    linarith
  have hG_maps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStep V_S α x ∈ Set.Icc xbar 1 :=
    fun x hx => p.dynamicTopLockInStep_mem_basin V_S α h_level_top hx
  obtain ⟨xs, hxs_mem, hfix, hleast⟩ :=
    Sanctions.MonotoneThreshold.exists_least_fixedPoint_of_monotoneOn_Icc
      hxbar_le hG_mono hG_maps
  exact ⟨xs, hxs_mem, hfix,
    p.dynamicTopRealizedRule_eq_self_of_step_fixedPoint V_S α hfix, hleast⟩

/-! ## General-`F` siblings

The three theorems above are stated on the affine path
`x_{n+1} = (1−δ)x_n + δ·σ_n`. The siblings below restate them for the
**abstract transition** `p.F` (`dynamicTopLockInPathF` /
`dynamicTopLockInStepF`, `Theory/LockIn/DynamicTopLockIn.lean`). Two
affine-specific devices do not survive, and are weakened rather than
propped up with new hypotheses:

* the closed-form sanction recovery `σ_n = (x_{n+1} − (1−δ)x_n)/δ`
  (affine inversion) — for a general `F` the realized sanction is not
  a function of consecutive states, so the sanction-convergence clause
  weakens to **subsequential** convergence (compactness of `[0,1]`),
  which still feeds the (already `F`-general) Berge closed-graph
  passage and additionally delivers the self-reproduction identity
  `F(x*, s*) = x*`;
* the `δ > 0` cancellation `G(y) = y → σ_real(y) = y` — for a general
  `F` that is only *weakly* monotone in `s` (`F_mono_s`), a fixed
  point of the `F`-step instead forces `F(y, ·)` to be **flat on the
  whole band** `[y, σ_real(y)]`. Under the maintained
  `StrictAdjustment` condition, however, `F(y,s) = y ↔ s = y`, so the
  band again collapses to the point `y`.

The base limit theorem and the least-fixed-point theorem take exactly
the affine theorems' hypotheses: since BG2.1 (2026-10-06) the general-`F`
basin lemmas of `DynamicTopLockIn.lean` no longer need `0 ≤ xbar`, so
these two dropped it too. The strict-adjustment upgrades keep `0 ≤ xbar`,
because `StrictAdjustment` is stated on `[0,1]` and is applied at the
limit state `x* ∈ [x̄, 1]`; no genuinely new assumption. -/

/-- **The general-`F` lock-in limit is an equilibrium-consistent
steady state.** From any basin start, under the basin level condition,
the general-`F` upper-dynamic state path converges to some
`x* ∈ [x̄, 1]`; some subsequence of the realized sanctions converges
to a sanction `s* ∈ [0, 1]`; and the limit configuration is a
self-reproducing optimal steady state: `s*` is an optimal Sender
sanction at the limit state (`s* ∈ dynamicArgmaxSet V_S x* (α x*)`),
the transition reproduces the state (`F(x*, s*) = x*`), and `s*` is
below the realized rule at `x*`. Affine sibling:
`dynamicTopLockInPath_tendsto_steadyState` (there the affine inversion
upgrades the subsequential clause to full convergence with `s* = x*`).
General in `F`. No `0 ≤ xbar`: it was read only by the basin lemmas,
which no longer need it (dropped on 2026-10-06, BG2.1), so the result
holds for any basin floor `x̄`. -/
theorem dynamicTopLockInPathF_tendsto_steadyState
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      Tendsto (p.dynamicTopLockInPathF V_S α x₀) atTop (𝓝 xs) ∧
      ∃ ss ∈ Sanctions.I,
        (∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (p.dynamicTopLockInSanctionsF V_S α x₀ ∘ φ)
            atTop (𝓝 ss)) ∧
        ss ∈ p.dynamicArgmaxSet V_S xs (α xs) ∧
        p.F xs ss = xs ∧
        ss ≤ p.dynamicTopRealizedRule V_S α xs := by
  set path := p.dynamicTopLockInPathF V_S α x₀ with hpath_def
  have hmono : Monotone path :=
    p.dynamicTopLockInPathF_mono V_S α h_level_top hx₀
  have hmem : ∀ n, path n ∈ Set.Icc xbar 1 :=
    p.dynamicTopLockInPathF_mem_basin V_S α h_level_top hx₀
  have hbdd : BddAbove (Set.range path) := by
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (hmem n).2
  have htend : Tendsto path atTop (𝓝 (⨆ n, path n)) :=
    tendsto_atTop_ciSup hmono hbdd
  set xs := ⨆ n, path n with hxs_def
  have hxs_mem : xs ∈ Set.Icc xbar 1 := by
    constructor
    · exact le_trans (hmem 0).1 (le_ciSup hbdd 0)
    · exact ciSup_le (fun n => (hmem n).2)
  -- The sanction sequence lives in the compact `[0, 1]`: extract a
  -- convergent subsequence (the affine inversion is unavailable).
  have hmemI : ∀ n,
      p.dynamicTopLockInSanctionsF V_S α x₀ n ∈ Sanctions.I :=
    fun n => p.dynamicTopRealizedRule_mem V_S α (path n)
  obtain ⟨ss, -, φ, hφ_mono, hφ_tend⟩ :=
    isCompact_Icc.tendsto_subseq hmemI
  have htend_sub : Tendsto (path ∘ φ) atTop (𝓝 xs) :=
    htend.comp hφ_mono.tendsto_atTop
  -- Joint continuity of the Sender dynamic objective in (x, s).
  have hΦcont : Continuous fun q : ℝ × ℝ =>
      p.U_S q.1 (α q.1) q.2
        + p.β_S * V_S (Sanctions.clipS' (p.F q.1 q.2)) := by
    have hUS : Continuous fun q : ℝ × ℝ => p.U_S q.1 (α q.1) q.2 := by
      have htriple : Continuous fun q : ℝ × ℝ =>
          ((q.1, α q.1, q.2) : ℝ × ℝ × ℝ) :=
        continuous_fst.prodMk
          ((hα_cont.comp continuous_fst).prodMk continuous_snd)
      exact p.U_S_continuous.comp htriple
    have hF : Continuous fun q : ℝ × ℝ =>
        p.F q.1 q.2 :=
      p.F_continuous
    have hVS : Continuous fun q : ℝ × ℝ =>
        V_S (Sanctions.clipS' (p.F q.1 q.2)) :=
      V_S.continuous.comp (Sanctions.clipS'_continuous.comp hF)
    exact hUS.add (continuous_const.mul hVS)
  -- Along the subsequence each sanction maximizes at its state; pass
  -- to the limit through the (already F-general) Berge closed graph.
  have hmax : ∀ k, IsMaxOn
      (fun s => p.U_S (path (φ k)) (α (path (φ k))) s
        + p.β_S * V_S (Sanctions.clipS'
            (p.F (path (φ k)) s)))
      Sanctions.I ((p.dynamicTopLockInSanctionsF V_S α x₀ ∘ φ) k) :=
    fun k => p.σ_dyn_top_isMaxOn V_S (path (φ k)) (α (path (φ k)))
  obtain ⟨hssI, hssmax⟩ :=
    Sanctions.Foundations.Berge.isMaxOn_of_tendsto_of_isMaxOn
      (Φ := fun x s => p.U_S x (α x) s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      hΦcont isClosed_Icc htend_sub hφ_tend
      (fun k => hmemI (φ k)) hmax
  have hargmax : ss ∈ p.dynamicArgmaxSet V_S xs (α xs) := ⟨hssI, hssmax⟩
  -- The limit configuration reproduces itself: `F(x*, s*) = x*`.
  have h_lhs : Tendsto
      (fun k => p.F (path (φ k))
        ((p.dynamicTopLockInSanctionsF V_S α x₀ ∘ φ) k))
      atTop (𝓝 (p.F xs ss)) := by
    have := p.F_continuous.tendsto (xs, ss)
    exact this.comp (htend_sub.prodMk_nhds hφ_tend)
  have h_rhs : Tendsto (fun k => path (φ k + 1)) atTop (𝓝 xs) :=
    htend.comp ((tendsto_add_atTop_nat 1).comp hφ_mono.tendsto_atTop)
  have hstep_eq : ∀ k, path (φ k + 1)
      = p.F (path (φ k))
          ((p.dynamicTopLockInSanctionsF V_S α x₀ ∘ φ) k) := by
    intro k
    simp only [hpath_def, dynamicTopLockInPathF_succ]
    rfl
  have hFfix : p.F xs ss = xs :=
    (tendsto_nhds_unique (Tendsto.congr hstep_eq h_rhs) h_lhs).symm
  refine ⟨xs, hxs_mem, htend, ss, hssI, ⟨φ, hφ_mono, hφ_tend⟩,
    hargmax, hFfix, ?_⟩
  exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S xs (α xs)) hargmax

/-- **Strict adjustment identifies the general-`F` steady-state
sanction with the limiting state.** The base general-`F` limit theorem
constructs an optimal subsequential sanction limit `s*` satisfying
`F(x*, s*) = x*`. The maintained phase-line condition
`StrictAdjustment` makes that identity equivalent to `s* = x*`.
Thus the limit is the same economically sharp self-sustaining pair as
in the affine theorem. The next theorem upgrades this identification to
full sanction-sequence convergence. -/
theorem dynamicTopLockInPathF_tendsto_steadyState_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      Tendsto (p.dynamicTopLockInPathF V_S α x₀) atTop (𝓝 xs) ∧
      ∃ ss ∈ Sanctions.I,
        (∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (p.dynamicTopLockInSanctionsF V_S α x₀ ∘ φ)
            atTop (𝓝 ss)) ∧
        ss ∈ p.dynamicArgmaxSet V_S xs (α xs) ∧
        p.F xs ss = xs ∧
        ss = xs ∧
        ss ≤ p.dynamicTopRealizedRule V_S α xs := by
  obtain ⟨xs, hxs, hpath, ss, hss, hsub, hopt, hF, hle⟩ :=
    p.dynamicTopLockInPathF_tendsto_steadyState V_S α hα_cont
      h_level_top hx₀
  have hxsI : xs ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hxbar0 hxs.1, hxs.2⟩
  have heq : ss = xs := (hAdj.F_eq_self_iff hxsI hss).mp hF
  exact ⟨xs, hxs, hpath, ss, hss, hsub, hopt, hF, heq, hle⟩

/-- **Under strict adjustment, the entire general-`F` equilibrium sanction
sequence converges to the limiting state.** The state path converges by the
general lock-in theorem. For any subsequence of equilibrium sanctions,
compactness of `[0,1]` supplies a convergent subsubsequence. Joint continuity
of `F` and the transition recursion imply that its limit `s'` satisfies
`F(x*,s') = x*`; strict adjustment forces `s' = x*`. Since every subsequence
has a subsubsequence converging to `x*`, the full sanction sequence converges.

This argument recovers the affine theorem's full-sequence conclusion without
inverting `F` or imposing monotonicity or continuity on the realized rule. -/
theorem dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      Tendsto (p.dynamicTopLockInPathF V_S α x₀) atTop (𝓝 xs) ∧
      Tendsto (p.dynamicTopLockInSanctionsF V_S α x₀) atTop (𝓝 xs) ∧
      xs ∈ p.dynamicArgmaxSet V_S xs (α xs) ∧
      xs ≤ p.dynamicTopRealizedRule V_S α xs := by
  obtain ⟨xs, hxs, hpath, ss, -, -, hopt, -, hss_eq, hle⟩ :=
    p.dynamicTopLockInPathF_tendsto_steadyState_of_strictAdjustment hAdj
      V_S α hα_cont hxbar0 h_level_top hx₀
  have hxsI : xs ∈ Sanctions.I := ⟨le_trans hxbar0 hxs.1, hxs.2⟩
  have hsanctions :
      Tendsto (p.dynamicTopLockInSanctionsF V_S α x₀) atTop (𝓝 xs) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hmem_ns : ∀ n,
        (p.dynamicTopLockInSanctionsF V_S α x₀ ∘ ns) n ∈ Sanctions.I :=
      fun n => p.dynamicTopRealizedRule_mem V_S α
        (p.dynamicTopLockInPathF V_S α x₀ (ns n))
    obtain ⟨s', hs'I, φ, hφ_mono, hφ_tend⟩ :=
      isCompact_Icc.tendsto_subseq hmem_ns
    have hidx : Tendsto (ns ∘ φ) atTop atTop :=
      hns.comp hφ_mono.tendsto_atTop
    have hstate : Tendsto
        (p.dynamicTopLockInPathF V_S α x₀ ∘ (ns ∘ φ)) atTop (𝓝 xs) :=
      hpath.comp hidx
    have h_lhs : Tendsto
        (fun k => p.F (p.dynamicTopLockInPathF V_S α x₀ ((ns ∘ φ) k))
          (((p.dynamicTopLockInSanctionsF V_S α x₀ ∘ ns) ∘ φ) k))
        atTop (𝓝 (p.F xs s')) := by
      exact (p.F_continuous.tendsto (xs, s')).comp
        (hstate.prodMk_nhds hφ_tend)
    have h_rhs : Tendsto
        (fun k => p.dynamicTopLockInPathF V_S α x₀ ((ns ∘ φ) k + 1))
        atTop (𝓝 xs) :=
      hpath.comp ((tendsto_add_atTop_nat 1).comp hidx)
    have hstep_eq : ∀ k,
        p.dynamicTopLockInPathF V_S α x₀ ((ns ∘ φ) k + 1) =
          p.F (p.dynamicTopLockInPathF V_S α x₀ ((ns ∘ φ) k))
            (((p.dynamicTopLockInSanctionsF V_S α x₀ ∘ ns) ∘ φ) k) := by
      intro k
      simp only [dynamicTopLockInPathF_succ]
      rfl
    have hFfix : p.F xs s' = xs :=
      (tendsto_nhds_unique (Tendsto.congr hstep_eq h_rhs) h_lhs).symm
    have hs'eq : s' = xs := (hAdj.F_eq_self_iff hxsI hs'I).mp hFfix
    refine ⟨φ, ?_⟩
    simpa only [Function.comp_apply, hs'eq] using hφ_tend
  refine ⟨xs, hxs, hpath, hsanctions, ?_, ?_⟩
  · simpa only [hss_eq] using hopt
  · simpa only [hss_eq] using hle

/-- **A realized-rule fixed point is a general-`F` step fixed point.**
If the realized sanction equals the state (`σ_real(y) = y`), then `y`
is a fixed point of the general-`F` step map (`F_diag`: `F y y = y`).
This is the direction of the affine cancellation
`dynamicTopRealizedRule_eq_self_of_step_fixedPoint` that survives for
a general weakly-`s`-monotone `F`; the converse direction weakens to
band flatness (`dynamicTop_F_eq_self_on_band_of_stepF_fixedPoint`
below), since without strict responsiveness of `F` in `s` a step fixed
point does not pin the sanction to the state. -/
theorem dynamicTopLockInStepF_fixedPoint_of_realizedRule_eq_self
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {y : ℝ}
    (hrule : p.dynamicTopRealizedRule V_S α y = y) :
    p.dynamicTopLockInStepF V_S α y = y := by
  unfold dynamicTopLockInStepF
  rw [hrule, p.F_diag y]

/-- **Strict adjustment gives the converse fixed-point direction for
the general transition.** At a feasible state `y`, if the endogenous
general-`F` step is fixed, then the realized optimal sanction equals
the state. The proof uses only the maintained phase-line condition:
`F(y, σ_real(y)) = y` and `F(y,s) = y ↔ s = y`. Together with
`dynamicTopLockInStepF_fixedPoint_of_realizedRule_eq_self`, this
identifies the fixed points of the state step with the crossings of
the equilibrium sanction rule and the 45-degree line. -/
theorem dynamicTopRealizedRule_eq_self_of_stepF_fixedPoint_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {y : ℝ}
    (hy : y ∈ Sanctions.I)
    (hfix : p.dynamicTopLockInStepF V_S α y = y) :
    p.dynamicTopRealizedRule V_S α y = y := by
  have hruleI : p.dynamicTopRealizedRule V_S α y ∈ Sanctions.I :=
    p.dynamicTopRealizedRule_mem V_S α y
  have hF : p.F y (p.dynamicTopRealizedRule V_S α y) = y := by
    simpa only [dynamicTopLockInStepF] using hfix
  exact (hAdj.F_eq_self_iff hy hruleI).mp hF

/-- **Under strict adjustment, state-step fixed points are exactly rule
crossings.** At every feasible state, the endogenous general-`F` step is
fixed if and only if the equilibrium-derived realized sanction equals
that state. Thus changing the transition law while holding the realized
rule fixed cannot change its steady-state set within the maintained
strict-adjustment class; transition changes can still alter paths and
which fixed point a path selects. -/
theorem dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {y : ℝ}
    (hy : y ∈ Sanctions.I) :
    p.dynamicTopLockInStepF V_S α y = y ↔
      p.dynamicTopRealizedRule V_S α y = y := by
  constructor
  · exact p.dynamicTopRealizedRule_eq_self_of_stepF_fixedPoint_of_strictAdjustment
      hAdj V_S α hy
  · exact p.dynamicTopLockInStepF_fixedPoint_of_realizedRule_eq_self V_S α

/-- **At a general-`F` step fixed point, the transition is flat on the
whole state-to-sanction band.** If `F(y, σ_real(y)) = y`, then
`F(y, s) = y` for EVERY `s ∈ [y, σ_real(y)]`: squeeze between
`F y y = y` (`F_diag`) and `F y (σ_real y) = y` (the fixed point) via
weak `s`-monotonicity (`F_mono_s`). This is the honest general-`F`
form of the affine cancellation `σ_real(y) = y`
(`dynamicTopRealizedRule_eq_self_of_step_fixedPoint`): the affine
transition is strictly responsive in `s` (`δ > 0`), which collapses
the flat band to the single point `y`. -/
theorem dynamicTop_F_eq_self_on_band_of_stepF_fixedPoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {y : ℝ}
    (hfix : p.dynamicTopLockInStepF V_S α y = y) :
    ∀ s ∈ Set.Icc y (p.dynamicTopRealizedRule V_S α y),
      p.F y s = y := by
  intro s hs
  unfold dynamicTopLockInStepF at hfix
  have h_lo : p.F y y ≤ p.F y s := p.F_mono_s y hs.1
  have h_hi : p.F y s ≤ p.F y (p.dynamicTopRealizedRule V_S α y) :=
    p.F_mono_s y hs.2
  rw [p.F_diag y] at h_lo
  rw [hfix] at h_hi
  exact le_antisymm h_hi h_lo

/-- **Steady-state band of the realized rule, general-`F` form.**
Under the basin level condition and monotonicity of the realized rule
on the basin, the general-`F` step map `x ↦ F(x, σ_real(x))` has a
least fixed point `x*` on `[x̄, 1]` (scalar Knaster-Tarski; the step
map is monotone by `F_mono_x` ∘ `F_mono_s` ∘ rule monotonicity). At
`x*` the sanction weakly exceeds the state (`x* ≤ σ_real(x*)`, from
the level condition) and the transition is flat on the whole band
`[x*, σ_real(x*)]` (`F(x*, s) = x*` there) — the general-`F`
weakening of the affine clause `σ_real(x*) = x*` in
`dynamicTopLockInStep_exists_least_fixedPoint`. General in `F`. No
`0 ≤ xbar`: it was read only by the basin lemma, which no longer needs it
(dropped on 2026-10-06, BG2.1). -/
theorem dynamicTopLockInStepF_exists_least_fixedPoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar : ℝ} (hxbar_le : xbar ≤ 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
        (Set.Icc xbar 1)) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF V_S α xs = xs ∧
      xs ≤ p.dynamicTopRealizedRule V_S α xs ∧
      (∀ s ∈ Set.Icc xs (p.dynamicTopRealizedRule V_S α xs),
        p.F xs s = xs) ∧
      ∀ y ∈ Set.Icc xbar 1,
        p.dynamicTopLockInStepF V_S α y = y → xs ≤ y := by
  have hG_mono : MonotoneOn (p.dynamicTopLockInStepF V_S α)
      (Set.Icc xbar 1) := by
    intro x hx y hy hxy
    unfold dynamicTopLockInStepF
    have h1 : p.F x (p.dynamicTopRealizedRule V_S α x)
        ≤ p.F x (p.dynamicTopRealizedRule V_S α y) :=
      p.F_mono_s x (hrule_mono hx hy hxy)
    have h2 : p.F x (p.dynamicTopRealizedRule V_S α y)
        ≤ p.F y (p.dynamicTopRealizedRule V_S α y) :=
      p.F_mono_x (p.dynamicTopRealizedRule V_S α y) hxy
    exact le_trans h1 h2
  have hG_maps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF V_S α x ∈ Set.Icc xbar 1 :=
    fun x hx =>
      p.dynamicTopLockInStepF_mem_basin V_S α h_level_top hx
  obtain ⟨xs, hxs_mem, hfix, hleast⟩ :=
    Sanctions.MonotoneThreshold.exists_least_fixedPoint_of_monotoneOn_Icc
      hxbar_le hG_mono hG_maps
  refine ⟨xs, hxs_mem, hfix, ?_,
    p.dynamicTop_F_eq_self_on_band_of_stepF_fixedPoint V_S α hfix,
    hleast⟩
  exact le_trans (le_max_left xs sbar) (h_level_top xs hxs_mem)

/-- **The least general-`F` fixed point lies on the equilibrium
sanction rule under strict adjustment.** The base theorem constructs
the least basin fixed point and only needs weak monotonicity, so it
retains a possibly flat transition band. The maintained phase-line
condition collapses that band: at the least fixed point the endogenous
optimal sanction is exactly the political state. The original
fixed-point, band-flatness, and leastness conclusions are retained. -/
theorem dynamicTopLockInStepF_exists_least_fixedPoint_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar) (hxbar_le : xbar ≤ 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
        (Set.Icc xbar 1)) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF V_S α xs = xs ∧
      xs ≤ p.dynamicTopRealizedRule V_S α xs ∧
      p.dynamicTopRealizedRule V_S α xs = xs ∧
      (∀ s ∈ Set.Icc xs (p.dynamicTopRealizedRule V_S α xs),
        p.F xs s = xs) ∧
      ∀ y ∈ Set.Icc xbar 1,
        p.dynamicTopLockInStepF V_S α y = y → xs ≤ y := by
  obtain ⟨xs, hxs, hfix, hle, hband, hleast⟩ :=
    p.dynamicTopLockInStepF_exists_least_fixedPoint V_S α hxbar_le
      h_level_top hrule_mono
  have hxsI : xs ∈ Sanctions.I := ⟨le_trans hxbar0 hxs.1, hxs.2⟩
  have heq :=
    p.dynamicTopRealizedRule_eq_self_of_stepF_fixedPoint_of_strictAdjustment
      hAdj V_S α hxsI hfix
  exact ⟨xs, hxs, hfix, hle, heq, hband, hleast⟩

/-- **The lower-endpoint general-`F` orbit lies below the least selected
fixed point.** Single crossing makes the greatest equilibrium sanction rule
monotone on the basin, hence the induced general-`F` step is monotone there.
The least fixed point of that selected step is therefore an upper bound for
every iterate from `xbar` and, by closedness of the order, for the orbit limit.

The limit is an equilibrium-consistent self-sanction and both the state and
sanction paths converge to it under strict adjustment. It need not equal the
least fixed point: the greatest optimal selector can jump upward at a limiting
state with multiple optimal sanctions. -/
theorem dynamicTopLockInPathF_tendsto_below_least_fixedPoint_of_rule_mono
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar) (hxbar_le : xbar ≤ 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
        (Set.Icc xbar 1)) :
    ∃ xl ∈ Set.Icc xbar 1, ∃ xf ∈ Set.Icc xbar 1,
      Tendsto (p.dynamicTopLockInPathF V_S α xbar) atTop (𝓝 xl) ∧
      Tendsto (p.dynamicTopLockInSanctionsF V_S α xbar) atTop (𝓝 xl) ∧
      xl ∈ p.dynamicArgmaxSet V_S xl (α xl) ∧
      xl ≤ p.dynamicTopRealizedRule V_S α xl ∧
      p.dynamicTopLockInStepF V_S α xf = xf ∧
      p.dynamicTopRealizedRule V_S α xf = xf ∧
      xl ≤ xf ∧
      ∀ y ∈ Set.Icc xbar 1,
        p.dynamicTopLockInStepF V_S α y = y → xf ≤ y := by
  have hxbar_mem : xbar ∈ Set.Icc xbar (1 : ℝ) := ⟨le_rfl, hxbar_le⟩
  obtain ⟨xl, hxl, hpath, hsanctions, hopt, hxl_rule⟩ :=
    p.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment
      hAdj V_S α hα_cont hxbar0 h_level_top hxbar_mem
  obtain ⟨xf, hxf, hfix, -, hrule_fix, -, hleast⟩ :=
    p.dynamicTopLockInStepF_exists_least_fixedPoint_of_strictAdjustment
      hAdj V_S α hxbar0 hxbar_le h_level_top hrule_mono
  have hstep_mono : MonotoneOn (p.dynamicTopLockInStepF V_S α)
      (Set.Icc xbar 1) := by
    intro x hx y hy hxy
    unfold dynamicTopLockInStepF
    have h1 : p.F x (p.dynamicTopRealizedRule V_S α x) ≤
        p.F x (p.dynamicTopRealizedRule V_S α y) :=
      p.F_mono_s x (hrule_mono hx hy hxy)
    have h2 : p.F x (p.dynamicTopRealizedRule V_S α y) ≤
        p.F y (p.dynamicTopRealizedRule V_S α y) :=
      p.F_mono_x (p.dynamicTopRealizedRule V_S α y) hxy
    exact le_trans h1 h2
  have hpath_le : ∀ n, p.dynamicTopLockInPathF V_S α xbar n ≤ xf := by
    intro n
    induction n with
    | zero =>
        simpa only [dynamicTopLockInPathF_zero] using hxf.1
    | succ n ih =>
        rw [dynamicTopLockInPathF_succ]
        calc
          p.dynamicTopLockInStepF V_S α
              (p.dynamicTopLockInPathF V_S α xbar n) ≤
              p.dynamicTopLockInStepF V_S α xf :=
            hstep_mono
              (p.dynamicTopLockInPathF_mem_basin V_S α
                h_level_top hxbar_mem n) hxf ih
          _ = xf := hfix
  have hxl_le : xl ≤ xf :=
    le_of_tendsto hpath (Filter.Eventually.of_forall hpath_le)
  exact ⟨xl, hxl, xf, hxf, hpath, hsanctions, hopt, hxl_rule,
    hfix, hrule_fix, hxl_le, hleast⟩

/-- **Single-crossing version of the lower-orbit bound.** Single crossing
of the dynamic Sender objective makes the greatest equilibrium sanction
rule monotone. The preceding theorem then compares the equilibrium-consistent
orbit limit with the least fixed point of the selected general-`F` step. -/
theorem dynamicTopLockInPathF_tendsto_below_least_fixedPoint_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar) (hxbar_le : xbar ≤ 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
        max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hSC : MilgromShannon.SingleCrossingOn Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S x (α x) s)) :
    ∃ xl ∈ Set.Icc xbar 1, ∃ xf ∈ Set.Icc xbar 1,
      Tendsto (p.dynamicTopLockInPathF V_S α xbar) atTop (𝓝 xl) ∧
      Tendsto (p.dynamicTopLockInSanctionsF V_S α xbar) atTop (𝓝 xl) ∧
      xl ∈ p.dynamicArgmaxSet V_S xl (α xl) ∧
      xl ≤ p.dynamicTopRealizedRule V_S α xl ∧
      p.dynamicTopLockInStepF V_S α xf = xf ∧
      p.dynamicTopRealizedRule V_S α xf = xf ∧
      xl ≤ xf ∧
      ∀ y ∈ Set.Icc xbar 1,
        p.dynamicTopLockInStepF V_S α y = y → xf ≤ y :=
  p.dynamicTopLockInPathF_tendsto_below_least_fixedPoint_of_rule_mono
    hAdj V_S α hα_cont hxbar0 hxbar_le h_level_top
      (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC)

end Params
end AbstractGame

end

end Sanctions
