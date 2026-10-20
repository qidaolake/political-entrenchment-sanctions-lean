/-
Sanctions/Theory/LockIn/LockIn.lean

**Reduced-form lock-in path consequences for the abstract sanctions game.**

Parametric over `Sanctions.AbstractGame.Params` plus a Target policy
`α : ℝ → ℝ`. The realized sanction rule along the path is the
equilibrium-derived

  `realizedRule p α x := p.σ x (α x)`,

where `p.σ` is the Sender's stage argmax (carried by `Params` via the
structural `σ_isMaxOn_U_S` hypothesis — i.e. equilibrium-derived by
construction). `α` is a Target policy that, in equilibrium applications,
should attain the Target Bellman fixed point; that attainment is
discharged at the call site via `verification_target_one_shot_deviation`
(see `Theory/Bellman/Verification.lean`).

This module proves the **kinematic path consequences** of the
equilibrium-driven dynamics on a forward-invariant high basin, once the
standard economic conditions on the realized rule hold as hypotheses:

* `level condition` — `max x sbar ≤ realizedRule α x` on `[xbar, 1]`
  (substantive: saturation of the projected response, i.e. the
  equilibrium sanction is at least as high as the inherited state and
  a positive floor `sbar`);
* `realized-rule monotonicity` — `realizedRule α` is monotone on
  `[xbar, 1]` (substantive: Topkis-monotone comparative statics on the
  equilibrium sanction response).

(Feasibility `realizedRule α x ∈ [0, 1]` is automatic via `p.σ_mem`.)

Consequences:

* Forward invariance of `[xbar, 1]` under the natural dynamics;
* The state path from any `x₀ ∈ [xbar, 1]` is non-decreasing;
* The realized sanction sequence stays in `[0, 1]`, is bounded below
  by `sbar > 0`, and is non-decreasing.

The module also formalizes the **temporary-shock hysteresis arithmetic**
purely kinematically: a closed-form `1 - (1 - δ)^n · (1 - x₀)` for the
exogenously-forced maximum-sanction path, convergence to 1, eventual
entry into any basin `[xbar, 1]` with `xbar < 1`. The shock phase is
the project's sole Rule-1 exception (the sanction path is forced, not
chosen). Post-shock dynamics inherit the equilibrium rule and the
lock-in conclusions above; this is packaged as
`temporary_shock_post_shock_persistence`.

**Rule-1 compliance.** Every theorem here uses
`realizedRule α x = p.σ x (α x)` with `p.σ` the equilibrium Sender
response. No hand-chosen sanction rule appears anywhere. The
dynamic-vs-myopic comparison theorems compare against either the zero
baseline or a generic vanishing sequence — not a hand-chosen
comparator.

**Rule-3 compliance.** No new fields on `AbstractGame.Params`. No new
Postulate structure. The basin/floor and level/monotonicity conditions
are local theorem-parameter hypotheses on existing data (namely on
`p.σ x (α x)`); they are provable at any concrete `AbstractGame.Params`
instantiation from saturation arithmetic + Topkis single-crossing.

**Rule-5 compliance.** All theorems parametric. No witness-specific
theorems; no `g ≡ 1`-style hand-chosen sanction rule. Non-vacuity at
concrete `AbstractGame.Params` is discharged in the
`Sanctions/Examples/` layer, which now carries four complete
certificate witnesses (`eeCertCertificate` 2026-07-01,
`qbCertCertificateMS` and `lbLow_generalF_three_goals` 2026-07-03,
and the B2 non-monotone-continuation witness 2026-07-04).
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Foundations.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence

namespace Sanctions

open Set Filter Topology

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Equilibrium-derived realized sanction rule -/

/-- The **myopic** realized sanction rule along the Target policy `α`:
at each state `x`, the Sender plays its *stage* argmax `p.σ x (α x)`
(Rule-1 compliance is via `p.σ_isMaxOn_U_S`, which makes `σ` a genuine
argmax rather than an assumed function).

**⚠ This is the COMPARATOR, not the equilibrium rule.** `p.σ` ignores
the continuation value entirely — `myopify_realizedRule` and its path
siblings hold by `rfl`, i.e. this family is β-independent. The
forward-looking equilibrium rule is `dynamicTopRealizedRule`, built from
`σ_dyn_top` and the Sender continuation value `V_S`. Quoting monotonicity
of `lockInSanctions` as "the equilibrium path ratchets" quotes the
comparator and collapses the paper's central dynamic-vs-myopic
comparison into a tautology. -/
def realizedRule (α : ℝ → ℝ) : ℝ → ℝ := fun x => p.σ x (α x)

/-- The realized rule is automatically feasible (from `p.σ_mem`). -/
theorem realizedRule_mem (α : ℝ → ℝ) (x : ℝ) :
    p.realizedRule α x ∈ Sanctions.I :=
  p.σ_mem x (α x)

/-! ## One-step natural dynamics -/

/-- One step of the natural dynamics under the equilibrium rule.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** Hard-codes
`(1 − δ)·x + δ·rule`; does **not** route through `p.F`. Theorems stated
over `lockInStep` / `lockInPath` are affine-restricted with no `hF` in
their signature. Prefer a general-`F` formulation in new work. -/
def lockInStep (α : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - p.δ) * x + p.δ * p.realizedRule α x

/-- The natural state path from `x₀` (iterated `lockInStep`). -/
def lockInPath (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.lockInStep α x)^[n] x₀

/-- The realized sanction sequence along the natural path. -/
def lockInSanctions (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  p.realizedRule α (p.lockInPath α x₀ n)

@[simp] theorem lockInPath_zero (α : ℝ → ℝ) (x₀ : ℝ) :
    p.lockInPath α x₀ 0 = x₀ := rfl

@[simp] theorem lockInPath_succ (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.lockInPath α x₀ (n + 1) = p.lockInStep α (p.lockInPath α x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-! ## Forward invariance and monotonicity of the state path -/

/-- Under the level condition `max x sbar ≤ realizedRule α x` on the
basin, one natural step is weakly above the current state. -/
theorem lockInStep_ge_self (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    x ≤ p.lockInStep α x := by
  have h_x_le : x ≤ p.realizedRule α x :=
    le_trans (le_max_left x sbar) (h_level x hx)
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  unfold lockInStep
  nlinarith [mul_nonneg hδ_nonneg (sub_nonneg.mpr h_x_le)]

/-- One natural step stays below 1 (uses only feasibility + `δ ∈ (0,1)`). -/
theorem lockInStep_le_one (α : ℝ → ℝ) {xbar : ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.lockInStep α x ≤ 1 := by
  have hg := p.realizedRule_mem α x
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have h1δ_nonneg : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  unfold lockInStep
  have hpart₁ : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
    mul_le_mul_of_nonneg_left hx.2 h1δ_nonneg
  have hpart₂ : p.δ * p.realizedRule α x ≤ p.δ * 1 :=
    mul_le_mul_of_nonneg_left hg.2 hδ_nonneg
  nlinarith

/-- Forward invariance of `[xbar, 1]` under the natural dynamics. -/
theorem lockInStep_mem_basin (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.lockInStep α x ∈ Set.Icc xbar 1 := by
  refine ⟨?_, p.lockInStep_le_one α hx⟩
  exact le_trans hx.1 (p.lockInStep_ge_self α h_level hx)

/-- Every natural state stays in `[xbar, 1]` from a starting state in
`[xbar, 1]`. -/
theorem lockInPath_mem_basin (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.lockInPath α x₀ n ∈ Set.Icc xbar 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [lockInPath_succ]
    exact p.lockInStep_mem_basin α h_level ih

/-- The natural state path is non-decreasing. -/
theorem lockInPath_mono (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.lockInPath α x₀) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [lockInPath_succ]
  exact p.lockInStep_ge_self α h_level (p.lockInPath_mem_basin α h_level hx₀ n)

/-! ## Realized sanction sequence -/

/-- Along the natural path, sanctions stay feasible. -/
theorem lockInSanctions_mem (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.lockInSanctions α x₀ n ∈ Sanctions.I :=
  p.realizedRule_mem α _

/-- Along the natural path in the basin, sanctions are bounded below by `sbar`. -/
theorem lockInSanctions_floor (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, sbar ≤ p.lockInSanctions α x₀ n := by
  intro n
  unfold lockInSanctions
  exact le_trans (le_max_right (p.lockInPath α x₀ n) sbar)
    (h_level (p.lockInPath α x₀ n) (p.lockInPath_mem_basin α h_level hx₀ n))

/-- If the equilibrium rule is monotone on the basin, the sanction
sequence is non-decreasing. -/
theorem lockInSanctions_mono (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    (h_rule_mono : MonotoneOn (p.realizedRule α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.lockInSanctions α x₀) := by
  intro m n hmn
  unfold lockInSanctions
  exact h_rule_mono
    (p.lockInPath_mem_basin α h_level hx₀ m)
    (p.lockInPath_mem_basin α h_level hx₀ n)
    (p.lockInPath_mono α h_level hx₀ hmn)

/-! ## Dynamic-vs-myopic comparison -/

/-- Under the lock-in regime with positive floor `sbar > 0`, dynamic
sanctions are pointwise weakly higher than the zero baseline. -/
theorem lockInSanctions_ge_zero (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hsbar_pos : 0 < sbar)
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, (0:ℝ) ≤ p.lockInSanctions α x₀ n := by
  intro n
  have hf : sbar ≤ p.lockInSanctions α x₀ n :=
    p.lockInSanctions_floor α h_level hx₀ n
  linarith

/-- For any vanishing comparison sequence `s_myo → 0`, dynamic sanctions
are eventually weakly higher. -/
theorem lockInSanctions_eventually_ge_vanishing (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hsbar_pos : 0 < sbar)
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1)
    {s_myo : ℕ → ℝ} (h_myo : Tendsto s_myo atTop (𝓝 0)) :
    ∀ᶠ n in atTop, s_myo n ≤ p.lockInSanctions α x₀ n := by
  have h_event_lt : ∀ᶠ n in atTop, s_myo n < sbar :=
    h_myo.eventually (eventually_lt_nhds hsbar_pos)
  filter_upwards [h_event_lt] with n hn
  exact le_trans (le_of_lt hn) (p.lockInSanctions_floor α h_level hx₀ n)

/-! ## Temporary exogenous shock arithmetic

The shock phase is the project's sole Rule-1 exception: during a
transient externally-imposed phase, the Sender's sanction is forced to
`s = 1` regardless of either player's optimization. After the shock
ends, the natural dynamics under the equilibrium rule resume and the
lock-in conclusions above apply. -/

/-- One period of exogenously forced maximum sanction.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** Hard-codes the affine law and
does **not** route through `p.F`. The general-`F` sibling is `shockStepF`
(`p.F x 1`) with path `shockPathF`; prefer those in new work. -/
def shockStep (x : ℝ) : ℝ := (1 - p.δ) * x + p.δ * 1

/-- The state path during the shock phase, starting from `x₀`
(iterated `shockStep`). -/
def shockPath (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.shockStep x)^[n] x₀

@[simp] theorem shockPath_zero (x₀ : ℝ) : p.shockPath x₀ 0 = x₀ := rfl

@[simp] theorem shockPath_succ (x₀ : ℝ) (n : ℕ) :
    p.shockPath x₀ (n + 1) = p.shockStep (p.shockPath x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- Closed-form for the shock path:
`x_n = 1 - (1 - δ)^n · (1 - x₀)`. -/
theorem shockPath_closed_form (x₀ : ℝ) :
    ∀ n, p.shockPath x₀ n = 1 - (1 - p.δ)^n * (1 - x₀) := by
  intro n
  induction n with
  | zero => simp [shockPath]
  | succ n ih =>
    simp only [shockPath_succ, shockStep, ih, pow_succ]
    ring

/-- The shock path stays in `[x₀, 1]` from any `x₀ ∈ [0, 1]`. The
lower-bound hypothesis `x₀ ≥ 0` is kept in the signature for
caller clarity but is not consumed by the proof (which only needs
`x₀ ≤ 1` plus the per-step convex combination). -/
theorem shockPath_mem_Icc {x₀ : ℝ} (_hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∀ n, p.shockPath x₀ n ∈ Set.Icc x₀ 1 := by
  intro n
  induction n with
  | zero => exact ⟨le_refl _, hx₀_le⟩
  | succ n ih =>
    obtain ⟨ih_ge, ih_le⟩ := ih
    have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
    have h1δ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
    simp only [shockPath_succ, shockStep]
    refine ⟨?_, ?_⟩
    · have h_diff_nn : 0 ≤ p.δ * (1 - p.shockPath x₀ n) :=
        mul_nonneg hδ_nn (by linarith)
      nlinarith
    · nlinarith

/-- The shock path converges to 1. -/
theorem shockPath_tendsto_one (x₀ : ℝ) :
    Tendsto (p.shockPath x₀) atTop (𝓝 1) := by
  have h_eq : ∀ n, p.shockPath x₀ n = 1 - (1 - p.δ)^n * (1 - x₀) :=
    p.shockPath_closed_form x₀
  have hδ_lt : 1 - p.δ < 1 := by linarith [p.δ_mem.1]
  have hδ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  have h_pow : Tendsto (fun n => (1 - p.δ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hδ_nn hδ_lt
  have h_mul : Tendsto (fun n => (1 - p.δ)^n * (1 - x₀)) atTop (𝓝 0) := by
    have := h_pow.mul_const (1 - x₀)
    simpa using this
  have h_sub : Tendsto (fun n => 1 - (1 - p.δ)^n * (1 - x₀)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h_mul
  simp only [sub_zero] at h_sub
  convert h_sub using 1
  funext n; exact h_eq n

/-- For any basin floor `xbar < 1`, the shock path from any
`x₀ ∈ [0, 1]` eventually enters `[xbar, 1]`. -/
theorem shockPath_eventually_in_basin {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1)
    {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∃ N : ℕ, ∀ n ≥ N, p.shockPath x₀ n ∈ Set.Icc xbar 1 := by
  have h_tend : Tendsto (p.shockPath x₀) atTop (𝓝 1) :=
    p.shockPath_tendsto_one x₀
  have h_event_gt : ∀ᶠ n in atTop, xbar < p.shockPath x₀ n :=
    h_tend.eventually (eventually_gt_nhds hxbar_lt)
  rw [Filter.eventually_atTop] at h_event_gt
  obtain ⟨N, hN⟩ := h_event_gt
  refine ⟨N, fun n hn => ?_⟩
  refine ⟨le_of_lt (hN n hn), ?_⟩
  exact (p.shockPath_mem_Icc hx₀_nn hx₀_le n).2

/-! ## General-`F` exogenous shock (Option B, R-2026-06-22)

The affine shock objects above force `s = 1` through the affine law.
The siblings below force `s = 1` through the **abstract transition**
`p.F x 1`, so finite entry holds for any `F` (the affine law is the
`F := affineF δ` instance). The shock remains the project's sole Rule-1
exogenous-phase exception. Where the affine path has the closed form
`x_n = 1 − (1−δ)^n(1−x₀)` (hence the explicit horizon `N_*`), the
general-`F` path uses **monotone convergence**: the iterates rise
(`F x 1 ≥ F x x = x`), are bounded by `1`, hence converge to a fixed
point of `F(·,1)` by continuity; the strict-above-diagonal hypothesis
`hF_top` (`∀ x ∈ [0,1), x < F x 1`) excludes every interior fixed point,
so the limit is `1` and entry into any basin `[xbar, 1]` with `xbar < 1`
is finite. The price of generality is the loss of the closed-form
horizon `N_*`. -/

/-- One period of exogenously forced maximum sanction under the abstract
transition `p.F`. -/
def shockStepF (x : ℝ) : ℝ := p.F x 1

/-- The one-period state gain under an exogenously forced maximum sanction. -/
def fullShockDrift (x : ℝ) : ℝ := p.F x 1 - x

/-- **Canonical minimum full-sanction drift below a basin threshold.**
This is the paper's `η_F(xbar)`: the infimum of `F(x, 1) - x` over
the compact pre-basin interval `[0, xbar]`. Under strict adjustment and
`xbar ∈ [0, 1)`, the infimum is attained and strictly positive. -/
noncomputable def fullShockMinDrift (xbar : ℝ) : ℝ :=
  sInf (p.fullShockDrift '' Set.Icc (0 : ℝ) xbar)

/-- **Canonical conservative full-sanction entry horizon.**
This is the paper's `N̂_F(xbar) = ⌈xbar / η_F(xbar)⌉`. -/
noncomputable def fullShockEntryHorizon (xbar : ℝ) : ℕ :=
  Nat.ceil (xbar / p.fullShockMinDrift xbar)

/-- The general-`F` shock state path from `x₀` (iterated `shockStepF`). -/
def shockPathF (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.shockStepF x)^[n] x₀

@[simp] theorem shockPathF_zero (x₀ : ℝ) : p.shockPathF x₀ 0 = x₀ := rfl

@[simp] theorem shockPathF_succ (x₀ : ℝ) (n : ℕ) :
    p.shockPathF x₀ (n + 1) = p.shockStepF (p.shockPathF x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- One general-`F` shock step is weakly above the current state
(`F x 1 ≥ F x x = x`, since `x ≤ 1` and `F_mono_s` + `F_diag`). -/
theorem shockStepF_ge_self {x : ℝ} (hx1 : x ≤ 1) : x ≤ p.shockStepF x := by
  have hmono : p.F x x ≤ p.F x 1 := p.F_mono_s x hx1
  rwa [p.F_diag x] at hmono

/-- One general-`F` shock step from a feasible state stays feasible. -/
theorem shockStepF_mem_Icc01 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    p.shockStepF x ∈ Set.Icc (0 : ℝ) 1 :=
  p.F_mem x 1 hx ⟨by norm_num, le_refl _⟩

/-- The general-`F` shock path stays in `[x₀, 1]` from any `x₀ ∈ [0, 1]`. -/
theorem shockPathF_mem_Icc {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∀ n, p.shockPathF x₀ n ∈ Set.Icc x₀ 1 := by
  intro n
  induction n with
  | zero => exact ⟨le_refl _, hx₀_le⟩
  | succ n ih =>
    obtain ⟨ih_ge, ih_le⟩ := ih
    have hxn_mem : p.shockPathF x₀ n ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans hx₀_nn ih_ge, ih_le⟩
    rw [shockPathF_succ]
    exact ⟨le_trans ih_ge (p.shockStepF_ge_self ih_le),
           (p.shockStepF_mem_Icc01 hxn_mem).2⟩

/-- The general-`F` shock path is non-decreasing from `x₀ ∈ [0, 1]`. -/
theorem shockPathF_mono {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    Monotone (p.shockPathF x₀) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [shockPathF_succ]
  exact p.shockStepF_ge_self (p.shockPathF_mem_Icc hx₀_nn hx₀_le n).2

/-- General-`F` shock paths preserve the order of their initial states. -/
theorem shockPathF_mono_start {x₀ y₀ : ℝ} (hxy : x₀ ≤ y₀) :
    ∀ n, p.shockPathF x₀ n ≤ p.shockPathF y₀ n := by
  intro n
  induction n with
  | zero => exact hxy
  | succ n ih =>
    rw [shockPathF_succ, shockPathF_succ]
    exact p.F_mono_x 1 ih

/-- **General-`F` shock convergence to saturation.** From any
`x₀ ∈ [0, 1]`, the strict-above-diagonal hypothesis `hF_top` forces the
monotone bounded shock path to converge to `1`: its limit is a fixed
point of `F(·, 1)` (continuity), and `hF_top` excludes every interior
fixed point. -/
theorem shockPathF_tendsto_one
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    Tendsto (p.shockPathF x₀) atTop (𝓝 1) := by
  have hmono : Monotone (p.shockPathF x₀) := p.shockPathF_mono hx₀_nn hx₀_le
  have hbdd : BddAbove (Set.range (p.shockPathF x₀)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (p.shockPathF_mem_Icc hx₀_nn hx₀_le n).2
  set S := ⨆ n, p.shockPathF x₀ n with hS
  have h_tend : Tendsto (p.shockPathF x₀) atTop (𝓝 S) :=
    tendsto_atTop_ciSup hmono hbdd
  -- The limit is a fixed point of `F(·, 1)` by continuity.
  have hcont : Continuous (fun x => p.F x 1) := by
    have h2 : Continuous (fun x : ℝ => (x, (1 : ℝ))) := by fun_prop
    exact p.F_continuous.comp h2
  have h_tend_shift : Tendsto (fun n => p.shockPathF x₀ (n + 1)) atTop (𝓝 S) :=
    h_tend.comp (tendsto_add_atTop_nat 1)
  have h_tend_F : Tendsto (fun n => p.F (p.shockPathF x₀ n) 1) atTop (𝓝 (p.F S 1)) :=
    (hcont.tendsto S).comp h_tend
  have h_fix : p.F S 1 = S := by
    have h_eq : (fun n => p.shockPathF x₀ (n + 1)) =
        fun n => p.F (p.shockPathF x₀ n) 1 := by
      funext n; rw [shockPathF_succ]; rfl
    rw [h_eq] at h_tend_shift
    exact tendsto_nhds_unique h_tend_F h_tend_shift
  have hx0_le_S : x₀ ≤ S := le_ciSup hbdd 0
  have hS_nn : 0 ≤ S := le_trans hx₀_nn hx0_le_S
  have hS_le : S ≤ 1 := ciSup_le (fun n => (p.shockPathF_mem_Icc hx₀_nn hx₀_le n).2)
  have hS_eq : S = 1 := by
    rcases lt_or_eq_of_le hS_le with hlt | heq
    · exfalso
      have hcontra := hF_top S ⟨hS_nn, hlt⟩
      rw [h_fix] at hcontra
      exact lt_irrefl S hcontra
    · exact heq
  rwa [hS_eq] at h_tend

/-- For any basin floor `xbar < 1`, the general-`F` shock path from any
`x₀ ∈ [0, 1]` eventually enters `[xbar, 1]` (finite entry, no closed-form
horizon). -/
theorem shockPathF_eventually_in_basin
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1)
    {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∃ N : ℕ, ∀ n ≥ N, p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  have h_tend : Tendsto (p.shockPathF x₀) atTop (𝓝 1) :=
    p.shockPathF_tendsto_one hF_top hx₀_nn hx₀_le
  have h_event_gt : ∀ᶠ n in atTop, xbar < p.shockPathF x₀ n :=
    h_tend.eventually (eventually_gt_nhds hxbar_lt)
  rw [Filter.eventually_atTop] at h_event_gt
  obtain ⟨N, hN⟩ := h_event_gt
  refine ⟨N, fun n hn => ⟨le_of_lt (hN n hn), ?_⟩⟩
  exact (p.shockPathF_mem_Icc hx₀_nn hx₀_le n).2

/-- **Worst-case general-`F` shock-entry horizon.** A single finite
duration works for every feasible initial state. The duration is the one
needed from state `0`, which is worst-case because `F` is monotone in the
inherited state. -/
theorem shockPathF_uniform_eventually_in_basin
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∃ N : ℕ, ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ N,
      p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  obtain ⟨N, hN⟩ := p.shockPathF_eventually_in_basin hF_top
    (x₀ := 0) (le_refl 0) zero_le_one hxbar_lt
  refine ⟨N, ?_⟩
  intro x₀ hx₀ n hn
  have hzero := hN n hn
  exact ⟨le_trans hzero.1 (p.shockPathF_mono_start hx₀.1 n),
    (p.shockPathF_mem_Icc hx₀.1 hx₀.2 n).2⟩

/-- Under strict adjustment toward the current sanction, one finite
maximum-sanction duration moves every feasible initial state into any
nondegenerate high basin. -/
theorem shockPathF_uniform_eventually_in_basin_of_strictAdjustment
    (hAdj : p.StrictAdjustment) {xbar : ℝ} (hxbar_lt : xbar < 1) :
    ∃ N : ℕ, ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ N,
      p.shockPathF x₀ n ∈ Set.Icc xbar 1 :=
  p.shockPathF_uniform_eventually_in_basin hAdj.hF_top hxbar_lt

/-- **Positive minimum full-sanction drift below a basin threshold.**
Under strict adjustment, continuity makes `fullShockDrift` attain its
minimum on `[0, xbar]`, and F5 makes that minimum strictly positive when
`xbar < 1`. The witness `xmin` records that `η` is the actual minimum,
not merely an arbitrary positive lower bound. -/
theorem fullShockDrift_exists_pos_isMinOn
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar, η = p.fullShockDrift xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x := by
  have hcont : Continuous (p.fullShockDrift) := by
    have hpair : Continuous (fun x : ℝ => (x, (1 : ℝ))) := by fun_prop
    exact (p.F_continuous.comp hpair).sub continuous_id
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hxbar.1) hcont.continuousOn
  let η := p.fullShockDrift xmin
  have hη_pos : 0 < η := by
    have hxminIco : xmin ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨hxmin.1, lt_of_le_of_lt hxmin.2 hxbar.2⟩
    have hlt := hAdj.self_lt_F_one hxminIco
    dsimp [η, fullShockDrift]
    linarith
  refine ⟨η, hη_pos, ⟨xmin, hxmin, rfl⟩, ?_⟩
  intro x hx
  exact hmin hx

/-- **The canonical general-`F` minimum drift is positive and attained.**
Under strict adjustment, `fullShockMinDrift` is the actual minimum of
`F(x, 1) - x` on `[0, xbar]`, not merely an arbitrary drift floor. -/
theorem fullShockMinDrift_pos_attains_isMinOn
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    0 < p.fullShockMinDrift xbar ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar,
        p.fullShockMinDrift xbar = p.fullShockDrift xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xbar,
        p.fullShockMinDrift xbar ≤ p.fullShockDrift x := by
  obtain ⟨η, hη_pos, ⟨xmin, hxmin, hη_eq⟩, hη_min⟩ :=
    p.fullShockDrift_exists_pos_isMinOn hAdj hxbar
  let driftRange : Set ℝ := p.fullShockDrift '' Set.Icc (0 : ℝ) xbar
  have hRange_nonempty : driftRange.Nonempty :=
    ⟨p.fullShockDrift xmin, ⟨xmin, hxmin, rfl⟩⟩
  have hRange_bdd : BddBelow driftRange := by
    refine ⟨η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hMin_le : p.fullShockMinDrift xbar ≤ η := by
    apply csInf_le hRange_bdd
    exact ⟨xmin, hxmin, hη_eq.symm⟩
  have hMin_ge : η ≤ p.fullShockMinDrift xbar := by
    apply le_csInf hRange_nonempty
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hMin_eq : p.fullShockMinDrift xbar = η :=
    le_antisymm hMin_le hMin_ge
  refine ⟨hMin_eq ▸ hη_pos, ⟨xmin, hxmin, hMin_eq.trans hη_eq⟩, ?_⟩
  intro x hx
  rw [hMin_eq]
  exact hη_min x hx

/-- **Linear growth while the worst-case shock path remains below the
basin.** If every pre-basin state gains at least `η` under a full
sanction, then the shock path from zero has gained at least `n * η`
after `n` periods, provided its earlier iterates remain below `xbar`. -/
theorem shockPathF_linear_lower_bound_before_basin
    {xbar η : ℝ}
    (hη : ∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x) :
    ∀ n : ℕ, (∀ k < n, p.shockPathF 0 k ≤ xbar) →
      (n : ℝ) * η ≤ p.shockPathF 0 n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hstay
    have hprev_mem : p.shockPathF 0 n ∈ Set.Icc (0 : ℝ) xbar :=
      ⟨(p.shockPathF_mem_Icc (le_refl 0) zero_le_one n).1,
        hstay n (Nat.lt_succ_self n)⟩
    have hdrift := hη _ hprev_mem
    have hih : (n : ℝ) * η ≤ p.shockPathF 0 n :=
      ih (fun k hk => hstay k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    rw [shockPathF_succ]
    simp only [shockStepF, Nat.cast_add, Nat.cast_one]
    unfold fullShockDrift at hdrift
    linarith

/-- **Explicit general-`F` entry horizon from a drift floor.** If
`η > 0` is a lower bound for the full-sanction drift on `[0, xbar]`,
then `⌈xbar / η⌉₊` shock periods move every feasible initial state into
`[xbar, 1]`. Every longer imposed episode also works. -/
theorem shockPathF_uniform_natCeil_entry_of_drift
    {xbar η : ℝ} (hη_pos : 0 < η)
    (hη : ∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ Nat.ceil (xbar / η),
      p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  have hzero :
      p.shockPathF 0 (Nat.ceil (xbar / η)) ∈ Set.Icc xbar 1 := by
    let N := Nat.ceil (xbar / η)
    have hupper := (p.shockPathF_mem_Icc (le_refl 0) zero_le_one N).2
    refine ⟨?_, hupper⟩
    by_contra hnot
    have hlt : p.shockPathF 0 N < xbar := lt_of_not_ge hnot
    have hmono := p.shockPathF_mono (le_refl 0) zero_le_one
    have hstay : ∀ k < N, p.shockPathF 0 k ≤ xbar := by
      intro k hk
      exact le_trans (hmono (Nat.le_of_lt hk)) (le_of_lt hlt)
    have hlower : (N : ℝ) * η ≤ p.shockPathF 0 N :=
      p.shockPathF_linear_lower_bound_before_basin hη N hstay
    have hceil : xbar ≤ (N : ℝ) * η := by
      have hratio : xbar / η ≤ (N : ℝ) := by
        simpa [N] using (Nat.le_ceil (xbar / η))
      calc
        xbar = (xbar / η) * η := by field_simp
        _ ≤ (N : ℝ) * η := mul_le_mul_of_nonneg_right hratio hη_pos.le
    linarith
  intro x₀ hx₀ n hn
  refine ⟨?_, (p.shockPathF_mem_Icc hx₀.1 hx₀.2 n).2⟩
  exact le_trans hzero.1 <| le_trans
    (p.shockPathF_mono_start hx₀.1 (Nat.ceil (xbar / η)))
    (p.shockPathF_mono hx₀.1 hx₀.2 hn)

/-- **Quantitative uniform general-`F` shock bound under F5.** There is
an attained minimum drift `η_F(xbar) > 0` on `[0, xbar]`, and the
explicit duration

`N_F(xbar) = ⌈xbar / η_F(xbar)⌉₊`

moves every feasible initial state into the high basin. This derives a
computable-form upper bound from the existing continuity and strict-
adjustment assumptions; it adds no primitive hypothesis. -/
theorem shockPathF_exists_min_drift_uniform_natCeil_bound_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar, η = p.fullShockDrift xmin) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x) ∧
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ Nat.ceil (xbar / η),
        p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  obtain ⟨η, hη_pos, hη_attains, hη⟩ :=
    p.fullShockDrift_exists_pos_isMinOn hAdj hxbar
  exact ⟨η, hη_pos, hη_attains, hη,
    p.shockPathF_uniform_natCeil_entry_of_drift hη_pos hη⟩

/-- **The canonical general-`F` horizon uniformly guarantees basin entry.**
Under strict adjustment, every feasible initial state is in `[xbar, 1]`
at the paper's conservative horizon
`fullShockEntryHorizon p xbar = ⌈xbar / fullShockMinDrift p xbar⌉`,
and remains there at every later shock date. -/
theorem shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
      ∀ n ≥ p.fullShockEntryHorizon xbar,
        p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  obtain ⟨hη_pos, _, hη_min⟩ :=
    p.fullShockMinDrift_pos_attains_isMinOn hAdj hxbar
  exact p.shockPathF_uniform_natCeil_entry_of_drift hη_pos hη_min

/-- **Quantitative shock-entry horizon bound (Issue 5).** Given any
basin floor `xbar`, any starting state `x₀ ∈ [0, 1]`, and any shock
duration `T : ℕ` satisfying the pow-bound `(1 - δ)^T · (1 - x₀) ≤
1 - xbar`, the iterated maximum-sanction shock from `x₀` reaches the
basin in `T` periods: `shockPath x₀ T ≥ xbar`.

The bound is the explicit substantive condition. The closed-form
solution (paper-facing) is

  `T_*(xbar, δ) = ⌈log(1 - xbar) / log(1 - δ)⌉`

since `(1 - δ)^T ≤ 1 - xbar` iff `T · log(1 - δ) ≤ log(1 - xbar)` iff
`T ≥ log(1 - xbar) / log(1 - δ)` (the inequality flips because
`log(1 - δ) < 0`). Quantitative reading: for `δ = 0.3`, `xbar = 0.5`,
`T_* = 2`; for `xbar = 0.9`, `T_* = 7`; for `xbar = 0.99`,
`T_* = 13`. As `xbar → 1`, `T_* → ∞`. The "temporary" framing of
Theorem 3 in the paper should not be read as a small-bounded-number
claim.

The closed-form solution itself is elementary algebra and is not
machine-checked here; the substantive Lean content is the pow-bound
sufficient condition.

⚠ **Affine-restricted, deliberately (CLAUDE.md Rule 22, axis 2).** Both the
hypothesis `(1 − δ)^T · (1 − x₀) ≤ 1 − xbar` and the conclusion `xbar ≤ shockPath
x₀ T` are affine objects, and the proof is `rw [shockPath_closed_form]; linarith`.
Unlike every other affine footprint in the tree this one is **not a defect and
should not be generalised**: the geometric closed form *is* the content of the
theorem — a sharp horizon, not merely a finite one — and it exists only because
the transition is affine.

The general-`F` counterpart is already proved and is a different, weaker statement:
`shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment` (below) delivers an
explicit horizon `⌈x̄ / η_F(x̄)⌉` from `StrictAdjustment` alone — linear-drift
rather than geometric. Anyone wanting a general transition should cite that; this
theorem is the affine sharpening and is labelled as such in the headline snapshot
and in the paper's formalization map. Round BB (2026-09-28): `StrictAdjustment` is
more than that horizon needs. Pre-basin ascent — full sanction strictly raises every
state in `[0, x̄]` — suffices, with `0 ≤ x̄`
(`shockPathF_uniform_fullShockEntryHorizon_of_preBasinAscent`,
`LocalisedShockEntry.lean`).

Since the closing round of the renovation (2026-10-08, the author's decision; a
Rule 18 re-pin) the two initial-state bounds `0 ≤ x₀ ≤ 1`, which the proof never
read, are not binders. -/
theorem shockEntryHorizon_bound
    {x₀ : ℝ}
    {xbar : ℝ} (T : ℕ)
    (h_pow : (1 - p.δ) ^ T * (1 - x₀) ≤ 1 - xbar) :
    xbar ≤ p.shockPath x₀ T := by
  rw [p.shockPath_closed_form x₀ T]
  linarith

/-- **The affine horizon bound without the initial-state bounds** (round L, doc
80 M8). The two bounds `0 ≤ x₀ ≤ 1` of `shockEntryHorizon_bound` were not
consumed by its proof — the unused-binder audit of round K listed them as its
only two candidates — and this sibling stated the bound without them. Since the
closing round of the renovation (2026-10-08) the headline itself has this
statement, and this name is kept as an alias of it. Affine-restricted like its
parent (Rule 22, axis 2). -/
theorem shockEntryHorizon_bound_of_pow {x₀ xbar : ℝ} (T : ℕ)
    (h_pow : (1 - p.δ) ^ T * (1 - x₀) ≤ 1 - xbar) :
    xbar ≤ p.shockPath x₀ T :=
  p.shockEntryHorizon_bound T h_pow

/-! ## Composition: temporary-shock hysteresis (post-shock persistence) -/

/-- **Temporary shock causes permanent high sanctions.**

Given a basin `[xbar, 1]` with `xbar < 1`, a positive sanction floor
`sbar`, and the equilibrium-rule level condition on the basin: after
some shock duration `N`, the post-shock natural dynamics (under the
equilibrium rule `p.σ x (α x)`) stay in the basin forever and the
sanction sequence is bounded below by `sbar`. -/
theorem temporary_shock_post_shock_persistence (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.lockInPath α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.lockInSanctions α (p.shockPath x₀ N) n) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.lockInPath_mem_basin α h_level h_N_in,
    p.lockInSanctions_floor α h_level h_N_in⟩

/-- **Temporary shock + monotone equilibrium rule → permanent
non-decreasing high sanctions.** Strengthens the previous theorem
with the monotone-rule hypothesis to conclude monotonicity of the
post-shock sanction sequence. -/
theorem temporary_shock_post_shock_monotone (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                  max x sbar ≤ p.realizedRule α x)
    (h_rule_mono : MonotoneOn (p.realizedRule α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.lockInPath α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.lockInSanctions α (p.shockPath x₀ N) n) ∧
      Monotone (p.lockInSanctions α (p.shockPath x₀ N)) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.lockInPath_mem_basin α h_level h_N_in,
    p.lockInSanctions_floor α h_level h_N_in,
    p.lockInSanctions_mono α h_level h_rule_mono h_N_in⟩

end Params
end AbstractGame
end Sanctions
