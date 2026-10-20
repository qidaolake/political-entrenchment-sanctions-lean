/-
Sanctions/Theory/LockIn/DynamicLockIn.lean

**Forward-looking dynamic lock-in path consequences.**

Bridges `Sanctions/Theory/LockIn/LockIn.lean` (kinematic results for
the *stage*-argmax sanction rule `p.σ x (α x)`) to the *forward-looking*
Sender response

  `dynamicRealizedRule V_S α x := p.σ_dyn V_S x (α x)`

where `σ_dyn` is the Sender's argmax of the **dynamic** objective
`U_S(x, a, s) + β_S · V_S(F(x, s))` (defined in
`Theory/Equilibrium/JointMPE.lean`). For `β_S > 0` this is the true
Rule-1 equilibrium-derived Sender response; the stage argmax `p.σ`
coincides with `σ_dyn` only when `β_S = 0`.

This file proves the **same kinematic consequences** as `LockIn.lean`,
but for the dynamic rule:

* Forward invariance of `[xbar, 1]` under the dynamic step;
* Non-decreasing dynamic state path on `[xbar, 1]`;
* Dynamic sanction sequence floor `sbar`;
* Dynamic sanction sequence monotonicity (under monotone-rule hypothesis).

It also proves the **dynamic-vs-myopic comparison theorem** at the
path level: under a pointwise inequality `σ x (α x) ≤ σ_dyn V_S x (α x)`
(the canonical economic content "forward-looking Sender weakly more
aggressive than myopic Sender" — discharged at the call site from
`V_S_x ≥ 0` + Topkis single-crossing in the standard regime), the
dynamic state path dominates the myopic state path, and consequently
the dynamic sanction sequence dominates the myopic one.

Finally, post-shock composition: the exogenous shock arithmetic from
`LockIn.lean` (`shockPath`, `shockPath_eventually_in_basin`) is reused
verbatim — the shock phase is the project's sole Rule-1 exception and
its `s ≡ 1` path is independent of either argmax — so we get
`dynamic_temporary_shock_post_shock_persistence` and its monotone
sibling.

## Rule compliance

**Rule 1.** Every theorem here uses
`p.σ_dyn V_S x (α x)` (the true forward-looking equilibrium-derived
Sender response) as the realized sanction along the natural path.
The Target policy `α` is universal-quantified; its Bellman optimality
is to be discharged at the call site (e.g. via
`Theory/Bellman/Verification.lean` against the joint Target Bellman
of `JointMPE.lean`). No fixed / hand-chosen sanction rule appears.

**Rule 2 / 3.** Local theorem-parameter hypotheses only
(`h_level_dyn`, `h_rule_mono_dyn`, `h_dyn_ge_myo`); no new fields on
`AbstractGame.Params`; no new Postulates; no new global `Prop` taken
as a hypothesis of a load-bearing theorem. Each hypothesis parallels
an existing kinematic hypothesis in `LockIn.lean`, just instantiated
to the dynamic argmax `σ_dyn V_S`.

**Rule 5.** All theorems parametric over
`(p : AbstractGame.Params, V_S, α, …)`. No witness-specific
instantiation here; non-vacuity of the parameter region is discharged
in the `Sanctions/Examples/` layer, which now carries four complete
certificate witnesses (`eeCertCertificate` 2026-07-01,
`qbCertCertificateMS` and `lbLow_generalF_three_goals` 2026-07-03,
and the B2 non-monotone-continuation witness 2026-07-04).
-/

import Sanctions.Theory.LockIn.LockIn
import Sanctions.Theory.Equilibrium.JointMPE

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Forward-looking equilibrium-derived realized sanction rule -/

/-- The *dynamic* realized sanction rule along the Target policy `α`:
at each state `x`, the Sender plays its **forward-looking** argmax
`p.σ_dyn V_S x (α x)`. Rule-1 compliance is via `σ_dyn_isMaxOn`
(the argmax of the dynamic Sender objective
`U_S(x, a, s) + β_S · V_S(F(x, s))`). -/
noncomputable def dynamicRealizedRule
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) : ℝ → ℝ :=
  fun x => p.σ_dyn V_S x (α x)

/-- The dynamic realized rule is automatically feasible
(from `σ_dyn_mem`). -/
theorem dynamicRealizedRule_mem
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) :
    p.dynamicRealizedRule V_S α x ∈ Sanctions.I :=
  p.σ_dyn_mem V_S x (α x)

/-! ## One-step dynamic natural dynamics -/

/-- One step of the natural dynamics under the **dynamic** equilibrium
rule.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** The body writes
`(1 − δ)·x + δ·rule` by hand and **never routes through `p.F`**, so every
theorem stated over `dynamicLockInStep` / `dynamicLockInPath` /
`dynamicLockInSanctions` is restricted to the affine transition *even
though its signature contains no* `hF : p.F = affineF p.δ`. That
invisibility is the axis Rule 22 exists to catch.

Unlike `dynamicTopLockInStep`, this family has **no `…F` general-transition
sibling anywhere in the tree**. New general-`F` work should use
`dynamicTopLockInStepF` / `dynamicTopLockInPathF` /
`dynamicTopLockInSanctionsF` (`Theory/LockIn/DynamicTopLockIn.lean`)
instead of adding theorems here. -/
noncomputable def dynamicLockInStep
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - p.δ) * x + p.δ * p.dynamicRealizedRule V_S α x

/-- The dynamic natural state path from `x₀`. -/
noncomputable def dynamicLockInPath
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.dynamicLockInStep V_S α x)^[n] x₀

/-- The dynamic realized sanction sequence along the dynamic natural path. -/
noncomputable def dynamicLockInSanctions
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  p.dynamicRealizedRule V_S α (p.dynamicLockInPath V_S α x₀ n)

@[simp] theorem dynamicLockInPath_zero
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) :
    p.dynamicLockInPath V_S α x₀ 0 = x₀ := rfl

@[simp] theorem dynamicLockInPath_succ
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicLockInPath V_S α x₀ (n + 1) =
      p.dynamicLockInStep V_S α (p.dynamicLockInPath V_S α x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-! ## Dynamic forward invariance and state-path monotonicity -/

/-- Under the dynamic level condition
`max x sbar ≤ σ_dyn V_S x (α x)` on the basin, one dynamic step is
weakly above the current state. -/
theorem dynamicLockInStep_ge_self
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    x ≤ p.dynamicLockInStep V_S α x := by
  have h_x_le : x ≤ p.dynamicRealizedRule V_S α x :=
    le_trans (le_max_left x sbar) (h_level_dyn x hx)
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  unfold dynamicLockInStep
  nlinarith [mul_nonneg hδ_nonneg (sub_nonneg.mpr h_x_le)]

/-- One dynamic step stays below 1 (feasibility + `δ ∈ (0,1)`). -/
theorem dynamicLockInStep_le_one
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar : ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicLockInStep V_S α x ≤ 1 := by
  have hg := p.dynamicRealizedRule_mem V_S α x
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have h1δ_nonneg : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  unfold dynamicLockInStep
  have hpart₁ : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
    mul_le_mul_of_nonneg_left hx.2 h1δ_nonneg
  have hpart₂ : p.δ * p.dynamicRealizedRule V_S α x ≤ p.δ * 1 :=
    mul_le_mul_of_nonneg_left hg.2 hδ_nonneg
  nlinarith

/-- Forward invariance of `[xbar, 1]` under the dynamic dynamics. -/
theorem dynamicLockInStep_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicLockInStep V_S α x ∈ Set.Icc xbar 1 := by
  refine ⟨?_, p.dynamicLockInStep_le_one V_S α hx⟩
  exact le_trans hx.1 (p.dynamicLockInStep_ge_self V_S α h_level_dyn hx)

/-- Every dynamic state stays in `[xbar, 1]`. -/
theorem dynamicLockInPath_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.dynamicLockInPath V_S α x₀ n ∈ Set.Icc xbar 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicLockInPath_succ]
    exact p.dynamicLockInStep_mem_basin V_S α h_level_dyn ih

/-- The dynamic state path is non-decreasing. -/
theorem dynamicLockInPath_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.dynamicLockInPath V_S α x₀) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [dynamicLockInPath_succ]
  exact p.dynamicLockInStep_ge_self V_S α h_level_dyn
    (p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n)

/-! ## Dynamic sanction sequence -/

/-- Along the dynamic natural path, sanctions stay feasible. -/
theorem dynamicLockInSanctions_mem
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicLockInSanctions V_S α x₀ n ∈ Sanctions.I :=
  p.dynamicRealizedRule_mem V_S α _

/-- Along the dynamic natural path in the basin, sanctions are bounded
below by `sbar`. -/
theorem dynamicLockInSanctions_floor
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, sbar ≤ p.dynamicLockInSanctions V_S α x₀ n := by
  intro n
  unfold dynamicLockInSanctions
  exact le_trans (le_max_right (p.dynamicLockInPath V_S α x₀ n) sbar)
    (h_level_dyn (p.dynamicLockInPath V_S α x₀ n)
      (p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n))

/-- If the dynamic equilibrium rule is monotone on the basin, the
dynamic sanction sequence is non-decreasing. -/
theorem dynamicLockInSanctions_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    (h_rule_mono_dyn :
        MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.dynamicLockInSanctions V_S α x₀) := by
  intro m n hmn
  unfold dynamicLockInSanctions
  exact h_rule_mono_dyn
    (p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ m)
    (p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n)
    (p.dynamicLockInPath_mono V_S α h_level_dyn hx₀ hmn)

/-! ## Dynamic-vs-myopic comparison

The headline comparison: under a *pointwise* "forward-looking ≥ myopic"
inequality on the realized Sender response (canonical economic content
discharged from `V_S_x ≥ 0` + Topkis single-crossing in the standard
regime), the dynamic state path is pointwise ≥ the myopic state path,
and consequently the dynamic sanction sequence pointwise ≥ the myopic
sanction sequence.

The myopic comparator is the existing `lockInStep` of `LockIn.lean`,
which uses `p.σ x (α x)` (the *stage* argmax). At `β_S = 0` we have
`σ_dyn V_S x a = p.σ x a`, so `lockInStep` is the genuine β-zero
comparator. (We don't construct a separate `myopicParams` at
`β_S = β_T = 0`; the same `α` is used in both paths and the comparison
is purely at the Sender-rule level.) -/

/-- Pointwise monotonicity of one step in the realized rule: if
`g₁ x ≤ g₂ x` then the corresponding one-step updates satisfy the
same inequality. (Auxiliary; not depending on dynamic vs myopic.) -/
private theorem step_mono_in_rule
    {g₁ g₂ : ℝ → ℝ} {x : ℝ} (h_rule : g₁ x ≤ g₂ x) :
    (1 - p.δ) * x + p.δ * g₁ x ≤ (1 - p.δ) * x + p.δ * g₂ x := by
  have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  nlinarith [mul_le_mul_of_nonneg_left h_rule hδ_nn]

/-- **Dynamic state path dominates myopic state path** under
`σ x (α x) ≤ σ_dyn V_S x (α x)` and monotonicity of the dynamic rule
on the basin (so the dynamic path stays in the basin where the
comparison hypothesis applies). -/
theorem dynamicLockInPath_ge_lockInPath
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    (h_level_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.realizedRule α x)
    (h_dyn_ge_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      p.realizedRule α x ≤ p.dynamicRealizedRule V_S α x)
    (h_dyn_mono : MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.lockInPath α x₀ n ≤ p.dynamicLockInPath V_S α x₀ n := by
  intro n
  induction n with
  | zero => simp [lockInPath, dynamicLockInPath]
  | succ n ih =>
    have h_myo_in : p.lockInPath α x₀ n ∈ Set.Icc xbar 1 :=
      p.lockInPath_mem_basin α h_level_myo hx₀ n
    have h_dyn_in : p.dynamicLockInPath V_S α x₀ n ∈ Set.Icc xbar 1 :=
      p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n
    have h_dyn_succ_in : p.dynamicLockInPath V_S α x₀ (n + 1) ∈ Set.Icc xbar 1 :=
      p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ (n + 1)
    -- Step 1: at the myopic state, the dynamic step from this state dominates
    -- the myopic step from this state (because σ_dyn ≥ σ pointwise on the basin).
    have h_step_at_myo :
        p.lockInStep α (p.lockInPath α x₀ n)
          ≤ p.dynamicLockInStep V_S α (p.lockInPath α x₀ n) := by
      unfold lockInStep dynamicLockInStep
      exact p.step_mono_in_rule (h_dyn_ge_myo _ h_myo_in)
    -- Step 2: the dynamic step from the myopic state is dominated by the
    -- dynamic step from the (≥) dynamic state — because the dynamic step
    -- function `(1-δ) x + δ · σ_dyn V_S x (α x)` is monotone in `x` on the
    -- basin (both `(1-δ) x` and `σ_dyn V_S x (α x)` are monotone there).
    have h_step_dyn_mono :
        p.dynamicLockInStep V_S α (p.lockInPath α x₀ n)
          ≤ p.dynamicLockInStep V_S α (p.dynamicLockInPath V_S α x₀ n) := by
      unfold dynamicLockInStep
      have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
      have h1δ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
      have h_rule_mono :
          p.dynamicRealizedRule V_S α (p.lockInPath α x₀ n)
            ≤ p.dynamicRealizedRule V_S α (p.dynamicLockInPath V_S α x₀ n) :=
        h_dyn_mono h_myo_in h_dyn_in ih
      have h_state_mono :
          (1 - p.δ) * p.lockInPath α x₀ n
            ≤ (1 - p.δ) * p.dynamicLockInPath V_S α x₀ n :=
        mul_le_mul_of_nonneg_left ih h1δ_nn
      have h_rule_part :
          p.δ * p.dynamicRealizedRule V_S α (p.lockInPath α x₀ n)
            ≤ p.δ * p.dynamicRealizedRule V_S α (p.dynamicLockInPath V_S α x₀ n) :=
        mul_le_mul_of_nonneg_left h_rule_mono hδ_nn
      linarith
    -- Compose:
    simp only [lockInPath_succ, dynamicLockInPath_succ]
    exact le_trans h_step_at_myo h_step_dyn_mono

/-- **Dynamic sanction sequence pointwise dominates myopic sanction
sequence** on the basin, under the σ_dyn ≥ σ comparison hypothesis
plus dynamic-rule monotonicity. -/
theorem dynamicLockInSanctions_ge_lockInSanctions
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    (h_level_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.realizedRule α x)
    (h_dyn_ge_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      p.realizedRule α x ≤ p.dynamicRealizedRule V_S α x)
    (h_dyn_mono : MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.lockInSanctions α x₀ n ≤ p.dynamicLockInSanctions V_S α x₀ n := by
  intro n
  have h_myo_in : p.lockInPath α x₀ n ∈ Set.Icc xbar 1 :=
    p.lockInPath_mem_basin α h_level_myo hx₀ n
  have h_dyn_in : p.dynamicLockInPath V_S α x₀ n ∈ Set.Icc xbar 1 :=
    p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n
  have h_path_le : p.lockInPath α x₀ n ≤ p.dynamicLockInPath V_S α x₀ n :=
    p.dynamicLockInPath_ge_lockInPath V_S α h_level_dyn h_level_myo
      h_dyn_ge_myo h_dyn_mono hx₀ n
  -- Sanctions:  σ(x_myo, α) ≤ σ_dyn(x_myo, α) ≤ σ_dyn(x_dyn, α)
  unfold lockInSanctions dynamicLockInSanctions
  calc p.realizedRule α (p.lockInPath α x₀ n)
      ≤ p.dynamicRealizedRule V_S α (p.lockInPath α x₀ n) :=
          h_dyn_ge_myo _ h_myo_in
    _ ≤ p.dynamicRealizedRule V_S α (p.dynamicLockInPath V_S α x₀ n) :=
          h_dyn_mono h_myo_in h_dyn_in h_path_le

/-! ## Long-run convergence of the dynamic path and sanctions

The state path is monotone non-decreasing on `[xbar, 1]` and bounded
above by `1`, so it converges to some limit `xlim ∈ [x₀, 1]`. From the
recurrence `x_{n+1} = (1 - δ) x_n + δ s_n` with `δ > 0`, the dynamic
sanction sequence converges to the *same* limit. The positive sanction
floor `sbar` lifts to a lower bound on the limit: `sbar ≤ xlim`. -/

/-- **Long-run convergence of the dynamic state path.** Monotone +
bounded above gives convergence to the supremum of the trajectory. -/
theorem dynamicLockInPath_tendsto
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∃ xlim ∈ Set.Icc x₀ 1,
      Tendsto (p.dynamicLockInPath V_S α x₀) atTop (𝓝 xlim) := by
  have h_mono := p.dynamicLockInPath_mono V_S α h_level_dyn hx₀
  have h_bdd : BddAbove (Set.range (p.dynamicLockInPath V_S α x₀)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n).2
  have h_tend := tendsto_atTop_ciSup h_mono h_bdd
  refine ⟨⨆ n, p.dynamicLockInPath V_S α x₀ n, ?_, h_tend⟩
  refine ⟨?_, ?_⟩
  · -- x₀ = path 0 ≤ ⨆ n, path n
    have h0 : x₀ = p.dynamicLockInPath V_S α x₀ 0 := rfl
    rw [h0]
    exact le_ciSup h_bdd 0
  · -- ⨆ n, path n ≤ 1
    exact ciSup_le (fun n =>
      (p.dynamicLockInPath_mem_basin V_S α h_level_dyn hx₀ n).2)

/-- **Long-run convergence of the dynamic sanction sequence to the
same limit as the state path.** From the recurrence
`x_{n+1} = (1 - δ) x_n + δ s_n` with `δ > 0`, we recover
`s_n = (x_{n+1} - (1 - δ) x_n) / δ`, which tends to
`(xlim - (1 - δ) xlim) / δ = xlim`. -/
theorem dynamicLockInSanctions_tendsto_same_limit
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (x₀ : ℝ) {xlim : ℝ}
    (h_path_tend : Tendsto (p.dynamicLockInPath V_S α x₀) atTop (𝓝 xlim)) :
    Tendsto (p.dynamicLockInSanctions V_S α x₀) atTop (𝓝 xlim) := by
  have hδ_pos : 0 < p.δ := p.δ_mem.1
  -- Pointwise expression: s_n = (x_{n+1} - (1 - δ) x_n) / δ.
  have h_step : ∀ n,
      p.dynamicLockInSanctions V_S α x₀ n
        = (p.dynamicLockInPath V_S α x₀ (n + 1)
           - (1 - p.δ) * p.dynamicLockInPath V_S α x₀ n) / p.δ := by
    intro n
    have h_succ := p.dynamicLockInPath_succ V_S α x₀ n
    have h_san : p.dynamicLockInSanctions V_S α x₀ n
                  = p.dynamicRealizedRule V_S α (p.dynamicLockInPath V_S α x₀ n) :=
      rfl
    -- x_{n+1} = (1 - δ) x_n + δ * dynamicRealizedRule
    -- ⇒ dynamicRealizedRule = (x_{n+1} - (1 - δ) x_n) / δ
    rw [h_san]
    have hδ_ne : p.δ ≠ 0 := ne_of_gt hδ_pos
    have h_eq : (1 - p.δ) * p.dynamicLockInPath V_S α x₀ n
                + p.δ * p.dynamicRealizedRule V_S α
                          (p.dynamicLockInPath V_S α x₀ n)
              = p.dynamicLockInPath V_S α x₀ (n + 1) := by
      rw [h_succ]; unfold dynamicLockInStep; rfl
    have : p.δ * p.dynamicRealizedRule V_S α
                  (p.dynamicLockInPath V_S α x₀ n)
            = p.dynamicLockInPath V_S α x₀ (n + 1)
              - (1 - p.δ) * p.dynamicLockInPath V_S α x₀ n := by
      linarith
    field_simp at this ⊢
    linarith
  -- The shifted path also converges to xlim.
  have h_path_succ_tend :
      Tendsto (fun n => p.dynamicLockInPath V_S α x₀ (n + 1)) atTop (𝓝 xlim) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr h_path_tend
  -- Combined: ((path(n+1)) - (1 - δ) * path n) / δ → (xlim - (1 - δ) xlim) / δ = xlim.
  have h_combo :
      Tendsto (fun n => (p.dynamicLockInPath V_S α x₀ (n + 1)
                         - (1 - p.δ) * p.dynamicLockInPath V_S α x₀ n) / p.δ)
              atTop (𝓝 ((xlim - (1 - p.δ) * xlim) / p.δ)) := by
    have h_diff := h_path_succ_tend.sub (h_path_tend.const_mul (1 - p.δ))
    exact h_diff.div_const _
  have h_limit_eq : (xlim - (1 - p.δ) * xlim) / p.δ = xlim := by
    have hδ_ne : p.δ ≠ 0 := ne_of_gt hδ_pos
    field_simp
    ring
  rw [← h_limit_eq]
  exact h_combo.congr (fun n => (h_step n).symm)

/-- **Long-run lower bound: the dynamic state-path limit is at least
the sanction floor `sbar`.** Combines the convergence of dynamic
sanctions to the same limit as the path with the per-period sanction
floor. -/
theorem dynamicLockInPath_limit_ge_sbar
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) {xlim : ℝ}
    (h_path_tend : Tendsto (p.dynamicLockInPath V_S α x₀) atTop (𝓝 xlim)) :
    sbar ≤ xlim := by
  have h_san_tend :=
    p.dynamicLockInSanctions_tendsto_same_limit V_S α x₀ h_path_tend
  have h_san_ge : ∀ n, sbar ≤ p.dynamicLockInSanctions V_S α x₀ n :=
    p.dynamicLockInSanctions_floor V_S α h_level_dyn hx₀
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_san_tend h_san_ge

/-! ## Dynamic comparison with vanishing baseline -/

/-- Under the dynamic lock-in regime with positive floor `sbar > 0`,
dynamic sanctions are pointwise weakly higher than the zero baseline. -/
theorem dynamicLockInSanctions_ge_zero
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hsbar_pos : 0 < sbar)
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, (0:ℝ) ≤ p.dynamicLockInSanctions V_S α x₀ n := by
  intro n
  have hf : sbar ≤ p.dynamicLockInSanctions V_S α x₀ n :=
    p.dynamicLockInSanctions_floor V_S α h_level_dyn hx₀ n
  linarith

/-- For any vanishing comparison sequence `s_myo → 0`, dynamic
sanctions are eventually weakly higher. (The same is established for
the stage-argmax rule in `LockIn.lockInSanctions_eventually_ge_vanishing`.) -/
theorem dynamicLockInSanctions_eventually_ge_vanishing
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hsbar_pos : 0 < sbar)
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1)
    {s_myo : ℕ → ℝ} (h_myo : Tendsto s_myo atTop (𝓝 0)) :
    ∀ᶠ n in atTop, s_myo n ≤ p.dynamicLockInSanctions V_S α x₀ n := by
  have h_event_lt : ∀ᶠ n in atTop, s_myo n < sbar :=
    h_myo.eventually (eventually_lt_nhds hsbar_pos)
  filter_upwards [h_event_lt] with n hn
  exact le_trans (le_of_lt hn)
    (p.dynamicLockInSanctions_floor V_S α h_level_dyn hx₀ n)

/-! ## Post-shock dynamic persistence

The exogenous shock arithmetic from `LockIn.lean` (`shockPath`,
`shockPath_eventually_in_basin`) is independent of the realized
post-shock argmax — during the shock the Sender's action is
exogenously `s = 1`, the project's sole Rule-1 exception. So we can
compose the shock arithmetic with the *dynamic* post-shock dynamics. -/

/-- **Temporary shock causes permanent high sanctions under the
forward-looking dynamic equilibrium rule.**

Given a basin `[xbar, 1]` with `xbar < 1`, a positive sanction floor
`sbar`, and the dynamic level condition on the basin: after some shock
duration `N`, the post-shock dynamic natural dynamics
(using `p.σ_dyn V_S x (α x)`) stay in the basin forever and the dynamic
sanction sequence is bounded below by `sbar`. -/
theorem dynamic_temporary_shock_post_shock_persistence
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicLockInPath V_S α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicLockInSanctions V_S α (p.shockPath x₀ N) n) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.dynamicLockInPath_mem_basin V_S α h_level_dyn h_N_in,
    p.dynamicLockInSanctions_floor V_S α h_level_dyn h_N_in⟩

/-- **Temporary shock + monotone dynamic rule → permanent non-decreasing
high sanctions under the forward-looking dynamic equilibrium rule.** -/
theorem dynamic_temporary_shock_post_shock_monotone
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    (h_rule_mono_dyn :
        MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicLockInPath V_S α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicLockInSanctions V_S α (p.shockPath x₀ N)) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.dynamicLockInPath_mem_basin V_S α h_level_dyn h_N_in,
    p.dynamicLockInSanctions_floor V_S α h_level_dyn h_N_in,
    p.dynamicLockInSanctions_mono V_S α h_level_dyn h_rule_mono_dyn h_N_in⟩

/-- **Post-shock dynamic ≥ myopic sanctions.**
Composes the shock-entry arithmetic with the dynamic-vs-myopic
comparison: from any `x₀ ∈ [0, 1]`, after `N` shock periods the state
is in `[xbar, 1]`, and the post-shock dynamic sanction sequence
pointwise dominates the post-shock myopic sanction sequence (both
starting from the same post-shock state). -/
theorem dynamic_temporary_shock_post_shock_dominates_myopic
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level_dyn : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicRealizedRule V_S α x)
    (h_level_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.realizedRule α x)
    (h_dyn_ge_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      p.realizedRule α x ≤ p.dynamicRealizedRule V_S α x)
    (h_dyn_mono : MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ, ∀ n,
      p.lockInSanctions α (p.shockPath x₀ N) n
        ≤ p.dynamicLockInSanctions V_S α (p.shockPath x₀ N) n := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.dynamicLockInSanctions_ge_lockInSanctions V_S α h_level_dyn h_level_myo
      h_dyn_ge_myo h_dyn_mono h_N_in⟩

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
