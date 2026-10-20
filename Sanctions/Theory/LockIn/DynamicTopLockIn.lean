/-
Sanctions/Theory/LockIn/DynamicTopLockIn.lean

**Top-selector dynamic lock-in path consequences.**

Mirrors `DynamicLockIn.lean` but uses the *upper* dynamic Sender argmax
selector `σ_dyn_top` (`Theory/LockIn/SigmaDynComparison.lean`) instead
of the `Classical.choose`-based `σ_dyn` (`Theory/Equilibrium/JointMPE.lean`).

Under monotone Sender continuation value `V_S`, `σ_dyn_top ≥ σ`
*unconditionally* (no uniqueness needed; cf. `σ_dyn_top_ge_sigma`), so
the top-selector lock-in path admits a clean equilibrium-vs-myopic
dominance theorem (`dynamicTopSanctions_ge_myopify_same_alpha` in
`Theory/Basin/JointPreferenceBasin.lean`) without the auxiliary
"same level on the myopic side" hypothesis required by the σ_dyn analog
`DynamicLockIn.dynamicLockInSanctions_ge_lockInSanctions`.

## Rule compliance

**Rule 1.** Every theorem uses `p.σ_dyn_top V_S x (α x)` — the upper
selector of the dynamic Sender argmax set — as the realized sanction
along the natural path. This is equilibrium-derived: `σ_dyn_top` is
in `dynamicArgmaxSet V_S x a` (i.e. is a forward-looking Sender
maximizer; `σ_dyn_top_mem_dynamicArgmaxSet` in `SigmaDynComparison`).

**Rule 2 / 3.** Local theorem-parameter hypotheses only
(`h_level_top`, `h_top_rule_mono`); no new fields on
`AbstractGame.Params`; no new Postulates; no new global `Prop` taken
as a hypothesis of a load-bearing theorem. Each hypothesis parallels
an existing kinematic hypothesis in `LockIn.lean` / `DynamicLockIn.lean`.

**Rule 5.** All theorems parametric over `(p, V_S, α, …)`. No
witness-specific instantiation.
-/

import Sanctions.Theory.LockIn.DynamicLockIn
import Sanctions.Theory.LockIn.SigmaDynComparison

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Forward-looking equilibrium-derived realized sanction rule (top selector) -/

/-- The *upper-selector* dynamic realized sanction rule along the Target
policy `α`: at each state `x`, the Sender plays the **maximum** element
of its forward-looking argmax set, `p.σ_dyn_top V_S x (α x)`. -/
noncomputable def dynamicTopRealizedRule
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) : ℝ → ℝ :=
  fun x => p.σ_dyn_top V_S x (α x)

/-- The upper-selector dynamic realized rule is automatically feasible
(from `σ_dyn_top_mem_I`). -/
theorem dynamicTopRealizedRule_mem
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) :
    p.dynamicTopRealizedRule V_S α x ∈ Sanctions.I :=
  p.σ_dyn_top_mem_I V_S x (α x)

/-! ## One-step top-dynamic natural dynamics -/

/-- One step of the natural dynamics under the upper-dynamic
equilibrium rule.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** This definition hard-codes
`(1 − δ)·x + δ·rule` and **never routes through `p.F`**. Every theorem
whose conclusion is stated over `dynamicTopLockInStep` /
`dynamicTopLockInPath` / `dynamicTopLockInSanctions` is therefore
restricted to the affine transition *even though its signature contains
no* `hF : p.F = affineF p.δ`. That invisibility is exactly why the
project's scope note under-reported the affine surface for so long.

**Use `dynamicTopLockInStepF` / `dynamicTopLockInPathF` /
`dynamicTopLockInSanctionsF` (below) in new work.** They are the
general-`F` siblings — same definitions with `p.F x (…)` in place of the
hand-written affine law — and they are what the project's general-`F`
design goal requires. The bridge back is
`dynamicTopLockInStep_eq_stepF_of_affine`
(`Examples/AffineInstance/Kinematics.lean`), which consumes `hF`. -/
noncomputable def dynamicTopLockInStep
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - p.δ) * x + p.δ * p.dynamicTopRealizedRule V_S α x

/-- The upper-dynamic natural state path from `x₀`. -/
noncomputable def dynamicTopLockInPath
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.dynamicTopLockInStep V_S α x)^[n] x₀

/-- The upper-dynamic realized sanction sequence along the upper-dynamic
natural path. -/
noncomputable def dynamicTopLockInSanctions
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  p.dynamicTopRealizedRule V_S α (p.dynamicTopLockInPath V_S α x₀ n)

@[simp] theorem dynamicTopLockInPath_zero
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) :
    p.dynamicTopLockInPath V_S α x₀ 0 = x₀ := rfl

@[simp] theorem dynamicTopLockInPath_succ
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicTopLockInPath V_S α x₀ (n + 1) =
      p.dynamicTopLockInStep V_S α (p.dynamicTopLockInPath V_S α x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-! ## Forward invariance and state-path monotonicity on the basin -/

/-- Under the top-selector level condition
`max x sbar ≤ σ_dyn_top V_S x (α x)` on the basin, one top-dynamic step
is weakly above the current state. -/
theorem dynamicTopLockInStep_ge_self
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    x ≤ p.dynamicTopLockInStep V_S α x := by
  have h_x_le : x ≤ p.dynamicTopRealizedRule V_S α x :=
    le_trans (le_max_left x sbar) (h_level_top x hx)
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  unfold dynamicTopLockInStep
  nlinarith [mul_nonneg hδ_nonneg (sub_nonneg.mpr h_x_le)]

/-- One top-dynamic step stays below 1 (feasibility + `δ ∈ (0,1)`). -/
theorem dynamicTopLockInStep_le_one
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar : ℝ}
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicTopLockInStep V_S α x ≤ 1 := by
  have hg := p.dynamicTopRealizedRule_mem V_S α x
  have hδ_nonneg : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have h1δ_nonneg : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  unfold dynamicTopLockInStep
  have hpart₁ : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
    mul_le_mul_of_nonneg_left hx.2 h1δ_nonneg
  have hpart₂ : p.δ * p.dynamicTopRealizedRule V_S α x ≤ p.δ * 1 :=
    mul_le_mul_of_nonneg_left hg.2 hδ_nonneg
  nlinarith

/-- Forward invariance of `[xbar, 1]` under the top-dynamic dynamics. -/
theorem dynamicTopLockInStep_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicTopLockInStep V_S α x ∈ Set.Icc xbar 1 := by
  refine ⟨?_, p.dynamicTopLockInStep_le_one V_S α hx⟩
  exact le_trans hx.1 (p.dynamicTopLockInStep_ge_self V_S α h_level_top hx)

/-- Every top-dynamic state stays in `[xbar, 1]`. -/
theorem dynamicTopLockInPath_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPath_succ]
    exact p.dynamicTopLockInStep_mem_basin V_S α h_level_top ih

/-- The top-dynamic state path is non-decreasing. -/
theorem dynamicTopLockInPath_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.dynamicTopLockInPath V_S α x₀) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [dynamicTopLockInPath_succ]
  exact p.dynamicTopLockInStep_ge_self V_S α h_level_top
    (p.dynamicTopLockInPath_mem_basin V_S α h_level_top hx₀ n)

/-! ## General-`F` realized path (Option B, R-2026-06-22)

The realized-path objects above evolve the state by the affine law
`(1 − δ)·x + δ·σ`. The siblings below evolve it by the **abstract
transition** `p.F x σ`, so the persistence conclusions hold for any `F`
satisfying the structural fields (`F_mem`, `F_mono_s`, `F_diag`) — not
only the affine instance; the affine objects are the `F := affineF δ`
specialisation. The realized sanction rule `dynamicTopRealizedRule` (the
forward-looking equilibrium top selector) is unchanged; only the
state-evolution map is generalised. **No new assumption**: the basin
lemmas consume `F_mono_s` (the next state weakly rises in the sanction),
`F_diag` (`F x x = x`), and, for the upper edge, `F_le_one_of_le` (from
`F_mem_uIcc`, which holds on all of `ℝ`). They used to carry an extra
`0 ≤ xbar`, read only to make basin states feasible for `F_mem`; since
BG2.1 (2026-10-06) the upper edge no longer needs it, and the basin
lemmas below hold for any `xbar`. -/

/-- One step of the natural dynamics under the upper-dynamic equilibrium
rule, evolved by the **abstract transition** `p.F` rather than the affine
law. -/
noncomputable def dynamicTopLockInStepF
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.F x (p.dynamicTopRealizedRule V_S α x)

/-- The general-`F` upper-dynamic natural state path from `x₀`. -/
noncomputable def dynamicTopLockInPathF
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.dynamicTopLockInStepF V_S α x)^[n] x₀

/-- The general-`F` upper-dynamic realized sanction sequence. -/
noncomputable def dynamicTopLockInSanctionsF
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  p.dynamicTopRealizedRule V_S α (p.dynamicTopLockInPathF V_S α x₀ n)

@[simp] theorem dynamicTopLockInPathF_zero
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) :
    p.dynamicTopLockInPathF V_S α x₀ 0 = x₀ := rfl

@[simp] theorem dynamicTopLockInPathF_succ
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicTopLockInPathF V_S α x₀ (n + 1) =
      p.dynamicTopLockInStepF V_S α (p.dynamicTopLockInPathF V_S α x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- Feasibility: one general-`F` step from a feasible state stays feasible
(`F_mem` + rule feasibility). -/
theorem dynamicTopLockInStepF_mem_I_of_mem_I
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    p.dynamicTopLockInStepF V_S α x ∈ Sanctions.I :=
  p.F_mem x _ hx (p.dynamicTopRealizedRule_mem V_S α x)

/-- Under the top-selector level condition, one general-`F` step is weakly
above the current state: `x = F x x ≤ F x σ` since `σ ≥ x`
(`F_mono_s` + `F_diag`). -/
theorem dynamicTopLockInStepF_ge_self
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    x ≤ p.dynamicTopLockInStepF V_S α x := by
  have h_x_le : x ≤ p.dynamicTopRealizedRule V_S α x :=
    le_trans (le_max_left x sbar) (h_level_top x hx)
  have hmono : p.F x x ≤ p.F x (p.dynamicTopRealizedRule V_S α x) :=
    p.F_mono_s x h_x_le
  rwa [p.F_diag x] at hmono

/-- **Upper edge of any basin `[xbar, 1]`, domain-free (general in `F`).**
`F x s ≤ 1` whenever `x ≤ 1` and `s ≤ 1`, with no lower bound on `x` or
`s`. The next state lies between the current state and the sanction
(`F_mem_uIcc`, from `F_mono_x`, `F_mono_s` and `F_diag`, all global on
`ℝ`), so it is at most `max x s ≤ 1`. Economically: a state that is not
above full compliance, pushed by a sanction that is not above the full
sanction, never overshoots full compliance. It replaces the
`F_mem`-route upper edge, which needed `0 ≤ x` and `0 ≤ s` and was the
only reason the basin lemmas below used to carry `0 ≤ xbar` (BG2.1). -/
theorem F_le_one_of_le {x s : ℝ} (hx : x ≤ 1) (hs : s ≤ 1) : p.F x s ≤ 1 := by
  rcases Set.mem_uIcc.1 (p.F_mem_uIcc x s) with h | h
  exacts [h.2.trans hs, h.2.trans hx]

/-- Forward invariance of `[xbar, 1]` under the general-`F` dynamics
(general in `F`). The lower edge is the ratchet `x ≤ F x (rule x)`; the
upper edge is `F_le_one_of_le`. Holds for every `xbar`: the hypothesis
`0 ≤ xbar`, which the old `F_mem` route to the upper edge needed, was
dropped on 2026-10-06 (BG2.1). -/
theorem dynamicTopLockInStepF_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicTopLockInStepF V_S α x ∈ Set.Icc xbar 1 :=
  ⟨le_trans hx.1 (p.dynamicTopLockInStepF_ge_self V_S α h_level_top hx),
   p.F_le_one_of_le hx.2 (p.dynamicTopRealizedRule_mem V_S α x).2⟩

/-- Every general-`F` state stays in `[xbar, 1]` (general in `F`; no
`0 ≤ xbar`, dropped in BG2.1). -/
theorem dynamicTopLockInPathF_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPathF_succ]
    exact p.dynamicTopLockInStepF_mem_basin V_S α h_level_top ih

/-- The general-`F` state path is non-decreasing (general in `F`; no
`0 ≤ xbar`, dropped in BG2.1). -/
theorem dynamicTopLockInPathF_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.dynamicTopLockInPathF V_S α x₀) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [dynamicTopLockInPathF_succ]
  exact p.dynamicTopLockInStepF_ge_self V_S α h_level_top
    (p.dynamicTopLockInPathF_mem_basin V_S α h_level_top hx₀ n)

/-- General-`F` sanction floor: `sbar ≤ s_n` along the `F`-path (general
in `F`; no `0 ≤ xbar`, dropped in BG2.1). -/
theorem dynamicTopLockInSanctionsF_floor
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n := by
  intro n
  unfold dynamicTopLockInSanctionsF
  exact le_trans (le_max_right (p.dynamicTopLockInPathF V_S α x₀ n) sbar)
    (h_level_top (p.dynamicTopLockInPathF V_S α x₀ n)
      (p.dynamicTopLockInPathF_mem_basin V_S α h_level_top hx₀ n))

/-- General-`F` `xbar`-floor: `xbar ≤ s_n` along the `F`-path (general in
`F`; no `0 ≤ xbar`, dropped in BG2.1). -/
theorem dynamicTopLockInSanctionsF_ge_xbar
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n := by
  intro n
  unfold dynamicTopLockInSanctionsF
  have h_mem : p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1 :=
    p.dynamicTopLockInPathF_mem_basin V_S α h_level_top hx₀ n
  exact le_trans (le_max_of_le_left h_mem.1)
    (h_level_top (p.dynamicTopLockInPathF V_S α x₀ n) h_mem)

/-- General-`F` sanction monotonicity along the `F`-path (rule monotone on
the basin ∘ monotone path-into-basin; general in `F`; no `0 ≤ xbar`,
dropped in BG2.1). -/
theorem dynamicTopLockInSanctionsF_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (h_top_rule_mono :
        MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  intro m n hmn
  unfold dynamicTopLockInSanctionsF
  exact h_top_rule_mono
    (p.dynamicTopLockInPathF_mem_basin V_S α h_level_top hx₀ m)
    (p.dynamicTopLockInPathF_mem_basin V_S α h_level_top hx₀ n)
    (p.dynamicTopLockInPathF_mono V_S α h_level_top hx₀ hmn)

/-! ## The ratchet alone gives the entry floor (BH2.1, 2026-10-06)

The level condition `max x sbar ≤ R x` bundles two facts: the *ratchet*
`x ≤ R x` (the realised sanction is at least the current state) and the
*floor* `sbar ≤ R x`. Basin invariance, the non-decreasing state path and the
floor `max x₀ xbar` inherited at entry read only the ratchet: on the basin
`max x xbar = x`, so the ratchet is the level condition at `sbar := xbar`.
The persistence and post-entry results that state these conclusions used to
take the whole eight-field joint basin, including the interval-dominance
direction input (A1) and the Target's sanction preference (P4); the lemmas
here take the ratchet and nothing else. -/

/-- **The ratchet is the level condition with the pivot as floor** (general in
`F`: no transition is read). On the basin `[xbar, 1]` we have `max x xbar = x`,
so `x ≤ R x` there is exactly `max x xbar ≤ R x`. -/
theorem dynamicTopRealizedRule_level_of_ratchet
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule V_S α x) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), max x xbar ≤ p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  rw [max_eq_left hx.1]
  exact h_ratchet x hx

/-- **Entry floor from the ratchet alone** (general in `F`). If the realised rule
is weakly above the state on the basin `[xbar, 1]`, then from every basin start
`x₀` every realised sanction along the general-`F` path is at least
`max x₀ xbar`: the path stays in the basin and never falls below `x₀`, and the
rule sits above the state it is applied to.

Hypotheses dropped against `jointPreferenceBasinTopF_sanctions_ge_entry`
(`PostEntryNonTermination.lean`), which states the same conclusion: the joint
basin is replaced by its one consumed consequence, the ratchet. No `0 ≤ xbar`
(the basin lemmas lost it in BG2.1), no sanction floor `sbar`, no
interval-dominance input and no Target sanction preference. The ratchet is also
necessary for this conclusion: at `n = 0` it reads `x₀ ≤ R x₀`. Kinematic: `α`
is arbitrary here; cite an equilibrium-anchored form for an economic claim. -/
theorem dynamicTopLockInSanctionsF_ge_entry
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar x₀ : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule V_S α x)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, max x₀ xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n := by
  have hlevel := p.dynamicTopRealizedRule_level_of_ratchet V_S α h_ratchet
  intro n
  rw [max_eq_left hx₀.1]
  have hx₀_le_path : x₀ ≤ p.dynamicTopLockInPathF V_S α x₀ n := by
    simpa using p.dynamicTopLockInPathF_mono V_S α hlevel hx₀ (Nat.zero_le n)
  unfold dynamicTopLockInSanctionsF
  exact le_trans hx₀_le_path
    (h_ratchet _ (p.dynamicTopLockInPathF_mem_basin V_S α hlevel hx₀ n))

/-! ## Basin-free `[0, 1]`-invariance

Needed for the same-α dominance theorem in `JointPreferenceBasin`,
which compares the upper-dynamic path against the myopic path without
imposing a basin level condition (the dominance follows from the
unconditional `σ_dyn_top ≥ σ` under monotone $V_S$, not from a level
hypothesis). -/

/-- One top-dynamic step from a feasible state stays feasible. -/
theorem dynamicTopLockInStep_mem_I_of_mem_I
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    p.dynamicTopLockInStep V_S α x ∈ Sanctions.I := by
  have hg := p.dynamicTopRealizedRule_mem V_S α x
  have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
  have h1δ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  unfold dynamicTopLockInStep
  refine ⟨?_, ?_⟩
  · have h1 : 0 ≤ (1 - p.δ) * x := mul_nonneg h1δ_nn hx.1
    have h2 : 0 ≤ p.δ * p.dynamicTopRealizedRule V_S α x :=
      mul_nonneg hδ_nn hg.1
    linarith
  · have h1 : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
      mul_le_mul_of_nonneg_left hx.2 h1δ_nn
    have h2 : p.δ * p.dynamicTopRealizedRule V_S α x ≤ p.δ * 1 :=
      mul_le_mul_of_nonneg_left hg.2 hδ_nn
    nlinarith

/-- Every top-dynamic state from a feasible starting state stays feasible. -/
theorem dynamicTopLockInPath_mem_I_of_mem_I
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Sanctions.I := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPath_succ]
    exact p.dynamicTopLockInStep_mem_I_of_mem_I V_S α ih

/-! ## Top-dynamic sanction sequence -/

theorem dynamicTopLockInSanctions_mem
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicTopLockInSanctions V_S α x₀ n ∈ Sanctions.I :=
  p.dynamicTopRealizedRule_mem V_S α _

/-- Along the top-dynamic natural path in the basin, sanctions are
bounded below by `sbar`. -/
theorem dynamicTopLockInSanctions_floor
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n := by
  intro n
  unfold dynamicTopLockInSanctions
  exact le_trans (le_max_right (p.dynamicTopLockInPath V_S α x₀ n) sbar)
    (h_level_top (p.dynamicTopLockInPath V_S α x₀ n)
      (p.dynamicTopLockInPath_mem_basin V_S α h_level_top hx₀ n))

/-- **Strengthened floor: sanctions stay at least at the basin pivot
`xbar`.** Since `x_n ∈ [xbar, 1]` and the level condition gives
`max x_n sbar ≤ σ_dyn_top V_S x_n (α x_n)`, and clearly
`xbar ≤ x_n ≤ max x_n sbar`, we get the cleaner "high sanction"
statement `xbar ≤ s_n`. (Compare `dynamicTopLockInSanctions_floor`,
which gives the `sbar`-floor; the `xbar`-floor is independent of
`sbar`'s sign, but it identifies "high" with the basin geometry
rather than the separate sanction floor.) -/
theorem dynamicTopLockInSanctions_ge_xbar
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, xbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n := by
  intro n
  unfold dynamicTopLockInSanctions
  have h_mem :
      p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1 :=
    p.dynamicTopLockInPath_mem_basin V_S α h_level_top hx₀ n
  have h_max_ge :
      xbar ≤ max (p.dynamicTopLockInPath V_S α x₀ n) sbar :=
    le_max_of_le_left h_mem.1
  exact le_trans h_max_ge
    (h_level_top (p.dynamicTopLockInPath V_S α x₀ n) h_mem)

/-- If the top-dynamic equilibrium rule is monotone on the basin, the
top-dynamic sanction sequence is non-decreasing. -/
theorem dynamicTopLockInSanctions_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (h_top_rule_mono :
        MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    Monotone (p.dynamicTopLockInSanctions V_S α x₀) := by
  intro m n hmn
  unfold dynamicTopLockInSanctions
  exact h_top_rule_mono
    (p.dynamicTopLockInPath_mem_basin V_S α h_level_top hx₀ m)
    (p.dynamicTopLockInPath_mem_basin V_S α h_level_top hx₀ n)
    (p.dynamicTopLockInPath_mono V_S α h_level_top hx₀ hmn)

/-! ## Post-shock top-dynamic persistence

The exogenous shock arithmetic from `LockIn.lean` (`shockPath`,
`shockPath_eventually_in_basin`) is independent of the realized
post-shock argmax — during the shock the Sender's action is exogenously
`s = 1`, the project's sole Rule-1 exception. So we can compose the
shock arithmetic with the upper-dynamic post-shock dynamics. -/

/-- **Temporary shock causes permanent high sanctions under the
upper-dynamic equilibrium rule.** -/
theorem dynamicTop_temporary_shock_post_shock_persistence
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.dynamicTopLockInPath_mem_basin V_S α h_level_top h_N_in,
    p.dynamicTopLockInSanctions_floor V_S α h_level_top h_N_in⟩

/-- **Temporary shock + monotone upper-dynamic rule → permanent
non-decreasing high sanctions.** -/
theorem dynamicTop_temporary_shock_post_shock_monotone
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (h_top_rule_mono :
        MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N)) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N,
    p.dynamicTopLockInPath_mem_basin V_S α h_level_top h_N_in,
    p.dynamicTopLockInSanctions_floor V_S α h_level_top h_N_in,
    p.dynamicTopLockInSanctions_mono V_S α h_level_top h_top_rule_mono h_N_in⟩

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
