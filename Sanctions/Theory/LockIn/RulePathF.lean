/-
Sanctions/Theory/LockIn/RulePathF.lean

**The general-`F` rule path: the state path that a realized sanction rule
drives under the maintained transition, and its order facts.**

Renovation round BH-6, item BH6.9 (2026-10-07). The declarations in §1–§3 were
moved here unchanged (same full names, same statements) from §11 of
`Theory/LockIn/DifferentPolicyComparator.lean`, so that the affine rule-path
lemmas of that file and of `Theory/Basin/JointPreferenceBasin.lean` can be
proved as instances of them. `JointPreferenceBasin.lean` imports this file, and
`DifferentPolicyComparator.lean` imports `JointPreferenceBasin.lean`, so every
former consumer still sees every name.

## What is here, in English

* **§1. The path.** Fix any realized sanction rule `R : ℝ → ℝ`. The next state
  is `F(x, R x)`, the maintained transition evaluated at the sanction the rule
  levies today; `rulePathF R x₀ n` is the state after `n` such periods.
* **§2. Feasibility.** A rule that keeps sanctions in `[0,1]` keeps the path in
  `[0,1]`.
* **§3. Order.** If the upper rule (or its closed loop) is monotone and
  dominates the lower rule, the lower path never overtakes the upper path —
  on `[0,1]`, or on a basin `[xbar, 1]` that both rules preserve.
* **§4. The affine copy.** `p.affineCopy` is the economy `p` with its
  transition replaced by the affine law `(1 − δ)·x + δ·s` at `δ := p.δ`.
  Every other primitive (payoffs, discount factors, the static selector) is
  `p`'s own. The hF-free affine paths of the tree (`ruleStep`/`rulePath`,
  `lockInStep`/`lockInPath`) are, by `rfl`, the general rule path of this copy,
  so the affine lemmas about them are one-line instances of §2–§3.

**Generality (Rule 22).** §1–§3 are general in `F`: they use only the
`Params` transition fields `F_mono_x`, `F_mono_s`, `F_diag` (and `F_mem`,
`F_mem_uIcc`, derived from them). §4 is affine-restricted by construction —
`affineCopy` reads `p.δ` and fixes `F := affineF p.δ` — and exists only to
express the affine kinematics as instances; it adds no hypothesis to any
theorem (no `hF : p.F = affineF p.δ` is introduced anywhere).

**Rule 3.** No new assumption: §4 discharges the four transition fields of the
copy from the existing lemmas `affineF_continuous`, `affineF_mono_x`,
`affineF_mono_s` (from `p.δ_mem`) and `affineF_diag`
(`Postulates/AbstractGame.lean`).
-/

import Sanctions.Postulates.AbstractGame

namespace Sanctions

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1–3. The general-`F` rule path, its feasibility, and path order

Moved from `DifferentPolicyComparator.lean` §11 (BH6.9); statements unchanged.
-/

/-- One general-`F` natural-dynamics step under an arbitrary realized
rule `R`: the next state is the abstract transition `F(x, R x)` rather
than the affine convex combination. Specialises to `ruleStep` at
`F := affineF δ`, and to `dynamicTopLockInStepF V_S α` at
`R := dynamicTopRealizedRule V_S α`. -/
def ruleStepF (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.F x (R x)

/-- General-`F` natural state path under a realized rule `R`, from `x₀`. -/
def rulePathF (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  (fun x => p.ruleStepF R x)^[n] x₀

/-- Sanction sequence along the general-`F` natural path under rule `R`. -/
def ruleSanctionsF (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  R (p.rulePathF R x₀ n)

@[simp] theorem rulePathF_zero (R : ℝ → ℝ) (x₀ : ℝ) :
    p.rulePathF R x₀ 0 = x₀ := rfl

@[simp] theorem rulePathF_succ (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.rulePathF R x₀ (n + 1) = p.ruleStepF R (p.rulePathF R x₀ n) :=
  Function.iterate_succ_apply' _ _ _

/-- If a rule preserves feasibility on `I`, so does its general-`F`
natural path (`F_mem`). General-`F` sibling of `rulePath_mem_I`. -/
theorem rulePathF_mem_I
    {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePathF R x₀ n ∈ Sanctions.I := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ k ih =>
    rw [rulePathF_succ]
    exact p.F_mem _ _ ih (hR_mem _ ih)

/-- **General-`F` path comparison from closed-loop monotonicity.**
Sibling of `rulePathF_le_of_rule_le_and_upper_mono` with the upper *rule*'s
monotonicity replaced by monotonicity of the upper *closed loop*
`x ↦ F(x, R₂ x)` on `[0,1]`. In plain terms: if the upper policy's
state-to-next-state map preserves order, the upper rule dominates the lower
one pointwise, and both rules are feasible, then the lower state path never
overtakes the upper one. The inductive step only ever compares
`F(y₁, R₁ y₁) ≤ F(y₁, R₂ y₁) ≤ F(y₂, R₂ y₂)`: the first inequality is
`F_mono_s` through the rule comparison, the second is exactly closed-loop
monotonicity, so the rule itself never has to be monotone. Dropped:
`MonotoneOn R₂ I`. A monotone rule gives a monotone closed loop
(`ruleStepF_monotoneOn_of_rule_monotoneOn`), and the converse fails
(`exists_closedLoopMono_without_monotone_rule`,
`Examples/CrossStepWithoutMonotoneRule.lean`), so this is a strict
weakening. General in `F` (BG1.8, 2026-10-06). -/
theorem rulePathF_le_of_rule_le_and_closedLoop_mono
    {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hstep₂_mono : MonotoneOn (p.ruleStepF R₂) Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ Sanctions.I, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
  intro n
  -- Strengthen IH with feasibility of both paths.
  have h_aux :
      ∀ n, p.rulePathF R₁ x₀ n ∈ Sanctions.I
          ∧ p.rulePathF R₂ x₀ n ∈ Sanctions.I
          ∧ p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using hx₀, by simpa using hx₀, le_rfl⟩
    | succ k ih =>
      obtain ⟨h_y1_mem, h_y2_mem, h_y_le⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · rw [rulePathF_succ]
        exact p.F_mem _ _ h_y1_mem (hR₁_mem _ h_y1_mem)
      · rw [rulePathF_succ]
        exact p.F_mem _ _ h_y2_mem (hR₂_mem _ h_y2_mem)
      · -- `F_mono_s` at the lower state, then the monotone upper closed loop.
        rw [rulePathF_succ, rulePathF_succ]
        calc p.ruleStepF R₁ (p.rulePathF R₁ x₀ k)
            = p.F (p.rulePathF R₁ x₀ k) (R₁ (p.rulePathF R₁ x₀ k)) := rfl
          _ ≤ p.F (p.rulePathF R₁ x₀ k) (R₂ (p.rulePathF R₁ x₀ k)) :=
              p.F_mono_s _ (hR₁_le_R₂ _ h_y1_mem)
          _ = p.ruleStepF R₂ (p.rulePathF R₁ x₀ k) := rfl
          _ ≤ p.ruleStepF R₂ (p.rulePathF R₂ x₀ k) :=
              hstep₂_mono h_y1_mem h_y2_mem h_y_le
  exact (h_aux n).2.2

/-- **Generic general-`F` path comparison.** If `R₂` is monotone on
`I`, pointwise dominates `R₁` on `I`, and both preserve feasibility,
then the general-`F` natural state path under `R₁` is dominated by the
general-`F` natural state path under `R₂` from any feasible start.
General-`F` sibling of `rulePath_le_of_rule_le_and_upper_mono`: the
inductive step chains `F_mono_s` (through the rule comparison
`R₁ y₁ ≤ R₂ y₁ ≤ R₂ y₂`) with `F_mono_x` (through the path comparison
`y₁ ≤ y₂`). Since BG1.8 (2026-10-06) it is a corollary of
`rulePathF_le_of_rule_le_and_closedLoop_mono`: the monotone rule is used only
to make the closed loop monotone. Statement unchanged. -/
theorem rulePathF_le_of_rule_le_and_upper_mono
    {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR₂_mem : ∀ x ∈ Sanctions.I, R₂ x ∈ Sanctions.I)
    (hR₂_mono : MonotoneOn R₂ Sanctions.I)
    (hR₁_le_R₂ : ∀ x ∈ Sanctions.I, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
  -- A monotone rule makes the closed loop monotone: `F_mono_s` through the
  -- rule, then `F_mono_x` in the state.
  exact p.rulePathF_le_of_rule_le_and_closedLoop_mono hR₁_mem hR₂_mem
    (fun x hx y hy hxy =>
      le_trans (p.F_mono_s x (hR₂_mono hx hy hxy)) (p.F_mono_x (R₂ y) hxy))
    hR₁_le_R₂ hx₀

/-- **Feasibility of the lower path**, extracted so the sanction comparison can
consume it without re-running the induction. -/
theorem rulePathF_mem_I_of_rule_mem
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (n : ℕ) :
    p.rulePathF R x₀ n ∈ Sanctions.I := by
  induction n with
  | zero => simpa using hx₀
  | succ j ih => rw [rulePathF_succ]; exact p.F_mem _ _ ih (hR_mem _ ih)

/-- **Localized general-`F` path comparison on a basin
`Set.Icc xbar 1`.** Same content as
`rulePath_le_of_rule_le_and_upper_monoOn_basin`, with the state
evolved by the abstract transition `p.F`. Every hypothesis is
restricted to the basin `[xbar, 1]`; both rules must map the basin
into itself (`hR₁_basin`, `hR₂_basin`). The affine ring identity
`xbar = (1 − δ)·xbar + δ·xbar` in the invariance step is replaced by
the diagonal anchor `F xbar xbar = xbar` (`F_diag`) chained through
`F_mono_x` / `F_mono_s`. General in `F`. The upper basin edge comes from
`F_mem_uIcc` (the next state lies between the state and the sanction, both
at most `1`), which holds on all of `ℝ`, so the statement holds for every
`xbar`: the hypothesis `0 ≤ xbar`, once read only to make basin states
feasible for `F_mem`, was dropped on 2026-10-06 (BG2.1). Since BH6.9
(2026-10-07) this file proves that edge inline, by the argument of
`F_le_one_of_le` (`DynamicTopLockIn.lean`), which sits above this file in
the import order; the statement is unchanged. -/
theorem rulePathF_le_of_rule_le_and_upper_monoOn_basin
    {R₁ R₂ : ℝ → ℝ} {xbar : ℝ}
    (hR₁_basin : ∀ x ∈ Set.Icc xbar 1, R₁ x ∈ Set.Icc xbar 1)
    (hR₂_basin : ∀ x ∈ Set.Icc xbar 1, R₂ x ∈ Set.Icc xbar 1)
    (hR₂_monoOn : MonotoneOn R₂ (Set.Icc xbar 1))
    (hR₁_le_R₂ : ∀ x ∈ Set.Icc xbar 1, R₁ x ≤ R₂ x)
    {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n,
      p.rulePathF R₁ x₀ n ∈ Set.Icc xbar 1
      ∧ p.rulePathF R₂ x₀ n ∈ Set.Icc xbar 1
      ∧ p.rulePathF R₁ x₀ n ≤ p.rulePathF R₂ x₀ n := by
  -- One-step basin invariance under any basin-preserving rule:
  -- lower bound by `xbar = F xbar xbar ≤ F y (R y)` (`F_diag` +
  -- `F_mono_x` + `F_mono_s`), upper bound from `F_mem_uIcc`: the next state
  -- lies between `y ≤ 1` and `R y ≤ 1`.
  have h_step_basin :
      ∀ (R : ℝ → ℝ), (∀ x ∈ Set.Icc xbar 1, R x ∈ Set.Icc xbar 1) →
        ∀ y ∈ Set.Icc xbar 1, p.ruleStepF R y ∈ Set.Icc xbar 1 := by
    intro R hR_basin y hy
    have hRy := hR_basin y hy
    refine ⟨?_, (Set.mem_uIcc.1 (p.F_mem_uIcc y (R y))).elim
      (fun h => h.2.trans hRy.2) (fun h => h.2.trans hy.2)⟩
    calc xbar = p.F xbar xbar := (p.F_diag xbar).symm
      _ ≤ p.F y xbar := p.F_mono_x xbar hy.1
      _ ≤ p.F y (R y) := p.F_mono_s y hRy.1
  intro n
  induction n with
  | zero =>
    exact ⟨by simpa using hx₀, by simpa using hx₀, le_rfl⟩
  | succ k ih =>
    obtain ⟨h_y1_mem, h_y2_mem, h_y_le⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- R₁ basin invariance at next step.
      rw [rulePathF_succ]
      exact h_step_basin R₁ hR₁_basin _ h_y1_mem
    · -- R₂ basin invariance at next step.
      rw [rulePathF_succ]
      exact h_step_basin R₂ hR₂_basin _ h_y2_mem
    · -- Path comparison at next step (same chain as the global version).
      rw [rulePathF_succ, rulePathF_succ]
      have h_rules : R₁ (p.rulePathF R₁ x₀ k) ≤ R₂ (p.rulePathF R₂ x₀ k) :=
        le_trans (hR₁_le_R₂ _ h_y1_mem)
          (hR₂_monoOn h_y1_mem h_y2_mem h_y_le)
      calc p.ruleStepF R₁ (p.rulePathF R₁ x₀ k)
          = p.F (p.rulePathF R₁ x₀ k) (R₁ (p.rulePathF R₁ x₀ k)) := rfl
        _ ≤ p.F (p.rulePathF R₁ x₀ k) (R₂ (p.rulePathF R₂ x₀ k)) :=
            p.F_mono_s _ h_rules
        _ ≤ p.F (p.rulePathF R₂ x₀ k) (R₂ (p.rulePathF R₂ x₀ k)) :=
            p.F_mono_x _ h_y_le
        _ = p.ruleStepF R₂ (p.rulePathF R₂ x₀ k) := rfl

/-! ## 4. The affine copy of an economy

`p.affineCopy` keeps every primitive of `p` except the transition, which it
replaces by the affine law at rate `p.δ`. It is the bridge that lets the
hF-free affine kinematics — paths that hard-code `(1 − δ)·x + δ·rule` but never
assume `p.F = affineF p.δ` — be proved as instances of the general-`F`
rule path above, with no statement change and no `hF` added. -/

/-- **The affine copy of an economy.** The economy `p` with its transition
replaced by the affine law `affineF p.δ`, i.e. `F(x, s) = (1 − δ)·x + δ·s` at
`δ := p.δ`; payoffs, discount factors, the static selector and `δ` itself are
`p`'s own. The four transition fields are discharged from the existing affine
lemmas (`affineF_continuous`, `affineF_mono_x` and `affineF_mono_s` from
`p.δ_mem`, `affineF_diag`), so no assumption is added.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22), by construction.** This is not a
claim that `p.F` is affine: `p.affineCopy.F` is `affineF p.δ` whatever `p.F`
is. Its only use is to restate the tree's hF-free affine path lemmas
(`rulePath_*` in `DifferentPolicyComparator.lean`, `lockInPath_mem_I_of_mem_I`
in `JointPreferenceBasin.lean`) as instances of the general-`F` lemmas of this
file. -/
def affineCopy : Params :=
  { p with
    F := affineF p.δ
    F_continuous := affineF_continuous p.δ
    F_mono_x := affineF_mono_x p.δ_mem
    F_mono_s := affineF_mono_s p.δ_mem
    F_diag := affineF_diag p.δ }

/-- The affine copy's transition is the affine law at `p.δ` (by `rfl`).
Affine-restricted by construction (see `affineCopy`). -/
@[simp] theorem affineCopy_F : p.affineCopy.F = affineF p.δ := rfl

/-- The affine copy keeps `p`'s rate parameter `δ` (by `rfl`).
Affine-restricted by construction (see `affineCopy`). -/
@[simp] theorem affineCopy_δ : p.affineCopy.δ = p.δ := rfl

/-- The affine copy keeps `p`'s static Sender selector `σ` (by `rfl`), so a
rule built from `p.σ` — such as `p.realizedRule α` — is the same rule in the
copy. General: no transition appears. -/
@[simp] theorem affineCopy_σ : p.affineCopy.σ = p.σ := rfl

end Params
end AbstractGame

end

end Sanctions
