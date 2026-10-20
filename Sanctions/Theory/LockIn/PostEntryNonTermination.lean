/-
Sanctions/Theory/LockIn/PostEntryNonTermination.lean

**Post-entry non-termination and the relief barrier.**

This file extracts duration and relief consequences already contained in
the upper-selector persistence machinery. It introduces no new game
primitive, parameter field, or structural assumption:

* every relief level is already feasible because `Sanctions.I = [0, 1]`;
* the existing basin level condition keeps the equilibrium sanction above
  the state inherited at basin entry;
* the existing Sender `IsMaxOn` theorem compares the realized sanction
  against every feasible relief action;
* the existing `DynamicArgmaxUnique` predicate upgrades top-selector
  statements to selector-independent and strict conclusions.

The falsification lemmas record why the two strict clauses are necessary:
allowing the cutoff to equal the floor permits termination at the floor,
and tied maximizers prevent strict preference over alternative relief.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Equilibrium.SelectionRobust

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Falsification boundary -/

/-- A floor alone does not rule out reaching a cutoff that is merely
weakly below the floor: the constant path at the floor is a counterexample.
The no-relief theorem therefore requires the strict inequality
`q < entryFloor`. -/
theorem weak_cutoff_no_relief_counterexample :
    ∃ (sanctions : ℕ → ℝ) (floor q : ℝ),
      (∀ n, floor ≤ sanctions n) ∧ q ≤ floor ∧ ∃ n, sanctions n ≤ q := by
  refine ⟨fun _ => 0, 0, 0, ?_, le_rfl, 0, le_rfl⟩
  intro n
  exact le_rfl

/-- Without argmax uniqueness, an optimal realized sanction need not
strictly dominate every distinct relief action: a constant objective has
distinct tied maximizers. -/
theorem strict_relief_without_uniqueness_counterexample :
    ∃ (f : ℝ → ℝ) (s r : ℝ),
      s ∈ Sanctions.I ∧ r ∈ Sanctions.I ∧ s ≠ r ∧
      IsMaxOn f Sanctions.I s ∧ IsMaxOn f Sanctions.I r ∧ ¬f r < f s := by
  refine ⟨fun _ : ℝ => (0 : ℝ), 1, 0, ?_, ?_, by norm_num, ?_, ?_, by simp⟩
  · exact ⟨by norm_num, by norm_num⟩
  · exact ⟨by norm_num, by norm_num⟩
  · simp [IsMaxOn, IsMaxFilter]
  · simp [IsMaxOn, IsMaxFilter]

/-! ## Tail identities -/

/-- Restarting the stationary upper-dynamic state path at date `T`
reproduces the original tail. -/
theorem dynamicTopLockInPath_add
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (x₀ : ℝ) (T n : ℕ) :
    p.dynamicTopLockInPath V_S α x₀ (T + n) =
      p.dynamicTopLockInPath V_S α
        (p.dynamicTopLockInPath V_S α x₀ T) n := by
  unfold dynamicTopLockInPath
  rw [Nat.add_comm T n, Function.iterate_add_apply]

/-- Restarting at date `T` also reproduces the original realized-sanction
tail. -/
theorem dynamicTopLockInSanctions_add
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (x₀ : ℝ) (T n : ℕ) :
    p.dynamicTopLockInSanctions V_S α x₀ (T + n) =
      p.dynamicTopLockInSanctions V_S α
        (p.dynamicTopLockInPath V_S α x₀ T) n := by
  unfold dynamicTopLockInSanctions
  rw [p.dynamicTopLockInPath_add V_S α x₀ T n]

/-- Restarting the general-`F` upper-dynamic state path at date `T`
reproduces the original tail. -/
theorem dynamicTopLockInPathF_add
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (x₀ : ℝ) (T n : ℕ) :
    p.dynamicTopLockInPathF V_S α x₀ (T + n) =
      p.dynamicTopLockInPathF V_S α
        (p.dynamicTopLockInPathF V_S α x₀ T) n := by
  unfold dynamicTopLockInPathF
  rw [Nat.add_comm T n, Function.iterate_add_apply]

/-- Restarting at date `T` also reproduces the original general-`F`
realized-sanction tail. -/
theorem dynamicTopLockInSanctionsF_add
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (x₀ : ℝ) (T n : ℕ) :
    p.dynamicTopLockInSanctionsF V_S α x₀ (T + n) =
      p.dynamicTopLockInSanctionsF V_S α
        (p.dynamicTopLockInPathF V_S α x₀ T) n := by
  unfold dynamicTopLockInSanctionsF
  rw [p.dynamicTopLockInPathF_add V_S α x₀ T n]

/-! ## The ratchet alone (BH2.1, 2026-10-06)

The general-`F` floor, no-relief and relief-times theorems below used to take
the full joint basin `JointPreferenceBasinTop` — eight fields, among them the
interval-dominance input (A1, `top_rule_mono`) and the Target's sanction
preference (P4, `target_prefers_sanctions`). Their proofs read only the ratchet
`x ≤ R x` on `[xbar, 1]` (through `dynamicTopLockInSanctionsF_ge_entry`); the
tail-monotonicity conjunct reads in addition that the rule is monotone on the
basin. The lemmas here state exactly that, and the joint-basin theorems become
one-line corollaries through `JointPreferenceBasinTop.ratchet_dyn_top`. They are
kinematic (the policy `α` is arbitrary); the equilibrium-anchored no-relief form
is `equilibriumTop_tailF_no_relief_of_ratchet` below. -/

/-- **Post-entry floor and tail monotonicity from the ratchet and a monotone
rule** (general in `F`; kinematic). Once the general-`F` path is in the basin at
date `T`, every later sanction is at least `max (x_T) xbar`, and, if the rule is
monotone on the basin, the sanction tail is non-decreasing. The floor uses only
the ratchet; the monotone conjunct uses the monotone rule. Dropped against
`jointPreferenceBasinTopF_tail_floor_and_mono`: every joint-basin field except
these two consequences (no `0 ≤ xbar`, no Target-policy optimality or
feasibility, no Target sanction preference). -/
theorem dynamicTopLockInSanctionsF_tail_floor_and_mono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar x₀ : ℝ} {T : ℕ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule V_S α x)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1))
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1) :
    (∀ n, max (p.dynamicTopLockInPathF V_S α x₀ T) xbar ≤
      p.dynamicTopLockInSanctionsF V_S α x₀ (T + n)) ∧
    Monotone (fun n => p.dynamicTopLockInSanctionsF V_S α x₀ (T + n)) := by
  constructor
  · intro n
    rw [p.dynamicTopLockInSanctionsF_add V_S α x₀ T n]
    exact p.dynamicTopLockInSanctionsF_ge_entry V_S α h_ratchet hT n
  · intro m n hmn
    change p.dynamicTopLockInSanctionsF V_S α x₀ (T + m) ≤
      p.dynamicTopLockInSanctionsF V_S α x₀ (T + n)
    rw [p.dynamicTopLockInSanctionsF_add V_S α x₀ T m,
      p.dynamicTopLockInSanctionsF_add V_S α x₀ T n]
    exact p.dynamicTopLockInSanctionsF_mono V_S α
      (p.dynamicTopRealizedRule_level_of_ratchet V_S α h_ratchet) h_mono hT hmn

/-- **Post-entry non-termination from the ratchet alone** (general in `F`;
kinematic). After the general-`F` path enters the basin at date `T`, no relief
cutoff strictly below `max (x_T) xbar` is ever reached. Dropped against
`jointPreferenceBasinTopF_tail_no_relief`: the whole joint basin except the
ratchet, including `0 ≤ xbar`, A1 and P4. -/
theorem dynamicTopLockInSanctionsF_tail_no_relief
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar x₀ q : ℝ} {T : ℕ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule V_S α x)
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPathF V_S α x₀ T) xbar) :
    ∀ n, ¬p.dynamicTopLockInSanctionsF V_S α x₀ (T + n) ≤ q := by
  intro n hrelief
  rw [p.dynamicTopLockInSanctionsF_add V_S α x₀ T n] at hrelief
  exact (not_le_of_gt hq)
    (le_trans (p.dynamicTopLockInSanctionsF_ge_entry V_S α h_ratchet hT n) hrelief)

/-- First-passage-set form of `dynamicTopLockInSanctionsF_tail_no_relief`
(general in `F`; kinematic): the set of post-entry dates at which the sanction
is at or below a strict cutoff is empty. Ratchet only. -/
theorem dynamicTopLockInSanctionsF_tail_relief_times_eq_empty
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar x₀ q : ℝ} {T : ℕ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule V_S α x)
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPathF V_S α x₀ T) xbar) :
    {n : ℕ | p.dynamicTopLockInSanctionsF V_S α x₀ (T + n) ≤ q} = ∅ := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact p.dynamicTopLockInSanctionsF_tail_no_relief V_S α h_ratchet hT hq n

/-- **Equilibrium-anchored post-entry non-termination from the ratchet**
(general in `F`; the manuscript-facing form of BH2.1). Along the general-`F`
path of an actual top-selector equilibrium `E`, once the state is in a basin
`[xbar, 1]` on which the equilibrium rule is weakly above the state, no relief
cutoff strictly below the inherited level `max (x_T) xbar` is ever reached.

The trajectory is the equilibrium path: the policy is `E.α` and the sanction
rule is the Sender's greatest forward-looking best response against
`E.V_S` (Rule 1). Against `jointPreferenceBasinTopF_tail_no_relief` at `E`, the
joint basin is replaced by the ratchet; in particular neither interval
dominance (A1) nor the Target's sanction preference (P4) is used. The ratchet
follows from the level condition, which the pivot-star inputs deliver
(`level_dyn_top_of_local_star`, `SenderPersistencePackage.lean`). -/
theorem equilibriumTop_tailF_no_relief_of_ratchet
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar x₀ q : ℝ} {T : ℕ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hT : p.dynamicTopLockInPathF E.V_S E.α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPathF E.V_S E.α x₀ T) xbar) :
    ∀ n, ¬p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n) ≤ q :=
  p.dynamicTopLockInSanctionsF_tail_no_relief E.V_S E.α h_ratchet hT hq

/-! ## Post-entry floor, monotonicity, and non-termination -/

/-- From a basin start, sanctions stay above the state inherited at
entry. Since `x₀ ∈ [xbar, 1]`, this is equivalently the paper's floor
`max x₀ xbar`. -/
theorem jointPreferenceBasinTop_sanctions_ge_entry
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, max x₀ xbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  have hpath_mono := p.dynamicTopLockInPath_mono V_S α hlevel hx₀
  intro n
  rw [max_eq_left hx₀.1]
  have hx₀_le_path :
      x₀ ≤ p.dynamicTopLockInPath V_S α x₀ n := by
    simpa using hpath_mono (Nat.zero_le n)
  unfold dynamicTopLockInSanctions
  exact le_trans hx₀_le_path <|
    le_trans (le_max_left _ sbar) <|
      hlevel _ (p.dynamicTopLockInPath_mem_basin V_S α hlevel hx₀ n)

/-- General-`F` sibling of
`jointPreferenceBasinTop_sanctions_ge_entry`. Since BH2.1 (2026-10-06) a
one-line corollary of `dynamicTopLockInSanctionsF_ge_entry`: of the joint basin
only the ratchet is read. Statement unchanged. -/
theorem jointPreferenceBasinTopF_sanctions_ge_entry
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, max x₀ xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n :=
  p.dynamicTopLockInSanctionsF_ge_entry V_S α
    (JointPreferenceBasinTop.ratchet_dyn_top p hB) hx₀

/-- Once the original path enters the high basin at date `T`, its entire
tail stays above the inherited entry state and is non-decreasing. -/
theorem jointPreferenceBasinTop_tail_floor_and_mono
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ} {T : ℕ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPath V_S α x₀ T ∈ Set.Icc xbar 1) :
    (∀ n, max (p.dynamicTopLockInPath V_S α x₀ T) xbar ≤
      p.dynamicTopLockInSanctions V_S α x₀ (T + n)) ∧
    Monotone (fun n => p.dynamicTopLockInSanctions V_S α x₀ (T + n)) := by
  have hbase := p.jointPreferenceBasinTop_long_run_nonDecreasing hB hT
  constructor
  · intro n
    rw [p.dynamicTopLockInSanctions_add V_S α x₀ T n]
    exact p.jointPreferenceBasinTop_sanctions_ge_entry hB hT n
  · intro m n hmn
    change p.dynamicTopLockInSanctions V_S α x₀ (T + m) ≤
      p.dynamicTopLockInSanctions V_S α x₀ (T + n)
    rw [p.dynamicTopLockInSanctions_add V_S α x₀ T m]
    rw [p.dynamicTopLockInSanctions_add V_S α x₀ T n]
    exact hbase.2.2.2 hmn

/-- General-`F` post-entry tail floor and sanction monotonicity. Since BH2.1
(2026-10-06) a one-line corollary of
`dynamicTopLockInSanctionsF_tail_floor_and_mono`: of the joint basin only the
ratchet and `top_rule_mono` are read. Statement unchanged. -/
theorem jointPreferenceBasinTopF_tail_floor_and_mono
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ} {T : ℕ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1) :
    (∀ n, max (p.dynamicTopLockInPathF V_S α x₀ T) xbar ≤
      p.dynamicTopLockInSanctionsF V_S α x₀ (T + n)) ∧
    Monotone (fun n => p.dynamicTopLockInSanctionsF V_S α x₀ (T + n)) :=
  p.dynamicTopLockInSanctionsF_tail_floor_and_mono V_S α
    (JointPreferenceBasinTop.ratchet_dyn_top p hB) hB.top_rule_mono hT

/-- **Post-entry non-termination.** After basin entry at date `T`, no
strictly lower relief cutoff is ever reached by the upper-selector
equilibrium path. This is the direct quantifier form of an infinite
first-passage time. -/
theorem jointPreferenceBasinTop_tail_no_relief
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ q : ℝ} {T : ℕ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPath V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPath V_S α x₀ T) xbar) :
    ∀ n, ¬p.dynamicTopLockInSanctions V_S α x₀ (T + n) ≤ q := by
  have hfloor := (p.jointPreferenceBasinTop_tail_floor_and_mono hB hT).1
  intro n hrelief
  exact (not_le_of_gt hq) (le_trans (hfloor n) hrelief)

/-- **General-`F` post-entry non-termination.** After basin entry at
date `T`, no strictly lower relief cutoff is ever reached by the
upper-selector equilibrium path evolved by `p.F`. Since BH2.1 (2026-10-06) a
one-line corollary of `dynamicTopLockInSanctionsF_tail_no_relief`: of the joint
basin only the ratchet is read (no A1, no P4). Statement unchanged. -/
theorem jointPreferenceBasinTopF_tail_no_relief
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ q : ℝ} {T : ℕ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPathF V_S α x₀ T) xbar) :
    ∀ n, ¬p.dynamicTopLockInSanctionsF V_S α x₀ (T + n) ≤ q :=
  p.dynamicTopLockInSanctionsF_tail_no_relief V_S α
    (JointPreferenceBasinTop.ratchet_dyn_top p hB) hT hq

/-- The set of post-entry dates at which the equilibrium sanction is at
or below a strict relief cutoff is empty. -/
theorem jointPreferenceBasinTop_tail_relief_times_eq_empty
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ q : ℝ} {T : ℕ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPath V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPath V_S α x₀ T) xbar) :
    {n : ℕ | p.dynamicTopLockInSanctions V_S α x₀ (T + n) ≤ q} = ∅ := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact p.jointPreferenceBasinTop_tail_no_relief hB hT hq n

/-- General-`F` first-passage-set form of post-entry non-termination. Since
BH2.1 (2026-10-06) a one-line corollary of
`dynamicTopLockInSanctionsF_tail_relief_times_eq_empty` (ratchet only).
Statement unchanged. -/
theorem jointPreferenceBasinTopF_tail_relief_times_eq_empty
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ q : ℝ} {T : ℕ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hT : p.dynamicTopLockInPathF V_S α x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.dynamicTopLockInPathF V_S α x₀ T) xbar) :
    {n : ℕ | p.dynamicTopLockInSanctionsF V_S α x₀ (T + n) ≤ q} = ∅ :=
  p.dynamicTopLockInSanctionsF_tail_relief_times_eq_empty V_S α
    (JointPreferenceBasinTop.ratchet_dyn_top p hB) hT hq

/-! ## Optimality against feasible relief -/

/-- Along every tail of a top-selector equilibrium path, the realized
sanction weakly dominates every feasible relief action in the Sender's
dynamic objective. This is an optimality comparison, not a fixed-policy
assumption. -/
theorem equilibriumTop_tail_sender_optimal_against_relief
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (x₀ : ℝ) (T n : ℕ) {r : ℝ} (hr : r ∈ Sanctions.I) :
    p.senderDynObjective E.V_S
        (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))) r ≤
      p.senderDynObjective E.V_S
        (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n)))
        (p.dynamicTopLockInSanctions E.V_S E.α x₀ (T + n)) := by
  simpa [dynamicTopLockInSanctions, dynamicTopRealizedRule, senderDynObjective] using
    E.ρ_isMaxOn
      (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
      (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))) hr

/-- General-`F` optimality comparison against every feasible relief
action along an equilibrium tail. -/
theorem equilibriumTop_tailF_sender_optimal_against_relief
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (x₀ : ℝ) (T n : ℕ) {r : ℝ} (hr : r ∈ Sanctions.I) :
    p.senderDynObjective E.V_S
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))) r ≤
      p.senderDynObjective E.V_S
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)))
        (p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)) := by
  simpa [dynamicTopLockInSanctionsF, dynamicTopRealizedRule,
      senderDynObjective] using
    E.ρ_isMaxOn
      (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
      (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))) hr

/-- Under the existing state-local dynamic-argmax uniqueness condition,
every feasible relief action distinct from the realized sanction is
strictly worse for the Sender along the post-entry tail. -/
theorem equilibriumTop_jointPreferenceBasinTop_tail_relief_strictly_worse_of_unique
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar sbar x₀ : ℝ} {T n : ℕ}
    (hB : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar sbar)
    (hT : p.dynamicTopLockInPath E.V_S E.α x₀ T ∈ Set.Icc xbar 1)
    (h_unique : p.DynamicArgmaxUnique E.V_S)
    {r : ℝ} (hr : r ∈ Sanctions.I)
    (hr_ne : r ≠ p.dynamicTopLockInSanctions E.V_S E.α x₀ (T + n)) :
    p.senderDynObjective E.V_S
        (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))) r <
      p.senderDynObjective E.V_S
        (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n)))
        (p.dynamicTopLockInSanctions E.V_S E.α x₀ (T + n)) := by
  let x := p.dynamicTopLockInPath E.V_S E.α x₀ (T + n)
  let s := p.dynamicTopLockInSanctions E.V_S E.α x₀ (T + n)
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  have hx_basin : x ∈ Set.Icc xbar 1 := by
    dsimp [x]
    rw [p.dynamicTopLockInPath_add E.V_S E.α x₀ T n]
    exact p.dynamicTopLockInPath_mem_basin E.V_S E.α hlevel hT n
  have hx_phys : x ∈ Sanctions.S :=
    ⟨le_trans hB.xbar_nonneg hx_basin.1, hx_basin.2⟩
  have hs_mem : s ∈ Sanctions.I := by
    dsimp [s]
    exact p.dynamicTopLockInSanctions_mem E.V_S E.α x₀ (T + n)
  have hs_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S x (E.α x) z)
        Sanctions.I s := by
    dsimp [x, s]
    simpa [dynamicTopLockInSanctions, dynamicTopRealizedRule, senderDynObjective] using
      E.ρ_isMaxOn
        (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n)))
  have hle :
      p.senderDynObjective E.V_S x (E.α x) r ≤
        p.senderDynObjective E.V_S x (E.α x) s :=
    hs_max hr
  have hne_value :
      p.senderDynObjective E.V_S x (E.α x) r ≠
        p.senderDynObjective E.V_S x (E.α x) s := by
    intro heq
    have hr_max :
        IsMaxOn
          (fun z => p.senderDynObjective E.V_S x (E.α x) z)
          Sanctions.I r := by
      intro z hz
      exact le_trans (hs_max hz) heq.symm.le
    have hrs :
        r = s := by
      exact h_unique x hx_phys (E.α x) r s hr hs_mem hr_max hs_max
    exact hr_ne hrs
  exact lt_of_le_of_ne hle hne_value

/-- With dynamic-argmax uniqueness, every Sender maximizer on a
post-entry tail equals the realized sanction and therefore lies above
the inherited relief barrier. This is the selector-independent version
of post-entry non-termination. -/
theorem equilibriumTop_jointPreferenceBasinTop_tail_every_maximizer_above_entry_of_unique
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar sbar x₀ : ℝ} {T n : ℕ}
    (hB : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar sbar)
    (hT : p.dynamicTopLockInPath E.V_S E.α x₀ T ∈ Set.Icc xbar 1)
    (h_unique : p.DynamicArgmaxUnique E.V_S)
    {r : ℝ} (hr : r ∈ Sanctions.I)
    (hr_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S
          (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
          (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))) z)
        Sanctions.I r) :
    max (p.dynamicTopLockInPath E.V_S E.α x₀ T) xbar ≤ r := by
  let x := p.dynamicTopLockInPath E.V_S E.α x₀ (T + n)
  let s := p.dynamicTopLockInSanctions E.V_S E.α x₀ (T + n)
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  have hx_basin : x ∈ Set.Icc xbar 1 := by
    dsimp [x]
    rw [p.dynamicTopLockInPath_add E.V_S E.α x₀ T n]
    exact p.dynamicTopLockInPath_mem_basin E.V_S E.α hlevel hT n
  have hx_phys : x ∈ Sanctions.S :=
    ⟨le_trans hB.xbar_nonneg hx_basin.1, hx_basin.2⟩
  have hs_mem : s ∈ Sanctions.I := by
    dsimp [s]
    exact p.dynamicTopLockInSanctions_mem E.V_S E.α x₀ (T + n)
  have hs_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S x (E.α x) z)
        Sanctions.I s := by
    dsimp [x, s]
    simpa [dynamicTopLockInSanctions, dynamicTopRealizedRule, senderDynObjective] using
      E.ρ_isMaxOn
        (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ (T + n)))
  have hrs : r = s := by
    apply h_unique x hx_phys (E.α x) r s hr hs_mem
    · simpa [x] using hr_max
    · exact hs_max
  rw [hrs]
  dsimp [s]
  exact (p.jointPreferenceBasinTop_tail_floor_and_mono hB hT).1 n

/-- **Strict relief comparison along a feasible general-`F` equilibrium tail**
(general in `F`; BH2.1, 2026-10-06). Under the state-local dynamic-argmax
uniqueness condition, at every date after `T` every feasible relief action
distinct from the realised sanction is strictly worse for the Sender, provided
only that the date-`T` state is feasible.

Dropped against
`equilibriumTop_jointPreferenceBasinTopF_tail_relief_strictly_worse_of_unique`:
the joint basin and basin entry. They served only to put the date-`T + n` state
in `[0, 1]`, where uniqueness applies, and the general-`F` path from a feasible
state stays feasible (`F_mem`); so no `xbar`, no ratchet, no A1 and no P4. -/
theorem equilibriumTop_tailF_relief_strictly_worse_of_unique
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} {T n : ℕ}
    (hxT : p.dynamicTopLockInPathF E.V_S E.α x₀ T ∈ Sanctions.I)
    (h_unique : p.DynamicArgmaxUnique E.V_S)
    {r : ℝ} (hr : r ∈ Sanctions.I)
    (hr_ne : r ≠
      p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)) :
    p.senderDynObjective E.V_S
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))) r <
      p.senderDynObjective E.V_S
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)))
        (p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)) := by
  let x := p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)
  let s := p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)
  -- The restarted path from a feasible state stays feasible (`F_mem`).
  have hI : ∀ m, p.dynamicTopLockInPathF E.V_S E.α
      (p.dynamicTopLockInPathF E.V_S E.α x₀ T) m ∈ Sanctions.I := by
    intro m
    induction m with
    | zero => simpa using hxT
    | succ m ih =>
      rw [dynamicTopLockInPathF_succ]
      exact p.dynamicTopLockInStepF_mem_I_of_mem_I E.V_S E.α ih
  have hx_phys : x ∈ Sanctions.S := by
    dsimp [x]
    rw [p.dynamicTopLockInPathF_add E.V_S E.α x₀ T n]
    exact hI n
  have hs_mem : s ∈ Sanctions.I := by
    dsimp [s]
    unfold dynamicTopLockInSanctionsF
    exact p.dynamicTopRealizedRule_mem E.V_S E.α _
  have hs_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S x (E.α x) z)
        Sanctions.I s := by
    dsimp [x, s]
    simpa [dynamicTopLockInSanctionsF, dynamicTopRealizedRule,
      senderDynObjective] using
      E.ρ_isMaxOn
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)))
  have hle :
      p.senderDynObjective E.V_S x (E.α x) r ≤
        p.senderDynObjective E.V_S x (E.α x) s :=
    hs_max hr
  have hne_value :
      p.senderDynObjective E.V_S x (E.α x) r ≠
        p.senderDynObjective E.V_S x (E.α x) s := by
    intro heq
    have hr_max :
        IsMaxOn
          (fun z => p.senderDynObjective E.V_S x (E.α x) z)
          Sanctions.I r := by
      intro z hz
      exact le_trans (hs_max hz) heq.symm.le
    have hrs : r = s :=
      h_unique x hx_phys (E.α x) r s hr hs_mem hr_max hs_max
    exact hr_ne hrs
  exact lt_of_le_of_ne hle hne_value

/-- **Selector-independent relief barrier from the ratchet** (general in `F`;
BH2.1, 2026-10-06). Under state-local dynamic-argmax uniqueness, once the
general-`F` equilibrium path is in a basin `[xbar, 1]` with `0 ≤ xbar` on which
the equilibrium rule is weakly above the state, every Sender maximiser at every
later date lies at or above the inherited level `max (x_T) xbar`.

Dropped against
`equilibriumTop_jointPreferenceBasinTopF_tail_every_maximizer_above_entry_of_unique`:
the joint basin, except `0 ≤ xbar` (which puts the tail states in `[0, 1]`,
where uniqueness applies) and the ratchet (which gives the entry floor). No
sanction floor `sbar`, no A1, no Target-policy fields and no P4. -/
theorem equilibriumTop_tailF_every_maximizer_above_entry_of_ratchet
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar x₀ : ℝ} {T n : ℕ}
    (hxbar0 : 0 ≤ xbar)
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hT : p.dynamicTopLockInPathF E.V_S E.α x₀ T ∈ Set.Icc xbar 1)
    (h_unique : p.DynamicArgmaxUnique E.V_S)
    {r : ℝ} (hr : r ∈ Sanctions.I)
    (hr_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S
          (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
          (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))) z)
        Sanctions.I r) :
    max (p.dynamicTopLockInPathF E.V_S E.α x₀ T) xbar ≤ r := by
  let x := p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)
  let s := p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)
  have hlevel := p.dynamicTopRealizedRule_level_of_ratchet E.V_S E.α h_ratchet
  have hx_basin : x ∈ Set.Icc xbar 1 := by
    dsimp [x]
    rw [p.dynamicTopLockInPathF_add E.V_S E.α x₀ T n]
    exact p.dynamicTopLockInPathF_mem_basin E.V_S E.α hlevel hT n
  have hx_phys : x ∈ Sanctions.S :=
    ⟨le_trans hxbar0 hx_basin.1, hx_basin.2⟩
  have hs_mem : s ∈ Sanctions.I := by
    dsimp [s]
    unfold dynamicTopLockInSanctionsF
    exact p.dynamicTopRealizedRule_mem E.V_S E.α _
  have hs_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S x (E.α x) z)
        Sanctions.I s := by
    dsimp [x, s]
    simpa [dynamicTopLockInSanctionsF, dynamicTopRealizedRule,
      senderDynObjective] using
      E.ρ_isMaxOn
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)))
  have hrs : r = s := by
    apply h_unique x hx_phys (E.α x) r s hr hs_mem
    · simpa [x] using hr_max
    · exact hs_max
  rw [hrs]
  dsimp [s]
  rw [p.dynamicTopLockInSanctionsF_add E.V_S E.α x₀ T n]
  exact p.dynamicTopLockInSanctionsF_ge_entry E.V_S E.α h_ratchet hT n

/-- General-`F` sibling of the strict relief comparison under
state-local dynamic-argmax uniqueness. Since BH2.1 (2026-10-06) a one-line
corollary of `equilibriumTop_tailF_relief_strictly_worse_of_unique`: the basin
is read only through `0 ≤ xbar`, to make the date-`T` state feasible.
Statement unchanged. -/
theorem equilibriumTop_jointPreferenceBasinTopF_tail_relief_strictly_worse_of_unique
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar sbar x₀ : ℝ} {T n : ℕ}
    (hB : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar sbar)
    (hT : p.dynamicTopLockInPathF E.V_S E.α x₀ T ∈ Set.Icc xbar 1)
    (h_unique : p.DynamicArgmaxUnique E.V_S)
    {r : ℝ} (hr : r ∈ Sanctions.I)
    (hr_ne : r ≠
      p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)) :
    p.senderDynObjective E.V_S
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))) r <
      p.senderDynObjective E.V_S
        (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n)))
        (p.dynamicTopLockInSanctionsF E.V_S E.α x₀ (T + n)) :=
  equilibriumTop_tailF_relief_strictly_worse_of_unique E
    ⟨le_trans hB.xbar_nonneg hT.1, hT.2⟩ h_unique hr hr_ne

/-- General-`F` selector-independent relief barrier under state-local
dynamic-argmax uniqueness. Since BH2.1 (2026-10-06) a one-line corollary of
`equilibriumTop_tailF_every_maximizer_above_entry_of_ratchet`: the basin is read
only through `0 ≤ xbar` and the ratchet. Statement unchanged. -/
theorem equilibriumTop_jointPreferenceBasinTopF_tail_every_maximizer_above_entry_of_unique
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar sbar x₀ : ℝ} {T n : ℕ}
    (hB : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar sbar)
    (hT : p.dynamicTopLockInPathF E.V_S E.α x₀ T ∈ Set.Icc xbar 1)
    (h_unique : p.DynamicArgmaxUnique E.V_S)
    {r : ℝ} (hr : r ∈ Sanctions.I)
    (hr_max :
      IsMaxOn
        (fun z => p.senderDynObjective E.V_S
          (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))
          (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ (T + n))) z)
        Sanctions.I r) :
    max (p.dynamicTopLockInPathF E.V_S E.α x₀ T) xbar ≤ r :=
  equilibriumTop_tailF_every_maximizer_above_entry_of_ratchet E hB.xbar_nonneg
    (JointPreferenceBasinTop.ratchet_dyn_top p hB) hT h_unique hr hr_max

#print axioms jointPreferenceBasinTop_tail_no_relief
#print axioms jointPreferenceBasinTop_tail_relief_times_eq_empty
#print axioms equilibriumTop_tail_sender_optimal_against_relief
#print axioms equilibriumTop_jointPreferenceBasinTop_tail_relief_strictly_worse_of_unique
#print axioms
  equilibriumTop_jointPreferenceBasinTop_tail_every_maximizer_above_entry_of_unique
#print axioms jointPreferenceBasinTopF_tail_no_relief
#print axioms jointPreferenceBasinTopF_tail_relief_times_eq_empty
#print axioms equilibriumTop_tailF_sender_optimal_against_relief
#print axioms
  equilibriumTop_jointPreferenceBasinTopF_tail_relief_strictly_worse_of_unique
#print axioms
  equilibriumTop_jointPreferenceBasinTopF_tail_every_maximizer_above_entry_of_unique
#print axioms dynamicTopLockInSanctionsF_tail_no_relief
#print axioms dynamicTopLockInSanctionsF_tail_floor_and_mono
#print axioms equilibriumTop_tailF_no_relief_of_ratchet
#print axioms equilibriumTop_tailF_relief_strictly_worse_of_unique
#print axioms equilibriumTop_tailF_every_maximizer_above_entry_of_ratchet

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
