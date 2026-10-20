/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.LockIn.SubintervalLockIn

/-!
# The escalation gap must vanish at the top of an invariant interval

`Theory/LockIn/SubintervalLockIn.lean` gives the *closed*-interval price of
sub-interval lock-in: if `[a,b]` is forward invariant and the realised rule
never falls below the state, the rule fixes `b` exactly
(`dynamicTopLockIn_subinterval_forces_fixed_endpoint`).  On the *half-open*
interval `[a,b)` — the interval the strict-escalation theorems
(`dynamicTopLockInPathF_strictMono_of_gt_self`,
`dynamicTopLockInSanctionsF_strictMono_of_gt_self`) actually run on — no
endpoint is available to be fixed, so that argument says nothing, and it is
natural to ask whether strict escalation is obstructed there too.

It is not.  What replaces the fixed endpoint is a strictly weaker, purely
kinematic requirement: **the per-period drift cannot be uniformly positive.**
A closed loop that gains at least `η > 0` of state every period leaves any
bounded interval in at most `⌈(b − x₀)/η⌉` periods, so invariance forces the
drift to become arbitrarily small somewhere on `[a,b)`.

That is a real restriction — it is exactly what fails at the B2 economy, whose
realised rule overshoots the diagonal by at least `1/4` on its
strictly-increasing stretch — but it is a *shape* condition on the rule, not an
impossibility.  A rule whose excess over the diagonal shrinks to zero at `b`
(e.g. `R x = (x + b)/2`) satisfies it, and `Examples/DeterministicStrictEscalation.lean`
exhibits a constructed deterministic equilibrium that does.

## Rule compliance

**Rule 3.** No new assumption: the theorems consume only `p.δ ∈ (0,1)` (already
a `Params` field) and the existing path constructions.  Nothing is added to any
structure.

**Rule 5.** Stated over an arbitrary `Params`, an arbitrary Sender continuation
value, an arbitrary Target policy, and an arbitrary interval; the witness
applications are corollaries elsewhere.

**Rule 19.** These mention `Params` and the project's own lock-in path
constructions, so they are model wiring and belong in `Theory/`, not
`Foundations/`.
-/

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Part 1 — general transition `F` -/

/-- **A uniformly positive per-period drift escapes any bounded interval.**
If every state of `[a,b)` gains at least `η > 0` in one closed-loop step, and
`[a,b)` is forward invariant, the two requirements are contradictory: the path
would satisfy `x_n ≥ x₀ + n·η` while staying below `b`. -/
theorem dynamicTopLockInPathF_escape_of_uniform_drift
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b η x₀ : ℝ}
    (hη : 0 < η)
    (hdrift : ∀ x ∈ Set.Ico a b, x + η ≤ p.dynamicTopLockInStepF V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hx₀ : x₀ ∈ Set.Ico a b) : False := by
  have hmem : ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Ico a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [dynamicTopLockInPathF_succ]; exact hinv _ ih
  have hlin : ∀ n : ℕ, x₀ + n * η ≤ p.dynamicTopLockInPathF V_S α x₀ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have h := hdrift _ (hmem k)
      have hexp : x₀ + (↑(k + 1) : ℝ) * η = (x₀ + (k : ℝ) * η) + η := by
        push_cast; ring
      rw [hexp, dynamicTopLockInPathF_succ]
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - x₀) / η)
  have hbig : b - x₀ < (n : ℝ) * η := by
    rw [div_lt_iff₀ hη] at hn; linarith
  linarith [hlin n, (hmem n).2]

/-- **The positive form.**  On a forward-invariant half-open interval the
closed-loop drift comes arbitrarily close to zero somewhere: for every `ε > 0`
there is a state of `[a,b)` whose one-step gain is smaller than `ε`. -/
theorem exists_small_drift_of_invariant
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b x₀ : ℝ}
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hx₀ : x₀ ∈ Set.Ico a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x < x + ε := by
  by_contra hcon
  refine p.dynamicTopLockInPathF_escape_of_uniform_drift V_S α hε
    (fun x hx => ?_) hinv hx₀
  by_contra hlt
  exact hcon ⟨x, hx, not_le.mp hlt⟩

/-! ## Axiom hygiene (Rule 10) -/

#print axioms dynamicTopLockInPathF_escape_of_uniform_drift
#print axioms exists_small_drift_of_invariant

end Params
end AbstractGame

end

end Sanctions
