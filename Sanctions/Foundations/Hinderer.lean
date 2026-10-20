/-
Sanctions/Foundations/Hinderer.lean

**Hinderer 2005 Theorem 4.2(c) — closed-form Lipschitz bound for value
functions in Markovian decision processes.**

Hinderer 2005 (Mathematical Methods of Operations Research 62(1):3-22,
`PaperRefer/MathTheory/LipschitzValueFunctionsMDP-Hinderer-2005.md`)
proves a closed-form Lipschitz constant for the value function of a
discounted MDP under the recursion bound

  `l(V_{n+1}) ≤ α + γ · l(V_n)`

where `l(·)` is the state-space Lipschitz seminorm and `γ < 1` is the
discount-weighted transition-Lipschitz constant. Theorem 4.2(c) shows
that when `γ < 1`, the limit value function `V := lim V_n` exists and
satisfies the explicit bound

  `l(V) ≤ α / (1 - γ)`.

This module supplies the generic real-analysis lemmas underlying the
Hinderer bound, in two forms convenient for the project's
`bellmanLipConstant` framework:

* **`hinderer_lipschitz_invariance`** — Lipschitz cone preservation:
  if the initial Lipschitz constant `L 0 ≤ α/(1-γ)`, then the
  iterated bound `L n ≤ α/(1-γ)` is preserved at every iterate. This
  is the cone-membership preservation theorem the project's
  `valLipBall K` carrier consumes implicitly.

* **`hinderer_lipschitz_geometric_convergence`** — the explicit
  geometric-rate bound

  `L n ≤ K + γ^n · (L 0 - K)`

  where `K := α/(1-γ)` is the fixed-point Lipschitz constant. This is
  the discrete-time analogue of Hinderer's Theorem 4.2(c) limit
  argument, exposing the geometric convergence rate.

* **`hinderer_specialises_to_bellmanLipConstant`** — identity showing
  that the Hinderer closed form `α/(1-γ)` matches the project's
  `bellmanLipConstant β γ α := α/(1-β·γ)` from
  `Foundations/StokeyLucas.lean` when one identifies the
  Hinderer `γ` with `β·γ_project` (i.e. when the project's `γ`
  parameter measures the un-discounted transition Lipschitz and the
  Hinderer `γ` measures the discounted version).

## Literature anchors

* Karl Hinderer, *Lipschitz Continuity of Value Functions in Markovian
  Decision Processes*, Mathematical Methods of Operations Research
  62(1):3–22 (2005). Theorem 4.2 is the closed-form Lipschitz bound whose
  rate is the transition's state modulus taken uniformly over actions, which
  is the project's constant; the present module formalises its inductive part
  4.2(c). (Through round AH the module cited Theorem 4.1(c), whose rate uses
  the transition's joint modulus; re-anchored round AI, 2026-09-22, after the
  held text was read.)
* **Scope caveat (state direction only).** The Hinderer bound
  regularises the value function in the **state** direction: a Lipschitz
  stage payoff plus a Lipschitz transition give a value function
  Lipschitz in `x`. It does **not** supply Lipschitz continuity in the
  leader's own **action** direction — a uniform-Lipschitz-in-action
  integrand need not be jointly Lipschitz once the follower response
  `σ(x, a)` re-enters the leader objective through `a`. This is the
  literature anchor for why the interior shocked-existence development
  (`Theory/Shocked/ShockedLeaderLipschitz.lean`) **consumes** the
  Stackelberg-coupling action-Lipschitz estimate `h_obj_diff` as an
  honest open input rather than deriving it from the smear kernel: the
  kernel regularises state, not action.
* Stokey-Lucas-Prescott 1989, Theorem 4.6 with Corollary 1 to Theorem 3.2 —
  the carrier-inheritance route the closed form `K = L_U/(1-β·γ)` feeds; the
  formula itself is Hinderer's, generalised to additive-separable MDPs with
  state-dependent feasibility.
* Bertsekas-Tsitsiklis 1996 *Neuro-Dynamic Programming* Ch. 2 — the
  weighted-max-norm pseudo-contraction theorem the present module
  also instantiates.

## Rule compliance

**Rule 1** ✓ — no strategies; pure real-analysis content.
**Rule 3** ✓ — no new `Params` fields; theorem-parameter inputs only
(a sequence `L : ℕ → ℝ` of non-negative reals satisfying the
recursion, plus the discount + cross-Lipschitz scalars).
**Rule 5** ✓ — fully parametric over `(α, γ, L)`.
**Rule 8** ✓ — module header explains every introduced object in
plain English.
**Rule 10** ✓ — verified axiom-clean post-build.
**Rule 19** ✓ — generic real-analysis content with no project-specific
economic dependencies; lives in `Foundations/`.
-/

import Sanctions.Foundations.StokeyLucas

namespace Sanctions
namespace Foundations
namespace Hinderer

/-- **Hinderer 2005 Theorem 4.2(c) — Lipschitz cone preservation.**
Under the recursion `L (n+1) ≤ α + γ · L n` with `0 ≤ γ < 1`,
`0 ≤ α`, and initial condition `L 0 ≤ α/(1-γ)`, the bound
`L n ≤ α/(1-γ)` is preserved at every iterate.

In project terms: this is the cone-membership preservation theorem
the `valLipBall K` carrier consumes implicitly. If the Bellman
operator generates a sequence of value-function iterates with
Lipschitz constants satisfying the recursion, and the initial
iterate starts inside the Lipschitz ball of radius `α/(1-γ)`, then
every iterate stays inside the ball. -/
theorem hinderer_lipschitz_invariance
    {α γ : ℝ} (_hα_nn : 0 ≤ α) (hγ_nn : 0 ≤ γ) (hγ_lt : γ < 1)
    (L : ℕ → ℝ) (h_recursion : ∀ n, L (n + 1) ≤ α + γ * L n)
    (h_init : L 0 ≤ α / (1 - γ)) :
    ∀ n, L n ≤ α / (1 - γ) := by
  have hK_pos : 0 < 1 - γ := by linarith
  intro n
  induction n with
  | zero => exact h_init
  | succ k ih =>
    have h_step : L (k + 1) ≤ α + γ * L k := h_recursion k
    have h_bound : α + γ * L k ≤ α / (1 - γ) := by
      have : γ * L k ≤ γ * (α / (1 - γ)) :=
        mul_le_mul_of_nonneg_left ih hγ_nn
      have h_alg : α + γ * (α / (1 - γ)) = α / (1 - γ) := by
        have h_ne : (1 - γ) ≠ 0 := ne_of_gt hK_pos
        field_simp
        ring
      linarith
    linarith

/-- **Hinderer 2005 Theorem 4.2(c) — geometric-rate convergence
bound.** Under the recursion `L (n+1) ≤ α + γ · L n` with
`0 ≤ γ < 1`, `0 ≤ α`, the explicit bound

  `L n ≤ α/(1-γ) + γ^n · (L 0 - α/(1-γ))`

holds for every `n`. When `L 0 ≤ α/(1-γ)` the bound collapses to
`L n ≤ α/(1-γ)` (cone preservation); when `L 0 > α/(1-γ)` the bound
shows geometric convergence to the fixed point at rate `γ^n`. -/
theorem hinderer_lipschitz_geometric_convergence
    {α γ : ℝ} (_hα_nn : 0 ≤ α) (hγ_nn : 0 ≤ γ) (hγ_lt : γ < 1)
    (L : ℕ → ℝ) (h_recursion : ∀ n, L (n + 1) ≤ α + γ * L n) :
    ∀ n, L n ≤ α / (1 - γ) + γ ^ n * (L 0 - α / (1 - γ)) := by
  have hK_pos : 0 < 1 - γ := by linarith
  intro n
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h_step : L (k + 1) ≤ α + γ * L k := h_recursion k
    have h_ne : (1 - γ) ≠ 0 := ne_of_gt hK_pos
    have h_alg : α + γ * (α / (1 - γ)) = α / (1 - γ) := by
      field_simp; ring
    have h_mul : γ * L k ≤ γ * (α / (1 - γ) + γ ^ k * (L 0 - α / (1 - γ))) :=
      mul_le_mul_of_nonneg_left ih hγ_nn
    calc
      L (k + 1)
        ≤ α + γ * L k := h_step
      _ ≤ α + γ * (α / (1 - γ) + γ ^ k * (L 0 - α / (1 - γ))) := by linarith
      _ = α + γ * (α / (1 - γ)) + γ * γ ^ k * (L 0 - α / (1 - γ)) := by ring
      _ = α / (1 - γ) + γ ^ (k + 1) * (L 0 - α / (1 - γ)) := by
        rw [h_alg, pow_succ]; ring

/-- **Identity: Hinderer's closed form matches `bellmanLipConstant`.**
The Hinderer closed-form Lipschitz bound `α/(1-γ)` from
Theorem 4.2(c) is definitionally equal to
`StokeyLucas.bellmanLipConstant 1 γ α`, the project's closed-form
constant at unit discount. The general
`StokeyLucas.bellmanLipConstant β γ_unweighted α` corresponds to
identifying the Hinderer `γ` with `β · γ_unweighted` (the
discount-weighted transition Lipschitz). -/
@[simp] theorem hinderer_specialises_to_bellmanLipConstant
    (α γ : ℝ) :
    α / (1 - γ) = Sanctions.StokeyLucas.bellmanLipConstant 1 γ α := by
  simp [Sanctions.StokeyLucas.bellmanLipConstant]

end Hinderer
end Foundations
end Sanctions
