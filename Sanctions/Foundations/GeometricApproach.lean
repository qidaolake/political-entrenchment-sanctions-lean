/-
Sanctions/Foundations/GeometricApproach.lean

**Geometric wash-out and wash-in sequences, and the comparison recursion.**

Two one-dimensional facts that every path bound under a chord-regular
transition reduces to (Rung 5, docs 53/55):

* **Wash-out.** A nonnegative sequence that loses at least the fraction `d` of
  itself each period, `x_{t+1} ≤ (1 − d)·x_t`, is bounded by `(1 − d)^t·x₀` and
  tends to zero when `d > 0`.
* **Wash-in.** The sequence `y_t = b·(1 − (1 − d)^t)` starts at `0`, obeys
  `y_{t+1} = y_t + d·(b − y_t)`, stays in `[0, b]`, and tends to `b`. Any
  sequence that starts above it and satisfies the one-step comparison
  `y_t ≤ x_t → y_{t+1} ≤ x_{t+1}` dominates it forever, so its eventual lower
  bound is `b`.

The comparison recursion is stated with the one-step implication as a
hypothesis because that is exactly what a monotone transition with a lower
sanction chord supplies at the equilibrium path (`Theory/LockIn/RegimePathBounds`):
`x_{t+1} = F(x_t, s_t) ≥ F(y_t, b) ≥ y_t + d·(b − y_t)` whenever `x_t ≥ y_t` and
`s_t ≥ b`, and that inequality is used only at `y_t ≤ b`, which is where the
affine minorant of `F(·, b)` is valid.

Nothing here mentions a transition, a payoff, or `Params` (Rule 19).
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Sanctions
namespace GeometricApproach

open Filter Topology

/-! ## Wash-out -/

/-- **Geometric wash-out bound.** A nonnegative sequence losing at least the
fraction `d ∈ [0,1]` of itself each period lies below `(1 − d)^t·x₀`. -/
theorem le_geom_of_step {d : ℝ} (hd1 : d ≤ 1) {x : ℕ → ℝ}
    (hstep : ∀ t, x (t + 1) ≤ (1 - d) * x t) :
    ∀ t, x t ≤ (1 - d) ^ t * x 0 := by
  intro t
  induction t with
  | zero => simp
  | succ k ih =>
    calc x (k + 1) ≤ (1 - d) * x k := hstep k
      _ ≤ (1 - d) * ((1 - d) ^ k * x 0) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - d) ^ (k + 1) * x 0 := by ring

/-- **Geometric wash-out.** With `d ∈ (0, 1]` the sequence tends to zero. -/
theorem tendsto_zero_of_step {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) {x : ℕ → ℝ}
    (hnn : ∀ t, 0 ≤ x t) (hstep : ∀ t, x (t + 1) ≤ (1 - d) * x t) :
    Tendsto x atTop (𝓝 0) := by
  have hgeom : Tendsto (fun t : ℕ => (1 - d) ^ t * x 0) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - d)
      (by linarith : (1 : ℝ) - d < 1)
    simpa using h.mul_const (x 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom hnn
    (le_geom_of_step hd1 hstep)

/-! ## Wash-in -/

/-- The wash-in sequence `b·(1 − (1 − d)^t)`: the state a transition with lower
sanction chord `d` is driven to from `0` under a sanction held at `b`. -/
def approach (b d : ℝ) (t : ℕ) : ℝ := b * (1 - (1 - d) ^ t)

@[simp] theorem approach_zero (b d : ℝ) : approach b d 0 = 0 := by
  simp [approach]

/-- The one-step law: each period closes the fraction `d` of the remaining
gap to `b`. -/
theorem approach_succ (b d : ℝ) (t : ℕ) :
    approach b d (t + 1) = approach b d t + d * (b - approach b d t) := by
  unfold approach
  ring

theorem approach_nonneg {b d : ℝ} (hb : 0 ≤ b) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (t : ℕ) :
    0 ≤ approach b d t := by
  unfold approach
  have : (1 - d) ^ t ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  exact mul_nonneg hb (by linarith)

theorem approach_le {b d : ℝ} (hb : 0 ≤ b) (hd1 : d ≤ 1) (t : ℕ) :
    approach b d t ≤ b := by
  unfold approach
  have : 0 ≤ (1 - d) ^ t := pow_nonneg (by linarith) t
  nlinarith

/-- **Wash-in.** With `d ∈ (0, 1]` the sequence tends to `b`. -/
theorem approach_tendsto {b d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    Tendsto (approach b d) atTop (𝓝 b) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - d)
    (by linarith : (1 : ℝ) - d < 1)
  have h2 : Tendsto (fun t : ℕ => b * (1 - (1 - d) ^ t)) atTop (𝓝 (b * (1 - 0))) :=
    (tendsto_const_nhds.sub h).const_mul b
  simpa [approach] using h2

/-! ## The comparison recursion -/

/-- **Domination by induction.** A sequence that starts above another and
satisfies the one-step comparison stays above it. -/
theorem ge_of_step_ge {x y : ℕ → ℝ} (h0 : y 0 ≤ x 0)
    (hstep : ∀ t, y t ≤ x t → y (t + 1) ≤ x (t + 1)) : ∀ t, y t ≤ x t := by
  intro t
  induction t with
  | zero => exact h0
  | succ k ih => exact hstep k ih

/-- **Eventual lower bound.** A sequence dominating the wash-in sequence is
eventually above every level below `b`. -/
theorem eventually_ge_of_ge_approach {b d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    {x : ℕ → ℝ} (hx : ∀ t, approach b d t ≤ x t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, b - ε ≤ x t := by
  have h := (approach_tendsto (b := b) hd0 hd1).eventually
    (eventually_ge_nhds (show b - ε < b by linarith))
  exact h.mono fun t ht => le_trans ht (hx t)

end GeometricApproach
end Sanctions
