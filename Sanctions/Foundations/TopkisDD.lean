/-
Sanctions/Foundations/TopkisDD.lean

Topkis-based derivative-free preservation of decreasing/increasing
differences under a one-step Bellman update.

This module provides a *derivative-free* route to the DD conclusion
(`R_xa ≤ 0`) using Topkis's submodularity-preservation machinery
(Topkis 1998, Theorem 3.9.2) specialized to deterministic-affine
transitions. The point is to show that the DD conclusion is **robust to
dropping the `V_xx < 0` regularity assumption** whenever the value
function is linear in the state — which holds for any concrete payoff
linear in the state with affine response (e.g. a linear-quadratic
instantiation).

The key cancellation: the Bellman one-step preserves decreasing
differences `(a, x) ↦ g(a, x)` provided the transition `F` is affine
in `(a, x)` with zero second cross-difference and the continuation `V`
is linear. The "curvature × slope" term `V'' · F_a · F_x` that would
otherwise need to be controlled vanishes identically under either
condition.

All theorems in this module are stated abstractly over generic
`r, V, F, ε, β, γ, α` and apply to any concrete model with the
linearity and no-interaction structure described above.
-/

import Sanctions.Foundations.Basic
import Mathlib.Topology.Order.Basic

noncomputable section
open Set Topology

namespace Sanctions

/-! ## Decreasing differences on `ℝ × ℝ`

A function `f : ℝ → ℝ → ℝ` has *decreasing differences* in `(a, x)` on
`A × X` if for all `a ≤ a'` in `A` and `x ≤ x'` in `X`,
  `f a' x' - f a x' ≤ f a' x - f a x`.

Equivalently (for smooth `f`), `∂²f/∂a∂x ≤ 0`. This is the lattice
characterization of submodularity used by Topkis (1998, §2.6). -/

def DecreasingDifferences (f : ℝ → ℝ → ℝ) (A X : Set ℝ) : Prop :=
  ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → a ≤ a' →
    ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X → x ≤ x' →
      f a' x' - f a x' ≤ f a' x - f a x

/-- *Decreasing differences with margin `ε`*. For smooth `f` this is the
pointwise condition `f_ax ≤ -ε`. The margin scales with the rectangle size:
  `[f(a',x') - f(a,x')] - [f(a',x) - f(a,x)]  ≤  -ε · (a' - a) · (x' - x)`.

Used for quantitative DD claims (`R_xa ≤ -ε`) rather than the qualitative
sign claim alone. -/
def DecreasingDifferencesBy (f : ℝ → ℝ → ℝ) (A X : Set ℝ) (ε : ℝ) : Prop :=
  ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → a ≤ a' →
    ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X → x ≤ x' →
      f a' x' - f a x' - f a' x + f a x ≤ -ε * (a' - a) * (x' - x)

/-- *Increasing differences with margin `ε`* (the dual of
`DecreasingDifferencesBy`). For smooth `f` this is `f_ax ≥ ε`. -/
def IncreasingDifferencesBy (f : ℝ → ℝ → ℝ) (A X : Set ℝ) (ε : ℝ) : Prop :=
  ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → a ≤ a' →
    ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X → x ≤ x' →
      ε * (a' - a) * (x' - x) ≤ f a' x' - f a x' - f a' x + f a x

/-- *Increasing differences* (qualitative version, `f_ax ≥ 0`). The dual of
`DecreasingDifferences`. -/
def IncreasingDifferences (f : ℝ → ℝ → ℝ) (A X : Set ℝ) : Prop :=
  ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → a ≤ a' →
    ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X → x ≤ x' →
      f a' x - f a x ≤ f a' x' - f a x'

/-! ## Bellman preservation when the value function is linear

This is the key lemma. Given a stage payoff `r` with decreasing
differences and a continuation value `V x = α + γ x` (linear), the
one-step dynamic objective `g(a, x) := r(a, x) + β · V(F(a, x))` inherits
decreasing differences whenever `F` is *affine in `(a, x)` with zero
second cross-difference*.

The proof is direct:
  g(a', x') - g(a, x') - g(a', x) + g(a, x)
    = [r(a', x') - r(a, x') - r(a', x) + r(a, x)]              -- ≤ 0 by DD of r
      + β·γ·[F(a', x') - F(a, x') - F(a', x) + F(a, x)]        -- = 0 by zero second cross
    = (something ≤ 0) + 0 = ≤ 0.

No assumption on the sign of `γ` is needed — the zero-second-cross
condition on `F` kills the term regardless. -/

theorem decreasingDifferences_preservation_linear_V
    (r : ℝ → ℝ → ℝ) (A X : Set ℝ)
    (h_r_dd : DecreasingDifferences r A X)
    (β γ α : ℝ) (_hβ_nn : 0 ≤ β)
    (F : ℝ → ℝ → ℝ)
    (hF_no_interaction :
      ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X →
        F a' x' - F a x' - F a' x + F a x = 0) :
    DecreasingDifferences
      (fun a x => r a x + β * (α + γ * F a x)) A X := by
  intro a a' ha ha' haa x x' hx hx' hxx
  have h_r := h_r_dd ha ha' haa hx hx' hxx
  have h_F := hF_no_interaction ha ha' hx hx'
  -- Reduce the goal to the algebraic identity plus the two ingredients.
  have h_key :
      (r a' x' + β * (α + γ * F a' x'))
        - (r a x' + β * (α + γ * F a x'))
        - ((r a' x + β * (α + γ * F a' x))
            - (r a x + β * (α + γ * F a x)))
      = (r a' x' - r a x' - (r a' x - r a x))
        + β * γ * (F a' x' - F a x' - F a' x + F a x) := by ring
  have h_F_term : β * γ * (F a' x' - F a x' - F a' x + F a x) = 0 := by
    rw [h_F]; ring
  linarith

/-- **Margin-preserving** version of the Bellman lemma. If `r` has
decreasing differences with margin `ε` and the same linearity/no-interaction
hypotheses on `V` and `F` hold, then `g(a, x) := r(a, x) + β · V(F(a, x))`
inherits decreasing differences with margin `ε`. This is the quantitative
DD claim `R_xa ≤ -ε`, not just `R_xa ≤ 0`. -/
theorem decreasingDifferencesBy_preservation_linear_V
    (r : ℝ → ℝ → ℝ) (A X : Set ℝ) (ε : ℝ)
    (h_r_ddb : DecreasingDifferencesBy r A X ε)
    (β γ α : ℝ) (_hβ_nn : 0 ≤ β)
    (F : ℝ → ℝ → ℝ)
    (hF_no_interaction :
      ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X →
        F a' x' - F a x' - F a' x + F a x = 0) :
    DecreasingDifferencesBy
      (fun a x => r a x + β * (α + γ * F a x)) A X ε := by
  intro a a' ha ha' haa x x' hx hx' hxx
  have h_r := h_r_ddb ha ha' haa hx hx' hxx
  have h_F := hF_no_interaction ha ha' hx hx'
  have h_key :
      (r a' x' + β * (α + γ * F a' x'))
        - (r a x' + β * (α + γ * F a x'))
        - ((r a' x + β * (α + γ * F a' x))
            - (r a x + β * (α + γ * F a x)))
      = (r a' x' - r a x' - r a' x + r a x)
        + β * γ * (F a' x' - F a x' - F a' x + F a x) := by ring
  have h_F_term : β * γ * (F a' x' - F a x' - F a' x + F a x) = 0 := by
    rw [h_F]; ring
  linarith

/-- **Dual** of the margin-preserving lemma: same hypotheses on `V`, `F`
but with `r` having *increasing* differences by margin `ε`. The proof
is mechanical: the cross-difference of `F` still vanishes, regardless
of the direction of the inequality on `r`. Used for the Topkis-based
ID conclusion via a sanction-curvature-style channel at a concrete
instantiation. -/
theorem increasingDifferencesBy_preservation_linear_V
    (r : ℝ → ℝ → ℝ) (A X : Set ℝ) (ε : ℝ)
    (h_r_idb : IncreasingDifferencesBy r A X ε)
    (β γ α : ℝ) (_hβ_nn : 0 ≤ β)
    (F : ℝ → ℝ → ℝ)
    (hF_no_interaction :
      ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X →
        F a' x' - F a x' - F a' x + F a x = 0) :
    IncreasingDifferencesBy
      (fun a x => r a x + β * (α + γ * F a x)) A X ε := by
  intro a a' ha ha' haa x x' hx hx' hxx
  have h_r := h_r_idb ha ha' haa hx hx' hxx
  have h_F := hF_no_interaction ha ha' hx hx'
  have h_key :
      (r a' x' + β * (α + γ * F a' x'))
        - (r a x' + β * (α + γ * F a x'))
        - ((r a' x + β * (α + γ * F a' x))
            - (r a x + β * (α + γ * F a x)))
      = (r a' x' - r a x' - r a' x + r a x)
        + β * γ * (F a' x' - F a x' - F a' x + F a x) := by ring
  have h_F_term : β * γ * (F a' x' - F a x' - F a' x + F a x) = 0 := by
    rw [h_F]; ring
  linarith

/-! ## A useful helper: affine `F` has zero second cross-difference

For `F(a, x) := c + d·a + e·x` (no `a · x` interaction), the second
cross-difference vanishes by direct algebra. -/

theorem affine_no_interaction_no_cross (c d e : ℝ)
    (A X : Set ℝ) :
    ∀ ⦃a a' : ℝ⦄, a ∈ A → a' ∈ A → ∀ ⦃x x' : ℝ⦄, x ∈ X → x' ∈ X →
      (c + d * a' + e * x') - (c + d * a + e * x')
      - ((c + d * a' + e * x) - (c + d * a + e * x)) = 0 := by
  intro a a' _ _ x x' _ _
  ring

/-! ## Iterated preservation: limit of a DD-preserving iteration is DD

If the Bellman operator `T` preserves decreasing differences (i.e.,
`T : DDcone → DDcone` where `DDcone` is the cone of functions with the
given DD property), and `T^n V₀` converges pointwise to `V` starting
from some `V₀ ∈ DDcone`, then `V` inherits DD.

This is the *real* limit-preservation argument: induction shows every
iterate `T^n V₀` is in `DDcone`, and `DDcone` is closed under pointwise
limits because the DD inequality is preserved under limits.

(The previous version of this theorem assumed `V ∈ DDcone` as a
hypothesis and returned the same conclusion — that was circular and
vacuous; it has been replaced with this honest limit-preservation form.) -/

/-- **DD is preserved under pointwise limits.** If a sequence of
DD-functions converges pointwise on `A × X`, the limit has DD on
`A × X`. -/
theorem DD_of_pointwise_limit
    {V_seq : ℕ → ℝ → ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (A X : Set ℝ)
    (h_seq_dd : ∀ n, DecreasingDifferences (V_seq n) A X)
    (h_lim : ∀ a x, Filter.Tendsto (fun n => V_seq n a x)
                Filter.atTop (𝓝 (V a x))) :
    DecreasingDifferences V A X := by
  intro a a' ha ha' ha_le x x' hx hx' hx_le
  have h_each : ∀ n,
      V_seq n a' x' - V_seq n a x' ≤ V_seq n a' x - V_seq n a x :=
    fun n => h_seq_dd n ha ha' ha_le hx hx' hx_le
  have h_tend_lhs : Filter.Tendsto
      (fun n => V_seq n a' x' - V_seq n a x') Filter.atTop
      (𝓝 (V a' x' - V a x')) :=
    (h_lim a' x').sub (h_lim a x')
  have h_tend_rhs : Filter.Tendsto
      (fun n => V_seq n a' x - V_seq n a x) Filter.atTop
      (𝓝 (V a' x - V a x)) :=
    (h_lim a' x).sub (h_lim a x)
  exact le_of_tendsto_of_tendsto h_tend_lhs h_tend_rhs
    (Filter.Eventually.of_forall h_each)

/-- **DD inherited by Banach iteration limit from a DD seed.**
If `T` preserves DD on the cone, and `V = lim T^n V₀` pointwise for some
`V₀ ∈ DDcone`, then `V ∈ DDcone`.

This is the *honest* fixed-point-inheritance form: the proof works by
(1) induction showing each iterate is in DDcone, and (2) limit
preservation of DD via `DD_of_pointwise_limit`. No assumption on the
limit `V` itself is required other than the convergence statement. -/
theorem DD_inherited_by_pointwise_iteration
    {T : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} (A X : Set ℝ)
    (h_preserve : ∀ g, DecreasingDifferences g A X →
                       DecreasingDifferences (T g) A X)
    (V₀ : ℝ → ℝ → ℝ) (h_V₀_dd : DecreasingDifferences V₀ A X)
    (V : ℝ → ℝ → ℝ)
    (h_lim : ∀ a x, Filter.Tendsto (fun n => (T^[n] V₀) a x)
                Filter.atTop (𝓝 (V a x))) :
    DecreasingDifferences V A X := by
  -- All iterates have DD by induction on the iteration count.
  have h_iter : ∀ n, DecreasingDifferences (T^[n] V₀) A X := by
    intro n
    induction n with
    | zero => simpa using h_V₀_dd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact h_preserve _ ih
  -- Limit preservation closes the argument.
  exact DD_of_pointwise_limit A X h_iter h_lim

/-!
## Application sketch (generic linear-quadratic instantiation)

To apply `decreasingDifferences_preservation_linear_V` to a concrete
realized-response Bellman with `V` linear in the state `x`, an
instantiation needs three ingredients:

1. **Primitive submodularity of the reduced-form stage payoff**
   `r(x, a) := U_T(x, a, σ(x, a))` on interior response regions. For
   a payoff `U_T` jointly linear-in-`x` and quadratic-in-`a` together
   with an affine response `σ(x, a)`, the chain rule through `σ` gives
   `r_xa  =  U_T_xa  +  U_T_xs · σ_a  +  U_T_sa · σ_x  +  U_T_ss · σ_a · σ_x`,
   whose sign reduces to a clean primitive parametric inequality.

2. **Linearity of `V` in `x`**, which is automatic from linearity of
   `U_T` in `x` plus an affine `σ` plus an affine transition `F`: the
   Bellman operator maps linear-in-`x` functions to linear-in-`x`
   functions, and the unique fixed point is therefore linear in `x`.

3. **Affine `F` with zero `(a, x)` interaction**, which follows
   whenever `σ` is jointly affine in `(x, a)` with no `a · x` cross
   term — automatic for affine response functions of the form
   `σ_raw(x, a) = c + d_x · x + d_a · a` (then
   `F(x, a) = (1-δ)·x + δ·σ_raw` inherits the no-interaction
   property).

Combining (1)–(3) with `decreasingDifferences_preservation_linear_V`
yields `R_xa ≤ 0` (DD) **without invoking `V_xx < 0`**. A concrete
instantiation specializing `r, F, V` to particular closed-form
expressions and discharging the primitive bound (1) via `linarith` is
a clean follow-up; the theorems above are the substantive content.
-/

end Sanctions

end
