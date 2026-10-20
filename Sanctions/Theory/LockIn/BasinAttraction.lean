/-
Sanctions/Theory/LockIn/BasinAttraction.lean

**From "converges to some steady state" to "converges to this one."**

`LockInLimit` proves that a monotone equilibrium path on a certified basin
converges to *a* steady state, and that a least closed-loop fixed point exists.
Neither statement names the limit of an arbitrary path: two different starting
points in the same basin are not yet known to share a limit. That gap is exactly
the distance between a *certified invariant basin* and an *attractor*, and it is
what this file closes.

Nothing here is affine, functional-form, or numerical. Every statement is over an
arbitrary `p : Params`, the abstract transition `p.F`, arbitrary equilibrium-
derived `V_S` and `α`, and an arbitrary feasible interval (Rule 22). The
constructed economies in `Examples/` play no part in any statement below.

## Layering

* `Foundations/MonotoneAttraction.lean` — the abstract interval-map theorem,
  with no economics in it, plus the counterexample showing that the uniqueness
  hypothesis cannot be dropped.
* here — the equilibrium bridge: the closed loop `dynamicTopLockInStepF`, whose
  rule is equilibrium-derived and whose transition is `p.F`, is shown to satisfy
  the abstract theorem's hypotheses, and the interval fixed point is identified.

## The two results

`dynamicTopLockInPathF_tendsto_of_unique_fixedPoint` (Target C) is the bridge: on
any feasible interval the closed loop preserves, if the closed loop has exactly
one fixed point there, then every equilibrium path from that interval converges
to it, and under `StrictAdjustment` the realized sanction converges to the same
limit.

`dynamicTopLockInPathF_tendsto_right_endpoint` (Target D) removes the
equilibrium-level uniqueness hypothesis in favour of an economic one: if the
realized rule is *strictly above the diagonal* everywhere below the interval's
right endpoint and fixes that endpoint, then under strict adjustment no other
fixed point can exist, and every path converges to the endpoint. Its mirror
`..._tendsto_left_endpoint` does the same for a wash-out interval.

That direction condition is the paper's own strict-ratchet language, so Target D
is the economically interpretable form. Neither theorem asserts a rate, Lyapunov
stability, or robustness of the equilibrium under perturbation of primitives.
-/

import Sanctions.Foundations.MonotoneAttraction
import Sanctions.Theory.LockIn.LockInLimit
import Sanctions.Theory.Equilibrium.BasinCornerExistence
import Sanctions.Theory.Equilibrium.SelectionRobust

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Regularity of the closed loop, inherited from the rule -/

/-- **The closed loop is monotone wherever the realized rule is.**

`G x = F x (R x)` composes `F`'s two monotonicity fields with monotonicity of the
equilibrium-derived rule. Extracted as a named lemma because `LockInLimit` proves
it inline. -/
theorem dynamicTopLockInStepF_monotoneOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b)) :
    MonotoneOn (p.dynamicTopLockInStepF V_S α) (Set.Icc a b) := by
  intro x hx y hy hxy
  have h1 : p.F x (p.dynamicTopRealizedRule V_S α x)
      ≤ p.F y (p.dynamicTopRealizedRule V_S α x) :=
    p.F_mono_x _ hxy
  have h2 : p.F y (p.dynamicTopRealizedRule V_S α x)
      ≤ p.F y (p.dynamicTopRealizedRule V_S α y) :=
    p.F_mono_s _ (hrule_mono hx hy hxy)
  exact le_trans h1 h2

/-- **The closed loop is continuous wherever the realized rule is.**

`F` is jointly continuous (a `Params` field), so `x ↦ F x (R x)` is continuous on
any set where `R` is. -/
theorem dynamicTopLockInStepF_continuousOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b)) :
    ContinuousOn (p.dynamicTopLockInStepF V_S α) (Set.Icc a b) :=
  p.F_continuous.comp_continuousOn (continuousOn_id.prodMk hrule_cont)

/-! ## Target C — the equilibrium bridge -/

/-- **Every equilibrium path in a preserved interval converges to the interval's
unique closed-loop fixed point.**

Hypotheses, in English: the interval `[a,b]` is feasible and the equilibrium's
closed loop maps it into itself; the equilibrium-derived realized rule is
monotone and continuous there; and `x_star` is the only state of `[a,b]` the
closed loop leaves unchanged. Conclusion: the state path from *any* starting
point of `[a,b]` converges to `x_star`.

This is the named-limit statement `LockInLimit` does not provide. The transition
is the abstract `p.F` throughout. -/
theorem dynamicTopLockInPathF_tendsto_of_unique_fixedPoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b x_star : ℝ}
    (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α y = y → y = x_star)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop (𝓝 x_star) :=
  Sanctions.MonotoneAttraction.monotoneOn_orbit_tendsto_of_unique hab
    (p.dynamicTopLockInStepF_monotoneOn V_S α hrule_mono)
    (p.dynamicTopLockInStepF_continuousOn V_S α hrule_cont)
    hmaps hUniq hx₀

/-- **The limit is a genuine equilibrium-consistent steady state.**

Non-vacuity companion to the bridge: under the same hypotheses `x_star` really
does lie in the interval and really is fixed by the closed loop. -/
theorem uniqueFixedPoint_mem_and_isFixed_of_rule
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b x_star : ℝ}
    (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α y = y → y = x_star) :
    x_star ∈ Set.Icc a b ∧ p.dynamicTopLockInStepF V_S α x_star = x_star :=
  Sanctions.MonotoneAttraction.uniqueFixedPointOn_mem_and_isFixed hab
    (p.dynamicTopLockInStepF_monotoneOn V_S α hrule_mono)
    (p.dynamicTopLockInStepF_continuousOn V_S α hrule_cont)
    hmaps hUniq

/-! ## Target D — attraction to an endpoint from a strict direction condition

Target C still hypothesizes fixed-point uniqueness at equilibrium level. The
theorems below replace it with the paper's own strict-ratchet and wash-out
language, which is a condition on the equilibrium rule's position relative to the
diagonal — an economic statement, not a fixed-point-counting one. -/

/-- **Strict ratchet below the right endpoint forces attraction to it.**

If the equilibrium-derived realized rule lies strictly above the diagonal at
every state of `[a, b)` and fixes `b`, then under `StrictAdjustment` the closed
loop has no fixed point in `[a,b]` other than `b`, and every equilibrium path
from `[a,b]` converges to `b`.

`StrictAdjustment` is what converts "the closed loop is unchanged at `y`" into
"the realized rule crosses the diagonal at `y`"; without it a flat transition
band could fix the state while the rule sits strictly above it. -/
theorem dynamicTopLockInPathF_tendsto_right_endpoint
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop (𝓝 b) := by
  refine p.dynamicTopLockInPathF_tendsto_of_unique_fixedPoint V_S α hab
    hrule_mono hrule_cont hmaps ?_ hx₀
  intro y hy hfix
  by_contra hne
  have hyb : y < b := lt_of_le_of_ne hy.2 hne
  have hyI : y ∈ Sanctions.I := ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  have hrule :=
    (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
      hAdj V_S α hyI).mp hfix
  have := hstrict y ⟨hy.1, hyb⟩
  rw [hrule] at this
  exact lt_irrefl y this

/-- **Strict wash-out above the left endpoint forces attraction to it.**

The mirror of the previous theorem for a low basin: if the realized rule lies
strictly *below* the diagonal at every state of `(a, b]` and fixes `a`, then
under `StrictAdjustment` every equilibrium path from `[a,b]` converges to `a`. -/
theorem dynamicTopLockInPathF_tendsto_left_endpoint
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Ioc a b, p.dynamicTopRealizedRule V_S α x < x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop (𝓝 a) := by
  refine p.dynamicTopLockInPathF_tendsto_of_unique_fixedPoint V_S α hab
    hrule_mono hrule_cont hmaps ?_ hx₀
  intro y hy hfix
  by_contra hne
  have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hne)
  have hyI : y ∈ Sanctions.I := ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  have hrule :=
    (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
      hAdj V_S α hyI).mp hfix
  have := hstrict y ⟨hay, hy.2⟩
  rw [hrule] at this
  exact lt_irrefl y this


/-! ## Target E — exactly what separates persistence from attraction

The persistence machinery supplies a level condition with a *weak* inequality
(`max x sbar ≤ R x`). Target D needs a *strict* one below the endpoint. The
theorem below shows the gap is not merely sufficient-but-unnecessary: given the
weak level condition, strictness below the endpoint is **equivalent** to the
closed loop having the endpoint as its only fixed point.

So the single missing ingredient between the current hypotheses and attraction to
a named steady state is the strictness of the ratchet inequality — no additional
regularity, no rate, and no new primitive. `MonotoneAttraction.weak_level_condition_insufficient`
shows the weak form genuinely cannot deliver it: a rule sitting weakly above the
diagonal may fix every state of the basin. -/

/-- **Strict ratchet below the endpoint ⟺ the endpoint is the only rest point.**

Assume the equilibrium-derived realized rule satisfies the *weak* level condition
`x ≤ R x` on the feasible interval `[a,b]`, and assume `StrictAdjustment`. Then:

  `R x > x` for every `x ∈ [a,b)`   ↔   every `y ∈ [a,b]` the closed loop
                                        leaves unchanged equals `b`.

This is *location plus at-most-one*, not existence: on its own it does not say
the closed loop fixes anything. `strict_ratchet_endpoint_existsUnique_fixedPoint`
adds existence and is the only statement here entitled to `∃!`.

Read from left to right this is what Target D consumes. Read from right to left
it says the strictness hypothesis is not an artefact of the proof: any route to
endpoint attraction must establish it, because it is implied by the conclusion.

Nothing here is assumed about functional form, and the transition is `p.F`. -/
theorem strict_ratchet_iff_endpoint_is_only_fixedPoint
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hlevel : ∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x) :
    (∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
      ↔ (∀ y ∈ Set.Icc a b,
            p.dynamicTopLockInStepF V_S α y = y → y = b) := by
  constructor
  · intro hstrict y hy hfix
    by_contra hne
    have hyb : y < b := lt_of_le_of_ne hy.2 hne
    have hyI : y ∈ Sanctions.I := ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
    have hrule :=
      (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
        hAdj V_S α hyI).mp hfix
    have hlt := hstrict y ⟨hy.1, hyb⟩
    rw [hrule] at hlt
    exact lt_irrefl y hlt
  · intro huniq x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
    refine lt_of_le_of_ne (hlevel x hxIcc) (fun heq => ?_)
    have hstepfix : p.dynamicTopLockInStepF V_S α x = x :=
      p.dynamicTopLockInStepF_fixedPoint_of_realizedRule_eq_self V_S α heq.symm
    exact absurd (huniq x hxIcc hstepfix) (ne_of_lt hx.2)

/-! ## Fixed-point identification at the rest point -/

/-- **The realized rule crosses the diagonal at the interval's only rest point.**

A fixed-point *identification*, not a convergence statement: it says the limit
candidate satisfies `R x_star = x_star`. Sanction-sequence convergence is a
separate and stronger claim, proved for an actual equilibrium in
`equilibriumTop_sanctions_tendsto_of_only_fixedPoint`. -/
theorem realizedRule_eq_self_at_only_closedLoop_fixedPoint
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b x_star : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α y = y → y = x_star) :
    p.dynamicTopRealizedRule V_S α x_star = x_star := by
  obtain ⟨hmem, hfix⟩ :=
    p.uniqueFixedPoint_mem_and_isFixed_of_rule V_S α hab hrule_mono hrule_cont
      hmaps hUniq
  have hI : x_star ∈ Sanctions.I := ⟨le_trans ha0 hmem.1, le_trans hmem.2 hb1⟩
  exact (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
    hAdj V_S α hI).mp hfix

/-! ## Genuine existence and uniqueness

`strict_ratchet_iff_endpoint_is_only_fixedPoint` establishes *location and
at-most-one*: any rest point in the interval must be the endpoint. It is not an
existence statement. The corollary below adds existence, and is the only
declaration here entitled to say `∃!`. -/

/-- **Under a strict ratchet the endpoint is the unique rest point.**

Genuine `∃!`: existence comes from the orbit argument (a monotone continuous
self-map of a compact interval has a rest point), and at-most-one comes from the
strict ratchet.  Requires the regularity the orbit argument needs, which the
at-most-one characterization does not. -/
theorem strict_ratchet_endpoint_existsUnique_fixedPoint
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x) :
    ∃! y, y ∈ Set.Icc a b ∧ p.dynamicTopLockInStepF V_S α y = y := by
  have hOnly : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α y = y → y = b := by
    intro y hy hfix
    by_contra hne
    have hyb : y < b := lt_of_le_of_ne hy.2 hne
    have hyI : y ∈ Sanctions.I := ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
    have hrule :=
      (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
        hAdj V_S α hyI).mp hfix
    have hlt := hstrict y ⟨hy.1, hyb⟩
    rw [hrule] at hlt
    exact lt_irrefl y hlt
  obtain ⟨hmem, hfix⟩ :=
    p.uniqueFixedPoint_mem_and_isFixed_of_rule V_S α hab hrule_mono hrule_cont
      hmaps hOnly
  exact ⟨b, ⟨hmem, hfix⟩, fun z hz => hOnly z hz.1 hz.2⟩

/-! ## Round 3 — actual-equilibrium capstones

Everything above accepts arbitrary `V_S` and `α`, so it is kinematics: true of
any pair of functions, equilibrium or not.  The declarations below consume a
genuine `E : p.FeedbackStackelbergEquilibriumTop`, whose fields carry both
players' optimality and feasibility, and instantiate the rule at `E.V_S` and
`E.α`.  They add no new equilibrium condition; they reuse the kinematic
theorems internally.

The two conditions that remain hypotheses at this layer — continuity of the
realized rule on the basin, and the strict ratchet — are displayed in every
signature rather than bundled, because neither is yet discharged from
primitives. -/

/-- **State-path attraction at an actual equilibrium.**

Every equilibrium state path started in a preserved basin converges to the
basin's only closed-loop rest point.  `E` supplies both players' Bellman
optimality and feasibility through its own fields; nothing about the equilibrium
is reconstructed here. -/
theorem equilibriumTop_path_tendsto_of_only_fixedPoint
    (E : p.FeedbackStackelbergEquilibriumTop) {a b x_star : ℝ}
    (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    (hOnly : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α y = y → y = x_star)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
      (𝓝 x_star) :=
  p.dynamicTopLockInPathF_tendsto_of_unique_fixedPoint E.V_S E.α hab
    hrule_mono hrule_cont hmaps hOnly hx₀

/-- Every equilibrium state path stays in a basin the closed loop preserves. -/
theorem equilibriumTop_path_mem
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    ∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc a b := by
  intro n
  induction n with
  | zero => simpa [AbstractGame.Params.dynamicTopLockInPathF] using hx₀
  | succ k ih =>
    rw [AbstractGame.Params.dynamicTopLockInPathF, Function.iterate_succ_apply']
    exact hmaps _ ih

/-- **Sanction-path attraction at an actual equilibrium.**

This is a genuine `Tendsto` statement about the realized sanction *sequence*,
not an identification of a fixed point.  The sanction path is the realized rule
evaluated along the state path, so continuity of the rule on the basin carries
the state limit to the sanction limit; `StrictAdjustment` then identifies that
limit with the state limit itself. -/
theorem equilibriumTop_sanctions_tendsto_of_only_fixedPoint
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {a b x_star : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    (hOnly : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α y = y → y = x_star)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
      (𝓝 x_star) := by
  obtain ⟨hmem_star, hfix_star⟩ :=
    p.uniqueFixedPoint_mem_and_isFixed_of_rule E.V_S E.α hab hrule_mono
      hrule_cont hmaps hOnly
  have hstarI : x_star ∈ Sanctions.I :=
    ⟨le_trans ha0 hmem_star.1, le_trans hmem_star.2 hb1⟩
  have hrule_star : p.dynamicTopRealizedRule E.V_S E.α x_star = x_star :=
    (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
      hAdj E.V_S E.α hstarI).mp hfix_star
  have hpath :=
    p.equilibriumTop_path_tendsto_of_only_fixedPoint E hab hrule_mono hrule_cont
      hmaps hOnly hx₀
  have hmem := p.equilibriumTop_path_mem E hmaps hx₀
  have hwithin :
      Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
        (nhdsWithin x_star (Set.Icc a b)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpath
      (Filter.Eventually.of_forall hmem)
  have hcomp := (hrule_cont x_star hmem_star).tendsto.comp hwithin
  rw [hrule_star] at hcomp
  exact hcomp

/-- **Endpoint attraction at an actual equilibrium, from the strict ratchet.**

The economically interpretable capstone: on a preserved basin where the
equilibrium realized rule is strictly above the diagonal below the right
endpoint, every equilibrium state path converges to that endpoint, and the
realized sanction converges with it. -/
theorem equilibriumTop_tendsto_right_endpoint
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop (𝓝 b) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
        (𝓝 b) := by
  have hOnly : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α y = y → y = b := by
    intro y hy hfix
    by_contra hne
    have hyb : y < b := lt_of_le_of_ne hy.2 hne
    have hyI : y ∈ Sanctions.I := ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
    have hrule :=
      (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
        hAdj E.V_S E.α hyI).mp hfix
    have hlt := hstrict y ⟨hy.1, hyb⟩
    rw [hrule] at hlt
    exact lt_irrefl y hlt
  refine ⟨p.equilibriumTop_path_tendsto_of_only_fixedPoint E hab hrule_mono
      hrule_cont hmaps hOnly hx₀,
    p.equilibriumTop_sanctions_tendsto_of_only_fixedPoint hAdj E hab ha0 hb1
      hrule_mono hrule_cont hmaps hOnly hx₀⟩

/-- **Wash-out attraction at an actual equilibrium, from the strict downward
condition.** Mirror of `equilibriumTop_tendsto_right_endpoint`. -/
theorem equilibriumTop_tendsto_left_endpoint
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Ioc a b, p.dynamicTopRealizedRule E.V_S E.α x < x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop (𝓝 a) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
        (𝓝 a) := by
  have hOnly : ∀ y ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α y = y → y = a := by
    intro y hy hfix
    by_contra hne
    have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hne)
    have hyI : y ∈ Sanctions.I := ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
    have hrule :=
      (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
        hAdj E.V_S E.α hyI).mp hfix
    have hlt := hstrict y ⟨hay, hy.2⟩
    rw [hrule] at hlt
    exact lt_irrefl y hlt
  exact ⟨p.equilibriumTop_path_tendsto_of_only_fixedPoint E hab hrule_mono
      hrule_cont hmaps hOnly hx₀,
    p.equilibriumTop_sanctions_tendsto_of_only_fixedPoint hAdj E hab ha0 hb1
      hrule_mono hrule_cont hmaps hOnly hx₀⟩

/-! ## Round 4B — discharging strict crossing from the existing level condition

The persistence packages supply the level condition in the form

  `∀ x ∈ [xbar, 1], max x sbar ≤ R x`

where `sbar` is a **sanction floor**. Written that way the inequality is weak
against `x` — but it is *not* weak against `sbar`. Wherever the floor exceeds
the current state, `R x ≥ sbar > x` is already strict, with nothing added.

So strict crossing is discharged, from an existing hypothesis, exactly on
`[xbar, sbar)`. This is a genuine primitive-level discharge on that range, not a
new assumption. Its reach is the floor's reach, and that reach is also its
limitation: a floor extending to the top state covers the whole basin, but
`sbar = 1` forces `R x = 1` at every basin state, so the rule is *constant at
the corner* there. The strict crossing is then discharged in the degenerate
case, not in the interior one. -/

/-- **The sanction floor makes the ratchet strict below itself.**

From the persistence level condition alone: at any basin state strictly below
the floor, the realized rule strictly exceeds the state. No new hypothesis. -/
theorem strict_ratchet_of_level_floor
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x) :
    ∀ x ∈ Set.Ico xbar (min sbar 1),
      x < p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  have hx1 : x ≤ 1 := le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))
  have hxs : x < sbar := lt_of_lt_of_le hx.2 (min_le_left _ _)
  exact lt_of_lt_of_le hxs
    (le_trans (le_max_right x sbar) (h_level_top x ⟨hx.1, hx1⟩))

/-- **A floor at the top state discharges strict crossing on the whole basin.**

With `sbar = 1` the previous lemma covers all of `[xbar, 1)`, so the strict
ratchet hypothesis of the endpoint theorems is met outright. -/
theorem strict_ratchet_of_top_level_floor
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar : ℝ}
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x 1 ≤ p.dynamicTopRealizedRule V_S α x) :
    ∀ x ∈ Set.Ico xbar (1 : ℝ), x < p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  have := p.strict_ratchet_of_level_floor V_S α h_level_top x (by simpa using hx)
  exact this

/-- **Attraction to the top state at an actual equilibrium, with strict crossing
discharged.**

Given the persistence level condition with a floor at the top state, the
strict-ratchet hypothesis is *derived* rather than assumed, and every
equilibrium path in the basin converges to `1`, state and realized sanction
alike.

Read the hypothesis `h_level_top` carefully before reading the conclusion as
general: `max x 1 ≤ R x` with `x ≤ 1` says `1 ≤ R x`, so on a feasible rule it
pins `R x = 1` at **every** basin state. This is the **absorbing corner**, the
degenerate end of the parameter range, not the interior ratchet the paper's
mechanism section describes. Its attraction claim is real but weak.

Three hypotheses remain: monotonicity of the realized rule and invariance of the
basin — both supplied by the persistence machinery (`top_rule_mono`, and
`dynamicTopLockInStepF_mem_basin` from the level condition) — and continuity,
which is **not** discharged here (see `dynamicTopRealizedRule_continuousOn_of_argmaxUnique`
below for the discharge). `StrictAdjustment` is a fourth, and is a structural
condition on `p.F` that no persistence package supplies. -/
theorem equilibriumTop_tendsto_one_of_top_level_floor
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1))
    (hrule_cont :
      ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x 1 ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar (1 : ℝ)) :
    Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop (𝓝 1) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
        (𝓝 1) :=
  p.equilibriumTop_tendsto_right_endpoint hAdj E hxbar1 hxbar0 le_rfl
    hrule_mono hrule_cont hmaps
    (p.strict_ratchet_of_top_level_floor E.V_S E.α h_level_top) hx₀

/-! ## Round 4A — discharging continuity of the realized equilibrium rule

The realized rule is the *greatest* element of the Sender's dynamic argmax, and
a greatest selector of an argmax correspondence is in general only upper
semicontinuous: it jumps wherever the argmax set changes discontinuously. So
continuity is a genuine second condition, independent of the strict ratchet, and
it is not implied by monotonicity.

It is, however, discharged in this development from single-valuedness of the
Sender's dynamic argmax. `σ_dyn_top_continuous_subtype_SI_of_unique_on` derives
continuity of `(x, a) ↦ σ_dyn_top V_S x a` at physical compliance from
`DynamicArgmaxUniqueOnI V_S` (and `σ_dyn_top_continuous_subtype_of_unique_on`, at
every real `a`, from `DynamicArgmaxUnique V_S`), and the equilibrium object
carries continuity of the Target policy, with values in `[0,1]`, in its field
`hα`. Composing the two gives continuity of the realized rule. Since round BJ4.3
a value-class certificate carries the compliance-local form, which is what this
route reads. -/

/-- **Continuity of the realized equilibrium rule, from compliance-local argmax
uniqueness (round BJ4.3, 2026-10-08).** General in `F`.

If the Sender's dynamic argmax against `E.V_S` is single-valued at physical
states and physical compliance levels (`DynamicArgmaxUniqueOnI`), the realized
equilibrium rule `x ↦ σ_dyn_top E.V_S x (E.α x)` is continuous on any feasible
interval. Compliance-local sibling of
`dynamicTopRealizedRule_continuousOn_of_argmaxUnique`: uniqueness at compliance
levels outside `[0,1]` is dropped, because on the state space the equilibrium
policy only plays compliance levels in `[0,1]` (`E.α_mem`), where the projected
selector of `σ_dyn_top_continuous_subtype_SI_of_unique_on` is the selector
itself. This is the form a value-class certificate supplies
(`ValueClass2.sender_unique_on`). -/
theorem dynamicTopRealizedRule_continuousOn_of_argmaxUniqueOnI
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUniqueOnI E.V_S)
    {a b : ℝ} (hsub : Set.Icc a b ⊆ (Sanctions.S : Set ℝ)) :
    ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b) := by
  have hg : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top E.V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) :=
    p.σ_dyn_top_continuous_subtype_SI_of_unique_on E.V_S hUniq
  have hmap : Continuous (fun x : ℝ => (Sanctions.clipS' x, E.α x)) :=
    Sanctions.clipS'_continuous.prodMk E.hα
  have hcomp : Continuous (fun x : ℝ =>
      p.σ_dyn_top E.V_S (Sanctions.clipS' x).val
        (Set.projIcc (0 : ℝ) 1 zero_le_one (E.α x) : ℝ)) := hg.comp hmap
  refine hcomp.continuousOn.congr ?_
  intro x hx
  simp only [AbstractGame.Params.dynamicTopRealizedRule,
    Sanctions.clipS'_val_eq_of_mem (hsub hx),
    Set.projIcc_of_mem zero_le_one (E.α_mem x (hsub hx))]

/-- **Continuity of the realized equilibrium rule, from argmax uniqueness.**

If the Sender's dynamic argmax against `E.V_S` is single-valued, then the
realized equilibrium rule `x ↦ σ_dyn_top E.V_S x (E.α x)` is continuous on any
feasible interval. Uniqueness supplies continuity of the selector; the
equilibrium's own field `E.hα` supplies continuity of the Target policy.

`DynamicArgmaxUnique` is an existing project predicate. Since round BJ4.3 the
value-class certificates carry only its compliance-local form, which the sibling
`dynamicTopRealizedRule_continuousOn_of_argmaxUniqueOnI` reads; this full form is
a corollary of it.

Since round BJ4.3 (2026-10-08) a corollary of the compliance-local
`dynamicTopRealizedRule_continuousOn_of_argmaxUniqueOnI` at `hUniq.toOnI`;
statement unchanged. -/
theorem dynamicTopRealizedRule_continuousOn_of_argmaxUnique
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S)
    {a b : ℝ} (hsub : Set.Icc a b ⊆ (Sanctions.S : Set ℝ)) :
    ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b) :=
  p.dynamicTopRealizedRule_continuousOn_of_argmaxUniqueOnI E hUniq.toOnI hsub

/-- **Conditional equilibrium attraction at the absorbing corner, with
continuity and strict direction discharged.**

Both *regularity* conditions are derived rather than assumed: continuity from
`DynamicArgmaxUnique` — single-valuedness of the Sender's dynamic argmax — and
the strict ratchet from the persistence level condition with a floor at the top
state.

What is still assumed, and must be read as part of the claim:

* `hAdj` — `StrictAdjustment`, the structural sign condition on `p.F`. It is a
  `Params`-level condition discharged at explicit witnesses; **no persistence
  package supplies it**.
* `hrule_mono` and `hmaps` — monotonicity of the realized rule on the basin and
  invariance of the basin under the closed loop. These the persistence machinery
  does supply (`SenderPersistenceBasinTop.top_rule_mono`, and
  `dynamicTopLockInStepF_mem_basin` from the same level condition).
* `h_level_top` — the top floor, which as noted above pins `R x = 1` throughout
  the basin. This is the absorbing corner, not the interior case.

So this is *conditional* attraction at the corner, not unconditional attraction
in general. The interior statement — a floor strictly below the basin's right
endpoint — remains open. -/
theorem equilibriumTop_tendsto_one_of_argmaxUnique_and_top_floor
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {xbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x 1 ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar (1 : ℝ)) :
    Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop (𝓝 1) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
        (𝓝 1) := by
  have hsub : Set.Icc xbar (1 : ℝ) ⊆ (Sanctions.S : Set ℝ) := by
    intro y hy
    exact ⟨le_trans hxbar0 hy.1, hy.2⟩
  exact p.equilibriumTop_tendsto_one_of_top_level_floor hAdj E hxbar0 hxbar1
    hrule_mono (p.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E hUniq hsub)
    hmaps h_level_top hx₀

/-! ## Round 5 — two basins, one equilibrium

The capstone the paper's dual-basin claim needs. There is a **single**
equilibrium `E` and therefore a single equilibrium-induced rule; the two
intervals are two invariant regions of that one rule. The initial state selects
which named limit the path reaches. Nothing here concerns multiplicity of
equilibria, switching between equilibria, expectation-driven selection,
stochastic metastability, genericity, or structural stability, and none of those
follows from it. -/

/-- **History-dependent long-run outcomes within one equilibrium rule.**

One equilibrium `E`. A low interval on which the realized rule lies strictly
below the diagonal above its left endpoint, and a high interval, disjoint from
and above it, on which the rule lies strictly above the diagonal below its right
endpoint. Then every equilibrium path from the low interval converges — state
and realized sanction alike — to the low endpoint, every path from the high
interval converges to the high endpoint, and the two limits are distinct.

The economic reading is history dependence: the initial political state, not a
change of equilibrium, decides which long-run outcome is reached. -/
theorem equilibriumTop_twoBasin_tendsto
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {aL bL aH bH : ℝ}
    (hL : aL ≤ bL) (hH : aH ≤ bH) (hsep : bL < aH)
    (haL0 : 0 ≤ aL) (hbH1 : bH ≤ 1)
    (hmonoL : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc aL bL))
    (hcontL : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc aL bL))
    (hmapsL : ∀ x ∈ Set.Icc aL bL,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc aL bL)
    (hstrictL : ∀ x ∈ Set.Ioc aL bL,
      p.dynamicTopRealizedRule E.V_S E.α x < x)
    (hmonoH : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc aH bH))
    (hcontH : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc aH bH))
    (hmapsH : ∀ x ∈ Set.Icc aH bH,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc aH bH)
    (hstrictH : ∀ x ∈ Set.Ico aH bH,
      x < p.dynamicTopRealizedRule E.V_S E.α x) :
    (∀ x₀ ∈ Set.Icc aL bL,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 aL) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 aL)) ∧
      (∀ x₀ ∈ Set.Icc aH bH,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 bH) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 bH)) ∧
      aL < bH := by
  have hbL1 : bL ≤ 1 := le_trans (le_of_lt hsep) (le_trans hH hbH1)
  have haH0 : 0 ≤ aH := le_trans haL0 (le_trans hL (le_of_lt hsep))
  refine ⟨fun x₀ hx₀ =>
      p.equilibriumTop_tendsto_left_endpoint hAdj E hL haL0 hbL1 hmonoL hcontL
        hmapsL hstrictL hx₀,
    fun x₀ hx₀ =>
      p.equilibriumTop_tendsto_right_endpoint hAdj E hH haH0 hbH1 hmonoH hcontH
        hmapsH hstrictH hx₀,
    ?_⟩
  exact lt_of_le_of_lt hL (lt_of_lt_of_le hsep hH)

/-! ## Phase 2 — order selection at the model level, general in `p.F`

Everything before this point needs the closed loop's rest point to be **unique**
on the basin, or needs a **strict** sign condition strong enough to force
uniqueness. Neither is available in the interior case, and
`weak_level_condition_insufficient` shows the weak level condition cannot supply
either.

The theorems here need neither. They carry the abstract order-selection results
(`Foundations/MonotoneAttraction.lean`, targets A1–A3) across to the closed loop
`G(x) = F(x, R(x))`, so the conclusion becomes: whichever way the state first
moves, it converges to the extremal rest point on that side. Several rest points
in the basin are fine.

The bridge is the direction transfer below. It is short, and it is the only place
the transition's own axioms are used: `F_diag` (a sanction equal to the state
leaves the state unchanged) and `F_mono_s` (higher sanctions do not lower the
next state) turn a sanction-side inequality into a state-side one. -/

/-- **Rule-11: the weak transition axioms cannot deliver a strict step.**

Diagonal fixation and monotonicity in the sanction are compatible with a
transition that never moves at all — `F x s = x`. So the strict halves of the
direction transfer genuinely need `StrictAdjustment`, and cannot be obtained by
strengthening the conclusion of the weak halves.

Stated over a bare `F : ℝ → ℝ → ℝ` carrying only the two axioms in question, so
that the refutation is about those axioms and not about one economy. -/
theorem diagonal_and_sanction_monotone_insufficient_for_strict_step :
    ¬ ∀ (F : ℝ → ℝ → ℝ), (∀ x, F x x = x) → (∀ x, Monotone (F x)) →
        ∀ x s : ℝ, x < s → x < F x s := by
  intro h
  have hbad := h (fun x _ => x) (fun _ => rfl) (fun _ _ _ _ => le_rfl) 0 1
    (by norm_num)
  exact absurd hbad (lt_irrefl 0)

/-- **B1 (up, weak) — a sanction at or above the state does not lower it.**

`G x = F(x, R x) ≥ F(x, x) = x`, by monotonicity of the transition in the
sanction and diagonal fixation. No feasibility hypothesis is needed: `F_mono_s`
is monotonicity on all of `ℝ`. -/
theorem self_le_stepF_of_self_le_rule
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x : ℝ}
    (h : x ≤ p.dynamicTopRealizedRule V_S α x) :
    x ≤ p.dynamicTopLockInStepF V_S α x := by
  have hmono : p.F x x ≤ p.F x (p.dynamicTopRealizedRule V_S α x) :=
    p.F_mono_s x h
  rwa [p.F_diag x] at hmono

/-- **B1 (down, weak) — a sanction at or below the state does not raise it.** -/
theorem stepF_le_self_of_rule_le_self
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x : ℝ}
    (h : p.dynamicTopRealizedRule V_S α x ≤ x) :
    p.dynamicTopLockInStepF V_S α x ≤ x := by
  have hmono : p.F x (p.dynamicTopRealizedRule V_S α x) ≤ p.F x x :=
    p.F_mono_s x h
  rwa [p.F_diag x] at hmono

/-- **B1 (up, strict) — a sanction strictly above the state strictly raises it.**

This is exactly `StrictAdjustment`, with the realized rule's own feasibility
(`dynamicTopRealizedRule_mem`) discharging the sanction-side membership. -/
theorem self_lt_stepF_of_self_lt_rule
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Sanctions.I) (h : x < p.dynamicTopRealizedRule V_S α x) :
    x < p.dynamicTopLockInStepF V_S α x :=
  hAdj.self_lt_F_of_lt_s hx (p.dynamicTopRealizedRule_mem V_S α x) h

/-- **B1 (down, strict) — a sanction strictly below the state strictly lowers
it.** -/
theorem stepF_lt_self_of_rule_lt_self
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Sanctions.I) (h : p.dynamicTopRealizedRule V_S α x < x) :
    p.dynamicTopLockInStepF V_S α x < x :=
  hAdj.F_lt_self_of_s_lt hx (p.dynamicTopRealizedRule_mem V_S α x) h

/-- **B2 (up), closed-loop form — a state whose equilibrium sanction is at or
above it converges to the lowest rest point above it, given a monotone closed
loop (round BH-2, 2026-10-06, BH2.7).**

No uniqueness hypothesis, and no strict sign condition. The basin may contain any
number of rest points; the path settles at the first one at or above where it
started.

Dropped relative to `dynamicTopLockInPathF_tendsto_least_fixedPoint_above`:
monotonicity of the realized rule `R` is replaced by monotonicity of the closed
loop `G(x) = F(x, R x)` on `[a, b]`, which is all the abstract iteration theorem
reads. Rule monotonicity implies closed-loop monotonicity
(`dynamicTopLockInStepF_monotoneOn`), and not conversely as a predicate
(`exists_closedLoopMono_without_monotone_rule`). General in `F`. -/
theorem dynamicTopLockInPathF_tendsto_least_fixedPoint_above_of_stepMonotoneOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hstep_mono : MonotoneOn (p.dynamicTopLockInStepF V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hup : x₀ ≤ p.dynamicTopRealizedRule V_S α x₀) :
    ∃ x_star ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α x_star = x_star ∧ x₀ ≤ x_star ∧
      (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α y = y → x₀ ≤ y →
        x_star ≤ y) ∧
      Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
        (𝓝 x_star) :=
  Sanctions.MonotoneAttraction.monotoneOn_orbit_tendsto_least_fixedPoint_above
    hab hstep_mono
    (p.dynamicTopLockInStepF_continuousOn V_S α hrule_cont) hmaps hx₀
    (p.self_le_stepF_of_self_le_rule V_S α hup)

/-- **B2 (down), closed-loop form — a state whose equilibrium sanction is at or
below it converges to the highest rest point below it, given a monotone closed
loop (round BH-2, 2026-10-06, BH2.7).** The wash-out mirror. Monotonicity of the
realized rule is replaced by monotonicity of the closed loop on `[a, b]`.
General in `F`. -/
theorem dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below_of_stepMonotoneOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hstep_mono : MonotoneOn (p.dynamicTopLockInStepF V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hdown : p.dynamicTopRealizedRule V_S α x₀ ≤ x₀) :
    ∃ x_star ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α x_star = x_star ∧ x_star ≤ x₀ ∧
      (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α y = y → y ≤ x₀ →
        y ≤ x_star) ∧
      Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
        (𝓝 x_star) :=
  Sanctions.MonotoneAttraction.monotoneOn_orbit_tendsto_greatest_fixedPoint_below
    hab hstep_mono
    (p.dynamicTopLockInStepF_continuousOn V_S α hrule_cont) hmaps hx₀
    (p.stepF_le_self_of_rule_le_self V_S α hdown)

/-- **B2 (up) — a state whose equilibrium sanction is at or above it converges
to the lowest rest point above it.**

No uniqueness hypothesis, and no strict sign condition. The basin may contain any
number of rest points; the path settles at the first one at or above where it
started. Since round BH-2 a one-line corollary of the closed-loop form
`dynamicTopLockInPathF_tendsto_least_fixedPoint_above_of_stepMonotoneOn`, through
`dynamicTopLockInStepF_monotoneOn`. -/
theorem dynamicTopLockInPathF_tendsto_least_fixedPoint_above
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hup : x₀ ≤ p.dynamicTopRealizedRule V_S α x₀) :
    ∃ x_star ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α x_star = x_star ∧ x₀ ≤ x_star ∧
      (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α y = y → x₀ ≤ y →
        x_star ≤ y) ∧
      Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
        (𝓝 x_star) :=
  p.dynamicTopLockInPathF_tendsto_least_fixedPoint_above_of_stepMonotoneOn V_S α hab
    (p.dynamicTopLockInStepF_monotoneOn V_S α hrule_mono) hrule_cont hmaps hx₀ hup

/-- **B2 (down) — a state whose equilibrium sanction is at or below it converges
to the highest rest point below it.** The wash-out mirror. Since round BH-2 a
one-line corollary of
`dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below_of_stepMonotoneOn`. -/
theorem dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hdown : p.dynamicTopRealizedRule V_S α x₀ ≤ x₀) :
    ∃ x_star ∈ Set.Icc a b,
      p.dynamicTopLockInStepF V_S α x_star = x_star ∧ x_star ≤ x₀ ∧
      (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α y = y → y ≤ x₀ →
        y ≤ x_star) ∧
      Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
        (𝓝 x_star) :=
  p.dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below_of_stepMonotoneOn V_S α hab
    (p.dynamicTopLockInStepF_monotoneOn V_S α hrule_mono) hrule_cont hmaps hx₀ hdown

/-- **B2 — the complete classification at the model level.**

`le_total` makes the two cases exhaustive, so this says: for *every* starting
state in a basin the closed loop preserves, the equilibrium sanction's position
relative to the state at date zero already determines which rest point the
economy ends at, and it is the extremal one on that side. Nothing is assumed
about how many rest points the basin holds. -/
theorem dynamicTopLockInPathF_tendsto_order_selected_fixedPoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule V_S α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF V_S α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
          (𝓝 x_star)) ∧
    (p.dynamicTopRealizedRule V_S α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF V_S α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
          (𝓝 x_star)) :=
  ⟨fun hup => p.dynamicTopLockInPathF_tendsto_least_fixedPoint_above V_S α hab
      hrule_mono hrule_cont hmaps hx₀ hup,
   fun hdown => p.dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below V_S α
      hab hrule_mono hrule_cont hmaps hx₀ hdown⟩

/-! ### B3 — the sanction limit, in two separate steps

The plan's discipline: prove the honest conclusion first, and identify the limit
only afterwards, from a genuinely separate hypothesis. Merging them hides which
half needs `StrictAdjustment`. -/

/-- **B3, step one (honest) — the sanction path converges to the rule's value at
the state limit.**

Pure continuity: the sanction path is the realized rule evaluated along the state
path, so a converging state path carries the rule's value with it. **No claim is
made that this limit equals the state limit** — that is step two, and it needs a
hypothesis this statement does not have. -/
theorem dynamicTopLockInSanctionsF_tendsto_rule_at_limit
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b x_star : ℝ}
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
    (hstar : x_star ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hpath : Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
      (𝓝 x_star)) :
    Filter.Tendsto (p.dynamicTopLockInSanctionsF V_S α x₀) Filter.atTop
      (𝓝 (p.dynamicTopRealizedRule V_S α x_star)) := by
  have hmem : ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc a b :=
    Sanctions.MonotoneAttraction.orbit_mem_Icc hmaps hx₀
  have hwithin :
      Filter.Tendsto (p.dynamicTopLockInPathF V_S α x₀) Filter.atTop
        (nhdsWithin x_star (Set.Icc a b)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpath
      (Filter.Eventually.of_forall hmem)
  exact (hrule_cont x_star hstar).tendsto.comp hwithin

/-- **B3, step two (identification) — at a closed-loop rest point the sanction
equals the state.**

This is where `StrictAdjustment` enters, and it is the whole of its role here: a
state the closed loop leaves unchanged can only be one at which the sanction is
not pulling in either direction. Combined with step one, states and sanctions
converge to the *same* selected rest point. -/
theorem realizedRule_eq_self_of_stepF_fixed
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Sanctions.I)
    (hfix : p.dynamicTopLockInStepF V_S α x = x) :
    p.dynamicTopRealizedRule V_S α x = x :=
  (p.dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment
    hAdj V_S α hx).mp hfix

/-! ## Phase 3 — order selection at an actual equilibrium

The capstones. Each consumes `E : p.FeedbackStackelbergEquilibriumTop`, whose
fields carry both players' Bellman optimality and feasibility, and reads the
value function and policy off that object. Continuity is discharged from
`DynamicArgmaxUnique E.V_S`, single-valuedness of the Sender's dynamic argmax, so
continuity itself is not a hypothesis here; compliance-local uniqueness, the form
a value-class certificate carries since round BJ4.3, suffices for that discharge
(`dynamicTopRealizedRule_continuousOn_of_argmaxUniqueOnI`).

### Order selection is *not* basin-wide attraction. Keep the two apart.

This is the distinction the whole section turns on, and getting it wrong is easy
because both conclusions are `Tendsto` statements.

* **Order selection** (this section). The limit `x_star` is bound *inside* the
  conclusion, after the starting state `x₀`, so it may depend on `x₀`. The claim
  is that *each* orbit converges, and that its limit is the extremal rest point
  on the side the orbit first moved. It does **not** say two different starting
  states share a limit.
* **Attraction to a common named point** (Target D above, and the threshold
  results in Phase 6). One point, one `Tendsto` for every start in the basin.

The identity map separates them: every orbit converges to its own order-selected
rest point — itself — and no point attracts a neighbourhood.
`MonotoneAttraction.nonunique_fixedPoint_breaks_named_limit` is that refutation,
and it is why a strict sign condition, fixed-point uniqueness, or some other
isolation condition is still needed whenever the paper wants a common limit.

### The hypotheses, sorted by what they are for

Keeping these two groups apart is what the three tiers of `C1` are for.

**For order selection itself** — monotonicity of the realized rule on the basin
(`SenderPersistenceBasinTop.top_rule_mono`, from P3), invariance of the basin
(`dynamicTopLockInStepF_mem_basin`, from the level condition), and continuity of
the realized rule. Continuity is a genuine mathematical requirement;
`DynamicArgmaxUnique` is one economic condition that supplies it, which is why
tier 1 takes continuity directly and tier 2 discharges it. Rule monotonicity is
read only through monotonicity of the closed loop
(`dynamicTopLockInStepF_monotoneOn`); since round BH-2 the tier-1 theorems have
closed-loop siblings (`..._of_stepMonotoneOn`) that assume that weaker condition
directly.

**For identifying the sanction limit with the state limit** — `StrictAdjustment`
alone, in tier 3. It contributes nothing to where the political state goes.

`p.F` is free of any *functional form* throughout, which is a different and weaker
statement than unrestricted: `StrictAdjustment` is a structural sign condition on
it, and no persistence package supplies that.

### A caution for manuscript promotion

`DynamicArgmaxUnique` is an existing project predicate, so nothing here widens the
`Params` surface. It is **not** a field of `SenderPersistencePackage`, and it is
not assumed by the manuscript's current long-run proposition, whose Lean backing
`dynamicTopLockInPathF_tendsto_steadyState` needs neither it nor rule
monotonicity nor rule continuity. So these theorems do **not** dominate that
proposition: they draw a sharper conclusion under more regularity. Promoting them
widens the paper-facing assumption surface for that claim even though it widens
nothing in Lean. -/

/-- **C1 (tier 1) — order-selected convergence from continuity of the realized
rule alone.**

The mathematical requirement, stated as a mathematical requirement. Monotonicity
and continuity of the equilibrium realized rule on a preserved interval, and
nothing else: no argmax-uniqueness condition, no condition on the transition
beyond its maintained fields, and not even feasibility of the interval.

If the equilibrium sanction at the starting state is at or above it, the political
state converges to the *lowest* equilibrium rest point at or above where it
started; if at or below, to the *highest* at or below. The realized sanction
converges to the rule's value at that limit.

Tiers 2 and 3 below each replace or add hypotheses, and each buys exactly one
thing. Tier 2 **trades** the continuity hypothesis for `DynamicArgmaxUnique`
*plus* the physical-domain bounds `0 ≤ a` and `b ≤ 1` — three signature changes,
not one, because argmax uniqueness is a condition on physical states and the
interval must lie among them. Tier 3 adds `StrictAdjustment`, which identifies
the sanction limit with the state limit.

Separating the tiers keeps the mathematics from being read as economics:
continuity of the realized rule is what the argument needs, and argmax
uniqueness is one economic condition that supplies it.

**This is selection, not attraction.** `x_star` is bound after `x₀` and may depend
on it; see the section header, and `MonotoneAttraction.attraction_iff_unique_fixedPoint`
for the exact price of upgrading.

Rule monotonicity is read only through monotonicity of the closed loop; the
closed-loop sibling `equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn`
(round BH-2) assumes that weaker condition directly and drops `a ≤ b`. This
statement is unchanged (pinned headline row). -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ} (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) := by
  constructor
  · intro hup
    obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path⟩ :=
      p.dynamicTopLockInPathF_tendsto_least_fixedPoint_above E.V_S E.α hab
        hrule_mono hrule_cont hmaps hx₀ hup
    exact ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path,
      p.dynamicTopLockInSanctionsF_tendsto_rule_at_limit E.V_S E.α hrule_cont
        hmaps hz_mem hx₀ hz_path⟩
  · intro hdown
    obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path⟩ :=
      p.dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below E.V_S E.α hab
        hrule_mono hrule_cont hmaps hx₀ hdown
    exact ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path,
      p.dynamicTopLockInSanctionsF_tendsto_rule_at_limit E.V_S E.α hrule_cont
        hmaps hz_mem hx₀ hz_path⟩

/-- **C1 (tier 1, identified) — the continuity-tier selection with the two
limits identified by strict adjustment.**

This is the corollary the manuscript states after the order-selection
proposition (`cor:order-selection-identified`): under the *continuity-tier*
hypotheses — a monotone, continuous realized rule on a feasible invariant
interval — and strict directional adjustment `(F5)`, the political state and
the realized sanction converge to the **same** order-selected rest point.

It is the composition of the two branches of
`equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` with the
identification step `realizedRule_eq_self_of_stepF_fixed`, and nothing else.
In particular it does **not** consume `DynamicArgmaxUnique`: continuity is
taken directly, as the manuscript's proposition takes it, so this wrapper is
the exact statement backing the corollary. Tier 3 below
(`equilibriumTop_tendsto_order_selected_fixedPoint`) reaches the same
conclusion by discharging continuity from argmax uniqueness instead; the two
are siblings with different hypothesis surfaces, not a strengthening of one
another. The feasibility bounds `0 ≤ a`, `b ≤ 1` enter only through the
identification step, which is stated on physical states.

**This is selection, not attraction.** `x_star` is bound after `x₀` and may
depend on it; see the section header.

Closed-loop sibling (round BH-2):
`equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn`,
which assumes monotonicity of the closed loop instead of the realized rule and
drops `a ≤ b`. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_continuousOn
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) := by
  have hsub : Set.Icc a b ⊆ Sanctions.I := fun y hy =>
    ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  obtain ⟨hu, hd⟩ :=
    p.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn E hab
      hrule_mono hrule_cont hmaps hx₀
  constructor
  · intro hup
    obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path, hz_sanc⟩ := hu hup
    rw [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α (hsub hz_mem) hz_fix]
      at hz_sanc
    exact ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path, hz_sanc⟩
  · intro hdown
    obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path, hz_sanc⟩ := hd hdown
    rw [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α (hsub hz_mem) hz_fix]
      at hz_sanc
    exact ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path, hz_sanc⟩

/-! ### C1, closed-loop form (round BH-2, 2026-10-06, BH2.7)

The two tier-1 theorems above read monotonicity of the realized rule `R_E` only
through monotonicity of the closed loop `G_E(x) = F(x, R_E x)`
(`dynamicTopLockInStepF_monotoneOn`, from `F_mono_x` and `F_mono_s`). The
siblings below assume that closed-loop condition directly, and also drop
`a ≤ b`, which the start `x₀ ∈ [a, b]` implies. The tier-1 statements are
unchanged; the primed siblings in the Round L section are now one-line
corollaries of these.

**Scope (Rule 9B).** As a predicate, closed-loop monotonicity is strictly weaker
than rule monotonicity: `exists_closedLoopMono_without_monotone_rule` exhibits a
feasible rule, in the maintained transition class, whose closed loop is
monotone although the rule is not. That rule is a comparison object, not the
realized rule of an equilibrium; no economy in the tree exhibits an equilibrium
whose closed loop is monotone while its realized rule is not. So these theorems
state a weaker sufficient condition; that they cover strictly more equilibria
is unwitnessed. -/

/-- **C1 (tier 1), closed-loop form — order-selected convergence from a monotone
closed loop and a continuous realized rule.**

At an actual equilibrium `E`, on an interval `[a, b]` that the closed loop
`G_E(x) = F(x, R_E x)` maps into itself and on which `G_E` is non-decreasing and
the realized rule `R_E` is continuous: if the equilibrium sanction at the start
is at or above the state, the political state converges to the lowest rest point
at or above where it started; if at or below, to the highest rest point at or
below. The realized sanction converges to the rule's value at that limit.

In plain terms: whichever way the political state first moves, it keeps moving
that way until the first steady state on that side, provided that a higher state
today never leads to a lower state tomorrow under the equilibrium rule.

Dropped relative to
`equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn`: monotonicity
of the realized rule (replaced by the implied, weaker monotonicity of the closed
loop) and `a ≤ b`. **This is selection, not attraction**: `x_star` is bound
after `x₀`. General in `F`. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (hstep_mono : MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) := by
  have hab : a ≤ b := hx₀.1.trans hx₀.2
  constructor
  · intro hup
    obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path⟩ :=
      p.dynamicTopLockInPathF_tendsto_least_fixedPoint_above_of_stepMonotoneOn E.V_S
        E.α hab hstep_mono hrule_cont hmaps hx₀ hup
    exact ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path,
      p.dynamicTopLockInSanctionsF_tendsto_rule_at_limit E.V_S E.α hrule_cont
        hmaps hz_mem hx₀ hz_path⟩
  · intro hdown
    obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path⟩ :=
      p.dynamicTopLockInPathF_tendsto_greatest_fixedPoint_below_of_stepMonotoneOn E.V_S
        E.α hab hstep_mono hrule_cont hmaps hx₀ hdown
    exact ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path,
      p.dynamicTopLockInSanctionsF_tendsto_rule_at_limit E.V_S E.α hrule_cont
        hmaps hz_mem hx₀ hz_path⟩

/-- **C1 (tier 1, identified), closed-loop form — the two limits identified by
strict adjustment.**

Under a monotone closed loop, a continuous realized rule on a feasible invariant
interval `[a, b] ⊆ [0, 1]`, and strict directional adjustment `(F5)`, the
political state and the realized sanction converge to the **same**
order-selected rest point.

Dropped relative to
`equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_continuousOn`:
monotonicity of the realized rule (replaced by the implied, weaker monotonicity
of the closed loop) and `a ≤ b`. **This is selection, not attraction.** General
in `F`. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hstep_mono : MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) := by
  have hsub : Set.Icc a b ⊆ Sanctions.I := fun y hy =>
    ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  obtain ⟨hu, hd⟩ :=
    p.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn E hstep_mono
      hrule_cont hmaps hx₀
  constructor
  · intro hup
    obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path, hz_sanc⟩ := hu hup
    rw [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α (hsub hz_mem) hz_fix]
      at hz_sanc
    exact ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path, hz_sanc⟩
  · intro hdown
    obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path, hz_sanc⟩ := hd hdown
    rw [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α (hsub hz_mem) hz_fix]
      at hz_sanc
    exact ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path, hz_sanc⟩

/-- **C1 (tier 2) — the same, with continuity discharged from argmax
uniqueness.**

For every starting state in a basin the equilibrium closed loop preserves: if the
equilibrium sanction at that state is at or above it, the political state
converges to the *lowest* equilibrium rest point at or above where it started; if
at or below, to the *highest* rest point at or below. The two cases are
exhaustive. The realized sanction converges to the rule's value **at that limit**,
`R(x_star)` — this form makes no claim that the two limits coincide.

Single-valuedness of the Sender's dynamic argmax makes the realized rule
continuous on any feasible interval, so this is tier 1 with its regularity
hypothesis supplied by argmax uniqueness rather than assumed (compliance-local
uniqueness suffices: `dynamicTopRealizedRule_continuousOn_of_argmaxUniqueOnI`).
Feasibility of `[a,b]` enters only for that discharge.

`StrictAdjustment` is still absent, deliberately. Comparing this statement with
`equilibriumTop_tendsto_order_selected_fixedPoint` below shows exactly what that
condition buys: nothing about where the state goes, and everything about whether
the sanction ends up at the same place.

**This is selection, not attraction.** `x_star` is bound after `x₀` and may
depend on it; see the section header. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_and_rule_limit
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) := by
  have hsub : Set.Icc a b ⊆ (Sanctions.S : Set ℝ) := fun y hy =>
    ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  exact p.equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn E hab
    hrule_mono (p.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E hUniq hsub)
    hmaps hx₀

/-- **C1 (tier 3) — order-selected convergence with the two limits identified.**

The corollary of the theorem above under `StrictAdjustment`: at a rest point of
the closed loop the sanction equals the state, so the realized sanction converges
to the *same* value as the political state rather than merely to the rule's value
there. Everything else is unchanged.

The economic reading is that history — the inherited political state — selects
among the equilibrium's long-run outcomes, within a single equilibrium rule.

**Three things this does not say**, all of which the earlier draft of this
docstring blurred.

1. It is **not** attraction to a common point. The limit is chosen after the
   starting state and may differ across starting states; see the section header
   and `MonotoneAttraction.nonunique_fixedPoint_breaks_named_limit`.
   Under the maintained monotonicity, continuity and invariance conditions,
   attraction of a whole basin to one limit is **equivalent** to that basin
   containing a unique rest point (`MonotoneAttraction.attraction_iff_unique_fixedPoint`),
   and equivalent again to the strict sign condition off the limit
   (`..._iff_strictly_signed`). Local isolation of the candidate limit does not
   suffice.
2. `p.F` is unrestricted in *functional form* only. `hAdj` is a genuine
   structural condition on it, and no persistence package supplies it.
3. It says nothing about rates, Lyapunov stability, or robustness under
   perturbation of the primitives.

What it does say: no hypothesis about how many rest points the basin holds, no
strict sign condition, no named endpoint, no numeral.

**Attribution.** The order-theoretic step is classical monotone iteration — Amann
(1976) Theorem 6.1 and Corollary 6.2, in an ordered Banach space. What is new
here is the equilibrium-level statement: carrying that step across a transition
generated by a forward-looking political equilibrium, taking monotonicity and
invariance from equilibrium restrictions rather than assuming them, and keeping
the convergence of the political state separate from the convergence of the
sanction. See the attribution section in
`Foundations/MonotoneAttraction.lean`. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) := by
  have hsub : Set.Icc a b ⊆ (Sanctions.S : Set ℝ) := fun y hy =>
    ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  obtain ⟨hu, hd⟩ :=
    p.equilibriumTop_tendsto_order_selected_fixedPoint_and_rule_limit E hUniq hab
      ha0 hb1 hrule_mono hmaps hx₀
  constructor
  · intro hup
    obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path, hz_sanc⟩ := hu hup
    rw [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α (hsub hz_mem) hz_fix]
      at hz_sanc
    exact ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_path, hz_sanc⟩
  · intro hdown
    obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path, hz_sanc⟩ := hd hdown
    rw [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α (hsub hz_mem) hz_fix]
      at hz_sanc
    exact ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_path, hz_sanc⟩

/-- **C2 — dual-basin path dependence with the limits derived, not named.**

One equilibrium, two disjoint invariant basins. Every path converges — state and
realized sanction alike — to a rest point *of its own basin*, and because the
basins are separated the two long-run outcomes are necessarily distinct.

The strengthening over `equilibriumTop_twoBasin_tendsto` is that the limits are
no longer supplied as hand-selected endpoints, and **no strict sign condition is
assumed on either basin**. The wash-out hypothesis on the low interval and the
ratchet hypothesis on the high one are both gone. What produces two different
long-run outcomes is only the separation of the two invariant regions; which
outcome an economy reaches is decided by which region its initial political state
lies in. -/
theorem equilibriumTop_twoBasin_order_selected
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {aL bL aH bH : ℝ}
    (hL : aL ≤ bL) (hH : aH ≤ bH) (hsep : bL < aH)
    (haL0 : 0 ≤ aL) (hbH1 : bH ≤ 1)
    (hmonoL : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc aL bL))
    (hmapsL : ∀ x ∈ Set.Icc aL bL,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc aL bL)
    (hmonoH : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc aH bH))
    (hmapsH : ∀ x ∈ Set.Icc aH bH,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc aH bH)
    {xL₀ xH₀ : ℝ} (hxL₀ : xL₀ ∈ Set.Icc aL bL) (hxH₀ : xH₀ ∈ Set.Icc aH bH) :
    ∃ xL ∈ Set.Icc aL bL, ∃ xH ∈ Set.Icc aH bH,
      p.dynamicTopLockInStepF E.V_S E.α xL = xL ∧
      p.dynamicTopLockInStepF E.V_S E.α xH = xH ∧
      Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α xL₀) Filter.atTop
        (𝓝 xL) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α xL₀) Filter.atTop
        (𝓝 xL) ∧
      Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α xH₀) Filter.atTop
        (𝓝 xH) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α xH₀) Filter.atTop
        (𝓝 xH) ∧
      xL < xH := by
  have hbL1 : bL ≤ 1 := le_trans (le_of_lt hsep) (le_trans hH hbH1)
  have haH0 : 0 ≤ aH := le_trans haL0 (le_trans hL (le_of_lt hsep))
  obtain ⟨zL, hzL_mem, hzL_fix, hzL_path, hzL_sanc⟩ :
      ∃ z ∈ Set.Icc aL bL, p.dynamicTopLockInStepF E.V_S E.α z = z ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α xL₀) Filter.atTop
          (𝓝 z) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α xL₀)
          Filter.atTop (𝓝 z) := by
    rcases le_total xL₀ (p.dynamicTopRealizedRule E.V_S E.α xL₀) with hup | hdown
    · obtain ⟨z, hz_mem, hz_fix, -, -, hz_path, hz_sanc⟩ :=
        (p.equilibriumTop_tendsto_order_selected_fixedPoint hAdj E hUniq hL haL0
          hbL1 hmonoL hmapsL hxL₀).1 hup
      exact ⟨z, hz_mem, hz_fix, hz_path, hz_sanc⟩
    · obtain ⟨z, hz_mem, hz_fix, -, -, hz_path, hz_sanc⟩ :=
        (p.equilibriumTop_tendsto_order_selected_fixedPoint hAdj E hUniq hL haL0
          hbL1 hmonoL hmapsL hxL₀).2 hdown
      exact ⟨z, hz_mem, hz_fix, hz_path, hz_sanc⟩
  obtain ⟨zH, hzH_mem, hzH_fix, hzH_path, hzH_sanc⟩ :
      ∃ z ∈ Set.Icc aH bH, p.dynamicTopLockInStepF E.V_S E.α z = z ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α xH₀) Filter.atTop
          (𝓝 z) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α xH₀)
          Filter.atTop (𝓝 z) := by
    rcases le_total xH₀ (p.dynamicTopRealizedRule E.V_S E.α xH₀) with hup | hdown
    · obtain ⟨z, hz_mem, hz_fix, -, -, hz_path, hz_sanc⟩ :=
        (p.equilibriumTop_tendsto_order_selected_fixedPoint hAdj E hUniq hH haH0
          hbH1 hmonoH hmapsH hxH₀).1 hup
      exact ⟨z, hz_mem, hz_fix, hz_path, hz_sanc⟩
    · obtain ⟨z, hz_mem, hz_fix, -, -, hz_path, hz_sanc⟩ :=
        (p.equilibriumTop_tendsto_order_selected_fixedPoint hAdj E hUniq hH haH0
          hbH1 hmonoH hmapsH hxH₀).2 hdown
      exact ⟨z, hz_mem, hz_fix, hz_path, hz_sanc⟩
  exact ⟨zL, hzL_mem, zH, hzH_mem, hzL_fix, hzH_fix, hzL_path, hzL_sanc,
    hzH_path, hzH_sanc,
    lt_of_le_of_lt hzL_mem.2 (lt_of_lt_of_le hsep hzH_mem.1)⟩

/-! ### C3 — the top-floor theorem, reclassified

`equilibriumTop_tendsto_one_of_argmaxUnique_and_top_floor` is retained. It is
**not** the main stability theorem: it is the absorbing-corner specialization of
`equilibriumTop_tendsto_order_selected_fixedPoint`, obtained by taking the basin
to be `[xbar, 1]` and the level floor to be `1`, which pins the realized rule at
the corner throughout. The corollary below records that relationship in Lean, so
the classification cannot drift back. -/

/-- **The top-floor case is the corner instance of order selection.**

With a floor at the top state the level condition gives `x ≤ R x` at every basin
state, so the upward branch of the general theorem applies at every starting
point, and the selected rest point is `1` because `1` is the only candidate at or
above a state whose rule already sits at `1`. Same conclusion as
`equilibriumTop_tendsto_one_of_argmaxUnique_and_top_floor`, derived from the
general result rather than proved separately. -/
theorem equilibriumTop_top_floor_is_corner_case_of_order_selection
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {xbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x 1 ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar (1 : ℝ)) :
    Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop (𝓝 1) ∧
      Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
        (𝓝 1) := by
  have hup : x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ :=
    le_trans (le_max_left x₀ 1) (h_level_top x₀ hx₀)
  obtain ⟨z, hz_mem, hz_fix, hz_ge, -, hz_path, hz_sanc⟩ :=
    (p.equilibriumTop_tendsto_order_selected_fixedPoint hAdj E hUniq hxbar1
      hxbar0 le_rfl hrule_mono hmaps hx₀).1 hup
  -- The selected rest point is `1`: at any basin state the floor forces the
  -- rule to the corner, and `StrictAdjustment` then forbids a rest point below.
  have hz1 : z = 1 := by
    by_contra hne
    have hzlt : z < 1 := lt_of_le_of_ne hz_mem.2 hne
    have hzI : z ∈ Sanctions.I :=
      ⟨le_trans hxbar0 hz_mem.1, hz_mem.2⟩
    have hrule_z : p.dynamicTopRealizedRule E.V_S E.α z = z :=
      p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α hzI hz_fix
    have hfloor : (1 : ℝ) ≤ p.dynamicTopRealizedRule E.V_S E.α z :=
      le_trans (le_max_right z 1) (h_level_top z hz_mem)
    rw [hrule_z] at hfloor
    exact absurd hfloor (not_le.mpr hzlt)
  exact ⟨hz1 ▸ hz_path, hz1 ▸ hz_sanc⟩

/-! ## Phase 4 — where strict interior direction comes from, and where it does not

The question this phase settles: given the weak level condition the persistence
machinery supplies (`x ≤ R x`), what does it take to upgrade it to `x < R x` in
the interior — on a basin whose sanction floor lies strictly below its right
endpoint?

**First, what the Phase-3 capstone does and does not remove.** The capstone
`equilibriumTop_tendsto_order_selected_fixedPoint` needs no strict condition, so
strictness is **not** required for *orbit convergence and order selection*: every
path settles, and its limit is the extremal rest point on the side it first
moved.

It is still required for *attraction to a common named limit*. Order selection
lets the limit depend on the starting state, and without an isolation condition
two starts in the same basin can settle at different rest points — the identity
map does exactly that. So the interior question is not closed and was never
closed by Phase 3. What changed is its scope: it is now the gap between
per-orbit selection and a common limit, not a gap in convergence itself.

**Second, the bridge, which is free.** Optimality alone converts any strictly
profitable deviation into strictness, given the weak level condition. That is
`self_lt_realizedRule_of_level_and_profitable_deviation` below: no new
hypothesis, no restriction on `F`, and the deviation need not even lie above the
state.

**Third, the obstruction, which is real.** What optimality does not supply is the
profitable deviation itself, and the existing persistence conditions cannot
supply it either. P5 constrains the Sender's objective on `[0, max x s̄]` and
nowhere else, so above the floor its range collapses to `[0, x]` — see
`subpivot_range_collapses_above_floor` and
`subpivot_strictMono_and_weak_level_insufficient_for_strict_ratchet` in
`Theory/Certificates/SubpivotChordNecessity.lean`, which exhibits a single-peaked
objective satisfying every consequence the current route extracts from P5 while
the ratchet stays weak. That refutes the route, not the raw hypothesis: no
complete `Params` economy satisfying P5 with weak-but-not-strict persistence has
been constructed.

No new assumption was introduced, and none is proposed here. The general
theorem does not need one for order selection; a paper claim of a common interior
attractor would need one, and that is a Rule-3 decision, not a proof gap to grind
at. -/

/-- **D1 — a strictly profitable deviation rules out resting at the state.**

If any feasible sanction `s` gives the Sender a strictly higher dynamic objective
at `x` than the sanction `x` itself does, then the equilibrium realized rule at
`x` is not `x`. Pure optimization logic: the realized rule is a maximizer, so it
weakly beats `s`, so it cannot be a point that `s` strictly beats.

`s` is **not** required to lie above `x`. Any profitable deviation whatever, in
either direction, is enough to move the rule off the diagonal. -/
theorem realizedRule_ne_self_of_profitable_deviation
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x s : ℝ}
    (hs : s ∈ Sanctions.I)
    (hgain : p.senderDynObjective V_S x (α x) x
        < p.senderDynObjective V_S x (α x) s) :
    p.dynamicTopRealizedRule V_S α x ≠ x := by
  intro hR
  have hmax := (p.σ_dyn_top_mem_dynamicArgmaxSet V_S x (α x)).2
  have h : p.senderDynObjective V_S x (α x) s
      ≤ p.senderDynObjective V_S x (α x) (p.σ_dyn_top V_S x (α x)) := hmax hs
  rw [show p.σ_dyn_top V_S x (α x) = x from hR] at h
  exact absurd h (not_le.mpr hgain)

/-- **D1 — the weak level condition plus any profitable deviation gives strict
persistence.**

The general optimization bridge from weak to strict persistence. It introduces no
assumption: `hlevel` is what the persistence machinery already delivers, and
`hgain` is a statement about the Sender's own objective, not a new primitive.

What it does *not* do is produce `hgain`. That is the whole of the interior
question, and Phase 4's obstruction results show the existing persistence
conditions do not answer it. -/
theorem self_lt_realizedRule_of_level_and_profitable_deviation
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {x s : ℝ}
    (hs : s ∈ Sanctions.I)
    (hlevel : x ≤ p.dynamicTopRealizedRule V_S α x)
    (hgain : p.senderDynObjective V_S x (α x) x
        < p.senderDynObjective V_S x (α x) s) :
    x < p.dynamicTopRealizedRule V_S α x :=
  lt_of_le_of_ne hlevel
    (Ne.symm (p.realizedRule_ne_self_of_profitable_deviation V_S α hs hgain))

/-! ## Phase 6 — the threshold, at an actual equilibrium

The abstract side (`Foundations/MonotoneAttraction.lean`, Phase 6) shows that a
point where the sign of `G x − x` changes is a rest point by continuity alone.
Carried across here, that says something the paper has been assuming: the
**threshold** between a wash-out region and a ratchet region is not a separate
object to be posited or calibrated. It is a steady state of the same equilibrium
closed loop, and it sits where it sits because that is where the equilibrium
sanction crosses the political state.

Both theorems below are stated in terms of the sign of `R x − x`, the position of
the *equilibrium sanction* relative to the *current political state*. That is the
economically legible primitive: below the threshold the Sender's optimal sanction
undershoots the inherited state and entrenchment erodes; above it the sanction
overshoots and entrenchment builds. `StrictAdjustment` carries each sign from the
sanction to the state, and continuity is discharged from `DynamicArgmaxUnique`. -/

/-- **The threshold is an equilibrium rest point, and the sanction there equals
the state.**

Where the equilibrium sanction crosses the political state — strictly below on
one side, strictly above on the other — the crossing point is fixed by the closed
loop, and the realized sanction at it equals the state itself. Neither is
assumed: continuity from each side gives one inequality, and `StrictAdjustment`
converts the sanction-side signs into state-side ones.

No monotonicity is needed for this. The threshold's existence as a rest point is
a continuity fact, not an order fact. -/
theorem equilibriumTop_threshold_is_restPoint
    (hAdj : p.StrictAdjustment) (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {a t b : ℝ}
    (hat : a < t) (htb : t < b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hdown : ∀ x ∈ Set.Ioo a t, p.dynamicTopRealizedRule E.V_S E.α x < x)
    (hup : ∀ x ∈ Set.Ioo t b, x < p.dynamicTopRealizedRule E.V_S E.α x) :
    p.dynamicTopLockInStepF E.V_S E.α t = t ∧
      p.dynamicTopRealizedRule E.V_S E.α t = t := by
  have hsub : Set.Icc a b ⊆ (Sanctions.S : Set ℝ) := fun y hy =>
    ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  have hcont : ContinuousOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc a b) :=
    p.dynamicTopLockInStepF_continuousOn E.V_S E.α
      (p.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E hUniq hsub)
  have hmemI : ∀ x ∈ Set.Ioo a b, x ∈ Sanctions.I := fun x hx =>
    hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hfix : p.dynamicTopLockInStepF E.V_S E.α t = t :=
    Sanctions.MonotoneAttraction.signFlip_is_fixedPoint hat htb hcont
      (fun x hx => p.stepF_lt_self_of_rule_lt_self hAdj E.V_S E.α
        (hmemI x ⟨hx.1, lt_trans hx.2 htb⟩) (hdown x hx))
      (fun x hx => p.self_lt_stepF_of_self_lt_rule hAdj E.V_S E.α
        (hmemI x ⟨lt_trans hat hx.1, hx.2⟩) (hup x hx))
  exact ⟨hfix, p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α
    (hsub ⟨le_of_lt hat, le_of_lt htb⟩) hfix⟩

/-- **The threshold splits the interval into two basins with different long-run
outcomes.**

Below the threshold every equilibrium state path converges to the bottom rest
point; above it, every path converges to the top one. One equilibrium, one rule,
one sign change, two outcomes — and the initial political state decides which.

Be precise about what is derived here, because it is easy to overstate.

**Derived:** that the interior crossing `t` is a rest point of the closed loop
(`equilibriumTop_threshold_is_restPoint`); that each side is invariant, from its
own sign condition; and continuity of the rule, from `DynamicArgmaxUnique`.

**Supplied:** the two endpoints `a` and `b`, together with the requirement that
the rule fix each of them; monotonicity of the rule on each side; and the sign
regions themselves — that the rule undershoots throughout `(a,t)` and overshoots
throughout `(t,b)`. None of those is derived from payoff and transition
primitives here.

So this is not "the basin structure falls out of the primitives". It is: given
the sign pattern and the endpoints, the dividing line between the two regions is
a steady state rather than a further assumption. Unlike the order-selection
capstones, this **is** attraction to a common limit on each side — the strict
sign conditions are what buy that.

The threshold itself belongs to neither basin: it is a rest point, so a path
starting exactly on it never moves. That is why the intervals are half-open. -/
theorem equilibriumTop_threshold_separates_basins
    (hAdj : p.StrictAdjustment) (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {a t b : ℝ}
    (hat : a < t) (htb : t < b) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hmonoL : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a t))
    (hmonoH : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc t b))
    (hfix_a : p.dynamicTopRealizedRule E.V_S E.α a = a)
    (hfix_b : p.dynamicTopRealizedRule E.V_S E.α b = b)
    (hdown : ∀ x ∈ Set.Ioo a t, p.dynamicTopRealizedRule E.V_S E.α x < x)
    (hup : ∀ x ∈ Set.Ioo t b, x < p.dynamicTopRealizedRule E.V_S E.α x) :
    (∀ x₀ ∈ Set.Ico a t,
      Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop (𝓝 a)) ∧
    (∀ x₀ ∈ Set.Ioc t b,
      Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
        (𝓝 b)) := by
  have hsub : Set.Icc a b ⊆ (Sanctions.S : Set ℝ) := fun y hy =>
    ⟨le_trans ha0 hy.1, le_trans hy.2 hb1⟩
  have hcontR : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b) :=
    p.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E hUniq hsub
  have hsubL : Set.Icc a t ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc le_rfl (le_of_lt htb)
  have hsubH : Set.Icc t b ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (le_of_lt hat) le_rfl
  have hmemI : ∀ x ∈ Set.Ioo a b, x ∈ Sanctions.I := fun x hx =>
    hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hGa : p.dynamicTopLockInStepF E.V_S E.α a = a := by
    change p.F a (p.dynamicTopRealizedRule E.V_S E.α a) = a
    rw [hfix_a]; exact p.F_diag a
  have hGb : p.dynamicTopLockInStepF E.V_S E.α b = b := by
    change p.F b (p.dynamicTopRealizedRule E.V_S E.α b) = b
    rw [hfix_b]; exact p.F_diag b
  constructor
  · intro x₀ hx₀
    exact Sanctions.MonotoneAttraction.threshold_below_tendsto_left
      (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hmonoL)
      (p.dynamicTopLockInStepF_continuousOn E.V_S E.α (hcontR.mono hsubL))
      hGa
      (fun x hx => p.stepF_lt_self_of_rule_lt_self hAdj E.V_S E.α
        (hmemI x ⟨hx.1, lt_trans hx.2 htb⟩) (hdown x hx)) hx₀
  · intro x₀ hx₀
    exact Sanctions.MonotoneAttraction.threshold_above_tendsto_right
      (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hmonoH)
      (p.dynamicTopLockInStepF_continuousOn E.V_S E.α (hcontR.mono hsubH))
      hGb
      (fun x hx => p.self_lt_stepF_of_self_lt_rule hAdj E.V_S E.α
        (hmemI x ⟨lt_trans hat hx.1, hx.2⟩) (hup x hx)) hx₀

/-! ## S6 — the locator route to a common long-run outcome, attempted

The question this section attacks, in the form §12.3 of the round record sharpened
it to: a common long-run outcome for a whole interval is **equivalent** to that
interval holding a unique rest point, so the research target is not "prove
attraction" but "derive uniqueness from primitives".

The Huang–Pouzo–Rodríguez-Clare (2025) route to exactly that, in a single-agent
dynamic problem, is a **locator function** whose sign gives the direction of
motion, with global convergence following when the locator is single-crossing from
above. The natural object here is the escalation gap.

### What the attempt found

**The conclusion half is already free.** Single crossing from above of the
closed-loop gap gives a common limit outright — that is
`equilibriumTop_attraction_of_closedLoopGap_singleCrossing` below, and it is a
two-line consequence of the equivalence, with no new assumption. So the locator
route's *payoff* needs nothing further.

**The locator half fails from what the route extracts.** What the persistence
route *extracts* about the realized rule on the basin is monotonicity (from the
interval-dominance condition) and the level condition `max x s̄ ≤ R x` (from the
sub-pivot chord against the Lipschitz carrier). Those two are satisfied by
`R = id`, which fixes every point of the basin — so they are consistent with a
continuum of rest points and cannot yield single crossing. This bounds the
extracted consequences, not the raw package: no complete `Params` economy
satisfying every field of `SenderPersistencePackage` with two rest points in a
claimed interval has been constructed.
`persistence_consequences_insufficient_for_basin_uniqueness` records that;
`MonotoneAttraction.weak_level_condition_insufficient` is the same obstruction at
the abstract level.

The failure is not an accident of proof search. The level condition is an
inequality that permits equality everywhere, and equality everywhere *is* the
degenerate case. Nothing among the extracted consequences breaks the tie, for the
same structural reason recorded in `SubpivotChordNecessity.lean`: the sub-pivot
chord constrains the Sender's objective only at sanctions weakly below the
current state.

### Rule-3 status

**No new primitive is introduced here, and none is assumed.** The bridge below is
an explicitly *conditional* theorem, is not a headline row, and takes its sign
hypotheses as inequalities over objects the model already carries rather than as a
named `Prop` on the assumption surface.

A new primitive would be needed only to claim a common limit on an interval
**named in advance**. It is not needed for the model to have a common limit at
all — see the resolution below, which derives the interval instead. -/

/-! ### S6, resolved — attraction on a derived interval

The refutation above is correct and its scope is narrow. What the persistence
route *extracts* from the package — monotonicity of the realized rule, from the
interval-dominance condition, and the level condition `max x s̄ ≤ R x`, from the
sub-pivot chord against the Lipschitz carrier — does not pin a unique rest point
on an interval whose upper endpoint is **chosen in advance**. `R = id` satisfies
both extracted consequences and fixes every state.

But the project's own discipline elsewhere is to *derive* an interval's endpoints
rather than choose them, and applying it here dissolves the problem. Take the
interval to end at the **least** closed-loop steady state above the pivot. Then
uniqueness holds by construction — nothing below a least fixed point is fixed —
and a common limit follows with **no new assumption**.

So the two questions come apart:

* *"Is there a common long-run outcome on `[x̄, b]` for a **given** `b`?"* — not
  from the extracted consequences.
  `persistence_consequences_insufficient_for_basin_uniqueness`.
* *"Is there an interval on which every equilibrium path shares a limit?"* —
  **yes**, and the theorems below prove it. The interval is `[x̄, x_s]` with `x_s`
  the least steady state above the pivot.

### Terminology, deliberately

This is **attraction on a derived interval**, not "interior attraction". The
phrase *interior steady state* is reserved for a result establishing `x_s < 1`,
and no such result exists here: `x_s` may well be the corner, in which case the
derived interval is the whole basin and the statement is the corner case again.
Nothing below proves otherwise, and nothing below should be cited as if it did.

What remains genuinely open is narrower than the frontier used to sound: whether
a *particular named* interval — the whole high basin, or one reaching the corner —
has a single rest point. That needs either a new primitive or an economy-specific
calculation. -/

/-- **The equilibrium escalation gap.** How far the Sender's optimal sanction sits
above the inherited political state. Pure notation over existing objects. -/
noncomputable def equilibriumGap
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.dynamicTopRealizedRule V_S α x - x

/-- **The closed-loop gap.** How far next period's political state sits above this
period's, under the equilibrium rule. This is the object whose sign the dynamics
actually follow; `equilibriumGap` maps onto it one way only, and the converse
needs `StrictAdjustment`. -/
noncomputable def closedLoopGap
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) : ℝ :=
  p.dynamicTopLockInStepF V_S α x - x

/-- **A single-crossing closed-loop gap gives a common long-run outcome.**

If the closed-loop gap is strictly positive below `x_star` and strictly negative
above it, then *every* equilibrium path in the interval converges to `x_star` — a
common limit, not order selection.

This is the locator route's conclusion, and it costs nothing: it is the
equivalence `attraction_iff_unique_fixedPoint` composed with
`unique_fixedPoint_iff_strictly_signed`, both proved without new assumptions.

**It is conditional and it is not a headline row.** The sign hypotheses are
supplied by nobody; cite it only together with a proof of them at the economy in
hand. -/
theorem equilibriumTop_attraction_of_closedLoopGap_singleCrossing
    (E : p.FeedbackStackelbergEquilibriumTop) {a b x_star : ℝ} (hab : a ≤ b)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    (hpos : ∀ x ∈ Set.Icc a b, x < x_star → 0 < p.closedLoopGap E.V_S E.α x)
    (hneg : ∀ x ∈ Set.Icc a b, x_star < x → p.closedLoopGap E.V_S E.α x < 0) :
    ∀ x₀ ∈ Set.Icc a b,
      Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
        (𝓝 x_star) := by
  refine (Sanctions.MonotoneAttraction.attraction_iff_unique_fixedPoint hab
    (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hrule_mono)
    (p.dynamicTopLockInStepF_continuousOn E.V_S E.α hrule_cont) hmaps).mpr ?_
  refine (Sanctions.MonotoneAttraction.unique_fixedPoint_iff_strictly_signed hab
    (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hrule_mono)
    (p.dynamicTopLockInStepF_continuousOn E.V_S E.α hrule_cont) hmaps).mpr ?_
  exact ⟨fun x hx h => by
      have hx' := hneg x hx h; unfold closedLoopGap at hx'; linarith,
    fun x hx h => by
      have hx' := hpos x hx h; unfold closedLoopGap at hx'; linarith⟩

/-- **Rule-11: the extracted persistence consequences do not deliver uniqueness on
a pre-chosen interval, so the locator cannot be read off them.**

The two things the persistence route extracts about the realized rule on the
basin are here: it is non-decreasing (from the interval-dominance condition), and
it sits at or above `max x s̄` (from the sub-pivot chord against the Lipschitz
carrier). Both are satisfied by the identity rule, which fixes *every* state.

**Scope, exactly.** This refutes the implication from those two *extracted
consequences* to uniqueness on a given interval. It does **not** refute the raw
package: no complete `Params` economy satisfying every field of
`SenderPersistencePackage` with two rest points in a claimed interval has been
constructed. And it says nothing against
`equilibriumTop_attraction_up_to_least_steadyState_of_continuousOn` below, which
gets uniqueness from the *choice of interval* rather than from the conditions. -/
theorem persistence_consequences_insufficient_for_basin_uniqueness :
    ¬ ∀ (R : ℝ → ℝ) (xbar sbar : ℝ),
        0 ≤ xbar → xbar ≤ 1 → sbar ≤ xbar →
        MonotoneOn R (Set.Icc xbar 1) →
        (∀ x ∈ Set.Icc xbar (1 : ℝ), max x sbar ≤ R x) →
        ∃! y, y ∈ Set.Icc xbar (1 : ℝ) ∧ R y = y := by
  intro h
  obtain ⟨y, -, huniq⟩ := h id 0 0 le_rfl zero_le_one le_rfl
    (fun _ _ _ _ hxy => hxy)
    (fun x hx => by simpa using hx.1)
  have h0 : (0 : ℝ) = y := huniq 0 ⟨by norm_num, rfl⟩
  have h1 : (1 : ℝ) = y := huniq 1 ⟨by norm_num, rfl⟩
  rw [← h0] at h1
  norm_num at h1

/-- **Attraction on a derived interval, from invariance and a monotone closed
loop (round BH-2, 2026-10-06, BH2.7).**

At an actual equilibrium `E`, suppose the closed loop `G_E(x) = F(x, R_E x)` maps
`[x̄, 1]` into itself and is non-decreasing there, and the realized rule is
continuous there. Then there is a least steady state `x_s` of `G_E` in `[x̄, 1]`,
the interval `[x̄, x_s]` is invariant, and every equilibrium path started in
`[x̄, x_s]` converges to `x_s` — one limit, shared by every start.

In plain terms: if a higher political state today never leads to a lower one
tomorrow, then everything between the pivot and the first steady state above it
drifts to that steady state.

Dropped relative to `equilibriumTop_attraction_up_to_least_steadyState_of_invariant`:
monotonicity of the realized rule, replaced by the implied, weaker monotonicity
of the closed loop, which is all the argument reads (least fixed point, the
invariance of `[x̄, x_s]`, and the unique-fixed-point attraction theorem).
Uniqueness of the rest point on `[x̄, x_s]` holds by construction. Nothing is
claimed about states above `x_s` or about whether `x_s` is interior. Rule 9B: a
weaker sufficient condition; strictly wider coverage of equilibria is
unwitnessed. General in `F`. -/
theorem equilibriumTop_attraction_up_to_least_steadyState_of_stepMonotoneOn
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar : ℝ}
    (hxbar1 : xbar ≤ 1)
    (hstep_mono : MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α)
      (Set.Icc xbar 1))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      (∀ x ∈ Set.Icc xbar xs,
        p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar xs) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  obtain ⟨xs, hxs_mem, hxs_fix, hleast⟩ :=
    Sanctions.MonotoneThreshold.exists_least_fixedPoint_of_monotoneOn_Icc hxbar1
      hstep_mono hmaps
  have hsubI : Set.Icc xbar xs ⊆ Set.Icc xbar 1 :=
    Set.Icc_subset_Icc le_rfl hxs_mem.2
  have hmaps' : ∀ x ∈ Set.Icc xbar xs,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar xs := by
    intro x hx
    refine ⟨(hmaps x (hsubI hx)).1, ?_⟩
    have h := hstep_mono (hsubI hx) hxs_mem hx.2
    rwa [hxs_fix] at h
  refine ⟨xs, hxs_mem, hxs_fix, hleast, hmaps', ?_⟩
  have hOnly : ∀ y ∈ Set.Icc xbar xs,
      p.dynamicTopLockInStepF E.V_S E.α y = y → y = xs := fun y hy hfy =>
    le_antisymm hy.2 (hleast y (hsubI hy) hfy)
  intro x₀ hx₀
  exact Sanctions.MonotoneAttraction.monotoneOn_orbit_tendsto_of_unique
    hxs_mem.1 (hstep_mono.mono hsubI)
    (p.dynamicTopLockInStepF_continuousOn E.V_S E.α (hrule_cont.mono hsubI))
    hmaps' hOnly hx₀

/-- **Attraction on a derived interval, from invariance alone.**

The mathematical core, and the exact backing for the manuscript's proposition:
an interval the closed loop preserves, plus monotonicity and continuity of the
realized rule on it. **No level condition, no sanction floor, no persistence
package**, and not even feasibility of the pivot.

Every equilibrium path started between the pivot and the **first** steady state
above it converges to that steady state — one limit, shared by every start in the
interval.

Uniqueness of the rest point there is not assumed: it holds by construction,
because `x_s` is the *least* steady state above the pivot, so nothing below it is
fixed. The conclusion also exposes invariance of `[x̄, x_s]`, which the sanction
statement needs.

The level-condition version below is the corollary that derives invariance from
the persistence machinery; it is strictly less general, because the level
condition implies invariance (`dynamicTopLockInStepF_mem_basin`) and not
conversely. Nothing is claimed about states above `x_s`, about whether `x_s` is
interior, or about whether `x̄ < x_s`.

Since round BH-2 (2026-10-06, BH2.7) a one-line corollary of the closed-loop
form `equilibriumTop_attraction_up_to_least_steadyState_of_stepMonotoneOn`,
through `dynamicTopLockInStepF_monotoneOn`. -/
theorem equilibriumTop_attraction_up_to_least_steadyState_of_invariant
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar : ℝ}
    (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      (∀ x ∈ Set.Icc xbar xs,
        p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar xs) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) :=
  p.equilibriumTop_attraction_up_to_least_steadyState_of_stepMonotoneOn E hxbar1
    (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hrule_mono) hrule_cont hmaps

/-- **The same, with invariance derived from the persistence level condition.**

Every equilibrium path started between the pivot and the **first** closed-loop
steady state above it converges to that steady state — one limit, shared by every
start in the interval.

Continuity of the realized rule is assumed directly here, as it is in `C1` tier 1,
so that the mathematical requirement stays separate from the economic condition
that supplies it. Monotonicity comes from the persistence package's
interval-dominance condition and the level condition from its sub-pivot chord
against the Lipschitz carrier.

Uniqueness of the rest point — which `attraction_iff_unique_fixedPoint` shows is
exactly what a common limit requires — is **not** assumed. It holds by
construction, because `x_s` is the *least* steady state above the pivot, so
nothing below it is fixed. That is the whole reason this works where the
pre-chosen-endpoint version provably fails.

The conclusion also exposes invariance of `[x̄, x_s]`, which downstream sanction
statements need. Nothing is claimed about states above `x_s`, and nothing is
claimed about whether `x_s` is interior.

General in `F`. No `0 ≤ x̄`: it was read only by the basin invariance lemma
`dynamicTopLockInStepF_mem_basin`, which no longer needs it (dropped on
2026-10-06, BG2.1). -/
theorem equilibriumTop_attraction_up_to_least_steadyState_of_continuousOn
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar : ℝ}
    (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      (∀ x ∈ Set.Icc xbar xs,
        p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar xs) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  exact p.equilibriumTop_attraction_up_to_least_steadyState_of_invariant E hxbar1
    hrule_mono hrule_cont
    (fun x hx => p.dynamicTopLockInStepF_mem_basin E.V_S E.α h_level_top hx)

/-- **The same, with continuity discharged from argmax uniqueness.**

Single-valuedness of the Sender's dynamic argmax supplies continuity of the
realized rule on any feasible interval, so this is the theorem above with its
regularity hypothesis derived rather than assumed. -/
theorem equilibriumTop_attraction_up_to_least_steadyState
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {xbar sbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  have hsubS : Set.Icc xbar (1 : ℝ) ⊆ (Sanctions.S : Set ℝ) := fun y hy =>
    ⟨le_trans hxbar0 hy.1, hy.2⟩
  obtain ⟨xs, hxs_mem, hxs_fix, hleast, -, hatt⟩ :=
    p.equilibriumTop_attraction_up_to_least_steadyState_of_continuousOn E
      hxbar1 hrule_mono
      (p.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E hUniq hsubS)
      h_level_top
  exact ⟨xs, hxs_mem, hxs_fix, hleast, hatt⟩

/-! #### Non-degeneracy is a separate question, and a harder one than it looks

The attraction theorems above permit `x_s = x̄`, in which case the derived interval
is a single point and the statement, while true, is empty. Ruling that out is a
**separate** condition and must be priced separately.

Read the layering carefully, because it is easy to run the two together:

* *Attraction on the derived interval* — approved regularity (monotonicity and
  continuity of the realized rule) plus the persistence route's level condition.
  Nothing further.
* *Positive length of that interval* — an **additional** condition, below.
* *Interiority, `x_s < 1`* — neither proved nor needed anywhere.

**And the obvious economic route to positive length is vacuous on the package's
own basin.** `SenderPersistencePackage.toSenderPersistenceBasinTop` produces the
basin with pivot *and* floor both equal to `max xT xS`, so `s̄ = x̄` there and the
floor-gap hypothesis `x̄ < min s̄ 1` is not merely unsupplied — it is false. On that
route, positive length reduces to `R(x̄) > x̄` strictly, which is exactly the strict
persistence the sub-pivot chord does not deliver. Positive length and strict
persistence are therefore the *same* open question wherever the floor sits at the
pivot; the corollaries below bite only where a strictly higher floor comes from
elsewhere, as it does at the dual-basin witness. -/

/-- **A direct sufficient condition for non-degeneracy: the closed loop does not
fix the pivot.**

If `G_E(x̄) ≠ x̄` then no steady state sits at the pivot, so any steady state at or
above it is strictly above it. Nothing else is used — no level condition, no
monotonicity, no transition condition, and no leastness: this applies to *any*
fixed point above the pivot, not only the least one. -/
theorem fixedPoint_gt_pivot_of_stepF_ne
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar xs : ℝ}
    (hge : xbar ≤ xs) (hfix : p.dynamicTopLockInStepF V_S α xs = xs)
    (hne : p.dynamicTopLockInStepF V_S α xbar ≠ xbar) : xbar < xs := by
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exact absurd (h ▸ hfix) hne

/-- The strict-inequality form, as a corollary of the `≠` form above. -/
theorem least_steadyState_gt_pivot_of_stepF_gt
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar xs : ℝ}
    (hge : xbar ≤ xs) (hfix : p.dynamicTopLockInStepF V_S α xs = xs)
    (hstep : xbar < p.dynamicTopLockInStepF V_S α xbar) : xbar < xs :=
  p.fixedPoint_gt_pivot_of_stepF_ne V_S α hge hfix (ne_of_gt hstep)

/-- **Economic sufficient condition for it: a sanction floor above the pivot,
plus (F5).**

Where the guaranteed floor strictly exceeds the pivot, the level condition already
makes the ratchet strict there, and strict directional adjustment carries that
from the sanction to the state. -/
theorem stepF_gt_pivot_of_floor_of_strictAdjustment
    (hAdj : p.StrictAdjustment)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hgap : xbar < min sbar 1) :
    xbar < p.dynamicTopLockInStepF V_S α xbar :=
  p.self_lt_stepF_of_self_lt_rule hAdj V_S α ⟨hxbar0, hxbar1⟩
    (p.strict_ratchet_of_level_floor V_S α h_level_top xbar ⟨le_rfl, hgap⟩)

/-- **The derived interval is non-degenerate under a floor above the pivot.**

The economic packaging of the two lemmas above: floor strictly above the pivot,
plus strict directional adjustment, gives `x̄ < x_s`. -/
theorem equilibriumTop_least_steadyState_gt_pivot_of_floor
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {xbar sbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hgap : xbar < min sbar 1) :
    ∃ xs ∈ Set.Icc xbar 1, xbar < xs ∧
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  obtain ⟨xs, hxs_mem, hxs_fix, -, hatt⟩ :=
    p.equilibriumTop_attraction_up_to_least_steadyState E hUniq hxbar0 hxbar1
      hrule_mono h_level_top
  exact ⟨xs, hxs_mem,
    p.least_steadyState_gt_pivot_of_stepF_gt E.V_S E.α hxs_mem.1 hxs_fix
      (p.stepF_gt_pivot_of_floor_of_strictAdjustment hAdj E.V_S E.α hxbar0 hxbar1
        h_level_top hgap),
    hxs_fix, hatt⟩

/-- **Under (F5) the realized sanction converges to whatever fixed state the path
reaches.**

Continuity carries the state limit to the rule's value there, and strict
directional adjustment identifies that value with the state itself, since a state
the closed loop leaves unchanged is one at which the sanction pulls in neither
direction.

**Leastness is not used.** The hypothesis is only that `xs` is fixed and that the
state path converges to it, so this applies at any steady state the path reaches;
the name below records that. -/
theorem equilibriumTop_sanctions_tendsto_fixedState
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar xs : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxs_mem : xs ∈ Set.Icc xbar 1)
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar xs))
    (hmaps : ∀ x ∈ Set.Icc xbar xs,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar xs)
    (hxs_fix : p.dynamicTopLockInStepF E.V_S E.α xs = xs)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar xs)
    (hpath : Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
      (𝓝 xs)) :
    Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
      (𝓝 xs) := by
  have hxsI : xs ∈ Sanctions.I := ⟨le_trans hxbar0 hxs_mem.1, hxs_mem.2⟩
  have h := p.dynamicTopLockInSanctionsF_tendsto_rule_at_limit E.V_S E.α
    hrule_cont hmaps (Set.right_mem_Icc.mpr hxs_mem.1) hx₀ hpath
  rwa [p.realizedRule_eq_self_of_stepF_fixed hAdj E.V_S E.α hxsI hxs_fix] at h

/-- The former name, retained: at the least steady state in particular. -/
theorem equilibriumTop_sanctions_tendsto_least_steadyState
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar xs : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxs_mem : xs ∈ Set.Icc xbar 1)
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar xs))
    (hmaps : ∀ x ∈ Set.Icc xbar xs,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar xs)
    (hxs_fix : p.dynamicTopLockInStepF E.V_S E.α xs = xs)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar xs)
    (hpath : Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
      (𝓝 xs)) :
    Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
      (𝓝 xs) :=
  p.equilibriumTop_sanctions_tendsto_fixedState hAdj E hxbar0 hxs_mem hrule_cont
    hmaps hxs_fix hx₀ hpath

/-- **State and sanction together, on the derived interval — closed-loop form
(round BH-2, 2026-10-06, BH2.7).**

At an actual equilibrium `E`, suppose the closed loop `G_E` maps `[x̄, 1]` into
itself (with `0 ≤ x̄ ≤ 1`) and is non-decreasing there, the realized rule is
continuous there, and the transition satisfies strict directional adjustment
`(F5)`. Then every equilibrium path started between the pivot and the first
steady state `x_s` above it converges to `x_s`, and so does the realized
sanction along it.

Dropped relative to `equilibriumTop_attraction_on_derived_interval_of_invariant`
(which is now a one-line corollary): monotonicity of the realized rule, replaced
by the implied, weaker monotonicity of the closed loop. `(F5)` and `0 ≤ x̄` are
still read, only by the sanction half (identifying the rule's value at `x_s`
with `x_s`). The interval may be a single point, and `x_s` is not claimed to be
interior. Rule 9B: a weaker sufficient condition; strictly wider coverage of
equilibria is unwitnessed. General in `F`. -/
theorem equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hstep_mono : MonotoneOn (p.dynamicTopLockInStepF E.V_S E.α)
      (Set.Icc xbar 1))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  obtain ⟨xs, hxs_mem, hxs_fix, hleast, hmaps', hatt⟩ :=
    p.equilibriumTop_attraction_up_to_least_steadyState_of_stepMonotoneOn E hxbar1
      hstep_mono hrule_cont hmaps
  refine ⟨xs, hxs_mem, hxs_fix, hleast, fun x₀ hx₀ => ⟨hatt x₀ hx₀, ?_⟩⟩
  exact p.equilibriumTop_sanctions_tendsto_fixedState hAdj E hxbar0 hxs_mem
    (hrule_cont.mono (Set.Icc_subset_Icc le_rfl hxs_mem.2)) hmaps' hxs_fix hx₀
    (hatt x₀ hx₀)

/-- **State and sanction together, on the derived interval — invariance form.**

The manuscript's `prop:derived-interval` verbatim: an invariant interval, a
monotone continuous realized rule, and strict directional adjustment for the
sanction half. No level condition and no persistence package.

Every equilibrium path started between the pivot and the first steady state above
it converges to that steady state, and so does the realized sanction along it.

The interval may be a single point — see the non-degeneracy section above — and
`x_s` is not claimed to be interior.

Since round BH-2 (2026-10-06, BH2.7) a one-line corollary of the closed-loop
form `equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn`. The
statement is unchanged (it is a pinned headline row). -/
theorem equilibriumTop_attraction_on_derived_interval_of_invariant
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc xbar 1) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) :=
  p.equilibriumTop_attraction_on_derived_interval_of_stepMonotoneOn hAdj E hxbar0 hxbar1
    (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hrule_mono) hrule_cont hmaps

/-- **State and sanction together, with invariance derived from the level
condition.**

The weakest bundle: monotonicity and continuity of the realized rule, the level
condition, and strict directional adjustment for the sanction half. No
argmax-uniqueness condition, so the manuscript cannot present that condition as
necessary when it is only one way to obtain continuity.

`x_s` is not claimed to be interior, and the interval is not claimed to have
positive length — see the non-degeneracy section above. -/
theorem equilibriumTop_attraction_on_derived_interval_of_continuousOn
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  exact p.equilibriumTop_attraction_on_derived_interval_of_invariant hAdj E
    hxbar0 hxbar1 hrule_mono hrule_cont
    (fun x hx => p.dynamicTopLockInStepF_mem_basin E.V_S E.α h_level_top hx)

/-- **State and sanction together, with continuity discharged from argmax
uniqueness.**

The user-facing bundle: from the persistence conditions plus argmax uniqueness and
strict directional adjustment, there is a steady state `x_s` — the least one above
the pivot — such that every equilibrium path started in `[x̄, x_s]` converges to
it, and so does the realized sanction along that path.

`x_s` is not claimed to be interior. -/
theorem equilibriumTop_attraction_on_derived_interval
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hUniq : p.DynamicArgmaxUnique E.V_S) {xbar sbar : ℝ}
    (hxbar0 : 0 ≤ xbar) (hxbar1 : xbar ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
      (Set.Icc xbar 1))
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x) :
    ∃ xs ∈ Set.Icc xbar 1,
      p.dynamicTopLockInStepF E.V_S E.α xs = xs ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p.dynamicTopLockInStepF E.V_S E.α y = y → xs ≤ y) ∧
      ∀ x₀ ∈ Set.Icc xbar xs,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 xs) := by
  have hsubS : Set.Icc xbar (1 : ℝ) ⊆ (Sanctions.S : Set ℝ) := fun y hy =>
    ⟨le_trans hxbar0 hy.1, hy.2⟩
  exact p.equilibriumTop_attraction_on_derived_interval_of_continuousOn hAdj E
    hxbar0 hxbar1 hrule_mono
    (p.dynamicTopRealizedRule_continuousOn_of_argmaxUnique E hUniq hsubS)
    h_level_top

/-! ## Round 8 — the dividing line derived from the equilibrium closed loop

Everything above takes an interval and asks what happens inside it. The interval
arrives from outside: a certified basin, a pivot, a chosen endpoint. This section
turns that around. Given only that the equilibrium closed loop **erodes** the
political state at one state and **does not erode** it at a higher one, with
continuity in between, the dividing line between the two behaviours is
constructed from the closed loop itself — as the lowest state at which erosion
stops — and the strict erosion below it comes out as a conclusion.

That is what `signFlip_is_fixedPoint` could not do. It says a crossing is a rest
point, but it takes the sign pattern on *both* sides as given, so the crossing is
still supplied. Here two endpoint readings and continuity replace the whole sign
pattern, and the threshold is a function of the equilibrium.

Nothing here assumes the realized rule is monotone. The wash-out and ratchet
conclusions rest on `strictBelow_basin_tendsto_of_lowerBound` and its mirror,
which trade order-preservation for feasibility bounds — and that matters,
because a derived threshold is typically extracted across a region between two
certified basins where monotonicity of the rule is exactly what is *not* known.

**Rule 3.** No new assumption surface. The endpoint readings are inequalities on
the existing closed loop, discharged at economies from already-certified basin
facts; continuity is the same hypothesis Round 4A already discharges from
`DynamicArgmaxUnique`; the feasibility bounds restate `F_mem`. -/

/-- **The equilibrium's own erosion threshold.**

Hypotheses in English: on a window `[a,b]` of political states the realized
equilibrium rule is continuous; at the bottom of the window the closed loop
strictly lowers the state (entrenchment erodes at `a`); at the top it does not
lower it. Conclusion: there is a state `t` strictly inside the window above `a`
which is

* a **steady state** of the closed loop;
* preceded by **strict erosion everywhere below it** in the window; and
* the **least** steady state of the window.

The point is what is *not* assumed. Nothing is supposed about the sign of the
closed-loop gap anywhere strictly between the two endpoints, nor that the rule is
monotone. The threshold is `sInf {x ∈ [a,b] | x ≤ G_E x}` — an object read off
the equilibrium closed loop, not a constant handed to the theorem. -/
theorem equilibriumTop_derived_threshold
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ} (hab : a ≤ b)
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hero : p.dynamicTopLockInStepF E.V_S E.α a < a)
    (hstop : b ≤ p.dynamicTopLockInStepF E.V_S E.α b) :
    ∃ t ∈ Set.Ioc a b,
      p.dynamicTopLockInStepF E.V_S E.α t = t ∧
      (∀ x ∈ Set.Ico a t, p.dynamicTopLockInStepF E.V_S E.α x < x) ∧
      (∀ y ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α y = y → t ≤ y) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Sanctions.MonotoneAttraction.leastWeakAbove_spec hab
      (p.dynamicTopLockInStepF_continuousOn E.V_S E.α hrule_cont) hero hstop
  exact ⟨_, ⟨h1, h2⟩, h3, h4, h5⟩

/-- **The equilibrium's own ratchet threshold.** The mirror: with the closed loop
*not raising* the state at the bottom of the window and strictly raising it at the
top, the highest state at which building stops is a steady state, everything above
it strictly builds, and it is the greatest steady state of the window. -/
theorem equilibriumTop_derived_upper_threshold
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ} (hab : a ≤ b)
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hstop : p.dynamicTopLockInStepF E.V_S E.α a ≤ a)
    (hbuild : b < p.dynamicTopLockInStepF E.V_S E.α b) :
    ∃ t ∈ Set.Ico a b,
      p.dynamicTopLockInStepF E.V_S E.α t = t ∧
      (∀ x ∈ Set.Ioc t b, x < p.dynamicTopLockInStepF E.V_S E.α x) ∧
      (∀ y ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ t) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Sanctions.MonotoneAttraction.greatestWeakBelow_spec hab
      (p.dynamicTopLockInStepF_continuousOn E.V_S E.α hrule_cont) hstop hbuild
  exact ⟨_, ⟨h1, h2⟩, h3, h4, h5⟩

/-- **Two basins with both dividing lines derived from the equilibrium.**

The capstone of this section, and the statement the dual-basin economy needs.

Hypotheses in English. Two named long-run states `lo < hi` are steady states of
the one equilibrium closed loop. A certified wash-out region reaches up to `xL`
(the state strictly erodes at every state of `(lo, xL]`) and a certified ratchet
region reaches down to `xH` (the state strictly builds on `[xH, hi)`). Between
`xL` and `xH` **nothing is assumed about the sign** — that middle region is
exactly where a certificate is silent. Continuity of the realized rule on the
whole interval, and the feasibility bounds that keep the closed loop between the
two named states, complete the list. Monotonicity is not required anywhere.

Conclusion. Two thresholds `t ≤ t'` are extracted from the closed loop itself,
both steady states, both inside the previously-silent middle region, and:

* every equilibrium path started **below** `t` washes out to `lo`;
* every equilibrium path started **above** `t'` ratchets to `hi`;
* `t = t'` exactly when the middle region holds a single steady state, in which
  case the interval splits cleanly at one derived dividing line.

So the certified basins **extend** — from `[lo, xL]` up to `[lo, t)`, and from
`[xH, hi]` down to `(t', hi]` — with the new endpoints read off the equilibrium
rather than assumed. What remains unclaimed is `[t, t']`, and by
`attraction_iff_unique_fixedPoint` that gap is not a weakness of the argument:
where two steady states sit in a region, a common limit across it is false, not
merely unproved. -/
theorem equilibriumTop_derived_dual_basins
    (E : p.FeedbackStackelbergEquilibriumTop) {lo xL xH hi : ℝ}
    (hlo : lo < xL) (hmid : xL ≤ xH) (hhi : xH < hi)
    (hrule_cont :
      ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc lo hi))
    (hfix_lo : p.dynamicTopLockInStepF E.V_S E.α lo = lo)
    (hfix_hi : p.dynamicTopLockInStepF E.V_S E.α hi = hi)
    (hlow_erode : ∀ x ∈ Set.Ioc lo xL,
      p.dynamicTopLockInStepF E.V_S E.α x < x)
    (hhigh_build : ∀ x ∈ Set.Ico xH hi,
      x < p.dynamicTopLockInStepF E.V_S E.α x)
    (hlb : ∀ x ∈ Set.Icc lo hi, lo ≤ p.dynamicTopLockInStepF E.V_S E.α x)
    (hub : ∀ x ∈ Set.Icc lo hi, p.dynamicTopLockInStepF E.V_S E.α x ≤ hi) :
    ∃ t ∈ Set.Ioc xL xH, ∃ t' ∈ Set.Ico xL xH,
      t ≤ t' ∧
      p.dynamicTopLockInStepF E.V_S E.α t = t ∧
      p.dynamicTopLockInStepF E.V_S E.α t' = t' ∧
      (∀ x₀ ∈ Set.Ico lo t,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 lo)) ∧
      (∀ x₀ ∈ Set.Ioc t' hi,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 hi)) ∧
      (t = t' ↔ ∀ y ∈ Set.Icc xL xH, ∀ z ∈ Set.Icc xL xH,
        p.dynamicTopLockInStepF E.V_S E.α y = y →
        p.dynamicTopLockInStepF E.V_S E.α z = z → y = z) := by
  have hG_cont : ContinuousOn (p.dynamicTopLockInStepF E.V_S E.α)
      (Set.Icc lo hi) := p.dynamicTopLockInStepF_continuousOn E.V_S E.α hrule_cont
  have hsubW : Set.Icc xL xH ⊆ Set.Icc lo hi :=
    Set.Icc_subset_Icc (le_of_lt hlo) (le_of_lt hhi)
  have hcW := hG_cont.mono hsubW
  have hxL : p.dynamicTopLockInStepF E.V_S E.α xL < xL :=
    hlow_erode xL ⟨hlo, le_rfl⟩
  have hxH : xH < p.dynamicTopLockInStepF E.V_S E.α xH :=
    hhigh_build xH ⟨le_rfl, hhi⟩
  obtain ⟨ht1, ht2, htfix, htdown, -⟩ :=
    Sanctions.MonotoneAttraction.leastWeakAbove_spec hmid hcW hxL (le_of_lt hxH)
  obtain ⟨hs1, hs2, hsfix, hsup, -⟩ :=
    Sanctions.MonotoneAttraction.greatestWeakBelow_spec hmid hcW (le_of_lt hxL) hxH
  refine ⟨_, ⟨ht1, ht2⟩, _, ⟨hs1, hs2⟩,
    Sanctions.MonotoneAttraction.leastWeakAbove_le_greatestWeakBelow hmid hcW hxL hxH,
    htfix, hsfix, ?_, ?_,
    Sanctions.MonotoneAttraction.derivedThresholds_eq_iff_unique_fixedPoint
      hmid hcW hxL hxH⟩
  · -- below the lower threshold: wash-out to `lo`
    intro x₀ hx₀
    have hsubL : Set.Icc lo (Sanctions.MonotoneAttraction.leastWeakAbove
        (p.dynamicTopLockInStepF E.V_S E.α) xL xH) ⊆ Set.Icc lo hi :=
      Set.Icc_subset_Icc le_rfl (le_trans ht2 (le_of_lt hhi))
    refine Sanctions.MonotoneAttraction.threshold_below_tendsto_left_of_lowerBound
      (hG_cont.mono hsubL) hfix_lo ?_ (fun x hx => hlb x (hsubL hx)) hx₀
    intro x hx
    rcases le_total x xL with h | h
    · exact hlow_erode x ⟨hx.1, h⟩
    · exact htdown x ⟨h, hx.2⟩
  · -- above the upper threshold: ratchet to `hi`
    intro x₀ hx₀
    have hsubH : Set.Icc (Sanctions.MonotoneAttraction.greatestWeakBelow
        (p.dynamicTopLockInStepF E.V_S E.α) xL xH) hi ⊆ Set.Icc lo hi :=
      Set.Icc_subset_Icc (le_trans (le_of_lt hlo) hs1) le_rfl
    refine Sanctions.MonotoneAttraction.threshold_above_tendsto_right_of_upperBound
      (hG_cont.mono hsubH) hfix_hi ?_ (fun x hx => hub x (hsubH hx)) hx₀
    intro x hx
    rcases le_total x xH with h | h
    · exact hsup x ⟨hx.1, h⟩
    · exact hhigh_build x ⟨h, hx.2⟩

/-! ## Round L (doc 80, M8) — siblings without the derivable hypotheses

The reader's round-K validation package (2026-09-10, document 03 §5) named
three binders of this file's manuscript-cited theorems that their other
hypotheses already imply: the order `a ≤ b` of the interval, which the start
`x₀ ∈ [a, b]` supplies, and the two endpoint fixations of the dividing-line
theorem, which continuity, the strict drifts next to the endpoints and the
feasibility bounds supply
(`MonotoneAttraction.fixed_left_of_continuousOn_strict_below`,
`fixed_right_of_continuousOn_strict_above`). The three theorems keep their
statements (they are headline rows, Rule 18); the siblings below state the same
conclusions without those binders and are one-line corollaries.

Since round BH-2 (2026-10-06, BH2.7) the two primed order-selection siblings are
one-line corollaries of their closed-loop forms
(`equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn` and
`..._identified_of_stepMonotoneOn`), which also drop `a ≤ b` and assume
monotonicity of the closed loop instead of the realized rule. -/

/-- `equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn` without
`a ≤ b`, which `x₀ ∈ [a, b]` implies. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_of_continuousOn'
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 (p.dynamicTopRealizedRule E.V_S E.α x_star))) :=
  p.equilibriumTop_tendsto_order_selected_fixedPoint_of_stepMonotoneOn E
    (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hrule_mono) hrule_cont hmaps hx₀

/-- `equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_continuousOn`
without `a ≤ b`, which `x₀ ∈ [a, b]` implies. -/
theorem equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_continuousOn'
    (hAdj : p.StrictAdjustment)
    (E : p.FeedbackStackelbergEquilibriumTop) {a b : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hrule_cont : ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc a b))
    (hmaps : ∀ x ∈ Set.Icc a b,
      p.dynamicTopLockInStepF E.V_S E.α x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ ≤ p.dynamicTopRealizedRule E.V_S E.α x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x₀ ≤ x_star ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → x₀ ≤ y →
          x_star ≤ y) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) ∧
    (p.dynamicTopRealizedRule E.V_S E.α x₀ ≤ x₀ →
      ∃ x_star ∈ Set.Icc a b,
        p.dynamicTopLockInStepF E.V_S E.α x_star = x_star ∧ x_star ≤ x₀ ∧
        (∀ y ∈ Set.Icc a b, p.dynamicTopLockInStepF E.V_S E.α y = y → y ≤ x₀ →
          y ≤ x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star) ∧
        Filter.Tendsto (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) Filter.atTop
          (𝓝 x_star)) :=
  p.equilibriumTop_tendsto_order_selected_fixedPoint_identified_of_stepMonotoneOn hAdj E
    ha0 hb1 (p.dynamicTopLockInStepF_monotoneOn E.V_S E.α hrule_mono) hrule_cont hmaps hx₀

/-- `equilibriumTop_derived_dual_basins` without the two endpoint fixations, which
continuity, the strict drifts next to the endpoints and the feasibility bounds
supply. -/
theorem equilibriumTop_derived_dual_basins'
    (E : p.FeedbackStackelbergEquilibriumTop) {lo xL xH hi : ℝ}
    (hlo : lo < xL) (hmid : xL ≤ xH) (hhi : xH < hi)
    (hrule_cont :
      ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc lo hi))
    (hlow_erode : ∀ x ∈ Set.Ioc lo xL,
      p.dynamicTopLockInStepF E.V_S E.α x < x)
    (hhigh_build : ∀ x ∈ Set.Ico xH hi,
      x < p.dynamicTopLockInStepF E.V_S E.α x)
    (hlb : ∀ x ∈ Set.Icc lo hi, lo ≤ p.dynamicTopLockInStepF E.V_S E.α x)
    (hub : ∀ x ∈ Set.Icc lo hi, p.dynamicTopLockInStepF E.V_S E.α x ≤ hi) :
    ∃ t ∈ Set.Ioc xL xH, ∃ t' ∈ Set.Ico xL xH,
      t ≤ t' ∧
      p.dynamicTopLockInStepF E.V_S E.α t = t ∧
      p.dynamicTopLockInStepF E.V_S E.α t' = t' ∧
      (∀ x₀ ∈ Set.Ico lo t,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 lo)) ∧
      (∀ x₀ ∈ Set.Ioc t' hi,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 hi)) ∧
      (t = t' ↔ ∀ y ∈ Set.Icc xL xH, ∀ z ∈ Set.Icc xL xH,
        p.dynamicTopLockInStepF E.V_S E.α y = y →
        p.dynamicTopLockInStepF E.V_S E.α z = z → y = z) := by
  have hG_cont : ContinuousOn (p.dynamicTopLockInStepF E.V_S E.α) (Set.Icc lo hi) :=
    p.dynamicTopLockInStepF_continuousOn E.V_S E.α hrule_cont
  exact p.equilibriumTop_derived_dual_basins E hlo hmid hhi hrule_cont
    (Sanctions.MonotoneAttraction.fixed_left_of_continuousOn_strict_below hlo
      (hmid.trans hhi.le) hG_cont hlow_erode hlb)
    (Sanctions.MonotoneAttraction.fixed_right_of_continuousOn_strict_above hhi
      (hlo.le.trans hmid) hG_cont hhigh_build hub)
    hlow_erode hhigh_build hlb hub

/-- **The dividing line on the whole unit interval (round BH-2, 2026-10-06,
BH2.5).**

`equilibriumTop_derived_dual_basins'` with the two named long-run states at the
ends of the state space, `lo = 0` and `hi = 1`. At an actual equilibrium `E`,
take two thresholds `0 < x̄_L ≤ x̄_H < 1` such that the closed loop strictly
erodes the political state on `(0, x̄_L]` and strictly builds it on `[x̄_H, 1)`,
and suppose the realized rule is continuous on `[0, 1]`. Then two steady states
`x̄_L < t ≤ t' < x̄_H` are extracted from the closed loop itself, every
equilibrium path started below `t` converges to `0`, every one started above
`t'` converges to `1`, and `t = t'` exactly when `[x̄_L, x̄_H]` holds a single
steady state.

In plain terms: if sanctions erode entrenchment near the bottom and build it
near the top, the equilibrium itself draws the line between the two long-run
outcomes; nothing has to be assumed about the middle region.

Dropped relative to `equilibriumTop_derived_dual_basins'`: the two bounds that
keep the closed loop between `lo` and `hi`. On `[0, 1]` they are the feasibility
of the transition (`F_mem`) together with feasibility of the realized rule
(`dynamicTopLockInStepF_mem_I_of_mem_I`), so no "the closed loop maps `[0, 1]`
into itself" hypothesis is needed. No monotonicity of the rule and no basin
preference package are assumed. General in `F`. -/
theorem equilibriumTop_derived_dual_basins_unit
    (E : p.FeedbackStackelbergEquilibriumTop) {xL xH : ℝ}
    (hlo : 0 < xL) (hmid : xL ≤ xH) (hhi : xH < 1)
    (hrule_cont :
      ContinuousOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc 0 1))
    (hlow_erode : ∀ x ∈ Set.Ioc 0 xL,
      p.dynamicTopLockInStepF E.V_S E.α x < x)
    (hhigh_build : ∀ x ∈ Set.Ico xH 1,
      x < p.dynamicTopLockInStepF E.V_S E.α x) :
    ∃ t ∈ Set.Ioc xL xH, ∃ t' ∈ Set.Ico xL xH,
      t ≤ t' ∧
      p.dynamicTopLockInStepF E.V_S E.α t = t ∧
      p.dynamicTopLockInStepF E.V_S E.α t' = t' ∧
      (∀ x₀ ∈ Set.Ico 0 t,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 0)) ∧
      (∀ x₀ ∈ Set.Ioc t' 1,
        Filter.Tendsto (p.dynamicTopLockInPathF E.V_S E.α x₀) Filter.atTop
          (𝓝 1)) ∧
      (t = t' ↔ ∀ y ∈ Set.Icc xL xH, ∀ z ∈ Set.Icc xL xH,
        p.dynamicTopLockInStepF E.V_S E.α y = y →
        p.dynamicTopLockInStepF E.V_S E.α z = z → y = z) :=
  p.equilibriumTop_derived_dual_basins' E hlo hmid hhi hrule_cont hlow_erode hhigh_build
    (fun _ hx => (p.dynamicTopLockInStepF_mem_I_of_mem_I E.V_S E.α hx).1)
    (fun _ hx => (p.dynamicTopLockInStepF_mem_I_of_mem_I E.V_S E.α hx).2)

end Params
end AbstractGame

end

end Sanctions
