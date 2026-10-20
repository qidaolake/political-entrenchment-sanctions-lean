/-
Sanctions/Foundations/BoundedMeasurable.lean

**Substrate for retyping the value carrier from bounded *continuous* to bounded
*measurable* functions.**

## The problem this addresses

`FeedbackStackelbergEquilibriumTop` (in `Theory/Basin/JointPreferenceBasin.lean`)
carries a field whose own docstring concedes why it is there:

```lean
/-- Continuity of α, for `bellmanS_BCF` compatibility. -/
hα : Continuous α
```

*For compatibility.* Value functions are typed `↥S →ᵇ ℝ` — bounded **continuous**
— so the Sender Bellman operator can only return to that space if the leader's
policy `α` is continuous. Continuity of `α` in turn forces the leader's argmax to
be a singleton moving continuously, which needs strict concavity of the
σ-substituted Target objective; the project's own design note reports that this
fails even in the linear-quadratic case, because the Sender's response has regime
boundaries that put kinks in it.

Economically the requirement is not merely unnecessary but **wrong for this
model**. `Continuous α` says the Target's optimal compliance never jumps as
political entrenchment varies. The phenomenon under study is lock-in: at a
critical entrenchment level the incumbent switches from accommodation to
defiance. A continuous policy forbids exactly the discontinuity the paper exists
to explain. And every existence theorem in this literature — Levy, He–Sun,
Balbus–Reffett–Woźny, Escobar, Bucarey — defines stationary strategies as
**measurable**, never continuous.

## What retyping needs, and what is here

Several obligations arise when `↥S →ᵇ ℝ` is replaced by bounded measurable
functions under the sup metric. This file supplies two *ingredients*. It does
**not** perform the migration, and the scope note in §"What is NOT here" below
is load-bearing — read it before citing this file.

1. **Measurability is preserved by uniform limits** —
   `measurable_of_uniform_limit` below. A sup-metric Cauchy sequence of
   measurable functions cannot leave the class, which is the *measurability*
   half of what completeness of such a carrier would need.

   This is an **ingredient for** completeness, not completeness: no carrier
   type, sup-norm, or `CompleteSpace` instance is built here, so nothing below
   licenses "the carrier is complete" or "Banach still applies" — see item 4 of
   §"What is NOT here", which is the governing statement where this summary and
   that section disagree.

2. **The state-wise supremum is measurable**, i.e. the sup over the action set
   of a measurable-in-state, continuous-in-action integrand is measurable in the
   state — `measurable_sSup_image` below, proved by reducing the supremum over
   the continuum of actions to a supremum over a countable dense sequence.

## What is NOT here (correction, 2026-08-31)

An earlier version of this header said the file "discharges the first two" of
three obligations and that action-continuity is "untouched by the retyping."
Both were wrong. Four separate obstructions remain, and `hα` **cannot** be
removed on the strength of anything below.

1. **Action continuity is *not* untouched.** The integrand's dependence on the
   action runs *through* the value function — the continuation term is
   `V (clipS' (F x s))`, and `s` is an action. Demoting `V` from continuous to
   merely measurable therefore breaks continuity in the action, which is exactly
   the hypothesis `measurable_sSup_image` needs. Concretely, with `F x s = s`
   and `V z = if 1/2 ≤ z then 1 else 0`, `V` is bounded and Borel while
   `s ↦ V (F x s)` is discontinuous. This is a real circularity in the migration
   plan, not a technicality.

2. **Measurability does not give attainment.** `g s = s` for `s < 1` and
   `g 1 = 0` is bounded and Borel on `[0,1]` with supremum `1` and no maximizer.
   Weierstrass is doing work that measurability alone will not do.

3. **Pointwise boundedness is not uniform boundedness.** The hypothesis `hbdd`
   of `measurable_sSup_image` is `BddAbove` *at each state*; its conclusion is
   `Measurable` and nothing more. Neither a uniform bound over states nor
   membership in a *bounded* measurable carrier follows.

4. **No carrier exists yet.** There is no `BoundedMeasurableFunction` type here,
   no sup-norm instance, and no `CompleteSpace` instance — so item 1 above is an
   ingredient for completeness, not a proof that any carrier is complete.

5. **A measurable selection of the argmax** — Kuratowski–Ryll-Nardzewski — is
   **not** built here and nothing in this file supplies it. Nothing downstream
   may consume a measurable selector until it is constructed (Rule 15).

So: the lemmas below are correct and reusable, and the retyping remains a
*staged research programme*, not a route that this file opens.

## Rule 19

External theory: measurability of suprema and of limits. No `Params`, no
sanctions, no value functions.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

namespace Sanctions.BddMeasurable

open Set Filter Topology MeasureTheory

variable {alpha : Type*} [MeasurableSpace alpha]

/-! ## 1. Measurability survives uniform limits

The measurability constraint is preserved under sup-metric limits. This is one
ingredient of completeness for a bounded-measurable carrier, not a proof that
any such carrier is complete, and not a licence to carry a contraction argument
across the retyping — see §"What is NOT here". Uniform convergence is stronger
than what is needed — pointwise suffices — which is stated first. -/

/-- **Measurability passes to pointwise limits.** A thin restatement of
`measurable_of_tendsto_metrizable` in the pointwise form that is convenient to
apply. -/
theorem measurable_of_pointwise_limit {f : ℕ → alpha → ℝ} {g : alpha → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Measurable g :=
  measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hlim)

/-- **The completeness ingredient.** If measurable functions converge *uniformly*
to `g`, then `g` is measurable — so the class of bounded measurable functions is
closed in the sup metric, and a Cauchy sequence produced by Banach iteration
cannot escape it.

This is the entire technical content of "the carrier is still complete": the
metric-space completeness of bounded functions under the sup metric is standard,
and measurability is the only extra constraint, which this shows is preserved. -/
theorem measurable_of_uniform_limit {f : ℕ → alpha → ℝ} {g : alpha → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |f n x - g x| ≤ ε) :
    Measurable g := by
  refine measurable_of_pointwise_limit hf (fun x => ?_)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hunif (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn x
  rw [Real.dist_eq]
  linarith

/-! ## 2. The Bellman image stays measurable

The operator takes a supremum over the action set. Over a continuum of actions
that is not automatically measurable in the state; the reduction below replaces
it with a supremum over a countable dense sequence of actions, which is. -/

/-- **The supremum over a dense sequence agrees with the supremum over the set.**

If `h` is continuous and `A` is contained in the closure of the range of a
sequence `u` taking values in `A`, then maximising over `A` and over the sequence
give the same value. Continuity is used only in the action variable. -/
theorem sSup_image_eq_iSup_of_dense
    {A : Set ℝ} {u : ℕ → ℝ} (hu : ∀ n, u n ∈ A)
    (hdense : A ⊆ closure (Set.range u))
    {h : ℝ → ℝ} (hcont : Continuous h)
    (hne : A.Nonempty) (hbdd : BddAbove (h '' A)) :
    sSup (h '' A) = ⨆ n, h (u n) := by
  have hbdd' : BddAbove (Set.range fun n => h (u n)) := by
    obtain ⟨C, hC⟩ := hbdd
    exact ⟨C, by rintro y ⟨n, rfl⟩; exact hC ⟨u n, hu n, rfl⟩⟩
  have hne' : (h '' A).Nonempty := hne.image h
  have hiSup_eq : (⨆ n, h (u n)) = sSup (Set.range fun n => h (u n)) := rfl
  refine le_antisymm ?_ ?_
  · -- Every value attained on `A` is a limit of values along the sequence.
    refine csSup_le hne' ?_
    rintro y ⟨a, haA, rfl⟩
    have hmem : a ∈ closure (Set.range u) := hdense haA
    rw [mem_closure_iff_seq_limit] at hmem
    obtain ⟨v, hv_mem, hv⟩ := hmem
    have hlim : Tendsto (fun k => h (v k)) atTop (𝓝 (h a)) :=
      (hcont.tendsto a).comp hv
    refine le_of_tendsto hlim ?_
    filter_upwards with k
    obtain ⟨n, hn⟩ := hv_mem k
    rw [hiSup_eq, ← hn]
    exact le_csSup hbdd' ⟨n, rfl⟩
  · rw [hiSup_eq]
    refine csSup_le ⟨h (u 0), ⟨0, rfl⟩⟩ ?_
    rintro y ⟨n, rfl⟩
    exact le_csSup hbdd ⟨u n, hu n, rfl⟩

/-- **The Bellman image is measurable.**

For an integrand measurable in the state at each fixed action and continuous in
the action at each fixed state, the state-wise supremum over the action set is
measurable. The action set enters only through a countable dense sequence, which
the unit interval of course has.

**Scope (corrected 2026-08-31).** The conclusion is `Measurable`, full stop. It
is *not* a proof that a Bellman operator maps a bounded measurable carrier into
itself: `hbdd` is `BddAbove` at each state separately, so no uniform bound over
states is available, and `hcont` — continuity in the action — is precisely what
a measurable value function fails to supply once the continuation is evaluated
at a state the action moves. See this file's header. -/
theorem measurable_sSup_image
    {g : alpha → ℝ → ℝ} {A : Set ℝ} {u : ℕ → ℝ}
    (hu : ∀ n, u n ∈ A) (hdense : A ⊆ closure (Set.range u))
    (hne : A.Nonempty)
    (hmeas : ∀ a : ℝ, Measurable fun x => g x a)
    (hcont : ∀ x, Continuous fun a => g x a)
    (hbdd : ∀ x, BddAbove ((fun a => g x a) '' A)) :
    Measurable fun x => sSup ((fun a => g x a) '' A) := by
  have hrw : (fun x => sSup ((fun a => g x a) '' A))
      = fun x => ⨆ n, g x (u n) := by
    funext x
    exact sSup_image_eq_iSup_of_dense hu hdense (hcont x) hne (hbdd x)
  rw [hrw]
  exact Measurable.iSup fun n => hmeas (u n)

end Sanctions.BddMeasurable
