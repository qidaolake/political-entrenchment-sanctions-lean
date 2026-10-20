/-
Sanctions/Theory/Equilibrium/ArgmaxUniquenessFromConcavity.lean

**Strict-concavity ⇒ argmax uniqueness helpers, with the stage /
dynamic distinction made explicit.**

The audit-47 critique noted that `DynamicArgmaxUnique` and
`TargetArgmaxUnique` are paper-facing awkward as abstract
regularity assumptions. The standard economic primitive that
discharges both is **strict concavity** of the relevant objective
on `Sanctions.I`. This file packages that derivation as two
helper theorems:

* `dynamicArgmaxUnique_of_strictConcaveOn` — derives
  `p.DynamicArgmaxUnique V_S` from strict concavity of the Sender
  dynamic objective `s ↦ U_S(x,a,s) + β_S · V_S(F(x,s))`.
* `targetArgmaxUnique_of_strictConcaveOn` — derives
  `p.TargetArgmaxUnique V_T V_S` from strict concavity of the
  joint Target integrand `a ↦ joint_T_integrand V_T V_S x a` in
  `a` on `Sanctions.I`.
* `senderStage_isMaxOn_unique_of_strictConcaveOn` — derives only
  uniqueness of a **stage** Sender maximizer from strict concavity of
  `s ↦ U_S(x,a,s)`.
* `stage_strictConcavity_does_not_force_dynamic_uniqueness` — a
  kernel-checked counterexample in which a strictly concave stage term
  is exactly offset by the continuation term, leaving every feasible
  action dynamically optimal.

Both proofs use the standard fact: a strictly concave function on
a convex set has at most one maximizer (if two distinct points
attained the max, their midpoint would have strictly greater value,
contradicting maximality).

## Rule compliance

Rule 1 ✓ (no strategies). Rule 3 — both helpers are pure
discharges of EXISTING `DynamicArgmaxUnique` / `TargetArgmaxUnique`
predicates from the canonical economic primitive (strict
concavity).

**Audit-48 wording correction.** Strict concavity is *not* logically
weaker than uniqueness — generically it is logically *stronger*
(strict concavity implies uniqueness, but a function with a unique
maximizer need not be strictly concave). The economic value is
that strict concavity is a **more interpretable / canonical
sufficient condition** for uniqueness; a JET referee will recognize
strict concavity as primitive economic content, whereas abstract
"unique-argmax" predicates look like assuming the conclusion.

The category-3 classification of the dynamic-objective helper is therefore
"interpretability improvement," not "category-2 weakening": the
user can still hypothesize `DynamicArgmaxUnique` / `TargetArgmaxUnique`
directly if their model gives uniqueness without strict concavity.

Crucially, strict concavity of the **stage payoff alone** is not a
premise of `dynamicArgmaxUnique_of_strictConcaveOn`.  That theorem
requires strict concavity of the complete Bellman objective, including
the continuation term.  Stage concavity by itself proves only the
stage-level helper below.

Rule 5 ✓ (fully parametric over `V_T`, `V_S`).
-/

import Sanctions.Theory.Equilibrium.SelectionRobust
import Sanctions.Theory.Equilibrium.TargetSelectorFromUnique
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Foundations.MilgromShannon
-- The generic midpoint argument, lifted to `Foundations/` on 2026-08-17 so the
-- convex-analysis content is citable independently of the game (Rule 19).
import Sanctions.Foundations.ConcaveArgmax
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Generic strict-concavity ⇒ argmax-uniqueness lemma -/

/-- **Strictly concave ⇒ at most one maximizer.** A strictly
concave function `f` on a convex set `S` has the property that any
two `IsMaxOn`-witnesses agree. The proof is the standard midpoint
argument: if `s₁ ≠ s₂` both attained the maximum, strict concavity
would give `f((s₁+s₂)/2) > (f s₁ + f s₂)/2 = f-max`, contradicting
maximality at the midpoint. -/
theorem isMaxOn_unique_of_strictConcaveOn
    {f : ℝ → ℝ} {S : Set ℝ}
    (hconc : StrictConcaveOn ℝ S f)
    {s₁ s₂ : ℝ}
    (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S)
    (h₁ : IsMaxOn f S s₁) (h₂ : IsMaxOn f S s₂) :
    s₁ = s₂ :=
  -- Statement unchanged; the midpoint argument now lives in `Foundations/`
  -- (2026-08-17) so that the convex analysis is citable without the game.
  Sanctions.ConcaveArgmax.eq_of_isMaxOn_of_strictConcaveOn hconc hs₁ hs₂
    (fun _ hy => h₁ hy) (fun _ hy => h₂ hy)

/-! ## What stage strict concavity does, and does not, imply -/

/-- **Strict concavity of the Sender stage payoff gives stage-argmax
uniqueness only.**

No continuation value or transition appears in either the hypothesis
or conclusion.  To obtain `DynamicArgmaxUnique`, callers must instead
establish strict concavity (or another uniqueness condition) for the
complete dynamic objective. -/
theorem senderStage_isMaxOn_unique_of_strictConcaveOn
    (hconc :
      ∀ x ∈ Sanctions.S, ∀ a : ℝ,
        StrictConcaveOn ℝ Sanctions.I (fun s => p.U_S x a s)) :
    ∀ x ∈ Sanctions.S, ∀ a : ℝ, ∀ {s₁ s₂ : ℝ},
      s₁ ∈ Sanctions.I →
      s₂ ∈ Sanctions.I →
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I s₁ →
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I s₂ →
      s₁ = s₂ := by
  intro x hx a s₁ s₂ hs₁ hs₂ hmax₁ hmax₂
  exact
    isMaxOn_unique_of_strictConcaveOn
      (hconc x hx a) hs₁ hs₂ hmax₁ hmax₂

/-- **Counterexample: stage strict concavity does not force dynamic
argmax uniqueness.**

Take the stage component `-s²` and the continuation component `s²`.
The stage component is strictly concave on `[0,1]`, but their sum is
identically zero, so both `0` and `1` are dynamic maximizers.  This
formalizes why an A3-style stage-curvature assumption cannot by itself
discharge `DynamicArgmaxUnique`. -/
theorem stage_strictConcavity_does_not_force_dynamic_uniqueness :
    ∃ (stage continuation : ℝ → ℝ),
      StrictConcaveOn ℝ Sanctions.I stage ∧
      (∀ s : ℝ, stage s + continuation s = 0) ∧
      ∃ s₁ ∈ Sanctions.I, ∃ s₂ ∈ Sanctions.I,
        s₁ ≠ s₂ ∧
        IsMaxOn (fun s => stage s + continuation s)
          Sanctions.I s₁ ∧
        IsMaxOn (fun s => stage s + continuation s)
          Sanctions.I s₂ := by
  let stage : ℝ → ℝ := fun s => -(s^2)
  let continuation : ℝ → ℝ := fun s => s^2
  have hconc_univ : StrictConcaveOn ℝ Set.univ stage := by
    dsimp [stage]
    apply strictConcaveOn_univ_of_deriv2_neg
    · fun_prop
    · intro x
      have hfirst :
          deriv (fun y : ℝ => -(y^2)) = fun y => -(2*y) := by
        funext y
        simpa using ((hasDerivAt_pow 2 y).neg.deriv)
      have hsecond :
          deriv (fun y : ℝ => -(2*y)) x = -2 := by
        simpa [mul_comm] using
          ((hasDerivAt_id x).const_mul (-2 : ℝ)).deriv
      rw [show (deriv^[2]) (fun y : ℝ => -(y^2)) x =
          deriv (deriv (fun y : ℝ => -(y^2))) x by rfl]
      rw [hfirst, hsecond]
      norm_num
  have hconc : StrictConcaveOn ℝ Sanctions.I stage :=
    hconc_univ.subset (Set.subset_univ _)
      (convex_Icc (0 : ℝ) 1)
  refine
    ⟨stage, continuation, hconc, ?_,
      0, ?_, 1, ?_, by norm_num, ?_, ?_⟩
  · intro s
    simp [stage, continuation]
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · intro s hs
    simp [stage, continuation]
  · intro s hs
    simp [stage, continuation]

/-! ## Discharger for `DynamicArgmaxUnique` -/

/-- **Strict concavity of the Sender dynamic objective ⇒
`DynamicArgmaxUnique V_S`.** If the function
`s ↦ U_S(x, a, s) + β_S · V_S(F(x, s))` is strictly concave on
`Sanctions.I` for every `(x, a)`, then any two `IsMaxOn`-witnesses
of that objective on `Sanctions.I` agree. -/
theorem dynamicArgmaxUnique_of_strictConcaveOn
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hconc : ∀ x ∈ Sanctions.S, ∀ a : ℝ,
      StrictConcaveOn ℝ Sanctions.I
        (fun s => p.U_S x a s
          + p.β_S * V_S
              (Sanctions.clipS' (p.F x s)))) :
    p.DynamicArgmaxUnique V_S := by
  intro x hx a s₁ s₂ hs₁_mem hs₂_mem h₁ h₂
  exact isMaxOn_unique_of_strictConcaveOn (hconc x hx a) hs₁_mem hs₂_mem h₁ h₂

/-! ## Discharger for `TargetArgmaxUnique` -/

/-- **Strict concavity of the joint Target integrand ⇒
`TargetArgmaxUnique V_T V_S`.** If the function
`a ↦ joint_T_integrand V_T V_S x a` is strictly concave on
`Sanctions.I` for every `x`, then any two `IsMaxOn`-witnesses of
that integrand on `Sanctions.I` agree. -/
theorem targetArgmaxUnique_of_strictConcaveOn
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hconc : ∀ x ∈ Sanctions.S,
      StrictConcaveOn ℝ Sanctions.I
        (fun a => p.joint_T_integrand V_T V_S x a)) :
    p.TargetArgmaxUnique V_T V_S := by
  intro x hx a₁ a₂ ha₁_mem ha₂_mem h₁ h₂
  exact isMaxOn_unique_of_strictConcaveOn (hconc x hx) ha₁_mem ha₂_mem h₁ h₂

/-! ## Round-24: StrictMonoOn-based dischargers (linear-payoff sibling)

The strict-concavity route above fails for linear per-period payoffs
(linear functions are not strictly concave), but the
`polyComplianceParams` witness in
`Sanctions/Examples/StandardCompliancePolynomialSkeleton.lean`
needs *some* uniqueness route at exactly the linear-`U_S` /
linear-in-`a`-`U_T` setting. The sibling dischargers below use the
*strict-monotonicity* form (Milgrom-Shannon §4 boundary-argmax
discussion): if the relevant single-variable objective is strictly
monotone on `Sanctions.I`, then it has a unique maximizer (the upper
boundary), so the uniqueness predicate is satisfied.

Both wrappers are one-line corollaries of
`Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn`, mirroring
the structure of the strict-concavity dischargers above. -/

/-- **Strict monotonicity of the Sender dynamic objective ⇒
`DynamicArgmaxUnique V_S`.** If the function
`s ↦ U_S(x, a, s) + β_S · V_S(F(x, s))` is strictly monotone on
`Sanctions.I` for every `(x, a)`, then any two `IsMaxOn`-witnesses
of that objective on `Sanctions.I` agree. Use this sibling discharger
when the Sender payoff is linear in `s` (e.g. `U_S = s`), where strict
concavity fails. -/
theorem dynamicArgmaxUnique_of_strictMonoOn
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hmono : ∀ x ∈ Sanctions.S, ∀ a : ℝ,
      StrictMonoOn
        (fun s => p.U_S x a s
          + p.β_S * V_S
              (Sanctions.clipS' (p.F x s)))
        Sanctions.I) :
    p.DynamicArgmaxUnique V_S := by
  intro x hx a s₁ s₂ hs₁_mem hs₂_mem h₁ h₂
  exact Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
    (hmono x hx a) hs₁_mem hs₂_mem h₁ h₂

/-- **Strict monotonicity of the joint Target integrand ⇒
`TargetArgmaxUnique V_T V_S`.** If the function
`a ↦ joint_T_integrand V_T V_S x a` is strictly monotone on
`Sanctions.I` for every `x`, then any two `IsMaxOn`-witnesses of that
integrand on `Sanctions.I` agree. Use this sibling discharger when the
Target integrand is linear (or merely strictly monotone) in `a`, where
strict concavity fails. -/
theorem targetArgmaxUnique_of_strictMonoOn
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hmono : ∀ x ∈ Sanctions.S,
      StrictMonoOn (fun a => p.joint_T_integrand V_T V_S x a)
        Sanctions.I) :
    p.TargetArgmaxUnique V_T V_S := by
  intro x hx a₁ a₂ ha₁_mem ha₂_mem h₁ h₂
  exact Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
    (hmono x hx) ha₁_mem ha₂_mem h₁ h₂

/-! ## Carrier-set forms (2026-08-17)

The two dischargers above are stated at a single value function. The ball
constructors need them quantified over a carrier *set*, and the distinction is
not cosmetic: `ValueClass.ofLipBall` consumes

```text
∀ V_S ∈ valLipBall M K, DynamicArgmaxUnique V_S
```

**in order to build the value class**. A discharger phrased in terms of
`D.carrier` therefore cannot be used to produce `D` — it would need the object it
is helping to construct. Phrasing the hypothesis over a bare `Set Val` breaks
that: the carrier set is known before the value class exists.

These are the forms `ofBall`, `ofLipBall` and `ofLipGainBall` take directly. -/

/-- **Carrier-set form of the Sender discharger.** Circularity-free: quantified
over a set, not over a `ValueClass` that does not yet exist. -/
theorem dynamicArgmaxUnique_on_set_of_strictConcaveOn
    {C : Set (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    (hconc : ∀ V_S ∈ C, ∀ x ∈ Sanctions.S, ∀ a : ℝ,
      StrictConcaveOn ℝ Sanctions.I
        (fun s => p.U_S x a s
          + p.β_S * V_S (Sanctions.clipS' (p.F x s)))) :
    ∀ V_S ∈ C, p.DynamicArgmaxUnique V_S :=
  fun _ hV_S => p.dynamicArgmaxUnique_of_strictConcaveOn (hconc _ hV_S)

/-- **Carrier-set form of the leader discharger.** Pairwise over the carrier, in
the shape the ball constructors consume. -/
theorem targetArgmaxUnique_on_set_of_strictConcaveOn
    {C : Set (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    (hconc : ∀ V_T ∈ C, ∀ V_S ∈ C, ∀ x ∈ Sanctions.S,
      StrictConcaveOn ℝ Sanctions.I
        (fun a => p.joint_T_integrand V_T V_S x a)) :
    ∀ V_T ∈ C, ∀ V_S ∈ C, p.TargetArgmaxUnique V_T V_S :=
  fun _ hV_T _ hV_S => p.targetArgmaxUnique_of_strictConcaveOn (hconc _ hV_T _ hV_S)

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
