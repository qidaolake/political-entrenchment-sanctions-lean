/-
Sanctions/Examples/TransitionShapeNotPreserved.lean

**The transition class alone destroys curvature — no coupling required.**

`Postulates/AbstractGame.lean` asks five things of the transition: it maps the
feasible square into itself, is continuous, is non-decreasing in each argument
separately, and fixes its diagonal (`F x x = x`). Rule 22 keeps every result
general in `F`, so any carrier the development might impose has to survive
*every* member of that class.

This file exhibits a member that no curvature cone survives. Take

    F x s = min x s

— a sanction below the state pulls the state down to it, a sanction above it
leaves the state alone. Every transition field holds, with `min t t = t` the
diagonal. Pair it with a Sender whose stage payoff is `-(s - c)^2`, so that the
constant sanction `c` is the Sender's genuine stage argmax at every state and
every compliance level (Rule 1: the rule is an optimisation result, not a
posited constant). The closed loop is then

    x ↦ F x c = min x c,

whose slope falls from `1` to `0` at `x = c`. That kink is a defect *linear* in
the chord width, while any semiconvexity modulus caps the defect *quadratically*,
so no modulus survives — `Foundations/SemiconvexityDefect.lean` isolates exactly
that argument.

**What this licenses, and what it does not** (Rule 9). It refutes a universal:
there is no theorem of the form "for every `p : Params`, the closed-loop
successor map is `c`-semiconvex for some `c`". It says nothing about whether any
*particular* economy of interest has the property, and nothing about the
non-affine witnesses this development actually uses. Its point is architectural:
a curvature cone cannot be imposed as a carrier over the general transition
class, so the first-order carriers this development does use
(`valLipGainBall` — sup-norm bound, Lipschitz bound, lower slope) are not a
stylistic preference but the available option.

The companion file `SelectorShapeNotPreserved.lean` shows the *second*, logically
independent obstruction: the same failure occurs with an affine transition once
the sanction is the other player's state-dependent argmax rather than a constant.
The two should not be conflated — neither implies the other.

Rule 3: no new assumption. Refuting a universal widens nothing; every field
below is discharged from the concrete data.
-/
import Sanctions.Postulates.AbstractGame
import Sanctions.Foundations.SemiconvexityDefect

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame

/-- **The lattice-meet transition, with a constant optimal sanction.**

Replaces a parameter vector's transition by `F x s = min x s` and its Sender
stage payoff by the single-peaked loss `-(s - c)^2`, whose stage argmax on
`[0,1]` is the constant `c`. Target preferences and both discount factors are
left untouched. -/
def Params.minMeetTransition (p : Params) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    Params :=
  { p with
    F := fun x s => min x s
    F_continuous := continuous_fst.min continuous_snd
    F_mono_x := fun _ _ _ h => min_le_min h le_rfl
    F_mono_s := fun _ _ _ h => min_le_min le_rfl h
    F_diag := fun x => min_self x
    U_S := fun _ _ s => -(s - c) ^ 2
    U_S_continuous := by fun_prop
    σ := fun _ _ => c
    σ_mem := fun _ _ => hc
    σ_isMaxOn_U_S := by
      intro x a s _
      change -(s - c) ^ 2 ≤ -(c - c) ^ 2
      simp only [sub_self]
      nlinarith [sq_nonneg (s - c)] }

/-- **`Params.minMeetTransition` has a continuous static Sender selector.** A
transformation with the meet transition `F x s = min x s` (not affine); the constant
selector does not read it. The proof is the one that was the economy's `σ_continuous`
field until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance Params.minMeetTransition_staticSelectorContinuous (p : Params) (c : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (Params.minMeetTransition p c hc).StaticSelectorContinuous where
  σ_continuous := continuous_const

/-- **The lattice-join transition, with the same constant optimal sanction.**
The mirror of `minMeetTransition`: a sanction above the state pulls the state up
to it, one below leaves it alone. -/
def Params.maxJoinTransition (p : Params) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) :
    Params :=
  { p with
    F := fun x s => max x s
    F_continuous := continuous_fst.max continuous_snd
    F_mono_x := fun _ _ _ h => max_le_max h le_rfl
    F_mono_s := fun _ _ _ h => max_le_max le_rfl h
    F_diag := fun x => max_self x
    U_S := fun _ _ s => -(s - c) ^ 2
    U_S_continuous := by fun_prop
    σ := fun _ _ => c
    σ_mem := fun _ _ => hc
    σ_isMaxOn_U_S := by
      intro x a s _
      change -(s - c) ^ 2 ≤ -(c - c) ^ 2
      simp only [sub_self]
      nlinarith [sq_nonneg (s - c)] }

/-- **`Params.maxJoinTransition` has a continuous static Sender selector.** A
transformation with the join transition `F x s = max x s` (not affine); the constant
selector does not read it. The proof is the one that was the economy's `σ_continuous`
field until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance Params.maxJoinTransition_staticSelectorContinuous (p : Params) (c : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (Params.maxJoinTransition p c hc).StaticSelectorContinuous where
  σ_continuous := continuous_const

namespace Params

variable {p : Params}

@[simp] theorem minMeetTransition_F (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (x s : ℝ) :
    (p.minMeetTransition c hc).F x s = min x s := rfl

@[simp] theorem minMeetTransition_sigma (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (x a : ℝ) :
    (p.minMeetTransition c hc).σ x a = c := rfl

/-- **The constant sanction really is the Sender's stage argmax**, so the closed
loop below is an equilibrium object and not an assumed policy (Rule 1). -/
theorem minMeetTransition_sigma_isMaxOn (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (x a : ℝ) :
    IsMaxOn (fun s => (p.minMeetTransition c hc).U_S x a s) (Icc (0 : ℝ) 1)
      ((p.minMeetTransition c hc).σ x a) :=
  (p.minMeetTransition c hc).σ_isMaxOn_U_S x a

/-- **The closed-loop successor map admits no semiconvexity modulus.**

Along the Sender's own optimal static rule, the next state as a function of the
current one is `x ↦ min x c`, and its slope drop at `x = c` defeats every
proposed modulus. The compliance policy `α` is arbitrary, because the Sender's
optimal response here does not depend on it — which is what makes the failure a
statement about the *transition*, with the strategic layer held fixed. -/
theorem minMeetTransition_closedLoop_not_semiconvex
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (α : ℝ → ℝ) :
    ¬ ∃ ρ : ℝ, Sanctions.Semiconcave.SemiconvexOnSet
      (fun x => (p.minMeetTransition c ⟨hc.1.le, hc.2.le⟩).F x
        ((p.minMeetTransition c ⟨hc.1.le, hc.2.le⟩).σ x (α x)))
      Sanctions.I ρ := by
  have hd : 0 < min c (1 - c) := lt_min hc.1 (by linarith [hc.2])
  refine Sanctions.not_semiconvexOnSet_of_linearDefect (t := c) hd ?_ ?_ ?_
  · intro ε hε hle
    have h1 : ε ≤ c := hle.trans (min_le_left _ _)
    exact ⟨by linarith, by linarith [hc.2]⟩
  · intro ε hε hle
    have h1 : ε ≤ 1 - c := hle.trans (min_le_right _ _)
    exact ⟨by linarith [hc.1], by linarith⟩
  · intro ε hε hle
    have h1 : ε ≤ c := hle.trans (min_le_left _ _)
    change min (c - ε) c + min (c + ε) c + ε ≤ 2 * min c c
    rw [min_self, min_eq_left (by linarith : c - ε ≤ c),
      min_eq_right (by linarith : c ≤ c + ε)]
    linarith

/-- **And the mirror: the join transition admits no semiconcavity modulus.**

Along the same constant optimal sanction the closed loop is `x ↦ max x c`, whose
slope *rises* at `x = c`. Stated so that neither one-sided cone can be claimed
for the class: the meet kills the semiconvex cone, the join kills the semiconcave
one, and both transitions are ordinary members of the maintained class. -/
theorem maxJoinTransition_closedLoop_not_semiconcave
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (α : ℝ → ℝ) :
    ¬ ∃ ρ : ℝ, Sanctions.Semiconcave.SemiconcaveOnSet
      (fun x => (p.maxJoinTransition c ⟨hc.1.le, hc.2.le⟩).F x
        ((p.maxJoinTransition c ⟨hc.1.le, hc.2.le⟩).σ x (α x)))
      Sanctions.I ρ := by
  have hd : 0 < min c (1 - c) := lt_min hc.1 (by linarith [hc.2])
  refine Sanctions.not_semiconcaveOnSet_of_linearDefect (t := c) hd ?_ ?_ ?_
  · intro ε hε hle
    have h1 : ε ≤ c := hle.trans (min_le_left _ _)
    exact ⟨by linarith, by linarith [hc.2]⟩
  · intro ε hε hle
    have h1 : ε ≤ 1 - c := hle.trans (min_le_right _ _)
    exact ⟨by linarith [hc.1], by linarith⟩
  · intro ε hε hle
    have h1 : ε ≤ 1 - c := hle.trans (min_le_right _ _)
    change 2 * max c c + ε ≤ max (c - ε) c + max (c + ε) c
    rw [max_self, max_eq_right (by linarith : c - ε ≤ c),
      max_eq_left (by linarith : c ≤ c + ε)]
    linarith

end Params
end AbstractGame

end

end Sanctions
