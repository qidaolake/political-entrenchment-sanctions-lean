/-
Sanctions/Examples/SelectorShapeNotPreserved.lean

**The moving argmax destroys curvature too — and it does so under an affine
transition.**

`TransitionShapeNotPreserved.lean` shows that the maintained transition class
alone admits members no curvature cone survives. That leaves open whether the
failure is *only* about the transition, and whether restricting to an affine law
would restore a curvature carrier. It would not, and this file is the reason.

Take the transition that adjusts fully to the current sanction,

    F x s = s,

which is affine in both arguments and is the extreme point of the affine family.
Give the Sender the single-peaked stage loss

    U_S x a s = -(s - (2x - 1/2))^2,

whose ideal sanction `2x - 1/2` rises with the political state and leaves the
feasible interval at both ends. The Sender's genuine stage argmax is then the
clamp

    σ x a = clipS (2x - 1/2),

an optimisation result at every state and compliance level (Rule 1), which is
*unique*, *continuous*, *monotone* and *Lipschitz* — hence simultaneously the
least, the greatest, the optimistic and the pessimistic selection, so no choice
of selection convention can evade what follows.

The closed loop is `x ↦ clipS (2x - 1/2)`, and it has two kinks of opposite sign:
the slope rises from `0` to `2` at `x = 1/4`, where the clamp releases at the
bottom, and falls from `2` to `0` at `x = 3/4`, where it binds at the top. The
first kills every semiconcavity modulus and the second every semiconvexity
modulus, so this single economy refutes both one-sided cones at once.

**Why the two files are independent.** In `TransitionShapeNotPreserved.lean` the
sanction is constant and the transition supplies the kink; here the transition is
affine and the *selection* supplies it. Neither result implies the other, and an
architecture note that cites only one of them is describing half the obstruction.
This is the one-dimensional form of the phenomenon Chen, Li and So isolate for
bilevel programs (arXiv:2506.04587, Example 3): a lower-level problem that is
smooth and strongly convex, with a unique Lipschitz solution, can still produce a
reduced objective with no weak-convexity modulus, because the solution meets a
constraint boundary. The kink is created by the active set, not by any
irregularity of the payoff.

**What this licenses, and what it does not** (Rule 9). It refutes universals: no
theorem asserts that the closed-loop successor map is semiconvex, or
semiconcave, for some modulus, uniformly over economies — not even over affine
ones. It says nothing about any particular calibrated economy, and it does not
show that *some* weaker invariant fails; order cones and Lipschitz cones survive
this example untouched, which is precisely why the development's carriers are
built from those.

Rule 3: no new assumption. Rule 22: the transition here is affine deliberately,
because affineness is what the example is designed *not* to need.
-/
import Sanctions.Postulates.AbstractGame
import Sanctions.Domain.UnitIntervalProjection
import Sanctions.Foundations.SemiconvexityDefect

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame

/-- The Sender's ideal sanction at state `x`: rising, and leaving `[0,1]` at both
ends of the feasible state space. -/
def peakS (x : ℝ) : ℝ := 2 * x - 1 / 2

/-- **The clamp is the nearest feasible point**, hence the stage argmax of a
single-peaked quadratic loss. -/
theorem clipS_sq_le (m : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (Sanctions.clipS m - m) ^ 2 ≤ (s - m) ^ 2 := by
  obtain ⟨hs0, hs1⟩ := hs
  rcases le_total m 0 with hm | hm
  · have h : Sanctions.clipS m = 0 := by
      simp only [Sanctions.clipS]
      rw [min_eq_right (by linarith : m ≤ 1), max_eq_left hm]
    rw [h]; nlinarith
  · rcases le_total m 1 with hm1 | hm1
    · have h : Sanctions.clipS m = m := by
        simp only [Sanctions.clipS]
        rw [min_eq_right hm1, max_eq_right hm]
      rw [h]; nlinarith [sq_nonneg (s - m)]
    · have h : Sanctions.clipS m = 1 := by
        simp only [Sanctions.clipS]
        rw [min_eq_left hm1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      rw [h]; nlinarith

/-- **Full adjustment, with a state-dependent clamped optimal sanction.**

The transition adjusts completely to the current sanction — affine, and the
extreme point of the affine family — while the Sender's stage problem is a
single-peaked loss whose peak `2x - 1/2` walks out of the feasible interval at
both ends. -/
def Params.clampedPeakSender (p : Params) : Params :=
  { p with
    F := fun _ s => s
    F_continuous := continuous_snd
    F_mono_x := fun _ _ _ _ => le_rfl
    F_mono_s := fun _ _ _ h => h
    F_diag := fun _ => rfl
    U_S := fun x _ s => -(s - peakS x) ^ 2
    U_S_continuous := by unfold peakS; fun_prop
    σ := fun x _ => Sanctions.clipS (peakS x)
    σ_mem := fun x _ => Sanctions.clipS_mem (peakS x)
    σ_isMaxOn_U_S := by
      intro x a s hs
      change -(s - peakS x) ^ 2 ≤ -(Sanctions.clipS (peakS x) - peakS x) ^ 2
      have := clipS_sq_le (peakS x) hs
      linarith }

/-- **`Params.clampedPeakSender` has a continuous static Sender selector.** A
transformation with the full-adjustment transition `F x s = s`; the selector, the clamp of
the peak `2x - 1/2`, does not read the transition. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance Params.clampedPeakSender_staticSelectorContinuous (p : Params) :
    (Params.clampedPeakSender p).StaticSelectorContinuous where
  σ_continuous := by
    have h : Continuous (fun xa : ℝ × ℝ => peakS xa.1) := by
      unfold peakS; fun_prop
    exact Sanctions.clipS_continuous.comp h

namespace Params

variable {p : Params}

@[simp] theorem clampedPeakSender_F (x s : ℝ) :
    p.clampedPeakSender.F x s = s := rfl

@[simp] theorem clampedPeakSender_sigma (x a : ℝ) :
    p.clampedPeakSender.σ x a = Sanctions.clipS (peakS x) := rfl

/-- **The clamped response really is the Sender's stage argmax** — unique,
continuous, monotone and Lipschitz, hence every selection convention at once
(Rule 1). -/
theorem clampedPeakSender_sigma_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => p.clampedPeakSender.U_S x a s) (Icc (0 : ℝ) 1)
      (p.clampedPeakSender.σ x a) :=
  p.clampedPeakSender.σ_isMaxOn_U_S x a

/-- The closed loop, written out: the next state is the clamped peak. -/
theorem clampedPeakSender_closedLoop (α : ℝ → ℝ) (x : ℝ) :
    p.clampedPeakSender.F x (p.clampedPeakSender.σ x (α x))
      = Sanctions.clipS (peakS x) := rfl

/-- **No semiconcavity modulus: the clamp releasing at the bottom is a convex
kink.** At `x = 1/4` the Sender's ideal sanction reaches `0` and the response
starts to move, so the closed-loop slope jumps from `0` to `2`. -/
theorem clampedPeakSender_closedLoop_not_semiconcave (α : ℝ → ℝ) :
    ¬ ∃ ρ : ℝ, Sanctions.Semiconcave.SemiconcaveOnSet
      (fun x => p.clampedPeakSender.F x (p.clampedPeakSender.σ x (α x)))
      Sanctions.I ρ := by
  refine Sanctions.not_semiconcaveOnSet_of_linearDefect (t := 1/4) (d := 1/4)
    (by norm_num) ?_ ?_ ?_
  · intro ε hε hle; exact ⟨by linarith, by linarith⟩
  · intro ε hε hle; exact ⟨by linarith, by linarith⟩
  · intro ε hε hle
    change 2 * Sanctions.clipS (peakS (1/4)) + ε
      ≤ Sanctions.clipS (peakS (1/4 - ε)) + Sanctions.clipS (peakS (1/4 + ε))
    have e0 : Sanctions.clipS (peakS (1/4)) = 0 := by
      have h : peakS (1/4) = 0 := by unfold peakS; norm_num
      rw [h]; simp only [Sanctions.clipS]; norm_num
    have eL : Sanctions.clipS (peakS (1/4 - ε)) = 0 := by
      have h : peakS (1/4 - ε) = -(2 * ε) := by unfold peakS; ring
      rw [h]; simp only [Sanctions.clipS]
      rw [min_eq_right (by linarith : -(2 * ε) ≤ 1),
        max_eq_left (by linarith : -(2 * ε) ≤ 0)]
    have eR : Sanctions.clipS (peakS (1/4 + ε)) = 2 * ε := by
      have h : peakS (1/4 + ε) = 2 * ε := by unfold peakS; ring
      rw [h]; simp only [Sanctions.clipS]
      rw [min_eq_right (by linarith : 2 * ε ≤ 1),
        max_eq_right (by linarith : (0 : ℝ) ≤ 2 * ε)]
    rw [e0, eL, eR]; linarith

/-- **No semiconvexity modulus: the clamp binding at the top is a concave
kink.** At `x = 3/4` the Sender's ideal sanction reaches `1` and the response
stops moving, so the closed-loop slope falls from `2` to `0`.

Together with the previous theorem, one economy — affine transition, unique
Lipschitz monotone optimal response — refutes both one-sided curvature cones. -/
theorem clampedPeakSender_closedLoop_not_semiconvex (α : ℝ → ℝ) :
    ¬ ∃ ρ : ℝ, Sanctions.Semiconcave.SemiconvexOnSet
      (fun x => p.clampedPeakSender.F x (p.clampedPeakSender.σ x (α x)))
      Sanctions.I ρ := by
  refine Sanctions.not_semiconvexOnSet_of_linearDefect (t := 3/4) (d := 1/4)
    (by norm_num) ?_ ?_ ?_
  · intro ε hε hle; exact ⟨by linarith, by linarith⟩
  · intro ε hε hle; exact ⟨by linarith, by linarith⟩
  · intro ε hε hle
    change Sanctions.clipS (peakS (3/4 - ε)) + Sanctions.clipS (peakS (3/4 + ε)) + ε
      ≤ 2 * Sanctions.clipS (peakS (3/4))
    have e0 : Sanctions.clipS (peakS (3/4)) = 1 := by
      have h : peakS (3/4) = 1 := by unfold peakS; norm_num
      rw [h]; simp only [Sanctions.clipS]; norm_num
    have eL : Sanctions.clipS (peakS (3/4 - ε)) = 1 - 2 * ε := by
      have h : peakS (3/4 - ε) = 1 - 2 * ε := by unfold peakS; ring
      rw [h]; simp only [Sanctions.clipS]
      rw [min_eq_right (by linarith : 1 - 2 * ε ≤ 1),
        max_eq_right (by linarith : (0 : ℝ) ≤ 1 - 2 * ε)]
    have eR : Sanctions.clipS (peakS (3/4 + ε)) = 1 := by
      have h : peakS (3/4 + ε) = 1 + 2 * ε := by unfold peakS; ring
      rw [h]; simp only [Sanctions.clipS]
      rw [min_eq_left (by linarith : (1 : ℝ) ≤ 1 + 2 * ε),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    rw [e0, eL, eR]; linarith

end Params
end AbstractGame

end

end Sanctions
