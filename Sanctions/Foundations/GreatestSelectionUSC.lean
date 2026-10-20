/-
Sanctions/Foundations/GreatestSelectionUSC.lean

**The greatest maximizer of a parameter-dependent objective need not be upper
semicontinuous in the parameter — even when the objective is bounded and the
action set is compact.**

## What this settles, and what it does not

A recurring hope in this development is that the follower's response could be
kept well-behaved by *retyping* it: if the continuation value were allowed to be
merely upper semicontinuous rather than continuous, perhaps the
greatest-selection rule would inherit upper semicontinuity, Weierstrass would
still give the leader an attained maximum, and the continuity field `hα` of
`FeedbackStackelbergEquilibriumTop` — the requirement that the Target's optimal
compliance never jump as entrenchment varies — would become unnecessary.

**It does not.** The economy below is a counterexample, and it is admissible:
the transition `F x s = (x + s)/2` is continuous, monotone in each argument,
maps the unit square into itself, and satisfies `F x x = x`. The follower's
stage payoff is identically zero, the follower discounts at `1/2`, and the
continuation value is the indicator of `[0, 1/4]` — bounded, and upper
semicontinuous, since the indicator of a closed set is.

At those data the follower's best-reply set is `[0, 1/2 − x]` while `x ≤ 1/2`,
and jumps to the whole action set `[0,1]` the moment `x > 1/2`, because past
that threshold no action reaches the region the follower values and every action
is therefore optimal. The greatest selection is `1/2 − x`, then `1`: value `0`
at `x = 1/2` and value `1` immediately to the right, so it fails upper
semicontinuity at that single point.

Economically: once entrenchment passes the level from which a sanction can no
longer pull the state back into the region the Sender values, the Sender becomes
*indifferent across every sanction*, and a rule breaking ties toward the harshest
sanction jumps discontinuously. Indifference, not conflict, is what breaks the
selection.

## The honest scope of this (read before citing it)

This refutes the **general propagation lemma** — that greatest selections of
upper semicontinuous objectives are upper semicontinuous, which is what a library
supporting the retyping would have had to prove. It does **not** show that the
value functions the Bellman recursion actually reaches fail to be upper
semicontinuous, and it is **not** a nonexistence result for equilibrium.

The literature cuts the other way on existence: Caruso–Ceparano–Morgan (2024,
Prop. 3.1) gives a nonempty closed lower-Stackelberg equilibrium set when the
follower correspondence is continuous and compact-valued and the leader's payoff
is *continuous* — with no argmax uniqueness and no continuous selection. So what
this leaves standing is "continuity of the leader's value under a discontinuous
selector", not "upper semicontinuity fails to propagate". The route dies; the
wall stays a wall rather than becoming an impossibility theorem.

## Rule 19

External theory: a counterexample about greatest selections of argmax
correspondences on the reals. No `Params`, no sanctions, no value functions. The
objective is written out directly rather than through the game's operators
precisely so the counterexample cannot be dismissed as an artifact of the wiring.

**Why this belongs in `Foundations/` and not in `Examples/`.** It is the
*necessity fence* on a positive result that already lives here:
`Foundations/Berge.lean`'s `argmax_continuous` shows an argmax selection is
continuous when the objective is strictly concave in the action. This file shows
what that strict concavity is buying — drop it, and the greatest-argmax selection
is not merely discontinuous but not even upper semicontinuous. The two are the
two halves of one library statement about argmax selections on the reals, and
neither mentions the sanctions game. A relocation to `Examples/` was considered
on 2026-08-31 and declined: `Sanctions/Examples.lean` states its own admission
test — a relocated witness must not sit in the library whose theorems it
certifies — and this file imports no `Foundations` module, so it fails that test.
-/

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

namespace Sanctions.GreatestSelectionUSC

open Set Filter Topology

/-! ## 1. The objective and its greatest maximizer -/

/-- **The follower's objective at the counterexample economy.**

This is `β_S * V_S (F x s)` with `β_S = 1/2`, `F x s = (x+s)/2`, and `V_S` the
indicator of `[0, 1/4]`, rescaled by `2` so the value is `0` or `1` rather than
`0` or `1/2` — a rescaling changes no argmax. The condition `(x+s)/2 ≤ 1/4` is
`x + s ≤ 1/2`. -/
noncomputable def obj (x s : ℝ) : ℝ := if x + s ≤ 1/2 then 1 else 0

/-- **The greatest-maximizer selection.** Below the threshold the follower is
held to `s ≤ 1/2 − x`, whose largest member is `1/2 − x`; above it the follower
is indifferent and the largest action is `1`. -/
noncomputable def topSel (x : ℝ) : ℝ := if x ≤ 1/2 then 1/2 - x else 1

theorem topSel_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : topSel x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  unfold topSel; split_ifs with h <;> constructor <;> linarith

/-- `topSel x` is a maximizer of the objective over the action set. -/
theorem topSel_isMaxOn {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (obj x) (Icc (0 : ℝ) 1) (topSel x) := by
  obtain ⟨h0, h1⟩ := hx
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  simp only [Set.mem_setOf_eq, obj, topSel]
  split_ifs <;> norm_num <;> linarith

/-- …and it is the *greatest* one: every maximizer is at most `topSel x`. -/
theorem topSel_greatest {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hmax : IsMaxOn (obj x) (Icc (0 : ℝ) 1) s) :
    s ≤ topSel x := by
  obtain ⟨h0, h1⟩ := hx
  obtain ⟨hs0, hs1⟩ := hs
  unfold topSel
  split_ifs with hxle
  · by_contra hcon
    rw [not_le] at hcon
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have hle := hmax h0mem
    simp only [Set.mem_setOf_eq, obj] at hle
    rw [if_pos (by linarith : x + 0 ≤ 1/2)] at hle
    rw [if_neg (by linarith : ¬ (x + s ≤ 1/2))] at hle
    linarith
  · exact hs1

/-- The packaged statement: `topSel x` is the greatest maximizer. -/
theorem topSel_isGreatest {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IsGreatest {s | s ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (obj x) (Icc (0 : ℝ) 1) s} (topSel x) :=
  ⟨⟨topSel_mem hx, topSel_isMaxOn hx⟩,
   fun _ hs => topSel_greatest hx hs.1 hs.2⟩

/-! ## 2. The failure -/

theorem topSel_half : topSel (1/2 : ℝ) = 0 := by
  unfold topSel; rw [if_pos (le_refl _)]; norm_num

theorem topSel_of_gt {x : ℝ} (hx : 1/2 < x) : topSel x = 1 := by
  unfold topSel; rw [if_neg (by linarith)]

/-- **The greatest selection is not upper semicontinuous.**

At the threshold state `1/2` the selection is `0`, but every neighbourhood of
`1/2` contains states above it where the selection is `1`. So the leader's
reduced objective, read through this selector, can fail to attain its maximum —
and no amount of upper semicontinuity in the *continuation value* repairs it. -/
theorem not_upperSemicontinuousAt_topSel :
    ¬ UpperSemicontinuousAt topSel (1/2 : ℝ) := by
  rw [upperSemicontinuousAt_iff]
  intro h
  have hev := h (1/2) (by rw [topSel_half]; norm_num)
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
  obtain ⟨ε, hε, hsub⟩ := hev
  set x := (1/2 : ℝ) + min ε 1 / 2 with hxdef
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have hxgt : 1/2 < x := by simp only [hxdef]; linarith
  have hxball : x ∈ Metric.ball (1/2 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have h2 : min ε 1 ≤ ε := min_le_left _ _
    simp only [hxdef]
    rw [abs_of_pos (by linarith)]
    linarith
  have hlt := hsub hxball
  simp only [Set.mem_setOf_eq] at hlt
  rw [topSel_of_gt hxgt] at hlt
  linarith

/-- **Corollary: the propagation lemma is false.** There is no theorem of the
form "greatest selections of bounded objectives on a compact action set are upper
semicontinuous in the parameter", since `obj` is bounded and its greatest
selection is not. -/
theorem no_general_usc_propagation :
    ¬ (∀ g : ℝ → ℝ → ℝ, (∀ x s, g x s ∈ Icc (0 : ℝ) 1) →
        ∀ sel : ℝ → ℝ,
          (∀ x ∈ Icc (0 : ℝ) 1,
            IsGreatest {s | s ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (g x) (Icc (0 : ℝ) 1) s} (sel x)) →
          UpperSemicontinuousAt sel (1/2 : ℝ)) := by
  intro h
  refine not_upperSemicontinuousAt_topSel (h obj ?_ topSel (fun x hx => topSel_isGreatest hx))
  intro x s
  unfold obj; split_ifs <;> constructor <;> norm_num

end Sanctions.GreatestSelectionUSC
