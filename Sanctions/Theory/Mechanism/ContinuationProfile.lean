/-
Sanctions/Theory/Mechanism/ContinuationProfile.lean

**Which government looks ahead: the four continuation regimes.**

The development compares two regimes — both governments forward-looking, or
neither. That identifies what the two continuation motives do *together*, and
nothing else. It cannot say which government caused which part of the change,
nor whether one government's dynamic motive changes the other's behaviour.

This file adds the missing axis. A `ContinuationProfile` switches each
government's continuation term independently, giving four regimes:

| profile | Target | Sender | the motive it isolates |
|---|---|---|---|
| `p00` | myopic | myopic | neither; the stage benchmark |
| `p10` | forward | myopic | **political preservation** — the Target endures more now because complying would shift tomorrow's political balance against it |
| `p01` | myopic | forward | **political investment** — the Sender departs from its best current sanction because today's sanction reshapes tomorrow's politics |
| `p11` | forward | forward | the full model |

**Index convention, which is load-bearing.** The first coordinate is always the
*Target*, the second the *Sender*. Reversing them would silently reverse every
economic interpretation in the factorial, so the profile is a structure with
*named* fields rather than a pair of `Bool`s, and the interaction below is
defined over a profile-indexed family rather than four positional arguments.
Neither can be scrambled by an argument-order slip.

## No new assumption is added here

`Params.β_T_mem` and `β_S_mem` place the discount factors in `Set.Ico 0 1` —
half-open, so **zero is already admissible**. A myopic regime is therefore a
legitimate `Params`, not a new object needing new axioms, and
`Params.withProfile` is a *view* of an economy rather than a different economy:
it changes the two discount factors and nothing else. Payoffs, the static
response, and the transition are carried across untouched.

The consequence is that no new equilibrium structure is needed either. A regime
equilibrium is `FeedbackStackelbergEquilibriumTop (p.withProfile c)` — the
existing structure read at the profile view — because every condition in it
routes through `p.β_T` and `p.β_S`. Setting a discount factor to zero collapses
that player's Bellman equation to its stage problem, which is what "myopic"
means.
-/

import Sanctions.Postulates.AbstractGame

namespace Sanctions
namespace Mechanism

open Set

/-! ## The profile -/

/-- **Which governments look ahead.** `targetForward` and `senderForward` say
whether the Target and the Sender respectively carry a continuation value.

Named fields, not a `Bool × Bool`: the whole factorial is uninterpretable if the
two coordinates are ever swapped, and a positional pair invites exactly that. -/
structure ContinuationProfile where
  /-- Does the Target discount the future political state, or ignore it? -/
  targetForward : Bool
  /-- Does the Sender discount the future political state, or ignore it? -/
  senderForward : Bool
  deriving DecidableEq, Repr

namespace ContinuationProfile

/-- Neither government looks ahead — the stage benchmark. -/
def p00 : ContinuationProfile := ⟨false, false⟩

/-- Only the Target looks ahead: the political-preservation channel alone. -/
def p10 : ContinuationProfile := ⟨true, false⟩

/-- Only the Sender looks ahead: the political-investment channel alone. -/
def p01 : ContinuationProfile := ⟨false, true⟩

/-- Both look ahead — the full model. -/
def p11 : ContinuationProfile := ⟨true, true⟩

@[simp] theorem p00_targetForward : p00.targetForward = false := rfl
@[simp] theorem p00_senderForward : p00.senderForward = false := rfl
@[simp] theorem p10_targetForward : p10.targetForward = true := rfl
@[simp] theorem p10_senderForward : p10.senderForward = false := rfl
@[simp] theorem p01_targetForward : p01.targetForward = false := rfl
@[simp] theorem p01_senderForward : p01.senderForward = true := rfl
@[simp] theorem p11_targetForward : p11.targetForward = true := rfl
@[simp] theorem p11_senderForward : p11.senderForward = true := rfl

/-- The four profiles are distinct, so the factorial has four cells and not
fewer. Trivial, and worth having as the sanity check that the indexing means
what the table above says. -/
theorem four_distinct :
    p00 ≠ p10 ∧ p00 ≠ p01 ∧ p00 ≠ p11 ∧
      p10 ≠ p01 ∧ p10 ≠ p11 ∧ p01 ≠ p11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end ContinuationProfile

end Mechanism

namespace AbstractGame
namespace Params

open Sanctions.Mechanism

variable (p : Params)

/-! ## The profile view of an economy -/

/-- The Target's discount factor under a profile: its own when the Target looks
ahead, zero when it does not. -/
def profileβ_T (c : ContinuationProfile) : ℝ :=
  if c.targetForward then p.β_T else 0

/-- The Sender's discount factor under a profile. -/
def profileβ_S (c : ContinuationProfile) : ℝ :=
  if c.senderForward then p.β_S else 0

theorem profileβ_T_mem (c : ContinuationProfile) :
    p.profileβ_T c ∈ Set.Ico (0 : ℝ) 1 := by
  unfold profileβ_T
  split
  · exact p.β_T_mem
  · exact ⟨le_refl 0, one_pos⟩

theorem profileβ_S_mem (c : ContinuationProfile) :
    p.profileβ_S c ∈ Set.Ico (0 : ℝ) 1 := by
  unfold profileβ_S
  split
  · exact p.β_S_mem
  · exact ⟨le_refl 0, one_pos⟩

/-- **The economy, read at a continuation profile.**

Only the two discount factors change. Payoffs, the static Sender response, the
transition, and every regularity field are the same objects, so this is one
economy viewed four ways rather than four economies. That is what makes the
factorial a *decomposition* of a single model instead of a comparison across
models. -/
def withProfile (c : ContinuationProfile) : Params :=
  { p with
    β_T := p.profileβ_T c
    β_T_mem := p.profileβ_T_mem c
    β_S := p.profileβ_S c
    β_S_mem := p.profileβ_S_mem c }

@[simp] theorem withProfile_β_T (c : ContinuationProfile) :
    (p.withProfile c).β_T = p.profileβ_T c := rfl

@[simp] theorem withProfile_β_S (c : ContinuationProfile) :
    (p.withProfile c).β_S = p.profileβ_S c := rfl

@[simp] theorem withProfile_U_T (c : ContinuationProfile) :
    (p.withProfile c).U_T = p.U_T := rfl

@[simp] theorem withProfile_U_S (c : ContinuationProfile) :
    (p.withProfile c).U_S = p.U_S := rfl

@[simp] theorem withProfile_σ (c : ContinuationProfile) :
    (p.withProfile c).σ = p.σ := rfl

/-- **Reading the economy at a profile keeps the static selector continuous.**
`withProfile` leaves `σ` unchanged, so if the static Sender response of `p` is
jointly continuous in the state and the compliance level, so is that of
`p.withProfile c`. General in `F`. Round BJ5.1 (2026-10-07): joint continuity
of `σ` was a `Params` field that `{ p with … }` copied; it is now the instance
the static-Sender results (the regime-`10` value, the canonical myopic
equilibrium) read, and this carries it to every profile. -/
instance withProfile_staticSelectorContinuous [p.StaticSelectorContinuous]
    (c : ContinuationProfile) : (p.withProfile c).StaticSelectorContinuous :=
  ⟨p.σ_continuous⟩

@[simp] theorem withProfile_F (c : ContinuationProfile) :
    (p.withProfile c).F = p.F := rfl

@[simp] theorem withProfile_δ (c : ContinuationProfile) :
    (p.withProfile c).δ = p.δ := rfl

/-- **The full profile is the economy itself.** `11` is not a new model; it is
`p`. This is what makes the factorial a decomposition of the existing theory
rather than a parallel one. -/
@[simp] theorem withProfile_p11 : p.withProfile ContinuationProfile.p11 = p := by
  cases p; rfl

/-- Under the myopic profile both discount factors vanish, so each government's
Bellman equation collapses to its stage problem. -/
@[simp] theorem withProfile_p00_β_T :
    (p.withProfile ContinuationProfile.p00).β_T = 0 := rfl

@[simp] theorem withProfile_p00_β_S :
    (p.withProfile ContinuationProfile.p00).β_S = 0 := rfl

/-- The Target-only profile keeps the Target's discount factor and zeroes the
Sender's: the political-preservation channel, alone. -/
@[simp] theorem withProfile_p10_β_T :
    (p.withProfile ContinuationProfile.p10).β_T = p.β_T := rfl

@[simp] theorem withProfile_p10_β_S :
    (p.withProfile ContinuationProfile.p10).β_S = 0 := rfl

/-- The Sender-only profile: the political-investment channel, alone. -/
@[simp] theorem withProfile_p01_β_T :
    (p.withProfile ContinuationProfile.p01).β_T = 0 := rfl

@[simp] theorem withProfile_p01_β_S :
    (p.withProfile ContinuationProfile.p01).β_S = p.β_S := rfl

end Params
end AbstractGame

namespace Mechanism

open ContinuationProfile

/-! ## Interaction

The four regimes give four numbers at each state. The **interaction** asks
whether the two motives merely add, or reinforce each other.

Concretely: if sanctions are `0.30` with neither motive, `0.40` with the
Target's alone and `0.45` with the Sender's alone, then the two motives
contribute `+0.10` and `+0.15`. Adding gives `0.55`. If the joint regime lands
*above* `0.55` the motives amplify one another; at `0.55` they simply add; below
it, they partly substitute. The interaction is that comparison.

**Vocabulary, which the paper must keep straight.** Two effects of the same
sign is *reinforcement*, and it is not this. Only a sign on the cross-difference
below licenses the words "complementarity" or "amplification".

**Read the scale warning before using this.** See `interaction_sign_not_scale_invariant`. -/

/-- **The interaction of the two continuation channels**, for any
profile-indexed quantity — a sanction rule, a defiance policy, a value.

Taking a *function of the profile* rather than four positional arguments is
deliberate: it is the one formulation in which the index convention cannot be
scrambled by an argument-order slip. -/
def interaction (f : ContinuationProfile → ℝ) : ℝ :=
  f p11 - f p10 - f p01 + f p00

/-- **The interaction is exactly supermodularity in the two switches.**

On the two-point lattice of profiles, `p10` and `p01` are the incomparable pair;
a nonnegative interaction says the joint regime plus the myopic one beat the two
unilateral ones together. This is the sense — the only sense — in which the two
continuation channels are "complements". -/
theorem interaction_nonneg_iff (f : ContinuationProfile → ℝ) :
    0 ≤ interaction f ↔ f p10 + f p01 ≤ f p11 + f p00 := by
  unfold interaction; constructor <;> intro h <;> linarith

/-- Zero interaction is exactly additivity: the joint effect is the sum of the
two unilateral effects. -/
theorem interaction_eq_zero_iff (f : ContinuationProfile → ℝ) :
    interaction f = 0 ↔ f p11 - f p00 = (f p10 - f p00) + (f p01 - f p00) := by
  unfold interaction; constructor <;> intro h <;> linarith

/-- Defiance is compliance reversed. Mechanism comparisons are stated in
defiance so that a more reluctant Target and a harsher Sender both point *up*;
in compliance they point in opposite directions and every table reads
backwards. -/
def defiance (a : ℝ) : ℝ := 1 - a

/-- The interaction in defiance is the negative of the interaction in
compliance — the reorientation flips the sign, and nothing else. -/
theorem interaction_defiance (a : ContinuationProfile → ℝ) :
    interaction (fun c => defiance (a c)) = -interaction a := by
  unfold interaction defiance; ring

/-! ## A warning that has to travel with the definition

The direction results — "the Target's motive raises defiance", "the Sender's
raises sanctions" — survive any relabelling of the action scale, because they
are order statements. The interaction does not: it is a comparison of
*distances*, and distances depend on the ruler.

The theorem below exhibits the failure. Four sanction levels whose interaction
is negative become, after squaring — a strictly increasing reparametrisation of
`[0,1]`, changing no economics whatever — four levels whose interaction is
positive. "Substitutes" becomes "complements" because the units changed.

This matters because the sanction here is a normalised index on `[0,1]` with no
intrinsic cardinal meaning, so a cross-difference claim inherits whatever the
normalisation happened to be. A referee is entitled to ask which ruler the
complementarity was measured in.

**What to do about it.** Prefer an interaction statement that is invariant:
strict *inclusion* of the self-sustaining state sets,
`H p10 ∪ H p01 ⊂ H p11`, says the joint regime sustains sanctions from strictly
more political states than either channel alone, and no relabelling of the
sanction axis can disturb it. A *difference of thresholds* is not invariant and
inherits the same defect as the cross-difference. -/

/-- **The sign of the interaction is not invariant under reparametrising the
action scale.**

`s ↦ s²` is strictly increasing on `[0,1]`, so it is a pure change of units. It
reverses the sign of the interaction on the exhibited data. Hence a
complementarity claim stated as a cross-difference is a claim about units, not
only about behaviour. -/
theorem interaction_sign_not_scale_invariant :
    ∃ f : ContinuationProfile → ℝ,
      (∀ c, f c ∈ Set.Icc (0 : ℝ) 1) ∧
        interaction f < 0 ∧ 0 < interaction (fun c => f c ^ 2) := by
  refine ⟨fun c => if c = p11 then 9/10 else if c = p00 then 0 else 1/2,
    ?_, ?_, ?_⟩
  · intro c
    by_cases h1 : c = p11
    · subst h1; constructor <;> norm_num
    · by_cases h0 : c = p00
      · subst h0
        simp only [if_neg (by decide : ¬ (p00 : ContinuationProfile) = p11)]
        constructor <;> norm_num
      · simp only [if_neg h1, if_neg h0]
        constructor <;> norm_num
  · unfold interaction
    norm_num [p11, p10, p01, p00]
  · unfold interaction
    norm_num [p11, p10, p01, p00]

end Mechanism
end Sanctions

/-! ### Rule 16(b) decision-procedure guards

`decide` is used above on `ContinuationProfile` equality. Rule 16(b) requires a
true-case and a false-case check in the same file, so a `Decidable` instance
that silently answered one way would be caught here rather than in audit. -/

#guard decide (Sanctions.Mechanism.ContinuationProfile.p00
                 = Sanctions.Mechanism.ContinuationProfile.p00)
#guard ! decide (Sanctions.Mechanism.ContinuationProfile.p00
                   = Sanctions.Mechanism.ContinuationProfile.p11)
