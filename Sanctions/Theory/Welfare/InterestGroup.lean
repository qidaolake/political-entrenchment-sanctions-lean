/-
Sanctions/Theory/Welfare/InterestGroup.lean

**Interest-group representations of the governments' payoffs** (round W, 2026-10-15;
the author: welfare "in general abstract form, and the parametric and numeric only stays in
the example as a witness").

An interest-group representation of a pair of government payoffs `US`, `UT` consists of
finitely many groups on each side, each with an arbitrary welfare function and a political
weight that is positive on the feasible cube, such that each government's payoff is the
weighted sum of its groups' welfare at every state and action. Aggregate welfare puts weight
one on every group. Nothing here reads the transition, a functional form, or a sign
condition: the Kaempfer--Lowenberg polity (`FourGroupCoeffs`) and the family's welfare
completions (`PlacableEconomyF.WelfareCompletion`) are instances.

* **W1** `payoffs_add_eq`: the two governments' payoffs sum to aggregate welfare plus, over
  the groups, each group's welfare times its political weight less one.
* **W2** `rescaleS`, `rescaleS_welfare`, `exists_rescaleS_ranks`: multiplying one Sender
  group's welfare by `φ > 0` and dividing its weight by `φ` leaves both payoffs (hence the
  game and its equilibria) unchanged and shifts aggregate welfare by `(φ - 1)` times that
  group's welfare; when that group does better on one path than on another by a uniform
  margin, some such rescaling makes the planner prefer the first path at every discount
  factor.
-/
import Sanctions.Domain.UnitInterval
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators

namespace Sanctions
namespace Welfare

/-- **An interest-group representation** of the government payoffs `US` (Sender) and `UT`
(Target): finite group sets, arbitrary group welfare, political weights positive on the
feasible cube, and the two representation identities at every state and action. -/
structure InterestGroupRep (US UT : ℝ → ℝ → ℝ → ℝ) where
  /-- The Sender's groups. -/
  GS : Type
  /-- The Target's groups. -/
  GT : Type
  [fintypeS : Fintype GS]
  [fintypeT : Fintype GT]
  [decS : DecidableEq GS]
  [decT : DecidableEq GT]
  /-- The welfare of each Sender group at `(x, a, s)`. -/
  wS : GS → ℝ → ℝ → ℝ → ℝ
  /-- The welfare of each Target group at `(x, a, s)`. -/
  wT : GT → ℝ → ℝ → ℝ → ℝ
  /-- The Sender government's political weight on each of its groups. -/
  θS : GS → ℝ → ℝ → ℝ → ℝ
  /-- The Target government's political weight on each of its groups. -/
  θT : GT → ℝ → ℝ → ℝ → ℝ
  θS_pos : ∀ g x a s, x ∈ Sanctions.I → a ∈ Sanctions.I → s ∈ Sanctions.I → 0 < θS g x a s
  θT_pos : ∀ g x a s, x ∈ Sanctions.I → a ∈ Sanctions.I → s ∈ Sanctions.I → 0 < θT g x a s
  repS : ∀ x a s, US x a s = ∑ g, θS g x a s * wS g x a s
  repT : ∀ x a s, UT x a s = ∑ g, θT g x a s * wT g x a s

attribute [instance] InterestGroupRep.fintypeS InterestGroupRep.fintypeT
  InterestGroupRep.decS InterestGroupRep.decT

namespace InterestGroupRep

variable {US UT : ℝ → ℝ → ℝ → ℝ} (R : InterestGroupRep US UT)

/-- **Aggregate welfare**: every group at weight one. -/
def welfare (x a s : ℝ) : ℝ := ∑ g, R.wS g x a s + ∑ g, R.wT g x a s

/-- **W1. The accounting identity.** At every state and action the two governments' payoffs
sum to aggregate welfare plus, over the groups, each group's welfare times its political
weight less one. No sign condition and no transition is read. -/
theorem payoffs_add_eq (x a s : ℝ) :
    US x a s + UT x a s = R.welfare x a s
      + ((∑ g, (R.θS g x a s - 1) * R.wS g x a s)
        + ∑ g, (R.θT g x a s - 1) * R.wT g x a s) := by
  rw [R.repS, R.repT, welfare]
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

/-- **W2. Rescaling one Sender group**: its welfare is multiplied by `φ > 0` and its
political weight divided by `φ`. -/
noncomputable def rescaleS (h : R.GS) (φ : ℝ) (hφ : 0 < φ) : InterestGroupRep US UT where
  GS := R.GS
  GT := R.GT
  wS g x a s := if g = h then φ * R.wS g x a s else R.wS g x a s
  wT := R.wT
  θS g x a s := if g = h then R.θS g x a s / φ else R.θS g x a s
  θT := R.θT
  θS_pos g x a s hx ha hs := by
    split_ifs
    · exact div_pos (R.θS_pos g x a s hx ha hs) hφ
    · exact R.θS_pos g x a s hx ha hs
  θT_pos := R.θT_pos
  repS x a s := by
    rw [R.repS]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hφ0 : φ ≠ 0 := hφ.ne'
    change R.θS g x a s * R.wS g x a s
      = (if g = h then R.θS g x a s / φ else R.θS g x a s)
        * (if g = h then φ * R.wS g x a s else R.wS g x a s)
    split_ifs
    · field_simp
    · rfl
  repT := R.repT

/-- **W2. Rescaling leaves both payoffs unchanged** (they are the same `US`, `UT` by
construction) **and shifts aggregate welfare by `(φ - 1)` times the group's welfare.** -/
theorem rescaleS_welfare (h : R.GS) (φ : ℝ) (hφ : 0 < φ) (x a s : ℝ) :
    (R.rescaleS h φ hφ).welfare x a s = R.welfare x a s + (φ - 1) * R.wS h x a s := by
  have hsplit : ∀ g : R.GS,
      (if g = h then φ * R.wS g x a s else R.wS g x a s)
        = R.wS g x a s + (if g = h then (φ - 1) * R.wS g x a s else 0) := by
    intro g
    split_ifs <;> ring
  have hsum : ∑ g : R.GS, (if g = h then φ * R.wS g x a s else R.wS g x a s)
      = ∑ g : R.GS, R.wS g x a s + (φ - 1) * R.wS h x a s := by
    rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
  change ∑ g : R.GS, (if g = h then φ * R.wS g x a s else R.wS g x a s)
      + ∑ g : R.GT, R.wT g x a s = R.welfare x a s + (φ - 1) * R.wS h x a s
  rw [hsum, welfare]
  ring

end InterestGroupRep

/-- A termwise strict inequality between bounded flows survives discounting, at every
discount factor in `[0, 1)`. -/
theorem tsum_pow_mul_lt_of_forall_lt {β M : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    {f g : ℕ → ℝ} (hf : ∀ t, |f t| ≤ M) (hg : ∀ t, |g t| ≤ M) (hlt : ∀ t, f t < g t) :
    ∑' t : ℕ, β ^ t * f t < ∑' t : ℕ, β ^ t * g t := by
  have hsum : ∀ h : ℕ → ℝ, (∀ t, |h t| ≤ M) → Summable (fun t : ℕ => β ^ t * h t) := by
    intro h hh
    refine Summable.of_norm_bounded (g := fun t : ℕ => M * β ^ t)
      ((summable_geometric_of_lt_one hβ.1 hβ.2).mul_left _) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.1, mul_comm]
    exact mul_le_mul_of_nonneg_right (hh t) (pow_nonneg hβ.1 t)
  refine Summable.tsum_lt_tsum (i := 0) (fun t => ?_) ?_ (hsum f hf) (hsum g hg)
  · exact mul_le_mul_of_nonneg_left (hlt t).le (pow_nonneg hβ.1 t)
  · simpa using hlt 0

/-- **W2, the ranking step on flows.** If one group's welfare is higher on a first path than
on a second by a uniform margin `ε > 0`, and all flows are bounded, then some `φ > 0`
weights that group enough that discounted aggregate welfare ranks the first path strictly
above the second at every discount factor in `[0, 1)`. -/
theorem exists_scale_ranks {A B a b : ℕ → ℝ} {M ε : ℝ} (hε : 0 < ε)
    (hA : ∀ t, |A t| ≤ M) (hB : ∀ t, |B t| ≤ M) (ha : ∀ t, |a t| ≤ M) (hb : ∀ t, |b t| ≤ M)
    (hsep : ∀ t, b t + ε ≤ a t) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ β ∈ Set.Ico (0 : ℝ) 1,
      ∑' t : ℕ, β ^ t * (B t + (φ - 1) * b t) < ∑' t : ℕ, β ^ t * (A t + (φ - 1) * a t) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hA 0)
  set c : ℝ := (2 * M + 1) / ε
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hε.le
  have hcε : c * ε = 2 * M + 1 := div_mul_cancel₀ _ hε.ne'
  refine ⟨1 + c, by linarith, fun β hβ => ?_⟩
  have e : (1 + c) - 1 = c := by ring
  rw [e]
  have hbd : ∀ (F f : ℕ → ℝ), (∀ t, |F t| ≤ M) → (∀ t, |f t| ≤ M) →
      ∀ t, |F t + c * f t| ≤ M + c * M := by
    intro F f hF hf t
    calc |F t + c * f t| ≤ |F t| + |c * f t| := abs_add_le _ _
      _ = |F t| + c * |f t| := by rw [abs_mul, abs_of_nonneg hc0]
      _ ≤ M + c * M := add_le_add (hF t) (mul_le_mul_of_nonneg_left (hf t) hc0)
  refine tsum_pow_mul_lt_of_forall_lt hβ (hbd B b hB hb) (hbd A a hA ha) (fun t => ?_)
  have h1 : c * (b t + ε) ≤ c * a t := mul_le_mul_of_nonneg_left (hsep t) hc0
  have hA' := (abs_le.mp (hA t)).1
  have hB' := (abs_le.mp (hB t)).2
  nlinarith [h1, hcε, hA', hB', mul_add c (b t) ε]

namespace InterestGroupRep

variable {US UT : ℝ → ℝ → ℝ → ℝ} (R : InterestGroupRep US UT)

/-- **W2. The game does not fix the planner's ranking of two paths.** Take two sequences of
states and actions `P`, `Q`. If Sender group `h` does better along `P` than along `Q` by a
uniform margin `ε > 0` at every date, and aggregate welfare and that group's welfare are
bounded along both, then some rescaling of `h` (which leaves both payoffs, and so the game
and its equilibria, unchanged) makes discounted aggregate welfare rank `P` strictly above
`Q` at every discount factor in `[0, 1)`. -/
theorem exists_rescaleS_ranks (h : R.GS) (P Q : ℕ → ℝ × ℝ × ℝ) {M ε : ℝ} (hε : 0 < ε)
    (hWP : ∀ t, |R.welfare (P t).1 (P t).2.1 (P t).2.2| ≤ M)
    (hWQ : ∀ t, |R.welfare (Q t).1 (Q t).2.1 (Q t).2.2| ≤ M)
    (hwP : ∀ t, |R.wS h (P t).1 (P t).2.1 (P t).2.2| ≤ M)
    (hwQ : ∀ t, |R.wS h (Q t).1 (Q t).2.1 (Q t).2.2| ≤ M)
    (hsep : ∀ t, R.wS h (Q t).1 (Q t).2.1 (Q t).2.2 + ε ≤ R.wS h (P t).1 (P t).2.1 (P t).2.2) :
    ∃ φ : ℝ, ∃ hφ : 0 < φ, ∀ β ∈ Set.Ico (0 : ℝ) 1,
      ∑' t : ℕ, β ^ t * (R.rescaleS h φ hφ).welfare (Q t).1 (Q t).2.1 (Q t).2.2
        < ∑' t : ℕ, β ^ t * (R.rescaleS h φ hφ).welfare (P t).1 (P t).2.1 (P t).2.2 := by
  obtain ⟨φ, hφ, hrank⟩ := exists_scale_ranks (A := fun t => R.welfare (P t).1 (P t).2.1 (P t).2.2)
    (B := fun t => R.welfare (Q t).1 (Q t).2.1 (Q t).2.2)
    (a := fun t => R.wS h (P t).1 (P t).2.1 (P t).2.2)
    (b := fun t => R.wS h (Q t).1 (Q t).2.1 (Q t).2.2) hε hWP hWQ hwP hwQ hsep
  refine ⟨φ, hφ, fun β hβ => ?_⟩
  simp only [R.rescaleS_welfare h φ hφ]
  exact hrank β hβ

end InterestGroupRep

end Welfare
end Sanctions

#print axioms Sanctions.Welfare.InterestGroupRep.payoffs_add_eq
#print axioms Sanctions.Welfare.InterestGroupRep.rescaleS_welfare
#print axioms Sanctions.Welfare.InterestGroupRep.exists_rescaleS_ranks
