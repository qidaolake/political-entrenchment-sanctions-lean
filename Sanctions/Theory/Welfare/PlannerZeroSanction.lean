/-
Sanctions/Theory/Welfare/PlannerZeroSanction.lean

**When zero sanctions are planner-optimal: a general sufficient condition** (round W,
2026-10-15; W3 of the welfare derivation plan).

A planner chooses compliance and the sanction at every date to maximise discounted
aggregate welfare `W`, under a state transition on the unit interval. Nothing here reads a
functional form for `W` or for the transition, or an interest-group polity: `W` is any
bounded welfare flow (for instance the aggregate welfare of an `InterestGroupRep`).

`zeroSanction_planner_optimal`: suppose that

* at zero sanction a compliance level `a*(x)` maximises welfare, and a sanction `s` adds at
  most `η·s` to welfare (`W x a s ≤ W x (a* x) 0 + η·s`): the social marginal return to a
  sanction is at most `η`;
* zero-sanction welfare rises with the state at a rate of at most `B` (upper chords);
* the transition is non-decreasing in the state at zero sanction and in the sanction, its
  zero-sanction section has upper chord `lam`, and a sanction raises the next state by at most
  `L` per unit;
* `η + β·(max B 0 / (1 - β·lam))·L ≤ 0`, with `β·lam < 1`.

Then the zero-sanction path with compliance `a*` attains the planner's optimum against every
time-dependent plan over both actions, from every feasible start. The proof: the
zero-sanction value rises with the state at a rate of at most `max B 0 / (1 - β·lam)`, so the
condition makes it a Bellman supersolution of the planner's problem, and the Foundations
verification theorem concludes. The Kaempfer--Lowenberg polity's two cases
(`FourGroup.plannerOptimalValue_eq_of_nonpos`, `..._of_upperChords`) are the instance with
welfare linear in the state.
-/
import Sanctions.Foundations.InfiniteHorizonVerification
import Sanctions.Domain.UnitInterval

namespace Sanctions
namespace Welfare

open InfiniteHorizonVerification

/-- The feasible zero sanction (or compliance). -/
def zeroI : ↥(Sanctions.I : Set ℝ) := ⟨0, le_rfl, zero_le_one⟩

/-- A stationary plan's path, shifted by one date, is the path from the next state. -/
theorem statePath_stationary_succ {X A : Type*} (F : X → A → X) (α : X → A) (x : X) :
    ∀ n : ℕ, statePath F (stationaryPlan α) x (n + 1)
      = statePath F (stationaryPlan α) (F x (α x)) n
  | 0 => rfl
  | n + 1 => by
      have ih := statePath_stationary_succ F α x n
      calc statePath F (stationaryPlan α) x (n + 1 + 1)
          = F (statePath F (stationaryPlan α) x (n + 1))
              (α (statePath F (stationaryPlan α) x (n + 1))) := rfl
        _ = F (statePath F (stationaryPlan α) (F x (α x)) n)
              (α (statePath F (stationaryPlan α) (F x (α x)) n)) := by rw [ih]
        _ = statePath F (stationaryPlan α) (F x (α x)) (n + 1) := rfl

/-- **The Bellman equation of a stationary plan's value**, for bounded flows. -/
theorem discountedPayoff_stationary_eq {X A : Type*} (u : X → A → ℝ) (F : X → A → X) (β : ℝ)
    (α : X → A) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (M : ℝ) (hu : ∀ x a, |u x a| ≤ M) (x : X) :
    discountedPayoff u F β (stationaryPlan α) x
      = u x (α x) + β * discountedPayoff u F β (stationaryPlan α) (F x (α x)) := by
  have hs : Summable (discountedStage u F β (stationaryPlan α) x) :=
    discountedStage_summable_of_uniform_bound u F β hβ0 hβ1 _ x M (fun n => hu _ _)
  have hterm : ∀ n : ℕ, discountedStage u F β (stationaryPlan α) x (n + 1)
      = β * discountedStage u F β (stationaryPlan α) (F x (α x)) n := by
    intro n
    unfold discountedStage
    rw [statePath_stationary_succ F α x n]
    simp only [stationaryPlan]
    ring
  unfold discountedPayoff
  rw [hs.tsum_eq_zero_add]
  congr 1
  · simp [discountedStage, stationaryPlan]
  · simp only [hterm]
    exact tsum_mul_left

/-- A stationary plan's value is bounded by `M / (1 - β)` when its flow is bounded by `M`. -/
theorem abs_discountedPayoff_stationary_le {X A : Type*} (u : X → A → ℝ) (F : X → A → X)
    (β : ℝ) (α : X → A) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (M : ℝ) (hu : ∀ x a, |u x a| ≤ M)
    (x : X) :
    |discountedPayoff u F β (stationaryPlan α) x| ≤ M / (1 - β) := by
  have hs : Summable (discountedStage u F β (stationaryPlan α) x) :=
    discountedStage_summable_of_uniform_bound u F β hβ0 hβ1 _ x M (fun n => hu _ _)
  have hg : Summable (fun n : ℕ => M * β ^ n) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left M
  have hgsum : ∑' n : ℕ, M * β ^ n = M / (1 - β) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
  have hterm : ∀ n, |discountedStage u F β (stationaryPlan α) x n| ≤ M * β ^ n := by
    intro n
    unfold discountedStage
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hu _ _) (pow_nonneg hβ0 n)
  rw [abs_le]
  constructor
  · have hneg : Summable (fun n : ℕ => -(M * β ^ n)) := hg.neg
    have h := hneg.tsum_le_tsum (fun n => neg_le_of_abs_le (hterm n)) hs
    rw [tsum_neg, hgsum] at h
    unfold discountedPayoff
    exact h
  · have h := hs.tsum_le_tsum (fun n => le_of_abs_le (hterm n)) hg
    rw [hgsum] at h
    unfold discountedPayoff
    exact h

section Planner

/-- The planner's flow over both actions (compliance, sanction). -/
def plannerFlow (W : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ℝ)
    (x : ↥(Sanctions.S : Set ℝ)) (p : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)) : ℝ :=
  W x p.1 p.2

/-- The planner's state step: only the sanction moves the state. -/
def plannerStep (Fc : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.S : Set ℝ))
    (x : ↥(Sanctions.S : Set ℝ)) (p : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)) :
    ↥(Sanctions.S : Set ℝ) :=
  Fc x p.2

/-- The zero-sanction plan with compliance `astar`. -/
def zeroSanctionPlan (astar : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ))
    (x : ↥(Sanctions.S : Set ℝ)) : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ) :=
  (astar x, zeroI)

variable (Fc : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.S : Set ℝ))
  (W : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ℝ)
  (astar : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ))

/-- The zero-sanction path from `x`. -/
def zeroPath (x : ↥(Sanctions.S : Set ℝ)) (n : ℕ) : ↥(Sanctions.S : Set ℝ) :=
  statePath (plannerStep Fc) (stationaryPlan (zeroSanctionPlan astar)) x n

/-- **Ordered zero-sanction paths with a contracting gap.** If the zero-sanction section is
non-decreasing with upper chord `lam ≥ 0`, two zero-sanction paths stay ordered and their gap
shrinks at least by `lam` per period. -/
theorem zeroPath_ordered (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hmono : ∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 → (Fc x zeroI).1 ≤ (Fc y zeroI).1)
    (hchord : ∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 →
      (Fc y zeroI).1 - (Fc x zeroI).1 ≤ lam * (y.1 - x.1))
    {x y : ↥(Sanctions.S : Set ℝ)} (hxy : x.1 ≤ y.1) :
    ∀ n : ℕ, (zeroPath Fc astar x n).1 ≤ (zeroPath Fc astar y n).1 ∧
      (zeroPath Fc astar y n).1 - (zeroPath Fc astar x n).1 ≤ lam ^ n * (y.1 - x.1)
  | 0 => ⟨hxy, by simp [zeroPath]⟩
  | n + 1 => by
      obtain ⟨hle, hgap⟩ := zeroPath_ordered lam hlam0 hmono hchord hxy n
      have hx : zeroPath Fc astar x (n + 1) = Fc (zeroPath Fc astar x n) zeroI := rfl
      have hy : zeroPath Fc astar y (n + 1) = Fc (zeroPath Fc astar y n) zeroI := rfl
      rw [hx, hy]
      refine ⟨hmono _ _ hle, ?_⟩
      calc (Fc (zeroPath Fc astar y n) zeroI).1 - (Fc (zeroPath Fc astar x n) zeroI).1
          ≤ lam * ((zeroPath Fc astar y n).1 - (zeroPath Fc astar x n).1) := hchord _ _ hle
        _ ≤ lam * (lam ^ n * (y.1 - x.1)) := mul_le_mul_of_nonneg_left hgap hlam0
        _ = lam ^ (n + 1) * (y.1 - x.1) := by ring

/-- **W3. Zero sanctions are planner-optimal when the first unit of sanction does not pay
socially.** See the module docstring for the hypotheses. The conclusion: the zero-sanction
plan with compliance `astar` attains the planner's optimum against every time-dependent plan
over both actions, from every feasible start. -/
theorem zeroSanction_planner_optimal (β lam L B η M : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam0 : 0 ≤ lam) (hβlam : β * lam < 1)
    (hbound : ∀ x a s, |W x a s| ≤ M)
    (hsoc : ∀ x a s, W x a s ≤ W x (astar x) zeroI + η * s.1)
    (hchordW : ∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 →
      W y (astar y) zeroI - W x (astar x) zeroI ≤ B * (y.1 - x.1))
    (hmono0 : ∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 → (Fc x zeroI).1 ≤ (Fc y zeroI).1)
    (hchord0 : ∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 →
      (Fc y zeroI).1 - (Fc x zeroI).1 ≤ lam * (y.1 - x.1))
    (hmonoS : ∀ (x : ↥(Sanctions.S : Set ℝ)) (s : ↥(Sanctions.I : Set ℝ)),
      (Fc x zeroI).1 ≤ (Fc x s).1)
    (hchordS : ∀ (x : ↥(Sanctions.S : Set ℝ)) (s : ↥(Sanctions.I : Set ℝ)),
      (Fc x s).1 - (Fc x zeroI).1 ≤ L * s.1)
    (hcond : η + β * (max B 0 / (1 - β * lam)) * L ≤ 0)
    (π : MarkovPlan ↥(Sanctions.S : Set ℝ) (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
    (x₀ : ↥(Sanctions.S : Set ℝ)) :
    discountedPayoff (plannerFlow W) (plannerStep Fc) β π x₀
      ≤ discountedPayoff (plannerFlow W) (plannerStep Fc) β
          (stationaryPlan (zeroSanctionPlan astar)) x₀ := by
  set u := plannerFlow W
  set step := plannerStep Fc
  set α := zeroSanctionPlan astar
  set V : ↥(Sanctions.S : Set ℝ) → ℝ := fun x => discountedPayoff u step β (stationaryPlan α) x
  have hu : ∀ x p, |u x p| ≤ M := fun x p => hbound x p.1 p.2
  set K : ℝ := max B 0 / (1 - β * lam) with hK
  have hden : 0 < 1 - β * lam := by linarith
  have hK0 : 0 ≤ K := div_nonneg (le_max_right _ _) hden.le
  -- the Bellman equation of the zero-sanction value
  have hVeq : ∀ x, V x = W x (astar x) zeroI + β * V (Fc x zeroI) := fun x =>
    discountedPayoff_stationary_eq u step β α hβ0 hβ1 M hu x
  -- the zero-sanction value rises with the state at a rate of at most `K`
  have hVchord : ∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 → V y - V x ≤ K * (y.1 - x.1) := by
    intro x y hxy
    have hsx : Summable (discountedStage u step β (stationaryPlan α) x) :=
      discountedStage_summable_of_uniform_bound u step β hβ0 hβ1 _ x M (fun n => hu _ _)
    have hsy : Summable (discountedStage u step β (stationaryPlan α) y) :=
      discountedStage_summable_of_uniform_bound u step β hβ0 hβ1 _ y M (fun n => hu _ _)
    have hβlam0 : 0 ≤ β * lam := mul_nonneg hβ0 hlam0
    have hg : Summable (fun n : ℕ => (max B 0 * (y.1 - x.1)) * (β * lam) ^ n) :=
      (summable_geometric_of_lt_one hβlam0 hβlam).mul_left _
    have hterm : ∀ n : ℕ, discountedStage u step β (stationaryPlan α) y n
        - discountedStage u step β (stationaryPlan α) x n
          ≤ (max B 0 * (y.1 - x.1)) * (β * lam) ^ n := by
      intro n
      obtain ⟨hle, hgap⟩ := zeroPath_ordered Fc astar lam hlam0 hmono0 hchord0 hxy n
      have hdiff : W (zeroPath Fc astar y n) (astar (zeroPath Fc astar y n)) zeroI
          - W (zeroPath Fc astar x n) (astar (zeroPath Fc astar x n)) zeroI
            ≤ max B 0 * (lam ^ n * (y.1 - x.1)) := by
        have h1 := hchordW _ _ hle
        have hd : 0 ≤ (zeroPath Fc astar y n).1 - (zeroPath Fc astar x n).1 := by linarith
        calc W (zeroPath Fc astar y n) (astar (zeroPath Fc astar y n)) zeroI
              - W (zeroPath Fc astar x n) (astar (zeroPath Fc astar x n)) zeroI
            ≤ B * ((zeroPath Fc astar y n).1 - (zeroPath Fc astar x n).1) := h1
          _ ≤ max B 0 * ((zeroPath Fc astar y n).1 - (zeroPath Fc astar x n).1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hd
          _ ≤ max B 0 * (lam ^ n * (y.1 - x.1)) :=
              mul_le_mul_of_nonneg_left hgap (le_max_right _ _)
      have hstage : ∀ z, discountedStage u step β (stationaryPlan α) z n
          = β ^ n * W (zeroPath Fc astar z n) (astar (zeroPath Fc astar z n)) zeroI := by
        intro z; rfl
      rw [hstage y, hstage x]
      have hβn : 0 ≤ β ^ n := pow_nonneg hβ0 n
      calc β ^ n * W (zeroPath Fc astar y n) (astar (zeroPath Fc astar y n)) zeroI
            - β ^ n * W (zeroPath Fc astar x n) (astar (zeroPath Fc astar x n)) zeroI
          = β ^ n * (W (zeroPath Fc astar y n) (astar (zeroPath Fc astar y n)) zeroI
            - W (zeroPath Fc astar x n) (astar (zeroPath Fc astar x n)) zeroI) := by ring
        _ ≤ β ^ n * (max B 0 * (lam ^ n * (y.1 - x.1))) := mul_le_mul_of_nonneg_left hdiff hβn
        _ = (max B 0 * (y.1 - x.1)) * (β * lam) ^ n := by rw [mul_pow]; ring
    have hle := (hsy.sub hsx).tsum_le_tsum hterm hg
    rw [hsy.tsum_sub hsx, tsum_mul_left, tsum_geometric_of_lt_one hβlam0 hβlam] at hle
    have hV : V y - V x = ∑' n, discountedStage u step β (stationaryPlan α) y n
        - ∑' n, discountedStage u step β (stationaryPlan α) x n := rfl
    rw [hV]
    calc ∑' n, discountedStage u step β (stationaryPlan α) y n
          - ∑' n, discountedStage u step β (stationaryPlan α) x n
        ≤ max B 0 * (y.1 - x.1) * (1 - β * lam)⁻¹ := hle
      _ = K * (y.1 - x.1) := by rw [hK]; ring
  -- the Bellman inequality over both actions
  have hbell : ∀ x p, u x p + β * V (step x p) ≤ V x := by
    intro x p
    have hs0 : 0 ≤ p.2.1 := p.2.2.1
    have h1 : u x p ≤ W x (astar x) zeroI + η * p.2.1 := hsoc x p.1 p.2
    have h2 : V (Fc x p.2) ≤ V (Fc x zeroI) + K * (L * p.2.1) := by
      have hc := hVchord (Fc x zeroI) (Fc x p.2) (hmonoS x p.2)
      have hcs : K * ((Fc x p.2).1 - (Fc x zeroI).1) ≤ K * (L * p.2.1) :=
        mul_le_mul_of_nonneg_left (hchordS x p.2) hK0
      linarith
    have h3 : β * V (Fc x p.2) ≤ β * V (Fc x zeroI) + β * (K * (L * p.2.1)) := by
      have := mul_le_mul_of_nonneg_left h2 hβ0
      linarith [mul_add β (V (Fc x zeroI)) (K * (L * p.2.1))]
    have h4 : p.2.1 * (η + β * K * L) ≤ 0 := by nlinarith [hs0, hcond]
    have hstepx : step x p = Fc x p.2 := rfl
    rw [hstepx, hVeq x]
    nlinarith [h1, h3, h4, mul_comm p.2.1 (η + β * K * L)]
  -- equality along the zero-sanction plan
  have hatt : ∀ x, u x (α x) + β * V (step x (α x)) = V x := fun x => (hVeq x).symm
  -- the value bound
  have hVb : ∀ x, |V x| ≤ M / (1 - β) := fun x =>
    abs_discountedPayoff_stationary_le u step β α hβ0 hβ1 M hu x
  exact stationary_optimal_against_markov_deviation_of_global_bounds u step β V α hβ0 hβ1
    hbell hatt M (M / (1 - β)) hu hVb π x₀

end Planner

end Welfare
end Sanctions

#print axioms Sanctions.Welfare.zeroSanction_planner_optimal
