/-
Sanctions/Examples/ChordEconomyWelfareGeneral.lean

**Welfare on the general class** (round W, 2026-10-15; W4 and W5 of the welfare derivation
plan). The author: welfare "in general abstract form, and the parametric and numeric only
stays in the example as a witness".

Both results are stated on the abstract class (`ChordEconomy`, `ChordEconomyCs`), with
interest-group representations in the general sense of `Welfare.InterestGroupRep`: arbitrary
group welfare and positive political weights. The family's statements
(`PlacableEconomyFcs.exists_completions_reversing_regime_ranking_of_response_monotone`,
`PlacableEconomyF.exists_planner_efficient_completion`) are their witnesses with linear
group payoffs.

* **W4** `ChordEconomyCs.exists_reps_reversing_regime_ranking`: on an economy of the class
  satisfying the four-case conditions, two representations (two groups per country,
  positive constant weights) reproduce the governments' payoffs, hence the same four
  constructed equilibria, yet rank them `11 > 10 > 00 = 01` and `00 = 01 > 10 > 11` at every
  start and every common planner discount factor. The Sender side carries a free net sanction
  coefficient `η`; on the Target side compliance is a transfer between the two groups, so the
  two zero-sanction cases tie under zero-sanction neutrality.
* **W4 for the main comparison** `ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking`
  (round W2, 2026-10-16): the same reversal for the myopic case `00` against the
  forward-looking case `11` alone, under the conditions of the stage-form regime separation
  (no zero-sanction neutrality, semiconvex sanction sections or dynamic relief condition).
  The representation `etaRep` is stated on `ChordEconomy`, so both forms use it.
* **W5** `ChordEconomy.exists_planner_efficient_rep`,
  `ChordEconomy.planner_efficient_rep_at_policy_zero`: on an economy of the class under
  zero-sanction neutrality there is a representation whose aggregate welfare is the Sender's
  payoff; at the planner discount `β_S` the play of every equilibrium at which the Target
  fully defies attains the planner's optimum against every time-dependent plan over both
  actions. No restriction `r = n = 0` (the family's boundary) is needed.
-/
import Sanctions.Examples.PlacableSenderWelfareCompletion
import Sanctions.Examples.PlacableSenderDefianceValues
import Sanctions.Theory.Welfare.InterestGroup

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-- Discounted welfare of a flow at discount factor `β`. -/
def discountedWelfare (β : ℝ) (f : ℕ → ℝ) : ℝ := ∑' t : ℕ, β ^ t * f t

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Under zero-sanction neutrality, compliance never raises the Sender's payoff** (S10 with
`k_lo > 0`). -/
theorem U_S_le_defiance (hZ : E.ZeroSanctionNeutral) {x a s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : E.U_S x a s ≤ E.U_S x 0 s := by
  have h := E.hUS_placLo x hx 0 zero_mem_I a ha 0 zero_mem_I s hs ha.1 hs.1
  have hz := hZ x hx a ha
  have hk : 0 ≤ E.klo * ((a - 0) * (s - 0)) :=
    mul_nonneg E.hklo.le (mul_nonneg (by linarith [ha.1]) (by linarith [hs.1]))
  linarith

/-- **A representation whose aggregate welfare is the Sender's payoff**: Sender groups with
welfare `s` and `U_S - s`, both at weight one; Target groups with welfare `U_T` and `-U_T`, at
weights two and one. -/
def senderWelfareRep : Welfare.InterestGroupRep E.U_S E.U_T where
  GS := Bool
  GT := Bool
  wS g x a s := cond g s (E.U_S x a s - s)
  wT g x a s := cond g (E.U_T x a s) (-E.U_T x a s)
  θS _ _ _ _ := 1
  θT g _ _ _ := cond g 2 1
  θS_pos _ _ _ _ _ _ _ := one_pos
  θT_pos g _ _ _ _ _ _ := by cases g <;> norm_num
  repS x a s := by rw [Fintype.sum_bool]; simp only [cond_true, cond_false]; ring
  repT x a s := by rw [Fintype.sum_bool]; simp only [cond_true, cond_false]; ring

theorem senderWelfareRep_welfare (x a s : ℝ) :
    E.senderWelfareRep.welfare x a s = E.U_S x a s := by
  change (∑ g : Bool, cond g s (E.U_S x a s - s))
      + ∑ g : Bool, cond g (E.U_T x a s) (-E.U_T x a s) = E.U_S x a s
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [cond_true, cond_false]
  ring

/-- The planner's flow on the cube for a representation. -/
def repFlow (R : Welfare.InterestGroupRep E.U_S E.U_T) (x : ↥(Sanctions.S : Set ℝ))
    (p : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)) : ℝ :=
  R.welfare x.1 p.1.1 p.2.1

/-- The planner's state step on the cube. -/
def cubeStep (x : ↥(Sanctions.S : Set ℝ)) (p : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)) :
    ↥(Sanctions.S : Set ℝ) :=
  Sanctions.clipS' (E.F x.1 p.2.1)

/-- Full defiance and the Sender's constructed response, as a stationary plan. -/
def defiancePlan (x : ↥(Sanctions.S : Set ℝ)) : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ) :=
  (⟨0, le_rfl, zero_le_one⟩, ⟨E.responsePath E.VSstar x.1, E.responsePath_mem _ _⟩)

/-- **W5. Persistent play can be planner-optimal, on the whole class.** Under zero-sanction
neutrality there is an interest-group representation (two groups per country, positive
weights) whose aggregate welfare is the Sender's payoff, and at the planner discount `β_S`
the plan of full defiance with the Sender's constructed response is optimal against every
time-dependent plan over both actions, from every feasible start. -/
theorem exists_planner_efficient_rep (hZ : E.ZeroSanctionNeutral) :
    ∃ R : Welfare.InterestGroupRep E.U_S E.U_T,
      (∀ x a s, R.welfare x a s = E.U_S x a s) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff (E.repFlow R) E.cubeStep E.β_S π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff (E.repFlow R) E.cubeStep E.β_S
              (InfiniteHorizonVerification.stationaryPlan E.defiancePlan) x₀ := by
  refine ⟨E.senderWelfareRep, E.senderWelfareRep_welfare, fun π x₀ => ?_⟩
  refine InfiniteHorizonVerification.stationary_optimal_against_markov_deviation_of_global_bounds
    (E.repFlow E.senderWelfareRep) E.cubeStep E.β_S (fun x => E.VSstar x) E.defiancePlan
    E.hβS0.le E.hβS1 ?_ ?_ E.MU E.MS ?_ ?_ π x₀
  · -- Bellman inequality over both actions: compliance only lowers the Sender's payoff
    intro x p
    have hle : E.U_S x.1 p.1.1 p.2.1 ≤ E.U_S x.1 0 p.2.1 :=
      E.U_S_le_defiance hZ x.2 p.1.2 p.2.2
    have h : E.U_S x.1 0 p.2.1 + E.β_S * E.VSstar (Sanctions.clipS' (E.F x.1 p.2.1))
        ≤ E.VSstar x := E.senderObj_le_VSstar x p.2.2
    change E.senderWelfareRep.welfare x.1 p.1.1 p.2.1
        + E.β_S * E.VSstar (Sanctions.clipS' (E.F x.1 p.2.1)) ≤ E.VSstar x
    rw [E.senderWelfareRep_welfare]
    linarith
  · -- equality at full defiance and the constructed response
    intro x
    have h : E.U_S x.1 0 (E.responsePath E.VSstar x.1)
        + E.β_S * E.VSstar (Sanctions.clipS' (E.F x.1 (E.responsePath E.VSstar x.1)))
        = E.VSstar x := E.senderObj_responsePath_eq_VSstar x
    change E.senderWelfareRep.welfare x.1 0 (E.responsePath E.VSstar x.1)
        + E.β_S * E.VSstar (Sanctions.clipS' (E.F x.1 (E.responsePath E.VSstar x.1)))
        = E.VSstar x
    rw [E.senderWelfareRep_welfare]
    exact h
  · -- flow bound
    intro x p
    change |E.senderWelfareRep.welfare x.1 p.1.1 p.2.1| ≤ E.MU
    rw [E.senderWelfareRep_welfare]
    exact E.abs_U_S_le_MU x.2 p.1.2 p.2.2
  · -- value bound, from carrier membership
    intro x
    exact (E.VSstar.norm_coe_le_norm x).trans E.VSstar_mem.1.1

/-- **W5 at every full-defiance equilibrium.** Under zero-sanction neutrality there is an
interest-group representation whose aggregate welfare is the Sender's payoff such that, for
every equilibrium at which the Target fully defies, the plan `defiancePlan` is that
equilibrium's play (its Target policy and its realised sanction rule, at every feasible state),
and at the planner discount `β_S` this play attains the planner's optimum against every
time-dependent plan over both actions, from every feasible start. -/
theorem planner_efficient_rep_at_policy_zero (hZ : E.ZeroSanctionNeutral) :
    ∃ R : Welfare.InterestGroupRep E.U_S E.U_T,
      (∀ x a s, R.welfare x a s = E.U_S x a s) ∧
      ∀ (Eq : E.toParams.FeedbackStackelbergEquilibriumTop),
        (∀ x ∈ Sanctions.I, Eq.α x = 0) →
        (∀ x : ↥(Sanctions.S : Set ℝ),
          (E.defiancePlan x).1.1 = Eq.α x.1 ∧
          (E.defiancePlan x).2.1 = E.toParams.dynamicEquilibriumRule Eq x.1) ∧
        ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
              (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
          (x₀ : ↥(Sanctions.S : Set ℝ)),
          InfiniteHorizonVerification.discountedPayoff (E.repFlow R) E.cubeStep E.β_S π x₀
            ≤ InfiniteHorizonVerification.discountedPayoff (E.repFlow R) E.cubeStep E.β_S
                (InfiniteHorizonVerification.stationaryPlan E.defiancePlan) x₀ := by
  obtain ⟨R, hW, hopt⟩ := E.exists_planner_efficient_rep hZ
  refine ⟨R, hW, fun Eq hα => ⟨fun x => ⟨(hα x.1 x.2).symm, ?_⟩, hopt⟩⟩
  exact ((E.values_eq_of_policy_zero Eq hα).2.2 x.1 x.2).symm

/-- **A representation with a free net sanction coefficient `η`.** Sender groups with welfare
`2·η·s` at weight one half and `U_S - η·s` at weight one; Target groups with welfare
`-(U_T(x,0,s) - U_T(x,a,s))` at weight two and `U_T(x,0,s) + (U_T(x,0,s) - U_T(x,a,s))` at
weight one, so that compliance is a transfer between them. Aggregate welfare is
`U_S + U_T(·,0,·) + η·s` (`etaRep_welfare`). -/
def etaRep (η : ℝ) : Welfare.InterestGroupRep E.U_S E.U_T where
  GS := Bool
  GT := Bool
  wS g x a s := cond g (2 * η * s) (E.U_S x a s - η * s)
  wT g x a s := cond g (-(E.U_T x 0 s - E.U_T x a s))
    (E.U_T x 0 s + (E.U_T x 0 s - E.U_T x a s))
  θS g _ _ _ := cond g (1 / 2) 1
  θT g _ _ _ := cond g 2 1
  θS_pos g _ _ _ _ _ _ := by cases g <;> norm_num
  θT_pos g _ _ _ _ _ _ := by cases g <;> norm_num
  repS x a s := by rw [Fintype.sum_bool]; simp only [cond_true, cond_false]; ring
  repT x a s := by rw [Fintype.sum_bool]; simp only [cond_true, cond_false]; ring

theorem etaRep_welfare (η x a s : ℝ) :
    (E.etaRep η).welfare x a s = E.U_S x a s + E.U_T x 0 s + η * s := by
  change (∑ g : Bool, cond g (2 * η * s) (E.U_S x a s - η * s))
      + ∑ g : Bool, cond g (-(E.U_T x 0 s - E.U_T x a s))
          (E.U_T x 0 s + (E.U_T x 0 s - E.U_T x a s)) = E.U_S x a s + E.U_T x 0 s + η * s
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [cond_true, cond_false]
  ring

end ChordEconomy

namespace ChordEconomyCs

variable (E : ChordEconomyCs)

/-- Welfare flow of a representation along the fully myopic regime. -/
def repFlow00 (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (R : Welfare.InterestGroupRep E.U_S E.U_T) (x₀ : ℝ) (t : ℕ) : ℝ :=
  R.welfare ((E.myopicPath hInt hSR hP) x₀ t)
    ((E.myopicEquilibriumTop hInt hSR hP).α ((E.myopicPath hInt hSR hP) x₀ t))
    (E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP)
      ((E.myopicPath hInt hSR hP) x₀ t))

/-- Welfare flow of a representation along the Sender-only regime. -/
def repFlow01 (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hZ : E.ZeroSanctionNeutral)
    (R : Welfare.InterestGroupRep E.U_S E.U_T) (x₀ : ℝ) (t : ℕ) : ℝ :=
  R.welfare ((E.senderOnlyPath' hInt hP) hrelief hZ x₀ t)
    (((E.senderOnlyEquilibriumTop' hInt hP) hrelief hZ).α
      ((E.senderOnlyPath' hInt hP) hrelief hZ x₀ t))
    (E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hZ)
      ((E.senderOnlyPath' hInt hP) hrelief hZ x₀ t))

/-- Welfare flow of a representation along the Target-only regime. -/
def repFlow10 (hTM : E.LossOffset) (R : Welfare.InterestGroupRep E.U_S E.U_T) (x₀ : ℝ)
    (t : ℕ) : ℝ :=
  R.welfare ((E.targetOnlyPath hTM) x₀ t)
    ((E.targetOnlyEquilibriumTop hTM).α ((E.targetOnlyPath hTM) x₀ t))
    (E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) ((E.targetOnlyPath hTM) x₀ t))

/-- Welfare flow of a representation along the forward-looking regime, given a
nondecreasing response. -/
def repFlow11 (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (R : Welfare.InterestGroupRep E.U_S E.U_T) (x₀ : ℝ) (t : ℕ) : ℝ :=
  R.welfare ((E.dynamicPathOf hTM hmono) x₀ t)
    ((E.equilibriumTop hTM hmono).α ((E.dynamicPathOf hTM hmono) x₀ t))
    (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono)
      ((E.dynamicPathOf hTM hmono) x₀ t))

/-- **W4. The governments' game does not determine the welfare ranking of the four
constructed equilibria, on the whole class.** On an economy of the class satisfying the
four-case conditions (interiority, the loss-offset condition, placability, a nondecreasing
response at defiance as under the dynamic complementarity condition, the sharp relief margin,
which gives the dynamic relief condition and semiconvex sanction sections, and zero-sanction
neutrality), there are two interest-group representations (two groups per country, positive
constant weights) of the same government payoffs, hence the same four constructed
equilibria, such that at every feasible start and every common planner discount factor in
`[0, 1)` one ranks the regimes `11 > 10 > 00 = 01` and the other `00 = 01 > 10 > 11`. -/
theorem exists_reps_reversing_regime_ranking (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hZ : E.ZeroSanctionNeutral) :
    ∃ Rp Rm : Welfare.InterestGroupRep E.U_S E.U_T,
      ∀ x₀ ∈ Sanctions.I, ∀ β ∈ Set.Ico (0 : ℝ) 1,
        (discountedWelfare β (E.repFlow10 hTM Rp x₀)
            < discountedWelfare β (E.repFlow11 hTM hmono Rp x₀)
          ∧ discountedWelfare β
              (E.repFlow00 hInt (E.stageRelief_of_reliefSharp hrelief) hP Rp x₀)
            < discountedWelfare β (E.repFlow10 hTM Rp x₀)
          ∧ discountedWelfare β
              (E.repFlow00 hInt (E.stageRelief_of_reliefSharp hrelief) hP Rp x₀)
            = discountedWelfare β (E.repFlow01 hInt hP hrelief hZ Rp x₀))
        ∧ (discountedWelfare β (E.repFlow11 hTM hmono Rm x₀)
            < discountedWelfare β (E.repFlow10 hTM Rm x₀)
          ∧ discountedWelfare β (E.repFlow10 hTM Rm x₀)
            < discountedWelfare β
              (E.repFlow00 hInt (E.stageRelief_of_reliefSharp hrelief) hP Rm x₀)
          ∧ discountedWelfare β
              (E.repFlow00 hInt (E.stageRelief_of_reliefSharp hrelief) hP Rm x₀)
            = discountedWelfare β (E.repFlow01 hInt hP hrelief hZ Rm x₀)) := by
  have hSR : E.StageRelief := E.stageRelief_of_reliefSharp hrelief
  set Mb : ℝ := E.MU + E.MT₀
  have hMb0 : 0 ≤ Mb := add_nonneg E.MU_nonneg E.MT₀_nonneg
  set μ : ℝ := min E.sfloor E.wedge
  have hμ0 : 0 < μ := lt_min E.sfloor_pos E.wedge_pos
  set ηp : ℝ := (2 * Mb + 1) / μ
  have hηp0 : 0 ≤ ηp := div_nonneg (by linarith) hμ0.le
  have hηpμ : ηp * μ = 2 * Mb + 1 := div_mul_cancel₀ _ hμ0.ne'
  refine ⟨E.etaRep ηp, E.etaRep (-ηp), fun x₀ hx₀ β hβ => ?_⟩
  -- feasibility along the four paths
  have hy : ∀ t, (E.myopicPath hInt hSR hP) x₀ t ∈ Sanctions.I := fun t =>
    E.toParams.rulePathF_mem_I (fun x hx => by
      rw [(E.myopicRule_eq_zero hInt hSR hP) hx]; exact ⟨le_rfl, zero_le_one⟩) hx₀ t
  have h10 : ∀ t, (E.targetOnlyPath hTM) x₀ t ∈ Sanctions.I := fun t =>
    E.toParams.rulePathF_mem_I (fun _ hx => (E.targetOnlyRule_mem hTM) hx) hx₀ t
  have h11 : ∀ t, (E.dynamicPathOf hTM hmono) x₀ t ∈ Sanctions.I := fun t =>
    E.toParams.rulePathF_mem_I (E.dynamicRule_mem_of_response_monotone hTM hmono) hx₀ t
  have heq : ∀ t, (E.myopicPath hInt hSR hP) x₀ t
      = (E.senderOnlyPath' hInt hP) hrelief hZ x₀ t := fun t =>
    E.myopicPath_eq_senderOnlyPath_of_reliefSharp hInt hP hrelief hZ hx₀ t
  have h01 : ∀ t, (E.senderOnlyPath' hInt hP) hrelief hZ x₀ t ∈ Sanctions.I := fun t => by
    rw [← heq t]; exact hy t
  -- the realised sanctions
  have hs10 : ∀ t, E.σ ((E.targetOnlyPath hTM) x₀ t) 0 ∈ Sanctions.I := fun t => E.σ_mem _ 0
  have hs11 : ∀ t, E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t) ∈ Sanctions.I :=
    fun t => E.responsePath_mem _ _
  have hs10μ : ∀ t, μ ≤ E.σ ((E.targetOnlyPath hTM) x₀ t) 0 := fun t =>
    (min_le_left _ _).trans (E.sfloor_le (h10 t))
  have hgap : ∀ t, E.σ ((E.targetOnlyPath hTM) x₀ t) 0 + μ
      ≤ E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t) := by
    intro t
    have h := E.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone
      hInt hTM hmono hx₀ t
    rw [(E.targetOnlyRule_eq_stage hTM) (h10 t),
      (E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono) (h11 t)] at h
    linarith [min_le_right E.sfloor E.wedge]
  -- the base flow and its bound
  have hbase : ∀ x s, x ∈ Sanctions.I → s ∈ Sanctions.I →
      |E.U_S x 0 s + E.U_T x 0 s| ≤ Mb := by
    intro x s hx hs
    calc |E.U_S x 0 s + E.U_T x 0 s| ≤ |E.U_S x 0 s| + |E.U_T x 0 s| := abs_add_le _ _
      _ ≤ E.MU + E.MT₀ := add_le_add (E.abs_U_S_le_MU hx ChordEconomy.zero_mem_I hs)
          (E.abs_U_T_le_MT₀ hx ChordEconomy.zero_mem_I hs)
  have hflowb : ∀ η x s, |η| ≤ ηp → x ∈ Sanctions.I → s ∈ Sanctions.I →
      |E.U_S x 0 s + E.U_T x 0 s + η * s| ≤ Mb + ηp := by
    intro η x s hη hx hs
    have hηs : |η * s| ≤ ηp := by
      rw [abs_mul, abs_of_nonneg hs.1]
      calc |η| * s ≤ ηp * 1 := mul_le_mul hη hs.2 hs.1 hηp0
        _ = ηp := mul_one _
    calc |E.U_S x 0 s + E.U_T x 0 s + η * s|
        ≤ |E.U_S x 0 s + E.U_T x 0 s| + |η * s| := abs_add_le _ _
      _ ≤ Mb + ηp := add_le_add (hbase x s hx hs) hηs
  have hηabs : |ηp| ≤ ηp := (abs_of_nonneg hηp0).le
  have hηabs' : |-ηp| ≤ ηp := by rw [abs_neg]; exact hηabs
  -- the four flows in closed form
  have f00 : ∀ η t, E.repFlow00 hInt hSR hP (E.etaRep η) x₀ t
      = E.U_S ((E.myopicPath hInt hSR hP) x₀ t) 0 0
        + E.U_T ((E.myopicPath hInt hSR hP) x₀ t) 0 0 := by
    intro η t
    unfold repFlow00
    rw [E.etaRep_welfare, (E.myopicRule_eq_zero hInt hSR hP) (hy t),
      hZ _ (hy t) _ ((E.myopicEquilibriumTop hInt hSR hP).α_mem _ (hy t))]
    ring
  have f01 : ∀ η t, E.repFlow01 hInt hP hrelief hZ (E.etaRep η) x₀ t
      = E.U_S ((E.myopicPath hInt hSR hP) x₀ t) 0 0
        + E.U_T ((E.myopicPath hInt hSR hP) x₀ t) 0 0 := by
    intro η t
    unfold repFlow01
    rw [E.etaRep_welfare, (E.senderOnlyRule_eq_zero' hInt hP) hrelief hZ (h01 t),
      hZ _ (h01 t) _ (((E.senderOnlyEquilibriumTop' hInt hP) hrelief hZ).α_mem _ (h01 t)),
      ← heq t]
    ring
  have f10 : ∀ η t, E.repFlow10 hTM (E.etaRep η) x₀ t
      = E.U_S ((E.targetOnlyPath hTM) x₀ t) 0 (E.σ ((E.targetOnlyPath hTM) x₀ t) 0)
        + E.U_T ((E.targetOnlyPath hTM) x₀ t) 0 (E.σ ((E.targetOnlyPath hTM) x₀ t) 0)
        + η * E.σ ((E.targetOnlyPath hTM) x₀ t) 0 := by
    intro η t
    unfold repFlow10
    have hα : (E.targetOnlyEquilibriumTop hTM).α ((E.targetOnlyPath hTM) x₀ t) = 0 := rfl
    rw [hα, E.etaRep_welfare, (E.targetOnlyRule_eq_stage hTM) (h10 t)]
  have f11 : ∀ η t, E.repFlow11 hTM hmono (E.etaRep η) x₀ t
      = E.U_S ((E.dynamicPathOf hTM hmono) x₀ t) 0
          (E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t))
        + E.U_T ((E.dynamicPathOf hTM hmono) x₀ t) 0
          (E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t))
        + η * E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t) := by
    intro η t
    unfold repFlow11
    have hα : (E.equilibriumTop hTM hmono).α ((E.dynamicPathOf hTM hmono) x₀ t) = 0 := rfl
    rw [hα, E.etaRep_welfare,
      (E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono) (h11 t)]
  -- bounds on every flow
  have hB00 : ∀ η, |η| ≤ ηp → ∀ t, |E.repFlow00 hInt hSR hP (E.etaRep η) x₀ t| ≤ Mb + ηp := by
    intro η _ t
    rw [f00 η t]
    linarith [hbase _ 0 (hy t) ChordEconomy.zero_mem_I]
  have hB01 : ∀ η, |η| ≤ ηp → ∀ t,
      |E.repFlow01 hInt hP hrelief hZ (E.etaRep η) x₀ t| ≤ Mb + ηp := by
    intro η _ t
    rw [f01 η t]
    linarith [hbase _ 0 (hy t) ChordEconomy.zero_mem_I]
  have hB10 : ∀ η, |η| ≤ ηp → ∀ t, |E.repFlow10 hTM (E.etaRep η) x₀ t| ≤ Mb + ηp := by
    intro η hη t
    rw [f10 η t]
    exact hflowb η _ _ hη (h10 t) (hs10 t)
  have hB11 : ∀ η, |η| ≤ ηp → ∀ t, |E.repFlow11 hTM hmono (E.etaRep η) x₀ t| ≤ Mb + ηp := by
    intro η hη t
    rw [f11 η t]
    exact hflowb η _ _ hη (h11 t) (hs11 t)
  -- the tie between the two zero-sanction regimes
  have htie : ∀ η, discountedWelfare β (E.repFlow00 hInt hSR hP (E.etaRep η) x₀)
      = discountedWelfare β (E.repFlow01 hInt hP hrelief hZ (E.etaRep η) x₀) := by
    intro η
    unfold discountedWelfare
    congr 1
    funext t
    rw [f00 η t, f01 η t]
  -- one-sided bounds on the base flow
  have hlo : ∀ x s, x ∈ Sanctions.I → s ∈ Sanctions.I → -Mb ≤ E.U_S x 0 s + E.U_T x 0 s :=
    fun x s hx hs => (abs_le.mp (hbase x s hx hs)).1
  have hhi : ∀ x s, x ∈ Sanctions.I → s ∈ Sanctions.I → E.U_S x 0 s + E.U_T x 0 s ≤ Mb :=
    fun x s hx hs => (abs_le.mp (hbase x s hx hs)).2
  refine ⟨⟨?_, ?_, htie ηp⟩, ⟨?_, ?_, htie (-ηp)⟩⟩
  · -- (+) 11 above 10
    unfold discountedWelfare
    refine Welfare.tsum_pow_mul_lt_of_forall_lt hβ (hB10 ηp hηabs) (hB11 ηp hηabs) (fun t => ?_)
    rw [f10 ηp t, f11 ηp t]
    have h1 := mul_le_mul_of_nonneg_left (hgap t) hηp0
    have h2 := hlo _ _ (h11 t) (hs11 t)
    have h3 := hhi _ _ (h10 t) (hs10 t)
    nlinarith [h1, h2, h3, hηpμ]
  · -- (+) 10 above 00
    unfold discountedWelfare
    refine Welfare.tsum_pow_mul_lt_of_forall_lt hβ (hB00 ηp hηabs) (hB10 ηp hηabs) (fun t => ?_)
    rw [f00 ηp t, f10 ηp t]
    have h1 := mul_le_mul_of_nonneg_left (hs10μ t) hηp0
    have h2 := hlo _ _ (h10 t) (hs10 t)
    have h3 := hhi _ 0 (hy t) ChordEconomy.zero_mem_I
    nlinarith [h1, h2, h3, hηpμ]
  · -- (−) 10 above 11
    unfold discountedWelfare
    refine Welfare.tsum_pow_mul_lt_of_forall_lt hβ (hB11 (-ηp) hηabs') (hB10 (-ηp) hηabs')
      (fun t => ?_)
    rw [f10 (-ηp) t, f11 (-ηp) t]
    have h1 := mul_le_mul_of_nonneg_left (hgap t) hηp0
    have h2 := hhi _ _ (h11 t) (hs11 t)
    have h3 := hlo _ _ (h10 t) (hs10 t)
    nlinarith [h1, h2, h3, hηpμ]
  · -- (−) 00 above 10
    unfold discountedWelfare
    refine Welfare.tsum_pow_mul_lt_of_forall_lt hβ (hB10 (-ηp) hηabs') (hB00 (-ηp) hηabs')
      (fun t => ?_)
    rw [f00 (-ηp) t, f10 (-ηp) t]
    have h1 := mul_le_mul_of_nonneg_left (hs10μ t) hηp0
    have h2 := hhi _ _ (h10 t) (hs10 t)
    have h3 := hlo _ 0 (hy t) ChordEconomy.zero_mem_I
    nlinarith [h1, h2, h3, hηpμ]

end ChordEconomyCs

namespace ChordEconomyRelief

variable (E : ChordEconomyRelief)

/-- Welfare flow of a representation along the myopic equilibrium, in its stage form (the
one-period forms of interiority and placability, `u_hi < q` and `u_hi < k_lo`).
Scope: general class (relief extension). -/
def repFlowMyopic (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo)
    (R : Welfare.InterestGroupRep E.U_S E.U_T) (x₀ : ℝ) (t : ℕ) : ℝ :=
  R.welfare ((E.myopicPathS hS hSR hPs) x₀ t)
    ((E.myopicEquilibriumTopS hS hSR hPs).α ((E.myopicPathS hS hSR hPs) x₀ t))
    (E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs)
      ((E.myopicPathS hS hSR hPs) x₀ t))

/-- Welfare flow of a representation along the constructed forward-looking equilibrium, given a
nondecreasing response.
Scope: general class (relief extension). -/
def repFlowForward (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (R : Welfare.InterestGroupRep E.U_S E.U_T) (x₀ : ℝ) (t : ℕ) : ℝ :=
  R.welfare ((E.dynamicPathOf hTM hmono) x₀ t)
    ((E.equilibriumTop hTM hmono).α ((E.dynamicPathOf hTM hmono) x₀ t))
    (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono)
      ((E.dynamicPathOf hTM hmono) x₀ t))

/-- **W4 for the main comparison: the governments' game does not determine the welfare
ranking of the myopic and the forward-looking equilibria** (round W2, 2026-10-16; the author's
layout decision D3: the main text compares case `00` with case `11`). Under the conditions of
the stage-form regime separation (`myopic_dynamic_equilibrium_separation_generalF_stage`: the
one-period forms of interiority and placability, stage relief, the loss-offset condition, and
a nondecreasing response at defiance), there are two interest-group representations (two
groups per country, positive constant weights) of the same government payoffs, hence the same
two constructed equilibria, such that at every feasible start and every common planner discount
factor in `[0, 1)` one ranks the forward-looking equilibrium strictly above the myopic one and
the other strictly below. No zero-sanction neutrality, no semiconvex sanction sections and no
dynamic relief condition: those are read only by the Sender-only case `01`, which this
comparison does not contain. The representations are `etaRep (±ηp)`: the Sender side carries a
net sanction coefficient of either sign; the forward-looking sanction is at least the floor
`sfloor > 0` at every date and the myopic sanction is zero.
Scope: general class (relief extension). -/
theorem exists_reps_reversing_myopic_forward_ranking (hS : E.uhi < E.q)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    ∃ Rp Rm : Welfare.InterestGroupRep E.U_S E.U_T,
      ∀ x₀ ∈ Sanctions.I, ∀ β ∈ Set.Ico (0 : ℝ) 1,
        discountedWelfare β (E.repFlowMyopic hS hSR hPs Rp x₀)
            < discountedWelfare β (E.repFlowForward hTM hmono Rp x₀)
        ∧ discountedWelfare β (E.repFlowForward hTM hmono Rm x₀)
            < discountedWelfare β (E.repFlowMyopic hS hSR hPs Rm x₀) := by
  set Mb : ℝ := E.MU + E.MT₀
  have hMb0 : 0 ≤ Mb := add_nonneg E.MU_nonneg E.MT₀_nonneg
  set μ : ℝ := E.sfloor
  have hμ0 : 0 < μ := E.sfloor_pos
  set ηp : ℝ := (2 * Mb + 1) / μ
  have hηp0 : 0 ≤ ηp := div_nonneg (by linarith) hμ0.le
  have hηpμ : ηp * μ = 2 * Mb + 1 := div_mul_cancel₀ _ hμ0.ne'
  refine ⟨E.etaRep ηp, E.etaRep (-ηp), fun x₀ hx₀ β hβ => ?_⟩
  -- feasibility along the two paths
  have hy : ∀ t, (E.myopicPathS hS hSR hPs) x₀ t ∈ Sanctions.I := fun t =>
    E.toParams.rulePathF_mem_I (fun x hx => by
      rw [(E.myopicRuleS_eq_zero hS hSR hPs) hx]; exact ⟨le_rfl, zero_le_one⟩) hx₀ t
  have h11 : ∀ t, (E.dynamicPathOf hTM hmono) x₀ t ∈ Sanctions.I := fun t =>
    E.toParams.rulePathF_mem_I (E.dynamicRule_mem_of_response_monotone hTM hmono) hx₀ t
  have ha : ∀ t, (E.myopicEquilibriumTopS hS hSR hPs).α ((E.myopicPathS hS hSR hPs) x₀ t)
      ∈ Sanctions.I := fun t => (E.myopicEquilibriumTopS hS hSR hPs).α_mem _ (hy t)
  -- the forward-looking sanction, at least the floor
  have hs11 : ∀ t, E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t) ∈ Sanctions.I :=
    fun t => E.responsePath_mem _ _
  have hs11μ : ∀ t, μ ≤ E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t) :=
    fun t => E.responsePath_ge_sfloor E.VSstar_mem (h11 t)
  -- the base flow and its bound
  have hbase : ∀ x a s, x ∈ Sanctions.I → a ∈ Sanctions.I → s ∈ Sanctions.I →
      |E.U_S x a s + E.U_T x 0 s| ≤ Mb := by
    intro x a s hx ha hs
    calc |E.U_S x a s + E.U_T x 0 s| ≤ |E.U_S x a s| + |E.U_T x 0 s| := abs_add_le _ _
      _ ≤ E.MU + E.MT₀ := add_le_add (E.abs_U_S_le_MU hx ha hs)
          (E.abs_U_T_le_MT₀ hx ChordEconomy.zero_mem_I hs)
  have hlo : ∀ x a s, x ∈ Sanctions.I → a ∈ Sanctions.I → s ∈ Sanctions.I →
      -Mb ≤ E.U_S x a s + E.U_T x 0 s :=
    fun x a s hx ha hs => (abs_le.mp (hbase x a s hx ha hs)).1
  have hhi : ∀ x a s, x ∈ Sanctions.I → a ∈ Sanctions.I → s ∈ Sanctions.I →
      E.U_S x a s + E.U_T x 0 s ≤ Mb :=
    fun x a s hx ha hs => (abs_le.mp (hbase x a s hx ha hs)).2
  have hflowb : ∀ η x s, |η| ≤ ηp → x ∈ Sanctions.I → s ∈ Sanctions.I →
      |E.U_S x 0 s + E.U_T x 0 s + η * s| ≤ Mb + ηp := by
    intro η x s hη hx hs
    have hηs : |η * s| ≤ ηp := by
      rw [abs_mul, abs_of_nonneg hs.1]
      calc |η| * s ≤ ηp * 1 := mul_le_mul hη hs.2 hs.1 hηp0
        _ = ηp := mul_one _
    calc |E.U_S x 0 s + E.U_T x 0 s + η * s|
        ≤ |E.U_S x 0 s + E.U_T x 0 s| + |η * s| := abs_add_le _ _
      _ ≤ Mb + ηp := add_le_add (hbase x 0 s hx ChordEconomy.zero_mem_I hs) hηs
  have hηabs : |ηp| ≤ ηp := (abs_of_nonneg hηp0).le
  have hηabs' : |-ηp| ≤ ηp := by rw [abs_neg]; exact hηabs
  -- the two flows in closed form
  have f00 : ∀ η t, E.repFlowMyopic hS hSR hPs (E.etaRep η) x₀ t
      = E.U_S ((E.myopicPathS hS hSR hPs) x₀ t)
          ((E.myopicEquilibriumTopS hS hSR hPs).α ((E.myopicPathS hS hSR hPs) x₀ t)) 0
        + E.U_T ((E.myopicPathS hS hSR hPs) x₀ t) 0 0 := by
    intro η t
    unfold repFlowMyopic
    rw [E.etaRep_welfare, (E.myopicRuleS_eq_zero hS hSR hPs) (hy t)]
    ring
  have f11 : ∀ η t, E.repFlowForward hTM hmono (E.etaRep η) x₀ t
      = E.U_S ((E.dynamicPathOf hTM hmono) x₀ t) 0
          (E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t))
        + E.U_T ((E.dynamicPathOf hTM hmono) x₀ t) 0
          (E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t))
        + η * E.responsePath E.VSstar ((E.dynamicPathOf hTM hmono) x₀ t) := by
    intro η t
    unfold repFlowForward
    have hα : (E.equilibriumTop hTM hmono).α ((E.dynamicPathOf hTM hmono) x₀ t) = 0 := rfl
    rw [hα, E.etaRep_welfare,
      (E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono) (h11 t)]
  -- bounds on both flows
  have hB00 : ∀ η t, |E.repFlowMyopic hS hSR hPs (E.etaRep η) x₀ t| ≤ Mb + ηp := by
    intro η t
    rw [f00 η t]
    linarith [hbase _ _ 0 (hy t) (ha t) ChordEconomy.zero_mem_I]
  have hB11 : ∀ η, |η| ≤ ηp → ∀ t,
      |E.repFlowForward hTM hmono (E.etaRep η) x₀ t| ≤ Mb + ηp := by
    intro η hη t
    rw [f11 η t]
    exact hflowb η _ _ hη (h11 t) (hs11 t)
  refine ⟨?_, ?_⟩
  · -- (+) the forward-looking equilibrium above the myopic one
    unfold discountedWelfare
    refine Welfare.tsum_pow_mul_lt_of_forall_lt hβ (hB00 ηp) (hB11 ηp hηabs) (fun t => ?_)
    rw [f00 ηp t, f11 ηp t]
    have h1 := mul_le_mul_of_nonneg_left (hs11μ t) hηp0
    have h2 := hlo _ 0 _ (h11 t) ChordEconomy.zero_mem_I (hs11 t)
    have h3 := hhi _ _ 0 (hy t) (ha t) ChordEconomy.zero_mem_I
    nlinarith [h1, h2, h3, hηpμ]
  · -- (−) the myopic equilibrium above the forward-looking one
    unfold discountedWelfare
    refine Welfare.tsum_pow_mul_lt_of_forall_lt hβ (hB11 (-ηp) hηabs') (hB00 (-ηp)) (fun t => ?_)
    rw [f11 (-ηp) t, f00 (-ηp) t]
    have h1 := mul_le_mul_of_nonneg_left (hs11μ t) hηp0
    have h2 := hhi _ 0 _ (h11 t) ChordEconomy.zero_mem_I (hs11 t)
    have h3 := hlo _ _ 0 (hy t) (ha t) ChordEconomy.zero_mem_I
    nlinarith [h1, h2, h3, hηpμ]

end ChordEconomyRelief

end

end Examples
end Sanctions

#print axioms Sanctions.Examples.ChordEconomy.exists_planner_efficient_rep
#print axioms Sanctions.Examples.ChordEconomy.planner_efficient_rep_at_policy_zero
#print axioms Sanctions.Examples.ChordEconomyCs.exists_reps_reversing_regime_ranking
#print axioms Sanctions.Examples.ChordEconomyRelief.exists_reps_reversing_myopic_forward_ranking
