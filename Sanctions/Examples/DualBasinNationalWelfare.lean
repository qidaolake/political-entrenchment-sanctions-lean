/-
Sanctions/Examples/DualBasinNationalWelfare.lean

**Entrenchment and the government-nation gap at the two-basin economy**
(Lean round D; design in `suggestions/2026-10-10-jet-submission/framing-2026-10-12/LEAN-ROUND-D.md`).

Plain words. At the dual-basin economy `dualParams`, each government's payoff is its
nation's welfare plus a political part that grows with the Target-side hardliners'
power `x`: the Sender government earns `2xs` from sanctioning an entrenched adversary,
and the Target incumbent earns `(19/10)x`. Both political parts are zero at `x = 0`, so at
full trade government payoff and national welfare coincide (D1, D2). After a long enough
temporary full-sanction episode, the certified equilibrium keeps full sanctions and full
defiance forever. Each nation is then worse off in every period than at full trade, the
Sender government is better off in every period, and the Target government is exactly as
well off as under permanent relief from the same state (D3). A Sender whose payoff is its
nation's welfare would not sanction at all (D4).

Scope (Rule 9A). Everything here is "at one economy" or "there is an equilibrium". It is
an existence certificate; it licenses no claim about other economies, about every
equilibrium, or about magnitudes. The comparison in D4 is within the class of equilibria
whose Target value lies in the dual-basin Target carrier `dbCarrierT`.

Rule 9B (non-vacuity of the new economy `dualRepParams`) is in section 5.
-/
import Sanctions.Examples.DualBasinSelectionWitness
import Sanctions.Examples.DualBasinTwoSidedRegimes
import Sanctions.Theory.Welfare.RepresentativeSender

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. D1: the welfare split -/

/-- Sender-country welfare: the Sender government's payoff without the political return
`2xs` to sanctioning an entrenched adversary. It does not depend on the state `x`. -/
def dbW_S (_x a s : ℝ) : ℝ := a - 1/2 * s ^ 2 - 1/2 * s - 2 * a * s

/-- Target-country welfare: the Target government's payoff without the incumbent's value
`(19/10)x` of the hardliners' power. It does not depend on the state `x`. -/
def dbW_T (_x a s : ℝ) : ℝ := -(1/5) * a - 9/10 * s

/-- The Sender government's payoff is national welfare plus the political return `2xs`.
An identity of the definitions, at every state and action. -/
theorem dbU_S_split (x a s : ℝ) : dbU_S x a s = dbW_S x a s + 2 * x * s := by
  unfold dbU_S dbW_S; ring

/-- The Target government's payoff is national welfare plus the incumbent's value
`(19/10)x` of the hardliners' power. An identity of the definitions. -/
theorem dbU_T_split (x a s : ℝ) : dbU_T x a s = dbW_T x a s + 19/10 * x := by
  unfold dbU_T dbW_T; ring

/-- At full trade (`x = 0`) both political parts vanish: each government's payoff equals
its nation's welfare, at every action. -/
theorem db_political_parts_zero_at_full_trade (a s : ℝ) :
    dbU_S 0 a s = dbW_S 0 a s ∧ dbU_T 0 a s = dbW_T 0 a s := by
  constructor
  · rw [dbU_S_split]; ring
  · rw [dbU_T_split]; ring

/-- Both political parts are non-decreasing in the hardliners' power `x` (the Sender's for
any non-negative sanction `s`). -/
theorem db_political_parts_monotone {s : ℝ} (hs : 0 ≤ s) :
    Monotone (fun x : ℝ => 2 * x * s) ∧ Monotone (fun x : ℝ => 19/10 * x) := by
  constructor
  · intro x y h
    change 2 * x * s ≤ 2 * y * s
    nlinarith
  · intro x y h
    change 19/10 * x ≤ 19/10 * y
    linarith

/-! ## 2. D2: the representative stage choice and payoffs at full trade -/

/-- Below the state `1/4`, the Sender's own stage choice `dbσ` is no sanction, whatever
non-negative compliance the Target chooses. At the dual-basin economy only. -/
theorem dbσ_eq_zero_of_le {x a : ℝ} (hx : x ≤ 1 / 4) (ha : 0 ≤ a) : dbσ x a = 0 := by
  unfold dbσ
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))

/-- Along permanent full trade (state `0`, no sanction, full defiance `a = 0`), each
government's payoff equals its nation's welfare. -/
theorem db_full_trade_payoffs_eq_welfare :
    dbU_S 0 0 0 = dbW_S 0 0 0 ∧ dbU_T 0 0 0 = dbW_T 0 0 0 :=
  db_political_parts_zero_at_full_trade 0 0

/-! ## 3. D3: entrenchment loss after the episode -/

/-- The closed-form path of the state under permanent full sanction from `z`:
`1 - (1 - z)(9/10)^n`, the iterates of `F(., 1) = (9x + 1)/10`. -/
def dbHighPath (z : ℝ) (n : ℕ) : ℝ := 1 - (1 - z) * (9/10 : ℝ) ^ n

/-- The closed-form path of the state under permanent relief from `z`:
`z (9/10)^n`, the iterates of `F(., 0) = 9x/10`. -/
def dbReliefPath (z : ℝ) (n : ℕ) : ℝ := z * (9/10 : ℝ) ^ n

/-- A state sequence obeying `y_{n+1} = (9 y_n + 1)/10` is the closed-form full-sanction
path from its first state. -/
theorem dbHighPath_of_step (y : ℕ → ℝ) (h : ∀ n, y (n + 1) = (9 * y n + 1) / 10) :
    ∀ n, y n = dbHighPath (y 0) n := by
  intro n
  induction n with
  | zero => simp [dbHighPath]
  | succ n ih =>
    rw [h n, ih]
    unfold dbHighPath
    ring

/-- With the factor `β ∈ [0,1)`, a constant per-period amount `c` has discounted sum
`c / (1 - β)`. -/
theorem db_discounted_const_hasSum (c : ℝ) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    HasSum (fun n : ℕ => β ^ n * c) (c / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ.1 hβ.2).mul_right c
  rwa [← div_eq_inv_mul] at h

/-- The per-period national payoffs at full sanction `s = 1` and full defiance `a = 0`,
at any state: Sender welfare `-1`, Target welfare `-9/10`. Relative to full trade, where
both are `0`, these are the per-period national losses. -/
theorem db_nation_payoffs_full_sanction (x : ℝ) :
    dbW_S x 0 1 = -1 ∧ dbW_T x 0 1 = -(9/10) := by
  constructor <;> norm_num [dbW_S, dbW_T]

/-- Under permanent full sanction, the Target government's discounted payoff at the Target's
own discount factor `9/10`, from state `z`, is `10 z`. -/
theorem dbHigh_target_hasSum (z : ℝ) :
    HasSum (fun n : ℕ => (9/10 : ℝ) ^ n * dbU_T (dbHighPath z n) 0 1) (10 * z) := by
  have h1 : HasSum (fun n : ℕ => (9/10 : ℝ) ^ n) 10 := by
    have := hasSum_geometric_of_lt_one (r := (9/10 : ℝ)) (by norm_num) (by norm_num)
    convert this using 1; norm_num
  have h2 : HasSum (fun n : ℕ => (81/100 : ℝ) ^ n) (100/19) := by
    have := hasSum_geometric_of_lt_one (r := (81/100 : ℝ)) (by norm_num) (by norm_num)
    convert this using 1; norm_num
  have h := h1.sub (h2.mul_left (19/10 * (1 - z)))
  convert h using 1
  · funext n
    have e : (81/100 : ℝ) ^ n = (9/10) ^ n * (9/10) ^ n := by
      rw [← mul_pow]; norm_num
    unfold dbU_T dbHighPath
    rw [e]; ring
  · ring

/-- Under permanent relief (no sanction, full defiance), the Target government's
discounted payoff at the discount factor `9/10`, from state `z`, is also `10 z`. -/
theorem dbRelief_target_hasSum (z : ℝ) :
    HasSum (fun n : ℕ => (9/10 : ℝ) ^ n * dbU_T (dbReliefPath z n) 0 0) (10 * z) := by
  have h2 : HasSum (fun n : ℕ => (81/100 : ℝ) ^ n) (100/19) := by
    have := hasSum_geometric_of_lt_one (r := (81/100 : ℝ)) (by norm_num) (by norm_num)
    convert this using 1; norm_num
  have h := h2.mul_left (19/10 * z)
  convert h using 1
  · funext n
    have e : (81/100 : ℝ) ^ n = (9/10) ^ n * (9/10) ^ n := by
      rw [← mul_pow]; norm_num
    unfold dbU_T dbReliefPath
    rw [e]; ring
  · ring

/-- **Entrenchment loss after a temporary full-sanction episode (there is an equilibrium).**
There is a certified equilibrium `E` of the dual-basin economy such that, from every
feasible start `x₀` and after every full-sanction episode of at least the canonical length
`fullShockEntryHorizon (19/20)`, the resumed state path `y` satisfies the following at
every later date `n`.

1. The state lies in the high basin `[19/20, 1]`, the Target defies fully (`E.α (y n) = 0`)
   and the realised sanction is `1`.
2. Per-period national losses against full trade (where both nations' welfare is `0`):
   Sender nation `-1`, Target nation `-9/10`.
3. For every national discount factor `β ∈ [0,1)` the discounted national losses are
   `-1/(1-β)` and `-(9/10)/(1-β)`.
4. The Sender government gains every period: its payoff is `2 y n - 1 ≥ 9/10`, above its
   payoff `0` at full trade.
5. The Target government is exactly as well off as under permanent relief from the
   episode-end state `y 0`: at its own discount factor `9/10` both discounted sums equal
   `10 (y 0)`.

Scope: one economy and one equilibrium (the one of `dbCert_three_goals_high`); nothing is
claimed about other equilibria or other economies. -/
theorem db_entrenchment_loss_after_episode :
    ∃ E : dualParams.FeedbackStackelbergEquilibriumTop,
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ T : ℕ, dualParams.fullShockEntryHorizon (19/20) ≤ T →
      ∀ y : ℕ → ℝ,
        y = dualParams.dynamicTopLockInPathF E.V_S E.α
              (dualParams.episodePath (fun _ => 1) x₀ T) →
        (∀ n, y n ∈ Set.Icc (19/20 : ℝ) 1 ∧ E.α (y n) = 0 ∧
            dualParams.dynamicTopRealizedRule E.V_S E.α (y n) = 1) ∧
        (∀ n, dbW_S (y n) (E.α (y n)) 1 = -1 ∧ dbW_T (y n) (E.α (y n)) 1 = -(9/10)) ∧
        (∀ β ∈ Set.Ico (0 : ℝ) 1,
            HasSum (fun n : ℕ => β ^ n * dbW_S (y n) (E.α (y n)) 1) (-1 / (1 - β)) ∧
            HasSum (fun n : ℕ => β ^ n * dbW_T (y n) (E.α (y n)) 1) (-(9/10) / (1 - β))) ∧
        (∀ n, dbU_S (y n) (E.α (y n)) 1 = 2 * y n - 1 ∧
            dbU_S 0 0 0 + 9/10 ≤ dbU_S (y n) (E.α (y n)) 1) ∧
        (HasSum (fun n : ℕ => (9/10 : ℝ) ^ n * dbU_T (y n) (E.α (y n)) 1) (10 * y 0) ∧
          HasSum (fun n : ℕ => (9/10 : ℝ) ^ n * dbU_T (dbReliefPath (y 0) n) 0 0)
            (10 * y 0)) := by
  obtain ⟨E, hVT, hVS, -, -, -⟩ := dbCert_three_goals_high
  have hhi : ∀ x ∈ Set.Icc (19/20 : ℝ) 1,
      max x (1 : ℝ) ≤ dualParams.dynamicTopRealizedRule E.V_S E.α x := by
    intro x hx
    rw [dbCert_highBasin_rule_eq_one E hVT hVS hx]
    exact max_le hx.2 le_rfl
  refine ⟨E, fun x₀ hx₀ T hT y hy => ?_⟩
  have hend : dualParams.episodePath (fun _ => 1) x₀ T ∈ Set.Icc (19/20 : ℝ) 1 := by
    rw [dualParams.episodePath_const_one]
    exact dualParams.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
      dbParams_strictAdjustment ⟨by norm_num, by norm_num⟩ x₀ hx₀ T hT
  have hmem : ∀ n, y n ∈ Set.Icc (19/20 : ℝ) 1 := fun n => by
    rw [hy]
    exact dualParams.dynamicTopLockInPathF_mem_basin E.V_S E.α hhi hend n
  have hα : ∀ n, E.α (y n) = 0 := fun n =>
    dbCert_E_alpha_eq_zero E hVT (show y n ∈ Sanctions.S from
      ⟨by linarith [(hmem n).1], (hmem n).2⟩)
  have hr : ∀ n, dualParams.dynamicTopRealizedRule E.V_S E.α (y n) = 1 := fun n =>
    dbCert_highBasin_rule_eq_one E hVT hVS (hmem n)
  have hstep : ∀ n, y (n + 1) = (9 * y n + 1) / 10 := fun n => by
    have h : y (n + 1) = dualParams.F (y n)
        (dualParams.dynamicTopRealizedRule E.V_S E.α (y n)) := by
      rw [hy, dualParams.dynamicTopLockInPathF_succ]; rfl
    rw [h, hr n, dualParams_F]
  have hhigh := dbHighPath_of_step y hstep
  refine ⟨fun n => ⟨hmem n, hα n, hr n⟩, fun n => ?_, fun β hβ => ?_, fun n => ?_, ?_⟩
  · rw [hα n]; exact db_nation_payoffs_full_sanction _
  · have hS : (fun n : ℕ => β ^ n * dbW_S (y n) (E.α (y n)) 1)
        = fun n : ℕ => β ^ n * (-1 : ℝ) := by
      funext n; rw [hα n, (db_nation_payoffs_full_sanction _).1]
    have hT' : (fun n : ℕ => β ^ n * dbW_T (y n) (E.α (y n)) 1)
        = fun n : ℕ => β ^ n * (-(9/10) : ℝ) := by
      funext n; rw [hα n, (db_nation_payoffs_full_sanction _).2]
    rw [hS, hT']
    exact ⟨db_discounted_const_hasSum _ hβ, db_discounted_const_hasSum _ hβ⟩
  · have hU : dbU_S (y n) (E.α (y n)) 1 = 2 * y n - 1 := by
      rw [hα n]; unfold dbU_S; ring
    refine ⟨hU, ?_⟩
    have := (hmem n).1
    have h0 : dbU_S 0 0 0 = 0 := by unfold dbU_S; ring
    rw [hU, h0]; linarith
  · have hT' : (fun n : ℕ => (9/10 : ℝ) ^ n * dbU_T (y n) (E.α (y n)) 1)
        = fun n : ℕ => (9/10 : ℝ) ^ n * dbU_T (dbHighPath (y 0) n) 0 1 := by
      funext n; rw [hα n, hhigh n]
    rw [hT']
    exact ⟨dbHigh_target_hasSum _, dbRelief_target_hasSum _⟩

/-! ## 4. D4: a Sender whose payoff is its nation's welfare ends the lock-in -/

/-- **The representative-Sender economy.** `dualParams` with the Sender's payoff replaced
by national welfare `dbW_S` and its stage choice replaced by the clipped vertex
`max 0 (min 1 (-1/2 - 2a))` of `dbW_S` in the sanction (zero for every `a ≥ -1/4`). The
Target side, the transition and the discount factors are those of `dualParams`. -/
def dualRepParams : AbstractGame.Params where
  δ := dualParams.δ
  δ_mem := dualParams.δ_mem
  β_T := dualParams.β_T
  β_T_mem := dualParams.β_T_mem
  β_S := dualParams.β_S
  β_S_mem := dualParams.β_S_mem
  U_T := dbU_T
  U_S := dbW_S
  σ := fun _ a => max 0 (min 1 (-1/2 - 2 * a))
  σ_mem := fun _ a => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  σ_isMaxOn_U_S := fun _ a =>
    WitnessKit.clipVertex_isMaxOn (by norm_num : (0 : ℝ) < 1/2)
      (C := a + 1/2 * (-1/2 - 2 * a) ^ 2) (fun s => by simp only [dbW_S]; ring)
  U_T_continuous := by unfold dbU_T; fun_prop
  U_S_continuous := by unfold dbW_S; fun_prop
  F := dualParams.F
  F_continuous := dualParams.F_continuous
  F_mono_x := dualParams.F_mono_x
  F_mono_s := dualParams.F_mono_s
  F_diag := dualParams.F_diag

@[simp] theorem dualRepParams_U_S : dualRepParams.U_S = dbW_S := rfl
@[simp] theorem dualRepParams_U_T : dualRepParams.U_T = dbU_T := rfl
@[simp] theorem dualRepParams_β_S : dualRepParams.β_S = 1/2 := rfl
@[simp] theorem dualRepParams_β_T : dualRepParams.β_T = 9/10 := rfl

/-- The representative-Sender economy has the transition `F(x, s) = (9x + s)/10`, as
`dualParams` does. -/
theorem dualRepParams_F (x s : ℝ) : dualRepParams.F x s = (9 * x + s) / 10 :=
  dualParams_F x s

/-- The Sender's welfare payoff at full defiance is strictly lower with any positive
sanction than with none, at every state. -/
theorem dbW_S_zero_lt {s : ℝ} (hs : 0 < s) (x : ℝ) : dbW_S x 0 s < 0 := by
  unfold dbW_S; nlinarith

/-- The Target's value function of the exact equilibrium: `V_T(x) = 10 x`. -/
def dualRepV_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => 10 * x.val, continuous_const.mul continuous_subtype_val⟩

theorem dualRepV_T_apply (x : ↥(Sanctions.S : Set ℝ)) : dualRepV_T x = 10 * x.val := rfl

/-- With the Sender value zero, the Target's joint integrand at the representative-Sender
economy is `10 x - a/5` for every feasible state and compliance. -/
theorem dualRep_joint_T_top_integrand_exact {x : ℝ} (hx : x ∈ Sanctions.S) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    dualRepParams.joint_T_top_integrand dualRepV_T 0 x a = 10 * x - a / 5 := by
  have hσ : dualRepParams.σ_dyn_top 0 x a = 0 :=
    dualRepParams.σ_dyn_top_eq_zero_of_stateFree_of_alpha_zero 0 (fun _ _ => rfl) x a
      (fun s hs hs0 => by
        have hs' : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        change dbW_S x a s < dbW_S x a 0
        unfold dbW_S; nlinarith [ha.1])
  simp only [AbstractGame.Params.joint_T_top_integrand]
  rw [hσ]
  have hF : dualRepParams.F x 0 = 9 * x / 10 := by rw [dualRepParams_F]; ring
  have hmem : 9 * x / 10 ∈ (Sanctions.S : Set ℝ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hF, dualRepV_T_apply]
  have hv : ((Sanctions.clipS' (9 * x / 10) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 9 * x / 10 :=
    Sanctions.clipS'_val_eq_of_mem hmem
  rw [hv]
  simp only [dualRepParams_U_T, dualRepParams_β_T, dbU_T]
  ring

/-- **An exact equilibrium of the representative-Sender economy (there is an equilibrium).**
The Sender's value is identically `0`, the Target's is `V_T(x) = 10 x`, the Target defies
fully at every state, and the Sender's response is no sanction. The Bellman checks:
`10x = (19/10)x + (9/10)·10·(9x/10)`; the Sender's maximum of `-s²/2 - s/2` over `[0,1]` is
`0`, attained at `s = 0`; and the Target's integrand `10x - a/5` is maximal at `a = 0`. -/
def dualRepEquilibriumTop : dualRepParams.FeedbackStackelbergEquilibriumTop where
  V_T := dualRepV_T
  V_S := 0
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := by
    symm
    refine dualRepParams.bellmanS_BCF_zero_of_stage_nonpos continuous_const ?_ ?_
    · intro x _ s hs
      change dbW_S x 0 s ≤ 0
      unfold dbW_S; nlinarith [hs.1]
    · intro x _
      change dbW_S x 0 0 = 0
      unfold dbW_S; ring
  V_T_fix_top := by
    intro x
    have hg : IsGreatest ((fun a => dualRepParams.joint_T_top_integrand dualRepV_T 0 x.val a) ''
        Sanctions.I) (10 * x.val) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · change dualRepParams.joint_T_top_integrand dualRepV_T 0 x.val 0 = 10 * x.val
        rw [dualRep_joint_T_top_integrand_exact x.property ⟨le_rfl, zero_le_one⟩]; ring
      · rintro _ ⟨a, ha, rfl⟩
        change dualRepParams.joint_T_top_integrand dualRepV_T 0 x.val a ≤ 10 * x.val
        rw [dualRep_joint_T_top_integrand_exact x.property ha]
        linarith [ha.1]
    rw [hg.csSup_eq, dualRepV_T_apply]
  α_opt_top := by
    intro x hx
    refine isMaxOn_iff.2 fun a ha => ?_
    change dualRepParams.joint_T_top_integrand dualRepV_T 0 x a ≤
      dualRepParams.joint_T_top_integrand dualRepV_T 0 x 0
    rw [dualRep_joint_T_top_integrand_exact hx ha,
      dualRep_joint_T_top_integrand_exact hx ⟨le_rfl, zero_le_one⟩]
    linarith [ha.1]

/-- **A representative Sender plays no sanction at the exact equilibrium (there is an
equilibrium).** At `dualRepEquilibriumTop` of the economy `dualRepParams`, the realised
sanction rule is `0` at every feasible state; in particular the high-basin lock-in of
`dualParams` does not arise. -/
theorem dualRep_rule_eq_zero {x : ℝ} (hx : x ∈ Sanctions.S) :
    dualRepParams.dynamicTopRealizedRule dualRepEquilibriumTop.V_S
      dualRepEquilibriumTop.α x = 0 :=
  (dualRepParams.dynamicTopRealizedRule_eq_zero_of_stateFree dualRepEquilibriumTop
    (fun _ _ => rfl) (fun x _ => by change dbW_S x 0 0 = 0; unfold dbW_S; ring)
    (fun x _ s hs hs0 => dbW_S_zero_lt (lt_of_le_of_ne hs.1 (Ne.symm hs0)) x)).2 x hx

/-- Joint Target integrand in closed form at the representative-Sender economy, for any
equilibrium value pair with `V_T` in the dual-basin Target carrier: the knife edge of the
Target (sanctions cost it exactly what they add through the continuation) makes it
independent of the Sender's choice. -/
theorem dualRep_joint_T_top_integrand_eq
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (hV_T : V_T ∈ dbCarrierT)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    dualRepParams.joint_T_top_integrand V_T V_S x a
      = 10 * x - 1 / 5 * a + 9 / 10 * V_T (Sanctions.clipS' 0) := by
  simp only [AbstractGame.Params.joint_T_top_integrand]
  exact dbCert_targetObj_const hV_T hx (dualRepParams.σ_dyn_top_mem_I V_S x a) a

/-- **Every representative-Sender equilibrium with Target value in the dual-basin carrier
has realised sanction zero (scope: that class).** Let `E` be any upper-selector
equilibrium of `dualRepParams` with `E.V_T ∈ dbCarrierT`. Then the Target defies fully at
every feasible state (as `dbCert_E_alpha_eq_zero` shows at `dualParams`), the Sender's
value is identically `0`, and the realised sanction is `0` at every feasible state. It
says nothing about equilibria whose Target value lies outside `dbCarrierT`. -/
theorem dualRep_rule_eq_zero_of_carrier
    (E : dualRepParams.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ dbCarrierT) {x : ℝ} (hx : x ∈ Sanctions.S) :
    dualRepParams.dynamicTopRealizedRule E.V_S E.α x = 0 := by
  have hα0 : ∀ y ∈ Sanctions.S, E.α y = 0 := by
    intro y hy
    have h : dualRepParams.joint_T_top_integrand E.V_T E.V_S y 0
        ≤ dualRepParams.joint_T_top_integrand E.V_T E.V_S y (E.α y) :=
      E.α_opt_top y hy (show (0 : ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
    rw [dualRep_joint_T_top_integrand_eq hVT E.V_S hy 0,
      dualRep_joint_T_top_integrand_eq hVT E.V_S hy (E.α y)] at h
    linarith [(E.α_mem y hy).1]
  exact (dualRepParams.dynamicTopRealizedRule_eq_zero_of_stateFree E hα0
    (fun x _ => by change dbW_S x 0 0 = 0; unfold dbW_S; ring)
    (fun x _ s hs hs0 => dbW_S_zero_lt (lt_of_le_of_ne hs.1 (Ne.symm hs0)) x)).2 x hx

/-! ## 5. Rule 9B: non-vacuity of `dualRepParams` -/

/-- Rule 9B: the economy is concrete data, not assumed, and differs from `dualParams`. -/
example : dualRepParams.U_S 1 0 1 ≠ dualParams.U_S 1 0 1 := by
  norm_num [dbW_S, dbU_S]

/-- Rule 9B: the Sender's stage choice is not constantly zero (it is `1` for `a = -1`),
so the zero rule in D4 is a result about the equilibrium, not about a degenerate `σ`. -/
example : dualRepParams.σ 0 (-1) = 1 := by
  norm_num [dualRepParams]

/-- Rule 9B: the equilibrium hypothesis bundle is inhabited, by `dualRepEquilibriumTop`
(joint satisfiability; the carrier lemma is not about an empty class), and the exact
equilibrium has a non-zero Target value, so it is not a degenerate all-zero object. -/
example : dualRepEquilibriumTop.V_T ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 10 := by
  change 10 * (1 : ℝ) = 10
  norm_num

/-! ## Rule 10 -/

-- #print axioms Sanctions.Examples.db_entrenchment_loss_after_episode
-- #print axioms Sanctions.Examples.dualRep_rule_eq_zero_of_carrier
-- #print axioms Sanctions.Examples.dualRep_rule_eq_zero

end

end Examples
end Sanctions
