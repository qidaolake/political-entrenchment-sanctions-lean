/-
Sanctions/Theory/Microfoundations/FourGroupPlannerOptimum.lean

**The planner's optimum for any four-group polity and any transition** (BI.2,
2026-10-07; the reader's E5-1; `prop:planner-optimum-lower-bound`).

`Examples/FourGroupPlannerWitness.lean` solves the unit-weight planner's problem
at one polity (`fourGroupCert`) and one transition (the affine law at `δ = 1/2`):
the zero-sanction path attains the supremum of discounted welfare over all
feasible paths. This file proves the same verdict for every polity and every
transition that keeps the cube and is monotone in both arguments, under an
explicit margin, and the certificate theorem becomes an instance.

**Objects.** A feasible planner path from `x0` (`PlannerPath F x0`) is any
cube-valued triple of state, compliance and sanction sequences that starts at
`x0` and obeys `x_{t+1} = F(x_t, s_t)`; `plannerOptimalValue` is the supremum of
the discounted planner welfare over them; `zeroValue` is the value of the
zero-sanction path with the best constant compliance `a*`. The compliance part
of the planner flow is `φ(a) = (base_S + c_K − c_J)·a − k_T·a²`
(`complianceFlow`); its maximiser on `[0,1]` exists by compactness
(`exists_complianceFlow_max`) and is chosen, not assumed (`optCompliance`).

**The theorem.** Write `B = b_J − b_K`. The candidate value
`v(x) = B·Σ_t β^t y_t(x) + φ(a*)/(1 − β)`, with `y_t(x)` the zero-sanction path
from `x`, satisfies the one-step planner inequality
`W(x,a,s) + β·v(F(x,s)) ≤ v(x)` at every feasible triple as soon as the
**political margin** `(g_J − q_K − d_s)·s + β·B·(Y(F(x,s)) − Y(F(x,0))) ≤ 0`
holds (`bellman_le_of_politicalMargin`; the rest of the slack is
`φ(a) − φ(a*) − k_S·s² − w_pl·s·a ≤ 0`, from the polity's own fields `kS_pos` and
`w_pl_nn`). The supersolution bound of `Foundations/DiscountedChordSum` then
bounds every feasible value by `v(x0)`, and the zero-sanction path attains it
(`plannerOptimalValue_eq_of_politicalMargin`). The margin is discharged in two
cases on the sign of `B` (the approved hypotheses of BI.2, on the new theorems
only):

* `B ≥ 0` (`plannerOptimalValue_eq_of_upperChords`): a sanction upper chord `L`
  (`SanctionUpperChord F L`), an upper state chord `λ` on the zero-sanction
  section with `β·λ < 1`, and `g_J − q_K + β·B·L/(1 − β·λ) ≤ d_s`;
* `B ≤ 0` (`plannerOptimalValue_eq_of_nonpos`): `g_J − q_K ≤ d_s` and nothing on
  `F` beyond monotonicity, since a higher sanction then raises the state and the
  planner values the state negatively;
* affine, either sign (`plannerOptimalValue_eq_affineF`, affine-restricted):
  `g_J − q_K + β·δ·B/(1 − β(1 − δ)) ≤ d_s`, where the political term is computed
  exactly.

The loss corollaries (`plannerOptimalValue_loss_of_upperChords`, `_of_nonpos`,
`plannerOptimalValue_loss_affineF`) subtract the value of the persistent corner
path (full sanctions against full defiance), using the accounting identity of
`FourGroupPlanner.lean`. That path is equilibrium play only where an equilibrium
is shown to play it (at the certificate economy, `fgcExactEquilibriumTop`;
Rule 1); here it is a feasible comparison path.

Rule 22: general in `F` except the affine corollaries, which say so. Rule 3: the
margin cases, the chord pair `(L, λ)` and `β·λ < 1` are the user-approved
hypotheses of BI.2 (2026-10-06) and sit on these new theorems only; no existing
statement changes. The maximiser `a*` is constructed. The political-margin core
is a verification theorem in the sense of Stokey–Lucas–Prescott §4.1; its
hypothesis is discharged in each corollary.
-/

import Sanctions.Theory.Microfoundations.FourGroupPlanner
import Sanctions.Foundations.DiscountedChordSum

namespace Sanctions
namespace KaempferLowenberg

open Set
open Sanctions.Foundations.DiscountedChordSum

/-! ## 1. Feasible planner paths -/

/-- **A feasible planner path from `x0` under a transition `F`** (general in `F`):
cube-valued state, compliance and sanction sequences, starting at `x0`, with the
state obeying `x_{t+1} = F(x_t, s_t)`. The definition of the planner's feasible
set, not an economic assumption; the certificate economy's `FGCPlannerPath` is
the case `F = fgcParams.F` field by field. -/
structure PlannerPath (F : ℝ → ℝ → ℝ) (x0 : ℝ) where
  x : ℕ → ℝ
  a : ℕ → ℝ
  s : ℕ → ℝ
  x_zero : x 0 = x0
  x_mem : ∀ t, x t ∈ Icc (0 : ℝ) 1
  a_mem : ∀ t, a t ∈ Icc (0 : ℝ) 1
  s_mem : ∀ t, s t ∈ Icc (0 : ℝ) 1
  step : ∀ t, x (t + 1) = F (x t) (s t)

/-! ## 2. The discounted state sum along the zero-sanction path

`Y(x) = Σ_t β^t y_t(x)` with `y_t(x)` the zero-sanction path from `x`
(`zeroPathF`). It is the planner's capitalised value of the state when sanctions
are off, per unit of `B`. Everything here is general in `F`. -/

/-- **The discounted zero-sanction state sum** `Y(x) = Σ_t β^t y_t(x)` (general in
`F`). -/
noncomputable def zeroStateSum (F : ℝ → ℝ → ℝ) (β x : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * zeroPathF F x t

/-- The zero-sanction path from `x` shifted by one date is the zero-sanction path
from `F(x, 0)`. -/
theorem zeroPathF_succ_eq_shift (F : ℝ → ℝ → ℝ) (x : ℝ) :
    ∀ t, zeroPathF F x (t + 1) = zeroPathF F (F x 0) t
  | 0 => rfl
  | t + 1 => by
      rw [zeroPathF_succ F x (t + 1), zeroPathF_succ_eq_shift F x t,
        zeroPathF_succ F (F x 0) t]

/-- Under monotonicity in the state the zero-sanction path is monotone in its
start. -/
theorem zeroPathF_mono {F : ℝ → ℝ → ℝ} (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    {x x' : ℝ} (h : x ≤ x') : ∀ t, zeroPathF F x t ≤ zeroPathF F x' t
  | 0 => h
  | t + 1 => hF_mono_x 0 (zeroPathF_mono hF_mono_x h t)

/-- On the cube the zero-sanction path is bounded by one in absolute value. -/
theorem abs_zeroPathF_le {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (t : ℕ) : |zeroPathF F x t| ≤ 1 := by
  have h := zeroPathF_mem_cube hF_mem hx t
  exact abs_le.mpr ⟨by linarith [h.1], h.2⟩

/-- Along the zero-sanction path from a cube start the discounted state series
`Σ_t β^t y_t(x)` is summable (general in `F`; only cube preservation is used). -/
theorem zeroStateSum_summable {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Summable (fun t : ℕ => β ^ t * zeroPathF F x t) :=
  summable_pow_mul_of_abs_le hβ.1 hβ.2 (abs_zeroPathF_le hF_mem hx)

/-- `|Y(x)| ≤ 1/(1 − β)` on the cube. -/
theorem abs_zeroStateSum_le {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |zeroStateSum F β x| ≤ 1 / (1 - β) :=
  abs_tsum_pow_mul_le hβ.1 hβ.2 (abs_zeroPathF_le hF_mem hx)

/-- **The head-and-shift identity** `Y(x) = x + β·Y(F(x, 0))` (general in `F`). -/
theorem zeroStateSum_eq_head {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    zeroStateSum F β x = x + β * zeroStateSum F β (F x 0) := by
  unfold zeroStateSum
  rw [tsum_pow_mul_eq_head_add hβ.1 hβ.2 (abs_zeroPathF_le hF_mem hx)]
  simp only [zeroPathF_zero, zeroPathF_succ_eq_shift]

/-- `Y` is monotone on the cube when `F` is monotone in the state. -/
theorem zeroStateSum_mono {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x x' : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hx' : x' ∈ Icc (0 : ℝ) 1) (h : x ≤ x') :
    zeroStateSum F β x ≤ zeroStateSum F β x' :=
  (zeroStateSum_summable hF_mem hβ hx).tsum_le_tsum
    (fun t => mul_le_mul_of_nonneg_left (zeroPathF_mono hF_mono_x h t) (pow_nonneg hβ.1 t))
    (zeroStateSum_summable hF_mem hβ hx')

/-- **The zero-section band rate is nonnegative**, given monotonicity in the state,
so it need not be assumed: the band between the states `0` and `1` reads
`0 ≤ F(1,0) − F(0,0) ≤ λ`. -/
theorem zeroBand_nonneg {F : ℝ → ℝ → ℝ} {lam : ℝ}
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hband : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      F y₂ 0 - F y₁ 0 ≤ lam * (y₂ - y₁)) : 0 ≤ lam := by
  have h := hband 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  have hm : F 0 0 ≤ F 1 0 := hF_mono_x 0 zero_le_one
  linarith

/-- Under the zero-section band at rate `λ`, two zero-sanction paths separate by at
most `λ^t` times their initial gap. -/
theorem zeroPathF_sub_le_pow {F : ℝ → ℝ → ℝ} {lam : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hband : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      F y₂ 0 - F y₁ 0 ≤ lam * (y₂ - y₁))
    {x x' : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx' : x' ∈ Icc (0 : ℝ) 1) (h : x ≤ x') :
    ∀ t, zeroPathF F x' t - zeroPathF F x t ≤ lam ^ t * (x' - x)
  | 0 => by simp
  | t + 1 => by
      have hlam := zeroBand_nonneg hF_mono_x hband
      have ih := zeroPathF_sub_le_pow hF_mem hF_mono_x hband hx hx' h t
      have hm := zeroPathF_mono hF_mono_x h t
      have hb := hband _ (zeroPathF_mem_cube hF_mem hx t) _ (zeroPathF_mem_cube hF_mem hx' t) hm
      rw [zeroPathF_succ, zeroPathF_succ, pow_succ]
      calc F (zeroPathF F x' t) 0 - F (zeroPathF F x t) 0
          ≤ lam * (zeroPathF F x' t - zeroPathF F x t) := hb
        _ ≤ lam * (lam ^ t * (x' - x)) := mul_le_mul_of_nonneg_left ih hlam
        _ = lam ^ t * lam * (x' - x) := by ring

/-- **The band bounds the rise of `Y`** (general in `F`): under the zero-section
band at rate `λ` with `β·λ < 1`, `Y(x') − Y(x) ≤ (x' − x)/(1 − β·λ)` for
`x ≤ x'` on the cube. -/
theorem zeroStateSum_sub_le {F : ℝ → ℝ → ℝ} {lam : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hband : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      F y₂ 0 - F y₁ 0 ≤ lam * (y₂ - y₁))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) (hβlam : β * lam < 1)
    {x x' : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx' : x' ∈ Icc (0 : ℝ) 1) (h : x ≤ x') :
    zeroStateSum F β x' - zeroStateSum F β x ≤ (x' - x) / (1 - β * lam) := by
  have hlam := zeroBand_nonneg hF_mono_x hband
  have hs := zeroStateSum_summable hF_mem hβ hx
  have hs' := zeroStateSum_summable hF_mem hβ hx'
  have hq0 : 0 ≤ β * lam := mul_nonneg hβ.1 hlam
  have hg := summable_geometric_of_lt_one hq0 hβlam
  unfold zeroStateSum
  rw [← hs'.tsum_sub hs]
  calc ∑' t : ℕ, (β ^ t * zeroPathF F x' t - β ^ t * zeroPathF F x t)
      ≤ ∑' t : ℕ, (x' - x) * (β * lam) ^ t := by
        refine (hs'.sub hs).tsum_le_tsum (fun t => ?_) (hg.mul_left _)
        have hp := zeroPathF_sub_le_pow hF_mem hF_mono_x hband hx hx' h t
        rw [← mul_sub, mul_pow]
        calc β ^ t * (zeroPathF F x' t - zeroPathF F x t)
            ≤ β ^ t * (lam ^ t * (x' - x)) := mul_le_mul_of_nonneg_left hp (pow_nonneg hβ.1 t)
          _ = (x' - x) * (β ^ t * lam ^ t) := by ring
    _ = (x' - x) / (1 - β * lam) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hβlam, div_eq_mul_inv]

/-- **Affine-restricted (Rule 22)**: under `F = affineF δ`, `Y(x) = x/(1 − β(1 − δ))`
exactly, for every start. -/
theorem zeroStateSum_affineF {δ β : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hβ : β ∈ Ico (0 : ℝ) 1) (x : ℝ) :
    zeroStateSum (AbstractGame.affineF δ) β x = x / (1 - β * (1 - δ)) := by
  have hγ0 : 0 ≤ β * (1 - δ) := mul_nonneg hβ.1 (by linarith [hδ.2])
  have hγ1 : β * (1 - δ) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hβ.1 (by linarith [hδ.1])) hβ.2
  unfold zeroStateSum
  rw [zeroPathF_affineF]
  simp only [affineZeroPath]
  calc ∑' t : ℕ, β ^ t * (x * (1 - δ) ^ t) = ∑' t : ℕ, x * (β * (1 - δ)) ^ t :=
        tsum_congr (fun t => by rw [mul_pow]; ring)
    _ = x / (1 - β * (1 - δ)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hγ0 hγ1, div_eq_mul_inv]

/-! ## 3. The compliance flow, the zero-sanction value and the planner's value -/

namespace FourGroup

variable (G : FourGroup)

/-- **The compliance part of the planner flow**,
`φ(a) = (base_S + c_K − c_J)·a − k_T·a²`: what the unit-weight planner collects
from compliance when no sanction is imposed. No transition enters. -/
def complianceFlow (a : ℝ) : ℝ := (G.base_S + G.c_K - G.c_J) * a - G.kT * a ^ 2

/-- The compliance flow `φ` is continuous: it is a polynomial in `a`. No transition
enters. -/
theorem complianceFlow_continuous : Continuous G.complianceFlow := by
  unfold complianceFlow
  fun_prop

/-- **The best compliance exists, by compactness** (the plan's `exists_phi_max`):
`φ` is continuous, so it attains its maximum on `[0,1]`. This is why the
maximiser `a*` is data and not an assumption. -/
theorem exists_complianceFlow_max :
    ∃ a ∈ Icc (0 : ℝ) 1, IsMaxOn G.complianceFlow (Icc (0 : ℝ) 1) a :=
  isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one)
    G.complianceFlow_continuous.continuousOn

/-- **A chosen best compliance `a*`** (constructed from `exists_complianceFlow_max`,
not assumed). -/
noncomputable def optCompliance : ℝ := Classical.choose G.exists_complianceFlow_max

/-- The chosen best compliance `a*` lies in `[0,1]`. No transition enters. -/
theorem optCompliance_mem : G.optCompliance ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec G.exists_complianceFlow_max).1

/-- `a*` maximises the compliance flow on `[0,1]`: `φ(a) ≤ φ(a*)` for every feasible
compliance `a`. No transition enters. -/
theorem complianceFlow_le_optCompliance {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    G.complianceFlow a ≤ G.complianceFlow G.optCompliance :=
  isMaxOn_iff.mp (Classical.choose_spec G.exists_complianceFlow_max).2 a ha

/-- The planner flow split into its sanction, compliance, curvature, placation and
state parts. Algebra; no transition enters. -/
theorem plannerW_eq_split (x a s : ℝ) :
    G.plannerW x a s = (G.g_J - G.q_K - G.d_s) * s + G.complianceFlow a
      - G.kS * s ^ 2 - G.w_pl * s * a + (G.b_J - G.b_K) * x := by
  simp only [plannerW, complianceFlow]
  ring

/-- At zero sanctions the planner flow is the state's value plus the compliance
flow. -/
theorem plannerW_zero_sanction (x a : ℝ) :
    G.plannerW x a 0 = (G.b_J - G.b_K) * x + G.complianceFlow a := by
  simp only [plannerW, complianceFlow]
  ring

/-- **The planner's feasible welfare levels from `x0`** (general in `F`). -/
def plannerFeasibleValues (F : ℝ → ℝ → ℝ) (β x0 : ℝ) : Set ℝ :=
  {v | ∃ P : PlannerPath F x0, v = G.pathValue β P.x P.a P.s}

/-- **The planner's optimal value** (general in `F`): the supremum of discounted
unit-weight welfare over all feasible paths from `x0`. No attainment is built in. -/
noncomputable def plannerOptimalValue (F : ℝ → ℝ → ℝ) (β x0 : ℝ) : ℝ :=
  sSup (G.plannerFeasibleValues F β x0)

/-- **The zero-sanction value** (general in `F`): the discounted welfare of the
path with no sanctions and the best constant compliance `a*`, from `x0`. -/
noncomputable def zeroValue (F : ℝ → ℝ → ℝ) (β x0 : ℝ) : ℝ :=
  G.pathValue β (zeroPathF F x0) (fun _ => G.optCompliance) (fun _ => 0)

/-- The zero-sanction path with the best constant compliance is feasible. -/
noncomputable def zeroPlannerPath (F : ℝ → ℝ → ℝ)
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (x0 : ℝ) (hx0 : x0 ∈ Icc (0 : ℝ) 1) : PlannerPath F x0 where
  x := zeroPathF F x0
  a := fun _ => G.optCompliance
  s := fun _ => 0
  x_zero := rfl
  x_mem := zeroPathF_mem_cube hF_mem hx0
  a_mem := fun _ => G.optCompliance_mem
  s_mem := fun _ => ⟨le_rfl, zero_le_one⟩
  step := fun _ => rfl

/-- The zero-sanction value is one of the planner's feasible welfare levels from
`x0`: it is the value of `zeroPlannerPath` (general in `F`; only cube preservation
is used). -/
theorem zeroValue_mem_plannerFeasibleValues {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (β : ℝ) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.zeroValue F β x0 ∈ G.plannerFeasibleValues F β x0 :=
  ⟨G.zeroPlannerPath F hF_mem x0 hx0, rfl⟩

/-- **The zero-sanction value in closed form** (general in `F`):
`B·Y(x0) + φ(a*)/(1 − β)`. -/
theorem zeroValue_eq {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.zeroValue F β x0
      = (G.b_J - G.b_K) * zeroStateSum F β x0
        + G.complianceFlow G.optCompliance / (1 - β) := by
  have hs1 := zeroStateSum_summable hF_mem hβ hx0
  have hs2 : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.1 hβ.2
  simp only [zeroValue, pathValue, plannerW_zero_sanction]
  calc ∑' t : ℕ, β ^ t * ((G.b_J - G.b_K) * zeroPathF F x0 t
          + G.complianceFlow G.optCompliance)
      = ∑' t : ℕ, ((G.b_J - G.b_K) * (β ^ t * zeroPathF F x0 t)
          + G.complianceFlow G.optCompliance * β ^ t) :=
        tsum_congr (fun t => by ring)
    _ = (G.b_J - G.b_K) * zeroStateSum F β x0
          + G.complianceFlow G.optCompliance * ∑' t : ℕ, β ^ t := by
        rw [(hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
        rfl
    _ = _ := by
        rw [tsum_geometric_of_lt_one hβ.1 hβ.2, div_eq_mul_inv]

/-- The zero-sanction path with zero compliance is worth `B·Y(x0)` (general in
`F`; no hypothesis, since the constant factor leaves any `tsum`). -/
theorem pathValue_zeroPathF_eq (F : ℝ → ℝ → ℝ) (β x0 : ℝ) :
    G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
      = (G.b_J - G.b_K) * zeroStateSum F β x0 := by
  have hφ0 : G.complianceFlow 0 = 0 := by simp only [complianceFlow]; ring
  simp only [pathValue, plannerW_zero_sanction, hφ0, add_zero]
  unfold zeroStateSum
  rw [← tsum_mul_left]
  exact tsum_congr (fun t => by ring)

/-! ## 4. The verification core -/

/-- **The one-step planner inequality under the political margin** (general in
`F`). With `v(x) = B·Y(x) + φ(a*)/(1 − β)`, at every feasible triple
`W(x,a,s) + β·v(F(x,s)) ≤ v(x)` whenever
`(g_J − q_K − d_s)·s + β·B·(Y(F(x,s)) − Y(F(x,0))) ≤ 0`. The rest of the slack,
`φ(a) − φ(a*) − k_S·s² − w_pl·s·a`, is nonpositive by the choice of `a*` and the
polity's own fields `kS_pos` and `w_pl_nn`. -/
theorem bellman_le_of_politicalMargin {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x a s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hPM : (G.g_J - G.q_K - G.d_s) * s
        + β * (G.b_J - G.b_K) * (zeroStateSum F β (F x s) - zeroStateSum F β (F x 0)) ≤ 0) :
    G.plannerW x a s
        + β * ((G.b_J - G.b_K) * zeroStateSum F β (F x s)
          + G.complianceFlow G.optCompliance / (1 - β))
      ≤ (G.b_J - G.b_K) * zeroStateSum F β x
        + G.complianceFlow G.optCompliance / (1 - β) := by
  have hd : (1 : ℝ) - β ≠ 0 := by linarith [hβ.2]
  have hc : β * (G.complianceFlow G.optCompliance / (1 - β))
      = G.complianceFlow G.optCompliance / (1 - β) - G.complianceFlow G.optCompliance := by
    field_simp
    ring
  have hφ := G.complianceFlow_le_optCompliance ha
  have hk := mul_nonneg G.kS_pos.le (sq_nonneg s)
  have hw := mul_nonneg (mul_nonneg G.w_pl_nn hs.1) ha.1
  rw [zeroStateSum_eq_head hF_mem hβ hx, G.plannerW_eq_split]
  nlinarith [hPM, hφ, hk, hw, hc]

/-- **Every feasible path is worth at most the zero-sanction value, under the
political margin** (general in `F`). The supersolution bound
(`DiscountedChordSum.tsum_pow_mul_le_of_le_add_mul_succ`) applied along the path,
with the cube bound `plannerWBound` and `|Y| ≤ 1/(1 − β)` for boundedness. -/
theorem pathValue_le_zeroValue_of_politicalMargin {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1)
    (hPM : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (G.g_J - G.q_K - G.d_s) * s
        + β * (G.b_J - G.b_K) * (zeroStateSum F β (F x s) - zeroStateSum F β (F x 0)) ≤ 0)
    (P : PlannerPath F x0) :
    G.pathValue β P.x P.a P.s ≤ G.zeroValue F β x0 := by
  rw [G.zeroValue_eq hF_mem hβ hx0]
  have hd : 0 < 1 - β := by linarith [hβ.2]
  have hWB : 0 ≤ G.plannerWBound := by unfold plannerWBound; positivity
  have hR : 0 ≤ (|G.b_J - G.b_K| + |G.complianceFlow G.optCompliance|) / (1 - β) := by
    positivity
  have hV : ∀ t, |(G.b_J - G.b_K) * zeroStateSum F β (P.x t)
      + G.complianceFlow G.optCompliance / (1 - β)|
      ≤ G.plannerWBound + (|G.b_J - G.b_K| + |G.complianceFlow G.optCompliance|) / (1 - β) := by
    intro t
    have hY := abs_zeroStateSum_le hF_mem hβ (P.x_mem t)
    have h1 : |(G.b_J - G.b_K) * zeroStateSum F β (P.x t)| ≤ |G.b_J - G.b_K| / (1 - β) := by
      rw [abs_mul]
      calc |G.b_J - G.b_K| * |zeroStateSum F β (P.x t)|
          ≤ |G.b_J - G.b_K| * (1 / (1 - β)) := mul_le_mul_of_nonneg_left hY (abs_nonneg _)
        _ = |G.b_J - G.b_K| / (1 - β) := by ring
    have h2 : |G.complianceFlow G.optCompliance / (1 - β)|
        = |G.complianceFlow G.optCompliance| / (1 - β) := by rw [abs_div, abs_of_pos hd]
    have h3 := abs_add_le ((G.b_J - G.b_K) * zeroStateSum F β (P.x t))
      (G.complianceFlow G.optCompliance / (1 - β))
    have h4 : (|G.b_J - G.b_K| + |G.complianceFlow G.optCompliance|) / (1 - β)
        = |G.b_J - G.b_K| / (1 - β) + |G.complianceFlow G.optCompliance| / (1 - β) :=
      add_div _ _ _
    linarith
  have hu : ∀ t, |G.plannerW (P.x t) (P.a t) (P.s t)|
      ≤ G.plannerWBound + (|G.b_J - G.b_K| + |G.complianceFlow G.optCompliance|) / (1 - β) := by
    intro t
    have h1 := G.plannerW_abs_le_cube (P.x_mem t) (P.a_mem t) (P.s_mem t)
    linarith
  have hstep : ∀ t, G.plannerW (P.x t) (P.a t) (P.s t)
      + β * ((G.b_J - G.b_K) * zeroStateSum F β (P.x (t + 1))
        + G.complianceFlow G.optCompliance / (1 - β))
      ≤ (G.b_J - G.b_K) * zeroStateSum F β (P.x t)
        + G.complianceFlow G.optCompliance / (1 - β) := by
    intro t
    rw [P.step t]
    exact G.bellman_le_of_politicalMargin hF_mem hβ (P.x_mem t) (P.a_mem t) (P.s_mem t)
      (hPM _ (P.x_mem t) _ (P.s_mem t))
  have key := tsum_pow_mul_le_of_le_add_mul_succ hβ.1 hβ.2
    (V := fun t => (G.b_J - G.b_K) * zeroStateSum F β (P.x t)
      + G.complianceFlow G.optCompliance / (1 - β))
    (u := fun t => G.plannerW (P.x t) (P.a t) (P.s t)) hV hu hstep
  simp only [P.x_zero] at key
  exact key

/-- **The planner's optimum under the political margin** (general in `F`): the
supremum of discounted welfare over feasible paths equals the zero-sanction value,
which the zero-sanction path with the best constant compliance attains. The
verification core of the three corollaries below, each of which discharges the
margin from its own (user-approved) hypotheses. -/
theorem plannerOptimalValue_eq_of_politicalMargin {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1)
    (hPM : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (G.g_J - G.q_K - G.d_s) * s
        + β * (G.b_J - G.b_K) * (zeroStateSum F β (F x s) - zeroStateSum F β (F x 0)) ≤ 0) :
    G.plannerOptimalValue F β x0 = G.zeroValue F β x0 := by
  have hmem := G.zeroValue_mem_plannerFeasibleValues hF_mem β hx0
  have hub : ∀ v ∈ G.plannerFeasibleValues F β x0, v ≤ G.zeroValue F β x0 := by
    rintro v ⟨P, rfl⟩
    exact G.pathValue_le_zeroValue_of_politicalMargin hF_mem hβ hx0 hPM P
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

/-! ## 5. The margin in the two signs of `B`, and the affine case -/

open Sanctions.TransitionChords in
/-- **The planner's optimum for a nonnegative state valuation** (BI.2; general in
`F`). For any transition that keeps the cube and is monotone in both arguments,
with a sanction upper chord `L` (`F(x,s₂) − F(x,s₁) ≤ L·(s₂ − s₁)`) and an upper
state chord `λ` on the zero-sanction section (`F(y₂,0) − F(y₁,0) ≤ λ·(y₂ − y₁)`)
with `β·λ < 1`, and for `B = b_J − b_K ≥ 0`, the margin
`g_J − q_K + β·B·L/(1 − β·λ) ≤ d_s` makes the zero-sanction path (with the best
constant compliance) planner-optimal: `plannerOptimalValue = zeroValue`.

In words: a unit of sanction buys the hawks net of the trade-dependents
`g_J − q_K` and raises the state by at most `L`, which the planner values at most
`β·B/(1 − β·λ)` per unit from next period on; if both together do not cover the
direct sanction cost `d_s`, the planner never sanctions. The chord pair and
`β·λ < 1` are the user-approved hypotheses of BI.2, on this new theorem only;
`λ ≥ 0` is derived (`zeroBand_nonneg`), not assumed. -/
theorem plannerOptimalValue_eq_of_upperChords {F : ℝ → ℝ → ℝ} {L lam : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hL : SanctionUpperChord F L)
    (hband : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      F y₂ 0 - F y₁ 0 ≤ lam * (y₂ - y₁))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) (hβlam : β * lam < 1)
    (hB : 0 ≤ G.b_J - G.b_K)
    (hmargin : G.g_J - G.q_K + β * (G.b_J - G.b_K) * L / (1 - β * lam) ≤ G.d_s)
    {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.plannerOptimalValue F β x0 = G.zeroValue F β x0 := by
  refine G.plannerOptimalValue_eq_of_politicalMargin hF_mem hβ hx0 (fun x hx s hs => ?_)
  have hd : 0 < 1 - β * lam := by linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hFs : F x 0 ≤ F x s := hF_mono_s x hs.1
  have hY := zeroStateSum_sub_le hF_mem hF_mono_x hband hβ hβlam (hF_mem _ _ hx h0)
    (hF_mem _ _ hx hs) hFs
  have hc : F x s - F x 0 ≤ L * (s - 0) := hL hx h0 hs hs.1
  have hβB : 0 ≤ β * (G.b_J - G.b_K) := mul_nonneg hβ.1 hB
  have h1 : β * (G.b_J - G.b_K) * (zeroStateSum F β (F x s) - zeroStateSum F β (F x 0))
      ≤ β * (G.b_J - G.b_K) * ((F x s - F x 0) / (1 - β * lam)) :=
    mul_le_mul_of_nonneg_left hY hβB
  have h2 : (F x s - F x 0) / (1 - β * lam) ≤ L * s / (1 - β * lam) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have h3 : β * (G.b_J - G.b_K) * ((F x s - F x 0) / (1 - β * lam))
      ≤ β * (G.b_J - G.b_K) * (L * s / (1 - β * lam)) :=
    mul_le_mul_of_nonneg_left h2 hβB
  have h4 : (G.g_J - G.q_K - G.d_s) * s + β * (G.b_J - G.b_K) * (L * s / (1 - β * lam))
      = s * (G.g_J - G.q_K + β * (G.b_J - G.b_K) * L / (1 - β * lam) - G.d_s) := by ring
  have h5 : s * (G.g_J - G.q_K + β * (G.b_J - G.b_K) * L / (1 - β * lam) - G.d_s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs.1 (by linarith)
  linarith

/-- **The planner's optimum for a nonpositive state valuation** (BI.2; general in
`F`). For any transition that keeps the cube and is monotone in both arguments,
and for `B = b_J − b_K ≤ 0`, the margin `g_J − q_K ≤ d_s` alone makes the
zero-sanction path planner-optimal. A sanction raises the state (monotonicity in
the sanction), which a planner with `B ≤ 0` does not value; so only the stage
sanction terms matter, and no chord on `F` is needed. -/
theorem plannerOptimalValue_eq_of_nonpos {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) (hB : G.b_J - G.b_K ≤ 0)
    (hmargin : G.g_J - G.q_K ≤ G.d_s) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.plannerOptimalValue F β x0 = G.zeroValue F β x0 := by
  refine G.plannerOptimalValue_eq_of_politicalMargin hF_mem hβ hx0 (fun x hx s hs => ?_)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hY := zeroStateSum_mono hF_mem hF_mono_x hβ (hF_mem _ _ hx h0) (hF_mem _ _ hx hs)
    (hF_mono_s x hs.1)
  have h1 : β * (G.b_J - G.b_K) * (zeroStateSum F β (F x s) - zeroStateSum F β (F x 0)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ.1 hB) (by linarith)
  have h2 : (G.g_J - G.q_K - G.d_s) * s ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hs.1
  linarith

/-- **The planner's optimum under the affine law, either sign of `B`**
(affine-restricted, Rule 22; BI.2). Under `F = affineF δ` the political term is
computed exactly (`zeroStateSum_affineF`), and the margin
`g_J − q_K + β·δ·B/(1 − β(1 − δ)) ≤ d_s` makes the zero-sanction path
planner-optimal for every sign of `B = b_J − b_K`, with optimal value
`B·x0/(1 − β(1 − δ)) + φ(a*)/(1 − β)`. At `fourGroupCert` (`δ = 1/2`, `B = 1`,
`g_J = q_K`, `φ ≡ 0`) this is `x0/(1 − β/2)`, the certificate optimum
(`Examples.fgcPlannerOptimalValue_eq`). -/
theorem plannerOptimalValue_eq_affineF {δ β : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hβ : β ∈ Ico (0 : ℝ) 1)
    (hmargin : G.g_J - G.q_K + β * δ * (G.b_J - G.b_K) / (1 - β * (1 - δ)) ≤ G.d_s)
    {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.plannerOptimalValue (AbstractGame.affineF δ) β x0
      = (G.b_J - G.b_K) * x0 / (1 - β * (1 - δ))
        + G.complianceFlow G.optCompliance / (1 - β) := by
  have hF_mem := AbstractGame.affineF_mem hδ
  rw [G.plannerOptimalValue_eq_of_politicalMargin hF_mem hβ hx0 (fun x _ s hs => ?_),
    G.zeroValue_eq hF_mem hβ hx0, zeroStateSum_affineF hδ hβ]
  · ring
  rw [zeroStateSum_affineF hδ hβ, zeroStateSum_affineF hδ hβ]
  have hγ1 : β * (1 - δ) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hβ.1 (by linarith [hδ.1])) hβ.2
  have hd : (1 : ℝ) - β * (1 - δ) ≠ 0 := by linarith
  have h4 : (G.g_J - G.q_K - G.d_s) * s
      + β * (G.b_J - G.b_K) * (AbstractGame.affineF δ x s / (1 - β * (1 - δ))
        - AbstractGame.affineF δ x 0 / (1 - β * (1 - δ)))
      = s * (G.g_J - G.q_K + β * δ * (G.b_J - G.b_K) / (1 - β * (1 - δ)) - G.d_s) := by
    simp only [AbstractGame.affineF]
    field_simp
    ring
  rw [h4]
  exact mul_nonpos_of_nonneg_of_nonpos hs.1 (by linarith)

/-! ## 6. The planner's loss against the persistent corner path -/

/-- **Zero-sanction value minus corner value** (general in `F`): the accounting
identity `pathValue_cornerF_gap` plus the capitalised best compliance flow,
`H/(1 − β) + B·Σ_t β^t z_t + φ(a*)/(1 − β)`. -/
theorem zeroValue_sub_cornerValue {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.zeroValue F β x0 - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t
        + G.complianceFlow G.optCompliance / (1 - β) := by
  have hgap := G.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0
  rw [G.pathValue_zeroPathF_eq F β x0] at hgap
  rw [G.zeroValue_eq hF_mem hβ hx0]
  linarith

open Sanctions.TransitionChords in
/-- **The planner's exact loss, nonnegative state valuation** (BI.2; general in
`F`): under the hypotheses of `plannerOptimalValue_eq_of_upperChords`, the
planner's optimum exceeds the value of the persistent corner path (full sanctions
against full defiance) by `H/(1 − β) + B·Σ_t β^t z_t + φ(a*)/(1 − β)`. -/
theorem plannerOptimalValue_loss_of_upperChords {F : ℝ → ℝ → ℝ} {L lam : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hL : SanctionUpperChord F L)
    (hband : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      F y₂ 0 - F y₁ 0 ≤ lam * (y₂ - y₁))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) (hβlam : β * lam < 1)
    (hB : 0 ≤ G.b_J - G.b_K)
    (hmargin : G.g_J - G.q_K + β * (G.b_J - G.b_K) * L / (1 - β * lam) ≤ G.d_s)
    {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.plannerOptimalValue F β x0
        - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t
        + G.complianceFlow G.optCompliance / (1 - β) := by
  rw [G.plannerOptimalValue_eq_of_upperChords hF_mem hF_mono_x hF_mono_s hL hband hβ hβlam hB
    hmargin hx0]
  exact G.zeroValue_sub_cornerValue hF_mem hF_mono_x hF_mono_s hβ hx0

/-- **The planner's exact loss, nonpositive state valuation** (BI.2; general in
`F`): under the hypotheses of `plannerOptimalValue_eq_of_nonpos`, the same
identity. -/
theorem plannerOptimalValue_loss_of_nonpos {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) (hB : G.b_J - G.b_K ≤ 0)
    (hmargin : G.g_J - G.q_K ≤ G.d_s) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.plannerOptimalValue F β x0
        - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t
        + G.complianceFlow G.optCompliance / (1 - β) := by
  rw [G.plannerOptimalValue_eq_of_nonpos hF_mem hF_mono_x hF_mono_s hβ hB hmargin hx0]
  exact G.zeroValue_sub_cornerValue hF_mem hF_mono_x hF_mono_s hβ hx0

/-- **The planner's exact loss under the affine law, either sign of `B`**
(affine-restricted, Rule 22; BI.2): under the margin of
`plannerOptimalValue_eq_affineF`, the planner's optimum exceeds the value of the
persistent corner path by `H/(1 − β) + B/(1 − β(1 − δ)) + φ(a*)/(1 − β)`. At
`fourGroupCert` this is `23/(10(1 − β)) + 1/(1 − β/2)`. -/
theorem plannerOptimalValue_loss_affineF {δ β : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hβ : β ∈ Ico (0 : ℝ) 1)
    (hmargin : G.g_J - G.q_K + β * δ * (G.b_J - G.b_K) / (1 - β * (1 - δ)) ≤ G.d_s)
    {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    G.plannerOptimalValue (AbstractGame.affineF δ) β x0
        - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * (1 - δ))
        + G.complianceFlow G.optCompliance / (1 - β) := by
  have hgap := G.pathValue_affineCorner_gap hδ hβ x0
  have hzero := G.pathValue_zeroPathF_eq (AbstractGame.affineF δ) β x0
  rw [zeroPathF_affineF, zeroStateSum_affineF hδ hβ] at hzero
  rw [hzero] at hgap
  rw [G.plannerOptimalValue_eq_affineF hδ hβ hmargin hx0]
  have hγ1 : β * (1 - δ) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hβ.1 (by linarith [hδ.1])) hβ.2
  have hd : (1 : ℝ) - β * (1 - δ) ≠ 0 := by linarith
  have e : (G.b_J - G.b_K) * (x0 / (1 - β * (1 - δ)))
      = (G.b_J - G.b_K) * x0 / (1 - β * (1 - δ)) := by ring
  rw [e] at hgap
  linarith

end FourGroup

end KaempferLowenberg
end Sanctions

#print axioms Sanctions.KaempferLowenberg.zeroStateSum_sub_le
#print axioms Sanctions.KaempferLowenberg.zeroStateSum_affineF
#print axioms Sanctions.KaempferLowenberg.FourGroup.exists_complianceFlow_max
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_politicalMargin
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_upperChords
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_of_nonpos
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_eq_affineF
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_loss_of_upperChords
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_loss_of_nonpos
#print axioms Sanctions.KaempferLowenberg.FourGroup.plannerOptimalValue_loss_affineF
