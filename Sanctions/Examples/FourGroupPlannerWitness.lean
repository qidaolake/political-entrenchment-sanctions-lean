/-
Sanctions/Examples/FourGroupPlannerWitness.lean

**P2 welfare layer at the microfounded four-group witness: the certified
sanctions lock-in is strictly planner-inefficient, with exact margins.**

The utilitarian planner objective (`FourGroup.plannerW`, user-approved
definition 2026-07-11) evaluates at the witness to

  W(x,a,s) = x − (14/5)s − ½s² − (11/5)s·a.

Equilibrium benchmark (Rule 1): the certified corner play of
`fourGroupCertCertificate` — sanctions maxed `σ_dyn(·,0) = 1`
(`fgc_σ_dyn_zero_eq_one`) against the derived full-defiance leader policy
`α_on ≡ 0` (`fgc_α_on_eq_zero`), both pinned at EVERY physical state — so
the equilibrium state path is `x_{t+1} = (x_t+1)/2`, i.e.
`eqPath x0 t = 1 − (1−x0)·(1/2)^t → 1` (lock-in). The planner comparison
path shuts sanctions off (`s ≡ 0`, `a ≡ 0`): `altPath x0 t = x0·(1/2)^t → 0`.
The comparison policy is *feasible*, not an equilibrium — an inefficiency
theorem does not require the planner's alternative to be equilibrium play.

Exact margins (all identities, no estimates):
  * per period: W(altPath,0,0) − W(eqPath,0,1) = 23/10 + (1/2)^t (x0 cancels);
  * lock-in flow value: W(1,0,1) = −23/10 — the absorbing state is worth +1
    but sustaining it burns d_s + kS = 33/10 of resources per period;
  * discounted, uniform over ALL starts x0 ∈ [0,1] and ALL β ∈ [0,1):
    V_alt − V_eq = 23/(10(1−β)) + 1/(1−β/2) > 0
    ( = 89/15 at β = β_S = 1/2, = 273/11 at β = β_T = 9/10 — Rule 16(a)
    ordered endpoints).

P2a fixed-point pinning: the documented affine closed forms are upgraded
from "orientation only" to EXACT Bellman fixed points: T_S(V_S*) = V_S* and
T_T(V_T*) = V_T* under the certified corner policies, at `fourGroupCert`
(V_S* = 11/3 + (4/3)x, V_T* = 52/11 + (80/11)x) and at `eeCert`
(V_S* = (16x+17)/3, V_T* = (82x+39)/11) — via the existing kernel-checked
Bellman image lemmas plus affine algebra.
-/

import Sanctions.Examples.FourGroupCertWitness
import Sanctions.Examples.EECertWitness
import Sanctions.Theory.Microfoundations.FourGroupPlanner
import Sanctions.Theory.Microfoundations.FourGroupPlannerOptimum
import Sanctions.Foundations.InfiniteHorizonVerification
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params
open KaempferLowenberg

noncomputable section

/-! ## 1. The planner objective at the witness -/

/-- **Planner objective at the microfounded witness, closed form**:
`W(x,a,s) = x − (14/5)s − ½s² − (11/5)s·a`. The political state is worth
`x` to the planner (net target-group value `b_J − b_K = 1`), the sender
groups' sanction benefits net out (`g_J − q_K = 0`), and sanctions burn
resources: cost `d_s = 14/5`, deadweight `kS·s² = s²/2`, placation
transfer `w_pl·s·a = (11/5)s·a`. Every coefficient is an existing
`fourGroupCert` field. -/
@[simp] theorem fgcW (x a s : ℝ) :
    fourGroupCert.plannerW x a s
      = x - 14/5 * s - 1/2 * s ^ 2 - 11/5 * s * a := by
  simp only [FourGroup.plannerW, fourGroupCert]
  ring

/-! ## 2. The two state paths and their transition laws -/

/-- **Equilibrium lock-in state path** from start `x0`:
`eqPath x0 t = 1 − (1−x0)·(1/2)^t`, the orbit of `x ↦ F(x,1) = (x+1)/2`
— the transition under the CERTIFIED corner play (sanctions maxed against
full defiance). Converges upward to the lock-in state `1`. -/
def eqPath (x0 : ℝ) (t : ℕ) : ℝ := 1 - (1 - x0) * (1/2) ^ t

/-- **Planner comparison state path** from start `x0`:
`altPath x0 t = x0·(1/2)^t`, the orbit of `x ↦ F(x,0) = x/2` (sanctions
shut off). Converges downward to `0`. This is a *feasible* policy, not an
equilibrium — an inefficiency theorem needs a feasible dominating
alternative, not an equilibrium one (the equilibrium side is Rule-1
certified; the planner side is the counterfactual). -/
def altPath (x0 : ℝ) (t : ℕ) : ℝ := x0 * (1/2) ^ t

@[simp] theorem eqPath_zero (x0 : ℝ) : eqPath x0 0 = x0 := by
  simp [eqPath]

@[simp] theorem altPath_zero (x0 : ℝ) : altPath x0 0 = x0 := by
  simp [altPath]

/-- Kinematic transition law of the equilibrium path: one step is the
transition at the sanction corner `s = 1`. -/
theorem eqPath_step (x0 : ℝ) (t : ℕ) :
    eqPath x0 (t + 1) = fgcParams.F (eqPath x0 t) 1 := by
  rw [fgcParams_F]
  simp only [eqPath]
  ring

/-- Kinematic transition law of the comparison path: one step is the
transition at zero sanctions. -/
theorem altPath_step (x0 : ℝ) (t : ℕ) :
    altPath x0 (t + 1) = fgcParams.F (altPath x0 t) 0 := by
  rw [fgcParams_F]
  simp only [altPath]
  ring

/-- The equilibrium path stays in the physical state cube `[0,1]`. -/
theorem eqPath_mem_cube {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    eqPath x0 t ∈ Set.Icc (0 : ℝ) 1 := by
  have hp0 : (0 : ℝ) ≤ (1/2 : ℝ) ^ t := by positivity
  have hp1 : ((1 : ℝ)/2) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 : (1 - x0) * (1/2 : ℝ) ^ t ≤ 1 :=
    mul_le_one₀ (by linarith [hx0.1]) hp0 hp1
  have h0 : 0 ≤ (1 - x0) * (1/2 : ℝ) ^ t :=
    mul_nonneg (by linarith [hx0.2]) hp0
  exact ⟨by simp only [eqPath]; linarith, by simp only [eqPath]; linarith⟩

/-- The comparison path stays in the physical state cube `[0,1]`. -/
theorem altPath_mem_cube {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    altPath x0 t ∈ Set.Icc (0 : ℝ) 1 := by
  have hp0 : (0 : ℝ) ≤ (1/2 : ℝ) ^ t := by positivity
  have hp1 : ((1 : ℝ)/2) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 : x0 * (1/2 : ℝ) ^ t ≤ 1 := mul_le_one₀ hx0.2 hp0 hp1
  have h0 : 0 ≤ x0 * (1/2 : ℝ) ^ t := mul_nonneg hx0.1 hp0
  exact ⟨by simp only [altPath]; linarith, by simp only [altPath]; linarith⟩

/-- **Basin membership**: from a basin start `x0 ∈ [1/10, 1]` the whole
equilibrium orbit stays in the certified high basin `[1/10, 1]` (the path
is increasing toward `1`), so the certificate's derived corner policies
remain the equilibrium actions along the entire orbit. -/
theorem eqPath_mem_basin {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (1 / 10 : ℝ) 1) (t : ℕ) :
    eqPath x0 t ∈ Set.Icc (1 / 10 : ℝ) 1 := by
  have hp0 : (0 : ℝ) ≤ (1/2 : ℝ) ^ t := by positivity
  have hp1 : ((1 : ℝ)/2) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hle : (1 - x0) * (1/2 : ℝ) ^ t ≤ 9/10 * 1 :=
    mul_le_mul (by linarith [hx0.1]) hp1 hp0 (by norm_num)
  have h0 : 0 ≤ (1 - x0) * (1/2 : ℝ) ^ t :=
    mul_nonneg (by linarith [hx0.2]) hp0
  exact ⟨by simp only [eqPath]; linarith, by simp only [eqPath]; linarith⟩

/-- **Rule-1 tie to the certificate**: one step of the equilibrium path IS
the transition under the certified equilibrium play — the derived leader
policy `α_on ≡ 0` (full defiance, `fgc_α_on_eq_zero`) and the derived
Sender corner `σ_dyn(·,0) = 1` (`fgc_σ_dyn_zero_eq_one`) — for every
carrier pair. The equilibrium side of the planner comparison is therefore
fully optimization-derived, not hand-imposed. -/
theorem eqPath_step_certified (V_T : fgcClass.CarrierT)
    (V_S : fgcClass.CarrierS) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    eqPath x0 (t + 1)
      = fgcParams.F (eqPath x0 t)
          (fgcParams.σ_dyn V_S.val (eqPath x0 t)
            (fgcClass.α_on V_T V_S (eqPath x0 t))) := by
  simp only [fgc_α_on_eq_zero V_T V_S]
  rw [fgc_σ_dyn_zero_eq_one V_S.property (eqPath_mem_cube hx0 t)]
  exact eqPath_step x0 t

/-! ## 3. Per-period gap and stationary planner facts -/

/-- **Per-period planner gap, exact**: at every period the planner's flow
welfare on the zero-sanctions path exceeds the flow welfare on the
certified lock-in path by exactly `23/10 + (1/2)^t` — the start `x0`
cancels. The planner gains `23/10` every period forever by abandoning the
sanctions war, plus a vanishing transition bonus. -/
theorem fgc_perPeriod_gap (x0 : ℝ) (t : ℕ) :
    fourGroupCert.plannerW (altPath x0 t) 0 0
      - fourGroupCert.plannerW (eqPath x0 t) 0 1
      = 23/10 + (1/2) ^ t := by
  simp only [fgcW, altPath, eqPath]
  ring

/-- **Lock-in flow value**: at the equilibrium's absorbing state
`(x,a,s) = (1,0,1)`, planner welfare is exactly `−23/10` per period — the
maximal political state is worth `+1`, but sustaining it burns
`d_s + kS = 14/5 + 1/2 = 33/10` in sanction resource costs. -/
theorem fgc_planner_lockin_val :
    fourGroupCert.plannerW 1 0 1 = -(23/10) := by
  simp only [fgcW]
  norm_num

/-- **Stationary planner optimum**: among stationary points of the
transition (`x = F(x,s)` iff `x = s` under the affine law), the planner
weakly prefers the zero point `(0,0,0)` to every feasible stationary
`(s,a,s)`: `W(s,a,s) = −(9/5)s − ½s² − (11/5)s·a ≤ 0 = W(0,0,0)`. -/
theorem fgc_planner_stationary_le {s a : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    fourGroupCert.plannerW s a s ≤ fourGroupCert.plannerW 0 0 0 := by
  simp only [fgcW]
  nlinarith [hs.1, sq_nonneg s, mul_nonneg hs.1 ha.1]

/-- **Strict stationary dominance for any positive sanction level**: every
stationary point with `s > 0` is strictly planner-worse than `(0,0,0)`. Every
zero-sanction stationary triple `(0,a,0)` ties at `0`, so what is pinned is
that *sanctioning* at a stationary point destroys planner value, not that the
origin is the unique maximiser (wording corrected 2026-09-15, the reader's
09-11 package S3; the appendix already said so). -/
theorem fgc_planner_stationary_lt {s a : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hs0 : 0 < s) :
    fourGroupCert.plannerW s a s < fourGroupCert.plannerW 0 0 0 := by
  simp only [fgcW]
  nlinarith [hs0, sq_nonneg s, mul_nonneg hs.1 ha.1]

/-- **Witness instantiation of the parametric flip boundary** (Rule 5:
one-line corollary of `FourGroup.plannerW_lockin_dominated_iff`): at the
four-group witness the planner's linear flow gain from the lock-in corner
is `(g_J − q_K) + (b_J − b_K) = 1`, strictly below the per-period resource
burn `kS + d_s = 33/10` — comfortable slack, so the lock-in is
planner-dominated by the zero stationary point. -/
theorem fgc_lockin_dominated :
    fourGroupCert.plannerW 1 0 1 < fourGroupCert.plannerW 0 0 0 :=
  fourGroupCert.plannerW_lockin_dominated_iff.mpr
    (by simp only [fourGroupCert]; norm_num)

/-! ## 4. The discounted layer -/

/-- **Discounted planner value of a path triple** `(x_t, a_t, s_t)` under
discount `β`: `Σ_t β^t · plannerW(x_t, a_t, s_t)` (a `tsum`; the theorems
below establish summability wherever it is consumed). Parametric over the
four-group economy `G` (Rule 5). -/
def plannerValue (G : FourGroup) (β : ℝ) (xp ap sp : ℕ → ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * G.plannerW (xp t) (ap t) (sp t)

/-- **Uniform bound on the witness planner objective over the cube**:
`|plannerW| ≤ 13/2` on `[0,1]³` (true sup `11/2`; the slack constant is
what the summability comparison consumes). -/
theorem fgc_plannerW_abs_le {x a s : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |fourGroupCert.plannerW x a s| ≤ 13/2 := by
  rw [fgcW, abs_le]
  have hsa : s * a ≤ 1 := mul_le_one₀ hs.2 ha.1 ha.2
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
  have hsa0 : 0 ≤ s * a := mul_nonneg hs.1 ha.1
  constructor
  · nlinarith [hx.1, hs.2, hsa, hs2]
  · nlinarith [hx.2, hs.1, hsa0, sq_nonneg s]

/-- **Well-definedness of the discounted planner value**: along any path
triple that stays in the cube, the defining series is summable — geometric
comparison via the uniform bound `|plannerW| ≤ 13/2`. -/
theorem fgc_plannerValue_summable {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1)
    {xp ap sp : ℕ → ℝ} (hxp : ∀ t, xp t ∈ Set.Icc (0 : ℝ) 1)
    (hap : ∀ t, ap t ∈ Set.Icc (0 : ℝ) 1)
    (hsp : ∀ t, sp t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun t : ℕ =>
      β ^ t * fourGroupCert.plannerW (xp t) (ap t) (sp t)) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => 13/2 * β ^ t)
    ((summable_geometric_of_lt_one hb.1 hb.2).mul_left _) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hb.1]
  have hW := fgc_plannerW_abs_le (hxp t) (hap t) (hsp t)
  have hpow : (0 : ℝ) ≤ β ^ t := pow_nonneg hb.1 t
  nlinarith [mul_le_mul_of_nonneg_left hW hpow]

/-- **Discounted equilibrium planner value, closed form**: along the
certified lock-in path (sanctions maxed, full defiance),
`V_eq(x0;β) = −23/(10(1−β)) − (1−x0)/(1−β/2)` — exactly, for every start
and every `β ∈ [0,1)`. -/
theorem fgc_plannerValue_eqPath (x0 : ℝ) {β : ℝ}
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0) (fun _ => 0) (fun _ => 1)
      = -(23/(10 * (1 - β))) - (1 - x0)/(1 - β/2) := by
  have hb0 : (0 : ℝ) ≤ β := hb.1
  have hb1 : β < 1 := hb.2
  have hb20 : (0 : ℝ) ≤ β/2 := by linarith
  have hb21 : β/2 < 1 := by linarith
  have hg1 : Summable (fun t : ℕ => β ^ t) :=
    summable_geometric_of_lt_one hb0 hb1
  have hg2 : Summable (fun t : ℕ => (β/2) ^ t) :=
    summable_geometric_of_lt_one hb20 hb21
  have hterm : ∀ t : ℕ,
      β ^ t * fourGroupCert.plannerW (eqPath x0 t) 0 1
        = -(23/10) * β ^ t - (1 - x0) * (β/2) ^ t := by
    intro t
    simp only [fgcW, eqPath]
    ring
  simp only [plannerValue]
  rw [tsum_congr hterm,
      (hg1.mul_left (-(23/10))).tsum_sub (hg2.mul_left (1 - x0)),
      tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one hb0 hb1, tsum_geometric_of_lt_one hb20 hb21]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have h2 : (1 : ℝ) - β/2 ≠ 0 := by linarith
  field_simp

/-- **Discounted comparison planner value, closed form**: along the
zero-sanctions path, `V_alt(x0;β) = x0/(1−β/2)` — the planner collects the
decaying political state and burns nothing. -/
theorem fgc_plannerValue_altPath (x0 : ℝ) {β : ℝ}
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0)
      = x0/(1 - β/2) := by
  have hb20 : (0 : ℝ) ≤ β/2 := by linarith [hb.1]
  have hb21 : β/2 < 1 := by linarith [hb.2]
  have hterm : ∀ t : ℕ,
      β ^ t * fourGroupCert.plannerW (altPath x0 t) 0 0
        = x0 * (β/2) ^ t := by
    intro t
    simp only [fgcW, altPath]
    ring
  simp only [plannerValue]
  calc ∑' t : ℕ, β ^ t * fourGroupCert.plannerW (altPath x0 t) 0 0
      = ∑' t : ℕ, x0 * (β/2) ^ t := tsum_congr hterm
    _ = x0 * (1 - β/2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hb20 hb21]
    _ = x0 / (1 - β/2) := (div_eq_mul_inv x0 (1 - β/2)).symm

/-! ## 5. THE HEADLINE: strict planner inefficiency of the certified
lock-in, exact discounted margin -/

/-- **Planner inefficiency of the certified sanctions lock-in — exact
identity form.** For every feasible start `x0 ∈ [0,1]` and every discount
`β ∈ [0,1)`, the discounted planner value of the certified equilibrium
lock-in path falls short of the feasible zero-sanctions alternative by
EXACTLY

  `23/(10(1−β)) + 1/(1−β/2)`

— the capitalized per-period stationary margin plus the capitalized
transition bonus, uniform over all starts (the `x0`-dependence cancels).
The equilibrium side is the Rule-1 certified corner play of
`fourGroupCertCertificate`; the comparison side is a feasible planner
policy (not an equilibrium — none is required for an inefficiency claim).
The start hypothesis scopes the claim to physically feasible starts. -/
theorem fgc_planner_inefficiency {x0 : ℝ} (_hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0) (fun _ => 0) (fun _ => 1)
        + 23/(10 * (1 - β)) + 1/(1 - β/2)
      = plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0) := by
  rw [fgc_plannerValue_eqPath x0 hb, fgc_plannerValue_altPath x0 hb]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith [hb.2]
  have h2 : (1 : ℝ) - β/2 ≠ 0 := by linarith [hb.2]
  field_simp
  ring

/-- **Strict-inequality corollary**: the certified lock-in is strictly
planner-dominated — the discounted planner value of the equilibrium path
is strictly below the zero-sanctions alternative, for every feasible start
and every `β ∈ [0,1)` (the margin `23/(10(1−β)) + 1/(1−β/2)` is positive). -/
theorem fgc_planner_inefficiency_lt {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0) (fun _ => 0) (fun _ => 1)
      < plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0) := by
  have h := fgc_planner_inefficiency hx0 hb
  have hm1 : (0 : ℝ) < 23/(10 * (1 - β)) :=
    div_pos (by norm_num) (by nlinarith [hb.2])
  have hm2 : (0 : ℝ) < 1/(1 - β/2) :=
    div_pos (by norm_num) (by linarith [hb.2])
  linarith

/-- **Rule-16(a) endpoint, Sender discount `β_S = 1/2`**: the exact
discounted planner margin at the witness Sender's own discount factor is
`89/15`. -/
theorem fgc_planner_inefficiency_βS {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    plannerValue fourGroupCert fgcParams.β_S (eqPath x0)
        (fun _ => 0) (fun _ => 1) + 89/15
      = plannerValue fourGroupCert fgcParams.β_S (altPath x0)
          (fun _ => 0) (fun _ => 0) := by
  have h := fgc_planner_inefficiency hx0
    (β := fgcParams.β_S) (by rw [fgcParams_β_S]; constructor <;> norm_num)
  rw [fgcParams_β_S] at h ⊢
  have hc : (23 : ℝ)/(10 * (1 - 1/2)) + 1/(1 - (1/2)/2) = 89/15 := by norm_num
  linarith

/-- **Rule-16(a) endpoint, Target discount `β_T = 9/10`**: the exact
discounted planner margin at the witness Target's own discount factor is
`273/11`. Together with the `β_S` endpoint this pins the economically
intended direction: more patience (`1/2 < 9/10`) capitalizes a strictly
larger inefficiency (`89/15 < 273/11`). -/
theorem fgc_planner_inefficiency_βT {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    plannerValue fourGroupCert fgcParams.β_T (eqPath x0)
        (fun _ => 0) (fun _ => 1) + 273/11
      = plannerValue fourGroupCert fgcParams.β_T (altPath x0)
          (fun _ => 0) (fun _ => 0) := by
  have h := fgc_planner_inefficiency hx0
    (β := fgcParams.β_T) (by rw [fgcParams_β_T]; constructor <;> norm_num)
  rw [fgcParams_β_T] at h ⊢
  have hc : (23 : ℝ)/(10 * (1 - 9/10)) + 1/(1 - (9/10)/2) = 273/11 := by
    norm_num
  linarith

/-- Rule 16(a): the two endpoints are provably distinct and ordered. -/
example : fgcParams.β_S < fgcParams.β_T := by
  rw [fgcParams_β_S, fgcParams_β_T]; norm_num

/-- Rule 16(a): the margins at the ordered endpoints are ordered the same
way (patience amplifies the capitalized inefficiency). -/
example : (89 : ℝ)/15 < 273/11 := by norm_num

/-! ## 6. Planner-optimum lower bound over all feasible paths -/

/-- A feasible planner path from `x0`: physical states and both actions stay
in `[0,1]`, the initial state is `x0`, and the state obeys the witness
transition under the path's sanction choice.  This is a definition of the
planner's feasible set, not an added economic assumption. -/
structure FGCPlannerPath (x0 : ℝ) where
  x : ℕ → ℝ
  a : ℕ → ℝ
  s : ℕ → ℝ
  x_zero : x 0 = x0
  x_mem : ∀ t, x t ∈ Set.Icc (0 : ℝ) 1
  a_mem : ∀ t, a t ∈ Set.Icc (0 : ℝ) 1
  s_mem : ∀ t, s t ∈ Set.Icc (0 : ℝ) 1
  step : ∀ t, x (t + 1) = fgcParams.F (x t) (s t)

/-- The zero-sanctions comparison is a feasible planner path from every
physical initial state. -/
def fgcAltPlannerPath (x0 : ℝ) (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    FGCPlannerPath x0 where
  x := altPath x0
  a := fun _ => 0
  s := fun _ => 0
  x_zero := altPath_zero x0
  x_mem := altPath_mem_cube hx0
  a_mem := fun _ => by norm_num
  s_mem := fun _ => by norm_num
  step := altPath_step x0

/-- Discounted welfare levels generated by feasible planner paths. -/
def fgcPlannerFeasibleValues (x0 β : ℝ) : Set ℝ :=
  {v | ∃ P : FGCPlannerPath x0,
    v = plannerValue fourGroupCert β P.x P.a P.s}

/-- The planner's optimal value is the supremum over feasible discounted
welfare levels.  No attainment claim is built into this definition. -/
noncomputable def fgcPlannerOptimalValue (x0 β : ℝ) : ℝ :=
  sSup (fgcPlannerFeasibleValues x0 β)

/-- Every feasible discounted value is bounded above by the capitalized
cube bound `(13/2)/(1-β)`. -/
theorem fgc_plannerValue_le_geometric {β : ℝ}
    (hb : β ∈ Set.Ico (0 : ℝ) 1) {xp ap sp : ℕ → ℝ}
    (hxp : ∀ t, xp t ∈ Set.Icc (0 : ℝ) 1)
    (hap : ∀ t, ap t ∈ Set.Icc (0 : ℝ) 1)
    (hsp : ∀ t, sp t ∈ Set.Icc (0 : ℝ) 1) :
    plannerValue fourGroupCert β xp ap sp ≤ (13 / 2) / (1 - β) := by
  have hsum := fgc_plannerValue_summable hb hxp hap hsp
  have hgeom : Summable (fun t : ℕ => (13 / 2) * β ^ t) :=
    (summable_geometric_of_lt_one hb.1 hb.2).mul_left _
  have hterm : ∀ t : ℕ,
      β ^ t * fourGroupCert.plannerW (xp t) (ap t) (sp t)
        ≤ (13 / 2) * β ^ t := by
    intro t
    have hW := fgc_plannerW_abs_le (hxp t) (hap t) (hsp t)
    have hp : (0 : ℝ) ≤ β ^ t := pow_nonneg hb.1 _
    have hWupper : fourGroupCert.plannerW (xp t) (ap t) (sp t) ≤ 13 / 2 :=
      le_trans (le_abs_self _) hW
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hWupper hp
  change (∑' t : ℕ, β ^ t *
      fourGroupCert.plannerW (xp t) (ap t) (sp t)) ≤ _
  calc
    (∑' t : ℕ, β ^ t * fourGroupCert.plannerW (xp t) (ap t) (sp t))
        ≤ ∑' t : ℕ, (13 / 2) * β ^ t :=
      hsum.tsum_le_tsum hterm hgeom
    _ = (13 / 2) / (1 - β) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hb.1 hb.2]
      ring

theorem fgcPlannerFeasibleValues_bddAbove {x0 β : ℝ}
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    BddAbove (fgcPlannerFeasibleValues x0 β) := by
  refine ⟨(13 / 2) / (1 - β), ?_⟩
  intro v hv
  rcases hv with ⟨P, rfl⟩
  exact fgc_plannerValue_le_geometric hb P.x_mem P.a_mem P.s_mem

/-- The previously constructed zero-sanctions comparison belongs to the
planner's feasible-value set. -/
theorem fgcAltPlannerValue_mem {x0 β : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0)
      ∈ fgcPlannerFeasibleValues x0 β := by
  exact ⟨fgcAltPlannerPath x0 hx0, rfl⟩

theorem fgc_alt_le_plannerOptimalValue {x0 β : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0)
      ≤ fgcPlannerOptimalValue x0 β := by
  apply le_csSup (fgcPlannerFeasibleValues_bddAbove hb)
  exact fgcAltPlannerValue_mem hx0

/-- **Planner-optimum welfare lower bound.**  The feasible comparison and
the exact pathwise identity imply that the planner's supremum value exceeds
the certified equilibrium value by at least the same explicit amount
`23/(10(1-β)) + 1/(1-β/2)`.  This strengthens a comparison with one
feasible path to a lower bound on the full planner problem without claiming
that the exhibited path itself is optimal. -/
theorem fgc_plannerOptimalValue_lower_bound {x0 β : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0) (fun _ => 0) (fun _ => 1)
        + (23 / (10 * (1 - β)) + 1 / (1 - β / 2))
      ≤ fgcPlannerOptimalValue x0 β := by
  have halt := fgc_alt_le_plannerOptimalValue hx0 hb
  have hgap := fgc_planner_inefficiency hx0 hb
  linarith

theorem fgc_equilibrium_lt_plannerOptimalValue {x0 β : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0) (fun _ => 0) (fun _ => 1)
      < fgcPlannerOptimalValue x0 β := by
  have hbound := fgc_alt_le_plannerOptimalValue hx0 hb
  have hpos := fgc_planner_inefficiency_lt hx0 hb
  linarith

/-! ## 7. P2a fixed-point pinning: the affine closed forms are EXACT
Bellman fixed points

The witness files document affine value candidates "for orientation only".
Here they are upgraded: `T_S(V_S*) = V_S*` and `T_T(V_T*) = V_T*` exactly,
under the certified corner policies, at both `fourGroupCert` and `eeCert`.
The sSup collapse is done by the existing kernel-checked image lemmas
(`fgc_bellmanS_image` / `fgc_jointTarget_image` /
`eeCert_bellmanS_image` / `eeCert_jointTarget_image`); what remains is
affine algebra. -/

/-- The affine-with-intercept BCF `y ↦ b + c·y` on the compact state space
`↥S = [0,1]` (the plain `affineBCF` has no intercept; the exact Bellman
fixed points do). -/
def affineInterceptBCF (b c : ℝ) : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => b + c * y.val)
      (by fun_prop))

@[simp] theorem affineInterceptBCF_apply (b c : ℝ)
    (y : ↥(Sanctions.S : Set ℝ)) :
    affineInterceptBCF b c y = b + c * y.val := rfl

/-- `affineInterceptBCF b c ∈ valLipGainBall M c c 0` for `0 ≤ b`, `0 ≤ c`,
`b + c ≤ M`: sup-norm `≤ M` (the function is nonnegative and peaks at
`b + c`), Lipschitz constant exactly `c`, minimum upward slope exactly `c`
— i.e. the intercepted affine functions are legitimate members of the
slope-pinned carriers. -/
theorem affineInterceptBCF_mem_gainBall {b c M : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbcM : b + c ≤ M) :
    affineInterceptBCF b c ∈ valLipGainBall M c c 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le (by linarith : (0 : ℝ) ≤ M)]
    intro y
    rw [affineInterceptBCF_apply, Real.norm_eq_abs, abs_le]
    have hcy0 : 0 ≤ c * y.val := mul_nonneg hc y.property.1
    have hcy1 : c * y.val ≤ c := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr y.property.2)]
    exact ⟨by linarith, by linarith⟩
  · intro y₁ y₂
    rw [affineInterceptBCF_apply, affineInterceptBCF_apply,
        Subtype.dist_eq, Real.dist_eq,
        show b + c * y₂.val - (b + c * y₁.val) = c * (y₂.val - y₁.val)
          by ring,
        abs_mul, abs_of_nonneg hc, abs_sub_comm y₁.val y₂.val]
  · intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [affineInterceptBCF_apply, affineInterceptBCF_apply,
        Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    nlinarith [hle']

/-- The exact fgc Sender fixed value `V_S* = 11/3 + (4/3)x`. -/
def fgcVSstar : Val := affineInterceptBCF (11/3) (4/3)

/-- The exact fgc Target fixed value `V_T* = 52/11 + (80/11)x`. -/
def fgcVTstar : Val := affineInterceptBCF (52/11) (80/11)

/-- The exact eeCert Sender fixed value `V_S* = (16x+17)/3`. -/
def eeVSstar : Val := affineInterceptBCF (17/3) (16/3)

/-- The exact eeCert Target fixed value `V_T* = (82x+39)/11`. -/
def eeVTstar : Val := affineInterceptBCF (39/11) (82/11)

/-- `V_S*` lives in the fgc Sender carrier (sup `5 ≤ 8`, slope `4/3`). -/
theorem fgcVSstar_mem : fgcVSstar ∈ fgcCarrierS := by
  rw [fgcCarrierS_eq]
  exact affineInterceptBCF_mem_gainBall (by norm_num) (by norm_num) (by norm_num)

/-- `V_T*` lives in the fgc Target carrier (sup `12 ≤ 40`, slope `80/11`). -/
theorem fgcVTstar_mem : fgcVTstar ∈ fgcCarrierT := by
  rw [fgcCarrierT_eq]
  exact affineInterceptBCF_mem_gainBall (by norm_num) (by norm_num) (by norm_num)

/-- ee `V_S*` lives in the ee Sender carrier (sup `11 ≤ 12`, slope `16/3`). -/
theorem eeVSstar_mem : eeVSstar ∈ eeCarrierS := by
  rw [eeCarrierS_eq]
  exact affineInterceptBCF_mem_gainBall (by norm_num) (by norm_num) (by norm_num)

/-- ee `V_T*` lives in the ee Target carrier (sup `11 ≤ 80`, slope `82/11`). -/
theorem eeVTstar_mem : eeVTstar ∈ eeCarrierT := by
  rw [eeCarrierT_eq]
  exact affineInterceptBCF_mem_gainBall (by norm_num) (by norm_num) (by norm_num)

/-- **fgc Sender fixed point** `T_S(V_S*) = V_S*`: the Sender Bellman
operator at the derived defiance policy `α ≡ 0` (sSup collapsed at the
certified corner `s = 1` by `fgc_bellmanS_image`) fixes
`V_S* = 11/3 + (4/3)x` exactly — slope `4/3 = 1 + (1/2)(4/3)(1/2)`,
intercept `11/3 = 3/2 + 11/6 + 1/3`. Upgrades the documented closed form
from "orientation only" to an exact Bellman fixed point. -/
theorem fgc_VS_star_fixed :
    fgcParams.bellmanS_BCF (fun _ => 0) continuous_const fgcVSstar
      = fgcVSstar := by
  ext y
  rw [fgc_bellmanS_image fgcVSstar_mem y]
  have hmem : (y.val + 1)/2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [y.property.1], by nlinarith [y.property.2]⟩
  simp only [fgcVSstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- **fgc Target fixed point** `T_T(V_T*) = V_T*`: the joint Target
Bellman operator (sSup collapsed at the certified defiance corner `a = 0`,
where `σ_dyn = 1`, by `fgc_jointTarget_image`) fixes
`V_T* = 52/11 + (80/11)x` exactly — slope `80/11 = 4 + (9/10)(80/11)(1/2)`,
intercept `52/11 = −14/5 + 468/110 + 36/11`. The Sender-side carrier input
is the exact Sender fixed point `V_S*`. -/
theorem fgc_VT_star_fixed (y : ↥(Sanctions.S : Set ℝ)) :
    fgcParams.jointTarget_BCF_on_S fgcVTstar fgcVSstar
        (fgc_DAU_on_carrier fgcVSstar_mem).toOnI y
      = fgcVTstar y := by
  have h : fgcParams.jointTarget_BCF_on_S fgcVTstar fgcVSstar
        (fgc_DAU_on_carrier fgcVSstar_mem).toOnI y
      = 4 * y.val - 14/5
        + 9/10 * fgcVTstar (Sanctions.clipS' ((y.val + 1)/2)) :=
    fgc_jointTarget_image ⟨fgcVTstar, fgcVTstar_mem⟩
      ⟨fgcVSstar, fgcVSstar_mem⟩ y
  rw [h]
  have hmem : (y.val + 1)/2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [y.property.1], by nlinarith [y.property.2]⟩
  simp only [fgcVTstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- **Exact equilibrium object for the four-group certificate.** The value
pair `(fgcVTstar, fgcVSstar)` is fixed by the two Bellman operators, the
Target policy is its derived joint-objective maximizer, and the Sender uses
the upper dynamic maximizer. This bundles the separate fixed-point results
into the equilibrium object required by Rule 1. -/
noncomputable def fgcExactEquilibriumTop :
    fgcParams.FeedbackStackelbergEquilibriumTop := by
  let V_T : fgcClass.CarrierT := ⟨fgcVTstar, fgcVTstar_mem⟩
  let V_S : fgcClass.CarrierS := ⟨fgcVSstar, fgcVSstar_mem⟩
  refine {
    V_T := fgcVTstar
    V_S := fgcVSstar
    α := fgcClass.α_on V_T V_S
    hα := fgcClass.α_on_continuous V_T V_S
    α_mem := fun x _hx => fgcClass.α_on_mem V_T V_S x
    V_S_fix := ?_
    V_T_fix_top := ?_
    α_opt_top := ?_
  }
  · simpa only [fgc_α_on_eq_zero V_T V_S] using fgc_VS_star_fixed.symm
  · intro x
    have h_apply :
        fgcParams.jointTarget_BCF_on_S fgcVTstar fgcVSstar
            (fgc_DAU_on_carrier fgcVSstar_mem).toOnI x =
          sSup ((fun a => fgcParams.joint_T_integrand fgcVTstar fgcVSstar x.val a) ''
            Sanctions.I) :=
      fgcParams.jointTarget_BCF_on_S_apply fgcVTstar fgcVSstar
        (fgc_DAU_on_carrier fgcVSstar_mem).toOnI x
    have hint :
        (fun a => fgcParams.joint_T_top_integrand fgcVTstar fgcVSstar x.val a) =
          (fun a => fgcParams.joint_T_integrand fgcVTstar fgcVSstar x.val a) := by
      funext a
      exact fgcParams.joint_T_top_integrand_eq_joint_T_integrand_of_unique
        (fgc_DAU_on_carrier fgcVSstar_mem) x.property a
    rw [hint]
    calc
      fgcVTstar x =
          fgcParams.jointTarget_BCF_on_S fgcVTstar fgcVSstar
            (fgc_DAU_on_carrier fgcVSstar_mem).toOnI x :=
        (fgc_VT_star_fixed x).symm
      _ = sSup ((fun a => fgcParams.joint_T_integrand fgcVTstar fgcVSstar x.val a) ''
          Sanctions.I) := h_apply
  · intro x hx a ha
    change fgcParams.joint_T_top_integrand fgcVTstar fgcVSstar x a ≤
      fgcParams.joint_T_top_integrand fgcVTstar fgcVSstar x
        (fgcClass.α_on V_T V_S x)
    rw [fgcParams.joint_T_top_integrand_eq_joint_T_integrand_of_unique
          (fgc_DAU_on_carrier fgcVSstar_mem) hx a,
        fgcParams.joint_T_top_integrand_eq_joint_T_integrand_of_unique
          (fgc_DAU_on_carrier fgcVSstar_mem) hx (fgcClass.α_on V_T V_S x)]
    exact fgcClass.α_on_isMaxOn V_T V_S hx ha

/-- Target actions along `eqPath`, derived from the exact equilibrium value
pair rather than inserted as a literal path. -/
def fgcEquilibriumTargetPath (x0 : ℝ) (t : ℕ) : ℝ :=
  fgcExactEquilibriumTop.α (eqPath x0 t)

/-- Sender actions along `eqPath`, derived as upper dynamic maximizers at the
exact equilibrium continuation value and realized Target policy. -/
noncomputable def fgcEquilibriumSenderPath (x0 : ℝ) (t : ℕ) : ℝ :=
  fgcExactEquilibriumTop.ρ (eqPath x0 t) (fgcEquilibriumTargetPath x0 t)

@[simp] theorem fgcEquilibriumTargetPath_eq_zero (x0 : ℝ) (t : ℕ) :
    fgcEquilibriumTargetPath x0 t = 0 := by
  change fgcClass.α_on ⟨fgcVTstar, fgcVTstar_mem⟩
    ⟨fgcVSstar, fgcVSstar_mem⟩ (eqPath x0 t) = 0
  rw [fgc_α_on_eq_zero]

theorem fgcEquilibriumSenderPath_eq_one {x0 : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    fgcEquilibriumSenderPath x0 t = 1 := by
  change fgcParams.σ_dyn_top fgcVSstar (eqPath x0 t)
    (fgcEquilibriumTargetPath x0 t) = 1
  rw [fgcEquilibriumTargetPath_eq_zero]
  rw [← fgcParams.σ_dyn_eq_σ_dyn_top_of_unique fgcVSstar (eqPath x0 t) 0
    (fgc_DAU_on_carrier fgcVSstar_mem (eqPath x0 t) (eqPath_mem_cube hx0 t) 0)]
  exact fgc_σ_dyn_zero_eq_one fgcVSstar_mem (eqPath_mem_cube hx0 t)

/-- **Planner inefficiency stated on equilibrium-derived actions.** This is
the Rule-1-compliant headline form of `fgc_planner_inefficiency`: the
equilibrium side refers to `fgcExactEquilibriumTop` and its optimal Target
and Sender policies. The feasible zero-sanction planner alternative remains
a counterfactual, as permitted for an inefficiency comparison. -/
theorem fgc_planner_inefficiency_equilibrium {x0 : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0)
        (fgcEquilibriumTargetPath x0) (fgcEquilibriumSenderPath x0)
        + 23 / (10 * (1 - β)) + 1 / (1 - β / 2) =
      plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0) := by
  have hα : fgcEquilibriumTargetPath x0 = fun _ => (0 : ℝ) := by
    funext t
    exact fgcEquilibriumTargetPath_eq_zero x0 t
  have hσ : fgcEquilibriumSenderPath x0 = fun _ => (1 : ℝ) := by
    funext t
    exact fgcEquilibriumSenderPath_eq_one hx0 t
  rw [hα, hσ]
  exact fgc_planner_inefficiency hx0 hb

/-- **eeCert Sender fixed point** `T_S(V_S*) = V_S*`: the Sender Bellman
operator at the defiance policy (sSup collapsed at `s = 1` by
`eeCert_bellmanS_image`) fixes `V_S* = (16x+17)/3` exactly — slope
`16/3 = 4 + 4/3`, intercept `17/3 = 3/2 + 17/6 + 4/3`. -/
theorem eeCert_VS_star_fixed :
    eeCertParams.bellmanS_BCF (fun _ => 0) continuous_const eeVSstar
      = eeVSstar := by
  ext y
  rw [eeCert_bellmanS_image eeVSstar_mem y]
  have hmem : (y.val + 1)/2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [y.property.1], by nlinarith [y.property.2]⟩
  simp only [eeVSstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- **eeCert Target fixed point** `T_T(V_T*) = V_T*`: the joint Target
Bellman operator (sSup collapsed at the defiance corner by
`eeCert_jointTarget_image`) fixes `V_T* = (82x+39)/11` exactly — slope
`82/11 = 41/10 + 369/110`, intercept `39/11 = −3 + 72/11`. -/
theorem eeCert_VT_star_fixed (y : ↥(Sanctions.S : Set ℝ)) :
    eeCertParams.jointTarget_BCF_on_S eeVTstar eeVSstar
        (eeCert_DAU_on_carrier eeVSstar_mem).toOnI y
      = eeVTstar y := by
  have h : eeCertParams.jointTarget_BCF_on_S eeVTstar eeVSstar
        (eeCert_DAU_on_carrier eeVSstar_mem).toOnI y
      = 41/10 * y.val - 3
        + 9/10 * eeVTstar (Sanctions.clipS' ((y.val + 1)/2)) :=
    eeCert_jointTarget_image ⟨eeVTstar, eeVTstar_mem⟩
      ⟨eeVSstar, eeVSstar_mem⟩ y
  rw [h]
  have hmem : (y.val + 1)/2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [y.property.1], by nlinarith [y.property.2]⟩
  simp only [eeVTstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

end -- noncomputable section

#print axioms fgc_planner_inefficiency
#print axioms fgc_planner_inefficiency_lt
#print axioms fgc_planner_inefficiency_βS
#print axioms fgc_planner_inefficiency_βT
/-- **The planner lower bound, on equilibrium-derived paths (Rule 1).**

This is `\Cref{prop:planner-optimum-lower-bound}`'s exact content: the planner's
optimal value exceeds the value *the equilibrium actually attains* by at least
`23/(10(1−β)) + 1/(1−β/2)`.

**Why this exists alongside `fgc_plannerOptimalValue_lower_bound`.** That sibling
states the same inequality but evaluates the equilibrium side at the hand-chosen
constant paths `α ≡ 0`, `σ ≡ 1`. Numerically the two are identical, because at
this economy the equilibrium paths *are* those constants — but there the
constants are **assumed**, and here they are **derived**:
`fgcEquilibriumTargetPath_eq_zero` and `fgcEquilibriumSenderPath_eq_one` prove
the equilibrium plays them. Rule 1 is exactly this distinction — a welfare gap
computed against an assumed strategy is a statement about a dynamical system,
not about equilibrium behaviour — so the paper's proposition should cite this
form and not the sibling.

No new hypothesis: it is the sibling plus the two path identities. -/
theorem fgc_plannerOptimalValue_lower_bound_equilibrium {x0 β : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    plannerValue fourGroupCert β (eqPath x0)
        (fgcEquilibriumTargetPath x0) (fgcEquilibriumSenderPath x0)
        + (23 / (10 * (1 - β)) + 1 / (1 - β / 2))
      ≤ fgcPlannerOptimalValue x0 β := by
  have hα : fgcEquilibriumTargetPath x0 = fun _ => (0 : ℝ) := by
    funext t; exact fgcEquilibriumTargetPath_eq_zero x0 t
  have hσ : fgcEquilibriumSenderPath x0 = fun _ => (1 : ℝ) := by
    funext t; exact fgcEquilibriumSenderPath_eq_one hx0 t
  rw [hα, hσ]
  exact fgc_plannerOptimalValue_lower_bound hx0 hb

/-! ## 8. Round S (2026-09-15; doc 87 W2): the general identity evaluated here,
and the planner optimum attained

The identity `V⁰ − Vᴱ = H/(1−β) + B/(1−β(1−δ))` of
`FourGroup.pathValue_affineCorner_gap` (Theory, general in the polity) is
evaluated at `fourGroupCert` and recovers the displayed margin as a one-line
corollary (Rule 5). Then the planner's problem at this economy is solved: with
the candidate value `v₀(x) = x/(1 − β/2)` the one-step planner inequality
holds at every feasible triple with equality at zero sanctions, so the
Foundations verification lemma (`InfiniteHorizonVerification`, the finite
telescope plus the vanishing terminal term) bounds every feasible path's value
by `v₀(x0)`; the zero-sanction path attains it. The supremum
`fgcPlannerOptimalValue` is therefore `x0/(1 − β/2)`, and the lower bound of
`fgc_plannerOptimalValue_lower_bound_equilibrium` (headline row 29's sibling)
is an equality. No new primitive; no claim of a unique planner policy
(compliance is free at zero sanctions). The reader's 2026-09-11 and 09-12
packages supplied the argument; `docs/archive/workflow-scratch/fourgroup_welfare_sign.py`
checked the slack on a cube grid first (Rule 9C). -/

/-- The Examples-level value is definitionally the Theory-level one, so the
pinned rows keep their types. -/
theorem plannerValue_eq_pathValue (G : FourGroup) (β : ℝ) (xp ap sp : ℕ → ℝ) :
    plannerValue G β xp ap sp = G.pathValue β xp ap sp := rfl

theorem affineCornerPath_half (x0 : ℝ) :
    KaempferLowenberg.affineCornerPath (1/2) x0 = eqPath x0 := by
  funext t; simp only [KaempferLowenberg.affineCornerPath, eqPath]; norm_num

theorem affineZeroPath_half (x0 : ℝ) :
    KaempferLowenberg.affineZeroPath (1/2) x0 = altPath x0 := by
  funext t; simp only [KaempferLowenberg.affineZeroPath, altPath]; norm_num

/-- **The general identity evaluated at the certificate economy** (Rule 5): the
witness margin is the primitive formula at `B = 1`, `C = 33/10`, `H = 23/10`,
`δ = 1/2`. Numerically the same statement as `fgc_planner_inefficiency`; here
it is a substitution into the polity-general identity. -/
theorem fgc_affineCornerGap_eq {β : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    plannerValue fourGroupCert β (altPath x0) (fun _ => 0) (fun _ => 0)
      - plannerValue fourGroupCert β (eqPath x0) (fun _ => 0) (fun _ => 1)
      = 23 / (10 * (1 - β)) + 1 / (1 - β / 2) := by
  rw [plannerValue_eq_pathValue, plannerValue_eq_pathValue, ← affineZeroPath_half,
    ← affineCornerPath_half,
    fourGroupCert.pathValue_affineCorner_gap (by constructor <;> norm_num) hb x0]
  simp only [fourGroupCert]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith [hb.2]
  have h2 : (1 : ℝ) - β / 2 ≠ 0 := by linarith [hb.2]
  field_simp
  ring

/-- **A Bellman upper bound for the planner at the certificate economy.** With
the candidate value `v₀(x) = x/(1 − β/2)`, at every feasible triple
`W(x,a,s) + β·v₀(F(x,s)) ≤ v₀(x)`, with slack
`s(β/(2−β) − 14/5) − s²/2 − (11/5)sa ≤ 0` and equality at `s = 0`. -/
theorem fgc_planner_bellman_upper {β x a s : ℝ} (hb : β ∈ Set.Ico (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    fourGroupCert.plannerW x a s + β * (fgcParams.F x s / (1 - β / 2)) ≤ x / (1 - β / 2) := by
  rw [fgcParams_F, fgcW]
  have hd : 0 < 1 - β / 2 := by linarith [hb.2]
  rw [le_div_iff₀ hd]
  have h2 : (2 : ℝ) - β ≠ 0 := by linarith [hb.2]
  have h1 : β * ((x + s) / 2 / (1 - β / 2)) * (1 - β / 2) = β * (x + s) / 2 := by
    field_simp
  rw [add_mul, h1]
  have hsa : 0 ≤ s * a := mul_nonneg hs.1 ha.1
  nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hb.2.le),
    mul_nonneg (sq_nonneg s) (by linarith [hb.2] : (0 : ℝ) ≤ 2 - β),
    mul_nonneg hsa (by linarith [hb.2] : (0 : ℝ) ≤ 2 - β), hs.1, hb.1]

/-- The physical state and action set as a type, for the Foundations
verification lemma. -/
abbrev fgcCube := ↥(Set.Icc (0 : ℝ) 1)

/-- The planner's one-step state transition at the certificate economy, on the
cube: `(x, (a, s)) ↦ F(x, s)`. -/
noncomputable def fgcPlannerStep (x : fgcCube) (p : fgcCube × fgcCube) : fgcCube :=
  ⟨fgcParams.F x.1 p.2.1, fgcParams.F_mem _ _ x.2 p.2.2⟩

/-- The planner flow on the cube: `(x, (a, s)) ↦ W(x, a, s)`. -/
noncomputable def fgcPlannerStage (x : fgcCube) (p : fgcCube × fgcCube) : ℝ :=
  fourGroupCert.plannerW x.1 p.1.1 p.2.1

/-- A feasible planner path read as a time-dependent Markov plan on the cube
(the plan reads the path's dated actions and ignores the state argument). -/
def FGCPlannerPath.plan {x0 : ℝ} (P : FGCPlannerPath x0) :
    InfiniteHorizonVerification.MarkovPlan fgcCube (fgcCube × fgcCube) :=
  fun t _ => (⟨P.a t, P.a_mem t⟩, ⟨P.s t, P.s_mem t⟩)

/-- The Foundations state path of the plan is the feasible path's own state
sequence. -/
theorem FGCPlannerPath.statePath_eq {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (P : FGCPlannerPath x0) :
    ∀ t, (InfiniteHorizonVerification.statePath fgcPlannerStep P.plan ⟨x0, hx0⟩ t).1 = P.x t
  | 0 => by
      rw [InfiniteHorizonVerification.statePath_zero]
      exact P.x_zero.symm
  | t + 1 => by
      rw [InfiniteHorizonVerification.statePath_succ]
      change fgcParams.F
        (InfiniteHorizonVerification.statePath fgcPlannerStep P.plan ⟨x0, hx0⟩ t).1 (P.s t)
        = P.x (t + 1)
      rw [FGCPlannerPath.statePath_eq hx0 P t, P.step t]

/-- **Every feasible planner path is worth at most `x0/(1 − β/2)`**: the Bellman
upper bound telescopes along the path (Foundations verification lemma), with
the uniform bounds `|W| ≤ 13/2` and `|v₀| ≤ 2` discharging summability and the
vanishing terminal term. -/
theorem fgc_plannerPath_value_le {x0 β : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) (P : FGCPlannerPath x0) :
    plannerValue fourGroupCert β P.x P.a P.s ≤ x0 / (1 - β / 2) := by
  have hpath := P.statePath_eq hx0
  set sp := InfiniteHorizonVerification.statePath fgcPlannerStep P.plan ⟨x0, hx0⟩ with hsp
  have hd : 0 < 1 - β / 2 := by linarith [hb.2]
  have hu : ∀ n : ℕ, |fgcPlannerStage (sp n) (P.plan n (sp n))| ≤ 13 / 2 := by
    intro n
    change |fourGroupCert.plannerW (sp n).1 (P.a n) (P.s n)| ≤ 13 / 2
    exact fgc_plannerW_abs_le (sp n).2 (P.a_mem n) (P.s_mem n)
  have hV : ∀ n : ℕ, |(sp n).1 / (1 - β / 2)| ≤ 2 := by
    intro n
    have hxm := (sp n).2
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_of_nonneg hxm.1]
    linarith [hxm.2, hb.2]
  have hval := InfiniteHorizonVerification.discountedPayoff_le_value_of_uniform_bounds
    fgcPlannerStage fgcPlannerStep β (fun x : fgcCube => x.1 / (1 - β / 2)) hb.1 hb.2
    (fun _ p => fgc_planner_bellman_upper hb p.1.2 p.2.2) P.plan ⟨x0, hx0⟩ (13 / 2) 2
    hu hV
  calc plannerValue fourGroupCert β P.x P.a P.s
      = InfiniteHorizonVerification.discountedPayoff fgcPlannerStage fgcPlannerStep β
          P.plan ⟨x0, hx0⟩ := by
        simp only [plannerValue, InfiniteHorizonVerification.discountedPayoff,
          InfiniteHorizonVerification.discountedStage]
        refine tsum_congr (fun t => ?_)
        change β ^ t * fourGroupCert.plannerW (P.x t) (P.a t) (P.s t)
          = β ^ t * fourGroupCert.plannerW (sp t).1 (P.a t) (P.s t)
        rw [hpath t]
    _ ≤ x0 / (1 - β / 2) := hval

/-- **The certificate planner problem is the general one at `F = fgcParams.F`**
(BI.2, 2026-10-07; affine-restricted, the witness transition is `affineF (1/2)`).
`FGCPlannerPath x0` and the Theory-level `PlannerPath fgcParams.F x0` have the same
fields, so the two feasible-value sets coincide and the certificate optimum is the
general `plannerOptimalValue` of `fourGroupCert`. -/
theorem fgcPlannerFeasibleValues_eq_general (x0 β : ℝ) :
    fgcPlannerFeasibleValues x0 β = fourGroupCert.plannerFeasibleValues fgcParams.F β x0 := by
  ext v
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨⟨P.x, P.a, P.s, P.x_zero, P.x_mem, P.a_mem, P.s_mem, P.step⟩, rfl⟩
  · rintro ⟨P, rfl⟩
    exact ⟨⟨P.x, P.a, P.s, P.x_zero, P.x_mem, P.a_mem, P.s_mem, P.step⟩, rfl⟩

/-- The certificate optimum is `FourGroup.plannerOptimalValue` at `fourGroupCert`
and `fgcParams.F` (BI.2; affine-restricted). -/
theorem fgcPlannerOptimalValue_eq_general (x0 β : ℝ) :
    fgcPlannerOptimalValue x0 β = fourGroupCert.plannerOptimalValue fgcParams.F β x0 := by
  unfold fgcPlannerOptimalValue FourGroup.plannerOptimalValue
  rw [fgcPlannerFeasibleValues_eq_general]

/-- **The planner's optimal value at the certificate economy is attained by the
zero-sanction path**: `fgcPlannerOptimalValue x0 β = x0/(1 − β/2)` for every
physical start and every planner discount. Since BI.2 (2026-10-07) an instance of
the general affine theorem `FourGroup.plannerOptimalValue_eq_affineF` at `δ = 1/2`
(`B = 1`, `g_J = q_K`, compliance flow `φ ≡ 0`), whose margin reads
`β/(2 − β) ≤ 14/5` here; the witness-level verification
`fgc_plannerPath_value_le` is kept beside it. Affine-restricted (Rule 22). -/
theorem fgcPlannerOptimalValue_eq {x0 β : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    fgcPlannerOptimalValue x0 β = x0 / (1 - β / 2) := by
  have hF : fgcParams.F = AbstractGame.affineF (1 / 2) := rfl
  have hd : (0 : ℝ) < 1 - β * (1 - 1 / 2) := by linarith [hb.2]
  have hφ : fourGroupCert.complianceFlow fourGroupCert.optCompliance = 0 := by
    simp only [FourGroup.complianceFlow, fourGroupCert]
    ring
  have hm : fourGroupCert.g_J - fourGroupCert.q_K
      + β * (1 / 2) * (fourGroupCert.b_J - fourGroupCert.b_K) / (1 - β * (1 - 1 / 2))
      ≤ fourGroupCert.d_s := by
    have h1 : β * (1 / 2) * (fourGroupCert.b_J - fourGroupCert.b_K) / (1 - β * (1 - 1 / 2))
        ≤ 1 := by
      rw [div_le_one hd]
      simp only [fourGroupCert]
      linarith [hb.2]
    simp only [fourGroupCert] at h1 ⊢
    linarith
  rw [fgcPlannerOptimalValue_eq_general, hF,
    fourGroupCert.plannerOptimalValue_eq_affineF (by constructor <;> norm_num) hb hm hx0, hφ]
  simp only [fourGroupCert]
  have h3 : (1 : ℝ) - β * (1 - 1 / 2) = 1 - β / 2 := by ring
  rw [h3]
  ring

/-- **The exact planner loss of the equilibrium** (the equality form of
`fgc_plannerOptimalValue_lower_bound_equilibrium`, on the equilibrium-derived
paths): `𝒲*_β(x0) − Vᴱ(x0; β) = 23/(10(1−β)) + 1/(1−β/2)`. -/
theorem fgc_plannerOptimalValue_gap_eq_equilibrium {x0 β : ℝ}
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (hb : β ∈ Set.Ico (0 : ℝ) 1) :
    fgcPlannerOptimalValue x0 β
        - plannerValue fourGroupCert β (eqPath x0)
            (fgcEquilibriumTargetPath x0) (fgcEquilibriumSenderPath x0)
      = 23 / (10 * (1 - β)) + 1 / (1 - β / 2) := by
  have h := fgc_planner_inefficiency_equilibrium hx0 hb
  rw [fgcPlannerOptimalValue_eq hx0 hb, ← fgc_plannerValue_altPath x0 hb]
  linarith

#print axioms fgc_affineCornerGap_eq
#print axioms fgc_planner_bellman_upper
#print axioms fgc_plannerPath_value_le
#print axioms fgcPlannerOptimalValue_eq
#print axioms fgc_plannerOptimalValue_gap_eq_equilibrium
#print axioms fgc_plannerOptimalValue_lower_bound
#print axioms fgc_equilibrium_lt_plannerOptimalValue
#print axioms fgc_VS_star_fixed
#print axioms fgc_VT_star_fixed
#print axioms fgcExactEquilibriumTop
#print axioms fgc_planner_inefficiency_equilibrium
#print axioms fgc_plannerOptimalValue_lower_bound_equilibrium
#print axioms eeCert_VS_star_fixed
#print axioms eeCert_VT_star_fixed

end Examples

end Sanctions
