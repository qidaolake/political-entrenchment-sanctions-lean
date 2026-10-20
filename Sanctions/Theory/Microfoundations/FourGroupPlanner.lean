/-
Sanctions/Theory/Microfoundations/FourGroupPlanner.lean

**The utilitarian planner objective over a four-group polity, and the
machine-checked identity that locates the payoff wedge in the political
weights.**

`plannerW` is the welfare a utilitarian social planner counts: the
Grossman-Helpman aggregate `U_S + U_T` with every political-effectiveness
weight `θ_g` replaced by `1` — the unweighted sum of the four group
welfares — **retaining** the group-borne resource terms that already enter
`U_S`/`U_T` with unit weight (sanction deadweight `kS·s²`, placation
`w_pl·s·a`, direct compliance benefit `base_S·a`, compliance concavity
`kT·a²`, sanction cost `d_s·s`).

This is a **DEFINITION, not an assumption** (Rule-3 status: user-approved
2026-07-11). Zero new scalars, Props, or hypotheses: every coefficient is
an existing `FourGroup` field (symbol economy). The single design choice —
unit weights, resource terms kept — is load-bearing: dropping the resource
terms leaves `(g_J − q_K)·s + (b_J − b_K)·x + (c_K − c_J)·a` in general and, at
the witness (`g_J = q_K`, `c_J = c_K`), just `W = x`, under which the
stationary lock-in triple maximises the planner flow at the witness and the
comparison below is empty there (the general residual stated 2026-09-15, the
reader's S6). No claim is made about every `FourGroup` economy.

The identity is then

  U_S + U_T − plannerW = Σ_g (θ_g − 1)·w_g

(`plannerW_distortion`): at any common action triple, the sum of the two
governments' stage payoffs exceeds what the planner counts by exactly the
politically over- and under-weighted group welfares. It is an algebraic
identity at a common action — the two governments do not jointly maximise
that sum — so it locates the payoff wedge in the weights and does not by
itself attribute an equilibrium inefficiency to them; the equilibrium
comparisons are the fgc planner-inefficiency theorems in
`Sanctions/Examples/FourGroupPlannerWitness.lean`, which consume it.

Since 2026-10-07 the layer is proved over bare coefficients (`FourGroupCoeffs`,
BH6.2) and the `FourGroup` forms are `rfl` corollaries; section 4 adds the
hawk-rescaling family (BH6.1): a polity and its rescaling play the same game for
every transition while the unit-weight planner's gap moves by `−(k − 1)·g_J/(1 − β)`.
-/

import Sanctions.Theory.Microfoundations.FourGroupPolity
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.DiscountedSignCharacterization
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sanctions
namespace KaempferLowenberg

/-! ## 1. The planner objective and the stationary comparison

**Layout (BH6.2, 2026-10-07).** Every section of this file states its welfare
results twice. First over bare coefficients, `G : FourGroupCoeffs` — the eighteen
numbers of a four-group polity with none of the four region-(R) fields — where the
proofs live; the results therefore hold for every coefficient vector, including
empowerment-dominant polities outside region (R). Then over `G : FourGroup`, where
each theorem keeps its statement and is the coefficient form read at `G.toCoeffs`,
by `rfl`; the definitions `plannerW`, `stationaryPlannerValue`, `pathValue` and
`plannerWBound` keep their bodies (`toCoeffs_plannerW` and siblings). Pinned rows
(`plannerW_distortion`, `plannerW_lockin_dominated_iff`) keep their statements. -/

namespace FourGroupCoeffs

variable (G : FourGroupCoeffs)

/-- **Utilitarian planner objective** (user-approved definition,
2026-07-11): the Grossman-Helpman aggregate `U_S + U_T` with every
political-effectiveness weight `θ_g` set to `1` — i.e. the unweighted sum
of the four group welfares `w_{J_S} + w_{K_S} + w_{J_T} + w_{K_T}`,
**retaining** the group-borne resource terms exactly as they already enter
the stage payoffs with unit weight: sanction deadweight `kS·s²`, placation
transfer `w_pl·s·a`, direct compliance benefit `base_S·a`, compliance
concavity `kT·a²`, and the target-side sanction cost `d_s·s`.

No new scalar, no new hypothesis, no assumption-surface change. Dropping the
resource terms instead (the "labeled-linear-only" reading) would leave
`(g_J − q_K)·s + (b_J − b_K)·x + (c_K − c_J)·a` (at the witness, `x`), under
which the lock-in triple maximises the planner flow at the witness; that
reading is excluded by design.
Coefficient form (BH6.2, 2026-10-07): every coefficient is a field of
`FourGroupCoeffs`, named as in `FourGroup`; no region-(R) field is assumed, so it
holds for every coefficient vector; no transition enters. -/
def plannerW (x a s : ℝ) : ℝ :=
  (G.g_J * s - G.q_K * s + G.base_S * a - G.kS * s ^ 2 - G.w_pl * s * a)
    + ((G.b_J - G.b_K) * x + (G.c_K - G.c_J) * a - G.kT * a ^ 2 - G.d_s * s)

/-- **The payoff wedge is the political weights** (exact ring identity, all
18 fields): at any common action triple, the sum of the two governments'
stage payoffs exceeds the utilitarian planner objective by exactly the
politically re-weighted group welfares,

  `U_S + U_T = plannerW + Σ_g (θ_g − 1)·w_g`,

where `θ_{J_S}(x) = th0_JS + ν·x` weights the sender hawks' welfare
`g_J·s`, `θ_{K_S} = th0_KS` weights the sender trade-dependents' welfare
`−q_K·s`, `θ_{J_T}(s) = th0_JT + ρ·s` weights the target regime's welfare
`b_J·x − c_J·a`, and `θ_{K_T}(s) = th0_KT + μ·s` weights the target
opposition's welfare `−b_K·x + c_K·a`. Whenever some `θ_g ≠ 1`, the
politically-derived stage payoffs value that group's welfare differently
from the planner. The identity is a same-action algebraic difference: it
locates the payoff wedge in the political-effectiveness weights, and says
nothing by itself about equilibrium play, which the two governments choose
separately; the equilibrium welfare comparisons are the consumers named in
the file header.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem plannerW_distortion (x a s : ℝ) :
    G.U_S x a s + G.U_T x a s
      = G.plannerW x a s
        + (G.th0_JS + G.nu * x - 1) * (G.g_J * s)
        + (G.th0_KS - 1) * (-(G.q_K * s))
        + (G.th0_JT + G.rho * s - 1) * (G.b_J * x - G.c_J * a)
        + (G.th0_KT + G.mu * s - 1) * (-(G.b_K * x) + G.c_K * a) := by
  simp only [U_S, U_T, plannerW]
  ring

/-- **Parametric lock-in-vs-zero planner boundary** (strict inequality
among existing fields — no new scalar, Rule-3 symbol economy; Rule 5:
witnesses instantiate this as one-line corollaries). The sanctions
lock-in stationary point `(x, a, s) = (1, 0, 1)` — political state maxed,
full defiance, sanctions maxed — is strictly planner-dominated by the
zero stationary point `(0, 0, 0)` **iff** the planner's linear flow gain
from holding the lock-in state, `(g_J − q_K) + (b_J − b_K)` (net sender
group benefit of maximal sanctions plus net target group value of the
maximal political state), is strictly below the per-period resource burn
`kS + d_s` (sender deadweight plus target-side sanction cost) needed to
sustain it.

Scope note (honest boundary): this characterizes the lock-in corner
against the zero stationary point specifically; an economy failing the
inequality could in principle still be stationary-inefficient relative to
some other non-zero stationary point.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem plannerW_lockin_dominated_iff :
    G.plannerW 1 0 1 < G.plannerW 0 0 0 ↔
      (G.g_J - G.q_K) + (G.b_J - G.b_K) < G.kS + G.d_s := by
  have h0 : G.plannerW 0 0 0 = 0 := by
    simp only [plannerW]; ring
  have h1 : G.plannerW 1 0 1
      = (G.g_J - G.q_K) + (G.b_J - G.b_K) - (G.kS + G.d_s) := by
    simp only [plannerW]; ring
  rw [h0, h1]
  constructor <;> intro h <;> linarith

/-- Discounted utilitarian welfare along a stationary triple
`(x, a, s)`.  This is the capitalized version of `plannerW`, with a
planner discount factor `β`.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
noncomputable def stationaryPlannerValue (G : FourGroupCoeffs)
    (β x a s : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * G.plannerW x a s

/-- A stationary planner flow is capitalized by the usual geometric
factor.  No restriction beyond `β ∈ [0,1)` is added to the four-group
economy.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem stationaryPlannerValue_eq {β x a s : ℝ}
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    G.stationaryPlannerValue β x a s = G.plannerW x a s / (1 - β) := by
  simp only [stationaryPlannerValue]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ.1 hβ.2]
  ring

/-- **Parametric discounted lock-in boundary.** For every planner
discount factor in `[0,1)`, the stationary lock-in path is strictly
planner-dominated by the stationary zero path exactly under the same
primitive resource-cost inequality as the one-period comparison.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem stationaryPlannerValue_lockin_dominated_iff {β : ℝ}
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    G.stationaryPlannerValue β 1 0 1
        < G.stationaryPlannerValue β 0 0 0 ↔
      (G.g_J - G.q_K) + (G.b_J - G.b_K) < G.kS + G.d_s := by
  rw [stationaryPlannerValue_eq G hβ, stationaryPlannerValue_eq G hβ,
      div_lt_div_iff_of_pos_right (sub_pos.mpr hβ.2)]
  exact G.plannerW_lockin_dominated_iff

/-- The exact discounted gain from replacing the stationary lock-in
path by the stationary zero path, expressed only in existing
four-group primitives.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem stationaryPlannerValue_relief_gain {β : ℝ}
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    G.stationaryPlannerValue β 0 0 0
        - G.stationaryPlannerValue β 1 0 1 =
      ((G.kS + G.d_s)
          - ((G.g_J - G.q_K) + (G.b_J - G.b_K))) / (1 - β) := by
  rw [stationaryPlannerValue_eq G hβ, stationaryPlannerValue_eq G hβ]
  have h0 : G.plannerW 0 0 0 = 0 := by
    simp only [plannerW]
    ring
  have h1 : G.plannerW 1 0 1 =
      (G.g_J - G.q_K) + (G.b_J - G.b_K) - (G.kS + G.d_s) := by
    simp only [plannerW]
    ring
  rw [h0, h1]
  ring

/-! ## 2. Path accounting, general in the polity (round S, 2026-09-15; doc 87 W1)

The discounted planner value along a state–action path, the coefficient bound
that makes it summable on the cube, and the two comparison paths behind the
welfare verdict of `sec:policy:welfare`: the persistent corner path (full
sanctions against full defiance) and the zero path (no sanctions, no
compliance), both from a common start. Everything is stated over bare
coefficients `G : FourGroupCoeffs` (BH6.2, 2026-10-07), so no region field of
`FourGroup` enters at all, which is why the sign of the gap is a theorem about
the coefficients and not a consequence of region (R)
(`Examples/FourGroupWelfareSign.lean` exhibits region-(R) polities with the
opposite sign). The affine closed forms carry the affine label (Rule 22); the
recursive paths of section 3 are general in the transition. The identities
and both sign conditions were derived by the reader (packages of 2026-09-11,
09-12 and 09-15, answering doc 86) and checked in exact rational arithmetic
(`docs/archive/workflow-scratch/fourgroup_welfare_sign.py`, Rule 9C) before
this Lean was written.

Proof abbreviations used in the docstrings, never as new primitives:
`B = b_J − b_K` (the Target groups' net state valuation), `C = (k_S + d_s) −
(g_J − q_K)` (the per-period resource burn net of the Sender groups' sanction
benefit), and `H = C − B = W(0,0,0) − W(1,0,1)`, the stationary flow gap of
`plannerW_lockin_dominated_iff`. -/

/-- **Discounted planner value along a path triple** `(x_t, a_t, s_t)` under
the planner discount `β`: `Σ_t β^t·W(x_t, a_t, s_t)`, a `tsum`; the theorems
below establish summability wherever it is consumed. The Examples-level
`plannerValue` is definitionally the `FourGroup` form `FourGroup.pathValue`
(`Examples.plannerValue_eq_pathValue`), which is this at `G.toCoeffs`
(`FourGroup.toCoeffs_pathValue`), so nothing pinned there changes.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
noncomputable def pathValue (β : ℝ) (xp ap sp : ℕ → ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * G.plannerW (xp t) (ap t) (sp t)

/-- **The coefficient bound on the planner flow**: the sum of the absolute
coefficients of the six monomials of `plannerW`, each of which has modulus at
most one on the cube. General in the polity, with no sign restriction; it
replaces the witness-specific `13/2` as the summability certificate.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
noncomputable def plannerWBound : ℝ :=
  |G.g_J - G.q_K - G.d_s| + |G.base_S + G.c_K - G.c_J| + |G.kS| + |G.w_pl|
    + |G.b_J - G.b_K| + |G.kT|

/-- On `[0,1]³`, `|W| ≤ plannerWBound`: the triangle inequality over the six
monomials, each bounded by the modulus of its coefficient there.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem plannerW_abs_le_cube {x a s : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |G.plannerW x a s| ≤ G.plannerWBound := by
  have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have ha1 : |a| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hs2 : |s ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs1
  have ha2 : |a ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha1
  have hsa : |s * a| ≤ 1 := by rw [abs_mul]; exact mul_le_one₀ hs1 (abs_nonneg _) ha1
  have h1 : |(G.g_J - G.q_K - G.d_s) * s| ≤ |G.g_J - G.q_K - G.d_s| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs1
  have h2 : |(G.base_S + G.c_K - G.c_J) * a| ≤ |G.base_S + G.c_K - G.c_J| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) ha1
  have h3 : |G.kS * s ^ 2| ≤ |G.kS| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs2
  have h4 : |G.w_pl * (s * a)| ≤ |G.w_pl| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hsa
  have h5 : |(G.b_J - G.b_K) * x| ≤ |G.b_J - G.b_K| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hx1
  have h6 : |G.kT * a ^ 2| ≤ |G.kT| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) ha2
  have hW : G.plannerW x a s = (G.g_J - G.q_K - G.d_s) * s + (G.base_S + G.c_K - G.c_J) * a
      - G.kS * s ^ 2 - G.w_pl * (s * a) + (G.b_J - G.b_K) * x - G.kT * a ^ 2 := by
    simp only [plannerW]; ring
  rw [hW, plannerWBound, abs_le]
  constructor <;> linarith [le_abs_self ((G.g_J - G.q_K - G.d_s) * s),
    neg_abs_le ((G.g_J - G.q_K - G.d_s) * s),
    le_abs_self ((G.base_S + G.c_K - G.c_J) * a), neg_abs_le ((G.base_S + G.c_K - G.c_J) * a),
    le_abs_self (G.kS * s ^ 2), neg_abs_le (G.kS * s ^ 2),
    le_abs_self (G.w_pl * (s * a)), neg_abs_le (G.w_pl * (s * a)),
    le_abs_self ((G.b_J - G.b_K) * x), neg_abs_le ((G.b_J - G.b_K) * x),
    le_abs_self (G.kT * a ^ 2), neg_abs_le (G.kT * a ^ 2)]

/-- Along any cube-valued path the discounted flow is summable, by geometric
comparison against `plannerWBound · β^t`.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; no transition enters. -/
theorem pathValue_summable {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {xp ap sp : ℕ → ℝ}
    (hxp : ∀ t, xp t ∈ Set.Icc (0 : ℝ) 1) (hap : ∀ t, ap t ∈ Set.Icc (0 : ℝ) 1)
    (hsp : ∀ t, sp t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun t : ℕ => β ^ t * G.plannerW (xp t) (ap t) (sp t)) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => G.plannerWBound * β ^ t)
    ((summable_geometric_of_lt_one hβ.1 hβ.2).mul_left _) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.1]
  have hW := G.plannerW_abs_le_cube (hxp t) (hap t) (hsp t)
  have hpow : (0 : ℝ) ≤ β ^ t := pow_nonneg hβ.1 t
  nlinarith [mul_le_mul_of_nonneg_left hW hpow]

end FourGroupCoeffs

namespace FourGroup

variable (G : FourGroup)

/-- **Utilitarian planner objective** (user-approved definition,
2026-07-11): the Grossman-Helpman aggregate `U_S + U_T` with every
political-effectiveness weight `θ_g` set to `1` — i.e. the unweighted sum
of the four group welfares `w_{J_S} + w_{K_S} + w_{J_T} + w_{K_T}`,
**retaining** the group-borne resource terms exactly as they already enter
the stage payoffs with unit weight: sanction deadweight `kS·s²`, placation
transfer `w_pl·s·a`, direct compliance benefit `base_S·a`, compliance
concavity `kT·a²`, and the target-side sanction cost `d_s·s`.

Every coefficient is an existing `FourGroup` field — no new scalar, no new
hypothesis, no assumption-surface change. Dropping the resource terms
instead (the "labeled-linear-only" reading) would leave
`(g_J − q_K)·s + (b_J − b_K)·x + (c_K − c_J)·a` (at the witness, `x`), under
which the lock-in triple maximises the planner flow at the witness; that
reading is excluded by design.
Body unchanged; it is `FourGroupCoeffs.plannerW` of `G.toCoeffs` by `rfl` (BH6.2).
-/
def plannerW (x a s : ℝ) : ℝ :=
  (G.g_J * s - G.q_K * s + G.base_S * a - G.kS * s ^ 2 - G.w_pl * s * a)
    + ((G.b_J - G.b_K) * x + (G.c_K - G.c_J) * a - G.kT * a ^ 2 - G.d_s * s)

/-- **The payoff wedge is the political weights** (exact ring identity, all
18 fields): at any common action triple, the sum of the two governments'
stage payoffs exceeds the utilitarian planner objective by exactly the
politically re-weighted group welfares,

  `U_S + U_T = plannerW + Σ_g (θ_g − 1)·w_g`,

where `θ_{J_S}(x) = th0_JS + ν·x` weights the sender hawks' welfare
`g_J·s`, `θ_{K_S} = th0_KS` weights the sender trade-dependents' welfare
`−q_K·s`, `θ_{J_T}(s) = th0_JT + ρ·s` weights the target regime's welfare
`b_J·x − c_J·a`, and `θ_{K_T}(s) = th0_KT + μ·s` weights the target
opposition's welfare `−b_K·x + c_K·a`. Whenever some `θ_g ≠ 1`, the
politically-derived stage payoffs value that group's welfare differently
from the planner. The identity is a same-action algebraic difference: it
locates the payoff wedge in the political-effectiveness weights, and says
nothing by itself about equilibrium play, which the two governments choose
separately; the equilibrium welfare comparisons are the consumers named in
the file header.
The `FourGroup` form of `FourGroupCoeffs.plannerW_distortion`, by `rfl` through
`toCoeffs` (BH6.2); statement unchanged; no transition enters. -/
theorem plannerW_distortion (x a s : ℝ) :
    G.U_S x a s + G.U_T x a s
      = G.plannerW x a s
        + (G.th0_JS + G.nu * x - 1) * (G.g_J * s)
        + (G.th0_KS - 1) * (-(G.q_K * s))
        + (G.th0_JT + G.rho * s - 1) * (G.b_J * x - G.c_J * a)
        + (G.th0_KT + G.mu * s - 1) * (-(G.b_K * x) + G.c_K * a) :=
  G.toCoeffs.plannerW_distortion x a s

/-- **Parametric lock-in-vs-zero planner boundary** (strict inequality
among existing fields — no new scalar, Rule-3 symbol economy; Rule 5:
witnesses instantiate this as one-line corollaries). The sanctions
lock-in stationary point `(x, a, s) = (1, 0, 1)` — political state maxed,
full defiance, sanctions maxed — is strictly planner-dominated by the
zero stationary point `(0, 0, 0)` **iff** the planner's linear flow gain
from holding the lock-in state, `(g_J − q_K) + (b_J − b_K)` (net sender
group benefit of maximal sanctions plus net target group value of the
maximal political state), is strictly below the per-period resource burn
`kS + d_s` (sender deadweight plus target-side sanction cost) needed to
sustain it.

Scope note (honest boundary): this characterizes the lock-in corner
against the zero stationary point specifically; an economy failing the
inequality could in principle still be stationary-inefficient relative to
some other non-zero stationary point.
The `FourGroup` form of `FourGroupCoeffs.plannerW_lockin_dominated_iff`, by `rfl`
through `toCoeffs` (BH6.2); statement unchanged; no transition enters. -/
theorem plannerW_lockin_dominated_iff :
    G.plannerW 1 0 1 < G.plannerW 0 0 0 ↔
      (G.g_J - G.q_K) + (G.b_J - G.b_K) < G.kS + G.d_s :=
  G.toCoeffs.plannerW_lockin_dominated_iff

/-- Discounted utilitarian welfare along a stationary triple
`(x, a, s)`.  This is the capitalized version of `plannerW`, with a
planner discount factor `β`.
Body unchanged; it is `FourGroupCoeffs.stationaryPlannerValue` of `G.toCoeffs` by
`rfl` (BH6.2). -/
noncomputable def stationaryPlannerValue (G : FourGroup)
    (β x a s : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * G.plannerW x a s

/-- A stationary planner flow is capitalized by the usual geometric factor. The
`FourGroup` form of `FourGroupCoeffs.stationaryPlannerValue_eq`, by `rfl` through
`toCoeffs` (BH6.2); statement unchanged; no transition enters. -/
theorem stationaryPlannerValue_eq {β x a s : ℝ}
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    G.stationaryPlannerValue β x a s = G.plannerW x a s / (1 - β) :=
  G.toCoeffs.stationaryPlannerValue_eq hβ

/-- **Parametric discounted lock-in boundary.** For every planner discount in
`[0,1)`, the stationary lock-in path is strictly planner-dominated by the
stationary zero path exactly under the one-period resource-cost inequality. The
`FourGroup` form of `FourGroupCoeffs.stationaryPlannerValue_lockin_dominated_iff`,
by `rfl` through `toCoeffs` (BH6.2); statement unchanged; no transition enters. -/
theorem stationaryPlannerValue_lockin_dominated_iff {β : ℝ}
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    G.stationaryPlannerValue β 1 0 1
        < G.stationaryPlannerValue β 0 0 0 ↔
      (G.g_J - G.q_K) + (G.b_J - G.b_K) < G.kS + G.d_s :=
  G.toCoeffs.stationaryPlannerValue_lockin_dominated_iff hβ

/-- The exact discounted gain from replacing the stationary lock-in path by the
stationary zero path, expressed only in existing four-group primitives. The
`FourGroup` form of `FourGroupCoeffs.stationaryPlannerValue_relief_gain`, by `rfl`
through `toCoeffs` (BH6.2); statement unchanged; no transition enters. -/
theorem stationaryPlannerValue_relief_gain {β : ℝ}
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    G.stationaryPlannerValue β 0 0 0
        - G.stationaryPlannerValue β 1 0 1 =
      ((G.kS + G.d_s)
          - ((G.g_J - G.q_K) + (G.b_J - G.b_K))) / (1 - β) :=
  G.toCoeffs.stationaryPlannerValue_relief_gain hβ

/-! The `FourGroup` forms of the path accounting (BH6.2, 2026-10-07): the
definitions keep their bodies, and each theorem is the coefficient form above read
at `G.toCoeffs`, by `rfl`. -/

/-- **Discounted planner value along a path triple** `(x_t, a_t, s_t)` under
the planner discount `β`: `Σ_t β^t·W(x_t, a_t, s_t)`, a `tsum`; the theorems
below establish summability wherever it is consumed. The Examples-level
`plannerValue` is definitionally this (`Examples.plannerValue_eq_pathValue`),
so nothing pinned there changes.
Body unchanged; it is `FourGroupCoeffs.pathValue` of `G.toCoeffs` by `rfl` (BH6.2).
-/
noncomputable def pathValue (β : ℝ) (xp ap sp : ℕ → ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * G.plannerW (xp t) (ap t) (sp t)

/-- **The coefficient bound on the planner flow**: the sum of the absolute
coefficients of the six monomials of `plannerW`, each of which has modulus at
most one on the cube. General in the polity, with no sign restriction; it
replaces the witness-specific `13/2` as the summability certificate.
Body unchanged; it is `FourGroupCoeffs.plannerWBound` of `G.toCoeffs` by `rfl`
(BH6.2). -/
noncomputable def plannerWBound : ℝ :=
  |G.g_J - G.q_K - G.d_s| + |G.base_S + G.c_K - G.c_J| + |G.kS| + |G.w_pl|
    + |G.b_J - G.b_K| + |G.kT|

/-- The planner objective of a polity is that of its coefficients (`rfl`, BH6.2). -/
theorem toCoeffs_plannerW : G.toCoeffs.plannerW = G.plannerW := rfl

/-- The stationary planner value of a polity is that of its coefficients (`rfl`). -/
theorem toCoeffs_stationaryPlannerValue :
    G.toCoeffs.stationaryPlannerValue = G.stationaryPlannerValue := rfl

/-- The discounted path value of a polity is that of its coefficients (`rfl`). -/
theorem toCoeffs_pathValue : G.toCoeffs.pathValue = G.pathValue := rfl

/-- The cube bound of a polity is that of its coefficients (`rfl`). -/
theorem toCoeffs_plannerWBound : G.toCoeffs.plannerWBound = G.plannerWBound := rfl

/-- On `[0,1]³`, `|W| ≤ plannerWBound`. The `FourGroup` form of
`FourGroupCoeffs.plannerW_abs_le_cube`, by `rfl` through `toCoeffs` (BH6.2);
statement unchanged; no transition enters. -/
theorem plannerW_abs_le_cube {x a s : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |G.plannerW x a s| ≤ G.plannerWBound :=
  G.toCoeffs.plannerW_abs_le_cube hx ha hs

/-- Along any cube-valued path the discounted flow is summable, by geometric
comparison against `plannerWBound · β^t`. The `FourGroup` form of
`FourGroupCoeffs.pathValue_summable`, by `rfl` through `toCoeffs` (BH6.2); statement
unchanged; no transition enters. -/
theorem pathValue_summable {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {xp ap sp : ℕ → ℝ}
    (hxp : ∀ t, xp t ∈ Set.Icc (0 : ℝ) 1) (hap : ∀ t, ap t ∈ Set.Icc (0 : ℝ) 1)
    (hsp : ∀ t, sp t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun t : ℕ => β ^ t * G.plannerW (xp t) (ap t) (sp t)) :=
  G.toCoeffs.pathValue_summable hβ hxp hap hsp

end FourGroup

/-! ### The affine comparison paths (affine-labelled, Rule 22) -/

/-- **Affine-labelled**: the persistent corner state path from `x0` under the
affine law at rate `δ`, `1 − (1 − x0)(1 − δ)^t` — the orbit of
`x ↦ affineF δ x 1`, sanctions maximal at every date. At `δ = 1/2` it is the
witness path `Examples.eqPath`. -/
def affineCornerPath (δ x0 : ℝ) (t : ℕ) : ℝ := 1 - (1 - x0) * (1 - δ) ^ t

/-- **Affine-labelled**: the zero-sanction state path from `x0`, `x0(1 − δ)^t`
— the orbit of `x ↦ affineF δ x 0`. At `δ = 1/2` it is `Examples.altPath`. -/
def affineZeroPath (δ x0 : ℝ) (t : ℕ) : ℝ := x0 * (1 - δ) ^ t

@[simp] theorem affineCornerPath_zero (δ x0 : ℝ) : affineCornerPath δ x0 0 = x0 := by
  simp [affineCornerPath]

@[simp] theorem affineZeroPath_zero (δ x0 : ℝ) : affineZeroPath δ x0 0 = x0 := by
  simp [affineZeroPath]

/-- One step of the corner path is the affine transition at the sanction corner. -/
theorem affineCornerPath_step (δ x0 : ℝ) (t : ℕ) :
    affineCornerPath δ x0 (t + 1) = AbstractGame.affineF δ (affineCornerPath δ x0 t) 1 := by
  simp only [affineCornerPath, AbstractGame.affineF]; ring

/-- One step of the zero path is the affine transition at zero sanctions. -/
theorem affineZeroPath_step (δ x0 : ℝ) (t : ℕ) :
    affineZeroPath δ x0 (t + 1) = AbstractGame.affineF δ (affineZeroPath δ x0 t) 0 := by
  simp only [affineZeroPath, AbstractGame.affineF]; ring

theorem affineCornerPath_mem_cube {δ x0 : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) : affineCornerPath δ x0 t ∈ Set.Icc (0 : ℝ) 1 := by
  have hp0 : (0 : ℝ) ≤ (1 - δ) ^ t := pow_nonneg (by linarith [hδ.2]) t
  have hp1 : (1 - δ) ^ t ≤ 1 := pow_le_one₀ (by linarith [hδ.2]) (by linarith [hδ.1])
  have h1 : 0 ≤ (1 - x0) * (1 - δ) ^ t := mul_nonneg (by linarith [hx0.2]) hp0
  have h2 : (1 - x0) * (1 - δ) ^ t ≤ (1 - x0) * 1 :=
    mul_le_mul_of_nonneg_left hp1 (by linarith [hx0.2])
  constructor <;> simp only [affineCornerPath] <;> linarith [hx0.1]

theorem affineZeroPath_mem_cube {δ x0 : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) : affineZeroPath δ x0 t ∈ Set.Icc (0 : ℝ) 1 := by
  have hp0 : (0 : ℝ) ≤ (1 - δ) ^ t := pow_nonneg (by linarith [hδ.2]) t
  have hp1 : (1 - δ) ^ t ≤ 1 := pow_le_one₀ (by linarith [hδ.2]) (by linarith [hδ.1])
  have h1 : 0 ≤ x0 * (1 - δ) ^ t := mul_nonneg hx0.1 hp0
  have h2 : x0 * (1 - δ) ^ t ≤ x0 * 1 := mul_le_mul_of_nonneg_left hp1 hx0.1
  constructor <;> simp only [affineZeroPath] <;> linarith [hx0.2]

namespace FourGroupCoeffs

variable (G : FourGroupCoeffs)

/-- **Per-period gap on the affine corner paths** (affine-labelled): with both
paths started at the same `x0`, the flow of the zero path exceeds the flow of
the corner path by `H + B(1 − δ)^t` — the stationary gap `H` plus a vanishing
transition bonus — and the start cancels identically. Pure algebra in the
eighteen coefficients; no sign is used.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; affine-restricted (Rule 22). -/
theorem plannerW_affineCorner_gap (δ x0 : ℝ) (t : ℕ) :
    G.plannerW (affineZeroPath δ x0 t) 0 0 - G.plannerW (affineCornerPath δ x0 t) 0 1
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K))
        + (G.b_J - G.b_K) * (1 - δ) ^ t := by
  simp only [plannerW, affineZeroPath, affineCornerPath]; ring

/-- **The discounted affine gap in primitives** (affine-labelled): for every
`δ ∈ (0,1)`, every planner discount `β ∈ [0,1)` and every start,

  `V⁰ − Vᴱ = H/(1 − β) + B/(1 − β(1 − δ))`,

the capitalised stationary gap plus the capitalised transition bonus, whose
ratio is the inherited-state weight `1 − δ` times the discount. Two geometric
series; the start drops out. At `fourGroupCert` (`δ = 1/2`, `B = 1`,
`H = 23/10`) this is the manuscript's `23/(10(1−β)) + 1/(1−β/2)`
(`Examples.fgc_affineCornerGap_eq`).
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; affine-restricted (Rule 22). -/
theorem pathValue_affineCorner_gap {δ β : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * (1 - δ)) := by
  have hb0 := hβ.1
  have hb1 := hβ.2
  have hγ0 : 0 ≤ 1 - δ := by linarith [hδ.2]
  have hγ1 : 1 - δ ≤ 1 := by linarith [hδ.1]
  have hbg0 : 0 ≤ β * (1 - δ) := mul_nonneg hb0 hγ0
  have hbg1 : β * (1 - δ) < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hb0 hγ1) hb1
  have hg1 : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hb0 hb1
  have hg2 : Summable (fun t : ℕ => (β * (1 - δ)) ^ t) :=
    summable_geometric_of_lt_one hbg0 hbg1
  have hzero : ∀ t : ℕ, β ^ t * G.plannerW (affineZeroPath δ x0 t) 0 0
      = ((G.b_J - G.b_K) * x0) * (β * (1 - δ)) ^ t := by
    intro t; simp only [plannerW, affineZeroPath]; rw [mul_pow]; ring
  have hcorner : ∀ t : ℕ, β ^ t * G.plannerW (affineCornerPath δ x0 t) 0 1
      = (-((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K))) * β ^ t
        - ((G.b_J - G.b_K) * (1 - x0)) * (β * (1 - δ)) ^ t := by
    intro t; simp only [plannerW, affineCornerPath]; rw [mul_pow]; ring
  simp only [pathValue]
  rw [tsum_congr hzero, tsum_congr hcorner, tsum_mul_left,
    (hg1.mul_left _).tsum_sub (hg2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hb0 hb1, tsum_geometric_of_lt_one hbg0 hbg1]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have h2 : (1 : ℝ) - β * (1 - δ) ≠ 0 := by linarith
  field_simp
  ring

/-- **The exact sign of the affine gap at a fixed planner discount**:
`V⁰ − Vᴱ > 0` iff `H(1 − β(1 − δ)) + B(1 − β) > 0` (equivalently
`C(1 − β + βδ) > Bβδ`). The conjunction `H > 0 ∧ B ≥ 0` is sufficient and not
necessary: `H = 0, B > 0` gives a positive transient gain, and a negative `B`
is compatible with a positive gap.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; affine-restricted (Rule 22). -/
theorem affineCornerGap_pos_iff {δ β : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    0 < G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
        - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1)
      ↔ 0 < ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) * (1 - β * (1 - δ))
          + (G.b_J - G.b_K) * (1 - β) := by
  rw [G.pathValue_affineCorner_gap hδ hβ x0]
  have h1 : (0 : ℝ) < 1 - β := by linarith [hβ.2]
  have h2 : (0 : ℝ) < 1 - β * (1 - δ) := by
    have : β * (1 - δ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right hβ.1 (by linarith [hδ.1])) hβ.2
    linarith
  have key : ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * (1 - δ))
      = (((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) * (1 - β * (1 - δ))
          + (G.b_J - G.b_K) * (1 - β)) / ((1 - β) * (1 - β * (1 - δ))) := by
    rw [div_add_div _ _ h1.ne' h2.ne']
    ring
  rw [key, div_pos_iff_of_pos_right (mul_pos h1 h2)]

/-- **The exact sign of the affine gap at every planner discount**: the zero
path beats the corner path for every `β ∈ [0,1)` iff `C > 0` and `H ≥ 0`, i.e.
`k_S + d_s > g_J − q_K` and `k_S + d_s ≥ (g_J − q_K) + (b_J − b_K)`. At `β = 0`
the gap is `C`; as `β → 1` the numerator tends to `Hδ`; conversely the
numerator is `C(1 − β) + Hβδ`. Neither inequality follows from region (R):
`Examples/FourGroupWelfareSign.lean` gives a region-(R) polity with the same
government payoffs as `fourGroupCert` and `C < 0` (Rule 11: the refutation
was built before this characterization was proved).
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; affine-restricted (Rule 22). -/
theorem affineCornerGap_pos_all_discounts_iff {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : ℝ) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ 0 ≤ (G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) := by
  set H := (G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K) with hH
  set B := G.b_J - G.b_K with hB
  have hiff : ∀ β ∈ Set.Ico (0 : ℝ) 1,
      (0 < G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
            - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1))
        ↔ 0 < H * (1 - β * (1 - δ)) + B * (1 - β) :=
    fun β hβ => G.affineCornerGap_pos_iff hδ hβ x0
  have hC : (G.kS + G.d_s) - (G.g_J - G.q_K) = H + B := by rw [hH, hB]; ring
  rw [hC]
  constructor
  · intro h
    have h0 : 0 < H * (1 - 0 * (1 - δ)) + B * (1 - 0) :=
      (hiff 0 ⟨le_rfl, by norm_num⟩).mp (h 0 ⟨le_rfl, by norm_num⟩)
    have hHB : 0 < H + B := by linarith [h0]
    refine ⟨hHB, ?_⟩
    by_contra hneg'
    have hneg : H < 0 := not_le.mp hneg'
    have hden : 0 < H + B - H * δ := by nlinarith [hδ.1]
    have hne : H + B - H * δ ≠ 0 := hden.ne'
    set β₀ := (H + B) / (H + B - H * δ) with hβ₀
    have hβ₀0 : 0 < β₀ := div_pos hHB hden
    have hβ₀1 : β₀ < 1 := (div_lt_one hden).mpr (by nlinarith [hδ.1])
    set β := (β₀ + 1) / 2 with hβdef
    have hβmem : β ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hN := (hiff β hβmem).mp (h β hβmem)
    have hmul : (H + B - H * δ) * β₀ = H + B := by
      rw [hβ₀]; field_simp
    have hkey : H * (1 - β * (1 - δ)) + B * (1 - β) = (H + B - H * δ) * (β₀ - β) := by
      linear_combination -hmul
    have hlt : β₀ - β < 0 := by linarith
    have : (H + B - H * δ) * (β₀ - β) < 0 := mul_neg_of_pos_of_neg hden hlt
    linarith
  · rintro ⟨hHB, hH0⟩ β hβ
    rw [hiff β hβ]
    have h1 : 0 < 1 - β := by linarith [hβ.2]
    nlinarith [mul_pos hHB h1, mul_nonneg (mul_nonneg hH0 hβ.1) hδ.1.le]

end FourGroupCoeffs

namespace FourGroup

variable (G : FourGroup)

/-- **Per-period gap on the affine corner paths**. The `FourGroup` form of
`FourGroupCoeffs.plannerW_affineCorner_gap`, by `rfl` through `toCoeffs` (BH6.2);
statement unchanged; affine-restricted (Rule 22). -/
theorem plannerW_affineCorner_gap (δ x0 : ℝ) (t : ℕ) :
    G.plannerW (affineZeroPath δ x0 t) 0 0 - G.plannerW (affineCornerPath δ x0 t) 0 1
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K))
        + (G.b_J - G.b_K) * (1 - δ) ^ t :=
  G.toCoeffs.plannerW_affineCorner_gap δ x0 t

/-- **The discounted affine gap in primitives**. The `FourGroup` form of
`FourGroupCoeffs.pathValue_affineCorner_gap`, by `rfl` through `toCoeffs` (BH6.2);
statement unchanged; affine-restricted (Rule 22). -/
theorem pathValue_affineCorner_gap {δ β : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * (1 - δ)) :=
  G.toCoeffs.pathValue_affineCorner_gap hδ hβ x0

/-- **The exact sign of the affine gap at a fixed planner discount**. The
conjunction `H > 0 ∧ B ≥ 0` is sufficient and not necessary (see the coefficient
form for the scope note). The `FourGroup` form of
`FourGroupCoeffs.affineCornerGap_pos_iff`, by `rfl` through `toCoeffs` (BH6.2);
statement unchanged; affine-restricted (Rule 22). -/
theorem affineCornerGap_pos_iff {δ β : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1) (x0 : ℝ) :
    0 < G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
        - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1)
      ↔ 0 < ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) * (1 - β * (1 - δ))
          + (G.b_J - G.b_K) * (1 - β) :=
  G.toCoeffs.affineCornerGap_pos_iff hδ hβ x0

/-- **The exact sign of the affine gap at every planner discount**. Neither
inequality follows from region (R): `Examples/FourGroupWelfareSign.lean` gives a
region-(R) polity with the same government payoffs as `fourGroupCert` and `C < 0`.
The `FourGroup` form of `FourGroupCoeffs.affineCornerGap_pos_all_discounts_iff`, by
`rfl` through `toCoeffs` (BH6.2); statement unchanged; affine-restricted (Rule 22).
-/
theorem affineCornerGap_pos_all_discounts_iff {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (x0 : ℝ) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (affineZeroPath δ x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (affineCornerPath δ x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ 0 ≤ (G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) :=
  G.toCoeffs.affineCornerGap_pos_all_discounts_iff hδ x0

end FourGroup

/-! ## 3. The same accounting under a general transition (Rule 22)

The closed forms above are affine. The accounting identity is not: for any
transition that keeps the cube, is monotone in both arguments and fixes the
diagonal — the `Params` transition fields, nothing more — the two endpoint
paths are ordered, the residual `z_t = 1 − e_t + y_t` lies in `[0,1]` with
`z_0 = 1`, and the discounted gap is `H/(1 − β) + B·Σ_t β^t z_t`. Two lower
bounds follow from `1 ≤ Σ β^t z_t ≤ 1/(1 − β)`, one for each sign of `B`; the
affine formula is the case `z_t = (1 − δ)^t` (`cornerPathF_affineF`). A lower
*sanction* chord bounds `Σ β^t z_t` from above and gives no lower bound for
`B ≥ 0`; a lower *state* chord on the two endpoint sections would sharpen the
`B ≥ 0` bound to `H/(1−β) + B/(1−βg)` (round BD:
`pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords`, in
`FourGroupPlannerStateChord.lean`). -/

/-- The recursive full-sanction state path from `x0` under a transition `F`:
`e_0 = x0`, `e_{t+1} = F(e_t, 1)`. -/
def cornerPathF (F : ℝ → ℝ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => F (cornerPathF F x0 t) 1

/-- The recursive zero-sanction state path from `x0` under `F`:
`y_0 = x0`, `y_{t+1} = F(y_t, 0)`. -/
def zeroPathF (F : ℝ → ℝ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => F (zeroPathF F x0 t) 0

@[simp] theorem cornerPathF_zero (F : ℝ → ℝ → ℝ) (x0 : ℝ) : cornerPathF F x0 0 = x0 := rfl

@[simp] theorem cornerPathF_succ (F : ℝ → ℝ → ℝ) (x0 : ℝ) (t : ℕ) :
    cornerPathF F x0 (t + 1) = F (cornerPathF F x0 t) 1 := rfl

@[simp] theorem zeroPathF_zero (F : ℝ → ℝ → ℝ) (x0 : ℝ) : zeroPathF F x0 0 = x0 := rfl

@[simp] theorem zeroPathF_succ (F : ℝ → ℝ → ℝ) (x0 : ℝ) (t : ℕ) :
    zeroPathF F x0 (t + 1) = F (zeroPathF F x0 t) 0 := rfl

/-- The general recursion specialises to the affine closed form. -/
theorem cornerPathF_affineF (δ x0 : ℝ) :
    cornerPathF (AbstractGame.affineF δ) x0 = affineCornerPath δ x0 := by
  funext t
  induction t with
  | zero => simp
  | succ t ih => rw [cornerPathF_succ, ih, affineCornerPath_step]

theorem zeroPathF_affineF (δ x0 : ℝ) :
    zeroPathF (AbstractGame.affineF δ) x0 = affineZeroPath δ x0 := by
  funext t
  induction t with
  | zero => simp
  | succ t ih => rw [zeroPathF_succ, ih, affineZeroPath_step]

theorem cornerPathF_mem_cube {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) : ∀ t, cornerPathF F x0 t ∈ Set.Icc (0 : ℝ) 1
  | 0 => hx0
  | t + 1 => hF_mem _ _ (cornerPathF_mem_cube hF_mem hx0 t) ⟨zero_le_one, le_rfl⟩

theorem zeroPathF_mem_cube {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) : ∀ t, zeroPathF F x0 t ∈ Set.Icc (0 : ℝ) 1
  | 0 => hx0
  | t + 1 => hF_mem _ _ (zeroPathF_mem_cube hF_mem hx0 t) ⟨le_rfl, zero_le_one⟩

/-- Under coordinatewise monotonicity the zero path never overtakes the corner
path: `y_t ≤ e_t`. -/
theorem zeroPathF_le_cornerPathF {F : ℝ → ℝ → ℝ}
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s)) (x0 : ℝ) :
    ∀ t, zeroPathF F x0 t ≤ cornerPathF F x0 t
  | 0 => le_rfl
  | t + 1 => by
      have h1 : F (zeroPathF F x0 t) 0 ≤ F (cornerPathF F x0 t) 0 :=
        hF_mono_x 0 (zeroPathF_le_cornerPathF hF_mono_x hF_mono_s x0 t)
      have h2 : F (cornerPathF F x0 t) 0 ≤ F (cornerPathF F x0 t) 1 :=
        hF_mono_s (cornerPathF F x0 t) zero_le_one
      exact h1.trans h2

/-- The residual separation `z_t = 1 − e_t + y_t` of the two endpoint paths. -/
def residualF (F : ℝ → ℝ → ℝ) (x0 : ℝ) (t : ℕ) : ℝ :=
  1 - cornerPathF F x0 t + zeroPathF F x0 t

@[simp] theorem residualF_zero (F : ℝ → ℝ → ℝ) (x0 : ℝ) : residualF F x0 0 = 1 := by
  simp [residualF]

theorem residualF_mem {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    residualF F x0 t ∈ Set.Icc (0 : ℝ) 1 := by
  have he := cornerPathF_mem_cube hF_mem hx0 t
  have hy := zeroPathF_mem_cube hF_mem hx0 t
  have hle := zeroPathF_le_cornerPathF hF_mono_x hF_mono_s x0 t
  constructor <;> simp only [residualF] <;> linarith [he.1, he.2, hy.1, hy.2]

theorem residualF_summable {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun t : ℕ => β ^ t * residualF F x0 t) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => β ^ t)
    (summable_geometric_of_lt_one hβ.1 hβ.2) ?_
  intro t
  have hzt := residualF_mem hF_mem hF_mono_x hF_mono_s hx0 t
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.1, abs_of_nonneg hzt.1]
  exact mul_le_of_le_one_right (pow_nonneg hβ.1 t) hzt.2

/-- `1 ≤ Σ_t β^t z_t`: the date-zero term is one and the rest are nonnegative. -/
theorem one_le_tsum_residualF {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ ∑' t : ℕ, β ^ t * residualF F x0 t := by
  have hz := residualF_summable hF_mem hF_mono_x hF_mono_s hβ hx0
  have h0 : β ^ 0 * residualF F x0 0 = 1 := by simp
  calc (1 : ℝ) = β ^ 0 * residualF F x0 0 := h0.symm
    _ ≤ ∑' t : ℕ, β ^ t * residualF F x0 t :=
      hz.le_tsum 0 (fun j _ =>
        mul_nonneg (pow_nonneg hβ.1 j) (residualF_mem hF_mem hF_mono_x hF_mono_s hx0 j).1)

/-- `Σ_t β^t z_t ≤ 1/(1 − β)`: every residual is at most one. -/
theorem tsum_residualF_le {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    ∑' t : ℕ, β ^ t * residualF F x0 t ≤ 1 / (1 - β) := by
  have hz := residualF_summable hF_mem hF_mono_x hF_mono_s hβ hx0
  have hg : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.1 hβ.2
  calc ∑' t : ℕ, β ^ t * residualF F x0 t ≤ ∑' t : ℕ, β ^ t :=
        hz.tsum_le_tsum (fun t => mul_le_of_le_one_right (pow_nonneg hβ.1 t)
          (residualF_mem hF_mem hF_mono_x hF_mono_s hx0 t).2) hg
    _ = 1 / (1 - β) := by rw [tsum_geometric_of_lt_one hβ.1 hβ.2, one_div]

namespace FourGroupCoeffs

variable (G : FourGroupCoeffs)

/-- **Per-period gap on the general endpoint paths**: `H + B·z_t`. Algebra.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem plannerW_cornerF_gap (F : ℝ → ℝ → ℝ) (x0 : ℝ) (t : ℕ) :
    G.plannerW (zeroPathF F x0 t) 0 0 - G.plannerW (cornerPathF F x0 t) 0 1
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K))
        + (G.b_J - G.b_K) * residualF F x0 t := by
  simp only [plannerW, residualF]; ring

/-- **The discounted gap under a general transition** (general in `F`):
`V⁰ − Vᴱ = H/(1 − β) + B·Σ_t β^t z_t`, from the `Params` transition fields
alone — no closed form, no chord, no strict adjustment.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t := by
  have hsum0 : Summable (fun t : ℕ => β ^ t * G.plannerW (zeroPathF F x0 t) 0 0) :=
    G.pathValue_summable hβ (zeroPathF_mem_cube hF_mem hx0) (fun _ => by norm_num)
      (fun _ => by norm_num)
  have hsum1 : Summable (fun t : ℕ => β ^ t * G.plannerW (cornerPathF F x0 t) 0 1) :=
    G.pathValue_summable hβ (cornerPathF_mem_cube hF_mem hx0) (fun _ => by norm_num)
      (fun _ => by norm_num)
  have hg : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.1 hβ.2
  have hz := residualF_summable hF_mem hF_mono_x hF_mono_s hβ hx0
  have hterm : ∀ t : ℕ, β ^ t * G.plannerW (zeroPathF F x0 t) 0 0
      - β ^ t * G.plannerW (cornerPathF F x0 t) 0 1
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) * β ^ t
        + (G.b_J - G.b_K) * (β ^ t * residualF F x0 t) := by
    intro t; rw [← mul_sub, G.plannerW_cornerF_gap]; ring
  simp only [pathValue]
  rw [← hsum0.tsum_sub hsum1, tsum_congr hterm, (hg.mul_left _).tsum_add (hz.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hβ.1 hβ.2]
  ring

/-- **Lower bound for a nonnegative transition coefficient**: when `B ≥ 0`,
`V⁰ − Vᴱ ≥ H/(1 − β) + B` (the date-zero residual alone).
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap_ge_of_nonneg {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hB : 0 ≤ G.b_J - G.b_K) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β) + (G.b_J - G.b_K)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) := by
  rw [G.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0]
  have h1 := one_le_tsum_residualF hF_mem hF_mono_x hF_mono_s hβ hx0
  nlinarith [mul_le_mul_of_nonneg_left h1 hB]

/-- **Lower bound for a negative transition coefficient**: when `B < 0`,
`V⁰ − Vᴱ ≥ C/(1 − β)` (the residual sum is at most `1/(1 − β)` and the
multiplication reverses). The sign of `B` cannot be suppressed in a general
statement.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap_ge_of_neg {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hB : G.b_J - G.b_K < 0) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K)) / (1 - β)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) := by
  rw [G.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0]
  have hS := tsum_residualF_le hF_mem hF_mono_x hF_mono_s hβ hx0
  have hmul : (G.b_J - G.b_K) * (1 / (1 - β))
      ≤ (G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t :=
    mul_le_mul_of_nonpos_left hS hB.le
  have key : ((G.kS + G.d_s) - (G.g_J - G.q_K)) / (1 - β)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) * (1 / (1 - β)) := by ring
  linarith

end FourGroupCoeffs

namespace FourGroup

variable (G : FourGroup)

/-- **Per-period gap on the general endpoint paths**. The `FourGroup` form of
`FourGroupCoeffs.plannerW_cornerF_gap`, by `rfl` through `toCoeffs` (BH6.2);
statement unchanged; general in `F`. -/
theorem plannerW_cornerF_gap (F : ℝ → ℝ → ℝ) (x0 : ℝ) (t : ℕ) :
    G.plannerW (zeroPathF F x0 t) 0 0 - G.plannerW (cornerPathF F x0 t) 0 1
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K))
        + (G.b_J - G.b_K) * residualF F x0 t :=
  G.toCoeffs.plannerW_cornerF_gap F x0 t

/-- **The discounted gap under a general transition**. The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap`, by `rfl` through `toCoeffs` (BH6.2);
statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t :=
  G.toCoeffs.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0

/-- **Lower bound for a nonnegative transition coefficient**. The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_ge_of_nonneg`, by `rfl` through `toCoeffs`
(BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_ge_of_nonneg {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hB : 0 ≤ G.b_J - G.b_K) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β) + (G.b_J - G.b_K)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) :=
  G.toCoeffs.pathValue_cornerF_gap_ge_of_nonneg hF_mem hF_mono_x hF_mono_s hβ hx0 hB

/-- **Lower bound for a negative transition coefficient**. The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_ge_of_neg`, by `rfl` through `toCoeffs`
(BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_ge_of_neg {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1)
    (hB : G.b_J - G.b_K < 0) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K)) / (1 - β)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) :=
  G.toCoeffs.pathValue_cornerF_gap_ge_of_neg hF_mem hF_mono_x hF_mono_s hβ hx0 hB

end FourGroup

/-! ### Strict adjustment: the endpoint paths converge, and the all-discount sign
(round U, 2026-09-15; doc 87 W6)

A positive lower sanction chord — the family's `dlo > 0`, the existing
predicate `SanctionLowerChord` — is strict adjustment: at every state the
full sanction moves the state up by at least `dlo·(1 − x)` and the zero
sanction moves it down by at least `dlo·x`. The corner path then converges to
one and the zero path to zero geometrically, the separation `d_t = e_t − y_t`
tends to one, and the Foundations characterization
(`DiscountedSign.tsum_pos_all_discounts_iff`) turns the general-transition
identity into the same all-discount sign condition as the affine case,
`C > 0 ∧ B ≤ C`, with no affine rate and no quantitative chord beyond
`dlo > 0`. Without strict adjustment the necessity direction fails: the
identity transition keeps both paths at the start, the residual stays one,
and the gap is `C/(1 − β)` whatever `B` is (`pathValue_cornerF_gap_of_identity`,
`not_necessary_without_strict_adjustment`). -/

open Sanctions.TransitionChords in
/-- A lower sanction chord is at most one: the chord at the state `0` between
the sanctions `0` and `1` cannot exceed the cube. -/
theorem sanctionLowerChord_le_one {F : ℝ → ℝ → ℝ} {dlo : ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_diag : ∀ x, F x x = x) (hlo : SanctionLowerChord F dlo) : dlo ≤ 1 := by
  have h := hlo (x := 0) (s₁ := 0) (s₂ := 1) ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ zero_le_one
  have h1 := (hF_mem 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).2
  rw [hF_diag 0] at h
  linarith

open Sanctions.TransitionChords in
/-- Under a lower sanction chord the corner path closes the gap to one
geometrically: `1 − e_t ≤ (1 − dlo)^t (1 − x0)`. -/
theorem one_sub_cornerPathF_le {F : ℝ → ℝ → ℝ} {dlo : ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_diag : ∀ x, F x x = x) (hlo : SanctionLowerChord F dlo)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t, 1 - cornerPathF F x0 t ≤ (1 - dlo) ^ t * (1 - x0)
  | 0 => by simp
  | t + 1 => by
      have hdlo1 := sanctionLowerChord_le_one hF_mem hF_diag hlo
      have he := cornerPathF_mem_cube hF_mem hx0 t
      have hstep := hlo he he ⟨zero_le_one, le_rfl⟩ he.2
      rw [hF_diag] at hstep
      have ih := one_sub_cornerPathF_le hF_mem hF_diag hlo hx0 t
      rw [cornerPathF_succ, pow_succ]
      have hγ : 0 ≤ 1 - dlo := by linarith
      nlinarith [mul_le_mul_of_nonneg_left ih hγ]

open Sanctions.TransitionChords in
/-- Under a lower sanction chord the zero path decays geometrically:
`y_t ≤ (1 − dlo)^t x0`. -/
theorem zeroPathF_le {F : ℝ → ℝ → ℝ} {dlo : ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_diag : ∀ x, F x x = x) (hlo : SanctionLowerChord F dlo)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t, zeroPathF F x0 t ≤ (1 - dlo) ^ t * x0
  | 0 => by simp
  | t + 1 => by
      have hdlo1 := sanctionLowerChord_le_one hF_mem hF_diag hlo
      have hy := zeroPathF_mem_cube hF_mem hx0 t
      have hstep := hlo hy ⟨le_rfl, zero_le_one⟩ hy hy.1
      rw [hF_diag] at hstep
      have ih := zeroPathF_le hF_mem hF_diag hlo hx0 t
      rw [zeroPathF_succ, pow_succ]
      have hγ : 0 ≤ 1 - dlo := by linarith
      nlinarith [mul_le_mul_of_nonneg_left ih hγ]

open Sanctions.TransitionChords Filter Topology in
/-- **Strict adjustment separates the endpoint paths completely**: with a
positive lower sanction chord, `e_t − y_t → 1`. -/
theorem separationF_tendsto_one {F : ℝ → ℝ → ℝ} {dlo : ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) (hlo : SanctionLowerChord F dlo) (hdlo : 0 < dlo)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun t : ℕ => cornerPathF F x0 t - zeroPathF F x0 t) atTop (𝓝 1) := by
  have hdlo1 := sanctionLowerChord_le_one hF_mem hF_diag hlo
  have hγ0 : 0 ≤ 1 - dlo := by linarith
  have hγ1 : 1 - dlo < 1 := by linarith
  have hpow : Tendsto (fun t : ℕ => (1 - dlo) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
  have hlow : Tendsto (fun t : ℕ => 1 - (1 - dlo) ^ t) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hpow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro t
    have h1 := one_sub_cornerPathF_le hF_mem hF_diag hlo hx0 t
    have h2 := zeroPathF_le hF_mem hF_diag hlo hx0 t
    simp only
    nlinarith
  · intro t
    have := (residualF_mem hF_mem hF_mono_x hF_mono_s hx0 t).1
    simp only [residualF] at this
    simp only
    linarith

/-! ### Qualitative strict adjustment suffices (round X, 2026-09-17; the reader's
P4 of 2026-09-16)

The chord `dlo > 0` above is a *uniform speed* of adjustment. The paper's
maintained class (F5) asks only for the *direction*: the full sanction strictly
raises every state below one and the zero sanction strictly lowers every
positive state (`Params.StrictAdjustment`). With the continuity of `F` that the
class already carries, direction is enough for the endpoint paths to converge:
the corner path is monotone and bounded, its limit is a fixed point of `F(·,1)`,
and strict adjustment leaves only `1`; symmetrically the zero path converges to
`0`. The separation therefore still tends to one and the all-discount sign
condition is unchanged. What is lost is the geometric rate, which no sign
statement uses. The `Params` form at the end consumes nothing beyond the
structure's own fields and `StrictAdjustment`. -/

open Filter Topology in
/-- Under continuity and strict upward adjustment at the full sanction the corner
path converges to one. -/
theorem cornerPathF_tendsto_one_of_strictAdjust {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x)
    (hF_cont : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hup : ∀ x ∈ Set.Icc (0 : ℝ) 1, x < 1 → x < F x 1)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (cornerPathF F x0) atTop (𝓝 1) := by
  have hmem := cornerPathF_mem_cube hF_mem hx0
  have hmono : Monotone (cornerPathF F x0) := by
    refine monotone_nat_of_le_succ fun t => ?_
    rw [cornerPathF_succ]
    calc cornerPathF F x0 t = F (cornerPathF F x0 t) (cornerPathF F x0 t) := (hF_diag _).symm
      _ ≤ F (cornerPathF F x0 t) 1 := hF_mono_s _ (hmem t).2
  have hbdd : BddAbove (Set.range (cornerPathF F x0)) :=
    ⟨1, by rintro _ ⟨t, rfl⟩; exact (hmem t).2⟩
  have hlim : Tendsto (cornerPathF F x0) atTop (𝓝 (⨆ t, cornerPathF F x0 t)) :=
    tendsto_atTop_ciSup hmono hbdd
  have hzmem : (⨆ t, cornerPathF F x0 t) ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  have hfix : F (⨆ t, cornerPathF F x0 t) 1 = ⨆ t, cornerPathF F x0 t := by
    have h1 : Tendsto (fun t => F (cornerPathF F x0 t) 1) atTop
        (𝓝 (F (⨆ t, cornerPathF F x0 t) 1)) :=
      (hF_cont.tendsto (⨆ t, cornerPathF F x0 t, 1)).comp (hlim.prodMk_nhds tendsto_const_nhds)
    have h2 : Tendsto (fun t => F (cornerPathF F x0 t) 1) atTop
        (𝓝 (⨆ t, cornerPathF F x0 t)) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, cornerPathF_succ] using this
    exact tendsto_nhds_unique h1 h2
  have hz1 : (⨆ t, cornerPathF F x0 t) = 1 := by
    by_contra hne
    have hlt : (⨆ t, cornerPathF F x0 t) < 1 := lt_of_le_of_ne hzmem.2 hne
    have := hup _ hzmem hlt
    rw [hfix] at this
    exact lt_irrefl _ this
  rw [hz1] at hlim
  exact hlim

open Filter Topology in
/-- Under continuity and strict downward adjustment at the zero sanction the zero
path converges to zero. -/
theorem zeroPathF_tendsto_zero_of_strictAdjust {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x)
    (hF_cont : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hdown : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < x → F x 0 < x)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (zeroPathF F x0) atTop (𝓝 0) := by
  have hmem := zeroPathF_mem_cube hF_mem hx0
  have hanti : Antitone (zeroPathF F x0) := by
    refine antitone_nat_of_succ_le fun t => ?_
    rw [zeroPathF_succ]
    calc F (zeroPathF F x0 t) 0 ≤ F (zeroPathF F x0 t) (zeroPathF F x0 t) :=
          hF_mono_s _ (hmem t).1
      _ = zeroPathF F x0 t := hF_diag _
  have hbdd : BddBelow (Set.range (zeroPathF F x0)) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩
  have hlim : Tendsto (zeroPathF F x0) atTop (𝓝 (⨅ t, zeroPathF F x0 t)) :=
    tendsto_atTop_ciInf hanti hbdd
  have hzmem : (⨅ t, zeroPathF F x0 t) ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  have hfix : F (⨅ t, zeroPathF F x0 t) 0 = ⨅ t, zeroPathF F x0 t := by
    have h1 : Tendsto (fun t => F (zeroPathF F x0 t) 0) atTop
        (𝓝 (F (⨅ t, zeroPathF F x0 t) 0)) :=
      (hF_cont.tendsto (⨅ t, zeroPathF F x0 t, 0)).comp (hlim.prodMk_nhds tendsto_const_nhds)
    have h2 : Tendsto (fun t => F (zeroPathF F x0 t) 0) atTop
        (𝓝 (⨅ t, zeroPathF F x0 t)) := by
      have := hlim.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, zeroPathF_succ] using this
    exact tendsto_nhds_unique h1 h2
  have hz0 : (⨅ t, zeroPathF F x0 t) = 0 := by
    by_contra hne
    have hpos : 0 < ⨅ t, zeroPathF F x0 t := lt_of_le_of_ne hzmem.1 (Ne.symm hne)
    have := hdown _ hzmem hpos
    rw [hfix] at this
    exact lt_irrefl _ this
  rw [hz0] at hlim
  exact hlim

open Filter Topology in
/-- **Direction alone separates the endpoint paths completely**: under continuity
and strict adjustment in both directions, `e_t − y_t → 1`. -/
theorem separationF_tendsto_one_of_strictAdjust {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x)
    (hF_cont : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hup : ∀ x ∈ Set.Icc (0 : ℝ) 1, x < 1 → x < F x 1)
    (hdown : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < x → F x 0 < x)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun t : ℕ => cornerPathF F x0 t - zeroPathF F x0 t) atTop (𝓝 1) := by
  simpa using
    (cornerPathF_tendsto_one_of_strictAdjust hF_mem hF_mono_s hF_diag hF_cont hup hx0).sub
      (zeroPathF_tendsto_zero_of_strictAdjust hF_mem hF_mono_s hF_diag hF_cont hdown hx0)

namespace FourGroupCoeffs

variable (G : FourGroupCoeffs)

/-- The general-transition gap as a single discounted series in the separation
`d_t = e_t − y_t`: `V⁰ − Vᴱ = Σ β^t (C − B d_t)`.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap_eq_tsum {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ∑' t : ℕ, β ^ t * (((G.kS + G.d_s) - (G.g_J - G.q_K))
          - (G.b_J - G.b_K) * (cornerPathF F x0 t - zeroPathF F x0 t)) := by
  rw [G.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0]
  have hz := residualF_summable hF_mem hF_mono_x hF_mono_s hβ hx0
  have hg : Summable (fun t : ℕ => β ^ t) := summable_geometric_of_lt_one hβ.1 hβ.2
  have hterm : ∀ t : ℕ, β ^ t * (((G.kS + G.d_s) - (G.g_J - G.q_K))
        - (G.b_J - G.b_K) * (cornerPathF F x0 t - zeroPathF F x0 t))
      = ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) * β ^ t
        + (G.b_J - G.b_K) * (β ^ t * residualF F x0 t) := by
    intro t; simp only [residualF]; ring
  rw [tsum_congr hterm, (hg.mul_left _).tsum_add (hz.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one hβ.1 hβ.2]
  ring

open Sanctions.TransitionChords in
/-- **The all-discount sign under a general transition with strict adjustment**
(general in `F`; the affine rate plays no role): with a positive lower sanction
chord, the zero path beats the corner path at every planner discount iff
`C > 0` and `B ≤ C`, i.e. `k_S + d_s > g_J − q_K` and
`(g_J − q_K) + (b_J − b_K) ≤ k_S + d_s` — the same condition as
`affineCornerGap_pos_all_discounts_iff`.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap_pos_all_discounts_iff {F : ℝ → ℝ → ℝ} {dlo : ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) (hlo : SanctionLowerChord F dlo) (hdlo : 0 < dlo)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ (G.b_J - G.b_K) ≤ (G.kS + G.d_s) - (G.g_J - G.q_K)) := by
  have hd0 : cornerPathF F x0 0 - zeroPathF F x0 0 = 0 := by simp
  have hd : ∀ t, cornerPathF F x0 t - zeroPathF F x0 t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    have := residualF_mem hF_mem hF_mono_x hF_mono_s hx0 t
    simp only [residualF] at this
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hlim := separationF_tendsto_one hF_mem hF_mono_x hF_mono_s hF_diag hlo hdlo hx0
  have key := DiscountedSign.tsum_pos_all_discounts_iff
    (C := (G.kS + G.d_s) - (G.g_J - G.q_K)) (B := G.b_J - G.b_K)
    (d := fun t => cornerPathF F x0 t - zeroPathF F x0 t) hd0 hd hlim
  rw [← key]
  constructor
  · intro h β hβ
    rw [← G.pathValue_cornerF_gap_eq_tsum hF_mem hF_mono_x hF_mono_s hβ hx0]
    exact h β hβ
  · intro h β hβ
    rw [G.pathValue_cornerF_gap_eq_tsum hF_mem hF_mono_x hF_mono_s hβ hx0]
    exact h β hβ

/-- **The all-discount sign under qualitative strict adjustment** (general in
`F`; no rate, no chord): with continuity and the two strict-adjustment
directions, the zero path beats the corner path at every planner discount iff
`C > 0` and `B ≤ C`. Same condition as the chord form and the affine form.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap_pos_all_discounts_iff_of_strictAdjust {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x)
    (hF_cont : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hup : ∀ x ∈ Set.Icc (0 : ℝ) 1, x < 1 → x < F x 1)
    (hdown : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < x → F x 0 < x)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ (G.b_J - G.b_K) ≤ (G.kS + G.d_s) - (G.g_J - G.q_K)) := by
  have hd0 : cornerPathF F x0 0 - zeroPathF F x0 0 = 0 := by simp
  have hd : ∀ t, cornerPathF F x0 t - zeroPathF F x0 t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    have := residualF_mem hF_mem hF_mono_x hF_mono_s hx0 t
    simp only [residualF] at this
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hlim := separationF_tendsto_one_of_strictAdjust hF_mem hF_mono_s hF_diag hF_cont
    hup hdown hx0
  have key := DiscountedSign.tsum_pos_all_discounts_iff
    (C := (G.kS + G.d_s) - (G.g_J - G.q_K)) (B := G.b_J - G.b_K)
    (d := fun t => cornerPathF F x0 t - zeroPathF F x0 t) hd0 hd hlim
  rw [← key]
  constructor
  · intro h β hβ
    rw [← G.pathValue_cornerF_gap_eq_tsum hF_mem hF_mono_x hF_mono_s hβ hx0]
    exact h β hβ
  · intro h β hβ
    rw [G.pathValue_cornerF_gap_eq_tsum hF_mem hF_mono_x hF_mono_s hβ hx0]
    exact h β hβ

/-- **On the paper's maintained class (F1)--(F5).** For any economy `p : Params`
with strict adjustment, the transition `p.F` supplies every hypothesis of the
previous theorem from the structure's own fields — the cube is kept, both
monotonicities, the diagonal, continuity — and `StrictAdjustment` supplies the
two directions. Nothing else is assumed.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; general in `F`. -/
theorem pathValue_cornerF_gap_pos_all_discounts_iff_of_params
    (p : Sanctions.AbstractGame.Params) (hsa : p.StrictAdjustment)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (zeroPathF p.F x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (cornerPathF p.F x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ (G.b_J - G.b_K) ≤ (G.kS + G.d_s) - (G.g_J - G.q_K)) :=
  G.pathValue_cornerF_gap_pos_all_discounts_iff_of_strictAdjust
    p.F_mem p.F_mono_x p.F_mono_s p.F_diag p.F_continuous
    (fun _ hx hlt => hsa.self_lt_F_one ⟨hx.1, hlt⟩)
    (fun _ hx hpos => hsa.F_zero_lt_self hx hpos) hx0

/-- **Refutation boundary (Rule 11)**: the identity transition `F(x,s) = x`
keeps the cube, is monotone in both arguments and fixes the diagonal, but does
not adjust. Both endpoint paths stay at the start, the residual is one, and
the gap is `C/(1 − β)` whatever `B` is.
Coefficient form (BH6.2, 2026-10-07): no region-(R) field is assumed, so it holds
for every coefficient vector; stated at the identity transition, the refutation
boundary of the general-`F` characterization. -/
theorem pathValue_cornerF_gap_of_identity {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    G.pathValue β (zeroPathF (fun x _ => x) x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (cornerPathF (fun x _ => x) x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K)) / (1 - β) := by
  have hmem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      (fun x _ => x : ℝ → ℝ → ℝ) x s ∈ Set.Icc (0 : ℝ) 1 := fun x _ hx _ => hx
  have hmx : ∀ s, Monotone (fun x => (fun x _ => x : ℝ → ℝ → ℝ) x s) := fun _ => monotone_id
  have hms : ∀ x, Monotone (fun s => (fun x _ => x : ℝ → ℝ → ℝ) x s) := fun _ => monotone_const
  rw [G.pathValue_cornerF_gap hmem hmx hms hβ hx0]
  have hres : ∀ t, residualF (fun x _ => x) x0 t = 1 := by
    intro t
    have hc : ∀ t, cornerPathF (fun x _ => x) x0 t = x0 := by
      intro t; induction t with
      | zero => rfl
      | succ t ih => rw [cornerPathF_succ, ih]
    have hz : ∀ t, zeroPathF (fun x _ => x) x0 t = x0 := by
      intro t; induction t with
      | zero => rfl
      | succ t ih => rw [zeroPathF_succ, ih]
    simp [residualF, hc, hz]
  simp only [hres, mul_one]
  rw [tsum_geometric_of_lt_one hβ.1 hβ.2]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith [hβ.2]
  field_simp
  ring

end FourGroupCoeffs

namespace FourGroup

variable (G : FourGroup)

/-- The general-transition gap as a single discounted series in the separation
`d_t = e_t − y_t`. The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_eq_tsum`, by `rfl` through `toCoeffs`
(BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_eq_tsum {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = ∑' t : ℕ, β ^ t * (((G.kS + G.d_s) - (G.g_J - G.q_K))
          - (G.b_J - G.b_K) * (cornerPathF F x0 t - zeroPathF F x0 t)) :=
  G.toCoeffs.pathValue_cornerF_gap_eq_tsum hF_mem hF_mono_x hF_mono_s hβ hx0

open Sanctions.TransitionChords in
/-- **The all-discount sign under a general transition with strict adjustment**. The
`FourGroup` form of `FourGroupCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff`,
by `rfl` through `toCoeffs` (BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_pos_all_discounts_iff {F : ℝ → ℝ → ℝ} {dlo : ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) (hlo : SanctionLowerChord F dlo) (hdlo : 0 < dlo)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ (G.b_J - G.b_K) ≤ (G.kS + G.d_s) - (G.g_J - G.q_K)) :=
  G.toCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff hF_mem hF_mono_x hF_mono_s hF_diag
    hlo hdlo hx0

/-- **The all-discount sign under qualitative strict adjustment**. The `FourGroup`
form of
`FourGroupCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff_of_strictAdjust`, by
`rfl` through `toCoeffs` (BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_pos_all_discounts_iff_of_strictAdjust {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x)
    (hF_cont : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hup : ∀ x ∈ Set.Icc (0 : ℝ) 1, x < 1 → x < F x 1)
    (hdown : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < x → F x 0 < x)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ (G.b_J - G.b_K) ≤ (G.kS + G.d_s) - (G.g_J - G.q_K)) :=
  G.toCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff_of_strictAdjust hF_mem hF_mono_x
    hF_mono_s hF_diag hF_cont hup hdown hx0

/-- **On the paper's maintained class (F1)--(F5).** The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff_of_params`, by `rfl`
through `toCoeffs` (BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_pos_all_discounts_iff_of_params
    (p : Sanctions.AbstractGame.Params) (hsa : p.StrictAdjustment)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < G.pathValue β (zeroPathF p.F x0) (fun _ => 0) (fun _ => 0)
              - G.pathValue β (cornerPathF p.F x0) (fun _ => 0) (fun _ => 1))
      ↔ (0 < (G.kS + G.d_s) - (G.g_J - G.q_K)
          ∧ (G.b_J - G.b_K) ≤ (G.kS + G.d_s) - (G.g_J - G.q_K)) :=
  G.toCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff_of_params p hsa hx0

/-- **Refutation boundary (Rule 11)**. The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_of_identity`, by `rfl` through `toCoeffs`
(BH6.2); statement unchanged; stated at the identity transition, the refutation
boundary of the general-`F` characterization. -/
theorem pathValue_cornerF_gap_of_identity {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    G.pathValue β (zeroPathF (fun x _ => x) x0) (fun _ => 0) (fun _ => 0)
      - G.pathValue β (cornerPathF (fun x _ => x) x0) (fun _ => 0) (fun _ => 1)
      = ((G.kS + G.d_s) - (G.g_J - G.q_K)) / (1 - β) :=
  G.toCoeffs.pathValue_cornerF_gap_of_identity hβ hx0

end FourGroup

/-- A polity with `C = 1 < 2 = B` (region (R) holds): under the identity
transition its gap is `1/(1 − β) > 0` at every discount although `B > C`, so
the all-discount characterization needs strict adjustment. -/
def fourGroupIdentityProbe : FourGroup where
  th0_JS := 0
  nu := 1
  g_J := 1
  th0_KS := 0
  q_K := 1
  kS := 1
  w_pl := 0
  base_S := 0
  th0_JT := 0
  rho := 1
  b_J := 3
  c_J := 0
  th0_KT := 0
  mu := 1
  b_K := 1
  c_K := 0
  kT := 0
  d_s := 0
  w_pl_nn := le_rfl
  kS_pos := one_pos
  senderRally_pos := by norm_num
  rally_dom := by norm_num

theorem not_necessary_without_strict_adjustment {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ β ∈ Set.Ico (0 : ℝ) 1,
        0 < fourGroupIdentityProbe.pathValue β (zeroPathF (fun x _ => x) x0)
                (fun _ => 0) (fun _ => 0)
              - fourGroupIdentityProbe.pathValue β (cornerPathF (fun x _ => x) x0)
                  (fun _ => 0) (fun _ => 1))
      ∧ ¬ ((fourGroupIdentityProbe.b_J - fourGroupIdentityProbe.b_K)
            ≤ (fourGroupIdentityProbe.kS + fourGroupIdentityProbe.d_s)
              - (fourGroupIdentityProbe.g_J - fourGroupIdentityProbe.q_K)) := by
  refine ⟨fun β hβ => ?_, ?_⟩
  · rw [fourGroupIdentityProbe.pathValue_cornerF_gap_of_identity hβ hx0]
    simp only [fourGroupIdentityProbe]
    exact div_pos (by norm_num) (by linarith [hβ.2])
  · simp only [fourGroupIdentityProbe]; norm_num

/-! ## 4. The hawk-rescaling family: same game, shifted welfare (BH6.1, 2026-10-07)

`FourGroup.hawkRescale G k hk` (`FourGroupPolity.lean`) multiplies the hawks'
per-unit benefit `g_J` by `k ≠ 0` and divides their weight schedule by `k`; it
induces the same `Params` as `G` under every transition (`hawkRescale_toParamsF`).
The unit-weight planner counts the hawks' benefit `g_J·s` at weight one, so its
flow rises by `(k − 1)·g_J·s` (`hawkRescale_plannerW`), its value along any cube
path by `(k − 1)·g_J·Σ_t β^t s_t` (`hawkRescale_pathValue`), and the gap between
the zero-sanction and the full-sanction paths falls by exactly
`(k − 1)·g_J/(1 − β)` under every transition that keeps the cube
(`hawkRescale_cornerF_gap`). Under every cube-preserving transition monotone in
both arguments the unrescaled gap is bounded by `(|H| + |B|)/(1 − β)`
(`abs_cornerF_gap_le`), so a large enough `k > 0` makes the gap negative when
`g_J > 0` and positive when `g_J < 0`, at every planner discount, every start and
every such transition (`exists_hawkRescale_cornerF_gap_neg`,
`exists_hawkRescale_cornerF_gap_pos`). The government game therefore never
certifies that the zero-sanction path is at least as good for the planner
(gap `≥ 0`) at a polity whose hawks gain from sanctions, nor the reverse
(gap `≤ 0`) at one whose hawks lose. Each statement is one-directional: by the
shift identity, at a polity with `g_J > 0` whose gap is at most `−g_J/(1 − β)` no
member with `k > 0` has a positive gap. Members with `k < 0` are polities too
(`hawkRescale` needs only `k ≠ 0`), but they flip the sign of the hawks' weight
schedule, and nothing here uses them. The certificate witness
`fourGroupCertHawkScaled` is the member `k = 5`
(`Examples/FourGroupWelfareSign.lean`). General in `F` throughout. The rescaling
needs only `k ≠ 0`; the gap identity adds cube preservation of `F`; the bound and
the existence statements add monotonicity of `F` in both arguments, and the
existence statements the sign of `g_J`. -/

namespace FourGroup

variable (G : FourGroup)

/-- **The rescaled planner flow** (BH6.1; no transition enters): the unit-weight
planner of the hawk-rescaled polity counts `(k − 1)·g_J·s` more than that of `G`,
at every triple, because it weights the hawks' benefit `k·g_J·s` by one. -/
theorem hawkRescale_plannerW (k : ℝ) (hk : k ≠ 0) (x a s : ℝ) :
    (G.hawkRescale k hk).plannerW x a s = G.plannerW x a s + (k - 1) * G.g_J * s := by
  simp only [plannerW, hawkRescale]
  ring

/-- **The rescaled path value** (BH6.1; no transition enters): along any
cube-valued path triple, the hawk-rescaled polity's discounted planner value
exceeds that of `G` by `(k − 1)·g_J` times the discounted sanction sum. -/
theorem hawkRescale_pathValue (k : ℝ) (hk : k ≠ 0) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    {xp ap sp : ℕ → ℝ} (hxp : ∀ t, xp t ∈ Set.Icc (0 : ℝ) 1)
    (hap : ∀ t, ap t ∈ Set.Icc (0 : ℝ) 1) (hsp : ∀ t, sp t ∈ Set.Icc (0 : ℝ) 1) :
    (G.hawkRescale k hk).pathValue β xp ap sp
      = G.pathValue β xp ap sp + (k - 1) * G.g_J * ∑' t : ℕ, β ^ t * sp t := by
  have h1 := G.pathValue_summable hβ hxp hap hsp
  have h2 : Summable (fun t : ℕ => β ^ t * sp t) :=
    Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ.1 t) (hsp t).1)
      (fun t => mul_le_of_le_one_right (pow_nonneg hβ.1 t) (hsp t).2)
      (summable_geometric_of_lt_one hβ.1 hβ.2)
  simp only [pathValue]
  rw [← tsum_mul_left, ← h1.tsum_add (h2.mul_left _)]
  refine tsum_congr fun t => ?_
  rw [hawkRescale_plannerW]
  ring

/-- **The gap shift under every transition** (BH6.1; general in `F`): for any
transition that keeps the cube, the zero-sanction-versus-full-sanction planner gap
of the hawk-rescaled polity is the gap of `G` minus `(k − 1)·g_J/(1 − β)`. Only the
full-sanction path collects the extra hawk benefit, one unit of sanction at every
date. No monotonicity, chord or closed form of `F` is used. -/
theorem hawkRescale_cornerF_gap (k : ℝ) (hk : k ≠ 0) {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    (G.hawkRescale k hk).pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
        - (G.hawkRescale k hk).pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)
      = (G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1))
        - (k - 1) * G.g_J / (1 - β) := by
  rw [G.hawkRescale_pathValue k hk hβ (zeroPathF_mem_cube hF_mem hx0)
      (fun _ => by norm_num) (fun _ => by norm_num),
    G.hawkRescale_pathValue k hk hβ (cornerPathF_mem_cube hF_mem hx0)
      (fun _ => by norm_num) (fun _ => by norm_num)]
  simp only [mul_zero, tsum_zero, mul_one]
  rw [tsum_geometric_of_lt_one hβ.1 hβ.2]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith [hβ.2]
  field_simp
  ring

/-- **The gap is bounded by the capitalised coefficients** (general in `F`): under
any transition that keeps the cube and is monotone in both arguments,
`|V⁰ − Vᴱ| ≤ (|H| + |B|)/(1 − β)`, from the identity `pathValue_cornerF_gap` and
`0 ≤ Σ_t β^t z_t ≤ 1/(1 − β)`. -/
theorem abs_cornerF_gap_le {F : ℝ → ℝ → ℝ}
    (hF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      F x s ∈ Set.Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) :
    |G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
        - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1)|
      ≤ (|(G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)| + |G.b_J - G.b_K|)
          / (1 - β) := by
  rw [G.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0]
  have hS0 : 0 ≤ ∑' t : ℕ, β ^ t * residualF F x0 t :=
    zero_le_one.trans (one_le_tsum_residualF hF_mem hF_mono_x hF_mono_s hβ hx0)
  have hS1 := tsum_residualF_le hF_mem hF_mono_x hF_mono_s hβ hx0
  have hd : 0 < 1 - β := by linarith [hβ.2]
  have e1 : |((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)|
      = |(G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)| / (1 - β) := by
    rw [abs_div, abs_of_pos hd]
  have e2 : |(G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t|
      ≤ |G.b_J - G.b_K| / (1 - β) := by
    rw [abs_mul, abs_of_nonneg hS0]
    calc |G.b_J - G.b_K| * ∑' t : ℕ, β ^ t * residualF F x0 t
        ≤ |G.b_J - G.b_K| * (1 / (1 - β)) := mul_le_mul_of_nonneg_left hS1 (abs_nonneg _)
      _ = |G.b_J - G.b_K| / (1 - β) := by ring
  calc _ ≤ |((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)|
        + |(G.b_J - G.b_K) * ∑' t : ℕ, β ^ t * residualF F x0 t| := abs_add_le _ _
    _ ≤ |(G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)| / (1 - β)
        + |G.b_J - G.b_K| / (1 - β) := by rw [e1]; linarith
    _ = _ := by ring

/-- **Some rescaling makes the gap negative, uniformly** (BH6.1; general in
`F`): for every polity whose hawks gain from sanctions (`g_J > 0`) there is a
`k > 0` such that the hawk-rescaled polity — the same game as `G` under every
transition (`hawkRescale_toParamsF`) — has a strictly negative
zero-versus-full-sanction planner gap at every planner discount, every transition
that keeps the cube and is monotone in both arguments, and every start. So at such
a polity neither region (R) nor the government game certifies that the
zero-sanction path is at least as good for the planner (gap `≥ 0`). One-directional:
it says nothing about making the gap positive. Hypothesis: the sign of `g_J` only,
beside the maintained cube and monotonicity conditions on `F`. -/
theorem exists_hawkRescale_cornerF_gap_neg (hg : 0 < G.g_J) :
    ∃ k : ℝ, ∃ hk : 0 < k, ∀ F : ℝ → ℝ → ℝ,
      (∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
        F x s ∈ Set.Icc (0 : ℝ) 1) →
      (∀ s, Monotone (fun x => F x s)) → (∀ x, Monotone (fun s => F x s)) →
      ∀ β ∈ Set.Ico (0 : ℝ) 1, ∀ x0 ∈ Set.Icc (0 : ℝ) 1,
        (G.hawkRescale k hk.ne').pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - (G.hawkRescale k hk.ne').pathValue β (cornerPathF F x0) (fun _ => 0)
              (fun _ => 1) < 0 := by
  set M := |(G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)| + |G.b_J - G.b_K|
    with hM
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hq : 0 ≤ M / G.g_J := div_nonneg hM0 hg.le
  refine ⟨2 + M / G.g_J, by linarith, ?_⟩
  intro F hF_mem hF_mono_x hF_mono_s β hβ x0 hx0
  rw [G.hawkRescale_cornerF_gap _ _ hF_mem hβ hx0]
  have hup := (abs_le.mp (G.abs_cornerF_gap_le hF_mem hF_mono_x hF_mono_s hβ hx0)).2
  rw [← hM] at hup
  have hd : 0 < 1 - β := by linarith [hβ.2]
  have hk1 : (2 + M / G.g_J - 1) * G.g_J = G.g_J + M := by
    field_simp
    ring
  rw [hk1, add_div]
  have hpos : 0 < G.g_J / (1 - β) := div_pos hg hd
  linarith

/-- **Some rescaling makes the gap positive, uniformly** (BH6.1; general in `F`):
the mirror of `exists_hawkRescale_cornerF_gap_neg` for a polity whose hawks lose
from sanctions (`g_J < 0`, allowed by region (R) when `ν < 0`): some `k > 0` gives a
strictly positive gap at every planner discount, every start and every
cube-preserving transition monotone in both arguments, so the government game never
certifies gap `≤ 0` there. One-directional, like its mirror. -/
theorem exists_hawkRescale_cornerF_gap_pos (hg : G.g_J < 0) :
    ∃ k : ℝ, ∃ hk : 0 < k, ∀ F : ℝ → ℝ → ℝ,
      (∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
        F x s ∈ Set.Icc (0 : ℝ) 1) →
      (∀ s, Monotone (fun x => F x s)) → (∀ x, Monotone (fun s => F x s)) →
      ∀ β ∈ Set.Ico (0 : ℝ) 1, ∀ x0 ∈ Set.Icc (0 : ℝ) 1,
        0 < (G.hawkRescale k hk.ne').pathValue β (zeroPathF F x0) (fun _ => 0)
              (fun _ => 0)
          - (G.hawkRescale k hk.ne').pathValue β (cornerPathF F x0) (fun _ => 0)
              (fun _ => 1) := by
  set M := |(G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)| + |G.b_J - G.b_K|
    with hM
  have hM0 : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hq : 0 ≤ M / (-G.g_J) := div_nonneg hM0 (by linarith)
  refine ⟨2 + M / (-G.g_J), by linarith, ?_⟩
  intro F hF_mem hF_mono_x hF_mono_s β hβ x0 hx0
  rw [G.hawkRescale_cornerF_gap _ _ hF_mem hβ hx0]
  have hlo := (abs_le.mp (G.abs_cornerF_gap_le hF_mem hF_mono_x hF_mono_s hβ hx0)).1
  rw [← hM] at hlo
  have hd : 0 < 1 - β := by linarith [hβ.2]
  have hg0 : G.g_J ≠ 0 := hg.ne
  have hk1 : (2 + M / (-G.g_J) - 1) * G.g_J = G.g_J - M := by
    field_simp
    ring
  rw [hk1, sub_div]
  have hpos : 0 < (-G.g_J) / (1 - β) := div_pos (by linarith) hd
  have hneg : G.g_J / (1 - β) = -((-G.g_J) / (1 - β)) := by ring
  linarith

end FourGroup

#print axioms FourGroup.plannerW_distortion
#print axioms FourGroup.plannerW_lockin_dominated_iff
#print axioms FourGroup.stationaryPlannerValue_lockin_dominated_iff
#print axioms FourGroup.stationaryPlannerValue_relief_gain
#print axioms FourGroup.pathValue_affineCorner_gap
#print axioms FourGroup.affineCornerGap_pos_iff
#print axioms FourGroup.affineCornerGap_pos_all_discounts_iff
#print axioms FourGroup.pathValue_cornerF_gap
#print axioms FourGroup.pathValue_cornerF_gap_ge_of_nonneg
#print axioms FourGroup.pathValue_cornerF_gap_ge_of_neg
#print axioms FourGroup.pathValue_cornerF_gap_pos_all_discounts_iff
#print axioms FourGroup.pathValue_cornerF_gap_of_identity
#print axioms not_necessary_without_strict_adjustment
#print axioms separationF_tendsto_one
#print axioms cornerPathF_tendsto_one_of_strictAdjust
#print axioms zeroPathF_tendsto_zero_of_strictAdjust
#print axioms separationF_tendsto_one_of_strictAdjust
#print axioms FourGroup.pathValue_cornerF_gap_pos_all_discounts_iff_of_strictAdjust
#print axioms FourGroup.pathValue_cornerF_gap_pos_all_discounts_iff_of_params
#print axioms FourGroupCoeffs.plannerW_distortion
#print axioms FourGroupCoeffs.plannerW_lockin_dominated_iff
#print axioms FourGroupCoeffs.pathValue_affineCorner_gap
#print axioms FourGroupCoeffs.affineCornerGap_pos_all_discounts_iff
#print axioms FourGroupCoeffs.pathValue_cornerF_gap
#print axioms FourGroupCoeffs.pathValue_cornerF_gap_pos_all_discounts_iff_of_params
#print axioms FourGroup.hawkRescale_cornerF_gap
#print axioms FourGroup.abs_cornerF_gap_le
#print axioms FourGroup.exists_hawkRescale_cornerF_gap_neg
#print axioms FourGroup.exists_hawkRescale_cornerF_gap_pos

end KaempferLowenberg
end Sanctions
