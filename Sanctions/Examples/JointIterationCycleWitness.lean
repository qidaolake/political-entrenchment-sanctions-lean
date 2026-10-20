/-
Sanctions/Examples/JointIterationCycleWitness.lean

**Kernel-checked exact-rational 2-cycle certificate for the joint Bellman
value iteration.**

The joint (Jacobi) value-iteration update
`(V_T, V_S) ↦ (Target Bellman image, Sender Bellman image at the
leader-optimal policy)` on the deterministic (atomic-kernel) transition was
previously known to cycle only *numerically*: value/best-response iteration
on a Dirac transition kernel is the Doraszelski–Satterthwaite (2010 §3)
atomic-kernel degeneracy recorded in
`docs/archive/EXISTENCE-VIA-PURIFICATION-NOTE.md` §1 — the reason
equilibrium existence in this project routes through the purified
(atomless-noise, He–Sun) model rather than through iteration of the joint
operator. This file upgrades that numerical observation to a
**kernel-checked exact certificate**: an explicit rational period-2 orbit
of the joint iteration, at an economy whose Sender payoff satisfies the
maintained strict-concavity assumption (quadratic in `s` with coefficient
`−1/2`), verified for **all** states `x ∈ [0,1]` (the value functions are
affine and both Bellman images are computed in closed form — no grid, no
numerics).

THE ECONOMY (`cycleParams`): `δ = β_T = β_S = 1/2`, `F(x,s) = (x+s)/2`,

  `U_S(x,a,s) = −½(s − 1/4 − a/2)² + (15/32)·x·a`
  `U_T(x,a,s) = −(21/10)x + 8xs − 4xa − (3/40)a`.

THE ORBIT (affine on `S = [0,1]`):

  pair 0: `V_T0 = 25/192 + x`,       `V_S0 = 209/3072 + x/8`
  pair 1: `V_T1 = 89/480 + (2/5)·x`, `V_S1 = 89/1536 + x/2`.

THE MECHANISM (leader flip through the D3b order-reversal channel). The
Sender dynamic best response is the interior vertex
`s*(x,a) = 1/4 + a/2 + U_i/4` (`U_i` = current `V_S` slope), strictly
inside `(0,1)` at every `(x,a) ∈ [0,1]²`, so the state clip is provably
inactive and the Sender argmax is a singleton with quadratic margin
`½(s − s*)²`. Substituting `s*` into the leader integrand, the `8xs` and
`−4xa` terms cancel identically (`8·(1/2) − 4 = 0`), leaving the joint
Target integrand **affine in `a` with a constant (state-independent)
coefficient** `c_i = −3/40 + T_i/8` whose sign flips with the current
`V_T` slope `T_i`: at pair 0 (`T_0 = 1`) `c_0 = +1/20 > 0` and the leader
corners at `a* = 1` (margin `(1/20)(1−a)`); at pair 1 (`T_1 = 2/5`)
`c_1 = −1/40 < 0` and the leader corners at `a* = 0` (margin `(1/40)·a`).
A pointwise-higher `V_T` slope *raises* the leader argmax — exactly the
order-reversal channel exhibited in `Examples/JointBellmanNotOrderHom.lean`.
That file refutes **antitonicity** of the leader argmax in `V_T`
(`b2_leaderArgmax_not_antitone_in_V_T`) and, in the other direction,
**monotonicity** (`b2_leaderArgmax_not_monotone_in_V_T`): the argmax moves
in neither order direction, so the joint Bellman map is not an order
homomorphism for the pointwise order either way. Here the same channel is
shown to produce genuine period-2 cycling of the joint iteration itself.

STATEMENT LEVEL (honesty). The certificate is stated at the state-local
level — `jointTarget_BCF_on_S` with `DynamicArgmaxUnique` (Sender argmax
uniqueness at physical states `x ∈ [0,1]` only) and `bellmanS_BCF` at the
*derived* constant leader policy — NOT through the `jointTargetOp` wrapper:
the wrapper's hypothesis `DynamicArgmaxUniqueGlobal` (uniqueness at all
`x ∈ ℝ`) is FALSE at these value functions (at unphysical `x < 0` the clip
kink creates two exact global maximizers; cf. the docstring of
`SelectionRobust.lean`). On `[0,1]` every argmax on the orbit is a
singleton with an explicit rational margin, so the orbit is independent of
the selection convention: `σ_dyn = σ_dyn_top = s*` on the orbit, and the
Sender image is the same for *every* feasible Bellman-optimal leader
selector (`cyc_bellmanS_pair0_robust` / `cyc_bellmanS_pair1_robust`).

Rule-1 status: both strategic objects on the orbit are optimization
results — the Sender response is the unique dynamic argmax, and the
constant leader policy is *forced* by the unique joint-Bellman argmax
(`cyc_pair0_leader_argmax_eq_one` / `cyc_pair1_leader_argmax_eq_zero`).
This file adds NO new assumption and NO new `Params` field, and does not
touch `Sanctions/Headlines.lean`: the theorems below are witness-level
certificates (headline-shaped, not headline rows).

Ground-truth spec (28/28 adversarially verified exact symbolic checks):
`docs/archive/workflow-scratch/cycle_certificate_spec.md`.
-/

import Sanctions.Examples.SubstantiveComplianceWitness
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.Equilibrium.JointExistenceFromPrimitives
import Sanctions.Theory.Equilibrium.ArgmaxUniquenessFromConcavity

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-! ## 1. The economy -/

/-- Sender stage payoff: concave parabola in `s` (coefficient `−1/2`,
vertex `1/4 + a/2`) plus the branch-coupling term `(15/32)·x·a` that makes
the next `V_S` slope depend on the current leader action. -/
def cycU_S (x a s : ℝ) : ℝ := -(1/2) * (s - 1/4 - a/2) ^ 2 + 15/32 * x * a

/-- Target stage payoff. The `8xs` term against `−4xa` is tuned so the
`x·a` terms cancel identically once the Sender vertex (of `a`-slope `1/2`)
is substituted, leaving a constant leader coefficient `−3/40 + T_i/8`. -/
def cycU_T (x a s : ℝ) : ℝ := -(21/10) * x + 8 * x * s - 4 * x * a - 3/40 * a

/-- Static (myopic) Sender response: the clipped vertex of the concave
parabola `U_S(x,a,·)`, `σ(x,a) = clip(1/4 + a/2)` — interior in
`[1/4, 3/4]` for feasible `a`. -/
def cycσ (_x a : ℝ) : ℝ := max 0 (min 1 (1/4 + a/2))

/-- Feasibility of the static Sender response. -/
theorem cycσ_mem (x a : ℝ) : cycσ x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Joint continuity of the static Sender response. -/
theorem cycσ_continuous :
    Continuous (fun (xa : ℝ × ℝ) => cycσ xa.1 xa.2) := by
  unfold cycσ
  fun_prop

/-- **Rule-1 coupling.** The clipped vertex maximizes `U_S(x,a,·)` on
`[0,1]`: `U_S(x,a,s) = C(x,a) − ½(s − t)²` with `t = 1/4 + a/2`. -/
theorem cycσ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => cycU_S x a s) (Set.Icc (0 : ℝ) 1) (cycσ x a) :=
  WitnessKit.clipVertex_isMaxOn (by norm_num : (0:ℝ) < 1/2)
    (C := 15/32 * x * a)
    (fun s => by simp only [cycU_S]; ring)

/-- **The 2-cycle economy** (`δ = β_T = β_S = 1/2`, affine transition
`F(x,s) = (x+s)/2`). Every field is discharged from the closed forms. -/
def cycleParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1/2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := cycU_T
  U_S := cycU_S
  σ := cycσ
  σ_mem := cycσ_mem
  σ_isMaxOn_U_S := cycσ_isMaxOn
  U_T_continuous := by unfold cycU_T; fun_prop
  U_S_continuous := by unfold cycU_S; fun_prop
  F := AbstractGame.affineF (1/2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`cycleParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance cycleParams_staticSelectorContinuous :
    cycleParams.StaticSelectorContinuous where
  σ_continuous := cycσ_continuous

@[simp] theorem cycleParams_U_S : cycleParams.U_S = cycU_S := rfl
@[simp] theorem cycleParams_U_T : cycleParams.U_T = cycU_T := rfl
@[simp] theorem cycleParams_δ : cycleParams.δ = 1/2 := rfl
@[simp] theorem cycleParams_β_S : cycleParams.β_S = 1/2 := rfl
@[simp] theorem cycleParams_β_T : cycleParams.β_T = 1/2 := rfl

/-- Transition closed form: `F(x,s) = (x+s)/2`. -/
theorem cycleParams_F (x s : ℝ) : cycleParams.F x s = (x + s) / 2 := by
  change AbstractGame.affineF (1/2) x s = (x + s) / 2
  unfold AbstractGame.affineF
  ring

/-- `1 ∈ [0,1]` (feasible full compliance / full sanction). -/
private theorem one_mem_I : (1:ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩

/-- `0 ∈ [0,1]` (feasible full defiance / zero sanction). -/
private theorem zero_mem_I : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩

/-! ## 2. The orbit: two exact affine value pairs -/

/-- The affine BCF `y ↦ t + c·y` on the compact state space `↥S = [0,1]`
(intercept-slope form; the intercept-free sibling is `affineBCF`). -/
def cycBCF (t c : ℝ) : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => t + c * y.val) (by fun_prop))

@[simp] theorem cycBCF_apply (t c : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    cycBCF t c y = t + c * y.val := rfl

/-- Evaluation through the state clip: for `z ∈ [0,1]` the clip is inactive
and `cycBCF t c (clip z) = t + c·z`. -/
theorem cycBCF_clip_eval (t c : ℝ) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    cycBCF t c (Sanctions.clipS' z) = t + c * z := by
  rw [cycBCF_apply, clipS'_val_of_mem hz]

/-- Pair-0 Target value: `V_T0(x) = 25/192 + x` (slope `T_0 = 1`). -/
def cycV_T0 : Val := cycBCF (25/192) 1

/-- Pair-0 Sender value: `V_S0(x) = 209/3072 + x/8` (slope `U_0 = 1/8`). -/
def cycV_S0 : Val := cycBCF (209/3072) (1/8)

/-- Pair-1 Target value: `V_T1(x) = 89/480 + (2/5)x` (slope `T_1 = 2/5`). -/
def cycV_T1 : Val := cycBCF (89/480) (2/5)

/-- Pair-1 Sender value: `V_S1(x) = 89/1536 + x/2` (slope `U_1 = 1/2`). -/
def cycV_S1 : Val := cycBCF (89/1536) (1/2)

theorem cycV_T0_def : cycV_T0 = cycBCF (25/192) 1 := rfl
theorem cycV_S0_def : cycV_S0 = cycBCF (209/3072) (1/8) := rfl
theorem cycV_T1_def : cycV_T1 = cycBCF (89/480) (2/5) := rfl
theorem cycV_S1_def : cycV_S1 = cycBCF (89/1536) (1/2) := rfl

/-- The two Target values are distinct (evaluate at `x = 0`:
`25/192 ≠ 89/480`). -/
theorem cycV_T_ne : cycV_T0 ≠ cycV_T1 := by
  intro h
  have h0 : cycV_T0 (⟨0, ⟨le_refl 0, by norm_num⟩⟩ : ↥(Sanctions.S : Set ℝ))
      = cycV_T1 (⟨0, ⟨le_refl 0, by norm_num⟩⟩ : ↥(Sanctions.S : Set ℝ)) := by rw [h]
  rw [cycV_T0_def, cycV_T1_def, cycBCF_apply, cycBCF_apply] at h0
  norm_num at h0

/-- The two Sender values are distinct (evaluate at `x = 0`:
`209/3072 ≠ 89/1536`). -/
theorem cycV_S_ne : cycV_S0 ≠ cycV_S1 := by
  intro h
  have h0 : cycV_S0 (⟨0, ⟨le_refl 0, by norm_num⟩⟩ : ↥(Sanctions.S : Set ℝ))
      = cycV_S1 (⟨0, ⟨le_refl 0, by norm_num⟩⟩ : ↥(Sanctions.S : Set ℝ)) := by rw [h]
  rw [cycV_S0_def, cycV_S1_def, cycBCF_apply, cycBCF_apply] at h0
  norm_num at h0

/-! ## 3. The Sender best response: interior vertex, singleton argmax

At an affine continuation `V_S = u + U·x`, the dynamic Sender objective on
the physical box is the concave parabola
`−½(s − v)² + C(x,a)` with vertex `v = 1/4 + a/2 + U/4`: the clip is
inactive (`F(x,s) = (x+s)/2 ∈ [0,1]` for `(x,s) ∈ [0,1]²`), so the argmax
is the singleton `{v}` with quadratic margin `½(s − v)²`. -/

/-- **Sender dynamic objective in closed form** at an affine continuation
`cycBCF u U`, for physical `x` and feasible `s` (clip inactive). -/
theorem cyc_senderObj_eq (u U a : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Sanctions.I) :
    cycleParams.U_S x a s
        + cycleParams.β_S * (cycBCF u U) (Sanctions.clipS' (cycleParams.F x s))
      = -(1/2) * (s - (1/4 + a/2 + U/4)) ^ 2
        + (15/32 * x * a + u/2 + U/4 * x + (1/4 + a/2) * (U/4) + U^2/32) := by
  have hmem : (x + s) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hs.1, hx.1], by linarith [hs.2, hx.2]⟩
  simp only [cycleParams_U_S, cycU_S, cycleParams_β_S, cycleParams_F]
  rw [cycBCF_clip_eval u U hmem]
  ring

/-- **The interior vertex maximizes the Sender dynamic objective** on
`[0,1]` (provided the vertex is feasible). -/
theorem cyc_sender_vertex_isMaxOn (u U a : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hv : 1 / 4 + a / 2 + U / 4 ∈ Sanctions.I) :
    IsMaxOn
      (fun s => cycleParams.U_S x a s
        + cycleParams.β_S * (cycBCF u U) (Sanctions.clipS' (cycleParams.F x s)))
      Sanctions.I (1/4 + a/2 + U/4) := by
  rw [isMaxOn_iff]
  intro s hs
  rw [cyc_senderObj_eq u U a hx hs, cyc_senderObj_eq u U a hx hv]
  nlinarith [sq_nonneg (s - (1/4 + a/2 + U/4))]

/-- Vertex maximizer, restated at any point `v` equal to the vertex (the
form the per-pair evaluations consume, with `v` a clean rational). -/
theorem cyc_sender_isMaxOn_at (u U a v : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hveq : v = 1 / 4 + a / 2 + U / 4) (hv : v ∈ Sanctions.I) :
    IsMaxOn
      (fun s => cycleParams.U_S x a s
        + cycleParams.β_S * (cycBCF u U) (Sanctions.clipS' (cycleParams.F x s)))
      Sanctions.I v := by
  subst hveq
  exact cyc_sender_vertex_isMaxOn u U a hx hv

/-- **Explicit Sender margin**: the vertex beats every feasible `s` by
exactly `½(s − v)²` (the strict-concavity margin identity). -/
theorem cyc_sender_vertex_margin (u U a : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Sanctions.I) (hv : 1 / 4 + a / 2 + U / 4 ∈ Sanctions.I) :
    (cycleParams.U_S x a (1/4 + a/2 + U/4)
        + cycleParams.β_S
            * (cycBCF u U) (Sanctions.clipS' (cycleParams.F x (1/4 + a/2 + U/4))))
      - (cycleParams.U_S x a s
        + cycleParams.β_S * (cycBCF u U) (Sanctions.clipS' (cycleParams.F x s)))
      = 1/2 * (s - (1/4 + a/2 + U/4)) ^ 2 := by
  rw [cyc_senderObj_eq u U a hx hs, cyc_senderObj_eq u U a hx hv]
  ring

/-- **State-local `DynamicArgmaxUnique` at every affine continuation.** On
the physical state space the Sender dynamic objective is a strictly concave
parabola (leading coefficient exactly `−1/2`; the clip is inactive), so the
argmax is unique. NOTE (honesty): the *global* form
`DynamicArgmaxUniqueGlobal` is FALSE at the orbit values — at unphysical
`x < 0` the clip kink creates two exact maximizers — which is why the
certificate is stated through `jointTarget_BCF_on_S` / the state-local
predicate, not through the `jointTargetOp` wrapper. -/
theorem cycBCF_DAU (u U : ℝ) : cycleParams.DynamicArgmaxUnique (cycBCF u U) := by
  apply cycleParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne q r hq hr hqr
  have hr_eq : r = 1 - q := by linarith
  subst hr_eq
  have hmid : q * s₁ + (1 - q) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hq.le, hr.le],
     by nlinarith [hs₁.2, hs₂.2, hq.le, hr.le]⟩
  simp only [smul_eq_mul, cyc_senderObj_eq u U a hx hs₁,
    cyc_senderObj_eq u U a hx hs₂, cyc_senderObj_eq u U a hx hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [mul_pos (mul_pos hq hr) hsq]

/-- State-local Sender argmax uniqueness at the pair-0 continuation. -/
theorem cyc_DAU_S0 : cycleParams.DynamicArgmaxUnique cycV_S0 :=
  cycBCF_DAU (209/3072) (1/8)

/-- State-local Sender argmax uniqueness at the pair-1 continuation. -/
theorem cyc_DAU_S1 : cycleParams.DynamicArgmaxUnique cycV_S1 :=
  cycBCF_DAU (89/1536) (1/2)

/-- **`σ_dyn` pinned at the vertex** (uniqueness + exhibited maximizer). -/
theorem cyc_σ_dyn_eq_at (u U a v : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hveq : v = 1 / 4 + a / 2 + U / 4) (hv : v ∈ Sanctions.I) :
    cycleParams.σ_dyn (cycBCF u U) x a = v :=
  cycBCF_DAU u U x hx a (cycleParams.σ_dyn (cycBCF u U) x a) v
    (cycleParams.σ_dyn_mem (cycBCF u U) x a) hv
    (cycleParams.σ_dyn_isMaxOn (cycBCF u U) x a)
    (cyc_sender_isMaxOn_at u U a v hx hveq hv)

/-- **`σ_dyn_top` pinned at the vertex**: the upper selector (sup of the
dynamic argmax set) coincides with the unique argmax, so the certificate is
independent of the selection convention. -/
theorem cyc_σ_dyn_top_eq_at (u U a v : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hveq : v = 1 / 4 + a / 2 + U / 4) (hv : v ∈ Sanctions.I) :
    cycleParams.σ_dyn_top (cycBCF u U) x a = v :=
  cycBCF_DAU u U x hx a (cycleParams.σ_dyn_top (cycBCF u U) x a) v
    (cycleParams.σ_dyn_top_mem_I (cycBCF u U) x a) hv
    (cycleParams.σ_dyn_top_isMaxOn (cycBCF u U) x a)
    (cyc_sender_isMaxOn_at u U a v hx hveq hv)

/-- Pair-0 Sender response: `σ_dyn = 9/32 + a/2 ∈ [9/32, 25/32]`, strictly
interior for every physical `(x, a)`. -/
theorem cyc_σ_dyn_pair0 {x a : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Sanctions.I) :
    cycleParams.σ_dyn cycV_S0 x a = 9/32 + a/2 := by
  rw [cycV_S0_def]
  exact cyc_σ_dyn_eq_at (209/3072) (1/8) a (9/32 + a/2) hx (by ring)
    ⟨by linarith [ha.1], by linarith [ha.2]⟩

/-- Pair-1 Sender response: `σ_dyn = 3/8 + a/2 ∈ [3/8, 7/8]`, strictly
interior for every physical `(x, a)`. -/
theorem cyc_σ_dyn_pair1 {x a : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Sanctions.I) :
    cycleParams.σ_dyn cycV_S1 x a = 3/8 + a/2 := by
  rw [cycV_S1_def]
  exact cyc_σ_dyn_eq_at (89/1536) (1/2) a (3/8 + a/2) hx (by ring)
    ⟨by linarith [ha.1], by linarith [ha.2]⟩

/-- Pair-0 upper-selector agreement: `σ_dyn_top = σ_dyn = 9/32 + a/2`. -/
theorem cyc_σ_dyn_top_pair0 {x a : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Sanctions.I) :
    cycleParams.σ_dyn_top cycV_S0 x a = 9/32 + a/2 := by
  rw [cycV_S0_def]
  exact cyc_σ_dyn_top_eq_at (209/3072) (1/8) a (9/32 + a/2) hx (by ring)
    ⟨by linarith [ha.1], by linarith [ha.2]⟩

/-- Pair-1 upper-selector agreement: `σ_dyn_top = σ_dyn = 3/8 + a/2`. -/
theorem cyc_σ_dyn_top_pair1 {x a : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Sanctions.I) :
    cycleParams.σ_dyn_top cycV_S1 x a = 3/8 + a/2 := by
  rw [cycV_S1_def]
  exact cyc_σ_dyn_top_eq_at (89/1536) (1/2) a (3/8 + a/2) hx (by ring)
    ⟨by linarith [ha.1], by linarith [ha.2]⟩

/-! ## 4. The leader integrand: affine in `a` with constant coefficient

Substituting the Sender vertex, the joint Target integrand is affine in the
leader action with a **constant** coefficient: the `8x·s*` contribution
`8x·(a/2) = 4xa` cancels the `−4xa` term identically, and the remaining
`a`-coefficient is `−3/40 + β_T·δ·(1/2)·T_i = −3/40 + T_i/8`. -/

/-- **Pair-0 joint Target integrand in closed form**:
`13/96 + (1/20)·a + (2/5)·x` — the leader coefficient is the constant
`c_0 = +1/20 > 0` (compliance corner `a* = 1`). -/
theorem cyc_joint_T_integrand_pair0 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    cycleParams.joint_T_integrand cycV_T0 cycV_S0 x a
      = 13/96 + 1/20 * a + 2/5 * x := by
  have hσ := cyc_σ_dyn_pair0 hx ha
  have hland : (x + (9/32 + a/2)) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, ha.1], by linarith [hx.2, ha.2]⟩
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [show cycleParams.F x (9/32 + a/2) = (x + (9/32 + a/2)) / 2 from cycleParams_F x _,
    cycV_T0_def, cycBCF_clip_eval _ _ hland]
  simp only [cycleParams_U_T, cycU_T, cycleParams_β_T]
  ring

/-- **Pair-1 joint Target integrand in closed form**:
`25/192 − (1/40)·a + x` — the leader coefficient is the constant
`c_1 = −1/40 < 0` (defiance corner `a* = 0`). -/
theorem cyc_joint_T_integrand_pair1 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    cycleParams.joint_T_integrand cycV_T1 cycV_S1 x a
      = 25/192 - 1/40 * a + x := by
  have hσ := cyc_σ_dyn_pair1 hx ha
  have hland : (x + (3/8 + a/2)) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1, ha.1], by linarith [hx.2, ha.2]⟩
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [show cycleParams.F x (3/8 + a/2) = (x + (3/8 + a/2)) / 2 from cycleParams_F x _,
    cycV_T1_def, cycBCF_clip_eval _ _ hland]
  simp only [cycleParams_U_T, cycU_T, cycleParams_β_T]
  ring

/-- **Pair-0 leader corner**: full compliance `a = 1` maximizes the joint
Target integrand at every physical state (`c_0 = +1/20 > 0`). -/
theorem cyc_pair0_leader_isMaxOn_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => cycleParams.joint_T_integrand cycV_T0 cycV_S0 x a)
      Sanctions.I 1 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [cyc_joint_T_integrand_pair0 hx ha, cyc_joint_T_integrand_pair0 hx one_mem_I]
  linarith [ha.2]

/-- **Pair-1 leader corner**: full defiance `a = 0` maximizes the joint
Target integrand at every physical state (`c_1 = −1/40 < 0`). -/
theorem cyc_pair1_leader_isMaxOn_zero {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => cycleParams.joint_T_integrand cycV_T1 cycV_S1 x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [cyc_joint_T_integrand_pair1 hx ha, cyc_joint_T_integrand_pair1 hx zero_mem_I]
  linarith [ha.1]

/-- Pair-0 leader corner as an `IsGreatest` of the integrand image (the
form the `sSup` collapse consumes). -/
theorem cyc_pair0_leader_isGreatest {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest
      ((fun a => cycleParams.joint_T_integrand cycV_T0 cycV_S0 x a) '' Sanctions.I)
      (cycleParams.joint_T_integrand cycV_T0 cycV_S0 x 1) := by
  constructor
  · exact ⟨1, one_mem_I, rfl⟩
  · rintro z ⟨a, haI, rfl⟩
    exact cyc_pair0_leader_isMaxOn_one hx haI

/-- Pair-1 leader corner as an `IsGreatest` of the integrand image. -/
theorem cyc_pair1_leader_isGreatest {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest
      ((fun a => cycleParams.joint_T_integrand cycV_T1 cycV_S1 x a) '' Sanctions.I)
      (cycleParams.joint_T_integrand cycV_T1 cycV_S1 x 0) := by
  constructor
  · exact ⟨0, zero_mem_I, rfl⟩
  · rintro z ⟨a, haI, rfl⟩
    exact cyc_pair1_leader_isMaxOn_zero hx haI

/-- **Explicit pair-0 leader margin**: the corner `a = 1` beats feasible `a`
by exactly `(1/20)·(1 − a)` — uniform in the state. -/
theorem cyc_pair0_leader_margin {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    cycleParams.joint_T_integrand cycV_T0 cycV_S0 x 1
        - cycleParams.joint_T_integrand cycV_T0 cycV_S0 x a
      = 1/20 * (1 - a) := by
  rw [cyc_joint_T_integrand_pair0 hx ha, cyc_joint_T_integrand_pair0 hx one_mem_I]
  ring

/-- **Explicit pair-1 leader margin**: the corner `a = 0` beats feasible `a`
by exactly `(1/40)·a` — uniform in the state. -/
theorem cyc_pair1_leader_margin {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    cycleParams.joint_T_integrand cycV_T1 cycV_S1 x 0
        - cycleParams.joint_T_integrand cycV_T1 cycV_S1 x a
      = 1/40 * a := by
  rw [cyc_joint_T_integrand_pair1 hx ha, cyc_joint_T_integrand_pair1 hx zero_mem_I]
  ring

/-- **State-local `TargetArgmaxUnique` at pair 0**: the integrand is
strictly increasing in `a` (slope `+1/20`), so the leader argmax is a
singleton. -/
theorem cyc_TAU_pair0 : cycleParams.TargetArgmaxUnique cycV_T0 cycV_S0 :=
  cycleParams.targetArgmaxUnique_of_strictMonoOn fun x hx a₁ ha₁ a₂ ha₂ hlt => by
    simp only [cyc_joint_T_integrand_pair0 hx ha₁,
      cyc_joint_T_integrand_pair0 hx ha₂]
    linarith

/-- **State-local `TargetArgmaxUnique` at pair 1**: the integrand is
strictly decreasing in `a` (slope `−1/40`), so the leader argmax is a
singleton. -/
theorem cyc_TAU_pair1 : cycleParams.TargetArgmaxUnique cycV_T1 cycV_S1 :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn fun x hx a₁ ha₁ a₂ ha₂ hlt => by
    simp only [cyc_joint_T_integrand_pair1 hx ha₁,
      cyc_joint_T_integrand_pair1 hx ha₂]
    linarith

/-- **Rule-1 forcing, pair 0**: ANY feasible maximizer of the pair-0 joint
Target integrand at a physical state equals `1` — the compliance corner is
the *derived* leader policy, not an assumption. -/
theorem cyc_pair0_leader_argmax_eq_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => cycleParams.joint_T_integrand cycV_T0 cycV_S0 x a')
      Sanctions.I a) :
    a = 1 :=
  cyc_TAU_pair0 x hx a 1 ha one_mem_I hmax (cyc_pair0_leader_isMaxOn_one hx)

/-- **Rule-1 forcing, pair 1**: ANY feasible maximizer of the pair-1 joint
Target integrand at a physical state equals `0`. -/
theorem cyc_pair1_leader_argmax_eq_zero {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => cycleParams.joint_T_integrand cycV_T1 cycV_S1 x a')
      Sanctions.I a) :
    a = 0 :=
  cyc_TAU_pair1 x hx a 0 ha zero_mem_I hmax (cyc_pair1_leader_isMaxOn_zero hx)

/-! ## 5. Bellman images in closed form

The Target image collapses the `a`-sSup at the (unique) leader corner; the
Sender image collapses the `s`-sSup at the (unique) interior vertex, for
ANY feasible Bellman-optimal leader selector. -/

/-- **Target Bellman image of pair 0, pointwise**: the sSup collapses at
`a* = 1` and evaluates to `V_T1` at every state. -/
theorem cyc_jointTarget_pair0_apply (y : ↥(Sanctions.S : Set ℝ)) :
    cycleParams.jointTarget_BCF_on_S cycV_T0 cycV_S0 cyc_DAU_S0.toOnI y = cycV_T1 y := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn cycV_T0 cycV_S0 cyc_DAU_S0.toOnI y one_mem_I
      (cyc_pair0_leader_isMaxOn_one y.property),
    cyc_joint_T_integrand_pair0 y.property one_mem_I, cycV_T1_def, cycBCF_apply]
  ring

/-- **Target Bellman image of pair 1, pointwise**: the sSup collapses at
`a* = 0` and evaluates to `V_T0` at every state. -/
theorem cyc_jointTarget_pair1_apply (y : ↥(Sanctions.S : Set ℝ)) :
    cycleParams.jointTarget_BCF_on_S cycV_T1 cycV_S1 cyc_DAU_S1.toOnI y = cycV_T0 y := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn cycV_T1 cycV_S1 cyc_DAU_S1.toOnI y zero_mem_I
      (cyc_pair1_leader_isMaxOn_zero y.property),
    cyc_joint_T_integrand_pair1 y.property zero_mem_I, cycV_T0_def, cycBCF_apply]
  ring

/-- **Selection-robust Sender image of pair 0**: for EVERY feasible leader
selector `α` that is Bellman-optimal against the pair-0 joint integrand
(all such selectors equal `1` on `S`, by `cyc_pair0_leader_argmax_eq_one`),
the Sender Bellman image evaluates to `V_S1` at every state. The sSup
collapses at the interior vertex `s* = 25/32`. -/
theorem cyc_bellmanS_pair0_robust {α : ℝ → ℝ} (hα : Continuous α)
    (hmem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I)
    (hopt : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => cycleParams.joint_T_integrand cycV_T0 cycV_S0 x a)
        Sanctions.I (α x))
    (y : ↥(Sanctions.S : Set ℝ)) :
    cycleParams.bellmanS_BCF α hα cycV_S0 y = cycV_S1 y := by
  have hα1 : α y.val = 1 :=
    cyc_pair0_leader_argmax_eq_one y.property (hmem y.val y.property)
      (hopt y.val y.property)
  have hvI : (25/32 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hland : (y.val + 25/32) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
  have hmax : IsMaxOn
      (fun s => cycleParams.U_S y.val (α y.val) s
        + cycleParams.β_S * cycV_S0 (Sanctions.clipS' (cycleParams.F y.val s)))
      Sanctions.I (25/32) := by
    rw [hα1, cycV_S0_def]
    exact cyc_sender_isMaxOn_at (209/3072) (1/8) 1 (25/32) y.property (by norm_num) hvI
  rw [WitnessKit.bellmanS_image_of_isMaxOn (p := cycleParams) hα cycV_S0 y hvI hmax,
    hα1, show cycleParams.F y.val (25/32) = (y.val + 25/32) / 2 from cycleParams_F _ _,
    cycV_S0_def, cycBCF_clip_eval _ _ hland, cycV_S1_def]
  simp only [cycleParams_U_S, cycU_S, cycleParams_β_S, cycBCF_apply]
  ring

/-- **Selection-robust Sender image of pair 1**: for EVERY feasible
Bellman-optimal leader selector against the pair-1 joint integrand (all
equal `0` on `S`), the Sender image evaluates to `V_S0` at every state. The
sSup collapses at the interior vertex `s* = 3/8`. -/
theorem cyc_bellmanS_pair1_robust {α : ℝ → ℝ} (hα : Continuous α)
    (hmem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I)
    (hopt : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => cycleParams.joint_T_integrand cycV_T1 cycV_S1 x a)
        Sanctions.I (α x))
    (y : ↥(Sanctions.S : Set ℝ)) :
    cycleParams.bellmanS_BCF α hα cycV_S1 y = cycV_S0 y := by
  have hα0 : α y.val = 0 :=
    cyc_pair1_leader_argmax_eq_zero y.property (hmem y.val y.property)
      (hopt y.val y.property)
  have hvI : (3/8 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hland : (y.val + 3/8) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
  have hmax : IsMaxOn
      (fun s => cycleParams.U_S y.val (α y.val) s
        + cycleParams.β_S * cycV_S1 (Sanctions.clipS' (cycleParams.F y.val s)))
      Sanctions.I (3/8) := by
    rw [hα0, cycV_S1_def]
    exact cyc_sender_isMaxOn_at (89/1536) (1/2) 0 (3/8) y.property (by norm_num) hvI
  rw [WitnessKit.bellmanS_image_of_isMaxOn (p := cycleParams) hα cycV_S1 y hvI hmax,
    hα0, show cycleParams.F y.val (3/8) = (y.val + 3/8) / 2 from cycleParams_F _ _,
    cycV_S1_def, cycBCF_clip_eval _ _ hland, cycV_S0_def]
  simp only [cycleParams_U_S, cycU_S, cycleParams_β_S, cycBCF_apply]
  ring

/-- **Sender Bellman image of pair 0 at the derived leader policy `α ≡ 1`,
pointwise**: evaluates to `V_S1` at every state. -/
theorem cyc_bellmanS_pair0_apply (y : ↥(Sanctions.S : Set ℝ)) :
    cycleParams.bellmanS_BCF (fun _ => (1:ℝ)) continuous_const cycV_S0 y
      = cycV_S1 y :=
  cyc_bellmanS_pair0_robust continuous_const (fun _ _ => one_mem_I)
    (fun _ hx => cyc_pair0_leader_isMaxOn_one hx) y

/-- **Sender Bellman image of pair 1 at the derived leader policy `α ≡ 0`,
pointwise**: evaluates to `V_S0` at every state. -/
theorem cyc_bellmanS_pair1_apply (y : ↥(Sanctions.S : Set ℝ)) :
    cycleParams.bellmanS_BCF (fun _ => (0:ℝ)) continuous_const cycV_S1 y
      = cycV_S0 y :=
  cyc_bellmanS_pair1_robust continuous_const (fun _ _ => zero_mem_I)
    (fun _ hx => cyc_pair1_leader_isMaxOn_zero hx) y

/-! ## 6. THE 2-CYCLE: exact image identities, distinctness, no fixed point

The four Bellman-image identities below are genuine equalities of bounded
continuous functions on `S = [0,1]` — i.e. the joint iteration maps pair 0
exactly onto pair 1 and pair 1 exactly onto pair 0. -/

/-- **Cycle identity T(0→1)**: the joint Target Bellman image of
`(V_T0, V_S0)` is exactly `V_T1`. -/
theorem jointIteration_cycle_T01 :
    cycleParams.jointTarget_BCF_on_S cycV_T0 cycV_S0 cyc_DAU_S0.toOnI = cycV_T1 :=
  BoundedContinuousFunction.ext cyc_jointTarget_pair0_apply

/-- **Cycle identity S(0→1)**: the Sender Bellman image of `V_S0` at the
derived pair-0 leader policy `α ≡ 1` is exactly `V_S1`. -/
theorem jointIteration_cycle_S01 :
    cycleParams.bellmanS_BCF (fun _ => (1:ℝ)) continuous_const cycV_S0 = cycV_S1 :=
  BoundedContinuousFunction.ext cyc_bellmanS_pair0_apply

/-- **Cycle identity T(1→0)**: the joint Target Bellman image of
`(V_T1, V_S1)` is exactly `V_T0`. -/
theorem jointIteration_cycle_T10 :
    cycleParams.jointTarget_BCF_on_S cycV_T1 cycV_S1 cyc_DAU_S1.toOnI = cycV_T0 :=
  BoundedContinuousFunction.ext cyc_jointTarget_pair1_apply

/-- **Cycle identity S(1→0)**: the Sender Bellman image of `V_S1` at the
derived pair-1 leader policy `α ≡ 0` is exactly `V_S0`. -/
theorem jointIteration_cycle_S10 :
    cycleParams.bellmanS_BCF (fun _ => (0:ℝ)) continuous_const cycV_S1 = cycV_S0 :=
  BoundedContinuousFunction.ext cyc_bellmanS_pair1_apply

/-- **The two value pairs are distinct** (slopes `1 ≠ 2/5`, `1/8 ≠ 1/2`;
witnessed at `x = 0`). -/
theorem cycle_pair_ne : (cycV_T0, cycV_S0) ≠ (cycV_T1, cycV_S1) := by
  intro h
  exact cycV_T_ne (congrArg Prod.fst h)

/-- **Pair 0 is NOT a fixed point** of the joint iteration: its image is
`(V_T1, V_S1) ≠ (V_T0, V_S0)`. -/
theorem cycle_pair0_not_fixed :
    (cycleParams.jointTarget_BCF_on_S cycV_T0 cycV_S0 cyc_DAU_S0.toOnI,
      cycleParams.bellmanS_BCF (fun _ => (1:ℝ)) continuous_const cycV_S0)
      ≠ (cycV_T0, cycV_S0) := by
  rw [jointIteration_cycle_T01, jointIteration_cycle_S01]
  intro h
  exact cycV_T_ne (congrArg Prod.fst h).symm

/-- **Pair 1 is NOT a fixed point** of the joint iteration: its image is
`(V_T0, V_S0) ≠ (V_T1, V_S1)`. -/
theorem cycle_pair1_not_fixed :
    (cycleParams.jointTarget_BCF_on_S cycV_T1 cycV_S1 cyc_DAU_S1.toOnI,
      cycleParams.bellmanS_BCF (fun _ => (0:ℝ)) continuous_const cycV_S1)
      ≠ (cycV_T1, cycV_S1) := by
  rw [jointIteration_cycle_T10, jointIteration_cycle_S10]
  intro h
  exact cycV_T_ne (congrArg Prod.fst h)

/-- **THE PERIOD-2 CERTIFICATE.** The joint Bellman value iteration
(Target component: sSup of the joint integrand over the leader action;
Sender component: Sender Bellman operator at the derived leader policy)
maps `(V_T0, V_S0)` exactly onto `(V_T1, V_S1)` and `(V_T1, V_S1)` exactly
back onto `(V_T0, V_S0)`, and the two pairs are distinct — an exact
rational 2-cycle. In particular the deterministic joint value iteration
does not converge from either pair: the Doraszelski–Satterthwaite
atomic-kernel cycling, kernel-checked. -/
theorem jointIteration_two_cycle :
    (cycleParams.jointTarget_BCF_on_S cycV_T0 cycV_S0 cyc_DAU_S0.toOnI = cycV_T1
      ∧ cycleParams.bellmanS_BCF (fun _ => (1:ℝ)) continuous_const cycV_S0 = cycV_S1)
    ∧ (cycleParams.jointTarget_BCF_on_S cycV_T1 cycV_S1 cyc_DAU_S1.toOnI = cycV_T0
      ∧ cycleParams.bellmanS_BCF (fun _ => (0:ℝ)) continuous_const cycV_S1 = cycV_S0)
    ∧ (cycV_T0, cycV_S0) ≠ (cycV_T1, cycV_S1) :=
  ⟨⟨jointIteration_cycle_T01, jointIteration_cycle_S01⟩,
    ⟨jointIteration_cycle_T10, jointIteration_cycle_S10⟩, cycle_pair_ne⟩

end -- noncomputable section

#print axioms jointIteration_cycle_T01
#print axioms jointIteration_cycle_S01
#print axioms jointIteration_cycle_T10
#print axioms jointIteration_cycle_S10
#print axioms cycle_pair_ne
#print axioms cycle_pair0_not_fixed
#print axioms cycle_pair1_not_fixed
#print axioms jointIteration_two_cycle

end Examples

end Sanctions
