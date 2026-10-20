/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.P3SubBasinMonotonicity

/-!
# The P3 Sender spread is pinned for every equilibrium

Until now the strong results about the full-width `P₃` economy — the strictly
ratcheting sub-basin, the exact realised rule, every quantity keyed to the
Sender endpoint spread — were stated for the one explicitly **constructed**
equilibrium `mwEqEquilibrium`, because the economy has no uniqueness theorem.
This file removes that restriction for the spread, and hence for everything
determined by it.

`mwSpread_pinned` : for **every** equilibrium `E` of the specialization,

  `E.V_S(1) − E.V_S(0) = mwEqSenderSpread`.

Consequently `mwAlphaOne_pinned` pins the Target's top action, and
`mwSenderRule_pinned` pins the entire realised Sender rule as a function of
`(x, a)`, for every equilibrium.

## The route, and where the content is

**The Target's top action is derived, never assumed.**  `mwAlphaOne_pin` has
exactly one hypothesis — the equilibrium itself.  Optimality enters only through
the structure's genuine `α_opt_shock` field, a real `IsMaxOn` over the real
action set.  At the top state the Target's integrand is an *exact quadratic*
whose curvature is `−29/24`, a constant **independent of the equilibrium**
(`Jgen_vertex_form`, closed by `ring`).  So "no deviation is better" upgrades to
"the action equals the vertex" by completing the square, with no regularity
condition assumed anywhere.

The single tested deviation is the vertex `a* = (315 + 5Δ_S − 9Δ_T)/580`, and it
is *proved* admissible rather than supposed: `leaderVert_one_pos` and
`leaderVert_one_lt_one` rule out the corner `α(1) = 1`, and the accompanying
Sender response is shown to sit strictly inside the unclipped branch — the clip
at the top state, which is what makes that state special elsewhere in this
development, is proved not to bite at `a*`.

**A branch trap, found and closed.**  The bottom-state response satisfies
`s₀ = 0` **iff** `Δ_S ≤ 2`, and the proved arbitrary-equilibrium window
`[17/10, 45/16]` *straddles* `2`.  The quartic eliminant only holds on the
`s₀ = 0` branch, so "every equilibrium satisfies the quartic" was **false as
stated** until the other branch was excluded.  `branchB_excluded` does that: the
branch-`B` system forces a cubic that `branchBCubic_pos` shows is strictly
positive on `[2, 45/16]`.  Without this the keystone would have been a false
theorem with a plausible proof.

**Uniqueness of the root is algebraic.**  `mwEqQuartic_strictAntiOn` uses the
divided-difference chord identity `q(a) − q(b) = (a−b)·B(a,b)`, proved by `ring`,
with `B < 0` on the window by factorisation — no derivative, no mean value
theorem.  Combined with the sign change at the window's endpoints this gives
exactly one root, and the window endpoints `17/10` and `45/16` are themselves
*derived* for every equilibrium (`mwD_ge_seventeen_tenths`, `mwD_le`), not
numerically chosen.

## What this does and does not settle

It pins `Δ_S`, `Δ_T`, `α(1)`, and the whole Sender rule as a function of
`(x, a)`.  It does **not** pin `α(x)` at every state, so it is **not** full
equilibrium uniqueness for this economy; two equilibria could still differ in
the Target policy away from the top state.  Every claim below is stated at the
strength actually proved.

Where a conclusion holds with an equilibrium-independent witness, it is stated
in that order: `p3_exists_ratchet_invariant_subinterval_uniform` gives **one**
sub-interval that works for **every** equilibrium, rather than an interval per
equilibrium.  The weaker per-equilibrium form is retained as a corollary for
callers that want that shape.

No numerically-obtained constant appears in any statement; every constant is an
exact rational.
-/

namespace Sanctions.Examples
namespace P3Pin

open Set
open Sanctions.Examples.P3WeakFloor

noncomputable section

/-! ## 1.  STEP 2 — at most one quartic root on the arbitrary-`E` window.

Pure exact-rational algebra: an explicit divided-difference (chord) identity
plus a sign bound on the chord factor.  No analysis, no numeric oracle. -/

theorem mwEqQuartic_chord (a b : ℝ) :
    mwEqQuartic a - mwEqQuartic b
      = (a - b) *
          (81 * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
            - 186120 * (a ^ 2 + a * b + b ^ 2)
            + 108518950 * (a + b) - 6625517528) := by
  unfold mwEqQuartic; ring

theorem mwEqQuartic_chordFactor_neg {a b : ℝ}
    (ha : a ∈ Icc (17 / 10 : ℝ) (45 / 16)) (hb : b ∈ Icc (17 / 10 : ℝ) (45 / 16)) :
    81 * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)
      - 186120 * (a ^ 2 + a * b + b ^ 2)
      + 108518950 * (a + b) - 6625517528 < 0 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hap : (0 : ℝ) < a := by linarith
  have hbp : (0 : ℝ) < b := by linarith
  have hasq : a ^ 2 ≤ (45 / 16 : ℝ) ^ 2 := by nlinarith
  have hbsq : b ^ 2 ≤ (45 / 16 : ℝ) ^ 2 := by nlinarith
  have hcubes :
      a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3
        ≤ (2 * (45 / 16 : ℝ) ^ 2) * (2 * (45 / 16 : ℝ)) := by
    have hfac : a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 = (a ^ 2 + b ^ 2) * (a + b) := by ring
    rw [hfac]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have hquad : (0 : ℝ) ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  nlinarith [hcubes, hquad]

/-- `mwEqQuartic` is strictly decreasing on `[17/10, 45/16]`. -/
theorem mwEqQuartic_strictAntiOn :
    StrictAntiOn mwEqQuartic (Icc (17 / 10 : ℝ) (45 / 16)) := by
  intro a ha b hb hab
  have hch := mwEqQuartic_chord a b
  have hneg := mwEqQuartic_chordFactor_neg ha hb
  have hlt : a - b < 0 := by linarith
  have := mul_pos_of_neg_of_neg hlt hneg
  linarith

theorem mwEqSenderSpread_mem_wide :
    mwEqSenderSpread ∈ Icc (17 / 10 : ℝ) (45 / 16) := by
  obtain ⟨hlo, hhi⟩ := mwEqSenderSpread_bounds
  exact ⟨by linarith, by linarith⟩

/-- Any root of the quartic in the arbitrary-`E` window is the constructed
spread. -/
theorem eq_mwEqSenderSpread_of_quartic_zero
    {D : ℝ} (hD : D ∈ Icc (17 / 10 : ℝ) (45 / 16)) (hz : mwEqQuartic D = 0) :
    D = mwEqSenderSpread :=
  mwEqQuartic_strictAntiOn.injOn hD mwEqSenderSpread_mem_wide
    (hz.trans mwEqSenderSpread_quartic.symm)

/-! ## 2.  Arithmetic core of the pin — no model content.

`Jgen D T x a` is the Target's shocked objective at state `x` and leader action
`a`, on the region where the Sender response equals the *unclipped* vertex
`v(x,a) = 9x/8 − 1/12 − (5/12)a + D/24`, constant continuation term dropped.
`D = Δ_S`, `T = Δ_T`. -/

def senderVert (D x a : ℝ) : ℝ := (9 / 8) * x - 1 / 12 - (5 / 12) * a + D / 24

def Jgen (D T x a : ℝ) : ℝ :=
  -a ^ 2 + 2 * x * a - a + senderVert D x a * (x + a / 2 - 1 / 2 + (9 / 100) * T)

/-- The interior first-order condition — the vertex of `Jgen` in `a`. -/
def leaderVert (D T x : ℝ) : ℝ := (5 * D - 9 * T + 515 * x - 200) / 580

/-- `Jgen` is an exact concave quadratic in `a` with vertex `leaderVert` and
curvature `−29/12`, a **constant** independent of `D`, `T`, `x`. -/
theorem Jgen_vertex_form (D T x a b : ℝ) :
    Jgen D T x a - Jgen D T x b
      = (29 / 24) * ((b - leaderVert D T x) ^ 2 - (a - leaderVert D T x) ^ 2) := by
  unfold Jgen senderVert leaderVert; ring

/-- Being at least as good as the *clipped* vertex forces equality with it. -/
theorem pin_clip {w a : ℝ} (ha : 0 ≤ a) (h : (a - w) ^ 2 ≤ (max 0 w - w) ^ 2) :
    a = max 0 w := by
  rcases le_or_gt 0 w with hw | hw
  · rw [max_eq_right hw] at h ⊢; nlinarith
  · rw [max_eq_left hw.le] at h ⊢; nlinarith

/-- Packaged: `Jgen`-optimality at the clipped vertex pins the action. -/
theorem pin_of_Jgen_ge {D T x a : ℝ} (ha : 0 ≤ a)
    (h : Jgen D T x (max 0 (leaderVert D T x)) ≤ Jgen D T x a) :
    a = max 0 (leaderVert D T x) := by
  refine pin_clip ha ?_
  have hv := Jgen_vertex_form D T x a (max 0 (leaderVert D T x))
  nlinarith [hv]

/-! ### Feasibility, on the proved arbitrary-`E` windows.

`leaderVert D T 1 = astar D T` is the top-state first-order condition. -/

theorem leaderVert_one_pos {D T : ℝ} (hD : 17 / 10 ≤ D) (hT : T ≤ 60 / 11) :
    0 < leaderVert D T 1 := by unfold leaderVert; linarith

theorem leaderVert_one_lt_one {D T : ℝ} (hD : D ≤ 45 / 16) (hT : 0 ≤ T) :
    leaderVert D T 1 < 1 := by unfold leaderVert; linarith

theorem senderVert_at_leaderVert_one_pos {D T : ℝ}
    (hD : 0 ≤ D) (hT : 0 ≤ T) :
    0 < senderVert D 1 (leaderVert D T 1) := by unfold senderVert leaderVert; linarith

theorem senderVert_at_leaderVert_one_lt_one {D T : ℝ}
    (hDu : D ≤ 45 / 16) (hT : T ≤ 60 / 11) :
    senderVert D 1 (leaderVert D T 1) < 1 := by unfold senderVert leaderVert; linarith

/-! ## 3.  P0 — the Target endpoint spread identity, for an arbitrary `E`.

Subtracting the two Target Bellman equations at the endpoints, using that at
half-width one the smeared continuation is *exactly affine*
(`movAvgBCF_one_sub_eq`), gives an EQUATION: the Target endpoint spread times
the smear-chord factor `16/25 − (9/100)(s₁ − s₀)` equals the endpoint stage
gain.  `α(0) = 0` (`mwAlphaZero`) has been substituted.  (Currently trapped
inside the proof of `mwT_spread_ge_half`,
`Sanctions/Examples/P3WeakFloorSpreadBound.lean:560-568`.) -/

set_option maxHeartbeats 1600000 in
theorem mwT_spread_identity
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0))
      * (16 / 25 - (9 / 100) *
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            - mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))
      = -(E.α 1) ^ 2 + E.α 1
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
            * (1 / 2 + E.α 1 / 2)
        + mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 / 2 := by
  have hx0val : ((Sanctions.clipS' (0:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 0 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hx1val : ((Sanctions.clipS' (1:ℝ) : ↥(Sanctions.S : Set ℝ)) : ℝ) = 1 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have h0S : (0:ℝ) ∈ Sanctions.S := by norm_num
  have h1S : (1:ℝ) ∈ Sanctions.S := by norm_num
  have hs1I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs0I : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      ∈ Sanctions.I := mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hbell0 := mwShockedOne_target_bellman_eq_at_alpha E (Sanctions.clipS' 0)
  have hbell1 := mwShockedOne_target_bellman_eq_at_alpha E (Sanctions.clipS' 1)
  rw [hx0val, mwAlphaZero E] at hbell0
  rw [hx1val] at hbell1
  have hJ1 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1)
      = mwU_T 1 (E.α 1)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)))) := rfl
  have hJ0 : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 0 0
      = mwU_T 0 0 (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 0
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0))) := rfl
  rw [hJ1] at hbell1
  rw [hJ0] at hbell0
  have hF0 : mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 0 _ h0S hs0I
  have hF1 : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S hs1I
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 0
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0)))
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))))
  rw [Sanctions.clipS'_val_eq_of_mem hF0, Sanctions.clipS'_val_eq_of_mem hF1] at hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope hbell0 hbell1
  unfold mwU_T at hbell0 hbell1
  linear_combination hbell1 - hbell0 + (9/10) * hslope

/-! ## 4.  P1 — THE PIN AT THE TOP STATE.

`α(1)` is *derived* from the equilibrium argmax `α_opt_shock 1`, tested against
the single deviation `a = leaderVert Δ_S Δ_T 1`.  The Target's top-state
objective is an exact concave quadratic with constant curvature `−29/12` on the
unclipped Sender region; the candidate sits strictly inside that region and
strictly inside the action set, so optimality forces equality. -/

set_option maxHeartbeats 1600000 in
theorem mwAlphaOne_pin
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.α 1
      = leaderVert (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
          (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)) 1 := by
  have h1S : (1:ℝ) ∈ Sanctions.S := by norm_num
  have ha1 : E.α 1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have hDlo := mwD_ge_seventeen_tenths E
  have hDhi := mwD_le E
  have hTlo := mwT_spread_nonneg E
  have hThi := mwShockedOne_target_endpoint_spread_le E
  have hs_alpha := mwTopResponse_eq E
  set D := E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) with hDdef
  set T := E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) with hTdef
  have haI : leaderVert D T 1 ∈ Sanctions.I :=
    ⟨(leaderVert_one_pos hDlo hThi).le, (leaderVert_one_lt_one hDhi hTlo).le⟩
  have hvert : mwSenderVertexOne E.V_S 1 (leaderVert D T 1)
      = 25 / 24 + D / 24 - (5 / 12) * leaderVert D T 1 := by
    unfold mwSenderVertexOne; rw [← hDdef]; ring
  have hvpos : 0 < mwSenderVertexOne E.V_S 1 (leaderVert D T 1) := by
    rw [hvert]
    have := senderVert_at_leaderVert_one_pos (D := D) (T := T) (by linarith) hTlo
    unfold senderVert at this; linarith
  have hvlt : mwSenderVertexOne E.V_S 1 (leaderVert D T 1) < 1 := by
    rw [hvert]
    have := senderVert_at_leaderVert_one_lt_one (D := D) (T := T) hDhi hThi
    unfold senderVert at this; linarith
  have hs_dev : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (leaderVert D T 1)
      = 25 / 24 + D / 24 - (5 / 12) * leaderVert D T 1 := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S h1S (leaderVert D T 1),
      min_eq_right hvlt.le, max_eq_right hvpos.le, hvert]
  have hopt := E.α_opt_shock 1 h1S haI
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (leaderVert D T 1) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1) at hopt
  have hJa : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (E.α 1)
      = mwU_T 1 (E.α 1)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)))) := rfl
  have hJd : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) 1 (leaderVert D T 1)
      = mwU_T 1 (leaderVert D T 1)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (leaderVert D T 1))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F 1
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1
                (leaderVert D T 1)))) := rfl
  rw [hJa, hJd] at hopt
  have hFa : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hFd : mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (leaderVert D T 1))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem 1 _ h1S
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))))
    (Sanctions.clipS' (mechanismWitnessParams.F 1
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (leaderVert D T 1))))
  rw [Sanctions.clipS'_val_eq_of_mem hFa, Sanctions.clipS'_val_eq_of_mem hFd] at hslope
  rw [hs_alpha, hs_dev] at hopt hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hopt hslope
  unfold mwU_T at hopt
  rw [← hTdef] at hslope
  have hkey : Jgen D T 1 (max 0 (leaderVert D T 1)) ≤ Jgen D T 1 (E.α 1) := by
    rw [max_eq_right (leaderVert_one_pos hDlo hThi).le]
    unfold Jgen senderVert
    linarith [hopt, hslope]
  have := pin_of_Jgen_ge (D := D) (T := T) (x := 1) ha1.1 hkey
  rw [this, max_eq_right (leaderVert_one_pos hDlo hThi).le]

/-! ## 5.  P2 — the bottom-state Sender response is exactly `0`.

`s₀ = max 0 (min 1 (−1/12 + Δ_S/24))`, so `s₀ = 0` iff `Δ_S ≤ 2`, and the
proved window `[17/10, 45/16]` **straddles** `2`.  The branch `Δ_S > 2` is
*refuted*: on it the two exact spread identities plus the pin force a cubic
eliminant that is strictly positive on `[2, 45/16]`. -/

def branchBCubic (D : ℝ) : ℝ :=
  645540 * D ^ 3 - 416884281 * D ^ 2 + 399568339492 * D - 703564304580

theorem branchBCubic_pos {D : ℝ} (h2 : 2 ≤ D) (hu : D ≤ 45 / 16) :
    0 < branchBCubic D := by
  unfold branchBCubic; nlinarith [sq_nonneg D, sq_nonneg (D - 2)]

theorem branchB_eliminant {D T a s1 s0 : ℝ}
    (hs0 : s0 = (D - 2) / 24)
    (ha : a = leaderVert D T 1)
    (hs1 : s1 = 25 / 24 + D / 24 - (5 / 12) * a)
    (hS : D * (7 / 10 + s0 / 20)
      = 29 / 10 - (12 / 5) * s1 + (3 / 5) * s1 ^ 2 + (3 / 5) * s0 ^ 2 + s0 / 10)
    (hTid : T * (16 / 25 - (9 / 100) * (s1 - s0))
      = -a ^ 2 + a + s1 * (1 / 2 + a / 2) + s0 / 2) :
    branchBCubic D = 0 := by
  unfold leaderVert at ha
  subst hs0; subst ha; subst hs1
  have hnS : -555 * D ^ 2 + 954 * D * T - 2421946 * D + 81 * T ^ 2
      - 29682 * T + 4320465 = 0 := by linear_combination (-3229440 : ℝ) * hS
  have hnT : 25 * D ^ 2 - 90 * D * T + 14750 * D + 81 * T ^ 2
      - 155658 * T + 232625 = 0 := by linear_combination (-278400 : ℝ) * hTid
  have hW : (9 * D + 1086) * T = 5 * D ^ 2 + 21006 * D - 35240 := by
    linear_combination (1 / 116 : ℝ) * hnS - (1 / 116 : ℝ) * hnT
  unfold branchBCubic
  linear_combination (-(1 : ℝ) / 9) * (9 * D + 1086) ^ 2 * hnT
    + ((1 : ℝ) / 9) * (-90 * D * (9 * D + 1086)
        + 81 * ((9 * D + 1086) * T + (5 * D ^ 2 + 21006 * D - 35240))
        - 155658 * (9 * D + 1086)) * hW

theorem mwBottomResponse_zero
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0 = 0
      ∧ E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) ≤ 2 := by
  have hDlo := mwD_ge_seventeen_tenths E
  have hDhi := mwD_le E
  have hvert : mwSenderVertexOne E.V_S 0 0
      = -1/12 + (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) / 24 := by
    unfold mwSenderVertexOne; ring
  have hclip : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
      = max 0 (-1/12 + (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) / 24) := by
    rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S (by norm_num : (0:ℝ) ∈ Sanctions.S) 0, hvert,
      min_eq_right (by linarith)]
  rcases le_or_gt (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) 2 with hle | hgt
  · exact ⟨by rw [hclip, max_eq_left (by linarith)], hle⟩
  · exfalso
    have hs0 : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 0
        = ((E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) - 2) / 24 := by
      rw [hclip, max_eq_right (by linarith)]; ring
    have hSid := mwSenderSpread_reduced_identity E
    have hTid := mwT_spread_identity E
    rw [hs0] at hSid hTid
    have hcub := branchB_eliminant (D := E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
      (T := E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0))
      (a := E.α 1)
      (s1 := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      (s0 := ((E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) - 2) / 24)
      rfl (mwAlphaOne_pin E) (mwTopResponse_eq E) (by linarith) (by linarith)
    have := branchBCubic_pos (D := E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
      (by linarith) hDhi
    linarith

/-! ## 6.  P3 — the quartic, and the pinned spreads, for EVERY equilibrium. -/

theorem branchA_polynomials {D T a s1 : ℝ}
    (ha : a = leaderVert D T 1)
    (hs1 : s1 = 25 / 24 + D / 24 - (5 / 12) * a)
    (hS : D * (7 / 10) = 29 / 10 - (12 / 5) * s1 + (3 / 5) * s1 ^ 2)
    (hTid : T * (16 / 25 - (9 / 100) * s1) = -a ^ 2 + a + s1 * (1 / 2 + a / 2)) :
    (2809 * D ^ 2 + 954 * D * T - 2435402 * D + 81 * T ^ 2 - 29682 * T + 4333921 = 0)
    ∧ (25 * D ^ 2 + 954 * D * T + 8950 * D + 81 * T ^ 2 - 157746 * T + 244225 = 0) := by
  unfold leaderVert at ha
  subst ha; subst hs1
  exact ⟨by linear_combination (-3229440 : ℝ) * hS,
         by linear_combination (-278400 : ℝ) * hTid⟩

theorem quartic_from_conics {D T : ℝ}
    (hPS : 2809 * D ^ 2 + 954 * D * T - 2435402 * D + 81 * T ^ 2
      - 29682 * T + 4333921 = 0)
    (hPT : 25 * D ^ 2 + 954 * D * T + 8950 * D + 81 * T ^ 2
      - 157746 * T + 244225 = 0) :
    T = -(D ^ 2 - 878 * D + 1469) / 46 ∧ mwEqQuartic D = 0 := by
  have helim : D ^ 2 - 878 * D + 46 * T + 1469 = 0 := by
    linear_combination (1 / 2784 : ℝ) * hPS - (1 / 2784 : ℝ) * hPT
  have hT : T = -(D ^ 2 - 878 * D + 1469) / 46 := by linarith
  refine ⟨hT, ?_⟩
  subst hT
  unfold mwEqQuartic
  linear_combination (2116 : ℝ) * hPT

/-- **STEP 1, HEADLINE.**  The Sender endpoint spread of EVERY full-width P3
shocked equilibrium is a root of `mwEqQuartic`, and its Target endpoint spread
is the eliminated closed form.  No hypothesis on `α 1`. -/
theorem mwQuartic_of_equilibrium
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    mwEqQuartic (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) = 0
      ∧ (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0))
          = -((E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) ^ 2
              - 878 * (E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)) + 1469) / 46 := by
  obtain ⟨hs0, _⟩ := mwBottomResponse_zero E
  have hSid := mwSenderSpread_reduced_identity E
  have hTid := mwT_spread_identity E
  rw [hs0] at hSid hTid
  obtain ⟨hPS, hPT⟩ :=
    branchA_polynomials (D := E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0))
      (T := E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0))
      (a := E.α 1)
      (s1 := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1))
      (mwAlphaOne_pin E) (mwTopResponse_eq E) (by linarith) (by linarith)
  obtain ⟨h1, h2⟩ := quartic_from_conics hPS hPT
  exact ⟨h2, h1⟩

/-- **THE KEYSTONE.**  The Sender endpoint spread is PINNED for every
equilibrium of the full-width P3 shocked economy. -/
theorem mwSpread_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) = mwEqSenderSpread :=
  eq_mwEqSenderSpread_of_quartic_zero
    ⟨mwD_ge_seventeen_tenths E, mwD_le E⟩ (mwQuartic_of_equilibrium E).1

/-- The Target endpoint spread is pinned too. -/
theorem mwTargetSpread_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) = mwEqTargetSpread := by
  have h := (mwQuartic_of_equilibrium E).2
  rw [mwSpread_pinned E] at h
  rw [h, mwEqTargetSpread]

/-- **The Sender response FUNCTION is pinned**: every equilibrium induces the
same Sender rule `mwEqSenderRule` at every state and every action. -/
theorem mwSenderRule_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x a = mwEqSenderRule x a := by
  rw [mwSigmaDynTop_eq_clip_vertex_one E.V_S hx a]
  unfold mwEqSenderRule mwEqSenderVertex mwSenderVertexOne
  rw [mwSpread_pinned E]
  ring_nf

/-- Top-state compliance is pinned to the constructed leader policy's value. -/
theorem mwAlphaOne_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.α 1 = mwEqLeaderPolicy 1 := by
  rw [mwAlphaOne_pin E, mwSpread_pinned E, mwTargetSpread_pinned E,
    mwEqLeaderPolicy_one]
  unfold leaderVert mwEqLeaderVertex
  ring_nf

/-! ## 7.  The pin at a GENERAL state on `[2/5, 1]`.

The same complete-the-square works at every state: `Jgen`'s curvature `−29/12`
is independent of `x`, and its vertex is exactly `mwEqLeaderVertex x`.  Two
corner facts make the argument go through on `[2/5, 1]` without any new
hypothesis:

* the **lower** Sender clip never binds there (`mwEqSenderVertex_nonneg`);
* the **upper** Sender clip can only *lower* the Target's payoff, because the
  Target's marginal value of sanctions at the top selector,
  `x + a/2 − 1/2 + (9/100)·Δ_T`, is `≥ 1/20 > 0` on `[2/5,1]`.

So `trueJ(α(x)) ≤ Jgen(α(x))` while `trueJ(candidate) = Jgen(candidate)`, and
the equilibrium inequality runs the right way. -/

theorem mwEqSenderVertex_nonneg {x a : ℝ} (hx0 : 2 / 5 ≤ x) (ha : a ≤ 1) :
    0 ≤ mwEqSenderVertex x a := by
  obtain ⟨hlo, hhi⟩ := mwEqSenderSpread_bounds
  unfold mwEqSenderVertex; linarith

theorem mwEqSenderVertex_le_one_at_policy {x : ℝ} (hx1 : x ≤ 1) :
    mwEqSenderVertex x (mwEqLeaderPolicy x) ≤ 1 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  unfold mwEqLeaderPolicy
  rcases le_or_gt (mwEqLeaderVertex x) 0 with hw | hw
  · rw [max_eq_left hw]
    unfold mwEqLeaderVertex at hw
    unfold mwEqSenderVertex
    linarith
  · rw [max_eq_right hw.le]
    unfold mwEqSenderVertex mwEqLeaderVertex
    linarith

set_option maxHeartbeats 3200000 in
/-- **THE POLICY PIN.**  On `[2/5, 1]` every equilibrium's Target policy equals
the constructed leader policy.  Derived from `α_opt_shock x`; nothing assumed. -/
theorem mwAlpha_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx0 : 2 / 5 ≤ x) (hx1 : x ≤ 1) :
    E.α x = mwEqLeaderPolicy x := by
  have hxS : x ∈ Sanctions.S := ⟨by linarith, hx1⟩
  have hax : E.α x ∈ Sanctions.I := E.α_mem x hxS
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  have hcI : mwEqLeaderPolicy x ∈ Sanctions.I := mwEqLeaderPolicy_mem x hxS
  -- Sender responses: exact at the candidate, weakly below the vertex at `α x`
  have hs_c : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x
      (mwEqLeaderPolicy x) = mwEqSenderVertex x (mwEqLeaderPolicy x) := by
    rw [mwSenderRule_pinned E hxS]
    unfold mwEqSenderRule
    rw [min_eq_right (mwEqSenderVertex_le_one_at_policy hx1),
      max_eq_right (mwEqSenderVertex_nonneg hx0 hcI.2)]
  have hs_alpha : mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)
      = mwEqSenderRule x (E.α x) := mwSenderRule_pinned E hxS _
  have hs_alpha_le : mwEqSenderRule x (E.α x) ≤ mwEqSenderVertex x (E.α x) := by
    unfold mwEqSenderRule
    rw [max_eq_right (le_min (by norm_num) (mwEqSenderVertex_nonneg hx0 hax.2))]
    exact min_le_right _ _
  -- the equilibrium argmax, tested at the constructed candidate
  have hopt := E.α_opt_shock x hxS hcI
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x
        (mwEqLeaderPolicy x) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x) at hopt
  have hJa : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (E.α x)
      = mwU_T x (E.α x)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F x
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)))) := rfl
  have hJc : mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S) x (mwEqLeaderPolicy x)
      = mwU_T x (mwEqLeaderPolicy x)
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (mwEqLeaderPolicy x))
        + (9/10) * Sanctions.movAvgBCF one_pos E.V_T
            (Sanctions.clipS' (mechanismWitnessParams.F x
              (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x
                (mwEqLeaderPolicy x)))) := rfl
  rw [hJa, hJc] at hopt
  have hFa : mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem x _ hxS
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hFc : mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (mwEqLeaderPolicy x))
      ∈ Sanctions.S := mechanismWitnessParams.F_mem x _ hxS
        (mechanismWitnessParams.σ_dyn_top_mem_I _ _ _)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x))))
    (Sanctions.clipS' (mechanismWitnessParams.F x
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (mwEqLeaderPolicy x))))
  rw [Sanctions.clipS'_val_eq_of_mem hFa, Sanctions.clipS'_val_eq_of_mem hFc] at hslope
  rw [hs_alpha, hs_c] at hopt hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hopt hslope
  unfold mwU_T at hopt
  rw [mwTargetSpread_pinned E] at hslope
  -- the upper Sender clip can only lower the Target's payoff
  have hK : (0:ℝ) ≤ x + E.α x / 2 - 1 / 2 + (9 / 100) * mwEqTargetSpread := by
    linarith [hax.1]
  have hmul : mwEqSenderRule x (E.α x)
        * (x + E.α x / 2 - 1 / 2 + (9 / 100) * mwEqTargetSpread)
      ≤ mwEqSenderVertex x (E.α x)
        * (x + E.α x / 2 - 1 / 2 + (9 / 100) * mwEqTargetSpread) :=
    mul_le_mul_of_nonneg_right hs_alpha_le hK
  have hkey : Jgen mwEqSenderSpread mwEqTargetSpread x
        (max 0 (leaderVert mwEqSenderSpread mwEqTargetSpread x))
      ≤ Jgen mwEqSenderSpread mwEqTargetSpread x (E.α x) := by
    show Jgen mwEqSenderSpread mwEqTargetSpread x (mwEqLeaderPolicy x)
      ≤ Jgen mwEqSenderSpread mwEqTargetSpread x (E.α x)
    unfold Jgen senderVert
    unfold mwEqSenderVertex at hopt hmul hslope
    linarith [hopt, hslope, hmul]
  exact pin_of_Jgen_ge hax.1 hkey

/-! ## 8.  PAYOFF — the realized rule and the sub-basin results, for EVERY `E`. -/

/-- **The realized equilibrium sanction rule is pinned on `[2/5, 1]`.** -/
theorem mwRealizedRule_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx0 : 2 / 5 ≤ x) (hx1 : x ≤ 1) :
    mechanismWitnessParams.dynamicTopRealizedRule (mwSenderValueOne E.V_S) E.α x
      = mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x := by
  have hxS : x ∈ Sanctions.S := ⟨by linarith, hx1⟩
  show mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x (E.α x)
    = mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x
  rw [mwSenderRule_pinned E hxS, mwAlpha_pinned E hx0 hx1,
    mwEqDynamicTopRealizedRule_eq hxS]

theorem mwEqFixedState_le_one : mwEqFixedState ≤ 1 := by
  have := mwEqFixedState_bracket; linarith [this.2]

/-- **The ratchet, for EVERY equilibrium.** -/
theorem mwRatchet_on_Icc_fixed_allE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a : ℝ} (ha : 2 / 5 ≤ a) :
    ∀ x ∈ Set.Icc a mwEqFixedState,
      x ≤ mechanismWitnessParams.dynamicTopRealizedRule (mwSenderValueOne E.V_S) E.α x := by
  intro x hx
  rw [mwRealizedRule_pinned E (le_trans ha hx.1)
    (le_trans hx.2 mwEqFixedState_le_one)]
  exact mwEq_ratchet_on_Icc_fixed ha x hx

/-- **Forward invariance, for EVERY equilibrium.** -/
theorem mwStepF_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx0 : 2 / 5 ≤ x) (hx1 : x ≤ 1) :
    mechanismWitnessParams.dynamicTopLockInStepF (mwSenderValueOne E.V_S) E.α x
      = mechanismWitnessParams.dynamicTopLockInStepF
          (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x := by
  show mechanismWitnessParams.F x
      (mechanismWitnessParams.dynamicTopRealizedRule (mwSenderValueOne E.V_S) E.α x)
    = mechanismWitnessParams.F x
      (mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x)
  rw [mwRealizedRule_pinned E hx0 hx1]

theorem mwInvariant_on_Icc_fixed_allE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a : ℝ} (ha : 2 / 5 ≤ a) :
    ∀ x ∈ Set.Icc a mwEqFixedState,
      mechanismWitnessParams.dynamicTopLockInStepF (mwSenderValueOne E.V_S) E.α x
        ∈ Set.Icc a mwEqFixedState := by
  intro x hx
  rw [mwStepF_pinned E (le_trans ha hx.1) (le_trans hx.2 mwEqFixedState_le_one)]
  exact mwEq_invariant_on_Icc_fixed ha x hx

/-- The whole state path coincides with the constructed equilibrium's path,
and stays in the sub-basin. -/
theorem mwPathF_pinned
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a x₀ : ℝ} (ha : 2 / 5 ≤ a) (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) (n : ℕ) :
    mechanismWitnessParams.dynamicTopLockInPathF (mwSenderValueOne E.V_S) E.α x₀ n
        = mechanismWitnessParams.dynamicTopLockInPathF
            (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n
      ∧ mechanismWitnessParams.dynamicTopLockInPathF
            (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n
          ∈ Set.Icc a mwEqFixedState := by
  induction n with
  | zero => exact ⟨rfl, hx₀⟩
  | succ n ih =>
    obtain ⟨heq, hmem⟩ := ih
    constructor
    · rw [AbstractGame.Params.dynamicTopLockInPathF_succ,
        AbstractGame.Params.dynamicTopLockInPathF_succ, heq,
        mwStepF_pinned E (le_trans ha hmem.1) (le_trans hmem.2 mwEqFixedState_le_one)]
    · rw [AbstractGame.Params.dynamicTopLockInPathF_succ]
      exact mwEq_invariant_on_Icc_fixed ha _ hmem

/-- The whole state-path FUNCTION coincides with the constructed one. -/
theorem mwPathF_eq
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a x₀ : ℝ} (ha : 2 / 5 ≤ a) (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) :
    mechanismWitnessParams.dynamicTopLockInPathF (mwSenderValueOne E.V_S) E.α x₀
      = mechanismWitnessParams.dynamicTopLockInPathF
          (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ :=
  funext fun n => (mwPathF_pinned E ha hx₀ n).1

/-- The whole realized-sanction sequence coincides with the constructed one. -/
theorem mwSanctionsF_eq
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a x₀ : ℝ} (ha : 2 / 5 ≤ a) (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) :
    mechanismWitnessParams.dynamicTopLockInSanctionsF (mwSenderValueOne E.V_S) E.α x₀
      = mechanismWitnessParams.dynamicTopLockInSanctionsF
          (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ := by
  funext n
  obtain ⟨heq, hmem⟩ := mwPathF_pinned E ha hx₀ n
  show mechanismWitnessParams.dynamicTopRealizedRule (mwSenderValueOne E.V_S) E.α
      (mechanismWitnessParams.dynamicTopLockInPathF (mwSenderValueOne E.V_S) E.α x₀ n)
    = mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy
        (mechanismWitnessParams.dynamicTopLockInPathF
          (mwSenderValueOne mwEqSenderValue) mwEqLeaderPolicy x₀ n)
  rw [heq, mwRealizedRule_pinned E (le_trans ha hmem.1)
    (le_trans hmem.2 mwEqFixedState_le_one)]

/-- **Monotone state path, for EVERY equilibrium.** -/
theorem mwPath_mono_allE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a x₀ : ℝ} (ha : 2 / 5 ≤ a) (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) :
    Monotone (mechanismWitnessParams.dynamicTopLockInPathF
      (mwSenderValueOne E.V_S) E.α x₀) := by
  rw [mwPathF_eq E ha hx₀]; exact mwEq_path_mono ha hx₀

/-- **Monotone realized sanctions, for EVERY equilibrium.** -/
theorem mwSanctions_mono_allE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {a x₀ : ℝ} (ha : 2 / 5 ≤ a) (hx₀ : x₀ ∈ Set.Icc a mwEqFixedState) :
    Monotone (mechanismWitnessParams.dynamicTopLockInSanctionsF
      (mwSenderValueOne E.V_S) E.α x₀) := by
  rw [mwSanctionsF_eq E ha hx₀]; exact mwEq_sanctions_mono ha hx₀

/-- **The headline positive with fully rational data, for EVERY equilibrium.**
From any state in the RATIONAL interval `[2/5, 1129/2000]`, the realized
equilibrium state path and sanction path are both STRICTLY increasing forever,
and the state never leaves `[2/5, 1]` — no longer only for the constructed
equilibrium. -/
theorem p3_monotone_sanctions_from_rational_start_allE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x₀ : ℝ} (h0 : 2 / 5 ≤ x₀) (h1 : x₀ ≤ 1129 / 2000) :
    StrictMono (mechanismWitnessParams.dynamicTopLockInPathF
        (mwSenderValueOne E.V_S) E.α x₀) ∧
      StrictMono (mechanismWitnessParams.dynamicTopLockInSanctionsF
        (mwSenderValueOne E.V_S) E.α x₀) ∧
      (∀ n, mechanismWitnessParams.dynamicTopLockInPathF
        (mwSenderValueOne E.V_S) E.α x₀ n ∈ Set.Icc (2 / 5 : ℝ) 1) := by
  have hbr := mwEqFixedState_bracket
  have hlt : x₀ < mwEqFixedState := by linarith [hbr.1]
  have hmem : x₀ ∈ Set.Icc (2 / 5 : ℝ) mwEqFixedState := ⟨h0, le_of_lt hlt⟩
  have hpath := mwPathF_eq E (le_refl (2/5 : ℝ)) hmem
  have hsanc := mwSanctionsF_eq E (le_refl (2/5 : ℝ)) hmem
  obtain ⟨hp, hs, hin⟩ := p3_monotone_sanctions_from_rational_start h0 h1
  refine ⟨by rw [hpath]; exact hp, by rw [hsanc]; exact hs, fun n => ?_⟩
  rw [hpath]; exact hin n

/-! ### The rational-endpoint refutation, upgraded from ∀E to per-E.

`p3_no_rational_ratchet_invariant_subinterval`
(`Sanctions/Examples/P3SubBasinMonotonicity.lean:649`) refutes only the
*existence of a rational-endpoint sub-basin carried by every equilibrium*, and
is discharged by one instantiation.  Its docstring flags exactly this gap:
"It does **not** show that no equilibrium whatsoever has a rational-endpoint
sub-basin."  With the pin, it does now. -/

theorem p3_no_rational_ratchet_invariant_subinterval_perE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ¬ ∃ (a : ℝ) (b : ℚ), 2 / 5 ≤ a ∧ a < (b : ℝ) ∧ (b : ℝ) ≤ 1 ∧
      (∀ x ∈ Set.Icc a (b : ℝ), x ≤ mechanismWitnessParams.dynamicTopRealizedRule
          (mwSenderValueOne E.V_S) E.α x) ∧
      (∀ x ∈ Set.Icc a (b : ℝ), mechanismWitnessParams.dynamicTopLockInStepF
          (mwSenderValueOne E.V_S) E.α x ∈ Set.Icc a (b : ℝ)) := by
  rintro ⟨a, b, ha, hab, hb1, hr, hi⟩
  refine mwEqFixedState_irrational
    ⟨b, mwEq_subinterval_forces_fixed_endpoint ha hab.le hb1 ?_ ?_⟩
  · intro x hx
    rw [← mwRealizedRule_pinned E (le_trans ha hx.1) (le_trans hx.2 hb1)]
    exact hr x hx
  · intro x hx
    rw [← mwStepF_pinned E (le_trans ha hx.1) (le_trans hx.2 hb1)]
    exact hi x hx

/-! ### Two-equilibrium agreement (the uniqueness reading). -/

theorem mwSpread_eq_of_two
    (E F : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0)
      = F.V_S (Sanctions.clipS' 1) - F.V_S (Sanctions.clipS' 0) := by
  rw [mwSpread_pinned E, mwSpread_pinned F]

theorem mwAlpha_eq_of_two
    (E F : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx0 : 2 / 5 ≤ x) (hx1 : x ≤ 1) : E.α x = F.α x := by
  rw [mwAlpha_pinned E hx0 hx1, mwAlpha_pinned F hx0 hx1]

theorem mwSenderRule_eq_of_two
    (E F : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) x a
      = mechanismWitnessParams.σ_dyn_top (mwSenderValueOne F.V_S) x a := by
  rw [mwSenderRule_pinned E hx, mwSenderRule_pinned F hx]

/-- **THE UPGRADED HEADLINE.**  The full-width P3 shocked economy carries a
non-degenerate ratcheting, forward-invariant sub-basin — with right endpoint
bracketed by explicit rationals — on which the state path and the realized
sanction path are monotone, **for every equilibrium of the specialization**,
not merely for the explicitly constructed one. -/
theorem p3_exists_ratchet_invariant_subinterval_uniform :
    ∃ b : ℝ, 1129 / 2000 < b ∧ b < 2823 / 5000 ∧
      ∀ E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Set.Icc (2 / 5 : ℝ) b,
            x ≤ mechanismWitnessParams.dynamicTopRealizedRule
              (mwSenderValueOne E.V_S) E.α x) ∧
        (∀ x ∈ Set.Icc (2 / 5 : ℝ) b,
            mechanismWitnessParams.dynamicTopLockInStepF
              (mwSenderValueOne E.V_S) E.α x ∈ Set.Icc (2 / 5 : ℝ) b) ∧
        (∀ x₀ ∈ Set.Icc (2 / 5 : ℝ) b,
            Monotone (mechanismWitnessParams.dynamicTopLockInPathF
              (mwSenderValueOne E.V_S) E.α x₀) ∧
            Monotone (mechanismWitnessParams.dynamicTopLockInSanctionsF
              (mwSenderValueOne E.V_S) E.α x₀)) := by
  have hbr := mwEqFixedState_bracket
  exact ⟨mwEqFixedState, hbr.1, hbr.2, fun E =>
    ⟨mwRatchet_on_Icc_fixed_allE E le_rfl,
     mwInvariant_on_Icc_fixed_allE E le_rfl,
     fun x₀ hx₀ => ⟨mwPath_mono_allE E le_rfl hx₀, mwSanctions_mono_allE E le_rfl hx₀⟩⟩⟩

/-- The weaker per-equilibrium reading, for callers that want it in that shape.
Note the interval is the *same* one in every instance --- that is the content of
`p3_exists_ratchet_invariant_subinterval_uniform` above, and the reason this
corollary is strictly weaker. -/
theorem p3_exists_ratchet_invariant_subinterval_allE
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ∃ b : ℝ, 1129 / 2000 < b ∧ b < 2823 / 5000 ∧
      (∀ x ∈ Set.Icc (2 / 5 : ℝ) b,
          x ≤ mechanismWitnessParams.dynamicTopRealizedRule
            (mwSenderValueOne E.V_S) E.α x) ∧
      (∀ x ∈ Set.Icc (2 / 5 : ℝ) b,
          mechanismWitnessParams.dynamicTopLockInStepF
            (mwSenderValueOne E.V_S) E.α x ∈ Set.Icc (2 / 5 : ℝ) b) ∧
      (∀ x₀ ∈ Set.Icc (2 / 5 : ℝ) b,
          Monotone (mechanismWitnessParams.dynamicTopLockInPathF
            (mwSenderValueOne E.V_S) E.α x₀) ∧
          Monotone (mechanismWitnessParams.dynamicTopLockInSanctionsF
            (mwSenderValueOne E.V_S) E.α x₀)) := by
  obtain ⟨b, hlo, hhi, hall⟩ := p3_exists_ratchet_invariant_subinterval_uniform
  exact ⟨b, hlo, hhi, (hall E).1, (hall E).2.1, (hall E).2.2⟩

/-! ## 9.  Rule-11 non-vacuity and consistency probes. -/

example : Nonempty ((mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :=
  ⟨mwEqEquilibrium⟩

/-- The pin agrees with the constructed equilibrium (it must — but this
exhibits it rather than asserting it). -/
example : mwEqEquilibrium.α 1 = mwEqLeaderPolicy 1 := mwAlphaOne_pinned mwEqEquilibrium

/-- Consistency with the previously proved arbitrary-`E` lower bound on
top-state compliance (`mwAlphaOne_ge_5_12`): the pinned value clears it. -/
example (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (5:ℝ)/12 ≤ E.α 1 := by
  rw [mwAlphaOne_pinned E, mwEqLeaderPolicy_one]
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  unfold mwEqLeaderVertex; linarith

/-- **Independent cross-check against `mwAlphaOne_lb`** (`P3WeakFloorSpreadBound
.lean:733`), the previously proved arbitrary-`E` lower bound
`α(1) ≥ 15181/58300 + (12/53)·s(1)`.  Re-derived here *from the pin alone*,
without citing that theorem: if the pin were the wrong first-order condition,
this would fail. -/
example (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    15181/58300
        + (12/53) * mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1)
      ≤ E.α 1 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  rw [mwTopResponse_eq E, mwSpread_pinned E, mwAlphaOne_pinned E, mwEqLeaderPolicy_one]
  unfold mwEqLeaderVertex
  linarith

/-- Cross-check against `mwTopResponse_ge_29_42`, re-derived from the pin. -/
example (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    (29:ℝ)/42 ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 (E.α 1) := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  rw [mwTopResponse_eq E, mwSpread_pinned E, mwAlphaOne_pinned E, mwEqLeaderPolicy_one]
  unfold mwEqLeaderVertex
  linarith

/-- The pin has CONTENT: the pinned policy is non-constant on `[2/5, 1]`, so
`mwAlpha_pinned` is not "everything equals a constant". -/
example : mwEqLeaderPolicy (2/5 : ℝ) = 0 ∧ 0 < mwEqLeaderPolicy 1 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  refine ⟨?_, ?_⟩
  · unfold mwEqLeaderPolicy; rw [max_eq_left]; unfold mwEqLeaderVertex; linarith
  · rw [mwEqLeaderPolicy_one]; exact mwEqLeaderVertex_one_pos

/-- Top-state compliance is strictly interior for EVERY equilibrium — a new
arbitrary-`E` fact (previously only `α(1) ≥ 5/12` was available, with no upper
bound below `1`). -/
example (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    0 < E.α 1 ∧ E.α 1 < 1 := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  rw [mwAlphaOne_pinned E, mwEqLeaderPolicy_one]
  unfold mwEqLeaderVertex
  constructor <;> linarith

/-! ### SCOPE EXHIBIT — why `2/5` is not gratuitous.

The general-`x` pin needs the Sender clip to move the Target's payoff in the
*right* direction: when the response is clipped, the clipped value must be on
the losing side.  On `[2/5, 1]` the lower clip never binds and the marginal
value of sanctions `x + a/2 − 1/2 + (9/100)Δ_T` is `≥ 1/20 > 0`, so the upper
clip only lowers the payoff.  Strictly below `≈0.379` that breaks: there are
feasible actions at which the Sender vertex is negative (lower clip binds,
raising the realized sanction above the vertex) while the marginal value is
still positive — the inequality then runs the wrong way.  This exhibits it at
`x = 1/5`, `a = 1`. -/
example : mwEqSenderVertex (1/5 : ℝ) 1 < 0
    ∧ 0 < (1/5 : ℝ) + 1/2 - 1/2 + (9/100) * mwEqTargetSpread := by
  obtain ⟨hSlo, hShi⟩ := mwEqSenderSpread_bounds
  obtain ⟨hTlo, hThi⟩ := mwEqTargetSpread_bounds
  unfold mwEqSenderVertex
  constructor <;> linarith

end

/-! ## 10.  Axiom audit (Rule 10). -/

#print axioms P3Pin.mwEqQuartic_strictAntiOn
#print axioms P3Pin.eq_mwEqSenderSpread_of_quartic_zero
#print axioms P3Pin.Jgen_vertex_form
#print axioms P3Pin.pin_of_Jgen_ge
#print axioms P3Pin.mwT_spread_identity
#print axioms P3Pin.mwAlphaOne_pin
#print axioms P3Pin.mwBottomResponse_zero
#print axioms P3Pin.mwQuartic_of_equilibrium
#print axioms P3Pin.mwSpread_pinned
#print axioms P3Pin.mwTargetSpread_pinned
#print axioms P3Pin.mwSenderRule_pinned
#print axioms P3Pin.mwAlphaOne_pinned
#print axioms P3Pin.mwAlpha_pinned
#print axioms P3Pin.mwRealizedRule_pinned
#print axioms P3Pin.mwRatchet_on_Icc_fixed_allE
#print axioms P3Pin.mwInvariant_on_Icc_fixed_allE
#print axioms P3Pin.mwPathF_pinned
#print axioms P3Pin.mwPath_mono_allE
#print axioms P3Pin.mwSanctions_mono_allE
#print axioms P3Pin.p3_exists_ratchet_invariant_subinterval_uniform
#print axioms P3Pin.p3_exists_ratchet_invariant_subinterval_allE
#print axioms P3Pin.mwPathF_eq
#print axioms P3Pin.mwSanctionsF_eq
#print axioms P3Pin.p3_monotone_sanctions_from_rational_start_allE
#print axioms P3Pin.p3_no_rational_ratchet_invariant_subinterval_perE
#print axioms P3Pin.mwSpread_eq_of_two
#print axioms P3Pin.mwAlpha_eq_of_two
#print axioms P3Pin.mwSenderRule_eq_of_two
#print axioms P3Pin.mwStepF_pinned
#print axioms P3Pin.mwEqSenderVertex_le_one_at_policy

end P3Pin
end Sanctions.Examples
