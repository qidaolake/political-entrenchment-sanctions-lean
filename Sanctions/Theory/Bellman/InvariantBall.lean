/-
Sanctions/Theory/Bellman/InvariantBall.lean

**Gap 4 discharge (audit-33 follow-up): `ValueClass.ofBall` on the
sup-norm ball, with `IsInvariant` discharged from primitive payoff
cube bounds.**

The audit-33 round added `ValueClass` (`InvariantValueClass.lean`) but
left `IsInvariant` as a theorem-parameter primitive. The most natural
concrete carrier is the sup-norm ball `{V : Val | ‖V‖ ≤ M}` for
`M ≥ max(cube_T / (1 - β_T), cube_S / (1 - β_S))` where `cube_T` /
`cube_S` are cube bounds on `|U_T|` / `|U_S|` over the unit cube
`I × I × I` (both finite by compactness + continuity).

The two key lemmas are sup-norm bounds on the joint Bellman operators:

* `jointTarget_BCF_norm_le`: `‖jointTarget_BCF V_T V_S h‖
  ≤ cube_T + β_T · ‖V_T‖`
* `bellmanS_BCF_norm_le`: `‖bellmanS_BCF α hα V_S‖
  ≤ cube_S + β_S · ‖V_S‖`

Combined with the contraction inequalities
`cube_T + β_T · M ≤ M` (i.e. `M ≥ cube_T / (1 - β_T)`) and similarly
for Sender, the ball is preserved — exactly `ValueClass.IsInvariant`.

## Rule compliance

**Rule 1.** No new strategy. The ball is a sup-norm-bounded set of
value functions; the dynamics use the existing equilibrium-derived
operators `jointTarget_BCF_on`, `jointSender_BCF_on`.

**Rule 3.** No new `Params` fields. The cube bounds `cube_T`,
`cube_S` are theorem-parameter primitives; uniqueness predicates
are the existing `DynamicArgmaxUnique`, `TargetArgmaxUnique`
restricted to the ball. Strictly weaker than the global-uniqueness
hypothesis of audit-32's
`exists_feedbackStackelberg_from_uniqueness_row_bounds`.

**Rule 5.** Fully parametric over `(p, M, cube_T, cube_S)` and the
uniqueness primitives.
-/

import Sanctions.Theory.Bellman.InvariantValueClass

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Auto-derived primitive cube bounds for `U_T`, `U_S`
(Round 23 — assumption shrink)

The cube bounds `cube_T`, `cube_S` on `|U_T|`, `|U_S|` over the unit
cube `I × I × I` are no longer user-supplied scalars: they follow
directly from the `Params.U_T_continuous` / `U_S_continuous`
continuity fields plus compactness of `I × I × I`, via
`Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous` (SLP 1989
Theorem 3.1, Weierstrass extreme-value theorem). The two thin
wrappers below are the `Params`-level discharge points; the
underlying mathematics lives in `Foundations/StokeyLucas.lean`.

Round-17 (`bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz` in
`InvariantLipBall.lean`), Round-20
(`jointTarget_BCF_mem_valLipBall_of_integrand_lipschitz`), and the
present file's `ofBall_IsInvariant_of_cube_bounds` all consume an
`hU_T_cube` / `hU_S_cube` hypothesis whose existential closure is
exactly what these two wrappers produce. -/

/-- **Auto-discharge of the `cube_T` primitive.**
From `p.U_T_continuous` (Target payoff `U_T : ℝ → ℝ → ℝ → ℝ` is
jointly continuous in `(x, a, s)`) plus compactness of the unit
cube `I × I × I = Icc 0 1 × Icc 0 1 × Icc 0 1`, the absolute value
`|p.U_T x a s|` is bounded by some nonnegative constant `cube_T`
uniformly over `(x, a, s) ∈ I × I × I`.

This recasts the previously user-supplied `cube_T : ℝ` scalar +
`hU_T_cube` hypothesis pair as a derived `∃ cube_T ≥ 0, …`
existence statement, eliminating the scalar from the assumption
surface of `ofBall_IsInvariant_of_cube_bounds` and the Round-20
Target Lipschitz cone preservation lemma. Discharger style: SLP
Theorem 3.1 (`cube_bound_unitCube_of_continuous`). -/
theorem cube_bound_U_T :
    ∃ cube_T : ℝ, 0 ≤ cube_T ∧
      ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
        |p.U_T x a s| ≤ cube_T :=
  Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous p.U_T_continuous

/-- **Auto-discharge of the `cube_S` primitive.**
From `p.U_S_continuous` (Sender payoff `U_S : ℝ → ℝ → ℝ → ℝ` is
jointly continuous in `(x, a, s)`) plus compactness of the unit
cube `I × I × I`, the absolute value `|p.U_S x a s|` is bounded by
some nonnegative constant `cube_S` uniformly over
`(x, a, s) ∈ I × I × I`.

Sender-side companion of `cube_bound_U_T`. Eliminates the scalar
`cube_S : ℝ` + `hU_S_cube` hypothesis pair from
`ofBall_IsInvariant_of_cube_bounds` and the Round-17 Sender
Lipschitz cone preservation lemma
(`bellmanS_BCF_mem_valLipBall_of_payoff_lipschitz`). Discharger
style: SLP Theorem 3.1
(`cube_bound_unitCube_of_continuous`). -/
theorem cube_bound_U_S :
    ∃ cube_S : ℝ, 0 ≤ cube_S ∧
      ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
        |p.U_S x a s| ≤ cube_S :=
  Sanctions.StokeyLucas.cube_bound_unitCube_of_continuous p.U_S_continuous

/-! ## The sup-norm ball in `Val` -/

/-- The closed sup-norm ball of radius `M` in `Val = ↥S →ᵇ ℝ`. -/
def valBall (M : ℝ) : Set Val := {V : Val | ‖V‖ ≤ M}

theorem valBall_isClosed (M : ℝ) : IsClosed (valBall M) :=
  isClosed_le continuous_norm continuous_const

theorem zero_mem_valBall {M : ℝ} (hM : 0 ≤ M) :
    (0 : Val) ∈ valBall M := by
  show ‖(0 : Val)‖ ≤ M
  simp [hM]

theorem valBall_nonempty {M : ℝ} (hM : 0 ≤ M) :
    (valBall M).Nonempty := ⟨0, zero_mem_valBall hM⟩

theorem mem_valBall_iff {M : ℝ} {V : Val} :
    V ∈ valBall M ↔ ‖V‖ ≤ M := Iff.rfl

/-! ## Sup-norm bound for the joint Target Bellman BCF -/

/-- Sup-norm bound for `jointTarget_BCF V_T V_S h`: if `|U_T|` is
cube-bounded by `cube_T` on `I × I × I` and `‖V_T‖` is bounded by
`R_T`, then `‖jointTarget_BCF V_T V_S h‖ ≤ cube_T + β_T · R_T`.

Round BJ1.2 (2026-10-07): the three sign binders are derived, not assumed.
`0 ≤ β_T` is the `Params` field `β_T_mem.1`; `0 ≤ R_T` follows from
`‖V_T‖ ≤ R_T`; `0 ≤ cube_T` follows from the cube bound at the corner
`(0, 0, 0)`. General in `F`: the transition enters only through `clipS'`.

Round BJ4.3 (2026-10-08): the state-local operator takes compliance-local
uniqueness, so it is applied to `h_unique.toOnI`; the statement is otherwise
unchanged. -/
theorem jointTarget_BCF_norm_le
    (V_T V_S : Val) (h_unique : p.DynamicArgmaxUnique V_S)
    {cube_T R_T : ℝ}
    (hV_T_norm : ‖V_T‖ ≤ R_T)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T) :
    ‖p.jointTarget_BCF_on_S V_T V_S h_unique.toOnI‖ ≤ cube_T + p.β_T * R_T := by
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have hR_T_nn : 0 ≤ R_T := (norm_nonneg V_T).trans hV_T_norm
  have hcube_T_nn : 0 ≤ cube_T := (abs_nonneg _).trans
    (hU_T_cube 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩)
  have h_rhs_nn : 0 ≤ cube_T + p.β_T * R_T :=
    add_nonneg hcube_T_nn (mul_nonneg hβ_T_nn hR_T_nn)
  rw [BoundedContinuousFunction.norm_le h_rhs_nn]
  intro x
  show |p.jointTarget_BCF_on_S V_T V_S h_unique.toOnI x| ≤ cube_T + p.β_T * R_T
  rw [p.jointTarget_BCF_on_S_apply V_T V_S h_unique.toOnI x]
  -- Pointwise bound on the integrand at each a ∈ I.
  have h_x_mem : x.val ∈ Sanctions.I := by
    refine ⟨?_, ?_⟩
    · exact x.property.1
    · exact x.property.2
  have h_int_bound : ∀ a ∈ Sanctions.I,
      |p.joint_T_integrand V_T V_S x.val a| ≤ cube_T + p.β_T * R_T := by
    intro a ha
    simp only [joint_T_integrand]
    -- = |U_T(x, a, σ_dyn V_S x a) + β_T * V_T (clipS' (F x (σ_dyn V_S x a)))|
    -- ≤ |U_T| + β_T * |V_T| ≤ cube_T + β_T * ‖V_T‖ ≤ cube_T + β_T * R_T
    have h_σ_mem : p.σ_dyn V_S x.val a ∈ Sanctions.I :=
      p.σ_dyn_mem V_S x.val a
    have h_U_bound :
        |p.U_T x.val a (p.σ_dyn V_S x.val a)| ≤ cube_T :=
      hU_T_cube x.val h_x_mem a ha (p.σ_dyn V_S x.val a) h_σ_mem
    have h_V_bound :
        |V_T (Sanctions.clipS'
          (p.F x.val (p.σ_dyn V_S x.val a)))| ≤ ‖V_T‖ := by
      have := BoundedContinuousFunction.norm_coe_le_norm V_T
        (Sanctions.clipS' (p.F x.val (p.σ_dyn V_S x.val a)))
      rwa [Real.norm_eq_abs] at this
    calc |p.U_T x.val a (p.σ_dyn V_S x.val a)
            + p.β_T * V_T (Sanctions.clipS'
              (p.F x.val (p.σ_dyn V_S x.val a)))|
        ≤ |p.U_T x.val a (p.σ_dyn V_S x.val a)|
            + |p.β_T * V_T (Sanctions.clipS'
              (p.F x.val (p.σ_dyn V_S x.val a)))| := abs_add_le _ _
      _ = |p.U_T x.val a (p.σ_dyn V_S x.val a)|
            + p.β_T * |V_T (Sanctions.clipS'
              (p.F x.val (p.σ_dyn V_S x.val a)))| := by
            rw [abs_mul, abs_of_nonneg hβ_T_nn]
      _ ≤ cube_T + p.β_T * ‖V_T‖ := by
            gcongr
      _ ≤ cube_T + p.β_T * R_T := by
            gcongr
  -- Image is nonempty (0 ∈ I) and bounded.
  have h_img_ne : ((fun a => p.joint_T_integrand V_T V_S x.val a) ''
                    Sanctions.I).Nonempty :=
    ⟨_, ⟨0, by simp [Sanctions.I], rfl⟩⟩
  have h_img_bdd : BddAbove
      ((fun a => p.joint_T_integrand V_T V_S x.val a) '' Sanctions.I) := by
    refine ⟨cube_T + p.β_T * R_T, ?_⟩
    rintro y ⟨a, ha, rfl⟩
    have := h_int_bound a ha
    linarith [abs_le.mp this]
  -- Upper bound: sSup ≤ cube_T + β_T * R_T.
  have h_sSup_upper :
      sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) '' Sanctions.I)
        ≤ cube_T + p.β_T * R_T := by
    apply csSup_le h_img_ne
    rintro y ⟨a, ha, rfl⟩
    have := h_int_bound a ha
    linarith [abs_le.mp this]
  -- Lower bound: sSup ≥ -(cube_T + β_T * R_T).
  have h_sSup_lower :
      -(cube_T + p.β_T * R_T) ≤
        sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) ''
                Sanctions.I) := by
    obtain ⟨a₀, ha₀⟩ := h_img_ne
    -- a₀ is some specific point a*, hY : integrand x.val a* = a₀
    -- Need: -(cube_T + β_T*R_T) ≤ sSup ≥ a₀
    have h_a₀_lower : -(cube_T + p.β_T * R_T) ≤ a₀ := by
      -- a₀ = integrand at some a*. By h_int_bound, |a₀| ≤ cube_T + β_T*R_T.
      obtain ⟨a, ha, rfl⟩ := ha₀
      have := h_int_bound a ha
      linarith [abs_le.mp this]
    have h_a₀_le_sSup :
        a₀ ≤ sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) ''
                    Sanctions.I) :=
      le_csSup h_img_bdd ha₀
    linarith
  exact abs_le.mpr ⟨h_sSup_lower, h_sSup_upper⟩

/-! ## Sup-norm bound for the Sender Bellman BCF -/

/-- Sup-norm bound for `bellmanS_BCF α hα V_S`: if `|U_S|` is
cube-bounded by `cube_S` on `I × I × I` and `‖V_S‖` is bounded by
`R_S`, then `‖bellmanS_BCF α hα V_S‖ ≤ cube_S + β_S · R_S`.

Round BJ1.2 (2026-10-07): the three sign binders are derived, not assumed.
`0 ≤ β_S` is the `Params` field `β_S_mem.1`; `0 ≤ R_S` follows from
`‖V_S‖ ≤ R_S`; `0 ≤ cube_S` follows from the cube bound at the corner
`(0, 0, 0)`. General in `F`: the transition enters only through `clipS'`. -/
theorem bellmanS_BCF_norm_le
    {α : ℝ → ℝ} (hα : Continuous α)
    (α_mem : ∀ x : ℝ, α x ∈ Sanctions.I)
    (V_S : Val)
    {cube_S R_S : ℝ}
    (hV_S_norm : ‖V_S‖ ≤ R_S)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S) :
    ‖p.bellmanS_BCF α hα V_S‖ ≤ cube_S + p.β_S * R_S := by
  have hβ_S_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have hR_S_nn : 0 ≤ R_S := (norm_nonneg V_S).trans hV_S_norm
  have hcube_S_nn : 0 ≤ cube_S := (abs_nonneg _).trans
    (hU_S_cube 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩)
  have h_rhs_nn : 0 ≤ cube_S + p.β_S * R_S :=
    add_nonneg hcube_S_nn (mul_nonneg hβ_S_nn hR_S_nn)
  rw [BoundedContinuousFunction.norm_le h_rhs_nn]
  intro x
  show |p.bellmanS_BCF α hα V_S x| ≤ cube_S + p.β_S * R_S
  -- bellmanS_BCF α hα V_S x = bellmanS_at α (V_S coerce) x.val = sSup (integrandS image)
  have h_apply : p.bellmanS_BCF α hα V_S x =
      sSup ((fun s => p.integrandS α (fun y => V_S y) (x.val, s)) ''
              Sanctions.I) := rfl
  rw [h_apply]
  have h_x_mem : x.val ∈ Sanctions.I := ⟨x.property.1, x.property.2⟩
  have h_α_mem : α x.val ∈ Sanctions.I := α_mem x.val
  -- Pointwise integrand bound.
  have h_int_bound : ∀ s ∈ Sanctions.I,
      |p.integrandS α (fun y => V_S y) (x.val, s)|
        ≤ cube_S + p.β_S * R_S := by
    intro s hs
    simp only [integrandS]
    have h_U_bound : |p.U_S x.val (α x.val) s| ≤ cube_S :=
      hU_S_cube x.val h_x_mem (α x.val) h_α_mem s hs
    have h_V_bound :
        |V_S (Sanctions.clipS' (p.F x.val s))| ≤ ‖V_S‖ := by
      have := BoundedContinuousFunction.norm_coe_le_norm V_S
        (Sanctions.clipS' (p.F x.val s))
      rwa [Real.norm_eq_abs] at this
    calc |p.U_S x.val (α x.val) s
            + p.β_S * V_S (Sanctions.clipS' (p.F x.val s))|
        ≤ |p.U_S x.val (α x.val) s|
            + |p.β_S * V_S (Sanctions.clipS' (p.F x.val s))| :=
          abs_add_le _ _
      _ = |p.U_S x.val (α x.val) s|
            + p.β_S * |V_S (Sanctions.clipS' (p.F x.val s))| := by
          rw [abs_mul, abs_of_nonneg hβ_S_nn]
      _ ≤ cube_S + p.β_S * ‖V_S‖ := by gcongr
      _ ≤ cube_S + p.β_S * R_S := by gcongr
  have h_img_ne : ((fun s => p.integrandS α (fun y => V_S y) (x.val, s)) ''
                    Sanctions.I).Nonempty :=
    ⟨_, ⟨0, by simp [Sanctions.I], rfl⟩⟩
  have h_img_bdd : BddAbove
      ((fun s => p.integrandS α (fun y => V_S y) (x.val, s)) ''
        Sanctions.I) := by
    refine ⟨cube_S + p.β_S * R_S, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have := h_int_bound s hs
    linarith [abs_le.mp this]
  have h_sSup_upper :
      sSup ((fun s => p.integrandS α (fun y => V_S y) (x.val, s)) ''
              Sanctions.I)
        ≤ cube_S + p.β_S * R_S := by
    apply csSup_le h_img_ne
    rintro y ⟨s, hs, rfl⟩
    have := h_int_bound s hs
    linarith [abs_le.mp this]
  have h_sSup_lower :
      -(cube_S + p.β_S * R_S) ≤
        sSup ((fun s => p.integrandS α (fun y => V_S y) (x.val, s)) ''
                Sanctions.I) := by
    obtain ⟨a₀, ha₀⟩ := h_img_ne
    have h_a₀_lower : -(cube_S + p.β_S * R_S) ≤ a₀ := by
      obtain ⟨s, hs, rfl⟩ := ha₀
      have := h_int_bound s hs
      linarith [abs_le.mp this]
    have h_a₀_le_sSup := le_csSup h_img_bdd ha₀
    linarith
  exact abs_le.mpr ⟨h_sSup_lower, h_sSup_upper⟩

/-! ## `ValueClass.ofBall` constructor -/

namespace ValueClass

/-- Construct a `ValueClass` from the sup-norm ball plus uniqueness
primitives restricted to the ball. The carrier is `valBall M`. -/
noncomputable def ofBall
    {M : ℝ} (hM : 0 ≤ M)
    (h_unique_S : ∀ V_S ∈ valBall M, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valBall M, ∀ V_S ∈ valBall M,
        p.TargetArgmaxUnique V_T V_S) :
    p.ValueClass where
  carrier := valBall M
  isClosed := valBall_isClosed M
  nonempty := valBall_nonempty hM
  sender_unique_on := h_unique_S
  target_unique_on := h_unique_T

end ValueClass

/-! ## `IsInvariant` discharge for the ball -/

/-- **`IsInvariant` for the ball, from primitive payoff cube bounds.**

Given cube bounds on `|U_T|` and `|U_S|` over `I × I × I`, and the
sup-norm contraction inequalities `cube_T + β_T · M ≤ M` and
`cube_S + β_S · M ≤ M` (equivalently `M ≥ cube_T / (1 - β_T)` and
`M ≥ cube_S / (1 - β_S)`), the joint Bellman operator pair preserves
the ball `valBall M` — every joint Target output has norm
`≤ cube_T + β_T · M ≤ M`, and every joint Sender output has norm
`≤ cube_S + β_S · M ≤ M`.

Round BJ1.2 (2026-10-07): the binders `0 ≤ cube_T` and `0 ≤ cube_S` are
deleted; each follows from its cube bound at the corner `(0, 0, 0)`. The radius
sign `hM` stays, because the ball constructor `ofBall` needs it for
nonemptiness. General in `F`. -/
theorem ValueClass.ofBall_IsInvariant_of_cube_bounds
    {M cube_T cube_S : ℝ} (hM : 0 ≤ M)
    (h_unique_S : ∀ V_S ∈ valBall M, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valBall M, ∀ V_S ∈ valBall M,
        p.TargetArgmaxUnique V_T V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
    (hU_S_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_S x a s| ≤ cube_S)
    (hR_T_margin : cube_T + p.β_T * M ≤ M)
    (hR_S_margin : cube_S + p.β_S * M ≤ M) :
    (ValueClass.ofBall p hM h_unique_S h_unique_T).IsInvariant := by
  intro V_T V_S
  have hV_T_norm : ‖V_T.val‖ ≤ M := V_T.property
  have hV_S_norm : ‖V_S.val‖ ≤ M := V_S.property
  refine ⟨?_, ?_⟩
  · -- jointTarget_BCF_on V_T V_S ∈ valBall M
    change ‖p.jointTarget_BCF_on_S V_T.val V_S.val
              (h_unique_S V_S.val V_S.property).toOnI‖ ≤ M
    exact le_trans
      (p.jointTarget_BCF_norm_le V_T.val V_S.val (h_unique_S V_S.val V_S.property)
        hV_T_norm hU_T_cube)
      hR_T_margin
  · -- jointSender_BCF_on V_T V_S ∈ valBall M
    change ‖p.bellmanS_BCF
              ((ValueClass.ofBall p hM h_unique_S h_unique_T).α_on V_T V_S)
              ((ValueClass.ofBall p hM h_unique_S h_unique_T).α_on_continuous V_T V_S)
              V_S.val‖ ≤ M
    exact le_trans
      (p.bellmanS_BCF_norm_le _
        (fun x =>
          (ValueClass.ofBall p hM h_unique_S h_unique_T).α_on_mem V_T V_S x)
        V_S.val hV_S_norm hU_S_cube)
      hR_S_margin

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
