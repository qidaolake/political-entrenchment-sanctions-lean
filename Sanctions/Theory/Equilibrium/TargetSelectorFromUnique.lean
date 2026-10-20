/-
Sanctions/Theory/Equilibrium/TargetSelectorFromUnique.lean

**`DynamicTargetSelector.of_unique`: continuous leader selector from
uniqueness of the leader's joint Bellman argmax.**

`Theory/Equilibrium/JointExistenceFromPrimitives.lean` takes a
`DynamicTargetSelector` as an external structural primitive. This file
discharges that primitive from a **uniqueness of leader argmax**
hypothesis via the same Berge sequential-continuity machinery used in
`Theory/Equilibrium/BergeContinuity.lean` for the Sender side.

The Berge step. The leader's joint Bellman integrand
`joint_T_integrand V_T V_S x a = U_T(x, a, σ_dyn V_S x a) + β_T · V_T(F(x, σ_dyn V_S x a))`
is jointly continuous in `(x, a)` under uniqueness of the Sender
dynamic argmax (`joint_T_integrand_continuous_jointly_of_unique`).
The argmax of this objective in `a` on the compact set `Sanctions.I`
exists by `IsCompact.exists_isMaxOn`. Selecting via `Classical.choose`
gives `targetArgmax`. Under uniqueness of the leader argmax at every
`x` (`TargetArgmaxUnique`), Berge's sequential-continuity theorem
(compactness of `[0,1]` + Bolzano-Weierstrass + uniqueness for cluster
points) yields continuity of `targetArgmax` in `x`. Packaging this
with feasibility and the `Classical.choose` argmax property gives a
`DynamicTargetSelector` instance.

Combined with global Sender argmax uniqueness, this reduces the
operator-level equilibrium-existence theorem
`exists_feedbackStackelberg_from_selector_row_bounds` to **two
uniqueness primitives + row-Lipschitz bounds** — the
`DynamicTargetSelector` primitive itself is no longer external.

## Rule compliance

**Rule 1.** `targetArgmax V_T V_S x` is the leader's equilibrium
argmax of `joint_T_integrand V_T V_S x ·` on `Sanctions.I` via
`Classical.choose` of `IsCompact.exists_isMaxOn`. No hand-chosen
policy appears.

**Rule 3.** All new declarations are local Props (`TargetArgmaxUnique`)
or `noncomputable def`s parametric over a Params instance. No new
fields on `AbstractGame.Params`; no new Postulates; no new global
load-bearing `Prop`. The uniqueness hypotheses are uniformly the
canonical sufficient pattern (strict concavity / strict
single-crossing), matching `DynamicArgmaxUnique` and
`σ_dyn_continuous_of_unique`.

**Rule 5.** Fully parametric over `(p, V_T, V_S, h_unique_S, h_unique_T)`.
-/

import Sanctions.Theory.Equilibrium.JointExistenceFromPrimitives
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Uniqueness predicate for the leader argmax -/

/-- **Global uniqueness of the leader's joint Bellman argmax (all states).**
The legacy `∀ x : ℝ` form, retained for the *global* Berge route
(`targetArgmax_continuous_of_unique` needs a selector continuous on all
of `ℝ`). Genuinely stronger than the state-local `TargetArgmaxUnique`:
at unphysical states the follower response `σ_dyn` is not pinned, so
leader-argmax uniqueness can fail there for concrete witnesses. -/
def TargetArgmaxUniqueGlobal (V_T V_S : Val) : Prop :=
  ∀ x : ℝ, ∀ a₁ a₂ : ℝ, a₁ ∈ Sanctions.I → a₂ ∈ Sanctions.I →
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₁ →
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₂ →
    a₁ = a₂

/-- **State-local uniqueness of the leader's joint Bellman argmax
(Design A, leader side).** Uniqueness only at *physical* states
`x ∈ S = [0,1]` — the economically meaningful domain (the clamped
dynamics never leave `[0,1]`, and the state-local machinery
(`targetArgmaxOnS_continuous`, `α_on_ext`) only invokes uniqueness
there). The canonical economic sufficient condition is strict concavity
or strict monotonicity of the joint Target return
`joint_T_integrand V_T V_S x ·` in the leader action on `S`. This is
the leader-side analog of the state-local `DynamicArgmaxUnique`. -/
def TargetArgmaxUnique (V_T V_S : Val) : Prop :=
  ∀ x ∈ Sanctions.S, ∀ a₁ a₂ : ℝ, a₁ ∈ Sanctions.I → a₂ ∈ Sanctions.I →
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₁ →
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₂ →
    a₁ = a₂

/-- Global leader uniqueness restricts to state-local (trivial). -/
theorem targetArgmaxUnique_of_global
    {V_T V_S : Val}
    (h : p.TargetArgmaxUniqueGlobal V_T V_S) :
    p.TargetArgmaxUnique V_T V_S :=
  fun x _hx a₁ a₂ ha₁ ha₂ h₁ h₂ => h x a₁ a₂ ha₁ ha₂ h₁ h₂

/-! ## Existence of the leader argmax on the compact action set -/

/-- The leader's joint Bellman integrand attains its sSup on `[0, 1]`
at each state, by compactness of `[0, 1]` and continuity in `a` of the
integrand. -/
theorem joint_T_integrand_isMaxOn_exists
    (V_T V_S : Val) (h_unique_S : p.DynamicArgmaxUniqueGlobal V_S) (x : ℝ) :
    ∃ a ∈ Sanctions.I,
      IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a := by
  have hcont_joint :
      Continuous (fun xa : ℝ × ℝ => p.joint_T_integrand V_T V_S xa.1 xa.2) :=
    p.joint_T_integrand_continuous_jointly_of_unique V_T V_S h_unique_S
  have hcont_a :
      Continuous (fun a : ℝ => p.joint_T_integrand V_T V_S x a) := by
    have h_pair : Continuous (fun a : ℝ => (x, a)) :=
      continuous_const.prodMk continuous_id
    exact hcont_joint.comp h_pair
  exact IsCompact.exists_isMaxOn isCompact_Icc
    ⟨0, by simp [Sanctions.I]⟩ hcont_a.continuousOn

/-! ## Leader argmax selector (`Classical.choose` packaging) -/

/-- **Leader argmax selector.** Selects an argmax of the leader's joint
Bellman integrand at each state via `Classical.choose`. Continuity is
proved separately (`targetArgmax_continuous_of_unique`) under the
leader uniqueness hypothesis. -/
noncomputable def targetArgmax
    (V_T V_S : Val) (h_unique_S : p.DynamicArgmaxUniqueGlobal V_S) (x : ℝ) : ℝ :=
  Classical.choose (p.joint_T_integrand_isMaxOn_exists V_T V_S h_unique_S x)

theorem targetArgmax_mem
    (V_T V_S : Val) (h_unique_S : p.DynamicArgmaxUniqueGlobal V_S) (x : ℝ) :
    p.targetArgmax V_T V_S h_unique_S x ∈ Sanctions.I :=
  (Classical.choose_spec
    (p.joint_T_integrand_isMaxOn_exists V_T V_S h_unique_S x)).1

theorem targetArgmax_isMaxOn
    (V_T V_S : Val) (h_unique_S : p.DynamicArgmaxUniqueGlobal V_S) (x : ℝ) :
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I
      (p.targetArgmax V_T V_S h_unique_S x) :=
  (Classical.choose_spec
    (p.joint_T_integrand_isMaxOn_exists V_T V_S h_unique_S x)).2

/-! ## Berge limit step for the leader integrand

If `(x_n, a_n)` with `a_n` an argmax of `joint_T_integrand V_T V_S x_n ·`
on `[0, 1]` and `(x_n, a_n) → (x_0, a_*)`, then `a_*` is an argmax at
`x_0`. Pure pass-to-limit in `IsMaxOn` using joint continuity. -/

theorem isMaxOn_joint_T_integrand_of_limit
    (V_T V_S : Val) (h_unique_S : p.DynamicArgmaxUniqueGlobal V_S)
    {x_seq : ℕ → ℝ} {x₀ : ℝ}
    (h_x_tendsto : Tendsto x_seq atTop (𝓝 x₀))
    {a_seq : ℕ → ℝ} {aStar : ℝ}
    (h_a_tendsto : Tendsto a_seq atTop (𝓝 aStar))
    (h_a_max : ∀ n, IsMaxOn (fun a => p.joint_T_integrand V_T V_S (x_seq n) a)
      Sanctions.I (a_seq n)) :
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x₀ a) Sanctions.I aStar := by
  intro a' ha'
  have hcont :
      Continuous (fun xa : ℝ × ℝ => p.joint_T_integrand V_T V_S xa.1 xa.2) :=
    p.joint_T_integrand_continuous_jointly_of_unique V_T V_S h_unique_S
  -- Pointwise: f(x_n, a') ≤ f(x_n, a_n) by the argmax property at x_n
  have h_ptn : ∀ n,
      (fun xa : ℝ × ℝ => p.joint_T_integrand V_T V_S xa.1 xa.2) (x_seq n, a')
      ≤ (fun xa : ℝ × ℝ => p.joint_T_integrand V_T V_S xa.1 xa.2)
          (x_seq n, a_seq n) :=
    fun n => h_a_max n ha'
  -- LHS tendsto: f(x_n, a') → f(x₀, a') (constant second arg).
  have h_xas_lhs : Tendsto (fun n : ℕ => (x_seq n, a')) atTop (𝓝 (x₀, a')) :=
    .prodMk_nhds h_x_tendsto tendsto_const_nhds
  have h_lhs := (hcont.tendsto _).comp h_xas_lhs
  -- RHS tendsto: f(x_n, a_n) → f(x₀, aStar).
  have h_xas_rhs : Tendsto (fun n : ℕ => (x_seq n, a_seq n)) atTop
                            (𝓝 (x₀, aStar)) :=
    .prodMk_nhds h_x_tendsto h_a_tendsto
  have h_rhs := (hcont.tendsto _).comp h_xas_rhs
  exact le_of_tendsto_of_tendsto' h_lhs h_rhs h_ptn

/-! ## Berge continuity of `targetArgmax` -/

/-- **Berge continuity of the leader argmax selector.** Under
uniqueness of the leader's joint Bellman argmax at every state, the
`Classical.choose`-defined `targetArgmax V_T V_S` is continuous in
`x`. Proof: sequential continuity via compactness of `[0, 1]` +
Bolzano-Weierstrass + Berge limit step + uniqueness for cluster
points. -/
theorem targetArgmax_continuous_of_unique
    (V_T V_S : Val)
    (h_unique_S : p.DynamicArgmaxUniqueGlobal V_S)
    (h_unique_T : p.TargetArgmaxUniqueGlobal V_T V_S) :
    Continuous (fun x : ℝ => p.targetArgmax V_T V_S h_unique_S x) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  by_contra h_neg
  push Not at h_neg
  -- For each δ > 0, there's x with dist x x₀ < δ but
  -- |targetArgmax x - targetArgmax x₀| ≥ ε. Apply at δ = 1/(n+1).
  choose x_seq h_close h_far using fun n : ℕ =>
    h_neg (1 / (n + 1)) (by positivity)
  -- Tendsto x_seq → x₀.
  have h_x_tendsto : Tendsto x_seq atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    calc dist (x_seq n) x₀
        < 1 / (n + 1) := h_close n
      _ ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < δ := hN
  -- Let a_seq n = targetArgmax (x_seq n).
  set a_seq : ℕ → ℝ :=
    fun n => p.targetArgmax V_T V_S h_unique_S (x_seq n) with ha_def
  have ha_mem : ∀ n, a_seq n ∈ Sanctions.I :=
    fun n => p.targetArgmax_mem V_T V_S h_unique_S _
  -- Extract convergent subsequence by compactness of [0, 1].
  have h_compact_I : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
  obtain ⟨aStar, haStar_mem, φ, hφ_mono, h_sub_tendsto⟩ :=
    h_compact_I.tendsto_subseq ha_mem
  -- Subsequence x_seq ∘ φ → x₀.
  have h_x_sub_tendsto : Tendsto (x_seq ∘ φ) atTop (𝓝 x₀) :=
    h_x_tendsto.comp hφ_mono.tendsto_atTop
  -- Each a_seq (φ n) is the leader argmax at x_seq (φ n).
  have h_a_max_sub : ∀ n, IsMaxOn
      (fun a => p.joint_T_integrand V_T V_S (x_seq (φ n)) a)
      Sanctions.I (a_seq (φ n)) :=
    fun n => p.targetArgmax_isMaxOn V_T V_S h_unique_S _
  -- Berge: aStar is the leader argmax at x₀.
  have h_aStar_max := p.isMaxOn_joint_T_integrand_of_limit V_T V_S h_unique_S
    h_x_sub_tendsto h_sub_tendsto h_a_max_sub
  -- The chosen targetArgmax is also a leader argmax at x₀.
  have h_argmax_x₀_max := p.targetArgmax_isMaxOn V_T V_S h_unique_S x₀
  have h_argmax_x₀_mem := p.targetArgmax_mem V_T V_S h_unique_S x₀
  -- Uniqueness: aStar = targetArgmax x₀.
  have h_eq : aStar = p.targetArgmax V_T V_S h_unique_S x₀ := by
    apply h_unique_T x₀ aStar (p.targetArgmax V_T V_S h_unique_S x₀)
      haStar_mem h_argmax_x₀_mem
    · exact h_aStar_max
    · exact h_argmax_x₀_max
  rw [h_eq] at h_sub_tendsto
  -- Each a_seq (φ n) is ≥ ε away from targetArgmax x₀; contradicts
  -- the convergence to that same point.
  have h_far_sub : ∀ n,
      ε ≤ dist (a_seq (φ n)) (p.targetArgmax V_T V_S h_unique_S x₀) := by
    intro n
    rw [ha_def]
    linarith [h_far (φ n)]
  have h_tendsto_zero :
      Tendsto (fun n => dist (a_seq (φ n))
                              (p.targetArgmax V_T V_S h_unique_S x₀))
              atTop (𝓝 0) := by
    rw [show (0 : ℝ) = dist (p.targetArgmax V_T V_S h_unique_S x₀)
                            (p.targetArgmax V_T V_S h_unique_S x₀) from
        (dist_self _).symm]
    exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp
      h_sub_tendsto
  have h_zero_ge_ε : ε ≤ 0 := by
    apply ge_of_tendsto h_tendsto_zero
    exact Filter.Eventually.of_forall h_far_sub
  linarith

/-! ## State-local (Design A) leader argmax on the compact subtype `↥S`

State-local companions of the global `targetArgmax` machinery. They need
Sender/Target argmax uniqueness only at physical states `x ∈ S = [0,1]`,
and live on the compact subtype `↥S` (so existence and Berge continuity
follow from the subtype-joint continuity
`joint_T_integrand_subtype_continuous_of_unique_on`, without global
continuity off `[0,1]`). The `↥S`-valued selector is extended to a
globally-continuous `ℝ → ℝ` leader policy downstream via `clipS'`.

Since round BJ4.3 (2026-10-08) the Sender input is the compliance-local
`DynamicArgmaxUniqueOnI` (uniqueness also only at physical compliance levels
`a ∈ I`), in place of `DynamicArgmaxUnique` (every real `a`). Each declaration
below keeps its conclusion: the leader only ever chooses `a ∈ I`, so the
Target integrand is needed only on `↥S × I`
(`joint_T_integrand_continuousOn_I_of_unique_on`). An existing
`DynamicArgmaxUnique` proof `h` is passed as `h.toOnI`. General in `F`. -/

/-- **Leader argmax existence at physical states.** At each `x : ↥S`,
the joint Target integrand attains its max on the compact action set
`[0,1]`, by continuity in `a` on `[0,1]` (from the subtype-joint continuity).
Compliance-local Sender uniqueness since round BJ4.3. General in `F`. -/
theorem joint_T_integrand_isMaxOn_exists_on_S
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    ∃ a ∈ Sanctions.I,
      IsMaxOn (fun a => p.joint_T_integrand V_T V_S x.val a) Sanctions.I a := by
  exact IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by simp [Sanctions.I]⟩
    (p.joint_T_integrand_continuousOn_I_of_unique_on V_T V_S h_unique_on x.property)

/-- **Leader argmax selector on `↥S`.** Selects a leader argmax at each
physical state via `Classical.choose`. -/
noncomputable def targetArgmaxOnS
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ↥(Sanctions.S : Set ℝ)) : ℝ :=
  Classical.choose (p.joint_T_integrand_isMaxOn_exists_on_S V_T V_S h_unique_on x)

theorem targetArgmaxOnS_mem
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.targetArgmaxOnS V_T V_S h_unique_on x ∈ Sanctions.I :=
  (Classical.choose_spec
    (p.joint_T_integrand_isMaxOn_exists_on_S V_T V_S h_unique_on x)).1

theorem targetArgmaxOnS_isMaxOn
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x.val a) Sanctions.I
      (p.targetArgmaxOnS V_T V_S h_unique_on x) :=
  (Classical.choose_spec
    (p.joint_T_integrand_isMaxOn_exists_on_S V_T V_S h_unique_on x)).2

/-- **Berge limit step for the leader integrand on `↥S`.** Uniqueness-free
pass-to-limit using the subtype-joint continuity. General in `F`.

Since round BJ4.3 (2026-10-08) the Sender input is the compliance-local
`DynamicArgmaxUniqueOnI`, under which the integrand is continuous only on
`↥S × I`. The leader actions `a_seq n` are therefore required to be feasible
(`h_a_mem`), as every leader argmax selector's are; the limit `aStar` is then
feasible because `I` is closed. -/
theorem isMaxOn_joint_T_integrand_of_limit_on_S
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    {x_seq : ℕ → ↥(Sanctions.S : Set ℝ)} {x₀ : ↥(Sanctions.S : Set ℝ)}
    (h_x_tendsto : Tendsto x_seq atTop (𝓝 x₀))
    {a_seq : ℕ → ℝ} {aStar : ℝ}
    (h_a_tendsto : Tendsto a_seq atTop (𝓝 aStar))
    (h_a_mem : ∀ n, a_seq n ∈ Sanctions.I)
    (h_a_max : ∀ n, IsMaxOn
      (fun a => p.joint_T_integrand V_T V_S (x_seq n).val a) Sanctions.I (a_seq n)) :
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x₀.val a) Sanctions.I aStar := by
  intro a' ha'
  have hcont := p.joint_T_integrand_subtype_continuous_of_unique_on V_T V_S h_unique_on
  have haStar : aStar ∈ Sanctions.I :=
    isClosed_Icc.mem_of_tendsto h_a_tendsto (Filter.Eventually.of_forall h_a_mem)
  -- On `I` the projection onto `[0,1]` is the identity.
  have hproj : ∀ b ∈ Sanctions.I,
      ((Set.projIcc (0 : ℝ) 1 zero_le_one b : ℝ)) = b := fun b hb => by
    rw [Set.projIcc_of_mem zero_le_one hb]
  have h_ptn : ∀ n,
      (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ => p.joint_T_integrand V_T V_S xa.1.val
          (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) (x_seq n, a')
      ≤ (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ => p.joint_T_integrand V_T V_S xa.1.val
          (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) (x_seq n, a_seq n) := by
    intro n
    simp only [hproj a' ha', hproj (a_seq n) (h_a_mem n)]
    exact h_a_max n ha'
  have h_lhs := (hcont.tendsto ((x₀, a') : ↥(Sanctions.S : Set ℝ) × ℝ)).comp
    (h_x_tendsto.prodMk_nhds (tendsto_const_nhds (x := a')))
  have h_rhs := (hcont.tendsto ((x₀, aStar) : ↥(Sanctions.S : Set ℝ) × ℝ)).comp
    (h_x_tendsto.prodMk_nhds h_a_tendsto)
  have h := le_of_tendsto_of_tendsto' h_lhs h_rhs h_ptn
  simpa only [Function.comp_apply, hproj a' ha', hproj aStar haStar] using h

/-- **Berge continuity of the leader argmax on `↥S`.** Under Sender and
Target argmax uniqueness at physical states, `targetArgmaxOnS` is
continuous on the compact subtype `↥S`. Compliance-local Sender uniqueness
since round BJ4.3. General in `F`. -/
theorem targetArgmaxOnS_continuous
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (h_unique_T_on : ∀ x ∈ Sanctions.S, ∀ a₁ a₂,
        a₁ ∈ Sanctions.I → a₂ ∈ Sanctions.I →
        IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₁ →
        IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₂ → a₁ = a₂) :
    Continuous (fun x : ↥(Sanctions.S : Set ℝ) =>
      p.targetArgmaxOnS V_T V_S h_unique_on x) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  by_contra h_neg
  push Not at h_neg
  choose x_seq h_close h_far using fun n : ℕ =>
    h_neg (1 / (n + 1)) (by positivity)
  have h_x_tendsto : Tendsto x_seq atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    calc dist (x_seq n) x₀
        < 1 / (n + 1) := h_close n
      _ ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < δ := hN
  set a_seq : ℕ → ℝ :=
    fun n => p.targetArgmaxOnS V_T V_S h_unique_on (x_seq n) with ha_def
  have ha_mem : ∀ n, a_seq n ∈ Sanctions.I :=
    fun n => p.targetArgmaxOnS_mem V_T V_S h_unique_on _
  have h_compact_I : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
  obtain ⟨aStar, haStar_mem, φ, hφ_mono, h_sub_tendsto⟩ :=
    h_compact_I.tendsto_subseq ha_mem
  have h_x_sub_tendsto : Tendsto (x_seq ∘ φ) atTop (𝓝 x₀) :=
    h_x_tendsto.comp hφ_mono.tendsto_atTop
  have h_a_max_sub : ∀ n, IsMaxOn
      (fun a => p.joint_T_integrand V_T V_S (x_seq (φ n)).val a)
      Sanctions.I (a_seq (φ n)) :=
    fun n => p.targetArgmaxOnS_isMaxOn V_T V_S h_unique_on _
  have h_aStar_max := p.isMaxOn_joint_T_integrand_of_limit_on_S V_T V_S h_unique_on
    h_x_sub_tendsto h_sub_tendsto (fun n => ha_mem (φ n)) h_a_max_sub
  have h_argmax_x₀_max := p.targetArgmaxOnS_isMaxOn V_T V_S h_unique_on x₀
  have h_argmax_x₀_mem := p.targetArgmaxOnS_mem V_T V_S h_unique_on x₀
  have h_eq : aStar = p.targetArgmaxOnS V_T V_S h_unique_on x₀ := by
    apply h_unique_T_on x₀.val x₀.property aStar
      (p.targetArgmaxOnS V_T V_S h_unique_on x₀) haStar_mem h_argmax_x₀_mem
    · exact h_aStar_max
    · exact h_argmax_x₀_max
  rw [h_eq] at h_sub_tendsto
  have h_far_sub : ∀ n,
      ε ≤ dist (a_seq (φ n)) (p.targetArgmaxOnS V_T V_S h_unique_on x₀) := by
    intro n
    rw [ha_def]
    linarith [h_far (φ n)]
  have h_tendsto_zero :
      Tendsto (fun n => dist (a_seq (φ n))
                              (p.targetArgmaxOnS V_T V_S h_unique_on x₀))
              atTop (𝓝 0) := by
    rw [show (0 : ℝ) = dist (p.targetArgmaxOnS V_T V_S h_unique_on x₀)
                            (p.targetArgmaxOnS V_T V_S h_unique_on x₀) from
        (dist_self _).symm]
    exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp h_sub_tendsto
  have h_zero_ge_ε : ε ≤ 0 := by
    apply ge_of_tendsto h_tendsto_zero
    exact Filter.Eventually.of_forall h_far_sub
  linarith

/-! ## Globally-continuous leader policy via state clamping (Design A §3)

The `↥S`-valued `targetArgmaxOnS` is extended to a globally-continuous
`ℝ → ℝ` leader policy `α_on_ext` by clamping the state into `S` with
`clipS'`. This is what `bellmanS_BCF` (which requires a global
`Continuous α`) consumes. On `S`, `α_on_ext` IS the derived leader argmax
(so leader optimality holds at every physical state); off `S` it is a
continuous filler at states the clamped dynamics never visit. -/

/-- **Globally-continuous state-clamped leader policy.** Built from
compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`) since round
BJ4.3; an existing `DynamicArgmaxUnique` proof `h` enters as `h.toOnI`. -/
noncomputable def α_on_ext
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ℝ) : ℝ :=
  p.targetArgmaxOnS V_T V_S h_unique_on (Sanctions.clipS' x)

theorem α_on_ext_mem
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ℝ) :
    p.α_on_ext V_T V_S h_unique_on x ∈ Sanctions.I :=
  p.targetArgmaxOnS_mem V_T V_S h_unique_on (Sanctions.clipS' x)

theorem α_on_ext_continuous
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (h_unique_T_on : ∀ x ∈ Sanctions.S, ∀ a₁ a₂,
        a₁ ∈ Sanctions.I → a₂ ∈ Sanctions.I →
        IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₁ →
        IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I a₂ → a₁ = a₂) :
    Continuous (p.α_on_ext V_T V_S h_unique_on) :=
  (p.targetArgmaxOnS_continuous V_T V_S h_unique_on h_unique_T_on).comp
    Sanctions.clipS'_continuous

/-- On physical states `x ∈ S`, `α_on_ext` is the leader argmax of the
joint Target integrand — the derived (Rule 1) leader optimality. -/
theorem α_on_ext_isMaxOn_of_mem
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I
      (p.α_on_ext V_T V_S h_unique_on x) := by
  have hval : (Sanctions.clipS' x).val = x := by
    obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hx
    show Sanctions.clipS x = x
    unfold Sanctions.clipS
    rw [min_eq_right h1, max_eq_right h0]
  have h := p.targetArgmaxOnS_isMaxOn V_T V_S h_unique_on (Sanctions.clipS' x)
  rw [hval] at h
  exact h

/-! ## Package `targetArgmax` as a `DynamicTargetSelector`

Under global uniqueness of both the Sender and Target argmaxes, the
operator-level equilibrium-existence theorem
`exists_feedbackStackelberg_from_selector_row_bounds` no longer needs
an externally-supplied `DynamicTargetSelector` — the leader selector
is derived from the uniqueness primitives via Berge. -/

/-- **`DynamicTargetSelector` from uniqueness primitives.** Packages
the `targetArgmax` selector (continuous, feasible, leader Bellman
optimal) into a `DynamicTargetSelector` instance, reducing the
external structural primitive to two uniqueness hypotheses (one for
the Sender's dynamic argmax, one for the leader's joint Bellman
argmax). Named `dynamicTargetSelector_of_unique` (not
`DynamicTargetSelector.of_unique`) because `p.DynamicTargetSelector`
parses as a `Type`, not an object, so dot-notation chaining requires
the result to be a method of `Params` itself. -/
noncomputable def dynamicTargetSelector_of_unique
    (h_unique_S_all : ∀ V_S : Val, p.DynamicArgmaxUniqueGlobal V_S)
    (h_unique_T_all : ∀ V_T V_S : Val, p.TargetArgmaxUniqueGlobal V_T V_S) :
    p.DynamicTargetSelector where
  α := fun z x => p.targetArgmax z.1 z.2 (h_unique_S_all z.2) x
  α_continuous := fun z =>
    p.targetArgmax_continuous_of_unique z.1 z.2
      (h_unique_S_all z.2) (h_unique_T_all z.1 z.2)
  α_mem := fun z x =>
    p.targetArgmax_mem z.1 z.2 (h_unique_S_all z.2) x
  α_opt := fun z x =>
    p.targetArgmax_isMaxOn z.1 z.2 (h_unique_S_all z.2) x

/-! ## Existence with the discharged selector

One-line composition: `DynamicTargetSelector.of_unique` plugged into
`exists_feedbackStackelberg_from_selector_row_bounds`. -/

/-- **Existence of `FeedbackStackelbergEquilibrium` from uniqueness +
row-Lipschitz primitives.** With the leader selector discharged via
`DynamicTargetSelector.of_unique`, the operator-level existence
theorem only requires:

* global Sender argmax uniqueness `h_unique_S_all`,
* global Target (leader) argmax uniqueness `h_unique_T_all`,
* explicit row-Lipschitz contraction bounds on the joint Target/Sender
  operator pair with `β_T + L_TS < 1` and `β_S + L_ST < 1`.

The `DynamicTargetSelector` structural primitive is no longer
externally supplied. -/
theorem exists_feedbackStackelberg_from_uniqueness_row_bounds
    (h_unique_S_all : ∀ V_S : Val, p.DynamicArgmaxUniqueGlobal V_S)
    (h_unique_T_all : ∀ V_T V_S : Val, p.TargetArgmaxUniqueGlobal V_T V_S)
    {βS βT LTS LST : ℝ}
    (hβS_nn : 0 ≤ βS)
    (hβT_nn : 0 ≤ βT)
    (hLTS_nn : 0 ≤ LTS)
    (hLST_nn : 0 ≤ LST)
    (hT_row :
      ∀ V W V' W' : Val,
        dist
          (p.jointTargetOp h_unique_S_all (V, W))
          (p.jointTargetOp h_unique_S_all (V', W'))
          ≤ βT * dist V V' + LTS * dist W W')
    (hS_row :
      ∀ V W V' W' : Val,
        dist
          (p.jointSenderOp
            (p.dynamicTargetSelector_of_unique h_unique_S_all h_unique_T_all)
            (V, W))
          (p.jointSenderOp
            (p.dynamicTargetSelector_of_unique h_unique_S_all h_unique_T_all)
            (V', W'))
          ≤ LST * dist V V' + βS * dist W W')
    (hT_sum : βT + LTS < 1)
    (hS_sum : βS + LST < 1) :
    Nonempty p.FeedbackStackelbergEquilibrium :=
  p.exists_feedbackStackelberg_from_selector_row_bounds
    (p.dynamicTargetSelector_of_unique h_unique_S_all h_unique_T_all)
    h_unique_S_all hβS_nn hβT_nn hLTS_nn hLST_nn
    hT_row hS_row hT_sum hS_sum

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
