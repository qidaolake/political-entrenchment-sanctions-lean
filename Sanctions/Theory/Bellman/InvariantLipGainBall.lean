/-
Sanctions/Theory/Bellman/InvariantLipGainBall.lean

**Audit-46 Patch 4: gain-restricted Lipschitz-bounded ball carrier.**

The audit-46 critique noted that `hV_T_gain_on_E`
(`LowerSlopeOnValueOn V_T (Set.Icc xT 1) g`) is the core
political-economy condition — the Target incumbent values the high
political state on the basin. Best to move it into the **carrier**
rather than carry it as a per-equilibrium hypothesis.

This file delivers:

* `valLipGainBall M K g xT` — the strictly narrower carrier
  `{V | ‖V‖ ≤ M ∧ ValueLipschitzWith V K ∧ LowerSlopeOnValueOn V (Icc xT 1) g}`.
* `valLipGainBall_isClosed` — closed (intersection of three closed sets).
* `ValueClass.ofLipGainBall` — constructor of a `ValueClass`. Takes
  the nonempty witness explicitly (concrete payoff families
  typically supply their own, e.g., the linear `V(y) = g · y.val`
  when `M ≥ g`).
* `ofLipGainBall_V_T_lipschitz_carrier` — auto-discharge of
  K-Lipschitz from carrier membership.
* `ofLipGainBall_V_T_gain_on_carrier` — auto-discharge of
  `LowerSlopeOnValueOn` from carrier membership.

## Rule compliance

Rule 1 ✓ (no strategies). Rule 3 — `valLipGainBall` is structurally
a *narrower* version of `valLipBall` (with one extra membership
condition), so it does NOT widen the assumption surface; the
discharge constructors REDUCE the surface (eliminate
`hV_T_gain_on_E` per-E primitive). Category-(1) scaffolding.
Rule 5 ✓ (fully parametric over `M`, `K`, `g`, `xT`).
-/

import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Foundations.StokeyLucas

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The gain-restricted Lipschitz-bounded ball -/

/-- **Gain-restricted Lipschitz-bounded ball.** Strictly narrower
than `valLipBall M K`: adds the `LowerSlopeOnValueOn V (Set.Icc xT 1) g`
constraint on the basin range. -/
def valLipGainBall (M K g xT : ℝ) : Set Val :=
  {V : Val | ‖V‖ ≤ M ∧ ValueLipschitzWith V K ∧
              LowerSlopeOnValueOn V (Set.Icc xT 1) g}

/-- Membership unfold. -/
theorem mem_valLipGainBall_iff {M K g xT : ℝ} {V : Val} :
    V ∈ valLipGainBall M K g xT ↔
      ‖V‖ ≤ M ∧ ValueLipschitzWith V K ∧
      LowerSlopeOnValueOn V (Set.Icc xT 1) g := Iff.rfl

/-! ## Closedness of `LowerSlopeOnValueOn` and `valLipGainBall` -/

/-- **The `LowerSlopeOnValueOn` set in BCF is closed.** The
condition `g * dist y₁ y₂ ≤ V y₂ - V y₁` for each fixed pair
`(y₁, y₂) ∈ B × B` with `y₁ ≤ y₂` defines a closed subset of BCF
via pointwise-continuous evaluation. The intersection over all
such pairs is closed. -/
theorem lowerSlopeOnValueOn_isClosed (B : Set ℝ) (g : ℝ) :
    IsClosed {V : Val | LowerSlopeOnValueOn V B g} := by
  rw [show {V : Val | LowerSlopeOnValueOn V B g}
        = ⋂ (y₁ : ↥(Sanctions.S : Set ℝ)) (y₂ : ↥(Sanctions.S : Set ℝ))
              (_ : y₁.val ∈ B) (_ : y₂.val ∈ B) (_ : y₁ ≤ y₂),
            {V : Val | g * dist y₁ y₂ ≤ V y₂ - V y₁} from ?_]
  · -- Each pointwise set is closed.
    apply isClosed_iInter; intro y₁
    apply isClosed_iInter; intro y₂
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro _
    apply isClosed_iInter; intro _
    -- {V | g * dist y₁ y₂ ≤ V y₂ - V y₁} is closed.
    have h_eval₁ : Continuous (fun V : Val => V y₁) :=
      ContinuousEvalConst.continuous_eval_const y₁
    have h_eval₂ : Continuous (fun V : Val => V y₂) :=
      ContinuousEvalConst.continuous_eval_const y₂
    exact isClosed_le continuous_const (h_eval₂.sub h_eval₁)
  · -- Set equality.
    ext V
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h y₁ y₂ hy₁ hy₂ hle; exact h y₁ y₂ hy₁ hy₂ hle
    · intro h y₁ y₂ hy₁ hy₂ hle; exact h y₁ y₂ hy₁ hy₂ hle

/-- `valLipGainBall M K g xT` is closed: intersection of three closed sets. -/
theorem valLipGainBall_isClosed (M K g xT : ℝ) :
    IsClosed (valLipGainBall M K g xT) := by
  unfold valLipGainBall
  rw [show {V : Val | ‖V‖ ≤ M ∧ ValueLipschitzWith V K ∧
              LowerSlopeOnValueOn V (Set.Icc xT 1) g}
        = ({V : Val | ‖V‖ ≤ M} ∩ {V : Val | ValueLipschitzWith V K}) ∩
            {V : Val | LowerSlopeOnValueOn V (Set.Icc xT 1) g} from ?_]
  · exact ((isClosed_le continuous_norm continuous_const).inter
            (valueLipschitz_isClosed K)).inter
          (lowerSlopeOnValueOn_isClosed (Set.Icc xT 1) g)
  · ext V; simp [Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]

/-- `valLipGainBall M K g xT ⊆ valLipBall M K`. -/
theorem valLipGainBall_subset_valLipBall (M K g xT : ℝ) :
    valLipGainBall M K g xT ⊆ valLipBall M K := by
  intro V hV
  exact ⟨hV.1, hV.2.1⟩

/-- **Gain-ball membership splits into the Lipschitz ball plus the slope
floor.** Purely an unfolding, but the load-bearing one for assembling
invariance: the sup-norm and Lipschitz halves are exactly what the Lipschitz-ball
machinery already delivers, so the only genuinely new obligation on the gain ball
is the minimum upward state slope. Every preservation proof below is organised
around this split — reuse two thirds, prove one third. -/
theorem mem_valLipGainBall_iff_mem_valLipBall_and_lowerSlope
    {M K g xT : ℝ} {V : Val} :
    V ∈ valLipGainBall M K g xT ↔
      V ∈ valLipBall M K ∧ LowerSlopeOnValueOn V (Set.Icc xT 1) g :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- **Members of a zero-based gain ball with nonnegative minimum slope
are monotone.** For `V ∈ valLipGainBall M K g 0` the lower-slope
constraint holds on `Icc 0 1 = S`, where the membership side conditions
are automatic for every point of the state space; so for `y₁ ≤ y₂`,
`V y₂ − V y₁ ≥ g · dist y₁ y₂ ≥ 0`. This is the general discharger for
carrier-monotonicity fields (e.g. `hV_S_mono_carrier` in the MS-form
certificate): on zero-based nonnegative-gain carriers, monotonicity is
carrier geometry, not an extra assumption. -/
theorem monotone_of_mem_valLipGainBall {M K g : ℝ} (hg : 0 ≤ g)
    {V : Val} (hV : V ∈ valLipGainBall M K g 0) :
    Monotone ⇑V := by
  intro y₁ y₂ hle
  have hmem₁ : y₁.val ∈ Set.Icc (0 : ℝ) 1 := y₁.property
  have hmem₂ : y₂.val ∈ Set.Icc (0 : ℝ) 1 := y₂.property
  have hslope := hV.2.2 y₁ y₂ hmem₁ hmem₂ hle
  have hnn : 0 ≤ g * dist y₁ y₂ := mul_nonneg hg dist_nonneg
  linarith

/-! ## Slope-pinned gain balls at the SLP closed-form radii

A *slope-pinned* gain ball `valLipGainBall M c c 0` demands Lipschitz
constant `c` **and** minimum upward slope `c`. The two squeeze each
other, so its members are exactly affine with slope `c` on the state
space (`valLipGainBall_clip_diff`). Such a ball has exactly two
magnitudes — the slope `c` and the radius `M` — and this section proves
that **both are governed by the primitives**, neither freely chosen. For
the ball to be Bellman-invariant under a corner-pinned affine image:

* the slope `c` must be *exactly* the Hinderer 4.2(c) closed form
  `bellmanLipConstant β δ g_U = g_U/(1 − β·δ)`;
* the radius `M` must be *at least* the closed form
  `bellmanNormBound β M_U = M_U/(1 − β)`, which is therefore the
  smallest invariant radius; larger radii are invariant too, so any
  slack a witness carries is visible as the gap `M − M_U/(1 − β)`.
-/

/-- **Affine extraction on a slope-pinned gain ball.** Every member of
`valLipGainBall M c c 0` — Lipschitz constant `c` together with minimum
upward slope `c` — is exactly affine with slope `c` on the state space:
for all `z₁, z₂ ∈ [0,1]`,
`V(clip z₂) − V(clip z₁) = c · (z₂ − z₁)`.

The economic content: on a slope-pinned carrier the *value difference*
between two political states is pinned by carrier membership alone, with
no reference to which member `V` happens to be. That is what lets a
corner-pinned Bellman image be computed in closed form uniformly over
the carrier.

`Sanctions.Examples.gainBall_clip_diff` is the witness-side alias. -/
theorem valLipGainBall_clip_diff {c M : ℝ} (_hc : 0 ≤ c) {V : Val}
    (hV : V ∈ valLipGainBall M c c 0)
    {z₁ z₂ : ℝ} (h1 : z₁ ∈ Set.Icc (0 : ℝ) 1) (h2 : z₂ ∈ Set.Icc (0 : ℝ) 1) :
    V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) = c * (z₂ - z₁) := by
  have hLip : ValueLipschitzWith V c := hV.2.1
  have hGain : LowerSlopeOnValueOn V (Set.Icc 0 1) c := hV.2.2
  have hmem₁ : (Sanctions.clipS' z₁).val ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem _
  have hmem₂ : (Sanctions.clipS' z₂).val ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem _
  have hd : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = |z₁ - z₂| := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem h1,
      Sanctions.clipS'_val_eq_of_mem h2]
  rcases le_total z₁ z₂ with hle | hle
  · have hord : Sanctions.clipS' z₁ ≤ Sanctions.clipS' z₂ := Sanctions.clipS'_mono hle
    have hlow := hGain (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) hmem₁ hmem₂ hord
    have hup := hLip (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    rw [hd, abs_of_nonpos (by linarith : z₁ - z₂ ≤ 0)] at hlow
    rw [hd, abs_of_nonpos (by linarith : z₁ - z₂ ≤ 0)] at hup
    have := abs_le.mp hup
    nlinarith [this.2, hlow]
  · have hord : Sanctions.clipS' z₂ ≤ Sanctions.clipS' z₁ := Sanctions.clipS'_mono hle
    have hlow := hGain (Sanctions.clipS' z₂) (Sanctions.clipS' z₁) hmem₂ hmem₁ hord
    have hup := hLip (Sanctions.clipS' z₂) (Sanctions.clipS' z₁)
    rw [dist_comm, hd, abs_of_nonneg (by linarith : (0:ℝ) ≤ z₁ - z₂)] at hlow
    rw [dist_comm, hd, abs_of_nonneg (by linarith : (0:ℝ) ≤ z₁ - z₂)] at hup
    have := abs_le.mp hup
    nlinarith [this.2, hlow]

/-- **Corner-pinned affine Bellman images stay inside the closed-form
carrier.** Suppose a Bellman image `W` has been evaluated in closed form
at a *derived* corner policy, so that at every political state `y`

  `W y = c₀ + g_U · y + β · V(clip(δ·y + (1 − δ)))`,

i.e. an affine stage payoff `c₀ + g_U·y` (the stage payoff collected
along the certified corner path) plus the discounted continuation at the
corner-pinned transition `F(y, 1) = δ·y + (1 − δ)`. Suppose further that
the stage payoff is bounded in absolute value by `M_U` on the state
space, and that the incoming value `V` lies in the slope-pinned gain
ball whose slope is the Hinderer 4.2(c) closed form
`K = bellmanLipConstant β δ g_U = g_U/(1 − β·δ)` and whose radius is the
closed form `M = bellmanNormBound β M_U = M_U/(1 − β)`.

Then the image `W` lies in **that same ball**.

Both magnitudes are forced, and neither is a free choice:

* the slope, by the Hinderer 4.2(c) margin identity `g_U + β·K·δ = K`
  (`bellman_closed_form_lipschitz_margin`) — the image's slope is
  `g_U + β·K·δ`, so it re-enters the ball exactly when `K` is the
  closed form;
* the radius, by the margin inequality `M_U + β·M ≤ M`, which
  (`bellman_closed_form_norm_margin`) holds exactly when
  `M ≥ M_U/(1 − β) = bellmanNormBound β M_U` — the image's sup-norm is at
  most `M_U + β·M`, so the closed form is the **smallest** invariant
  radius and every larger one is invariant too. A witness that needs no
  slack takes `M` to be the closed form itself (`le_rfl`); a witness that
  deliberately carries slack — because a downstream ε-isolation statement
  spends it — supplies the larger radius and discharges `hM` by
  arithmetic, with the slack visible in one place.

This is the general parametric statement behind every witness carrier in
`Examples/`; each witness discharges it by supplying its own
`(β, δ, c₀, g_U, M_U)` read off the primitives, with any numeric radius
recovered afterwards as a `norm_num` evaluation rather than chosen up
front.

**Reading the `δ` binder — it is the transition's state-retention
multiplier, not the adjustment rate.** The corner-pinned successor here is
`δ·y + (1 − δ)`, and `bellmanLipConstant`'s second argument is its own
`γ`. For the project's affine law `affineF d x s = (1 − d)·x + d·s` the
successor at the certified corner is `F(y,1) = (1 − d)·y + d`, so a caller
instantiates this theorem at `δ := 1 − d`, giving the Hinderer-4.2(c) lower-slope
denominator `1 − β·(1 − d)`. Passing the adjustment rate `d` directly is
wrong in general and is silently correct only at `d = 1/2`, where
`d = 1 − d`; every witness in `Examples/` happens to sit at that point, so
the error is invisible there. Call sites pass `1 - p.δ` explicitly. -/
theorem mem_valLipGainBall_bellman_closedForm
    {β δ c₀ g_U M_U M : ℝ}
    (hβ_nn : 0 ≤ β) (hβ_lt : β < 1) (hδ_nn : 0 ≤ δ) (hδ_le : δ ≤ 1)
    (hg_nn : 0 ≤ g_U)
    (hM_U : ∀ y : ℝ, y ∈ Set.Icc (0:ℝ) 1 → |c₀ + g_U * y| ≤ M_U)
    (hM : StokeyLucas.bellmanNormBound β M_U ≤ M)
    {V W : Val}
    (hV : V ∈ valLipGainBall M
            (StokeyLucas.bellmanLipConstant β δ g_U)
            (StokeyLucas.bellmanLipConstant β δ g_U) 0)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
        W y = c₀ + g_U * y.val
          + β * V (Sanctions.clipS' (δ * y.val + (1 - δ)))) :
    W ∈ valLipGainBall M
          (StokeyLucas.bellmanLipConstant β δ g_U)
          (StokeyLucas.bellmanLipConstant β δ g_U) 0 := by
  -- Contraction margins.
  have hβδ : β * δ < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hβ_nn hδ_le) hβ_lt
  have hM_U_nn : (0:ℝ) ≤ M_U :=
    le_trans (abs_nonneg _) (by simpa using hM_U 0 ⟨le_refl 0, by norm_num⟩)
  obtain ⟨hK_nn, hK_margin⟩ :=
    StokeyLucas.bellman_closed_form_lipschitz_margin hg_nn hβ_nn hδ_nn hβδ
  obtain ⟨hMmin_nn, _⟩ :=
    StokeyLucas.bellman_closed_form_norm_margin hM_U_nn hβ_nn hβ_lt
  set K : ℝ := StokeyLucas.bellmanLipConstant β δ g_U with hK_def
  have hK_nn' : (0:ℝ) ≤ K := hK_nn
  have hM_nn' : (0:ℝ) ≤ M := le_trans hMmin_nn hM
  have hK_marg : g_U + β * K * δ = K := hK_margin
  -- The radius margin: `M ≥ M_U/(1−β)` is exactly `M_U + β·M ≤ M`.
  have hM_marg : M_U + β * M ≤ M := by
    have hden : (0:ℝ) < 1 - β := by linarith
    have := (div_le_iff₀ hden).mp
      (by simpa [StokeyLucas.bellmanNormBound] using hM)
    nlinarith [this]
  -- The corner-pinned transition never leaves the state space.
  have htrans : ∀ y : ↥(Sanctions.S : Set ℝ),
      δ * y.val + (1 - δ) ∈ Set.Icc (0:ℝ) 1 := by
    intro y
    have hy := y.property
    constructor
    · nlinarith [hy.1]
    · nlinarith [hy.2]
  -- Exact affine difference of the image, with slope `K`.
  have hdiffW : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
      W y₂ - W y₁ = K * (y₂.val - y₁.val) := by
    intro y₁ y₂
    have hdV := valLipGainBall_clip_diff hK_nn' hV (htrans y₁) (htrans y₂)
    rw [himg y₁, himg y₂]
    have : δ * y₂.val + (1 - δ) - (δ * y₁.val + (1 - δ))
        = δ * (y₂.val - y₁.val) := by ring
    rw [this] at hdV
    linear_combination β * hdV + (y₂.val - y₁.val) * hK_marg
  refine ⟨?_, ?_, ?_⟩
  · -- Sup-norm radius: `M_U + β·M ≤ M`.
    rw [BoundedContinuousFunction.norm_le hM_nn']
    intro y
    rw [himg y, Real.norm_eq_abs]
    have hVb : |V (Sanctions.clipS' (δ * y.val + (1 - δ)))| ≤ M := by
      have h1 := BoundedContinuousFunction.norm_coe_le_norm V
        (Sanctions.clipS' (δ * y.val + (1 - δ)))
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 hV.1
    have hstage : |c₀ + g_U * y.val| ≤ M_U := hM_U y.val y.property
    have hcont : |β * V (Sanctions.clipS' (δ * y.val + (1 - δ)))| ≤ β * M := by
      rw [abs_mul, abs_of_nonneg hβ_nn]
      exact mul_le_mul_of_nonneg_left hVb hβ_nn
    have h1 := abs_le.mp hstage
    have h2 := abs_le.mp hcont
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hM_marg]
  · -- Lipschitz constant exactly `K`.
    intro y₁ y₂
    rw [hdiffW y₁ y₂, Subtype.dist_eq, Real.dist_eq, abs_mul,
      abs_of_nonneg hK_nn', abs_sub_comm y₁.val y₂.val]
  · -- Minimum upward slope exactly `K`.
    intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [hdiffW y₁ y₂, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    nlinarith [hle']

/-! ## `ValueClass.ofLipGainBall` constructor

Takes the nonempty witness as an explicit hypothesis. Concrete
payoff families typically supply their own witness — e.g., the
linear value function `V(y) = g · y.val` satisfies all three
constraints when `M ≥ g`, `K ≥ g`, `g ≥ 0`. -/

namespace ValueClass

/-- Construct a `ValueClass` from the gain-restricted
Lipschitz-bounded ball, with the nonempty witness supplied
explicitly. -/
noncomputable def ofLipGainBall
    {M K g xT : ℝ}
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT,
        p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT,
        p.TargetArgmaxUnique V_T V_S) :
    p.ValueClass where
  carrier := valLipGainBall M K g xT
  isClosed := valLipGainBall_isClosed M K g xT
  nonempty := h_nonempty
  sender_unique_on := h_unique_S
  target_unique_on := h_unique_T

end ValueClass

/-! ## Domain restriction and the structural `IsInvariant` discharger -/

/-- **A lower-slope guarantee restricts to a smaller basin.** The condition is
universally quantified over pairs in the domain, so shrinking the domain weakens
it. Needed because the Sender-side cone lemmas conclude on all of `[0,1]` while
the gain ball asks for `[xT,1]`. -/
theorem LowerSlopeOnValueOn.mono_set {V : Val} {B B' : Set ℝ} {g : ℝ}
    (h : LowerSlopeOnValueOn V B g) (hsub : B' ⊆ B) :
    LowerSlopeOnValueOn V B' g :=
  fun y₁ y₂ hy₁ hy₂ hle => h y₁ y₂ (hsub hy₁) (hsub hy₂) hle

/-- **`IsInvariant` for `valLipGainBall` from operator preservation.**

The gain-ball analogue of `ofLipBall_IsInvariant_of_preservation`. It was the
missing structural step: the gain ball had a Target-side slope-preservation
theorem (general in `F`) and, since 2026-08-17, a general-`F` Sender-side one in
`Bellman/SenderLowerSlopeCone.lean`, but no discharger to feed them into.

Membership in `valLipGainBall` is a conjunction of three conditions — sup-norm
bound, Lipschitz bound, and the minimum upward state slope — so each operator
must be shown to preserve all three; that is what the two hypotheses below
package.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem ofLipGainBall_IsInvariant_of_preservation
    {M K g xT : ℝ}
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT, p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT, p.TargetArgmaxUnique V_T V_S)
    (h_T_preserves :
      ∀ V_T V_S : Val,
        (hV_T : V_T ∈ valLipGainBall M K g xT) →
        (hV_S : V_S ∈ valLipGainBall M K g xT) →
        p.jointTarget_BCF_on_S V_T V_S (h_unique_S V_S hV_S).toOnI
          ∈ valLipGainBall M K g xT)
    (h_S_preserves :
      ∀ V_T V_S : Val,
        (hV_T : V_T ∈ valLipGainBall M K g xT) →
        (hV_S : V_S ∈ valLipGainBall M K g xT) →
        (ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
            h_unique_T).jointSender_BCF_on ⟨V_T, hV_T⟩ ⟨V_S, hV_S⟩
          ∈ valLipGainBall M K g xT) :
    (ValueClass.ofLipGainBall (p := p) h_nonempty h_unique_S
      h_unique_T).IsInvariant := by
  intro V_T V_S
  exact ⟨h_T_preserves V_T.val V_S.val V_T.property V_S.property,
         h_S_preserves V_T.val V_S.val V_T.property V_S.property⟩

/-! ## Automatic dischargers from carrier membership -/

/-- **`h_V_T_lipschitz_carrier` is automatic on `valLipGainBall`.** -/
theorem ofLipGainBall_V_T_lipschitz_carrier
    {M K g xT : ℝ}
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT,
        p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT,
        p.TargetArgmaxUnique V_T V_S) :
    ∀ V_T : Val,
      V_T ∈ (ValueClass.ofLipGainBall (p := p) h_nonempty
                h_unique_S h_unique_T).carrier →
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
        |V_T y₁ - V_T y₂| ≤ K * dist y₁ y₂ := by
  intro V_T hV_T y₁ y₂
  have h_lip : ValueLipschitzWith V_T K := hV_T.2.1
  have h := h_lip y₂ y₁
  rw [dist_comm] at h
  exact h

/-- **`hV_T_gain_on_E` is automatic on `valLipGainBall`.** -/
theorem ofLipGainBall_V_T_gain_on_carrier
    {M K g xT : ℝ}
    (h_nonempty : (valLipGainBall M K g xT).Nonempty)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT,
        p.DynamicArgmaxUnique V_S)
    (h_unique_T : ∀ V_T ∈ valLipGainBall M K g xT,
        ∀ V_S ∈ valLipGainBall M K g xT,
        p.TargetArgmaxUnique V_T V_S) :
    ∀ V_T : Val,
      V_T ∈ (ValueClass.ofLipGainBall (p := p) h_nonempty
                h_unique_S h_unique_T).carrier →
      LowerSlopeOnValueOn V_T (Set.Icc xT 1) g := fun _ hV_T => hV_T.2.2

/-! ## Round-27 γ_σ envelope companion: Target-side lower-slope

The Target-side parallel of Round 20's `jointTarget_BCF_lipschitz_of_integrand_lipschitz`
(absolute-difference Lipschitz) and Round 25's
`bellmanLipConstant` (closed-form Lipschitz). Where R20 / R25 land
the **upper** bound `|V y₂ − V y₁| ≤ K · dist y₁ y₂` on the joint
Target Bellman operator from an integrand-Lipschitz primitive and
the closed-form `K := L_U / (1 − β · γ_F)`, Round 27 lands the
**lower** bound `LowerSlopeOnValueOn (jointTarget_BCF V_T V_S _)
(Set.Icc xT 1) gT` from an integrand-lower-slope primitive and the
closed-form `gT := g_U / (1 − β_T · (1 − δ))`.

This is the closed-form lower-slope recursion (Hinderer 2005 Thm 4.2(c); not
the Benveniste–Scheinkman envelope theorem, SLP Thm 4.10, which needs a
differentiable value and is not used):
the value function inherits the stage payoff's lower state-slope
deflated by the geometric series of the discounted transition
multiplier. The economic content: if the stage Target payoff
increases at rate `g_U` per unit state `x`, and the value-function
contribution adds `β_T · gT · (1 − δ)` per unit `x` via the
transition `F(x, s) = (1 − δ)·x + δ·s`, then the fixed-point identity
`gT = g_U + β_T · gT · (1 − δ)` gives `gT = g_U / (1 − β_T · (1 − δ))`.
Equivalently: the Target incumbent valuing higher non-compliance states
at rate `gT` on the basin is **derived** from the primitive
single-period payoff state-slope, not assumed independently.

Rule-1 caveat on closed-loop α: at the equilibrium argmax, the
envelope statement `v'(x) = F_x(x, α*(x))` means α drops out of the
state-derivative. We use the existing α-on-substituted integrand
machinery from R20 (`joint_T_integrand V_T V_S x a`), where σ_dyn is
already the Sender's best response and the `sSup` over `a ∈ I` picks
the Target's argmax — the wrapper does not fix any strategy.

## Rule compliance

* Rule 1: structural — no strategy fixings; the user-supplied
  `h_integrand_lowerSlope` is a lower bound on the joint integrand
  uniform in `a`, and the `sSup` over `a ∈ I` automatically picks the
  Target's argmax.
* Rule 3: pure cat-2 weakening. The Target gain rate `gT` becomes
  derived as `bellmanLowerSlopeConstant p.β_T (1 - p.δ) g_U`; the
  carrier-local value-gain condition becomes derived from a
  scalar primitive (integrand state-slope) plus the contraction
  margin `β_T · (1 − δ) < 1`. (Both were fields of the core compliance
  certificate until round BJ1.4, 2026-10-07, which deleted the Target
  loss-offset stack from it; the discharger stands on its own.) No new fields are added; the
  primitives this discharger consumes are strictly weaker than the
  opaque `LowerSlopeOnValueOn` Prop it discharges.
* Rule 5: fully parametric over `(V_T, V_S, g_U, xT)`.
* Rule 8: paraphrase above plus inline docs below.
* Rule 9: non-vacuity witness in `StandardCompliancePolynomialSkeleton.lean`. -/

/-- **Round-27 Hinderer-4.2(c) lower-slope: `jointTarget_BCF V_T V_S _` has
minimum upward slope `g` on the basin from an integrand lower-slope
primitive.**

From the pointwise-in-x lower-slope bound `g · dist y₁ y₂ ≤
joint_T_integrand V_T V_S y₂.val a − joint_T_integrand V_T V_S y₁.val a`
(uniform in `a ∈ I`, valid for `y₁.val ≤ y₂.val ∈ B`), conclude
`LowerSlopeOnValueOn (jointTarget_BCF V_T V_S h_unique) B g`.

Proof: the `sSup`-over-`a` lower-slope follows from
`Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise`.

In closed-form usage, callers instantiate `g := bellmanLowerSlopeConstant
p.β_T (1 − p.δ) g_U` after deriving the integrand bound from a primitive
stage-payoff state-slope `g_U` via the inductive lower-slope
preservation chain seeded by `V₀(y) = g_U · y` and the cone-margin
identity `g_U + β_T · g · (1 − δ) = g`.

Round BJ1.2 (2026-10-07): the integrand bound is the only hypothesis. The cube
block (`cube_T`, `R_T`, `‖V_T‖ ≤ R_T`, the cube bound and their signs) and
`0 ≤ g` were there only to bound the integrand image above, and that follows
from primitives: `cube_bound_U_T` bounds `|U_T|` on the feasible cube and
`‖V_T‖` bounds the continuation. The former paper-facing duplicate
`jointTarget_BCF_preserves_lowerSlopeOnValueOn` (a rename with the same
statement) is merged into this theorem. General in `F`: the transition enters
only through the integrand.

Round BJ4.3 (2026-10-08): the state-local operator `jointTarget_BCF_on_S` now
takes compliance-local Sender uniqueness (`DynamicArgmaxUniqueOnI`), so it is
applied to the `.toOnI` image of the `DynamicArgmaxUnique` proof. Hypotheses
and conclusion are otherwise unchanged. General in `F`. -/
theorem jointTarget_BCF_lowerSlope_of_integrand_lowerSlope
    (V_T V_S : Val) (h_unique : p.DynamicArgmaxUnique V_S)
    {g xT : ℝ}
    (h_integrand_lowerSlope :
      ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        y₁.val ∈ Set.Icc xT 1 → y₂.val ∈ Set.Icc xT 1 → y₁ ≤ y₂ →
        g * dist y₁ y₂ ≤
          p.joint_T_integrand V_T V_S y₂.val a
          - p.joint_T_integrand V_T V_S y₁.val a) :
    LowerSlopeOnValueOn (p.jointTarget_BCF_on_S V_T V_S h_unique.toOnI)
      (Set.Icc xT 1) g := by
  intro y₁ y₂ hy₁ hy₂ hle
  -- jointTarget_BCF V_T V_S _ y_i = sSup ((fun a => joint_T_integrand V_T V_S y_i.val a) '' I)
  rw [p.jointTarget_BCF_on_S_apply V_T V_S h_unique.toOnI y₁,
      p.jointTarget_BCF_on_S_apply V_T V_S h_unique.toOnI y₂]
  -- Apply the sup-difference lower-bound lemma.
  -- Pointwise: g · dist y₁ y₂ ≤ joint_T_integrand V_T V_S y₂.val a
  --                              - joint_T_integrand V_T V_S y₁.val a.
  have h_pointwise :
      ∀ a ∈ Sanctions.I,
        g * dist y₁ y₂ ≤
          p.joint_T_integrand V_T V_S y₂.val a
          - p.joint_T_integrand V_T V_S y₁.val a := fun a ha =>
    h_integrand_lowerSlope y₁ y₂ a ha hy₁ hy₂ hle
  -- BddAbove witness for the y₂ image: the primitive cube bound on `U_T`
  -- plus the sup norm of `V_T`.
  obtain ⟨cube_T, -, hU_T_cube⟩ := p.cube_bound_U_T
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_int_bound :
      ∀ y : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
        p.joint_T_integrand V_T V_S y.val a ≤ cube_T + p.β_T * ‖V_T‖ := by
    intro y a ha
    have hy_mem : y.val ∈ Sanctions.I := ⟨y.property.1, y.property.2⟩
    simp only [joint_T_integrand]
    have h_σ_mem : p.σ_dyn V_S y.val a ∈ Sanctions.I :=
      p.σ_dyn_mem V_S y.val a
    have hUle : p.U_T y.val a (p.σ_dyn V_S y.val a) ≤ cube_T :=
      le_of_abs_le (hU_T_cube y.val hy_mem a ha (p.σ_dyn V_S y.val a) h_σ_mem)
    have hVle : V_T (Sanctions.clipS'
          (p.F y.val (p.σ_dyn V_S y.val a))) ≤ ‖V_T‖ := by
      have := BoundedContinuousFunction.norm_coe_le_norm V_T
        (Sanctions.clipS' (p.F y.val (p.σ_dyn V_S y.val a)))
      rw [Real.norm_eq_abs] at this
      exact le_of_abs_le this
    have h_term :
        p.β_T * V_T (Sanctions.clipS'
          (p.F y.val (p.σ_dyn V_S y.val a))) ≤ p.β_T * ‖V_T‖ :=
      mul_le_mul_of_nonneg_left hVle hβ_T_nn
    linarith
  have h_I_ne : (Sanctions.I : Set ℝ).Nonempty := ⟨0, by simp [Sanctions.I]⟩
  -- Wrap the BddAbove for the y₂ image.
  have hf_bdd : BddAbove
      ((fun a => p.joint_T_integrand V_T V_S y₂.val a) '' Sanctions.I) := by
    refine ⟨cube_T + p.β_T * ‖V_T‖, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact h_int_bound y₂ a ha
  -- Apply the sup-difference lower-bound lemma from Foundations.
  exact Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise
    h_I_ne h_pointwise hf_bdd

/-! ## Discharging the integrand lower slope at a general transition

`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope` above is already general in `F` —
it carries no `hF` — but it consumes `h_integrand_lowerSlope`, and until now that
hypothesis had **no parametric discharger anywhere**: the only one in the tree is
at a single witness (`polyComplianceParams_joint_T_integrand_lowerSlope_at_carrier`
in `Examples/StandardCompliancePolynomialSkeleton.lean`), and the route its
docstring sketches runs through `bellmanLowerSlopeConstant β_T (1−δ)`, which is
affine-flavoured. So the gain-ball route was general in form but affine in
practice.

The device that freed the Sender cone works here too. `V_T` has lower slope `g`
iff `V_T − g·id` is increasing, and monotonicity is a closed convex cone property
in the sense of Smith and McCardle (2002), *Structural Properties of Stochastic
Dynamic Programs*, Operations Research 50(5), 796–809 — so the transition belongs
inside a modified reward rather than in a condition of its own.

One complication the Sender side did not have: here the sanction moves with the
state, because the integrand is evaluated at `σ_dyn V_S x a`. So the chord is
taken along the *realised* pair `(x, σ_dyn V_S x a)` rather than at a fixed
sanction, and the successor states must be ordered — which is `hsucc_mono` below,
not automatic from `F_mono_x` alone since `σ_dyn` also varies.

Economically: *moving to a deeper political state raises the Target's realised
stage payoff plus the discounted value of the entrenchment its own best response
then produces by at least `g` per unit.* Both channels counted together, at the
sanctions actually chosen. -/

/-- **Integrand lower slope from one joint chord, at a general transition.**
Discharges `h_integrand_lowerSlope` — the hypothesis of
`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope` — without any condition on `F`
beyond the basin staying put and the successor states being ordered.

Inputs:

* `hV_T_cone` — the incoming Target value already has minimum upward slope `g` on
  the basin (this is carrier membership, so it is free inside the gain ball);
* `hbasin` — the transition keeps the basin: from a basin state, any feasible
  sanction lands back in `[xT, 1]`;
* `hsucc_mono` — a deeper state produces a weakly deeper successor *at the
  realised sanction*;
* `h_joint_chord` — the single substantive condition, combining the Target's
  stage payoff and the discounted successor state at the realised sanctions.

No `hF`, no chord on `F` alone, no named scalar beyond `g` itself. -/
theorem joint_T_integrand_lowerSlope_of_joint_chord
    {V_T V_S : Val} {g xT : ℝ}
    (hxT_nn : 0 ≤ xT)
    (hV_T_cone : LowerSlopeOnValueOn V_T (Set.Icc xT 1) g)
    (hbasin : ∀ x ∈ Set.Icc xT (1 : ℝ), ∀ s ∈ Sanctions.I,
      p.F x s ∈ Set.Icc xT 1)
    (hsucc_mono :
      ∀ a ∈ Sanctions.I, ∀ x₁ ∈ Set.Icc xT (1 : ℝ), ∀ x₂ ∈ Set.Icc xT (1 : ℝ),
        x₁ ≤ x₂ →
          p.F x₁ (p.σ_dyn V_S x₁ a) ≤ p.F x₂ (p.σ_dyn V_S x₂ a))
    (h_joint_chord :
      ∀ a ∈ Sanctions.I, ∀ x₁ ∈ Set.Icc xT (1 : ℝ), ∀ x₂ ∈ Set.Icc xT (1 : ℝ),
        x₁ ≤ x₂ →
          g * (x₂ - x₁)
            ≤ (p.U_T x₂ a (p.σ_dyn V_S x₂ a) - p.U_T x₁ a (p.σ_dyn V_S x₁ a))
              + p.β_T * g
                  * (p.F x₂ (p.σ_dyn V_S x₂ a) - p.F x₁ (p.σ_dyn V_S x₁ a))) :
    ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), ∀ a ∈ Sanctions.I,
      y₁.val ∈ Set.Icc xT 1 → y₂.val ∈ Set.Icc xT 1 → y₁ ≤ y₂ →
      g * dist y₁ y₂ ≤
        p.joint_T_integrand V_T V_S y₂.val a
          - p.joint_T_integrand V_T V_S y₁.val a := by
  intro y₁ y₂ a ha hy₁ hy₂ hle
  have hβ : (0 : ℝ) ≤ p.β_T := p.β_T_mem.1
  have hyle : y₁.val ≤ y₂.val := hle
  have hd : dist y₁ y₂ = y₂.val - y₁.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  have hs₁ : p.σ_dyn V_S y₁.val a ∈ Sanctions.I := p.σ_dyn_mem V_S y₁.val a
  have hs₂ : p.σ_dyn V_S y₂.val a ∈ Sanctions.I := p.σ_dyn_mem V_S y₂.val a
  have hF₁ : p.F y₁.val (p.σ_dyn V_S y₁.val a) ∈ Set.Icc xT 1 :=
    hbasin y₁.val hy₁ _ hs₁
  have hF₂ : p.F y₂.val (p.σ_dyn V_S y₂.val a) ∈ Set.Icc xT 1 :=
    hbasin y₂.val hy₂ _ hs₂
  have hF₁I : p.F y₁.val (p.σ_dyn V_S y₁.val a) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hxT_nn hF₁.1, hF₁.2⟩
  have hF₂I : p.F y₂.val (p.σ_dyn V_S y₂.val a) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hxT_nn hF₂.1, hF₂.2⟩
  have hFle : p.F y₁.val (p.σ_dyn V_S y₁.val a)
      ≤ p.F y₂.val (p.σ_dyn V_S y₂.val a) :=
    hsucc_mono a ha y₁.val hy₁ y₂.val hy₂ hyle
  have hc₁ : (Sanctions.clipS' (p.F y₁.val (p.σ_dyn V_S y₁.val a))).val
      = p.F y₁.val (p.σ_dyn V_S y₁.val a) :=
    Sanctions.clipS'_val_eq_of_mem hF₁I
  have hc₂ : (Sanctions.clipS' (p.F y₂.val (p.σ_dyn V_S y₂.val a))).val
      = p.F y₂.val (p.σ_dyn V_S y₂.val a) :=
    Sanctions.clipS'_val_eq_of_mem hF₂I
  have hord : Sanctions.clipS' (p.F y₁.val (p.σ_dyn V_S y₁.val a))
      ≤ Sanctions.clipS' (p.F y₂.val (p.σ_dyn V_S y₂.val a)) :=
    Sanctions.clipS'_mono hFle
  have hcone := hV_T_cone
    (Sanctions.clipS' (p.F y₁.val (p.σ_dyn V_S y₁.val a)))
    (Sanctions.clipS' (p.F y₂.val (p.σ_dyn V_S y₂.val a)))
    (by rw [hc₁]; exact hF₁) (by rw [hc₂]; exact hF₂) hord
  have hdist :
      dist (Sanctions.clipS' (p.F y₁.val (p.σ_dyn V_S y₁.val a)))
           (Sanctions.clipS' (p.F y₂.val (p.σ_dyn V_S y₂.val a)))
        = p.F y₂.val (p.σ_dyn V_S y₂.val a)
          - p.F y₁.val (p.σ_dyn V_S y₁.val a) := by
    rw [Subtype.dist_eq, Real.dist_eq, hc₁, hc₂, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [hdist] at hcone
  have hscaled : p.β_T * (g * (p.F y₂.val (p.σ_dyn V_S y₂.val a)
        - p.F y₁.val (p.σ_dyn V_S y₁.val a)))
      ≤ p.β_T * (V_T (Sanctions.clipS' (p.F y₂.val (p.σ_dyn V_S y₂.val a)))
          - V_T (Sanctions.clipS' (p.F y₁.val (p.σ_dyn V_S y₁.val a)))) :=
    mul_le_mul_of_nonneg_left hcone hβ
  have hU := h_joint_chord a ha y₁.val hy₁ y₂.val hy₂ hyle
  rw [hd]
  simp only [joint_T_integrand]
  nlinarith [hU, hscaled]

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
