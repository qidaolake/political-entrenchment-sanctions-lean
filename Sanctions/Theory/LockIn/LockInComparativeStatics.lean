/-
Sanctions/Theory/LockIn/LockInComparativeStatics.lean

**Band-MCS round: deep-parameter comparative statics of the lock-in
level (digest [75], Acemoglu-Jensen 2015; user-approved all phases
2026-06-12).**

The E2 round established the lock-in band: on the basin the step map
`G(x) = (1−δ)x + δ·σ_real(x)` has a least fixed point, and at every
fixed point the realized sanction equals the state. This round makes
the band MOVE in interpretable directions:

1. **Transport form** (`dynamicTopLockIn_least_fixedPoint_le_of_rule_le`):
   ANY change — payoffs, patience, carriers, Target policy — that
   weakly raises the realized sanction rule pointwise on the basin
   weakly raises the lock-in level. Stated across two `Params` (the
   same-`p` form is the diagonal instance). Engine:
   `least_fixedPoint_le_fixedPoint_of_pointwise_le`
   (`Foundations/MonotoneThreshold.lean`). Since round BH-2
   (2026-10-06, BH2.4) the comparison runs through an `F`-free, `δ`-free
   core on the least crossings of the realized rules
   (`dynamicTopRealizedRule_leastCrossing_le_of_rule_le`); the two `δ`s
   need not be equal, the levels are exported as *least* fixed points,
   and the general-`F` step has its own siblings
   (`dynamicTopLockInStepF_least_fixedPoint_le_of_rule_le` and
   `..._of_strictAdjustment`).

2. **Weak weighted-step comparison, with a positive-weight invariance
   boundary**
   (`dynamicTopLockIn_band_mono_in_weight`): at a FIXED realized
   rule with the basin floor `x ≤ σ_real(x)` (an output of the
   persistence machinery), the weighted step maps
   `x ↦ (1−w)x + w·σ_real(x)` have least fixed points monotone in
   the weight. The comparison is potentially nontrivial at `w = 0`.
   For every positive weight, however, the fixed-point equation is
   equivalent to `σ_real(x) = x`, so the fixed-point set is invariant.
   Faster adjustment may change transition paths or basin-entry speed;
   it does not move the steady-state set at a fixed rule. The
   `δ`-inside-the-objective channel is not claimed.

3. **Patience deepens lock-in — the Phase-2 result**
   (`σ_dyn_top_le_of_beta_le` + `dynamicTopLockIn_band_le_of_beta_le`):
   across two economies identical except for Sender patience
   (`U_S`, `δ` equal, `β_S₁ ≤ β_S₂`), at fixed continuation value
   and fixed Target policy the more patient Sender's greatest
   sanction response is pointwise weakly higher on the basin, and
   therefore its lock-in level is weakly higher. The one
   assumption (user-approved Rule-3 stop, 2026-06-12): the Sender
   value is weakly increasing on the basin transition range,
   stated with the EXISTING predicate at slope zero —
   `LowerSlopeOnValueOn V_S (Icc lo 1) 0`, `lo ≤ (1−δ)·x̄` — "the
   Sender weakly prefers deeper entrenchment on its own lock-in
   basin's reachable range." No new Prop, no new scalar. Witness
   anchor: constant `V_S` (R34) satisfies it with equality.
   HONEST SCOPE: this is the direct effect at fixed `(V_S, α)`;
   the equilibrium re-adjustment of `V_S` and `α` (channel 3, the
   full Acemoglu-Jensen 2015 program) was recorded as open here and
   is now CLOSED AT THE CORNER WITNESS FAMILIES (Wave-6 P11,
   2026-07-12): `Examples/FeedbackComparativeStatics.lean` computes
   the full-adjustment derivatives in exact closed form via the
   parametrized pinned Bellman fixed points (machine-checked
   full = direct + feedback splits; exact δ-invariance of the
   lock-in value; the zero policy-response term exhibited). The
   interior-policy feedback channel (nonzero `dσ*/dθ`) remains open.
   Both results ship in general-transition form
   (`σ_dyn_top_le_of_beta_le_generalF`,
   `dynamicTopLockIn_band_le_of_beta_le_generalF`): the affine
   hypotheses `hF₁`/`hF₂` are replaced by shared-transition
   `hFeq : p₁.F = p₂.F` and the affine floor `lo ≤ (1−δ)·x̄` by its
   `F`-parametric form `lo ≤ F(x̄, 0)`, with `F_mem`/`F_mono_x`/
   `F_mono_s` supplying the reachable-range bounds. The affine
   theorems are retained as one-step corollaries (Rule 5). Since
   round BH-2 the band comparison needs no `δ₁ = δ₂`, exports
   leastness, and has a general-`F`-step sibling
   (`dynamicTopLockInStepF_band_le_of_beta_le_generalF`).

Rule 3: one approved hypothesis, zero new symbols. Rule 13:
additive. Rule 19: the fixed-point and argmax comparison engines
are generic and live in `Foundations/MonotoneThreshold.lean`.
-/

import Sanctions.Theory.LockIn.LockInLimit
import Sanctions.Foundations.PatienceDecomposition
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.LockIn.LocalisedShockEntry

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame

/-! ## Comparative statics of the quantitative general-`F` shock bound

Since BG2.4 (2026-10-06) these comparisons carry no two-sided adjustment
hypothesis. Where a positive drift is needed (the horizon bounds), they ask only
that the *first* law lift every pre-basin state at full sanction,
`x < F₁(x,1)` on `[0, xbar]`, plus `0 ≤ xbar`; the second law inherits the
ascent through the dominance hypothesis. The named-minimum comparisons need no
adjustment hypothesis at all: the minimum is attained by continuity
(`Params.fullShockMinDrift_attains_isMinOn`), whatever its sign. The old
hypotheses — strict adjustment (F5) of both laws and `xbar ∈ [0,1)` — imply the
new ones (`preBasinAscent_of_strictAdjustment`), so every statement here is a
weakening. -/

/-- **The canonical minimum drift is attained, with no adjustment hypothesis.**
Attainment helper for the named-minimum comparisons below: the full-sanction
drift `F(x,1) − x` is continuous, so on the compact non-empty interval
`[0, xbar]` it attains its minimum, and the named infimum `fullShockMinDrift xbar`
equals that minimum. Nothing about the sign of the drift is assumed. General in
`F` (BG2.4). -/
theorem Params.fullShockMinDrift_attains_isMinOn (p : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar) :
    (∃ xmin ∈ Set.Icc (0 : ℝ) xbar,
        p.fullShockMinDrift xbar = p.fullShockDrift xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) xbar, p.fullShockMinDrift xbar ≤ p.fullShockDrift x := by
  have hcont : Continuous (p.fullShockDrift) := by
    have hpair : Continuous (fun x : ℝ => (x, (1 : ℝ))) := by fun_prop
    exact (p.F_continuous.comp hpair).sub continuous_id
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hxbar_nn) hcont.continuousOn
  have hleast : IsLeast (p.fullShockDrift '' Set.Icc (0 : ℝ) xbar)
      (p.fullShockDrift xmin) :=
    ⟨⟨xmin, hxmin, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmin hx⟩
  have heq : p.fullShockMinDrift xbar = p.fullShockDrift xmin := hleast.csInf_eq
  refine ⟨⟨xmin, hxmin, heq⟩, fun x hx => ?_⟩
  rw [heq]
  exact hmin hx

/-- **A stronger full-sanction transition raises minimum drift and
weakly shortens the quantitative shock bound.** Suppose the first
transition law lifts every pre-basin state at full sanction,
`x < F₁(x,1)` on `[0, xbar]`, and the second law is pointwise weakly
above the first at full sanction there. Their attained minimum drifts
can then be chosen so that `η₁ ≤ η₂`, and hence

`⌈xbar / η₂⌉₊ ≤ ⌈xbar / η₁⌉₊`.

The comparison changes only the exogenous shock-entry bound. Once the
shock ends, the equilibrium persistence theorem remains responsible
for the endogenous continuation path.

General in `F`. Since BG2.4 (2026-10-06) the hypotheses are `0 ≤ xbar`,
pre-basin ascent of the first law, and the dominance; strict adjustment of
both laws and `xbar < 1` were dropped. The second law's positive drift comes
from the first law's through the dominance, and `xbar < 1` is implied by
ascent at `xbar` (`lt_one_of_preBasinAscent`). -/
theorem fullShockDrift_minima_horizon_mono_of_top_transition_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF₁_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p₁.F x 1)
    (hF_top_le : ∀ x ∈ Set.Icc (0 : ℝ) xbar, p₁.F x 1 ≤ p₂.F x 1) :
    ∃ η₁ η₂ : ℝ,
      0 < η₁ ∧ 0 < η₂ ∧
      (∃ xmin₁ ∈ Set.Icc (0 : ℝ) xbar,
        η₁ = p₁.fullShockDrift xmin₁) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₁ ≤ p₁.fullShockDrift x) ∧
      (∃ xmin₂ ∈ Set.Icc (0 : ℝ) xbar,
        η₂ = p₂.fullShockDrift xmin₂) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₂ ≤ p₂.fullShockDrift x) ∧
      η₁ ≤ η₂ ∧
      Nat.ceil (xbar / η₂) ≤ Nat.ceil (xbar / η₁) := by
  obtain ⟨η₁, hη₁_pos, hη₁_attains, hη₁_min⟩ :=
    p₁.fullShockDrift_exists_pos_isMinOn_of_preBasinAscent hxbar_nn hF₁_top_pre
  -- the second law ascends wherever the first does, by dominance
  obtain ⟨η₂, hη₂_pos, hη₂_attains, hη₂_min⟩ :=
    p₂.fullShockDrift_exists_pos_isMinOn_of_preBasinAscent hxbar_nn
      (fun x hx => lt_of_lt_of_le (hF₁_top_pre x hx) (hF_top_le x hx))
  have hdrift_le : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      p₁.fullShockDrift x ≤ p₂.fullShockDrift x := by
    intro x hx
    unfold Params.fullShockDrift
    linarith [hF_top_le x hx]
  have hη_le : η₁ ≤ η₂ := by
    obtain ⟨xmin₂, hxmin₂, hη₂_eq⟩ := hη₂_attains
    calc
      η₁ ≤ p₁.fullShockDrift xmin₂ := hη₁_min xmin₂ hxmin₂
      _ ≤ p₂.fullShockDrift xmin₂ := hdrift_le xmin₂ hxmin₂
      _ = η₂ := hη₂_eq.symm
  have hratio : xbar / η₂ ≤ xbar / η₁ :=
    div_le_div_of_nonneg_left hxbar_nn hη₁_pos hη_le
  exact ⟨η₁, η₂, hη₁_pos, hη₂_pos, hη₁_attains, hη₁_min,
    hη₂_attains, hη₂_min, hη_le, Nat.ceil_mono hratio⟩

/-- **Strict full-sanction transition dominance strictly raises the
minimum drift.** If the second transition is strictly higher at every
pre-basin state, then `η₁ < η₂`. The integer shock-horizon comparison
remains weak because the ceiling function is locally constant.

General in `F`. Since BG2.4 (2026-10-06): `0 ≤ xbar` and pre-basin ascent of
the first law replace strict adjustment of both laws and `xbar ∈ [0,1)`. -/
theorem fullShockDrift_minima_horizon_strict_of_top_transition_lt
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF₁_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p₁.F x 1)
    (hF_top_lt : ∀ x ∈ Set.Icc (0 : ℝ) xbar, p₁.F x 1 < p₂.F x 1) :
    ∃ η₁ η₂ : ℝ,
      0 < η₁ ∧ 0 < η₂ ∧
      (∃ xmin₁ ∈ Set.Icc (0 : ℝ) xbar,
        η₁ = p₁.fullShockDrift xmin₁) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₁ ≤ p₁.fullShockDrift x) ∧
      (∃ xmin₂ ∈ Set.Icc (0 : ℝ) xbar,
        η₂ = p₂.fullShockDrift xmin₂) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₂ ≤ p₂.fullShockDrift x) ∧
      η₁ < η₂ ∧
      Nat.ceil (xbar / η₂) ≤ Nat.ceil (xbar / η₁) := by
  obtain ⟨η₁, η₂, hη₁_pos, hη₂_pos, hη₁_attains, hη₁_min,
      hη₂_attains, hη₂_min, -, hN_le⟩ :=
    fullShockDrift_minima_horizon_mono_of_top_transition_le
      p₁ p₂ hxbar_nn hF₁_top_pre (fun x hx => (hF_top_lt x hx).le)
  have hη_lt : η₁ < η₂ := by
    obtain ⟨xmin₂, hxmin₂, hη₂_eq⟩ := hη₂_attains
    calc
      η₁ ≤ p₁.fullShockDrift xmin₂ := hη₁_min xmin₂ hxmin₂
      _ < p₂.fullShockDrift xmin₂ := by
        unfold Params.fullShockDrift
        linarith [hF_top_lt xmin₂ hxmin₂]
      _ = η₂ := hη₂_eq.symm
  exact ⟨η₁, η₂, hη₁_pos, hη₂_pos, hη₁_attains, hη₁_min,
    hη₂_attains, hη₂_min, hη_lt, hN_le⟩

/-- **Canonical minimum drift is monotone under full-sanction transition
dominance.** This is the named-object version of
`fullShockDrift_minima_horizon_mono_of_top_transition_le`: a transition
that is pointwise higher at full sanction on `[0, xbar]` has a weakly
higher canonical minimum drift.

General in `F`. Since BG2.4 (2026-10-06) no adjustment hypothesis at all:
only `0 ≤ xbar`, so that both minima are attained
(`Params.fullShockMinDrift_attains_isMinOn`); the minima need not be positive
for the comparison. Strict adjustment of both laws and `xbar < 1` were
dropped. -/
theorem fullShockMinDrift_mono_of_top_transition_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_le : ∀ x ∈ Set.Icc (0 : ℝ) xbar, p₁.F x 1 ≤ p₂.F x 1) :
    p₁.fullShockMinDrift xbar ≤ p₂.fullShockMinDrift xbar := by
  obtain ⟨-, hmin₁⟩ := p₁.fullShockMinDrift_attains_isMinOn hxbar_nn
  obtain ⟨⟨xmin₂, hxmin₂, hmin₂_eq⟩, -⟩ :=
    p₂.fullShockMinDrift_attains_isMinOn hxbar_nn
  calc
    p₁.fullShockMinDrift xbar ≤ p₁.fullShockDrift xmin₂ :=
      hmin₁ xmin₂ hxmin₂
    _ ≤ p₂.fullShockDrift xmin₂ := by
      unfold Params.fullShockDrift
      linarith [hF_top_le xmin₂ hxmin₂]
    _ = p₂.fullShockMinDrift xbar := hmin₂_eq.symm

/-- **Strict full-sanction transition dominance strictly raises the
canonical minimum drift.** The minimum for the stronger transition is
attained; evaluating the weaker transition at that same minimizer gives
the strict comparison.

General in `F`. Since BG2.4 (2026-10-06) no adjustment hypothesis at all:
only `0 ≤ xbar`, for attainment. Strict adjustment of both laws and
`xbar < 1` were dropped. -/
theorem fullShockMinDrift_strictMono_of_top_transition_lt
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF_top_lt : ∀ x ∈ Set.Icc (0 : ℝ) xbar, p₁.F x 1 < p₂.F x 1) :
    p₁.fullShockMinDrift xbar < p₂.fullShockMinDrift xbar := by
  obtain ⟨-, hmin₁⟩ := p₁.fullShockMinDrift_attains_isMinOn hxbar_nn
  obtain ⟨⟨xmin₂, hxmin₂, hmin₂_eq⟩, -⟩ :=
    p₂.fullShockMinDrift_attains_isMinOn hxbar_nn
  calc
    p₁.fullShockMinDrift xbar ≤ p₁.fullShockDrift xmin₂ :=
      hmin₁ xmin₂ hxmin₂
    _ < p₂.fullShockDrift xmin₂ := by
      unfold Params.fullShockDrift
      linarith [hF_top_lt xmin₂ hxmin₂]
    _ = p₂.fullShockMinDrift xbar := hmin₂_eq.symm

/-- **The canonical conservative shock horizon is antitone in the
full-sanction transition.** A weakly stronger transition raises the
minimum drift, so the ceiling bound `⌈xbar / η_F(xbar)⌉` weakly falls.

General in `F`. Since BG2.4 (2026-10-06): `0 ≤ xbar` and pre-basin ascent of
the first law, which makes its minimum drift positive so the ratio is
meaningful, replace strict adjustment of both laws and `xbar ∈ [0,1)`. -/
theorem fullShockEntryHorizon_anti_of_top_transition_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {xbar : ℝ} (hxbar_nn : 0 ≤ xbar)
    (hF₁_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p₁.F x 1)
    (hF_top_le : ∀ x ∈ Set.Icc (0 : ℝ) xbar, p₁.F x 1 ≤ p₂.F x 1) :
    p₂.fullShockEntryHorizon xbar ≤ p₁.fullShockEntryHorizon xbar := by
  have hη₁_pos :=
    (p₁.fullShockMinDrift_pos_attains_isMinOn_of_preBasinAscent hxbar_nn
      hF₁_top_pre).1
  have hη_le :=
    fullShockMinDrift_mono_of_top_transition_le p₁ p₂ hxbar_nn hF_top_le
  unfold Params.fullShockEntryHorizon
  exact Nat.ceil_mono
    (div_le_div_of_nonneg_left hxbar_nn hη₁_pos hη_le)

/-! ## Transport: rule dominance moves the band (cross-`Params`) -/

/-- **The least crossing of a dominated rule lies below every crossing of the
dominating rule** (round BH-2, 2026-10-06, BH2.4).

Two realized sanction rules `R₁`, `R₂` (possibly different `Params`, carriers,
values and Target policies) on the basin `[x̄, 1]`. If `R₁` is monotone, never
sanctions below the state (`x ≤ R₁ x`), and is pointwise below `R₂`, then `R₁`
has a least crossing `xs₁` of the 45-degree line in `[x̄, 1]`, and `xs₁` lies at
or below every crossing of `R₂` there.

In plain terms: anything that weakly raises the Sender's sanction rule on the
basin weakly raises its lowest self-sustaining sanction level, the state at
which the realized sanction exactly sustains the political state.

`F`-free and `δ`-free: neither the transition nor the adjustment speed appears,
so the statement is general in `F` trivially (Rule 22). No monotonicity, floor
or crossing hypothesis on `R₂` is needed. The step-map comparisons below are
corollaries: a fixed point of the affine step is exactly a crossing for any
`δ > 0` (`dynamicTopRealizedRule_eq_self_of_step_fixedPoint`), and so is a fixed
point of the general-`F` step under strict adjustment. -/
theorem dynamicTopRealizedRule_leastCrossing_le_of_rule_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (V_S₁ V_S₂ : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α₁ α₂ : ℝ → ℝ)
    {xbar : ℝ} (hxbar_le : xbar ≤ 1)
    (hfloor₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      x ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S₁ α₁)
      (Set.Icc xbar 1))
    (hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S₁ α₁ x
        ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x) :
    ∃ xs₁ ∈ Set.Icc xbar 1,
      p₁.dynamicTopRealizedRule V_S₁ α₁ xs₁ = xs₁ ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₁.dynamicTopRealizedRule V_S₁ α₁ y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₂.dynamicTopRealizedRule V_S₂ α₂ y = y → xs₁ ≤ y) := by
  have hlo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      xbar ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x :=
    fun x hx => hx.1.trans (hfloor₁ x hx)
  obtain ⟨xs₁, hxs₁_mem, hxs₁_fix, hleast⟩ :=
    Sanctions.MonotoneThreshold.exists_least_fixedPoint_of_monotoneOn_Icc hxbar_le
      hmono₁ (fun x hx => ⟨hlo x hx, (p₁.dynamicTopRealizedRule_mem V_S₁ α₁ x).2⟩)
  exact ⟨xs₁, hxs₁_mem, hxs₁_fix, hleast, fun y hy hfix =>
    Sanctions.MonotoneThreshold.least_fixedPoint_le_fixedPoint_of_pointwise_le
      hmono₁ hlo hleast hy hfix hrule_le⟩

/-- **The lock-in level is monotone under pointwise rule dominance.**
Two configurations (possibly different `Params`, different
carriers/values/policies) whose realized rules are pointwise ordered on the
basin have ordered least lock-in levels: `xs₁` is the least fixed point of the
first lock-in step on `[x̄, 1]`, `xs₂` the least of the second, and
`xs₁ ≤ xs₂`. Each level also pins the rule (`σ_real(x*) = x*`).

Since round BH-2 (2026-10-06, BH2.4) the two economies need not share `δ` (the
former hypothesis `hδeq` is dropped), and leastness of both levels is exported,
which the earlier statement left out (without it the conclusion held trivially
at `xs₁ = xs₂ = 1`). The proof is the `F`-free core
`dynamicTopRealizedRule_leastCrossing_le_of_rule_le` plus `δ`-cancellation: for
any `δ > 0` the fixed points of `(1−δ)·x + δ·σ_real(x)` are exactly the
crossings `σ_real(x) = x`. The step conjuncts are still stated over the affine
lock-in step `dynamicTopLockInStep`, which does not route through `p.F` (Rule 22,
axis 2), but they carry no transition content: the general-`F` siblings are
`dynamicTopLockInStepF_least_fixedPoint_le_of_rule_le` (shared `F`) and
`..._of_strictAdjustment` (strict adjustment). -/
theorem dynamicTopLockIn_least_fixedPoint_le_of_rule_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (V_S₁ V_S₂ : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α₁ α₂ : ℝ → ℝ)
    {xbar sbar₁ sbar₂ : ℝ} (hxbar_le : xbar ≤ 1)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S₁ α₁)
      (Set.Icc xbar 1))
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S₂ α₂)
      (Set.Icc xbar 1))
    (hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S₁ α₁ x
        ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      p₁.dynamicTopLockInStep V_S₁ α₁ xs₁ = xs₁ ∧
      p₁.dynamicTopRealizedRule V_S₁ α₁ xs₁ = xs₁ ∧
      p₂.dynamicTopLockInStep V_S₂ α₂ xs₂ = xs₂ ∧
      p₂.dynamicTopRealizedRule V_S₂ α₂ xs₂ = xs₂ ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₁.dynamicTopLockInStep V_S₁ α₁ y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₂.dynamicTopLockInStep V_S₂ α₂ y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  obtain ⟨xs₁, hxs₁_mem, hxs₁_rule, hxs₁_least, hxs₁_le⟩ :=
    dynamicTopRealizedRule_leastCrossing_le_of_rule_le p₁ p₂ V_S₁ V_S₂ α₁ α₂
      hxbar_le (fun x hx => le_trans (le_max_left x sbar₁) (h_level₁ x hx))
      hmono₁ hrule_le
  obtain ⟨xs₂, hxs₂_mem, hxs₂_rule, hxs₂_least, -⟩ :=
    dynamicTopRealizedRule_leastCrossing_le_of_rule_le p₂ p₂ V_S₂ V_S₂ α₂ α₂
      hxbar_le (fun x hx => le_trans (le_max_left x sbar₂) (h_level₂ x hx))
      hmono₂ (fun _ _ => le_rfl)
  -- `δ`-cancellation: a crossing of the rule is a fixed point of the affine step
  have hstep₁ : p₁.dynamicTopLockInStep V_S₁ α₁ xs₁ = xs₁ := by
    unfold Params.dynamicTopLockInStep
    rw [hxs₁_rule]
    ring
  have hstep₂ : p₂.dynamicTopLockInStep V_S₂ α₂ xs₂ = xs₂ := by
    unfold Params.dynamicTopLockInStep
    rw [hxs₂_rule]
    ring
  exact ⟨xs₁, hxs₁_mem, xs₂, hxs₂_mem, hstep₁, hxs₁_rule, hstep₂, hxs₂_rule,
    fun y hy hfix =>
      hxs₁_least y hy (p₁.dynamicTopRealizedRule_eq_self_of_step_fixedPoint V_S₁ α₁ hfix),
    fun y hy hfix =>
      hxs₂_least y hy (p₂.dynamicTopRealizedRule_eq_self_of_step_fixedPoint V_S₂ α₂ hfix),
    hxs₁_le xs₂ hxs₂_mem hxs₂_rule⟩

/-- **General-`F` lock-in levels are monotone under pointwise rule dominance,
for a shared transition** (round BH-2, 2026-10-06, BH2.4).

Two configurations sharing the transition (`p₁.F = p₂.F`) whose realized rules
are monotone, satisfy the basin level condition, and are pointwise ordered on
`[x̄, 1]`. Then the least fixed points of the two general-`F` closed loops
`x ↦ F(x, σ_real(x))` on `[x̄, 1]` are ordered, `xs₁ ≤ xs₂`. At each level the
sanction weakly exceeds the state and the transition is flat on the band
between them (`F(x*, s) = x*` for `s ∈ [x*, σ_real(x*)]`), the general-`F` form
of `σ_real(x*) = x*`.

In plain terms: under a common law of motion, raising the Sender's sanction
rule weakly raises the lowest steady political state on the basin.

General in `F`; no strict adjustment is assumed. The shared transition is what
orders the two closed loops pointwise (`F_mono_s`). Without it, and without
strict adjustment (next theorem), the rules alone do not order the least step
fixed points: a transition that ignores the sanction, `F(x, s) = x`, fixes every
state, so its least fixed point is `x̄` whatever the rule. Sibling of the
affine-step comparison
`dynamicTopLockIn_least_fixedPoint_le_of_rule_le`, which needs no shared
transition. -/
theorem dynamicTopLockInStepF_least_fixedPoint_le_of_rule_le
    (p₁ p₂ : Sanctions.AbstractGame.Params) (hFeq : p₁.F = p₂.F)
    (V_S₁ V_S₂ : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α₁ α₂ : ℝ → ℝ)
    {xbar sbar₁ sbar₂ : ℝ} (hxbar_le : xbar ≤ 1)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S₁ α₁)
      (Set.Icc xbar 1))
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S₂ α₂)
      (Set.Icc xbar 1))
    (hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S₁ α₁ x
        ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      p₁.dynamicTopLockInStepF V_S₁ α₁ xs₁ = xs₁ ∧
      xs₁ ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ xs₁ ∧
      (∀ s ∈ Set.Icc xs₁ (p₁.dynamicTopRealizedRule V_S₁ α₁ xs₁),
        p₁.F xs₁ s = xs₁) ∧
      p₂.dynamicTopLockInStepF V_S₂ α₂ xs₂ = xs₂ ∧
      xs₂ ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ xs₂ ∧
      (∀ s ∈ Set.Icc xs₂ (p₂.dynamicTopRealizedRule V_S₂ α₂ xs₂),
        p₂.F xs₂ s = xs₂) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₁.dynamicTopLockInStepF V_S₁ α₁ y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₂.dynamicTopLockInStepF V_S₂ α₂ y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  obtain ⟨xs₁, hxs₁_mem, hxs₁_fix, hxs₁_le, hxs₁_band, hxs₁_least⟩ :=
    p₁.dynamicTopLockInStepF_exists_least_fixedPoint V_S₁ α₁ hxbar_le h_level₁ hmono₁
  obtain ⟨xs₂, hxs₂_mem, hxs₂_fix, hxs₂_le, hxs₂_band, hxs₂_least⟩ :=
    p₂.dynamicTopLockInStepF_exists_least_fixedPoint V_S₂ α₂ hxbar_le h_level₂ hmono₂
  -- the first closed loop is monotone on the basin
  have hG_mono : MonotoneOn (p₁.dynamicTopLockInStepF V_S₁ α₁) (Set.Icc xbar 1) := by
    intro x hx y hy hxy
    unfold Params.dynamicTopLockInStepF
    exact le_trans (p₁.F_mono_s x (hmono₁ hx hy hxy))
      (p₁.F_mono_x (p₁.dynamicTopRealizedRule V_S₁ α₁ y) hxy)
  -- it never lowers a basin state: `x = F(x, x) ≤ F(x, σ_real(x))`
  have hlo : ∀ x ∈ Set.Icc xbar (1 : ℝ), xbar ≤ p₁.dynamicTopLockInStepF V_S₁ α₁ x := by
    intro x hx
    have hfl : x ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x :=
      le_trans (le_max_left x sbar₁) (h_level₁ x hx)
    have h : p₁.F x x ≤ p₁.F x (p₁.dynamicTopRealizedRule V_S₁ α₁ x) :=
      p₁.F_mono_s x hfl
    rw [p₁.F_diag x] at h
    exact hx.1.trans h
  -- the shared transition orders the two closed loops pointwise
  have hG : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopLockInStepF V_S₁ α₁ x ≤ p₂.dynamicTopLockInStepF V_S₂ α₂ x := by
    intro x hx
    unfold Params.dynamicTopLockInStepF
    rw [← hFeq]
    exact p₁.F_mono_s x (hrule_le x hx)
  exact ⟨xs₁, hxs₁_mem, xs₂, hxs₂_mem, hxs₁_fix, hxs₁_le, hxs₁_band, hxs₂_fix,
    hxs₂_le, hxs₂_band, hxs₁_least, hxs₂_least,
    Sanctions.MonotoneThreshold.least_fixedPoint_le_fixedPoint_of_pointwise_le
      hG_mono hlo hxs₁_least hxs₂_mem hxs₂_fix hG⟩

/-- **General-`F` lock-in levels are monotone under pointwise rule dominance,
under strict adjustment** (round BH-2, 2026-10-06, BH2.4).

Two configurations whose transitions both satisfy strict directional adjustment
`(F5)` — the transitions need not coincide — on a feasible basin `[x̄, 1]`
(`0 ≤ x̄`). If the first realized rule is monotone, satisfies the level
condition and is pointwise below the second, and the second is monotone and
satisfies the level condition, then the least fixed points of the two
general-`F` closed loops are ordered, `xs₁ ≤ xs₂`, and each pins its rule
(`σ_real(x*) = x*`).

In plain terms: if each law of motion moves the state toward the sanction,
raising the Sender's sanction rule weakly raises the lowest steady political
state, whatever the two laws are.

General in `F`. Under `(F5)` the fixed points of a general-`F` step on feasible
states are exactly the crossings of its rule
(`dynamicTopLockInStepF_fixedPoint_iff_realizedRule_eq_self_of_strictAdjustment`),
so this is the `F`-free core read through that identification. `(F5)` and
`0 ≤ x̄` are used only for it; the comparison itself needs neither. -/
theorem dynamicTopLockInStepF_least_fixedPoint_le_of_rule_le_of_strictAdjustment
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hAdj₁ : p₁.StrictAdjustment) (hAdj₂ : p₂.StrictAdjustment)
    (V_S₁ V_S₂ : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α₁ α₂ : ℝ → ℝ)
    {xbar sbar₁ sbar₂ : ℝ} (hxbar0 : 0 ≤ xbar) (hxbar_le : xbar ≤ 1)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S₁ α₁)
      (Set.Icc xbar 1))
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S₂ α₂)
      (Set.Icc xbar 1))
    (hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S₁ α₁ x
        ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      p₁.dynamicTopLockInStepF V_S₁ α₁ xs₁ = xs₁ ∧
      p₁.dynamicTopRealizedRule V_S₁ α₁ xs₁ = xs₁ ∧
      p₂.dynamicTopLockInStepF V_S₂ α₂ xs₂ = xs₂ ∧
      p₂.dynamicTopRealizedRule V_S₂ α₂ xs₂ = xs₂ ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₁.dynamicTopLockInStepF V_S₁ α₁ y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ),
        p₂.dynamicTopLockInStepF V_S₂ α₂ y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  have hsub : ∀ y ∈ Set.Icc xbar (1 : ℝ), y ∈ Sanctions.I :=
    fun y hy => ⟨hxbar0.trans hy.1, hy.2⟩
  obtain ⟨xs₁, hxs₁_mem, hxs₁_rule, hxs₁_least, hxs₁_le⟩ :=
    dynamicTopRealizedRule_leastCrossing_le_of_rule_le p₁ p₂ V_S₁ V_S₂ α₁ α₂
      hxbar_le (fun x hx => le_trans (le_max_left x sbar₁) (h_level₁ x hx))
      hmono₁ hrule_le
  obtain ⟨xs₂, hxs₂_mem, hxs₂_rule, hxs₂_least, -⟩ :=
    dynamicTopRealizedRule_leastCrossing_le_of_rule_le p₂ p₂ V_S₂ V_S₂ α₂ α₂
      hxbar_le (fun x hx => le_trans (le_max_left x sbar₂) (h_level₂ x hx))
      hmono₂ (fun _ _ => le_rfl)
  exact ⟨xs₁, hxs₁_mem, xs₂, hxs₂_mem,
    p₁.dynamicTopLockInStepF_fixedPoint_of_realizedRule_eq_self V_S₁ α₁ hxs₁_rule,
    hxs₁_rule,
    p₂.dynamicTopLockInStepF_fixedPoint_of_realizedRule_eq_self V_S₂ α₂ hxs₂_rule,
    hxs₂_rule,
    fun y hy hfix => hxs₁_least y hy
      (p₁.dynamicTopRealizedRule_eq_self_of_stepF_fixedPoint_of_strictAdjustment hAdj₁
        V_S₁ α₁ (hsub y hy) hfix),
    fun y hy hfix => hxs₂_least y hy
      (p₂.dynamicTopRealizedRule_eq_self_of_stepF_fixedPoint_of_strictAdjustment hAdj₂
        V_S₂ α₂ (hsub y hy) hfix),
    hxs₁_le xs₂ hxs₂_mem hxs₂_rule⟩

/-! ## Realized paths and limits under rule dominance -/

/-- **Pointwise rule dominance orders the realized general-`F` paths.**
Suppose two configurations share the same transition map, start from
the same state in the high basin, and the second realized sanction rule
is monotone and pointwise dominates the first on that basin. Then the
second state path is weakly above the first at every date.

The basin-level conditions are the existing persistence hypotheses.
They keep both paths inside the domain on which rule dominance and
monotonicity are known.

General in `F`. No `0 ≤ xbar`: it was read only by the basin lemma
`dynamicTopLockInPathF_mem_basin`, which no longer needs it (dropped on
2026-10-06, BG2.1). -/
theorem dynamicTopLockInPathF_le_of_rule_le_on_basin
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hFeq : p₁.F = p₂.F)
    (V_S₁ V_S₂ : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α₁ α₂ : ℝ → ℝ)
    {xbar sbar₁ sbar₂ : ℝ}
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S₂ α₂)
      (Set.Icc xbar 1))
    (hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S₁ α₁ x
        ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p₁.dynamicTopLockInPathF V_S₁ α₁ x₀ n
      ≤ p₂.dynamicTopLockInPathF V_S₂ α₂ x₀ n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
    have h₁_mem :=
      p₁.dynamicTopLockInPathF_mem_basin V_S₁ α₁ h_level₁ hx₀ k
    have h₂_mem :=
      p₂.dynamicTopLockInPathF_mem_basin V_S₂ α₂ h_level₂ hx₀ k
    have hrules :
        p₁.dynamicTopRealizedRule V_S₁ α₁
            (p₁.dynamicTopLockInPathF V_S₁ α₁ x₀ k)
          ≤
        p₂.dynamicTopRealizedRule V_S₂ α₂
            (p₂.dynamicTopLockInPathF V_S₂ α₂ x₀ k) :=
      le_trans (hrule_le _ h₁_mem) (hmono₂ h₁_mem h₂_mem ih)
    rw [Params.dynamicTopLockInPathF_succ,
      Params.dynamicTopLockInPathF_succ]
    unfold Params.dynamicTopLockInStepF
    calc
      p₁.F _ (p₁.dynamicTopRealizedRule V_S₁ α₁ _) ≤
          p₁.F _ (p₂.dynamicTopRealizedRule V_S₂ α₂ _) :=
        p₁.F_mono_s _ hrules
      _ ≤ p₁.F _ (p₂.dynamicTopRealizedRule V_S₂ α₂ _) :=
        p₁.F_mono_x _ ih
      _ = p₂.F _ (p₂.dynamicTopRealizedRule V_S₂ α₂ _) := by rw [hFeq]

/-- **Rule dominance orders convergent realized lock-in limits.**
This is the closed-order limit of
`dynamicTopLockInPathF_le_of_rule_le_on_basin`. It deliberately takes
the two convergence results as inputs, separating path comparison from
the maintained strict-adjustment theorem that supplies convergence.
General in `F`; no `0 ≤ xbar` (a pass-through, dropped in BG2.1). -/
theorem dynamicTopLockInPathF_limit_le_of_rule_le_on_basin
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hFeq : p₁.F = p₂.F)
    (V_S₁ V_S₂ : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α₁ α₂ : ℝ → ℝ)
    {xbar sbar₁ sbar₂ : ℝ}
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S₁ α₁ x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S₂ α₂)
      (Set.Icc xbar 1))
    (hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S₁ α₁ x
        ≤ p₂.dynamicTopRealizedRule V_S₂ α₂ x)
    {x₀ x₁ x₂ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1)
    (hpath₁ : Tendsto (p₁.dynamicTopLockInPathF V_S₁ α₁ x₀)
      atTop (𝓝 x₁))
    (hpath₂ : Tendsto (p₂.dynamicTopLockInPathF V_S₂ α₂ x₀)
      atTop (𝓝 x₂)) :
    x₁ ≤ x₂ := by
  apply le_of_tendsto_of_tendsto hpath₁ hpath₂
  exact Filter.Eventually.of_forall
    (dynamicTopLockInPathF_le_of_rule_le_on_basin p₁ p₂ hFeq
      V_S₁ V_S₂ α₁ α₂ h_level₁ h_level₂ hmono₂ hrule_le hx₀)

/-! ## Phase 2: patience deepens lock-in -/

/-- **A more patient Sender's greatest sanction response is weakly
higher — general-transition form.** The exact `F`-parametric sibling
of `σ_dyn_top_le_of_beta_le`: the two economies share the same
abstract transition (`hFeq : p₁.F = p₂.F`, generalizing "same `δ` and
both affine") and the same stage payoff, and the reachable-range
floor is stated at the transition itself (`hlo_le : lo ≤ p₁.F x 0`,
generalizing `lo ≤ (1−δ)·x`; `F_mono_s` then floors every reachable
next state `F x z`, `z ∈ [0,1]`, and `F_mem` caps it at `1`). Under
the same slope-zero value-monotonicity hypothesis the objective
difference `(β₂−β₁)·V_S(F(x,·))` is nondecreasing in the sanction,
so the greatest maximizers are ordered. No affine structure is used
anywhere; `δ` does not appear (it enters the dynamic objective only
through `F`). -/
theorem σ_dyn_top_le_of_beta_le_generalF
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hFeq : p₁.F = p₂.F)
    (hU : p₁.U_S = p₂.U_S)
    (hβ : p₁.β_S ≤ p₂.β_S)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {lo : ℝ}
    (hmonoV : Params.LowerSlopeOnValueOn V_S (Set.Icc lo 1) 0)
    {x a : ℝ} (hx01 : x ∈ Sanctions.I)
    (hlo_le : lo ≤ p₁.F x 0) :
    p₁.σ_dyn_top V_S x a ≤ p₂.σ_dyn_top V_S x a := by
  obtain ⟨hmem₁, hmax₁⟩ := p₁.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
  obtain ⟨hmem₂, hmax₂⟩ := p₂.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
  have hclip : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → Sanctions.clipS y = y := by
    intro y h0 h1
    simp [Sanctions.clipS, min_eq_right h1, max_eq_right h0]
  -- the reachable next states stay in [lo, 1] and in [0, 1]
  have hrange : ∀ z ∈ Sanctions.I,
      p₂.F x z ∈ Set.Icc lo 1 ∧
      (0 : ℝ) ≤ p₂.F x z ∧ p₂.F x z ≤ 1 := by
    intro z hz
    have hmem := p₂.F_mem x z hx01 hz
    have hfloor : lo ≤ p₂.F x z := by
      have h0 : p₂.F x 0 ≤ p₂.F x z := p₂.F_mono_s x hz.1
      have h1 : lo ≤ p₂.F x 0 := by rw [← hFeq]; exact hlo_le
      linarith
    exact ⟨⟨hfloor, hmem.2⟩, hmem.1, hmem.2⟩
  -- monotone V along the reachable range, in clip coordinates
  have hVmono : ∀ z₁ z₂ : ℝ, z₁ ∈ Sanctions.I → z₂ ∈ Sanctions.I →
      z₁ ≤ z₂ →
      V_S (Sanctions.clipS' (p₂.F x z₁))
        ≤ V_S (Sanctions.clipS' (p₂.F x z₂)) := by
    intro z₁ z₂ hz₁ hz₂ hzz
    obtain ⟨hr₁, h0₁, h1₁⟩ := hrange z₁ hz₁
    obtain ⟨hr₂, h0₂, h1₂⟩ := hrange z₂ hz₂
    have hy_le : p₂.F x z₁ ≤ p₂.F x z₂ := p₂.F_mono_s x hzz
    have h := hmonoV (Sanctions.clipS' (p₂.F x z₁))
      (Sanctions.clipS' (p₂.F x z₂))
      (by
        change Sanctions.clipS (p₂.F x z₁) ∈ Set.Icc lo 1
        rw [hclip _ h0₁ h1₁]
        exact hr₁)
      (by
        change Sanctions.clipS (p₂.F x z₂) ∈ Set.Icc lo 1
        rw [hclip _ h0₂ h1₂]
        exact hr₂)
      (Sanctions.clipS_mono hy_le)
    rw [zero_mul] at h
    linarith
  -- two-objective comparison: greatest maximizers ordered
  apply Sanctions.MonotoneThreshold.le_greatestMaxOn_of_diff_mono
    (f := fun s' => p₁.U_S x a s'
      + p₁.β_S * V_S (Sanctions.clipS' (p₁.F x s')))
    (g := fun s' => p₂.U_S x a s'
      + p₂.β_S * V_S (Sanctions.clipS' (p₂.F x s')))
    (S := Sanctions.I)
    hmem₁ hmem₂ (fun z hz => hmax₁ hz) (fun z hz => hmax₂ hz)
    (fun z hz hzmax =>
      le_csSup (p₂.dynamicArgmaxSet_bddAbove V_S x a)
        ⟨hz, fun w hw => hzmax w hw⟩)
    ?_
  intro z₁ z₂ hz₁ hz₂ hzz
  simp only
  rw [hU, hFeq]
  have hV := hVmono z₁ z₂ hz₁ hz₂ hzz
  have hmul := mul_le_mul_of_nonneg_left hV
    (by linarith : (0 : ℝ) ≤ p₂.β_S - p₁.β_S)
  nlinarith

/-- **Patience orders the realized general-`F` lock-in paths and
their limits, conditional on the existing direct-effect environment.**
The two economies share `F`, the stage payoff, continuation value, and
Target policy. Greater Sender patience raises the realized sanction
rule pointwise; transition monotonicity then orders every state-path
iterate. Under the maintained strict-adjustment condition, both state
and sanction paths converge and the first limit is weakly below the
second.

This is the realized-path counterpart to the extremal fixed-point
comparison. It preserves the same honest scope: continuation values
and the Target policy are held fixed, so equilibrium feedback through
those objects is not claimed.

General in `F`. Since BG2.4 (2026-10-06) strict adjustment is assumed of the
first economy only: `StrictAdjustment` reads nothing but the transition, and
the two economies share it (`hFeq`), so the second economy's copy was the
first one's moved across `hFeq`. -/
theorem dynamicTopLockInPathF_limit_le_of_beta_le_generalF
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hAdj₁ : p₁.StrictAdjustment)
    (hFeq : p₁.F = p₂.F)
    (hU : p₁.U_S = p₂.U_S) (hβ : p₁.β_S ≤ p₂.β_S)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hα_cont : Continuous α)
    {xbar sbar₁ sbar₂ lo x₀ : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlo_le : lo ≤ p₁.F xbar 0)
    (hmonoV : Params.LowerSlopeOnValueOn V_S (Set.Icc lo 1) 0)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S α x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S α x)
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1))
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∃ x₁ ∈ Set.Icc xbar 1, ∃ x₂ ∈ Set.Icc xbar 1,
      Tendsto (p₁.dynamicTopLockInPathF V_S α x₀) atTop (𝓝 x₁)
      ∧ Tendsto (p₁.dynamicTopLockInSanctionsF V_S α x₀) atTop (𝓝 x₁)
      ∧ Tendsto (p₂.dynamicTopLockInPathF V_S α x₀) atTop (𝓝 x₂)
      ∧ Tendsto (p₂.dynamicTopLockInSanctionsF V_S α x₀) atTop (𝓝 x₂)
      ∧ x₁ ≤ x₂ := by
  have hrule_le : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      p₁.dynamicTopRealizedRule V_S α x
        ≤ p₂.dynamicTopRealizedRule V_S α x := by
    intro x hx
    have hxI : x ∈ Sanctions.I :=
      ⟨le_trans hxbar_mem.1 hx.1, hx.2⟩
    have hlo_x : lo ≤ p₁.F x 0 :=
      le_trans hlo_le (p₁.F_mono_x 0 hx.1)
    exact σ_dyn_top_le_of_beta_le_generalF p₁ p₂ hFeq hU hβ V_S hmonoV
      hxI hlo_x
  -- strict adjustment is a statement about the shared transition only
  have hAdj₂ : p₂.StrictAdjustment := by
    have h := hAdj₁
    unfold Params.StrictAdjustment at h ⊢
    rw [← hFeq]
    exact h
  obtain ⟨x₁, hx₁, hpath₁, hsanctions₁, -, -⟩ :=
    p₁.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment
      hAdj₁ V_S α hα_cont hxbar_mem.1 h_level₁ hx₀
  obtain ⟨x₂, hx₂, hpath₂, hsanctions₂, -, -⟩ :=
    p₂.dynamicTopLockInPathF_tendsto_steadyState_full_of_strictAdjustment
      hAdj₂ V_S α hα_cont hxbar_mem.1 h_level₂ hx₀
  have hx₁_le_x₂ :=
    dynamicTopLockInPathF_limit_le_of_rule_le_on_basin
      p₁ p₂ hFeq V_S V_S α α h_level₁ h_level₂ hmono₂
      hrule_le hx₀ hpath₁ hpath₂
  exact ⟨x₁, hx₁, x₂, hx₂, hpath₁, hsanctions₁, hpath₂,
    hsanctions₂, hx₁_le_x₂⟩


/-- **Patience deepens lock-in — general-transition form.** The exact
`F`-parametric sibling of `dynamicTopLockIn_band_le_of_beta_le`: the
two economies share the same abstract transition
(`hFeq : p₁.F = p₂.F`) and the basin floor is stated at the
transition (`hlo_le : lo ≤ p₁.F xbar 0`; `F_mono_x` transports it to
every basin state `x ≥ xbar`). The comparison of the two rules
(`σ_dyn_top_le_of_beta_le_generalF`, under `hFeq`) is general in `F`. The
conclusion: the more patient economy's least lock-in level is weakly higher,
both levels are least fixed points of their lock-in steps on `[x̄, 1]`, and
each pins the rule (`σ_real(x*) = x*`).

Since round BH-2 (2026-10-06, BH2.4) `hδeq : p₁.δ = p₂.δ` is dropped and
leastness is exported. The step conjuncts are stated over the affine lock-in
step `dynamicTopLockInStep = (1−δ)·x + δ·σ_real(x)` (Rule 22, axis 2), but for
any `δ > 0` its fixed points are exactly the rule crossings, so they carry no
transition content and need no equal speeds. The general-`F`-step form is
`dynamicTopLockInStepF_band_le_of_beta_le_generalF`. The transport engine is
`dynamicTopLockIn_least_fixedPoint_le_of_rule_le`. -/
theorem dynamicTopLockIn_band_le_of_beta_le_generalF
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hFeq : p₁.F = p₂.F)
    (hU : p₁.U_S = p₂.U_S)
    (hβ : p₁.β_S ≤ p₂.β_S)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar₁ sbar₂ lo : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlo_le : lo ≤ p₁.F xbar 0)
    (hmonoV : Params.LowerSlopeOnValueOn V_S (Set.Icc lo 1) 0)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S α x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S α x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1))
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1)) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      p₁.dynamicTopLockInStep V_S α xs₁ = xs₁ ∧
      p₁.dynamicTopRealizedRule V_S α xs₁ = xs₁ ∧
      p₂.dynamicTopLockInStep V_S α xs₂ = xs₂ ∧
      p₂.dynamicTopRealizedRule V_S α xs₂ = xs₂ ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ), p₁.dynamicTopLockInStep V_S α y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ), p₂.dynamicTopLockInStep V_S α y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  apply dynamicTopLockIn_least_fixedPoint_le_of_rule_le p₁ p₂
    V_S V_S α α hxbar_mem.2 h_level₁ h_level₂ hmono₁ hmono₂
  intro x hx
  have hxI : x ∈ Sanctions.I := ⟨le_trans hxbar_mem.1 hx.1, hx.2⟩
  have hlo_x : lo ≤ p₁.F x 0 :=
    le_trans hlo_le (p₁.F_mono_x 0 hx.1)
  exact σ_dyn_top_le_of_beta_le_generalF p₁ p₂ hFeq hU hβ V_S hmonoV
    hxI hlo_x

/-- **Patience deepens lock-in — general-`F` step** (round BH-2, 2026-10-06,
BH2.4). Across two economies identical except for Sender patience (shared
transition `hFeq`, shared stage payoff `hU`, `β_S₁ ≤ β_S₂`), at fixed
continuation value and Target policy and under the slope-zero value-monotonicity
hypothesis, the more patient economy's least steady state of the general-`F`
closed loop `x ↦ F(x, σ_real(x))` on the basin is weakly higher. Both levels are
least fixed points; at each the sanction weakly exceeds the state and the
transition is flat between them.

In plain terms: a more patient Sender, holding everything else fixed, sustains
weakly deeper lock-in under any common law of motion.

General in `F` in both the rule comparison and the conclusion; no `δ` appears
and no strict adjustment is assumed. Same hypotheses as
`dynamicTopLockIn_band_le_of_beta_le_generalF`; the conclusion is over
`dynamicTopLockInStepF`. Direct effect at fixed `(V_S, α)` only. -/
theorem dynamicTopLockInStepF_band_le_of_beta_le_generalF
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hFeq : p₁.F = p₂.F)
    (hU : p₁.U_S = p₂.U_S)
    (hβ : p₁.β_S ≤ p₂.β_S)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar₁ sbar₂ lo : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlo_le : lo ≤ p₁.F xbar 0)
    (hmonoV : Params.LowerSlopeOnValueOn V_S (Set.Icc lo 1) 0)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S α x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S α x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1))
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1)) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      p₁.dynamicTopLockInStepF V_S α xs₁ = xs₁ ∧
      xs₁ ≤ p₁.dynamicTopRealizedRule V_S α xs₁ ∧
      (∀ s ∈ Set.Icc xs₁ (p₁.dynamicTopRealizedRule V_S α xs₁), p₁.F xs₁ s = xs₁) ∧
      p₂.dynamicTopLockInStepF V_S α xs₂ = xs₂ ∧
      xs₂ ≤ p₂.dynamicTopRealizedRule V_S α xs₂ ∧
      (∀ s ∈ Set.Icc xs₂ (p₂.dynamicTopRealizedRule V_S α xs₂), p₂.F xs₂ s = xs₂) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ), p₁.dynamicTopLockInStepF V_S α y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ), p₂.dynamicTopLockInStepF V_S α y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  apply dynamicTopLockInStepF_least_fixedPoint_le_of_rule_le p₁ p₂ hFeq
    V_S V_S α α hxbar_mem.2 h_level₁ h_level₂ hmono₁ hmono₂
  intro x hx
  have hxI : x ∈ Sanctions.I := ⟨le_trans hxbar_mem.1 hx.1, hx.2⟩
  have hlo_x : lo ≤ p₁.F x 0 :=
    le_trans hlo_le (p₁.F_mono_x 0 hx.1)
  exact σ_dyn_top_le_of_beta_le_generalF p₁ p₂ hFeq hU hβ V_S hmonoV
    hxI hlo_x


namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Weighted-step comparison and its positive-weight boundary -/

/-- **Weighted-step least fixed points are weakly ordered.**
At a FIXED realized rule satisfying the basin floor (an output of
the persistence machinery), the weighted step maps
`x ↦ (1−w)x + w·σ_real(x)` have least fixed points monotone in the
weight. This theorem allows `w₁ = 0`, where the comparison can be
nontrivial. If both weights are positive, their fixed-point equations
are each equivalent to `σ_real(x) = x`, so the fixed-point sets
coincide. The result must therefore not be read as positive adjustment
speed moving steady states at a fixed realized rule. -/
theorem dynamicTopLockIn_band_mono_in_weight
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar w₁ w₂ : ℝ} (hxbar_le : xbar ≤ 1)
    (hw₁ : 0 ≤ w₁) (hw₂ : w₂ ≤ 1) (hww : w₁ ≤ w₂)
    (h_level_top : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x)
    (hrule_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1)) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      (1 - w₁) * xs₁ + w₁ * p.dynamicTopRealizedRule V_S α xs₁ = xs₁ ∧
      (1 - w₂) * xs₂ + w₂ * p.dynamicTopRealizedRule V_S α xs₂ = xs₂ ∧
      xs₁ ≤ xs₂ := by
  obtain ⟨xs₁, hxs₁_mem, xs₂, hxs₂_mem, hfix₁, hfix₂, _, _, hle⟩ :=
    Sanctions.MonotoneThreshold.exists_least_fixedPoints_le_of_weight_le
      hxbar_le hw₁ hw₂ hww hrule_mono
      (fun x hx => le_trans (le_max_left x sbar) (h_level_top x hx))
      (fun x hx => (p.dynamicTopRealizedRule_mem V_S α x).2)
  exact ⟨xs₁, hxs₁_mem, xs₂, hxs₂_mem, hfix₁, hfix₂, hle⟩

/-! ## Phase 3 — the patience identities, parametric and general in `F`

Phases 1 and 2 order *actions and paths* across two patience levels. This phase
records the two identities that order the Sender's **value**, and it does so at
the `Params` layer rather than at any one economy.

The algebra is `Foundations/PatienceDecomposition.lean`, which is stated over an
abstract state type precisely so it can be instantiated here at value functions
living on the feasible-state subtype. What this section adds is the wiring: the
successor is the model's own `p.F` evaluated at a constant action pair, and the
absorbing state needed by the second identity is **derived** from `F_diag`
rather than assumed.

**Generality.** No functional form for `F` is used, so these are general-`F`
statements in the sense of Rule 22 — the affine law is not required and does not
appear. The previous versions of both identities existed only at the
Eaton--Engers `β`-window economy, where the successor was hard-coded
`(x+1)/2`; those are now corollaries.

**Rule 15.** The two Bellman equations are *consumed*, not constructed. Every
statement below is conditional on being handed a pair of value functions that
solve them; existence is a separate question, settled at the callers by the
project's fixed-point machinery. The names say `_of_bellman` to keep that
visible. -/

/-- **The Sender value difference splits into a direct and a feedback term.**

Two Sender value functions solving the stationary Bellman equation along a
**constant** action pair `(a, s)` — the Target at a fixed compliance level, the
Sender at a fixed sanction — against the same stage payoff `p.U_S` and the same
transition `p.F`, but at different discount factors. Then at every feasible
state the value difference is

  `(β₂ − β₁) · V₂(successor)` — the same continuation, revalued at the new
  patience — plus `β₁ · (V₂ − V₁)(successor)` — the movement in the continuation
  itself.

Economically this separates *how much a more patient Sender values the political
state it was already going to reach* from *how much that state's own value has
moved*. Only the second term is feedback.

No functional form for `p.F` is used. -/
theorem senderValue_patience_decomposition_of_bellman
    (a s : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = p.U_S y.val a s + β₁ * V₁ (Sanctions.clipS' (p.F y.val s)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = p.U_S y.val a s + β₂ * V₂ (Sanctions.clipS' (p.F y.val s)))
    (y : ↥(Sanctions.S : Set ℝ)) :
    V₂ y - V₁ y
      = (β₂ - β₁) * V₂ (Sanctions.clipS' (p.F y.val s))
        + β₁ * (V₂ (Sanctions.clipS' (p.F y.val s))
            - V₁ (Sanctions.clipS' (p.F y.val s))) :=
  Sanctions.PatienceDecomposition.difference_decomposition
    (u := fun w : ↥(Sanctions.S : Set ℝ) => p.U_S w.val a s)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val s))
    h₁ h₂ y

/-- The top state is fixed by the closed loop when the sanction is maximal.

`F_diag` — a sanction equal to the state leaves the state unchanged — gives
`F 1 1 = 1` for free, so the absorbing state the amplification identity needs is
**derived from a maintained field**, not assumed. -/
theorem clipS'_top_fixed_of_sanction_one :
    Sanctions.clipS' (p.F 1 1) = (⟨1, by constructor <;> norm_num⟩ :
      ↥(Sanctions.S : Set ℝ)) := by
  apply Subtype.ext
  rw [Sanctions.clipS'_val_eq_of_mem (by rw [p.F_diag 1]; constructor <;> norm_num),
    p.F_diag 1]

/-- **At the lock-in corner the patience response is the direct response
amplified by `1/(1 − β₁)`.**

The feedback term at the top state is the value difference itself, because the
closed loop reproduces that state. Collecting it gives

  `(1 − β₁) · (V₂(1) − V₁(1)) = (β₂ − β₁) · V₂(1)`.

So the full equilibrium response to greater Sender patience at an absorbing
lock-in state exceeds the direct revaluation by the patience resolvent. Stated
without division, so no `β₁ ≠ 1` hypothesis is needed. -/
theorem senderValue_lockin_amplification_of_bellman
    (a : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = p.U_S y.val a 1 + β₁ * V₁ (Sanctions.clipS' (p.F y.val 1)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = p.U_S y.val a 1 + β₂ * V₂ (Sanctions.clipS' (p.F y.val 1))) :
    (1 - β₁) * (V₂ (⟨1, by constructor <;> norm_num⟩ :
          ↥(Sanctions.S : Set ℝ))
        - V₁ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)))
      = (β₂ - β₁) * V₂ (⟨1, by constructor <;> norm_num⟩ :
          ↥(Sanctions.S : Set ℝ)) :=
  Sanctions.PatienceDecomposition.amplification_at_fixedPoint
    (u := fun w : ↥(Sanctions.S : Set ℝ) => p.U_S w.val a 1)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val 1))
    h₁ h₂ (p.clipS'_top_fixed_of_sanction_one)

/-- **The lock-in value is the corner flow capitalised at the discount factor.**

`V(1) = U_S(1,a,1)/(1−β)`. The absorbing state is derived from `F_diag`, so this
needs no functional form for the transition. -/
theorem senderValue_lockin_capitalised_of_bellman
    (a : ℝ) {β : ℝ} {V : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h : ∀ y : ↥(Sanctions.S : Set ℝ),
      V y = p.U_S y.val a 1 + β * V (Sanctions.clipS' (p.F y.val 1)))
    (hβ : β ≠ 1) :
    V (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      = p.U_S 1 a 1 / (1 - β) :=
  Sanctions.PatienceDecomposition.value_at_fixedPoint
    (u := fun w : ↥(Sanctions.S : Set ℝ) => p.U_S w.val a 1)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val 1))
    h (p.clipS'_top_fixed_of_sanction_one) hβ

/-- **More patience deepens lock-in exactly when the corner flow is positive.**

An `iff`, and the direction matters. Greater Sender patience raises the
equilibrium Sender value at the absorbing lock-in state **if and only if** the
Sender's stage payoff there is positive. Where the locked-in regime pays the
Sender a negative flow, patience makes it strictly worse off, and no feature of
the dynamics reverses that. So "patience deepens lock-in" is a statement about
the stage payoff at the corner, not a general property of the mechanism. -/
theorem senderValue_lockin_strict_iff_of_bellman
    (a : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = p.U_S y.val a 1 + β₁ * V₁ (Sanctions.clipS' (p.F y.val 1)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = p.U_S y.val a 1 + β₂ * V₂ (Sanctions.clipS' (p.F y.val 1)))
    (hβ₁ : β₁ < 1) (hlt : β₁ < β₂) (hβ₂ : β₂ < 1) :
    V₁ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
        < V₂ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      ↔ 0 < p.U_S 1 a 1 :=
  Sanctions.PatienceDecomposition.strict_at_fixedPoint_iff
    (u := fun w : ↥(Sanctions.S : Set ℝ) => p.U_S w.val a 1)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val 1))
    h₁ h₂ (p.clipS'_top_fixed_of_sanction_one) hβ₁ hlt hβ₂

end Params

end AbstractGame

end

end Sanctions
