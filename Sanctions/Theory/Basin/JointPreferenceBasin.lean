/-
Sanctions/Theory/Basin/JointPreferenceBasin.lean

**Joint sanction-preference basin layer for the abstract game.**

A *joint sanction-preference basin* is a region `[xbar, 1]` of the
state space together with a sanction floor `sbar` where:

1. The Sender's forward-looking dynamic argmax contains some element
   `≥ max(x, sbar)` at every basin state — equivalently, the upper
   dynamic selector `σ_dyn_top` inherits the level condition
   `max x sbar ≤ σ_dyn_top V_S x (α x)`.
2. The Target prefers sanctions in the basin — the forward-looking
   Target payoff `U_T(x, α(x), s) + β_T · V_T(F(x, s))` is monotone
   non-decreasing in `s` on `[max(x, sbar), 1]`.
3. The Target policy `α` is Bellman-optimal against the **upper** dynamic
   Sender response on the basin (equilibrium-derived).

This basin formalization is the bridge between the kinematic lock-in
machinery (`DynamicTopLockIn`) and a clean equilibrium statement: when
both players prefer sanctions in the basin and the Target is
Bellman-optimal there, the upper dynamic equilibrium selector keeps the
state in the basin and the sanction sequence is non-decreasing.

## Rule compliance

**Rule 1.** The Sender side uses the upper dynamic argmax `σ_dyn_top`
(equilibrium-derived: `σ_dyn_top ∈ dynamicArgmaxSet` is a forward-
looking Sender maximizer). The Target side has explicit
Bellman-optimality of `α` against `joint_T_top_integrand`.

**Rule 3.** `JointPreferenceBasinTop` bundles theorem-parameter
hypotheses as a *structure* parameter for downstream theorems; it is
not a Postulate field and not a `Params` field. Every clause is
derivable from canonical primitives at any concrete instantiation —
the `sender_high_argmax_exists_of_strictMono_below_threshold`
discharger below provides one such derivation route (order-language
version of "positive marginal sanction benefit").

**Rule 5.** Fully parametric over `(p, V_T, V_S, α, xbar, sbar)`.
-/

import Sanctions.Theory.LockIn.DynamicTopLockIn
import Sanctions.Theory.LockIn.MyopicComparator
import Sanctions.Theory.LockIn.RulePathF
import Sanctions.Foundations.MilgromShannon
import Sanctions.Foundations.IntervalDominanceOrder

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Sender / Target objectives as functions of the sanction level -/

/-- Sender's forward-looking objective as a function of the sanction
level `s`. Equivalent to the body of the dynamic Sender argmax
problem in `JointMPE.σ_dyn`. -/
def senderDynObjective
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a s : ℝ) : ℝ :=
  p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))

/-- Target's forward-looking payoff if sanction `s` is treated as the
realized sanction (i.e. as a function of `s` rather than the actual
`σ_dyn_top V_S x a`). Used to state the order-language form of
"Target prefers sanctions" on the high range. -/
def targetSanctionObjective
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a s : ℝ) : ℝ :=
  p.U_T x a s + p.β_T * V_T (Sanctions.clipS' (p.F x s))

/-- **Exact Sender continuation-reversal threshold.** The dynamic Sender
objective ranks a higher comparison sanction `sH` above a lower comparison
sanction `sL` exactly when the discounted continuation-value gain exceeds the
associated stage-payoff loss. No monotonicity or functional-form assumption is
used: this is the algebraic decomposition of `senderDynObjective`. -/
theorem senderDynObjective_lt_iff_continuation_gain_gt_stage_loss
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a sL sH : ℝ) :
    p.senderDynObjective V_S x a sL < p.senderDynObjective V_S x a sH ↔
      p.U_S x a sL - p.U_S x a sH <
        p.β_S * (V_S (Sanctions.clipS' (p.F x sH)) -
          V_S (Sanctions.clipS' (p.F x sL))) := by
  unfold senderDynObjective
  constructor <;> intro h <;> linarith

/-- **Exact Target continuation-reversal threshold.** The Target's complete
sanction objective ranks `sH` above `sL` exactly when its discounted
continuation-value gain exceeds the stage-payoff loss from that comparison.
This is an assumption-free algebraic identity for `targetSanctionObjective`. -/
theorem targetSanctionObjective_lt_iff_continuation_gain_gt_stage_loss
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a sL sH : ℝ) :
    p.targetSanctionObjective V_T x a sL < p.targetSanctionObjective V_T x a sH ↔
      p.U_T x a sL - p.U_T x a sH <
        p.β_T * (V_T (Sanctions.clipS' (p.F x sH)) -
          V_T (Sanctions.clipS' (p.F x sL))) := by
  unfold targetSanctionObjective
  constructor <;> intro h <;> linarith

/-- Target Bellman integrand using the upper dynamic Sender equilibrium
selector `σ_dyn_top`. -/
noncomputable def joint_T_top_integrand
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  let s := p.σ_dyn_top V_S x a
  p.U_T x a s + p.β_T * V_T (Sanctions.clipS' (p.F x s))

/-! ## Bridge: stage sanction preference ⇒ dynamic sanction preference

The paper's economic primitive is stage-level: `∂U_S/∂s > 0` (Sender
likes more sanctions) and `∂U_T/∂s > 0` (Target likes more sanctions)
on the relevant interval. Lean's `senderDynObjective` and
`targetSanctionObjective` are forward-looking: they include the
discounted continuation term. The bridges below show that stage
monotonicity + monotone continuation value implies dynamic
monotonicity, so the paper's stage primitives suffice (no
forward-looking continuation derivative needed). -/

/-- **Bridge (Sender).** If the stage Sender payoff
`U_S(x, α(x), ·)` is strictly monotone non-decreasing in `s` on
`[0, max x sbar]` and the Sender continuation value `V_S` is monotone
non-decreasing, then the forward-looking Sender objective
`senderDynObjective V_S x (α x)` is strictly monotone non-decreasing
in `s` on the same interval.

The proof is the standard "strict + monotone = strict" sum: the stage
term is strict-mono by hypothesis; the continuation term
`β_S · V_S(F(x, s))` is monotone non-decreasing because `β_S ≥ 0`,
the transition `F(x, ·)` is monotone (since `δ > 0`), and `V_S` is
monotone on `↥S`. -/
theorem senderDynObjective_strictMono_of_stage_strictMono_and_V_mono
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (h_V_S_mono : Monotone V_S)
    {α : ℝ → ℝ} {x sbar : ℝ}
    (h_stage_strict :
      StrictMonoOn (fun s => p.U_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))) :
    StrictMonoOn (fun s => p.senderDynObjective V_S x (α x) s)
                 (Set.Icc (0 : ℝ) (max x sbar)) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  change p.U_S x (α x) s₁ + p.β_S * V_S
          (Sanctions.clipS' (p.F x s₁))
          < p.U_S x (α x) s₂ + p.β_S * V_S
          (Sanctions.clipS' (p.F x s₂))
  have h_stage_lt : p.U_S x (α x) s₁ < p.U_S x (α x) s₂ :=
    h_stage_strict hs₁ hs₂ hlt
  have h_F_le : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hlt.le
  have h_clip_le : Sanctions.clipS' (p.F x s₁)
                    ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono h_F_le
  have h_V_le := h_V_S_mono h_clip_le
  have hβ_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have h_βV_le := mul_le_mul_of_nonneg_left h_V_le hβ_nn
  linarith

/-- **Bridge (Target).** If the stage Target payoff
`U_T(x, α(x), ·)` is monotone non-decreasing in `s` on
`[max x sbar, 1]` and the Target continuation value `V_T` is monotone
non-decreasing, then the forward-looking Target sanction payoff
`targetSanctionObjective V_T x (α x)` is monotone non-decreasing in
`s` on the same interval. -/
theorem targetSanctionObjective_mono_of_stage_mono_and_V_mono
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} (h_V_T_mono : Monotone V_T)
    {α : ℝ → ℝ} {x sbar : ℝ}
    (h_stage_mono :
      MonotoneOn (fun s => p.U_T x (α x) s)
        (Set.Icc (max x sbar) 1)) :
    MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
               (Set.Icc (max x sbar) 1) := by
  intro s₁ hs₁ s₂ hs₂ hle
  change p.U_T x (α x) s₁ + p.β_T * V_T
          (Sanctions.clipS' (p.F x s₁))
          ≤ p.U_T x (α x) s₂ + p.β_T * V_T
          (Sanctions.clipS' (p.F x s₂))
  have h_stage_le := h_stage_mono hs₁ hs₂ hle
  have h_F_le : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hle
  have h_clip_le := Sanctions.clipS'_mono h_F_le
  have h_V_le := h_V_T_mono h_clip_le
  have hβ_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_βV_le := mul_le_mul_of_nonneg_left h_V_le hβ_nn
  linarith

/-! ## The joint preference basin (upper selector)

A Prop-valued structure bundling the basin's structural hypotheses,
introduced at theorem-parameter level (not as a `Params` field, not as
a `Postulates` Prop). -/

/-- **Joint sanction-preference basin under the upper dynamic selector.**
Predicate on `(V_T, V_S, α, xbar, sbar)` capturing:

1. Basin geometry (`xbar_nonneg`, `xbar_le_one`, `sbar_mem`).
2. `sender_high_argmax_exists`: at every basin state, some dynamic
   Sender maximizer is at least `max(x, sbar)` — this lifts to
   `σ_dyn_top ≥ max(x, sbar)` via the upper-selector definition.
3. `top_rule_mono`: the upper-selector realized rule is monotone on
   the basin (Topkis-style monotone comparative statics).
4. `target_prefers_sanctions`: the Target's forward-looking sanction
   payoff is non-decreasing in `s` on `[max(x, sbar), 1]` — the order
   form of `∂U_T/∂s + β_T · V_T ∘ F ≥ 0` on the high range.
5. `target_policy_optimal`: `α` is Bellman-optimal against the upper
   dynamic Sender response.

**Nondegeneracy note (audit-26 #6).** The `xbar < 1` (strict
nondegeneracy) condition is *not* a field of this structure: Goal 1
(long-run persistence from a state already inside the basin) does
not require it. Only `jointPreferenceBasinTop_temporary_shock_permanent_high`
and its public-wrapper relatives take `xbar < 1` as an explicit
hypothesis (needed so the shock path actually enters `[xbar, 1]` in
finite time). -/
structure JointPreferenceBasinTop
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xbar sbar : ℝ) : Prop where
  xbar_nonneg : 0 ≤ xbar
  /-- Audit-27 cleanup: `xbar ≤ 1` rules out vacuous basin structures
  with `xbar > 1` (theorems are then trivially uncallable but the
  structure itself was less clean). Strict nondegeneracy `xbar < 1`
  remains an explicit per-theorem hypothesis on the shock-entry
  theorems only. -/
  xbar_le_one : xbar ≤ 1
  sbar_mem : sbar ∈ Sanctions.I

  /-- Target policy is feasible on the basin: `α x ∈ [0, 1]` for every
  basin state. (Required for `target_policy_optimal` below to certify
  `α x` as a constrained-feasible maximizer rather than an unconstrained
  upper bound on the integrand image.) -/
  target_policy_feasible :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), α x ∈ Sanctions.I

  /-- Existence-level Sender condition: at every basin state, there is
  a high-sanction dynamic Sender maximizer. The top selector picks at
  least this high. -/
  sender_high_argmax_exists :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s ∧
        max x sbar ≤ s

  /-- Topkis / monotone-comparative-statics property for the upper
  dynamic equilibrium response. -/
  top_rule_mono :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1)

  /-- Target's forward-looking sanction preference on the high basin. -/
  target_prefers_sanctions :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
        (Set.Icc (max x sbar) 1)

  /-- Target policy is Bellman-optimal against the upper dynamic Sender
  selector. This is the Rule-1 (optimal-strategies-only) discharge on
  the Target side. -/
  target_policy_optimal :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a) Sanctions.I (α x)

/-! ## Bridge: basin existence ⇒ upper-selector level condition

This is the load-bearing bridge from the basin Prop to the kinematic
level condition consumed by `DynamicTopLockIn`. -/

/-- **A high Sender maximiser lifts the greatest one** (general in `F`: the
transition enters only through the Sender's objective). If at every basin
state some maximiser of the Sender's forward-looking objective is at least
`max x sbar`, then so is the upper selector `σ_dyn_top`, the greatest
maximiser, so the realised rule satisfies the level condition.

This is the body of `JointPreferenceBasinTop.level_dyn_top` stated on the one
basin field it reads, `sender_high_argmax_exists`. The other seven fields of
the joint basin, among them the interval-dominance direction input (A1,
`top_rule_mono`) and the Target's sanction preference (P4), are not used
(BH2.1, 2026-10-06). -/
theorem level_dyn_top_of_high_argmax
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (h_high : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s ∧
        max x sbar ≤ s) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  obtain ⟨s, hsI, hsMax, hsHigh⟩ := h_high x hx
  have hsSet : s ∈ p.dynamicArgmaxSet V_S x (α x) := by
    refine ⟨hsI, ?_⟩
    intro s' hs'
    have h := hsMax hs'
    -- senderDynObjective unfolds definitionally to the dynamicArgmaxSet body
    exact h
  unfold dynamicTopRealizedRule σ_dyn_top
  exact le_trans hsHigh (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x (α x)) hsSet)

/-- **Basin ⇒ upper-selector level condition.** If there is a high
Sender maximizer in the basin, the upper dynamic selector inherits the
level inequality `max x sbar ≤ σ_dyn_top V_S x (α x)`. Since BH2.1
(2026-10-06) a one-line corollary of `level_dyn_top_of_high_argmax`, which
reads only the `sender_high_argmax_exists` field; statement unchanged. -/
theorem JointPreferenceBasinTop.level_dyn_top
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x :=
  p.level_dyn_top_of_high_argmax hB.sender_high_argmax_exists

/-- **Basin ⇒ ratchet.** The joint basin puts the realised rule weakly above
the state on `[xbar, 1]` (general in `F`; the `le_max_left` half of the level
condition). This is the only consequence of the basin that the post-entry
floor and no-relief theorems consume (BH2.1, 2026-10-06). -/
theorem JointPreferenceBasinTop.ratchet_dyn_top
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule V_S α x :=
  fun x hx => le_trans (le_max_left x sbar) (JointPreferenceBasinTop.level_dyn_top p hB x hx)

/-! ## Discharger: `sender_high_argmax_exists` from strict monotonicity below threshold -/

/-- **Sender high-argmax exists from strict monotonicity below threshold.**
If the Sender's forward-looking objective is strictly increasing in
`s` on `[0, max(x, sbar)]` for each basin state `x`, then any
maximizer of the objective on `[0, 1]` lies at or above `max(x, sbar)`.

This is the order-language version of the paper's "positive marginal
sanction benefit" (`U_{S,s} > 0`, with monotone continuation). -/
theorem sender_high_argmax_exists_of_strictMono_below_threshold
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hxbar_nonneg : 0 ≤ xbar)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_strict : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      StrictMonoOn (fun s => p.senderDynObjective V_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s ∧
        max x sbar ≤ s := by
  intro x hx
  -- Get any dynamic argmax from sender_arg_max_exists.
  obtain ⟨s, hsI, hsMax⟩ := p.sender_arg_max_exists V_S x (α x)
  refine ⟨s, hsI, ?_, ?_⟩
  · -- Re-package as IsMaxOn for senderDynObjective (def-equal).
    intro s' hs'
    exact hsMax hs'
  · -- The maximizer must be ≥ max(x, sbar) by strict monotonicity below threshold.
    by_contra hnot
    have hs_lt : s < max x sbar := not_le.mp hnot
    have hthreshold_mem : max x sbar ∈ Sanctions.I := by
      refine ⟨?_, max_le hx.2 hsbar_mem.2⟩
      exact le_max_of_le_left (le_trans hxbar_nonneg hx.1)
    have hs_low : s ∈ Set.Icc (0 : ℝ) (max x sbar) :=
      ⟨hsI.1, le_of_lt hs_lt⟩
    have ht_low : max x sbar ∈ Set.Icc (0 : ℝ) (max x sbar) :=
      ⟨hthreshold_mem.1, le_refl _⟩
    have hlt :
        p.senderDynObjective V_S x (α x) s
          < p.senderDynObjective V_S x (α x) (max x sbar) :=
      h_strict x hx hs_low ht_low hs_lt
    have hmax :
        p.senderDynObjective V_S x (α x) (max x sbar)
          ≤ p.senderDynObjective V_S x (α x) s := hsMax hthreshold_mem
    linarith

/-- **The high argmax from the pivot beating every sub-pivot sanction** (round M,
doc 82 P3): if at each basin state the forward-looking objective at the pivot
`max x sbar` strictly exceeds its value at every sanction below the pivot, some
maximiser lies at or above the pivot. Weaker than strict monotonicity below the
pivot, which compares every pair of sanctions. -/
theorem sender_high_argmax_exists_of_pivot_beats_subpivot
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hxbar_nonneg : 0 ≤ xbar)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_star : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s ∈ Set.Ico (0 : ℝ) (max x sbar),
      p.senderDynObjective V_S x (α x) s
        < p.senderDynObjective V_S x (α x) (max x sbar)) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s ∧
        max x sbar ≤ s := by
  intro x hx
  obtain ⟨s, hsI, hsMax⟩ := p.sender_arg_max_exists V_S x (α x)
  refine ⟨s, hsI, ?_, ?_⟩
  · intro s' hs'
    exact hsMax hs'
  · by_contra hnot
    have hs_lt : s < max x sbar := not_le.mp hnot
    have hthreshold_mem : max x sbar ∈ Sanctions.I := by
      refine ⟨?_, max_le hx.2 hsbar_mem.2⟩
      exact le_max_of_le_left (le_trans hxbar_nonneg hx.1)
    have hlt := h_star x hx s ⟨hsI.1, hs_lt⟩
    have hmax :
        p.senderDynObjective V_S x (α x) (max x sbar)
          ≤ p.senderDynObjective V_S x (α x) s := hsMax hthreshold_mem
    linarith

/-! ## Discharger: top-rule monotonicity from Milgrom-Shannon single crossing

If the Sender's dynamic objective (as a function of choice `s` and
parameter `x`, with `α` already substituted) satisfies the scalar
Milgrom-Shannon single-crossing property
(`Foundations.MilgromShannon.SingleCrossing`), then
`dynamicTopRealizedRule V_S α` is monotone non-decreasing on `[xbar, 1]`.
This discharges the load-bearing `top_rule_mono` hypothesis of
`JointPreferenceBasinTop` from the canonical Milgrom-Shannon primitive,
reducing the strength of the basin Prop. -/

/-- **Top-rule monotonicity from localized single crossing
(Milgrom-Shannon, audit-28 #1).** Strictly weaker than
`dynamicTopRealizedRule_mono_of_singleCrossing` below — only requires SC
on the feasible choice set `Sanctions.I` and the basin parameter set
`Set.Icc xbar 1`. -/
theorem dynamicTopRealizedRule_mono_of_singleCrossingOn
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar : ℝ}
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc xbar 1)
            (fun s x => p.senderDynObjective V_S x (α x) s)) :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1) := by
  intro x₁ hx₁ x₂ hx₂ hle
  set s₁ := p.σ_dyn_top V_S x₁ (α x₁) with hs₁_def
  set s₂ := p.σ_dyn_top V_S x₂ (α x₂) with hs₂_def
  have hs₁_mem : s₁ ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x₁ (α x₁)
  have hs₂_mem : s₂ ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x₂ (α x₂)
  have hs₁_max : ∀ y ∈ Sanctions.I,
      p.senderDynObjective V_S x₁ (α x₁) y
        ≤ p.senderDynObjective V_S x₁ (α x₁) s₁ := by
    intro y hy; exact p.σ_dyn_top_isMaxOn V_S x₁ (α x₁) hy
  have hs₂_max : ∀ y ∈ Sanctions.I,
      p.senderDynObjective V_S x₂ (α x₂) y
        ≤ p.senderDynObjective V_S x₂ (α x₂) s₂ := by
    intro y hy; exact p.σ_dyn_top_isMaxOn V_S x₂ (α x₂) hy
  -- Apply localized Milgrom-Shannon: `max(s₁, s₂)` is an `x₂`-maximizer.
  obtain ⟨_, hmax_max⟩ :=
    Sanctions.MilgromShannon.monotone_argmax_of_singleCrossingOn hSC hle
      hx₁ hx₂ hs₁_mem hs₂_mem hs₁_max hs₂_max
  have hmax_mem : max s₁ s₂ ∈ Sanctions.I :=
    Sanctions.max_mem_I hs₁_mem hs₂_mem
  have hmax_in_set : max s₁ s₂ ∈ p.dynamicArgmaxSet V_S x₂ (α x₂) := by
    refine ⟨hmax_mem, ?_⟩
    intro y hy
    exact hmax_max y hy
  have h_max_le_s₂ : max s₁ s₂ ≤ s₂ := by
    rw [hs₂_def]
    unfold Params.σ_dyn_top
    exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S x₂ (α x₂)) hmax_in_set
  calc p.dynamicTopRealizedRule V_S α x₁
      = s₁ := rfl
    _ ≤ max s₁ s₂ := le_max_left _ _
    _ ≤ s₂ := h_max_le_s₂
    _ = p.dynamicTopRealizedRule V_S α x₂ := rfl

/-- **Top-rule monotonicity from the Interval Dominance Order (B1).**
Sibling of `dynamicTopRealizedRule_mono_of_singleCrossingOn` consuming the
strictly-weaker `IDOFamilyOn` of the Sender dynamic objective instead of
Milgrom–Shannon single crossing. Same conclusion (the realised top rule is
monotone on the basin), routed through the assumption-free
`IntervalDominanceOrder.monotone_argmax_of_IDOFamilyOn` (Quah–Strulovici
Prop 5 / Thm 1): IDO ⇒ the upper argmax selection does not fall as the
state rises. Single crossing is the special case via
`IDOFamilyOn.of_singleCrossingOn`, so this is a strict generalisation of
the route — usable wherever IDO of the objective can be discharged
(e.g. the non-strong-rally basin-combined-monotonicity regime). -/
theorem dynamicTopRealizedRule_mono_of_IDOFamilyOn
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar : ℝ}
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
            Sanctions.I (Set.Icc xbar 1)
            (fun s x => p.senderDynObjective V_S x (α x) s)) :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1) := by
  intro x₁ hx₁ x₂ hx₂ hle
  set s₁ := p.σ_dyn_top V_S x₁ (α x₁) with hs₁_def
  set s₂ := p.σ_dyn_top V_S x₂ (α x₂) with hs₂_def
  have hs₁_mem : s₁ ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x₁ (α x₁)
  have hs₂_mem : s₂ ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x₂ (α x₂)
  have hs₁_max : IsMaxOn (fun s => p.senderDynObjective V_S x₁ (α x₁) s)
      Sanctions.I s₁ := fun y hy => p.σ_dyn_top_isMaxOn V_S x₁ (α x₁) hy
  have hs₂_max : IsMaxOn (fun s => p.senderDynObjective V_S x₂ (α x₂) s)
      Sanctions.I s₂ := fun y hy => p.σ_dyn_top_isMaxOn V_S x₂ (α x₂) hy
  -- IDO ⇒ monotone argmax: `max s₁ s₂` is an `x₂`-maximizer.
  have hmax_max := Sanctions.IntervalDominanceOrder.monotone_argmax_of_IDOFamilyOn
    (convex_Icc (0 : ℝ) 1) hIDO hx₁ hx₂ hle hs₁_mem hs₂_mem hs₁_max hs₂_max
  have hmax_mem : max s₁ s₂ ∈ Sanctions.I := Sanctions.max_mem_I hs₁_mem hs₂_mem
  have hmax_in_set : max s₁ s₂ ∈ p.dynamicArgmaxSet V_S x₂ (α x₂) :=
    ⟨hmax_mem, fun y hy => hmax_max hy⟩
  have h_max_le_s₂ : max s₁ s₂ ≤ s₂ := by
    rw [hs₂_def]
    unfold Params.σ_dyn_top
    exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S x₂ (α x₂)) hmax_in_set
  calc p.dynamicTopRealizedRule V_S α x₁
      = s₁ := rfl
    _ ≤ max s₁ s₂ := le_max_left _ _
    _ ≤ s₂ := h_max_le_s₂
    _ = p.dynamicTopRealizedRule V_S α x₂ := rfl

/-- **Top-rule monotonicity from (global) single crossing
(Milgrom-Shannon).** Kept for callers that have the global form
`SingleCrossing` available; reduces to the localized form via
`SingleCrossing.toSingleCrossingOn`. The localized version is the
load-bearing one (audit-28 #1). -/
theorem dynamicTopRealizedRule_mono_of_singleCrossing
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar : ℝ}
    (hSC : Sanctions.MilgromShannon.SingleCrossing
            (fun s x => p.senderDynObjective V_S x (α x) s)) :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1) :=
  p.dynamicTopRealizedRule_mono_of_singleCrossingOn
    (hSC.toSingleCrossingOn Sanctions.I (Set.Icc xbar 1))

/-- Order-language version of "Target prefers sanctions on the high
basin" — `U_T + β_T · V_T ∘ F` non-decreasing in `s` on
`[max(x, sbar), 1]`. -/
def TargetLikesSanctionsOnBasin
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xbar sbar : ℝ) : Prop :=
  ∀ x ∈ Set.Icc xbar (1 : ℝ),
    MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
      (Set.Icc (max x sbar) 1)

/-! ## One-sided sanction-preference thresholds (Sections 5.1, Assumptions 1+2)

A more primitive abstraction than the joint preference basin Prop:
two independent, *one-sided* thresholds — `xT` (Target sanction
preference threshold) and `xS` (Sender sanction preference
threshold) — capturing the paper's
`prop:jointPref_nonempty` derivation of the joint region as the
intersection of two upper intervals.

This layer formalizes the paper's headline factoring:

> the one-sided primitives imply a nonempty joint sanction-preference
> region; persistence follows after combining the joint region with
> the (separately discharged) level condition that the dynamic
> Sender's selected best response is high enough on that region. -/

/-- **One-sided sanction-preference thresholds.** Prop bundle on
`(V_T, V_S, α, xT, xS, sbar)`:

* `xT, xS, sbar ∈ [0, 1]`.
* `sender_likes_to_threshold`: at every state in the *Sender* upper
  interval `[xS, 1]`, the Sender's forward-looking objective is
  strictly increasing in `s` up to the high threshold
  `max(x, sbar)` — order-language version of `U_{S,s}^{\rm dyn} > 0`
  below the threshold.
* `target_likes_high_sanctions`: at every state in the *Target* upper
  interval `[xT, 1]`, the Target's forward-looking sanction payoff is
  monotone non-decreasing in `s` on `[max(x, sbar), 1]` —
  order-language version of `U_{T,s}^{\rm dyn} \geq 0` on the high
  range.

The joint region is the intersection `[max(xT, xS), 1]` (always
non-empty since it contains `1`). -/
structure OneSidedSanctionPreferenceThresholds
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xT xS sbar : ℝ) : Prop where
  xT_mem : xT ∈ Sanctions.I
  xS_mem : xS ∈ Sanctions.I
  sbar_mem : sbar ∈ Sanctions.I

  /-- Sender forward-looking objective is strictly increasing in `s`
  below the high threshold, on the Sender upper interval `[xS, 1]`. -/
  sender_likes_to_threshold :
    ∀ x ∈ Set.Icc xS (1 : ℝ),
      StrictMonoOn (fun s => p.senderDynObjective V_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))

  /-- Target's forward-looking sanction payoff is monotone in `s`
  on the high range `[max(x, sbar), 1]`, at every state in the
  Target upper interval `[xT, 1]`. -/
  target_likes_high_sanctions :
    ∀ x ∈ Set.Icc xT (1 : ℝ),
      MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
        (Set.Icc (max x sbar) 1)

/-- **Bridge constructor: one-sided thresholds from stage preferences.**
Builds `OneSidedSanctionPreferenceThresholds` from the paper's stage-
level economic primitives (`∂U_S/∂s > 0` and `∂U_T/∂s ≥ 0` on the
relevant intervals, expressed as order-language strict/weak
monotonicity) plus monotone continuation values `V_S, V_T` — using
the bridges `senderDynObjective_strictMono_of_stage_strictMono_and_V_mono`
and `targetSanctionObjective_mono_of_stage_mono_and_V_mono` to lift
stage preferences to the forward-looking objectives. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_preferences
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_T_mono : Monotone V_T) (h_V_S_mono : Monotone V_S)
    {α : ℝ → ℝ} {xT xS sbar : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (α x) s)
          (Set.Icc (max x sbar) 1)) :
    p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar where
  xT_mem := hxT_mem
  xS_mem := hxS_mem
  sbar_mem := hsbar_mem
  sender_likes_to_threshold := fun x hx =>
    p.senderDynObjective_strictMono_of_stage_strictMono_and_V_mono
      h_V_S_mono (h_stage_sender x hx)
  target_likes_high_sanctions := fun x hx =>
    p.targetSanctionObjective_mono_of_stage_mono_and_V_mono
      h_V_T_mono (h_stage_target x hx)

/-- **R45 follow-up: alternative one-sided thresholds constructor from
    the combined chord on the Target side.**

    The Target-side input is the **per-equilibrium combined chord**
    inequality on the joint Target dynamic objective at the
    equilibrium Target action:

    ```
    U_T(x, α(x), s_1) + β_T · V_T(F(x, s_1))
      ≤ U_T(x, α(x), s_2) + β_T · V_T(F(x, s_2))
    ```

    for every basin `x ∈ [xT, 1]` and chord `s_1 ≤ s_2 ∈ [max(x, sbar), 1]`.

    This is **logically equivalent** to the `target_likes_high_sanctions`
    field of `OneSidedSanctionPreferenceThresholds` (since
    `targetSanctionObjective V_T x a s := U_T(x, a, s) + β_T · V_T(F(x, s))`),
    so the constructor proof is one `unfold` plus the assumption.

    The Sender-side input is the existing
    `senderDynObjective_strictMono_of_stage_strictMono_and_V_mono`
    bridge: stage-level Sender strict-monotone + monotone `V_S`. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_S_mono : Monotone V_S)
    {α : ℝ → ℝ} {xT xS sbar : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_target_combined :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        ∀ s₁ ∈ Set.Icc (max x sbar) (1 : ℝ),
        ∀ s₂ ∈ Set.Icc (max x sbar) (1 : ℝ),
        s₁ ≤ s₂ →
          p.U_T x (α x) s₁
              + p.β_T * V_T
                  (Sanctions.clipS' (p.F x s₁))
            ≤ p.U_T x (α x) s₂
              + p.β_T * V_T
                  (Sanctions.clipS' (p.F x s₂))) :
    p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar where
  xT_mem := hxT_mem
  xS_mem := hxS_mem
  sbar_mem := hsbar_mem
  sender_likes_to_threshold := fun x hx =>
    p.senderDynObjective_strictMono_of_stage_strictMono_and_V_mono
      h_V_S_mono (h_stage_sender x hx)
  target_likes_high_sanctions := by
    intro x hx s₁ hs₁ s₂ hs₂ hs_le
    unfold Sanctions.AbstractGame.Params.targetSanctionObjective
    exact h_target_combined x hx s₁ hs₁ s₂ hs₂ hs_le

/-! ## Bridge: one-sided thresholds ⇒ joint preference basin

The bridge consumes one-sided thresholds plus three auxiliary
hypotheses --- Target policy feasibility on the basin
(`hα_feas`), Topkis monotonicity of the upper-selector rule
(`hTopMono`; itself dischargeable from MS single crossing via
`dynamicTopRealizedRule_mono_of_singleCrossing`), and Target Bellman
optimality (`hα_opt`) --- to produce a `JointPreferenceBasinTop` on
the joint region `[max(xT, xS), 1]`. -/

/-- **Bridge: one-sided thresholds ⇒ `JointPreferenceBasinTop`.**

(Audit-27 cleanup: the prior `_hjoint_lt : max xT xS < 1` parameter
has been removed — it was unused. Strict nondegeneracy
`max xT xS < 1` is needed only for finite shock entry and is now
threaded directly into the shock theorems via `hxbar_lt_one`.) -/
theorem JointPreferenceBasinTop.of_oneSidedThresholds
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT xS sbar : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar)
    (hα_feas : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x ∈ Sanctions.I)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (max xT xS) 1))
    (hα_opt :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                Sanctions.I (α x)) :
    p.JointPreferenceBasinTop V_T V_S α (max xT xS) sbar where
  xbar_nonneg := le_max_of_le_left hOne.xT_mem.1
  xbar_le_one := max_le hOne.xT_mem.2 hOne.xS_mem.2
  sbar_mem := hOne.sbar_mem
  target_policy_feasible := hα_feas
  sender_high_argmax_exists := by
    -- Apply the existing discharger with basin = max xT xS.
    refine p.sender_high_argmax_exists_of_strictMono_below_threshold
      (le_max_of_le_left hOne.xT_mem.1)
      hOne.sbar_mem ?_
    intro x' hx'
    -- [max xT xS, 1] ⊆ [xS, 1] so the Sender hypothesis applies.
    exact hOne.sender_likes_to_threshold x'
      ⟨le_trans (le_max_right _ _) hx'.1, hx'.2⟩
  top_rule_mono := hTopMono
  target_prefers_sanctions := by
    intro x hx
    -- [max xT xS, 1] ⊆ [xT, 1] so the Target hypothesis applies.
    exact hOne.target_likes_high_sanctions x
      ⟨le_trans (le_max_left _ _) hx.1, hx.2⟩
  target_policy_optimal := hα_opt

/-! ## Goal 1: long-run non-decreasing high sanctions from the basin -/

/-- **Goal 1.** From any starting state in the basin, the upper-dynamic
state path stays in the basin, the sanction sequence is bounded below
by `sbar`, bounded below by the basin pivot `xbar`, and non-decreasing.
The `xbar`-floor identifies "high" with the basin pivot independently of
`sbar`'s sign (cf.~`dynamicTopLockInSanctions_ge_xbar`). -/
theorem jointPreferenceBasinTop_long_run_nonDecreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions V_S α x₀) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  exact ⟨
    p.dynamicTopLockInPath_mem_basin V_S α hlevel hx₀,
    p.dynamicTopLockInSanctions_floor V_S α hlevel hx₀,
    p.dynamicTopLockInSanctions_ge_xbar V_S α hlevel hx₀,
    p.dynamicTopLockInSanctions_mono V_S α hlevel hB.top_rule_mono hx₀⟩

/-- **Goal 1 over the general transition `F` (Option B).** Identical
conclusion to `jointPreferenceBasinTop_long_run_nonDecreasing`, but the
realized state path is evolved by the abstract transition `p.F`
(`dynamicTopLockInPathF`) rather than the affine law. Same basin data
`hB`; no new assumption — the `F`-path lemmas consume only `F_mono_s` /
`F_diag` / `F_mem_uIcc` (the last for the upper basin edge, on all of `ℝ`,
so `hB.xbar_nonneg` is no longer read here; BG2.1). -/
theorem jointPreferenceBasinTopF_long_run_nonDecreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  exact ⟨
    p.dynamicTopLockInPathF_mem_basin V_S α hlevel hx₀,
    p.dynamicTopLockInSanctionsF_floor V_S α hlevel hx₀,
    p.dynamicTopLockInSanctionsF_ge_xbar V_S α hlevel hx₀,
    p.dynamicTopLockInSanctionsF_mono V_S α hlevel
      hB.top_rule_mono hx₀⟩

/-- **Goal 1 with equilibrium evidence along the path.** Extends
`jointPreferenceBasinTop_long_run_nonDecreasing` with conjunctive
equilibrium-evidence conclusions: along the entire upper-dynamic path,

1. The Target policy `α` is feasible (`α x_n ∈ I`).
2. The Target policy `α` is Bellman-optimal against the joint top
   integrand at each state `x_n` (so `α` is a Stackelberg-leader
   best response along the path, not just an arbitrary function).
3. The realized sanction `σ_dyn_top V_S x_n (α x_n)` is a Sender
   dynamic maximizer at each state `x_n` (so the Sender is
   forward-looking optimizing along the path, by definition of the
   upper selector — it is the supremum of the dynamic argmax set).
4. **Target weakly prefers sanctions** at each path state — the
   forward-looking Target objective `s ↦ U_T + β_T·V_T(F(x_n, s))`
   is monotone non-decreasing in `s` on `[max(x_n, sbar), 1]`
   (audit-28 #4). This is the path-level reading of the basin's
   `target_prefers_sanctions` field.

Combined with the kinematic conclusions inherited from Goal 1
(basin invariance, sanction floor, sanction monotonicity), this
makes the headline "two forward-looking individuals reach a
permanent-high-sanction trajectory" Lean-cited rather than merely
asserted. -/
theorem jointPreferenceBasinTop_long_run_with_equilibrium_evidence
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions V_S α x₀) ∧
    (∀ n, α (p.dynamicTopLockInPath V_S α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S
                              (p.dynamicTopLockInPath V_S α x₀ n) a)
              Sanctions.I (α (p.dynamicTopLockInPath V_S α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective V_S
                              (p.dynamicTopLockInPath V_S α x₀ n)
                              (α (p.dynamicTopLockInPath V_S α x₀ n)) s')
              Sanctions.I (p.dynamicTopLockInSanctions V_S α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective V_T
        (p.dynamicTopLockInPath V_S α x₀ n)
        (α (p.dynamicTopLockInPath V_S α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath V_S α x₀ n) sbar) 1)) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  have h_path := p.dynamicTopLockInPath_mem_basin V_S α hlevel hx₀
  refine ⟨h_path,
          p.dynamicTopLockInSanctions_floor V_S α hlevel hx₀,
          p.dynamicTopLockInSanctions_ge_xbar V_S α hlevel hx₀,
          p.dynamicTopLockInSanctions_mono V_S α hlevel hB.top_rule_mono hx₀,
          ?_, ?_, ?_, ?_⟩
  · intro n; exact hB.target_policy_feasible _ (h_path n)
  · intro n; exact hB.target_policy_optimal _ (h_path n)
  · -- σ_dyn_top is the supremum of the argmax set, in particular it IS
    -- a dynamic Sender maximizer (`σ_dyn_top_isMaxOn`).
    intro n s' hs'
    exact p.σ_dyn_top_isMaxOn V_S
      (p.dynamicTopLockInPath V_S α x₀ n)
      (α (p.dynamicTopLockInPath V_S α x₀ n)) hs'
  · -- Target preference monotonicity along the path (audit-28 #4).
    intro n
    exact hB.target_prefers_sanctions _ (h_path n)

/-- **General-`F` Goal 1 with equilibrium evidence along the path.**
This is the abstract-transition sibling of
`jointPreferenceBasinTop_long_run_with_equilibrium_evidence`.  It keeps
all four equilibrium-evidence conclusions while evolving the state with
`p.F`: Target feasibility, Target Bellman optimality, Sender dynamic
optimality, and Target sanction-preference monotonicity at every path
state.  No assumption beyond the existing joint-preference basin is
added. -/
theorem jointPreferenceBasinTopF_long_run_with_equilibrium_evidence
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) ∧
    (∀ n, α (p.dynamicTopLockInPathF V_S α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S
                              (p.dynamicTopLockInPathF V_S α x₀ n) a)
              Sanctions.I (α (p.dynamicTopLockInPathF V_S α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective V_S
                              (p.dynamicTopLockInPathF V_S α x₀ n)
                              (α (p.dynamicTopLockInPathF V_S α x₀ n)) s')
              Sanctions.I (p.dynamicTopLockInSanctionsF V_S α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective V_T
        (p.dynamicTopLockInPathF V_S α x₀ n)
        (α (p.dynamicTopLockInPathF V_S α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPathF V_S α x₀ n) sbar) 1)) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  have h_path :=
    p.dynamicTopLockInPathF_mem_basin V_S α hlevel hx₀
  refine ⟨h_path,
          p.dynamicTopLockInSanctionsF_floor V_S α hlevel hx₀,
          p.dynamicTopLockInSanctionsF_ge_xbar V_S α hlevel hx₀,
          p.dynamicTopLockInSanctionsF_mono V_S α hlevel
            hB.top_rule_mono hx₀,
          ?_, ?_, ?_, ?_⟩
  · intro n
    exact hB.target_policy_feasible _ (h_path n)
  · intro n
    exact hB.target_policy_optimal _ (h_path n)
  · intro n s' hs'
    exact p.σ_dyn_top_isMaxOn V_S
      (p.dynamicTopLockInPathF V_S α x₀ n)
      (α (p.dynamicTopLockInPathF V_S α x₀ n)) hs'
  · intro n
    exact hB.target_prefers_sanctions _ (h_path n)

/-! ## Goal 2: top-dynamic sanctions ≥ myopic equilibrium sanctions (same α) -/

/-- **The affine lock-in path is the general-`F` rule path of the affine copy**
(BH6.9, 2026-10-07): `p.lockInPath α = p.affineCopy.rulePathF (p.realizedRule α)`,
by `rfl`. The step `(1 − δ)·x + δ·σ(x, α x)` of `lockInStep` is literally the
copy's transition `affineF p.δ` at the rule's sanction.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22), by construction.** Both sides are the
affine law at rate `p.δ`; neither assumes `p.F = affineF p.δ`. The bridge is
what lets the hF-free affine lemmas about `lockInPath` be instances of the
general-`F` rule-path lemmas (`RulePathF.lean`). -/
theorem lockInPath_eq_affineCopy (α : ℝ → ℝ) :
    p.lockInPath α = p.affineCopy.rulePathF (p.realizedRule α) := rfl

/-- Auxiliary: the *stage* equilibrium path stays in `[0, 1]` from any
feasible starting state (no level condition needed).

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** `lockInPath` hard-codes the affine
law `(1 − δ)·x + δ·rule`, although the signature carries no `hF`. Since BH6.9
(2026-10-07) the proof is a one-line instance of the general-`F`
`rulePathF_mem_I` (`RulePathF.lean`) at the affine copy `p.affineCopy` and
`R := realizedRule α`, through `lockInPath_eq_affineCopy`. The statement is
unchanged and no `hF` is added. -/
theorem lockInPath_mem_I_of_mem_I
    (α : ℝ → ℝ) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.lockInPath α x₀ n ∈ Sanctions.I :=
  p.affineCopy.rulePathF_mem_I (R := p.realizedRule α)
    (fun x _ => p.realizedRule_mem α x) hx₀

/-- **Goal 2.** Under monotone `V_S` and monotone upper-dynamic rule on
`[0, 1]`, the upper-dynamic sanction sequence weakly dominates the
myopic-equilibrium sanction sequence (driven by the stage argmax `σ`)
from any starting state in `[0, 1]`, **without** the kinematic-level-
on-the-myopic-side hypothesis required by the analogous
`Classical.choose`-based theorem in `DynamicLockIn`.

The myopic equilibrium is `p.myopify.lockInSanctions α x₀ n` — by
`myopify_lockInSanctions` this is identically the stage-σ lock-in
sanction path.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** Both sides are affine paths
(`lockInPath` and `dynamicTopLockInPath` hard-code `(1 − δ)·x + δ·rule`) and
the proof reads `p.δ`, although the signature carries no `hF`. General-`F`
siblings (BH2.9, 2026-10-06): `dynamicTopSanctionsF_ge_realizedRule_same_alpha`
(`DifferentPolicyComparator.lean` §11), same hypotheses over `p.F`; and
`dynamicTopSanctionsF_ge_realizedRule_same_alpha_of_responsePair`
(`TwoSidedForwardLooking.lean` §10), which also weakens `Monotone V_S` to the
response-pair condition. Left standing unchanged (no `hF` added). -/
theorem dynamicTopSanctions_ge_myopify_same_alpha
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {x₀ : ℝ}
    (hV : Monotone V_S)
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule V_S α) Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.myopify.lockInSanctions α x₀ n
            ≤ p.dynamicTopLockInSanctions V_S α x₀ n := by
  -- σ_dyn_top dominates σ pointwise under Monotone V_S (unconditional).
  have h_pointwise : ∀ x, p.σ x (α x) ≤ p.dynamicTopRealizedRule V_S α x :=
    fun x => p.σ_dyn_top_ge_sigma V_S hV x (α x)
  -- Both paths stay in I.
  have h_myo_I := p.lockInPath_mem_I_of_mem_I α hx₀
  have h_top_I := p.dynamicTopLockInPath_mem_I_of_mem_I V_S α hx₀
  -- Inductively prove lockInPath n ≤ dynamicTopLockInPath n.
  have h_path : ∀ n, p.lockInPath α x₀ n ≤ p.dynamicTopLockInPath V_S α x₀ n := by
    intro n
    induction n with
    | zero => simp [lockInPath, dynamicTopLockInPath]
    | succ n ih =>
      have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
      have h1δ_nn : 0 ≤ 1 - p.δ := by linarith [p.δ_mem.2]
      -- Step at the myopic state: stage step ≤ top-dynamic step at same x
      have h_step_at_myo :
          p.lockInStep α (p.lockInPath α x₀ n)
            ≤ p.dynamicTopLockInStep V_S α (p.lockInPath α x₀ n) := by
        unfold lockInStep dynamicTopLockInStep
        have h_rule :
            p.realizedRule α (p.lockInPath α x₀ n)
              ≤ p.dynamicTopRealizedRule V_S α (p.lockInPath α x₀ n) :=
          h_pointwise _
        nlinarith [mul_le_mul_of_nonneg_left h_rule hδ_nn]
      -- Top-dynamic step from myopic state ≤ from top state (rule monotone in x).
      have h_step_dyn_mono :
          p.dynamicTopLockInStep V_S α (p.lockInPath α x₀ n)
            ≤ p.dynamicTopLockInStep V_S α (p.dynamicTopLockInPath V_S α x₀ n) := by
        unfold dynamicTopLockInStep
        have h_rule_mono :
            p.dynamicTopRealizedRule V_S α (p.lockInPath α x₀ n)
              ≤ p.dynamicTopRealizedRule V_S α (p.dynamicTopLockInPath V_S α x₀ n) :=
          hTopMonoI (h_myo_I n) (h_top_I n) ih
        have h_state_mono :
            (1 - p.δ) * p.lockInPath α x₀ n
              ≤ (1 - p.δ) * p.dynamicTopLockInPath V_S α x₀ n :=
          mul_le_mul_of_nonneg_left ih h1δ_nn
        have h_rule_part :
            p.δ * p.dynamicTopRealizedRule V_S α (p.lockInPath α x₀ n)
              ≤ p.δ * p.dynamicTopRealizedRule V_S α
                        (p.dynamicTopLockInPath V_S α x₀ n) :=
          mul_le_mul_of_nonneg_left h_rule_mono hδ_nn
        linarith
      simp only [lockInPath_succ, dynamicTopLockInPath_succ]
      exact le_trans h_step_at_myo h_step_dyn_mono
  -- Sanctions: σ(x_myo, α) ≤ σ_dyn_top(x_myo, α) ≤ σ_dyn_top(x_top, α).
  intro n
  rw [myopify_lockInSanctions]
  unfold lockInSanctions dynamicTopLockInSanctions
  calc p.realizedRule α (p.lockInPath α x₀ n)
      ≤ p.dynamicTopRealizedRule V_S α (p.lockInPath α x₀ n) :=
          h_pointwise _
    _ ≤ p.dynamicTopRealizedRule V_S α (p.dynamicTopLockInPath V_S α x₀ n) :=
          hTopMonoI (h_myo_I n) (h_top_I n) (h_path n)

/-! ## Goal 3: temporary shock + basin ⇒ permanent high sanctions -/

/-- **Goal 3.** From any starting state in `[0, 1]`, a temporary shock
brings the state into the basin after some `N` steps, after which the
upper-dynamic state path stays in the basin and the sanction sequence
is bounded below by `sbar` and non-decreasing. The Target's
sanction-preference monotonicity (Target weakly prefers more sanctions
on the high range) is preserved along the post-shock path.

The hypothesis `hsbar_pos : 0 < sbar` makes the "permanent high
sanctions" framing literal: the floor `sbar ≤ s_n` then translates to
strictly positive post-shock sanctions at every period. Without
`hsbar_pos`, the floor inequality is still proved but the "high" in
the theorem name reduces to "non-negative". -/
theorem jointPreferenceBasinTop_temporary_shock_permanent_high
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hxbar_lt_one : xbar < 1)
    (hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective V_T
          (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)
          (α (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)) s)
        (Set.Icc (max (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n) sbar)
                 1)) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  obtain ⟨N, hN⟩ :=
    p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt_one
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  have h_floor :=
    p.dynamicTopLockInSanctions_floor V_S α hlevel h_N_in
  refine ⟨N, ?_, h_floor, ?_, ?_, ?_, ?_⟩
  · exact p.dynamicTopLockInPath_mem_basin V_S α hlevel h_N_in
  · exact p.dynamicTopLockInSanctions_ge_xbar V_S α hlevel h_N_in
  · intro n; exact lt_of_lt_of_le hsbar_pos (h_floor n)
  · exact p.dynamicTopLockInSanctions_mono V_S α hlevel hB.top_rule_mono h_N_in
  · intro n
    exact hB.target_prefers_sanctions
      (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)
      (p.dynamicTopLockInPath_mem_basin V_S α hlevel h_N_in n)

/-- **Goal 3 over the general transition `F` (Option B).** Temporary
maximum-sanction shock under the abstract transition `p.F` drives the
state into the basin in **finite** time (via `shockPathF` and the
strict-above-diagonal `hF_top`), after which the general-`F` natural
dynamics keep the state in the basin with permanently high,
non-decreasing sanctions. Mirrors
`jointPreferenceBasinTop_temporary_shock_permanent_high` with the affine
`shockPath`/`dynamicTopLockInPath` replaced by their `F`-driven
siblings. The price of generality is the loss of the closed-form shock
horizon `N_*`; only `∃ N` is asserted. -/
theorem jointPreferenceBasinTopF_temporary_shock_permanent_high
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hxbar_lt_one : xbar < 1)
    (hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective V_T
          (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n)
          (α (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n)) s)
        (Set.Icc
          (max (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n) sbar)
          1)) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  obtain ⟨N, hN⟩ :=
    p.shockPathF_eventually_in_basin hF_top hx₀_nn hx₀_le hxbar_lt_one
  have h_N_in : p.shockPathF x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  have h_floor :=
    p.dynamicTopLockInSanctionsF_floor V_S α hlevel h_N_in
  refine ⟨N, ?_, h_floor, ?_, ?_, ?_, ?_⟩
  · exact p.dynamicTopLockInPathF_mem_basin V_S α hlevel h_N_in
  · exact p.dynamicTopLockInSanctionsF_ge_xbar V_S α hlevel h_N_in
  · intro n; exact lt_of_lt_of_le hsbar_pos (h_floor n)
  · exact p.dynamicTopLockInSanctionsF_mono V_S α hlevel
      hB.top_rule_mono h_N_in
  · intro n
    exact hB.target_prefers_sanctions
      (p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n)
      (p.dynamicTopLockInPathF_mem_basin V_S α hlevel h_N_in n)

end Params
end AbstractGame

/-! ## Forward-looking equilibrium structure (top-selector version)

The top-selector parallel of `Theory/Equilibrium/StackelbergFeedback`'s
`FeedbackStackelbergEquilibrium`: a sequential feedback Stackelberg
equilibrium whose follower's response is the **upper** dynamic
selector `σ_dyn_top V_S` rather than the `Classical.choose`-based
`σ_dyn V_S`, and whose Target Bellman fixed-point equation uses
`joint_T_top_integrand`.

This keeps Rule 1 (optimal-strategies-only) strict at the
*top*-selector level: when combined with `JointPreferenceBasinTop`
the headline persistence theorem rests on a **stationary recursive
(feedback / fixed-point) Stackelberg equilibrium** — Banach Bellman
fixed points, leader argmax, upper follower selector — rather than on
arbitrary continuation functions.

**Scope of the optimality claim (read this before citing the concept).**
`α_opt_top` asserts `IsMaxOn (joint_T_top_integrand V_T V_S x) I (α x)`:
the leader's action is optimal *pointwise in the state, over actions,
against frozen continuation values* `V_T`, `V_S`. The Sender fixed-point
field `V_S_fix` pins the Sender value only *at the equilibrium policy*
`α`, so a hypothetical leader deviation is never accompanied by a Sender
re-solve. This is a fixed-point / Markov-feedback equilibrium (FPE) in
the sense of the recursive dynamic-programming literature.

It is **not** claimed to be a stationary *strong* Stackelberg
equilibrium (SSSE): nothing here quantifies over alternative stationary
leader policies, and no theorem in this development establishes that the
fixed point maximises the leader's value against the follower's true best
response to an arbitrary policy. The two concepts are known to differ,
and each can exist when the other fails (Bucarey et al.; Kudo–Akimoto).
The deviation results in the tree are: the one-shot bound below and in
`Theory/Equilibrium/StackelbergFeedback`, and — since Rung 5 — the lifetime
statements of `Theory/Equilibrium/TopLifetimeVerification`: the Target's
policy beats every time-dependent Markov deviation against the Sender's fixed
contingent response, and the Sender's response beats every such deviation
with the Target's policy fixed. Neither is a policy-space optimum with a
follower re-solve. -/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Sequential feedback Stackelberg equilibrium with the upper
dynamic selector.** Parallel of `FeedbackStackelbergEquilibrium`
(in `StackelbergFeedback`) using `joint_T_top_integrand` (i.e. the
follower's response is `σ_dyn_top V_S`, not the arbitrary
`Classical.choose`-based `σ_dyn V_S`).

Rule 1 reading: every load-bearing strategy is equilibrium-derived.
`V_T`, `V_S` are Banach Bellman fixed points; `α` is leader-argmax of
the top integrand; the implicit follower response
`σ_dyn_top V_S x a` is the supremum of the dynamic argmax set and
is itself a dynamic Sender maximizer (`σ_dyn_top_isMaxOn`). -/
structure FeedbackStackelbergEquilibriumTop where
  /-- Target (leader) value function. -/
  V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- Sender (follower) value function. -/
  V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
  /-- Target (leader) feedback policy. -/
  α : ℝ → ℝ
  /-- Continuity of α, for `bellmanS_BCF` compatibility. -/
  hα : Continuous α
  /-- α is feasible at every *feasible* state (audit-28 #2: restricted from
  `∀ x : ℝ` to `∀ x ∈ Sanctions.S`, since the global form is economically
  unnecessary). -/
  α_mem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I
  /-- **Follower fixed-point condition.** `V_S` is the Sender Bellman
  fixed point under leader policy α. -/
  V_S_fix : V_S = p.bellmanS_BCF α hα V_S
  /-- **Leader fixed-point condition (top).** `V_T(x)` solves the
  Target joint Bellman equation against the follower's
  *upper-selector* response `σ_dyn_top V_S` at every state in `↥S`. -/
  V_T_fix_top : ∀ x : ↥(Sanctions.S : Set ℝ),
    V_T x = sSup ((fun a => p.joint_T_top_integrand V_T V_S x.val a)
                    '' Sanctions.I)
  /-- **Leader Bellman optimality (top).** α attains the joint top
  integrand's argmax at every *feasible* state (audit-28 #2: restricted
  from `∀ x : ℝ` to `∀ x ∈ Sanctions.S`). -/
  α_opt_top : ∀ x ∈ Sanctions.S,
    IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a) Sanctions.I (α x)

/-- **Sender response projection (top selector)** for
`FeedbackStackelbergEquilibriumTop`. Exposes the implicit
upper-selector Sender best response `p.σ_dyn_top E.V_S x a` as an
accessible function. Under the regular value class assumed by
`StandardComplianceLocalCertificate` (where
`p.DynamicArgmaxUnique E.V_S` holds), this coincides pointwise with
the ordinary `FeedbackStackelbergEquilibrium.ρ` via
`σ_dyn_eq_σ_dyn_top_of_unique`. -/
noncomputable def FeedbackStackelbergEquilibriumTop.ρ
    {p : Sanctions.AbstractGame.Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (x a : ℝ) : ℝ :=
  p.σ_dyn_top E.V_S x a

/-- The top-selector Sender response projection lies in `Sanctions.I`. -/
theorem FeedbackStackelbergEquilibriumTop.ρ_mem
    {p : Sanctions.AbstractGame.Params}
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) :
    E.ρ x a ∈ Sanctions.I :=
  p.σ_dyn_top_mem_I E.V_S x a

/-- **Sender best-response optimality at the top-selector equilibrium.**
The top-selector Sender response projection
`E.ρ x a = p.σ_dyn_top E.V_S x a` is a maximizer of the Sender
dynamic objective at the equilibrium continuation value `E.V_S`.
Makes the Sender side of the top equilibrium visibly sequentially
rational at every `(x, a)`. -/
theorem FeedbackStackelbergEquilibriumTop.ρ_isMaxOn
    {p : Sanctions.AbstractGame.Params}
    (E : p.FeedbackStackelbergEquilibriumTop) (x a : ℝ) :
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * E.V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I (E.ρ x a) :=
  p.σ_dyn_top_isMaxOn E.V_S x a

end Params
end AbstractGame

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Paper-facing alias for the fully forward-looking equilibrium's
realized sanction rule.** At every state `x`, the fully
forward-looking feedback Stackelberg equilibrium realizes the
sanction `p.σ_dyn_top E.V_S x (E.α x)` — equivalently,
`p.dynamicTopRealizedRule E.V_S E.α x`. Here `E.α x` is the Target's
forward-looking Bellman-optimal policy and `σ_dyn_top` is the upper
selector of the Sender's dynamic argmax (the maximizer of
`U_S(x, E.α x, s) + β_S · E.V_S(F(x, s))`). This is exposed under a
paper-facing name so the regime-comparison theorem reads
`myopicEquilibriumRule M x ≤ dynamicEquilibriumRule E x` instead of
the lower-level `σ`/`σ_dyn_top` syntax. -/
noncomputable def dynamicEquilibriumRule
    (E : p.FeedbackStackelbergEquilibriumTop) : ℝ → ℝ :=
  fun x => p.dynamicTopRealizedRule E.V_S E.α x

/-- `dynamicEquilibriumRule` unfolds to `dynamicTopRealizedRule` at
the equilibrium's value function and policy. Definitional `rfl`
bridge so callers may rewrite freely between the two forms. -/
@[simp] theorem dynamicEquilibriumRule_eq
    (E : p.FeedbackStackelbergEquilibriumTop) (x : ℝ) :
    p.dynamicEquilibriumRule E x = p.dynamicTopRealizedRule E.V_S E.α x :=
  rfl

end Params
end AbstractGame

namespace AbstractGame
namespace Params

/-- **One-shot deviation principle for the Target (leader, top
selector).** Parallel of
`FeedbackStackelbergEquilibrium.target_one_shot_deviation`. -/
theorem FeedbackStackelbergEquilibriumTop.target_one_shot_deviation_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) :
    ∀ x : ↥(Sanctions.S : Set ℝ), ∀ a' ∈ Sanctions.I,
      p.joint_T_top_integrand E.V_T E.V_S x.val a' ≤ E.V_T x := by
  intro x a' ha'
  rw [E.V_T_fix_top x]
  have h_bdd : BddAbove
      ((fun a => p.joint_T_top_integrand E.V_T E.V_S x.val a)
        '' Sanctions.I) := by
    refine ⟨p.joint_T_top_integrand E.V_T E.V_S x.val (E.α x.val), ?_⟩
    rintro y ⟨a, ha, rfl⟩
    exact E.α_opt_top x.val x.property ha
  exact le_csSup h_bdd ⟨a', ha', rfl⟩

/-- **Equality at the optimal policy (top selector).** -/
theorem FeedbackStackelbergEquilibriumTop.target_value_at_alpha_top
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) :
    ∀ x : ↥(Sanctions.S : Set ℝ),
      E.V_T x = p.joint_T_top_integrand E.V_T E.V_S x.val (E.α x.val) := by
  intro x
  rw [E.V_T_fix_top x]
  apply le_antisymm
  · apply csSup_le
    · refine ⟨p.joint_T_top_integrand E.V_T E.V_S x.val 0,
              0, by simp [Sanctions.I], rfl⟩
    · rintro y ⟨a, ha, rfl⟩
      exact E.α_opt_top x.val x.property ha
  · have h_bdd : BddAbove
        ((fun a => p.joint_T_top_integrand E.V_T E.V_S x.val a)
          '' Sanctions.I) := by
      refine ⟨p.joint_T_top_integrand E.V_T E.V_S x.val (E.α x.val), ?_⟩
      rintro y ⟨a, ha, rfl⟩
      exact E.α_opt_top x.val x.property ha
    exact le_csSup h_bdd ⟨E.α x.val, E.α_mem x.val x.property, rfl⟩

/-! ## Canonical identification of `E.V_S` and `Monotone E.V_S` derivation

Audit-26 round 3 cleanup. The Sender value function `E.V_S` stored in a
`FeedbackStackelbergEquilibriumTop` is a *Banach-unique* fixed point of
`bellmanS_BCF E.α E.hα`, so it equals the canonical `p.V_S E.α E.hα`
defined in `BellmanS`. This unlocks the *primitive* monotonicity
derivation `V_S_monotone_of_integrand_monotone` (which is stated for
the canonical fixed point) for `E.V_S` too. -/

/-- **Canonical identification.** Banach uniqueness of the
`bellmanS_BCF E.α E.hα` fixed point identifies `E.V_S` with the
canonical Sender value function `p.V_S E.α E.hα` from `BellmanS`. -/
theorem FeedbackStackelbergEquilibriumTop.V_S_eq_canonical
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop) :
    E.V_S = p.V_S E.α E.hα := by
  -- `p.V_S α hα` is `ContractingWith.fixedPoint (bellmanS_BCF α hα) hContr`.
  -- `E.V_S_fix` makes `E.V_S` a fixed point of the same operator.
  -- Banach uniqueness ⇒ they coincide.
  have hContr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF E.α E.hα) :=
    p.bellmanS_BCF_contracting E.hα
  have hFix : Function.IsFixedPt (p.bellmanS_BCF E.α E.hα) E.V_S := by
    -- `E.V_S_fix : E.V_S = bellmanS_BCF E.α E.hα E.V_S`, want `f x = x`.
    exact E.V_S_fix.symm
  -- `p.V_S E.α E.hα = ContractingWith.fixedPoint (p.bellmanS_BCF E.α E.hα) hContr`
  -- (definitionally, by the V_S def in BellmanS).
  exact ContractingWith.fixedPoint_unique hContr hFix

/-- **`Monotone E.V_S` from primitive U_S state-monotonicity (audit-26 #3 path B).**

Drop-in derivation of the `Monotone E.V_S` hypothesis from the more
*primitive* condition that, at the leader policy `E.α`, the Sender's
stage payoff `U_S(x, E.α x, s)` is monotone non-decreasing in `x` at
every fixed sanction `s ∈ [0, 1]`.

The proof routes through the canonical identification
`V_S_eq_canonical` and the existing
`V_S_monotone_of_integrand_monotone` cone-preservation theorem in
`BellmanS`. -/
theorem FeedbackStackelbergEquilibriumTop.V_S_monotone_of_integrand_monotone
    {p : Params} (E : p.FeedbackStackelbergEquilibriumTop)
    (h_U_S_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (E.α x) s ≤ p.U_S y (E.α y) s) :
    Monotone (fun x : ↥(Sanctions.S : Set ℝ) => E.V_S x) := by
  -- Reduce to the canonical fixed point.
  rw [show (fun x : ↥(Sanctions.S : Set ℝ) => E.V_S x)
        = (fun x : ↥(Sanctions.S : Set ℝ) => (p.V_S E.α E.hα) x) by
      simp [E.V_S_eq_canonical]]
  -- Then apply existing cone-preservation theorem.
  exact p.V_S_monotone_of_integrand_monotone E.hα h_U_S_mono

/-! ## Headline: forward-looking equilibrium + basin Prop ⇒ persistence

The cleanest forward-looking-equilibrium statement combining
`FeedbackStackelbergEquilibriumTop` with `JointPreferenceBasinTop`:
along the upper-dynamic state path from any basin start, the state
remains in the basin, sanctions are bounded below by `sbar` and
non-decreasing, AND the Target Bellman fixed point + leader argmax
+ feasibility hold along the entire path.

This is the Rule-1 reading of Goal 1: persistence rests on a full
forward-looking equilibrium, not on arbitrary continuation
functions. -/

/-- **Headline (forward-looking equilibrium + basin Prop):**
along the upper-dynamic path from any basin start, the persistence
conclusions hold *and* the equilibrium structure is preserved at
every step. -/
theorem equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  have hlevel := JointPreferenceBasinTop.level_dyn_top p hB
  refine ⟨
    p.dynamicTopLockInPath_mem_basin E.V_S E.α hlevel hx₀,
    p.dynamicTopLockInSanctions_floor E.V_S E.α hlevel hx₀,
    p.dynamicTopLockInSanctions_ge_xbar E.V_S E.α hlevel hx₀,
    p.dynamicTopLockInSanctions_mono E.V_S E.α hlevel hB.top_rule_mono hx₀,
    ?_⟩
  -- Audit-28 #2: E.α_opt_top requires `_ ∈ Sanctions.S`. Derive from
  -- basin membership (`xbar ≥ 0` via `hB.xbar_nonneg`, so `[xbar, 1] ⊆ [0,1]`).
  intro n
  have h_path_n := p.dynamicTopLockInPath_mem_basin E.V_S E.α hlevel hx₀ n
  exact E.α_opt_top _
    ⟨le_trans hB.xbar_nonneg h_path_n.1, h_path_n.2⟩

end Params
end AbstractGame

/-! ## Public-facing wrappers from one-sided thresholds

The most representative paper-level statements: compose
`OneSidedSanctionPreferenceThresholds` (paper Assumptions 1+2),
`JointPreferenceBasinTop.of_oneSidedThresholds` (paper
\Cref{prop:jointPref_nonempty}), and the three goal theorems into
single-call wrappers that match the paper's claim API. -/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Headline (one-sided thresholds ⇒ long-run non-decreasing high
sanctions).** Composes
`JointPreferenceBasinTop.of_oneSidedThresholds` with
`jointPreferenceBasinTop_long_run_nonDecreasing`. -/
theorem oneSidedThresholds_long_run_nonDecreasing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar)
    (hα_feas : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x ∈ Sanctions.I)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
                            (Set.Icc (max xT xS) 1))
    (hα_opt : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
              IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                      Sanctions.I (α x))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions V_S α x₀) :=
  p.jointPreferenceBasinTop_long_run_nonDecreasing
    (JointPreferenceBasinTop.of_oneSidedThresholds p hOne
      hα_feas hTopMono hα_opt) hx₀

/-- **Single-crossing-discharged headline (Goal 1).** Replaces the raw
`hTopMono` hypothesis of `oneSidedThresholds_long_run_nonDecreasing`
with the Milgrom-Shannon single-crossing primitive
`hSC : SingleCrossing (fun s x => p.senderDynObjective V_S x (α x) s)`,
discharging top-rule monotonicity via
`dynamicTopRealizedRule_mono_of_singleCrossing`. -/
theorem oneSidedThresholds_long_run_nonDecreasing_of_singleCrossing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar)
    (hα_feas : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x ∈ Sanctions.I)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective V_S x (α x) s))
    (hα_opt : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
              IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                      Sanctions.I (α x))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions V_S α x₀) :=
  p.oneSidedThresholds_long_run_nonDecreasing hOne hα_feas
    (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC) hα_opt hx₀

/-- **Headline (one-sided thresholds ⇒ temporary-shock permanent
high sanctions).** -/
theorem oneSidedThresholds_temporary_shock_permanent_high
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hα_feas : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x ∈ Sanctions.I)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule V_S α)
                            (Set.Icc (max xT xS) 1))
    (hα_opt : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
              IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                      Sanctions.I (α x))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective V_T
          (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)
          (α (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)) s)
        (Set.Icc (max (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n) sbar)
                 1)) :=
  p.jointPreferenceBasinTop_temporary_shock_permanent_high
    (JointPreferenceBasinTop.of_oneSidedThresholds p hOne
      hα_feas hTopMono hα_opt) hjoint_lt hsbar_pos hx₀_nn hx₀_le

/-- **Single-crossing-discharged shock theorem (Goal 3).** -/
theorem oneSidedThresholds_temporary_shock_permanent_high_of_singleCrossing
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hα_feas : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x ∈ Sanctions.I)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective V_S x (α x) s))
    (hα_opt : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
              IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S x a)
                      Sanctions.I (α x))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective V_T
          (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)
          (α (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n)) s)
        (Set.Icc (max (p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n) sbar)
                 1)) :=
  p.oneSidedThresholds_temporary_shock_permanent_high hOne hsbar_pos
    hjoint_lt hα_feas
    (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC) hα_opt
    hx₀_nn hx₀_le

end Params
end AbstractGame

/-! ## Helpers for audit-28 #2: basin → feasible-state inclusion

The audit-28 #2 cleanup restricts `α_mem` and `α_opt_top` of
`FeedbackStackelbergEquilibriumTop` from `∀ x : ℝ` to `∀ x ∈ Sanctions.S`.
Most downstream wrappers operate on the basin `[max xT xS, 1]` with
`xT, xS ∈ Sanctions.I`; the helper below packages the basin → `Sanctions.S`
inclusion so call sites stay readable. -/

/-- Basin `[max xT xS, 1]` lies inside the feasible state space
`Sanctions.S = [0, 1]` whenever `xT ∈ Sanctions.I`. -/
private theorem icc_max_subset_S {xT xS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) :
    Set.Icc (max xT xS) (1 : ℝ) ⊆ Sanctions.S := fun _ hx =>
  ⟨le_trans (le_max_of_le_left hxT_mem.1) hx.1, hx.2⟩

/-! ## Equilibrium-top + one-sided-threshold wrappers

The strongest abstract headline: combine
`FeedbackStackelbergEquilibriumTop` (a full forward-looking
equilibrium under the upper selector) with
`OneSidedSanctionPreferenceThresholds` (paper Asn 1+2) for the
"two forward-looking individuals" persistence statement. -/

namespace AbstractGame
namespace Params

/-- **Strongest headline (full equilibrium + one-sided thresholds ⇒
persistence).** No witness needed; auxiliary `hα_feas` and `hα_opt`
are discharged from `E.α_mem` and `E.α_opt_top` automatically. -/
theorem equilibriumTop_oneSidedThresholds_long_run_nonDecreasing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) :=
  equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing E
    (JointPreferenceBasinTop.of_oneSidedThresholds p hOne
      (fun x hx => E.α_mem x (icc_max_subset_S hOne.xT_mem hx)) hTopMono
      (fun x hx => E.α_opt_top x (icc_max_subset_S hOne.xT_mem hx)))
    hx₀

/-- **Strongest headline (full equilibrium + one-sided thresholds ⇒
temporary-shock permanent high sanctions).** -/
theorem equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)) s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n) sbar)
          1)) :=
  p.jointPreferenceBasinTop_temporary_shock_permanent_high
    (JointPreferenceBasinTop.of_oneSidedThresholds p hOne
      (fun x hx => E.α_mem x (icc_max_subset_S hOne.xT_mem hx)) hTopMono
      (fun x hx => E.α_opt_top x (icc_max_subset_S hOne.xT_mem hx)))
    hjoint_lt hsbar_pos hx₀_nn hx₀_le

/-- **Equilibrium-facing Goal 2 wrapper (same-α myopified comparator).**

The same-α dominance of the upper-dynamic sanction sequence over the
myopified-stage one (`dynamicTopSanctions_ge_myopify_same_alpha`) re-
stated for a full forward-looking equilibrium `E`.

**Scope qualifier (audit-26 #3).** This is a *same-α* comparison: the
Target policy on **both** sides is `E.α`, which is Bellman-optimal on
the *dynamic* side by `E.α_opt_top`. On the *myopified* side this
theorem treats `E.α` as a same-policy comparator — `E.α` is
*not* in general the Bellman-optimal Target policy of the myopified
game `p.myopify`. So the conclusion is "the dynamic equilibrium
sanction sequence weakly dominates the myopified comparator under the
same Target policy", not "the dynamic equilibrium dominates an
independently-optimized myopic equilibrium". The strict-dominance
form (different α on each side) is paper-level theoretical content not
provided by this theorem. See
`equilibriumTop_dynamicTopSanctions_ge_myopify_same_alpha_with_myopic_target_evidence`
for the variant that additionally certifies the myopic side as a genuine
same-α equilibrium when `E.α` happens to also be myopically optimal.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** Stated over the affine paths of
`dynamicTopSanctions_ge_myopify_same_alpha`, with no `hF` in the signature.
General-`F` siblings: `dynamicTopSanctionsF_ge_realizedRule_same_alpha` at
`V_S := E.V_S`, `α := E.α` (`DifferentPolicyComparator.lean` §11), and its
response-pair form in `TwoSidedForwardLooking.lean` §10 (BH2.9). -/
theorem equilibriumTop_dynamicTopSanctions_ge_myopify_same_alpha
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ}
    (hV : Monotone E.V_S)
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                             Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ n, p.myopify.lockInSanctions E.α x₀ n
            ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n :=
  p.dynamicTopSanctions_ge_myopify_same_alpha hV hTopMonoI hx₀

/-- **Equilibrium-facing Goal 2 wrapper with explicit myopic-side
equilibrium evidence.** Conclusion is now a *conjunction* (audit-27
cleanup): (i) the same-α weak dominance of the upper-dynamic sanction
sequence over the myopified-stage path; (ii) the myopic-side
equilibrium evidence the caller supplied (`hα_myo_opt`), forwarded
through the conclusion so callers can chain it as path-level
witness data. Under this extra hypothesis, the same-α comparison is
genuinely equilibrium-vs-equilibrium on both sides (same α =
dynamic-optimal AND myopic-optimal). Strict dominance with a
different myopic α remains paper-level theoretical content.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** The dominance conjunct is stated
over the affine paths of `dynamicTopSanctions_ge_myopify_same_alpha`, with no
`hF` in the signature. General-`F` siblings of that conjunct:
`dynamicTopSanctionsF_ge_realizedRule_same_alpha`
(`DifferentPolicyComparator.lean` §11) and its response-pair form in
`TwoSidedForwardLooking.lean` §10 (BH2.9). -/
theorem equilibriumTop_dynamicTopSanctions_ge_myopify_same_alpha_with_myopic_target_evidence
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ}
    (hV : Monotone E.V_S)
    (hTopMonoI : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                             Sanctions.I)
    (hx₀ : x₀ ∈ Sanctions.I)
    (hα_myo_opt : ∀ x ∈ Sanctions.I,
        IsMaxOn (fun a => p.U_T x a (p.σ x a)) Sanctions.I (E.α x)) :
    (∀ n, p.myopify.lockInSanctions E.α x₀ n
            ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ x ∈ Sanctions.I,
        IsMaxOn (fun a => p.U_T x a (p.σ x a)) Sanctions.I (E.α x)) :=
  ⟨p.dynamicTopSanctions_ge_myopify_same_alpha hV hTopMonoI hx₀,
   hα_myo_opt⟩

/-- **Strongest headline with full equilibrium-evidence along path
(Goal 1).** Sibling of
`equilibriumTop_oneSidedThresholds_long_run_nonDecreasing` that
additionally returns the path-level equilibrium evidence (α
feasibility, α Bellman-optimal, `σ_dyn_top` is a Sender maximizer at
every basin state). This is the "two forward-looking individuals
reach and remain in the high-sanction region" theorem in fully
unfolded form. -/
theorem equilibriumTop_oneSidedThresholds_long_run_with_equilibrium_evidence
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n)
                              (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctions E.V_S E.α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective E.V_T
        (p.dynamicTopLockInPath E.V_S E.α x₀ n)
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath E.V_S E.α x₀ n) sbar) 1)) :=
  p.jointPreferenceBasinTop_long_run_with_equilibrium_evidence
    (JointPreferenceBasinTop.of_oneSidedThresholds p hOne
      (fun x hx => E.α_mem x (icc_max_subset_S hOne.xT_mem hx)) hTopMono
      (fun x hx => E.α_opt_top x (icc_max_subset_S hOne.xT_mem hx)))
    hx₀

/-- **Strongest headline with full equilibrium-evidence along path
(Goal 3, post-shock).** Sibling of
`equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high`
that additionally returns the path-level equilibrium evidence post-shock. -/
theorem equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_with_equilibrium_evidence
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      -- Kinematic conclusions (same as ..._temporary_shock_permanent_high):
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      -- Equilibrium evidence along the post-shock path:
      (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
              ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n) a)
                Sanctions.I
                (E.α (p.dynamicTopLockInPath E.V_S E.α
                        (p.shockPath x₀ N) n))) ∧
      (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n)
                                (E.α (p.dynamicTopLockInPath E.V_S E.α
                                        (p.shockPath x₀ N) n)) s')
                Sanctions.I
                (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n)) := by
  have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne
    (fun x hx => E.α_mem x (icc_max_subset_S hOne.xT_mem hx)) hTopMono
    (fun x hx => E.α_opt_top x (icc_max_subset_S hOne.xT_mem hx))
  -- Shock entry gives basin invariance + sanctions floor + monotone etc.
  obtain ⟨N, h_basin, h_floor, h_xbar, h_pos, h_mono, _h_target⟩ :=
    p.jointPreferenceBasinTop_temporary_shock_permanent_high hB hjoint_lt
      hsbar_pos hx₀_nn hx₀_le
  -- Post-shock equilibrium evidence from Goal 1 at the post-shock state.
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc (max xT xS) 1 := h_basin 0
  obtain ⟨_, _, _, _, h_α_feas, h_α_opt, h_σ_max, _h_target_path⟩ :=
    p.jointPreferenceBasinTop_long_run_with_equilibrium_evidence hB h_N_in
  exact ⟨N, h_basin, h_floor, h_xbar, h_pos, h_mono, h_α_feas, h_α_opt, h_σ_max⟩

/-- **Single-crossing-discharged strongest headline (Goal 1, equilibrium
+ thresholds).** -/
theorem equilibriumTop_oneSidedThresholds_long_run_nonDecreasing_of_singleCrossing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) :=
  equilibriumTop_oneSidedThresholds_long_run_nonDecreasing E hOne
    (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC) hx₀

/-- **Single-crossing-discharged strongest headline (Goal 3, equilibrium
+ thresholds + temporary shock).** -/
theorem equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_of_singleCrossing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)) s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n) sbar)
          1)) :=
  equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high E hOne
    hsbar_pos hjoint_lt
    (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC) hx₀_nn hx₀_le

/-! ## Stage-preference wrappers (paper-facing API)

The cleanest top-level API: theorems that start directly from the
paper's stage-level economic primitives (`∂U_S/∂s > 0` and
`∂U_T/∂s ≥ 0` on the relevant intervals, expressed as order-language
monotonicity) plus monotone continuation values $V_T, V_S$, and
deliver the headline persistence + equilibrium-evidence conclusions in
one step. Composes
`OneSidedSanctionPreferenceThresholds.of_stage_preferences` with
`equilibriumTop_oneSidedThresholds_*_with_equilibrium_evidence`. -/

/-- **Top API (Goal 1): stage preferences ⇒ long-run persistence
with full equilibrium evidence.** Starts directly from the paper's
stage-level sanction-preference primitives (lifted to forward-looking
preferences via the stage-to-dynamic bridges) plus monotone
continuation values; concludes Goal 1's persistence + the path-level
equilibrium evidence. -/
theorem equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T) (hV_S_mono : Monotone E.V_S)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n)
                              (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctions E.V_S E.α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective E.V_T
        (p.dynamicTopLockInPath E.V_S E.α x₀ n)
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath E.V_S E.α x₀ n) sbar) 1)) :=
  equilibriumTop_oneSidedThresholds_long_run_with_equilibrium_evidence E
    (OneSidedSanctionPreferenceThresholds.of_stage_preferences p
      hV_T_mono hV_S_mono hxT_mem hxS_mem hsbar_mem
      h_stage_sender h_stage_target)
    hTopMono hx₀

/-- **Top API (Goal 3): stage preferences + temporary shock ⇒
permanent high sanctions with full equilibrium evidence.** -/
theorem equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T) (hV_S_mono : Monotone E.V_S)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hjoint_lt : max xT xS < 1)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
              ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n) a)
                Sanctions.I
                (E.α (p.dynamicTopLockInPath E.V_S E.α
                        (p.shockPath x₀ N) n))) ∧
      (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n)
                                (E.α (p.dynamicTopLockInPath E.V_S E.α
                                        (p.shockPath x₀ N) n)) s')
                Sanctions.I
                (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n)) :=
  equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_with_equilibrium_evidence E
    (OneSidedSanctionPreferenceThresholds.of_stage_preferences p
      hV_T_mono hV_S_mono hxT_mem hxS_mem hsbar_mem
      h_stage_sender h_stage_target)
    hsbar_pos hjoint_lt hTopMono hx₀_nn hx₀_le

/-! ## Single-crossing-discharged top API wrappers (audit-26 #1, #2)

The cleanest paper-facing API: each variant takes the
Milgrom-Shannon single-crossing primitive
`Sanctions.MilgromShannon.SingleCrossing` of the Sender's dynamic
objective in $(s; x)$, and discharges the `hTopMono` (Topkis
monotonicity of the upper-selector rule) hypothesis via
`dynamicTopRealizedRule_mono_of_singleCrossing`. The result is a
chain of paper hypotheses that reduces to:

  stage preferences (or one-sided thresholds)
  + monotone continuation values
  + MS single crossing
  ⇒ Goal 1 / Goal 3 persistence with full path-level equilibrium evidence.
-/

-- Long descriptive theorem names below intentionally exceed 100 chars to
-- preserve the consistent `_of_singleCrossing` naming pattern; suppress
-- the line-length linter for each of the four new theorem signatures.

set_option linter.style.longLine false in
/-- **One-sided thresholds, full evidence, Goal 1 with single crossing.**
Single-crossing-discharged variant of
`equilibriumTop_oneSidedThresholds_long_run_with_equilibrium_evidence`.
The `hTopMono` hypothesis is replaced by an MS single-crossing
hypothesis on the Sender's forward-looking objective and discharged via
`dynamicTopRealizedRule_mono_of_singleCrossing`. -/
theorem equilibriumTop_oneSidedThresholds_long_run_with_equilibrium_evidence_of_singleCrossing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n)
                              (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctions E.V_S E.α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective E.V_T
        (p.dynamicTopLockInPath E.V_S E.α x₀ n)
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath E.V_S E.α x₀ n) sbar) 1)) :=
  equilibriumTop_oneSidedThresholds_long_run_with_equilibrium_evidence E
    hOne
    (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC) hx₀

set_option linter.style.longLine false in
/-- **One-sided thresholds, full evidence, Goal 3 with single crossing.**
Single-crossing-discharged variant of
`equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_with_equilibrium_evidence`. -/
theorem equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_with_equilibrium_evidence_of_singleCrossing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hOne : p.OneSidedSanctionPreferenceThresholds E.V_T E.V_S E.α xT xS sbar)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
              ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n) a)
                Sanctions.I
                (E.α (p.dynamicTopLockInPath E.V_S E.α
                        (p.shockPath x₀ N) n))) ∧
      (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n)
                                (E.α (p.dynamicTopLockInPath E.V_S E.α
                                        (p.shockPath x₀ N) n)) s')
                Sanctions.I
                (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n)) :=
  equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_with_equilibrium_evidence E
    hOne hsbar_pos hjoint_lt
    (p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC) hx₀_nn hx₀_le

set_option linter.style.longLine false in
/-- **Stage preferences, Goal 1 with single crossing.**
Strongest paper-facing API: starts from stage primitives + monotone
continuation values + MS single crossing, delivers full
equilibrium-evidence persistence. -/
theorem equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence_of_singleCrossing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T) (hV_S_mono : Monotone E.V_S)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n)
                              (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctions E.V_S E.α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective E.V_T
        (p.dynamicTopLockInPath E.V_S E.α x₀ n)
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath E.V_S E.α x₀ n) sbar) 1)) :=
  equilibriumTop_oneSidedThresholds_long_run_with_equilibrium_evidence_of_singleCrossing E
    (OneSidedSanctionPreferenceThresholds.of_stage_preferences p
      hV_T_mono hV_S_mono hxT_mem hxS_mem hsbar_mem
      h_stage_sender h_stage_target)
    hSC hx₀

set_option linter.style.longLine false in
/-- **Stage preferences, Goal 3 with single crossing.**
Strongest paper-facing API for the temporary-shock case. -/
theorem equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence_of_singleCrossing
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T) (hV_S_mono : Monotone E.V_S)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hjoint_lt : max xT xS < 1)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
              ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n) a)
                Sanctions.I
                (E.α (p.dynamicTopLockInPath E.V_S E.α
                        (p.shockPath x₀ N) n))) ∧
      (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n)
                                (E.α (p.dynamicTopLockInPath E.V_S E.α
                                        (p.shockPath x₀ N) n)) s')
                Sanctions.I
                (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n)) :=
  equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high_with_equilibrium_evidence_of_singleCrossing E
    (OneSidedSanctionPreferenceThresholds.of_stage_preferences p
      hV_T_mono hV_S_mono hxT_mem hxS_mem hsbar_mem
      h_stage_sender h_stage_target)
    hsbar_pos hjoint_lt hSC hx₀_nn hx₀_le

/-! ## Path-B variants: primitive state-monotonicity of `U_S` in place of `Monotone E.V_S`

Audit-26 round-3 Path B. The existing stage-preference wrappers take
`hV_S_mono : Monotone E.V_S` as a hypothesis. Path B replaces this with
the more *primitive* condition that the Sender's stage payoff
`U_S(x, E.α x, s)` is monotone non-decreasing in `x` at every fixed
sanction `s`, and derives `Monotone E.V_S` internally via
`E.V_S_monotone_of_integrand_monotone` (cone preservation of
`bellmanS_BCF` + Banach uniqueness identifying `E.V_S` with the
canonical fixed point).

The variants are otherwise identical to the Path-A wrappers above and
return the same equilibrium-evidence conclusions. They give the
caller a choice: pass `Monotone E.V_S` directly (Path A) or pass the
primitive `h_U_S_state_mono` (Path B). The Target side still takes
`Monotone E.V_T` as a hypothesis pending the analogous V_T canonical-
identification work for the *joint* Target Bellman operator. -/

set_option linter.style.longLine false in
/-- **Path-B variant of `equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence`.**
Drops `hV_S_mono`; takes primitive state-monotonicity of `U_S(·, E.α ·, s)`
instead. -/
theorem equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence_of_U_S_state_monotone
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T)
    (h_U_S_state_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (E.α x) s ≤ p.U_S y (E.α y) s)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n)
                              (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctions E.V_S E.α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective E.V_T
        (p.dynamicTopLockInPath E.V_S E.α x₀ n)
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath E.V_S E.α x₀ n) sbar) 1)) :=
  equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence E
    hV_T_mono (E.V_S_monotone_of_integrand_monotone h_U_S_state_mono)
    hxT_mem hxS_mem hsbar_mem
    h_stage_sender h_stage_target
    hTopMono hx₀

set_option linter.style.longLine false in
/-- **Path-B variant of `equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence`.**
Drops `hV_S_mono`; takes primitive state-monotonicity of `U_S(·, E.α ·, s)`
instead. -/
theorem equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence_of_U_S_state_monotone
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T)
    (h_U_S_state_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (E.α x) s ≤ p.U_S y (E.α y) s)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hjoint_lt : max xT xS < 1)
    (hTopMono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                            (Set.Icc (max xT xS) 1))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
              ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n) a)
                Sanctions.I
                (E.α (p.dynamicTopLockInPath E.V_S E.α
                        (p.shockPath x₀ N) n))) ∧
      (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n)
                                (E.α (p.dynamicTopLockInPath E.V_S E.α
                                        (p.shockPath x₀ N) n)) s')
                Sanctions.I
                (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n)) :=
  equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence E
    hV_T_mono (E.V_S_monotone_of_integrand_monotone h_U_S_state_mono)
    hxT_mem hxS_mem hsbar_mem hsbar_pos
    h_stage_sender h_stage_target
    hjoint_lt hTopMono hx₀_nn hx₀_le

set_option linter.style.longLine false in
/-- **Path-B + single-crossing Goal 1 wrapper.** Combines Path B (primitive
state-monotonicity of `U_S` instead of `Monotone E.V_S`) with the
single-crossing discharge of the top-rule monotonicity. -/
theorem equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence_of_singleCrossing_of_U_S_state_monotone
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T)
    (h_U_S_state_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (E.α x) s ≤ p.U_S y (E.α y) s)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
              Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                              (p.dynamicTopLockInPath E.V_S E.α x₀ n)
                              (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctions E.V_S E.α x₀ n)) ∧
    (∀ n, MonotoneOn
      (fun s => p.targetSanctionObjective E.V_T
        (p.dynamicTopLockInPath E.V_S E.α x₀ n)
        (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n)) s)
      (Set.Icc (max (p.dynamicTopLockInPath E.V_S E.α x₀ n) sbar) 1)) :=
  equilibriumTop_stagePreferences_long_run_with_equilibrium_evidence_of_singleCrossing E
    hV_T_mono (E.V_S_monotone_of_integrand_monotone h_U_S_state_mono)
    hxT_mem hxS_mem hsbar_mem
    h_stage_sender h_stage_target
    hSC hx₀

set_option linter.style.longLine false in
/-- **Path-B + single-crossing Goal 3 wrapper.** Path-B variant of the
strongest paper-facing API: stage primitives + state-monotone `U_S` +
MS single-crossing ⇒ temporary-shock permanent-high persistence with
full path-level equilibrium evidence. -/
theorem equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence_of_singleCrossing_of_U_S_state_monotone
    {p : Params}
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hV_T_mono : Monotone E.V_T)
    (h_U_S_state_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (E.α x) s ≤ p.U_S y (E.α y) s)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        MonotoneOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1))
    (hjoint_lt : max xT xS < 1)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
              Sanctions.I (Set.Icc (max xT xS) 1)
              (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
              ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n) a)
                Sanctions.I
                (E.α (p.dynamicTopLockInPath E.V_S E.α
                        (p.shockPath x₀ N) n))) ∧
      (∀ n, IsMaxOn (fun s' => p.senderDynObjective E.V_S
                                (p.dynamicTopLockInPath E.V_S E.α
                                  (p.shockPath x₀ N) n)
                                (E.α (p.dynamicTopLockInPath E.V_S E.α
                                        (p.shockPath x₀ N) n)) s')
                Sanctions.I
                (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n)) :=
  equilibriumTop_stagePreferences_temporary_shock_permanent_high_with_equilibrium_evidence_of_singleCrossing E
    hV_T_mono (E.V_S_monotone_of_integrand_monotone h_U_S_state_mono)
    hxT_mem hxS_mem hsbar_mem hsbar_pos
    h_stage_sender h_stage_target
    hjoint_lt hSC hx₀_nn hx₀_le

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
