/-
Sanctions/Theory/Certificates/TargetSanctionLossOffset.lean

**Audit-41 standard-sanctions Target high-basin discharger.**

The audit-41 critique identified a second sign issue in the
high-basin Target-side assumption: the existing
`LowerSlopeOn (fun s => U_T x (α x) s) ... mT` with positive `mT`
requires `U_T` to be (locally) *non-decreasing* in sanctions on the
high range. Under a standard sanctions model where `U_T_s < 0`
(sanctions hurt the Target), this is false.

The right standard-sanctions mechanism for Target high-basin lock-in
is:

```text
sanctions hurt today  (U_T_s < 0)
but high sanctions preserve / raise the hardline political state x'
which the Target incumbent values  (V_T_x ≥ 0 on the basin)
margin: stage sanction loss ≤ continuation state-value gain
⇒ targetSanctionObjective is non-decreasing in s
```

This file delivers the corresponding Lean discharger:

* `LowerLossSlopeOn f D c` — bounded-loss-slope: `f s₂ - f s₁ ≥
  -c · (s₂ - s₁)` for `s₁ ≤ s₂ ∈ D`. Equivalently, `f`'s downward
  rate in `s` is at most `c`. (Compatible with `U_T_s < 0` of
  magnitude ≤ c.)
* `LowerSlopeOnValue V g` — value function has *minimum upward
  slope*: `V y₂ - V y₁ ≥ g · dist y₁ y₂` for `y₁ ≤ y₂`. Says `V` is
  non-decreasing in the state with at least `g`-slope.
* **`targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value`**
  — the audit-41 Target-side discharger: under `LowerLossSlopeOn` on
  the stage payoff + `LowerSlopeOnValue` on the continuation +
  margin `c ≤ β_T · g · δ`, the dynamic Target's sanction objective
  is non-decreasing in `s` on the basin.

## Rule compliance

**Rule 1.** No strategies. Pure structural property of the dynamic
Target objective.

**Rule 3.** Introduces two new Props (`LowerLossSlopeOn`,
`LowerSlopeOnValue`). Per the user's audit-41 directive ("apply all
the fixes mentioned"), confirmed for inclusion. They are economically
interpretable: bounded sanction-damage rate + minimum continuation
state-value upward slope. Both are direct primitives from a standard
sanctions model with V_T derived as a Banach fixed point under
hardline-state preferences.

**Rule 5.** Fully parametric over `(c, g)`.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Foundations.StokeyLucas
import Sanctions.Foundations.TransitionChords
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Bounded-loss-slope predicate -/

/-- **Bounded-loss-slope predicate.** `f`'s downward rate over `D` is
at most `c`: `f s₂ - f s₁ ≥ -c · (s₂ - s₁)` for `s₁ ≤ s₂ ∈ D`. For
`c ≥ 0`, this is the maximum acceptable rate at which `f` may
decrease.

Compatible with `f` decreasing in `s` (sanctions hurting the Target),
provided the decrease rate is bounded by `c`. -/
def LowerLossSlopeOn (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) : Prop :=
  ∀ s₁ ∈ D, ∀ s₂ ∈ D, s₁ ≤ s₂ →
    f s₂ - f s₁ ≥ -c * (s₂ - s₁)

/-! ## Minimum-upward-slope predicate on value functions -/

/-- **Minimum-upward-slope predicate** on a value function. The value
`V : ↥S →ᵇ ℝ` has minimum upward slope `g ≥ 0`: for `y₁ ≤ y₂ ∈ ↥S`,
`V y₂ - V y₁ ≥ g · dist y₁ y₂`. Captures the economic content
"`V` is *at least* `g`-Lipschitz upward in the state."

Economically: under hardline-state preferences (Target values future
states with high non-compliance), `V_T` is non-decreasing in `x` with
slope ≥ `g`. -/
def LowerSlopeOnValue
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (g : ℝ) : Prop :=
  ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
    y₁ ≤ y₂ → g * dist y₁ y₂ ≤ V y₂ - V y₁

/-- **Audit-44 localized minimum-upward-slope predicate.** Same as
`LowerSlopeOnValue` but only required to hold on a sub-interval of the
state space (parameterized by a set `B ⊆ ℝ` containing the basin range).
Replaces the global form in paper-facing certificates so that the
"`V_T` valued higher at higher states" assumption is only required on
the high-political basin, not on the entire `[0, 1]`. Economically:
the Target incumbent values future high-noncompliance states only
within the high basin, not as universal welfare. -/
def LowerSlopeOnValueOn
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (B : Set ℝ) (g : ℝ) : Prop :=
  ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
    y₁.val ∈ B → y₂.val ∈ B → y₁ ≤ y₂ →
      g * dist y₁ y₂ ≤ V y₂ - V y₁

/-- **Global-to-local adapter** for `LowerSlopeOnValue`. A globally
minimum-upward-slope value function is also locally so on any subset
`B ⊆ ℝ`. -/
theorem LowerSlopeOnValue.toOn
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {g : ℝ}
    (h : LowerSlopeOnValue V g) (B : Set ℝ) :
    LowerSlopeOnValueOn V B g := by
  intro y₁ y₂ _ _ hle
  exact h y₁ y₂ hle

/-! ## The audit-41 Target-side discharger -/


/-- **General-`F` Target high-basin discharger (per equilibrium).**

Affine-free sibling of
`targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value_on`.
`hF` is deleted; the transition enters only through
`SanctionLowerChord p.F dlo` — raising the sanction by `Δ` raises next
period's political state by *at least* `dlo·Δ` — and the loss-offset margin is
denominated in `dlo` rather than `δ`.

In English: on the high basin the Target's *joint* payoff (this period's
sanction loss plus the discounted continuation value of the entrenchment the
sanction buys) is nondecreasing in the sanction, provided the stage loss rate
`c` is covered by the continuation gain `β_T · g · dlo` that the extra sanction
actually delivers.

**Why `0 ≤ g` appears here and not in the affine sibling.** The transition now
enters as an inequality, and scaling an inequality by `g` reverses it when
`g < 0`. Under the affine law that step is an equality, so the sign cannot
matter. Generality in `F` is exactly what makes the sign of the
continuation-gain rate load-bearing. -/
theorem targetSanctionObjective_mono_of_lowerChord_loss_offset_on
    {dlo : ℝ}
    (hchord : Sanctions.TransitionChords.SanctionLowerChord p.F dlo)
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT x sbar : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hx_mem : x ∈ Set.Icc xT (1 : ℝ))
    {c g : ℝ}
    (h_stage_loss :
      LowerLossSlopeOn (fun s => p.U_T x (α x) s)
        (Set.Icc (max x sbar) 1) c)
    (hV_gain_on : LowerSlopeOnValueOn V_T (Set.Icc xT 1) g)
    (hg_nn : 0 ≤ g)
    (hmargin : c ≤ p.β_T * g * dlo) :
    MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
      (Set.Icc (max x sbar) 1) := by
  intro s₁ hs₁ s₂ hs₂ hs_le
  unfold targetSanctionObjective
  have hβT_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have hx_I : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hxT_mem.1 hx_mem.1, hx_mem.2⟩
  have hs₁_ge_x : x ≤ s₁ := le_trans (le_max_left _ _) hs₁.1
  have hs₂_ge_x : x ≤ s₂ := le_trans (le_max_left _ _) hs₂.1
  have hs₁_I : s₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx_I.1 hs₁_ge_x, hs₁.2⟩
  have hs₂_I : s₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx_I.1 hs₂_ge_x, hs₂.2⟩
  have hF1_mem : p.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem x s₁ hx_I hs₁_I
  have hF2_mem : p.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem x s₂ hx_I hs₂_I
  have hF1_ge_x : x ≤ p.F x s₁ := by
    have h : p.F x x ≤ p.F x s₁ := p.F_mono_s x hs₁_ge_x
    rwa [p.F_diag x] at h
  have hF2_ge_x : x ≤ p.F x s₂ := by
    have h : p.F x x ≤ p.F x s₂ := p.F_mono_s x hs₂_ge_x
    rwa [p.F_diag x] at h
  have hF12 : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hs_le
  have hclip1_val : (Sanctions.clipS' (p.F x s₁)).val = p.F x s₁ := by
    change Sanctions.clipS (p.F x s₁) = p.F x s₁
    unfold Sanctions.clipS
    rw [min_eq_right hF1_mem.2, max_eq_right hF1_mem.1]
  have hclip2_val : (Sanctions.clipS' (p.F x s₂)).val = p.F x s₂ := by
    change Sanctions.clipS (p.F x s₂) = p.F x s₂
    unfold Sanctions.clipS
    rw [min_eq_right hF2_mem.2, max_eq_right hF2_mem.1]
  have hclip1_mem : (Sanctions.clipS' (p.F x s₁)).val ∈ Set.Icc xT 1 := by
    rw [hclip1_val]; exact ⟨le_trans hx_mem.1 hF1_ge_x, hF1_mem.2⟩
  have hclip2_mem : (Sanctions.clipS' (p.F x s₂)).val ∈ Set.Icc xT 1 := by
    rw [hclip2_val]; exact ⟨le_trans hx_mem.1 hF2_ge_x, hF2_mem.2⟩
  have hclip12 : Sanctions.clipS' (p.F x s₁) ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono hF12
  have h_stage_chord := h_stage_loss s₁ hs₁ s₂ hs₂ hs_le
  have h_val_chord :=
    hV_gain_on (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
      hclip1_mem hclip2_mem hclip12
  have h_dist :
      dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
        = p.F x s₂ - p.F x s₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, hclip1_val, hclip2_val, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [h_dist] at h_val_chord
  -- **The one replaced step**: affine displacement becomes the lower chord.
  have hchord' : dlo * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁ :=
    hchord hx_I hs₁_I hs₂_I hs_le
  have h_diff_nn : 0 ≤ s₂ - s₁ := by linarith
  have h_margin_chord : c * (s₂ - s₁) ≤ p.β_T * g * dlo * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right hmargin h_diff_nn
  have h_gain_lb : g * (dlo * (s₂ - s₁)) ≤ g * (p.F x s₂ - p.F x s₁) :=
    mul_le_mul_of_nonneg_left hchord' hg_nn
  have h_gain_scaled :
      p.β_T * (g * (dlo * (s₂ - s₁)))
        ≤ p.β_T * (g * (p.F x s₂ - p.F x s₁)) :=
    mul_le_mul_of_nonneg_left h_gain_lb hβT_nn
  have h_translate :
      p.β_T * g * dlo * (s₂ - s₁) = p.β_T * (g * (dlo * (s₂ - s₁))) := by ring
  have h_val_scaled :
      p.β_T * (g * (p.F x s₂ - p.F x s₁))
        ≤ p.β_T * (V_T (Sanctions.clipS' (p.F x s₂))
                    - V_T (Sanctions.clipS' (p.F x s₁))) :=
    mul_le_mul_of_nonneg_left h_val_chord hβT_nn
  linarith

/-- **General-`F` one-sided thresholds constructor — drop-in replacement for
`of_stage_lowerSlopes_compliance_target_on`.**

Identical shape to the affine constructor, with `hF` deleted and the transition
entering only through two chord rates:

* `hchord_lo` — `SanctionLowerChord p.F dlo`: an extra unit of sanction raises
  next period's political state by at least `dlo` (Target leg);
* `hF_chord` — a range-restricted sanction upper chord at rate `d`: on the
  Sender's own comparison range the same move raises it by at most `d`
  (Sender leg).

Each margin is then denominated in its own rate — `p.β_S · K_S · d < m_S`
(the Sender's discounted continuation sensitivity is strictly dominated by the
Sender's stage gain rate) and `c ≤ p.β_T · g · dlo` (the Target's stage loss
rate is covered by the continuation gain the sanction buys).

`..._recovered` below checks that the affine constructor is the
`d = dlo = p.δ` instance, so nothing is lost by deleting `hF`. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on_generalF
    {d dlo : ℝ}
    (hchord_lo : Sanctions.TransitionChords.SanctionLowerChord p.F dlo)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * d < mS)
    (hF_chord :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
          ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ ≤ s₂ →
            |p.F x s₂ - p.F x s₁| ≤ d * (s₂ - s₁))
    (hV_S_lip : ValueLipschitzWith V_S KS)
    {c g : ℝ}
    (h_stage_loss_T :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (α x) s)
          (Set.Icc (max x sbar) 1) c)
    (hV_T_gain_on : LowerSlopeOnValueOn V_T (Set.Icc xT 1) g)
    (hg_nn : 0 ≤ g)
    (h_margin : c ≤ p.β_T * g * dlo)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)) mS) :
    p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar where
  xT_mem := hxT_mem
  xS_mem := hxS_mem
  sbar_mem := hsbar_mem
  sender_likes_to_threshold := fun x hx =>
    p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
      (p.sender_transition_adjusted_chord_of_upperChordOn_lowerSlope
        hKS_nonneg (hF_chord x hx) hS_margin (h_stage_sender x hx))
      hV_S_lip
  target_likes_high_sanctions := fun x hx =>
    p.targetSanctionObjective_mono_of_lowerChord_loss_offset_on
      hchord_lo hxT_mem hx (h_stage_loss_T x hx) hV_T_gain_on hg_nn h_margin


/-- **General-`F` sibling of the combined-chord threshold constructor (G1).**

The affine twin above consumes `hF : p.F = affineF p.δ` at exactly one place —
the `sender_likes_to_threshold` field — and its Target leg is already ordinal
(`h_target_combined` mentions no `δ`).  So the entire affine dependence of the
constructor is one hypothesis and one margin, and both are replaced here:

* `hF` becomes `hF_chord`, a **sanction upper chord on the sub-pivot range**
  `[0, max x sbar]` at rate `d` — how far one unit of extra sanction can move
  next period's political state, on the range where the threshold argument runs;
* `hS_margin : β_S · K_S · δ < m_S` becomes `β_S · K_S · d < m_S`, the same
  margin with the affine displacement factor replaced by that chord rate.

Nothing else changes.  The transition is otherwise untouched: no `F_mono`, no
curvature, no functional form.

**Why the chord is range-restricted rather than stated on the unit square.** The
affine displacement identity holds on all of `ℝ²`, so a unit-square-scoped chord
(`Foundations.SanctionUpperChord`) would make this theorem *more general in `F`
and strictly less general in domain* — two downstream consumers bind their scalars
with no membership hypotheses and could not supply `x ∈ [0,1]`.  Restricting the
chord to the range the proof actually uses avoids that trade entirely.

**Affine recovery (Rule 5).** `affine_transitionChordPack` discharges `hF_chord`
at `d = δ`, so the affine constructor above is the `d := p.δ` corollary and every
existing witness keeps working unchanged. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlope_sender_and_target_combined_chord_generalF
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mS KS d : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * d < mS)
    (hV_S_lip : ValueLipschitzWith V_S KS)
    (hF_chord :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
          ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ ≤ s₂ →
            |p.F x s₂ - p.F x s₁| ≤ d * (s₂ - s₁))
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
                  (Sanctions.clipS' (p.F x s₂)))
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS) :
    p.OneSidedSanctionPreferenceThresholds V_T V_S α xT xS sbar where
  xT_mem := hxT_mem
  xS_mem := hxS_mem
  sbar_mem := hsbar_mem
  sender_likes_to_threshold := fun x hx =>
    p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
      (p.sender_transition_adjusted_chord_of_upperChordOn_lowerSlope
        hKS_nonneg (hF_chord x hx) hS_margin (h_stage_sender x hx))
      hV_S_lip
  target_likes_high_sanctions := by
    intro x hx s₁ hs₁ s₂ hs₂ hs_le
    unfold Sanctions.AbstractGame.Params.targetSanctionObjective
    exact h_target_combined x hx s₁ hs₁ s₂ hs₂ hs_le

/-! ## Audit-45 Step 4: uniform-in-action stage-bound dischargers

The compliance certificate's stage-bound fields
(`h_stage_target_loss_α`, `h_stage_sender_α`) quantify over every
top equilibrium `E` — paper-facing awkward. The dischargers below
reduce these `∀ E` fields to **uniform-in-action** versions
(stage bound holds for *every* feasible `a ∈ Sanctions.I`, not just
for the specific `E.α x`). The uniform-in-action form is strictly
stronger but much cleaner to state in the paper, and is the natural
discharge from a concrete payoff family. -/

/-- **Audit-45 Step 4 Target stage-loss discharger
(uniform-in-action ⇒ per-E).** If the Target stage payoff has
bounded downward rate `cT` in `s` uniformly over feasible actions
`a ∈ Sanctions.I`, then it holds at the specific `E.α x` for any
top equilibrium `E`. -/
theorem stage_target_loss_at_equilibrium_of_uniform_action_loss
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT sbar cT : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (h_uniform :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        ∀ a ∈ Sanctions.I,
          LowerLossSlopeOn
            (fun s => p.U_T x a s)
            (Set.Icc (max x sbar) 1) cT) :
    ∀ x ∈ Set.Icc xT (1 : ℝ),
      LowerLossSlopeOn
        (fun s => p.U_T x (E.α x) s)
        (Set.Icc (max x sbar) 1) cT := by
  intro x hx
  have hxS : x ∈ Sanctions.S := by
    refine ⟨?_, hx.2⟩
    exact le_trans hxT_mem.1 hx.1
  exact h_uniform x hx (E.α x) (E.α_mem x hxS)

/-- **Audit-45 Step 4 Sender stage-slope discharger
(uniform-in-action ⇒ per-E).** If the Sender stage payoff has
bounded lower slope `mS` in `s` uniformly over feasible actions
`a ∈ Sanctions.I`, then it holds at the specific `E.α x` for any
top equilibrium `E`. -/
theorem stage_sender_slope_at_equilibrium_of_uniform_action_slope
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xS sbar mS : ℝ}
    (hxS_mem : xS ∈ Sanctions.I)
    (h_uniform :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        ∀ a ∈ Sanctions.I,
          LowerSlopeOn
            (fun s => p.U_S x a s)
            (Set.Icc (0 : ℝ) (max x sbar)) mS) :
    ∀ x ∈ Set.Icc xS (1 : ℝ),
      LowerSlopeOn
        (fun s => p.U_S x (E.α x) s)
        (Set.Icc (0 : ℝ) (max x sbar)) mS := by
  intro x hx
  have hxS : x ∈ Sanctions.S := by
    refine ⟨?_, hx.2⟩
    exact le_trans hxS_mem.1 hx.1
  exact h_uniform x hx (E.α x) (E.α_mem x hxS)

end Params
end AbstractGame

/-! ## Round-11 Priority 1: C¹ discharger for `LowerLossSlopeOn`

A common case in concrete sanctions models is that the user has a
C¹ stage payoff together with a pointwise lower bound on its partial
derivative in `s`: `∂U_T/∂s(x, a, s) ≥ −cT`. This C¹ form is
paper-stateable ("sanctions hurt the Target's stage welfare at rate
at most `cT`") and strictly weaker than synthesizing the
discrete-chord `LowerLossSlopeOn` predicate by hand.

The discharger below converts the C¹ form into `LowerLossSlopeOn`
via the standard mean-value theorem (mathlib's
`Convex.mul_sub_le_image_sub_of_le_deriv` with `C := -c`). Pure
discharger — no new project assumption introduced.

## Rule compliance
* Rule 1 (optimal strategies): structural — no strategy fixings.
* Rule 3: pure discharger (no new field on the assumption surface);
  the user supplies a strictly weaker C¹ primitive.
* Rule 5: fully parametric over the derivative function `f'` and
  the bound constant `c`.
* Rule 8: human-language paraphrase below; "if the stage payoff's
  slope in `s` is bounded below by `−c`, then `f` decreases in `s`
  at rate at most `c`".
-/

namespace AbstractGame
namespace Params

/-- **Round-11 Priority 1: C¹ discharger for `LowerLossSlopeOn`.**
From a convex domain `D`, a pointwise derivative `f' s` of `f` at
every `s ∈ D` (via `HasDerivAt`), and a uniform lower bound
`−c ≤ f' s` on `D`, conclude `LowerLossSlopeOn f D c`.

Economically: a stage payoff with derivative `∂U/∂s ≥ −c` on the
domain decreases in sanctions at rate at most `c`, which is exactly
what the discrete-chord `LowerLossSlopeOn` predicate says.

Proof is a one-line application of the mathlib mean-value-theorem
lemma `Convex.mul_sub_le_image_sub_of_le_deriv` specialized to
`C := -c`. -/
theorem LowerLossSlopeOn.of_hasDerivAt_lowerBound
    {f : ℝ → ℝ} {D : Set ℝ} {c : ℝ} {f' : ℝ → ℝ}
    (hD : Convex ℝ D)
    (hf_diff : ∀ s ∈ D, HasDerivAt f (f' s) s)
    (hf_lower : ∀ s ∈ D, -c ≤ f' s) :
    LowerLossSlopeOn f D c := by
  intro s₁ hs₁ s₂ hs₂ hs_le
  -- Continuity on D from pointwise differentiability.
  have hf_contOn : ContinuousOn f D :=
    fun s hs => (hf_diff s hs).continuousAt.continuousWithinAt
  -- Differentiability on the interior (a fortiori on D).
  have hf_diffOn : DifferentiableOn ℝ f (interior D) := by
    intro s hs
    exact (hf_diff s (interior_subset hs)).differentiableAt.differentiableWithinAt
  -- The mathlib deriv equals our supplied f' at every point in the interior.
  have hf'_ge_deriv : ∀ s ∈ interior D, -c ≤ deriv f s := by
    intro s hs
    have hd : deriv f s = f' s := (hf_diff s (interior_subset hs)).deriv
    rw [hd]; exact hf_lower s (interior_subset hs)
  have hmvt := hD.mul_sub_le_image_sub_of_le_deriv
    hf_contOn hf_diffOn hf'_ge_deriv s₁ hs₁ s₂ hs₂ hs_le
  -- hmvt : -c * (s₂ - s₁) ≤ f s₂ - f s₁
  -- Goal:  f s₂ - f s₁ ≥ -c * (s₂ - s₁)
  linarith

end Params
end AbstractGame

/-! ## Round 40 — C¹ payoff existence wrappers for Target-side scalars

Companion to the Sender-side R40 wrappers in
`Theory/Bellman/InvariantLipBall.lean`. The R39 Phase 2 Foundations
signed-sup/inf lemmas (`cube_sup_unitCube_of_continuous`,
`cube_inf_unitCube_of_continuous`) lift to Target-side existence
certificates for the Target stage-loss rate `c_T` (from continuous
`∂U_T/∂s`) and the Target stage state-slope `g_U` (from continuous
`∂U_T/∂x`).

As with the Sender-side R40 wrappers, these are existence
certificates only — the user still needs the numeric values to
verify the wedge inequalities of \Cref{ass:target_pref}
(`c_T ≤ β_T · g_T · δ`). The wrappers ensure that under C¹ payoff
smoothness, *some* such constants exist; the numeric content is
inherent to the payoff.

## Rule compliance
* Rule 3 symbol-economy: no new primitives; existence certificates
  produced from existing continuity primitives only.
* Rule 5: parametric in the user's partial-derivative function.
* Rule 8: human-language paraphrase below. -/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **R40: existence of Target stage-loss rate `c_T` from a
    continuous claimed partial derivative `∂U_T/∂s`.**

    Under continuity of the user-claimed `∂U_T/∂s : ℝ → ℝ → ℝ → ℝ`
    on the unit cube `[0,1]³`, the existence of a non-negative
    loss-rate `c_T ≥ 0` with
    `-c_T ≤ ∂U_T/∂s(x, a, s)` for all `(x, a, s) ∈ [0,1]³`
    follows from the signed-inf Weierstrass form via
    R39's `cube_inf_unitCube_of_continuous`. Equivalently:
    `−(∂U_T/∂s)` has a finite sup on the cube, and `c_T` can be
    chosen as the `max` of that sup and 0.

    Once obtained, `c_T` enters the loss-offset margin
    `c_T ≤ β_T · g_T · δ` (\Cref{ass:target_pref} Item 3). The
    user-claimed derivative must additionally be verified as the
    actual partial derivative of `U_T` (via `HasDerivAt`) for R11's
    chord-form discharger to apply downstream; that step is
    independent of this existence certificate. -/
theorem exists_c_T_from_continuous_partial_s
    (U_T_partial_s : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        U_T_partial_s xas.1 xas.2.1 xas.2.2)) :
    ∃ c_T : ℝ, 0 ≤ c_T ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          - c_T ≤ U_T_partial_s x a s := by
  obtain ⟨m, hm⟩ := Sanctions.StokeyLucas.cube_inf_unitCube_of_continuous
    h_continuous
  refine ⟨max (-m) 0, le_max_right _ _, ?_⟩
  intro x hx a ha s hs
  have h1 : -max (-m) 0 ≤ -(-m) := by
    have := le_max_left (-m) (0 : ℝ)
    linarith
  have h2 : -(-m) ≤ U_T_partial_s x a s := by
    have := hm x hx a ha s hs; linarith
  linarith

/-- **R40: existence of Target stage state-slope lower bound `g_U`
    from a continuous claimed partial derivative `∂U_T/∂x`.**

    Under continuity of the user-claimed `∂U_T/∂x : ℝ → ℝ → ℝ → ℝ`
    on the unit cube `[0,1]³`, a finite lower bound `g_U` exists
    such that `g_U ≤ ∂U_T/∂x(x, a, s)` for all `(x, a, s) ∈ [0,1]³`.
    This is the signed-inf form of Weierstrass via R39's
    `cube_inf_unitCube_of_continuous`.

    Caveat: this wrapper guarantees only the **existence** of a
    lower bound `g_U`; the resulting `g_U` may be negative. For
    \Cref{ass:target_pref}'s loss-offset margin
    `c_T ≤ β_T · g_T · δ` with `g_T := g_U / (1 − β_T · (1 − δ))`,
    the user needs `g_U > 0` (strict positive lower slope on the
    basin — "the Target's stage payoff strictly rises in the
    political state"). This is genuine economic content that the
    R40 existence certificate cannot guarantee; the user must
    verify that the inf of `∂U_T/∂x` over the basin domain is
    strictly positive. -/
theorem exists_g_U_from_continuous_partial_x
    (U_T_partial_x : ℝ → ℝ → ℝ → ℝ)
    (h_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) =>
        U_T_partial_x xas.1 xas.2.1 xas.2.2)) :
    ∃ g_U : ℝ,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          g_U ≤ U_T_partial_x x a s :=
  Sanctions.StokeyLucas.cube_inf_unitCube_of_continuous h_continuous

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
