/-
Sanctions/Theory/Shocked/ShockedSingleCrossing.lean

**Step 1 (the gate): single crossing of the Sender objective SURVIVES the
atomless purification shock.**

The shocked Sender dynamic objective is the deterministic `senderDynObjective`
evaluated at the *smeared* continuation `sp.smear V_S`:

  `U_S(x, α x, s) + β_S · (sp.smear V_S)(clipS'(F x s))`.

i.e. it is literally `senderDynObjective` with the continuation `V_S` replaced by
`sp.smear V_S`. So every deterministic single-crossing lemma applies verbatim with
`V := sp.smear V_S` — PROVIDED the smeared continuation keeps a usable Lipschitz
constant. It does: the moving-average smear **preserves** the intrinsic Lipschitz
constant `KS` (`Foundations/MovingAverage.lean`, `movAvgBCF_valueLipschitz`), so the
strong-rally margin `β_S · KS · d < mS` (`d` the rate of the transition's sanction
chord; `d = δ` at the affine law) carries over **unchanged**. Hence the
issue-1 strong-rally route — the *live* (Lipschitz) route, not the dead convexity
route — survives the shock.

This is the disprove-first-verified gate: probe `docs/archive/workflow-scratch/probe_clip_singlecrossing.lean`
found `min ∂J/∂s > 0` on the basin for EVERY value shape and every shock width,
because the margin is Lipschitz-based and the smear preserves Lipschitz constants.

**Rule 1.** `V_S` is the Banach fixed point and `α` the equilibrium argmax — no
fixed strategy. **Rule 3.** No new `ShockedParams` field: the smear-preservation is
a *derived* property of the concrete box kernel (`movAvgShockedParams`), supplied as
a discharged hypothesis, not a postulate. The abstract form takes it as a hypothesis
(satisfied by the box kernel), keeping the assumption surface unchanged.
-/

import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.Shocked.MovingAverageShock
import Sanctions.Foundations.IntervalDominanceOrder

namespace Sanctions
namespace AbstractGame
namespace ShockedParams

open BoundedContinuousFunction Set

variable (sp : Sanctions.AbstractGame.ShockedParams)


/-- **Shocked strict monotonicity from the exact general-`F` chord.** On the high
basin, the shocked Sender objective is strictly increasing whenever each stage-payoff
gain from raising the sanction strictly exceeds the largest discounted continuation
loss permitted by the actual clipped displacement under `F`. The continuation bound
is stated for the smeared value, so no affine transition or separate sanction
Lipschitz modulus for `F` is required. -/
theorem senderDynObjective_shock_strictMonoOn_of_transition_adjusted_chord
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS KS : ℝ}
    (h_transition_adjusted_chord :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
          sp.toParams.β_S * KS *
              dist (Sanctions.clipS' (sp.toParams.F x s₁))
                   (Sanctions.clipS' (sp.toParams.F x s₂))
            < sp.toParams.U_S x (α x) s₂ - sp.toParams.U_S x (α x) s₁)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS) :
    ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
      StrictMonoOn
        (fun s => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s)
        Sanctions.I := by
  intro x hx
  have hmax : max x (1 : ℝ) = 1 := max_eq_right hx.2
  have hchord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x 1),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x 1), s₁ < s₂ →
          sp.toParams.β_S * KS *
              dist (Sanctions.clipS' (sp.toParams.F x s₁))
                   (Sanctions.clipS' (sp.toParams.F x s₂))
            < sp.toParams.U_S x (α x) s₂ - sp.toParams.U_S x (α x) s₁ := by
    rw [hmax]
    exact h_transition_adjusted_chord x hx
  have hmono :=
    sp.toParams.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
      (V_S := sp.smear V_S) (α := α) (x := x) (sbar := 1) (K := KS)
      hchord h_smear_lip
  rw [hmax] at hmono
  exact hmono

/-- **Shocked strong-rally strict monotonicity at a free sanction rate
(general in `F`).** Same conclusion as the affine form
`senderDynObjective_shock_strictMonoOn_of_strong_rally`
(`Examples/AffineInstance/LockInShocked.lean`), with the affine pin replaced
by an upper chord of the actual transition at a rate `d`: on the basin,
`|F(x,s₂) − F(x,s₁)| ≤ d·(s₂ − s₁)`, so one more unit of sanction moves next
period's political state by at most `d`. Together with the stage lower slope
`mS` and the margin `β_S · KS · d < mS`, it implies the exact
transition-adjusted chord: the stage gain from a higher sanction beats the
largest discounted continuation loss.

Round BG (2026-10-06): the rate used to be the inert slot `p.δ`, which has
no general-`F` meaning; it is now an implicit rate `d`. The affine forms in
`Examples/AffineInstance/LockInShocked.lean` (the strict monotonicity, the
single crossing and the dynamic-rule monotonicity) are the instance
`d := δ`: under the affine law the sanction chord is exact,
`|F(x,s₂) − F(x,s₁)| = δ·(s₂ − s₁)` (BG2.6). The hypothesis
`0 ≤ KS` was dropped: it follows from `h_smear_lip`
(`ValueLipschitzWith.nonneg`). No sign of `d` is needed.
The paper-facing general-`F` route is
`senderDynObjective_shock_strictMonoOn_of_transition_adjusted_chord`, which
uses the actual transition displacement and needs no sanction-coordinate
modulus at all. -/
theorem senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS mS KS d : ℝ}
    (hF_chord : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
          |sp.toParams.F x s₂ - sp.toParams.F x s₁| ≤ d * (s₂ - s₁))
    (hS_margin : sp.toParams.β_S * KS * d < mS)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS)
    (h_stage_full : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        Params.LowerSlopeOn (fun s => sp.toParams.U_S x (α x) s) (Set.Icc (0 : ℝ) 1) mS) :
    ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
      StrictMonoOn (fun s => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s)
        Sanctions.I := by
  apply sp.senderDynObjective_shock_strictMonoOn_of_transition_adjusted_chord
    (h_smear_lip := h_smear_lip)
  intro x hx s₁ hs₁ s₂ hs₂ hlt
  have hle : s₁ ≤ s₂ := le_of_lt hlt
  have h_stage_diff : mS * (s₂ - s₁)
      ≤ sp.toParams.U_S x (α x) s₂ - sp.toParams.U_S x (α x) s₁ :=
    h_stage_full x hx s₁ hs₁ s₂ hs₂ hle
  have h_F_lip :
      dist (Sanctions.clipS' (sp.toParams.F x s₁))
          (Sanctions.clipS' (sp.toParams.F x s₂))
        ≤ d * (s₂ - s₁) :=
    calc
      dist (Sanctions.clipS' (sp.toParams.F x s₁))
          (Sanctions.clipS' (sp.toParams.F x s₂))
          ≤ |sp.toParams.F x s₁ - sp.toParams.F x s₂| :=
        Sanctions.clipS'_lipschitz_dist _ _
      _ = |sp.toParams.F x s₂ - sp.toParams.F x s₁| := abs_sub_comm _ _
      _ ≤ d * (s₂ - s₁) :=
        hF_chord x hx s₁ hs₁ s₂ hs₂ hle
  calc
    sp.toParams.β_S * KS *
          dist (Sanctions.clipS' (sp.toParams.F x s₁))
            (Sanctions.clipS' (sp.toParams.F x s₂))
        ≤ sp.toParams.β_S * KS * (d * (s₂ - s₁)) :=
      mul_le_mul_of_nonneg_left h_F_lip
        (mul_nonneg sp.toParams.β_S_mem.1 h_smear_lip.nonneg)
    _ = (sp.toParams.β_S * KS * d) * (s₂ - s₁) := by ring
    _ < mS * (s₂ - s₁) :=
      mul_lt_mul_of_pos_right hS_margin (sub_pos.mpr hlt)
    _ ≤ sp.toParams.U_S x (α x) s₂ - sp.toParams.U_S x (α x) s₁ :=
      h_stage_diff


/-- **Shocked single crossing from the exact general-`F` chord.** The exact
transition-adjusted chord makes the shocked Sender objective strictly increasing in
the sanction at every basin state; interval dominance then upgrades this pointwise
ordering to Milgrom--Shannon single crossing in `(sanction; state)`. -/
theorem senderDynObjective_shock_singleCrossingOn_of_transition_adjusted_chord
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS KS : ℝ}
    (h_transition_adjusted_chord :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
          sp.toParams.β_S * KS *
              dist (Sanctions.clipS' (sp.toParams.F x s₁))
                   (Sanctions.clipS' (sp.toParams.F x s₂))
            < sp.toParams.U_S x (α x) s₂ - sp.toParams.U_S x (α x) s₁)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s) := by
  apply Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono
    (S := Sanctions.I) (T := Set.Icc (max xT xS) 1)
    (F := fun s x => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s)
  · exact convex_Icc _ _
  · intro x hx
    exact sp.senderDynObjective_shock_strictMonoOn_of_transition_adjusted_chord
      h_transition_adjusted_chord h_smear_lip x hx

/-- **Shocked single crossing, general transition (`_generalF` sibling, cross-partial
route).** The shocked Sender objective satisfies Milgrom–Shannon `SingleCrossingOn`
in `(sanction; state)` on the basin for ANY transition law `F` — no affine pin, and
no chord bound on `F` either. Route: the hF-free deterministic cross-partial engine
(Milgrom–Shannon 1994 Thm 6 / Topkis 1998 Thm 2.6.1, saturated-α form, mirroring
`hSC_on_of_cross_partial_nonneg_saturatedAlpha`) applied at the *smeared*
continuation `sp.smear V_S`. Hypotheses (all engine hypotheses stated at the smeared
value, R43-style `α₀` auto-extracted at the basin pivot `max xT xS`):

1. `h_saturated` — the equilibrium Target policy is saturated (constant) on the
   basin, equal to its value at the pivot;
2. `h_hasDerivAt` — a state-derivative witness `g_x` for the saturated-form shocked
   objective (C¹ in the state on the basin);
3. `h_cross` — the cross-partial monotonicity `s ≤ s' ⇒ g_x s x ≤ g_x s' x`
   (`∂²/∂s∂x ≥ 0` of the shocked objective).

The smear enters only through the objective inside the derivative witness, so the
statement is fully F-parametric. -/
theorem senderDynObjective_shock_singleCrossingOn_of_cross_partial_generalF
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS : ℝ} {g_x : ℝ → ℝ → ℝ}
    (h_saturated : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x = α (max xT xS))
    (h_hasDerivAt : ∀ s ∈ Sanctions.I, ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        HasDerivAt
          (fun y => sp.toParams.senderDynObjective (sp.smear V_S) y (α (max xT xS)) s)
          (g_x s x) x)
    (h_cross : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I, s ≤ s' → g_x s x ≤ g_x s' x) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s) := by
  -- Step 1: increasing differences for the saturated-form shocked objective.
  have hID : Sanctions.MilgromShannon.IncreasingDifferencesOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x =>
        sp.toParams.senderDynObjective (sp.smear V_S) x (α (max xT xS)) s) := by
    apply Sanctions.MilgromShannon.IncreasingDifferencesOn.of_smooth_cross_partial_nonneg_on
      (f_x := g_x)
    · exact convex_Icc _ _
    · intro s hs x hx; exact h_hasDerivAt s hs x hx
    · exact h_cross
  -- Step 2: ID ⇒ SC on the localized rectangle.
  have hSC_sat := hID.toSingleCrossingOn
  -- Step 3: transfer SC from the saturated form to the `α x` form on the basin.
  intro x y t t' hx hy hxy ht ht' htt
  have hSC_pair := hSC_sat hx hy hxy ht ht' htt
  simp only at hSC_pair
  refine ⟨fun h_weak => ?_, fun h_strict => ?_⟩
  · simp only at h_weak ⊢
    rw [h_saturated t' ht']
    exact hSC_pair.1 (by rw [← h_saturated t ht]; exact h_weak)
  · simp only at h_strict ⊢
    rw [h_saturated t' ht']
    exact hSC_pair.2 (by rw [← h_saturated t ht]; exact h_strict)


/-- **Shocked Target persistence, general transition (`_generalF` sibling,
combined-chord/MS route).** Same conclusion as
`targetSanctionObjective_shock_monotoneOn_of_loss_offset` — the shocked Target
objective is non-decreasing in the sanction on the basin's high-sanction range —
for ANY transition law `F`, with no affine pin and no chord bound on `F`. Route:
the hF-free combined-chord argument (`targetCombinedChordOn_of_stage_flip`
mechanics) at the smeared continuation, using only the structural transition
fields already in `Params`: `s ≥ x` keeps `F(x,s) ≥ F(x,x) = x` in the range
`[x, 1]` (`F_diag` + `F_mono_s`), where the smeared continuation is assumed
non-decreasing, and `F_mem` keeps the next state feasible so clipping is the
identity. Hypotheses:

1. `hx_I` — the basin state is feasible (`x ∈ [0,1]`, a domain restatement);
2. `h_stage` — the Target stage payoff has non-negative sanction chords on the
   range (the `mT ≥ β_T·KT·δ ≥ 0` instance of the affine theorem's stage slope);
3. `h_smear_mono` — the SMEARED continuation `sp.smear V_T` is non-decreasing on
   the reachable range `[x, 1]` (the hF-free engine's carrier-monotonicity
   hypothesis `hV_T_mono_carrier`, stated at the smeared value).

Replaces the Lipschitz pair (`KT`, margin) of the affine route with the ordinal
monotone-continuation hypothesis of the general-`F` deterministic route. -/
theorem targetSanctionObjective_shock_monotoneOn_of_smear_mono_generalF
    {V_T : SBCF} {α : ℝ → ℝ} {x sbar : ℝ}
    (hx_I : x ∈ Sanctions.I)
    (h_stage : Params.LowerSlopeOn (fun s => sp.toParams.U_T x (α x) s)
      (Set.Icc (max x sbar) 1) 0)
    (h_smear_mono : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
      y₁.val ∈ Set.Icc x 1 → y₂.val ∈ Set.Icc x 1 → y₁ ≤ y₂ →
        sp.smear V_T y₁ ≤ sp.smear V_T y₂) :
    MonotoneOn (fun s => sp.toParams.targetSanctionObjective (sp.smear V_T) x (α x) s)
      (Set.Icc (max x sbar) 1) := by
  intro s₁ hs₁ s₂ hs₂ hle
  -- Stage chord: non-negative from the zero lower slope.
  have h_stage_chord : (0 : ℝ) * (s₂ - s₁)
      ≤ sp.toParams.U_T x (α x) s₂ - sp.toParams.U_T x (α x) s₁ :=
    h_stage s₁ hs₁ s₂ hs₂ hle
  -- Geometry: `s_i ≥ x`, everything feasible.
  have hx_lo : (0 : ℝ) ≤ x := hx_I.1
  have hx_hi : x ≤ 1 := hx_I.2
  have hs₁_ge_x : x ≤ s₁ := le_trans (le_max_left _ _) hs₁.1
  have hs₂_ge_x : x ≤ s₂ := le_trans (le_max_left _ _) hs₂.1
  have hs₁_I : s₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx_lo hs₁_ge_x, hs₁.2⟩
  have hs₂_I : s₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx_lo hs₂_ge_x, hs₂.2⟩
  have hx_I01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx_lo, hx_hi⟩
  -- Next states: feasible, above `x`, ordered (F2–F4, no affine structure).
  have hF₁_mem : sp.toParams.F x s₁ ∈ Set.Icc (0 : ℝ) 1 :=
    sp.toParams.F_mem x s₁ hx_I01 hs₁_I
  have hF₂_mem : sp.toParams.F x s₂ ∈ Set.Icc (0 : ℝ) 1 :=
    sp.toParams.F_mem x s₂ hx_I01 hs₂_I
  have hF₁_ge_x : x ≤ sp.toParams.F x s₁ := by
    have h : sp.toParams.F x x ≤ sp.toParams.F x s₁ :=
      sp.toParams.F_mono_s x hs₁_ge_x
    rwa [sp.toParams.F_diag x] at h
  have hF₂_ge_x : x ≤ sp.toParams.F x s₂ := by
    have h : sp.toParams.F x x ≤ sp.toParams.F x s₂ :=
      sp.toParams.F_mono_s x hs₂_ge_x
    rwa [sp.toParams.F_diag x] at h
  have hF₁₂ : sp.toParams.F x s₁ ≤ sp.toParams.F x s₂ := sp.toParams.F_mono_s x hle
  -- Clipping is the identity on feasible next states.
  have hclip1_val : (Sanctions.clipS' (sp.toParams.F x s₁)).val = sp.toParams.F x s₁ := by
    change Sanctions.clipS (sp.toParams.F x s₁) = sp.toParams.F x s₁
    unfold Sanctions.clipS
    rw [min_eq_right hF₁_mem.2, max_eq_right hF₁_mem.1]
  have hclip2_val : (Sanctions.clipS' (sp.toParams.F x s₂)).val = sp.toParams.F x s₂ := by
    change Sanctions.clipS (sp.toParams.F x s₂) = sp.toParams.F x s₂
    unfold Sanctions.clipS
    rw [min_eq_right hF₂_mem.2, max_eq_right hF₂_mem.1]
  have hclip1_mem : (Sanctions.clipS' (sp.toParams.F x s₁)).val ∈ Set.Icc x 1 := by
    rw [hclip1_val]; exact ⟨hF₁_ge_x, hF₁_mem.2⟩
  have hclip2_mem : (Sanctions.clipS' (sp.toParams.F x s₂)).val ∈ Set.Icc x 1 := by
    rw [hclip2_val]; exact ⟨hF₂_ge_x, hF₂_mem.2⟩
  have hclip12 : Sanctions.clipS' (sp.toParams.F x s₁)
      ≤ Sanctions.clipS' (sp.toParams.F x s₂) := Sanctions.clipS'_mono hF₁₂
  -- Continuation chord: smeared value is non-decreasing on the reachable range.
  have h_val := h_smear_mono _ _ hclip1_mem hclip2_mem hclip12
  have hβT_nn : (0 : ℝ) ≤ sp.toParams.β_T := sp.toParams.β_T_mem.1
  have h_cont : sp.toParams.β_T * sp.smear V_T (Sanctions.clipS' (sp.toParams.F x s₁))
      ≤ sp.toParams.β_T * sp.smear V_T (Sanctions.clipS' (sp.toParams.F x s₂)) :=
    mul_le_mul_of_nonneg_left h_val hβT_nn
  simp only [Params.targetSanctionObjective]
  linarith


/-- **Shocked dynamic-rule monotonicity from the exact general-`F` chord.** The
exact transition-adjusted chord yields single crossing for the shocked Sender
objective and therefore a non-decreasing greatest optimal sanction along the basin
state order. -/
theorem dynamicTopRealizedRule_shock_monotoneOn_of_transition_adjusted_chord
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS KS : ℝ}
    (h_transition_adjusted_chord :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
          sp.toParams.β_S * KS *
              dist (Sanctions.clipS' (sp.toParams.F x s₁))
                   (Sanctions.clipS' (sp.toParams.F x s₂))
            < sp.toParams.U_S x (α x) s₂ - sp.toParams.U_S x (α x) s₁)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS) :
    MonotoneOn (sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α)
      (Set.Icc (max xT xS) 1) :=
  sp.toParams.dynamicTopRealizedRule_mono_of_singleCrossingOn
    (sp.senderDynObjective_shock_singleCrossingOn_of_transition_adjusted_chord
      h_transition_adjusted_chord h_smear_lip)

/-- **Shocked dynamic-rule monotonicity, general transition (`_generalF` sibling).**
Same conclusion as `dynamicTopRealizedRule_shock_monotoneOn_of_strong_rally` — the
shocked forward-looking Sender's greatest best-response sanction is non-decreasing
in the state on the basin — for ANY transition law, from the cross-partial single
crossing sibling (`senderDynObjective_shock_singleCrossingOn_of_cross_partial_generalF`)
fed into the same hF-free monotone-argmax engine
`dynamicTopRealizedRule_mono_of_singleCrossingOn`. -/
theorem dynamicTopRealizedRule_shock_monotoneOn_of_cross_partial_generalF
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS : ℝ} {g_x : ℝ → ℝ → ℝ}
    (h_saturated : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), α x = α (max xT xS))
    (h_hasDerivAt : ∀ s ∈ Sanctions.I, ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        HasDerivAt
          (fun y => sp.toParams.senderDynObjective (sp.smear V_S) y (α (max xT xS)) s)
          (g_x s x) x)
    (h_cross : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s ∈ Sanctions.I, ∀ s' ∈ Sanctions.I, s ≤ s' → g_x s x ≤ g_x s' x) :
    MonotoneOn (sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α)
      (Set.Icc (max xT xS) 1) :=
  sp.toParams.dynamicTopRealizedRule_mono_of_singleCrossingOn
    (sp.senderDynObjective_shock_singleCrossingOn_of_cross_partial_generalF
      h_saturated h_hasDerivAt h_cross)

end ShockedParams

/-- **The box-kernel smear preserves the value Lipschitz constant.** For the
concrete moving-average `ShockedParams` (`movAvgShockedParams`), if the base value
`V` is `K`-Lipschitz then so is its smear `(movAvgShockedParams q hh).smear V`, with
the SAME `K`. This discharges the `h_smear_lip` hypothesis of the gate theorems from
the base value's Lipschitzness — no new assumption. (Reduces to the Foundations
lemma `movAvgBCF_valueLipschitz`.) -/
theorem movAvgShockedParams_smear_valueLipschitz
    (q : Params) {h : ℝ} (hh : 0 < h) {V : SBCF} {K : ℝ} (hK : 0 ≤ K)
    (hVK : Params.ValueLipschitzWith V K) :
    Params.ValueLipschitzWith ((movAvgShockedParams q hh).smear V) K := by
  intro z₁ z₂
  rw [movAvgShockedParams_smear]
  exact Sanctions.movAvgBCF_valueLipschitz hh V hK hVK z₁ z₂


/-- **Box-kernel witness for the exact general-`F` shocked chord.** A Lipschitz
bound on the base value is preserved by the moving-average smear. Thus the exact
transition-adjusted chord, stated using the actual displacement under `q.F`, directly
delivers shocked Sender single crossing without an affine pin or a sanction modulus
for the transition. -/
theorem movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_transition_adjusted_chord
    (q : Params) {h : ℝ} (hh : 0 < h)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS KS : ℝ}
    (hKS_nonneg : 0 ≤ KS)
    (h_transition_adjusted_chord :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
          q.β_S * KS *
              dist (Sanctions.clipS' (q.F x s₁))
                   (Sanctions.clipS' (q.F x s₂))
            < q.U_S x (α x) s₂ - q.U_S x (α x) s₁)
    (hV_S_lip : Params.ValueLipschitzWith V_S KS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x =>
        q.senderDynObjective ((movAvgShockedParams q hh).smear V_S) x (α x) s) :=
  (movAvgShockedParams q hh).senderDynObjective_shock_singleCrossingOn_of_transition_adjusted_chord
      h_transition_adjusted_chord
      (movAvgShockedParams_smear_valueLipschitz q hh hKS_nonneg hV_S_lip)

/-- **Box-kernel dynamic-rule witness for the exact general-`F` chord.** Under the
same base-value Lipschitz bound and exact transition-adjusted chord, the greatest
shocked Sender best response is non-decreasing in the inherited state on the basin. -/
theorem movAvgShockedParams_dynamicTopRealizedRule_shock_monotoneOn_of_transition_adjusted_chord
    (q : Params) {h : ℝ} (hh : 0 < h)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS KS : ℝ}
    (hKS_nonneg : 0 ≤ KS)
    (h_transition_adjusted_chord :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
          q.β_S * KS *
              dist (Sanctions.clipS' (q.F x s₁))
                   (Sanctions.clipS' (q.F x s₂))
            < q.U_S x (α x) s₂ - q.U_S x (α x) s₁)
    (hV_S_lip : Params.ValueLipschitzWith V_S KS) :
    MonotoneOn
      (q.dynamicTopRealizedRule ((movAvgShockedParams q hh).smear V_S) α)
      (Set.Icc (max xT xS) 1) :=
  (movAvgShockedParams q hh).dynamicTopRealizedRule_shock_monotoneOn_of_transition_adjusted_chord
      h_transition_adjusted_chord
      (movAvgShockedParams_smear_valueLipschitz q hh hKS_nonneg hV_S_lip)


/-- **Box-kernel strong-rally gate at a free sanction rate (general in `F`).**
For the box-kernel shocked model, shocked Sender single crossing on the basin
follows from an upper chord of the actual transition `q.F` at a rate `d`, the
stage lower slope `mS`, the margin `β_S · KS · d < mS`, and a `KS`-Lipschitz
bound on the *base* (un-smeared) Sender value. Smear preservation of the
Lipschitz constant is discharged internally, and single crossing follows from
strict monotonicity. The affine witness gate
`movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_strong_rally`
in `Examples/AffineInstance/LockInShocked.lean` is the instance `d := δ`:
under the affine law the sanction chord is exact,
`|F(x,s₂) − F(x,s₁)| = δ·(s₂ − s₁)` (BG2.6).

Round BG (2026-10-06): the rate used to be the inert slot `q.δ`, used only as
a numerical modulus; it is now an implicit rate `d`. The hypothesis `0 ≤ KS`
was dropped: it follows from `hV_S_lip` (`ValueLipschitzWith.nonneg`). The
canonical paper-facing gate is
`movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_transition_adjusted_chord`,
which compares the stage gain with the actual clipped transition
displacement and introduces no sanction-coordinate modulus. -/
theorem movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_strong_rally_generalF
    (q : Params) {h : ℝ} (hh : 0 < h)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS mS KS d : ℝ}
    (hF_chord : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
          |q.F x s₂ - q.F x s₁| ≤ d * (s₂ - s₁))
    (hS_margin : q.β_S * KS * d < mS)
    (hV_S_lip : Params.ValueLipschitzWith V_S KS)
    (h_stage_full : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        Params.LowerSlopeOn (fun s => q.U_S x (α x) s) (Set.Icc (0 : ℝ) 1) mS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x => q.senderDynObjective ((movAvgShockedParams q hh).smear V_S) x (α x) s) := by
  apply Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono
    (S := Sanctions.I) (T := Set.Icc (max xT xS) 1)
    (F := fun s x =>
      q.senderDynObjective ((movAvgShockedParams q hh).smear V_S) x (α x) s)
  · exact convex_Icc _ _
  · intro x hx
    exact (movAvgShockedParams q hh).senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF
      hF_chord hS_margin
      (movAvgShockedParams_smear_valueLipschitz q hh hV_S_lip.nonneg hV_S_lip)
      h_stage_full x hx

/-- **The box-kernel smear preserves monotonicity.** For the concrete moving-average
`ShockedParams` (`movAvgShockedParams`), if the base value `V` is non-decreasing on
`↥S` then so is its smear — the box average of a monotone function along the
monotone window map `t ↦ clipS'(t + shift)` is monotone. This discharges the
`h_smear_mono` hypothesis of the general-`F` Target gate from the base value's
monotonicity — no new assumption. (Reduces to the Foundations lemma
`movAvgBCF_mono`.) -/
theorem movAvgShockedParams_smear_mono
    (q : Params) {h : ℝ} (hh : 0 < h) {V : SBCF}
    (hV_mono : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), y₁ ≤ y₂ → V y₁ ≤ V y₂) :
    ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), y₁ ≤ y₂ →
      (movAvgShockedParams q hh).smear V y₁ ≤ (movAvgShockedParams q hh).smear V y₂ := by
  intro y₁ y₂ hle
  rw [movAvgShockedParams_smear]
  exact Sanctions.movAvgBCF_mono hh V hV_mono y₁ y₂ hle

/-- **Witness Goal-1, general transition (`_generalF` sibling).** For the box-kernel
shocked model, the shocked Target objective is non-decreasing in the sanction on the
basin's high-sanction range (persistence) for ANY transition law, from primitives
stated on the *base* (un-smeared) continuation `V_T`: non-negative Target stage
chords plus base-value monotonicity. The smear-monotonicity is discharged
internally via `movAvgShockedParams_smear_mono`. NOTE: the base monotonicity is
taken on all of `↥S` (not just `[x, 1]`) because the box window at states near the
basin edge averages values from just below the basin; the global form is what the
box kernel transfers. -/
theorem movAvgShockedParams_targetSanctionObjective_shock_monotoneOn_of_smear_mono_generalF
    (q : Params) {h : ℝ} (hh : 0 < h)
    {V_T : SBCF} {α : ℝ → ℝ} {x sbar : ℝ}
    (hx_I : x ∈ Sanctions.I)
    (h_stage : Params.LowerSlopeOn (fun s => q.U_T x (α x) s)
      (Set.Icc (max x sbar) 1) 0)
    (hV_T_mono : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), y₁ ≤ y₂ → V_T y₁ ≤ V_T y₂) :
    MonotoneOn
      (fun s => q.targetSanctionObjective ((movAvgShockedParams q hh).smear V_T) x (α x) s)
      (Set.Icc (max x sbar) 1) :=
  (movAvgShockedParams q hh).targetSanctionObjective_shock_monotoneOn_of_smear_mono_generalF
    hx_I h_stage
    (fun y₁ y₂ _ _ hle => movAvgShockedParams_smear_mono q hh hV_T_mono y₁ y₂ hle)

end AbstractGame
end Sanctions
