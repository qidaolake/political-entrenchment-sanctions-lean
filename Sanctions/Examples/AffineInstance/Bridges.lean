/-
Sanctions/Examples/AffineInstance/Bridges.lean

**The affine transition as a worked instance: monotonicity, Lipschitz bounds,
and the JET equilibrium bridges.**

Twenty-one declarations moved out of `Sanctions/Theory/` on 2026-08-22, the
lower half of the affine tower --- the part the certificate results stand on.

What is here, in English.

* **Sanction monotonicity for each player.** That the Target's sanction
  objective is increasing in the sanction once the discounted continuation gain
  covers the current loss, and that the Sender's dynamic objective is *strictly*
  increasing under the corresponding strict margin. Under the affine law the
  displacement between two sanctions is exactly `delta` times their gap, which
  is what turns the margin inequality into monotonicity in one step.
* **Row-Lipschitz bounds for the joint Target operator.** The pointwise and
  operator-level Lipschitz constants for the coupled Bellman map, in the form
  the contraction argument consumes. Since round BH1.2 (2026-10-06) the two
  operator-level rows are one-line instances of the general-`F` rows in
  `Theory/Bellman/GeneralFOperatorRow.lean`, through the affine sanction chord
  at rate `delta`. The two pointwise bounds stay as they are: they hold at
  every real state, which is off the feasible square a chord speaks about.
* **The one-sided preference thresholds.** That above a threshold sanction the
  Target complies and below it does not --- the object the persistence results
  read off.
* **The JET bridges.** Persistence and shock-response at a feedback Stackelberg
  equilibrium, derived from the stage lower slopes and from the loss-offset
  form, plus the C1 Bellman-system versions.
* **The regular-economy three-goals results** in their statewise and pathwise
  forms.

Each has a general-`F` counterpart in `Theory/` stated over sanction chords ---
a lower rate `dlo` and an upper rate `d` bracketing how fast a sanction moves
the state --- of which the affine law is the pinned-rate member `dlo = d = delta`.

**Why these are in `Examples/` and not `Theory/`.** Every declaration below
carries `hF : p.F = affineF p.delta` in its statement --- the hypothesis that
one unit of sanction moves next period's political state by exactly `delta`, the
same amount at every state and every sanction level. Under Rule 22 that makes
each one affine-restricted by construction, so each is an *instance*, not part
of the general theory.

Nothing is deleted and nothing is weakened: each still type-checks exactly as it
did in `Theory/`, and each still earns its keep as an exhibit of what the affine
law discharges for free. What changed is only where they live, and therefore
what the general theory is allowed to lean on.

Checked before the move (Rule 23, three gates): the citation graph reported no
consumer outside the affine set itself; a textual sweep of `paper/`, `*.md` and
`*.lean` recorded every prose citation, and the paper was synced in the same
round for those it found (Rule 2); and `lake build` is the gate that settles it.
-/

import Sanctions.Theory
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Target dynamic monotonicity from primitive margins.**

Under primitive hypotheses on the *stage* objective lower slope `m`
and the continuation value Lipschitz constant `K`, with margin
inequality `β_T · K · δ ≤ m`, the dynamic Target objective
`s ↦ U_T(x, α x, s) + β_T · V_T(F(x, s))` is non-decreasing on
`[max x sbar, 1]`. -/
theorem targetSanctionObjective_mono_of_stage_lowerSlope_and_V_lipschitz
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {x sbar m K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hmargin : p.β_T * K * p.δ ≤ m)
    (h_stage :
      LowerSlopeOn
        (fun s => p.U_T x (α x) s)
        (Set.Icc (max x sbar) 1)
        m)
    (hV_lip : ValueLipschitzWith V_T K) :
    MonotoneOn
      (fun s => p.targetSanctionObjective V_T x (α x) s)
      (Set.Icc (max x sbar) 1) := by
  intro s₁ hs₁ s₂ hs₂ hle
  have h_stage_diff :
      m * (s₂ - s₁) ≤ p.U_T x (α x) s₂ - p.U_T x (α x) s₁ :=
    h_stage s₁ hs₁ s₂ hs₂ hle
  have hδ_nonneg : (0 : ℝ) ≤ p.δ := le_of_lt p.δ_mem.1
  have hβT_nonneg : (0 : ℝ) ≤ p.β_T := p.β_T_mem.1
  have h_sdiff_nonneg : (0 : ℝ) ≤ s₂ - s₁ := sub_nonneg.mpr hle
  -- F-Lipschitz: dist (clipS' (...s₁)) (clipS' (...s₂)) ≤ δ * (s₂ - s₁)
  have h_F_lip :
      dist (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁))
           (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
        ≤ p.δ * (s₂ - s₁) := by
    have hclip := Sanctions.clipS'_lipschitz_dist
      ((1 - p.δ) * x + p.δ * s₁)
      ((1 - p.δ) * x + p.δ * s₂)
    have habs :
        |((1 - p.δ) * x + p.δ * s₁) - ((1 - p.δ) * x + p.δ * s₂)|
          = p.δ * (s₂ - s₁) := by
      have hexpr :
          ((1 - p.δ) * x + p.δ * s₁) - ((1 - p.δ) * x + p.δ * s₂)
            = -(p.δ * (s₂ - s₁)) := by ring
      rw [hexpr, abs_neg]
      exact abs_of_nonneg (mul_nonneg hδ_nonneg h_sdiff_nonneg)
    linarith [hclip, habs.le, habs.ge]
  -- V_T-Lipschitz applied to F: |V_T (F s₂) - V_T (F s₁)| ≤ K * δ * (s₂ - s₁)
  have h_V_abs :
      |V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
        - V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁))|
        ≤ K * (p.δ * (s₂ - s₁)) := by
    have hVL := hV_lip
      (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁))
      (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
    have hKbnd :
        K * dist (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁))
                 (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
          ≤ K * (p.δ * (s₂ - s₁)) :=
      mul_le_mul_of_nonneg_left h_F_lip hK_nonneg
    exact le_trans hVL hKbnd
  -- Lower bound on V_T (F s₂) - V_T (F s₁): -(K * δ * (s₂ - s₁))
  have h_V_lower :
      -(K * (p.δ * (s₂ - s₁)))
        ≤ V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
          - V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁)) := by
    have hna := neg_abs_le
      (V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
        - V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁)))
    linarith
  -- Multiply by β_T ≥ 0 to get continuation-value bound.
  have h_βV_lower :
      p.β_T * (-(K * (p.δ * (s₂ - s₁))))
        ≤ p.β_T * (V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂))
                  - V_T (Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁))) :=
    mul_le_mul_of_nonneg_left h_V_lower hβT_nonneg
  -- Combine.
  have h_combined_nonneg :
      0 ≤ m * (s₂ - s₁) - p.β_T * (K * (p.δ * (s₂ - s₁))) := by
    have hfactor :
        m * (s₂ - s₁) - p.β_T * (K * (p.δ * (s₂ - s₁)))
          = (m - p.β_T * K * p.δ) * (s₂ - s₁) := by ring
    rw [hfactor]
    exact mul_nonneg (by linarith) h_sdiff_nonneg
  -- Conclude.
  unfold targetSanctionObjective
  simp only [hF, Sanctions.AbstractGame.affineF]
  linarith

/-- **The affine slope wedge implies the exact general-`F` chord.**
Under `F(x,s) = (1-δ)x + δs`, the transition displacement between two
sanctions is at most `δ(s₂-s₁)`. Hence the familiar strict margin
`β_S K δ < m`, together with a stage lower slope `m`, implies the
transition-adjusted chord used by the general theorem above.

Rule 5: this is now the `d := p.δ` corollary of
`sender_transition_adjusted_chord_of_upperChordOn_lowerSlope`.  The
recovery carries no domain side condition, because the affine
displacement identity holds on arbitrary reals — so the general sibling
loses nothing the affine statement had. -/
theorem sender_transition_adjusted_chord_of_affine_lowerSlope
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {α : ℝ → ℝ}
    {x sbar m K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hmargin : p.β_S * K * p.δ < m)
    (h_stage :
      LowerSlopeOn
        (fun s => p.U_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))
        m) :
    ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
      ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ < s₂ →
        p.β_S * K *
            dist (Sanctions.clipS' (p.F x s₁))
                 (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (α x) s₂ - p.U_S x (α x) s₁ := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hsdiff_pos : 0 < s₂ - s₁ := sub_pos.mpr hlt
  have hsdiff_nonneg : 0 ≤ s₂ - s₁ := hsdiff_pos.le
  have hδ_nonneg : (0 : ℝ) ≤ p.δ := p.δ_mem.1.le
  have hFdist :
      dist (Sanctions.clipS' (p.F x s₁))
           (Sanctions.clipS' (p.F x s₂))
        ≤ p.δ * (s₂ - s₁) := by
    rw [hF]
    have hclip := Sanctions.clipS'_lipschitz_dist
      (Sanctions.AbstractGame.affineF p.δ x s₁)
      (Sanctions.AbstractGame.affineF p.δ x s₂)
    have habs :
        |Sanctions.AbstractGame.affineF p.δ x s₁ -
          Sanctions.AbstractGame.affineF p.δ x s₂|
          = p.δ * (s₂ - s₁) := by
      unfold Sanctions.AbstractGame.affineF
      rw [show (1 - p.δ) * x + p.δ * s₁ -
          ((1 - p.δ) * x + p.δ * s₂) =
          -(p.δ * (s₂ - s₁)) by ring, abs_neg]
      exact abs_of_nonneg (mul_nonneg hδ_nonneg hsdiff_nonneg)
    exact hclip.trans_eq habs
  have hβK_nonneg : 0 ≤ p.β_S * K :=
    mul_nonneg p.β_S_mem.1 hK_nonneg
  have hdist_cost :
      p.β_S * K *
          dist (Sanctions.clipS' (p.F x s₁))
               (Sanctions.clipS' (p.F x s₂))
        ≤ p.β_S * K * (p.δ * (s₂ - s₁)) :=
    mul_le_mul_of_nonneg_left hFdist hβK_nonneg
  have hmargin_pair :
      p.β_S * K * (p.δ * (s₂ - s₁)) < m * (s₂ - s₁) := by
    nlinarith
  exact lt_of_lt_of_le (lt_of_le_of_lt hdist_cost hmargin_pair)
    (h_stage s₁ hs₁ s₂ hs₂ hlt.le)

/-- **Sender dynamic strict monotonicity from affine primitive margins.**

Strict version of the Target theorem under the strict margin
inequality `β_S · K · δ < m`. The dynamic Sender objective is
strictly increasing on `[0, max x sbar]`. -/
theorem senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {x sbar m K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hmargin : p.β_S * K * p.δ < m)
    (h_stage :
      LowerSlopeOn
        (fun s => p.U_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))
        m)
    (hV_lip : ValueLipschitzWith V_S K) :
    StrictMonoOn
      (fun s => p.senderDynObjective V_S x (α x) s)
      (Set.Icc (0 : ℝ) (max x sbar)) := by
  apply
    p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
      (p.sender_transition_adjusted_chord_of_affine_lowerSlope
        hF hK_nonneg hmargin h_stage)
      hV_lip

/-! ## 3. Primitive constructor for `OneSidedSanctionPreferenceThresholds`

Parallel of `OneSidedSanctionPreferenceThresholds.of_stage_preferences`,
but discharging both basin fields from primitive lower slopes and
value-Lipschitz constants — *no* `Monotone V_T` / `Monotone V_S`
hypothesis. -/

/-- **Primitive-margin constructor.** Builds an
`OneSidedSanctionPreferenceThresholds` instance from primitive stage
lower slopes (`mT`, `mS`) and primitive continuation-value Lipschitz
constants (`KT`, `KS`), subject to the margin inequalities

```
β_T · KT · δ ≤ mT     (weak, for Target)
β_S · KS · δ < mS     (strict, for Sender)
```

This replaces the `Monotone V_T` and `Monotone V_S` premises of
`of_stage_preferences` with primitive Lipschitz bounds, which can in
turn be discharged at the application site from finite-step Banach
iteration bounds on the value functions. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mT mS KT KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKT_nonneg : 0 ≤ KT)
    (hKS_nonneg : 0 ≤ KS)
    (hT_margin : p.β_T * KT * p.δ ≤ mT)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_T_lip : ValueLipschitzWith V_T KT)
    (hV_S_lip : ValueLipschitzWith V_S KS)
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_T x (α x) s)
          (Set.Icc (max x sbar) 1)
          mT)
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
    p.senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz
      hF hKS_nonneg hS_margin (h_stage_sender x hx) hV_S_lip
  target_likes_high_sanctions := fun x hx =>
    p.targetSanctionObjective_mono_of_stage_lowerSlope_and_V_lipschitz
      hF hKT_nonneg hT_margin (h_stage_target x hx) hV_T_lip

/-! ## Round-13 Priority 3: C¹ discharger for `LowerSlopeOn`

Sender-side analog of the Round-11 Priority-1 Target-loss-offset
discharger (`LowerLossSlopeOn.of_hasDerivAt_lowerBound`). The
`LowerSlopeOn f D m` predicate, used in the certificate's
`h_stage_sender_on` field to say the Sender stage payoff has minimum
upward slope `mS` in `s` on the basin range `[0, max x sbar]`, is
naturally produced from a C¹ partial-derivative lower bound
`∂U_S/∂s(x, a, s) ≥ mS`. Strictly weaker primitive, paper-stateable
in one line ("Sender's per-period sanction-marginal welfare is at
least `mS`").

## Rule compliance
* Rule 1: structural — no strategy fixings.
* Rule 3: pure discharger (no new field, no new hypothesis); the
  user replaces a synthetic discrete-chord Prop with a strictly
  weaker C¹ primitive (category-2 weakening).
* Rule 5: fully parametric over the derivative function and the
  bound constant.
* Rule 8: paraphrase above.
-/

/-- **Pointwise row-Lipschitz of the joint Target integrand**: a
direct algebraic decomposition gives
$|f(V_T, V_S; x, a) - f(V_T', V_S'; x, a)| \leq \beta_T \cdot
\mathrm{dist}\,V_T\,V_T' + L_\sigma(L_U + \beta_T K_V \delta) \cdot
\mathrm{dist}\,V_S\,V_S'$. -/
theorem joint_T_integrand_pointwise_row_lipschitz
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (V_T V_S V_T' V_S' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V)
    (h_σ_lipschitz : ∀ x a, |p.σ_dyn V_S x a - p.σ_dyn V_S' x a|
                              ≤ L_σ * dist V_S V_S')
    (h_U_lipschitz : ∀ x a s s', |p.U_T x a s - p.U_T x a s'|
                                    ≤ L_U * |s - s'|)
    (h_V_T_lipschitz : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
        |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    (x a : ℝ) :
    |p.joint_T_integrand V_T V_S x a - p.joint_T_integrand V_T' V_S' x a|
      ≤ p.β_T * dist V_T V_T'
        + L_σ * (L_U + p.β_T * K_V * p.δ) * dist V_S V_S' := by
  -- Unfold joint_T_integrand
  unfold joint_T_integrand
  -- Restrict to the affine transition (Schur/Lipschitz route uses the affine slope)
  simp only [hF, Sanctions.AbstractGame.affineF]
  -- Set abbreviations
  set s := p.σ_dyn V_S x a with hs_def
  set s' := p.σ_dyn V_S' x a with hs'_def
  set y := Sanctions.clipS' ((1 - p.δ) * x + p.δ * s) with hy_def
  set y' := Sanctions.clipS' ((1 - p.δ) * x + p.δ * s') with hy'_def
  -- Decompose absolute value via triangle inequality
  have h_decomp :
      |p.U_T x a s + p.β_T * V_T y - (p.U_T x a s' + p.β_T * V_T' y')|
        ≤ |p.U_T x a s - p.U_T x a s'|
          + p.β_T * |V_T y - V_T' y'| := by
    have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
    have h_eq : p.U_T x a s + p.β_T * V_T y - (p.U_T x a s' + p.β_T * V_T' y')
              = (p.U_T x a s - p.U_T x a s') + p.β_T * (V_T y - V_T' y') := by ring
    rw [h_eq]
    calc |(p.U_T x a s - p.U_T x a s') + p.β_T * (V_T y - V_T' y')|
        ≤ |p.U_T x a s - p.U_T x a s'| + |p.β_T * (V_T y - V_T' y')| :=
            abs_add_le _ _
      _ = |p.U_T x a s - p.U_T x a s'| + p.β_T * |V_T y - V_T' y'| := by
            rw [abs_mul, abs_of_nonneg hβ_T_nn]
  -- Bound the U_T part: |U_T(s) - U_T(s')| ≤ L_U |s - s'| ≤ L_U L_σ dist V_S V_S'
  have h_U_bound : |p.U_T x a s - p.U_T x a s'| ≤ L_U * L_σ * dist V_S V_S' := by
    calc |p.U_T x a s - p.U_T x a s'|
        ≤ L_U * |s - s'| := h_U_lipschitz x a s s'
      _ ≤ L_U * (L_σ * dist V_S V_S') := by
          apply mul_le_mul_of_nonneg_left (h_σ_lipschitz x a) hL_U_nn
      _ = L_U * L_σ * dist V_S V_S' := by ring
  -- Bound the V_T part: |V_T y - V_T' y'| ≤ K_V * δ * L_σ * dist V_S V_S' + dist V_T V_T'
  have h_V_T_bound : |V_T y - V_T' y'|
      ≤ K_V * p.δ * L_σ * dist V_S V_S' + dist V_T V_T' := by
    -- Triangle: |V_T y - V_T' y'| ≤ |V_T y - V_T y'| + |V_T y' - V_T' y'|
    have h_tri : |V_T y - V_T' y'|
        ≤ |V_T y - V_T y'| + |V_T y' - V_T' y'| := by
      calc |V_T y - V_T' y'|
          = |V_T y - V_T y' + (V_T y' - V_T' y')| := by ring_nf
        _ ≤ |V_T y - V_T y'| + |V_T y' - V_T' y'| := abs_add_le _ _
    -- |V_T y - V_T y'| ≤ K_V * dist y y'
    have h_V_T_part : |V_T y - V_T y'| ≤ K_V * dist y y' := h_V_T_lipschitz y y'
    -- |V_T y' - V_T' y'| ≤ dist V_T V_T' (BCF sup-norm pointwise)
    have h_BCF_part : |V_T y' - V_T' y'| ≤ dist V_T V_T' := by
      have := BoundedContinuousFunction.dist_coe_le_dist (f := V_T) (g := V_T') y'
      rwa [Real.dist_eq] at this
    -- dist y y' ≤ δ * |s - s'| via clipS' 1-Lipschitz
    have h_dist_y : dist y y' ≤ p.δ * |s - s'| := by
      have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
      calc dist y y'
          ≤ |((1 - p.δ) * x + p.δ * s) - ((1 - p.δ) * x + p.δ * s')| :=
              Sanctions.clipS'_lipschitz_dist _ _
        _ = |p.δ * (s - s')| := by ring_nf
        _ = p.δ * |s - s'| := by rw [abs_mul, abs_of_nonneg hδ_nn]
    -- Combine: K_V * dist y y' ≤ K_V * δ * |s - s'| ≤ K_V * δ * L_σ * dist V_S V_S'
    have h_K_V_part :
        K_V * dist y y' ≤ K_V * p.δ * L_σ * dist V_S V_S' := by
      have hδ_nn : 0 ≤ p.δ := le_of_lt p.δ_mem.1
      calc K_V * dist y y'
          ≤ K_V * (p.δ * |s - s'|) := mul_le_mul_of_nonneg_left h_dist_y hK_V_nn
        _ = K_V * p.δ * |s - s'| := by ring
        _ ≤ K_V * p.δ * (L_σ * dist V_S V_S') := by
            apply mul_le_mul_of_nonneg_left (h_σ_lipschitz x a)
            exact mul_nonneg hK_V_nn hδ_nn
        _ = K_V * p.δ * L_σ * dist V_S V_S' := by ring
    linarith [h_tri, mul_le_mul_of_nonneg_left h_dist_y hK_V_nn]
  -- Final combination
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  calc |p.U_T x a s + p.β_T * V_T y - (p.U_T x a s' + p.β_T * V_T' y')|
      ≤ |p.U_T x a s - p.U_T x a s'| + p.β_T * |V_T y - V_T' y'| := h_decomp
    _ ≤ L_U * L_σ * dist V_S V_S'
        + p.β_T * (K_V * p.δ * L_σ * dist V_S V_S' + dist V_T V_T') := by
          apply add_le_add h_U_bound
          exact mul_le_mul_of_nonneg_left h_V_T_bound hβ_T_nn
    _ = p.β_T * dist V_T V_T'
        + L_σ * (L_U + p.β_T * K_V * p.δ) * dist V_S V_S' := by ring

/-! ## Pointwise row-Lipschitz of the joint Target Bellman operator

`T_T_joint V_T V_S x = sSup ((joint_T_integrand V_T V_S x ·) '' I)`.
The pointwise row-Lipschitz bound for `T_T_joint` follows from the
sup-difference inequality applied to the integrand pointwise bound. -/

/-- **Pointwise row-Lipschitz of `T_T_joint`** under primitive
Lipschitz hypotheses. -/
theorem T_T_joint_pointwise_row_lipschitz
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (V_T V_S V_T' V_S' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V)
    (h_σ_lipschitz : ∀ x a, |p.σ_dyn V_S x a - p.σ_dyn V_S' x a|
                              ≤ L_σ * dist V_S V_S')
    (h_U_lipschitz : ∀ x a s s', |p.U_T x a s - p.U_T x a s'|
                                    ≤ L_U * |s - s'|)
    (h_V_T_lipschitz : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
        |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    (h_joint_T_integrand_bdd_V_S :
        ∀ x, BddAbove ((fun a => p.joint_T_integrand V_T V_S x a) '' Sanctions.I))
    (h_joint_T_integrand_bdd_V_S' :
        ∀ x, BddAbove ((fun a => p.joint_T_integrand V_T' V_S' x a) '' Sanctions.I))
    (x : ℝ) :
    |p.T_T_joint V_T V_S x - p.T_T_joint V_T' V_S' x|
      ≤ p.β_T * dist V_T V_T'
        + L_σ * (L_U + p.β_T * K_V * p.δ) * dist V_S V_S' := by
  unfold T_T_joint
  apply Sanctions.abs_sSup_image_sub_sSup_image_le
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
  · intro a _ha
    exact p.joint_T_integrand_pointwise_row_lipschitz hF V_T V_S V_T' V_S'
      hL_U_nn hK_V_nn h_σ_lipschitz h_U_lipschitz
      h_V_T_lipschitz x a
  · exact h_joint_T_integrand_bdd_V_S x
  · exact h_joint_T_integrand_bdd_V_S' x

/-- **Operator-level row-Lipschitz of `jointTargetOp_sub`.**
Pointwise Target row-Lipschitz (`JointLipschitz`) lifted to the BCF
metric via the sup-difference inequality. Bound:

```
dist (jointTargetOp_sub h_inv (V, W)) (jointTargetOp_sub h_inv (V', W'))
  ≤ β_T · dist V V' + (L_σ · (L_U + β_T · K_V · δ)) · dist W W'.
```

The `L_σ · (L_U + β_T · K_V · δ)` term is the standard joint Target
row-Lipschitz coefficient absorbing the σ-mediated V_S-dependence.

`h_V_T_lipschitz_carrier` is the Lipschitz hypothesis on each `V_T`
in the carrier; in practice it is discharged uniformly via
`ValueLipschitz.V_T_valueLipschitzWith_of_contraction` (audit-32
item 1) or via the cone-preservation Banach-iteration argument for
the joint Target Bellman.

**Affine-restricted, and an instance since round BH1.2 (2026-10-06).** `hF`
is used only to produce the sanction upper chord at rate `δ`
(`TransitionChords.affine_sanctionUpperChord`: one unit of sanction moves next
period's state by exactly `δ`, so by at most `δ`). With that chord this is the
general-`F` row `Params.jointTargetOp_sub_row_lipschitz_generalF` at `d = δ`.
Statement unchanged. -/
theorem jointTargetOp_sub_row_lipschitz
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {D : p.ValueClass} (h_inv : D.IsInvariant)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V) (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lipschitz : ∀ V_S V_S' : Val, ∀ x a,
        |p.σ_dyn V_S x a - p.σ_dyn V_S' x a| ≤ L_σ * dist V_S V_S')
    (h_U_lipschitz : ∀ x a s s',
        |p.U_T x a s - p.U_T x a s'| ≤ L_U * |s - s'|)
    (h_V_T_lipschitz_carrier : ∀ V_T : Val, V_T ∈ D.carrier →
        ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
          |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    (V W V' W' : D.Carrier) :
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ p.β_T * dist V V'
        + L_σ * (L_U + p.β_T * K_V * p.δ) * dist W W' := by
  have hchord : Sanctions.TransitionChords.SanctionUpperChord p.F p.δ := by
    rw [hF]; exact Sanctions.TransitionChords.affine_sanctionUpperChord p.δ
  exact p.jointTargetOp_sub_row_lipschitz_generalF hchord h_inv
    hL_U_nn hK_V_nn hL_σ_nn h_σ_lipschitz h_U_lipschitz
    h_V_T_lipschitz_carrier V W V' W'

/-! ## 2. Sender Bellman operator-level distance bound (at fixed `α`)

The simpler tier (i) Sender bound: at fixed leader policy `α`,
`bellmanS_BCF α hα V_S` is `β_S`-Lipschitz in `V_S` at the operator
level. Lifted from `bellmanS_BCF_pointwise_dist` via
`BoundedContinuousFunction.norm_le`. -/

/-- **Carrier-restricted version of `jointTargetOp_sub_row_lipschitz`.**
Takes the σ_dyn-Lipschitz hypothesis in the carrier-restricted form
`SigmaDynLipschitzOn D L_σ` (strictly weaker than the global form).

**Affine-restricted, and an instance since round BH1.2 (2026-10-06).** `hF`
is used only to produce the sanction upper chord at rate `δ`
(`TransitionChords.affine_sanctionUpperChord`). With that chord this is the
two-carrier general-`F` row `ValueClass2.jointTargetOp_sub_row_lipschitz_generalF`
at the homogeneous bridge `D.toValueClass2` and `d = δ`: the `σ_dyn` bound is
transported by `SigmaDynLipschitzOn.toValueClass2`, and the stage bound is
restricted to `S × I × I × I`. The earlier proof repeated the whole lift.
Statement unchanged. -/
theorem jointTargetOp_sub_row_lipschitz_of_carrier
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {D : p.ValueClass} (h_inv : D.IsInvariant)
    {L_σ L_U K_V : ℝ}
    (hL_U_nn : 0 ≤ L_U) (hK_V_nn : 0 ≤ K_V) (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lip : p.SigmaDynLipschitzOn D L_σ)
    (h_U_lipschitz : ∀ x a s s',
        |p.U_T x a s - p.U_T x a s'| ≤ L_U * |s - s'|)
    (h_V_T_lipschitz_carrier : ∀ V_T : Val, V_T ∈ D.carrier →
        ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
          |V_T y₁ - V_T y₂| ≤ K_V * dist y₁ y₂)
    (V W V' W' : D.Carrier) :
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ p.β_T * dist V V'
        + L_σ * (L_U + p.β_T * K_V * p.δ) * dist W W' := by
  have hchord : Sanctions.TransitionChords.SanctionUpperChord p.F p.δ := by
    rw [hF]; exact Sanctions.TransitionChords.affine_sanctionUpperChord p.δ
  exact D.toValueClass2.jointTargetOp_sub_row_lipschitz_generalF hchord
    (D.toValueClass2_IsInvariant h_inv) hL_U_nn hK_V_nn hL_σ_nn
    h_σ_lip.toValueClass2 (fun x _ a _ s _ s' _ => h_U_lipschitz x a s s')
    h_V_T_lipschitz_carrier V V' W W'

/-- **Audit-41 Target high-basin discharger.** The dynamic Target's
sanction objective `targetSanctionObjective V_T x α s` is non-decreasing
in `s` on the basin range `[max x sbar, 1]` provided:

* `h_stage_loss`: the stage payoff `s ↦ U_T(x, α, s)` has bounded
  downward rate `c` (i.e., `LowerLossSlopeOn` with constant `c`).
* `hV_gain`: the continuation value `V_T` has minimum upward slope
  `g` (`LowerSlopeOnValue V_T g`).
* `hmargin`: `c ≤ β_T · g · δ` — the continuation gain dominates the
  stage loss.

Then for any `s₁ ≤ s₂` in `[max x sbar, 1] ⊆ Sanctions.I`:
`targetSanctionObjective(s₂) − targetSanctionObjective(s₁) ≥ 0`.

Replaces the audit-pre-41 monotone-stage-payoff discharger
`targetSanctionObjective_mono_of_stage_mono_and_V_mono` under the
standard sanctions interpretation where `U_T_s < 0`. -/
theorem targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {x sbar : ℝ}
    (hx_mem : x ∈ Sanctions.I)
    {c g : ℝ}
    (h_stage_loss :
      LowerLossSlopeOn (fun s => p.U_T x (α x) s)
        (Set.Icc (max x sbar) 1) c)
    (hV_gain : LowerSlopeOnValue V_T g)
    (hmargin : c ≤ p.β_T * g * p.δ) :
    MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
      (Set.Icc (max x sbar) 1) := by
  intro s₁ hs₁ s₂ hs₂ hs_le
  -- targetSanctionObjective V_T x α s = U_T(x, α, s) + β_T · V_T(clipS'(F))
  -- F(s) = (1-δ)·x + δ·s.
  -- Want: targetSanctionObjective s₁ ≤ targetSanctionObjective s₂.
  -- Equivalently: U_T(s₂) - U_T(s₁) + β_T · (V_T(F(s₂)) - V_T(F(s₁))) ≥ 0.
  unfold targetSanctionObjective
  -- Schur/Lipschitz route: this discharger uses the affine slope.
  simp only [hF, Sanctions.AbstractGame.affineF]
  -- Stage loss bound: U_T(s₂) - U_T(s₁) ≥ -c · (s₂ - s₁).
  have h_stage : p.U_T x (α x) s₂ - p.U_T x (α x) s₁
                  ≥ -c * (s₂ - s₁) := h_stage_loss s₁ hs₁ s₂ hs₂ hs_le
  -- Continuation: V_T(F(s₂)) - V_T(F(s₁)) ≥ g · dist (F(s₁)) (F(s₂)).
  -- F values in S: need x ∈ I and s ∈ I.
  -- s₁, s₂ ∈ [max x sbar, 1] ⊆ [0, 1] = Sanctions.I.
  have hs₁_I : s₁ ∈ Sanctions.I := by
    refine ⟨?_, hs₁.2⟩; exact le_trans (le_max_of_le_left hx_mem.1) hs₁.1
  have hs₂_I : s₂ ∈ Sanctions.I := by
    refine ⟨?_, hs₂.2⟩; exact le_trans (le_max_of_le_left hx_mem.1) hs₂.1
  -- F(s) for s ∈ I, x ∈ I: F = (1-δ)·x + δ·s. Convex combination of x, s ∈ [0,1].
  have hδ_mem : (0 : ℝ) < p.δ := p.δ_mem.1
  have hδ_lt : p.δ < 1 := p.δ_mem.2
  have h1mδ_nn : 0 ≤ 1 - p.δ := by linarith
  have hF_in_I : ∀ s ∈ Sanctions.I,
      (1 - p.δ) * x + p.δ * s ∈ Sanctions.I := by
    intro s hs
    refine ⟨?_, ?_⟩
    · exact add_nonneg (mul_nonneg h1mδ_nn hx_mem.1)
        (mul_nonneg (le_of_lt hδ_mem) hs.1)
    · have h1 : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
        mul_le_mul_of_nonneg_left hx_mem.2 h1mδ_nn
      have h2 : p.δ * s ≤ p.δ * 1 :=
        mul_le_mul_of_nonneg_left hs.2 (le_of_lt hδ_mem)
      linarith
  have hF₁_in_I := hF_in_I s₁ hs₁_I
  have hF₂_in_I := hF_in_I s₂ hs₂_I
  -- clipS' restricted to I is identity (value-wise), so clipS'(F) ∈ ↥S with val = F.
  -- We work with the subtype elements directly.
  set y₁ : ↥(Sanctions.S : Set ℝ) := Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁) with hy₁_def
  set y₂ : ↥(Sanctions.S : Set ℝ) := Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂) with hy₂_def
  -- y₁.val = F(s₁), y₂.val = F(s₂) (clipS' is identity on I, since
  -- clipS y = max 0 (min 1 y), which is `y` for `y ∈ [0,1]`).
  have hclipS_id : ∀ y : ℝ, y ∈ Sanctions.I → Sanctions.clipS y = y := by
    intro y hy
    show max 0 (min 1 y) = y
    rw [min_eq_right hy.2, max_eq_right hy.1]
  have hy₁_val : y₁.val = (1 - p.δ) * x + p.δ * s₁ := by
    show Sanctions.clipS ((1 - p.δ) * x + p.δ * s₁) = (1 - p.δ) * x + p.δ * s₁
    exact hclipS_id _ hF₁_in_I
  have hy₂_val : y₂.val = (1 - p.δ) * x + p.δ * s₂ := by
    show Sanctions.clipS ((1 - p.δ) * x + p.δ * s₂) = (1 - p.δ) * x + p.δ * s₂
    exact hclipS_id _ hF₂_in_I
  -- Order on subtype: y₁ ≤ y₂ ⟺ y₁.val ≤ y₂.val.
  have hy_le : y₁ ≤ y₂ := by
    show y₁.val ≤ y₂.val
    rw [hy₁_val, hy₂_val]
    have : (1 - p.δ) * x + p.δ * s₁ ≤ (1 - p.δ) * x + p.δ * s₂ := by
      have : p.δ * s₁ ≤ p.δ * s₂ :=
        mul_le_mul_of_nonneg_left hs_le (le_of_lt hδ_mem)
      linarith
    exact this
  -- dist y₁ y₂ = |y₂.val - y₁.val| = δ · (s₂ - s₁).
  have h_dist : dist y₁ y₂ = p.δ * (s₂ - s₁) := by
    rw [Subtype.dist_eq, Real.dist_eq, hy₁_val, hy₂_val]
    have h_diff_eq :
        (1 - p.δ) * x + p.δ * s₁ - ((1 - p.δ) * x + p.δ * s₂) = -(p.δ * (s₂ - s₁)) := by
      ring
    rw [h_diff_eq, abs_neg]
    apply abs_of_nonneg
    exact mul_nonneg (le_of_lt hδ_mem) (by linarith)
  -- Continuation: V_T y₂ - V_T y₁ ≥ g · dist y₁ y₂ = g · δ · (s₂ - s₁).
  have h_cont : g * dist y₁ y₂ ≤ V_T y₂ - V_T y₁ := hV_gain y₁ y₂ hy_le
  rw [h_dist] at h_cont
  -- targetSanctionObjective(s₂) - targetSanctionObjective(s₁)
  --   = (U_T(s₂) - U_T(s₁)) + β_T · (V_T(F(s₂)) - V_T(F(s₁)))
  --   ≥ -c·(s₂-s₁) + β_T · g · δ · (s₂-s₁)
  --   = (β_T·g·δ - c) · (s₂-s₁) ≥ 0 (by margin).
  -- Recognize the V_T arguments as y₁, y₂ (goal already in affine form
  -- after the `simp only [hF, affineF]` above).
  change p.U_T x (α x) s₁ + p.β_T * V_T y₁
      ≤ p.U_T x (α x) s₂ + p.β_T * V_T y₂
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_s_diff_nn : 0 ≤ s₂ - s₁ := by linarith
  -- β_T · (V_T y₂ - V_T y₁) ≥ β_T · g · δ · (s₂ - s₁).
  have h_cont_scaled :
      p.β_T * g * p.δ * (s₂ - s₁) ≤ p.β_T * (V_T y₂ - V_T y₁) := by
    have h_step : p.β_T * (g * (p.δ * (s₂ - s₁))) ≤ p.β_T * (V_T y₂ - V_T y₁) :=
      mul_le_mul_of_nonneg_left h_cont hβ_T_nn
    nlinarith [h_step]
  -- Combine via margin c ≤ β_T · g · δ.
  have h_margin_step : -c * (s₂ - s₁) + p.β_T * g * p.δ * (s₂ - s₁) ≥ 0 := by
    have : (p.β_T * g * p.δ - c) * (s₂ - s₁) ≥ 0 := by
      apply mul_nonneg
      · linarith [hmargin]
      · exact h_s_diff_nn
    nlinarith [this]
  -- Final combination.
  nlinarith [h_stage, h_cont_scaled, h_margin_step]

/-! ## Audit-41 wiring into `OneSidedSanctionPreferenceThresholds`

The pre-audit-41 `of_stage_lowerSlopes` discharger uses
`LowerSlopeOn` of `U_T` (requires `U_T_s ≥ 0` on the high range —
backwards under literal compliance). This wiring provides a
compliance-direction variant: takes Phase-5 hypotheses
(`LowerLossSlopeOn` U_T + `LowerSlopeOnValue` V_T + margin) on the
Target side, while keeping the existing Sender side (`LowerSlopeOn`
of U_S; Sender liking sanctions on the low range is the standard
reading). -/

/-- **Audit-41 compliance-direction variant of
`OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes`.**
Replaces the Target-side `LowerSlopeOn` of `U_T` + `ValueLipschitzWith`
+ margin chain with the Phase-5 `LowerLossSlopeOn` + `LowerSlopeOnValue`
+ margin chain, which is sign-correct under literal compliance.

Sender side is unchanged (Sender prefers high sanctions on the low
range under any reading of `a`). -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith V_S KS)
    {c g : ℝ}
    -- Audit-41 Target stage-loss bound: U_T may decrease in s on
    -- the high range with rate at most c.
    (h_stage_loss_T :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (α x) s)
          (Set.Icc (max x sbar) 1) c)
    -- Audit-41 V_T continuation-gain bound: V_T has minimum upward
    -- slope g in the state.
    (hV_T_gain : LowerSlopeOnValue V_T g)
    -- Audit-41 margin: stage loss rate ≤ continuation gain rate.
    (h_margin : c ≤ p.β_T * g * p.δ)
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
    p.senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz
      hF hKS_nonneg hS_margin (h_stage_sender x hx) hV_S_lip
  target_likes_high_sanctions := fun x hx => by
    -- x ∈ Set.Icc xT 1 ⊆ Sanctions.I (since xT ≥ 0 and x ≤ 1).
    have hx_mem : x ∈ Sanctions.I := by
      refine ⟨?_, hx.2⟩
      exact le_trans hxT_mem.1 hx.1
    exact p.targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value
      hF hx_mem (h_stage_loss_T x hx) hV_T_gain h_margin

/-! ## Audit-44 localized variants

The audit-44 critique noted that the global form
`LowerSlopeOnValue V_T g` over all of `↥(Sanctions.S)` is stronger
than needed: the discharger only inspects `V_T` on the transition
image of the high-basin range `[xT, 1]`. The localized variants below
take the strictly weaker `LowerSlopeOnValueOn V_T (Set.Icc xT 1) g`.
The global form is recoverable as a one-step adapter via
`LowerSlopeOnValue.toOn`. -/

/-- **Audit-44 localized Target high-basin discharger.** Same as
`targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value`
but takes the localized `LowerSlopeOnValueOn V_T (Set.Icc xT 1) g`.
The proof shows that the constructed continuation-state subtypes
`y_i.val = (1-δ)·x + δ·s_i` lie in `[xT, 1]` whenever `x ∈ [xT, 1]`
and `s_i ∈ [max x sbar, 1]`, so the localized continuation-gain
inequality is enough. -/
theorem targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value_on
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT x sbar : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hx_mem : x ∈ Set.Icc xT (1 : ℝ))
    {c g : ℝ}
    (h_stage_loss :
      LowerLossSlopeOn (fun s => p.U_T x (α x) s)
        (Set.Icc (max x sbar) 1) c)
    (hV_gain_on : LowerSlopeOnValueOn V_T (Set.Icc xT 1) g)
    (hmargin : c ≤ p.β_T * g * p.δ) :
    MonotoneOn (fun s => p.targetSanctionObjective V_T x (α x) s)
      (Set.Icc (max x sbar) 1) := by
  intro s₁ hs₁ s₂ hs₂ hs_le
  unfold targetSanctionObjective
  -- Schur/Lipschitz route: this discharger uses the affine slope.
  simp only [hF, Sanctions.AbstractGame.affineF]
  -- Stage loss bound.
  have h_stage : p.U_T x (α x) s₂ - p.U_T x (α x) s₁
                  ≥ -c * (s₂ - s₁) := h_stage_loss s₁ hs₁ s₂ hs₂ hs_le
  -- x ∈ Sanctions.I.
  have hx_I : x ∈ Sanctions.I := by
    refine ⟨?_, hx_mem.2⟩; exact le_trans hxT_mem.1 hx_mem.1
  have hs₁_I : s₁ ∈ Sanctions.I := by
    refine ⟨?_, hs₁.2⟩; exact le_trans (le_max_of_le_left hx_I.1) hs₁.1
  have hs₂_I : s₂ ∈ Sanctions.I := by
    refine ⟨?_, hs₂.2⟩; exact le_trans (le_max_of_le_left hx_I.1) hs₂.1
  have hδ_mem : (0 : ℝ) < p.δ := p.δ_mem.1
  have hδ_lt : p.δ < 1 := p.δ_mem.2
  have h1mδ_nn : 0 ≤ 1 - p.δ := by linarith
  have hF_in_I : ∀ s ∈ Sanctions.I,
      (1 - p.δ) * x + p.δ * s ∈ Sanctions.I := by
    intro s hs
    refine ⟨?_, ?_⟩
    · exact add_nonneg (mul_nonneg h1mδ_nn hx_I.1)
        (mul_nonneg (le_of_lt hδ_mem) hs.1)
    · have h1 : (1 - p.δ) * x ≤ (1 - p.δ) * 1 :=
        mul_le_mul_of_nonneg_left hx_I.2 h1mδ_nn
      have h2 : p.δ * s ≤ p.δ * 1 :=
        mul_le_mul_of_nonneg_left hs.2 (le_of_lt hδ_mem)
      linarith
  have hF₁_in_I := hF_in_I s₁ hs₁_I
  have hF₂_in_I := hF_in_I s₂ hs₂_I
  set y₁ : ↥(Sanctions.S : Set ℝ) := Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₁) with hy₁_def
  set y₂ : ↥(Sanctions.S : Set ℝ) := Sanctions.clipS' ((1 - p.δ) * x + p.δ * s₂) with hy₂_def
  have hclipS_id : ∀ y : ℝ, y ∈ Sanctions.I → Sanctions.clipS y = y := by
    intro y hy
    show max 0 (min 1 y) = y
    rw [min_eq_right hy.2, max_eq_right hy.1]
  have hy₁_val : y₁.val = (1 - p.δ) * x + p.δ * s₁ := by
    show Sanctions.clipS ((1 - p.δ) * x + p.δ * s₁) = (1 - p.δ) * x + p.δ * s₁
    exact hclipS_id _ hF₁_in_I
  have hy₂_val : y₂.val = (1 - p.δ) * x + p.δ * s₂ := by
    show Sanctions.clipS ((1 - p.δ) * x + p.δ * s₂) = (1 - p.δ) * x + p.δ * s₂
    exact hclipS_id _ hF₂_in_I
  -- y_i.val ≥ x ≥ xT (since s_i ≥ max x sbar ≥ x, convex combo of x and s_i with x ≥ 0).
  have hy₁_ge_x : x ≤ y₁.val := by
    rw [hy₁_val]
    have hs₁_ge_x : x ≤ s₁ := le_trans (le_max_left _ _) hs₁.1
    have : p.δ * x ≤ p.δ * s₁ := mul_le_mul_of_nonneg_left hs₁_ge_x (le_of_lt hδ_mem)
    linarith
  have hy₂_ge_x : x ≤ y₂.val := by
    rw [hy₂_val]
    have hs₂_ge_x : x ≤ s₂ := le_trans (le_max_left _ _) hs₂.1
    have : p.δ * x ≤ p.δ * s₂ := mul_le_mul_of_nonneg_left hs₂_ge_x (le_of_lt hδ_mem)
    linarith
  have hy₁_in_B : y₁.val ∈ Set.Icc xT (1 : ℝ) :=
    ⟨le_trans hx_mem.1 hy₁_ge_x, by rw [hy₁_val]; exact hF₁_in_I.2⟩
  have hy₂_in_B : y₂.val ∈ Set.Icc xT (1 : ℝ) :=
    ⟨le_trans hx_mem.1 hy₂_ge_x, by rw [hy₂_val]; exact hF₂_in_I.2⟩
  have hy_le : y₁ ≤ y₂ := by
    show y₁.val ≤ y₂.val
    rw [hy₁_val, hy₂_val]
    have : p.δ * s₁ ≤ p.δ * s₂ :=
      mul_le_mul_of_nonneg_left hs_le (le_of_lt hδ_mem)
    linarith
  have h_dist : dist y₁ y₂ = p.δ * (s₂ - s₁) := by
    rw [Subtype.dist_eq, Real.dist_eq, hy₁_val, hy₂_val]
    have h_diff_eq :
        (1 - p.δ) * x + p.δ * s₁ - ((1 - p.δ) * x + p.δ * s₂) = -(p.δ * (s₂ - s₁)) := by
      ring
    rw [h_diff_eq, abs_neg]
    apply abs_of_nonneg
    exact mul_nonneg (le_of_lt hδ_mem) (by linarith)
  have h_cont : g * dist y₁ y₂ ≤ V_T y₂ - V_T y₁ :=
    hV_gain_on y₁ y₂ hy₁_in_B hy₂_in_B hy_le
  rw [h_dist] at h_cont
  -- Goal already in affine form after the `simp only [hF, affineF]` above.
  change p.U_T x (α x) s₁ + p.β_T * V_T y₁
      ≤ p.U_T x (α x) s₂ + p.β_T * V_T y₂
  have hβ_T_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_s_diff_nn : 0 ≤ s₂ - s₁ := by linarith
  have h_cont_scaled :
      p.β_T * g * p.δ * (s₂ - s₁) ≤ p.β_T * (V_T y₂ - V_T y₁) := by
    have h_step : p.β_T * (g * (p.δ * (s₂ - s₁))) ≤ p.β_T * (V_T y₂ - V_T y₁) :=
      mul_le_mul_of_nonneg_left h_cont hβ_T_nn
    nlinarith [h_step]
  have h_margin_step : -c * (s₂ - s₁) + p.β_T * g * p.δ * (s₂ - s₁) ≥ 0 := by
    have : (p.β_T * g * p.δ - c) * (s₂ - s₁) ≥ 0 := by
      apply mul_nonneg
      · linarith [hmargin]
      · exact h_s_diff_nn
    nlinarith [this]
  nlinarith [h_stage, h_cont_scaled, h_margin_step]

/-- **Audit-44 localized variant of
`OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target`.**
Takes `LowerSlopeOnValueOn V_T (Set.Icc xT 1) gT` (strictly weaker
than the global `LowerSlopeOnValue V_T gT`). Otherwise identical. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith V_S KS)
    {c g : ℝ}
    (h_stage_loss_T :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (α x) s)
          (Set.Icc (max x sbar) 1) c)
    (hV_T_gain_on : LowerSlopeOnValueOn V_T (Set.Icc xT 1) g)
    (h_margin : c ≤ p.β_T * g * p.δ)
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
    p.senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz
      hF hKS_nonneg hS_margin (h_stage_sender x hx) hV_S_lip
  target_likes_high_sanctions := fun x hx =>
    p.targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value_on
      hF hxT_mem hx (h_stage_loss_T x hx) hV_T_gain_on h_margin

/-! ## 2026-08-20 — de-affining the sanction displacement identity

Every `hF : p.F = affineF p.δ` in this file is consumed for exactly one fact:
that raising the sanction by `Δ` moves next period's political state by
*exactly* `δ·Δ`. The two declarations below replace that equality by the
inequality each side of the argument actually needs — a sanction **lower**
chord at rate `dlo` for the Target leg, a range-restricted sanction **upper**
chord at rate `d` for the Sender leg — leaving the transition otherwise
untouched (no functional form, no curvature).

The two rates cannot be collapsed into one: a lower and an upper chord at the
same rate force `F x s₂ − F x s₁ = d·(s₂ − s₁)` exactly, which with `F_diag`
pins `F = affineF d` on the square (`TightChords.eq_of_sanctionChords_tight`). The
generality is real only because the legs consume
different rates. -/

/-- **R45 follow-up: alternative one-sided thresholds constructor
    taking the Target combined chord directly (replacing the
    (c_T, g_T, margin) decomposition).**

    Same Sender-side signature as
    `of_stage_lowerSlopes_compliance_target_on` (so this constructor
    is signature-compatible with the existing persistence pipeline),
    but the Target-side `(c_T, g_T, h_stage_loss_T, hV_T_gain_on,
    h_margin)` block is replaced with the single combined chord
    inequality on the joint Target dynamic objective at the
    equilibrium Target action. -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_lowerSlope_sender_and_target_combined_chord
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith V_S KS)
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
    p.senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz
      hF hKS_nonneg hS_margin (h_stage_sender x hx) hV_S_lip
  target_likes_high_sanctions := by
    intro x hx s₁ hs₁ s₂ hs₂ hs_le
    unfold Sanctions.AbstractGame.Params.targetSanctionObjective
    exact h_target_combined x hx s₁ hs₁ s₂ hs₂ hs_le

/-- **Goal-1 persistence bridge (canonical).** From the loss-offset
Target chain (`LowerLossSlopeOn` on stage payoff +
`LowerSlopeOnValueOn` on continuation `V_T` + margin
`cT ≤ β_T · gT · δ`) plus the Sender slope chain
(`LowerSlopeOn` + `KS`-Lipschitz Sender continuation +
`β_S · KS · δ < mS`) plus the Quah–Strulovici (2007)
interval-dominance-order family condition on the Sender dynamic
objective (strictly weaker than Milgrom–Shannon single crossing —
any SCP discharge upcasts freely via
`IDOFamilyOn.of_singleCrossingOn`), derive the Goal-1 conclusions at
the top-selector equilibrium `E` for any starting state in the high
political basin. -/
theorem persistence_at_equilibriumTop_from_lossOffset_on
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on : LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin hV_S_lip
      h_stage_target_loss hV_T_gain_on hT_loss_margin
      h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  exact equilibriumTop_oneSidedThresholds_long_run_nonDecreasing E
    hOne hTopMono hx₀

/-- **R45 follow-up: alternative Goal-1 persistence bridge consuming
    the Target combined chord directly (bypassing the
    (c_T, g_T, margin) decomposition).**

    Same Sender-side signature as
    `persistence_at_equilibriumTop_from_lossOffset_on` (so this
    alternative is a drop-in replacement on the Sender side), but
    the Target-side `(c_T, g_T, h_stage_target_loss,
    hV_T_gain_on, hT_loss_margin)` block is replaced with the single
    combined chord inequality `h_target_combined` on the joint Target
    dynamic objective at the equilibrium Target action.

    The persistence conclusions are identical to the canonical theorem;
    only the Target-side entry path changes. This realizes the
    user-approved R45 reformulation: the canonical paper-facing surface
    of `\Cref{ass:target_pref}` is the combined chord, and a fully
    parallel Lean delivery exists (without modifying the existing
    certificate structure or breaking the existing persistence path). -/
theorem persistence_at_equilibriumTop_from_target_combined_chord_on
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    (h_target_combined :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        ∀ s₁ ∈ Set.Icc (max x sbar) (1 : ℝ),
        ∀ s₂ ∈ Set.Icc (max x sbar) (1 : ℝ),
        s₁ ≤ s₂ →
          p.U_T x (E.α x) s₁
              + p.β_T * E.V_T
                  (Sanctions.clipS' (p.F x s₁))
            ≤ p.U_T x (E.α x) s₂
              + p.β_T * E.V_T
                  (Sanctions.clipS' (p.F x s₂)))
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlope_sender_and_target_combined_chord
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin hV_S_lip
      h_target_combined h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC
  exact equilibriumTop_oneSidedThresholds_long_run_nonDecreasing E
    hOne hTopMono hx₀

/-- **Goal-3 shock-hysteresis bridge (canonical).** From the same
primitive surface as `persistence_at_equilibriumTop_from_lossOffset_on`
(including the interval-dominance-order family condition in place of
Milgrom–Shannon single crossing — SCP upcasts freely via
`IDOFamilyOn.of_singleCrossingOn`) plus boundary conditions on the
shock starting state, conclude that a finite shock of high sanctions
moves the state into the basin, after which the persistence
conclusions apply. -/
theorem shock_at_equilibriumTop_from_lossOffset_on
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on : LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n))
          s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
            sbar) 1)) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin hV_S_lip
      h_stage_target_loss hV_T_gain_on hT_loss_margin
      h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  exact equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high
    E hOne hsbar_pos hjoint_lt hTopMono hx₀_nn hx₀_le

/-! ## Round 1.9 — Milgrom-Shannon-form persistence bridge (Tier 1)

User-approved JET-referee Tier-1 simplification: replace the
self-referential strict-slope wedge / `LowerSlopeOn ... mS` form of
A1's level-discharger with a Milgrom-Shannon-style strict-monotonicity
condition on the stage Sender payoff. The infrastructure
`OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord`
already exists in `JointPreferenceBasin.lean` and consumes pure
qualitative MS-form inputs (no `K_S`, no `m_S`, no `gap`).

Anchors:
* **Milgrom-Shannon 1994**, Theorem 4 / 4' — single-crossing as the
  necessary-and-sufficient condition for monotone comparative statics.
* **Topkis 1998 §3.8.1** — strict supermodularity ⇒ monotone selectors.
* **AES 2012**, Theorem 4 — single-crossing in ordered states is the
  political-economy gold standard.

This sibling bridge consumes the MS-form inputs and routes through
the same long-run-non-decreasing infrastructure as the existing
`persistence_at_equilibriumTop_from_target_combined_chord_on`. Net:
**5 hypotheses removed** (`mS, KS, hKS_nonneg, hS_margin, hV_S_lip`),
**2 added** (`hV_S_mono, h_stage_sender_strictMono`); net -3.

## Rule compliance
* **Rule 1** ✓ — no strategy changes.
* **Rule 3** ✓ — no new `Params` fields, no new structural primitives;
  hypothesis form is a strict weakening (strict-mono is ordinal,
  Lipschitz-strict-chord is cardinal). Net assumption surface
  decreases.
* **Rule 5** ✓ — parametric.
* **Rule 19** ✓ — uses only existing Foundations machinery
  (`Sanctions.MilgromShannon.SingleCrossingOn` is already imported). -/

/-- **Goal 1 (persistence) composition from primitive lower slopes
and single-crossing.** Composes:

* `OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes` to
  discharge the high-basin Prop from stage lower slopes + value
  Lipschitz primitives.
* `dynamicTopRealizedRule_mono_of_singleCrossingOn` to discharge the
  monotone realized rule from a localized Milgrom-Shannon
  single-crossing primitive.
* `equilibriumTop_oneSidedThresholds_long_run_nonDecreasing` for the
  headline persistence conclusion.

**⚠ AUDIT-48 LITERAL-COMPLIANCE DEPRECATION.** This persistence
bridge consumes a Target `LowerSlopeOn` (stage payoff *non-decreasing*
in `s`), which is sign-correct only under the resistance reading
where high sanctions trigger compliance the Target values. Under
literal compliance, sanctions hurt today (`U_T_s < 0`); use
`jet_persistence_at_equilibriumTop_from_lossOffset_on` (audit-43+44)
instead. The canonical paper-facing route is
`standardCompliance_three_goals_local_uniform_starts`. -/
theorem jet_persistence_at_equilibriumTop_from_lowerSlopes
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mT mS KT KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKT_nonneg : 0 ≤ KT)
    (hKS_nonneg : 0 ≤ KS)
    (hT_margin : p.β_T * KT * p.δ ≤ mT)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_T_lip : ValueLipschitzWith E.V_T KT)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1)
          mT)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes p hF
      hxT_mem hxS_mem hsbar_mem hKT_nonneg hKS_nonneg
      hT_margin hS_margin hV_T_lip hV_S_lip
      h_stage_target h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC
  exact equilibriumTop_oneSidedThresholds_long_run_nonDecreasing E
    hOne hTopMono hx₀

/-! ## 2. Temporary shock → permanent high (Goal 3)
from primitive lower slopes + single-crossing -/

/-- **Goal 3 (temporary shock → permanent high) composition from
primitive lower slopes and single-crossing.** Same primitive inputs
as Goal 1, plus the shock-specific nondegeneracy primitives
(`hsbar_pos`, `hjoint_lt`). Composes:

* `of_stage_lowerSlopes` (high-basin from primitives).
* `dynamicTopRealizedRule_mono_of_singleCrossingOn` (monotone
  realized rule).
* `equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high`
  for the headline shock-hysteresis conclusion.

**⚠ AUDIT-48 LITERAL-COMPLIANCE DEPRECATION.** Same Target
`LowerSlopeOn` issue as the persistence bridge. Use
`jet_shock_at_equilibriumTop_from_lossOffset_on` for literal
compliance; cite `standardCompliance_three_goals_local_uniform_starts` for the
paper-facing combined result. -/
theorem jet_shock_at_equilibriumTop_from_lowerSlopes
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mT mS KT KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hKT_nonneg : 0 ≤ KT)
    (hKS_nonneg : 0 ≤ KS)
    (hT_margin : p.β_T * KT * p.δ ≤ mT)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_T_lip : ValueLipschitzWith E.V_T KT)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    (h_stage_target :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1)
          mT)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n))
          s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
            sbar) 1)) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes p hF
      hxT_mem hxS_mem hsbar_mem hKT_nonneg hKS_nonneg
      hT_margin hS_margin hV_T_lip hV_S_lip
      h_stage_target h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC
  exact equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high
    E hOne hsbar_pos hjoint_lt hTopMono hx₀_nn hx₀_le

/-! ## 3. Different-α dominance (Goal 2) on basin
from primitive α-ordering + σ-monotonicity -/

set_option linter.deprecated false in

/-- **Audit-43 sign-correct persistence bridge (loss-offset
discharge of Target stage payoff).** Same as
`jet_persistence_at_equilibriumTop_from_lowerSlopes` but uses the
audit-41 Target loss-offset discharger. -/
theorem jet_persistence_at_equilibriumTop_from_lossOffset
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain : LowerSlopeOnValue E.V_T gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin hV_S_lip
      h_stage_target_loss hV_T_gain hT_loss_margin
      h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC
  exact equilibriumTop_oneSidedThresholds_long_run_nonDecreasing E
    hOne hTopMono hx₀

/-- **Audit-43 sign-correct shock bridge (loss-offset discharge of
Target stage payoff).** Same as
`jet_shock_at_equilibriumTop_from_lowerSlopes` but uses the audit-41
Target loss-offset discharger. -/
theorem jet_shock_at_equilibriumTop_from_lossOffset
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain : LowerSlopeOnValue E.V_T gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n))
          s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
            sbar) 1)) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin hV_S_lip
      h_stage_target_loss hV_T_gain hT_loss_margin
      h_stage_sender
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC
  exact equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high
    E hOne hsbar_pos hjoint_lt hTopMono hx₀_nn hx₀_le

/-! ## 3c. Audit-44 localized persistence/shock bridges (loss-offset
+ localized `LowerSlopeOnValueOn` Target high-basin)

The audit-44 critique noted that `LowerSlopeOnValue V_T g` over all of
`↥(Sanctions.S)` is stronger than needed: the discharger only inspects
`V_T` on the transition image of the high-basin range. The bridges
below take `LowerSlopeOnValueOn V_T (Set.Icc xT 1) gT` (localized) and
otherwise mirror the audit-43 bridges. -/

/-- **Audit-44 localized persistence bridge.** Same as
`jet_persistence_at_equilibriumTop_from_lossOffset` but with
`LowerSlopeOnValueOn V_T (Set.Icc xT 1) gT` instead of the global
`LowerSlopeOnValue V_T gT`.

**Audit-49 follow-up Phase-C cleanup**: this bridge is sign-correct
under literal compliance, but its `jet_*` naming conflates it with
the legacy resistance-action `jet_*` bridges in this file. The
**canonical name** is now
`Sanctions.AbstractGame.Params.persistence_at_equilibriumTop_from_lossOffset_on`
in `Theory/Certificates/StandardComplianceBridges.lean`. The `jet_*`
form is retained for backward compatibility. -/
theorem jet_persistence_at_equilibriumTop_from_lossOffset_on
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on : LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) :=
  -- Audit-49 follow-up Item-9: proof body moved to
  -- `Theory/Certificates/StandardComplianceBridges.lean`. This `jet_*` form
  -- is now a one-line compatibility alias of the canonical-name version.
  p.persistence_at_equilibriumTop_from_lossOffset_on E hF
    hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin hV_S_lip
    h_stage_target_loss hV_T_gain_on hT_loss_margin
    h_stage_sender
    (Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn hSC)
    hx₀

/-- **Audit-44 localized shock bridge.** Same as
`jet_shock_at_equilibriumTop_from_lossOffset` but with localized
`LowerSlopeOnValueOn`.

**Audit-49 follow-up Phase-C cleanup**: this bridge is sign-correct
under literal compliance, but its `jet_*` naming conflates it with
the legacy resistance-action `jet_*` bridges in this file. The
**canonical name** is now
`Sanctions.AbstractGame.Params.shock_at_equilibriumTop_from_lossOffset_on`
in `Theory/Certificates/StandardComplianceBridges.lean`. The `jet_*`
form is retained for backward compatibility. -/
theorem jet_shock_at_equilibriumTop_from_lossOffset_on
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on : LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar))
          mS)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n))
          s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
            sbar) 1)) :=
  -- Audit-49 follow-up Item-9: proof body moved to
  -- `Theory/Certificates/StandardComplianceBridges.lean`. This `jet_*` form
  -- is now a one-line compatibility alias of the canonical-name version.
  p.shock_at_equilibriumTop_from_lossOffset_on E hF
    hxT_mem hxS_mem hsbar_mem hsbar_pos hjoint_lt
    hKS_nonneg hS_margin hV_S_lip
    h_stage_target_loss hV_T_gain_on hT_loss_margin
    h_stage_sender
    (Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn hSC)
    hx₀_nn hx₀_le

/-! ## 5. Value-Lipschitz threading for `E.V_S` via canonical identification

The JET top-level bridge takes `hV_S_lip_E` as a per-E primitive. The
audit-34 critique observes that the Sender side is composable from
primitives because `E.V_S = p.V_S E.α E.hα` (canonical identification
from `JointPreferenceBasin.V_S_eq_canonical`) and
`V_S_valueLipschitzWith_of_contraction` discharges
`ValueLipschitzWith (p.V_S α hα) (L_U / (1 - β_S · γ))` from primitive
stage payoff Lipschitz `L_U` in `x` (at fixed `α`) and transition
Lipschitz `γ`.

The theorem below packages exactly that composition, so the user no
longer has to supply `hV_S_lip_E` for the produced E — it is derived
from the same primitive payoff/transition Lipschitz constants the
audit-32 `ValueLipschitz.lean` round already isolated. -/

/-- **`E.V_S` value-Lipschitz from primitive payoff/transition Lipschitz.**
Composes `V_S_eq_canonical E` (Banach-uniqueness identification of
`E.V_S` with the canonical Sender fixed point `p.V_S E.α E.hα`) with
`V_S_valueLipschitzWith_of_contraction` (primitive Lipschitz discharge
of the canonical fixed point). The hypotheses are stated in their α-form
at `E.α` (any continuous α gives the discharge; here we instantiate at
`E.α`). The resulting Lipschitz constant `L_U / (1 - p.β_S · γ)` is the
canonical Banach-iteration bound.

Affine-restricted (it carries `hF` and states the transition modulus in its
affine form). Round BJ1.2 (2026-10-07): the sign binders `0 ≤ L_U` and `0 ≤ γ`
are deleted, because the underlying discharger no longer takes them (`0 ≤ L_U`
is derived from `h_U_lip`, `0 ≤ γ` was never read). -/
theorem FeedbackStackelbergEquilibriumTop.V_S_valueLipschitzWith_of_contraction
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {L_U γ : ℝ}
    (h_U_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |p.U_S x₂ (E.α x₂) s - p.U_S x₁ (E.α x₁) s| ≤ L_U * |x₂ - x₁|)
    (h_F_lip : ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
      |((1 - p.δ) * x₂ + p.δ * s) - ((1 - p.δ) * x₁ + p.δ * s)|
        ≤ γ * |x₂ - x₁|)
    (h_contract : p.β_S * γ < 1) :
    ValueLipschitzWith E.V_S (L_U / (1 - p.β_S * γ)) := by
  -- Lipschitz of the canonical fixed point.
  have hCanon : ValueLipschitzWith (p.V_S E.α E.hα) (L_U / (1 - p.β_S * γ)) :=
    p.V_S_valueLipschitzWith_of_contraction E.hα
      h_U_lip
      (fun x₁ x₂ s hs => by rw [hF]; exact h_F_lip x₁ x₂ s hs)
      h_contract
  -- Transport via the canonical identification.
  intro y₁ y₂
  have hEq : E.V_S = p.V_S E.α E.hα := E.V_S_eq_canonical
  calc |E.V_S y₂ - E.V_S y₁|
      = |(p.V_S E.α E.hα) y₂ - (p.V_S E.α E.hα) y₁| := by rw [hEq]
    _ ≤ (L_U / (1 - p.β_S * γ)) * dist y₁ y₂ := hCanon y₁ y₂

/-! ## 5b. Value-Lipschitz from C¹ bounded derivative (audit-37 Step 2)

The mean-value theorem on the convex unit interval `Sanctions.S = [0, 1]`
gives: if `V : C1Val K_d`, then `V.V : ↥S →ᵇ ℝ` is `K_d`-Lipschitz on
`↥S`. This eliminates the high-basin `K_T`, `K_S` per-E value-Lipschitz
primitives once the equilibrium values come from a C¹ structure.

Composes the C¹ `HasBoundedDerivOnS` field with mathlib's
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`. -/

/-- **Audit-44 C¹ compliance bridge.** Audit-44 C¹ compliance bridge
with localized `LowerSlopeOnValueOn`, floor/ceiling dominance
discharge, and derived basin invariance. (Originally documented as
"mirrors `_three_goals_compliance` with the audit-44 tightenings";
that earlier `_three_goals_compliance` was removed in the
2026-06-01 redundancy round.) -/
theorem jet_C1BellmanSystem_three_goals_compliance_on
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D_C1 : C1BellmanSystem p K_d)
    (hComplete : ValueClass_C1Complete D_C1.toValueClass_C1)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip_E :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss_α :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Set.Icc xT (1 : ℝ),
          LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
            (Set.Icc (max x sbar) 1) cT)
    -- Audit-44 Patch 6: localized continuation gain.
    (hV_T_gain_on_E :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender_α :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          LowerSlopeOn
            (fun s => p.U_S x (E.α x) s)
            (Set.Icc (0 : ℝ) (max x sbar))
            mS)
    (hSC_α :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        Sanctions.MilgromShannon.SingleCrossingOn
          Sanctions.I (Set.Icc (max xT xS) 1)
          (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (M_eq : p.MyopicFeedbackEquilibrium)
    (hMyo_basin :
      ∀ x ∈ Set.Icc (max xT xS) 1,
        p.σ x (M_eq.α x) ∈ Set.Icc (max xT xS) 1)
    -- Audit-44 Patch 5: myopic ceiling instead of direct rule dominance.
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1,
        p.σ x (M_eq.α x) ≤ max x sbar)
    {x₀ x₀shock : ℝ}
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1)
    (hx₀shock_nn : 0 ≤ x₀shock) (hx₀shock_le : x₀shock ≤ 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                ∈ Set.Icc (max xT xS) 1) ∧
       (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
       (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ n,
           p.ruleSanctions (fun x => p.σ x (M_eq.α x)) x₀ n
             ≤ p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) x₀ n)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀shock N) n
                  ∈ Set.Icc (max xT xS) 1) ∧
          (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath x₀shock N) n) ∧
          (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                (p.shockPath x₀shock N) n) := by
  obtain ⟨E⟩ :=
    D_C1.feedbackStackelbergEquilibriumTop_of_complete hK_d_nn hComplete
  -- Derive dynamic floor on basin (from loss-offset + SC).
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin (hV_S_lip_E E)
      (h_stage_target_loss_α E) (hV_T_gain_on_E E)
      hT_loss_margin (h_stage_sender_α E)
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn (hSC_α E)
  have hα_feas : ∀ x ∈ Set.Icc (max xT xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    apply E.α_mem
    refine ⟨?_, hx.2⟩
    exact le_trans (le_max_of_le_left hxT_mem.1) hx.1
  have hα_opt : ∀ x ∈ Set.Icc (max xT xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := by
    intro x hx
    apply E.α_opt_top
    refine ⟨?_, hx.2⟩
    exact le_trans (le_max_of_le_left hxT_mem.1) hx.1
  have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
  have hDynFloor : ∀ x ∈ Set.Icc (max xT xS) 1,
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    JointPreferenceBasinTop.level_dyn_top p hB
  -- Derive basin invariance + rule dominance from floor + ceiling.
  have hDynBasin : ∀ x ∈ Set.Icc (max xT xS) 1,
      p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc (max xT xS) 1 := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have hFloor := hDynFloor x hx
      have hx_le_max : x ≤ max x sbar := le_max_left _ _
      exact le_trans hx.1 (le_trans hx_le_max hFloor)
    · unfold dynamicTopRealizedRule
      exact (p.σ_dyn_top_mem_I E.V_S x (E.α x)).2
  have hRuleDom :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hDynFloor hMyoCeiling
  refine ⟨E, ?_, ?_, ?_⟩
  · exact p.jet_persistence_at_equilibriumTop_from_lossOffset_on E hF
      hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin (hV_S_lip_E E)
      (h_stage_target_loss_α E) (hV_T_gain_on_E E)
      hT_loss_margin (h_stage_sender_α E) (hSC_α E) hx₀
  · exact p.jet_dominance_at_equilibriumTop_audit41 E M_eq
      hMyo_basin hDynBasin hTopMono hRuleDom hx₀
  · obtain ⟨N, h1, h2, h3, _, _, _⟩ :=
      p.jet_shock_at_equilibriumTop_from_lossOffset_on E hF
        hxT_mem hxS_mem hsbar_mem hsbar_pos hjoint_lt
        hKS_nonneg hS_margin (hV_S_lip_E E)
        (h_stage_target_loss_α E) (hV_T_gain_on_E E)
        hT_loss_margin (h_stage_sender_α E) (hSC_α E)
        hx₀shock_nn hx₀shock_le
    exact ⟨N, h1, h2, h3⟩

/-! ## Audit-45 Step 7: C¹ compliance bridge (statewise, no `hMyo_basin`)

Mirrors the audit-45 Step 1 Core/Path split on the BCF side: the
statewise C¹ bridge returns Goal 1 + statewise dominance + Goal 3
without taking `hMyo_basin`. -/

/-- **Audit-45 statewise C¹ compliance bridge.** Same as
`jet_C1BellmanSystem_three_goals_compliance_on` but Goal 2 is
statewise (pointwise rule comparison on the basin) instead of
pathwise (sequence comparison along the endogenous myopic path).
No `hMyo_basin` is required. -/
theorem jet_C1BellmanSystem_three_goals_compliance_statewise
    {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D_C1 : C1BellmanSystem p K_d)
    (hComplete : ValueClass_C1Complete D_C1.toValueClass_C1)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS sbar mS KS : ℝ}
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip_E :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        ValueLipschitzWith E.V_S KS)
    {cT gT : ℝ}
    (h_stage_target_loss_α :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Set.Icc xT (1 : ℝ),
          LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
            (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on_E :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        LowerSlopeOnValueOn E.V_T (Set.Icc xT 1) gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * p.δ)
    (h_stage_sender_α :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          LowerSlopeOn
            (fun s => p.U_S x (E.α x) s)
            (Set.Icc (0 : ℝ) (max x sbar))
            mS)
    (hSC_α :
      ∀ E : p.FeedbackStackelbergEquilibriumTop,
        Sanctions.MilgromShannon.SingleCrossingOn
          Sanctions.I (Set.Icc (max xT xS) 1)
          (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (M_eq : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1,
        p.σ x (M_eq.α x) ≤ max x sbar)
    {x₀ x₀shock : ℝ}
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1)
    (hx₀shock_nn : 0 ≤ x₀shock) (hx₀shock_le : x₀shock ≤ 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                ∈ Set.Icc (max xT xS) 1) ∧
       (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
       (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max xT xS) 1,
           p.σ x (M_eq.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀shock N) n
                  ∈ Set.Icc (max xT xS) 1) ∧
          (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath x₀shock N) n) ∧
          (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                (p.shockPath x₀shock N) n) := by
  obtain ⟨E⟩ :=
    D_C1.feedbackStackelbergEquilibriumTop_of_complete hK_d_nn hComplete
  -- Build dynamic floor on the basin from compliance-chain inputs.
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on
      p hF hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin (hV_S_lip_E E)
      (h_stage_target_loss_α E) (hV_T_gain_on_E E)
      hT_loss_margin (h_stage_sender_α E)
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_singleCrossingOn (hSC_α E)
  have hα_feas : ∀ x ∈ Set.Icc (max xT xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    apply E.α_mem
    refine ⟨?_, hx.2⟩
    exact le_trans (le_max_of_le_left hxT_mem.1) hx.1
  have hα_opt : ∀ x ∈ Set.Icc (max xT xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := by
    intro x hx
    apply E.α_opt_top
    refine ⟨?_, hx.2⟩
    exact le_trans (le_max_of_le_left hxT_mem.1) hx.1
  have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
  have hDynFloor : ∀ x ∈ Set.Icc (max xT xS) 1,
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    JointPreferenceBasinTop.level_dyn_top p hB
  have hRuleDom :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hDynFloor hMyoCeiling
  refine ⟨E, ?_, ?_, ?_⟩
  · exact p.jet_persistence_at_equilibriumTop_from_lossOffset_on E hF
      hxT_mem hxS_mem hsbar_mem hKS_nonneg hS_margin (hV_S_lip_E E)
      (h_stage_target_loss_α E) (hV_T_gain_on_E E)
      hT_loss_margin (h_stage_sender_α E) (hSC_α E) hx₀
  · exact hRuleDom
  · obtain ⟨N, h1, h2, h3, _, _, _⟩ :=
      p.jet_shock_at_equilibriumTop_from_lossOffset_on E hF
        hxT_mem hxS_mem hsbar_mem hsbar_pos hjoint_lt
        hKS_nonneg hS_margin (hV_S_lip_E E)
        (h_stage_target_loss_α E) (hV_T_gain_on_E E)
        hT_loss_margin (h_stage_sender_α E) (hSC_α E)
        hx₀shock_nn hx₀shock_le
    exact ⟨N, h1, h2, h3⟩

namespace RegularEconomyCertificateC1ComplianceCore

variable {K_d : ℝ}

/-- **Audit-45 Step 7: C¹ Core (statewise) three-goals theorem.** -/
theorem three_goals_statewise (C : p.RegularEconomyCertificateC1ComplianceCore K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  p.jet_C1BellmanSystem_three_goals_compliance_statewise
    C.hK_d_nn C.D_C1 C.hComplete hF
    C.hxT_mem C.hxS_mem C.hsbar_mem C.hKS_nonneg C.hS_margin
    C.hV_S_lip_E
    C.h_stage_target_loss_α C.hV_T_gain_on_E C.hT_loss_margin
    C.h_stage_sender_α C.hSC_α C.hsbar_pos C.hjoint_lt
    C.M C.hMyoCeiling
    C.hx₀ C.hx₀shock_nn C.hx₀shock_le

end RegularEconomyCertificateC1ComplianceCore

namespace RegularEconomyCertificateC1Compliance

variable {K_d : ℝ}

/-- **C¹-route compliance three-goals theorem (audit-44/45 pathwise
form).** One-line delegation to
`jet_C1BellmanSystem_three_goals_compliance_on` (pathwise variant).
The audit-45 statewise alternative lives on the Core: see
`RegularEconomyCertificateC1ComplianceCore.three_goals_statewise`. -/
theorem three_goals_pathwise (C : p.RegularEconomyCertificateC1Compliance K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ n,
           p.ruleSanctions (fun x => p.σ x (C.M.α x)) C.x₀ n
             ≤ p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) C.x₀ n)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  p.jet_C1BellmanSystem_three_goals_compliance_on
    C.hK_d_nn C.D_C1 C.hComplete hF
    C.hxT_mem C.hxS_mem C.hsbar_mem C.hKS_nonneg C.hS_margin
    C.hV_S_lip_E
    C.h_stage_target_loss_α C.hV_T_gain_on_E C.hT_loss_margin
    C.h_stage_sender_α C.hSC_α C.hsbar_pos C.hjoint_lt
    C.M C.hMyo_basin C.hMyoCeiling
    C.hx₀ C.hx₀shock_nn C.hx₀shock_le

/-- **Backward-compatibility alias.** The original `three_goals`
name on `RegularEconomyCertificateC1Compliance` is preserved as an
alias to `three_goals_pathwise` (audit-45 rename). -/
theorem three_goals (C : p.RegularEconomyCertificateC1Compliance K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ n,
           p.ruleSanctions (fun x => p.σ x (C.M.α x)) C.x₀ n
             ≤ p.ruleSanctions (p.dynamicTopRealizedRule E.V_S E.α) C.x₀ n)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  RegularEconomyCertificateC1Compliance.three_goals_pathwise p C hF

end RegularEconomyCertificateC1Compliance

namespace StandardComplianceCertificateC1

variable {K_d : ℝ}

/-- **Audit-46 canonical C¹ paper-facing theorem.** -/
theorem three_goals (C : p.StandardComplianceCertificateC1 K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  RegularEconomyCertificateC1ComplianceCore.three_goals_statewise p C hF

end StandardComplianceCertificateC1

end Params

end AbstractGame

end

end Sanctions
