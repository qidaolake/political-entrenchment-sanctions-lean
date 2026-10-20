/-
Sanctions/Theory/Basin/StageFlipPersistence.lean

**The stage-flip route through the persistence certificate (round BH-1, item
BH1.8, 2026-10-06).**

`StageFlipCertificate.lean` routes the stage-flip primitives into the MS core
certificate `StandardComplianceLocalCoreCertificate_MS`, and from there into
the three-goals wrapper `standardCompliance_three_goals_from_stage_flip_generalF`.
That route pays for the MS certificate's Target block and strict pivot:

* the Target combined chord P4, built by `targetCombinedChordOn_of_stage_flip`
  from Target stage complementarity, the boundary sign `1 ∈ targetFlipSet s̄`
  and monotone carrier Target values;
* the strict pivot `max(x̄_T, x̂_S) ∈ (0, 1)`, built from the second boundary
  sign `0 ∉ targetFlipSet s̄` and from `max(x̄_T, x̂_S) < 1`.

None of the three goals reads P4 or the strict pivot (`PersistenceThreeGoals.lean`).
This file routes the same primitives into the persistence certificate
`StandardCompliancePersistenceCertificate` instead, and closes the three goals
through the round BH-1 composites of item BH1.6.

## What this file proves

* `lowerSlopeOn_Icc_zero_of_floor_and_diag` — the Sender's stage slope on
  `[0, t]` from its floor piece on `[0, s̄]` and its diagonal piece on
  `[s̄, t]`, wherever `s̄` lies relative to `0` and `t`.
* `StandardCompliancePersistenceCertificate.of_stage_flip` — the persistence
  certificate with derived pivots `xT := targetFlipPivot s̄` and
  `xS := senderFlipPivot s̄ m_S`.
* `standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent`
  (conclusion of the row-1 shape) and
  `standardCompliance_three_goals_from_stage_flip_generalF_min_drift_shock_of_preBasinAscent`
  (row-2 shape, with the minimum-drift shock length) — the three goals at the
  derived basin `[max(x̄_T, x̂_S), 1]`.

The old wrapper `standardCompliance_three_goals_from_stage_flip_generalF` is now
proved in `StageFlipCertificate.lean` as a corollary of the row-1 sibling.

## Hypotheses dropped against the MS route

| MS-route input | Why it is not needed here |
|---|---|
| `h0_T : 0 ∉ targetFlipSet s̄` | fed only the strict lower pivot bound |
| `hjoint_lt : max(x̄_T, x̂_S) < 1` | fed the strict pivot; pre-basin ascent implies it |
| `hV_T_mono_carrier` | fed only the Target combined chord P4 |
| `hID_T`, `h1_T` | fed P4 and feasibility of `x̄_T`, which always holds |
| `hsbar_le : s̄ ≤ max(x̄_T, x̂_S)` | aligned two chord ranges; the slope gluing needs no order |
| `hsbar_mem : s̄ ∈ [0, 1]` | placed the floor range in `[0, 1]` for the global primitive |
| `hID_S` on all sanctions in `[0, 1]` | the floor flip set reads only `[0, s̄]` |
| single crossing `hSC_on` | used only through interval dominance, now the input |
| `hF_top` on `[0, 1)` | shock entry needs ascent only on `[0, max(x̄_T, x̂_S)]` |

The route therefore needs, beyond the equilibrium-construction data and the
Sender's stage inputs, only interval dominance on the derived basin and ascent
at full sanction below it. The Target enters through the equilibrium policy
`D.α_on`, which the Sender's stage and dynamic objectives are evaluated at; the
Target flip set enters only as the location `x̄_T` of the basin's lower end.

## Scope

Rule 9: each three-goals theorem asserts the existence of one constructed
equilibrium in the certified carriers (the contraction fixed point), not a
property of every equilibrium. Non-vacuity: the stage-flip witness `sfParams`
(`Examples/StageFlipCertWitness.lean`) inhabits the constructor and the
minimum-drift sibling. Rule 9B: no economy is exhibited that this route reaches
and the MS route misses; the extra generality is, as yet, unwitnessed.

## Rule compliance

**Rule 1.** The equilibrium is constructed; the Target policy is the
Bellman-optimal carrier selector and the Sender's action is the upper dynamic
argmax. The shock phase is the exogenous transient-shock exception.

**Rule 3.** No new assumption. Every input is an input of the MS-route
constructor, weakened (`SenderStageIDOn` on `[0, s̄]` for `SenderStageID`,
interval dominance for single crossing, pre-basin ascent for `hF_top` with
`hjoint_lt`) or verbatim; the myopic ceiling is the MS route's verbatim.

**Rule 22.** General in `F`. The transition enters only through the `Params`
fields and the pre-basin ascent condition; the affine law appears nowhere.

**Round BJ5.1 (2026-10-07).** The two three-goals composites state the myopic
ceiling against `p.myopicFeedbackEquilibrium_canonical` and so take
`[p.StaticSelectorContinuous]`. That class is the static-selector continuity
condition, the joint continuity of the static Sender selector `σ`, which was
the `Params` field `σ_continuous`. The content is unchanged; the condition
moved from the economy to the binder. General in `F`.
-/

import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.Certificates.PersistenceThreeGoals

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The Sender's stage slope on the whole sub-pivot range -/

/-- **Slope on `[0, t]` from a floor piece and a diagonal piece.** If `f` has
lower slope at least `m` on `[0, s̄]` and on `[s̄, t]`, it has lower slope at
least `m` on `[0, t]`. No order between `0`, `s̄` and `t` is assumed: a chord
inside `[0, s̄]` uses the first piece, a chord inside `[s̄, t]` the second, and a
chord that crosses `s̄` splits there. Compared with `lowerSlopeOn_glue_Icc`,
the hypotheses `0 ≤ s̄` and `s̄ ≤ t` are dropped. Pure order fact, no
economics; no transition enters. -/
theorem lowerSlopeOn_Icc_zero_of_floor_and_diag {f : ℝ → ℝ} {sbar t m : ℝ}
    (hfloor : LowerSlopeOn f (Set.Icc (0 : ℝ) sbar) m)
    (hdiag : LowerSlopeOn f (Set.Icc sbar t) m) :
    LowerSlopeOn f (Set.Icc (0 : ℝ) t) m := by
  intro s₁ hs₁ s₂ hs₂ hs
  rcases le_or_gt s₂ sbar with h2 | h2
  · exact hfloor s₁ ⟨hs₁.1, le_trans hs h2⟩ s₂ ⟨hs₂.1, h2⟩ hs
  · rcases le_or_gt sbar s₁ with h1 | h1
    · exact hdiag s₁ ⟨h1, hs₁.2⟩ s₂ ⟨le_of_lt h2, hs₂.2⟩ hs
    · have ha := hfloor s₁ ⟨hs₁.1, le_of_lt h1⟩ sbar
        ⟨le_trans hs₁.1 (le_of_lt h1), le_rfl⟩ (le_of_lt h1)
      have hb := hdiag sbar ⟨le_rfl, le_trans (le_of_lt h2) hs₂.2⟩ s₂
        ⟨le_of_lt h2, hs₂.2⟩ (le_of_lt h2)
      have hsplit : m * (s₂ - s₁) = m * (sbar - s₁) + m * (s₂ - sbar) := by
        ring
      linarith

/-! ## The persistence certificate from the stage flip -/

/-- **Stage-flip constructor for the persistence certificate.** Builds
`StandardCompliancePersistenceCertificate` with derived pivots
`xT := targetFlipPivot s̄` and `xS := senderFlipPivot s̄ m_S`, from

* the equilibrium-construction data (value class, invariance, row-sum
  contraction);
* Sender stage complementarity on the floor range `[0, s̄]` only
  (`SenderStageIDOn`), the Sender boundary sign `1 ∈ senderFloorFlipSet s̄ m_S`,
  and the diagonal residual `h_diag_MS` (chords on `[s̄, max(x, x̄)]` at slope
  `m_S > 0`), which give the Sender's stage margin below the pivot;
* monotone carrier Sender values; and
* interval dominance of the Sender's dynamic objective on the derived basin
  `[max(x̄_T, x̂_S), 1]` (the direction input A1).

Sibling of `StandardComplianceLocalCoreCertificate_MS.of_stage_flip`. Dropped:
everything that fed only the MS certificate's Target combined chord or its
strict pivot (`hID_T`, `h1_T`, `h0_T`, `hjoint_lt`, `hV_T_mono_carrier`), the
ordering `hsbar_le`, `s̄ ∈ [0, 1]`, Sender stage complementarity outside the
floor range, and the myopic ceiling (not a persistence-certificate field;
the three-goals theorems below take it). Single crossing is replaced by the
interval dominance it was used to produce. The Target pivot `x̄_T` is feasible
with no hypothesis (`targetFlipPivot_feasible`); the Target's stage flip plays
no role in persistence. General in `F`. -/
noncomputable def StandardCompliancePersistenceCertificate.of_stage_flip
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    {sbar mS : ℝ} (hmS_pos : 0 < mS)
    (hID_S : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar))
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (h_diag_MS : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar
            (max x (max (p.targetFlipPivot sbar)
              (p.senderFlipPivot sbar mS)))) mS)
    (hV_S_mono_carrier : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hIDO_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)) :
    p.StandardCompliancePersistenceCertificate where
  D := D
  h_inv := h_inv
  β_T := β_T
  β_S := β_S
  L_TS := L_TS
  L_ST := L_ST
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hL_TS_nn := hL_TS_nn
  hL_ST_nn := hL_ST_nn
  hT_T_op := hT_T_op
  hT_S_op := hT_S_op
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S
  xT := p.targetFlipPivot sbar
  xS := p.senderFlipPivot sbar mS
  hxT_mem := p.targetFlipPivot_feasible sbar
  hxS_mem := p.senderFlipPivot_feasible sbar mS
  h_stage_sender_strictMono := by
    intro V_T V_S x hx
    -- Slope `m_S` on the whole sub-pivot range: the floor flip set on
    -- `[0, s̄]` and the diagonal residual on `[s̄, max(x, x̄)]`.
    have hxmem : x ∈ p.senderFloorFlipSet sbar mS := by
      rw [p.senderFloorFlipSet_eq_Icc_of_stageIDOn hID_S h1_S]
      exact hx
    have hfloor : LowerSlopeOn
        (fun s => p.U_S x (D.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) sbar) mS :=
      fun s₁ hs₁ s₂ hs₂ hs =>
        hxmem.2 (D.α_on V_T V_S x) (D.α_on_mem V_T V_S x)
          s₁ hs₁ s₂ hs₂ hs
    have hslope :=
      lowerSlopeOn_Icc_zero_of_floor_and_diag hfloor (h_diag_MS V_T V_S x hx)
    -- Positive lower slope gives strict monotonicity.
    intro s₁ hs₁ s₂ hs₂ hlt
    have hchord := hslope s₁ hs₁ s₂ hs₂ hlt.le
    have hpos : 0 < mS * (s₂ - s₁) :=
      mul_pos hmS_pos (sub_pos.mpr hlt)
    linarith
  hIDO_on := hIDO_on
  hV_S_mono_carrier := hV_S_mono_carrier

/-! ## The three goals from the stage flip, through the persistence route -/

/-- **The three goals from the stage flip, minimum-drift form, from pre-basin
ascent (round BH-1, item BH1.8).** There is a forward-looking feedback
Stackelberg equilibrium in the certified carriers such that, at the derived
basin `[x̄, 1]` with `x̄ = max(x̄_T, x̂_S)`:

1. from every basin start the general-`F` path stays in the basin, the
   realised sanction is at least `x̄`, and realised sanctions never fall;
2. on the basin the equilibrium sanction is at least the canonical myopic one;
3. the full-sanction drift attains a positive minimum `η` on `[0, x̄]`, and one
   shock of `⌈x̄ / η⌉` periods puts every initial state into the basin, after
   which the equilibrium path stays there with sanctions at least `x̄`.

Hypotheses: those of `StandardCompliancePersistenceCertificate.of_stage_flip`,
the myopic ceiling, and ascent at full sanction on `[0, x̄]`. Against the MS
route, the dropped inputs are listed in the module docstring; in particular no
Target stage condition, no Target boundary sign, no monotone Target carrier,
no `x̄ < 1` and no global ascent. General in `F`. -/
theorem standardCompliance_three_goals_from_stage_flip_generalF_min_drift_shock_of_preBasinAscent
    [p.StaticSelectorContinuous]
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    {sbar mS : ℝ} (hmS_pos : 0 < mS)
    (hID_S : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar))
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (h_diag_MS : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar
            (max x (max (p.targetFlipPivot sbar)
              (p.senderFlipPivot sbar mS)))) mS)
    (hV_S_mono_carrier : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hIDO_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (hMyoCeiling : ∀ x ∈ Set.Icc
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
      p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (p.targetFlipPivot sbar)
            (p.senderFlipPivot sbar mS)))
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ)
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)),
      x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ D.carrier_T
      ∧ E.V_S ∈ D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc
            (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (max (p.targetFlipPivot sbar)
                              (p.senderFlipPivot sbar mS)) 1) ∧
          (∀ n, max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)
                  ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc
            (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ)
              (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)),
            η = p.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ)
              (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)),
            η ≤ p.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          p.shockPathF x₀shock (Nat.ceil
              (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS) / η))
              ∈ Set.Icc
                (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1
          ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil
                      (max (p.targetFlipPivot sbar)
                        (p.senderFlipPivot sbar mS) / η))) n
                    ∈ Set.Icc
                      (max (p.targetFlipPivot sbar)
                        (p.senderFlipPivot sbar mS)) 1)
          ∧ (∀ n, max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)
                    ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                      (p.shockPathF x₀shock (Nat.ceil
                        (max (p.targetFlipPivot sbar)
                          (p.senderFlipPivot sbar mS) / η))) n) :=
  StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent
    (StandardCompliancePersistenceCertificate.of_stage_flip p D h_inv
      hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T_op hT_S_op hsuff_T hsuff_S
      hmS_pos hID_S h1_S h_diag_MS hV_S_mono_carrier hIDO_on)
    hMyoCeiling hF_top_pre

/-- **The three goals from the stage flip, row-1 shape, from pre-basin ascent
(round BH-1, item BH1.8).** Goals 1 and 2 as in the minimum-drift form; and for
every initial state in `[0, 1]` some finite full-sanction shock after which
the equilibrium path stays in the derived basin `[max(x̄_T, x̂_S), 1]` with
sanctions at least `max(x̄_T, x̂_S)`.

The conclusion is verbatim that of
`standardCompliance_three_goals_from_stage_flip_generalF`. Against it, the
route needs only interval dominance on the basin (for single crossing) and
ascent at full sanction on `[0, max(x̄_T, x̂_S)]` (for global ascent and
`max(x̄_T, x̂_S) < 1`), and it drops `hID_T`, `h1_T`, `h0_T`, `hsbar_le`,
`hV_T_mono_carrier` and `s̄ ∈ [0, 1]`, and Sender stage complementarity outside
`[0, s̄]`. In economic terms: the stage flip of the Sender, together with the
Sender's forward-looking direction condition, is what locks sanctions in; the
Target's own flip toward preferring sanctions is not needed for that.
General in `F`. -/
theorem standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent
    [p.StaticSelectorContinuous]
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    {sbar mS : ℝ} (hmS_pos : 0 < mS)
    (hID_S : p.SenderStageIDOn (Set.Icc (0 : ℝ) sbar))
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (h_diag_MS : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar
            (max x (max (p.targetFlipPivot sbar)
              (p.senderFlipPivot sbar mS)))) mS)
    (hV_S_mono_carrier : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hIDO_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (hMyoCeiling : ∀ x ∈ Set.Icc
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
      p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (p.targetFlipPivot sbar)
            (p.senderFlipPivot sbar mS)))
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ)
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)),
      x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ D.carrier_T
      ∧ E.V_S ∈ D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc
            (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (max (p.targetFlipPivot sbar)
                              (p.senderFlipPivot sbar mS)) 1) ∧
          (∀ n, max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)
                  ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc
            (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max (p.targetFlipPivot sbar)
                                (p.senderFlipPivot sbar mS)) 1) ∧
            (∀ n, max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)
                    ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                        (p.shockPathF x₀shock N) n)) :=
  StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent
    (StandardCompliancePersistenceCertificate.of_stage_flip p D h_inv
      hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T_op hT_S_op hsuff_T hsuff_S
      hmS_pos hID_S h1_S h_diag_MS hV_S_mono_carrier hIDO_on)
    hMyoCeiling hF_top_pre

end Params
end AbstractGame

end

end Sanctions

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.of_stage_flip
#print axioms Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_min_drift_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent
