/-
Sanctions/Theory/Basin/StageFlipCertificate.lean

**Stage-flip Round B: wiring the derived tipping thresholds into the
one-sided thresholds, the compliance certificate, and the three-goals
headline.**

Round A (`StageFlip.lean`) derived the basin geography from the two
stage-complementarity primitives. This file consumes it:

1. `OneSidedSanctionPreferenceThresholds.of_stage_flip` — the
   one-sided sanction-preference thresholds Prop (the paper's
   Assumptions 1+2 bundle at the `(V_T, V_S, α)` level) built with
   **derived pivots** `xT := targetFlipPivot`,
   `xS := senderFlipPivot`, from: the two ID primitives, boundary
   signs, monotone continuation values, and the Sender's above-floor
   diagonal residual at the equilibrium policy.

2. `StandardComplianceLocalCoreCertificate.of_stage_flip` — the
   alternative certificate constructor. **Moved to
   `Examples/AffineInstance/ComplianceTower.lean` on 2026-08-22** (Rule 22:
   it carries `hF`, so it is affine-restricted by construction). The
   general-transition sibling `StandardComplianceLocalCoreCertificate_MS`
   stays here, and is the route the headlines use. Auto-discharges the entire
   Target loss-offset block at `c_T = 0` (the Target's stage sanction
   loss rate on the basin — zero above the derived flip), `g_T = 0`
   (only plain monotonicity of carrier `V_T` on the basin range
   remains), with the loss-offset margin `c_T ≤ β_T·g_T·δ` trivial;
   derives the certificate locations `xT, xS` as the flip pivots; and
   derives the Sender stage-slope field from the floor flip set plus
   the diagonal residual. The contraction/Schur block, the
   single-crossing field, the myopic comparator + ceiling, and the
   carrier Lipschitz field are retained verbatim (as analyzed: they
   are not consequences of stage supermodularity).

3. `standardCompliance_three_goals_from_stage_flip` (also moved to
   `Examples/AffineInstance/ComplianceTower.lean`; the general-`F` sibling
   `standardCompliance_three_goals_from_stage_flip_generalF` stays here)
   — the wrapper: the three goals (basin-trapped non-decreasing sanctions;
   dynamic ≥ myopic; shock ⇒ permanent high sanctions) at the
   **derived** basin `[max(x̄_T, x̂_S), 1]`, by composing the
   constructor with the existing
   `standardCompliance_three_goals_local_uniform_starts`.

4. `OneSidedSanctionLowBasinPreferenceThresholds.of_stage_flip_low`
   — the low-basin dual (R47 structural prerequisites) from the SAME
   two primitives: below the flips the marginals are negative, so the
   dual flip sets deliver the stage-anti conditions of
   `of_stage_preferences_low` by restriction. One assumption set, two
   basins.

5. (§3b, Round R-ENH) The **general-`F` route**:
   `targetCombinedChordOn_of_stage_flip` (the combined chord of the
   paper's Assumption A2 derived on the basin for ANY (F2)–(F4)
   transition), `StandardComplianceLocalCoreCertificate_MS.of_stage_flip`
   (the MS-certificate constructor with derived pivots; Target block
   fully discharged), and
   `standardCompliance_three_goals_from_stage_flip_generalF` (the
   general-transition three-goals headline wrapper).

6. (Round BH-1, item BH1.8, 2026-10-06) The **persistence route**
   (`StageFlipPersistence.lean`): the same primitives build the persistence
   certificate (`StandardCompliancePersistenceCertificate.of_stage_flip`),
   which carries no Target combined chord and no strict pivot. The general-`F`
   wrapper `standardCompliance_three_goals_from_stage_flip_generalF` is now
   proved as a corollary of the row-1 sibling there; five of its binders
   (`hID_T`, `h1_T`, `h0_T`, `hsbar_le`, `hV_T_mono_carrier`) are no longer
   read and carry a leading underscore. Its statement is unchanged.

## Rule compliance

**Rule 1.** No strategies fixed: the Target policy enters only
through `D.α_on` (Bellman-derived) or a policy `α` whose optimality
is certified downstream; the Sender side is the dynamic argmax
machinery.

**Rule 3.** No new primitives: every input is a Round-A primitive
(user-approved), a boundary sign, the R28 sign restatement, or a
retained certificate field. The diagonal residual is a *strict
subset* of the previous `h_stage_sender_on` field (chords on
`[s̄, x]` instead of `[0, max(x, s̄)]`).

**Rule 5.** Fully parametric.

**Rule 19.** Wiring only; the generic machinery lives in
`Foundations/MonotoneThreshold.lean`.

**Round BJ5.1 (2026-10-07).**
`StandardComplianceLocalCoreCertificate_MS.of_stage_flip` and
`standardCompliance_three_goals_from_stage_flip_generalF` state the myopic
ceiling against `p.myopicFeedbackEquilibrium_canonical` and so take
`[p.StaticSelectorContinuous]`. That class is the static-selector continuity
condition, the joint continuity of the static Sender selector `σ`, which was
the `Params` field `σ_continuous`. The content is unchanged; the condition
moved from the economy to the binder. General in `F`.
-/

import Sanctions.Theory.Basin.StageFlip
import Sanctions.Theory.Basin.StageFlipPersistence
import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Certificates.StandardComplianceLowBasin
import Sanctions.Theory.Bellman.InvariantLipGainBall

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Chord-slope gluing -/

/-- **`LowerSlopeOn` glues across a shared midpoint.** A chord
crossing the midpoint splits into two in-range chords; the slope
bound adds. -/
theorem lowerSlopeOn_glue_Icc {f : ℝ → ℝ} {lo mid hi m : ℝ}
    (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (h₁ : LowerSlopeOn f (Set.Icc lo mid) m)
    (h₂ : LowerSlopeOn f (Set.Icc mid hi) m) :
    LowerSlopeOn f (Set.Icc lo hi) m := by
  intro s₁ hs₁ s₂ hs₂ hs
  rcases le_or_gt s₂ mid with h2 | h2
  · exact h₁ s₁ ⟨hs₁.1, le_trans hs h2⟩ s₂ ⟨hs₂.1, h2⟩ hs
  · rcases le_or_gt mid s₁ with h1 | h1
    · exact h₂ s₁ ⟨h1, hs₁.2⟩ s₂ ⟨le_of_lt h2, hs₂.2⟩ hs
    · have ha := h₁ s₁ ⟨hs₁.1, le_of_lt h1⟩ mid ⟨hlo, le_refl mid⟩
        (le_of_lt h1)
      have hb := h₂ mid ⟨le_refl mid, hhi⟩ s₂ ⟨le_of_lt h2, hs₂.2⟩
        (le_of_lt h2)
      have hsplit : m * (s₂ - s₁) = m * (mid - s₁) + m * (s₂ - mid) := by
        ring
      linarith

/-! ## 1. One-sided thresholds from the stage flip (high basin) -/

/-- **Stage-flip constructor for the one-sided sanction-preference
thresholds.** Builds the paper's Assumptions 1+2 bundle with
**derived pivots**: `xT := targetFlipPivot s̄` and
`xS := senderFlipPivot s̄ m`. Inputs: the two stage-complementarity
primitives, the boundary signs (`1 ∈` each flip set), monotone
continuation values, feasibility of the Target policy, and the
Sender's above-floor diagonal residual (chords on `[s̄, x]` at the
equilibrium policy — the part not derivable from the floor flip set). -/
theorem OneSidedSanctionPreferenceThresholds.of_stage_flip
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_T_mono : Monotone V_T) (h_V_S_mono : Monotone V_S)
    {α : ℝ → ℝ} {sbar m : ℝ} (hm : 0 < m)
    (hID_T : p.TargetStageID) (hID_S : p.SenderStageID)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h1_T : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar m)
    (hα_mem : ∀ x, α x ∈ Sanctions.I)
    (h_diag : ∀ x ∈ Set.Icc (p.senderFlipPivot sbar m) (1 : ℝ),
      sbar < x →
        LowerSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc sbar x) m) :
    p.OneSidedSanctionPreferenceThresholds V_T V_S α
      (p.targetFlipPivot sbar) (p.senderFlipPivot sbar m) sbar := by
  refine OneSidedSanctionPreferenceThresholds.of_stage_preferences p
    h_V_T_mono h_V_S_mono
    (p.targetFlipPivot_mem_I hID_T hsbar_mem h1_T)
    (p.senderFlipPivot_mem_I hID_S hsbar_mem h1_S)
    hsbar_mem ?_ ?_
  · -- Sender stage strict monotonicity on `[0, max(x, s̄)]`.
    intro x hx
    have hxmem : x ∈ p.senderFloorFlipSet sbar m := by
      rw [p.senderFloorFlipSet_eq_Icc hID_S hsbar_mem h1_S]
      exact hx
    have hfloor : LowerSlopeOn (fun s => p.U_S x (α x) s)
        (Set.Icc (0 : ℝ) sbar) m :=
      fun s₁ hs₁ s₂ hs₂ hs =>
        hxmem.2 (α x) (hα_mem x) s₁ hs₁ s₂ hs₂ hs
    have hstrict : ∀ {D : Set ℝ},
        LowerSlopeOn (fun s => p.U_S x (α x) s) D m →
        StrictMonoOn (fun s => p.U_S x (α x) s) D := by
      intro D hD s₁ hs₁ s₂ hs₂ hlt
      have h := hD s₁ hs₁ s₂ hs₂ (le_of_lt hlt)
      have hpos : 0 < m * (s₂ - s₁) := mul_pos hm (sub_pos.mpr hlt)
      simp only at h ⊢
      linarith
    rcases le_or_gt x sbar with hxs | hxs
    · rw [max_eq_right hxs]
      exact hstrict hfloor
    · rw [max_eq_left (le_of_lt hxs)]
      exact hstrict
        (lowerSlopeOn_glue_Icc hsbar_mem.1 (le_of_lt hxs) hfloor
          (h_diag x hx hxs))
  · -- Target stage monotonicity on the per-state high range.
    intro x hx
    have hxmem : x ∈ p.targetFlipSet sbar := by
      rw [p.targetFlipSet_eq_Icc hID_T hsbar_mem h1_T]
      exact hx
    exact p.monotoneOn_high_range_of_mem_targetFlipSet hxmem (hα_mem x)

/-! ## 2. The stage-flip certificate constructor -/


/-- **General-`F` combined chord from the stage flip.** Above the
Target flip pivot, the Target's joint dynamic objective (stage payoff
plus discounted continuation at the transitioned state) has
non-negative sanction chords on `[max(x, b), 1]` for any range floor
`b` with `s̄ ≤ b`: the stage chord comes from flip-set membership, the
continuation chord from carrier `V_T` monotonicity on the basin range,
which the transition cannot exit (`F(x,s) ≥ F(x,x) = x` for `s ≥ x`).
Works for every transition law satisfying (F2)–(F4). -/
theorem targetCombinedChordOn_of_stage_flip
    (D : p.ValueClass2)
    {sbar b : ℝ} (hsbar_mem : sbar ∈ Sanctions.I)
    (hID_T : p.TargetStageID)
    (h1_T : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (hsbar_le : sbar ≤ b)
    (hV_T_mono_carrier : ∀ V_T ∈ D.carrier_T,
      LowerSlopeOnValueOn V_T
        (Set.Icc (p.targetFlipPivot sbar) 1) 0) :
    p.TargetCombinedChordOn D (p.targetFlipPivot sbar) b := by
  intro V_T V_S x hx s₁ hs₁ s₂ hs₂ hle
  have hxT_mem := p.targetFlipPivot_mem_I hID_T hsbar_mem h1_T
  have hx_lo : (0 : ℝ) ≤ x := le_trans hxT_mem.1 hx.1
  have hx_hi : x ≤ 1 := hx.2
  -- `s_i ≥ x` (via `max x b ≥ x`) and `s_i ≥ s̄` (via `b ≥ s̄`).
  have hs₁_ge_x : x ≤ s₁ := le_trans (le_max_left _ _) hs₁.1
  have hs₂_ge_x : x ≤ s₂ := le_trans (le_max_left _ _) hs₂.1
  have hs₁_ge_sbar : sbar ≤ s₁ :=
    le_trans hsbar_le (le_trans (le_max_right _ _) hs₁.1)
  have hs₂_ge_sbar : sbar ≤ s₂ :=
    le_trans hsbar_le (le_trans (le_max_right _ _) hs₂.1)
  -- Stage chord: flip-set membership above the pivot.
  have hxflip : x ∈ p.targetFlipSet sbar := by
    rw [p.targetFlipSet_eq_Icc hID_T hsbar_mem h1_T]
    exact ⟨hx.1, hx.2⟩
  have h_stage : p.U_T x (D.α_on V_T V_S x) s₁
      ≤ p.U_T x (D.α_on V_T V_S x) s₂ :=
    hxflip.2 (D.α_on V_T V_S x) (D.α_on_mem V_T V_S x)
      s₁ ⟨hs₁_ge_sbar, hs₁.2⟩ s₂ ⟨hs₂_ge_sbar, hs₂.2⟩ hle
  -- Continuation chord: the transitioned states stay in `[x, 1] ⊆
  -- [pivot, 1]` (general `F`: diagonal fixed + monotone in `s`).
  have hx_I : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx_lo, hx_hi⟩
  have hs₁_I : s₁ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hx_lo hs₁_ge_x, hs₁.2⟩
  have hs₂_I : s₂ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans hx_lo hs₂_ge_x, hs₂.2⟩
  have hF₁_mem : p.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem x s₁ hx_I hs₁_I
  have hF₂_mem : p.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem x s₂ hx_I hs₂_I
  have hF₁_ge_x : x ≤ p.F x s₁ := by
    have h : p.F x x ≤ p.F x s₁ := p.F_mono_s x hs₁_ge_x
    rwa [p.F_diag x] at h
  have hF₂_ge_x : x ≤ p.F x s₂ := by
    have h : p.F x x ≤ p.F x s₂ := p.F_mono_s x hs₂_ge_x
    rwa [p.F_diag x] at h
  have hF₁₂ : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hle
  -- `clipS'` acts as the identity on `[0, 1]`.
  have hclip1_val : (Sanctions.clipS' (p.F x s₁)).val = p.F x s₁ := by
    show Sanctions.clipS (p.F x s₁) = p.F x s₁
    unfold Sanctions.clipS
    rw [min_eq_right hF₁_mem.2, max_eq_right hF₁_mem.1]
  have hclip2_val : (Sanctions.clipS' (p.F x s₂)).val = p.F x s₂ := by
    show Sanctions.clipS (p.F x s₂) = p.F x s₂
    unfold Sanctions.clipS
    rw [min_eq_right hF₂_mem.2, max_eq_right hF₂_mem.1]
  have hclip1_mem : (Sanctions.clipS' (p.F x s₁)).val
      ∈ Set.Icc (p.targetFlipPivot sbar) 1 := by
    rw [hclip1_val]; exact ⟨le_trans hx.1 hF₁_ge_x, hF₁_mem.2⟩
  have hclip2_mem : (Sanctions.clipS' (p.F x s₂)).val
      ∈ Set.Icc (p.targetFlipPivot sbar) 1 := by
    rw [hclip2_val]; exact ⟨le_trans hx.1 hF₂_ge_x, hF₂_mem.2⟩
  have hclip12 : Sanctions.clipS' (p.F x s₁) ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono hF₁₂
  have h_val := hV_T_mono_carrier V_T.val V_T.property
    (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
    hclip1_mem hclip2_mem hclip12
  have h_val' : (0 : ℝ) ≤ V_T.val (Sanctions.clipS' (p.F x s₂))
      - V_T.val (Sanctions.clipS' (p.F x s₁)) := by
    simpa using h_val
  have hβT_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_cont : p.β_T * V_T.val (Sanctions.clipS' (p.F x s₁))
      ≤ p.β_T * V_T.val (Sanctions.clipS' (p.F x s₂)) :=
    mul_le_mul_of_nonneg_left (by linarith) hβT_nn
  linarith

/-- **Stage-flip constructor for the general-`F` (MS) certificate.**
Builds `StandardComplianceLocalCoreCertificate_MS` — the certificate
consumed by the general-transition headline — with **derived pivots**
`xT := targetFlipPivot s̄`, `xS := senderFlipPivot s̄ m_S`. Compared
with the affine constructor `of_stage_flip`:

* the Target block needs no loss-offset data at all: the combined
  chord `h_target_combined` is **discharged** by
  `targetCombinedChordOn_of_stage_flip` (flip-set stage chords +
  carrier `V_T` monotonicity + (F2)–(F4)), machine-checking the
  "Assumption A2 is a theorem on the derived basin" claim for any
  monotone transition;
* the A1 MS-form strict monotonicity is derived from the Sender floor
  flip set glued with the diagonal residual `h_diag_MS` (whose range
  extends to the joint pivot), at the strictly positive wedge slope;
* pivot interiority `hpivot_mem` consumes the second boundary sign
  `h0_T : 0 ∉ targetFlipSet` (prop:tipping's other half);
* the ordering `hsbar_le : s̄ ≤ max(x̄_T, x̂_S)` (sanction floor below
  the joint pivot) aligns the flip-set chord range with the MS
  certificate's basin-anchored chord range. -/
noncomputable def StandardComplianceLocalCoreCertificate_MS.of_stage_flip
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
    {sbar mS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I) (hmS_pos : 0 < mS)
    (hID_T : p.TargetStageID) (hID_S : p.SenderStageID)
    (h1_T : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (h0_T : (0 : ℝ) ∉ p.targetFlipSet sbar)
    (hjoint_lt :
      max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS) < 1)
    (hsbar_le :
      sbar ≤ max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS))
    (h_diag_MS : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar
            (max x (max (p.targetFlipPivot sbar)
              (p.senderFlipPivot sbar mS)))) mS)
    (hV_T_mono_carrier : ∀ V_T ∈ D.carrier_T,
      LowerSlopeOnValueOn V_T
        (Set.Icc (p.targetFlipPivot sbar) 1) 0)
    (hV_S_mono_carrier : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hSC_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (hMyoCeiling : ∀ x ∈ Set.Icc
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
      p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (p.targetFlipPivot sbar)
            (p.senderFlipPivot sbar mS))) :
    p.StandardComplianceLocalCoreCertificate_MS where
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
  hxT_mem := p.targetFlipPivot_mem_I hID_T hsbar_mem h1_T
  hxS_mem := p.senderFlipPivot_mem_I hID_S hsbar_mem h1_S
  hpivot_mem :=
    ⟨lt_max_of_lt_left (p.targetFlipPivot_pos hID_T hsbar_mem h1_T h0_T),
     hjoint_lt⟩
  h_stage_sender_strictMono := by
    intro V_T V_S x hx
    -- Slope `m_S` on the full interval, by gluing the floor flip set
    -- with the diagonal residual at the shared midpoint `s̄`.
    have hxmem : x ∈ p.senderFloorFlipSet sbar mS := by
      rw [p.senderFloorFlipSet_eq_Icc hID_S hsbar_mem h1_S]
      exact hx
    have hfloor : LowerSlopeOn
        (fun s => p.U_S x (D.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) sbar) mS :=
      fun s₁ hs₁ s₂ hs₂ hs =>
        hxmem.2 (D.α_on V_T V_S x) (D.α_on_mem V_T V_S x)
          s₁ hs₁ s₂ hs₂ hs
    have hsbar_le_top : sbar ≤ max x (max (p.targetFlipPivot sbar)
        (p.senderFlipPivot sbar mS)) :=
      le_trans hsbar_le (le_max_right _ _)
    have hslope : LowerSlopeOn
        (fun s => p.U_S x (D.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (max (p.targetFlipPivot sbar)
          (p.senderFlipPivot sbar mS)))) mS :=
      lowerSlopeOn_glue_Icc hsbar_mem.1 hsbar_le_top hfloor
        (h_diag_MS V_T V_S x hx)
    -- Positive lower slope ⇒ strict monotonicity.
    intro s₁ hs₁ s₂ hs₂ hlt
    have hchord := hslope s₁ hs₁ s₂ hs₂ hlt.le
    have hpos : 0 < mS * (s₂ - s₁) :=
      mul_pos hmS_pos (sub_pos.mpr hlt)
    linarith
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (hSC_on V_T V_S)
  h_target_combined :=
    p.targetCombinedChordOn_of_stage_flip D hsbar_mem hID_T h1_T
      hsbar_le hV_T_mono_carrier
  hV_S_mono_carrier := hV_S_mono_carrier
  hMyoCeiling := hMyoCeiling

/-- **Three goals from stage supermodularity, general transition law
(headline wrapper, Round R-GF).** Composes the MS-certificate
stage-flip constructor with the general-`F` headline
`standardCompliance_three_goals_local_MS_generalF`: the three-goals
package at the **derived** basin `[max(x̄_T, x̂_S), 1]`, with the
realized political-state trajectory evolved by an **arbitrary**
transition law satisfying (F1)–(F4) plus strict ascent at full
sanctions (`hF_top`, Goal-3 finite entry only). The affine wrapper
`standardCompliance_three_goals_from_stage_flip` is the
`F := affineF δ` specialisation; the price of generality is the loss
of the closed-form shock horizon (Goal 3 asserts only `∃ N`).

Round BH-1 (item BH1.8, 2026-10-06): proved as a corollary of
`standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent`
(`StageFlipPersistence.lean`), the route through the persistence certificate.
The bridge reads `SenderStageID` only on `[0, s̄]` (via `s̄ ≤ 1`), single
crossing only through the interval dominance it implies, and `hF_top` with
`hjoint_lt` only through ascent on `[0, max(x̄_T, x̂_S)]`. The binders
`_hID_T`, `_h1_T`, `_h0_T`, `_hsbar_le` and `_hV_T_mono_carrier` are no longer
read: they fed only the MS certificate's Target combined chord and its strict
pivot, which none of the three goals uses. They are kept, so the statement is
unchanged. General in `F`. -/
theorem standardCompliance_three_goals_from_stage_flip_generalF [p.StaticSelectorContinuous]
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
    {sbar mS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I) (hmS_pos : 0 < mS)
    (_hID_T : p.TargetStageID) (hID_S : p.SenderStageID)
    (_h1_T : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (_h0_T : (0 : ℝ) ∉ p.targetFlipSet sbar)
    (hjoint_lt :
      max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS) < 1)
    (_hsbar_le :
      sbar ≤ max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS))
    (h_diag_MS : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar
            (max x (max (p.targetFlipPivot sbar)
              (p.senderFlipPivot sbar mS)))) mS)
    (_hV_T_mono_carrier : ∀ V_T ∈ D.carrier_T,
      LowerSlopeOnValueOn V_T
        (Set.Icc (p.targetFlipPivot sbar) 1) 0)
    (hV_S_mono_carrier : ∀ V_S ∈ D.carrier_S, Monotone V_S)
    (hSC_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (hMyoCeiling : ∀ x ∈ Set.Icc
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
      p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
        ≤ max x (max (p.targetFlipPivot sbar)
            (p.senderFlipPivot sbar mS)))
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) :
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
  standardCompliance_three_goals_from_stage_flip_generalF_of_preBasinAscent p D h_inv
    hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T_op hT_S_op hsuff_T hsuff_S hmS_pos
    (p.senderStageIDOn_of_senderStageID hID_S
      (fun _ hs => ⟨hs.1, le_trans hs.2 hsbar_mem.2⟩))
    h1_S h_diag_MS hV_S_mono_carrier
    (fun V_T V_S =>
      Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
        (hSC_on V_T V_S))
    hMyoCeiling (p.preBasinAscent_of_hF_top hF_top hjoint_lt)

/-! ## 4. Low-basin dual: one assumption set, two basins -/

/-- **Stage-flip constructor for the dual (low-basin) one-sided
thresholds.** The R47 structural prerequisites from the SAME two
stage-complementarity primitives: below the flips the sanction
marginals are negative, so the dual flip sets (downward closed,
derived ceilings `x̄*_T := targetLowFlipPivot`,
`x̄*_S := senderLowFlipPivot m`) deliver the stage-anti conditions of
`of_stage_preferences_low` by restriction to the R47 per-state
ranges. Inputs: the primitives, the dual boundary signs (`0 ∈` each
low flip set — the dovish corner is unflipped), antitone continuation
values (the low-basin regime), policy feasibility, and a free
sanction-range pivot `s̄*`. -/
theorem OneSidedSanctionLowBasinPreferenceThresholds.of_stage_flip_low
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (h_V_T_anti : Antitone V_T) (h_V_S_anti : Antitone V_S)
    {α : ℝ → ℝ} {sbar_star m : ℝ} (hm : 0 < m)
    (hID_T : p.TargetStageID) (hID_S : p.SenderStageID)
    (hsbar_star_mem : sbar_star ∈ Sanctions.I)
    (h0_T : (0 : ℝ) ∈ p.targetLowFlipSet)
    (h0_S : (0 : ℝ) ∈ p.senderLowFlipSet m)
    (hα_mem : ∀ x, α x ∈ Sanctions.I) :
    p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α
      p.targetLowFlipPivot (p.senderLowFlipPivot m) sbar_star := by
  refine
    OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low p
      h_V_T_anti h_V_S_anti
      (p.targetLowFlipPivot_mem_I hID_T h0_T)
      hsbar_star_mem ?_ ?_
  · -- Sender stage strict antitonicity on the per-state range.
    intro x hx
    have hxmem : x ∈ p.senderLowFlipSet m := by
      rw [p.senderLowFlipSet_eq_Icc hID_S h0_S]
      exact hx
    exact p.strictAntiOn_of_mem_senderLowFlipSet hm hxmem (hα_mem x)
      hsbar_star_mem
  · -- Target stage antitonicity on the per-state range.
    intro x hx
    have hxmem : x ∈ p.targetLowFlipSet := by
      rw [p.targetLowFlipSet_eq_Icc hID_T h0_T]
      exact hx
    exact p.antitoneOn_of_mem_targetLowFlipSet hxmem (hα_mem x)
      hsbar_star_mem

/-! ## Round E5 — carrier-choice discharge of the flip route's
`V_T`-monotonicity input

The stage-flip certificate constructor takes
`hV_T_mono_carrier : ∀ V_T ∈ D.carrier_T, LowerSlopeOnValueOn V_T
(Icc x̄_T 1) 0` (every carrier Target value is non-decreasing on the
basin range — the `g_T = 0` weakening of the old continuation-gain
field). For any carrier contained in a monotone-Lipschitz gain ball
`valLipGainBall M K 0 c` with `c` at or below the derived pivot, this
input is **automatic from carrier membership** — a carrier-choice
fact, not an assumption. Invariance of such carriers is the existing
R27 preservation theorem
(`jointTarget_BCF_lowerSlope_of_integrand_lowerSlope` at `g := 0`), which
consumes integrand-level state-monotonicity on the basin; deriving
THAT from stage primitives remains open (the σ-channel inside the
substituted integrand is unsigned at non-equilibrium actions —
documented in BUILD-STATUS), so no new primitive is introduced
here. -/

/-- **Flip-route `V_T`-monotonicity from a gain-ball carrier
(Round E5).** If the Target carrier sits inside a monotone-Lipschitz
gain ball at slope level `0` whose range starts at or below `xT'`,
then every carrier Target value is non-decreasing on `[xT', 1]` —
exactly the `hV_T_mono_carrier` input of
`StandardComplianceLocalCoreCertificate.of_stage_flip`. -/
theorem hV_T_mono_carrier_of_gainBall_subset
    (D : p.ValueClass2) {M K c xT' : ℝ}
    (hsub : D.carrier_T ⊆ valLipGainBall M K 0 c)
    (hc : c ≤ xT') :
    ∀ V_T ∈ D.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc xT' 1) 0 := by
  intro V_T hV_T y₁ y₂ h₁ h₂ hle
  have hball := hsub hV_T
  exact hball.2.2 y₁ y₂
    ⟨le_trans hc h₁.1, h₁.2⟩ ⟨le_trans hc h₂.1, h₂.2⟩ hle

/-- **`hV_S_mono_carrier` discharger at gain-ball carriers.** If the
Sender carrier sits inside a zero-based gain ball with nonnegative
minimum slope, then every carrier Sender value function is genuinely
`Monotone` — exactly the `hV_S_mono_carrier` field of the MS-form
certificate `StandardComplianceLocalCoreCertificate_MS`. The MS route's
carrier-monotonicity input is therefore automatic from carrier geometry
(no extra assumption) whenever the Sender carrier is a nonnegative-gain
ball — as with the certificate-complete witness carriers
`valLipGainBall M c c 0`. -/
theorem hV_S_mono_carrier_of_gainBall_subset
    (D : p.ValueClass2) {M K g : ℝ} (hg : 0 ≤ g)
    (hsub : D.carrier_S ⊆ valLipGainBall M K g 0) :
    ∀ V_S ∈ D.carrier_S, Monotone V_S :=
  fun _ hV_S => monotone_of_mem_valLipGainBall hg (hsub hV_S)

/-- **Same-action dynamic dominance directly from gain-ball membership.**
The nonnegative minimum-slope clause of a zero-based gain ball first yields
`Monotone V_S`; the Milgrom--Shannon upper-argmax comparison then gives the
paper's same-`α` dynamic-over-myopic sanction inequality.  This makes the
monotonicity premise an explicit derived carrier fact rather than a hidden
assumption at gain-ball witnesses. -/
theorem theorem2_dynamic_dominates_myopic_at_same_alpha_of_mem_valLipGainBall
    {M K g : ℝ} (hg : 0 ≤ g) {V_S : Val}
    (hV_S : V_S ∈ valLipGainBall M K g 0) (α : ℝ → ℝ) (x : ℝ) :
    p.σ x (α x) ≤ p.σ_dyn_top V_S x (α x) :=
  p.theorem2_dynamic_dominates_myopic_at_same_alpha V_S
    (monotone_of_mem_valLipGainBall hg hV_S) α x

end Params
end AbstractGame

end

end Sanctions
